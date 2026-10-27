module

public import CFSG.LocalAnalysis.StandardType.GGSixTCWP4Inputs
public import CFSG.LieType.Chevalley.RootCharacterConjugation
public import CFSG.LieType.Chevalley.GraphFixedD4TorusWords
public import CFSG.LieType.Chevalley.RootCharacterKernelProduct

public section

namespace CFSG.StandardType.TableCRes

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.LieType.AlgebraicGroups
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.HardMathSupport.Timmesfeld.LangTorus

section Counting

variable {τ : Tag} {L : Type} [Field L]

theorem rootChar_pow_eq_one_of_forall {p : ℕ} {a : Fin τ.rank → Lˣ} (ha : ∀ j, a j ^ p = 1)
    (v : Fin τ.rank → ℤ) : rootChar a v ^ p = 1 := by
  rw [rootChar, ← Finset.prod_pow]
  refine Finset.prod_eq_one fun i _ => ?_
  rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, ha i, one_zpow]

theorem rootChar_mul_tuple_fam (a b : Fin τ.rank → Lˣ) (v : Fin τ.rank → ℤ) :
    rootChar (a * b) v = rootChar a v * rootChar b v := by
  simp only [rootChar, Pi.mul_apply, mul_zpow, Finset.prod_mul_distrib]

theorem rootChar_one_tuple' (v : Fin τ.rank → ℤ) : rootChar (1 : Fin τ.rank → Lˣ) v = 1 := by
  simp [rootChar]

theorem rootChar_zsmul' (a : Fin τ.rank → Lˣ) (n : ℤ) (v : Fin τ.rank → ℤ) :
    rootChar a (n • v) = rootChar a v ^ n := by
  unfold rootChar
  rw [← Finset.prod_zpow]
  refine Finset.prod_congr rfl fun i _ => ?_
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [mul_comm, zpow_mul]

theorem rootChar_sum' (a : Fin τ.rank → Lˣ) {ι : Type*} (s : Finset ι)
    (f : ι → Fin τ.rank → ℤ) : rootChar a (∑ i ∈ s, f i) = (∏ i ∈ s, rootChar a (f i) : Lˣ) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [rootChar_zero]
  | insert i s hi ih => rw [Finset.sum_insert hi, Finset.prod_insert hi, rootChar_add, ih]

theorem card_le_mul_pow_of_torus
      {p : ℕ} [NeZero p]
    (B₁ D₁ : Subgroup (ModGL τ L)) [Finite B₁]
    (hB : ∀ b ∈ B₁, ∃ a : Fin τ.rank → Lˣ, b = rootDiagUnit τ a ∧ ∀ j, a j ^ p = 1)
    (Λ : Submodule ℤ (Fin τ.rank → ℤ))
    (hD : ∀ b ∈ B₁, ∀ a : Fin τ.rank → Lˣ, b = rootDiagUnit τ a →
      (∀ v ∈ Λ, rootChar a v = 1) → b ∈ D₁) (hDB : D₁ ≤ B₁) :
    Nat.card B₁ ≤ Nat.card D₁ * p ^ Module.finrank ℤ Λ := by
  classical
  choose! a ha hap using hB
  let bs := Module.Free.chooseBasis ℤ Λ
  have hamul : ∀ x ∈ B₁, ∀ y ∈ B₁, a (x * y) = a x * a y := fun x hx y hy =>
    rootDiagUnit_injective (by
      rw [← ha _ (B₁.mul_mem hx hy), rootDiagUnit_mul, ← ha _ hx, ← ha _ hy])
  have ha1 : a 1 = 1 := rootDiagUnit_injective (by rw [← ha 1 B₁.one_mem, rootDiagUnit_one])
  let E : B₁ →* (Module.Free.ChooseBasisIndex ℤ Λ → Lˣ) :=
    { toFun := fun b k => rootChar (a (b : ModGL τ L)) ((bs k : Λ) : Fin τ.rank → ℤ)
      map_one' := by
        funext k
        simp [ha1, rootChar_one_tuple']
      map_mul' := by
        intro x y
        funext k
        simp [hamul _ x.2 _ y.2, rootChar_mul_tuple_fam] }
  have : Finite D₁ := Finite.of_injective (fun x : D₁ => (⟨x, hDB x.2⟩ : B₁))
    (fun x y h => Subtype.ext (by have h' := congrArg Subtype.val h; exact h'))
  have hker : ∀ x : B₁, x ∈ E.ker → (x : ModGL τ L) ∈ D₁ := by
    intro x hx
    rw [MonoidHom.mem_ker] at hx
    refine hD x x.2 (a x) (ha x x.2) fun v hv => ?_
    have hrepr := bs.sum_repr ⟨v, hv⟩
    have hv' : v = ∑ k, (bs.repr ⟨v, hv⟩ k) • ((bs k : Λ) : Fin τ.rank → ℤ) := by
      have h2 := congrArg Subtype.val hrepr.symm
      rw [Submodule.coe_sum] at h2
      exact h2
    rw [hv', rootChar_sum']
    refine Finset.prod_eq_one fun k _ => ?_
    rw [rootChar_zsmul']
    have h3 : rootChar (a (x : ModGL τ L)) ((bs k : Λ) : Fin τ.rank → ℤ) = 1 := congrFun hx k
    rw [h3, one_zpow]
  have h1 : Nat.card E.ker ≤ Nat.card D₁ :=
    Nat.card_le_card_of_injective (fun x : E.ker => (⟨(x : B₁), hker x x.2⟩ : D₁))
      (fun x y h => Subtype.ext (Subtype.ext (by have h' := congrArg Subtype.val h; exact h')))
  have h2 : Nat.card E.range ≤ p ^ Module.finrank ℤ Λ := by
    have hmem : ∀ (y : E.range) (k : Module.Free.ChooseBasisIndex ℤ Λ), (y : _ → Lˣ) k ∈
        rootsOfUnity p L := by
      rintro ⟨_, b, rfl⟩ k
      rw [mem_rootsOfUnity]
      exact rootChar_pow_eq_one_of_forall (hap b b.2) _
    calc Nat.card E.range
        ≤ Nat.card (Module.Free.ChooseBasisIndex ℤ Λ → rootsOfUnity p L) :=
          Nat.card_le_card_of_injective (fun y k => ⟨(y : _ → Lˣ) k, hmem y k⟩)
            (fun y y' h => Subtype.ext (funext fun k => congrArg Subtype.val (congrFun h k)))
      _ = Nat.card (rootsOfUnity p L) ^ Nat.card (Module.Free.ChooseBasisIndex ℤ Λ) :=
          Nat.card_fun
      _ ≤ p ^ Module.finrank ℤ Λ := by
          rw [Nat.card_eq_fintype_card (α := Module.Free.ChooseBasisIndex ℤ Λ),
            ← Module.finrank_eq_card_chooseBasisIndex]
          exact Nat.pow_le_pow_left (card_rootsOfUnity ..) _
  calc Nat.card B₁ = Nat.card E.ker * Nat.card E.range := (Subgroup.card_ker_mul_card_range E).symm
    _ ≤ Nat.card D₁ * p ^ Module.finrank ℤ Λ := Nat.mul_le_mul h1 h2

end Counting

section Orbit

variable {τ : Tag} {L : Type} [Field L] {p₀ : ℕ}

abbrev famCharHom {ι : Type} (a : ι → Fin τ.rank → Lˣ) :
    Multiplicative (Fin τ.rank → ℤ) →* (ι → Lˣ) :=
  Pi.monoidHom fun u => rootCharHom (a u)

abbrev famOrbit (ρ : Equiv.Perm (Fin τ.rank → ℤ)) {ι : Type} (a : ι → Fin τ.rank → Lˣ)
    (i : KernelComponent (famCharHom a)) : Set (Fin τ.rank → ℤ) :=
  {γ | ∃ (k : ℕ) (δ : Fin τ.rank → ℤ), δ ∈ componentRoots (famCharHom a) i ∧
    γ = (ρ : (Fin τ.rank → ℤ) → (Fin τ.rank → ℤ))^[k] δ}

theorem mem_kernelRoots_famChar {ι : Type}
    (a : ι → Fin τ.rank → Lˣ) {γ : Fin τ.rank → ℤ} :
    γ ∈ kernelRoots (famCharHom a) ↔ IsRoot τ γ ∧ ∀ u, rootChar (a u) γ = 1 := by
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨h1, fun u => congrFun h2 u⟩
  · rintro ⟨h1, h2⟩
    exact ⟨h1, funext h2⟩

theorem rho_mem_kernelRoots_famChar
    [IsAlgClosed L]
    (S : LangSetup τ L p₀)
    {ι : Type} (a : ι → Fin τ.rank → Lˣ) (ha : ∀ u, rootDiagUnit τ (a u) ∈ S.D.torus)
    {γ : Fin τ.rank → ℤ} (hγ : γ ∈ kernelRoots (famCharHom a)) :
    S.ρ γ ∈ kernelRoots (famCharHom a) := by
  obtain ⟨h1, h2⟩ := (mem_kernelRoots_famChar a).1 hγ
  refine (mem_kernelRoots_famChar a).2 ⟨(S.frob.isRoot_iff γ).2 h1, fun u => ?_⟩
  rw [S.frob.rootChar_eq (a u) (ha u) γ h1, h2 u, one_pow]

end Orbit

section ImageComponent

open Matrix

variable {τ : Tag} {M : Type*} [CommGroup M]

private theorem eqvGen_map' {α β : Type*} {R : α → α → Prop} {R' : β → β → Prop} (f : α → β)
    (hf : ∀ x y, R x y → R' (f x) (f y)) {x y : α} (h : Relation.EqvGen R x y) :
    Relation.EqvGen R' (f x) (f y) := by
  induction h with
  | rel x y h => exact Relation.EqvGen.rel _ _ (hf x y h)
  | refl x => exact Relation.EqvGen.refl _
  | symm x y _ ih => exact Relation.EqvGen.symm _ _ ih
  | trans x y z _ _ ih1 ih2 => exact Relation.EqvGen.trans _ _ _ ih1 ih2

theorem exists_image_component_of_stable
    {ρ : Equiv.Perm (Fin τ.rank → ℤ)}
    (χ : Multiplicative (Fin τ.rank → ℤ) →* M) (hker : ∀ γ ∈ kernelRoots χ, ρ γ ∈ kernelRoots χ)
    (hform : ∀ γ δ, iform (ρ γ) (ρ δ) = iform γ δ) (i : KernelComponent χ) :
    ∃ j : KernelComponent χ, (ρ : (Fin τ.rank → ℤ) → _) '' componentRoots χ i =
      componentRoots χ j := by
  have hfin : (kernelRoots χ).Finite := (finite_setOf_isRoot τ).subset fun α hα => hα.1
  have hmaps : Set.MapsTo (ρ : (Fin τ.rank → ℤ) → _) (kernelRoots χ) (kernelRoots χ) :=
    fun γ hγ => hker γ hγ
  have hbij := (hfin.injOn_iff_bijOn_of_mapsTo hmaps).1 ρ.injective.injOn
  have hsymm : ∀ δ ∈ kernelRoots χ, ρ.symm δ ∈ kernelRoots χ := by
    intro δ hδ
    obtain ⟨γ, hγ, rfl⟩ := hbij.surjOn hδ
    simpa using hγ
  obtain ⟨γ₀, rfl⟩ := Quotient.exists_rep i
  let σ : kernelRoots χ → kernelRoots χ := fun γ => ⟨ρ γ, hker γ γ.2⟩
  have hrel : ∀ x y : kernelRoots χ,
      ((x : Fin τ.rank → ℤ) ⬝ᵥ (τ.symmetrizedCartan *ᵥ (y : Fin τ.rank → ℤ)) ≠ 0) →
      ((σ x : Fin τ.rank → ℤ) ⬝ᵥ (τ.symmetrizedCartan *ᵥ (σ y : Fin τ.rank → ℤ)) ≠ 0) := by
    intro x y h
    rw [dotProduct_mulVec_eq_iform] at h ⊢
    exact fun h0 => h (by rw [← hform]; exact h0)
  have hrel' : ∀ x y : kernelRoots χ,
      ((x : Fin τ.rank → ℤ) ⬝ᵥ (τ.symmetrizedCartan *ᵥ (y : Fin τ.rank → ℤ)) ≠ 0) →
      ((⟨ρ.symm x, hsymm x x.2⟩ : kernelRoots χ) : Fin τ.rank → ℤ) ⬝ᵥ (τ.symmetrizedCartan *ᵥ
        ((⟨ρ.symm y, hsymm y y.2⟩ : kernelRoots χ) : Fin τ.rank → ℤ)) ≠ 0 := by
    intro x y h
    rw [dotProduct_mulVec_eq_iform] at h ⊢
    simp only
    have := hform (ρ.symm x) (ρ.symm y)
    simp only [Equiv.apply_symm_apply] at this
    rw [← this]
    exact h
  refine ⟨⟦σ γ₀⟧, ?_⟩
  ext δ
  constructor
  · rintro ⟨γ, ⟨hγ, hγi⟩, rfl⟩
    refine ⟨hker γ hγ, ?_⟩
    have h1 : Relation.EqvGen _ (⟨γ, hγ⟩ : kernelRoots χ) γ₀ := Quotient.exact hγi
    exact Quotient.sound (eqvGen_map' (R := fun α β : kernelRoots χ =>
      (α : Fin τ.rank → ℤ) ⬝ᵥ (τ.symmetrizedCartan *ᵥ (β : Fin τ.rank → ℤ)) ≠ 0)
      (R' := fun α β : kernelRoots χ =>
      (α : Fin τ.rank → ℤ) ⬝ᵥ (τ.symmetrizedCartan *ᵥ (β : Fin τ.rank → ℤ)) ≠ 0)
      σ hrel h1)
  · rintro ⟨hδ, hδi⟩
    refine ⟨ρ.symm δ, ⟨hsymm δ hδ, ?_⟩, by simp⟩
    have h1 : Relation.EqvGen _ (⟨δ, hδ⟩ : kernelRoots χ) (σ γ₀) := Quotient.exact hδi
    have h2 := eqvGen_map' (R := fun α β : kernelRoots χ =>
      (α : Fin τ.rank → ℤ) ⬝ᵥ (τ.symmetrizedCartan *ᵥ (β : Fin τ.rank → ℤ)) ≠ 0)
      (R' := fun α β : kernelRoots χ =>
      (α : Fin τ.rank → ℤ) ⬝ᵥ (τ.symmetrizedCartan *ᵥ (β : Fin τ.rank → ℤ)) ≠ 0)
      (fun x : kernelRoots χ => (⟨ρ.symm x, hsymm x x.2⟩ : kernelRoots χ)) hrel' h1
    refine Quotient.sound ?_
    have h3 : (⟨ρ.symm (σ γ₀ : Fin τ.rank → ℤ), hsymm _ (σ γ₀).2⟩ : kernelRoots χ) = γ₀ :=
      Subtype.ext (by simp [σ])
    rw [h3] at h2
    exact h2

theorem image_ne_of_two_le_componentOrbitLength {ρ : Equiv.Perm (Fin τ.rank → ℤ)}
    {Ψ : Set (Fin τ.rank → ℤ)} (h : 2 ≤ componentOrbitLength ρ Ψ) :
    (ρ : (Fin τ.rank → ℤ) → _) '' Ψ ≠ Ψ := by
  intro heq
  have h1 : componentOrbitLength ρ Ψ ≤ 1 :=
    Nat.sInf_le ⟨Nat.one_pos, by simpa using heq⟩
  omega

theorem iform_eq_zero_of_mem_componentRoots'
    {χ : Multiplicative (Fin τ.rank → ℤ) →* M} {i j : KernelComponent χ} (hij : i ≠ j)
    {α β : Fin τ.rank → ℤ} (hα : α ∈ componentRoots χ i) (hβ : β ∈ componentRoots χ j) :
    iform α β = 0 := by
  obtain ⟨hα', rfl⟩ := hα
  obtain ⟨hβ', rfl⟩ := hβ
  exact iform_eq_zero_of_mk_ne hij

end ImageComponent

section Centralizer

variable {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] {p₀ : ℕ}

theorem rootSpan_rationalRoots_le_centralizer
    (S : LangSetup τ L p₀) {ι : Type} (a : ι → Fin τ.rank → Lˣ) (i : KernelComponent (famCharHom a))
    {b : Fin τ.rank → Lˣ} (hb : rootDiagUnit τ b ∈ S.D.torus)
    (hb1 : ∀ γ ∈ componentRoots (famCharHom a) i, rootChar b γ = 1) :
    rootSpan τ L (famOrbit S.ρ a i) ≤
      Subgroup.centralizer ({rootDiagUnit τ b} : Set (ModGL τ L)) := by
  have key : ∀ k : ℕ, ∀ δ, IsRoot τ δ → rootChar b δ = 1 →
      IsRoot τ ((S.ρ : (Fin τ.rank → ℤ) → _)^[k] δ) ∧
        rootChar b ((S.ρ : (Fin τ.rank → ℤ) → _)^[k] δ) = 1 := by
    intro k
    induction k with
    | zero => intro δ h1 h2; exact ⟨h1, h2⟩
    | succ k ih =>
      intro δ h1 h2
      obtain ⟨h3, h4⟩ := ih δ h1 h2
      rw [Function.iterate_succ_apply']
      exact ⟨(S.frob.isRoot_iff _).2 h3, by rw [S.frob.rootChar_eq b hb _ h3, h4, one_pow]⟩
  unfold rootSpan
  refine iSup₂_le fun α hα => ?_
  obtain ⟨k, δ, hδ, rfl⟩ := hα
  have hδr : IsRoot τ δ := by
    obtain ⟨h, -⟩ := hδ
    exact h.1
  obtain ⟨hr, hc⟩ := key k δ hδr (hb1 δ hδ)
  unfold rootSubgroup
  rw [Subgroup.closure_le]
  rintro _ ⟨c, rfl⟩
  rw [SetLike.mem_coe, Subgroup.mem_centralizer_iff]
  intro h hh
  rw [Set.mem_singleton_iff] at hh
  subst hh
  have h1 := rootDiagUnit_conj_pinnedX b hr c
  rw [hc, Units.val_one, one_mul] at h1
  exact (mul_inv_eq_iff_eq_mul.1 h1)

end Centralizer

section Rank

variable {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] {p₀ : ℕ}

theorem iform_eq_zero_of_mem_span
    {Ψ Ψ' : Set (Fin τ.rank → ℤ)}
    (h : ∀ x ∈ Ψ, ∀ y ∈ Ψ', iform x y = 0) {u v : Fin τ.rank → ℤ}
    (hu : u ∈ Submodule.span ℤ Ψ) (hv : v ∈ Submodule.span ℤ Ψ') : iform u v = 0 := by
  induction hu using Submodule.span_induction with
  | mem x hx =>
    induction hv using Submodule.span_induction with
    | mem y hy => exact h x hx y hy
    | zero => simp [iform]
    | add y z _ _ hy hz => rw [iform_add_right, hy, hz, add_zero]
    | smul c y _ hy => rw [iform_smul_right, hy, mul_zero]
  | zero => simp [iform]
  | add x y _ _ hx hy => rw [iform_add_left, hx, hy, add_zero]
  | smul c x _ hx => rw [iform_smul_left, hx, mul_zero]

theorem finrank_add_finrank_le_of_orth
    {Λ Λ' : Submodule ℤ (Fin τ.rank → ℤ)}
    (h : ∀ u ∈ Λ, ∀ v ∈ Λ', iform u v = 0) :
    Module.finrank ℤ Λ + Module.finrank ℤ Λ' ≤ τ.rank := by
  have hdisj : Λ ⊓ Λ' = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    obtain ⟨hx1, hx2⟩ := hx
    have h0 : iform x x = 0 := h x hx1 x hx2
    by_contra hne
    exact (iform_self_pos (show x ≠ 0 from hne)).ne' h0
  have hr := Submodule.rank_sup_add_rank_inf_eq Λ Λ'
  rw [hdisj, rank_bot, add_zero] at hr
  have hle : Module.rank ℤ ↥(Λ ⊔ Λ') ≤ τ.rank := by
    calc Module.rank ℤ ↥(Λ ⊔ Λ') ≤ Module.rank ℤ (Fin τ.rank → ℤ) := Submodule.rank_le _
      _ = τ.rank := by simp
  have h1 : (Module.finrank ℤ Λ : Cardinal) = Module.rank ℤ Λ := Module.finrank_eq_rank ℤ Λ
  have h2 : (Module.finrank ℤ Λ' : Cardinal) = Module.rank ℤ Λ' := Module.finrank_eq_rank ℤ Λ'
  have h3 : ((Module.finrank ℤ Λ + Module.finrank ℤ Λ' : ℕ) : Cardinal) ≤ τ.rank := by
    rw [Nat.cast_add, h1, h2, ← hr]
    exact hle
  exact_mod_cast h3

theorem rho_add'
    (S : LangSetup τ L p₀) (x y : Fin τ.rank → ℤ) :
    S.ρ (x + y) = S.ρ x + S.ρ y := by
  have h : ∀ z, iform (S.ρ (x + y) - S.ρ x - S.ρ y) (S.ρ z) = 0 := by
    intro z
    rw [iform_sub_left, iform_sub_left, S.frob.iform_eq, S.frob.iform_eq, S.frob.iform_eq,
      iform_add_left]
    ring
  have h0 := h (S.ρ.symm (S.ρ (x + y) - S.ρ x - S.ρ y))
  rw [Equiv.apply_symm_apply] at h0
  have h1 : S.ρ (x + y) - S.ρ x - S.ρ y = 0 := by
    by_contra hne
    exact (iform_self_pos hne).ne' h0
  rw [sub_sub, sub_eq_zero] at h1
  exact h1

@[expose] noncomputable def rhoLinMap
    (S : LangSetup τ L p₀) :
    (Fin τ.rank → ℤ) →ₗ[ℤ] (Fin τ.rank → ℤ) :=
  (AddMonoidHom.mk' (S.ρ : (Fin τ.rank → ℤ) → (Fin τ.rank → ℤ)) (rho_add' S)).toIntLinearMap

theorem two_mul_finrank_le_of_orbit
    (S : LangSetup τ L p₀) {ι : Type}
    (a : ι → Fin τ.rank → Lˣ) (ha : ∀ u, rootDiagUnit τ (a u) ∈ S.D.torus)
    (i : KernelComponent (famCharHom a))
    (h2 : 2 ≤ componentOrbitLength S.ρ (componentRoots (famCharHom a) i)) :
    2 * Module.finrank ℤ (Submodule.span ℤ (componentRoots (famCharHom a) i)) ≤ τ.rank := by
  obtain ⟨j, hj⟩ := exists_image_component_of_stable (famCharHom a)
    (fun γ hγ => rho_mem_kernelRoots_famChar S a ha hγ) S.frob.iform_eq i
  have hij : i ≠ j := by
    rintro rfl
    exact image_ne_of_two_le_componentOrbitLength h2 hj
  have hΛ' : Submodule.span ℤ (componentRoots (famCharHom a) j) =
      Submodule.map (rhoLinMap S) (Submodule.span ℤ (componentRoots (famCharHom a) i)) := by
    rw [← hj, Submodule.map_span]
    rfl
  have hfin : Module.finrank ℤ (Submodule.span ℤ (componentRoots (famCharHom a) j)) =
      Module.finrank ℤ (Submodule.span ℤ (componentRoots (famCharHom a) i)) := by
    rw [hΛ']
    exact (LinearEquiv.finrank_eq (Submodule.equivMapOfInjective _
      (fun x y hxy => S.ρ.injective hxy) _)).symm
  have horth := finrank_add_finrank_le_of_orth
    (Λ := Submodule.span ℤ (componentRoots (famCharHom a) i))
    (Λ' := Submodule.span ℤ (componentRoots (famCharHom a) j))
    (fun u hu v hv => iform_eq_zero_of_mem_span
      (fun x hx y hy => iform_eq_zero_of_mem_componentRoots' hij hx hy) hu hv)
  omega

end Rank

section Assembly

variable {τ : Tag} {L : Type} [Field L] {p₀ : ℕ}

theorem rootDiagUnit_pow_tuple (b : Fin τ.rank → Lˣ) (n : ℕ) :
    rootDiagUnit τ b ^ n = rootDiagUnit τ (b ^ n) := by
  induction n with
  | zero => rw [pow_zero, pow_zero, rootDiagUnit_one]
  | succ n ih => rw [pow_succ, pow_succ, ih, rootDiagUnit_mul]

theorem exists_param_of_torus
    {p : ℕ} {u : ModGL τ L} (hu : u ∈ torusGroup τ L) (hup : u ^ p = 1) :
    ∃ c : Fin τ.rank → Lˣ, u = rootDiagUnit τ c ∧ ∀ j, c j ^ p = 1 := by
  obtain ⟨c, hc⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup hu
  refine ⟨c, hc, fun j => ?_⟩
  have h1 : rootDiagUnit τ (c ^ p) = rootDiagUnit τ 1 := by
    rw [← rootDiagUnit_pow_tuple, ← hc, hup, rootDiagUnit_one]
  have h2 := congrFun (rootDiagUnit_injective h1) j
  simpa using h2

theorem card_le_of_famChar
    [IsAlgClosed L] (S : LangSetup τ L p₀) {p : ℕ} [NeZero p]
    (B₁ D₁ J₁ : Subgroup (ModGL τ L)) [Finite B₁] (hB : B₁ ≤ S.D.torus)
    (hexp : ∀ b ∈ B₁, b ^ p = 1) (hDB : D₁ ≤ B₁)
    (a : D₁ → Fin τ.rank → Lˣ)
    (i : KernelComponent (famCharHom a)) (hJ : J₁ ≤ rootSpan τ L (famOrbit S.ρ a i))
    (hC : B₁ ⊓ Subgroup.centralizer (J₁ : Set (ModGL τ L)) ≤ D₁) :
    Nat.card B₁ ≤ Nat.card D₁ *
      p ^ Module.finrank ℤ (Submodule.span ℤ (componentRoots (famCharHom a) i)) := by
  have hpar : ∀ b ∈ B₁, ∃ c : Fin τ.rank → Lˣ, b = rootDiagUnit τ c ∧ ∀ j, c j ^ p = 1 := by
    intro b hb
    obtain ⟨c, hc⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup (hB hb).1
    refine ⟨c, hc, fun j => ?_⟩
    have h1 : rootDiagUnit τ (c ^ p) = rootDiagUnit τ 1 := by
      rw [← rootDiagUnit_pow_tuple, ← hc, hexp b hb, rootDiagUnit_one]
    have h2 := congrFun (rootDiagUnit_injective h1) j
    simpa using h2
  refine card_le_mul_pow_of_torus B₁ D₁ hpar _ ?_ hDB
  intro b hb c hbc hc
  have hT : rootDiagUnit τ c ∈ S.D.torus := hbc ▸ hB hb
  have hΨ : ∀ γ ∈ componentRoots (famCharHom a) i, rootChar c γ = 1 := fun γ hγ =>
    hc γ (Submodule.subset_span hγ)
  have hle := rootSpan_rationalRoots_le_centralizer S a i hT hΨ
  refine hC (Subgroup.mem_inf.2 ⟨hb, ?_⟩)
  rw [Subgroup.mem_centralizer_iff]
  intro j hj
  have hj' := Subgroup.mem_centralizer_iff.1 (hle (hJ hj)) (rootDiagUnit τ c) rfl
  rw [hbc]
  exact hj'.symm

end Assembly

end CFSG.StandardType.TableCRes
