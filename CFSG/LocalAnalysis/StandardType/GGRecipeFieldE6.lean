module

public import CFSG.LocalAnalysis.StandardType.GGRecipeFieldExc
public import CFSG.LocalAnalysis.StandardType.GGInndiagNormalOtherE6
public import CFSG.LieType.Chevalley.OrdinaryEFieldGraphQuotient
public import CFSG.LieType.Chevalley.E6CanonicalFieldGraphFixed
public import CFSG.LocalAnalysis.StandardType.GGRecipeFieldCyclic

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley InndiagE6

namespace RecipeFieldE6

section Core

variable {M : Type} [Group M]

@[expose] def CommNF {ι : Type*} (H : Subgroup M) (D : ι → M) : Prop :=
  ∀ α β : MulAut H, ∃ g ∈ H, ∃ a : ι, (∀ h ∈ H, D a * h * (D a)⁻¹ ∈ H) ∧
    (∀ h ∈ H, (D a)⁻¹ * h * D a ∈ H) ∧
    ∀ h : H, ((α * β * α⁻¹ * β⁻¹) h : M) = g * D a * h * (g * D a)⁻¹

end Core

theorem commutator_mem_chevID_of_commNF {r : ℕ} {A : Matrix (Fin r) (Fin r) ℤ} {K : Type}
    [Field K] {H : Subgroup (LargeEvenChevGL A K)} (hZ : Subgroup.center H = ⊥)
    (hNF : CommNF H (TableB.diagHom A K)) (α β : MulAut (LargeEvenCenterQuot H)) :
    α * β * α⁻¹ * β⁻¹ ∈ LargeEvenChevIDImage A K H := by
  set e := centerQuotEquivOfBot hZ with he
  obtain ⟨g, hg, a, h1, h2, hform⟩ := hNF (MulAut.congr e α) (MulAut.congr e β)
  set g₀ : H := ⟨g, hg⟩
  set ψ : MulAut (LargeEvenCenterQuot H) :=
    (MulAut.conj (LargeEvenCenterMk H g₀))⁻¹ * (α * β * α⁻¹ * β⁻¹) with hψ
  have hψc : IsConjOn H ψ (TableB.diagHom A K a) := by
    refine ⟨h1, fun h hh => ?_⟩
    have hval := hform h
    have hcomm := congr_centerQuotEquivOfBot_mk hZ (α * β * α⁻¹ * β⁻¹) h
    have hmap : MulAut.congr e (α * β * α⁻¹ * β⁻¹) =
        MulAut.congr e α * MulAut.congr e β * (MulAut.congr e α)⁻¹ * (MulAut.congr e β)⁻¹ := by
      simp only [map_mul, map_inv]
    rw [hψ, MulAut.mul_apply, hcomm, hmap]
    rw [MulAut.inv_apply, MulEquiv.symm_apply_eq, conj_mk_centerQuot]
    congr 1
    apply Subtype.ext
    rw [hval]
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, g₀]
    group
  have hψmem : ψ ∈ LargeEvenChevDiagImage A K H := mem_chevDiagImage_of_isConjOn hψc h2
  have e1 : α * β * α⁻¹ * β⁻¹ = MulAut.conj (LargeEvenCenterMk H g₀) * ψ := by
    rw [hψ, mul_inv_cancel_left]
  rw [e1]
  exact Subgroup.mul_mem _ (Subgroup.subset_closure (Or.inl ⟨_, rfl⟩))
    (Subgroup.subset_closure (Or.inr hψmem))

section ConjAlg

variable {M : Type} [Group M] {H : Subgroup M}

theorem isConjOn_mul {φ ψ : MulAut (LargeEvenCenterQuot H)} {x y : M} (hφ : IsConjOn H φ x)
    (hψ : IsConjOn H ψ y) : IsConjOn H (φ * ψ) (x * y) := by
  refine ⟨fun h hh => ?_, fun h hh => ?_⟩
  · have e : x * y * h * (x * y)⁻¹ = x * (y * h * y⁻¹) * x⁻¹ := by group
    rw [e]
    exact hφ.1 _ (hψ.1 h hh)
  · have hy := hψ.1 h h.2
    rw [MulAut.mul_apply, hψ.2 h hy, hφ.2 ⟨_, hy⟩ (hφ.1 _ hy)]
    congr 1
    apply Subtype.ext
    simp only
    group

theorem isConjOn_inv {φ : MulAut (LargeEvenCenterQuot H)} {x : M} (hφ : IsConjOn H φ x)
    (hx : ∀ h ∈ H, x⁻¹ * h * x ∈ H) : IsConjOn H φ⁻¹ x⁻¹ := by
  refine ⟨fun h hh => by simpa using hx h hh, fun h hh => ?_⟩
  have hh' : x⁻¹ * h * x ∈ H := hx h h.2
  have e : (⟨x⁻¹ * h * x⁻¹⁻¹, hh⟩ : H) = ⟨x⁻¹ * h * x, hh'⟩ := Subtype.ext (by simp)
  rw [MulAut.inv_apply, MulEquiv.symm_apply_eq, e, hφ.2 ⟨_, hh'⟩ (hφ.1 _ hh')]
  congr 1
  apply Subtype.ext
  simp only
  group

theorem isConjOn_of_eq {φ : MulAut (LargeEvenCenterQuot H)} {x y : M} (hφ : IsConjOn H φ x)
    (e : x = y) : IsConjOn H φ y :=
  e ▸ hφ

theorem isConjOn_conj (g : H) : IsConjOn H (MulAut.conj (LargeEvenCenterMk H g)) g := by
  refine ⟨fun h hh => H.mul_mem (H.mul_mem g.2 hh) (H.inv_mem g.2), fun h hh => ?_⟩
  rw [conj_mk_centerQuot]
  rfl

end ConjAlg

theorem exists_isConjOn_of_mem_chevID {r : ℕ} {A : Matrix (Fin r) (Fin r) ℤ} {K : Type}
    [Field K] {H : Subgroup (LargeEvenChevGL A K)} {φ : MulAut (LargeEvenCenterQuot H)}
    (hφ : φ ∈ LargeEvenChevIDImage A K H) :
    ∃ g ∈ H, ∃ a : Fin r → Kˣ, (∀ h ∈ H, TableB.diagHom A K a * h * (TableB.diagHom A K a)⁻¹ ∈ H) ∧
      (∀ h ∈ H, (TableB.diagHom A K a)⁻¹ * h * TableB.diagHom A K a ∈ H) ∧
      IsConjOn H φ (g * TableB.diagHom A K a) := by
  have hφ' : φ ∈ Subgroup.closure
      (LargeEvenInnSet (LargeEvenCenterQuot H) ∪ LargeEvenChevDiagImage A K H) := hφ
  clear hφ
  set D := TableB.diagHom A K with hD
  induction hφ' using Subgroup.closure_induction with
  | mem x hx =>
    rcases hx with ⟨y, rfl⟩ | hx
    · obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective y
      refine ⟨g, g.2, 1, by simp, by simp, isConjOn_of_eq (isConjOn_conj g) (by simp)⟩
    · obtain ⟨a, ha, hinv⟩ := exists_isConjOn_of_mem_chevDiagImage hx
      exact ⟨1, H.one_mem, a, ha.1, hinv, isConjOn_of_eq ha (by rw [one_mul])⟩
  | one =>
    refine ⟨1, H.one_mem, 1, by simp, by simp, ⟨fun h hh => by simpa using hh, fun h hh => ?_⟩⟩
    rw [MulAut.one_apply]
    congr 1
    apply Subtype.ext
    simp
  | mul x y _ _ hx hy =>
    obtain ⟨g₁, hg₁, a, ha1, ha2, hx'⟩ := hx
    obtain ⟨g₂, hg₂, b, hb1, hb2, hy'⟩ := hy
    refine ⟨g₁ * (D a * g₂ * (D a)⁻¹), H.mul_mem hg₁ (ha1 _ hg₂), a * b, fun h hh => ?_,
      fun h hh => ?_, isConjOn_of_eq (isConjOn_mul hx' hy') ?_⟩
    · have e : D (a * b) * h * (D (a * b))⁻¹ = D a * (D b * h * (D b)⁻¹) * (D a)⁻¹ := by
        rw [map_mul]
        group
      rw [e]
      exact ha1 _ (hb1 h hh)
    · have e : (D (a * b))⁻¹ * h * D (a * b) = (D b)⁻¹ * ((D a)⁻¹ * h * D a) * D b := by
        rw [map_mul]
        group
      rw [e]
      exact hb2 _ (ha2 h hh)
    · rw [map_mul]
      group
  | inv x _ hx =>
    obtain ⟨g, hg, a, ha1, ha2, hx'⟩ := hx
    have hxinv : ∀ h ∈ H, (g * D a)⁻¹ * h * (g * D a) ∈ H := by
      intro h hh
      have e : (g * D a)⁻¹ * h * (g * D a) = (D a)⁻¹ * (g⁻¹ * h * g) * D a := by group
      rw [e]
      exact ha2 _ (H.mul_mem (H.mul_mem (H.inv_mem hg) hh) hg)
    refine ⟨(D a)⁻¹ * g⁻¹ * D a, ha2 _ (H.inv_mem hg), a⁻¹, fun h hh => ?_, fun h hh => ?_,
      isConjOn_of_eq (isConjOn_inv hx' hxinv) ?_⟩
    · rw [map_inv, inv_inv]
      exact ha2 h hh
    · rw [map_inv, inv_inv]
      exact ha1 h hh
    · rw [map_inv]
      group

@[expose] def CommNFOn (K : Type) [Field K] (τ : Tag) (S : (Fin τ.rank → ℤ) → Prop) : Prop :=
  Subgroup.center (MarkChev.chevH τ.cartan S K false) = ⊥ ∧
    CommNF (MarkChev.chevH τ.cartan S K false) (markDiagUnit S K)

theorem CommNFOn.of_eq {K : Type} [Field K] {τ : Tag} {S S' : (Fin τ.rank → ℤ) → Prop}
    (hS : S = S') (h : CommNFOn K τ S) : CommNFOn K τ S' :=
  hS ▸ h

@[expose] def E6FieldOn (K : Type) [Field K] (S : (Fin TwistTag.E6.tag.rank → ℤ) → Prop) : Prop :=
  Subgroup.center (MarkChev.chevH TwistTag.E6.tag.cartan S K false) = ⊥ ∧
    (∀ (σ : K ≃+* K) (h : MarkChev.chevH TwistTag.E6.tag.cartan S K false),
      ∃ h' : MarkChev.chevH TwistTag.E6.tag.cartan S K false,
        ((h' : MarkChev.GLS S K) : Module.End K (MarkChev.Space S K)) =
          MarkChev.entrywise S K σ (map_zero σ) ((h : MarkChev.GLS S K) : Module.End K _)) ∧
    ∀ (σ : K ≃+* K) (g : MarkChev.GLS S K) (a : Fin TwistTag.E6.tag.rank → Kˣ),
      g ∈ MarkChev.chevH TwistTag.E6.tag.cartan S K false →
      (∀ h : MarkChev.chevH TwistTag.E6.tag.cartan S K false,
        MarkChev.entrywise S K σ (map_zero σ) ((h : MarkChev.GLS S K) : Module.End K _) =
          ((g * markDiagUnit S K a * h * (g * markDiagUnit S K a)⁻¹ : MarkChev.GLS S K) :
            Module.End K _)) → σ = 1

theorem E6FieldOn.of_eq {K : Type} [Field K] {S S' : (Fin TwistTag.E6.tag.rank → ℤ) → Prop}
    (hS : S = S') (h : E6FieldOn K S) : E6FieldOn K S' :=
  hS ▸ h


theorem commNF_adjointGroup_E6 (K : Type) [Field K] [Finite K] :
    CommNF (adjointGroup TwistTag.E6.tag K) (rootDiagUnit TwistTag.E6.tag) := by
  obtain ⟨Θ, -, -, hker, -⟩ :=
    ordinary_E_field_graph_quotient_and_involutions TwistTag.E6.tag (Or.inl rfl) K
  intro α β
  have hΘ : Θ (α * β * α⁻¹ * β⁻¹) = 1 := by
    rw [map_mul, map_mul, map_mul, map_inv, map_inv]
    have hc : Θ α * Θ β = Θ β * Θ α := by
      refine Prod.ext ?_ ?_
      · exact ringEquiv_mul_comm_of_finite (Θ α).1 (Θ β).1
      · exact mul_comm (Θ α).2 (Θ β).2
    rw [hc]
    group
  obtain ⟨g, a, hg⟩ := (hker _).mp hΘ
  refine ⟨g, g.2, a, fun h hh => conj_rootDiagUnit_mem_adjointGroup a hh, fun h hh => ?_,
    fun h => ?_⟩
  · have := conj_rootDiagUnit_mem_adjointGroup (K := K) (a⁻¹) hh
    rwa [rootDiagUnit_inv a⁻¹, inv_inv, ← rootDiagUnit_inv] at this
  · rw [hg h]
    group

theorem commNFOn_isRoot_E6 (K : Type) [Field K] [Finite K] :
    CommNFOn K TwistTag.E6.tag (IsRoot TwistTag.E6.tag) := by
  unfold CommNFOn
  rw [chevH_false_eq_adjointGroup K TwistTag.E6.tag, markDiagUnit_isRoot]
  exact ⟨center_adjointGroup_eq_bot, commNF_adjointGroup_E6 K⟩

theorem ggRawFieldCentral_E6 (K : Type) [Field K] [Finite K] :
    GGRawFieldCentral (LargeEvenCenterQuot (LargeEvenChevH TwistTag.E6.tag.cartan K false))
      (LargeEvenChevIDImage TwistTag.E6.tag.cartan K
        (LargeEvenChevH TwistTag.E6.tag.cartan K false))
      (LargeEvenChevFieldImage TwistTag.E6.tag.cartan K
        (LargeEvenChevH TwistTag.E6.tag.cartan K false)) := by
  obtain ⟨hZ, hNF⟩ := (commNFOn_isRoot_E6 K).of_eq (largeEvenIsRoot_eq_isRoot TwistTag.E6.tag).symm
  refine ggRawFieldCentral_of_commutator_mem fun α β => commutator_mem_chevID_of_commNF ?_ ?_ α β
  · rw [largeEvenChevH_eq]
    exact hZ
  · rw [largeEvenChevH_eq, diagHom_eq_markDiagUnit]
    exact hNF

theorem e6FieldOn_isRoot (K : Type) [Field K] [Finite K] :
    E6FieldOn K (IsRoot TwistTag.E6.tag) := by
  obtain ⟨Θ, -, hΘ, hker, -⟩ :=
    ordinary_E_field_graph_quotient_and_involutions TwistTag.E6.tag (Or.inl rfl) K
  suffices key : ∀ H : Subgroup (MarkChev.GLS (IsRoot TwistTag.E6.tag) K),
      H = adjointGroup TwistTag.E6.tag K →
      Subgroup.center H = ⊥ ∧
      (∀ (σ : K ≃+* K) (h : H), ∃ h' : H,
        ((h' : MarkChev.GLS (IsRoot TwistTag.E6.tag) K) :
          Module.End K (MarkChev.Space (IsRoot TwistTag.E6.tag) K)) =
          MarkChev.entrywise (IsRoot TwistTag.E6.tag) K σ (map_zero σ)
            ((h : MarkChev.GLS (IsRoot TwistTag.E6.tag) K) :
              Module.End K (MarkChev.Space (IsRoot TwistTag.E6.tag) K))) ∧
      ∀ (σ : K ≃+* K) (g : MarkChev.GLS (IsRoot TwistTag.E6.tag) K)
        (a : Fin TwistTag.E6.tag.rank → Kˣ), g ∈ H →
        (∀ h : H, MarkChev.entrywise (IsRoot TwistTag.E6.tag) K σ (map_zero σ)
            ((h : MarkChev.GLS (IsRoot TwistTag.E6.tag) K) :
              Module.End K (MarkChev.Space (IsRoot TwistTag.E6.tag) K)) =
          ((g * rootDiagUnit TwistTag.E6.tag a * (h : MarkChev.GLS (IsRoot TwistTag.E6.tag) K) *
            (g * rootDiagUnit TwistTag.E6.tag a)⁻¹ : MarkChev.GLS (IsRoot TwistTag.E6.tag) K) :
              Module.End K (MarkChev.Space (IsRoot TwistTag.E6.tag) K))) → σ = 1 by
    have h := key _ (chevH_false_eq_adjointGroup K TwistTag.E6.tag)
    unfold E6FieldOn
    rw [markDiagUnit_isRoot]
    exact h
  intro H hH
  subst hH
  refine ⟨center_adjointGroup_eq_bot, fun σ h => ⟨entrywiseAdjointAut TwistTag.E6.tag σ h, ?_⟩,
    fun σ g a hg hrel => ?_⟩
  · show ((entrywiseAdjointAut TwistTag.E6.tag σ h : ModGL TwistTag.E6.tag K) :
      Module.End K (RootModule TwistTag.E6.tag K)) = _
    rw [coe_entrywiseAdjointAut]
    rfl
  · set α := entrywiseAdjointAut TwistTag.E6.tag σ with hα
    have hα1 : Θ α = 1 := by
      refine (hker α).mpr ⟨⟨g, hg⟩, a, fun h => ?_⟩
      apply Units.ext
      have e := hrel h
      rw [hα, coe_entrywiseAdjointAut]
      change entrywise (σ : K →+* K) _ = _
      refine e.trans ?_
      simp only [Units.val_mul, _root_.mul_inv_rev]
      rfl
    have hασ := hΘ α 1 1 σ ⟨0, exactE_pos _⟩ fun h => by
      rw [hα, coe_entrywiseAdjointAut, rootDiagUnit_one]
      change _ = _ * _ * exactQ TwistTag.E6.tag K 0 * _ * (exactQ TwistTag.E6.tag K 0)⁻¹ * _ * _
      rw [exactQ_zero]
      simp
    rw [hα1] at hασ
    exact (congrArg Prod.fst hασ).symm

theorem ggRawInnField_E6 (K : Type) [Field K] [Finite K] {p : ℕ} (hp : p ≠ 1) :
    GGRawInnField p (LargeEvenCenterQuot (LargeEvenChevH TwistTag.E6.tag.cartan K false))
      (LargeEvenChevIDImage TwistTag.E6.tag.cartan K
        (LargeEvenChevH TwistTag.E6.tag.cartan K false))
      (LargeEvenChevFieldImage TwistTag.E6.tag.cartan K
        (LargeEvenChevH TwistTag.E6.tag.cartan K false)) := by
  obtain ⟨hZ, hstab, hkey⟩ :=
    (e6FieldOn_isRoot K).of_eq (largeEvenIsRoot_eq_isRoot TwistTag.E6.tag).symm
  rw [← diagHom_eq_markDiagUnit] at hkey
  suffices key : ∀ H : Subgroup (LargeEvenChevGL TwistTag.E6.tag.cartan K),
      H = MarkChev.chevH TwistTag.E6.tag.cartan (LargeEvenIsRoot TwistTag.E6.tag.cartan) K false →
      GGRawInnField p (LargeEvenCenterQuot H) (LargeEvenChevIDImage TwistTag.E6.tag.cartan K H)
        (LargeEvenChevFieldImage TwistTag.E6.tag.cartan K H) from
    key _ (largeEvenChevH_eq _ K false)
  intro H hH
  subst hH
  refine ggRawInnField_of_subgroup hp
    (Subgroup.closure (LargeEvenInnSet _ ∪ LargeEvenChevDiagImage TwistTag.E6.tag.cartan K _)) rfl
    (conj_mem_chevIDImage _) fun φ hφ hφI => ?_
  obtain ⟨σ, hσ⟩ := hφ
  obtain ⟨g, hg, a, ha1, -, hconj⟩ := exists_isConjOn_of_mem_chevID hφI
  have hmk : Function.Injective (LargeEvenCenterMk
      (MarkChev.chevH TwistTag.E6.tag.cartan (LargeEvenIsRoot TwistTag.E6.tag.cartan) K false)) := by
    rw [← MonoidHom.ker_eq_bot_iff, LargeEvenCenterMk, QuotientGroup.ker_mk', hZ]
  have hrel : ∀ h : MarkChev.chevH TwistTag.E6.tag.cartan
      (LargeEvenIsRoot TwistTag.E6.tag.cartan) K false,
      MarkChev.entrywise (LargeEvenIsRoot TwistTag.E6.tag.cartan) K σ (map_zero σ)
          ((h : LargeEvenChevGL TwistTag.E6.tag.cartan K) :
            Module.End K (LargeEvenChevModule TwistTag.E6.tag.cartan K)) =
        ((g * TableB.diagHom TwistTag.E6.tag.cartan K a * (h : LargeEvenChevGL TwistTag.E6.tag.cartan K) *
          (g * TableB.diagHom TwistTag.E6.tag.cartan K a)⁻¹ :
          LargeEvenChevGL TwistTag.E6.tag.cartan K) :
            Module.End K (LargeEvenChevModule TwistTag.E6.tag.cartan K)) := by
    intro h
    obtain ⟨h', hh'⟩ := hstab σ h
    have e1 := hσ h h' hh'
    have e2 := hconj.2 h (hconj.1 h h.2)
    have e3 := hmk (e1.symm.trans e2)
    rw [← hh', e3]
  have hσ1 := hkey σ g a hg hrel
  subst hσ1
  ext z
  obtain ⟨h, rfl⟩ := QuotientGroup.mk_surjective z
  obtain ⟨h', hh'⟩ := hstab 1 h
  have e1 := hσ h h' hh'
  rw [MulAut.one_apply]
  change φ (LargeEvenCenterMk _ h) = LargeEvenCenterMk _ h
  rw [e1]
  congr 1
  apply Subtype.ext
  apply Units.ext
  rw [hh']
  exact largeEvenEntrywise_of_forall_eq _ (fun x => rfl) _

end RecipeFieldE6

open RecipeFieldE6

@[expose] def GGRecipeE6Label (lab : LargeEvenLabel) : Prop :=
  lab.tag = .E6

theorem ggRawFieldCentralOn_E6 :
    GGRawFieldCentralOn GGRecipeE6Label := by
  intro lab _ hS Q hQ
  obtain ⟨t, l, n⟩ := lab
  dsimp only [GGRecipeE6Label] at hS
  subst hS
  exact recipeChevalley_and (fun K _ _ _ => ggRawFieldCentral_E6 K) hQ

theorem ggRawInnFieldOn_E6 :
    GGRawInnFieldOn GGRecipeE6Label := by
  intro p hp _ lab _ hS Q hQ
  obtain ⟨t, l, n⟩ := lab
  dsimp only [GGRecipeE6Label] at hS
  subst hS
  exact recipeChevalley_and (fun K _ _ _ => ggRawInnField_E6 K hp.one_lt.ne') hQ

namespace RecipeFieldE6

@[expose] def TwistedCommNFOn (K : Type) [Field K] (τ : Tag) (ρ : Equiv.Perm (Fin τ.rank)) (n : ℕ)
    (S : (Fin τ.rank → ℤ) → Prop) : Prop :=
  Subgroup.center (MarkChev.twistedH τ.cartan S K ρ n) = ⊥ ∧
    CommNF (MarkChev.twistedH τ.cartan S K ρ n) (markDiagUnit S K)

theorem TwistedCommNFOn.of_eq {K : Type} [Field K] {τ : Tag} {ρ : Equiv.Perm (Fin τ.rank)}
    {n : ℕ} {S S' : (Fin τ.rank → ℤ) → Prop} (hS : S = S') (h : TwistedCommNFOn K τ ρ n S) :
    TwistedCommNFOn K τ ρ n S' :=
  hS ▸ h


theorem commNF_twistedE6 {n : ℕ} (hn : 1 ≤ n) (K : Type) [Field K] [Finite K]
    (hK : Nat.card K = (2 ^ n) ^ 2) (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ 2 ^ n) :
    CommNF (twistedE6RootGroup K σ) (rootDiagUnit TwistTag.E6.tag) := by
  obtain ⟨-, -, -, -, -, hcompat, hfield, hnf, ⟨Θ, hΘ, -, -⟩, -⟩ :=
    twisted_E6_all_characteristic_exact_automorphism_normal_form Nat.prime_two hn K hK σ hσ
  intro α β
  obtain ⟨g, u, δ, hγ⟩ := hnf (α * β * α⁻¹ * β⁻¹)
  have hδ : δ = 1 := by
    rw [← hΘ _ g u δ hγ, map_mul, map_mul, map_mul, map_inv, map_inv,
      ringEquiv_mul_comm_of_finite (Θ α) (Θ β)]
    group
  subst hδ
  set c := compatDiag TwistTag.E6 σ.toRingHom u with hc
  have hf1 : fieldActor σ (1 : K ≃+* K) = 1 := MulEquiv.ext fun x => Subtype.ext (by
    rw [hfield, MulAut.one_apply]
    apply Units.ext
    change entrywise ((1 : K ≃+* K) : K →+* K) _ = _
    apply Finsupp.lhom_ext'
    intro b
    ext l
    simp [entrywise])
  rw [hf1, mul_one] at hγ
  have hcomp : ∀ y : twistedE6RootGroup K σ,
      (((MulAut.conj g * compatDiagAutHom TwistTag.E6 K σ.toRingHom u :
        MulAut (twistedE6RootGroup K σ)) y : twistedE6RootGroup K σ) : ModGL TwistTag.E6.tag K) =
      (g : ModGL TwistTag.E6.tag K) * rootDiagUnit TwistTag.E6.tag c * y *
        ((g : ModGL TwistTag.E6.tag K) * rootDiagUnit TwistTag.E6.tag c)⁻¹ := by
    intro y
    rw [MulAut.mul_apply, MulAut.conj_apply, Subgroup.coe_mul, Subgroup.coe_mul,
      Subgroup.coe_inv, hcompat, ← hc]
    group
  refine ⟨g, g.2, c, fun h hh => ?_, fun h hh => ?_, fun h => ?_⟩
  · have hmem := (compatDiagAutHom TwistTag.E6 K σ.toRingHom u ⟨h, hh⟩).2
    rwa [hcompat, ← hc] at hmem
  · set y := (compatDiagAutHom TwistTag.E6 K σ.toRingHom u).symm ⟨h, hh⟩ with hy
    have hyy : compatDiagAutHom TwistTag.E6 K σ.toRingHom u y = ⟨h, hh⟩ :=
      MulEquiv.apply_symm_apply _ _
    have e := congrArg (fun z : twistedE6RootGroup K σ => (z : ModGL TwistTag.E6.tag K)) hyy
    simp only [hcompat] at e
    rw [← hc] at e
    have e' : (rootDiagUnit TwistTag.E6.tag c)⁻¹ * h * rootDiagUnit TwistTag.E6.tag c =
        (y : ModGL TwistTag.E6.tag K) := by
      rw [← e]
      group
    rw [e']
    exact y.2
  · rw [hγ, hcomp]

theorem twistedCommNFOn_isRoot_E6 {n : ℕ} (hn : 1 ≤ n) (K : Type) [Field K] [Finite K]
    (hK : Nat.card K = (2 ^ n) ^ 2) :
    TwistedCommNFOn K TwistTag.E6.tag TwistTag.E6.perm n (IsRoot TwistTag.E6.tag) := by
  have : CharP K 2 := charP_two_of_card (m := n * 2) (by rw [hK, pow_mul])
  set σ := iterateFrobeniusEquiv K 2 n with hσdef
  have hσ : ∀ c, σ c = c ^ 2 ^ n := fun c => by
    rw [hσdef, iterateFrobeniusEquiv_apply, iterateFrobenius_def]
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, hZ, -, -⟩ :=
    twisted_E6_all_characteristic_exact_automorphism_normal_form Nat.prime_two hn K hK σ hσ
  have hC : MarkChev.twistedH TwistTag.E6.tag.cartan (IsRoot TwistTag.E6.tag) K TwistTag.E6.perm
      n = twistedE6RootGroup K σ := by
    rw [twistedH_eq_commutator K .E6 n σ.toRingHom hσ]
    exact (finite_fixed_root_group_perfect TwistTag.E6 Nat.prime_two hn K hK σ.toRingHom hσ).2.2.1
  unfold TwistedCommNFOn
  rw [hC, markDiagUnit_isRoot]
  exact ⟨hZ, commNF_twistedE6 hn K hK σ hσ⟩

theorem ggRawFieldCentral_twE6 {n : ℕ} (hn : 1 ≤ n) (K : Type) [Field K] [Finite K]
    (hK : Nat.card K = (2 ^ n) ^ 2) :
    GGRawFieldCentral
      (LargeEvenCenterQuot (LargeEvenTwistedH TwistTag.E6.tag.cartan K TwistTag.E6.perm n))
      (LargeEvenChevIDImage TwistTag.E6.tag.cartan K
        (LargeEvenTwistedH TwistTag.E6.tag.cartan K TwistTag.E6.perm n))
      (LargeEvenChevFieldImage TwistTag.E6.tag.cartan K
        (LargeEvenTwistedH TwistTag.E6.tag.cartan K TwistTag.E6.perm n)) := by
  obtain ⟨hZ, hNF⟩ :=
    (twistedCommNFOn_isRoot_E6 hn K hK).of_eq (largeEvenIsRoot_eq_isRoot TwistTag.E6.tag).symm
  refine ggRawFieldCentral_of_commutator_mem fun α β => commutator_mem_chevID_of_commNF ?_ ?_ α β
  · rw [largeEvenTwistedH_eq]
    exact hZ
  · rw [largeEvenTwistedH_eq, diagHom_eq_markDiagUnit]
    exact hNF

end RecipeFieldE6

open RecipeFieldE6

@[expose] def GGRecipeTwE6Label (lab : LargeEvenLabel) : Prop :=
  lab.tag = .twE6

theorem ggRawFieldCentralOn_twE6 :
    GGRawFieldCentralOn GGRecipeTwE6Label := by
  intro lab hlab hS Q hQ
  obtain ⟨t, l, n⟩ := lab
  obtain ⟨hn, -⟩ := hlab
  dsimp only [GGRecipeTwE6Label] at hS
  subst hS
  exact recipeTwisted_and (fun K _ _ hK => ggRawFieldCentral_twE6 hn K hK) hQ

namespace RecipeFieldE6

section InnDiag

variable {M : Type} [Group M]

@[expose] def IsInnDiagOn {ι : Type*} (H : Subgroup M) (D : ι → M)
    (φ : MulAut (LargeEvenCenterQuot H)) : Prop :=
  ∃ g ∈ H, ∃ a : ι, (∀ h ∈ H, D a * h * (D a)⁻¹ ∈ H) ∧ (∀ h ∈ H, (D a)⁻¹ * h * D a ∈ H) ∧
    IsConjOn H φ (g * D a)

end InnDiag

theorem mem_chevID_iff_isInnDiagOn {r : ℕ} {A : Matrix (Fin r) (Fin r) ℤ} {K : Type} [Field K]
    {H : Subgroup (LargeEvenChevGL A K)} {φ : MulAut (LargeEvenCenterQuot H)} :
    φ ∈ LargeEvenChevIDImage A K H ↔ IsInnDiagOn H (TableB.diagHom A K) φ := by
  constructor
  · exact exists_isConjOn_of_mem_chevID
  · rintro ⟨g, hg, a, ha1, ha2, hφ⟩
    set g₀ : H := ⟨g, hg⟩
    have hψ : IsConjOn H ((MulAut.conj (LargeEvenCenterMk H g₀))⁻¹ * φ) (TableB.diagHom A K a) := by
      have h1 := isConjOn_inv (isConjOn_conj g₀) (fun h hh =>
        H.mul_mem (H.mul_mem (H.inv_mem hg) hh) hg)
      exact isConjOn_of_eq (isConjOn_mul h1 hφ) (by simp [g₀])
    have hmem := mem_chevDiagImage_of_isConjOn hψ ha2
    have e : φ = MulAut.conj (LargeEvenCenterMk H g₀) *
        ((MulAut.conj (LargeEvenCenterMk H g₀))⁻¹ * φ) := by group
    rw [e]
    exact Subgroup.mul_mem _ (Subgroup.subset_closure (Or.inl ⟨_, rfl⟩))
      (Subgroup.subset_closure (Or.inr hmem))

@[expose] def E6QuotOn (K : Type) [Field K] (S : (Fin TwistTag.E6.tag.rank → ℤ) → Prop) : Prop :=
  ∃ Ψ : MulAut (LargeEvenCenterQuot (MarkChev.chevH TwistTag.E6.tag.cartan S K false)) →*
      (K ≃+* K) × Multiplicative (ZMod (exactE TwistTag.E6.tag)),
    (∀ φ, Ψ φ = 1 ↔ IsInnDiagOn (MarkChev.chevH TwistTag.E6.tag.cartan S K false)
      (markDiagUnit S K) φ) ∧ ∀ τ : K ≃+* K, ∃ φ, Ψ φ = (τ, 1)

theorem E6QuotOn.of_eq {K : Type} [Field K] {S S' : (Fin TwistTag.E6.tag.rank → ℤ) → Prop}
    (hS : S = S') (h : E6QuotOn K S) : E6QuotOn K S' :=
  hS ▸ h


theorem e6QuotOn_isRoot (K : Type) [Field K] [Finite K] : E6QuotOn K (IsRoot TwistTag.E6.tag) := by
  obtain ⟨Θ, hsurj, -, hker, -⟩ :=
    ordinary_E_field_graph_quotient_and_involutions TwistTag.E6.tag (Or.inl rfl) K
  unfold E6QuotOn
  rw [markDiagUnit_isRoot]
  suffices key : ∀ H : Subgroup (MarkChev.GLS (IsRoot TwistTag.E6.tag) K),
      H = adjointGroup TwistTag.E6.tag K →
      ∃ Ψ : MulAut (LargeEvenCenterQuot H) →*
          (K ≃+* K) × Multiplicative (ZMod (exactE TwistTag.E6.tag)),
        (∀ φ, Ψ φ = 1 ↔ IsInnDiagOn H (rootDiagUnit TwistTag.E6.tag) φ) ∧
          ∀ τ : K ≃+* K, ∃ φ, Ψ φ = (τ, 1) from
    key _ (chevH_false_eq_adjointGroup K TwistTag.E6.tag)
  intro H hH
  subst hH
  have hZ : Subgroup.center (adjointGroup TwistTag.E6.tag K) = ⊥ := center_adjointGroup_eq_bot
  set e := centerQuotEquivOfBot hZ with he
  have hmk : Function.Injective (LargeEvenCenterMk (adjointGroup TwistTag.E6.tag K)) := by
    rw [← MonoidHom.ker_eq_bot_iff, LargeEvenCenterMk, QuotientGroup.ker_mk', hZ]
  refine ⟨Θ.comp (MulAut.congr e).toMonoidHom, fun φ => ?_, fun τ => ?_⟩
  · rw [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, ← MonoidHom.mem_ker, hker]
    constructor
    · rintro ⟨g, a, hg⟩
      refine ⟨g, g.2, a, fun h hh => conj_rootDiagUnit_mem_adjointGroup a hh, fun h hh => ?_,
        fun h hh => ?_, fun h hh => ?_⟩
      · have := conj_rootDiagUnit_mem_adjointGroup (K := K) (a⁻¹) hh
        rwa [rootDiagUnit_inv a⁻¹, inv_inv, ← rootDiagUnit_inv] at this
      · have e1 : (g : ModGL TwistTag.E6.tag K) * rootDiagUnit TwistTag.E6.tag a * h *
            ((g : ModGL TwistTag.E6.tag K) * rootDiagUnit TwistTag.E6.tag a)⁻¹ =
            g * (rootDiagUnit TwistTag.E6.tag a * h * (rootDiagUnit TwistTag.E6.tag a)⁻¹) *
              (g : ModGL TwistTag.E6.tag K)⁻¹ := by group
        rw [e1]
        exact (adjointGroup TwistTag.E6.tag K).mul_mem ((adjointGroup TwistTag.E6.tag K).mul_mem
          g.2 (conj_rootDiagUnit_mem_adjointGroup a hh)) ((adjointGroup TwistTag.E6.tag K).inv_mem g.2)
      · rw [congr_centerQuotEquivOfBot_mk hZ φ h]
        congr 1
        apply Subtype.ext
        rw [hg h]
        group
    · rintro ⟨g, hg, a, ha1, -, hφ⟩
      refine ⟨⟨g, hg⟩, a, fun h => ?_⟩
      have h1 := hφ.2 h (hφ.1 h h.2)
      rw [congr_centerQuotEquivOfBot_mk hZ φ h] at h1
      have h2 := congrArg Subtype.val (hmk h1)
      rw [h2]
      simp only
      group
  · obtain ⟨α, hα⟩ := hsurj (τ, 1)
    exact ⟨(MulAut.congr e).symm α, by
      rw [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulEquiv.apply_symm_apply, hα]⟩

theorem ggRawPCyclic_E6 {f : ℕ} (hf : 1 ≤ f) (K : Type) [Field K] [Finite K]
    (hK : Nat.card K = 2 ^ f) {p : ℕ} (hp : Odd p) :
    GGRawPCyclic p (LargeEvenCenterQuot (LargeEvenChevH TwistTag.E6.tag.cartan K false))
      (LargeEvenChevIDImage TwistTag.E6.tag.cartan K
        (LargeEvenChevH TwistTag.E6.tag.cartan K false))
      (LargeEvenChevFieldImage TwistTag.E6.tag.cartan K
        (LargeEvenChevH TwistTag.E6.tag.cartan K false)) := by
  intro _ _
  have hQ := (e6QuotOn_isRoot K).of_eq (largeEvenIsRoot_eq_isRoot TwistTag.E6.tag).symm
  unfold E6QuotOn at hQ
  rw [← diagHom_eq_markDiagUnit] at hQ
  suffices key : ∀ H : Subgroup (LargeEvenChevGL TwistTag.E6.tag.cartan K),
      H = MarkChev.chevH TwistTag.E6.tag.cartan (LargeEvenIsRoot TwistTag.E6.tag.cartan) K false →
      ∃ J S : Subgroup (MulAut (LargeEvenCenterQuot H)),
        (J : Set (MulAut (LargeEvenCenterQuot H))) = LargeEvenChevIDImage TwistTag.E6.tag.cartan K H ∧
        J ≤ S ∧ (J.subgroupOf S).Normal ∧ (∃ g ∈ S, ∀ s ∈ S, ∃ k : ℤ, g ^ k * s ∈ J) ∧
        ∀ α : MulAut (LargeEvenCenterQuot H), (∃ k : ℕ, α ^ p ^ k = 1) → α ∈ S from
    key _ (largeEvenChevH_eq _ K false)
  intro H hH
  subst hH
  obtain ⟨Ψ, hker, hsurj⟩ := hQ
  obtain ⟨Fr, -, -, hzp, -⟩ :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_automorphism_fixed_field_cardinality
      Nat.prime_two hf hK
  obtain ⟨g₀, hg₀⟩ := hsurj Fr
  set S : Subgroup (MulAut (LargeEvenCenterQuot _)) := ((MonoidHom.snd _ _).comp Ψ).ker with hS
  refine ⟨Ψ.ker, S, ?_, fun φ hφ => ?_, Subgroup.normal_subgroupOf, ⟨g₀, ?_, fun s hs => ?_⟩,
    fun α ⟨k, hk⟩ => ?_⟩
  · ext φ
    rw [SetLike.mem_coe, MonoidHom.mem_ker, hker, ← mem_chevID_iff_isInnDiagOn]
  · rw [MonoidHom.mem_ker] at hφ ⊢
    rw [MonoidHom.comp_apply, hφ]
    rfl
  · rw [MonoidHom.mem_ker, MonoidHom.comp_apply, hg₀]
    rfl
  · obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp (hzp ▸ Subgroup.mem_top (Ψ s).1)
    refine ⟨-k, ?_⟩
    rw [MonoidHom.mem_ker, map_mul, map_zpow, hg₀]
    have hs2 : (Ψ s).2 = 1 := hs
    refine Prod.ext ?_ ?_
    · change (Fr, (1 : Multiplicative (ZMod (exactE TwistTag.E6.tag)))).1 ^ (-k) * (Ψ s).1 = 1
      rw [← hk, ← _root_.zpow_add, neg_add_cancel, zpow_zero]
    · change (Fr, (1 : Multiplicative (ZMod (exactE TwistTag.E6.tag)))).2 ^ (-k) * (Ψ s).2 = 1
      rw [hs2, one_zpow, one_mul]
  · rw [MonoidHom.mem_ker, MonoidHom.comp_apply]
    set x := (Ψ α).2 with hx
    have hxp : x ^ p ^ k = 1 := by
      have := congrArg Prod.snd (congrArg Ψ hk)
      rw [map_pow, map_one] at this
      exact this
    have hx2 : x ^ 2 = 1 := by
      have hall : ∀ y : Multiplicative (ZMod 2), y ^ 2 = 1 := by decide
      exact hall x
    have hcop : Nat.Coprime (p ^ k) 2 := (Nat.Coprime.pow_left k (Nat.coprime_two_right.mpr hp))
    have h1 := orderOf_dvd_of_pow_eq_one hxp
    have h2 := orderOf_dvd_of_pow_eq_one hx2
    have h3 : orderOf x = 1 := Nat.eq_one_of_dvd_coprimes hcop h1 h2
    exact orderOf_eq_one_iff.mp h3

end RecipeFieldE6

open RecipeFieldE6

theorem ggRawPCyclicOn_E6 :
    GGRawPCyclicOn fun _ => GGRecipeE6Label := by
  intro p hp hp2 lab hlab hS Q hQ
  obtain ⟨t, l, n⟩ := lab
  obtain ⟨hn, -⟩ := hlab
  dsimp only [GGRecipeE6Label] at hS
  subst hS
  exact recipeChevalley_and (fun K _ _ hK => ggRawPCyclic_E6 hn K hK (hp.odd_of_ne_two hp2)) hQ

end CFSG.StandardType

end
