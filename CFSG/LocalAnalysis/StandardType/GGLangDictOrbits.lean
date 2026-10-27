module

public import CFSG.LocalAnalysis.StandardType.GGLangDictChar
public import CFSG.LocalAnalysis.StandardType.GGLangReidx

public section

namespace CFSG.StandardType

section DictOrbits

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Universal CFSG.LieType.RootSystem
open CFSG.Open CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint CFSG.LieType.AlgebraicGroups
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.HardMathSupport.Timmesfeld.LangTorus
open Matrix
open scoped Matrix

private def dictOrb_kernelRel {τ : Tag} {M : Type*} [CommGroup M]
    (χ : Multiplicative (Fin τ.rank → ℤ) →* M) :
    (Fin τ.rank → ℤ) → (Fin τ.rank → ℤ) → Prop :=
  fun a b => a ∈ kernelRoots χ ∧ b ∈ kernelRoots χ ∧ iform a b ≠ 0

private theorem dictOrb_eqvGen_map {X Y : Type*} {r : X → X → Prop} {s : Y → Y → Prop}
    (f : X → Y) (hf : ∀ x y, r x y → s (f x) (f y)) {x y : X}
    (h : Relation.EqvGen r x y) : Relation.EqvGen s (f x) (f y) := by
  induction h with
  | rel x y hxy => exact .rel _ _ (hf x y hxy)
  | refl x => exact .refl _
  | symm x y _ ih => exact .symm _ _ ih
  | trans x y z _ _ ih1 ih2 => exact .trans _ _ _ ih1 ih2

private theorem dictOrb_eqvGen_congr {X : Type*} {r s : X → X → Prop}
    (h : ∀ x y, r x y ↔ s x y) {a b : X} :
    Relation.EqvGen r a b ↔ Relation.EqvGen s a b :=
  ⟨dictOrb_eqvGen_map id (fun x y hxy => (h x y).1 hxy),
   dictOrb_eqvGen_map id (fun x y hxy => (h x y).2 hxy)⟩

private theorem dictOrb_eqvGen_equiv {X Y : Type*} (e : X ≃ Y) {r : X → X → Prop}
    {s : Y → Y → Prop} (h : ∀ x y, r x y ↔ s (e x) (e y)) (x y : X) :
    Relation.EqvGen r x y ↔ Relation.EqvGen s (e x) (e y) := by
  refine ⟨dictOrb_eqvGen_map e (fun a b hxy => (h a b).1 hxy), fun hh => ?_⟩
  have := dictOrb_eqvGen_map e.symm
    (fun a b hab => (h (e.symm a) (e.symm b)).2 (by simpa using hab)) hh
  simpa using this

private theorem dictOrb_eqvGen_mem_iff {X : Type*} {r : X → X → Prop} {P : Set X}
    (hP : ∀ {a b}, r a b → a ∈ P ∧ b ∈ P) {a b : X} (h : Relation.EqvGen r a b) :
    a ∈ P ↔ b ∈ P := by
  induction h with
  | rel x y hxy => exact iff_of_true (hP hxy).1 (hP hxy).2
  | refl x => exact Iff.rfl
  | symm x y _ ih => exact ih.symm
  | trans x y z _ _ ih1 ih2 => exact ih1.trans ih2

private theorem dictOrb_eqvGen_subtype_iff {X : Type*} {P : Set X} {r : X → X → Prop}
    (hr : ∀ {a b : X}, r a b → a ∈ P ∧ b ∈ P) {a b : X} (ha : a ∈ P) (hb : b ∈ P) :
    Relation.EqvGen r a b ↔
      Relation.EqvGen (fun x y : P => r (x : X) (y : X)) ⟨a, ha⟩ ⟨b, hb⟩ := by
  constructor
  · intro h
    have key : ∀ {x y : X}, Relation.EqvGen r x y → ∀ (hx : x ∈ P) (hy : y ∈ P),
        Relation.EqvGen (fun p q : P => r (p : X) (q : X)) ⟨x, hx⟩ ⟨y, hy⟩ := by
      intro x y hxy
      induction hxy with
      | rel x y hxy => intro hx hy; exact .rel _ _ hxy
      | refl x =>
          intro hx hy
          rw [show (⟨x, hx⟩ : P) = ⟨x, hy⟩ from Subtype.ext rfl]
          exact .refl _
      | symm x y hxy ih => intro hx hy; exact .symm _ _ (ih hy hx)
      | trans x y z hxy hyz ih1 ih2 =>
          intro hx hz
          have hy : y ∈ P := (dictOrb_eqvGen_mem_iff hr hxy).1 hx
          exact .trans _ _ _ (ih1 hx hy) (ih2 hy hz)
    exact key h ha hb
  · intro h
    exact dictOrb_eqvGen_map (fun p : P => (p : X)) (fun p q hpq => hpq) h

private theorem dictOrb_kernelComponent_eq_iff {τ : Tag} {M : Type*} [CommGroup M]
    {χ : Multiplicative (Fin τ.rank → ℤ) →* M} {a b : Fin τ.rank → ℤ}
    (ha : a ∈ kernelRoots χ) (hb : b ∈ kernelRoots χ) :
    (⟦⟨a, ha⟩⟧ : KernelComponent χ) = ⟦⟨b, hb⟩⟧ ↔
      Relation.EqvGen (dictOrb_kernelRel χ) a b := by
  rw [Quotient.eq]
  refine (dictOrb_eqvGen_congr (fun p q : kernelRoots χ => ?_)).trans
    (dictOrb_eqvGen_subtype_iff (r := dictOrb_kernelRel χ)
      (fun {u v} h => ⟨h.1, h.2.1⟩) ha hb).symm
  rw [dotProduct_mulVec_eq_iform]
  exact ⟨fun h => ⟨p.2, q.2, h⟩, fun h => h.2.2⟩

private theorem dictOrb_reidx_symm {R N : ℕ} (h : R = N) (v : Fin N → ℤ) :
    ggLangReidx h (ggLangReidx h.symm v) = v := by
  subst h
  rfl

private theorem dictOrb_reidx_latPerm_iterate {R N : ℕ} (h : R = N)
    (π : Equiv.Perm (Fin R)) (k : ℕ) (x : Fin R → ℤ) :
    ggLangReidx h ((latPerm π)^[k] x) =
      (latPerm (ggLangPerm h π))^[k] (ggLangReidx h x) := by
  induction k with
  | zero => rfl
  | succ k ih =>
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply',
        ggLang_reidx_latPerm, ih]

private theorem dictOrb_latPerm_smul {N : ℕ} (π : Equiv.Perm (Fin N)) (c : ℤ)
    (v : Fin N → ℤ) : latPerm π (c • v) = c • latPerm π v := by
  funext i
  simp [latPerm, Pi.smul_apply]

private theorem dictOrb_pow_eq_one_or_neg {ε : ℤ} (hε : ε = 1 ∨ ε = -1) (k : ℕ) :
    ε ^ k = 1 ∨ ε ^ k = -1 := by
  rcases hε with h | h
  · left; rw [h, one_pow]
  · rw [h]
    rcases Nat.even_or_odd k with he | ho
    · left; exact he.neg_one_pow
    · right; exact ho.neg_one_pow

private theorem dictOrb_kernelRel_neg
    {τ : Tag} {M : Type*} [CommGroup M]
    {χ : Multiplicative (Fin τ.rank → ℤ) →* M} {x : Fin τ.rank → ℤ}
    (hx : x ∈ kernelRoots χ) : dictOrb_kernelRel χ x (-x) := by
  refine ⟨hx, ⟨IsRoot.neg hx.1, chi_neg hx.2⟩, ?_⟩
  intro h0
  have hpos : 0 < iform x x := iform_self_pos_of_isRoot hx.1
  have hneg : iform x (-x) = -iform x x := iform_neg_right x x
  rw [hneg] at h0
  omega

private theorem dictOrb_kernelRel_zsmul_eqvGen
    {τ : Tag} {M : Type*} [CommGroup M]
    {χ : Multiplicative (Fin τ.rank → ℤ) →* M} {ε : ℤ} (hε : ε = 1 ∨ ε = -1)
    {x : Fin τ.rank → ℤ} (hx : x ∈ kernelRoots χ) (k : ℕ) :
    Relation.EqvGen (dictOrb_kernelRel χ) x (ε ^ k • x) := by
  rcases dictOrb_pow_eq_one_or_neg hε k with h | h
  · rw [h, one_zsmul]; exact .refl _
  · rw [h, neg_one_zsmul]; exact .rel _ _ (dictOrb_kernelRel_neg hx)

private theorem dictOrb_iterate_mem_kernelRoots {τ : Tag} {M : Type*} [CommGroup M]
    {ρ : Equiv.Perm (Fin τ.rank → ℤ)} {χ : Multiplicative (Fin τ.rank → ℤ) →* M}
    (hker : ∀ γ ∈ kernelRoots χ, ρ γ ∈ kernelRoots χ) (k : ℕ) {γ : Fin τ.rank → ℤ}
    (hγ : γ ∈ kernelRoots χ) :
    (ρ : (Fin τ.rank → ℤ) → (Fin τ.rank → ℤ))^[k] γ ∈ kernelRoots χ := by
  induction k with
  | zero => exact hγ
  | succ k ih =>
      rw [Function.iterate_succ_apply']
      exact hker _ ih

private theorem dictOrb_iform_iterate {τ : Tag} {ρ : Equiv.Perm (Fin τ.rank → ℤ)}
    (hform : ∀ γ δ, iform (ρ γ) (ρ δ) = iform γ δ) (k : ℕ) (x y : Fin τ.rank → ℤ) :
    iform ((ρ : (Fin τ.rank → ℤ) → _)^[k] x) ((ρ : (Fin τ.rank → ℤ) → _)^[k] y) =
      iform x y := by
  induction k generalizing x y with
  | zero => rfl
  | succ k ih =>
      rw [Function.iterate_succ_apply, Function.iterate_succ_apply, ih, hform]

private theorem dictOrb_kernelRel_iterate {τ : Tag} {M : Type*} [CommGroup M]
    {ρ : Equiv.Perm (Fin τ.rank → ℤ)} {χ : Multiplicative (Fin τ.rank → ℤ) →* M}
    (hker : ∀ γ ∈ kernelRoots χ, ρ γ ∈ kernelRoots χ)
    (hform : ∀ γ δ, iform (ρ γ) (ρ δ) = iform γ δ) (k : ℕ) {x y : Fin τ.rank → ℤ}
    (h : dictOrb_kernelRel χ x y) :
    dictOrb_kernelRel χ ((ρ : (Fin τ.rank → ℤ) → _)^[k] x)
      ((ρ : (Fin τ.rank → ℤ) → _)^[k] y) :=
  ⟨dictOrb_iterate_mem_kernelRoots hker k h.1,
   dictOrb_iterate_mem_kernelRoots hker k h.2.1,
   fun hz => h.2.2 ((dictOrb_iform_iterate hform k x y).symm.trans hz)⟩

private def dictOrb_orbitRoots {τ : Tag} {M : Type*} [CommGroup M]
    (ρ : Equiv.Perm (Fin τ.rank → ℤ)) (χ : Multiplicative (Fin τ.rank → ℤ) →* M)
    (i : KernelComponent χ) : Set (Fin τ.rank → ℤ) :=
  {γ | ∃ (k : ℕ) (δ : Fin τ.rank → ℤ), δ ∈ componentRoots χ i ∧
    γ = (ρ : (Fin τ.rank → ℤ) → (Fin τ.rank → ℤ))^[k] δ}

private theorem dictOrb_orbitRoots_mapsTo {τ : Tag} {M : Type*} [CommGroup M]
    {ρ : Equiv.Perm (Fin τ.rank → ℤ)} {χ : Multiplicative (Fin τ.rank → ℤ) →* M}
    (i : KernelComponent χ) :
    Set.MapsTo (ρ : (Fin τ.rank → ℤ) → (Fin τ.rank → ℤ))
      (dictOrb_orbitRoots ρ χ i) (dictOrb_orbitRoots ρ χ i) := by
  rintro _ ⟨k, δ, hδ, rfl⟩
  exact ⟨k + 1, δ, hδ, by rw [Function.iterate_succ_apply']⟩

private theorem dictOrb_orbitRoots_subset_kernelRoots {τ : Tag} {M : Type*} [CommGroup M]
    {ρ : Equiv.Perm (Fin τ.rank → ℤ)} {χ : Multiplicative (Fin τ.rank → ℤ) →* M}
    (hker : ∀ γ ∈ kernelRoots χ, ρ γ ∈ kernelRoots χ) (i : KernelComponent χ) :
    dictOrb_orbitRoots ρ χ i ⊆ kernelRoots χ := by
  rintro _ ⟨k, δ, ⟨hδ, -⟩, rfl⟩
  exact dictOrb_iterate_mem_kernelRoots hker k hδ

private theorem dictOrb_eqvGen_equiv_iff {X : Type*} {r : X → X → Prop} (e : X ≃ X)
    (hr : ∀ x y, r (e x) (e y) ↔ r x y) (x y : X) :
    Relation.EqvGen r (e x) (e y) ↔ Relation.EqvGen r x y :=
  (dictOrb_eqvGen_equiv e (fun x y => (hr x y).symm) x y).symm

private theorem dictOrb_orbitRoots_closed {τ : Tag} {M : Type*}
    [CommGroup M] {ρ : Equiv.Perm (Fin τ.rank → ℤ)}
    {χ : Multiplicative (Fin τ.rank → ℤ) →* M}
    (hker : ∀ γ ∈ kernelRoots χ, ρ γ ∈ kernelRoots χ)
    (hform : ∀ γ δ, iform (ρ γ) (ρ δ) = iform γ δ) (i : KernelComponent χ)
    {γ : Fin τ.rank → ℤ} (hγ : γ ∈ dictOrb_orbitRoots ρ χ i)
    (hγk : γ ∈ kernelRoots χ) {β : Fin τ.rank → ℤ} (hβ : β ∈ kernelRoots χ)
    (h : Relation.EqvGen (dictOrb_kernelRel χ) β γ) :
    β ∈ dictOrb_orbitRoots ρ χ i := by
  classical
  have hfin : (kernelRoots χ).Finite := (finite_setOf_isRoot τ).subset fun α h => h.1
  have : Finite (kernelRoots χ) := hfin.to_subtype
  have hsub : Relation.EqvGen
      (fun p q : kernelRoots χ =>
        (p : Fin τ.rank → ℤ) ⬝ᵥ (τ.symmetrizedCartan *ᵥ (q : Fin τ.rank → ℤ)) ≠ 0)
      ⟨β, hβ⟩ ⟨γ, hγk⟩ := by
    have h1 : Relation.EqvGen
        (fun p q : kernelRoots χ =>
          dictOrb_kernelRel χ (p : Fin τ.rank → ℤ) (q : Fin τ.rank → ℤ))
        ⟨β, hβ⟩ ⟨γ, hγk⟩ :=
      (dictOrb_eqvGen_subtype_iff (r := dictOrb_kernelRel χ)
        (fun {u v} h => ⟨h.1, h.2.1⟩) hβ hγk).1 h
    refine (dictOrb_eqvGen_congr (fun p q : kernelRoots χ => ?_)).1 h1
    rw [dotProduct_mulVec_eq_iform]
    exact ⟨fun hh => hh.2.2, fun hh => ⟨p.2, q.2, hh⟩⟩
  let σ : kernelRoots χ → kernelRoots χ := fun x => ⟨ρ x, hker x x.2⟩
  have hσinj : Function.Injective σ := fun x y h =>
    Subtype.ext (ρ.injective (congrArg Subtype.val h))
  let e : Equiv.Perm (kernelRoots χ) := Equiv.ofBijective σ (Finite.injective_iff_bijective.1 hσinj)
  have he_iter : ∀ (k : ℕ) (x : kernelRoots χ),
      (((e ^ k) x : kernelRoots χ) : Fin τ.rank → ℤ) = (ρ : (Fin τ.rank → ℤ) → _)^[k] x := by
    intro k
    induction k with
    | zero => intro x; simp
    | succ k ih =>
        intro x
        rw [pow_succ', Equiv.Perm.mul_apply]
        show ρ (((e ^ k) x : kernelRoots χ) : Fin τ.rank → ℤ) = _
        rw [ih, Function.iterate_succ_apply']
  have hr : ∀ (k : ℕ) (x y : kernelRoots χ),
      (((e ^ k) x : kernelRoots χ) : Fin τ.rank → ℤ) ⬝ᵥ
          (τ.symmetrizedCartan *ᵥ (((e ^ k) y : kernelRoots χ) : Fin τ.rank → ℤ)) ≠ 0 ↔
        (x : Fin τ.rank → ℤ) ⬝ᵥ (τ.symmetrizedCartan *ᵥ (y : Fin τ.rank → ℤ)) ≠ 0 := by
    intro k x y
    rw [dotProduct_mulVec_eq_iform, dotProduct_mulVec_eq_iform, he_iter, he_iter,
      dictOrb_iform_iterate hform]
  obtain ⟨k, δ, ⟨hδ, hδi⟩, rfl⟩ := hγ
  set y : kernelRoots χ := (e ^ k)⁻¹ ⟨β, hβ⟩ with hy
  have hey : (e ^ k) y = ⟨β, hβ⟩ := by simp [hy]
  have hex : (e ^ k) ⟨δ, hδ⟩ =
      ⟨(ρ : (Fin τ.rank → ℤ) → _)^[k] δ, dictOrb_iterate_mem_kernelRoots hker k hδ⟩ :=
    Subtype.ext (he_iter k ⟨δ, hδ⟩)
  have hyx : (⟦y⟧ : KernelComponent χ) = ⟦⟨δ, hδ⟩⟧ := by
    rw [Quotient.eq]
    refine (dictOrb_eqvGen_equiv_iff (e ^ k) (hr k) y ⟨δ, hδ⟩).1 ?_
    rw [hey, hex]
    exact hsub
  refine ⟨k, y, ⟨y.2, hyx.trans hδi⟩, ?_⟩
  have := congrArg Subtype.val hey
  rw [he_iter] at this
  exact this.symm

private theorem dictOrb_orbit_eq_of_char
    {τ : Tag} {M : Type*} [CommGroup M]
    {ρ : Equiv.Perm (Fin τ.rank → ℤ)} {σ : (Fin τ.rank → ℤ) → (Fin τ.rank → ℤ)} {ε : ℤ}
    (hε : ε = 1 ∨ ε = -1)
    {χ : Multiplicative (Fin τ.rank → ℤ) →* M}
    (hker : ∀ γ ∈ kernelRoots χ, ρ γ ∈ kernelRoots χ)
    (hform : ∀ γ δ, iform (ρ γ) (ρ δ) = iform γ δ)
    {δ0 : Fin τ.rank → ℤ} (hδ0 : δ0 ∈ kernelRoots χ)
    (hiter : ∀ k : ℕ, (σ : (Fin τ.rank → ℤ) → (Fin τ.rank → ℤ))^[k] δ0 =
      ε ^ k • (ρ : (Fin τ.rank → ℤ) → (Fin τ.rank → ℤ))^[k] δ0) :
    dictOrb_orbitRoots ρ χ ⟦⟨δ0, hδ0⟩⟧ =
      {γ | ∃ k : ℕ, Relation.EqvGen (dictOrb_kernelRel χ)
        ((σ : (Fin τ.rank → ℤ) → (Fin τ.rank → ℤ))^[k] δ0) γ} := by
  ext γ
  constructor
  · rintro ⟨k, δ, ⟨hδ, hδi⟩, rfl⟩
    have hδδ0 : Relation.EqvGen (dictOrb_kernelRel χ) δ δ0 :=
      (dictOrb_kernelComponent_eq_iff hδ hδ0).1 hδi
    have hρ : Relation.EqvGen (dictOrb_kernelRel χ)
        ((ρ : (Fin τ.rank → ℤ) → _)^[k] δ) ((ρ : (Fin τ.rank → ℤ) → _)^[k] δ0) :=
      dictOrb_eqvGen_map ((ρ : (Fin τ.rank → ℤ) → _)^[k])
        (fun x y hxy => dictOrb_kernelRel_iterate hker hform k hxy) hδδ0
    have hσ : Relation.EqvGen (dictOrb_kernelRel χ)
        ((ρ : (Fin τ.rank → ℤ) → _)^[k] δ0) (ε ^ k • (ρ : (Fin τ.rank → ℤ) → _)^[k] δ0) :=
      dictOrb_kernelRel_zsmul_eqvGen hε (dictOrb_iterate_mem_kernelRoots hker k hδ0) k
    refine ⟨k, ?_⟩
    rw [hiter k]
    exact Relation.EqvGen.trans _ _ _ hσ.symm hρ.symm
  · rintro ⟨k, h⟩
    have hmem : ((σ : (Fin τ.rank → ℤ) → _)^[k] δ0) ∈
        dictOrb_orbitRoots ρ χ ⟦⟨δ0, hδ0⟩⟧ := by
      rw [hiter k]
      have hpos : (ρ : (Fin τ.rank → ℤ) → _)^[k] δ0 ∈
          dictOrb_orbitRoots ρ χ ⟦⟨δ0, hδ0⟩⟧ :=
        ⟨k, δ0, ⟨hδ0, rfl⟩, rfl⟩
      rcases dictOrb_pow_eq_one_or_neg hε k with hk | hk
      · rw [hk, one_zsmul]; exact hpos
      · rw [hk, neg_one_zsmul]
        have hxker : (ρ : (Fin τ.rank → ℤ) → _)^[k] δ0 ∈ kernelRoots χ :=
          dictOrb_iterate_mem_kernelRoots hker k hδ0
        have hnegker : -(ρ : (Fin τ.rank → ℤ) → _)^[k] δ0 ∈ kernelRoots χ :=
          ⟨IsRoot.neg hxker.1, chi_neg hxker.2⟩
        refine dictOrb_orbitRoots_closed hker hform _ hpos hxker hnegker ?_
        exact Relation.EqvGen.symm _ _ (Relation.EqvGen.rel _ _ (dictOrb_kernelRel_neg hxker))
    have hmem_ker : ((σ : (Fin τ.rank → ℤ) → _)^[k] δ0) ∈ kernelRoots χ :=
      dictOrb_orbitRoots_subset_kernelRoots hker _ hmem
    have hnm : γ ∈ kernelRoots χ :=
      (dictOrb_eqvGen_mem_iff (r := dictOrb_kernelRel χ)
        (fun {a b} h => ⟨h.1, h.2.1⟩) h).1 hmem_ker
    exact dictOrb_orbitRoots_closed hker hform _ hmem hmem_ker hnm h.symm

private theorem dictOrb_latPerm_eq_smul_rho
    {L : Type} [Field L] [IsAlgClosed L] {t : StatedLieTag} {n f p : ℕ}
    {Bs : Subgroup (GGAutU t n f)}
    {S : Matrix (Fin (ggU (absTag t) 6 f).D.rank) (Fin (ggU (absTag t) 6 f).D.rank) ℤ}
    {π : Equiv.Perm (Fin (ggU (absTag t) 6 f).D.rank)}
    {coord : Bs →* Multiplicative (Fin (ggU (absTag t) 6 f).D.rank → ZMod p)}
    (B : GGLangData L t n f p Bs S π coord) {γ : Fin B.τ.rank → ℤ} (hγ : IsRoot B.τ γ) :
    latPerm (ggLangPerm B.rank_eq π) γ = B.ε • B.setup.ρ γ := by
  have h := ggLang_rho_eq_perm B hγ
  have hε : B.ε * B.ε = 1 := by rcases B.ε_cases with h | h <;> rw [h] <;> ring
  rw [h, smul_smul, hε, one_zsmul]

private theorem dictOrb_latPerm_iterate_eq_smul
    {L : Type} [Field L] [IsAlgClosed L] {t : StatedLieTag} {n f p : ℕ}
    {Bs : Subgroup (GGAutU t n f)}
    {S : Matrix (Fin (ggU (absTag t) 6 f).D.rank) (Fin (ggU (absTag t) 6 f).D.rank) ℤ}
    {π : Equiv.Perm (Fin (ggU (absTag t) 6 f).D.rank)}
    {coord : Bs →* Multiplicative (Fin (ggU (absTag t) 6 f).D.rank → ZMod p)}
    (B : GGLangData L t n f p Bs S π coord) {γ : Fin B.τ.rank → ℤ} (hγ : IsRoot B.τ γ)
    (k : ℕ) :
    (latPerm (ggLangPerm B.rank_eq π))^[k] γ = B.ε ^ k • (B.setup.ρ)^[k] γ := by
  have hρroot : ∀ k, IsRoot B.τ ((B.setup.ρ)^[k] γ) := by
    intro k
    induction k with
    | zero => exact hγ
    | succ k ih =>
        rw [Function.iterate_succ_apply']
        exact (B.setup.frob.isRoot_iff _).2 ih
  induction k with
  | zero => simp
  | succ k ih =>
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih, dictOrb_latPerm_smul,
        dictOrb_latPerm_eq_smul_rho B (hρroot k), smul_smul, ← pow_succ]

private theorem dictOrb_rho_mem_kernelRoots
    {L : Type} [Field L] [IsAlgClosed L] {t : StatedLieTag} {n f p : ℕ}
    {Bs : Subgroup (GGAutU t n f)}
    {S : Matrix (Fin (ggU (absTag t) 6 f).D.rank) (Fin (ggU (absTag t) 6 f).D.rank) ℤ}
    {π : Equiv.Perm (Fin (ggU (absTag t) 6 f).D.rank)}
    {coord : Bs →* Multiplicative (Fin (ggU (absTag t) 6 f).D.rank → ZMod p)}
    (B : GGLangData L t n f p Bs S π coord) (b : Bs) :
    ∀ γ ∈ kernelRoots (rootCharHom (B.a b)), B.setup.ρ γ ∈ kernelRoots (rootCharHom (B.a b)) := by
  rintro γ ⟨hγ, hchar⟩
  refine ⟨(B.setup.frob.isRoot_iff γ).2 hγ, ?_⟩
  have h : rootChar (B.a b) γ = 1 := hchar
  show rootChar (B.a b) (B.setup.ρ γ) = 1
  rw [B.setup.frob.rootChar_eq (B.a b) (B.a_torus b) γ hγ, h, one_pow]

private theorem dictOrb_rho_mem_kernelRoots_pi
    {L : Type} [Field L] [IsAlgClosed L] {t : StatedLieTag} {n f p : ℕ}
    {Bs : Subgroup (GGAutU t n f)}
    {S : Matrix (Fin (ggU (absTag t) 6 f).D.rank) (Fin (ggU (absTag t) 6 f).D.rank) ℤ}
    {π : Equiv.Perm (Fin (ggU (absTag t) 6 f).D.rank)}
    {coord : Bs →* Multiplicative (Fin (ggU (absTag t) 6 f).D.rank → ZMod p)}
    (B : GGLangData L t n f p Bs S π coord) (Us : Set Bs) :
    ∀ γ ∈ kernelRoots (Pi.monoidHom fun u : Us => rootCharHom (B.a u.1)),
      B.setup.ρ γ ∈ kernelRoots (Pi.monoidHom fun u : Us => rootCharHom (B.a u.1)) := by
  rintro γ ⟨hγ, hchar⟩
  refine ⟨(B.setup.frob.isRoot_iff γ).2 hγ, funext fun u : Us => ?_⟩
  have h : rootChar (B.a u.1) γ = 1 := congrFun hchar u
  show rootChar (B.a u.1) (B.setup.ρ γ) = 1
  rw [B.setup.frob.rootChar_eq (B.a u.1) (B.a_torus u.1) γ hγ, h, one_pow]

private theorem dictOrb_mem_latPhi_iff
    {L : Type} [Field L] [IsAlgClosed L] {t : StatedLieTag} {n f p : ℕ}
    {Bs : Subgroup (GGAutU t n f)}
    {S : Matrix (Fin (ggU (absTag t) 6 f).D.rank) (Fin (ggU (absTag t) 6 f).D.rank) ℤ}
    {π : Equiv.Perm (Fin (ggU (absTag t) 6 f).D.rank)}
    {coord : Bs →* Multiplicative (Fin (ggU (absTag t) 6 f).D.rank → ZMod p)}
    (B : GGLangData L t n f p Bs S π coord) (hp : p.Prime) (b : Bs)
    (v : Fin (ggU (absTag t) 6 f).D.rank → ℤ) :
    v ∈ latPhi (ggU (absTag t) 6 f).D.roots p (Multiplicative.toAdd (coord b)) ↔
      ggLangReidx B.rank_eq v ∈ kernelRoots (rootCharHom (B.a b)) := by
  constructor
  · rintro ⟨hvroot, hvchar⟩
    exact ⟨(B.roots_iff v).1 hvroot, (latChar_eq_zero_iff_rootChar_eq_one B hp b v).1 hvchar⟩
  · rintro ⟨hroot, hchar⟩
    exact ⟨(B.roots_iff v).2 hroot, (latChar_eq_zero_iff_rootChar_eq_one B hp b v).2 hchar⟩

private theorem dictOrb_mem_latPhi_family
    {L : Type} [Field L] [IsAlgClosed L] {t : StatedLieTag} {n f p : ℕ}
    {Bs : Subgroup (GGAutU t n f)}
    {S : Matrix (Fin (ggU (absTag t) 6 f).D.rank) (Fin (ggU (absTag t) 6 f).D.rank) ℤ}
    {π : Equiv.Perm (Fin (ggU (absTag t) 6 f).D.rank)}
    {coord : Bs →* Multiplicative (Fin (ggU (absTag t) 6 f).D.rank → ZMod p)}
    (B : GGLangData L t n f p Bs S π coord) (hp : p.Prime) (Us : Set Bs)
    (v : Fin (ggU (absTag t) 6 f).D.rank → ℤ) :
    v ∈ {α | α ∈ (ggU (absTag t) 6 f).D.roots ∧
        ∀ u ∈ Us, latChar p (Multiplicative.toAdd (coord u)) α = 0} ↔
      ggLangReidx B.rank_eq v ∈
        kernelRoots (Pi.monoidHom fun u : Us => rootCharHom (B.a u.1)) := by
  constructor
  · rintro ⟨hvroot, hvchar⟩
    refine ⟨(B.roots_iff v).1 hvroot, funext fun u : Us => ?_⟩
    exact (latChar_eq_zero_iff_rootChar_eq_one B hp u.1 v).1 (hvchar u.1 u.2)
  · rintro ⟨hroot, hchar⟩
    refine ⟨(B.roots_iff v).2 hroot, fun u hu => ?_⟩
    exact (latChar_eq_zero_iff_rootChar_eq_one B hp u v).2 (congrFun hchar ⟨u, hu⟩)

private theorem dictOrb_latLinked_of_mem_iff
    {L : Type} [Field L] [IsAlgClosed L] {t : StatedLieTag} {n f p : ℕ}
    {Bs : Subgroup (GGAutU t n f)}
    {S : Matrix (Fin (ggU (absTag t) 6 f).D.rank) (Fin (ggU (absTag t) 6 f).D.rank) ℤ}
    {π : Equiv.Perm (Fin (ggU (absTag t) 6 f).D.rank)}
    {coord : Bs →* Multiplicative (Fin (ggU (absTag t) 6 f).D.rank → ZMod p)}
    (B : GGLangData L t n f p Bs S π coord) {M : Type*} [CommGroup M]
    {χ : Multiplicative (Fin B.τ.rank → ℤ) →* M}
    {Φ : Set (Fin (ggU (absTag t) 6 f).D.rank → ℤ)}
    (hmem : ∀ v, v ∈ Φ ↔ ggLangReidx B.rank_eq v ∈ kernelRoots χ)
    (x y : Fin (ggU (absTag t) 6 f).D.rank → ℤ) :
    latLinked S Φ x y ↔
      Relation.EqvGen (dictOrb_kernelRel χ) (ggLangReidx B.rank_eq x)
        (ggLangReidx B.rank_eq y) := by
  rw [latLinked]
  refine dictOrb_eqvGen_equiv (s := dictOrb_kernelRel χ) (ggLangReidxEquiv B.rank_eq)
    (fun a b => ?_) x y
  rw [hmem a, hmem b, ggLang_gram_ne_zero_iff B a b]
  exact Iff.rfl

private theorem dictOrb_orbit_set_eq_of_char
    {L : Type} [Field L] [IsAlgClosed L] {t : StatedLieTag} {n f p : ℕ}
    {Bs : Subgroup (GGAutU t n f)}
    {S : Matrix (Fin (ggU (absTag t) 6 f).D.rank) (Fin (ggU (absTag t) 6 f).D.rank) ℤ}
    {π : Equiv.Perm (Fin (ggU (absTag t) 6 f).D.rank)}
    {coord : Bs →* Multiplicative (Fin (ggU (absTag t) 6 f).D.rank → ZMod p)}
    (B : GGLangData L t n f p Bs S π coord) {M : Type*} [CommGroup M]
    {χ : Multiplicative (Fin B.τ.rank → ℤ) →* M}
    {Φ : Set (Fin (ggU (absTag t) 6 f).D.rank → ℤ)}
    (hmem : ∀ v, v ∈ Φ ↔ ggLangReidx B.rank_eq v ∈ kernelRoots χ)
    (hker : ∀ γ ∈ kernelRoots χ, B.setup.ρ γ ∈ kernelRoots χ)
    {α : Fin (ggU (absTag t) 6 f).D.rank → ℤ} (hα : α ∈ Φ) :
    {β : Fin (ggU (absTag t) 6 f).D.rank → ℤ |
        ∃ k : ℕ, latLinked S Φ ((latPerm π)^[k] α) β}
      = ggLangReidx B.rank_eq ⁻¹'
          dictOrb_orbitRoots B.setup.ρ χ
            ⟦⟨ggLangReidx B.rank_eq α, (hmem α).1 hα⟩⟧ := by
  classical
  have hαker : ggLangReidx B.rank_eq α ∈ kernelRoots χ := (hmem α).1 hα
  have hcore := dictOrb_orbit_eq_of_char (ρ := B.setup.ρ)
    (σ := latPerm (ggLangPerm B.rank_eq π)) (ε := B.ε) B.ε_cases hker
    B.setup.frob.iform_eq hαker (fun k => dictOrb_latPerm_iterate_eq_smul B hαker.1 k)
  ext β
  simp only [Set.mem_setOf_eq, Set.mem_preimage, hcore]
  constructor
  · rintro ⟨k, hlink⟩
    refine ⟨k, ?_⟩
    have h := (dictOrb_latLinked_of_mem_iff B hmem ((latPerm π)^[k] α) β).1 hlink
    rwa [dictOrb_reidx_latPerm_iterate] at h
  · rintro ⟨k, hEq⟩
    exact ⟨k, (dictOrb_latLinked_of_mem_iff B hmem ((latPerm π)^[k] α) β).2 (by
      rw [dictOrb_reidx_latPerm_iterate]; exact hEq)⟩

theorem isCompOrbit_iff_rationalRoots
    {L : Type} [Field L] [IsAlgClosed L] {t : StatedLieTag} {n f p : ℕ}
    {Bs : Subgroup (GGAutU t n f)}
    {S : Matrix (Fin (ggU (absTag t) 6 f).D.rank) (Fin (ggU (absTag t) 6 f).D.rank) ℤ}
    {π : Equiv.Perm (Fin (ggU (absTag t) 6 f).D.rank)}
    {coord : Bs →* Multiplicative (Fin (ggU (absTag t) 6 f).D.rank → ZMod p)}
    (B : GGLangData L t n f p Bs S π coord) (hp : p.Prime) (b : Bs)
    (O : Set (Fin (ggU (absTag t) 6 f).D.rank → ℤ)) :
    IsCompOrbit S π (latPhi (ggU (absTag t) 6 f).D.roots p (Multiplicative.toAdd (coord b))) O ↔
      ∃ i : KernelComponent (rootCharHom (B.a b)),
        O = ggLangReidx B.rank_eq ⁻¹' rationalRoots B.setup.ρ (rootCharHom (B.a b)) i := by
  classical
  constructor
  · rintro ⟨α, hα, hO⟩
    refine ⟨⟦⟨ggLangReidx B.rank_eq α, (dictOrb_mem_latPhi_iff B hp b α).1 hα⟩⟧, ?_⟩
    rw [hO]
    exact dictOrb_orbit_set_eq_of_char B (dictOrb_mem_latPhi_iff B hp b)
      (dictOrb_rho_mem_kernelRoots B b) hα
  · rintro ⟨i, hO⟩
    obtain ⟨δ0, hδ0⟩ := Quotient.exists_rep i
    set α : Fin (ggU (absTag t) 6 f).D.rank → ℤ :=
      ggLangReidx B.rank_eq.symm (δ0 : Fin B.τ.rank → ℤ) with hαdef
    have hαre : ggLangReidx B.rank_eq α = (δ0 : Fin B.τ.rank → ℤ) :=
      dictOrb_reidx_symm B.rank_eq δ0.1
    have hαΦ : α ∈ latPhi (ggU (absTag t) 6 f).D.roots p (Multiplicative.toAdd (coord b)) := by
      rw [dictOrb_mem_latPhi_iff B hp b, hαre]
      exact δ0.2
    have hsub : (⟨ggLangReidx B.rank_eq α,
        (dictOrb_mem_latPhi_iff B hp b α).1 hαΦ⟩ :
          kernelRoots (rootCharHom (B.a b))) = δ0 := Subtype.ext hαre
    have hi : i = (⟦⟨ggLangReidx B.rank_eq α,
        (dictOrb_mem_latPhi_iff B hp b α).1 hαΦ⟩⟧ :
          KernelComponent (rootCharHom (B.a b))) := by
      rw [← hδ0, hsub]
    refine ⟨α, hαΦ, ?_⟩
    rw [hO, hi]
    exact (dictOrb_orbit_set_eq_of_char B (dictOrb_mem_latPhi_iff B hp b)
      (dictOrb_rho_mem_kernelRoots B b) hαΦ).symm

theorem isCompOrbit_iff_rationalRoots_family
    {L : Type} [Field L] [IsAlgClosed L] {t : StatedLieTag} {n f p : ℕ}
    {Bs : Subgroup (GGAutU t n f)}
    {S : Matrix (Fin (ggU (absTag t) 6 f).D.rank) (Fin (ggU (absTag t) 6 f).D.rank) ℤ}
    {π : Equiv.Perm (Fin (ggU (absTag t) 6 f).D.rank)}
    {coord : Bs →* Multiplicative (Fin (ggU (absTag t) 6 f).D.rank → ZMod p)}
    (B : GGLangData L t n f p Bs S π coord) (hp : p.Prime) (Us : Set Bs)
    (O : Set (Fin (ggU (absTag t) 6 f).D.rank → ℤ)) :
    IsCompOrbit S π {α | α ∈ (ggU (absTag t) 6 f).D.roots ∧
        ∀ u ∈ Us, latChar p (Multiplicative.toAdd (coord u)) α = 0} O ↔
      ∃ i : KernelComponent (Pi.monoidHom fun u : Us => rootCharHom (B.a u.1)),
        O = ggLangReidx B.rank_eq ⁻¹' {γ | ∃ (k : ℕ) (δ : Fin B.τ.rank → ℤ),
          δ ∈ componentRoots (Pi.monoidHom fun u : Us => rootCharHom (B.a u.1)) i ∧
            γ = (B.setup.ρ : (Fin B.τ.rank → ℤ) → (Fin B.τ.rank → ℤ))^[k] δ} := by
  classical
  let χU : Multiplicative (Fin B.τ.rank → ℤ) →* (Us → Lˣ) :=
    Pi.monoidHom fun u : Us => rootCharHom (B.a u.1)
  have hmem := dictOrb_mem_latPhi_family B hp Us
  have hker := dictOrb_rho_mem_kernelRoots_pi B Us
  constructor
  · rintro ⟨α, hα, hO⟩
    refine ⟨⟦⟨ggLangReidx B.rank_eq α, (hmem α).1 hα⟩⟧, ?_⟩
    rw [hO]
    exact dictOrb_orbit_set_eq_of_char B hmem hker hα
  · rintro ⟨i, hO⟩
    obtain ⟨δ0, hδ0⟩ := Quotient.exists_rep i
    set α : Fin (ggU (absTag t) 6 f).D.rank → ℤ :=
      ggLangReidx B.rank_eq.symm (δ0 : Fin B.τ.rank → ℤ) with hαdef
    have hαre : ggLangReidx B.rank_eq α = (δ0 : Fin B.τ.rank → ℤ) :=
      dictOrb_reidx_symm B.rank_eq δ0.1
    have hαΦ : α ∈ {α | α ∈ (ggU (absTag t) 6 f).D.roots ∧
        ∀ u ∈ Us, latChar p (Multiplicative.toAdd (coord u)) α = 0} := by
      rw [hmem, hαre]
      exact δ0.2
    have hsub : (⟨ggLangReidx B.rank_eq α, (hmem α).1 hαΦ⟩ :
          kernelRoots χU) = δ0 := Subtype.ext hαre
    have hi : i = (⟦⟨ggLangReidx B.rank_eq α, (hmem α).1 hαΦ⟩⟧ :
          KernelComponent χU) := by
      rw [← hδ0, hsub]
    refine ⟨α, hαΦ, ?_⟩
    rw [hO, hi]
    exact (dictOrb_orbit_set_eq_of_char B hmem hker hαΦ).symm

theorem ggLang_isSingleComp_componentRoots
    {L : Type} [Field L] [IsAlgClosed L] {t : StatedLieTag} {n f p : ℕ}
    {Bs : Subgroup (GGAutU t n f)}
    {S : Matrix (Fin (ggU (absTag t) 6 f).D.rank) (Fin (ggU (absTag t) 6 f).D.rank) ℤ}
    {π : Equiv.Perm (Fin (ggU (absTag t) 6 f).D.rank)}
    {coord : Bs →* Multiplicative (Fin (ggU (absTag t) 6 f).D.rank → ZMod p)}
    (B : GGLangData L t n f p Bs S π coord) (hp : p.Prime) (b : Bs)
    (i : KernelComponent (rootCharHom (B.a b))) :
    IsSingleComp S (latPhi (ggU (absTag t) 6 f).D.roots p (Multiplicative.toAdd (coord b)))
      (ggLangReidx B.rank_eq ⁻¹' componentRoots (rootCharHom (B.a b)) i) := by
  classical
  obtain ⟨δ0, hδ0⟩ := Quotient.exists_rep i
  refine ⟨ggLangReidx B.rank_eq.symm (δ0 : Fin B.τ.rank → ℤ), ?_, ?_⟩
  · show ggLangReidx B.rank_eq (ggLangReidx B.rank_eq.symm (δ0 : Fin B.τ.rank → ℤ))
      ∈ componentRoots (rootCharHom (B.a b)) i
    rw [dictOrb_reidx_symm]
    exact ⟨δ0.2, hδ0⟩
  · intro β hβ
    show latLinked S (latPhi (ggU (absTag t) 6 f).D.roots p (Multiplicative.toAdd (coord b)))
      (ggLangReidx B.rank_eq.symm (δ0 : Fin B.τ.rank → ℤ)) β
    obtain ⟨hβker, hβi⟩ := hβ
    refine (dictOrb_latLinked_of_mem_iff B (dictOrb_mem_latPhi_iff B hp b) _ _).2 ?_
    rw [dictOrb_reidx_symm]
    exact (dictOrb_kernelComponent_eq_iff δ0.2 hβker).1 (hδ0.trans hβi.symm)

end DictOrbits

end CFSG.StandardType
