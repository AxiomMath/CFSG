module

public import CFSG.LocalAnalysis.StandardType.GGSixTCWP4ULang
public import CFSG.Mathlib.Decide.Bounded

@[expose] public section

public noncomputable section

namespace CFSG.StandardType.F4ExplicitPos.JointIsolator

open CFSG.Blueprint.Chevalley CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.LieType.Chevalley CFSG.LieType.AlgebraicGroups CFSG.StandardType.TableCRes
  CFSG.LieType.Steinberg.Adjoint Matrix

open Classical

variable {τ : Tag}

theorem f4_signs : ∀ v ∈ rootFinset Tag.F4,
    (∀ i, 0 ≤ v i) ∨ (∀ i, v i ≤ 0) := by
  open scoped CFSG.Decide.Bounded in
  decide +kernel

theorem f4_abs_sum_le_eleven : ∀ v ∈ rootFinset Tag.F4,
    (∑ i, |v i|) ≤ 11 := by
  open scoped CFSG.Decide.Bounded in
  decide +kernel

theorem f4_signs_of_isRoot {v : Fin Tag.F4.rank → ℤ}
    (hv : IsRoot Tag.F4 v) : (∀ i, 0 ≤ v i) ∨ (∀ i, v i ≤ 0) :=
  f4_signs v (mem_rootFinset.2 hv)

def lamDiag {K : Type} [Field K] (J : Set (Fin τ.rank)) (lam : Kˣ) :
    Fin τ.rank → Kˣ :=
  open Classical in fun i => if i ∈ J then 1 else lam

@[simp] theorem lamDiag_apply_of_mem {K : Type} [Field K] {J : Set (Fin τ.rank)} {lam : Kˣ}
    {i : Fin τ.rank} (hi : i ∈ J) : lamDiag (K := K) J lam i = 1 := by
  simp [lamDiag, hi]

@[simp] theorem lamDiag_apply_of_not_mem {K : Type} [Field K] {J : Set (Fin τ.rank)} {lam : Kˣ}
    {i : Fin τ.rank} (hi : i ∉ J) : lamDiag (K := K) J lam i = lam := by
  simp [lamDiag, hi]

theorem rootChar_lamDiag {K : Type} [Field K] (J : Set (Fin τ.rank)) (lam : Kˣ)
    (γ : Fin τ.rank → ℤ) :
    rootChar (lamDiag (K := K) J lam) γ = lam ^ parabolicDegree τ J γ := by
  classical
  have key : ∀ s : Finset (Fin τ.rank), ∏ i ∈ s, (lamDiag (K := K) J lam i) ^ γ i =
      lam ^ (∑ i ∈ s, if i ∈ J then 0 else γ i) := by
    intro s
    induction s using Finset.induction_on with
    | empty => simp
    | insert i s hi ih =>
      rw [Finset.prod_insert hi, Finset.sum_insert hi, _root_.zpow_add, ih]
      congr 1
      by_cases hiJ : i ∈ J <;> simp [lamDiag, hiJ]
  exact key Finset.univ

theorem abs_parabolicDegree_le_eleven
    (J : Set (Fin Tag.F4.rank)) {v : Fin Tag.F4.rank → ℤ} (hv : IsRoot Tag.F4 v) :
    |parabolicDegree Tag.F4 J v| ≤ 11 := by
  have h1 : |parabolicDegree Tag.F4 J v| ≤ ∑ i, |if i ∈ J then 0 else v i| := by
    show |∑ i, (if i ∈ J then 0 else v i)| ≤ ∑ i, |if i ∈ J then 0 else v i|
    exact Finset.abs_sum_le_sum_abs _ _
  have h2 : (∑ i, |if i ∈ J then 0 else v i|) ≤ ∑ i, |v i| := by
    refine Finset.sum_le_sum fun i _ => ?_
    by_cases hi : i ∈ J <;> simp [hi]
  exact le_trans (le_trans h1 h2) (f4_abs_sum_le_eleven v (mem_rootFinset.2 hv))

theorem parabolicDegree_eq_zero_iff_of_sign (J : Set (Fin Tag.F4.rank))
    {v : Fin Tag.F4.rank → ℤ}
    (hsign : (∀ i, 0 ≤ v i) ∨ (∀ i, v i ≤ 0)) :
    parabolicDegree Tag.F4 J v = 0 ↔ ∀ i ∉ J, v i = 0 := by
  classical
  have hT : parabolicDegree Tag.F4 J v =
      ∑ i ∈ Finset.univ.filter (fun i => i ∉ J), v i := by
    show (∑ i, if i ∈ J then 0 else v i) = ∑ i ∈ Finset.univ.filter (fun i => i ∉ J), v i
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl fun i _ => ?_
    by_cases hi : i ∈ J <;> simp [hi]
  rw [hT]
  constructor
  · intro h i hi
    have hmem : i ∈ Finset.univ.filter (fun i => i ∉ J) := by simp [hi]
    rcases hsign with hs | hs
    · exact (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => hs j)).1 h i hmem
    · have hneg : ∑ j ∈ Finset.univ.filter (fun j => j ∉ J), (-v) j = 0 := by
        simp only [Pi.neg_apply]
        rw [Finset.sum_neg_distrib, h, neg_zero]
      have hz := (Finset.sum_eq_zero_iff_of_nonneg
        (fun j _ => neg_nonneg.2 (hs j))).1 hneg i hmem
      simpa using hz
  · intro h
    refine Finset.sum_eq_zero fun i hi => ?_
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
    exact h i hi

theorem eq_zero_of_zpow_eq_one_of_abs_le {Ω : Type} [Field Ω] {ℓ : ℕ} (hℓ : 11 < ℓ)
    {lam : Ωˣ} (hlam : IsPrimitiveRoot lam ℓ) {s : ℤ} (hs : |s| ≤ 11) (h : lam ^ s = 1) :
    s = 0 := by
  have hd : (orderOf lam : ℤ) ∣ s := orderOf_dvd_iff_zpow_eq_one.2 h
  have horder : orderOf lam = ℓ := hlam.eq_orderOf.symm
  refine Int.eq_zero_of_abs_lt_dvd (m := (orderOf lam : ℤ)) ?_ ?_
  · simpa [horder] using hd
  · rw [horder]
    have : (11 : ℤ) < (ℓ : ℤ) := by exact_mod_cast hℓ
    omega

theorem exists_primitiveRoot_unit (Ω : Type) [Field Ω] [IsAlgClosed Ω] (ℓ : ℕ) [NeZero ℓ]
    (hℓΩ : (ℓ : Ω) ≠ 0) : ∃ lam : Ωˣ, IsPrimitiveRoot lam ℓ := by
  have : IsSepClosed Ω := IsSepClosed.of_isAlgClosed Ω
  have : NeZero (ℓ : Ω) := ⟨hℓΩ⟩
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot Ω ℓ
  exact ⟨(hζ.isUnit (NeZero.ne ℓ)).unit, hζ.isUnit_unit (NeZero.ne ℓ)⟩

theorem kernelRoots_lamDiag_eq_parabolicRoots
    {Ω : Type} [Field Ω] {J : Set (Fin Tag.F4.rank)} {ℓ : ℕ} (hℓ : 11 < ℓ)
    {lam : Ωˣ} (hlam : IsPrimitiveRoot lam ℓ) :
    kernelRoots (rootCharHom (lamDiag (K := Ω) J lam)) = parabolicRoots Tag.F4 J := by
  ext α
  rw [kernelRoots_rootCharHom]
  change IsRoot Tag.F4 α ∧ rootChar (lamDiag (K := Ω) J lam) α = 1 ↔
    IsRoot Tag.F4 α ∧ ∀ i ∉ J, α i = 0
  constructor
  · rintro ⟨hroot, hchar⟩
    refine ⟨hroot, ?_⟩
    rw [rootChar_lamDiag] at hchar
    have hzero : parabolicDegree Tag.F4 J α = 0 :=
      eq_zero_of_zpow_eq_one_of_abs_le hℓ hlam (abs_parabolicDegree_le_eleven J hroot) hchar
    exact (parabolicDegree_eq_zero_iff_of_sign J (f4_signs_of_isRoot hroot)).1 hzero
  · rintro ⟨hroot, hoff⟩
    refine ⟨hroot, ?_⟩
    rw [rootChar_lamDiag]
    have hzero : parabolicDegree Tag.F4 J α = 0 := by
      show (∑ i, if i ∈ J then 0 else α i) = 0
      refine Finset.sum_eq_zero fun i _ => ?_
      by_cases hi : i ∈ J
      · simp [hi]
      · simp [hi, hoff i hi]
    rw [hzero, zpow_zero]

theorem kernelRoots_lamDiag_mul_eq_inter {Ω : Type} [Field Ω] {J : Set (Fin Tag.F4.rank)}
    {p ℓ : ℕ} (hcop : p.Coprime ℓ) {lam : Ωˣ} (hlam : IsPrimitiveRoot lam ℓ)
    {d' : Fin Tag.F4.rank → Ωˣ} (hd' : ∀ i, d' i ^ p = 1)
    (hkerz : kernelRoots (rootCharHom (lamDiag (K := Ω) J lam)) = parabolicRoots Tag.F4 J) :
    kernelRoots (rootCharHom (lamDiag (K := Ω) J lam * d')) =
      parabolicRoots Tag.F4 J ∩ kernelRoots (rootCharHom d') := by
  ext α
  rw [kernelRoots_rootCharHom]
  simp only [Set.mem_setOf_eq, Set.mem_inter_iff, parabolicRoots]
  constructor
  · rintro ⟨hroot, hchar⟩
    rw [rootChar_mul_tuple_fam] at hchar
    have hzpow : ∀ i, (lamDiag (K := Ω) J lam i) ^ ℓ = 1 := by
      intro i
      by_cases hi : i ∈ J <;> simp [lamDiag, hi, hlam.pow_eq_one]
    have hxℓ : (rootChar (lamDiag (K := Ω) J lam) α) ^ ℓ = 1 :=
      rootChar_pow_eq_one_of_forall hzpow α
    have hyp : (rootChar d' α) ^ p = 1 := rootChar_pow_eq_one_of_forall hd' α
    have hxp : (rootChar (lamDiag (K := Ω) J lam) α) ^ p = 1 := by
      have hxeq : rootChar (lamDiag (K := Ω) J lam) α = (rootChar d' α)⁻¹ :=
        eq_inv_of_mul_eq_one_left hchar
      rw [hxeq, inv_pow, hyp, inv_one]
    have hx1 : rootChar (lamDiag (K := Ω) J lam) α = 1 :=
      (pow_eq_one_iff_of_coprime hcop).1 ⟨hxp, hxℓ⟩
    have hy1 : rootChar d' α = 1 := by
      rw [hx1, one_mul] at hchar
      exact hchar
    have hmemz : α ∈ kernelRoots (rootCharHom (lamDiag (K := Ω) J lam)) := by
      rw [kernelRoots_rootCharHom]
      exact ⟨hroot, hx1⟩
    rw [hkerz] at hmemz
    exact ⟨⟨hroot, hmemz.2⟩, hroot, hy1⟩
  · rintro ⟨⟨hroot, hoff⟩, -, hd1⟩
    refine ⟨hroot, ?_⟩
    rw [rootChar_mul_tuple_fam]
    have hz : rootChar (lamDiag (K := Ω) J lam) α = 1 := by
      have hmemz : α ∈ kernelRoots (rootCharHom (lamDiag (K := Ω) J lam)) := by
        rw [hkerz]
        exact ⟨hroot, hoff⟩
      rw [kernelRoots_rootCharHom] at hmemz
      exact hmemz.2
    rw [hz, one_mul]
    exact hd1

theorem lamDiag_mul_pow {Ω : Type} [Field Ω] {J : Set (Fin Tag.F4.rank)} {p ℓ : ℕ}
    {lam : Ωˣ} (hlam : IsPrimitiveRoot lam ℓ) {d' : Fin Tag.F4.rank → Ωˣ}
    (hd' : ∀ i, d' i ^ p = 1) (i : Fin Tag.F4.rank) :
    (lamDiag (K := Ω) J lam * d') i ^ (p * ℓ) = 1 := by
  rw [Pi.mul_apply, mul_pow]
  have hz : (lamDiag (K := Ω) J lam i) ^ (p * ℓ) = 1 := by
    by_cases hi : i ∈ J
    · simp [lamDiag, hi]
    · simp only [lamDiag, if_neg hi]
      rw [pow_mul', hlam.pow_eq_one, one_pow]
  have hd : (d' i) ^ (p * ℓ) = 1 := by
    rw [pow_mul, hd' i, one_pow]
  rw [hz, hd, mul_one]

theorem exists_off_ne_one {Ω : Type} [Field Ω] {J : Set (Fin Tag.F4.rank)} {p ℓ : ℕ}
    (hcop : p.Coprime ℓ) {lam : Ωˣ} (hlam : IsPrimitiveRoot lam ℓ) (hlam1 : lam ≠ 1)
    {d' : Fin Tag.F4.rank → Ωˣ} (hd' : ∀ i, d' i ^ p = 1)
    {i : Fin Tag.F4.rank} (hi : i ∉ J) :
    (lamDiag (K := Ω) J lam * d') i ≠ 1 := by
  intro h
  rw [Pi.mul_apply, lamDiag_apply_of_not_mem hi] at h
  have hlamp : lam ^ p = 1 := by
    have hx : lam = (d' i)⁻¹ := eq_inv_of_mul_eq_one_left h
    rw [hx, inv_pow, hd' i, inv_one]
  exact hlam1 ((pow_eq_one_iff_of_coprime hcop).1 ⟨hlamp, hlam.pow_eq_one⟩)

theorem rootDiagUnit_ne_one_of_exists_ne_one
    {Ω : Type} [Field Ω]
    {b : Fin Tag.F4.rank → Ωˣ} (h : ∃ i, b i ≠ 1) :
    rootDiagUnit Tag.F4 b ≠ 1 := by
  intro hb
  obtain ⟨i, hi⟩ := h
  have h1 : b = 1 :=
    rootDiagUnit_injective (τ := Tag.F4) (by rw [hb, rootDiagUnit_one])
  exact hi (by simp [h1])

def KerAdjV {τ : Tag} {M : Type*} [CommGroup M]
    (χ : Multiplicative (Fin τ.rank → ℤ) →* M) (α β : Fin τ.rank → ℤ) : Prop :=
  α ∈ kernelRoots χ ∧ β ∈ kernelRoots χ ∧ iform α β ≠ 0

theorem kerRel_symm {τ : Tag} {M :
    Type*} [CommGroup M]
    (χ : Multiplicative (Fin τ.rank → ℤ) →* M) :
    Std.Symm (fun u v : kernelRoots χ =>
      (u : Fin τ.rank → ℤ) ⬝ᵥ (τ.symmetrizedCartan *ᵥ (v : Fin τ.rank → ℤ)) ≠ 0) :=
  ⟨fun u v h hc => by
    rw [dotProduct_mulVec_eq_iform] at h hc
    exact h (by rwa [iform_comm] at hc)⟩

theorem reflTransGen_map {α β : Type*} {r : α → α → Prop} {s : β → β → Prop}
    (f : α → β) (hf : ∀ a b, r a b → s (f a) (f b)) {a b : α}
    (h : Relation.ReflTransGen r a b) : Relation.ReflTransGen s (f a) (f b) := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail hprev hstep ih => exact ih.tail (hf _ _ hstep)

theorem eqvGen_of_reflTransGen {α : Type*} {r : α → α → Prop} {a b : α}
    (h : Relation.ReflTransGen r a b) : Relation.EqvGen r a b := by
  induction h with
  | refl => exact Relation.EqvGen.refl _
  | tail hprev hstep ih => exact Relation.EqvGen.trans _ _ _ ih (Relation.EqvGen.rel _ _ hstep)

theorem reflTransGen_restrict {α : Type*} {r : α → α → Prop} {S : Set α}
    (hS : ∀ ⦃a⦄, a ∈ S → ∀ ⦃b⦄, r a b → b ∈ S)
    {x : α} (hx : x ∈ S) {y : α} (h : Relation.ReflTransGen r x y) :
    ∃ hy : y ∈ S, Relation.ReflTransGen (fun a b : S => r a.1 b.1) ⟨x, hx⟩ ⟨y, hy⟩ := by
  induction h with
  | refl => exact ⟨hx, Relation.ReflTransGen.refl⟩
  | tail hprev hstep ih =>
      obtain ⟨hy, hpath⟩ := ih
      exact ⟨hS hy hstep, hpath.tail hstep⟩

theorem reflTransGen_kerAdjV_of_reflTransGen {τ : Tag} {M : Type*} [CommGroup M]
    (χ : Multiplicative (Fin τ.rank → ℤ) →* M) {a b : kernelRoots χ}
    (h : Relation.ReflTransGen (fun u v : kernelRoots χ =>
      (u : Fin τ.rank → ℤ) ⬝ᵥ (τ.symmetrizedCartan *ᵥ (v : Fin τ.rank → ℤ)) ≠ 0) a b) :
    Relation.ReflTransGen (KerAdjV χ) (a : Fin τ.rank → ℤ) (b : Fin τ.rank → ℤ) :=
  reflTransGen_map Subtype.val
    (fun u v huv => ⟨u.2, v.2, by rw [← dotProduct_mulVec_eq_iform]; exact huv⟩) h

end CFSG.StandardType.F4ExplicitPos.JointIsolator
end

end
