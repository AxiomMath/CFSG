module

public import CFSG.Mathlib.LinearAlgebra.RootSystem.TorusStabilizer
public import TauCeti.LinearAlgebra.RootSystem.Lowering
public import TauCeti.LinearAlgebra.RootSystem.Positive

public section

namespace CFSG.RootPairing

open TauCeti

section Basic

variable {ι R M N : Type*} [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N]
  [Module R N] {P : _root_.RootPairing ι R M N} (σ : P.Aut)

lemma indexEquiv_cube (hσ3 : σ ^ 3 = 1) (i : ι) :
    σ.indexEquiv (σ.indexEquiv (σ.indexEquiv i)) = i := by
  have h := congrArg (fun g : P.Aut => RootPairing.Equiv.indexHom P g i) hσ3
  simp only [map_pow, map_one, Equiv.Perm.one_apply, RootPairing.Equiv.indexHom_apply] at h
  rwa [pow_succ, pow_succ, pow_one, Equiv.Perm.mul_apply, Equiv.Perm.mul_apply] at h

@[expose] noncomputable def fixedWeylGroup : Subgroup P.weylGroup :=
  (Subgroup.centralizer {σ}).comap P.weylGroup.subtype

lemma mem_fixedWeylGroup {w : P.weylGroup} :
    w ∈ fixedWeylGroup σ ↔ (w : P.Aut) * σ = σ * w := by
  rw [fixedWeylGroup, Subgroup.mem_comap, Subgroup.coe_subtype,
    Subgroup.mem_centralizer_singleton_iff]

lemma conj_reflection (j : ι) :
    σ * RootPairing.Equiv.reflection P j * σ⁻¹ =
      RootPairing.Equiv.reflection P (σ.indexEquiv j) := by
  apply RootPairing.Equiv.weightHom_injective P
  refine LinearEquiv.ext fun x => ?_
  change (σ * RootPairing.Equiv.reflection P j * σ⁻¹) • x =
    RootPairing.Equiv.reflection P (σ.indexEquiv j) • x
  have hc : P.coroot' j (σ⁻¹ • x) = P.coroot' (σ.indexEquiv j) x := by
    rw [RootPairing.coroot'_smul, RootPairing.Equiv.indexEquiv_inv,
      RootPairing.Equiv.indexHom_apply, Equiv.Perm.inv_def, Equiv.symm_symm]
  rw [mul_smul, mul_smul, RootPairing.Equiv.reflection_smul, RootPairing.Equiv.reflection_smul,
    P.reflection_apply, P.reflection_apply, smul_sub, smul_inv_smul, smul_comm, hc,
    ← RootPairing.Equiv.root_indexEquiv_eq_smul]

lemma conj_ofIdx (j : ι) :
    σ * (RootPairing.weylGroup.ofIdx P j : P.Aut) * σ⁻¹ =
      (RootPairing.weylGroup.ofIdx P (σ.indexEquiv j) : P.Aut) := by
  simp only [RootPairing.weylGroup.coe_ofIdx]
  exact conj_reflection σ j

@[expose] noncomputable def orbitReflection (j : ι) : P.weylGroup :=
  RootPairing.weylGroup.ofIdx P j * RootPairing.weylGroup.ofIdx P (σ.indexEquiv j) *
    RootPairing.weylGroup.ofIdx P (σ.indexEquiv (σ.indexEquiv j))

lemma orbitReflection_of_eq {j : ι} (hj : σ.indexEquiv j = j) :
    orbitReflection σ j = RootPairing.weylGroup.ofIdx P j := by
  rw [orbitReflection, hj, hj, RootPairing.weylGroup.ofIdx_mul_self, one_mul]

lemma weylGroupToPerm_comm_of_mem_fixedWeylGroup {w : P.weylGroup} (hw : w ∈ fixedWeylGroup σ)
    (i : ι) : P.weylGroupToPerm w (σ.indexEquiv i) = σ.indexEquiv (P.weylGroupToPerm w i) := by
  have h := congrArg (fun g : P.Aut => RootPairing.Equiv.indexHom P g i)
    ((mem_fixedWeylGroup σ).mp hw)
  simp only [map_mul, Equiv.Perm.mul_apply, RootPairing.Equiv.indexHom_apply] at h
  exact h

lemma reflectionPerm_neg_eq (a x : ι) :
    P.reflectionPerm a (P.reflectionPerm x x) =
      P.reflectionPerm (P.reflectionPerm a x) (P.reflectionPerm a x) := by
  apply P.root.injective
  rw [P.root_reflectionPerm (P.reflectionPerm a x), P.reflection_apply_self,
    P.root_reflectionPerm a (P.reflectionPerm x x), P.root_reflectionPerm x x,
    P.reflection_apply_self, map_neg, P.root_reflectionPerm a x]

lemma two_mul_rootForm_root' [Fintype ι] (i : ι) (y : M) :
    2 * P.RootForm (P.root i) y = P.RootForm (P.root i) (P.root i) * P.coroot' i y := by
  have h := P.rootForm_reflection_reflection_apply i (P.root i) y
  rw [P.reflection_apply_self, P.reflection_apply, map_neg, LinearMap.neg_apply, map_sub,
    map_smul, smul_eq_mul] at h
  linear_combination -h

section OrbitFinset

variable [DecidableEq ι]

@[expose] def orbitFinset (i : ι) : Finset ι := {i, σ.indexEquiv i, σ.indexEquiv (σ.indexEquiv i)}

lemma mem_orbitFinset {i j : ι} :
    j ∈ orbitFinset σ i ↔ j = i ∨ j = σ.indexEquiv i ∨ j = σ.indexEquiv (σ.indexEquiv i) := by
  simp [orbitFinset]

lemma mem_orbitFinset_self (i : ι) : i ∈ orbitFinset σ i := (mem_orbitFinset σ).mpr (Or.inl rfl)

lemma image_orbitFinset (hσ3 : σ ^ 3 = 1) (i : ι) :
    (orbitFinset σ i).image σ.indexEquiv = orbitFinset σ i := by
  have h3 := indexEquiv_cube σ hσ3 i
  ext j
  simp only [Finset.mem_image, mem_orbitFinset]
  constructor
  · rintro ⟨k, hk | hk | hk, rfl⟩ <;> subst hk <;> simp [h3]
  · rintro (rfl | rfl | rfl)
    · exact ⟨_, Or.inr (Or.inr rfl), h3⟩
    · exact ⟨i, Or.inl rfl, rfl⟩
    · exact ⟨_, Or.inr (Or.inl rfl), rfl⟩

lemma sum_orbitFinset_comp {A : Type*} [AddCommMonoid A] (hσ3 : σ ^ 3 = 1) (i : ι)
    (F : ι → A) :
    ∑ γ ∈ orbitFinset σ i, F (σ.indexEquiv γ) = ∑ γ ∈ orbitFinset σ i, F γ := by
  conv_rhs => rw [← image_orbitFinset σ hσ3 i]
  rw [Finset.sum_image fun x _ y _ h => σ.indexEquiv.injective h]

lemma sum_orbitFinset_of_invariant {A : Type*} [AddCommMonoid A] (i : ι) (F : ι → A)
    (hF : ∀ γ, F (σ.indexEquiv γ) = F γ) :
    ∑ γ ∈ orbitFinset σ i, F γ = (orbitFinset σ i).card • F i := by
  rw [← Finset.sum_const]
  refine Finset.sum_congr rfl fun γ hγ => ?_
  rcases (mem_orbitFinset σ).mp hγ with rfl | rfl | rfl
  · rfl
  · exact hF _
  · rw [hF, hF]

end OrbitFinset

end Basic

section CharZero

variable {ι R M N : Type*} [CommRing R] [CharZero R] [AddCommGroup M] [Module R M]
  [AddCommGroup N] [Module R N] {P : _root_.RootPairing ι R M N} (b : P.Base) (σ : P.Aut)

lemma height_ne_zero (i : ι) : b.height i ≠ 0 := by
  let _ := P.indexNeg
  rcases RootPairing.Base.IsPos.or_neg b i with h | h
  · exact ((b.isPos_iff).mp h).ne'
  · have := (b.isPos_iff).mp h
    rw [b.height_reflectionPerm_self] at this
    omega

lemma exists_mem_support_pos_coroot' [Fintype ι] [LinearOrder R] [IsStrictOrderedRing R]
    {ν : M} (hν : ν ∈ posRootCone P b) (hν0 : ν ≠ 0) : ∃ k ∈ b.support, 0 < P.coroot' k ν := by
  obtain ⟨f, rfl⟩ := (mem_posRootCone P b).mp hν
  by_contra hcon
  simp only [not_exists, not_and, not_lt] at hcon
  have hpos := P.rootForm_pos_of_ne_zero (Submodule.sum_mem _ fun j _ =>
    Submodule.smul_of_tower_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)) hν0
  rw [map_sum] at hpos
  refine absurd hpos (not_lt.mpr (Finset.sum_nonpos fun k hk => ?_))
  rw [map_nsmul, nsmul_eq_mul]
  refine mul_nonpos_of_nonneg_of_nonpos (Nat.cast_nonneg _) ?_
  have h2 := two_mul_rootForm_root' (P := P) k (∑ j ∈ b.support, f j • P.root j)
  have hsymm : P.RootForm (∑ j ∈ b.support, f j • P.root j) (P.root k) =
      P.RootForm (P.root k) (∑ j ∈ b.support, f j • P.root j) := by
    rw [P.rootForm_apply_apply, P.rootForm_apply_apply]
    exact Finset.sum_congr rfl fun _ _ => mul_comm _ _
  have hk0 : 0 < P.RootForm (P.root k) (P.root k) :=
    P.rootForm_pos_of_ne_zero (Submodule.subset_span ⟨k, rfl⟩) (P.ne_zero k)
  rw [hsymm]
  nlinarith [hcon k hk]

variable [P.IsCrystallographic]

lemma pairingIn_indexEquiv (i j : ι) :
    P.pairingIn ℤ (σ.indexEquiv i) (σ.indexEquiv j) = P.pairingIn ℤ i j :=
  TauCeti.pairingIn_indexEquiv ℤ (σ : P.Equiv P).toHom i j

lemma pairingIn_of_root_eq_add {i j k : ι} (h : P.root k = P.root i + P.root j) (l : ι) :
    P.pairingIn ℤ k l = P.pairingIn ℤ i l + P.pairingIn ℤ j l := by
  apply (algebraMap ℤ R).injective_int
  rw [map_add, P.algebraMap_pairingIn, P.algebraMap_pairingIn, P.algebraMap_pairingIn,
    ← P.root_coroot_eq_pairing, ← P.root_coroot_eq_pairing, ← P.root_coroot_eq_pairing, h,
    map_add, LinearMap.add_apply]

lemma pairingIn_reflectionPerm_left (a x c : ι) :
    P.pairingIn ℤ (P.reflectionPerm a x) c =
      P.pairingIn ℤ x c - P.pairingIn ℤ x a * P.pairingIn ℤ a c := by
  apply (algebraMap ℤ R).injective_int
  rw [map_sub, map_mul, P.algebraMap_pairingIn, P.algebraMap_pairingIn, P.algebraMap_pairingIn,
    P.algebraMap_pairingIn, ← P.root_coroot_eq_pairing, P.root_reflectionPerm,
    P.reflection_apply_root, map_sub, map_smul, LinearMap.sub_apply, LinearMap.smul_apply,
    P.root_coroot_eq_pairing, P.root_coroot_eq_pairing, smul_eq_mul]

lemma pairingIn_eq_zero_of_isOrthogonal {a c : ι} (h : P.IsOrthogonal a c) :
    P.pairingIn ℤ a c = 0 ∧ P.pairingIn ℤ c a = 0 := by
  constructor <;> apply (algebraMap ℤ R).injective_int <;>
    rw [P.algebraMap_pairingIn, map_zero]
  exacts [h.1, h.2]

lemma card_smul_sum_orbitFinset [DecidableEq ι] (hσ3 : σ ^ 3 = 1) (i k : ι) :
    (orbitFinset σ i).card • ∑ k' ∈ orbitFinset σ k, P.pairingIn ℤ i k' =
      (orbitFinset σ k).card • ∑ γ ∈ orbitFinset σ i, P.pairingIn ℤ γ k := by
  have hB : ∀ γ, ∑ k' ∈ orbitFinset σ k, P.pairingIn ℤ (σ.indexEquiv γ) k' =
      ∑ k' ∈ orbitFinset σ k, P.pairingIn ℤ γ k' := by
    intro γ
    rw [← sum_orbitFinset_comp σ hσ3 k (fun k' => P.pairingIn ℤ (σ.indexEquiv γ) k')]
    exact Finset.sum_congr rfl fun k' _ => pairingIn_indexEquiv σ γ k'
  have hA : ∀ k', ∑ γ ∈ orbitFinset σ i, P.pairingIn ℤ γ (σ.indexEquiv k') =
      ∑ γ ∈ orbitFinset σ i, P.pairingIn ℤ γ k' := by
    intro k'
    rw [← sum_orbitFinset_comp σ hσ3 i (fun γ => P.pairingIn ℤ γ (σ.indexEquiv k'))]
    exact Finset.sum_congr rfl fun γ _ => pairingIn_indexEquiv σ γ k'
  rw [← sum_orbitFinset_of_invariant σ i
      (fun γ => ∑ k' ∈ orbitFinset σ k, P.pairingIn ℤ γ k') hB,
    ← sum_orbitFinset_of_invariant σ k (fun k' => ∑ γ ∈ orbitFinset σ i, P.pairingIn ℤ γ k') hA,
    Finset.sum_comm]

variable [Finite ι] [IsDomain R]

lemma height_indexEquiv (hσ : ∀ i ∈ b.support, σ.indexEquiv i ∈ b.support) (i : ι) :
    b.height (σ.indexEquiv i) = b.height i := by
  refine RootPairing.Base.induction_add (b := b) i
    (p := fun i => b.height (σ.indexEquiv i) = b.height i) ?_ ?_ ?_
  · intro j hj
    let _ := P.indexNeg
    have h := TauCeti.indexEquiv_reflectionPerm (σ : P.Equiv P).toHom j j
    rw [h]
    change b.height (-(σ.indexEquiv j)) = b.height (-j)
    rw [b.height_reflectionPerm_self, b.height_reflectionPerm_self, hj]
  · intro j hj
    rw [b.height_one_of_mem_support (hσ j hj), b.height_one_of_mem_support hj]
  · intro j k l hl hj hk
    have hl' : P.root (σ.indexEquiv l) = P.root (σ.indexEquiv j) + P.root (σ.indexEquiv k) :=
      (TauCeti.root_indexEquiv_eq_add_iff (σ : P.Equiv P) l j k).mpr hl
    rw [b.height_add hl', b.height_add hl, hj, b.height_one_of_mem_support (hσ k hk),
      b.height_one_of_mem_support hk]

lemma isPos_indexEquiv_iff (hσ : ∀ i ∈ b.support, σ.indexEquiv i ∈ b.support) (i : ι) :
    b.IsPos (σ.indexEquiv i) ↔ b.IsPos i := by
  rw [b.isPos_iff, b.isPos_iff, height_indexEquiv b σ hσ]

theorem pairingIn_indexEquiv_eq_zero [Module.IsTorsionFree R M]
    (hσ : ∀ i ∈ b.support, σ.indexEquiv i ∈ b.support) (hσ3 : σ ^ 3 = 1) {i : ι}
    (hi : σ.indexEquiv i ≠ i) : P.pairingIn ℤ i (σ.indexEquiv i) = 0 := by
  set s := σ.indexEquiv with hs
  have h3 : ∀ j, s (s (s j)) = j := indexEquiv_cube σ hσ3
  have hh : ∀ j, b.height (s j) = b.height j := height_indexEquiv b σ hσ
  have hp : ∀ j k, P.pairingIn ℤ (s j) (s k) = P.pairingIn ℤ j k := pairingIn_indexEquiv σ
  have hrootadd : ∀ j k l, P.root l = P.root j + P.root k →
      P.root (s l) = P.root (s j) + P.root (s k) := fun j k l h =>
    (TauCeti.root_indexEquiv_eq_add_iff (σ : P.Equiv P) l j k).mpr h
  have hneg : ∀ j k, P.root j = -P.root k → b.height j = -b.height k := by
    intro j k hjk
    let _ := P.indexNeg
    have : j = -k := P.root.injective (by
      rw [hjk]
      change -P.root k = P.root (P.reflectionPerm k k)
      rw [P.root_reflectionPerm, P.reflection_apply_self])
    rw [this, b.height_reflectionPerm_self]
  rcases lt_trichotomy (P.pairingIn ℤ i (s i)) 0 with ha | ha | ha
  · exfalso
    have ha' : P.pairingIn ℤ (s i) i < 0 := by
      have hne : P.pairingIn ℤ (s i) i ≠ 0 := fun h0 =>
        ha.ne ((P.pairingIn_eq_zero_iff (S := ℤ)).mp h0)
      have hnpos : ¬ 0 < P.pairingIn ℤ (s i) i := fun hpos =>
        absurd ((P.zero_lt_pairingIn_iff' ℤ).mp hpos) (not_lt.mpr ha.le)
      omega
    have hne1 : P.root i ≠ -P.root (s i) := fun h => by
      have := hneg _ _ h
      rw [hh] at this
      exact height_ne_zero b i (by omega)
    obtain ⟨k₁, hk₁⟩ := P.root_add_root_mem_of_pairingIn_neg ha hne1
    have hpk : P.pairingIn ℤ k₁ (s (s i)) < 0 := by
      rw [pairingIn_of_root_eq_add hk₁]
      have e1 : P.pairingIn ℤ i (s (s i)) = P.pairingIn ℤ (s i) i := by
        rw [← hp i (s (s i)), h3]
      have e2 : P.pairingIn ℤ (s i) (s (s i)) = P.pairingIn ℤ i (s i) := hp i (s i)
      rw [e1, e2]
      omega
    have hhk₁ : b.height k₁ = 2 * b.height i := by
      rw [b.height_add hk₁, hh]; ring
    have hne2 : P.root k₁ ≠ -P.root (s (s i)) := fun h => by
      have := hneg _ _ h
      rw [hh, hh, hhk₁] at this
      exact height_ne_zero b i (by omega)
    obtain ⟨m, hm⟩ := P.root_add_root_mem_of_pairingIn_neg hpk hne2
    have hsm : s m = m := by
      apply P.root.injective
      rw [hrootadd _ _ _ hm, hrootadd _ _ _ hk₁, h3, hm, hk₁]
      abel
    have hθ : P.pairingIn ℤ m m = 3 * P.pairingIn ℤ i m := by
      rw [pairingIn_of_root_eq_add hm, pairingIn_of_root_eq_add hk₁]
      have e1 : P.pairingIn ℤ (s i) m = P.pairingIn ℤ i m := by
        conv_lhs => rw [← hsm]
        exact hp i m
      have e2 : P.pairingIn ℤ (s (s i)) m = P.pairingIn ℤ i m := by
        conv_lhs => rw [← hsm, ← hsm]
        rw [hp, hp]
      rw [e1, e2]
      ring
    rw [P.pairingIn_same] at hθ
    omega
  · exact ha
  · exfalso
    obtain ⟨k, hk⟩ := P.root_sub_root_mem_of_pairingIn_pos ha (fun h => hi h.symm)
    have := b.height_sub hk
    rw [hh] at this
    exact height_ne_zero b k (by omega)

lemma isOrthogonal_indexEquiv [Module.IsTorsionFree R M]
    (hσ : ∀ i ∈ b.support, σ.indexEquiv i ∈ b.support) (hσ3 : σ ^ 3 = 1) {i : ι}
    (hi : σ.indexEquiv i ≠ i) : P.IsOrthogonal i (σ.indexEquiv i) := by
  have h0 := pairingIn_indexEquiv_eq_zero b σ hσ hσ3 hi
  have h1 : P.pairingIn ℤ (σ.indexEquiv i) i = 0 := (P.pairingIn_eq_zero_iff (S := ℤ)).mp h0
  refine ⟨?_, ?_⟩
  · rw [← P.algebraMap_pairingIn ℤ, h0, map_zero]
  · rw [← P.algebraMap_pairingIn ℤ, h1, map_zero]

lemma isOrthogonal_indexEquiv_sq [Module.IsTorsionFree R M]
    (hσ : ∀ i ∈ b.support, σ.indexEquiv i ∈ b.support) (hσ3 : σ ^ 3 = 1) {i : ι}
    (hi : σ.indexEquiv i ≠ i) : P.IsOrthogonal i (σ.indexEquiv (σ.indexEquiv i)) := by
  have h3 := indexEquiv_cube σ hσ3
  have hne : σ.indexEquiv (σ.indexEquiv (σ.indexEquiv i)) ≠ σ.indexEquiv (σ.indexEquiv i) := by
    rw [h3]
    intro h
    apply hi
    have := congrArg σ.indexEquiv h
    rw [h3] at this
    exact this
  have := isOrthogonal_indexEquiv b σ hσ hσ3 hne
  rw [h3] at this
  exact this.symm

lemma orbitReflection_mem_fixedWeylGroup [Module.IsTorsionFree R M]
    (hσ : ∀ i ∈ b.support, σ.indexEquiv i ∈ b.support) (hσ3 : σ ^ 3 = 1) (j : ι) :
    orbitReflection σ j ∈ fixedWeylGroup σ := by
  rw [mem_fixedWeylGroup]
  have h3 := indexEquiv_cube σ hσ3
  have hconj : σ * (orbitReflection σ j : P.Aut) * σ⁻¹ =
      (RootPairing.weylGroup.ofIdx P (σ.indexEquiv j) : P.Aut) *
        RootPairing.weylGroup.ofIdx P (σ.indexEquiv (σ.indexEquiv j)) *
          RootPairing.weylGroup.ofIdx P j := by
    simp only [orbitReflection, Subgroup.coe_mul]
    rw [show σ * (↑(RootPairing.weylGroup.ofIdx P j) * ↑(RootPairing.weylGroup.ofIdx P
        (σ.indexEquiv j)) * ↑(RootPairing.weylGroup.ofIdx P (σ.indexEquiv (σ.indexEquiv j)))) *
        σ⁻¹ = (σ * ↑(RootPairing.weylGroup.ofIdx P j) * σ⁻¹) *
          (σ * ↑(RootPairing.weylGroup.ofIdx P (σ.indexEquiv j)) * σ⁻¹) *
          (σ * ↑(RootPairing.weylGroup.ofIdx P (σ.indexEquiv (σ.indexEquiv j))) * σ⁻¹) by group]
    rw [conj_ofIdx, conj_ofIdx, conj_ofIdx, h3]
  have hcomm : (RootPairing.weylGroup.ofIdx P (σ.indexEquiv j) : P.Aut) *
      RootPairing.weylGroup.ofIdx P (σ.indexEquiv (σ.indexEquiv j)) *
        RootPairing.weylGroup.ofIdx P j = orbitReflection σ j := by
    by_cases hj : σ.indexEquiv j = j
    · rw [orbitReflection, hj, hj, Subgroup.coe_mul, Subgroup.coe_mul]
    · have c1 := RootPairing.weylGroup.commute_ofIdx_of_isOrthogonal P
        (isOrthogonal_indexEquiv b σ hσ hσ3 hj)
      have c2 := RootPairing.weylGroup.commute_ofIdx_of_isOrthogonal P
        (isOrthogonal_indexEquiv_sq b σ hσ hσ3 hj)
      have key : RootPairing.weylGroup.ofIdx P (σ.indexEquiv j) *
          RootPairing.weylGroup.ofIdx P (σ.indexEquiv (σ.indexEquiv j)) *
            RootPairing.weylGroup.ofIdx P j = orbitReflection σ j := by
        rw [orbitReflection, mul_assoc, ← c2.eq, ← mul_assoc, ← c1.eq]
      rw [← key, Subgroup.coe_mul, Subgroup.coe_mul]
  calc (orbitReflection σ j : P.Aut) * σ = σ * (orbitReflection σ j : P.Aut) * σ⁻¹ * σ := by
        rw [hconj, hcomm]
    _ = σ * orbitReflection σ j := by group

lemma isPos_and_height_orbitReflection [DecidableEq ι] [P.IsReduced] [Module.IsTorsionFree R M]
    (hσ : ∀ i ∈ b.support, σ.indexEquiv i ∈ b.support) (hσ3 : σ ^ 3 = 1) {i k : ι}
    (hi : b.IsPos i) (hib : i ∉ b.support) (hk : k ∈ b.support) :
    b.IsPos (P.weylGroupToPerm (orbitReflection σ k) i) ∧
      b.height (P.weylGroupToPerm (orbitReflection σ k) i) =
        b.height i - ∑ k' ∈ orbitFinset σ k, P.pairingIn ℤ i k' := by
  have hne : ∀ {l}, l ∈ b.support → i ≠ l := fun hl h => hib (h ▸ hl)
  by_cases hk1 : σ.indexEquiv k = k
  · have hO : orbitFinset σ k = {k} := by simp [orbitFinset, hk1]
    rw [orbitReflection_of_eq σ hk1, weylGroupToPerm_ofIdx, hO, Finset.sum_singleton,
      height_reflectionPerm_of_mem_support P b hk]
    exact ⟨hi.reflectionPerm hk (hne hk), rfl⟩
  have hk1b := hσ k hk
  have hk2b := hσ _ hk1b
  have o01 := pairingIn_eq_zero_of_isOrthogonal (isOrthogonal_indexEquiv b σ hσ hσ3 hk1)
  have o02 := pairingIn_eq_zero_of_isOrthogonal (isOrthogonal_indexEquiv_sq b σ hσ hσ3 hk1)
  have hk1' : σ.indexEquiv (σ.indexEquiv k) ≠ σ.indexEquiv k :=
    fun h => hk1 (σ.indexEquiv.injective h)
  have o12 := pairingIn_eq_zero_of_isOrthogonal (isOrthogonal_indexEquiv b σ hσ hσ3 hk1')
  have hk2 : σ.indexEquiv (σ.indexEquiv k) ≠ k := by
    intro h
    have := congrArg σ.indexEquiv h
    rw [indexEquiv_cube σ hσ3] at this
    exact hk1 this.symm
  have hO : ∑ k' ∈ orbitFinset σ k, P.pairingIn ℤ i k' = P.pairingIn ℤ i k +
      P.pairingIn ℤ i (σ.indexEquiv k) + P.pairingIn ℤ i (σ.indexEquiv (σ.indexEquiv k)) := by
    rw [orbitFinset, Finset.sum_insert, Finset.sum_insert, Finset.sum_singleton, add_assoc]
    · simpa using hk1'.symm
    · simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨fun h => hk1 h.symm, fun h => hk2 h.symm⟩
  set k₁ := σ.indexEquiv k
  set k₂ := σ.indexEquiv k₁
  set i₁ := P.reflectionPerm k₂ i with hi₁
  set i₂ := P.reflectionPerm k₁ i₁ with hi₂
  have hfix : ∀ {a c : ι}, P.pairingIn ℤ a c = 0 → P.reflectionPerm a c = c := fun h =>
    P.reflectionPerm_eq_of_pairing_eq_zero' (by rw [← P.algebraMap_pairingIn ℤ, h, map_zero])
  have hp₁ : b.IsPos i₁ := hi.reflectionPerm hk2b (hne hk2b)
  have hi₁ne : i₁ ≠ k₁ := by
    intro h
    apply hib
    have : i = P.reflectionPerm k₂ k₁ := by
      rw [← h, hi₁]
      exact (P.reflectionPerm_involutive k₂ i).symm
    rw [this, hfix o12.2]
    exact hk1b
  have hp₂ : b.IsPos i₂ := hp₁.reflectionPerm hk1b hi₁ne
  have hi₂ne : i₂ ≠ k := by
    intro h
    apply hib
    have h1 : i₁ = P.reflectionPerm k₁ k := by
      rw [← h, hi₂]
      exact (P.reflectionPerm_involutive k₁ i₁).symm
    rw [hfix o01.2] at h1
    have : i = P.reflectionPerm k₂ k := by
      rw [← h1, hi₁]
      exact (P.reflectionPerm_involutive k₂ i).symm
    rw [this, hfix o02.2]
    exact hk
  have hπ : P.weylGroupToPerm (orbitReflection σ k) i = P.reflectionPerm k i₂ := by
    simp only [orbitReflection, map_mul, Equiv.Perm.mul_apply, weylGroupToPerm_ofIdx]
    rfl
  rw [hπ]
  refine ⟨hp₂.reflectionPerm hk hi₂ne, ?_⟩
  rw [height_reflectionPerm_of_mem_support P b hk, hi₂, height_reflectionPerm_of_mem_support P b hk1b,
    hi₁, height_reflectionPerm_of_mem_support P b hk2b, pairingIn_reflectionPerm_left,
    pairingIn_reflectionPerm_left, pairingIn_reflectionPerm_left, o12.2, o02.2, o01.2, hO]
  ring

omit [IsDomain R] in
theorem exists_mem_fixedWeylGroup_mem_support [P.IsReduced] [Module.IsTorsionFree R M]
    [LinearOrder R] [IsStrictOrderedRing R]
    (hσ : ∀ i ∈ b.support, σ.indexEquiv i ∈ b.support) (hσ3 : σ ^ 3 = 1) (i : ι) :
    ∃ u ∈ fixedWeylGroup σ, P.weylGroupToPerm u i ∈ b.support := by
  classical
  have : Fintype ι := Fintype.ofFinite ι
  have hpos : ∀ n : ℕ, ∀ i, b.IsPos i → b.height i ≤ n →
      ∃ u ∈ fixedWeylGroup σ, P.weylGroupToPerm u i ∈ b.support := by
    intro n
    induction n with
    | zero =>
      intro i hi hn
      have := (b.isPos_iff).mp hi
      omega
    | succ n ih =>
      intro i hi hn
      by_cases hib : i ∈ b.support
      · exact ⟨1, one_mem _, by simpa using hib⟩
      have hposO : ∀ γ ∈ orbitFinset σ i, γ ∈ posRoots P b := by
        intro γ hγ
        rw [mem_posRoots]
        rcases (mem_orbitFinset σ).mp hγ with rfl | rfl | rfl
        · exact hi
        · exact (isPos_indexEquiv_iff b σ hσ _).mpr hi
        · exact (isPos_indexEquiv_iff b σ hσ _).mpr ((isPos_indexEquiv_iff b σ hσ _).mpr hi)
      have hν : ∑ γ ∈ orbitFinset σ i, P.root γ ∈ posRootCone P b :=
        AddSubmonoid.sum_mem _ fun γ hγ => root_mem_posRootCone_of_mem_posRoots P b (hposO γ hγ)
      have hν0 : ∑ γ ∈ orbitFinset σ i, P.root γ ≠ 0 :=
        sum_root_ne_zero_of_mem_posRoots P b (f := id) ⟨i, mem_orbitFinset_self σ i⟩ hposO
      obtain ⟨k, hk, hkpos⟩ := exists_mem_support_pos_coroot' b hν hν0
      have hA : 0 < ∑ γ ∈ orbitFinset σ i, P.pairingIn ℤ γ k := by
        have hc : P.coroot' k (∑ γ ∈ orbitFinset σ i, P.root γ) =
            ((∑ γ ∈ orbitFinset σ i, P.pairingIn ℤ γ k : ℤ) : R) := by
          rw [map_sum, Int.cast_sum]
          refine Finset.sum_congr rfl fun γ _ => ?_
          rw [P.root_coroot'_eq_pairing, ← P.algebraMap_pairingIn ℤ, algebraMap_int_eq,
            eq_intCast]
        rw [hc] at hkpos
        exact_mod_cast hkpos
      have hS : 0 < ∑ k' ∈ orbitFinset σ k, P.pairingIn ℤ i k' := by
        have hc := card_smul_sum_orbitFinset σ hσ3 i k
        have hci : 0 < (orbitFinset σ i).card :=
          Finset.card_pos.mpr ⟨i, mem_orbitFinset_self σ i⟩
        have hck : 0 < (orbitFinset σ k).card :=
          Finset.card_pos.mpr ⟨k, mem_orbitFinset_self σ k⟩
        rw [nsmul_eq_mul, nsmul_eq_mul] at hc
        by_contra hle
        rw [not_lt] at hle
        have h1 : ((orbitFinset σ i).card : ℤ) * ∑ k' ∈ orbitFinset σ k, P.pairingIn ℤ i k' ≤ 0 :=
          mul_nonpos_of_nonneg_of_nonpos (by positivity) hle
        have h2 : 0 < ((orbitFinset σ k).card : ℤ) * ∑ γ ∈ orbitFinset σ i, P.pairingIn ℤ γ k :=
          mul_pos (by exact_mod_cast hck) hA
        linarith
      obtain ⟨hjpos, hjh⟩ := isPos_and_height_orbitReflection b σ hσ hσ3 hi hib hk
      obtain ⟨u, hu, hu'⟩ := ih _ hjpos (by omega)
      refine ⟨u * orbitReflection σ k, mul_mem hu (orbitReflection_mem_fixedWeylGroup b σ hσ hσ3 k),
        ?_⟩
      rwa [map_mul, Equiv.Perm.mul_apply]
  rcases RootPairing.Base.IsPos.or_neg b i with hi | hi
  · exact hpos _ i hi (Int.self_le_toNat _)
  obtain ⟨u, hu, hj⟩ := hpos _ (P.reflectionPerm i i) hi (Int.self_le_toNat _)
  obtain ⟨j, hjdef⟩ : ∃ j, P.weylGroupToPerm u (P.reflectionPerm i i) = j := ⟨_, rfl⟩
  rw [hjdef] at hj
  have hui : P.weylGroupToPerm u i = P.reflectionPerm j j := by
    apply P.root.injective
    rw [P.root_reflectionPerm, P.reflection_apply_self, ← hjdef, ← P.weylGroup_apply_root,
      ← P.weylGroup_apply_root, P.root_reflectionPerm, P.reflection_apply_self, smul_neg, neg_neg]
  refine ⟨orbitReflection σ j * u, mul_mem (orbitReflection_mem_fixedWeylGroup b σ hσ hσ3 j) hu, ?_⟩
  rw [map_mul, Equiv.Perm.mul_apply, hui]
  have hfix : ∀ {a c : ι}, P.pairingIn ℤ a c = 0 → P.reflectionPerm a c = c := fun h =>
    P.reflectionPerm_eq_of_pairing_eq_zero' (by rw [← P.algebraMap_pairingIn ℤ, h, map_zero])
  by_cases hj1 : σ.indexEquiv j = j
  · rw [orbitReflection_of_eq σ hj1, weylGroupToPerm_ofIdx, P.reflectionPerm_self]
    exact hj
  have o01 := pairingIn_eq_zero_of_isOrthogonal (isOrthogonal_indexEquiv b σ hσ hσ3 hj1)
  have o02 := pairingIn_eq_zero_of_isOrthogonal (isOrthogonal_indexEquiv_sq b σ hσ hσ3 hj1)
  simp only [orbitReflection, map_mul, Equiv.Perm.mul_apply, weylGroupToPerm_ofIdx]
  rw [reflectionPerm_neg_eq, hfix o02.2, reflectionPerm_neg_eq, hfix o01.2, P.reflectionPerm_self]
  exact hj

end CharZero

end CFSG.RootPairing
