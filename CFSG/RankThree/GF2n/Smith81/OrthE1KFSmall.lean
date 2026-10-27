module

public import CFSG.RankThree.GF2n.Smith81.OrthE1Steps

public section

namespace CFSG.RankThree.GF2n.Smith81.Smith23E1

open CFSG CFSG.Open CFSG.Open.StatedAPI CFSG.Assembly.LowTwoRank CFSG.RankThree.GF2n
  CFSG.RankThree.GF2n.Stroth80 CFSG.RankThree.GF2n.Smith81
open CFSG.ComponentClassification.RankTwoClassical
open scoped Matrix

theorem kfs_card_eq_two_pow (K : Type) [Field K] [Finite K] [CharP K 2] :
    ∃ k : ℕ, 1 ≤ k ∧ Nat.card K = 2 ^ k := by
  letI := Fintype.ofFinite K
  obtain ⟨n, -, hn⟩ := FiniteField.card K 2
  have hcard : Nat.card K = 2 ^ (n : ℕ) := by rw [Nat.card_eq_fintype_card, hn]
  have h1 : 1 < Nat.card K := Finite.one_lt_card
  refine ⟨(n : ℕ), ?_, hcard⟩
  rcases Nat.eq_zero_or_pos (n : ℕ) with h0 | h0
  · rw [h0, pow_zero] at hcard
    omega
  · exact h0

theorem kfs_odd_sq_sub_one {q : ℕ} (h2 : 2 ∣ q) (h1 : 1 ≤ q) : Odd (q ^ 2 - 1) := by
  have hd : 2 ∣ q ^ 2 := dvd_pow h2 two_ne_zero
  have hp : 1 ≤ q ^ 2 := Nat.one_le_pow _ _ h1
  rw [Nat.odd_iff]
  generalize q ^ 2 = x at hd hp ⊢
  omega

theorem kfs_odd_pow_four_sub_one {q : ℕ} (h2 : 2 ∣ q) (h1 : 1 ≤ q) : Odd (q ^ 4 - 1) := by
  have hd : 2 ∣ q ^ 4 := dvd_pow h2 (by norm_num)
  have hp : 1 ≤ q ^ 4 := Nat.one_le_pow _ _ h1
  rw [Nat.odd_iff]
  generalize q ^ 4 = x at hd hp ⊢
  omega

theorem kfs_sylow_two_card {G : Type*} [Group G] [Finite G] {a m : ℕ} (hm : Odd m)
    (hG : Nat.card G = 2 ^ a * m) (P : Sylow 2 G) : Nat.card P = 2 ^ a := by
  have hm0 : m ≠ 0 := fun h => by simp [h] at hm
  rw [Sylow.card_eq_multiplicity, hG, Nat.factorization_mul (by positivity) hm0,
    Finsupp.add_apply, Nat.factorization_pow, Finsupp.smul_apply,
    Nat.Prime.factorization_self Nat.prime_two,
    Nat.factorization_eq_zero_of_not_dvd
      (fun h => (Nat.not_even_iff_odd.2 hm) (even_iff_two_dvd.2 h)),
    smul_eq_mul, mul_one, add_zero]

theorem kfs_prod_isPerfect (A B : Type) [Group A] [Group B] [Group.IsPerfect A]
    [Group.IsPerfect B] : Group.IsPerfect (A × B) := by
  rw [Group.isPerfect_def, _root_.commutator_def]
  have hA : ⁅(⊤ : Subgroup A), (⊤ : Subgroup A)⁆ = ⊤ := by
    rw [← _root_.commutator_def]
    exact Group.isPerfect_def.1 inferInstance
  have hB : ⁅(⊤ : Subgroup B), (⊤ : Subgroup B)⁆ = ⊤ := by
    rw [← _root_.commutator_def]
    exact Group.isPerfect_def.1 inferInstance
  have htop : (⊤ : Subgroup (A × B)) = (⊤ : Subgroup A).prod (⊤ : Subgroup B) := by
    ext x
    simp
  rw [htop, Subgroup.commutator_prod_prod, hA, hB]

theorem kfs_omega4Basic_of_parts {ι : Type} [Fintype ι] [DecidableEq ι] {K : Type} [Field K]
    [Finite K] [CharP K 2] {f : (ι → K) → K} (hperf : Group.IsPerfect ↥(StatedOmega f))
    (hcen : Subgroup.center ↥(StatedOmega f) = ⊥) {k m : ℕ} (hq : Nat.card K = 2 ^ k)
    (hm : Odd m) (hcard : Nat.card ↥(StatedOmega f) = Nat.card K ^ 2 * m) :
    Omega4BasicFor K f := by
  unfold Omega4BasicFor
  refine ⟨Subgroup.isPerfect_iff.1 hperf, hcen, fun P => ?_⟩
  have h2 : Nat.card K ^ 2 = 2 ^ (2 * k) := by rw [hq, ← pow_mul, mul_comm]
  rw [h2] at hcard ⊢
  exact kfs_sylow_two_card hm hcard P

theorem kfs_natCard_plus {K : Type} [Field K] [Finite K] [CharP K 2] (h4 : 4 ≤ Nat.card K) :
    Nat.card ↥(StatedOmega (StatedQuadPlus 2 K)) = Nat.card K ^ 2 * (Nat.card K ^ 2 - 1) ^ 2 := by
  have h := orthE2_card_omega_plus_two h4
  have hle : 1 ≤ Nat.card K ^ 2 := Nat.one_le_pow _ _ (by omega)
  have key : ((Nat.card ↥(StatedOmega (StatedQuadPlus 2 K)) : ℕ) : ℤ) =
      ((Nat.card K ^ 2 * (Nat.card K ^ 2 - 1) ^ 2 : ℕ) : ℤ) := by
    rw [h]
    push_cast [Nat.cast_sub hle]
    ring
  exact_mod_cast key

theorem kfs_natCard_minus {K : Type} [Field K] [Finite K] [CharP K 2] {b c : K}
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) :
    Nat.card ↥(StatedOmega (StatedQuadMinus 2 K b c)) = Nat.card K ^ 2 * (Nat.card K ^ 4 - 1) := by
  have h := orthE2_card_omega_minus_two hirr
  have hle : 1 ≤ Nat.card K ^ 4 := Nat.one_le_pow _ _ Nat.card_pos
  have key : ((Nat.card ↥(StatedOmega (StatedQuadMinus 2 K b c)) : ℕ) : ℤ) =
      ((Nat.card K ^ 2 * (Nat.card K ^ 4 - 1) : ℕ) : ℤ) := by
    rw [h]
    push_cast [Nat.cast_sub hle]
    ring
  exact_mod_cast key

theorem kfs_center_statedSL_two (K : Type) [Field K] [Finite K] [CharP K 2] :
    Subgroup.center ↥(StatedSL 2 K) = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  rw [Subgroup.mem_bot]
  obtain ⟨A, rfl⟩ := (specialLinearGroupEquivStatedSL 2 K).surjective x
  have hA : A ∈ Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) K) := by
    rw [Subgroup.mem_center_iff] at hx ⊢
    intro g
    apply (specialLinearGroupEquivStatedSL 2 K).injective
    simpa only [map_mul] using hx (specialLinearGroupEquivStatedSL 2 K g)
  have hmem := Subgroup.mem_map_of_mem
    (specialLinearGroupEquivStatedSL 2 K : Matrix.SpecialLinearGroup (Fin 2) K →* StatedSL 2 K) hA
  rw [map_center_eq_statedScalars 2 K, statedScalars_subgroupOf_statedSL_two_eq_bot,
    Subgroup.mem_bot] at hmem
  exact hmem

theorem kfs_center_plus {K : Type} [Field K] [Finite K] [CharP K 2] (h4 : 4 ≤ Nat.card K) :
    Subgroup.center ↥(StatedOmega (StatedQuadPlus 2 K)) = ⊥ := by
  obtain ⟨e⟩ := statedOmega_plus_four_nonempty_equiv K h4
  rw [eq_bot_iff]
  intro x hx
  rw [Subgroup.mem_bot]
  have hy : e x ∈ Subgroup.center (↥(StatedSL 2 K) × ↥(StatedSL 2 K)) := by
    rw [Subgroup.mem_center_iff] at hx ⊢
    intro g
    obtain ⟨g', rfl⟩ := e.surjective g
    simpa only [map_mul] using congrArg e (hx g')
  rw [Subgroup.center_prod, kfs_center_statedSL_two K] at hy
  obtain ⟨h1, h2⟩ := Subgroup.mem_prod.1 hy
  rw [Subgroup.mem_bot] at h1 h2
  apply e.injective
  rw [map_one]
  exact Prod.ext h1 h2

theorem kfs_center_minus {K : Type} [Field K] [Finite K] [CharP K 2] {b c : K}
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) :
    Subgroup.center ↥(StatedOmega (StatedQuadMinus 2 K b c)) = ⊥ := by
  haveI := ORigid.isSimpleGroup_statedOmega_quadMinus_of_two_le
    (m := 2) le_rfl hirr
  haveI : Group.IsPerfect ↥(StatedOmega (StatedQuadMinus 2 K b c)) :=
    Group.isPerfect_def.2
      (ORigid.commutator_statedOmega_quadMinus_eq_top
        (m := 2) le_rfl hirr)
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal
    (Subgroup.center ↥(StatedOmega (StatedQuadMinus 2 K b c))) with h | h
  · exact h
  · exact absurd (Subgroup.center_eq_top_iff.1 h)
      (Group.IsPerfect.not_isMulCommutative _)

theorem kfs_perfect_plus {K : Type} [Field K] [Finite K] [CharP K 2] (h4 : 4 ≤ Nat.card K) :
    Group.IsPerfect ↥(StatedOmega (StatedQuadPlus 2 K)) := by
  obtain ⟨e⟩ := statedOmega_plus_four_nonempty_equiv K h4
  haveI : Group.IsPerfect ↥(StatedSL 2 K) :=
    (statedSL_quasisimple_of_card 2 K le_rfl h4).1
  haveI := kfs_prod_isPerfect ↥(StatedSL 2 K) ↥(StatedSL 2 K)
  exact Group.IsPerfect.ofSurjective (f := e.symm.toMonoidHom) e.symm.surjective

theorem kfs_perfect_minus {K : Type} [Field K] [Finite K] [CharP K 2] {b c : K}
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) :
    Group.IsPerfect ↥(StatedOmega (StatedQuadMinus 2 K b c)) :=
  Group.isPerfect_def.2
    (ORigid.commutator_statedOmega_quadMinus_eq_top
      (m := 2) le_rfl hirr)

theorem omega4Basic_holds : Omega4BasicStatement := by
  intro K _ _ _ h4
  obtain ⟨k, hk, hq⟩ := kfs_card_eq_two_pow K
  have hK2 : 2 ∣ Nat.card K := by
    rw [hq]
    exact dvd_pow_self 2 (by omega)
  have hK1 : 1 ≤ Nat.card K := by omega
  refine ⟨?_, fun b c hirr => ?_⟩
  · exact kfs_omega4Basic_of_parts (kfs_perfect_plus h4) (kfs_center_plus h4) hq
      ((kfs_odd_sq_sub_one hK2 hK1).pow) (kfs_natCard_plus h4)
  · exact kfs_omega4Basic_of_parts (kfs_perfect_minus hirr) (kfs_center_minus hirr) hq
      (kfs_odd_pow_four_sub_one hK2 hK1) (kfs_natCard_minus hirr)

local instance kfsMulAction (K : Type) [Field K] : MulAction ↥(StatedSL 2 K) (Fin 2 → K) where
  smul g v := Matrix.mulVec ((g : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) v
  one_smul v := by
    show Matrix.mulVec ((((1 : ↥(StatedSL 2 K)) : GL (Fin 2) K)) : Matrix (Fin 2) (Fin 2) K) v = v
    simp
  mul_smul g h v := by
    show Matrix.mulVec ((((g * h : ↥(StatedSL 2 K)) : GL (Fin 2) K)) :
        Matrix (Fin 2) (Fin 2) K) v =
      Matrix.mulVec ((((g : ↥(StatedSL 2 K)) : GL (Fin 2) K)) : Matrix (Fin 2) (Fin 2) K)
        (Matrix.mulVec ((((h : ↥(StatedSL 2 K)) : GL (Fin 2) K)) : Matrix (Fin 2) (Fin 2) K) v)
    rw [Matrix.mulVec_mulVec]
    simp

abbrev kfsMat {K : Type} [Field K] (g : ↥(StatedSL 2 K)) : Matrix (Fin 2) (Fin 2) K :=
  ((g : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K)

def kfsCol {K : Type} [Field K] (v w : Fin 2 → K) : Matrix (Fin 2) (Fin 2) K :=
  Matrix.of fun i j => ![v, w] j i

theorem kfs_det_col {K : Type} [Field K] (v w : Fin 2 → K) :
    (kfsCol v w).det = v 0 * w 1 - w 0 * v 1 := by
  rw [Matrix.det_fin_two]
  simp [kfsCol]

theorem kfs_sq_entries {K : Type} [Field K] [CharP K 2] (a b c d : K)
    (h1 : a * d - b * c = 1) (h2 : (a - 1) * (d - 1) - b * c = 0) :
    a * a + b * c = 1 ∧ a * b + b * d = 0 ∧ c * a + d * c = 0 ∧ c * b + d * d = 1 := by
  have two : (2 : K) = 0 := CharTwo.two_eq_zero
  have htr : a + d = 0 := by linear_combination h1 - h2 + two
  have hd : d = a := by linear_combination htr - a * two
  refine ⟨?_, ?_, ?_, ?_⟩
  · linear_combination h1 + (-a) * hd + b * c * two
  · linear_combination b * htr
  · linear_combination c * htr
  · linear_combination h1 + d * hd + b * c * two

theorem kfs_sq_matrix {K : Type} [Field K] [CharP K 2] (A : Matrix (Fin 2) (Fin 2) K)
    (h1 : A.det = 1) (h2 : (A - 1).det = 0) : A * A = 1 := by
  rw [Matrix.det_fin_two] at h1
  simp [Matrix.det_fin_two, Matrix.one_apply] at h2
  obtain ⟨e1, e2, e3, e4⟩ := kfs_sq_entries (A 0 0) (A 0 1) (A 1 0) (A 1 1) h1
    (by linear_combination h2)
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.one_apply] <;>
    first
    | linear_combination e1
    | linear_combination e2
    | linear_combination e3
    | linear_combination e4

theorem kfs_sq_eq_one {K : Type} [Field K] [CharP K 2] {g : ↥(StatedSL 2 K)} {v : Fin 2 → K}
    (hv : v ≠ 0) (hgv : g • v = v) : g * g = 1 := by
  have hdet : (kfsMat g).det = 1 := det_of_mem_statedSL g.2
  have hfix : kfsMat g *ᵥ v = v := hgv
  have hsing : (kfsMat g - 1).det = 0 := by
    apply Matrix.exists_mulVec_eq_zero_iff.1
    exact ⟨v, hv, by rw [Matrix.sub_mulVec, Matrix.one_mulVec, hfix, sub_self]⟩
  apply Subtype.ext
  apply Units.ext
  exact kfs_sq_matrix (kfsMat g) hdet hsing

theorem kfs_isPGroup_stab {K : Type} [Field K] [CharP K 2] {v : Fin 2 → K} (hv : v ≠ 0) :
    IsPGroup 2 ↥(MulAction.stabilizer ↥(StatedSL 2 K) v) := by
  unfold IsPGroup
  intro g
  refine ⟨1, ?_⟩
  have hg := kfs_sq_eq_one hv (MulAction.mem_stabilizer_iff.1 g.2)
  rw [show (2 : ℕ) ^ 1 = 2 from rfl, pow_two]
  exact Subtype.ext hg

theorem kfs_exists_fixed {K : Type} [Field K] [Finite K] [CharP K 2]
    (P : Subgroup ↥(StatedSL 2 K)) (hP : IsPGroup 2 ↥P) :
    ∃ v : Fin 2 → K, v ≠ 0 ∧ ∀ g ∈ P, g • v = v := by
  classical
  have hcard := IsPGroup.card_modEq_card_fixedPoints hP (Fin 2 → K)
  obtain ⟨k, hk, hq⟩ := kfs_card_eq_two_pow K
  have hK2 : 2 ∣ Nat.card K := by
    rw [hq]
    exact dvd_pow_self 2 (by omega)
  have hsq : Nat.card (Fin 2 → K) % 2 = 0 := by
    rw [Nat.card_fun]
    simp only [Nat.card_eq_fintype_card, Fintype.card_fin]
    exact Nat.mod_eq_zero_of_dvd (dvd_pow hK2 two_ne_zero)
  unfold Nat.ModEq at hcard
  have hmod : Nat.card ↑(MulAction.fixedPoints ↥P (Fin 2 → K)) % 2 = 0 := by
    omega
  by_contra hcon
  have hzero : ∀ x : Fin 2 → K, x ∈ MulAction.fixedPoints ↥P (Fin 2 → K) → x = 0 := by
    intro x hx
    by_contra hx0
    exact hcon ⟨x, hx0, fun g hg => MulAction.mem_fixedPoints.1 hx ⟨g, hg⟩⟩
  have hsub : Subsingleton ↥(MulAction.fixedPoints ↥P (Fin 2 → K)) :=
    ⟨fun x y => Subtype.ext ((hzero x x.2).trans (hzero y y.2).symm)⟩
  have hle : Nat.card ↑(MulAction.fixedPoints ↥P (Fin 2 → K)) ≤ 1 :=
    Finite.card_le_one_iff_subsingleton.2 hsub
  have hpos : 0 < Nat.card ↑(MulAction.fixedPoints ↥P (Fin 2 → K)) :=
    Nat.card_pos_iff.2 ⟨⟨⟨0, MulAction.mem_fixedPoints.2 fun g => Matrix.mulVec_zero _⟩⟩,
      inferInstance⟩
  omega

theorem kfs_sylow_eq_stab {K : Type} [Field K] [Finite K] [CharP K 2]
    (P : Sylow 2 ↥(StatedSL 2 K)) {v : Fin 2 → K} (hv : v ≠ 0)
    (hfix : ∀ g ∈ (P : Subgroup ↥(StatedSL 2 K)), g • v = v) :
    MulAction.stabilizer ↥(StatedSL 2 K) v = (P : Subgroup ↥(StatedSL 2 K)) := by
  refine P.is_maximal' (kfs_isPGroup_stab hv) ?_
  intro g hg
  exact MulAction.mem_stabilizer_iff.2 (hfix g hg)

theorem kfs_stab_smul {K : Type} [Field K] {v : Fin 2 → K} {c : K} (hc : c ≠ 0) :
    MulAction.stabilizer ↥(StatedSL 2 K) (c • v) = MulAction.stabilizer ↥(StatedSL 2 K) v := by
  ext g
  rw [MulAction.mem_stabilizer_iff, MulAction.mem_stabilizer_iff]
  show Matrix.mulVec ((g : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) (c • v) = c • v ↔
    Matrix.mulVec ((g : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) v = v
  rw [Matrix.mulVec_smul, smul_right_inj hc]

theorem kfs_stab_eq_of_det_eq_zero {K : Type} [Field K] {v w : Fin 2 → K} (hv : v ≠ 0)
    (hw : w ≠ 0) (hdet : v 0 * w 1 - w 0 * v 1 = 0) :
    MulAction.stabilizer ↥(StatedSL 2 K) v = MulAction.stabilizer ↥(StatedSL 2 K) w := by
  have hsing : ∃ x : Fin 2 → K, x ≠ 0 ∧ (kfsCol v w) *ᵥ x = 0 :=
    Matrix.exists_mulVec_eq_zero_iff.2 (by rw [kfs_det_col]; exact hdet)
  obtain ⟨x, hx, hxv⟩ := hsing
  have h0 : ∀ i, v i * x 0 + w i * x 1 = 0 := by
    intro i
    have := congrFun hxv i
    simpa [kfsCol, Matrix.mulVec, dotProduct, Fin.sum_univ_two] using this
  by_cases hx1 : x 1 = 0
  · exfalso
    apply hv
    have hx0 : x 0 ≠ 0 := fun h => hx (by
      funext j
      fin_cases j
      · simpa using h
      · simpa using hx1)
    funext i
    have h := h0 i
    rw [hx1, mul_zero, add_zero] at h
    simpa using (mul_eq_zero.1 h).resolve_right hx0
  · have hwc : w = (-(x 0 / x 1)) • v := by
      funext i
      have h := h0 i
      simp only [Pi.smul_apply, smul_eq_mul]
      field_simp
      linear_combination h
    have hc : -(x 0 / x 1) ≠ 0 := by
      intro h
      apply hw
      rw [hwc, h, zero_smul]
    rw [hwc]
    exact (kfs_stab_smul hc).symm

theorem kfs_one_add_single_fix {K : Type} [Field K] {i j : Fin 2} (c : K) (e : Fin 2 → K)
    (he : e j = 0) : (1 + Matrix.single i j c) *ᵥ e = e := by
  rw [Matrix.add_mulVec, Matrix.one_mulVec, Matrix.single_mulVec_eq, he, mul_zero, zero_smul,
    add_zero]

theorem kfs_conj_fix {K : Type} [Field K] (M x : ↥(StatedSL 2 K)) (e0 : Fin 2 → K)
    (hMinv : kfsMat M⁻¹ * kfsMat M = 1) (hx : kfsMat x *ᵥ e0 = e0) :
    (M * x * M⁻¹) • (kfsMat M *ᵥ e0) = kfsMat M *ᵥ e0 := by
  show Matrix.mulVec (kfsMat (M * x * M⁻¹)) (Matrix.mulVec (kfsMat M) e0) =
    Matrix.mulVec (kfsMat M) e0
  have hBA : kfsMat M⁻¹ *ᵥ (kfsMat M *ᵥ e0) = e0 := by
    rw [Matrix.mulVec_mulVec, hMinv, Matrix.one_mulVec]
  have hprod : kfsMat (M * x * M⁻¹) = kfsMat M * kfsMat x * kfsMat M⁻¹ := rfl
  rw [hprod]
  simp only [← Matrix.mulVec_mulVec]
  rw [hBA, hx]

theorem kfs_transvection_fix {K : Type} [Field K] {i j : Fin 2} (hij : i ≠ j) (c : K)
    (e : Fin 2 → K) (he : e j = 0) :
    Matrix.mulVec (kfsMat (specialLinearGroupEquivStatedSL 2 K
      (Matrix.SpecialLinearGroup.transvection hij c))) e = e := by
  show Matrix.mulVec (1 + Matrix.single i j c) e = e
  exact kfs_one_add_single_fix c e he

theorem kfs_gen_of_frame {K : Type} [Field K] [Finite K] [CharP K 2] {v w : Fin 2 → K}
    (hdet : v 0 * w 1 - w 0 * v 1 = 1) (H : Subgroup ↥(StatedSL 2 K))
    (h1 : MulAction.stabilizer ↥(StatedSL 2 K) v ≤ H)
    (h2 : MulAction.stabilizer ↥(StatedSL 2 K) w ≤ H) : H = ⊤ := by
  have hdetM : (kfsCol v w).det = 1 := by rw [kfs_det_col]; exact hdet
  obtain ⟨M, hM⟩ : ∃ M : ↥(StatedSL 2 K), kfsMat M = kfsCol v w :=
    ⟨specialLinearGroupEquivStatedSL 2 K ⟨kfsCol v w, hdetM⟩, rfl⟩
  have hMe0 : kfsMat M *ᵥ Pi.single 0 1 = v := by
    rw [hM]
    funext i
    fin_cases i <;> simp [kfsCol, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  have hMe1 : kfsMat M *ᵥ Pi.single 1 1 = w := by
    rw [hM]
    funext i
    fin_cases i <;> simp [kfsCol, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  have hMinv : kfsMat M⁻¹ * kfsMat M = 1 := by
    show kfsMat (M⁻¹ * M) = 1
    rw [inv_mul_cancel]
    rfl
  have key : ∀ B : ↥(StatedSL 2 K), M * B * M⁻¹ ∈ H := by
    intro B
    obtain ⟨A, rfl⟩ := (specialLinearGroupEquivStatedSL 2 K).surjective B
    refine Matrix.SL2.transvection_induction
      (fun A : Matrix.SpecialLinearGroup (Fin 2) K =>
        M * specialLinearGroupEquivStatedSL 2 K A * M⁻¹ ∈ H) ?_ ?_ A
    · intro i j hij c
      fin_cases i <;> fin_cases j
      · exact absurd rfl hij
      · apply h1
        rw [MulAction.mem_stabilizer_iff, ← hMe0]
        exact kfs_conj_fix M _ _ hMinv (kfs_transvection_fix _ c _ (by simp))
      · apply h2
        rw [MulAction.mem_stabilizer_iff, ← hMe1]
        exact kfs_conj_fix M _ _ hMinv (kfs_transvection_fix _ c _ (by simp))
      · exact absurd rfl hij
    · intro A B hA hB
      have hsplit : M * specialLinearGroupEquivStatedSL 2 K (A * B) * M⁻¹ =
          (M * specialLinearGroupEquivStatedSL 2 K A * M⁻¹) *
            (M * specialLinearGroupEquivStatedSL 2 K B * M⁻¹) := by
        rw [map_mul]
        group
      rw [hsplit]
      exact H.mul_mem hA hB
  rw [eq_top_iff]
  intro B _
  have h := key (M⁻¹ * B * M)
  have e : M * (M⁻¹ * B * M) * M⁻¹ = B := by group
  rwa [e] at h

theorem sl2Root_holds : SL2RootStatement := by
  intro K _ _ _ P₁ P₂ hne
  obtain ⟨v₁, hv₁, hfix₁⟩ := kfs_exists_fixed (P₁ : Subgroup ↥(StatedSL 2 K)) P₁.isPGroup'
  obtain ⟨v₂, hv₂, hfix₂⟩ := kfs_exists_fixed (P₂ : Subgroup ↥(StatedSL 2 K)) P₂.isPGroup'
  have e₁ := kfs_sylow_eq_stab P₁ hv₁ hfix₁
  have e₂ := kfs_sylow_eq_stab P₂ hv₂ hfix₂
  obtain ⟨d, hd_def⟩ : ∃ d : K, d = v₁ 0 * v₂ 1 - v₂ 0 * v₁ 1 := ⟨_, rfl⟩
  have hd : d ≠ 0 := by
    intro h0
    apply hne
    apply Sylow.ext
    rw [← e₁, ← e₂]
    exact kfs_stab_eq_of_det_eq_zero hv₁ hv₂ (by rw [← hd_def, h0])
  have hdet : v₁ 0 * (d⁻¹ • v₂) 1 - (d⁻¹ • v₂) 0 * v₁ 1 = 1 := by
    simp only [Pi.smul_apply, smul_eq_mul]
    calc v₁ 0 * (d⁻¹ * v₂ 1) - d⁻¹ * v₂ 0 * v₁ 1 = d⁻¹ * (v₁ 0 * v₂ 1 - v₂ 0 * v₁ 1) := by
          ring
      _ = 1 := by rw [← hd_def, inv_mul_cancel₀ hd]
  apply kfs_gen_of_frame hdet
  · rw [e₁]
    exact le_sup_left
  · rw [kfs_stab_smul (inv_ne_zero hd), e₂]
    exact le_sup_right

end Smith23E1
