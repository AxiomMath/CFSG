module

public import CFSG.LocalAnalysis.UniquenessCase.UC22S2112aR34F2Even2PGL
public import CFSG.Adapters.Certificate43Check
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherFactsL2Orders
public import Mathlib.LinearAlgebra.Matrix.Notation
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherFactsL2Maximal
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PSL2Contragredient
public import Certificates.Certificate43

public section

namespace CFSG.StandardType.ZS

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

variable {p : ℕ} [Fact p.Prime]

private abbrev planePairClosure (A B : Matrix.GeneralLinearGroup (Fin 2) (ZMod p)) :
    Subgroup (Matrix.GeneralLinearGroup (Fin 2) (ZMod p)) :=
  Subgroup.closure ({A, B} : Set (Matrix.GeneralLinearGroup (Fin 2) (ZMod p)))

private abbrev planePairProjective (A B : Matrix.GeneralLinearGroup (Fin 2) (ZMod p)) :
    Subgroup (Matrix.ProjGenLinGroup (Fin 2) (ZMod p)) :=
  (planePairClosure A B).map Matrix.ProjGenLinGroup.mk

private theorem mk_mem_planePairProjective (A B : Matrix.GeneralLinearGroup (Fin 2) (ZMod p)) :
    Matrix.ProjGenLinGroup.mk A ∈ planePairProjective A B :=
  Subgroup.mem_map.mpr ⟨A, Subgroup.subset_closure (by simp), rfl⟩

private def planePairA (A B : Matrix.GeneralLinearGroup (Fin 2) (ZMod p)) :
    planePairProjective A B :=
  ⟨Matrix.ProjGenLinGroup.mk A, mk_mem_planePairProjective A B⟩

private def planePairB (A B : Matrix.GeneralLinearGroup (Fin 2) (ZMod p)) :
    planePairProjective A B :=
  ⟨Matrix.ProjGenLinGroup.mk B, Subgroup.mem_map.mpr
    ⟨B, Subgroup.subset_closure (by simp), rfl⟩⟩

private theorem matrix_pow_plane (τ b : ZMod p) (k : ℕ) :
    (!![τ, b; 0, 1] : Matrix (Fin 2) (Fin 2) (ZMod p)) ^ k =
      !![τ ^ k, b * ∑ i ∈ Finset.range k, τ ^ i; 0, 1] := by
  induction k with
  | zero =>
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  | succ k ih =>
    rw [pow_succ, ih, Finset.sum_range_succ, pow_succ]
    ext i j
    fin_cases i <;> fin_cases j
    all_goals simp [Matrix.mul_apply, Fin.sum_univ_two]
    all_goals ring

private theorem pow_eq_one_of_scalar_plane (τ b : ZMod p) {k : ℕ}
    (hc : ∃ c : ZMod p,
      (!![τ, b; 0, 1] : Matrix (Fin 2) (Fin 2) (ZMod p)) ^ k = c • 1) : τ ^ k = 1 := by
  obtain ⟨c, hc⟩ := hc
  have h00 : τ ^ k = c := by
    have h := congrArg (fun M : Matrix (Fin 2) (Fin 2) (ZMod p) => M 0 0) hc
    simpa [matrix_pow_plane, Matrix.smul_apply] using h
  have h11 : (1 : ZMod p) = c := by
    have h := congrArg (fun M : Matrix (Fin 2) (Fin 2) (ZMod p) => M 1 1) hc
    simpa [matrix_pow_plane, Matrix.smul_apply] using h
  rw [h00, ← h11]

private theorem orderOf_mk_eq_of_upper {A : Matrix.GeneralLinearGroup (Fin 2) (ZMod p)}
    {τ b : ZMod p} (hA : (A : Matrix (Fin 2) (Fin 2) (ZMod p)) = !![τ, b; 0, 1])
    (hτ1 : τ ≠ 1) :
    orderOf (Matrix.ProjGenLinGroup.mk A) = orderOf τ := by
  classical
  set m := orderOf τ
  have hsum : ∑ i ∈ Finset.range m, τ ^ i = 0 := by
    rw [geom_sum_eq hτ1 m, pow_orderOf_eq_one, sub_self, zero_div]
  have hpowA : A ^ m = 1 := by
    apply Units.ext
    rw [Units.val_pow_eq_pow_val, hA, matrix_pow_plane, hsum, mul_zero]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [m, pow_orderOf_eq_one]
  have hdvd1 : orderOf (Matrix.ProjGenLinGroup.mk A) ∣ m := by
    apply orderOf_dvd_of_pow_eq_one
    rw [← map_pow, hpowA, map_one]
  have hdvd2 : m ∣ orderOf (Matrix.ProjGenLinGroup.mk A) := by
    set d := orderOf (Matrix.ProjGenLinGroup.mk A)
    have hd : (Matrix.ProjGenLinGroup.mk A) ^ d = 1 := pow_orderOf_eq_one _
    have hsc : ∃ c : ZMod p,
        (!![τ, b; 0, 1] : Matrix (Fin 2) (Fin 2) (ZMod p)) ^ d = c • 1 := by
      have h1 : Matrix.ProjGenLinGroup.mk (A ^ d) = 1 := by rw [map_pow, hd]
      obtain ⟨u, hu⟩ := CFSG.LinearGroups.mk_eq_one_iff_exists_scalar.mp h1
      refine ⟨(u : ZMod p), ?_⟩
      rw [← hA, ← Units.val_pow_eq_pow_val, hu]
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply]
    exact orderOf_dvd_of_pow_eq_one (pow_eq_one_of_scalar_plane τ b hsc)
  exact Nat.dvd_antisymm hdvd1 hdvd2

private theorem matrix_pow_plane_lower (τ b' : ZMod p) (k : ℕ) :
    (!![1, 0; b', τ] : Matrix (Fin 2) (Fin 2) (ZMod p)) ^ k =
      !![1, 0; b' * ∑ i ∈ Finset.range k, τ ^ i, τ ^ k] := by
  induction k with
  | zero =>
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  | succ k ih =>
    rw [pow_succ, ih, Finset.sum_range_succ, pow_succ]
    ext i j
    fin_cases i <;> fin_cases j
    all_goals simp [Matrix.mul_apply, Fin.sum_univ_two]
    all_goals ring

private theorem pow_eq_one_of_scalar_plane_lower (τ b' : ZMod p) {k : ℕ}
    (hc : ∃ c : ZMod p,
      (!![1, 0; b', τ] : Matrix (Fin 2) (Fin 2) (ZMod p)) ^ k = c • 1) : τ ^ k = 1 := by
  obtain ⟨c, hc⟩ := hc
  have h00 : (1 : ZMod p) = c := by
    have h := congrArg (fun M : Matrix (Fin 2) (Fin 2) (ZMod p) => M 0 0) hc
    simpa [matrix_pow_plane_lower, Matrix.smul_apply] using h
  have h11 : τ ^ k = c := by
    have h := congrArg (fun M : Matrix (Fin 2) (Fin 2) (ZMod p) => M 1 1) hc
    simpa [matrix_pow_plane_lower, Matrix.smul_apply] using h
  rw [h11, ← h00]

private theorem orderOf_mk_eq_of_lower {B : Matrix.GeneralLinearGroup (Fin 2) (ZMod p)}
    {τ b' : ZMod p} (hB : (B : Matrix (Fin 2) (Fin 2) (ZMod p)) = !![1, 0; b', τ])
    (hτ1 : τ ≠ 1) :
    orderOf (Matrix.ProjGenLinGroup.mk B) = orderOf τ := by
  classical
  set m := orderOf τ
  have hsum : ∑ i ∈ Finset.range m, τ ^ i = 0 := by
    rw [geom_sum_eq hτ1 m, pow_orderOf_eq_one, sub_self, zero_div]
  have hpowB : B ^ m = 1 := by
    apply Units.ext
    rw [Units.val_pow_eq_pow_val, hB, matrix_pow_plane_lower, hsum, mul_zero]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [m, pow_orderOf_eq_one]
  have hdvd1 : orderOf (Matrix.ProjGenLinGroup.mk B) ∣ m := by
    apply orderOf_dvd_of_pow_eq_one
    rw [← map_pow, hpowB, map_one]
  have hdvd2 : m ∣ orderOf (Matrix.ProjGenLinGroup.mk B) := by
    set d := orderOf (Matrix.ProjGenLinGroup.mk B)
    have hd : (Matrix.ProjGenLinGroup.mk B) ^ d = 1 := pow_orderOf_eq_one _
    have hsc : ∃ c : ZMod p,
        (!![1, 0; b', τ] : Matrix (Fin 2) (Fin 2) (ZMod p)) ^ d = c • 1 := by
      have h1 : Matrix.ProjGenLinGroup.mk (B ^ d) = 1 := by rw [map_pow, hd]
      obtain ⟨u, hu⟩ := CFSG.LinearGroups.mk_eq_one_iff_exists_scalar.mp h1
      refine ⟨(u : ZMod p), ?_⟩
      rw [← hB, ← Units.val_pow_eq_pow_val, hu]
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply]
    exact orderOf_dvd_of_pow_eq_one (pow_eq_one_of_scalar_plane_lower τ b' hsc)
  exact Nat.dvd_antisymm hdvd1 hdvd2

private theorem mk_ne_mk_of_plane {A B : Matrix.GeneralLinearGroup (Fin 2) (ZMod p)}
    {τ b b' : ZMod p}
    (hA : (A : Matrix (Fin 2) (Fin 2) (ZMod p)) = !![τ, b; 0, 1])
    (hB : (B : Matrix (Fin 2) (Fin 2) (ZMod p)) = !![1, 0; b', τ])
    (hb : b ≠ 0) (hb' : b' ≠ 0) (hτ2 : τ ^ 2 ≠ 1) :
    Matrix.ProjGenLinGroup.mk A * Matrix.ProjGenLinGroup.mk B ≠
      Matrix.ProjGenLinGroup.mk B * Matrix.ProjGenLinGroup.mk A := by
  intro hcomm
  rw [← map_mul, ← map_mul, Matrix.ProjGenLinGroup.mk_eq_mk_iff] at hcomm
  obtain ⟨u, hu⟩ := hcomm
  have hu' : (A : Matrix (Fin 2) (Fin 2) (ZMod p)) * (B : Matrix (Fin 2) (Fin 2) (ZMod p)) *
      ((Matrix.GeneralLinearGroup.scalar (Fin 2) u : Matrix.GeneralLinearGroup (Fin 2) (ZMod p)) :
        Matrix (Fin 2) (Fin 2) (ZMod p)) =
      (B : Matrix (Fin 2) (Fin 2) (ZMod p)) * (A : Matrix (Fin 2) (Fin 2) (ZMod p)) := by
    simpa using congrArg (fun g : Matrix.GeneralLinearGroup (Fin 2) (ZMod p) =>
      (g : Matrix (Fin 2) (Fin 2) (ZMod p))) hu
  have h01 := congrArg (fun M : Matrix (Fin 2) (Fin 2) (ZMod p) => M 0 1) hu'
  have h10 := congrArg (fun M : Matrix (Fin 2) (Fin 2) (ZMod p) => M 1 0) hu'
  simp [hA, hB, Matrix.mul_apply, Fin.sum_univ_two, Matrix.GeneralLinearGroup.coe_scalar,
    Matrix.scalar_apply, mul_assoc] at h01 h10
  have hcτ : (u : ZMod p) * τ = 1 := by
    exact mul_left_cancel₀ hb (by linear_combination h01)
  have hc : (u : ZMod p) = τ := by
    rcases h10 with h | h
    · exact h
    · exact absurd h hb'
  apply hτ2
  calc τ ^ 2 = (u : ZMod p) * τ := by rw [hc]; ring
    _ = 1 := hcτ

private theorem not_dvd_card_map_mk_of_pow_eq_one {A B : Matrix.GeneralLinearGroup (Fin 2) (ZMod p)}
    (hpf : ∀ g ∈ Subgroup.closure ({A, B} :
      Set (Matrix.GeneralLinearGroup (Fin 2) (ZMod p))), g ^ p = 1 → g = 1) :
    ¬ p ∣ Nat.card ((Subgroup.closure ({A, B} :
      Set (Matrix.GeneralLinearGroup (Fin 2) (ZMod p)))).map Matrix.ProjGenLinGroup.mk) := by
  classical
  have : Finite (Matrix.ProjGenLinGroup (Fin 2) (ZMod p)) :=
    Finite.of_surjective Matrix.ProjGenLinGroup.mk Matrix.ProjGenLinGroup.mk_surjective
  let S : Subgroup (Matrix.GeneralLinearGroup (Fin 2) (ZMod p)) :=
    Subgroup.closure ({A, B} : Set (Matrix.GeneralLinearGroup (Fin 2) (ZMod p)))
  intro hdiv
  obtain ⟨x, hxord⟩ := exists_prime_orderOf_dvd_card' p hdiv
  obtain ⟨g, hgS, hgx⟩ := Subgroup.mem_map.mp x.2
  have hxeq : (x : Matrix.ProjGenLinGroup (Fin 2) (ZMod p)) =
      Matrix.ProjGenLinGroup.mk g := hgx.symm
  have hxord' : orderOf (Matrix.ProjGenLinGroup.mk g) = p := by
    rw [← hxeq, Subgroup.orderOf_coe, hxord]
  have hxp : (Matrix.ProjGenLinGroup.mk g) ^ p = 1 := by
    rw [← orderOf_dvd_iff_pow_eq_one, hxord']
  have h1 : Matrix.ProjGenLinGroup.mk (g ^ p) = 1 := by rw [map_pow, hxp]
  obtain ⟨u, hu⟩ := CFSG.LinearGroups.mk_eq_one_iff_exists_scalar.mp h1
  let h := g ^ (p - 1)
  have hhmem : h ∈ S := S.pow_mem hgS (p - 1)
  have hh1 : h ^ p = 1 := by
    have hmul : h ^ p = (g ^ p) ^ (p - 1) := by
      dsimp only [h]
      rw [← pow_mul, mul_comm, pow_mul]
    rw [hmul, hu, ← map_pow, ZMod.units_pow_card_sub_one_eq_one p u, map_one]
  have hheq : h = 1 := hpf h hhmem hh1
  have hxpm1 : x ^ (p - 1) = 1 := by
    have hh : Matrix.ProjGenLinGroup.mk h = 1 := by rw [hheq, map_one]
    have hxp1 : (x : Matrix.ProjGenLinGroup (Fin 2) (ZMod p)) ^ (p - 1) = 1 := by
      rw [hxeq, ← map_pow]
      exact hh
    apply Subtype.ext
    simpa using hxp1
  have hdvd_p : orderOf x ∣ p := by rw [hxord]
  have hdvd_pm1 : orderOf x ∣ p - 1 := orderOf_dvd_of_pow_eq_one hxpm1
  have hgdvd : orderOf x ∣ 1 := by
    have hsub := Nat.dvd_sub hdvd_p hdvd_pm1
    have hp1 : p - (p - 1) = 1 := by
      have hp2 : 1 ≤ p := (Fact.out : p.Prime).one_le
      omega
    rwa [hp1] at hsub
  have : orderOf x = 1 := Nat.dvd_one.mp hgdvd
  rw [hxord] at this
  exact (Fact.out : p.Prime).ne_one this

private theorem planePair_not_isCyclic {A B : Matrix.GeneralLinearGroup (Fin 2) (ZMod p)}
    {τ b b' : ZMod p}
    (hA : (A : Matrix (Fin 2) (Fin 2) (ZMod p)) = !![τ, b; 0, 1])
    (hB : (B : Matrix (Fin 2) (Fin 2) (ZMod p)) = !![1, 0; b', τ])
    (hb : b ≠ 0) (hb' : b' ≠ 0) (hτ : 4 ≤ orderOf τ) :
    ¬ IsCyclic (planePairProjective A B) := by
  intro hcyc
  have hτ1 : τ ≠ 1 := by rintro rfl; simp at hτ
  have hτ2 : τ ^ 2 ≠ 1 := by
    intro h
    have hdvd : orderOf τ ∣ 2 := orderOf_dvd_of_pow_eq_one h
    have hle : orderOf τ ≤ 2 := Nat.le_of_dvd (by norm_num) hdvd
    omega
  let : CommGroup (planePairProjective A B) := hcyc.commGroup
  exact mk_ne_mk_of_plane hA hB hb hb' hτ2
    (congrArg Subtype.val (mul_comm (planePairA A B) (planePairB A B)))

open CFSG.ComponentClassification.AschbacherKnownGroup.FactsL2 in
private theorem planePair_not_dihedral {A B : Matrix.GeneralLinearGroup (Fin 2) (ZMod p)}
    {τ b b' : ZMod p} {z : ℕ}
    (hA : (A : Matrix (Fin 2) (Fin 2) (ZMod p)) = !![τ, b; 0, 1])
    (hB : (B : Matrix (Fin 2) (Fin 2) (ZMod p)) = !![1, 0; b', τ])
    (hb : b ≠ 0) (hb' : b' ≠ 0) (hτ : 4 ≤ orderOf τ)
    (e : planePairProjective A B ≃* DihedralGroup z) : False := by
  have hτ1 : τ ≠ 1 := by rintro rfl; simp at hτ
  have hτ2 : τ ^ 2 ≠ 1 := by
    intro h
    have hdvd : orderOf τ ∣ 2 := orderOf_dvd_of_pow_eq_one h
    have hle : orderOf τ ≤ 2 := Nat.le_of_dvd (by norm_num) hdvd
    omega
  have hAord : orderOf (planePairA A B) = orderOf τ := by
    rw [← Subgroup.orderOf_coe (planePairA A B)]
    exact orderOf_mk_eq_of_upper hA hτ1
  have hBord : orderOf (planePairB A B) = orderOf τ := by
    rw [← Subgroup.orderOf_coe (planePairB A B)]
    exact orderOf_mk_eq_of_lower hB hτ1
  have hx : 2 < orderOf (planePairA A B) := by rw [hAord]; omega
  have hy : 2 < orderOf (planePairB A B) := by rw [hBord]; omega
  exact mk_ne_mk_of_plane hA hB hb hb' hτ2
    (congrArg Subtype.val (commute_of_equiv_dihedral e hx hy))

open CFSG.ComponentClassification.AschbacherKnownGroup.FactsL2 in
private theorem planePair_not_alt_four {A B : Matrix.GeneralLinearGroup (Fin 2) (ZMod p)}
    {τ b : ZMod p}
    (hA : (A : Matrix (Fin 2) (Fin 2) (ZMod p)) = !![τ, b; 0, 1])
    (hτ : 4 ≤ orderOf τ)
    (e : planePairProjective A B ≃* alternatingGroup (Fin 4)) : False := by
  have hτ1 : τ ≠ 1 := by rintro rfl; simp at hτ
  have hAord : orderOf (planePairA A B) = orderOf τ := by
    rw [← Subgroup.orderOf_coe (planePairA A B)]
    exact orderOf_mk_eq_of_upper hA hτ1
  rcases orderOf_dvd_of_equiv_alternating_four e (planePairA A B) with h | h
  · have hle : orderOf τ ≤ 2 := by
      rw [← hAord]; exact Nat.le_of_dvd (by norm_num) h
    omega
  · have hle : orderOf τ ≤ 3 := by
      rw [← hAord]; exact Nat.le_of_dvd (by norm_num) h
    omega

open CFSG.ComponentClassification.AschbacherKnownGroup.FactsL2 in
private theorem orderOf_eq_four_of_equiv_perm_four
    {A B : Matrix.GeneralLinearGroup (Fin 2) (ZMod p)} {τ b : ZMod p}
    (hA : (A : Matrix (Fin 2) (Fin 2) (ZMod p)) = !![τ, b; 0, 1])
    (hτ : 4 ≤ orderOf τ)
    (e : planePairProjective A B ≃* Equiv.Perm (Fin 4)) : orderOf τ = 4 := by
  have hτ1 : τ ≠ 1 := by rintro rfl; simp at hτ
  have hAord : orderOf (planePairA A B) = orderOf τ := by
    rw [← Subgroup.orderOf_coe (planePairA A B)]
    exact orderOf_mk_eq_of_upper hA hτ1
  rcases orderOf_dvd_of_equiv_perm_four e (planePairA A B) with h | h
  · have hle : orderOf τ ≤ 3 := by
      rw [← hAord]; exact Nat.le_of_dvd (by norm_num) h
    omega
  · have hle : orderOf τ ≤ 4 := by
      rw [← hAord]; exact Nat.le_of_dvd (by norm_num) h
    omega

open CFSG.ComponentClassification.AschbacherKnownGroup.FactsL2 in
private theorem orderOf_eq_five_of_equiv_alt_five {A B : Matrix.GeneralLinearGroup (Fin 2) (ZMod p)}
    {τ b : ZMod p} (hA : (A : Matrix (Fin 2) (Fin 2) (ZMod p)) = !![τ, b; 0, 1])
    (hτ : 4 ≤ orderOf τ)
    (e : planePairProjective A B ≃* alternatingGroup (Fin 5)) : orderOf τ = 5 := by
  have hτ1 : τ ≠ 1 := by rintro rfl; simp at hτ
  have hAord : orderOf (planePairA A B) = orderOf τ := by
    rw [← Subgroup.orderOf_coe (planePairA A B)]
    exact orderOf_mk_eq_of_upper hA hτ1
  rcases orderOf_dvd_of_equiv_alternating_five e (planePairA A B) with h | h | h
  · exfalso
    have hle : orderOf τ ≤ 2 := by
      rw [← hAord]; exact Nat.le_of_dvd (by norm_num) h
    omega
  · exfalso
    have hle : orderOf τ ≤ 3 := by
      rw [← hAord]; exact Nat.le_of_dvd (by norm_num) h
    omega
  · have hd : orderOf τ ∣ 5 := by rw [hAord] at h; exact h
    rcases (Nat.dvd_prime (by norm_num : Nat.Prime 5)).mp hd with h1 | h5
    · omega
    · exact h5

private theorem planePair_dickson_s4_or_a5 {A B : Matrix.GeneralLinearGroup (Fin 2) (ZMod p)}
    {τ b b' : ZMod p}
    (hA : (A : Matrix (Fin 2) (Fin 2) (ZMod p)) = !![τ, b; 0, 1])
    (hB : (B : Matrix (Fin 2) (Fin 2) (ZMod p)) = !![1, 0; b', τ])
    (hb : b ≠ 0) (hb' : b' ≠ 0)
    (hpf : ∀ g ∈ Subgroup.closure ({A, B} : Set (Matrix.GeneralLinearGroup (Fin 2) (ZMod p))),
      g ^ p = 1 → g = 1)
    (hτ : 4 ≤ orderOf τ) :
    (orderOf τ = 4 ∧ Nonempty (planePairProjective A B ≃* Equiv.Perm (Fin 4))) ∨
      (orderOf τ = 5 ∧ Nonempty (planePairProjective A B ≃* alternatingGroup (Fin 5))) := by
  classical
  let Sbar : Subgroup (Matrix.ProjGenLinGroup (Fin 2) (ZMod p)) := planePairProjective A B
  have hpdiv : ¬ p ∣ Nat.card Sbar := not_dvd_card_map_mk_of_pow_eq_one hpf
  rcases CFSG.LocalAnalysis.UniquenessCase.UC22.uc22s2112r34_pgl_tame_cases_iso
    Sbar hpdiv with hcyc | ⟨z, hz⟩ | hA4 | hS4 | hA5
  · exact absurd hcyc (planePair_not_isCyclic hA hB hb hb' hτ)
  · obtain ⟨e⟩ := hz
    exact False.elim (planePair_not_dihedral hA hB hb hb' hτ e)
  · obtain ⟨e⟩ := hA4
    exact False.elim (planePair_not_alt_four hA hτ e)
  · obtain ⟨e⟩ := hS4
    exact Or.inl ⟨orderOf_eq_four_of_equiv_perm_four hA hτ e, ⟨e⟩⟩
  · obtain ⟨e⟩ := hA5
    exact Or.inr ⟨orderOf_eq_five_of_equiv_alt_five hA hτ e, ⟨e⟩⟩

private theorem planePair_equiv_perm_four {A B : Matrix.GeneralLinearGroup (Fin 2) (ZMod p)}
    {τ b b' : ZMod p}
    (hA : (A : Matrix (Fin 2) (Fin 2) (ZMod p)) = !![τ, b; 0, 1])
    (hB : (B : Matrix (Fin 2) (Fin 2) (ZMod p)) = !![1, 0; b', τ]) (hb : b ≠ 0) (hb' : b' ≠ 0)
    (hpf : ∀ g ∈ Subgroup.closure ({A, B} : Set (Matrix.GeneralLinearGroup (Fin 2) (ZMod p))),
      g ^ p = 1 → g = 1)
    (hτ : orderOf τ = 4) :
    Nonempty (planePairProjective A B ≃* Equiv.Perm (Fin 4)) := by
  rcases planePair_dickson_s4_or_a5 hA hB hb hb' hpf (by omega) with ⟨-, h⟩ | ⟨h5, -⟩
  · exact h
  · omega

private theorem planePair_equiv_alt_five {A B : Matrix.GeneralLinearGroup (Fin 2) (ZMod p)}
    {τ b b' : ZMod p}
    (hA : (A : Matrix (Fin 2) (Fin 2) (ZMod p)) = !![τ, b; 0, 1])
    (hB : (B : Matrix (Fin 2) (Fin 2) (ZMod p)) = !![1, 0; b', τ]) (hb : b ≠ 0) (hb' : b' ≠ 0)
    (hpf : ∀ g ∈ Subgroup.closure ({A, B} : Set (Matrix.GeneralLinearGroup (Fin 2) (ZMod p))),
      g ^ p = 1 → g = 1)
    (hτ : orderOf τ = 5) :
    Nonempty (planePairProjective A B ≃* alternatingGroup (Fin 5)) := by
  rcases planePair_dickson_s4_or_a5 hA hB hb hb' hpf (by omega) with ⟨h4, -⟩ | ⟨-, h⟩
  · omega
  · exact h

open CFSG.ComponentClassification.AschbacherKnownGroup.FactsL2 in
private theorem perm_four_pow_dvd {M : Type*} [Group M]
    (e : M ≃* Equiv.Perm (Fin 4)) (x : M) : orderOf x ∣ 3 ∨ orderOf x ∣ 4 :=
  orderOf_dvd_of_equiv_perm_four e x

open CFSG.ComponentClassification.AschbacherKnownGroup.FactsL2 in
private theorem alt_five_pow_dvd {M : Type*} [Group M]
    (e : M ≃* alternatingGroup (Fin 5)) (x : M) :
    orderOf x ∣ 2 ∨ orderOf x ∣ 3 ∨ orderOf x ∣ 5 :=
  orderOf_dvd_of_equiv_alternating_five e x

private theorem exists_smul_one_of_mk_pow_eq_one {g : Matrix.GeneralLinearGroup (Fin 2) (ZMod p)}
    {k : ℕ} (h : (Matrix.ProjGenLinGroup.mk g) ^ k = 1) :
    ∃ c : ZMod p, ((g ^ k : Matrix.GeneralLinearGroup (Fin 2) (ZMod p)) :
      Matrix (Fin 2) (Fin 2) (ZMod p)) = c • 1 := by
  have h1 : Matrix.ProjGenLinGroup.mk (g ^ k) = 1 := by rw [map_pow, h]
  obtain ⟨u, hu⟩ := CFSG.LinearGroups.mk_eq_one_iff_exists_scalar.mp h1
  refine ⟨(u : ZMod p), ?_⟩
  rw [hu]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply]

private theorem exists_smul_one_of_projective_pow {A B : Matrix.GeneralLinearGroup (Fin 2) (ZMod p)}
    {g : Matrix.GeneralLinearGroup (Fin 2) (ZMod p)}
    (hg : g ∈ Subgroup.closure ({A, B} : Set (Matrix.GeneralLinearGroup (Fin 2) (ZMod p))))
    {k : ℕ}
    (h : (⟨Matrix.ProjGenLinGroup.mk g, Subgroup.mem_map.mpr ⟨g, hg, rfl⟩⟩ :
      planePairProjective A B) ^ k = 1) :
    ∃ c : ZMod p, ((g ^ k : Matrix.GeneralLinearGroup (Fin 2) (ZMod p)) :
      Matrix (Fin 2) (Fin 2) (ZMod p)) = c • 1 := by
  have h' : (Matrix.ProjGenLinGroup.mk g) ^ k = 1 := by
    simpa using congrArg (fun y : planePairProjective A B =>
      (y : Matrix.ProjGenLinGroup (Fin 2) (ZMod p))) h
  exact exists_smul_one_of_mk_pow_eq_one h'

theorem orderOf_eq_four_or_five_of_planePair
    {A B : Matrix.GeneralLinearGroup (Fin 2) (ZMod p)} {τ b b' : ZMod p}
    (hA : (A : Matrix (Fin 2) (Fin 2) (ZMod p)) = !![τ, b; 0, 1])
    (hB : (B : Matrix (Fin 2) (Fin 2) (ZMod p)) = !![1, 0; b', τ]) (hb : b ≠ 0) (hb' : b' ≠ 0)
    (hpf : ∀ g ∈ Subgroup.closure ({A, B} : Set (Matrix.GeneralLinearGroup (Fin 2) (ZMod p))),
      g ^ p = 1 → g = 1)
    (hτ : 4 ≤ orderOf τ) : orderOf τ = 4 ∨ orderOf τ = 5 := by
  rcases planePair_dickson_s4_or_a5 hA hB hb hb' hpf hτ with ⟨h4, -⟩ | ⟨h5, -⟩
  · exact Or.inl h4
  · exact Or.inr h5

theorem pow_eq_smul_of_planePair_four
    {A B : Matrix.GeneralLinearGroup (Fin 2) (ZMod p)} {τ b b' : ZMod p}
    (hA : (A : Matrix (Fin 2) (Fin 2) (ZMod p)) = !![τ, b; 0, 1])
    (hB : (B : Matrix (Fin 2) (Fin 2) (ZMod p)) = !![1, 0; b', τ]) (hb : b ≠ 0) (hb' : b' ≠ 0)
    (hpf : ∀ g ∈ Subgroup.closure ({A, B} : Set (Matrix.GeneralLinearGroup (Fin 2) (ZMod p))),
      g ^ p = 1 → g = 1)
    (hτ : orderOf τ = 4) :
    ∀ g ∈ Subgroup.closure ({A, B} : Set (Matrix.GeneralLinearGroup (Fin 2) (ZMod p))),
      ∃ c : ZMod p, ((g ^ 3 : Matrix.GeneralLinearGroup (Fin 2) (ZMod p)) :
          Matrix (Fin 2) (Fin 2) (ZMod p)) = c • 1 ∨
        ((g ^ 4 : Matrix.GeneralLinearGroup (Fin 2) (ZMod p)) :
          Matrix (Fin 2) (Fin 2) (ZMod p)) = c • 1 := by
  obtain ⟨e⟩ := planePair_equiv_perm_four hA hB hb hb' hpf hτ
  intro g hg
  let w : planePairProjective A B := ⟨Matrix.ProjGenLinGroup.mk g,
    Subgroup.mem_map.mpr ⟨g, hg, rfl⟩⟩
  rcases perm_four_pow_dvd e w with h | h
  · have hw3 : w ^ 3 = 1 := (orderOf_dvd_iff_pow_eq_one).mp h
    have h3 : (⟨Matrix.ProjGenLinGroup.mk g, Subgroup.mem_map.mpr ⟨g, hg, rfl⟩⟩ :
        planePairProjective A B) ^ 3 = 1 := hw3
    obtain ⟨c, hc⟩ := exists_smul_one_of_projective_pow hg h3
    exact ⟨c, Or.inl hc⟩
  · have hw4 : w ^ 4 = 1 := (orderOf_dvd_iff_pow_eq_one).mp h
    have h4 : (⟨Matrix.ProjGenLinGroup.mk g, Subgroup.mem_map.mpr ⟨g, hg, rfl⟩⟩ :
        planePairProjective A B) ^ 4 = 1 := hw4
    obtain ⟨c, hc⟩ := exists_smul_one_of_projective_pow hg h4
    exact ⟨c, Or.inr hc⟩

theorem pow_eq_smul_of_planePair_five
    {A B : Matrix.GeneralLinearGroup (Fin 2) (ZMod p)} {τ b b' : ZMod p}
    (hA : (A : Matrix (Fin 2) (Fin 2) (ZMod p)) = !![τ, b; 0, 1])
    (hB : (B : Matrix (Fin 2) (Fin 2) (ZMod p)) = !![1, 0; b', τ]) (hb : b ≠ 0) (hb' : b' ≠ 0)
    (hpf : ∀ g ∈ Subgroup.closure ({A, B} : Set (Matrix.GeneralLinearGroup (Fin 2) (ZMod p))),
      g ^ p = 1 → g = 1)
    (hτ : orderOf τ = 5) :
    ∀ g ∈ Subgroup.closure ({A, B} : Set (Matrix.GeneralLinearGroup (Fin 2) (ZMod p))),
      ∃ c : ZMod p, ((g ^ 2 : Matrix.GeneralLinearGroup (Fin 2) (ZMod p)) :
          Matrix (Fin 2) (Fin 2) (ZMod p)) = c • 1 ∨
        ((g ^ 3 : Matrix.GeneralLinearGroup (Fin 2) (ZMod p)) :
          Matrix (Fin 2) (Fin 2) (ZMod p)) = c • 1 ∨
        ((g ^ 5 : Matrix.GeneralLinearGroup (Fin 2) (ZMod p)) :
          Matrix (Fin 2) (Fin 2) (ZMod p)) = c • 1 := by
  obtain ⟨e⟩ := planePair_equiv_alt_five hA hB hb hb' hpf hτ
  intro g hg
  let w : planePairProjective A B := ⟨Matrix.ProjGenLinGroup.mk g,
    Subgroup.mem_map.mpr ⟨g, hg, rfl⟩⟩
  rcases alt_five_pow_dvd e w with h | h | h
  · have hw2 : w ^ 2 = 1 := (orderOf_dvd_iff_pow_eq_one).mp h
    have h2 : (⟨Matrix.ProjGenLinGroup.mk g, Subgroup.mem_map.mpr ⟨g, hg, rfl⟩⟩ :
        planePairProjective A B) ^ 2 = 1 := hw2
    obtain ⟨c, hc⟩ := exists_smul_one_of_projective_pow hg h2
    exact ⟨c, Or.inl hc⟩
  · have hw3 : w ^ 3 = 1 := (orderOf_dvd_iff_pow_eq_one).mp h
    have h3 : (⟨Matrix.ProjGenLinGroup.mk g, Subgroup.mem_map.mpr ⟨g, hg, rfl⟩⟩ :
        planePairProjective A B) ^ 3 = 1 := hw3
    obtain ⟨c, hc⟩ := exists_smul_one_of_projective_pow hg h3
    exact ⟨c, Or.inr (Or.inl hc)⟩
  · have hw5 : w ^ 5 = 1 := (orderOf_dvd_iff_pow_eq_one).mp h
    have h5 : (⟨Matrix.ProjGenLinGroup.mk g, Subgroup.mem_map.mpr ⟨g, hg, rfl⟩⟩ :
        planePairProjective A B) ^ 5 = 1 := hw5
    obtain ⟨c, hc⟩ := exists_smul_one_of_projective_pow hg h5
    exact ⟨c, Or.inr (Or.inr hc)⟩

end CFSG.StandardType.ZS

end
