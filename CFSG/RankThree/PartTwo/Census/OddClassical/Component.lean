module

public import CFSG.RankThree.PartTwo.Census.QuotientWitness
public import CFSG.ClassicalInvolution.SL2Facts

public section

namespace CFSG.RankThree.PartTwo.Census

open CFSG.Assembly CFSG.Assembly.RankThreeEven CFSG.ClassicalInvolution
open scoped MatrixGroups

section SL2

variable {F : Type*} [Field F]

@[expose] def sl2Unipotent (F : Type*) [Field F] : SL(2, F) :=
  ⟨!![1, 1; 0, 1], by simp [Matrix.det_fin_two]⟩

theorem coe_sl2Unipotent_pow (n : ℕ) :
    ((sl2Unipotent F ^ n : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) = !![1, (n : F); 0, 1] := by
  induction n with
  | zero =>
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  | succ n ih =>
    rw [pow_succ, Matrix.SpecialLinearGroup.coe_mul, ih]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [sl2Unipotent, Matrix.mul_apply, Fin.sum_univ_two, add_comm]

theorem not_isPGroup_two_sl2 (h2 : (2 : F) ≠ 0) : ¬ IsPGroup 2 SL(2, F) := by
  intro h
  obtain ⟨k, hk⟩ := h (sl2Unipotent F)
  have h01 := congrArg (fun A : SL(2, F) => (A : Matrix (Fin 2) (Fin 2) F) 0 1) hk
  simp only [coe_sl2Unipotent_pow, Matrix.SpecialLinearGroup.coe_one] at h01
  simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.empty_val', Matrix.cons_val_fin_one,
    Matrix.one_apply_ne (show (0 : Fin 2) ≠ 1 by decide),
    Nat.cast_pow, Nat.cast_ofNat] at h01
  exact pow_ne_zero k h2 h01

end SL2

section Subgroup

variable {H : Type} [Group H] {F : Type*} [Field F] [Finite F]

theorem commutator_eq_self_of_mulEquiv_sl2 {J : Subgroup H} (h4 : 4 ≤ Nat.card F)
    (e : J ≃* SL(2, F)) : ⁅J, J⁆ = J := by
  have hperf : Group.IsPerfect J := isPerfect_of_equiv_sl2 h4 e
  have hJ : (⊤ : Subgroup J).map J.subtype = J := by
    rw [← MonoidHom.range_eq_map, Subgroup.range_subtype]
  conv_lhs => rw [← hJ]
  rw [← Subgroup.map_commutator, ← commutator_def, hperf.commutator_eq_top, hJ]

theorem not_isPGroup_two_of_mulEquiv_sl2 {J : Subgroup H} (hodd : Odd (Nat.card F))
    (e : J ≃* SL(2, F)) : ¬ IsPGroup 2 J := fun h =>
  not_isPGroup_two_sl2 (CFSG.Semidihedral.OddFieldSL2.two_ne_zero_of_odd_card F hodd)
    (h.of_surjective e.toMonoidHom e.surjective)

theorem le_centralizer_of_mulEquiv_sl2 {J : Subgroup H} (h4 : 4 ≤ Nat.card F)
    (hodd : Odd (Nat.card F)) (e : J ≃* SL(2, F)) (M : Subgroup H) (hMJ : M ≤ J)
    (hMn : ∀ g ∈ J, ∀ m ∈ M, g * m * g⁻¹ ∈ M) (hM2 : IsPGroup 2 M) :
    M ≤ Subgroup.centralizer (J : Set H) := by
  have hnormal : (M.subgroupOf J).Normal := ⟨fun a ha g => hMn g g.2 a ha⟩
  have hsub : ∀ x (hx : x ∈ M), (⟨x, hMJ hx⟩ : J) ∈ M.subgroupOf J := fun x hx => hx
  rcases normal_cases_of_equiv_sl2 h4 e _ hnormal with h | h | h
  · intro x hx
    have := hsub x hx
    rw [h, Subgroup.mem_bot] at this
    have hx1 : x = 1 := congrArg Subtype.val this
    rw [hx1]
    exact Subgroup.one_mem _
  · intro x hx
    have hc := hsub x hx
    rw [h, Subgroup.mem_center_iff] at hc
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    exact congrArg Subtype.val (hc ⟨y, hy⟩)
  · exfalso
    refine not_isPGroup_two_of_mulEquiv_sl2 hodd e fun j => ?_
    have hj : j ∈ M.subgroupOf J := by rw [h]; trivial
    obtain ⟨k, hk⟩ := hM2 ⟨(j : H), hj⟩
    have hk' : (j : H) ^ 2 ^ k = 1 := by
      have := congrArg Subtype.val hk
      simpa using this
    exact ⟨k, Subtype.ext (by simpa using hk')⟩

end Subgroup

variable {H : Type} [Group H]

theorem conj_mem_centralizer_of_mem_center (N : Subgroup H) [N.Normal]
    (hNc : N ≤ Subgroup.center H) {t g k : H} (hg : g * t * g⁻¹ * t⁻¹ ∈ N) (hk : k * t = t * k) :
    g * k * g⁻¹ * t = t * (g * k * g⁻¹) := by
  have hw : g⁻¹ * t * g * t⁻¹ ∈ N := by
    have h1 := N.inv_mem ((inferInstance : N.Normal).conj_mem _ hg g⁻¹)
    convert h1 using 1
    group
  set w := g⁻¹ * t * g * t⁻¹ with hw_def
  have hwc := Subgroup.mem_center_iff.mp (hNc hw)
  have hcomm : k * (g⁻¹ * t * g) = (g⁻¹ * t * g) * k := by
    have e1 : g⁻¹ * t * g = w * t := by rw [hw_def]; group
    rw [e1]
    calc k * (w * t) = (k * w) * t := (mul_assoc _ _ _).symm
      _ = (w * k) * t := by rw [hwc k]
      _ = w * (k * t) := mul_assoc _ _ _
      _ = w * (t * k) := by rw [hk]
      _ = (w * t) * k := (mul_assoc _ _ _).symm
  calc g * k * g⁻¹ * t = g * (k * (g⁻¹ * t * g)) * g⁻¹ := by group
    _ = g * ((g⁻¹ * t * g) * k) * g⁻¹ := by rw [hcomm]
    _ = t * (g * k * g⁻¹) := by group

theorem not_isCharTwoType_of_sl2_component [Finite H] (N : Subgroup H) [N.Normal]
    (hNc : N ≤ Subgroup.center H) {t : H} (htN : t ∉ N) (ht2 : t ^ 2 ∈ N) {J : Subgroup H}
    (hJt : ∀ j ∈ J, j * t = t * j) (hJn : ∀ g : H, g * t = t * g → ∀ j ∈ J, g * j * g⁻¹ ∈ J)
    (hJN : J ⊓ N = ⊥) {F : Type*} [Field F] [Finite F] (h4 : 4 ≤ Nat.card F)
    (hodd : Odd (Nat.card F)) (e : J ≃* SL(2, F)) : ¬ IsCharTwoType (H ⧸ N) := by
  refine not_isCharTwoType_quotient N htN ht2 (K := Subgroup.centralizer {t}) (J := J)
    (fun k hk => ?_) (fun g hg k hk => ?_) (fun j hj => ?_) (fun g hg j hj => ?_) hJN
    (commutator_eq_self_of_mulEquiv_sl2 h4 e) (le_centralizer_of_mulEquiv_sl2 h4 hodd e)
    (not_isPGroup_two_of_mulEquiv_sl2 hodd e)
  · rw [Subgroup.mem_centralizer_singleton_iff] at hk
    rw [hk, mul_inv_cancel_right, mul_inv_cancel]
    exact N.one_mem
  · rw [Subgroup.mem_centralizer_singleton_iff] at hk ⊢
    exact conj_mem_centralizer_of_mem_center N hNc hg hk
  · rw [Subgroup.mem_centralizer_singleton_iff]
    exact hJt j hj
  · rw [Subgroup.mem_centralizer_singleton_iff] at hg
    exact hJn g hg j hj

end CFSG.RankThree.PartTwo.Census
