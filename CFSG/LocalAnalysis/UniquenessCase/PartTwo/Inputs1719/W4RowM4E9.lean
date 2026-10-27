module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4RowE9
import CFSG.GroupTheory.PGroup.ElemAbelianSq

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Row

open CFSG.Quasithin CFSG.HardMathSupport.Meierfrankenfeld.FFToolkit Subgroup

private theorem m4_b_not_mem_zpowers_a {G : Type} [Group G] [Finite G] {a b : G}
    (ha : a ^ 3 = 1) (ha1 : a ≠ 1) (hba : ∀ j < 3, b ≠ a ^ j) :
    b ∉ Subgroup.zpowers a := by
  classical
  have hao : orderOf a = 3 := orderOf_eq_prime ha ha1
  intro hbA
  rw [mem_zpowers_iff_mem_range_orderOf] at hbA
  simp only [Finset.mem_image, Finset.mem_range] at hbA
  obtain ⟨j, hj, hbj⟩ := hbA
  exact hba j (by rw [hao] at hj; exact hj) hbj.symm

private theorem m4_mul_eq_cube_of_rel {i0 i1 i2 i3 c0 c1 c2 c3 K : ℕ}
    (hK : 0 < K) (hrel0 : i0 * c0 = K) (hrel1 : i1 * c1 = K) (hrel2 : i2 * c2 = K)
    (hrel3 : i3 * c3 = K) (hprod : K = c0 * c1 * c2 * c3) :
    i0 * i1 * i2 * i3 = K ^ 3 := by
  have h1 : i0 * c0 * (i1 * c1) * (i2 * c2) * (i3 * c3) = K ^ 4 := by
    rw [hrel0, hrel1, hrel2, hrel3]; ring
  have h2 : i0 * i1 * i2 * i3 * (c0 * c1 * c2 * c3) = K ^ 4 := by
    rw [← h1]; ring
  rw [← hprod] at h2
  have h3 : i0 * i1 * i2 * i3 * K = K ^ 3 * K := by rw [h2]; ring
  exact Nat.mul_right_cancel hK h3

theorem index_fixV_cube_eq_prod_of_e9 {W : Type} [CommGroup W] [Finite W]
    (hW : ∀ w : W, w * w = 1) {a b : MulAut W} (ha : a ^ 3 = 1) (hb : b ^ 3 = 1)
    (ha1 : a ≠ 1) (hab : a * b = b * a) (hba : ∀ j < 3, b ≠ a ^ j) :
    (fixV (zpowers a ⊔ zpowers b)).index ^ 3 =
      (fixV (zpowers a)).index * (fixV (zpowers b)).index *
        (fixV (zpowers (a * b))).index * (fixV (zpowers (a * b ^ 2))).index := by
  classical
  let A : Subgroup (MulAut W) := Subgroup.zpowers a ⊔ Subgroup.zpowers b
  have hA : A = Subgroup.zpowers a ⊔ Subgroup.zpowers b := rfl
  have hb1 : b ≠ 1 := by
    have := hba 0 (by norm_num)
    simpa using this
  have hao : orderOf a = 3 := orderOf_eq_prime ha ha1
  have hbo : orderOf b = 3 := orderOf_eq_prime hb hb1
  have hcarda : Nat.card ↥(Subgroup.zpowers a) = 3 := by rw [Nat.card_zpowers, hao]
  have hcommXA : ∀ x ∈ Subgroup.zpowers a, x * b = b * x := by
    intro x hx
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 hx
    exact (Commute.zpow_left (show Commute a b from hab) n).eq
  obtain ⟨hAea, hAsupcard⟩ := CFSG.GroupTheory.isElemAbelian_sup_zpowers_of_commute
    (r := 3) (X := Subgroup.zpowers a) (v := b) hcarda hbo
    (m4_b_not_mem_zpowers_a ha ha1 hba) hcommXA
  have hAcard : Nat.card ↥A = 9 := by simpa [A] using hAsupcard
  have hAc : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hAea.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  have hAp : ∀ x ∈ A, x ^ 3 = 1 := hAea.2
  have hodd : Odd (Nat.card ↥A) := by rw [hAcard]; norm_num
  have hfix : fixV A ⊓ (normHom A).ker = ⊥ := fixV_inf_ker_normHom hW hodd
  have hcardK : Nat.card ↥(fixV A) * Nat.card ↥(normHom A).ker = Nat.card W :=
    card_ker_normHom_mul hW hodd
  have hKinv : ∀ x ∈ A, ∀ k ∈ (normHom A).ker, x k ∈ (normHom A).ker := fun x hx k hk =>
    map_ker_normHom (Subgroup.le_normalizer hx) hk
  have hga : a ∈ A := by
    rw [hA]; exact Subgroup.mem_sup_left (Subgroup.mem_zpowers a)
  have hgb : b ∈ A := by
    rw [hA]; exact Subgroup.mem_sup_right (Subgroup.mem_zpowers b)
  have hgab : a * b ∈ A := by
    rw [hA]
    exact Subgroup.mul_mem_sup (Subgroup.mem_zpowers a) (Subgroup.mem_zpowers b)
  have hgab2 : a * b ^ 2 ∈ A := by
    rw [hA]
    exact Subgroup.mul_mem_sup (Subgroup.mem_zpowers a)
      (Subgroup.pow_mem (Subgroup.zpowers b) (Subgroup.mem_zpowers b) 2)
  have hrel0 := index_mul_card_inf_ker_eq hga hfix hcardK
  have hrel1 := index_mul_card_inf_ker_eq hgb hfix hcardK
  have hrel2 := index_mul_card_inf_ker_eq hgab hfix hcardK
  have hrel3 := index_mul_card_inf_ker_eq hgab2 hfix hcardK
  have hprod := e9_hyperplane_card hW hA ha hb ha1 hab hba hAc hAp hAcard hKinv hfix
  have hidx : (fixV A).index = Nat.card ↥(normHom A).ker := by
    have h1 := Subgroup.card_mul_index (fixV A)
    have hpos : 0 < Nat.card ↥(fixV A) := Nat.card_pos
    have h2 : Nat.card ↥(fixV A) * (fixV A).index =
        Nat.card ↥(fixV A) * Nat.card ↥(normHom A).ker := by rw [h1, hcardK]
    exact Nat.mul_left_cancel hpos h2
  have hKpos : 0 < Nat.card ↥(normHom A).ker := Nat.card_pos
  have hmain : (fixV (Subgroup.zpowers a)).index * (fixV (Subgroup.zpowers b)).index *
        (fixV (Subgroup.zpowers (a * b))).index *
        (fixV (Subgroup.zpowers (a * b ^ 2))).index =
      (Nat.card ↥(normHom A).ker) ^ 3 :=
    m4_mul_eq_cube_of_rel hKpos hrel0 hrel1 hrel2 hrel3 hprod
  rw [← hA, hidx]
  exact hmain.symm

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Row
