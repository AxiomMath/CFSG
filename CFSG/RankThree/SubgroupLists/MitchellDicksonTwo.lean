module

public import CFSG.RankThree.SubgroupLists.MitchellDickson
public import CFSG.RankThree.SubgroupLists.MitchellDegenerate
public import Certificates.Certificate43
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherFactsL2Maximal
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PSL2Contragredient

public section

namespace CFSG.RankThree.SubgroupLists

open Matrix CFSG.BenderSuzuki.MatrixGroups CFSG.ComponentClassification.AschbacherKnownGroup.FactsL2

section TwoByTwo

variable {F : Type} [Field F]

theorem eq_one_or_neg_of_mul_self (h2 : (2 : F) ≠ 0) {A : Matrix (Fin 2) (Fin 2) F}
    (hdet : A.det = 1) (hA : A * A = 1) : A = 1 ∨ A = -1 := by
  have hCH := fin_two_mul_self A
  rw [hdet, one_smul, hA] at hCH
  have htr : A.trace • A = (2 : F) • (1 : Matrix (Fin 2) (Fin 2) F) := by
    rw [two_smul]
    rw [eq_sub_iff_add_eq] at hCH
    rw [← hCH]
  by_cases h0 : A.trace = 0
  · exfalso
    rw [h0, zero_smul] at htr
    have := congrFun (congrFun htr 0) 0
    simp at this
    exact h2 this.symm
  · have hA' : A = (2 / A.trace) • (1 : Matrix (Fin 2) (Fin 2) F) := by
      rw [div_eq_mul_inv, mul_comm, ← smul_smul, ← htr, smul_smul, inv_mul_cancel₀ h0, one_smul]
    set c := 2 / A.trace
    have hc : c * c = 1 := by
      have := congrFun (congrFun hA 0) 0
      rw [hA'] at this
      simpa [Matrix.mul_apply, Fin.sum_univ_two, Matrix.one_apply] using this
    have : (c - 1) * (c + 1) = 0 := by linear_combination hc
    rcases mul_eq_zero.mp this with h | h
    · left
      rw [hA', show c = 1 by linear_combination h, one_smul]
    · right
      rw [hA', show c = -1 by linear_combination h, neg_one_smul]

theorem mat_two_eq {α : Type*} {X Y : Matrix (Fin 2) (Fin 2) α} (h00 : X 0 0 = Y 0 0)
    (h01 : X 0 1 = Y 0 1) (h10 : X 1 0 = Y 1 0) (h11 : X 1 1 = Y 1 1) : X = Y := by
  ext i j
  fin_cases i <;> fin_cases j <;> assumption

theorem exists_eq_add_smul_of_commute {R A : Matrix (Fin 2) (Fin 2) F}
    (hR : ∀ c : F, R ≠ c • 1) (hA : A * R = R * A) :
    ∃ α β : F, A = α • 1 + β • R := by
  have e := fun i j => congrFun (congrFun hA i) j
  have e00 := e 0 0
  have e01 := e 0 1
  have e10 := e 1 0
  simp only [Matrix.mul_apply, Fin.sum_univ_two] at e00 e01 e10
  have key : ∀ α β : F, A 0 0 = α + β * R 0 0 → A 0 1 = β * R 0 1 → A 1 0 = β * R 1 0 →
      A 1 1 = α + β * R 1 1 → A = α • 1 + β • R := by
    intro α β h00 h01 h10 h11
    apply mat_two_eq <;>
      simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Matrix.one_apply_eq,
        Matrix.one_apply_ne (show (0 : Fin 2) ≠ 1 by decide),
        Matrix.one_apply_ne (show (1 : Fin 2) ≠ 0 by decide), mul_one, mul_zero, zero_add]
    · exact h00
    · exact h01
    · exact h10
    · exact h11
  by_cases hb : R 0 1 = 0
  · by_cases hc : R 1 0 = 0
    · have had : R 0 0 - R 1 1 ≠ 0 := by
        intro h
        apply hR (R 0 0)
        apply mat_two_eq <;>
          simp only [Matrix.smul_apply, smul_eq_mul, Matrix.one_apply_eq,
            Matrix.one_apply_ne (show (0 : Fin 2) ≠ 1 by decide),
            Matrix.one_apply_ne (show (1 : Fin 2) ≠ 0 by decide), mul_one, mul_zero]
        · exact hb
        · exact hc
        · linear_combination -h
      obtain ⟨β, hβ⟩ : ∃ β, β * (R 0 0 - R 1 1) = A 0 0 - A 1 1 :=
        ⟨(A 0 0 - A 1 1) / (R 0 0 - R 1 1), div_mul_cancel₀ _ had⟩
      have h01 : A 0 1 = 0 := by
        have : A 0 1 * (R 0 0 - R 1 1) = 0 := by rw [hb] at e01; linear_combination -e01
        exact (mul_eq_zero.mp this).resolve_right had
      have h10 : A 1 0 = 0 := by
        have : A 1 0 * (R 0 0 - R 1 1) = 0 := by rw [hc] at e10; linear_combination e10
        exact (mul_eq_zero.mp this).resolve_right had
      refine ⟨A 0 0 - β * R 0 0, β, key _ _ (by ring) (by rw [hb, mul_zero]; exact h01)
        (by rw [hc, mul_zero]; exact h10) (by linear_combination hβ)⟩
    · obtain ⟨β, hβ⟩ : ∃ β, β * R 1 0 = A 1 0 := ⟨A 1 0 / R 1 0, div_mul_cancel₀ _ hc⟩
      have h01 : A 0 1 = 0 := by
        have : A 0 1 * R 1 0 = 0 := by rw [hb] at e00; linear_combination e00
        exact (mul_eq_zero.mp this).resolve_right hc
      refine ⟨A 0 0 - β * R 0 0, β, key _ _ (by ring) (by rw [hb, mul_zero]; exact h01) hβ.symm
        ?_⟩
      apply mul_right_cancel₀ hc
      linear_combination e10 + (R 0 0 - R 1 1) * hβ
  · obtain ⟨β, hβ⟩ : ∃ β, β * R 0 1 = A 0 1 := ⟨A 0 1 / R 0 1, div_mul_cancel₀ _ hb⟩
    refine ⟨A 0 0 - β * R 0 0, β, key _ _ (by ring) hβ.symm ?_ ?_⟩
    · apply mul_right_cancel₀ hb
      linear_combination -e00 - R 1 0 * hβ
    · apply mul_right_cancel₀ hb
      linear_combination -e01 + (R 0 0 - R 1 1) * hβ

theorem commute_of_commute_of_ne_scalar {R A B : Matrix (Fin 2) (Fin 2) F}
    (hR : ∀ c : F, R ≠ c • 1) (hA : A * R = R * A) (hB : B * R = R * B) : A * B = B * A := by
  obtain ⟨a, b, rfl⟩ := exists_eq_add_smul_of_commute hR hA
  obtain ⟨c, d, rfl⟩ := exists_eq_add_smul_of_commute hR hB
  simp only [Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul,
    Matrix.mul_one]
  module

end TwoByTwo

section Dickson

variable {F : Type} [Field F] [Finite F] {p f : ℕ} [Fact p.Prime]

theorem nonempty_mulEquiv_alternating_five (hF : Nat.card F = p ^ f)
    (X : Subgroup (PSL2MatrixGroup F)) (hX : ¬ p ∣ Nat.card X) {x y : X} (hx : orderOf x = 5)
    (hy : 2 < orderOf y) (hxy : x * y ≠ y * x) : Nonempty (X ≃* alternatingGroup (Fin 5)) := by
  rcases CFSG.Glauberman.Dickson.huppert_II_8_24_dickson_case_no_p_part hF X hX with
    ⟨_, _, _, hcyc⟩ | ⟨_, _, _, ⟨e⟩⟩ | ⟨_, ⟨e⟩⟩ | ⟨_, ⟨e⟩⟩ | ⟨_, ⟨e⟩⟩
  · exfalso
    apply hxy
    obtain ⟨g, hg⟩ := hcyc.exists_generator
    obtain ⟨a, ha⟩ := Subgroup.mem_zpowers_iff.mp (hg x)
    obtain ⟨b, hb⟩ := Subgroup.mem_zpowers_iff.mp (hg y)
    rw [← ha, ← hb, ← _root_.zpow_add, ← _root_.zpow_add, add_comm]
  · exact absurd (commute_of_equiv_dihedral e (by rw [hx]; norm_num) hy) hxy
  · exfalso
    rcases orderOf_dvd_of_equiv_alternating_four e x with h | h <;> rw [hx] at h <;> norm_num at h
  · exfalso
    rcases orderOf_dvd_of_equiv_perm_four e x with h | h <;> rw [hx] at h <;> norm_num at h
  · exact ⟨e⟩

theorem nonempty_mulEquiv_perm_four (hF : Nat.card F = p ^ f)
    (X : Subgroup (PSL2MatrixGroup F)) (hX : ¬ p ∣ Nat.card X) {x y : X} (hx : orderOf x = 4)
    (hy : orderOf y = 4) (hxy : x * y ≠ y * x) : Nonempty (X ≃* Equiv.Perm (Fin 4)) := by
  rcases CFSG.Glauberman.Dickson.huppert_II_8_24_dickson_case_no_p_part hF X hX with
    ⟨_, _, _, hcyc⟩ | ⟨_, _, _, ⟨e⟩⟩ | ⟨_, ⟨e⟩⟩ | ⟨_, ⟨e⟩⟩ | ⟨_, ⟨e⟩⟩
  · exfalso
    apply hxy
    obtain ⟨g, hg⟩ := hcyc.exists_generator
    obtain ⟨a, ha⟩ := Subgroup.mem_zpowers_iff.mp (hg x)
    obtain ⟨b, hb⟩ := Subgroup.mem_zpowers_iff.mp (hg y)
    rw [← ha, ← hb, ← _root_.zpow_add, ← _root_.zpow_add, add_comm]
  · exact absurd (commute_of_equiv_dihedral e (by rw [hx]; norm_num) (by rw [hy]; norm_num)) hxy
  · exfalso
    rcases orderOf_dvd_of_equiv_alternating_four e x with h | h <;> rw [hx] at h <;> norm_num at h
  · exact ⟨e⟩
  · exfalso
    rcases orderOf_dvd_of_equiv_alternating_five e x with h | h | h <;> rw [hx] at h <;>
      norm_num at h

theorem eq_of_le_of_mulEquiv_alternating_five (hF : Nat.card F = p ^ f)
    {X Y : Subgroup (PSL2MatrixGroup F)} (hXY : X ≤ Y) (hY : ¬ p ∣ Nat.card Y)
    (eX : X ≃* alternatingGroup (Fin 5)) : X = Y := by
  have hX60 : Nat.card X = 60 := by
    rw [Nat.card_congr eX.toEquiv, nat_card_alternatingGroup, Nat.card_fin]
    decide
  have key : ∃ x y : X, orderOf x = 5 ∧ orderOf y = 3 ∧ x * y ≠ y * x := by
    have h1 : finRotate 5 ∈ alternatingGroup (Fin 5) := by
      rw [Equiv.Perm.mem_alternatingGroup]; decide
    have h2 : Equiv.swap (0 : Fin 5) 1 * Equiv.swap 0 2 ∈ alternatingGroup (Fin 5) := by
      rw [Equiv.Perm.mem_alternatingGroup]; decide
    refine ⟨eX.symm ⟨finRotate 5, h1⟩, eX.symm ⟨Equiv.swap 0 1 * Equiv.swap 0 2, h2⟩, ?_, ?_,
      ?_⟩
    · rw [MulEquiv.orderOf_eq, Subgroup.orderOf_mk]
      have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
      rw [orderOf_eq_prime_iff]
      exact ⟨by decide, by decide⟩
    · rw [MulEquiv.orderOf_eq, Subgroup.orderOf_mk]
      have : Fact (Nat.Prime 3) := ⟨by norm_num⟩
      rw [orderOf_eq_prime_iff]
      exact ⟨by decide, by decide⟩
    · rw [← map_mul, ← map_mul, Ne, eX.symm.injective.eq_iff]
      intro h
      have := congrArg Subtype.val h
      simp only [Subgroup.coe_mul] at this
      revert this
      decide
  obtain ⟨x, y, hx, hy, hxy⟩ := key
  set ι := Subgroup.inclusion hXY
  have hι : Function.Injective ι := Subgroup.inclusion_injective hXY
  have hx' : orderOf (ι x) = 5 := by rw [orderOf_injective ι hι, hx]
  have hy' : 2 < orderOf (ι y) := by rw [orderOf_injective ι hι, hy]; norm_num
  have hxy' : ι x * ι y ≠ ι y * ι x := by
    rw [← map_mul, ← map_mul]
    exact hι.ne hxy
  obtain ⟨eY⟩ := nonempty_mulEquiv_alternating_five hF Y hY hx' hy' hxy'
  have hY60 : Nat.card Y = 60 := by
    rw [Nat.card_congr eY.toEquiv, nat_card_alternatingGroup, Nat.card_fin]
    decide
  exact Subgroup.eq_of_le_of_card_ge hXY (by rw [hX60, hY60])

end Dickson

end CFSG.RankThree.SubgroupLists
