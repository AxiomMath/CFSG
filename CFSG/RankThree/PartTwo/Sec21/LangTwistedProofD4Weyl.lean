module

public import CFSG.RankThree.PartOne.KGD.D4Weyl

public noncomputable section

namespace CFSG.RankThree.PartTwo.Sec8.LangTwistedProof

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.Chevalley
  CFSG.RankThree.PartOne.KGD
open scoped Matrix

@[expose] def d4OrderThreeTab : List ℕ :=
  [124595, 4106645, 32036834, 32065980, 31887733, 12167021, 47959904, 47986193, 4246406,
    12015832, 51870906, 52011368, 266383, 12044563, 59834797, 60001548, 158289, 4180843,
    76811780, 77137288, 77178645, 49074326, 5547788, 1565439, 87857558, 89162372, 59911784,
    87744856, 51976716, 87785107, 77109869, 47898805]

theorem d4_tab_order_three :
    ∀ e ∈ d4WeylTab, d4Mat e ^ 3 = 1 → d4Mat e ≠ 1 → e ∈ d4OrderThreeTab := by
  decide +kernel

theorem d4_tab_commute_order_three : ∀ e₁ ∈ d4OrderThreeTab, ∀ e₂ ∈ d4OrderThreeTab,
    d4Mat e₁ * d4Mat e₂ = d4Mat e₂ * d4Mat e₁ → d4Mat e₂ = d4Mat e₁ ∨ d4Mat e₂ = d4Mat e₁ ^ 2 := by
  decide +kernel

theorem matrix_eq_of_mulVec_eq {A B : Matrix (Fin Tag.D4.rank) (Fin Tag.D4.rank) ℤ}
    (h : ∀ v, A *ᵥ v = B *ᵥ v) : A = B := by
  ext i j
  have hj := congrFun (h (Pi.single j 1)) i
  simpa [Matrix.mulVec_single] using hj

theorem exists_d4Mat (w : WeylGroup Tag.D4) :
    ∃ e ∈ d4WeylTab, ∀ n : ℕ, ∀ v, (w ^ n) • v = d4Mat e ^ n *ᵥ v := by
  obtain ⟨e, he, hw⟩ := exists_mem_d4WeylTab w
  exact ⟨e, he, fun n v => pow_smul_eq_d4Mat_pow_mulVec w hw n v⟩

theorem not_nine_dvd_card_weylGroup_D4 : ¬ 9 ∣ Nat.card (WeylGroup TwistTag.D4.tag) := by
  intro h9
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have h9' : 3 ^ 2 ∣ Nat.card (WeylGroup Tag.D4) := h9
  obtain ⟨H, hH⟩ := Sylow.exists_subgroup_card_pow_prime (G := WeylGroup Tag.D4) 3 h9'
  have hcomm : ∀ a b : H, a * b = b * a := fun a b =>
    (IsPGroup.isMulCommutative_of_card_eq_prime_sq hH).is_comm.comm a b
  have h3 : ∀ x : H, x ^ 3 = 1 := by
    intro x
    have h9' : x ^ 9 = 1 := by
      have h := (pow_card_eq_one' : x ^ Nat.card H = 1)
      rwa [hH] at h
    have h12 : x ^ 12 = 1 := Subtype.ext (by
      rw [Subgroup.coe_pow, Subgroup.coe_one]
      exact d4_weyl_pow_twelve x)
    calc x ^ 3 = x ^ 12 * (x ^ 9)⁻¹ := by
          rw [show (12 : ℕ) = 3 + 9 from rfl, pow_add, mul_inv_cancel_right]
      _ = 1 := by rw [h12, h9', inv_one, one_mul]
  have hcard1 : 1 < Nat.card H := by rw [hH]; norm_num
  have : Nontrivial H := Finite.one_lt_card_iff_nontrivial.1 hcard1
  obtain ⟨a, ha1⟩ := exists_ne (1 : H)
  obtain ⟨b, hb⟩ : ∃ b : H, b ≠ 1 ∧ b ≠ a ∧ b ≠ a ^ 2 := by
    by_contra hcon
    push Not at hcon
    have hsurj : Function.Surjective (fun i : Fin 3 => a ^ (i : ℕ)) := by
      intro b
      by_cases hb1 : b = 1
      · exact ⟨0, by rw [hb1]; exact pow_zero a⟩
      by_cases hba : b = a
      · exact ⟨1, by rw [hba]; exact pow_one a⟩
      exact ⟨2, (hcon b hb1 hba).symm⟩
    have := Nat.card_le_card_of_surjective _ hsurj
    rw [hH, Nat.card_eq_fintype_card, Fintype.card_fin] at this
    norm_num at this
  obtain ⟨hb1, hba, hba2⟩ := hb
  obtain ⟨ea, hea, hA⟩ := exists_d4Mat (a : WeylGroup Tag.D4)
  obtain ⟨eb, heb, hB⟩ := exists_d4Mat (b : WeylGroup Tag.D4)
  have hA1 : ∀ v, (a : WeylGroup Tag.D4) • v = d4Mat ea *ᵥ v := fun v => by
    simpa using hA 1 v
  have hB1 : ∀ v, (b : WeylGroup Tag.D4) • v = d4Mat eb *ᵥ v := fun v => by
    simpa using hB 1 v
  have hcube : ∀ (x : H) (e : ℕ), (∀ n : ℕ, ∀ v, ((x : WeylGroup Tag.D4) ^ n) • v =
      d4Mat e ^ n *ᵥ v) → d4Mat e ^ 3 = 1 := by
    intro x e hx
    refine matrix_eq_of_mulVec_eq fun v => ?_
    rw [← hx 3 v, Matrix.one_mulVec, ← Subgroup.coe_pow, h3 x, Subgroup.coe_one, one_smul]
  have hne1 : ∀ (x : H) (e : ℕ), (∀ v, (x : WeylGroup Tag.D4) • v = d4Mat e *ᵥ v) →
      x ≠ 1 → d4Mat e ≠ 1 := by
    intro x e hx hx1 he1
    apply hx1
    apply Subtype.ext
    refine FaithfulSMul.eq_of_smul_eq_smul (α := Fin Tag.D4.rank → ℤ) fun v => ?_
    rw [hx v, he1, Matrix.one_mulVec, Subgroup.coe_one, one_smul]
  have hea3 := d4_tab_order_three ea hea (hcube a ea hA) (hne1 a ea hA1 ha1)
  have heb3 := d4_tab_order_three eb heb (hcube b eb hB) (hne1 b eb hB1 hb1)
  have hAB : d4Mat ea * d4Mat eb = d4Mat eb * d4Mat ea := by
    refine matrix_eq_of_mulVec_eq fun v => ?_
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, ← hB1, ← hA1, ← hA1, ← hB1, ← mul_smul,
      ← mul_smul, ← Subgroup.coe_mul, ← Subgroup.coe_mul, hcomm a b]
  rcases d4_tab_commute_order_three ea hea3 eb heb3 hAB with h | h
  · apply hba
    apply Subtype.ext
    refine FaithfulSMul.eq_of_smul_eq_smul (α := Fin Tag.D4.rank → ℤ) fun v => ?_
    rw [hB1, hA1, h]
  · apply hba2
    apply Subtype.ext
    refine FaithfulSMul.eq_of_smul_eq_smul (α := Fin Tag.D4.rank → ℤ) fun v => ?_
    rw [hB1, h, Subgroup.coe_pow, hA 2 v]

end CFSG.RankThree.PartTwo.Sec8.LangTwistedProof
