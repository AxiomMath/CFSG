module

public import CFSG.LocalAnalysis.ShultStronglyClosedTI.OddPrimeInvertersLinear
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.OddPrimeInvertersSuzuki

public noncomputable section

namespace CFSG.ShultStronglyClosedTI.OddPrimeInverters

open CFSG.BenderSuzuki.MatrixGroups

theorem exists_card_eq_two_pow_of_even {k : Type} [Field k] [Finite k]
    (hk : Even (Nat.card k)) : ∃ f : ℕ, Nat.card k = 2 ^ f := by
  let : Fintype k := Fintype.ofFinite k
  obtain ⟨p, -, n, hp, hcard⟩ := FiniteField.card' k
  rw [← Fintype.card_eq_nat_card, hcard] at hk
  have hp2 : p = 2 := ((Nat.prime_dvd_prime_iff_eq Nat.prime_two hp).mp
    (Nat.prime_two.dvd_of_dvd_pow (even_iff_two_dvd.mp hk))).symm
  exact ⟨n, by rw [← Fintype.card_eq_nat_card, hcard, hp2]⟩

theorem psl2_oddPrimeInvertersAndSplitFusion_of_even
    {k : Type} [Field k] [Finite k]
    (hk : Even (Nat.card k)) (hk4 : 4 ≤ Nat.card k) :
    OddPrimeInvertersAndSplitFusion (PSL2MatrixGroup k) (Nat.card k) := by
  obtain ⟨f, hf⟩ := exists_card_eq_two_pow_of_even hk
  refine psl2_oddPrimeInvertersAndSplitFusion (f := f) ?_ hf
  by_contra h
  rw [hf] at hk4
  interval_cases f <;> simp at hk4

theorem oddPrimeInvertersAndSplitFusion_of_mulEquiv_psl2
    {F : Type*} [Group F] {k : Type}
    [Field k] [Finite k] {f : ℕ} (hf : 2 ≤ f) (hk : Nat.card k = 2 ^ f)
    (e : F ≃* PSL2MatrixGroup k) : OddPrimeInvertersAndSplitFusion F (Nat.card k) :=
  (psl2_oddPrimeInvertersAndSplitFusion hf hk).of_mulEquiv e

theorem oddPrimeInvertersAndSplitFusion_of_mulEquiv_suzukiMatrixGroup
    {F : Type*} [Group F]
    {m : ℕ} (hm : 1 ≤ m) (e : F ≃* SuzukiMatrixGroup m) :
    OddPrimeInvertersAndSplitFusion F (2 ^ (2 * m + 1)) :=
  (suzukiMatrixGroup_oddPrimeInvertersAndSplitFusion m hm).of_mulEquiv e

theorem linear_suzuki_odd_prime_inverters_and_split_fusion
    {F : Type*} [Group F] {q : ℕ}
    (hF : (∃ (k : Type) (_ : Field k) (_ : Finite k), Even (Nat.card k) ∧ 4 ≤ Nat.card k ∧
        q = Nat.card k ∧ Nonempty (F ≃* PSL2MatrixGroup k)) ∨
      (∃ (a : ℕ) (k : Type) (_ : Field k) (_ : Finite k), 1 ≤ a ∧
        Nat.card k = 2 ^ (2 * a + 1) ∧ q = Nat.card k ∧
        Nonempty (F ≃* CFSG.Blueprint.suzukiGroup a k))) :
    OddPrimeInvertersAndSplitFusion F q := by
  rcases hF with ⟨k, _, _, hk, hk4, rfl, ⟨e⟩⟩ | ⟨a, k, _, _, ha, hk, rfl, ⟨e⟩⟩
  · exact (psl2_oddPrimeInvertersAndSplitFusion_of_even hk hk4).of_mulEquiv e
  · exact (suzukiGroup_oddPrimeInvertersAndSplitFusion ha hk).of_mulEquiv e

end CFSG.ShultStronglyClosedTI.OddPrimeInverters
