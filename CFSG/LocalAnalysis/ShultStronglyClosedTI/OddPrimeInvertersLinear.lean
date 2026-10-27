module

public import CFSG.LocalAnalysis.ShultStronglyClosedTI.OddPrimeInvertersBasic
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.OddPrimeInvertersFrobenius
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionDenominatorLinearInvolutions
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Section11Lemma114Models
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.II.theorem_6_14
public import CFSG.ThirdParty.QiuzhenCFSG.Glauberman.DicksonSplitTorusMatrices
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionDenominatorOrbit

public noncomputable section

namespace CFSG.ShultStronglyClosedTI.OddPrimeInverters

open CFSG.BenderSuzuki CFSG.BenderSuzuki.MatrixGroups CFSG.Glauberman.Dickson
open CFSG.ProperTwoGeneratedCore.LocalCriterionDenominator
open scoped MatrixGroups

theorem commutator_eq_top_of_mulEquiv {G H : Type*} [Group G] [Group H] (e : G ≃* H)
    (h : commutator H = ⊤) : commutator G = ⊤ := by
  apply Subgroup.map_injective (f := e.toMonoidHom) e.injective
  rw [Subgroup.map_top_of_surjective _ e.surjective, commutator_def, Subgroup.map_commutator,
    Subgroup.map_top_of_surjective _ e.surjective, ← commutator_def, h]

theorem linear_card_factor {q : ℕ} (hq : 1 ≤ q) : q * (q ^ 2 - 1) = (q - 1) * (q * (q + 1)) := by
  obtain ⟨r, rfl⟩ : ∃ r, q = r + 1 := ⟨q - 1, by omega⟩
  rw [Nat.add_sub_cancel, Nat.sub_eq_of_eq_add (show (r + 1) ^ 2 = r * (r + 2) + 1 by ring)]
  ring

theorem linear_card_coprime {q : ℕ} (hq : Even q) (hq1 : 1 ≤ q) :
    Nat.Coprime (q - 1) (q * (q + 1)) := by
  obtain ⟨r, rfl⟩ : ∃ r, q = r + 1 := ⟨q - 1, by omega⟩
  rw [Nat.add_sub_cancel]
  have hr : Odd r := by
    rcases Nat.even_or_odd r with h | h
    · exact absurd hq (Nat.not_even_iff_odd.mpr h.add_one)
    · exact h
  refine Nat.Coprime.mul_right (Nat.coprime_self_add_right.mpr (Nat.coprime_one_right r)) ?_
  rw [add_assoc]
  exact Nat.coprime_self_add_right.mpr (Nat.coprime_two_right.mpr hr)

variable {K : Type} [Field K] [Finite K]

theorem charP_two_of_card_eq_two_pow {f : ℕ} (hK : Nat.card K = 2 ^ f) : CharP K 2 := by
  let : Fintype K := Fintype.ofFinite K
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact charP_of_card_eq_prime_pow (by rw [Fintype.card_eq_nat_card, hK])

omit [Finite K] in
theorem splitTorusSLHom_injective : Function.Injective (splitTorusSLHom K) := by
  intro a b h
  have h00 := congrArg (fun A : SL(2, K) => (A : Matrix (Fin 2) (Fin 2) K) 0 0) h
  exact Units.ext (by simpa using h00)

omit [Finite K] in
theorem card_range_splitTorusSLHom : Nat.card (splitTorusSLHom K).range = Nat.card K - 1 := by
  rw [← Nat.card_units K]
  exact Nat.card_congr (MonoidHom.ofInjective splitTorusSLHom_injective).symm.toEquiv

section CharTwo

variable [CharP K 2]

def sl2EquivPSL2Binary {f : ℕ} (hf : 0 < f) (hK : Nat.card K = 2 ^ f) :
    SL(2, K) ≃* PSL2BinaryMatrixGroup f :=
  psl2CharTwoEquivSL.symm.trans (pslFieldEquiv (binaryFieldEquiv f hf hK))

theorem sl2_commutator_eq_top {f : ℕ} (hf : 2 ≤ f) (hK : Nat.card K = 2 ^ f) :
    commutator SL(2, K) = ⊤ :=
  commutator_eq_top_of_mulEquiv (sl2EquivPSL2Binary (by omega) hK)
    ((IsSimpleBenderGroupAtExponent.isPSL2 ⟨MulEquiv.refl _⟩).isPerfect hf)

theorem sl2_oddSylow_isCyclic
    {f : ℕ} (hf : 2 ≤ f) (hK : Nat.card K = 2 ^ f) :
    ∀ p [Fact p.Prime], p ≠ 2 → ∀ P : Sylow p SL(2, K), IsCyclic P :=
  lemma114_psl2_oddSylow_isCyclic_of_equiv hf (sl2EquivPSL2Binary (by omega) hK)

theorem sl2_card : Nat.card SL(2, K) = Nat.card K * (Nat.card K ^ 2 - 1) := by
  have h1 := External.huppert614_card_psl_mul_center (K := K)
  rw [External.huppert614_card_center_of_neg_one_eq_one (CharTwo.neg_eq 1), mul_one] at h1
  rw [← h1]
  exact Nat.card_congr psl2CharTwoEquivSL.symm.toEquiv

omit [Finite K] in
@[expose] def sl2Swap : SL(2, K) :=
  ⟨!![0, 1; 1, 0], by simp [Matrix.det_fin_two, CharTwo.neg_eq]⟩

omit [Finite K] in
theorem sl2Swap_mul_self : sl2Swap * sl2Swap = (1 : SL(2, K)) := by
  apply Subtype.ext
  change !![0, 1; 1, 0] * !![0, 1; 1, 0] = (1 : Matrix (Fin 2) (Fin 2) K)
  simp [Matrix.one_fin_two]

omit [Finite K] in
theorem sl2Swap_conj_splitTorus (a : Kˣ) :
    sl2Swap * splitTorusSLHom K a * sl2Swap⁻¹ = (splitTorusSLHom K a)⁻¹ := by
  rw [inv_eq_of_mul_eq_one_right sl2Swap_mul_self, ← map_inv]
  apply Subtype.ext
  change !![0, 1; 1, 0] * (splitTorusSLHom K a : Matrix (Fin 2) (Fin 2) K) * !![0, 1; 1, 0] =
    (splitTorusSLHom K a⁻¹ : Matrix (Fin 2) (Fin 2) K)
  simp

theorem sl2_conj_eq_inv_of_frobenius {f : ℕ} (hK : Nat.card K = 2 ^ f) (p : ℕ) (hp : p.Prime)
    (hp2 : p ≠ 2) (hpq : ¬ p ∣ Nat.card K - 1) (y g : SL(2, K))
    (hy : IsPGroup p (Subgroup.zpowers y)) (hgy : g * y * g⁻¹ ∈ Subgroup.zpowers y)
    (hne : g * y * g⁻¹ ≠ y) : g * y * g⁻¹ = y⁻¹ := by
  let : Fintype K := Fintype.ofFinite K
  have : Fact p.Prime := ⟨hp⟩
  have hq : Fintype.card K = Nat.card K := Fintype.card_eq_nat_card
  have hq1 : 1 ≤ Nat.card K := Nat.card_pos
  have hdvd : orderOf y ∣ Nat.card K + 1 := by
    obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hy
    rw [Nat.card_zpowers] at hn
    have hG : orderOf y ∣ (Nat.card K - 1) * (Nat.card K * (Nat.card K + 1)) := by
      rw [← linear_card_factor hq1, ← sl2_card]
      exact orderOf_dvd_natCard y
    have hc1 : Nat.Coprime (orderOf y) (Nat.card K - 1) :=
      hn ▸ Nat.Coprime.pow_left _ ((Nat.Prime.coprime_iff_not_dvd hp).mpr hpq)
    have hc2 : Nat.Coprime (orderOf y) (Nat.card K) := by
      rw [hn, hK]
      exact Nat.Coprime.pow _ _ ((Nat.coprime_primes hp Nat.prime_two).mpr hp2)
    exact hc2.dvd_of_dvd_mul_left (hc1.dvd_of_dvd_mul_left hG)
  have hyq : y ^ Nat.card K = y⁻¹ :=
    eq_inv_of_mul_eq_one_left (by rw [← pow_succ]; exact orderOf_dvd_iff_pow_eq_one.mp hdvd)
  refine conj_eq_inv_of_lt_two hyq ?_ hne
  have h := exists_lt_conj_eq_pow_card_pow_of_dvd (K := K) (e := 0) (by norm_num)
    Matrix.SpecialLinearGroup.toGL Matrix.SpecialLinearGroup.toGL_injective hp hp2 hy
    (by rw [pow_zero, pow_one, hq]; exact hdvd) hgy
  simpa only [hq] using h

theorem sl2_oddPrimeInvertersAndSplitFusion
    {f : ℕ} (hf : 2 ≤ f) (hK : Nat.card K = 2 ^ f) :
    OddPrimeInvertersAndSplitFusion SL(2, K) (Nat.card K) := by
  have hq1 : 1 ≤ Nat.card K := Nat.card_pos
  have hqeven : Even (Nat.card K) := by
    rw [hK]
    exact (Nat.even_pow' (by omega)).mpr even_two
  refine oddPrimeInvertersAndSplitFusion_of_data (sl2_commutator_eq_top hf hK)
    (sl2_oddSylow_isCyclic hf hK) (fun t ht => sl2_involution_centralizer_isPGroup t ht)
    (by rw [sl2_card, linear_card_factor hq1]) (linear_card_coprime hqeven hq1)
    (splitTorusSLHom K).range card_range_splitTorusSLHom sl2Swap ?_
    (fun p hp hp2 hpq y g hy hgy hne =>
      Or.inl (sl2_conj_eq_inv_of_frobenius hK p hp hp2 hpq y g hy hgy hne))
  rintro _ ⟨a, rfl⟩
  exact sl2Swap_conj_splitTorus a

end CharTwo

theorem psl2_oddPrimeInvertersAndSplitFusion
    {f : ℕ} (hf : 2 ≤ f) (hK : Nat.card K = 2 ^ f) :
    OddPrimeInvertersAndSplitFusion (PSL2MatrixGroup K) (Nat.card K) :=
  have : CharP K 2 := charP_two_of_card_eq_two_pow hK
  (sl2_oddPrimeInvertersAndSplitFusion hf hK).of_mulEquiv psl2CharTwoEquivSL

end CFSG.ShultStronglyClosedTI.OddPrimeInverters
