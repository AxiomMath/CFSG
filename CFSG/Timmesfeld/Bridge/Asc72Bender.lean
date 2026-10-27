module

public import CFSG.Adapters.QiuzhenLegacy.BenderSuzuki.BenderLinearBorel
public import CFSG.Adapters.QiuzhenLegacy.BenderSuzuki.BenderSuzukiBorel
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.TheoremC.BorelFacts
import CFSG.Timmesfeld.Bridge.StrongEmbedding
import CFSG.LocalAnalysis.ProperTwoGeneratedCore.TheoremC.BorelLinear
import CFSG.LocalAnalysis.ProperTwoGeneratedCore.TheoremC.BorelSuzuki
import CFSG.LocalAnalysis.ProperTwoGeneratedCore.TheoremC.BorelUnitary

public section

namespace CFSG.Timmesfeld.Bridge.Asc72

open CFSG.BenderSuzuki CFSG.Open

variable {K : Type*} [Group K] [Finite K]

theorem IsBenderGroup.exists_fusionBenderBorel (hK : IsBenderGroup K) :
    ∃ q k : ℕ, fusionBenderBorel K q k ∧ 4 ≤ q ∧
      (k = 1 → ∃ n, 2 ≤ n ∧ Nonempty (K ≃* PSL2Model n)) := by
  have h4 : ∀ m, 2 ≤ m → 4 ≤ 2 ^ m := fun m hm =>
    (Nat.pow_le_pow_right (by norm_num) hm : 2 ^ 2 ≤ 2 ^ m)
  rcases hK with ⟨n, hn, e⟩ | ⟨n, hn, e⟩ | ⟨n, hn, e⟩
  · have : Finite (PSL2Model n) := Finite.of_surjective e e.surjective
    exact ⟨_, _, (bender_psl2_borel_full n hn).map_mulEquiv e.symm, h4 n hn,
      fun _ => ⟨n, hn, ⟨e⟩⟩⟩
  · have hmodel : SzModel n = Sz n := CFSG.Models.benderSzModel_eq_sz n
    let e' : K ≃* Sz n := e.trans (MulEquiv.subgroupCongr hmodel)
    have : Finite (Sz n) := Finite.of_surjective e' e'.surjective
    exact ⟨_, _, (bender_suzuki_borel_full n hn).map_mulEquiv e'.symm, h4 _ (by omega),
      fun h => absurd h (by norm_num)⟩
  · have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have hmodel : PSU3Model n = PSU3 2 n := CFSG.Models.benderPSU3Model_eq_psu3 n
    let e' : K ≃* PSU3 2 n := e.trans (MulEquiv.subgroupCongr hmodel)
    have : Finite (PSU3 2 n) := Finite.of_surjective e' e'.surjective
    exact ⟨_, _, (bender_psu3_borel_full n hn).map_mulEquiv e'.symm, h4 n hn,
      fun h => absurd h (by norm_num)⟩

theorem IsBenderGroup.benderBorelFacts (hK : IsBenderGroup K) (Q : Sylow 2 K) :
    CFSG.ProperTwoGeneratedCore.TheoremC.BenderBorelFacts K (Q : Subgroup K) := by
  rcases hK with ⟨n, hn, e⟩ | ⟨n, hn, e⟩ | ⟨n, hn, e⟩
  · exact CFSG.ProperTwoGeneratedCore.TheoremC.benderBorelFacts_sylow_of_mulEquiv e
      (CFSG.ProperTwoGeneratedCore.TheoremC.psl2BorelFacts n hn) Q
  · exact CFSG.ProperTwoGeneratedCore.TheoremC.benderBorelFacts_sylow_of_mulEquiv e
      (CFSG.ProperTwoGeneratedCore.TheoremC.suzukiBorelFacts n hn) Q
  · exact CFSG.ProperTwoGeneratedCore.TheoremC.benderBorelFacts_sylow_of_mulEquiv e
      (CFSG.ProperTwoGeneratedCore.TheoremC.unitaryBorelFacts n hn) Q

theorem IsBenderGroup.isConj_of_orderOf_eq_two (hK : IsBenderGroup K) {x y : K}
    (hx : orderOf x = 2) (hy : orderOf y = 2) : IsConj x y := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨q, k, hB, -⟩ := exists_fusionBenderBorel hK
  obtain ⟨Q⟩ : Nonempty (Sylow 2 K) := inferInstance
  exact CFSG.Timmesfeld.Bridge.isConj_of_orderOf_eq_two (hB Q).1 hx hy

theorem IsBenderGroup.commute_of_mul_self_eq_one (hK : IsBenderGroup K) (Q : Sylow 2 K) {x : K}
    (hxQ : x ∈ Q) (hx : x * x = 1) : ∀ y ∈ Q, Commute x y := by
  intro y hyQ
  rcases eq_or_ne x 1 with rfl | h1
  · exact Commute.one_left y
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨q, k, hB, -⟩ := exists_fusionBenderBorel hK
  have hx2 : orderOf x = 2 := orderOf_eq_prime (by rw [pow_two]; exact hx) h1
  exact (CFSG.Timmesfeld.Connectivity.commute_of_mem_sylow Q (hB Q).1 hxQ hx2 hyQ).symm

theorem IsBenderGroup.mul_self_eq_one_of_commute (hK : IsBenderGroup K) (Q : Sylow 2 K) {x : K}
    (hxQ : x ∈ Q) (hc : ∀ y ∈ Q, Commute x y) : x * x = 1 := by
  obtain ⟨q, k, hB, -⟩ := exists_fusionBenderBorel hK
  have hz : (⟨x, hxQ⟩ : (Q : Subgroup K)) ∈ Subgroup.center (Q : Subgroup K) :=
    Subgroup.mem_center_iff.2 fun g => Subtype.ext (hc g g.2).eq.symm
  have h := congrArg Subtype.val ((hB Q).2.2.1 _ hz)
  rw [← pow_two]
  exact h

theorem IsBenderGroup.four_le_card_center (hK : IsBenderGroup K) (Q : Sylow 2 K) :
    4 ≤ Nat.card (Subgroup.center (Q : Subgroup K)) := by
  obtain ⟨q, k, hB, hq, -⟩ := exists_fusionBenderBorel hK
  rw [(hB Q).2.2.2.1]
  exact hq

theorem IsBenderGroup.exists_psl2_of_commute (hK : IsBenderGroup K) (Q : Sylow 2 K)
    (hab : ∀ x ∈ Q, ∀ y ∈ Q, Commute x y) : ∃ n, 2 ≤ n ∧ Nonempty (K ≃* PSL2Model n) := by
  obtain ⟨q, k, hB, hq, hk⟩ := exists_fusionBenderBorel hK
  have htop : Subgroup.center (Q : Subgroup K) = ⊤ := by
    rw [Subgroup.eq_top_iff']
    intro z
    rw [Subgroup.mem_center_iff]
    intro g
    exact Subtype.ext (hab g g.2 z z.2).eq
  have hcard := Subgroup.card_top (G := (Q : Subgroup K))
  rw [← htop, (hB Q).2.2.2.1, (hB Q).2.2.2.2] at hcard
  have hk1 : q ^ k = q ^ 1 := by
    rw [pow_one]
    exact hcard.symm
  exact hk (Nat.pow_right_injective (by omega) hk1)

theorem IsBenderGroup.commute_of_psl2 {n : ℕ} (hn : 2 ≤ n) (e : K ≃* PSL2Model n)
    (Q : Sylow 2 K) : ∀ x ∈ Q, ∀ y ∈ Q, Commute x y := by
  have : Finite (PSL2Model n) := Finite.of_surjective e e.surjective
  obtain ⟨-, -, -, hZ, hQ⟩ := (bender_psl2_borel_full n hn).map_mulEquiv e.symm Q
  have htop : Subgroup.center (Q : Subgroup K) = ⊤ :=
    Subgroup.eq_top_of_card_eq _ (by rw [hZ, hQ, pow_one])
  intro x hx y hy
  have hz : (⟨x, hx⟩ : (Q : Subgroup K)) ∈ Subgroup.center (Q : Subgroup K) := htop ▸ trivial
  exact congrArg Subtype.val (Subgroup.mem_center_iff.1 hz ⟨y, hy⟩).symm

theorem IsBenderGroup.exists_normalizer_conj (hK : IsBenderGroup K) (Q : Sylow 2 K) {x y : K}
    (hx : x ∈ Q ∧ ∀ q ∈ Q, Commute q x) (hx1 : x ≠ 1)
    (hy : y ∈ Q ∧ ∀ q ∈ Q, Commute q y) (hy1 : y ≠ 1) :
    ∃ g ∈ Subgroup.normalizer (Q : Set K), g * x * g⁻¹ = y := by
  obtain ⟨D, -, hDN, -, htr, -⟩ := (benderBorelFacts hK Q).torus
  obtain ⟨d, hdD, hd⟩ := htr x y hx hx1 hy hy1
  exact ⟨d⁻¹, Subgroup.inv_mem _ (hDN hdD), by rw [inv_inv]; exact hd⟩

theorem IsBenderGroup.isStronglyEmbeddedOrder_normalizer (hK : IsBenderGroup K)
    (Q : Sylow 2 K) : IsStronglyEmbeddedOrder (Subgroup.normalizer (Q : Set K)) := by
  obtain ⟨q, k, hB, -⟩ := exists_fusionBenderBorel hK
  exact (CFSG.Timmesfeld.Bridge.fusionStronglyEmbedded_iff _).1 (hB Q).1

theorem IsBenderGroup.isSimpleBenderGroup (hK : IsBenderGroup K) : IsSimpleBenderGroup K := by
  rcases hK with ⟨n, hn, e⟩ | ⟨a, ha, e⟩ | ⟨n, hn, e⟩
  · exact IsSimpleBenderGroup.isPSL2 ⟨n, hn, ⟨e⟩⟩
  · exact IsSimpleBenderGroup.isSuzuki
      ⟨a, ha, ⟨e.trans (MulEquiv.subgroupCongr (szModel_eq_suzukiMatrixGroup a))⟩⟩
  · let J := binaryQuadraticHermitian n (by omega)
    have hEcard : Nat.card (FiniteField.Extension (GaloisField 2 n) 2 2) = (2 ^ n) ^ 2 := by
      rw [FiniteField.natCard_extension, GaloisField.card 2 n (by omega)]
    have hfixed : Nat.card {x : FiniteField.Extension (GaloisField 2 n) 2 2 // J.conj x = x} =
        2 ^ n := quadraticBinaryFrobenius_fixed_card n (by omega)
    have hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0] := rfl
    obtain ⟨e'⟩ := projectiveSpecialUnitary_equiv_PSU3Model J n hn hJ hEcard hfixed
    exact IsSimpleBenderGroup.isPSU3
      ⟨n, hn, _, inferInstance, inferInstance, J, hJ, hEcard, hfixed, ⟨e.trans e'.symm⟩⟩

theorem IsBenderGroup.isSimpleGroup (hK : IsBenderGroup K) : IsSimpleGroup K :=
  (isSimpleBenderGroup hK).isSimple

theorem IsBenderGroup.exists_not_commute (hK : IsBenderGroup K) : ∃ a b : K, ¬ Commute a b := by
  by_contra h
  exact (isSimpleBenderGroup hK).not_commutative fun x y => by
    by_contra hxy
    exact h ⟨x, y, hxy⟩

end CFSG.Timmesfeld.Bridge.Asc72
