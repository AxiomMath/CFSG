module

public import CFSG.RankThree.PartTwo.Sec8.Item82ProofDefs
public import CFSG.RankThree.PartTwo.Sec21.Item211ProofQuot
public import CFSG.RankThree.PartTwo.Sec4.LThreePiItem411
import CFSG.RankThree.PartTwo.Sec21.Item211ProofListOf
import CFSG.RankThree.PartTwo.KFacts.K71IdentSU3
import CFSG.Timmesfeld.Orders.Distinct

public section

namespace CFSG.RankThree.PartTwo.Sec8.Item82Proof

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.Sec21.Item211Proof
open CFSG.Assembly.LowTwoRank (StatedSL StatedSU)

theorem padicValNat_two_pow_cube_mul_odd {a x : ℕ} (hx : Odd x) :
    padicValNat 2 ((2 ^ a) ^ 3 * x) = 3 * a := by
  rw [← pow_mul, padicValNat.mul (by positivity) hx.pos.ne', padicValNat.prime_pow,
    padicValNat.eq_zero_of_not_dvd hx.not_two_dvd_nat, add_zero, mul_comm]

theorem padicValNat_card_statedSL_three {n : ℕ} (hn : 1 ≤ n) {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = 2 ^ n) : padicValNat 2 (Nat.card (StatedSL 3 K)) = 3 * n := by
  have : Fintype K := Fintype.ofFinite K
  rw [Nat.card_congr (Sec4.statedSLEquiv 3 K).toEquiv, KFacts.card_SL_three,
    ← Nat.card_eq_fintype_card, hK, mul_assoc]
  apply padicValNat_two_pow_cube_mul_odd
  exact (Timmesfeld.Orders.odd_pow_sub_one (by omega) (by norm_num)).mul
    (Timmesfeld.Orders.odd_pow_sub_one (by omega) (by norm_num))

theorem padicValNat_card_statedSU_three {m : ℕ} (hm : 1 ≤ m) {K : Type} [Field K]
    (hK : Nat.card K = (2 ^ m) ^ 2) :
    padicValNat 2 (Nat.card (StatedSU 3 (2 ^ m) K)) = 3 * m := by
  have hU : CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData 2 m K :=
    ⟨Nat.prime_two, hm, by rw [hK, ← pow_mul, mul_comm]⟩
  rw [show StatedSU 3 (2 ^ m) K = CFSG.ClassicalGroups.UnitaryFlag.unitarySU 2 m K 3 from rfl,
    KFacts.card_unitarySU_three hU, mul_assoc]
  apply padicValNat_two_pow_cube_mul_odd
  have heven : Even ((2 ^ m) ^ 3) := (Nat.even_pow' (by norm_num)).mpr
    ((Nat.even_pow' (by omega)).mpr even_two)
  exact (Timmesfeld.Orders.odd_pow_sub_one (by omega) (by norm_num)).mul heven.add_one


theorem item82TwoSLThree_of (h45 : Sec4.Item4_5) (h41 : Sec4.Item4_1LargePrime) :
    Item82TwoSLThree := by
  intro G _ _ A c L a h h81 n hn hn4 K _ _ hK
  refine ⟨fun e => ?_⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hG4 : TheoremFourHyp G := h.toTheoremFourHyp
  have hAF := h.mem_partTwoF
  have hAe : CFSG.Assembly.IsElemAbelian 3 A := hAF.1
  have hA : IsPGroup 3 A := fun x => ⟨1, Subtype.ext (by simpa using hAe.2 x x.2)⟩
  have hcA : c ∈ A := h.mem_A
  have hc1 : c ≠ 1 := h.ne_one
  have hLc : L ∈ thetaComponentsAt 3 c := h.mem_thetaComponentsAt
  have hLC : L ≤ Subgroup.centralizer ({c} : Set G) :=
    Sec6.le_centralizer_of_mem_thetaComponentsAt hLc
  have hAC : A ≤ Subgroup.centralizer ({c} : Set G) := fun x hx =>
    Subgroup.mem_centralizer_singleton_iff.mpr
      (congrArg Subtype.val (hAe.1.is_comm.comm ⟨x, hx⟩ ⟨c, hcA⟩))
  have hAL : A ≤ Subgroup.normalizer (L : Set G) :=
    Sec6.le_normalizer_of_mem_thetaComponentsAt h45 hG4 hAe hcA hc1 L hLc
  have hCA : A ⊓ Sec4.thetaQuotCentralizer L = Subgroup.zpowers c := by
    have hset := Sec13.sectionCentralizer_eq_inf hAL
    rw [h.sectionCentralizer_eq] at hset
    exact SetLike.coe_injective hset.symm
  have hq : IsQuasisimple (Sec21.lBar L) := by
    obtain ⟨L', hL', hLL'⟩ := hLc
    rw [← hLL']
    exact LocalCores.isQuasisimple_of_mulEquiv (Sec13.thetaQuotEquivSub _ L') hL'.2.2
  have hΛ : SectionFourHyp ↥(L ⊔ A) := hG4.sectionFourHyp
    (fun htop => Sec21.Item211Proof.centralizer_ne_top hG4 hc1
      (eq_top_iff.mpr (htop ▸ sup_le hLC hAC)))
  obtain ⟨Φ₀, -⟩ := exists_lEquiv hAL
  have hX : SectionFourHyp (QuotX L A) := sectionFourHyp_quotX h41 hΛ hA hAL Φ₀ hq
  have hq₁ : IsQuasisimple (lOne L A) := LocalCores.isQuasisimple_of_mulEquiv Φ₀ hq
  have hn1 : 1 ≤ n := by omega
  have hn3 : 2 ^ n % 3 = 1 := by
    obtain ⟨k, rfl⟩ := hn
    rw [← two_mul, pow_mul, Nat.pow_mod]
    norm_num
  have hSL : Sec4.IsSLThreePi (lOne L A) :=
    ⟨2 ^ n, K, inferInstance, inferInstance, Or.inl ⟨hK, hn3, ⟨Φ₀.symm.trans e⟩⟩⟩
  have hmax := maximal_aOne (L := L) hAe hAF.2.1
  have hcardA₁ : Nat.card (aOne L A) = 81 := by
    rw [← Nat.card_congr (aEquiv (L := L) hA).toEquiv, h81]
  have hc₁ : orderOf (piX L A ⟨c, Subgroup.mem_sup_right hcA⟩) = 3 := by
    have h1 : (piX L A ⟨c, Subgroup.mem_sup_right hcA⟩) =
        ((aEquiv (L := L) hA ⟨c, hcA⟩ : aOne L A) : QuotX L A) := rfl
    rw [h1, Subgroup.orderOf_coe, MulEquiv.orderOf_eq, Subgroup.orderOf_mk]
    exact orderOf_eq_prime (hAe.2 c hcA) hc1
  have halt := Sec4.rank3II_4_11 (QuotX L A) hX (lOne L A) (normal_lOne hAL) hSL hq₁
    (aOne L A) hmax (by omega) _ hc₁ (aOne_inf_centralizer hA hAL hcA hCA)
  rcases halt with ⟨h27, -⟩ | ⟨h27, -⟩ | ⟨h27, -⟩ | ⟨h27, -⟩ |
      ⟨-, -, -, -, ⟨m, hm, K', _, _, hK', ⟨e'⟩⟩, -⟩ | ⟨h27, -⟩
  · omega
  · omega
  · omega
  · omega
  ·
    have hm1 : 1 ≤ m := hm.pos
    have hcard : Nat.card (StatedSL 3 K) = Nat.card (StatedSU 3 (2 ^ m) K') :=
      Nat.card_congr ((Φ₀.symm.trans e).symm.trans e').toEquiv
    have h1 := padicValNat_card_statedSL_three hn1 hK
    rw [hcard, padicValNat_card_statedSU_three hm1 hK'] at h1
    obtain ⟨k, rfl⟩ := hn
    obtain ⟨j, rfl⟩ := hm
    omega
  · omega

end CFSG.RankThree.PartTwo.Sec8.Item82Proof
