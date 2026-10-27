module

public import CFSG.RankThree.PartTwo.Census.Criteria
public import CFSG.Adapters.TauCetiExceptional.Interface
public import CFSG.Walter.Ree.Model.PSL2
import CFSG.RankThree.PartTwo.Census.Carrier.G2Prime
import CFSG.Adapters.TauCetiExceptional.ReeBridge

public section

namespace CFSG.RankThree.PartTwo.Census

open CFSG.Assembly CFSG.Assembly.RankThreeEven TauCeti
open scoped MatrixGroups

namespace Carrier

section Simple

variable {H : Type} [Group H] [Finite H]

theorem not_isCharTwoType_of_simple_le_centralizer {t : H} (ht1 : t ≠ 1) (ht2 : t * t = 1)
    {J : Subgroup H} (hJt : J ≤ Subgroup.centralizer {t})
    (hJn : ∀ g : H, g * t = t * g → ∀ j ∈ J, g * j * g⁻¹ ∈ J) [IsSimpleGroup J]
    (hJ2 : ¬ IsPGroup 2 J) : ¬ IsCharTwoType H := by
  have hord : orderOf t = 2 := by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    exact orderOf_eq_prime (by rw [pow_two, ht2]) ht1
  have hL : IsTwoLocal (Subgroup.normalizer (Subgroup.zpowers t : Set H)) := by
    refine ⟨Subgroup.zpowers t, ?_, ?_, rfl⟩
    · rwa [Ne, Subgroup.zpowers_eq_bot]
    · exact IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hord, pow_one])
  refine not_isCharTwoType_of_normal_subgroup (K := J) hL ?_ ?_ ?_ ?_
  · intro j hj
    refine Subgroup.centralizer_le_normalizer _ (Subgroup.mem_centralizer_iff.mpr ?_)
    rintro _ ⟨n, rfl⟩
    have hc : j * t = t * j := Subgroup.mem_centralizer_singleton_iff.mp (hJt hj)
    exact (Commute.zpow_left hc.symm n).eq
  · intro g hg j hj
    exact hJn g (commute_of_mem_normalizer_zpowers_of_sq ht1 ht2 hg) j hj
  · intro N hNJ hNn hN2
    have hnorm : (N.subgroupOf J).Normal := ⟨fun n hn g => by
      rw [Subgroup.mem_subgroupOf] at hn ⊢
      exact hNn g g.2 n hn⟩
    rcases hnorm.eq_bot_or_eq_top with h | h
    · rw [Subgroup.subgroupOf_eq_bot] at h
      exact eq_bot_iff.2 fun n hn => Subgroup.disjoint_def.1 h hn (hNJ hn)
    · rw [Subgroup.subgroupOf_eq_top] at h
      exact absurd (hN2.to_le h) hJ2
  · intro hJ
    have : Nontrivial J := inferInstance
    exact (Subgroup.nontrivial_iff_ne_bot J).1 this hJ

end Simple

section Ree

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Ree
  CFSG.Walter.Ree.Model

variable {a : ℕ} {K : Type} [Field K] [Finite K] [CharP K ReeTag.G2.prime]

theorem not_isCharTwoType_reeGamma (ha : 1 ≤ a) (hK : Nat.card K = 3 ^ (2 * a + 1)) :
    ¬ IsCharTwoType (ReeTag.G2.reeGamma K a) := by
  have : Finite (ModGL ReeTag.G2.tag K) := finite_modGL
  obtain ⟨w₀, hw₀, -⟩ := weyl_longest_element ReeTag.G2.tag
  set Γ := ReeTag.G2.reeGamma K a
  set h := smallReeH a K (-1)
  set ψ := smallReePsi K a
  have hC : ∀ x, x ∈ smallReeInvCentralizer a K ↔ x ∈ Γ ∧ x * h = h * x := fun x => by
    rw [smallReeInvCentralizer, Subgroup.mem_inf, Subgroup.mem_centralizer_singleton_iff]
  have hψΓ : ψ.range ≤ Γ := by
    rintro _ ⟨g, rfl⟩
    exact ((hC _).1 (smallReePsi_mem hK hw₀ g)).1
  have hhΓ : h ∈ Γ := ((hC h).1 (smallReeH_mem_smallReeInvCentralizer hK (-1))).1
  have hCn : smallReeInvCentralizer a K ≤ Subgroup.normalizer (ψ.range : Set (ModGL _ K)) := by
    rw [← zpowers_sup_range_eq hK hw₀]
    exact sup_le ((zpowers_le_centralizer_range hK hw₀).trans
      (Subgroup.centralizer_le_normalizer _)) Subgroup.le_normalizer
  have hq27 : 27 ≤ Nat.card K := by
    rw [hK]
    calc 27 = 3 ^ (2 * 1 + 1) := by norm_num
      _ ≤ 3 ^ (2 * a + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  let eJ : ψ.range.subgroupOf Γ ≃* PSL(2, K) :=
    (Subgroup.subgroupOfEquivOfLe hψΓ).trans
      ((QuotientGroup.quotientMulEquivOfEq (smallReePsi_ker hK hw₀)).symm.trans
        (QuotientGroup.quotientKerEquivRange ψ)).symm
  have : IsSimpleGroup PSL(2, K) :=
    CFSG.ComponentClassification.CatalogueBGeneralLinear.projectiveSpecialLinear_simple 2 K
      le_rfl (Or.inr (by omega)) (Or.inr (by omega))
  have : IsSimpleGroup (ψ.range.subgroupOf Γ) := eJ.isSimpleGroup
  have hJ2 : ¬ IsPGroup 2 (ψ.range.subgroupOf Γ) := by
    intro hp
    obtain ⟨n, hn⟩ := (IsPGroup.iff_card (p := 2)).1 hp
    have hcard := two_mul_card_smallReePsi_range hK hw₀
    rw [← Nat.card_congr (Subgroup.subgroupOfEquivOfLe hψΓ).toEquiv, hn] at hcard
    have h3 : 3 ∣ 2 * 2 ^ n := by
      rw [hcard]
      exact Dvd.dvd.mul_right (dvd_pow_self 3 (by omega)) _
    have h3' : 3 ∣ 2 ^ (n + 1) := by rwa [pow_succ, mul_comm]
    have := (Nat.prime_three.dvd_of_dvd_pow h3')
    omega
  refine not_isCharTwoType_of_simple_le_centralizer (t := ⟨h, hhΓ⟩) ?_ ?_ ?_ ?_ hJ2
  · intro h1
    apply smallReeH_neg_one_not_mem_range hK hw₀
    rw [show smallReeH a K (-1) = 1 from congrArg Subtype.val h1]
    exact Subgroup.one_mem _
  · exact Subtype.ext smallReeH_neg_one_mul_self
  · intro j hj
    rw [Subgroup.mem_subgroupOf] at hj
    obtain ⟨g, hg⟩ := hj
    refine Subgroup.mem_centralizer_singleton_iff.mpr (Subtype.ext ?_)
    have := ((hC _).1 (smallReePsi_mem hK hw₀ g)).2
    rw [hg] at this
    exact this
  · intro g hg j hj
    rw [Subgroup.mem_subgroupOf] at hj ⊢
    have hgC : (g : ModGL _ K) ∈ smallReeInvCentralizer a K :=
      (hC g).2 ⟨g.2, congrArg Subtype.val hg⟩
    exact (Subgroup.mem_normalizer_iff.mp (hCn hgC) j).mp hj

theorem nonempty_derivedCentralQuotient_reeGamma (ha : 1 ≤ a)
    (hK : Nat.card K = 3 ^ (2 * a + 1)) :
    Nonempty (CFSG.Blueprint.DerivedCentralQuotient (ReeTag.G2.reeGamma K a) ≃*
      ReeTag.G2.reeGamma K a) := by
  have hcomm := (ReeTag.ree_generic_fixed_group_perfect .G2 a ha K hK).2.1
  have hD : ⁅ReeTag.G2.reeGamma K a, ReeTag.G2.reeGamma K a⁆ = ReeTag.G2.reeGamma K a := by
    rw [← Subgroup.map_subtype_commutator, hcomm, ← MonoidHom.range_eq_map,
      Subgroup.range_subtype]
  let e₁ : ↥⁅ReeTag.G2.reeGamma K a, ReeTag.G2.reeGamma K a⁆ ≃* ReeTag.G2.reeGamma K a :=
    MulEquiv.subgroupCongr hD
  have hZ : Subgroup.center ↥⁅ReeTag.G2.reeGamma K a, ReeTag.G2.reeGamma K a⁆ = ⊥ := by
    rw [eq_bot_iff]
    intro z hz
    have hz' : e₁ z ∈ Subgroup.center (ReeTag.G2.reeGamma K a) :=
      Subgroup.mem_center_iff.2 fun g => by
        obtain ⟨y, rfl⟩ := e₁.surjective g
        rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.1 hz y]
    rw [ReeTag.center_reeGamma_G2_eq_bot hK, Subgroup.mem_bot] at hz'
    exact Subgroup.mem_bot.2 (e₁.injective (hz'.trans (map_one e₁).symm))
  exact ⟨(QuotientGroup.quotientMulEquivOfEq hZ).trans (QuotientGroup.quotientBot.trans e₁)⟩

theorem nonempty_derivedCentralQuotient_equiv_reeGamma (ha : 1 ≤ a)
    (hK : Nat.card K = 3 ^ (2 * a + 1)) :
    Nonempty (CFSG.Blueprint.DerivedCentralQuotient (reeFixedGroup .G2 K reeG2Perm
        fun i => if i ∈ reeG2Long then 3 ^ a else 3 ^ (a + 1)) ≃* ReeTag.G2.reeGamma K a) := by
  have hH := ReeTag.reeGamma_eq_reeFixedGroup (t := .G2) (K := K) (a := a)
  show Nonempty (CFSG.Blueprint.DerivedCentralQuotient (reeFixedGroup ReeTag.G2.tag K
      ReeTag.G2.perm fun i => if i ∈ ReeTag.G2.longSet then ReeTag.G2.prime ^ a
        else ReeTag.G2.prime ^ (a + 1)) ≃* ReeTag.G2.reeGamma K a)
  rw [← hH]
  exact nonempty_derivedCentralQuotient_reeGamma ha hK

end Ree

end Carrier

open CFSG.Blueprint CFSG.LieType.Ree

theorem not_isCharTwoType_derivedCentralQuotient_reeG2 (a : ℕ) (ha : 1 ≤ a) (K : Type)
    [Field K] [Finite K] [CharP K 3] (hK : Nat.card K = 3 ^ (2 * a + 1)) :
    ¬ IsCharTwoType (CFSG.Blueprint.DerivedCentralQuotient (reeFixedGroup .G2 K reeG2Perm
        fun i => if i ∈ reeG2Long then 3 ^ a else 3 ^ (a + 1))) := by
  have : CharP K ReeTag.G2.prime := ‹CharP K 3›
  obtain ⟨e⟩ := Carrier.nonempty_derivedCentralQuotient_equiv_reeGamma ha hK
  exact fun h => Carrier.not_isCharTwoType_reeGamma ha hK (isCharTwoType_of_mulEquiv e h)

theorem excluded433_reeG2_of_bridge (hB : CFSG.TauCetiBridge.ReeG2Bridge) (a : ℕ) (ha : 1 ≤ a)
    (hv : (LieTypeIndex.reeG2 a).Valid) : Excluded433 (.lie ⟨.reeG2 a, hv⟩) := by
  intro G _ _ hG e
  have hcard : Nat.card (GaloisField 3 (2 * a + 1)) = 3 ^ (2 * a + 1) := by
    exact GaloisField.card 3 (2 * a + 1) (by omega)
  obtain ⟨f⟩ := hB a hv (GaloisField 3 (2 * a + 1)) hcard
  exact hG.false_of_not_isCharTwoType (e.trans f.symm)
    (not_isCharTwoType_derivedCentralQuotient_reeG2 a ha _ hcard)

theorem excluded433_reeG2_one_of_bridge (hB : CFSG.TauCetiBridge.ReeG2Bridge) :
    ∀ hv : (LieTypeIndex.reeG2 1).Valid, Excluded433 (.lie ⟨.reeG2 1, hv⟩) :=
  excluded433_reeG2_of_bridge hB 1 le_rfl

theorem excluded433_reeG2_one :
    ∀ hv : (LieTypeIndex.reeG2 1).Valid, Excluded433 (.lie ⟨.reeG2 1, hv⟩) :=
  excluded433_reeG2_one_of_bridge CFSG.TauCetiBridge.reeG2Bridge

end CFSG.RankThree.PartTwo.Census
