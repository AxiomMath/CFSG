
module

public import CFSG.Quasithin.Background.A3StructureDefs
public import CFSG.Quasithin.Background.A3StructureKGroup
import CFSG.GroupTheory.PCore.Transport

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.SectionRank CFSG.Open.SQTKTauCeti

theorem A3.pCore_eq_openCore (p : ℕ) (K : Type*) [Group K] :
    CFSG.pCore p K = CFSG.Open.pCore p K := (CFSG.Open.pCore_eq_pCore p K).symm

namespace SQTKHyp

variable {G : Type} [Group G]

theorem sqtkGroup [Finite G] (hG : SQTKHyp G) : SQTKGroup G := ⟨hG.sqt, hG.kgroup⟩

theorem subgroup [Finite G] (hG : SQTKHyp G) (H : Subgroup G) : SQTKGroup ↥H :=
  ⟨sqt_subgroup hG.sqt H, kGroup_subgroup hG.kgroup H⟩

theorem pRank_le [Finite G] (hG : SQTKHyp G) (H : Subgroup G) {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) : CFSG.Open.pRank p H ≤ 2 :=
  (pRank_mono hp.one_lt (le_top : H ≤ ⊤)).trans (hG.sqt p hp hp2)

theorem pCoreOf_le_of_subnormal (p : ℕ) [Fact p.Prime] [Finite G] {H K : Subgroup G}
    (h : IsSubnormal H K) : pCoreOf p H ≤ pCoreOf p K := by
  induction h with
  | refl => exact le_rfl
  | @step H M K hle hN _ ih =>
    refine le_trans ?_ ih
    refine CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer p
      ((CFSG.LieType.BorelTits.pCoreOf_le p H).trans hle) ?_
      (CFSG.LieType.BorelTits.pCoreOf_isPGroup p H)
    intro m hm
    have hmH : m ∈ Subgroup.normalizer (H : Set G) :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer hle).mp hN hm
    exact CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf p H hmH

theorem pCoreOf_two_of_subnormal (hG : SQTKHyp G) {L : Subgroup G} (hL : IsSubnormal L ⊤) :
    pCoreOf 2 L = ⊥ := by
  have := hG.finite
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h1 := pCoreOf_le_of_subnormal 2 hL
  have h2 : pCoreOf 2 (⊤ : Subgroup G) = ⊥ :=
    (CFSG.LieType.BorelTits.map_pCore_mulEquiv 2 (Subgroup.topEquiv (G := G))).trans
      ((A3.pCore_eq_openCore 2 G).symm.trans hG.o2)
  rw [h2] at h1
  exact le_bot_iff.mp h1

theorem pCore_two_of_subnormal (hG : SQTKHyp G) {L : Subgroup G} (hL : IsSubnormal L ⊤) :
    CFSG.pCore 2 ↥L = ⊥ := by
  have h : (CFSG.Open.pCore 2 ↥L).map L.subtype = ⊥ := hG.pCoreOf_two_of_subnormal hL
  exact (Subgroup.map_eq_bot_iff_of_injective _ L.subtype_injective).mp h

theorem of_subnormal (hG : SQTKHyp G) {L : Subgroup G} (hL : IsSubnormal L ⊤) :
    SQTKHyp ↥L := by
  have := hG.finite
  exact { finite := inferInstance
          sqt := (hG.subgroup L).1
          kgroup := (hG.subgroup L).2
          o2 := hG.pCore_two_of_subnormal hL }

theorem of_normal (hG : SQTKHyp G) (L : Subgroup G) [L.Normal] : SQTKHyp ↥L :=
  hG.of_subnormal (A3.subnormal_of_normal le_top inferInstance)

end SQTKHyp

theorem pCore_two_quotient_pCore_two (X : Type) [Group X] :
    CFSG.pCore 2 (X ⧸ CFSG.pCore 2 X) = ⊥ := by
  set N : Subgroup X := CFSG.pCore 2 X with hN
  set K : Subgroup X := (CFSG.pCore 2 (X ⧸ N)).comap (QuotientGroup.mk' N) with hK
  have hKp : IsPGroup 2 K := by
    rintro ⟨k, hk⟩
    obtain ⟨a, ha⟩ := (CFSG.pCore_isPGroup (G := X ⧸ N) (p := 2)) ⟨_, hk⟩
    have h1 : k ^ 2 ^ a ∈ N := by
      have := congrArg Subtype.val ha
      simp only [Subgroup.coe_pow, Subgroup.coe_one] at this
      rwa [← map_pow, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at this
    obtain ⟨b, hb⟩ := (CFSG.pCore_isPGroup (G := X) (p := 2)) ⟨_, h1⟩
    refine ⟨a + b, Subtype.ext ?_⟩
    have := congrArg Subtype.val hb
    simp only [Subgroup.coe_pow, Subgroup.coe_one] at this ⊢
    rw [pow_add, pow_mul]
    exact this
  have hKN : K ≤ N := le_sSup ⟨inferInstance, hKp⟩
  rw [eq_bot_iff]
  intro x hx
  obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective N x
  have hy : y ∈ N := hKN hx
  rw [Subgroup.mem_bot, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
  exact hy

theorem SQTKHyp.of_sqtkGroup (X : Type) [Group X] [Finite X] (hX : SQTKGroup X) :
    SQTKHyp (X ⧸ CFSG.pCore 2 X) where
  finite := inferInstance
  sqt := sqt_quotient_two_group hX.1 (CFSG.pCore 2 X) CFSG.pCore_isPGroup
  kgroup := kGroup_quotient hX.2 _
  o2 := pCore_two_quotient_pCore_two X

end CFSG.Quasithin
