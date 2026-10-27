module

public import CFSG.RankThree.PartTwo.Sec15.Item155w3ProofHJ
public import CFSG.RankThree.PartTwo.Sec15.Item155w3ProofE81
import CFSG.RankThree.PartTwo.Sec14.Item143Proof
import CFSG.RankThree.PartTwo.Sec14.Item147
import CFSG.RankThree.PartTwo.Sec14.Item14Tools
import CFSG.RankThree.PartTwo.Sec17.Item17Q0ProofTools

public section

namespace CFSG.RankThree.PartTwo.Sec15

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.LocalRank CFSG.GH74.GLS
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

namespace Proof155w3

theorem false_of_trivial_of_lB_eq_bot {A : Subgroup G} {c : G} {L : Subgroup G}
    (h : Sec14Std G A c L) {Y : Subgroup G} (hY : Y ∈ Sec15.scriptY4 A (lB A))
    {B : Subgroup G} (hB : IsHyperplane A B) (hLB : lB A B = ⊥)
    (hBtriv : ∀ b ∈ B, ∀ y ∈ Y, b * y * b⁻¹ * y⁻¹ ∈ CFSG.Open.pCoreOf 2 Y) : False := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hA : Late.IsE27 A := h.isE27
  set O := CFSG.Open.pCoreOf 2 Y with hO
  set OB := pPrimeCoreOf 3 (Subgroup.centralizer (B : Set G)) with hOB
  set OA := pPrimeCoreOf 3 (Subgroup.centralizer (A : Set G)) with hOA
  have hpi : ∀ X : Subgroup G, IsPiSubgroup (piCompl 3) (pPrimeCoreOf 3 X) := fun X =>
    (isPiSubgroup_piCompl_iff Nat.prime_three _).mpr
      ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp (coprime_card_pPrimeCoreOf 3 X))
  have hK : IsPiSubgroup (piCompl 3) (OA ⊔ OB) :=
    isPiSubgroup_piCompl_sup (hpi _) (hpi _)
      ((pPrimeCoreOf_le 3 _).trans (centralizer_le_normalizer_pPrimeCoreOf hB.1))
  set V := Y ⊓ (OA ⊔ OB) with hV
  have hYO : Y ≤ Subgroup.normalizer (O : Set G) := CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 Y
  have hYW : Y ≤ V ⊔ O := by
    refine hY.2.2.1.le.trans (sSup_le fun Q hQ => ?_)
    have hQ3 : ¬ 3 ∣ Nat.card Q := (isPiSubgroup_piCompl_iff Nat.prime_three Q).mp hQ.1.1.2.1
    have hBQ : B ≤ Subgroup.normalizer (Q : Set G) := hB.1.trans hQ.1.1.2.2
    rw [CFSG.RankThreeEvenClassification.Helpers.coprime_commutator_centralizer_factorization 3
      Nat.prime_three B Q (hA.isPGroup.to_le hB.1) hQ3 hBQ]
    refine sup_le ?_ ?_
    · rw [Subgroup.commutator_le]
      intro q hq b hb
      have h1 := O.inv_mem (hBtriv b hb q (hQ.2 hq))
      have e : ⁅q, b⁆ = (b * q * b⁻¹ * q⁻¹)⁻¹ := by
        rw [commutatorElement_def]
        group
      rw [e]
      exact Subgroup.mem_sup_right h1
    · have h1 := hQ.1.2 B hB
      rw [qBound, hLB, sup_bot_eq, sup_comm] at h1
      exact le_sup_of_le_left (le_inf (inf_le_left.trans hQ.2) h1)
  have hW3 : IsPiSubgroup (piCompl 3) (V ⊔ O) :=
    isPiSubgroup_piCompl_sup (isPiSubgroup_piCompl_of_le hK inf_le_right)
      (Sec17.Proof17Q0.isPiSubgroup_piCompl_pCoreOf Y) (inf_le_left.trans hYO)
  have hY3 : ¬ 3 ∣ Nat.card Y := fun h3 =>
    (isPiSubgroup_piCompl_iff Nat.prime_three _).mp hW3 (h3.trans (Subgroup.card_dvd_of_le hYW))
  have hY1 : Y = ⊥ := by
    rw [hY.2.1, oPrimeResidualOf_eq_closure, eq_bot_iff, Subgroup.closure_le]
    rintro x ⟨hxY, k, hxk⟩
    have hcop : Nat.Coprime (3 ^ k) (Nat.card Y) :=
      Nat.Coprime.pow_left k ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr hY3)
    have h1 : orderOf x ∣ 3 ^ k := orderOf_dvd_of_pow_eq_one hxk
    have h2 : orderOf x ∣ Nat.card Y := Subgroup.orderOf_dvd_natCard Y hxY
    have h3 : orderOf x ∣ 1 := by
      rw [← hcop.gcd_eq_one]
      exact Nat.dvd_gcd h1 h2
    exact orderOf_eq_one_iff.mp (Nat.dvd_one.mp h3)
  exact ne_bot_of_mem_scriptY4 hY hY1

section Certs


theorem nine_le_card_map_actQ_of_nhj (h134 : Item134) (h48 : Sec4.Item4_8)
    {A : Subgroup G} {c : G} {L : Subgroup G} (h : Sec14Std G A c L) (hNHJ : ¬ AllPointsHJ A)
    {Y : Subgroup G} (hY : Y ∈ Sec15.scriptY4 A (lB A)) :
    9 ≤ Nat.card ((A.subgroupOf (Subgroup.normalizer (Y : Set G))).map
      (Sec17.Proof17Res6.actQ Y)) := by
  refine nine_le_card_map_actQ_of_forall h hY.1.2 fun B hBA hB9 hBtriv => ?_
  have hB : IsHyperplane A B := ⟨hBA, by rw [h.isE27.2, hB9]⟩
  exact false_of_trivial_of_lB_eq_bot h hY hB (lB_eq_bot_of_not_allPointsHJ' h134 h48 h hNHJ hB)
    hBtriv

end Certs

theorem two_pow_mod_three_ne_zero (n : ℕ) : 2 ^ n % 3 ≠ 0 := by
  intro h
  have h3 : 3 ∣ 2 ^ n := Nat.dvd_of_mod_eq_zero h
  have := (Nat.prime_dvd_prime_iff_eq Nat.prime_three Nat.prime_two).mp
    (Nat.prime_three.dvd_of_dvd_pow h3)
  omega

end Proof155w3

open Proof155w3

@[expose] def KSL3NonPiAutThree : Prop :=
  ∀ (X : Type) [Group X] (n : ℕ), ¬ 3 ∣ n →
    (Nonempty (X ≃* CFSG.Assembly.RankThreeEven.projSL 3 (GaloisField 2 n)) ∧ 2 ^ n % 3 = 2 ∨
      2 < 2 ^ n ∧ Nonempty (X ≃* CFSG.Assembly.RankThreeEven.projSU 3 2 n) ∧ 2 ^ n % 3 = 1) →
    ∀ E : Subgroup (MulAut X), CFSG.Assembly.IsElemAbelian 3 E → Nat.card E ≤ 3

@[expose] noncomputable def Step155GrowAltTwoFieldW (A : Subgroup G) (c : G) (L : Subgroup G) :
    Prop :=
  Sec14Std G A c L → ¬ AllPointsHJ A → ∀ X K Y M T : Subgroup G, Ctx155 A X K Y M T →
    MaxT155 A X K T → Above155w A X → ¬ K ≤ Subgroup.normalizer (CFSG.Open.pCoreOf 2 Y : Set G) →
    ⁅CFSG.Open.pCoreOf 2 K, K⁆ ≤ CFSG.Open.pCoreOf 2 Y →
    ¬ ⁅CFSG.Open.pCoreOf 2 Y, K⁆ ≤ CFSG.Open.pCoreOf 2 K →
    Case154Two L K X →
    (¬ ∃ n : ℕ, 1 ≤ n ∧ Sec4.IsoLThreePi (↥X ⧸ CFSG.pCore 2 ↥X) 2 n) →
    IsEmpty (↥X ⧸ CFSG.pCore 2 ↥X ≃* alternatingGroup (Fin 5)) →
    (¬ ∃ (c' : G) (L' : Subgroup G), Subgroup.zpowers c' ∈ omegaA A ∧ L' ∈ lA A c' ∧
      L' = (L' ⊓ X) ⊔ CFSG.Open.pCoreOf 2 L') →
    (∀ n : ℕ, IsLThreeEpsAt (↥X ⧸ CFSG.pCore 2 ↥X) 2 n → 3 ∣ n) →
      Claim155 A K Y

@[expose] noncomputable def Step155GrowAltTwoFieldWR : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
    Sec15R G A c L → Step155GrowAltTwoFieldW A c L

section Provers


theorem step155GrowAltTwoNHJW_of_field (h134 : Item134) (h48 : Sec4.Item4_8)
    (hKf : KSL3NonPiAutThree) {A : Subgroup G} {c : G} {L : Subgroup G}
    (hres : Step155GrowAltTwoFieldW A c L) : Step155GrowAltTwoNHJW A c L := by
  intro h hNHJ X K Y M T hC hmax hab hKR hZR hRK htwo hpi ha5 hcl
  refine hres h hNHJ X K Y M T hC hmax hab hKR hZR hRK htwo hpi ha5 hcl fun n hε => ?_
  by_contra h3
  have hX4 : X ∈ scriptY4 A (lB A) := hC.res ▸ hC.isY.2.1
  have hAe : CFSG.Assembly.IsElemAbelian 3 A := h.toSec13Data.isElemAbelian
  have hn : 1 ≤ n := by
    rcases Nat.eq_zero_or_pos n with h0 | h0
    · exact absurd (h0 ▸ dvd_zero 3) h3
    · exact h0
  have hmod := two_pow_mod_three_ne_zero n
  have hkind : Nonempty (↥X ⧸ CFSG.pCore 2 ↥X ≃*
        CFSG.Assembly.RankThreeEven.projSL 3 (GaloisField 2 n)) ∧ 2 ^ n % 3 = 2 ∨
      2 < 2 ^ n ∧ Nonempty (↥X ⧸ CFSG.pCore 2 ↥X ≃* CFSG.Assembly.RankThreeEven.projSU 3 2 n) ∧
        2 ^ n % 3 = 1 := by
    rcases hε with hL | ⟨h2, hU⟩
    · refine Or.inl ⟨hL, ?_⟩
      have h1 : 2 ^ n % 3 ≠ 1 := fun h1 => hpi ⟨n, hn, Or.inl ⟨h1, hL⟩⟩
      omega
    · refine Or.inr ⟨h2, hU, ?_⟩
      have h1 : 2 ^ n % 3 ≠ 2 := fun h1 => hpi ⟨n, hn, Or.inr ⟨h1, hU⟩⟩
      omega
  set Ab := (A.subgroupOf (Subgroup.normalizer (X : Set G))).map (Sec17.Proof17Res6.actQ X)
    with hAb
  have hA9 : 9 ≤ Nat.card Ab := nine_le_card_map_actQ_of_nhj h134 h48 h hNHJ hX4
  have hAbe : CFSG.Assembly.IsElemAbelian 3 Ab := by
    refine ⟨⟨⟨fun x y => ?_⟩⟩, ?_⟩
    · obtain ⟨_, a, ha, rfl⟩ := x
      obtain ⟨_, b, hb, rfl⟩ := y
      have hab : (a : G) * b = b * a := congrArg Subtype.val
        (hAe.1.is_comm.comm ⟨_, Subgroup.mem_subgroupOf.mp ha⟩ ⟨_, Subgroup.mem_subgroupOf.mp hb⟩)
      have hab' : a * b = b * a := Subtype.ext hab
      apply Subtype.ext
      simp only [Subgroup.coe_mul]
      rw [← map_mul, ← map_mul, hab']
    · rintro _ ⟨a, ha, rfl⟩
      have ha3 : a ^ 3 = 1 := Subtype.ext (hAe.2 _ (Subgroup.mem_subgroupOf.mp ha))
      rw [← map_pow, ha3, map_one]
  have hle := hKf _ n h3 hkind Ab hAbe
  omega

theorem step155GrowAltTwoNHJWR_of_field (h134 : Item134) (h48 : Sec4.Item4_8)
    (hKf : KSL3NonPiAutThree) (hres : Step155GrowAltTwoFieldWR) : Step155GrowAltTwoNHJWR :=
  fun G _ _ A c L hR => step155GrowAltTwoNHJW_of_field h134 h48 hKf (hres G A c L hR)


theorem step155GrowAltTwoWR_of_field (h148 : Item148R) (hbot : Item145BotS14) (h134 : Item134)
    (h48 : Sec4.Item4_8) (hKf : KSL3NonPiAutThree) (hres : Step155GrowAltTwoFieldWR) :
    Step155GrowAltTwoWR :=
  step155GrowAltTwoWR_of_nhj h148 hbot (step155GrowAltTwoNHJWR_of_field h134 h48 hKf hres)

end Provers

end CFSG.RankThree.PartTwo.Sec15
