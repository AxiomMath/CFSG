module

public import CFSG.RankThree.PartTwo.Sec16.Item169StepsProofTheta
public import CFSG.RankThree.PartTwo.Sec15.HypS
public import CFSG.RankThree.PartTwo.Sec13.Item138N
import CFSG.RankThree.PartTwo.Sec15.NoModNine
import CFSG.RankThree.PartTwo.Sec6.Item612Core
import CFSG.CGT.PushingUp.TwoLocals
public import CFSG.RankThree.PartTwo.Sec13.Item136PGL
public import CFSG.RankThree.PartTwo.Sec14.Concl142HJ
public import CFSG.RankThree.PartTwo.Sec17.RouteForms

public section

namespace CFSG.RankThree.PartTwo.Sec16

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
  CFSG.RankThree.PartTwo.Sec13 CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.PartTwo.Sec15
  CFSG.GH74.GLS
open CFSG.Assembly.RankThreeEven (projSL projSU)

@[expose] noncomputable def Step1612Gen : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
    Ctx169 G A c L → Concl1611 A c L →
      (∀ n : ℕ, IsZ3LThreeTwo A c L n → ¬ (2 ^ n % 9 = 1 ∨ 2 ^ n % 9 = 8)) →
      IsEmpty (lBarA c L A ≃* Multiplicative (ZMod 3) × projSL 3 (GaloisField 2 2)) →
        L ≤ sSup (invariantPiSubgroups L A (piCompl 3))

namespace Proof1612

variable {G : Type} [Group G] [Finite G]

theorem isLThreePi_of_concl1611 {A : Subgroup G} {c : G} {L : Subgroup G}
    (hD : Sec13Data G A c L) (h1611 : Concl1611 A c L) :
    IsLThreePi (↥L ⧸ aschbacherSolvableCore 3 ↥L) ∧ 3 ∣ Nat.card L := by
  rcases h1611 with hPGL | ⟨n, hn1, hiso, ⟨φ⟩⟩
  · obtain ⟨hL3, -, D, hDL, -, hD9⟩ := facts_of_isZ3PGLThreePi hD hPGL
    refine ⟨hL3, ?_⟩
    have h9 : 9 ∣ Nat.card L := hD9 ▸ Subgroup.card_dvd_of_le hDL
    exact (show 3 ∣ 9 by norm_num).trans h9
  · have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    refine ⟨⟨2, n, inferInstance, hn1, hiso⟩, ?_⟩
    have h9 := card_inf_eq_nine hD (isPerfect_lBar hD) φ
    have h9' : 9 ∣ Nat.card L := h9 ▸ Subgroup.card_dvd_of_le inf_le_right
    exact (show 3 ∣ 9 by norm_num).trans h9'

theorem isSimpleGroup_lBar
    {A : Subgroup G} {c : G} {L : Subgroup G}
    (hD : Sec13Data G A c L) (hL3 : IsLThreePi (↥L ⧸ aschbacherSolvableCore 3 ↥L)) :
    IsSimpleGroup (↥L ⧸ aschbacherSolvableCore 3 ↥L) := by
  have hq := Sec6.isQuasisimple_of_mem_thetaComponentsAt hD.mem_thetaComponentsAt
  have hz := center_eq_bot_of_types hD.mem_thetaComponentsAt (Or.inr (Or.inl hL3))
  have e : (↥L ⧸ aschbacherSolvableCore 3 ↥L) ⧸ Subgroup.center (↥L ⧸ aschbacherSolvableCore 3 ↥L)
      ≃* ↥L ⧸ aschbacherSolvableCore 3 ↥L :=
    (QuotientGroup.quotientMulEquivOfEq hz).trans QuotientGroup.quotientBot
  exact (MulEquiv.isSimpleGroup_congr e).mp hq.2.1

theorem eq_oPrimeResidualOf_of_simple {L : Subgroup G} (hLp : Group.IsPerfect ↥L)
    (hsimp : IsSimpleGroup (↥L ⧸ aschbacherSolvableCore 3 ↥L)) (h3 : 3 ∣ Nat.card L) :
    L = oPrimeResidualOf 3 L := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hθ := solvable_prime_complement_core_characterization (H := ↥L) Nat.prime_three
  set θ := aschbacherSolvableCore 3 ↥L with hθdef
  set N := oPrimeResidual 3 ↥L with hNdef
  have hNn : N.Normal := oPrimeResidual_normal 3 ↥L
  have hmapn : (N.map (QuotientGroup.mk' θ)).Normal :=
    hNn.map _ (QuotientGroup.mk'_surjective θ)
  have hsup : N ⊔ θ = ⊤ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (N.map (QuotientGroup.mk' θ)) with
      hbot | htop
    · exfalso
      obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' 3 h3
      have hx3 : x ^ 3 = 1 := by rw [← hx, pow_orderOf_eq_one]
      have hxN : x ∈ N := Subgroup.subset_closure ⟨1, by rw [pow_one]; exact hx3⟩
      have hxθ : x ∈ θ := by
        have hmem : QuotientGroup.mk' θ x ∈ N.map (QuotientGroup.mk' θ) :=
          Subgroup.mem_map_of_mem _ hxN
        rw [hbot, Subgroup.mem_bot, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hmem
        exact hmem
      rw [eq_one_of_mem_aschbacherSolvableCore hxθ hx3, orderOf_one] at hx
      omega
    · have h1 := Subgroup.comap_map_eq (QuotientGroup.mk' θ) N
      rw [htop, Subgroup.comap_top, QuotientGroup.ker_mk'] at h1
      exact h1.symm
  have hsurj : Function.Surjective ((QuotientGroup.mk' N).comp θ.subtype) := by
    intro q
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective N q
    have hx : x ∈ N ⊔ θ := hsup ▸ Subgroup.mem_top x
    rw [Subgroup.mem_sup_of_normal_left] at hx
    obtain ⟨n, hn, t, ht, rfl⟩ := hx
    refine ⟨⟨t, ht⟩, ?_⟩
    simp only [MonoidHom.coe_comp, Function.comp_apply, Subgroup.coe_subtype,
      QuotientGroup.mk'_apply]
    rw [QuotientGroup.mk_mul, (QuotientGroup.eq_one_iff n).mpr hn, one_mul]
  have : Group.IsSolvable θ := hθ.1
  have hsolv : Group.IsSolvable (↥L ⧸ N) := Group.isSolvable_of_surjective hsurj
  have hperf : Group.IsPerfect (↥L ⧸ N) :=
    Group.IsPerfect.ofSurjective (f := QuotientGroup.mk' N) (QuotientGroup.mk'_surjective N)
  have hNtop : N = ⊤ := by
    by_contra hne
    have : Nontrivial (↥L ⧸ N) := QuotientGroup.nontrivial_iff.mpr hne
    exact Group.IsPerfect.not_isSolvable (↥L ⧸ N) hsolv
  rw [oPrimeResidualOf, ← hNdef, hNtop, ← MonoidHom.range_eq_map, Subgroup.range_subtype]

theorem mem_scriptQ_of_le_L {A : Subgroup G} {c : G} {L : Subgroup G} (h : Sec15R G A c L)
    (h142 : Item142 A (lB A) c L h.isElemAbelian.1 h.mem_A) {R : Subgroup G} (hRL : R ≤ L)
    (hR3 : ¬ 3 ∣ Nat.card R) (hAR : A ≤ Subgroup.normalizer (R : Set G)) :
    R ∈ scriptQ A (lB A) := by
  have hRH : R ∈ invariantPiSubgroups (Subgroup.normalizer (Subgroup.zpowers c : Set G)) A
      (piCompl 3) :=
    ⟨hRL.trans (h.le_centralizer.trans (centralizer_singleton_le_normalizer_zpowers c)),
      (isPiSubgroup_piCompl_iff Nat.prime_three R).mpr hR3, hAR⟩
  obtain ⟨R', hR', hRR'⟩ := exists_le_mem_maxInvariantPiSubgroups hRH
  exact mem_scriptQ_of_le (h142 R' hR').1.1 hRR' hAR

theorem eq_delta_of_gen {A : Subgroup G} {c : G} {L : Subgroup G} (h : Sec15R G A c L)
    (h142 : Item142 A (lB A) c L h.isElemAbelian.1 h.mem_A)
    (hgen : L ≤ sSup (invariantPiSubgroups L A (piCompl 3))) : L = delta A (lB A) L := by
  refine le_antisymm (hgen.trans (sSup_le fun Q hQ => ?_)) (delta_le L)
  obtain ⟨hQL, hQ3, hAQ⟩ := hQ
  exact le_delta (mem_scriptQ_of_le_L h h142 hQL
    ((isPiSubgroup_piCompl_iff Nat.prime_three Q).mp hQ3) hAQ) hQL

end Proof1612

open Proof1612 Proof169Theta

theorem step1612NotSimple_of
    (h135 : Item135Simple) (h1611 : Step1611) : Step1612NotSimple := by
  intro G _ _ A c L h hns _
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hD := h.toSec13Data
  obtain ⟨hL3, -⟩ := isLThreePi_of_concl1611 hD (h1611 G A c L h)
  have hθ := theta_eq_pCore_two_of_item135Simple h135 hD (Or.inl hL3)
  have hθ1 : aschbacherSolvableCore 3 ↥L ≠ ⊥ := by
    intro hbot
    apply hns
    have e : ↥L ≃* ↥L ⧸ aschbacherSolvableCore 3 ↥L :=
      QuotientGroup.quotientBot.symm.trans (QuotientGroup.quotientMulEquivOfEq hbot.symm)
    exact (MulEquiv.isSimpleGroup_congr e).mpr (isSimpleGroup_lBar hD hL3)
  set T := CFSG.Open.pCoreOf 2 L with hT
  have hT2 : IsPGroup 2 T := CFSG.LieType.BorelTits.pCoreOf_isPGroup (r := 2) L
  refine ⟨T, ⟨le_top, (isPiSubgroup_piOf_iff Nat.prime_two T).mpr hT2,
    sup_le (h.le_normalizer.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 L))
      (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 L)⟩, ?_⟩
  intro hTbot
  apply hθ1
  rw [hθ]
  rw [hT, CFSG.Open.pCoreOf, Subgroup.map_eq_bot_iff_of_injective _ L.subtype_injective] at hTbot
  exact hTbot

theorem step1612Y3_of
    (h152 : Item152R) (h142 : Item142R) (h135 : Item135Simple)
    (h138 : Item138N) (h1611 : Step1611) (hgen : Step1612Gen) : Step1612Y3 := by
  intro G _ _ A c L h h34 T hT hT1
  exfalso
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hD := h.toSec13Data
  have hc1611 := h1611 G A c L h
  obtain ⟨hL3, h3⟩ := isLThreePi_of_concl1611 hD hc1611
  have hLc : L ≤ Subgroup.centralizer {c} := hD.le_centralizer
  have hLtop : L ≠ ⊤ := fun htop =>
    Sec6.centralizer_ne_top_of_ne_one h.toTheoremFourHyp hD.ne_one (top_le_iff.mp (htop ▸ hLc))
  have hLp : Group.IsPerfect ↥L := Sec6.isPerfect_of_mem_thetaComponentsAt hD.mem_thetaComponentsAt
  have hL4 : L ∈ Sec15.scriptY4 A (lB A) :=
    ⟨⟨hLtop, hD.le_normalizer⟩, eq_oPrimeResidualOf_of_simple hLp (isSimpleGroup_lBar hD hL3) h3,
      eq_delta_of_gen h.toSec15R (h142 G A c L h.toSec15R) (hgen G A c L h hc1611 (fun n hn =>
        not_modNine_of_inner h.toSec15R h138 KFacts.kSL3PiOrder3TypeC hn.1 hn.2.1 hn.2.2) h34),
      h135 G A c L hD (Or.inl hL3)⟩
  obtain ⟨-, hTπ, hALT⟩ := hT
  have hT2 : IsPGroup 2 T := (isPiSubgroup_piOf_iff Nat.prime_two T).mp hTπ
  set M := Subgroup.normalizer (T : Set G) with hM
  have hAM : A ≤ M := le_sup_left.trans hALT
  have hLM : L ≤ M := le_sup_right.trans hALT
  have hTO : T ≤ CFSG.Open.pCoreOf 2 M :=
    CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 Subgroup.le_normalizer le_rfl hT2
  have hM2 : M ∈ scriptY2 A :=
    ⟨⟨normalizer_ne_top_of_isPGroup h.isSimpleGroup h.nonabelian hT1 hT2,
      hAM.trans Subgroup.le_normalizer⟩, fun h0 => hT1 (le_bot_iff.mp (h0 ▸ hTO))⟩
  have hloc : IsPLocal 2 M := CFSG.CGT.PushingUp.isPLocal_normalizer_of_isPGroup hT2 hT1
  have hF : generalizedFitting ↥M = CFSG.pCore 2 ↥M :=
    (isCharacteristicP_iff_generalizedFitting_eq_pCore ↥M 2).mp
      (CFSG.CGT.PushingUp.isCharacteristicP_of_isPLocal h.toTheoremFourHyp.charTwoType hloc)
  obtain ⟨X, -, -, hX0⟩ := h152 G A c L h.toSec15R L hL4 M hM2 hLM hF
  rw [h.scriptY0_eq] at hX0
  exact hX0

end CFSG.RankThree.PartTwo.Sec16
