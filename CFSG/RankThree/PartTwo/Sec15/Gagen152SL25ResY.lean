module

public import CFSG.RankThree.PartTwo.Sec15.Ronan152SixBigDefs
public import CFSG.RankThree.PartTwo.Sec15.Item1515ResProofS17
public import CFSG.RankThree.PartTwo.Sec15.Item15Res7ProofConj
import CFSG.RankThree.PartTwo.Sec6.Item612Core
import CFSG.RankThree.PartTwo.Sec14.Item148HJProofLB
import CFSG.RankThree.PartTwo.Sec14.Item147
import CFSG.RankThree.PartTwo.Sec14.Item14Tools
import CFSG.RankThree.PartTwo.Sec12.Gap128OTwoHJ
import CFSG.RankThree.PartTwo.KFacts.KS14HJNative
import CFSG.RankThree.PartTwo.Sec15.Item155wProofHJ
import CFSG.RankThree.PartTwo.Sec15.Item155wProofTools
import CFSG.RankThree.PartTwo.Sec15.Item155R2ProofMaxT
import CFSG.RankThree.PartTwo.Sec15.Item156Res4ProofON
import CFSG.RankThree.PartTwo.Sec16.Item163StepsQProof
import CFSG.RankThree.PartTwo.Sec17.Item171StepsProofTools
import CFSG.RankThree.PartTwo.Sec15.Item15Res4ProofHJD
import CFSG.RankThree.PartTwo.Sec15.Item152GenProofTheta
public import CFSG.RankThree.PartTwo.Sec14.Item145BotNo135

public section

namespace CFSG.RankThree.PartTwo.Sec15

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.LocalRank CFSG.GH74.GLS

namespace Gagen152SL25Res

open Proof15Res4 Proof15Res7

variable {G : Type} [Group G] [Finite G]

structure ConfY (A : Subgroup G) (c : G) (L Y : Subgroup G) : Prop where
  sec15R : Sec15R G A c L
  j2 : Nonempty (↥L ⧸ aschbacherSolvableCore 3 ↥L ≃* CFSG.Blueprint.NativeSporadic.J2)
  mem_scriptY0Star : Y ∈ scriptY0Star A (lB A)
  le : L ≤ Y
  eq_Y : Y = (Y ⊓ L) ⊔ CFSG.Open.pCoreOf 2 Y
  eq_L : L = (L ⊓ Y) ⊔ CFSG.Open.pCoreOf 2 L

variable {A : Subgroup G} {c : G} {L : Subgroup G}

theorem exists_confY
    (hlist : Step1515HJListLe) {A : Subgroup G} {b : G} {Lb : Subgroup G}
    (hRb : Sec15R G A b Lb)
    (hJ : Nonempty (↥Lb ⧸ aschbacherSolvableCore 3 ↥Lb ≃* CFSG.Blueprint.NativeSporadic.J2))
    (hO2 : CFSG.Open.pCoreOf 2 Lb ≠ ⊥) : ∃ Y, ConfY A b Lb Y := by
  classical
  have hJ' := hJ
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hSb := hRb.toSec14Std
  have hDb := hRb.toSec13Data
  have hLbtop : Lb ≠ ⊤ := fun htop => Sec6.centralizer_ne_top_of_ne_one hRb.toTheoremFourHyp
    hDb.ne_one (top_le_iff.mp (htop ▸ hDb.le_centralizer))
  have hLb4 : Lb ∈ scriptY4 A (lB A) := by
    have hperf := Sec6.isPerfect_of_mem_thetaComponentsAt hDb.mem_thetaComponentsAt
    obtain ⟨eθ⟩ := hJ
    have : IsSimpleGroup CFSG.Blueprint.NativeSporadic.J2 := CFSG.Sporadic.J2.isSimpleGroup_J2
    have hsimp : IsSimpleGroup (↥Lb ⧸ aschbacherSolvableCore 3 ↥Lb) := eθ.isSimpleGroup
    have h3L : 3 ∣ Nat.card Lb := three_dvd_card_of_thetaQuot_j2 ⟨eθ⟩
    obtain ⟨eJ⟩ := Sec12.gap128OTwoHJ ↥Lb (hRb.toTheoremFourHyp.sectionFourHyp hLbtop) hperf ⟨eθ⟩
    have hq : CFSG.IsQuasisimple (↥Lb ⧸ CFSG.pCore 2 ↥Lb) :=
      isQuasisimple_of_mulEquiv_nativeJ2 CFSG.Sporadic.J2.isSimpleGroup_J2
        (KFacts.KS14.center_nativeJ2_eq_bot Sec4.Sporadic.rank3II_4_15) eJ
    exact ⟨⟨hLbtop, hDb.le_normalizer⟩, Sec16.eq_oPrimeResidualOf_of_isSimpleGroup hperf hsimp h3L,
      le_antisymm (Proof155w.le_delta_of_le_of_j2 hSb ⟨eθ⟩ le_rfl) (delta_le Lb), hq⟩
  have hLb0 : Lb ∈ scriptY0 A (lB A) := ⟨hLb4, ⟨hLbtop, hDb.le_normalizer⟩, hO2⟩
  obtain ⟨Y₀, hLbY₀, hY₀⟩ := (Set.toFinite (scriptY0 A (lB A))).exists_le_maximal hLb0
  obtain ⟨eθ⟩ := hJ
  have hLJ : Nat.card (↥Lb ⧸ aschbacherSolvableCore 3 ↥Lb) = 604800 := by
    rw [Nat.card_congr eθ.toEquiv, KFacts.KS14.card_nativeJ2]
  have hdvd : 604800 ∣ Nat.card (↥Y₀ ⧸ CFSG.pCore 2 ↥Y₀) := hLJ ▸ Proof1514.card_thetaQuot_dvd hLbY₀
  obtain ⟨hYeq, hLeq⟩ : Y₀ = (Y₀ ⊓ Lb) ⊔ CFSG.Open.pCoreOf 2 Y₀ ∧
      Lb = (Lb ⊓ Y₀) ⊔ CFSG.Open.pCoreOf 2 Lb := by
    rcases hlist G A b Lb hRb ⟨eθ⟩ Y₀ hY₀ hLbY₀ with h5 | h36 | hON | hfac
    · obtain ⟨e5⟩ := h5
      rw [Nat.card_congr e5.toEquiv, card_alternatingGroup_five] at hdvd
      norm_num at hdvd
    · rw [card_of_isTripleCover h36, card_alternatingGroup_six] at hdvd
      norm_num at hdvd
    · rw [card_of_isTripleCover hON, CFSG.Sporadic.ON.card_ON_eq] at hdvd
      norm_num at hdvd
    · exact hfac
  exact ⟨Y₀, ⟨hRb, hJ', hY₀, hLbY₀, hYeq, hLeq⟩⟩

theorem ConfY.sec13Data {Y : Subgroup G} (h : ConfY A c L Y) : Sec13Data G A c L :=
  h.sec15R.toSec13Data

theorem ConfY.A_le_normalizer {Y : Subgroup G} (h : ConfY A c L Y) :
    A ≤ Subgroup.normalizer (Y : Set G) :=
  h.mem_scriptY0Star.prop.1.1.2

theorem ConfY.quot_pCore_two_equiv
    {Y : Subgroup G} (h : ConfY A c L Y) :
    Nonempty (↥Y ⧸ CFSG.pCore 2 ↥Y ≃* CFSG.Blueprint.NativeSporadic.J2) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hD := h.sec13Data
  have hR := h.sec15R
  have hLc := hD.le_centralizer
  have hLtop : L ≠ ⊤ := fun htop => Sec6.centralizer_ne_top_of_ne_one hR.toTheoremFourHyp
    hD.ne_one (top_le_iff.mp (htop ▸ hLc))
  obtain ⟨eJ⟩ := Sec12.gap128OTwoHJ ↥L (hR.toTheoremFourHyp.sectionFourHyp hLtop)
      (Sec6.isPerfect_of_mem_thetaComponentsAt hD.mem_thetaComponentsAt) h.j2
  have hYle : Y ≤ (L ⊓ Y) ⊔ CFSG.Open.pCoreOf 2 Y := by
    rw [inf_comm]
    exact h.eq_Y.le
  obtain ⟨eY⟩ := Proof155R2.isoQuot_of_le_sup (L := L ⊓ Y) (N := Y) inf_le_right hYle
    (inf_le_right.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 Y))
    (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 Y)
    (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 Y)
  obtain ⟨eL⟩ := Proof155R2.isoQuot_of_le_sup (L := L ⊓ Y) (N := L) inf_le_left h.eq_L.le
    (inf_le_left.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 L))
    (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 L)
    (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 L)
  exact ⟨(eY.symm.trans eL).trans eJ⟩

theorem ConfY.isJ2Type
    {Y : Subgroup G} (h : ConfY A c L Y) : IsJ2Type Y :=
  h.quot_pCore_two_equiv

section CertificatesConj

theorem ConfY.map_zHJ {Y : Subgroup G} (h : ConfY A c L Y) {d : G} (hdA : d ∈ A) (hd1 : d ≠ 1)
    (hdZ : IsZCentral L d) (hdL : d ∈ L) :
    ((zHJ L Y d).subgroupOf L).map (QuotientGroup.mk' (aschbacherSolvableCore 3 ↥L)) =
      Subgroup.centralizer
        ({QuotientGroup.mk' (aschbacherSolvableCore 3 ↥L) ⟨d, hdL⟩} :
          Set (↥L ⧸ aschbacherSolvableCore 3 ↥L)) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hD := h.sec13Data
  have hd3 : d ^ 3 = 1 := hD.isElemAbelian.2 d hdA
  set θ := aschbacherSolvableCore 3 ↥L with hθ
  set π := QuotientGroup.mk' θ with hπ
  set C := Subgroup.centralizer ({π ⟨d, hdL⟩} : Set (↥L ⧸ θ)) with hC
  have hOθ : CFSG.Open.pCoreOf 2 L ≤ (aschbacherSolvableCore 3 L).map L.subtype := by
    obtain ⟨-, -, -, -, -, -, hr⟩ :=
      solvable_prime_complement_core_characterization (H := ↥L) Nat.prime_three
    rw [CFSG.Open.pCoreOf]
    exact Subgroup.map_mono (hr 2 Nat.prime_two (by norm_num))
  have hcov : ((L ⊓ Y).subgroupOf L).map π = ⊤ := by
    rw [eq_top_iff]
    rintro q -
    obtain ⟨l, rfl⟩ := QuotientGroup.mk'_surjective θ q
    have hl : (l : G) ∈ (L ⊓ Y) ⊔ CFSG.Open.pCoreOf 2 L := by rw [← h.eq_L]; exact l.2
    obtain ⟨m, hm, o, ho, hmo⟩ := exists_mul_of_mem_sup
      (inf_le_left.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 L)) hl
    refine ⟨⟨m, hm.1⟩, Subgroup.mem_subgroupOf.mpr hm, ?_⟩
    rw [hπ, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq]
    obtain ⟨t, ht, hto⟩ := hOθ ho
    have he : (⟨m, hm.1⟩ : ↥L)⁻¹ * l = t := by
      apply Subtype.ext
      rw [Subgroup.coe_mul, Subgroup.coe_inv, hmo, ← hto]
      simp
    rw [he]
    exact ht
  have hdW : d ∈ Subgroup.normalizer ((L ⊓ Y : Subgroup G) : Set G) :=
    mem_normalizer_inf (Subgroup.le_normalizer hdL) (h.A_le_normalizer hdA)
  have hZ₀ : (((L ⊓ Y) ⊓ Subgroup.centralizer ({d} : Set G)).subgroupOf L).map π = C := by
    rw [map_inf_centralizer_eq_inf inf_le_left hdW hdL hd3, hcov, top_inf_eq]
  obtain ⟨hdL', S, hdS, hSd⟩ := exists_sylow_of_isZCentral hdZ
  have hzc := Item148HJ.exists_sylow_quot hdL' ⟨S, hdS, hSd⟩
  have hz1 : π ⟨d, hdL⟩ ≠ 1 := by
    intro h1
    rw [hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
    exact hd1 (congrArg Subtype.val (eq_one_of_mem_aschbacherSolvableCore h1
      (Subtype.ext (by simpa using hd3))))
  have htop : perfectResidual ↥C = ⊤ :=
    KFacts.KS14.Native.j2_perfectResidual_centralizer_eq_top h.j2 hz1 hzc
  have htop3 : oPrimeResidual 3 ↥C = ⊤ :=
    Sec17.Proof171Steps.oPrimeResidual_eq_top_of_isTripleCover
      (KFacts.KS14.Native.j2_centralizer_isTripleCover h.j2 hz1 hzc)
      Sec17.Proof171Steps.oPrimeResidual_alternatingGroup_six
  have hZ₀L : (L ⊓ Y) ⊓ Subgroup.centralizer ({d} : Set G) ≤ L := inf_le_left.trans inf_le_left
  have hJ₁ : ((inSubgroup perfectResidual ((L ⊓ Y) ⊓ Subgroup.centralizer ({d} : Set G))).subgroupOf
      L).map π = C := by
    rw [map_inSubgroup_perfectResidual_subgroupOf hZ₀L, hZ₀, inSubgroup, htop,
      ← MonoidHom.range_eq_map, Subgroup.range_subtype]
  have hJ₁L : inSubgroup perfectResidual ((L ⊓ Y) ⊓ Subgroup.centralizer ({d} : Set G)) ≤ L :=
    (Subgroup.map_subtype_le _).trans hZ₀L
  rw [zHJ, map_oPrimeResidualOf_subgroupOf hJ₁L, hJ₁, oPrimeResidualOf, htop3,
    ← MonoidHom.range_eq_map, Subgroup.range_subtype]

theorem ConfY.quot_three_central {Y : Subgroup G} (h : ConfY A c L Y) {d : G} (hdA : d ∈ A)
    (hd1 : d ≠ 1) (hdZ : IsZCentral L d) (hdL : d ∈ L) :
    QuotientGroup.mk' (aschbacherSolvableCore 3 ↥L) ⟨d, hdL⟩ ≠ 1 ∧
      ∃ P : Sylow 3 (↥L ⧸ aschbacherSolvableCore 3 ↥L),
        QuotientGroup.mk' (aschbacherSolvableCore 3 ↥L) ⟨d, hdL⟩ ∈ (P : Subgroup _) ∧
          (P : Subgroup _) ≤ Subgroup.centralizer
            {QuotientGroup.mk' (aschbacherSolvableCore 3 ↥L) ⟨d, hdL⟩} := by
  have hd3 : d ^ 3 = 1 := h.sec13Data.isElemAbelian.2 d hdA
  refine ⟨fun h1 => ?_, ?_⟩
  · rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
    exact hd1 (congrArg Subtype.val (eq_one_of_mem_aschbacherSolvableCore h1
      (Subtype.ext (by simpa using hd3))))
  · obtain ⟨hdL', S, hdS, hSd⟩ := exists_sylow_of_isZCentral hdZ
    exact Item148HJ.exists_sylow_quot hdL' ⟨S, hdS, hSd⟩

theorem ConfY.zHJ_quot {Y : Subgroup G} (h : ConfY A c L Y) {d : G}
    (hdA : d ∈ A) (hd1 : d ≠ 1) (hdZ : IsZCentral L d) (hdL : d ∈ L) :
    Nonempty (↥(zHJ L Y d) ⧸ CFSG.pCore 2 ↥(zHJ L Y d) ≃*
      ↥(Subgroup.centralizer
        ({QuotientGroup.mk' (aschbacherSolvableCore 3 ↥L) ⟨d, hdL⟩} :
          Set (↥L ⧸ aschbacherSolvableCore 3 ↥L)))) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hmap := h.map_zHJ hdA hd1 hdZ hdL
  obtain ⟨hz1, hzc⟩ := h.quot_three_central hdA hd1 hdZ hdL
  set θ := aschbacherSolvableCore 3 ↥L with hθ
  set π := QuotientGroup.mk' θ with hπ
  set C := Subgroup.centralizer ({π ⟨d, hdL⟩} : Set (↥L ⧸ θ)) with hC
  set Z := zHJ L Y d with hZdef
  have hZL : Z ≤ L := (zHJ_le L Y d).trans (inf_le_left.trans inf_le_left)
  have hmem : ∀ x : ↥Z, (π.comp (Subgroup.inclusion hZL)) x ∈ C := fun x => by
    rw [← hmap]
    exact ⟨Subgroup.inclusion hZL x, Subgroup.mem_subgroupOf.mpr x.2, rfl⟩
  set ρ : ↥Z →* ↥C := (π.comp (Subgroup.inclusion hZL)).codRestrict C hmem with hρ
  have hρs : Function.Surjective ρ := by
    rintro ⟨q, hq⟩
    rw [← hmap] at hq
    obtain ⟨x, hx, rfl⟩ := hq
    exact ⟨⟨x, Subgroup.mem_subgroupOf.mp hx⟩, rfl⟩
  have hθ2 : IsPGroup 2 θ := Proof152Gen.isPGroup_theta_of_j2 h.sec15R.toSec14Std h.j2
  have hker : IsPGroup 2 ρ.ker := by
    have hk : ρ.ker = θ.comap (Subgroup.inclusion hZL) := by
      ext x
      rw [MonoidHom.mem_ker, Subgroup.mem_comap]
      constructor
      · intro hx
        exact (QuotientGroup.eq_one_iff _).mp (congrArg Subtype.val hx)
      · intro hx
        exact Subtype.ext ((QuotientGroup.eq_one_iff _).mpr hx)
    rw [hk]
    exact hθ2.comap_of_injective _ (Subgroup.inclusion_injective hZL)
  exact nonempty_quot_pCore_two_equiv ρ hρs hker
    (KFacts.KS14.Native.j2_pCore_two_centralizer_eq_bot h.j2 hz1 hzc)

end CertificatesConj

theorem ConfY.delta_le_n155
    {Y : Subgroup G} (h : ConfY A c L Y)
    (h155 : Item155wJ2 A (lB A)) {d : G} (hdA : d ∈ A) (hd1 : d ≠ 1) (hdZ : IsZCentral L d)
    {R : Subgroup G} (hR2 : IsPGroup 2 R) (hR1 : R ≠ ⊥) (hRQ : R ∈ scriptQ A (lB A))
    (hAR : A ≤ Subgroup.normalizer (R : Set G))
    (hZR : zHJ L Y d ≤ Subgroup.normalizer (R : Set G))
    (hRY : R ≤ Subgroup.normalizer (Y : Set G))
    (hRd : R ≤ Subgroup.centralizer ({d} : Set G)) {M : Subgroup G}
    (hM : M ∈ CFSG.maximalTwoLocalsContaining ((A ⊔ (zHJ L Y d ⊔ R) : Subgroup G) : Set G)) :
    delta A (lB A) M ≤ n155 A Y := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hD := h.sec13Data
  have hS := h.sec15R.toSec14Std
  have hdL : d ∈ L := mem_of_isZCentral hdZ
  have hmap := h.map_zHJ hdA hd1 hdZ hdL
  obtain ⟨hdL', S, hdS, hSd⟩ := exists_sylow_of_isZCentral hdZ
  obtain ⟨eZ⟩ := h.zHJ_quot hdA hd1 hdZ hdL
  obtain ⟨hz1, hzc⟩ := h.quot_three_central hdA hd1 hdZ hdL
  have hCq : IsQuasisimple ↥(Subgroup.centralizer
      ({QuotientGroup.mk' (aschbacherSolvableCore 3 ↥L) ⟨d, hdL⟩} :
        Set (↥L ⧸ aschbacherSolvableCore 3 ↥L))) :=
    (Item148HJ.centralizer_facts h.j2 hz1 hzc).1
  have hC1080 : Nat.card ↥(Subgroup.centralizer
      ({QuotientGroup.mk' (aschbacherSolvableCore 3 ↥L) ⟨d, hdL⟩} :
        Set (↥L ⧸ aschbacherSolvableCore 3 ↥L))) = 1080 := by
    rw [card_of_isTripleCover (KFacts.KS14.Native.j2_centralizer_isTripleCover h.j2 hz1 hzc),
      card_alternatingGroup_six]
  have hAd : A ≤ Subgroup.centralizer ({d} : Set G) := fun x hx =>
    Subgroup.mem_centralizer_singleton_iff.mpr (hD.commute hx hdA)
  set Z := zHJ L Y d with hZdef
  have hZle := zHJ_le L Y d
  have hZL : Z ≤ L := hZle.trans (inf_le_left.trans inf_le_left)
  have hZY : Z ≤ Y := hZle.trans (inf_le_left.trans inf_le_right)
  have hZd : Z ≤ Subgroup.centralizer ({d} : Set G) := hZle.trans inf_le_right
  have hAZ : A ≤ Subgroup.normalizer (Z : Set G) :=
    le_normalizer_zHJ hD.le_normalizer h.A_le_normalizer (hAd.trans Subgroup.le_normalizer)
  have hZΔ : Z ≤ delta A (lB A) Z :=
    le_delta_of_map_eq_centralizer hS h.j2 hdA hd1 hdL' ⟨S, hdS, hSd⟩ hZL hAZ hmap
  set Y' := Z ⊔ R with hY'def
  have hY'C : Y' ≤ Subgroup.centralizer ({d} : Set G) := sup_le hZd hRd
  have hAY' : A ≤ Subgroup.normalizer (Y' : Set G) := le_normalizer_sup hAZ hAR
  have hY'R : Y' ≤ Subgroup.normalizer (R : Set G) := sup_le hZR Subgroup.le_normalizer
  have hRO' : R ≤ CFSG.Open.pCoreOf 2 Y' :=
    CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 le_sup_right hY'R hR2
  have hY'top : Y' ≠ ⊤ := fun htop =>
    Sec6.centralizer_ne_top_of_ne_one h.sec15R.toTheoremFourHyp hd1 (top_le_iff.mp (htop ▸ hY'C))
  have hY'Δ : Y' ≤ delta A (lB A) Y' :=
    sup_le (hZΔ.trans (delta_mono le_sup_left)) (le_delta hRQ le_sup_right)
  have hY'3 : Y' ∈ scriptY3 A (lB A) :=
    ⟨⟨⟨hY'top, hAY'⟩, fun h0 => hR1 (le_bot_iff.mp (h0 ▸ hRO'))⟩, le_antisymm hY'Δ (delta_le Y')⟩
  have hZ'Z : oPrimeResidualOf 3 Z = Z := by
    rw [hZdef, zHJ, Proof156Res4.oRes3_idem']
  set X' := oPrimeResidualOf 3 Y' with hX'def
  have hZX' : Z ≤ X' := hZ'Z ▸ oPrimeResidualOf_mono 3 le_sup_left
  have hX'Y' : X' ≤ Y' := oPrimeResidualOf_le_self 3 Y'
  have hX'le : X' ≤ Z ⊔ (X' ⊓ R) := Proof155w.le_sup_inf_of_le hZR hZX' hX'Y'
  have hX'R : X' ≤ Subgroup.normalizer ((X' ⊓ R : Subgroup G) : Set G) :=
    Late.le_normalizer_inf Subgroup.le_normalizer (hX'Y'.trans hY'R)
  obtain ⟨e₁⟩ := Proof155R2.isoQuot_of_le_sup hZX' hX'le (hZX'.trans hX'R) hX'R
    (hR2.to_le inf_le_right)
  set e := e₁.symm.trans eZ with he
  have hX'Δ : X' ≤ delta A (lB A) X' :=
    hX'le.trans (sup_le (hZΔ.trans (delta_mono hZX'))
      (le_delta (mem_scriptQ_of_le hRQ inf_le_right
        (Late.le_normalizer_inf (le_normalizer_oPrimeResidualOf hAY') hAR)) inf_le_left))
  have hX'4 : X' ∈ scriptY4 A (lB A) :=
    ⟨⟨fun htop => hY'top (top_le_iff.mp (htop ▸ hX'Y')), le_normalizer_oPrimeResidualOf hAY'⟩,
      (Proof156Res4.oRes3_idem' Y').symm, le_antisymm hX'Δ (delta_le X'),
      CFSG.LocalCores.isQuasisimple_of_mulEquiv e.symm hCq⟩
  have hY'eq : Y' = X' ⊔ CFSG.Open.pCoreOf 2 Y' :=
    le_antisymm (sup_le (hZX'.trans le_sup_left) (hRO'.trans le_sup_right))
      (sup_le hX'Y' (CFSG.LieType.BorelTits.pCoreOf_le 2 Y'))
  have hX'Y : X' ≤ Y :=
    Proof155R2.oPrimeResidualOf_le_of_le_sup hR2 hRY (sup_le_sup_right hZY R)
  have hΓ : Y ∈ gam155 A (lB A) Y' X' :=
    ⟨h.mem_scriptY0Star, hX'Y, sup_le (hZY.trans Subgroup.le_normalizer) hRY⟩
  have hX'1080 : Nat.card (↥X' ⧸ CFSG.pCore 2 ↥X') = 1080 := by
    rw [Nat.card_congr e.toEquiv, hC1080]
  have hhyp : omg155 A X' ∨ Y = X' ⊔ CFSG.Open.pCoreOf 2 Y := by
    refine Or.inl (Or.inl ⟨fun ⟨n, _, hiso⟩ =>
      not_isoLThreePi_of_card_small (Or.inr hX'1080) 2 n hiso, ⟨fun e5 => ?_⟩⟩)
    have h60 := Nat.card_congr e5.toEquiv
    rw [hX'1080, card_alternatingGroup_five] at h60
    norm_num at h60
  have hX'b : Big152 X' := by
    unfold Big152
    rw [hX'1080]
    norm_num
  exact (h155 Y' hY'3 hX'4 hX'b hY'eq Y hΓ h.isJ2Type hhyp M hM)

end Gagen152SL25Res

end CFSG.RankThree.PartTwo.Sec15
