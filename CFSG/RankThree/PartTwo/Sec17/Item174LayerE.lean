module

public import CFSG.RankThree.PartTwo.Sec17.Item174Layer
import CFSG.RankThree.PartTwo.Sec14.Item147
import CFSG.RankThree.PartTwo.Sec17.Item1712StepsProofSeven
import CFSG.GH74.GLS.Stage2.Signalizer.Odd87GrpCoreA
import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8KAGen
import CFSG.GH74.GLS.Stage2.Bender.Thm2.Basic
import CFSG.LocalAnalysis.ComponentClassification.Sol76LayerFix
import CFSG.Walter.Bender1970.S4.ComponentTools
import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Zassenhaus.PartA.S8Bridge
import CFSG.GH74.GLS.C3.Layer1.Th2CaseI

public section

namespace CFSG.RankThree.PartTwo.Sec17.Proof174Host

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.PartTwo.Sec15 CFSG.RankThree.PartTwo.Sec16
  CFSG.RankThree.PartTwo.Sec17 CFSG.RankThree.PartTwo.Late CFSG.RankThree.LocalRank CFSG.GH74.GLS
  CFSG.RankThree.PartTwo.Sec16.Proof165
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem le_normalizer_componentLayerOf (Y : Subgroup G) :
    Y ≤ Subgroup.normalizer (GorensteinWalter.componentLayerOf Y : Set G) := fun _ hy =>
  CFSG.Walter.mem_normalizer_componentLayerOf (Subgroup.le_normalizer hy)

theorem componentLayerOf_le' (Y : Subgroup G) : GorensteinWalter.componentLayerOf Y ≤ Y :=
  sSup_le fun _ hK => hK.1

theorem commutator_componentLayerOf (Y : Subgroup G) :
    ⁅GorensteinWalter.componentLayerOf Y, GorensteinWalter.componentLayerOf Y⁆ =
      GorensteinWalter.componentLayerOf Y := by
  have hperf := CFSG.GorensteinWalter.componentLayerOf_isPerfect Y
  rw [← Subgroup.map_subtype_commutator, hperf.commutator_eq_top, ← MonoidHom.range_eq_map,
    Subgroup.range_subtype]

theorem false_of_isComponentOf_of_solvable {K Y : Subgroup G}
    (hK : GorensteinWalter.IsComponentOf K Y) (hs : Group.IsSolvable ↥K) : False := by
  have hnt : Nontrivial ↥K := hK.2.2.1
  have hperf : Group.IsPerfect ↥K := CFSG.Walter.isPerfect_of_isComponentOf hK
  exact (Group.IsSolvable.commutator_lt_top_of_nontrivial (G := K)).ne hperf.commutator_eq_top

theorem commutator_isComponentOf_eq_bot {p : ℕ} [Fact p.Prime] {K Y S : Subgroup G}
    (hK : GorensteinWalter.IsComponentOf K Y) (hSY : S ≤ Y)
    (hYS : Y ≤ Subgroup.normalizer (S : Set G)) (hS : IsPGroup p S) : ⁅K, S⁆ = ⊥ := by
  rcases CFSG.GorensteinWalter.fstar_component_le_or_commutator_eq_bot_of_subnormal_subgroupOf hSY
    (CFSG.ComponentClassification.Sol76.isSubnormal_subgroupOf_of_le_normalizer hSY le_rfl hYS
      Subgroup.le_normalizer) hK with hKS | hKS
  · exfalso
    have hKp : IsPGroup p K := hS.to_le hKS
    haveI := hKp.isNilpotent
    exact false_of_isComponentOf_of_solvable hK inferInstance
  · exact hKS

theorem componentLayerOf_le_centralizer {A : Subgroup G} {c : G} {L : Subgroup G}
    (h : Sec15R G A c L) (h149 : Item149 A (lB A)) (h146 : Item146 A (lB A)) {Y : Subgroup G}
    (hY : Y ∈ scriptY1Star A (lB A)) :
    GorensteinWalter.componentLayerOf Y ≤ Subgroup.centralizer (A : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hA : IsE27 A := h.toSec14Std.isE27
  have hA3 : IsPGroup 3 A := hA.isPGroup
  obtain ⟨⟨hY2, hYΔ⟩, hYo⟩ := hY.prop
  have hY3' : ¬ 3 ∣ Nat.card Y := not_three_dvd_of_oPrimeResidualOf_eq_bot hYo
  have hAY : A ≤ Subgroup.normalizer (Y : Set G) := hY2.1.2
  have hYinv : Y ∈ invariantPiSubgroups ⊤ A (piCompl 3) :=
    ⟨le_top, (isPiSubgroup_piCompl_iff Nat.prime_three Y).mpr hY3', hAY⟩
  have hYQ : Y ∈ scriptQ A (lB A) := by
    have := delta_mem_scriptQ hA h146 hYinv
    rwa [← hYΔ] at this
  set X := deltaZero A (lB A) Y with hXdef
  have hYAX : ⁅Y, A⁆ ≤ X := by
    have hcomm : ⁅Y, A⁆ ≤ Y := Subgroup.le_normalizer_iff_commutator_le_left.mp hAY
    have hAcomm : A ≤ Subgroup.normalizer ((⁅Y, A⁆ : Subgroup G) : Set G) := by
      rw [Subgroup.commutator_comm]
      exact Subgroup.normalizer_commutator_ge_left A Y
    exact le_deltaZero ⟨mem_scriptQ_of_le hYQ hcomm hAcomm,
      (CFSG.RankThreeEvenClassification.Helpers.coprime_commutator_idempotent 3 Nat.prime_three
        A Y hA3 hY3' hAY).symm⟩ hcomm
  have hXY : X ≤ Y := deltaZero_le Y
  have hFX : generalizedFitting ↥X = CFSG.pCore 2 ↥X :=
    rank3II_16_7_1 h.isSimpleGroup h.nonabelian h.charTwoType h149 hY
  have hEX : GorensteinWalter.componentLayerOf X = ⊥ := by
    rw [CFSG.EvenSporadicStandard.HSStd.Zassenhaus.PartA.componentLayerOf_eq,
      CFSG.GH74.GLS.Stage2.Bender.Thm2.layer_eq_bot_of_pgroup Nat.prime_two hFX, Subgroup.map_bot]
  set E := GorensteinWalter.componentLayerOf Y with hEdef
  have hEY : E ≤ Y := componentLayerOf_le' Y
  have hAE : A ≤ Subgroup.normalizer (E : Set G) := fun _ ha =>
    CFSG.Walter.mem_normalizer_componentLayerOf (hAY ha)
  set D := ⁅E, A⁆ with hDdef
  have hDE : D ≤ E := Subgroup.le_normalizer_iff_commutator_le_left.mp hAE
  have hDX : D ≤ X := (Subgroup.commutator_mono hEY le_rfl).trans hYAX
  have hsub : (D.subgroupOf Y).IsSubnormal :=
    CFSG.ComponentClassification.Sol76.isSubnormal_subgroupOf_of_le_normalizer hDE hEY
      (Subgroup.normalizer_commutator_ge_left E A) (le_normalizer_componentLayerOf Y)
  have hcomp : ∀ K, GorensteinWalter.IsComponentOf K Y → ⁅K, D⁆ = ⊥ := by
    intro K hK
    rcases CFSG.GorensteinWalter.fstar_component_le_or_commutator_eq_bot_of_subnormal_subgroupOf
      (hDE.trans hEY) hsub hK with hKD | hKD
    · exfalso
      have hKX : GorensteinWalter.IsComponentOf K X :=
        CFSG.Walter.IsComponentOf.of_le hK (hKD.trans hDX) hXY
      have hK0 : K = ⊥ := le_bot_iff.mp (hEX ▸ (le_sSup hKX : K ≤ GorensteinWalter.componentLayerOf X))
      have hs : Group.IsSolvable ↥K := by
        rw [hK0]
        infer_instance
      exact false_of_isComponentOf_of_solvable hK hs
    · exact hKD
  have hEcD : ⁅E, D⁆ = ⊥ := by
    rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
    exact sSup_le fun K hK => Subgroup.commutator_eq_bot_iff_le_centralizer.mp (hcomp K hK)
  have hDcE : ⁅D, E⁆ = ⊥ := by rw [Subgroup.commutator_comm]; exact hEcD
  have h3 : ⁅⁅E, E⁆, A⁆ = ⊥ := by
    refine Subgroup.commutator_commutator_eq_bot_of_rotate hDcE ?_
    rw [Subgroup.commutator_comm A E]
    exact hDcE
  rw [commutator_componentLayerOf] at h3
  exact Subgroup.commutator_eq_bot_iff_le_centralizer.mp h3

@[expose] def KFact35PerfAt (A : Subgroup G) (c : G) (L Y₀ : Subgroup G) : Prop :=
  omegaA A = {Subgroup.zpowers c} → ¬ IsL3TwoPow L →
    ¬ ⁅CFSG.Open.pCoreOf 2 (Subgroup.centralizer (Y₀ : Set G)), Subgroup.zpowers c⁆ ≤
        pPrimeCoreOf 3 (normalClosureIn (Subgroup.centralizer ((A ⊓ L : Subgroup G) : Set G)) c) →
    ∀ J : Subgroup G, J ≤ Subgroup.centralizer (A : Set G) → ⁅J, J⁆ = J →
      ⁅J, normalClosureIn (Subgroup.centralizer ((A ⊓ L : Subgroup G) : Set G)) c⁆ ≤
        pPrimeCoreOf 3 (normalClosureIn (Subgroup.centralizer ((A ⊓ L : Subgroup G) : Set G)) c)

theorem componentLayerOf_eq_bot {A : Subgroup G} {c : G} {L Y₀ : Subgroup G}
    (h : Sec17Std G A c L Y₀) (h149 : Item149 A (lB A)) (h146 : Item146 A (lB A))
    (hE : IsHyperplane A (A ⊓ L)) (hcL : c ∉ L)
    (hQ : CFSG.Open.pCoreOf 2 Y₀ ∈ scriptQ A (lB A))
    (hF : generalizedFitting ↥Y₀ = CFSG.pCore 2 ↥Y₀) (hKP : KFact35PerfAt A c L Y₀)
    (hL : ¬ IsL3TwoPow L) {Ŷ : Subgroup G} (hŶ : Ŷ ∈ scriptY1Star A (lB A))
    (hŶM : Ŷ ≤ Subgroup.normalizer (Y₀ : Set G)) :
    GorensteinWalter.componentLayerOf Ŷ = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set Z := GorensteinWalter.componentLayerOf Ŷ with hZdef
  set W := CFSG.Open.pCoreOf 2 (Subgroup.centralizer (Y₀ : Set G)) with hWdef
  set B := CFSG.Open.pCoreOf 2 Ŷ with hBdef
  have hZŶ : Z ≤ Ŷ := componentLayerOf_le' Ŷ
  have hZZ : ⁅Z, Z⁆ = Z := commutator_componentLayerOf Ŷ
  have hZA : Z ≤ Subgroup.centralizer (A : Set G) :=
    componentLayerOf_le_centralizer h.toSec15R h149 h146 hŶ
  have hAZ : A ≤ Subgroup.normalizer (Z : Set G) := fun _ ha =>
    CFSG.Walter.mem_normalizer_componentLayerOf (hŶ.prop.1.1.1.2 ha)
  have hB2 : IsPGroup 2 B := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 Ŷ
  have hZB : ∀ z ∈ Z, ∀ b ∈ B, z * b = b * z := by
    have hle : Z ≤ Subgroup.centralizer (B : Set G) := by
      refine sSup_le fun K hK => ?_
      exact Subgroup.commutator_eq_bot_iff_le_centralizer.mp
        (commutator_isComponentOf_eq_bot hK (CFSG.LieType.BorelTits.pCoreOf_le 2 Ŷ)
          (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 Ŷ) hB2)
    intro z hz b hb
    exact ((Subgroup.mem_centralizer_iff.mp (hle hz)) b hb).symm
  have hodd1 : ∀ x ∈ Z, Odd (orderOf x) → x = 1 := by
    intro x hx hodd
    have hxM := hŶM (hZŶ hx)
    have hxY := commute_y0_of_odd h hQ hF hŶ hŶM hxM hodd (hZB x hx)
    rcases h.a10_or_omega with hA10 | hΩ
    · exact eq_one_of_le_y0 h hQ (h.le_y0_of_alternating_ten hA10) hŶ hŶM hxM hodd (hZB x hx) hxY
    have hW2 : IsPGroup 2 W := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _
    have hŶW : Ŷ ≤ Subgroup.normalizer (W : Set G) := hŶM.trans (normalizer_le_normalizer_w Y₀)
    have hWM : W ≤ Subgroup.normalizer (Y₀ : Set G) :=
      (CFSG.LieType.BorelTits.pCoreOf_le 2 _).trans (Subgroup.centralizer_le_normalizer _)
    have htop : Ŷ ⊔ W ≠ ⊤ := fun ht =>
      normalizer_y0_ne_top h (top_le_iff.mp (ht ▸ sup_le hŶM hWM))
    have hAW : A ≤ Subgroup.normalizer (W : Set G) :=
      Subgroup.le_normalizer.trans (h.normalizer_le.trans (normalizer_le_normalizer_w Y₀))
    have hZW : Z ≤ Subgroup.normalizer (W : Set G) := hZŶ.trans hŶW
    have hWZQ : ⁅W, Z⁆ ∈ scriptQ A (lB A) := by
      by_cases hW : ⁅W, Subgroup.zpowers c⁆ ≤
          pPrimeCoreOf 3 (normalClosureIn (Subgroup.centralizer ((A ⊓ L : Subgroup G) : Set G)) c)
      · have hWZW : ⁅W, Z⁆ ≤ W := Subgroup.le_normalizer_iff_commutator_le_left.mp hZW
        exact mem_scriptQ_of_commutator_le h hE hcL hWZW
          (le_normalizer_commutator hAW hAZ) ((Subgroup.commutator_mono hWZW le_rfl).trans hW)
      · exact commutator_mem_scriptQ h hE hcL hZA hAZ (hKP hΩ hL hW Z hZA hZZ)
    have hWZB : ⁅W, Z⁆ ≤ B :=
      le_pCoreOf_two_of_mem_scriptQ hŶ hW2 hŶW htop hWZQ
        (Subgroup.le_normalizer_iff_commutator_le_left.mp hZW)
    set X := Subgroup.zpowers x with hXdef
    have hXZ : X ≤ Z := Subgroup.zpowers_le.mpr hx
    have hXW : X ≤ Subgroup.normalizer (W : Set G) := hXZ.trans hZW
    have hcop : Nat.Coprime (Nat.card X) (Nat.card W) := by
      obtain ⟨k, hk⟩ := hW2.exists_card_eq
      rw [hk, Nat.card_zpowers]
      exact Nat.Coprime.pow_right k (Nat.coprime_two_right.mpr hodd)
    have h2 : ⁅⁅W, X⁆, X⁆ = ⊥ := by
      rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
      intro y hy
      rw [Subgroup.mem_centralizer_iff]
      intro g hg
      exact hZB g (hXZ hg) y (hWZB (Subgroup.commutator_mono le_rfl hXZ hy))
    have hWX : ⁅W, X⁆ = ⊥ :=
      (CFSG.GH74.GLS.Stage2.Signalizer.Odd87.CoreA.commutator_commutator_eq_of_coprime hXW
        hcop).symm.trans h2
    have hxC0 : x ∈ Subgroup.centralizer (Y₀ : Set G) :=
      Subgroup.mem_centralizer_iff.mpr fun g hg => (hxY g hg).symm
    have hxW : x ∈ W := by
      refine mem_pCoreOf_of_isCharacteristicP (isCharacteristicP_centralizer_y0 h) hxC0 ?_
      intro w hw
      exact (Subgroup.mem_centralizer_iff.mp
        (Subgroup.commutator_eq_bot_iff_le_centralizer.mp hWX hw)) x (Subgroup.mem_zpowers x)
    obtain ⟨k, hk⟩ := hW2 ⟨x, hxW⟩
    have hk' : x ^ (2 ^ k) = 1 := by simpa using congrArg Subtype.val hk
    exact orderOf_eq_one_iff.mp (Nat.Coprime.eq_one_of_dvd
      (Nat.Coprime.pow_right k (Nat.coprime_two_right.mpr hodd)) (orderOf_dvd_of_pow_eq_one hk'))
  rw [← CFSG.GH74.GLS.Stage2.Signalizer.Ivk8.ka_gen_odd_of_perfect Z hZZ, eq_bot_iff,
    Subgroup.closure_le]
  rintro x ⟨hx, hodd⟩
  exact Subgroup.mem_bot.mpr (hodd1 x hx hodd)

theorem layer_eq_bot_of_kfact {A : Subgroup G} {c : G} {L Y₀ : Subgroup G}
    (h : Sec17Std G A c L Y₀) (h149 : Item149 A (lB A)) (h146 : Item146 A (lB A))
    (hE : IsHyperplane A (A ⊓ L)) (hcL : c ∉ L)
    (hQ : CFSG.Open.pCoreOf 2 Y₀ ∈ scriptQ A (lB A))
    (hF : generalizedFitting ↥Y₀ = CFSG.pCore 2 ↥Y₀) (hKP : KFact35PerfAt A c L Y₀) :
    ¬ IsL3TwoPow L → ∀ Ŷ ∈ scriptY1Star A (lB A), Ŷ ≤ Subgroup.normalizer (Y₀ : Set G) →
      CFSG.layer ↥Ŷ = ⊥ := by
  intro hL Ŷ hŶ hŶM
  have h0 := componentLayerOf_eq_bot h h149 h146 hE hcL hQ hF hKP hL hŶ hŶM
  rw [CFSG.EvenSporadicStandard.HSStd.Zassenhaus.PartA.componentLayerOf_eq] at h0
  exact (Subgroup.map_eq_bot_iff_of_injective _ Ŷ.subtype_injective).mp h0

theorem kfact35PerfAt_of_kfact39At {A : Subgroup G} {c : G} {L Y₀ : Subgroup G}
    (h39 : KFact39At A c L Y₀) : KFact35PerfAt A c L Y₀ := by
  intro hΩ hL hW J hJA hJJ
  have hperf : Group.IsPerfect ↥J := by
    refine ⟨Subgroup.map_injective J.subtype_injective ?_⟩
    rw [commutator_def, Subgroup.map_commutator, Subgroup.map_top, Subgroup.range_subtype, hJJ]
  set X := normalClosureIn (Subgroup.centralizer ((A ⊓ L : Subgroup G) : Set G)) c with hXdef
  set K := pPrimeCoreOf 3 X with hKdef
  have hCX : Subgroup.centralizer (A : Set G) ≤ Subgroup.normalizer (X : Set G) :=
    (Subgroup.centralizer_le inf_le_left).trans (le_normalizer_normalClosureIn _ c)
  have hCK : Subgroup.centralizer (A : Set G) ≤ Subgroup.normalizer (K : Set G) :=
    hCX.trans (normalizer_le_normalizer_pPrimeCoreOf 3 X)
  have hJT : J ≤ trivialOn X K := by
    refine (CFSG.GH74.GLS.Th2.CaseI.le_closure_two_elements hperf).trans ?_
    rw [Subgroup.closure_le]
    rintro g ⟨hg, hk⟩
    exact mem_trivialOn.mpr ⟨hCX (hJA hg), hCK (hJA hg), h39 hΩ hL hW g (hJA hg) hk⟩
  rw [Subgroup.commutator_le]
  intro g hg x hx
  rw [commutatorElement_def]
  exact (mem_trivialOn.mp (hJT hg)).2.2 x hx

theorem generalizedFitting_y0 {A : Subgroup G} {c : G} {L Y₀ : Subgroup G}
    (h : Sec17Std G A c L Y₀) : generalizedFitting ↥Y₀ = CFSG.pCore 2 ↥Y₀ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact (CFSG.isCharacteristicP_iff_generalizedFitting_eq_pCore _ 2).mp
    (Sec15.isCharacteristicP_of_le_normalizer Subgroup.le_normalizer le_rfl
      (isCharacteristicP_normalizer_y0 h))

end CFSG.RankThree.PartTwo.Sec17.Proof174Host
