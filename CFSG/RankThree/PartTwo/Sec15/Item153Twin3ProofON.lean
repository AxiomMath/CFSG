module

public import CFSG.RankThree.PartTwo.Sec15.Item153Twin2ProofON
import CFSG.RankThree.PartTwo.Sec15.Item152Proof
import CFSG.RankThree.PartTwo.Sec15.Item153Claims
import CFSG.RankThree.PartTwo.Sec14.Item147
import CFSG.RankThree.PartTwo.Sec15.Item1515StepsProofRead
import CFSG.RankThree.PartTwo.Late.Transitivity
import CFSG.RankThree.PartTwo.Sec13.Item13Basic
import CFSG.GroupTheory.Fitting.CharacteristicP
import CFSG.LieType.BorelTits.Basic
public import Certificates.Kernel.ThCent.Leaves
public import CFSG.Certificates.CosetTableShort
public import CFSG.LocalAnalysis.ComponentClassification.TwoLayer
public import CFSG.LocalAnalysis.SectionRank.Ccomm.Supercritical
public import CFSG.RankThree.PartTwo.Sec11.Data
public import CFSG.RankThree.PartTwo.Sec14.Item148StepCases
public import CFSG.RankThree.PartTwo.Sec14.Item148StepOne
public import CFSG.RankThree.PartTwo.Sec16.Item164Proof
public import CFSG.RankThree.PartTwo.Sec16.Item169HJ
public import CFSG.RankThree.PartTwo.Sec6.Statements
public import CFSG.RankThree.S4Free.SuzukiEight
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.FinalTheorem
public import Certificates.Certificate2202
public import Certificates.Certificate2326
public import Certificates.Certificate3171
public import Certificates.Certificate3171Base
public import Certificates.Certificate43
public import Certificates.Certificate8166
public import Certificates.Data.Item434SporWords
import CFSG.LocalAnalysis.ComponentClassification.DisjointSolvableKernels
import CFSG.LocalAnalysis.ComponentClassification.LayerMultiplication
import CFSG.LocalAnalysis.ComponentClassification.MinimalBCenter
import CFSG.LocalAnalysis.ComponentClassification.OrdinaryComponentJoins
import CFSG.LocalAnalysis.ComponentClassification.UniversalOrbitBlock
import CFSG.RankThree.PartTwo.Sec15.Item1514Steps1515
import CFSG.RankThree.PartTwo.Sec15.Item1515StepsProofTools

public section

namespace CFSG.RankThree.PartTwo.Sec15

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.LocalRank CFSG.GH74.GLS

variable {G : Type} [Group G] [Finite G]

@[expose] def Step156ONK (A : Subgroup G) (LB : Subgroup G → Subgroup G) : Prop :=
  ∀ Y ∈ scriptY0Star A LB,
    Sec4.IsTripleCover (↥Y ⧸ CFSG.pCore 2 ↥Y) CFSG.Blueprint.NativeSporadic.ON →
      ∃ (c₀ : G) (K : Subgroup G), Subgroup.zpowers c₀ ∈ omegaA A ∧ K ∈ scriptY4 A LB ∧
        K ≤ Y ⊓ Subgroup.centralizer ({c₀} : Set G) ∧
        Sec4.IsTripleCover ↥((K.subgroupOf Y).map (QuotientGroup.mk' (CFSG.pCore 2 ↥Y)))
          (alternatingGroup (Fin 6))

@[expose] noncomputable def Step156ONKR : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
    Sec15R G A c L → Step156ONK A (lB A)

namespace Proof153Twin3

omit [Finite G] in
theorem isCharacteristicP_of_le_normalizer' {H Q : Subgroup G} (hQH : Q ≤ H)
    (hQp : IsPGroup 2 Q) (hnorm : H ≤ Subgroup.normalizer (Q : Set G))
    (hcen : ∀ c ∈ H, c ∈ Subgroup.centralizer (Q : Set G) → ∃ k : ℕ, c ^ 2 ^ k = 1) :
    IsCharacteristicP 2 H := by
  have hUn : (Q.subgroupOf H).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hQH).mpr hnorm
  have hUp : IsPGroup 2 (Q.subgroupOf H) := hQp.comap_of_injective H.subtype H.subtype_injective
  have hUO : Q.subgroupOf H ≤ CFSG.pCore 2 H := le_sSup ⟨hUn, hUp⟩
  have hCp : IsPGroup 2 (Subgroup.centralizer ((Q.subgroupOf H : Subgroup H) : Set H)) := by
    intro c
    have hcQ : ((c : H) : G) ∈ Subgroup.centralizer (Q : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro q hq
      have hq' : (⟨q, hQH hq⟩ : H) ∈ Q.subgroupOf H := Subgroup.mem_subgroupOf.mpr hq
      exact congrArg Subtype.val (Subgroup.mem_centralizer_iff.mp c.2 _ hq')
    obtain ⟨k, hk⟩ := hcen _ (c : H).2 hcQ
    exact ⟨k, Subtype.ext (Subtype.ext (by simpa using hk))⟩
  have hCn : (Subgroup.centralizer ((Q.subgroupOf H : Subgroup H) : Set H)).Normal := by
    have := hUn
    exact Subgroup.normal_centralizer
  change Subgroup.centralizer (CFSG.pCore 2 H : Set H) ≤ CFSG.pCore 2 H
  exact (Subgroup.centralizer_le hUO).trans (le_sSup ⟨hCn, hCp⟩)

omit [Finite G] in
theorem eq_bot_of_isTripleCover {T : Type*} [Group T] [Finite T]
    (hT : Sec4.IsTripleCover T (alternatingGroup (Fin 6))) {N : Subgroup T} [N.Normal]
    (hN : IsPGroup 2 N) : N = ⊥ := by
  obtain ⟨h3, ⟨ε⟩⟩ := hT
  have hs : IsSimpleGroup (alternatingGroup (Fin 6)) := alternatingGroup.isSimpleGroup (by simp)
  set f : T →* alternatingGroup (Fin 6) :=
    ε.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center T)) with hf
  have hfs : Function.Surjective f := ε.surjective.comp (QuotientGroup.mk'_surjective _)
  have hNf : (N.map f).Normal := Subgroup.Normal.map inferInstance f hfs
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (N.map f) with hb | ht
  ·
    have hNZ : N ≤ Subgroup.center T := by
      intro x hx
      have h1 : f x = 1 := (Subgroup.map_eq_bot_iff _).mp hb hx
      rw [hf, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, map_eq_one_iff _ ε.injective,
        QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
      exact h1
    have hdvd : Nat.card N ∣ 3 := h3 ▸ Subgroup.card_dvd_of_le hNZ
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hN
    rw [hk] at hdvd
    have hk0 : k = 0 := by
      by_contra hk0
      have h2 : 2 ∣ 3 := (dvd_pow_self 2 hk0).trans hdvd
      omega
    rw [hk0, pow_zero] at hk
    exact Subgroup.eq_bot_of_card_eq N hk
  ·
    exfalso
    have h2 : IsPGroup 2 (N.map f) := hN.map f
    rw [ht] at h2
    have h360 : Nat.card (⊤ : Subgroup (alternatingGroup (Fin 6))) = 360 := by
      rw [Subgroup.card_top, card_alternatingGroup_six]
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp h2
    rw [h360] at hk
    have h3' : 3 ∣ 2 ^ k := hk ▸ (by norm_num : 3 ∣ 360)
    have := (Nat.prime_dvd_prime_iff_eq Nat.prime_three Nat.prime_two).mp
      (Nat.prime_three.dvd_of_dvd_pow h3')
    omega

end Proof153Twin3

open Proof153Twin3

theorem step156ONXK_of_onk {A : Subgroup G} {c : G} {L : Subgroup G} (h : Sec14Std G A c L)
    (h152 : Item152 A (lB A)) (hK : Step156ONK A (lB A)) : Step156ONXK A (lB A) := by
  intro Y hY hON
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨c₀, K, hc₀, hK4, hKYc, hKbar⟩ := hK Y hY hON
  set P := CFSG.Open.pCoreOf 2 Y with hP
  have hKY : K ≤ Y := hKYc.trans inf_le_left
  have hKc : K ≤ Subgroup.centralizer ({c₀} : Set G) := hKYc.trans inf_le_right
  have hPY : P ≤ Y := CFSG.LieType.BorelTits.pCoreOf_le 2 Y
  have hYP : Y ≤ Subgroup.normalizer (P : Set G) :=
    CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 Y
  have hP2 : IsPGroup 2 P := CFSG.LieType.BorelTits.pCoreOf_isPGroup (r := 2) Y
  have hAY : A ≤ Subgroup.normalizer (Y : Set G) := hY.prop.1.1.2
  have hAP : A ≤ Subgroup.normalizer (P : Set G) :=
    hAY.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 Y)
  have hAK : A ≤ Subgroup.normalizer (K : Set G) := hK4.1.2
  have hc₀A : c₀ ∈ A := (zpowers_mem_omegaA_iff.mp hc₀).1
  have hmemP : ∀ u : ↥Y, (u : G) ∈ P ↔ u ∈ CFSG.pCore 2 ↥Y := by
    intro u
    rw [hP, CFSG.Open.pCoreOf]
    constructor
    · rintro ⟨v, hv, hvu⟩
      rwa [← Subtype.ext hvu]
    · intro hu
      exact ⟨u, hu, rfl⟩
  set Kh := K ⊔ P with hKh
  have hKhY : Kh ≤ Y := sup_le hKY hPY
  have hKhP : Kh ≤ Subgroup.normalizer (P : Set G) := hKhY.trans hYP
  obtain ⟨M, hM⟩ := exists_mem_maximalTwoLocalsContaining hY.prop.2
  obtain ⟨-, -, -, hF⟩ := facts_of_mem_maximalTwoLocalsContaining h hM
  have hYc : IsCharacteristicP 2 ↥Y :=
    isCharacteristicP_of_mem_thetaComponentsIn hF (mem_thetaComponentsIn_of_item152 h h152 hY hM)
  have hCP : ∀ x ∈ Y, x ∈ Subgroup.centralizer (P : Set G) → x ∈ P := by
    intro x hx hxc
    have h1 : (⟨x, hx⟩ : ↥Y) ∈ Subgroup.centralizer (CFSG.pCore 2 ↥Y : Set ↥Y) := by
      rw [Subgroup.mem_centralizer_iff]
      intro u hu
      apply Subtype.ext
      exact Subgroup.mem_centralizer_iff.mp hxc u ((hmemP u).mpr hu)
    exact (hmemP ⟨x, hx⟩).mpr (hYc h1)
  have hPKh : P ≤ CFSG.Open.pCoreOf 2 Kh :=
    CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 le_sup_right hKhP hP2
  have hKh2 : Kh ∈ scriptY2 A :=
    ⟨⟨fun htop => hY.prop.1.1.1 (top_le_iff.mp (htop ▸ hKhY)), Sec14.le_normalizer_sup hAK hAP⟩,
      fun h0 => hY.prop.2.2 (le_bot_iff.mp (h0 ▸ hPKh))⟩
  have hKhF : generalizedFitting ↥Kh = CFSG.pCore 2 ↥Kh := by
    refine (isCharacteristicP_iff_generalizedFitting_eq_pCore ↥Kh 2).mp ?_
    refine isCharacteristicP_of_le_normalizer' le_sup_right hP2 hKhP fun x hx hxc => ?_
    obtain ⟨k, hk⟩ := hP2 ⟨x, hCP x (hKhY hx) hxc⟩
    exact ⟨k, by simpa using congrArg Subtype.val hk⟩
  obtain ⟨X₁, hX₁θ, hKX₁, hX₁0⟩ := h152 K hK4 Kh hKh2 le_sup_left hKhF
  have hX₁Kh : X₁ ≤ Kh := le_of_mem_thetaComponentsIn hX₁θ
  have hX₁Y : X₁ ≤ Y := hX₁Kh.trans hKhY
  have hAX₁ : A ≤ Subgroup.normalizer (X₁ : Set G) := hX₁0.1.1.2
  have hNX₁ : X₁ ⊓ P ≤ CFSG.Open.pCoreOf 2 X₁ :=
    CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 inf_le_left
      (Late.le_normalizer_inf Subgroup.le_normalizer (hX₁Y.trans hYP)) (hP2.to_le inf_le_right)
  have hKP : ∀ x ∈ X₁, ∃ k ∈ K, ∃ u ∈ P, x = k * u := by
    intro x hx
    have hxKh : x ∈ ((K ⊔ P : Subgroup G) : Set G) := hX₁Kh hx
    rw [Subgroup.coe_mul_of_left_le_normalizer_right K P (hKY.trans hYP)] at hxKh
    obtain ⟨k, hk, u, hu, hxku⟩ := hxKh
    exact ⟨k, hk, u, hu, hxku.symm⟩
  refine ⟨c₀, X₁, hc₀, hX₁0, hX₁Y, ?_, ⟨hc₀A, fun x hx => hNX₁ ⟨?_, ?_⟩⟩⟩
  ·
    set f : ↥X₁ →* ↥Y ⧸ CFSG.pCore 2 ↥Y :=
      (QuotientGroup.mk' (CFSG.pCore 2 ↥Y)).comp (Subgroup.inclusion hX₁Y) with hf
    set Kb := (K.subgroupOf Y).map (QuotientGroup.mk' (CFSG.pCore 2 ↥Y)) with hKb
    have hrange : f.range = Kb := by
      apply le_antisymm
      · rintro _ ⟨x, rfl⟩
        obtain ⟨k, hk, u, hu, hxku⟩ := hKP x x.2
        refine ⟨⟨k, hKY hk⟩, Subgroup.mem_subgroupOf.mpr hk, ?_⟩
        have hu' : (⟨u, hPY hu⟩ : ↥Y) ∈ CFSG.pCore 2 ↥Y := (hmemP ⟨u, hPY hu⟩).mp hu
        have hxe : Subgroup.inclusion hX₁Y x = ⟨k, hKY hk⟩ * ⟨u, hPY hu⟩ := Subtype.ext hxku
        have hu1 : QuotientGroup.mk' (CFSG.pCore 2 ↥Y) ⟨u, hPY hu⟩ = 1 := by
          rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
          exact hu'
        rw [hf, MonoidHom.comp_apply, hxe, map_mul, hu1, mul_one]
      · rintro _ ⟨k, hk, rfl⟩
        exact ⟨⟨k, hKX₁ (Subgroup.mem_subgroupOf.mp hk)⟩, rfl⟩
    have hker : f.ker = CFSG.pCore 2 ↥X₁ := by
      apply le_antisymm
      ·
        refine le_sSup ⟨inferInstance, fun x => ?_⟩
        have hxP : ((x : ↥X₁) : G) ∈ P := by
          have h1 : f x = 1 := x.2
          have h2 : (Subgroup.inclusion hX₁Y (x : ↥X₁) : ↥Y) ∈ CFSG.pCore 2 ↥Y :=
            (QuotientGroup.eq_one_iff _).mp h1
          exact (hmemP _).mpr h2
        obtain ⟨k, hk⟩ := hP2 ⟨_, hxP⟩
        exact ⟨k, Subtype.ext (Subtype.ext (by simpa using congrArg Subtype.val hk))⟩
      ·
        have hKb' : Sec4.IsTripleCover ↥f.range (alternatingGroup (Fin 6)) :=
          Proof1515.isTripleCover_congr (MulEquiv.subgroupCongr hrange.symm) hKbar
        have hn : ((CFSG.pCore 2 ↥X₁).map f.rangeRestrict).Normal :=
          Subgroup.Normal.map inferInstance _ f.rangeRestrict_surjective
        have h2 : IsPGroup 2 ((CFSG.pCore 2 ↥X₁).map f.rangeRestrict) :=
          CFSG.pCore_isPGroup.map _
        have hbot := eq_bot_of_isTripleCover hKb' h2
        intro x hx
        have h1 : f.rangeRestrict x = 1 := by
          have : f.rangeRestrict x ∈ (CFSG.pCore 2 ↥X₁).map f.rangeRestrict :=
            Subgroup.mem_map_of_mem _ hx
          rwa [hbot, Subgroup.mem_bot] at this
        rw [MonoidHom.mem_ker]
        exact congrArg Subtype.val h1
    have e : ↥X₁ ⧸ CFSG.pCore 2 ↥X₁ ≃* ↥Kb :=
      (QuotientGroup.quotientMulEquivOfEq hker.symm).trans
        ((QuotientGroup.quotientKerEquivRange f).trans (MulEquiv.subgroupCongr hrange))
    exact Proof1515.isTripleCover_congr e.symm hKbar
  ·
    exact X₁.mul_mem ((Subgroup.mem_normalizer_iff.mp (hAX₁ hc₀A) x).mp hx) (X₁.inv_mem hx)
  ·
    obtain ⟨k, hk, u, hu, rfl⟩ := hKP x hx
    have hck : c₀ * k = k * c₀ :=
      Subgroup.mem_centralizer_iff.mp (hKc hk) c₀ (Set.mem_singleton c₀)
    have hcu : c₀ * u * c₀⁻¹ ∈ P := (Subgroup.mem_normalizer_iff.mp (hAP hc₀A) u).mp hu
    have hcomm : c₀ * u * c₀⁻¹ * u⁻¹ ∈ P := P.mul_mem hcu (P.inv_mem hu)
    have e1 : c₀ * (k * u) * c₀⁻¹ * (k * u)⁻¹ = k * (c₀ * u * c₀⁻¹ * u⁻¹) * k⁻¹ := by
      calc c₀ * (k * u) * c₀⁻¹ * (k * u)⁻¹ = (c₀ * k) * u * c₀⁻¹ * u⁻¹ * k⁻¹ := by group
        _ = (k * c₀) * u * c₀⁻¹ * u⁻¹ * k⁻¹ := by rw [hck]
        _ = k * (c₀ * u * c₀⁻¹ * u⁻¹) * k⁻¹ := by group
    rw [e1]
    exact (Subgroup.mem_normalizer_iff.mp (hYP (hKY hk)) _).mp hcomm

theorem step156ONXKR_of_onk (h152 : Item152R) (hK : Step156ONKR) : Step156ONXKR :=
  fun G _ _ A c L hR => step156ONXK_of_onk hR.toSec14Std (h152 G A c L hR) (hK G A c L hR)

end CFSG.RankThree.PartTwo.Sec15
