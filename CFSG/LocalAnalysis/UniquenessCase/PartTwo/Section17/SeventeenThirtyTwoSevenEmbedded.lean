module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.OutPRankBound
public import CFSG.LocalAnalysis.UniquenessCase.UCR638
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SylowCentralOuter
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Fourteen5QuotBasic
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Fourteen3a
public import CFSG.LocalAnalysis.UniquenessCase.UC6S846e
public import CFSG.LocalAnalysis.UniquenessCase.UC6S846f
public import CFSG.LocalAnalysis.UniquenessCase.UC6R
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.ThreeD4TwoAutHolds
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.ThreeD4TwoOrderFacts
public import CFSG.LocalAnalysis.UniquenessCase.UC22P22l
public import CFSG.LocalAnalysis.UniquenessCase.UC22P21c
public import CFSG.GroupTheory.CoprimeCentralizerTransport
public import CFSG.HardMathSupport.Malle.OvergroupTransport.Transport
public import CFSG.LocalAnalysis.SectionRank.PRank
public import CFSG.RankThree.PartTwo.Sec10.Sec10XProofTen
public import CFSG.LocalAnalysis.ComponentInitial.GL3TwoFixedModelSelector
public import CFSG.RankThree.PartTwo.KFacts.K72OutL2
public import CFSG.RankThree.PartTwo.KFacts.KS14HJSignalizer
public import CFSG.RankThree.PartTwo.Sec6.Statements

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17

open Subgroup CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)
open CFSG.RankThree.PartTwo.Sec10.Sec10XProof
open CFSG.LocalAnalysis.UniquenessCase.PartTwo

variable {G : Type} [Group G] [Finite G]

theorem exists_elemAbelian_fortyNine_le_of_is3D4
    (hS7 : Inputs1719.K_3D4TwoSylowSeven) {L : Subgroup G} (h3D4 : Is3D4 (Bar2 L) 1) :
    ∃ E : Subgroup G, E ≤ L ∧ CFSG.Open.IsElemAbelian 7 E ∧ Nat.card E = 49 := by
  classical
  obtain ⟨P⟩ : Nonempty (Sylow 7 (Bar2 L)) := inferInstance
  obtain ⟨hPel, hPcard⟩ := hS7 (Bar2 L) h3D4 P
  let π : ↥L →* Bar2 L := QuotientGroup.mk' (CFSG.pCore 2 ↥L)
  have hker : IsPGroup 2 π.ker := by
    rw [QuotientGroup.ker_mk']
    exact CFSG.pCore_isPGroup
  obtain ⟨Q, -, hQmap, hQdisj⟩ :=
    UC6S846.exists_lift_pGroup π (QuotientGroup.mk'_surjective _) hker
      Nat.prime_seven (by norm_num) (P : Subgroup (Bar2 L)) P.isPGroup'
  refine ⟨Q.map L.subtype, Subgroup.map_subtype_le _, ?_, ?_⟩
  · exact CFSG.SectionRank.isElemAbelian_map
      (UC6S846.isElemAbelian_of_disjoint_ker π Q hQdisj (by rw [hQmap]; exact hPel)) _
  · rw [Subgroup.card_map_of_injective L.subtype_injective,
      ← UC6S846.card_map_of_disjoint_ker π Q hQdisj, hQmap, hPcard]

theorem mem_centralizer_barImage_of_mem_centOverO2 {M L : Subgroup G} (hLM : L ≤ M)
    (hMN : M ≤ Subgroup.normalizer (L : Set G)) {y : G} (hy : y ∈ F08.CentOverO2 M L)
    (hyM : y ∈ M) :
    (QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨y, hyM⟩ : Bar2 M) ∈
      Subgroup.centralizer (barImage M L : Set (Bar2 M)) := by
  classical
  have hcore : CFSG.Open.pCoreOf 2 L ≤ CFSG.Open.pCoreOf 2 M :=
    CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2
      ((CFSG.LieType.BorelTits.pCoreOf_le 2 L).trans hLM)
      (hMN.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 L))
      (UC22.uc22p21c_isPGroup_pCoreOf L)
  rw [Subgroup.mem_centralizer_iff]
  intro z hz
  obtain ⟨m, hmL, rfl⟩ := UC22.uc22p21c_mem_barImage.1 hz
  have hmem : (⟨y, hyM⟩ * m * ⟨y, hyM⟩⁻¹ * m⁻¹ : ↥M) ∈ CFSG.pCore 2 ↥M :=
    (CFSG.mem_openPCoreOf_iff (p := 2) (H := M)
      (⟨y, hyM⟩ * m * ⟨y, hyM⟩⁻¹ * m⁻¹ : ↥M)).1
      (by simpa using hcore ((mem_centOverO2_iff.mp hy).2 m hmL))
  have h1 : QuotientGroup.mk' (CFSG.pCore 2 ↥M)
      (⟨y, hyM⟩ * m * ⟨y, hyM⟩⁻¹ * m⁻¹) = 1 := by
    rw [← MonoidHom.mem_ker, QuotientGroup.ker_mk']
    exact hmem
  rw [map_mul, map_mul, map_mul, map_inv, map_inv] at h1
  exact (mul_inv_eq_iff_eq_mul.1 (mul_inv_eq_one.1 h1)).symm

theorem one_le_pRank_centOverO2_of_is3D4 (hAut : Inputs1719.K_3D4TwoAut)
    (hRk : Inputs1719.K_3D4TwoThreeRank) {M L : Subgroup G}
    (hLM : L ≤ M) (hMN : M ≤ normalizer (L : Set G)) (h3D4 : Is3D4 (Bar2 L) 1)
    (hOp : UC22.F10.OpRes 3 M = M) (h3 : 3 ≤ CFSG.Open.pRank 3 M) :
    1 ≤ CFSG.Open.pRank 3 (F08.CentOverO2 M L) := by
  obtain ⟨hZ, hcyc, -⟩ := hAut (Bar2 L) h3D4
  have hbound := pRank_le_pRank_bar2_add_pRank_centOverO2 hLM hMN hZ hcyc
    Nat.prime_three (by norm_num) hOp
  have hbar := hRk (Bar2 L) h3D4
  omega

theorem one_lt_pRank_normalizer_of_is3D4
    (hN7 : Inputs1719.K_3D4TwoSevenNormalizer) {M L : Subgroup G} (hL : L ∈ calC M)
    (hMN : M ≤ Subgroup.normalizer (L : Set G)) (h3D4 : Is3D4 (Bar2 L) 1)
    (hC3 : 1 ≤ CFSG.Open.pRank 3 (F08.CentOverO2 M L)) {X : Subgroup G} (hXL : X ≤ L)
    (hX : Nat.card X = 7) :
    1 < CFSG.Open.pRank 3 (M ⊓ Subgroup.normalizer (X : Set G)) := by
  classical
  have hLM : L ≤ M := hL.1.le
  have hAut : Inputs1719.K_3D4TwoAut := Inputs1719.k_3D4TwoAut_holds
  have h3O2 : ¬ 3 ∣ Nat.card (CFSG.pCore 2 ↥M) :=
    @CFSG.GroupTheory.not_dvd_card_of_isPGroup ↥(CFSG.pCore 2 ↥M) _ _ 2 3
      ⟨Nat.prime_two⟩ (CFSG.pCore_isPGroup (p := 2) (G := ↥M)) Nat.prime_three
      (by norm_num)
  obtain ⟨C3, hC3le, hC3el, hC3card⟩ :=
    CFSG.SectionRank.exists_pRank (p := 3) (by norm_num) (F08.CentOverO2 M L)
  have hC3dvd : 3 ∣ Nat.card C3 := by
    rw [hC3card]
    exact dvd_pow_self 3 (by omega)
  obtain ⟨yE, hyE⟩ := @exists_prime_orderOf_dvd_card' ↥C3 _ _ 3 ⟨Nat.prime_three⟩ hC3dvd
  let y : G := yE
  have hyord : orderOf y = 3 := by
    change orderOf (yE : G) = 3
    rw [Subgroup.orderOf_coe]
    exact hyE
  have hyC : y ∈ F08.CentOverO2 M L := hC3le yE.2
  have hyM : y ∈ M := (mem_centOverO2_iff.mp hyC).1
  let ybar : Bar2 M := QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨y, hyM⟩
  have hyordM : orderOf (⟨y, hyM⟩ : ↥M) = 3 := by
    rw [← Subgroup.orderOf_coe]
    exact hyord
  have hybar_ord : orderOf ybar = 3 :=
    CFSG.GroupTheory.CoprimeTransport.orderOf_mk_eq_prime h3O2 hyordM
  have hybar_cent : ybar ∈ Subgroup.centralizer (barImage M L : Set (Bar2 M)) :=
    mem_centralizer_barImage_of_mem_centOverO2 hLM hMN hyC hyM
  obtain ⟨xE, hxE⟩ := @exists_prime_orderOf_dvd_card' ↥X _ _ 7 ⟨Nat.prime_seven⟩
    (by simpa [hX] using dvd_rfl)
  let x : G := xE
  have hxX : x ∈ X := xE.2
  have hxord : orderOf x = 7 := by
    change orderOf (xE : G) = 7
    rw [Subgroup.orderOf_coe]
    exact hxE
  have hXz : X = Subgroup.zpowers x := by
    have hcard : Nat.card X ≤ Nat.card (Subgroup.zpowers x) := by
      rw [Nat.card_zpowers, hxord, hX]
    exact (Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hxX) hcard).symm
  have hxL : x ∈ L := hXL hxX
  have hxM : x ∈ M := hLM hxL
  let xbarL : Bar2 L := QuotientGroup.mk' (CFSG.pCore 2 ↥L) ⟨x, hxL⟩
  have h7O2L : ¬ 7 ∣ Nat.card (CFSG.pCore 2 ↥L) :=
    @CFSG.GroupTheory.not_dvd_card_of_isPGroup ↥(CFSG.pCore 2 ↥L) _ _ 2 7
      ⟨Nat.prime_two⟩ (CFSG.pCore_isPGroup (p := 2) (G := ↥L)) Nat.prime_seven
      (by norm_num)
  have hxLord : orderOf (⟨x, hxL⟩ : ↥L) = 7 := by
    rw [← Subgroup.orderOf_coe]
    exact hxord
  have hxbarL_ord : orderOf xbarL = 7 :=
    CFSG.GroupTheory.CoprimeTransport.orderOf_mk_eq_prime h7O2L hxLord
  let xbarM : Bar2 M := QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨x, hxM⟩
  have hN7rank : CFSG.Open.pRank 3
      (⊤ : Subgroup ↥(Subgroup.normalizer (Subgroup.zpowers xbarL : Set (Bar2 L)))) = 1 :=
    hN7 (Bar2 L) h3D4 xbarL hxbarL_ord
  have hN7dvd : 3 ∣ Nat.card
      ↥(Subgroup.normalizer (Subgroup.zpowers xbarL : Set (Bar2 L))) := by
    obtain ⟨E7, -, hE7el, hE7card⟩ :=
      CFSG.SectionRank.exists_pRank (p := 3) (by norm_num)
        (⊤ : Subgroup ↥(Subgroup.normalizer (Subgroup.zpowers xbarL : Set (Bar2 L))))
    have hE7 : Nat.card E7 = 3 := by
      rw [hE7card, hN7rank]
      norm_num
    have hdvd : Nat.card E7 ∣ Nat.card
        ↥(Subgroup.normalizer (Subgroup.zpowers xbarL : Set (Bar2 L))) := by
      simpa using Subgroup.card_dvd_of_le
        (le_top : E7 ≤ (⊤ : Subgroup
          ↥(Subgroup.normalizer (Subgroup.zpowers xbarL : Set (Bar2 L)))))
    rwa [hE7] at hdvd
  obtain ⟨zN, hzN⟩ := @exists_prime_orderOf_dvd_card'
    ↥(Subgroup.normalizer (Subgroup.zpowers xbarL : Set (Bar2 L))) _ _ 3
    ⟨Nat.prime_three⟩ hN7dvd
  let zbarL : Bar2 L := zN
  have hzbarL_ord : orderOf zbarL = 3 := by
    change orderOf (zN : Bar2 L) = 3
    rw [Subgroup.orderOf_coe]
    exact hzN
  have hzbarL_norm : zbarL ∈ Subgroup.normalizer (Subgroup.zpowers xbarL : Set (Bar2 L)) :=
    zN.2
  obtain ⟨e, he⟩ := UC22.uc22p22l_barImage_equiv (L := M) (K := L) hL
  have hex : ((e xbarL : ↥(barImage M L)) : Bar2 M) = xbarM := by
    have h := he ⟨x, hxL⟩
    simpa [xbarL, xbarM, Subgroup.inclusion] using h
  let zbarM : Bar2 M := (e zbarL : ↥(barImage M L))
  have hzbarM_mem : zbarM ∈ barImage M L := (e zbarL).2
  have hzbarM_ord : orderOf zbarM = 3 := by
    change orderOf ((e zbarL : ↥(barImage M L)) : Bar2 M) = 3
    rw [Subgroup.orderOf_coe, MulEquiv.orderOf_eq, hzbarL_ord]
  have hxbarM_mem : xbarM ∈ barImage M L := by
    show xbarM ∈ (L.subgroupOf M).map (QuotientGroup.mk' (CFSG.pCore 2 ↥M))
    exact Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr hxL)
  have hybar_comm_x : ybar * xbarM = xbarM * ybar :=
    (Subgroup.mem_centralizer_iff.mp hybar_cent xbarM hxbarM_mem).symm
  have hybar_norm : ybar ∈ Subgroup.normalizer (Subgroup.zpowers xbarM : Set (Bar2 M)) := by
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    have hconj : MulAut.conj ybar xbarM = xbarM := by
      rw [MulAut.conj_apply, hybar_comm_x, mul_assoc, mul_inv_cancel, mul_one]
    rw [MonoidHom.map_zpowers]
    simpa using congrArg Subgroup.zpowers hconj
  have hzbarM_norm : zbarM ∈ Subgroup.normalizer
      (Subgroup.zpowers xbarM : Set (Bar2 M)) := by
    let H' : Subgroup ↥(barImage M L) :=
      (Subgroup.zpowers xbarL).map (e : Bar2 L →* ↥(barImage M L))
    have hz' : (e zbarL : ↥(barImage M L)) ∈
        Subgroup.normalizer (H' : Set ↥(barImage M L)) := by
      have h := Subgroup.mem_map_of_mem (e : Bar2 L →* ↥(barImage M L)) hzbarL_norm
      exact Subgroup.le_normalizer_map (e : Bar2 L →* ↥(barImage M L)) h
    have hmem : zbarM ∈ (Subgroup.normalizer (H' : Set ↥(barImage M L))).map
        (Subgroup.subtype (barImage M L)) :=
      Subgroup.mem_map_of_mem _ hz'
    have hle := Subgroup.le_normalizer_map (Subgroup.subtype (barImage M L)) hmem
    simpa [H', MonoidHom.map_zpowers, hex] using hle
  have hZ : Subgroup.center (Bar2 L) = ⊥ := (hAut (Bar2 L) h3D4).1
  have hcenter : barImage M L ⊓
      Subgroup.centralizer (barImage M L : Set (Bar2 M)) = ⊥ := by
    apply le_antisymm _ bot_le
    intro c hc
    have hc' : e.symm ⟨c, hc.1⟩ ∈ Subgroup.center (Bar2 L) := by
      rw [Subgroup.mem_center_iff]
      intro d
      have hd : ((e d : ↥(barImage M L)) : Bar2 M) ∈ barImage M L := (e d).2
      have hcomm : ((e d : ↥(barImage M L)) : Bar2 M) * c =
          c * ((e d : ↥(barImage M L)) : Bar2 M) :=
        Subgroup.mem_centralizer_iff.mp hc.2 ((e d : ↥(barImage M L)) : Bar2 M) hd
      have hcomm' : e d * (⟨c, hc.1⟩ : ↥(barImage M L)) =
          (⟨c, hc.1⟩ : ↥(barImage M L)) * e d :=
        Subtype.ext hcomm
      calc d * e.symm ⟨c, hc.1⟩ = e.symm (e d * ⟨c, hc.1⟩) := by simp
        _ = e.symm (⟨c, hc.1⟩ * e d) := by rw [hcomm']
        _ = e.symm ⟨c, hc.1⟩ * d := by simp
    have hcbot : e.symm ⟨c, hc.1⟩ = 1 := by
      rw [← Subgroup.mem_bot, ← hZ]
      exact hc'
    have hone : (⟨c, hc.1⟩ : ↥(barImage M L)) = 1 := by
      have h := congrArg e hcbot
      simpa using h
    have hcoe : c = 1 := by
      simpa using congrArg Subtype.val hone
    exact Subgroup.mem_bot.mpr hcoe
  have hint : Subgroup.zpowers ybar ⊓ Subgroup.zpowers zbarM = ⊥ := by
    apply le_antisymm _ bot_le
    intro w hw
    have hw1 : w ∈ barImage M L :=
      (Subgroup.zpowers_le.mpr hzbarM_mem) hw.2
    have hw2 : w ∈ Subgroup.centralizer (barImage M L : Set (Bar2 M)) :=
      (Subgroup.zpowers_le.mpr hybar_cent) hw.1
    have hwb : w ∈ barImage M L ⊓
        Subgroup.centralizer (barImage M L : Set (Bar2 M)) := ⟨hw1, hw2⟩
    rwa [hcenter] at hwb
  have hcomm_yz : ∀ a ∈ Subgroup.zpowers ybar, ∀ b ∈ Subgroup.zpowers zbarM,
      a * b = b * a := by
    intro a ha b hb
    exact (Subgroup.mem_centralizer_iff.mp
      ((Subgroup.zpowers_le.mpr hybar_cent) ha) b (Subgroup.zpowers_le.mpr hzbarM_mem hb)).symm
  let NX : Subgroup (Bar2 M) := Subgroup.normalizer (Subgroup.zpowers xbarM : Set (Bar2 M))
  have hyN : ybar ∈ NX := hybar_norm
  have hzN' : zbarM ∈ NX := hzbarM_norm
  let y' : ↥NX := ⟨ybar, hyN⟩
  let z' : ↥NX := ⟨zbarM, hzN'⟩
  have hy'_ord : orderOf y' = 3 := by
    rw [← Subgroup.orderOf_coe y']
    exact hybar_ord
  have hz'_ord : orderOf z' = 3 := by
    rw [← Subgroup.orderOf_coe z']
    exact hzbarM_ord
  have hy'p : y' ^ 3 = 1 := by
    have h := pow_orderOf_eq_one y'
    rwa [hy'_ord] at h
  have hz'p : z' ^ 3 = 1 := by
    have h := pow_orderOf_eq_one z'
    rwa [hz'_ord] at h
  have hy'el : CFSG.Open.IsElemAbelian 3 (Subgroup.zpowers y') :=
    CFSG.Open.isElemAbelian_zpowers hy'p
  have hz'el : CFSG.Open.IsElemAbelian 3 (Subgroup.zpowers z') :=
    CFSG.Open.isElemAbelian_zpowers hz'p
  have hy'card : Nat.card (Subgroup.zpowers y') = 3 ^ 1 := by
    rw [Nat.card_zpowers, hy'_ord]
    norm_num
  have hz'card : Nat.card (Subgroup.zpowers z') = 3 ^ 1 := by
    rw [Nat.card_zpowers, hz'_ord]
    norm_num
  have hy'z' : ∀ a ∈ Subgroup.zpowers y', ∀ b ∈ Subgroup.zpowers z',
      a * b = b * a := by
    intro a ha b hb
    have ha' : (a : Bar2 M) ∈ Subgroup.zpowers ybar := by
      have h := Subgroup.mem_map_of_mem (Subgroup.subtype NX) ha
      rwa [MonoidHom.map_zpowers] at h
    have hb' : (b : Bar2 M) ∈ Subgroup.zpowers zbarM := by
      have h := Subgroup.mem_map_of_mem (Subgroup.subtype NX) hb
      rwa [MonoidHom.map_zpowers] at h
    apply Subtype.ext
    simpa using hcomm_yz (a : Bar2 M) ha' (b : Bar2 M) hb'
  have hint' : Subgroup.zpowers y' ⊓ Subgroup.zpowers z' = ⊥ := by
    apply le_antisymm _ bot_le
    intro w hw
    have hw1 : (w : Bar2 M) ∈ Subgroup.zpowers ybar := by
      have h := Subgroup.mem_map_of_mem (Subgroup.subtype NX) hw.1
      rwa [MonoidHom.map_zpowers] at h
    have hw2 : (w : Bar2 M) ∈ Subgroup.zpowers zbarM := by
      have h := Subgroup.mem_map_of_mem (Subgroup.subtype NX) hw.2
      rwa [MonoidHom.map_zpowers] at h
    have hwb : (w : Bar2 M) ∈ Subgroup.zpowers ybar ⊓ Subgroup.zpowers zbarM :=
      ⟨hw1, hw2⟩
    rw [hint] at hwb
    exact Subgroup.mem_bot.mpr (Subtype.ext (Subgroup.mem_bot.mp hwb))
  obtain ⟨W, hWel, hWcard⟩ :=
    UC6S846.exists_elemAbelian_of_commute (Z := ↥NX) Nat.prime_three
      hy'el hz'el hy'card hz'card hy'z' hint'
  have hrankNX : 2 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup ↥NX) := by
    refine CFSG.SectionRank.le_pRank (p := 3) (by norm_num) (k := 2) le_top hWel ?_
    rw [hWcard]
  have hrankNX' : 2 ≤ CFSG.Open.pRank 3 NX := by
    rwa [← CFSG.SectionRank.pRank_eq_pRank_top_subgroup NX] at hrankNX
  have hXM : X ≤ M := hXL.trans hLM
  have hA : IsPGroup 7 (X.subgroupOf M) := by
    refine IsPGroup.of_card (n := 1) ?_
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hXM).toEquiv, hX]
    norm_num
  have h7O2M : ¬ 7 ∣ Nat.card (CFSG.pCore 2 ↥M) :=
    @CFSG.GroupTheory.not_dvd_card_of_isPGroup ↥(CFSG.pCore 2 ↥M) _ _ 2 7
      ⟨Nat.prime_two⟩ (CFSG.pCore_isPGroup (p := 2) (G := ↥M)) Nat.prime_seven
      (by norm_num)
  have hAmap : (X.subgroupOf M).map (QuotientGroup.mk' (CFSG.pCore 2 ↥M)) =
      Subgroup.zpowers xbarM := by
    have h1 : X.subgroupOf M = Subgroup.zpowers (⟨x, hxM⟩ : ↥M) := by
      rw [hXz]
      ext y
      rw [Subgroup.mem_subgroupOf, Subgroup.mem_zpowers_iff, Subgroup.mem_zpowers_iff]
      constructor
      · rintro ⟨k, hk⟩
        exact ⟨k, Subtype.ext (by simpa using hk)⟩
      · rintro ⟨k, hk⟩
        exact ⟨k, by simpa using congrArg Subtype.val hk⟩
    rw [h1, MonoidHom.map_zpowers]
  have hNmap : NX ≤ (Subgroup.normalizer (X.subgroupOf M : Subgroup ↥M)).map
      (QuotientGroup.mk' (CFSG.pCore 2 ↥M)) := by
    have h := normalizer_map_mk'_le_of_coprime (p := 7)
      (A := X.subgroupOf M) hA h7O2M
    rwa [hAmap] at h
  have hrankMap : 2 ≤ CFSG.Open.pRank 3
      ((Subgroup.normalizer (X.subgroupOf M : Subgroup ↥M)).map
        (QuotientGroup.mk' (CFSG.pCore 2 ↥M))) :=
    le_trans hrankNX' (CFSG.SectionRank.pRank_mono (p := 3) (by norm_num) hNmap)
  let NM : Subgroup ↥M := Subgroup.normalizer (X.subgroupOf M : Set ↥M)
  let f : ↥NM →* Bar2 M :=
    (QuotientGroup.mk' (CFSG.pCore 2 ↥M)).comp NM.subtype
  have hrange : f.range = NM.map (QuotientGroup.mk' (CFSG.pCore 2 ↥M)) := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
  have hker : f.ker = (CFSG.pCore 2 ↥M).subgroupOf NM := by
    ext x
    show ((x : ↥M) : Bar2 M) = 1 ↔
      x ∈ (CFSG.pCore 2 ↥M).subgroupOf NM
    rw [QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
  have hP2 : IsPGroup 2 f.ker := by
    rw [hker]
    exact CFSG.pCore_isPGroup.comap_subtype
  have h3P : ¬ 3 ∣ Nat.card f.ker :=
    @CFSG.GroupTheory.not_dvd_card_of_isPGroup ↥(f.ker) _ _ 2 3 ⟨Nat.prime_two⟩ hP2
      Nat.prime_three (by norm_num)
  have hrankquot : CFSG.Open.pRank 3 (⊤ : Subgroup (↥NM ⧸ f.ker)) =
      CFSG.Open.pRank 3 (⊤ : Subgroup ↥NM) :=
    CFSG.SectionRank.pRank_quotient_eq (p := 3) (hp := ⟨Nat.prime_three⟩) f.ker h3P
  let eQ : (↥NM ⧸ f.ker) ≃* ↥(NM.map (QuotientGroup.mk' (CFSG.pCore 2 ↥M))) :=
    (QuotientGroup.quotientKerEquivRange f).trans (MulEquiv.subgroupCongr hrange)
  have hrankquot' : CFSG.Open.pRank 3 (⊤ : Subgroup (↥NM ⧸ f.ker)) =
      CFSG.Open.pRank 3 (⊤ : Subgroup
        ↥(NM.map (QuotientGroup.mk' (CFSG.pCore 2 ↥M)))) :=
    CFSG.SectionRank.pRank_top_eq_of_mulEquiv (p := 3) (by norm_num) eQ
  have hrankImage : CFSG.Open.pRank 3
      (NM.map (QuotientGroup.mk' (CFSG.pCore 2 ↥M))) =
      CFSG.Open.pRank 3 NM := by
    rw [CFSG.SectionRank.pRank_eq_pRank_top_subgroup
        (NM.map (QuotientGroup.mk' (CFSG.pCore 2 ↥M)))]
    rw [← hrankquot']
    rw [hrankquot]
    rw [← CFSG.SectionRank.pRank_eq_pRank_top_subgroup NM]
  have hrankNM : 2 ≤ CFSG.Open.pRank 3 NM := by
    rw [← hrankImage]
    exact hrankMap
  let Y : Subgroup G := M ⊓ Subgroup.normalizer (X : Set G)
  have hYsub : Y.subgroupOf M = NM := by
    ext y
    constructor
    · intro hy
      exact mem_normalizer_subgroupOf_of_mem_normalizer (Subgroup.mem_subgroupOf.mp hy).2
    · intro hy
      exact Subgroup.mem_subgroupOf.mpr
        ⟨y.2, mem_normalizer_of_mem_normalizer_subgroupOf hXM hy⟩
  have hYmap : (Y.subgroupOf M).map M.subtype = Y :=
    Subgroup.map_subgroupOf_eq_of_le (inf_le_left : Y ≤ M)
  have hrankY : CFSG.Open.pRank 3 Y = CFSG.Open.pRank 3 (Y.subgroupOf M) := by
    have h : CFSG.Open.pRank 3 ((Y.subgroupOf M).map M.subtype) =
        CFSG.Open.pRank 3 (Y.subgroupOf M) :=
      CFSG.HardMathSupport.Malle.OvergroupTransport.pRank_map_of_injective 3
        M.subtype_injective (Y.subgroupOf M)
    rwa [hYmap] at h
  have hrankYsub : 2 ≤ CFSG.Open.pRank 3 (Y.subgroupOf M) := by
    rwa [hYsub]
  show 1 < CFSG.Open.pRank 3 Y
  rw [hrankY]
  exact hrankYsub

theorem isStronglyPEmbedded_seven_of_is3D4
    (hRk : Inputs1719.K_3D4TwoThreeRank) (hS7 : Inputs1719.K_3D4TwoSylowSeven)
    (hN7 : Inputs1719.K_3D4TwoSevenNormalizer) (D : Data G) (hSg : UC6S846.SigmaStd D)
    (h76 : F07.R76 D) (h614 : UC6.R6_14 D) {L : Subgroup G} (hL : L ∈ calC D.M)
    (hN : (L.subgroupOf D.M).Normal) (h3D4 : Is3D4 (Bar2 L) 1) :
    CFSG.RankThree.PartOne.IsStronglyPEmbedded 7 D.M := by
  classical
  have hLM : L ≤ D.M := hL.1.le
  have hMN : D.M ≤ Subgroup.normalizer (L : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hLM).1 hN
  have hns : ¬ Group.IsSolvable ↥D.M := UC6S846.not_solvable_of_mem_calC hL
  have hAut : Inputs1719.K_3D4TwoAut := Inputs1719.k_3D4TwoAut_holds
  have hSm : Inputs1719.K_3D4TwoSmallRank := Inputs1719.k_3D4TwoSmallRank_holds
  obtain ⟨E, hEL, hEel, hEcard⟩ := exists_elemAbelian_fortyNine_le_of_is3D4 hS7 h3D4
  have hEM : E ≤ D.M := hEL.trans hLM
  have hEr : IsPGroup 7 E := hEel.isPGroup
  have hab : ∀ P : Sylow 7 (Bar2 L), IsMulCommutative (P : Subgroup (Bar2 L)) :=
    fun P => (hS7 (Bar2 L) h3D4 P).1.1
  have hOutcard : Nat.card (Outer (Bar2 L)) = 3 := (hAut (Bar2 L) h3D4).2.2
  have hout : ¬ 7 ∣ (L ⊔ F08.CentOverO2 D.M L).relIndex D.M := by
    have hdvd := relIndex_centOverO2_dvd_card_outer hLM hMN
    rw [hOutcard] at hdvd
    exact fun h => absurd (h.trans hdvd) (by norm_num)
  obtain ⟨R, hRsyl, hER⟩ :=
    exists_sylow_le_centralizer_of_isMulCommutative Nat.prime_seven (by norm_num)
      hLM hMN hab hout hEL hEr
  by_cases h7 : 7 ∈ D.sig
  · exact UC6S846.sp_of_mem_sig hSg hns h7
  · by_cases h3 : 3 ∈ D.sig
    · have hsp3 : CFSG.RankThree.PartOne.IsStronglyPEmbedded 3 D.M :=
        UC6S846.sp_of_mem_sig hSg hns h3
      have hOp : UC22.F10.OpRes 3 D.M = D.M :=
        UC6.opRes_eq_of_stronglyEmbedded_uc6 D.standing.simple D.standing.nonab
          Nat.prime_three hsp3
      have hC3 : 1 ≤ CFSG.Open.pRank 3 (F08.CentOverO2 D.M L) :=
        one_le_pRank_centOverO2_of_is3D4 hAut hRk hLM hMN h3D4 hOp (hSg.three_le 3 h3)
      have hCle := pRank_centOverO2_le_pRank_inf_centralizer hLM hMN Nat.prime_three
        (by norm_num) Nat.prime_seven (by norm_num) (by norm_num) hEL hEr
      have hEc : 0 < CFSG.Open.pRank 3
          (D.M ⊓ Subgroup.centralizer (E : Set G)) := by omega
      have hXN : ∀ X' : Subgroup G, X' ≤ E → Nat.card X' = 7 →
          1 < CFSG.Open.pRank 3 (D.M ⊓ Subgroup.normalizer (X' : Set G)) :=
        fun X' hX'E hX'card =>
          one_lt_pRank_normalizer_of_is3D4 hN7 hL hMN h3D4 hC3
            (hX'E.trans hEL) hX'card
      have hΓ : rankThreeGamma 1 7 E ≤ D.M :=
        h76 3 Nat.prime_three (by norm_num) hsp3 7 Nat.prime_seven E hEM hEel hEcard
          hEc hXN
      exact h614 (UC6S846.sig_subset_sig1 hSg hns) 7 Nat.prime_seven (by norm_num)
        h7 R hRsyl E hER hEel hEcard hΓ
    · obtain ⟨p, hp⟩ := hSg.nonempty
      have hp3 : p ≠ 3 := fun h => h3 (h ▸ hp)
      have hp7 : p ≠ 7 := fun h => h7 (h ▸ hp)
      have hpp : p.Prime := (D.sig_prime p hp).1
      have hp2 : p ≠ 2 := (D.sig_prime p hp).2
      have hsp : CFSG.RankThree.PartOne.IsStronglyPEmbedded p D.M :=
        UC6S846.sp_of_mem_sig hSg hns hp
      have hOp : UC22.F10.OpRes p D.M = D.M :=
        UC6.opRes_eq_of_stronglyEmbedded_uc6 D.standing.simple D.standing.nonab hpp hsp
      have hZ : Subgroup.center (Bar2 L) = ⊥ := (hAut (Bar2 L) h3D4).1
      have hcyc : IsCyclic (Outer (Bar2 L)) := (hAut (Bar2 L) h3D4).2.1
      have hbound := pRank_le_pRank_bar2_add_pRank_centOverO2 hLM hMN hZ hcyc
        hpp hp2 hOp
      have hbar := hSm (Bar2 L) h3D4 p hpp hp2 hp3 hp7
      have h3p : 3 ≤ CFSG.Open.pRank p D.M := hSg.three_le p hp
      have hC2 : 2 ≤ CFSG.Open.pRank p (F08.CentOverO2 D.M L) := by omega
      have hCle := pRank_centOverO2_le_pRank_inf_centralizer hLM hMN hpp hp2
        Nat.prime_seven (by norm_num) (Ne.symm hp7) hEL hEr
      have hEc : 0 < CFSG.Open.pRank p
          (D.M ⊓ Subgroup.centralizer (E : Set G)) := by omega
      have hXN : ∀ X' : Subgroup G, X' ≤ E → Nat.card X' = 7 →
          1 < CFSG.Open.pRank p (D.M ⊓ Subgroup.normalizer (X' : Set G)) := by
        intro X' hX'E hX'card
        have hcen : Subgroup.centralizer (E : Set G) ≤
            Subgroup.normalizer (X' : Set G) :=
          (Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr hX'E)).trans
            (Subgroup.centralizer_le_normalizer _)
        have hmono : CFSG.Open.pRank p (D.M ⊓ Subgroup.centralizer (E : Set G)) ≤
            CFSG.Open.pRank p (D.M ⊓ Subgroup.normalizer (X' : Set G)) :=
          CFSG.SectionRank.pRank_mono (p := p) hpp.one_lt (inf_le_inf le_rfl hcen)
        omega
      have hΓ : rankThreeGamma 1 7 E ≤ D.M :=
        h76 p hpp hp2 hsp 7 Nat.prime_seven E hEM hEel hEcard hEc hXN
      exact h614 (UC6S846.sig_subset_sig1 hSg hns) 7 Nat.prime_seven (by norm_num)
        h7 R hRsyl E hER hEel hEcard hΓ

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17
