module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.A10EndPerfect
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.A10EndSuzuki
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.A10EndKey
import CFSG.Goldschmidt.Steps.G310Basic
import CFSG.Goldschmidt.Steps.LemmaXCore
import CFSG.LocalAnalysis.EvenBN.Tits.N.P6Sylow
import CFSG.GroupTheory.PCore.NormalPCoreOf
import CFSG.Quasithin.Vol2.Ch11SKFCompA
import CFSG.LocalAnalysis.RankThreeUC.AGL81S15K421LinSyl
import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimpleBInnerPClosure

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3

open CFSG.LocalAnalysis.UniquenessCase.UC22 (Data)

variable {G : Type} [Group G] [Finite G] {D : Data G}

namespace Ctx82E3.A10Frame

open CFSG.GH74.Uniqueness.SU.SU13.TA.L10

variable {c : Ctx82E3 D}

private theorem exists_mem_deg_three (F : A10Frame c) :
    ∃ e : G, e ∈ F.A ∧ F.deg (Subgroup.zpowers e) = 3 ∧ e ^ 3 = 1 := by
  classical
  have hpa : pa ∈ A10Perm.atilde := A10Perm.mem_atilde_iff.mpr ⟨1, 0, 0, by decide +kernel⟩
  rw [← F.map_A_phiA] at hpa
  obtain ⟨x, hx, hxe⟩ := Subgroup.mem_map.mp hpa
  have hxA : (x : G) ∈ F.A := Subgroup.mem_subgroupOf.mp hx
  have hxL : (x : G) ∈ c.L := F.P_le_L (F.A_le hxA)
  have hxe' : F.phiA ⟨(x : G), c.hyp81.1 hxL⟩ = pa := by
    rw [show (⟨(x : G), c.hyp81.1 hxL⟩ : ↥D.M) = x from Subtype.ext rfl]
    exact hxe
  have hdeg : F.deg (Subgroup.zpowers (x : G)) = 3 := by
    rw [F.deg_zpowers_eq hxL, hxe']
    rw [show pa = toP 1 0 0 by simp [toP], A10Perm.support_toP]
    decide +kernel
  have hne : (x : G) ≠ 1 := F.ne_one_of_deg_ne_zero hxL (by rw [hdeg]; norm_num)
  have hord : orderOf (x : G) = 3 := by
    have h := F.card_zpowers_of_mem_A hxA hne
    rwa [Nat.card_zpowers] at h
  exact ⟨(x : G), hxA, hdeg, by rw [← hord, pow_orderOf_eq_one]⟩

private theorem centralizer_ne_top [IsSimpleGroup G] {B : Subgroup G} (hB3 : Nat.card B = 3)
    (hnonab : ∃ a b : G, a * b ≠ b * a) :
    Subgroup.centralizer (B : Set G) ≠ ⊤ := by
  intro htop
  have hBc : B ≤ Subgroup.center G := Subgroup.centralizer_eq_top_iff_subset.mp htop
  have hbot := CFSG.GorensteinWalter.Helpers.center_eq_bot_of_noncommutative hnonab
  have hBb : B = ⊥ := le_bot_iff.mp (hbot ▸ hBc)
  rw [hBb, Subgroup.card_bot] at hB3
  omega

private theorem componentLayerOf_le_normalizer_component {H K : Subgroup G}
    (hK : CFSG.GorensteinWalter.IsComponentOf K H) :
    CFSG.GorensteinWalter.componentLayerOf H ≤ Subgroup.normalizer (K : Set G) := by
  rw [CFSG.GorensteinWalter.componentLayerOf]
  refine sSup_le fun L hL => ?_
  by_cases hLK : L = K
  · rw [hLK]
    exact Subgroup.le_normalizer
  · rw [Subgroup.le_normalizer_iff]
    intro x hx y hy
    have hcomm : x * y = y * x :=
      CFSG.Quasithin.Vol2.Ch11.SecS.KF.mul_comm_of_ne hL hK hLK hx hy
    rw [show x * y * x⁻¹ = y by rw [hcomm]; group]
    exact hy

private theorem not_le_center_of_isSylowOf {H K T E : Subgroup G}
    (hTK : T ≤ K) (hTsyl : CFSG.ABGLocalTools.IsSylowOf 2 T K)
    (h2K : 2 ∣ Nat.card K) (hKE : K ≤ E)
    (hEK : E ≤ Subgroup.normalizer (K : Set G))
    (hEH : E ≤ H) (hHE : H ≤ Subgroup.normalizer (E : Set G))
    (hO : CFSG.Open.pCoreOf 2 H = ⊥) :
    ¬ T ≤ (Subgroup.center ↥K).map K.subtype := by
  classical
  intro hTZ
  have hcentKT : K ≤ Subgroup.centralizer (T : Set G) := by
    intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro t ht
    obtain ⟨z, hz, hzt⟩ := Subgroup.mem_map.mp (hTZ ht)
    have hcomm : (⟨x, hx⟩ : ↥K) * z = z * ⟨x, hx⟩ := Subgroup.mem_center_iff.mp hz ⟨x, hx⟩
    have hval : x * (z : G) = (z : G) * x := congrArg Subtype.val hcomm
    have hzt' : (z : G) = t := hzt
    rw [hzt'] at hval
    exact hval.symm
  have hKnormT : K ≤ Subgroup.normalizer (T : Set G) :=
    hcentKT.trans (Subgroup.centralizer_le_normalizer (T : Set G))
  have hTnorm : (T.subgroupOf K).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hTK).mpr hKnormT
  have hTleO2K : T ≤ CFSG.Open.pCoreOf 2 K := by
    have hle : T.subgroupOf K ≤ CFSG.pCore 2 ↥K :=
      le_sSup ⟨hTnorm, hTsyl.isPGroup.comap_subtype⟩
    have hmap := Subgroup.map_mono (f := K.subtype) hle
    rw [Subgroup.map_subgroupOf_eq_of_le hTK] at hmap
    exact hmap
  have hchain : T ≤ CFSG.Open.pCoreOf 2 H :=
    hTleO2K.trans ((CFSG.GroupTheory.pCoreOf_le_pCoreOf_of_le_normalizer 2 hKE hEK).trans
      (CFSG.GroupTheory.pCoreOf_le_pCoreOf_of_le_normalizer 2 hEH hHE))
  rw [hO] at hchain
  have hTne : T ≠ ⊥ := by
    obtain ⟨Q, hQ⟩ := hTsyl.exists_sylow_eq_subgroupOf
    have hQne : (Q : Subgroup ↥K) ≠ ⊥ := Q.ne_bot_of_dvd_card h2K
    intro hbot
    exact hQne (by rw [hQ, hbot]; simp)
  exact hTne (le_bot_iff.mp hchain)

private theorem componentLayerOf_centralizer_le_of_deg_eq_three (F : A10Frame c)
    (hF : A10Facts F) {B : Subgroup G} (hBA : B ≤ F.A) (hB3 : Nat.card B = 3)
    (hdeg : F.deg B = 3) :
    CFSG.GorensteinWalter.componentLayerOf (Subgroup.centralizer (B : Set G)) ≤ D.M := by
  have hcomp : CFSG.GorensteinWalter.componentLayerOf (Subgroup.centralizer (B : Set G)) ≤
      Subgroup.centralizer (B : Set G) := sSup_le fun _ hK => hK.1
  obtain ⟨b, -, hBz⟩ :=
    CFSG.LocalAnalysis.RankThreeUC.S15.K421SylProof.exists_zpowers_of_card_three hB3
  have hbA : b ∈ F.A := hBA (by rw [hBz]; exact Subgroup.mem_zpowers b)
  have hHle : Subgroup.centralizer (B : Set G) ≤ Subgroup.centralizer ({b} : Set G) := by
    intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    rw [Set.mem_singleton_iff] at hy
    rw [hy]
    exact Subgroup.mem_centralizer_iff.mp hx b (by rw [hBz]; exact Subgroup.mem_zpowers b)
  refine hcomp.trans (hHle.trans (F.centralizer_le_M_of_deg_three hF hbA ?_))
  rwa [hBz] at hdeg

private theorem exists_isSylowOf_componentLayerOf_le_M
    (F : A10Frame c) (hF : A10Facts F)
    (hC : ∀ B ≤ F.A, Nat.card B = 3 →
      Subgroup.centralizer (B : Set G) ≤ (Subgroup.centralizer (B : Set G) ⊓ D.M) ⊔
        CFSG.Open.relPPrimeCore 3 (Subgroup.centralizer (B : Set G)))
    {H : Subgroup G} (hAH : F.A ≤ H)
    (hE3 : ¬ 3 ∣ Nat.card (CFSG.GorensteinWalter.componentLayerOf H)) :
    ∃ R : Subgroup G, CFSG.ABGLocalTools.IsSylowOf 2 R
        (CFSG.GorensteinWalter.componentLayerOf H) ∧ R ≤ D.M ∧
      F.A ≤ Subgroup.normalizer (R : Set G) := by
  have hHE : H ≤ Subgroup.normalizer
      (CFSG.GorensteinWalter.componentLayerOf H : Set G) :=
    CFSG.GorensteinWalter.le_normalizer_of_isNormalIn
      (CFSG.GorensteinWalter.componentLayerOf_isNormalIn H)
  obtain ⟨R, hRsyl, -, hAR⟩ := CFSG.Goldschmidt.G310.exists_invariant_sylow_containing
    (r := 3) (q := 2) Nat.prime_three Nat.prime_two
    (CFSG.Open.IsElemAbelian.isPGroup F.elemAbelian) hE3 (hAH.trans hHE) bot_le
    (IsPGroup.of_card (n := 0) (by simp))
    (by intro x _; rw [Subgroup.mem_normalizer_iff]; intro y; simp)
  have hRsyl' : CFSG.ABGLocalTools.IsSylowOf 2 R
      (CFSG.GorensteinWalter.componentLayerOf H) :=
    CFSG.LocalAnalysis.EvenBN.Tits.N.P6.isSylowOf_of_fusionIsSylowIn hRsyl
  exact ⟨R, hRsyl', F.le_M_of_isPGroup_two hF hC hRsyl'.isPGroup hAR, hAR⟩

private theorem component_le_M_of_isSylowOf
    (hKPSz : CFSG.RankThree.PartTwo.KFacts.KPSz)
    (hKP : CFSG.Open.IsKProper G) {H E R K : Subgroup G} {e : G}
    (hEH : E ≤ H) (hHE : H ≤ Subgroup.normalizer (E : Set G))
    (hKE : K ≤ E) (hEnormK : E ≤ Subgroup.normalizer (K : Set G))
    (hRsyl : CFSG.ABGLocalTools.IsSylowOf 2 R E) (hRM : R ≤ D.M)
    (h2K : 2 ∣ Nat.card K) (hK3 : ¬ 3 ∣ Nat.card K)
    (hK : CFSG.GorensteinWalter.IsComponentOf K H) (hHne : H ≠ ⊤)
    (heH : e ∈ H) (hepow : e ^ 3 = 1) (heM : Subgroup.centralizer ({e} : Set G) ≤ D.M)
    (hO : CFSG.Open.pCoreOf 2 H = ⊥) :
    K ≤ D.M := by
  have hTsyl : CFSG.ABGLocalTools.IsSylowOf 2 (R ⊓ K) K :=
    CFSG.ABGLocalTools.IsSylowOf.inf_of_le_normalizer hRsyl hKE hEnormK
  have hTZ : ¬ R ⊓ K ≤ (Subgroup.center ↥K).map K.subtype :=
    not_le_center_of_isSylowOf inf_le_right hTsyl h2K hKE hEnormK hEH hHE hO
  by_cases heK : e ∈ Subgroup.normalizer (K : Set G)
  · exact A10Gen.le_of_suzuki_component hKPSz hKP hHne hK hK3 hepow heK hTsyl
      (inf_le_left.trans hRM) (inf_le_right.trans heM)
  · refine A10Gen.le_of_component_conj_ne hK heH hepow ?_ heM inf_le_right
      (inf_le_left.trans hRM) hTZ
    intro heq
    exact heK (Subgroup.mem_normalizer_iff_map_conj_eq.mpr heq)

private theorem componentLayerOf_centralizer_le_of_deg_ne_three
    (F : A10Frame c) (hF : A10Facts F)
    (hC : ∀ B ≤ F.A, Nat.card B = 3 →
      Subgroup.centralizer (B : Set G) ≤ (Subgroup.centralizer (B : Set G) ⊓ D.M) ⊔
        CFSG.Open.relPPrimeCore 3 (Subgroup.centralizer (B : Set G)))
    (hKPSz : CFSG.RankThree.PartTwo.KFacts.KPSz) {B : Subgroup G} (hBA : B ≤ F.A)
    (hB3 : Nat.card B = 3) (hdeg : F.deg B ≠ 3)
    (hO : CFSG.Open.pCoreOf 2 (Subgroup.centralizer (B : Set G)) = ⊥) :
    CFSG.GorensteinWalter.componentLayerOf (Subgroup.centralizer (B : Set G)) ≤ D.M := by
  classical
  haveI : IsSimpleGroup G := D.standing.simple
  let H : Subgroup G := Subgroup.centralizer (B : Set G)
  let E : Subgroup G := CFSG.GorensteinWalter.componentLayerOf H
  change CFSG.GorensteinWalter.componentLayerOf H ≤ D.M
  have hEH : E ≤ H := (CFSG.GorensteinWalter.componentLayerOf_isNormalIn H).1
  have hHE : H ≤ Subgroup.normalizer (E : Set G) :=
    CFSG.GorensteinWalter.le_normalizer_of_isNormalIn
      (CFSG.GorensteinWalter.componentLayerOf_isNormalIn H)
  have hcop3 : Nat.Coprime 3 (Nat.card (CFSG.Open.relPPrimeCore 3 H)) :=
    CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimple.coprime_card_relPPrimeCore
      Nat.prime_three H
  have hAA : F.A ≤ Subgroup.centralizer (F.A : Set G) :=
    Subgroup.le_centralizer_iff_isMulCommutative.mpr F.elemAbelian.1
  have hAH : F.A ≤ H := Subgroup.le_centralizer_iff.mpr (hBA.trans hAA)
  obtain ⟨e, heA, he3, hepow⟩ := exists_mem_deg_three F
  have hErel : E ≤ CFSG.Open.relPPrimeCore 3 H := by
    change CFSG.GorensteinWalter.componentLayerOf H ≤ CFSG.Open.relPPrimeCore 3 H
    rw [CFSG.GorensteinWalter.componentLayerOf]
    exact sSup_le fun K hK => F.le_relPPrimeCore_of_perfect_of_deg_ne_three hBA hB3 hdeg
      (hC B hBA hB3) hK.1
      (Subgroup.isPerfect_iff.mp (Group.isPerfect_def.mpr hK.2.2.2.1))
  have hE3 : ¬ 3 ∣ Nat.card E :=
    Nat.prime_three.coprime_iff_not_dvd.mp
      (Nat.Coprime.coprime_dvd_right (Subgroup.card_dvd_of_le hErel) hcop3)
  obtain ⟨R, hRsyl, hRM, -⟩ :=
    exists_isSylowOf_componentLayerOf_le_M F hF hC hAH hE3
  rw [CFSG.GorensteinWalter.componentLayerOf]
  refine sSup_le fun K hK => ?_
  have hK3 : ¬ 3 ∣ Nat.card K := fun h => hE3 (h.trans (Subgroup.card_dvd_of_le (le_sSup hK)))
  refine component_le_M_of_isSylowOf hKPSz D.standing.kProper hEH hHE (le_sSup hK)
    (componentLayerOf_le_normalizer_component hK) hRsyl hRM ?_ hK3 hK
    (centralizer_ne_top hB3 D.standing.nonab) (hAH heA) hepow
    (F.centralizer_le_M_of_deg_three hF heA he3) hO
  exact CFSG.Goldschmidt.LemmaX.two_dvd_card_of_isQuasisimple
    (⟨hK.2.2.2.1, hK.2.2.2.2⟩ : CFSG.Open.IsQuasisimple ↥K)

theorem componentLayerOf_centralizer_le
    (F : A10Frame c) (hF : A10Facts F)
    (hC : ∀ B ≤ F.A, Nat.card B = 3 →
      Subgroup.centralizer (B : Set G) ≤ (Subgroup.centralizer (B : Set G) ⊓ D.M) ⊔
        CFSG.Open.relPPrimeCore 3 (Subgroup.centralizer (B : Set G)))
    (hKPSz : CFSG.RankThree.PartTwo.KFacts.KPSz) {B : Subgroup G} (hBA : B ≤ F.A)
    (hB3 : Nat.card B = 3)
    (hO : CFSG.Open.pCoreOf 2 (Subgroup.centralizer (B : Set G)) = ⊥) :
    CFSG.GorensteinWalter.componentLayerOf (Subgroup.centralizer (B : Set G)) ≤ D.M := by
  by_cases hdeg : F.deg B = 3
  · exact componentLayerOf_centralizer_le_of_deg_eq_three F hF hBA hB3 hdeg
  · exact componentLayerOf_centralizer_le_of_deg_ne_three F hF hC hKPSz hBA hB3 hdeg hO

end Ctx82E3.A10Frame

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3
