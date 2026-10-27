module

import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Thirteen6aSp
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.SeventeenFiftyEightLemmasB
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.SeventeenFortyFiveConfig
import CFSG.LocalAnalysis.UniquenessCase.UC22S217JPair
public import CFSG.CGT.PushingUpLit.Transport
public import CFSG.LocalAnalysis.SeitzReduction.EPilotPosition
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Bridge13
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.Defs
public import CFSG.RankThree.PartTwo.Sec3.TwoThreeStructure

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.S136a

open Subgroup CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22

variable {G : Type} [Group G] [Finite G]

private theorem s136aConcl_layer_eq {D : Data G} {L K : Subgroup G} (hL : L ∈ calC D.M)
    (hK : K ∈ calC D.M)
    (hall : ∀ J : Subgroup (Bar2 D.M), CFSG.IsComponent J →
      J = barImage D.M L ∨ J = barImage D.M K) :
    CFSG.layer (Bar2 D.M) = barImage D.M L ⊔ barImage D.M K := by
  refine le_antisymm ?_ (sup_le (CFSG.LocalCores.component_le_layer (s13_barImage_isComponent hL))
    (CFSG.LocalCores.component_le_layer (s13_barImage_isComponent hK)))
  rw [CFSG.layer.eq_sSup]
  exact sSup_le fun J hJ => by
    rcases hall J hJ with h | h
    · rw [h]; exact le_sup_left
    · rw [h]; exact le_sup_right

private theorem s136aConcl_barImage_Lp {D : Data G} (hThin : ThinList13) (hS : Setting13 D)
    {p : ℕ} (hpp : p.Prime) {L K : Subgroup G} (hL : L ∈ calC D.M) (hK : K ∈ calC D.M)
    (hpL : p ∣ Nat.card ↥(barImage D.M L)) (hpK : p ∣ Nat.card ↥(barImage D.M K))
    (hlayer : CFSG.layer (Bar2 D.M) = barImage D.M L ⊔ barImage D.M K) :
    barImage D.M (F13.Lp D.M p) = barImage D.M L ⊔ barImage D.M K := by
  have hcompL : CFSG.IsComponent (barImage D.M L) := s13_barImage_isComponent hL
  have hcompK : CFSG.IsComponent (barImage D.M K) := s13_barImage_isComponent hK
  have hple : ∀ (J : Subgroup (Bar2 D.M)), IsSimpleGroup ↥J → CFSG.IsComponent J →
      p ∣ Nat.card ↥J → J ≤ CFSG.RankThree.PartOne.pElementSubgroup p (CFSG.layer (Bar2 D.M)) := by
    intro J hsimple hJ hpJ
    obtain ⟨z, hzJ, hzord⟩ := s13_exists_element_of_dvd J hpp hpJ
    have hz1 : z ≠ 1 := by
      rintro rfl
      rw [orderOf_one] at hzord
      exact hpp.ne_one hzord.symm
    have hgen : CFSG.RankThree.PartOne.pElementSubgroup p J = J :=
      CFSG.RankThree.PartOne.KFU.pElementSubgroup_eq_of_simple hsimple hzJ hzord hz1
    rw [← hgen]
    exact Subgroup.closure_mono fun x hx =>
      ⟨(CFSG.LocalCores.component_le_layer hJ) hx.1, hx.2⟩
  have hLle : barImage D.M L ≤
      CFSG.RankThree.PartOne.pElementSubgroup p (CFSG.layer (Bar2 D.M)) :=
    hple _ (s13_isSimple_barImage hThin D hS hL) hcompL hpL
  have hKle : barImage D.M K ≤
      CFSG.RankThree.PartOne.pElementSubgroup p (CFSG.layer (Bar2 D.M)) :=
    hple _ (s13_isSimple_barImage hThin D hS hK) hcompK hpK
  rw [s13_barImage_Lp D.M hpp]
  exact le_antisymm ((s13_Bar13_opp_le p (CFSG.layer (Bar2 D.M))).trans (le_of_eq hlayer))
    (sup_le hLle hKle)

private theorem s136aConcl_Lp_le_sup {D : Data G} (hThin : ThinList13) (hS : Setting13 D)
    {p : ℕ} (hp : p ∈ D.sig) {L K : Subgroup G} (hL : L ∈ calC D.M) (hK : K ∈ calC D.M)
    (hpL : p ∣ Nat.card ↥(barImage D.M L)) (hpK : p ∣ Nat.card ↥(barImage D.M K))
    (hlayer : CFSG.layer (Bar2 D.M) = barImage D.M L ⊔ barImage D.M K) :
    F13.Lp D.M p ≤ L ⊔ K := by
  have hpp : p.Prime := (D.sig_prime p hp).1
  have hp2 : p ≠ 2 := (D.sig_prime p hp).2
  have hLM : L ≤ D.M := s13_le_of_mem_calC hL
  have hKM : K ≤ D.M := s13_le_of_mem_calC hK
  have hNM : L ⊔ K ≤ D.M := sup_le hLM hKM
  have hNnorm : ((L ⊔ K).subgroupOf D.M).Normal := by
    rw [Subgroup.subgroupOf_sup hLM hKM]
    exact Subgroup.sup_normal (H := L.subgroupOf D.M) (K := K.subgroupOf D.M)
      (hH := hS.hyp131.normal L hL) (hK := hS.hyp131.normal K hK)
  have hbarN : barImage D.M (L ⊔ K) = barImage D.M L ⊔ barImage D.M K :=
    s13_barImage_sup hLM hKM
  have hbarLp : barImage D.M (F13.Lp D.M p) = barImage D.M L ⊔ barImage D.M K :=
    s136aConcl_barImage_Lp hThin hS hpp hL hK hpL hpK hlayer
  have hLpEq : F13.Lp D.M p =
      Subgroup.closure {x : G | x ∈ F13.OTwoEIn D.M ∧ ∃ k : ℕ, orderOf x = p ^ k} := rfl
  rw [hLpEq, Subgroup.closure_le]
  rintro x ⟨hxE, k, hk⟩
  have hxM : x ∈ D.M := Subgroup.map_subtype_le (H := D.M) (OTwoE ↥D.M) hxE
  have hxLp : x ∈ F13.Lp D.M p := hLpEq.symm ▸ Subgroup.subset_closure
    (⟨hxE, k, hk⟩ : x ∈ {y : G | y ∈ F13.OTwoEIn D.M ∧ ∃ k : ℕ, orderOf y = p ^ k})
  have hbar : (QuotientGroup.mk' (CFSG.pCore 2 ↥D.M)) ⟨x, hxM⟩ ∈ barImage D.M (L ⊔ K) := by
    rw [hbarN, ← hbarLp]
    exact Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr hxLp)
  exact s13_mem_of_barImage_of_pPart hNM hNnorm hpp hp2 hxM
    ⟨k, by rw [← hk]; exact pow_orderOf_eq_one x⟩ hbar

private theorem s136aConcl_hinf_le {D : Data G} {L K : Subgroup G} (hL : L ∈ calC D.M)
    (hK : K ∈ calC D.M) (hN : ((L ⊔ K).subgroupOf D.M).Normal)
    (hperf : CFSG.perfectResidual (Bar2 D.M) = CFSG.layer (Bar2 D.M))
    (hlayer : CFSG.layer (Bar2 D.M) = barImage D.M L ⊔ barImage D.M K)
    (hbar : barImage D.M (L ⊔ K) = barImage D.M L ⊔ barImage D.M K) :
    Hinf D.M ≤ L ⊔ K := by
  have hNM : L ⊔ K ≤ D.M := sup_le (s13_le_of_mem_calC hL) (s13_le_of_mem_calC hK)
  have hO2M : pCoreOf 2 D.M ≤ D.M := CFSG.LieType.BorelTits.pCoreOf_le 2 D.M
  have hbarHinf : barImage D.M (Hinf D.M) ≤ barImage D.M (L ⊔ K) := by
    have h1 : barImage D.M (Hinf D.M) ≤ CFSG.perfectResidual (Bar2 D.M) := by
      intro q hq
      rw [uc22p21c_mem_barImage] at hq
      obtain ⟨m, hm, rfl⟩ := hq
      have hmP : m ∈ CFSG.perfectResidual ↥D.M := by
        obtain ⟨m', hm', hmeq⟩ := uc22p21c_mem_Hinf.mp hm
        have h : m' = m := Subtype.ext hmeq
        rwa [h] at hm'
      have h2 : (uc22p21cPi D.M) m ∈ (CFSG.perfectResidual ↥D.M).map (uc22p21cPi D.M) :=
        Subgroup.mem_map_of_mem _ hmP
      rwa [uc22p21c_map_perfectResidual _ (uc22p21c_pi_surjective D.M)] at h2
    calc barImage D.M (Hinf D.M) ≤ CFSG.perfectResidual (Bar2 D.M) := h1
      _ = CFSG.layer (Bar2 D.M) := hperf
      _ = barImage D.M L ⊔ barImage D.M K := hlayer
      _ = barImage D.M (L ⊔ K) := hbar.symm
  have hsub : Hinf D.M ≤ (L ⊔ K) ⊔ pCoreOf 2 D.M := by
    intro x hx
    have hxM : x ∈ D.M := uc22p21c_Hinf_le D.M hx
    exact S17.mem_sup_pCoreOf_of_mem_barImage hxM
      (hbarHinf (Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr hx)))
  have hNnormM : D.M ≤ Subgroup.normalizer ((L ⊔ K : Subgroup G) : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hNM).mp hN
  have hO2norm : (L ⊔ K) ≤ Subgroup.normalizer (pCoreOf 2 D.M : Set G) :=
    hNM.trans (Subgroup.le_normalizer.trans
      (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 D.M))
  have hO2p : IsPGroup 2 (pCoreOf 2 D.M) :=
    (CFSG.pCore_isPGroup (G := ↥D.M)).map D.M.subtype
  have hrel : (L ⊔ K).relIndex ((L ⊔ K) ⊔ pCoreOf 2 D.M) ∣ Nat.card (pCoreOf 2 D.M) := by
    rw [← CFSG.GroupTheory.FT63ChII.relIndex_eq_relIndex_sup_of_le_normalizer hO2norm]
    exact Subgroup.relIndex_dvd_card _ _
  obtain ⟨k, hk⟩ := hO2p.exists_card_eq
  rw [hk] at hrel
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hrel
  exact Subgroup.le_of_commutator_eq_self_of_relIndex_eq_prime_pow (D := L ⊔ K)
    (C := (L ⊔ K) ⊔ pCoreOf 2 D.M) (H := Hinf D.M) (p := 2) (k := j) Nat.prime_two
    le_sup_left (sup_le (hNM.trans hNnormM) (hO2M.trans hNnormM)) hj hsub
    (uc22p21c_Hinf_perfect D.M)

private theorem s136aConcl_sup_le_hinf {D : Data G} {L K : Subgroup G} (hL : L ∈ calC D.M)
    (hK : K ∈ calC D.M) : L ⊔ K ≤ Hinf D.M :=
  sup_le (uc22p21c_le_Hinf (s13_le_of_mem_calC hL) hL.2.1)
    (uc22p21c_le_Hinf (s13_le_of_mem_calC hK) hK.2.1)

private theorem s136aConcl_sup_le_Lp {D : Data G} (hThin : ThinList13) (hS : Setting13 D)
    {p : ℕ} (hp : p ∈ D.sig) {L K : Subgroup G} (hL : L ∈ calC D.M) (hK : K ∈ calC D.M)
    (hpL : p ∣ Nat.card ↥(barImage D.M L)) (hpK : p ∣ Nat.card ↥(barImage D.M K)) :
    L ⊔ K ≤ F13.Lp D.M p := by
  have hns : s13_NormalSimple (Bar2 D.M) := s13_normalSimple hThin D hS
  have hp1754 : S17.Hyp1754 D p := s136a_hyp1754 hS hp
  exact sup_le
    (s13_le_of_mem_calC (S17.mem_calC_Lp_of_dvd_card_barImage D hp1754 hns hL hpL))
    (s13_le_of_mem_calC (S17.mem_calC_Lp_of_dvd_card_barImage D hp1754 hns hK hpK))

private theorem s136aConcl_equiv {D : Data G} {p : ℕ} {L K : Subgroup G}
    (hL' : L ∈ calC (F13.Lp D.M p)) (hK' : K ∈ calC (F13.Lp D.M p)) (hLK : L ≠ K)
    (hZ : Subgroup.center (Bar2 L) = ⊥) (hLp : F13.Lp D.M p = L ⊔ K) :
    Nonempty (Bar2 (F13.Lp D.M p) ≃* Bar2 L × Bar2 K) := by
  have hLM : L ≤ F13.Lp D.M p := s13_le_of_mem_calC hL'
  have hKM : K ≤ F13.Lp D.M p := s13_le_of_mem_calC hK'
  have hsup : barImage (F13.Lp D.M p) L ⊔ barImage (F13.Lp D.M p) K = ⊤ := by
    rw [← s13_barImage_sup hLM hKM, ← hLp, s13_barImage_self]
  have hcomm : ∀ a ∈ barImage (F13.Lp D.M p) L, ∀ b ∈ barImage (F13.Lp D.M p) K,
      a * b = b * a := uc22p22l_barImage_commute hL' hK' hLK
  have hdisj : barImage (F13.Lp D.M p) L ⊓ barImage (F13.Lp D.M p) K = ⊥ :=
    uc22s217j_barImage_inf_eq_bot hL' hK' hLK hZ
  obtain ⟨e₁⟩ := s13_bar_equiv hL'
  obtain ⟨e₂⟩ := s13_bar_equiv hK'
  exact ⟨(S17.bar2SquareEquiv hsup hcomm hdisj).trans (MulEquiv.prodCongr e₁.symm e₂.symm)⟩

theorem s136a_hinf_eq_and_equiv (hThin : ThinList13) {D : Data G} (hS : Setting13 D) {p : ℕ}
    (hp : p ∈ D.sig) {L K : Subgroup G} (hL : L ∈ calC D.M) (hK : K ∈ calC D.M)
    (hne : barImage D.M L ≠ barImage D.M K)
    (hall : ∀ J : Subgroup (Bar2 D.M), CFSG.IsComponent J →
      J = barImage D.M L ∨ J = barImage D.M K)
    (hpL : p ∣ Nat.card (barImage D.M L)) (hpK : p ∣ Nat.card (barImage D.M K)) :
    Hinf D.M = F13.Lp D.M p ∧ Nonempty (Bar2 (F13.Lp D.M p) ≃* Bar2 L × Bar2 K) := by
  have hLM : L ≤ D.M := s13_le_of_mem_calC hL
  have hKM : K ≤ D.M := s13_le_of_mem_calC hK
  have hLK : L ≠ K := fun h => hne (by rw [h])
  have hlayer : CFSG.layer (Bar2 D.M) = barImage D.M L ⊔ barImage D.M K :=
    s136aConcl_layer_eq hL hK hall
  have hbarN : barImage D.M (L ⊔ K) = barImage D.M L ⊔ barImage D.M K :=
    s13_barImage_sup hLM hKM
  have hNnorm : ((L ⊔ K).subgroupOf D.M).Normal := by
    rw [Subgroup.subgroupOf_sup hLM hKM]
    exact Subgroup.sup_normal (H := L.subgroupOf D.M) (K := K.subgroupOf D.M)
      (hH := hS.hyp131.normal L hL) (hK := hS.hyp131.normal K hK)
  have hLp_le : F13.Lp D.M p ≤ L ⊔ K :=
    s136aConcl_Lp_le_sup hThin hS hp hL hK hpL hpK hlayer
  have hsup_le : L ⊔ K ≤ F13.Lp D.M p :=
    s136aConcl_sup_le_Lp hThin hS hp hL hK hpL hpK
  have hLp : F13.Lp D.M p = L ⊔ K := le_antisymm hLp_le hsup_le
  have hHinf_le : Hinf D.M ≤ L ⊔ K :=
    s136aConcl_hinf_le hL hK hNnorm hS.hyp131.layer hlayer hbarN
  have hle_Hinf : L ⊔ K ≤ Hinf D.M := s136aConcl_sup_le_hinf hL hK
  have hHinf : Hinf D.M = F13.Lp D.M p := by
    rw [hLp]
    exact le_antisymm hHinf_le hle_Hinf
  have hZ : Subgroup.center (Bar2 L) = ⊥ := by
    have hsimple : IsSimpleGroup ↥(barImage D.M L) := s13_isSimple_barImage hThin D hS hL
    obtain ⟨x, y, hxy⟩ := s13_Layer13_component_not_commutative (s13_barImage_isComponent hL)
    have hZbar : Subgroup.center ↥(barImage D.M L) = ⊥ :=
      (IsSimpleGroup.eq_bot_or_eq_top_of_normal
        (Subgroup.center ↥(barImage D.M L))).resolve_right fun h =>
          hxy (Subgroup.mem_center_iff.mp (h ▸ Subgroup.mem_top x) y).symm
    obtain ⟨e⟩ := s13_bar_equiv hL
    rw [← Subgroup.map_eq_bot_iff_of_injective (Subgroup.center (Bar2 L))
      (f := (e : Bar2 L →* barImage D.M L)) e.injective, Subgroup.map_center_eq e, hZbar]
  have hL' : L ∈ calC (F13.Lp D.M p) :=
    S17.mem_calC_Lp_of_dvd_card_barImage D (s136a_hyp1754 hS hp)
      (s13_normalSimple hThin D hS) hL hpL
  have hK' : K ∈ calC (F13.Lp D.M p) :=
    S17.mem_calC_Lp_of_dvd_card_barImage D (s136a_hyp1754 hS hp)
      (s13_normalSimple hThin D hS) hK hpK
  exact ⟨hHinf, s136aConcl_equiv hL' hK' hLK hZ hLp⟩

theorem s136a_concl136 {D : Data G} {p : ℕ} {L K : Subgroup G} {n : ℕ} (hn : IsPowTwo n)
    (hpn : p ∣ 2 ^ n + 1)
    (hsh : (IsL2 (Bar2 L) n ∧ IsL2 (Bar2 K) n ∧ F13.Sp D.M p ≠ ⊥) ∨
      (IsU3 (Bar2 L) n ∧ IsL2 (Bar2 K) n ∧ F13.Sp D.M p = ⊥) ∨
      (IsL2 (Bar2 L) n ∧ IsU3 (Bar2 K) n ∧ F13.Sp D.M p = ⊥))
    (hE : Nonempty (Bar2 (F13.Lp D.M p) ≃* Bar2 L × Bar2 K)) : F13.Concl136 D p n := by
  obtain ⟨e⟩ := hE
  refine ⟨?_, hn, hpn⟩
  rcases hsh with ⟨hL2, hK2, hSp⟩ | ⟨hU, hK2, hSp⟩ | ⟨hL2, hU, hSp⟩
  · exact Or.inl ⟨⟨Bar2 L, Bar2 K, inferInstance, inferInstance, hL2, hK2, ⟨e⟩⟩, hSp⟩
  · exact Or.inr ⟨⟨Bar2 K, Bar2 L, inferInstance, inferInstance, hK2, hU,
      ⟨e.trans MulEquiv.prodComm⟩⟩, hSp⟩
  · exact Or.inr ⟨⟨Bar2 L, Bar2 K, inferInstance, inferInstance, hL2, hU, ⟨e⟩⟩, hSp⟩

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.S136a
