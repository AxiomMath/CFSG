module

public import CFSG.OddTranspositions.PartThree.Eleven.OneThree.MainCase.Quotient
public import CFSG.OddTranspositions.PartThree.Eleven.OneThree.MainCase.ConjInv
import CFSG.OddTranspositions.PartThree.Eleven.OneThree.MainCase.TwoPoint
import CFSG.OddTranspositions.PartThree.Eleven.OneThree.MainCase.PCore
import CFSG.OddTranspositions.PartThree.Eleven.OneThree.MainCase.Center
import CFSG.OddTranspositions.PartFour.SeventeenTwo
import CFSG.LocalAnalysis.ComponentClassification.Foote47Lift
import CFSG.GroupTheory.PCore.TwoOddCoreSolvable
import CFSG.GroupTheory.ABGLocalTools.PStabilityRelative
import CFSG.Mathlib.GroupTheory.MulConjMemNormal

public section

namespace CFSG.OddTranspositions.PartThree.ElevenThree

open CFSG.Timmesfeld.Bridge CFSG.Timmesfeld.Bridge.Asc72 CFSG.Timmesfeld.Connectivity
open CFSG.OddTranspositions.QZ CFSG.OddTranspositions.PartFour

variable {G : Type} [Group G] [Finite G] {D : Set G} {hC : HypothesisC D}

theorem odd_card_oddLineImage (ε : Set G) : Odd (Nat.card (oddLineImage hC ε)) := by
  have hR : Odd (Nat.card (rBlock D ε)) := by
    rw [rBlock, Subgroup.card_map_of_injective (fun x y h => Subtype.ext h)]
    exact CFSG.ABGLocalTools.odd_card_oddCore
  have h1 : Nat.card (oddLineImage hC ε) ∣
      Nat.card ↥((rBlock D ε ⊓ lineGroup D hC.alpha ε).subgroupOf (Halpha D hC.alpha)) :=
    Subgroup.card_map_dvd ((rBlock D ε ⊓ lineGroup D hC.alpha ε).subgroupOf
      (Halpha D hC.alpha)) (QuotientGroup.mk' (CFSG.solvableRadical (Halpha D hC.alpha)))
  have h2 : Nat.card ↥((rBlock D ε ⊓ lineGroup D hC.alpha ε).subgroupOf (Halpha D hC.alpha)) ∣
      Nat.card ↥(rBlock D ε ⊓ lineGroup D hC.alpha ε) := by
    simpa only [Subgroup.comap_subtype] using
      Subgroup.card_comap_dvd_of_injective (rBlock D ε ⊓ lineGroup D hC.alpha ε)
        (Halpha D hC.alpha).subtype (fun x y h => Subtype.ext h)
  have h3 : Nat.card ↥(rBlock D ε ⊓ lineGroup D hC.alpha ε) ∣ Nat.card ↥(rBlock D ε) :=
    Subgroup.card_dvd_of_le inf_le_left
  exact Odd.of_dvd_nat hR (h1.trans (h2.trans h3))

omit [Finite G] in
theorem commute_mk_of_mem_oddLineImage {ε : Set G} {c : Halpha D hC.alpha} (hc : (c : G) ∈ ε) :
    ∀ n ∈ oddLineImage hC ε,
      Commute (QuotientGroup.mk' (CFSG.solvableRadical (Halpha D hC.alpha)) c) n := by
  intro n hn
  obtain ⟨u, hu, hnu⟩ := Subgroup.mem_map.mp hn
  rw [Subgroup.mem_subgroupOf] at hu
  obtain ⟨o, ho, huo⟩ := Subgroup.mem_map.mp hu.1
  have huH : (u : G) ∈ Halpha D ε := huo ▸ o.2
  have hcommG : Commute (c : G) (u : G) :=
    Subgroup.mem_centralizer_iff.mp (Halpha_le_centralizer D ε huH) (c : G) hc
  rw [← hnu]
  exact (Commute.map (Subtype.ext hcommG.eq) (QuotientGroup.mk' _))

namespace MainHyp

private theorem cimg_mem_oddCore_map {X : Subgroup G} {y : G}
    (hy : y ∈ Subgroup.normalizer (X : Set G)) {o : X} (ho : o ∈ CFSG.oddCore X) :
    y * (o : G) * y⁻¹ ∈ Subgroup.map X.subtype (CFSG.oddCore X) := by
  classical
  have hmap : Subgroup.map (↑(MulAut.conj y) : G →* G) X = X :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp hy
  let e : X ≃* X := (MulEquiv.subgroupMap (MulAut.conj y) X).trans (MulEquiv.subgroupCongr hmap)
  have hcoe : ∀ b : X, ((e b : X) : G) = y * (b : G) * y⁻¹ := by
    intro b
    rw [show e b = (MulEquiv.subgroupCongr hmap)
      (MulEquiv.subgroupMap (MulAut.conj y) X b) from rfl,
      MulEquiv.subgroupCongr_apply, MulEquiv.coe_subgroupMap_apply, MulAut.conj_apply]
  have hodd : Subgroup.map e.toMonoidHom (CFSG.oddCore X) = CFSG.oddCore X :=
    CFSG.ABGLocalTools.oddCore_map_mulEquiv e
  have hmem : e (⟨o, ho⟩ : CFSG.oddCore X) ∈ CFSG.oddCore X := by
    have h := Subgroup.mem_map_of_mem e.toMonoidHom ho
    rwa [hodd] at h
  exact ⟨e (⟨o, ho⟩ : CFSG.oddCore X), hmem, hcoe (⟨o, ho⟩ : CFSG.oddCore X)⟩

private theorem conj_mem_rBlock_inf_lineGroup {ε : Set G} (hε : ε ∈ Dalpha D hC.alpha)
    {c y' : Halpha D hC.alpha} (hc : (c : G) ∈ ε) (hcomm : y' * c * y'⁻¹ = c)
    {u : Halpha D hC.alpha} (hu : (u : G) ∈ rBlock D ε ⊓ lineGroup D hC.alpha ε) :
    ((y' * u * y'⁻¹ : Halpha D hC.alpha) : G) ∈ rBlock D ε ⊓ lineGroup D hC.alpha ε := by
  obtain ⟨huR, huL⟩ := hu
  have hc' : (y' : G) * (c : G) * (y' : G)⁻¹ = (c : G) :=
    congrArg Subtype.val hcomm
  have hcyε : cimg (y' : G) ε = ε := by
    have hmem : (c : G) ∈ cimg (y' : G) ε := ⟨(c : G), hc, hc'⟩
    have hclass : cimg (y' : G) ε ∈ blockClass hC.alpha := cimg_mem_blockClass_iff.mpr hε.1
    exact eq_of_mem_of_mem_blockClass hC.isBlock_alpha hclass hε.1 ⟨(c : G), hmem, hc⟩
  have hDε : cimg (y' : G) (DalphaStar D ε) = DalphaStar D ε := by
    rw [← DalphaStar_cimg hC.setup.normal (y' : G) ε, hcyε]
  have hy'NHε : (y' : G) ∈ Subgroup.normalizer (Halpha D ε : Set G) := by
    have hy'ε : (y' : G) ∈ Subgroup.normalizer ε := by
      rw [Subgroup.mem_normalizer_iff_conj_image_eq]
      exact hcyε
    exact normalizer_le_normalizer_Halpha hC.setup.normal hy'ε
  have hDα : cimg (y' : G) (DalphaStar D hC.alpha) = DalphaStar D hC.alpha :=
    cimg_eq_self_of_mem_normalizer (Halpha_le_normalizer hC.setup.normal y'.2)
  have hInt : cimg (y' : G) (DalphaStar D hC.alpha ∩ DalphaStar D ε) =
      DalphaStar D hC.alpha ∩ DalphaStar D ε := by
    rw [show cimg (y' : G) (DalphaStar D hC.alpha ∩ DalphaStar D ε) =
        cimg (y' : G) (DalphaStar D hC.alpha) ∩ cimg (y' : G) (DalphaStar D ε)
        from Set.image_inter conj_injective, hDα, hDε]
  have hu'R : (y' : G) * (u : G) * (y' : G)⁻¹ ∈ rBlock D ε := by
    obtain ⟨o, ho, hoo⟩ := Subgroup.mem_map.mp huR
    have hoo' : (o : G) = (u : G) := hoo
    have h := cimg_mem_oddCore_map hy'NHε ho
    rwa [show (y' : G) * (o : G) * (y' : G)⁻¹ = (y' : G) * (u : G) * (y' : G)⁻¹
      from by rw [hoo']] at h
  have hu'L : (y' : G) * (u : G) * (y' : G)⁻¹ ∈ lineGroup D hC.alpha ε := by
    have hLL : Subgroup.map (MulAut.conj (y' : G)).toMonoidHom (lineGroup D hC.alpha ε) =
        lineGroup D hC.alpha ε := by
      show (Subgroup.closure (DalphaStar D hC.alpha ∩ DalphaStar D ε)).map
        (MulAut.conj (y' : G)).toMonoidHom =
        Subgroup.closure (DalphaStar D hC.alpha ∩ DalphaStar D ε)
      rw [← closure_cimg, hInt]
    have h := Subgroup.mem_map_of_mem (MulAut.conj (y' : G)).toMonoidHom huL
    rw [hLL] at h
    simpa [MulAut.conj_apply] using h
  exact ⟨by simpa using hu'R, by simpa using hu'L⟩


private theorem exists_commuting_preimage (h : MainHyp hC) {ε : Set G}
    (hε : ε ∈ Dalpha D hC.alpha) {c : Halpha D hC.alpha} (hc : (c : G) ∈ ε)
    {y0 : Halpha D hC.alpha}
    (hcomm : Commute (QuotientGroup.mk' (CFSG.solvableRadical (Halpha D hC.alpha)) y0)
      (QuotientGroup.mk' (CFSG.solvableRadical (Halpha D hC.alpha)) c)) :
    ∃ y' : Halpha D hC.alpha,
      QuotientGroup.mk' (CFSG.solvableRadical (Halpha D hC.alpha)) y' =
        QuotientGroup.mk' (CFSG.solvableRadical (Halpha D hC.alpha)) y0 ∧
      y' * c * y'⁻¹ = c := by
  have hm : y0 * c * y0⁻¹ * c⁻¹ ∈ CFSG.solvableRadical (Halpha D hC.alpha) := by
    rw [← QuotientGroup.eq_one_iff (N := CFSG.solvableRadical (Halpha D hC.alpha))]
    change QuotientGroup.mk' (CFSG.solvableRadical (Halpha D hC.alpha))
      (y0 * c * y0⁻¹ * c⁻¹) = 1
    rw [map_mul, map_mul, map_mul, map_inv, map_inv, hcomm.eq]
    group
  obtain ⟨l, hlK, hleq⟩ := h.exists_twoOddCore_conj_eq_of_mem_solvableRadical
    (x := (c : G)) (y := (y0 : G) * (c : G) * (y0 : G)⁻¹)
    (subset_DalphaStar hε hc)
    (by simpa only [Subgroup.coe_mul] using hC.setup.normal (y0 : G) (c : G) (hε.2.1 hc))
    hm (by simp only [Subgroup.coe_mul, Subgroup.coe_inv]; group)
  have hlM : l ∈ CFSG.solvableRadical (Halpha D hC.alpha) :=
    CFSG.GroupTheory.comap_oddCore_pCore_two_le_solvableRadical _ hlK
  have hl1 : QuotientGroup.mk' (CFSG.solvableRadical (Halpha D hC.alpha)) l = 1 :=
    (QuotientGroup.eq_one_iff l).mpr hlM
  refine ⟨l⁻¹ * y0, ?_, ?_⟩
  · rw [map_mul, map_inv, hl1, inv_one, one_mul]
  · have h1 : l * c * l⁻¹ = y0 * c * y0⁻¹ := Subtype.ext hleq
    calc l⁻¹ * y0 * c * (l⁻¹ * y0)⁻¹ = l⁻¹ * (y0 * c * y0⁻¹) * l := by group
      _ = l⁻¹ * (l * c * l⁻¹) * l := by rw [← h1]
      _ = c := by group

private theorem cimg_kBlock_mem_Dalpha (h : MainHyp hC) {δ ε : Set G}
    (hδ : δ ∈ Dalpha D hC.alpha) (hε : ε ∈ Dalpha D hC.alpha) (hεδ : ε ∈ Dalpha D δ)
    {k a : G} (hk : k ∈ kBlock D ε) (ha : a ∈ δ)
    (hnc : ¬ Commute a (k * a * k⁻¹)) : cimg k δ ∈ Dalpha D hC.alpha := by
  obtain ⟨g, hg⟩ := mem_blockClass_iff.mp hε.1
  have hαε : (hC.conj g).alpha = ε := (HypothesisC.conj_alpha hC g).trans hg.symm
  have hδε : δ ∈ Dalpha D ε := mem_Dalpha_symm hεδ hδ.2.1
  have hδ' : δ ∈ Dalpha D (hC.conj g).alpha := by rw [hαε]; exact hδε
  have hθ' : hC.alpha ∈ Dalpha D (hC.conj g).alpha := by
    rw [hαε]
    exact mem_Dalpha_symm hε hC.isBlock_alpha.subset
  have hθδ' : hC.alpha ∈ Dalpha D δ := mem_Dalpha_symm hδ hC.isBlock_alpha.subset
  have hθline : hC.alpha ∉ blockLine D (hC.conj g).alpha δ := by
    rw [blockLine_eq_pair (h := h.conj g) hδ', hαε]
    intro hmem
    rcases hmem with hmem | hmem
    · exact hε.2.2.1 hmem.symm
    · exact hδ.2.2.1 hmem.symm
  have hk' : k ∈ kBlock D (hC.conj g).alpha := by rw [hαε]; exact hk
  obtain ⟨kk, hkK, hkke⟩ := Subgroup.mem_map.mp hk'
  have hkke' : (kk : G) = k := hkke
  have hnc' : ¬ Commute a ((kk : G) * a * (kk : G)⁻¹) := by rw [hkke']; exact hnc
  have hres := cimg_twoOddCore_mem_Dalpha (h := h.conj g) hδ' hθ' hθδ' hθline ha hkK hnc'
  rwa [hkke'] at hres

private theorem eq_of_commute_kBlock (h : MainHyp hC) {δ ε : Set G}
    (hδ : δ ∈ Dalpha D hC.alpha) (hε : ε ∈ Dalpha D hC.alpha) (hεδ : ε ∈ Dalpha D δ)
    {k a : G} (hk : k ∈ kBlock D ε) (ha : a ∈ δ)
    (hcomm : Commute a (k * a * k⁻¹)) : k * a * k⁻¹ = a := by
  obtain ⟨g, hg⟩ := mem_blockClass_iff.mp hε.1
  have hαε : (hC.conj g).alpha = ε := (HypothesisC.conj_alpha hC g).trans hg.symm
  have h' : MainHyp (hC.conj g) := h.conj g
  have hδε : δ ∈ Dalpha D ε := mem_Dalpha_symm hεδ hδ.2.1
  have hδ' : δ ∈ Dalpha D (hC.conj g).alpha := by rw [hαε]; exact hδε
  have hk' : k ∈ kBlock D (hC.conj g).alpha := by rw [hαε]; exact hk
  obtain ⟨kk, hkK, hkke⟩ := Subgroup.mem_map.mp hk'
  have hkke' : (kk : G) = k := hkke
  have haStar : a ∈ DalphaStar D (hC.conj g).alpha := subset_DalphaStar hδ' ha
  have haD : a ∈ D := hδ.2.1 ha
  have ha2 : a * a = 1 := hC.setup.oddT.mul_self_eq_one haD
  have hbD : k * a * k⁻¹ ∈ D := hC.setup.normal k a haD
  let aH : Halpha D (hC.conj g).alpha := ⟨a, Subgroup.subset_closure haStar⟩
  let bH : Halpha D (hC.conj g).alpha := kk * aH * kk⁻¹
  have hbHe : (bH : G) = k * a * k⁻¹ := by
    simp only [bH, aH, Subgroup.coe_mul, Subgroup.coe_inv, hkke']
  have hA2 : aH * aH = 1 := Subtype.ext (by simpa only [Subgroup.coe_mul, Subgroup.coe_one, aH]
    using ha2)
  have hqK : aH * bH ∈ EightOne.twoOddCore (Halpha D (hC.conj g).alpha) :=
    CFSG.GroupTheory.mul_mul_conj_mem_of_normal hkK hA2
  have hcommG : Commute (aH : G) (bH : G) := by
    rw [hbHe]
    exact hcomm
  have hqQ : aH * bH ∈ CFSG.pCore 2 (Halpha D (hC.conj g).alpha) :=
    mul_mem_pCore_of_mul_mem_twoOddCore (hC := hC.conj g)
      (by simpa [aH] using haD) (by simpa [bH, hbHe] using hbD) hcommG hqK
  have hwq : k * a * k⁻¹ = ((aH * bH : Halpha D (hC.conj g).alpha) : G) * a := by
    rw [Subgroup.coe_mul, hbHe, show (aH : G) = a from rfl]
    exact (show a * (k * a * k⁻¹) * a = k * a * k⁻¹ from by
      calc a * (k * a * k⁻¹) * a = a * ((k * a * k⁻¹) * a) := by rw [mul_assoc]
        _ = a * (a * (k * a * k⁻¹)) := by rw [← hcomm.eq]
        _ = a * a * (k * a * k⁻¹) := by group
        _ = k * a * k⁻¹ := by rw [ha2, one_mul]).symm
  obtain ⟨r, hrQ, hreq⟩ := exists_pCore_conj_eq (hC := hC.conj g) h' haStar hbD hqQ hwq
  have hreq' : (r : G) * (aH : G) * (r : G)⁻¹ = (bH : G) := by
    rw [hbHe]
    exact hreq
  have hba : (bH : G) = (aH : G) := eq_of_pCore_conj_eq h' hrQ hreq'
  rw [hbHe] at hba
  simpa [aH] using hba

private theorem lineGroup_mem_of_not_commute (h : MainHyp hC) {δ ε : Set G}
    (hδ : δ ∈ Dalpha D hC.alpha) (hε : ε ∈ Dalpha D hC.alpha) (hεδ : ε ∈ Dalpha D δ)
    {k a : G} (hk : k ∈ kBlock D ε) (ha : a ∈ δ)
    (hnc : ¬ Commute a (k * a * k⁻¹)) : a * (k * a * k⁻¹) ∈ lineGroup D hC.alpha ε := by
  have hδε : δ ∈ Dalpha D ε := mem_Dalpha_symm hεδ hδ.2.1
  have hδkα : cimg k δ ∈ Dalpha D hC.alpha := cimg_kBlock_mem_Dalpha h hδ hε hεδ hk ha hnc
  have hδkε : cimg k δ ∈ Dalpha D ε := by
    obtain ⟨kk, -, hkke⟩ := Subgroup.mem_map.mp hk
    exact conj_mem_Dalpha_of_mem_normalizer hC.setup.normal hδε
      (Halpha_le_normalizer_block D ε (by rw [← hkke]; exact kk.2))
  have hbδk : k * a * k⁻¹ ∈ cimg k δ := ⟨a, ha, rfl⟩
  exact Subgroup.mul_mem _
    (Subgroup.subset_closure ⟨subset_DalphaStar hδ ha, subset_DalphaStar hδε ha⟩)
    (Subgroup.subset_closure ⟨subset_DalphaStar hδkα hbδk, subset_DalphaStar hδkε hbδk⟩)

private theorem rBlock_mem_of_not_commute (h : MainHyp hC) {δ ε : Set G}
    (hδ : δ ∈ Dalpha D hC.alpha) (hε : ε ∈ Dalpha D hC.alpha) (hεδ : ε ∈ Dalpha D δ)
    {k a : G} (hk : k ∈ kBlock D ε) (ha : a ∈ δ)
    (hnc : ¬ Commute a (k * a * k⁻¹)) : a * (k * a * k⁻¹) ∈ rBlock D ε := by
  obtain ⟨kk, hkK, hkke⟩ := Subgroup.mem_map.mp hk
  have hkke' : (kk : G) = k := hkke
  have hδε : δ ∈ Dalpha D ε := mem_Dalpha_symm hεδ hδ.2.1
  have haD : a ∈ D := hδ.2.1 ha
  have ha2 : a * a = 1 := hC.setup.oddT.mul_self_eq_one haD
  have hbD : k * a * k⁻¹ ∈ D := hC.setup.normal k a haD
  have haH : a ∈ Halpha D ε := Subgroup.subset_closure (subset_DalphaStar hδε ha)
  have hbH : k * a * k⁻¹ ∈ Halpha D ε := by
    rw [← hkke']
    exact (Halpha D ε).mul_mem ((Halpha D ε).mul_mem kk.2 haH) ((Halpha D ε).inv_mem kk.2)
  let x : Halpha D ε := ⟨a * (k * a * k⁻¹), (Halpha D ε).mul_mem haH hbH⟩
  have hxeq : x = ⟨a, haH⟩ * (kk * ⟨a, haH⟩ * kk⁻¹) := by
    apply Subtype.ext
    simp only [x, Subgroup.coe_mul, Subgroup.coe_inv, hkke']
  have hxK : x ∈ EightOne.twoOddCore (Halpha D ε) := by
    rw [hxeq]
    exact CFSG.GroupTheory.mul_mul_conj_mem_of_normal hkK (Subtype.ext (by simpa using ha2))
  have hQε : CFSG.pCore 2 (Halpha D ε) ≤ Subgroup.center (Halpha D ε) := by
    obtain ⟨g, hg⟩ := mem_blockClass_iff.mp hε.1
    have hαε : (hC.conj g).alpha = ε := (HypothesisC.conj_alpha hC g).trans hg.symm
    rw [← hαε]
    exact pCore_le_center (h := h.conj g)
  have hxOdd : Odd (orderOf x) := by
    rw [← Subgroup.orderOf_coe x]
    exact hC.setup.oddT.odd_of_not_commute haD hbD hnc
  obtain ⟨W, hWO, -, -, hWchar, -⟩ := exists_odd_complement_le_oddCore (X := Halpha D ε) hQε
  exact Subgroup.mem_map_of_mem _ (hWO ((hWchar x hxK).mpr hxOdd))

private theorem mul_conj_mem_of_not_commute (h : MainHyp hC) {δ ε : Set G}
    (hδ : δ ∈ Dalpha D hC.alpha) (hε : ε ∈ Dalpha D hC.alpha) (hεδ : ε ∈ Dalpha D δ)
    {k a : G} (hk : k ∈ kBlock D ε) (ha : a ∈ δ)
    (hnc : ¬ Commute a (k * a * k⁻¹)) :
    a * (k * a * k⁻¹) ∈ rBlock D ε ⊓ lineGroup D hC.alpha ε ∧
      ∃ s ∈ Subgroup.zpowers (a * (k * a * k⁻¹)), s * a * s⁻¹ = k * a * k⁻¹ := by
  have haD : a ∈ D := hδ.2.1 ha
  have hbD : k * a * k⁻¹ ∈ D := hC.setup.normal k a haD
  have ha2 : a * a = 1 := hC.setup.oddT.mul_self_eq_one haD
  have hb2 : (k * a * k⁻¹) * (k * a * k⁻¹) = 1 := hC.setup.oddT.mul_self_eq_one hbD
  have hodd : Odd (orderOf (a * (k * a * k⁻¹))) :=
    hC.setup.oddT.odd_of_not_commute haD hbD hnc
  obtain ⟨u, hu, hbu⟩ :=
    CFSG.ComponentClassification.Foote47.exists_conj_of_odd_orderOf_mul ha2 hb2 hodd
  refine ⟨⟨rBlock_mem_of_not_commute h hδ hε hεδ hk ha hnc,
    lineGroup_mem_of_not_commute h hδ hε hεδ hk ha hnc⟩, u⁻¹, Subgroup.inv_mem _ hu, ?_⟩
  rw [inv_inv]
  exact hbu.symm

theorem mul_conj_mem_rBlock_inf_lineGroup (h : MainHyp hC) {δ ε : Set G}
    (hδ : δ ∈ Dalpha D hC.alpha) (hε : ε ∈ Dalpha D hC.alpha) (hεδ : ε ∈ Dalpha D δ)
    {k a : G} (hk : k ∈ kBlock D ε) (ha : a ∈ δ) :
    a * (k * a * k⁻¹) ∈ rBlock D ε ⊓ lineGroup D hC.alpha ε ∧
      ∃ s ∈ Subgroup.zpowers (a * (k * a * k⁻¹)), s * a * s⁻¹ = k * a * k⁻¹ := by
  by_cases hcomm : Commute a (k * a * k⁻¹)
  · have hba : k * a * k⁻¹ = a := eq_of_commute_kBlock h hδ hε hεδ hk ha hcomm
    have ha2 : a * a = 1 := hC.setup.oddT.mul_self_eq_one (hδ.2.1 ha)
    have hx1 : a * (k * a * k⁻¹) = 1 := by rw [hba, ha2]
    refine ⟨?_, 1, Subgroup.one_mem _, ?_⟩
    · rw [hx1]; exact Subgroup.one_mem _
    · rw [one_mul, inv_one, mul_one, hba]
  · exact mul_conj_mem_of_not_commute h hδ hε hεδ hk ha hcomm

theorem oddLineImage_le_closure_commSet (h : MainHyp hC) {ε : Set G}
    (hε : ε ∈ Dalpha D hC.alpha) {c : Halpha D hC.alpha} (hc : (c : G) ∈ ε) :
    oddLineImage hC ε ≤ Subgroup.closure
      (commSet (imageClass hC)
        (QuotientGroup.mk' (CFSG.solvableRadical (Halpha D hC.alpha)) c)) := by
  let M := CFSG.solvableRadical (Halpha D hC.alpha)
  let T := Subgroup.closure (commSet (imageClass hC) (QuotientGroup.mk' M c))
  have hgen : DalphaStar D hC.alpha ∩ DalphaStar D ε ⊆
      (Subgroup.comap (QuotientGroup.mk' M) T).map (Halpha D hC.alpha).subtype := by
    intro s hs
    obtain ⟨gam, hgam, hsgam⟩ := hs.2
    obtain ⟨bet, hbet, hsbet⟩ := hs.1
    have hsa : s ∈ DalphaStar D hC.alpha := subset_DalphaStar hbet hsbet
    have hclass : gam ∈ blockClass hC.alpha := (blockClass_eq_of_mem hε.1) ▸ hgam.1
    have hbg : bet = gam :=
      eq_of_mem_of_mem_blockClass hC.isBlock_alpha hbet.1 hclass ⟨s, hsbet, hsgam⟩
    have hebg : ε ∈ Dalpha D bet := hbg ▸ mem_Dalpha_symm hgam hε.2.1
    have hcommG : Commute s (c : G) :=
      ((mem_Dalpha_iff.mp hgam).2.2.2 (c : G) hc s hsgam).symm
    exact ⟨⟨s, Subgroup.subset_closure hsa⟩,
      Subgroup.mem_comap.mpr (Subgroup.subset_closure
        ⟨⟨⟨s, Subgroup.subset_closure hsa⟩, hsa, rfl⟩,
          Commute.map (show Commute (⟨s, Subgroup.subset_closure hsa⟩ :
            Halpha D hC.alpha) c from Subtype.ext hcommG.eq) (QuotientGroup.mk' M),
          h.mk_ne_mk_of_mem_Dalpha hbet hε hebg hsbet hc⟩), rfl⟩
  have hLle : lineGroup D hC.alpha ε ≤
      (Subgroup.comap (QuotientGroup.mk' M) T).map (Halpha D hC.alpha).subtype :=
    (Subgroup.closure_le _).mpr hgen
  have hsub : (rBlock D ε ⊓ lineGroup D hC.alpha ε).subgroupOf (Halpha D hC.alpha) ≤
      Subgroup.comap (QuotientGroup.mk' M) T := by
    intro x hx
    rw [Subgroup.mem_subgroupOf] at hx
    obtain ⟨y, hy, hyx⟩ := hLle hx.2
    have hxy : x = y := Subtype.ext hyx.symm
    rw [Subgroup.mem_comap, hxy]
    exact Subgroup.mem_comap.mp hy
  intro n hn
  exact Subgroup.map_le_iff_le_comap.mpr hsub (show n ∈ oddLineImage hC ε from hn)

theorem conj_mem_oddLineImage (h : MainHyp hC) {ε : Set G} (hε : ε ∈ Dalpha D hC.alpha)
    {c : Halpha D hC.alpha} (hc : (c : G) ∈ ε) :
    ∀ y ∈ imageClass hC,
      Commute y (QuotientGroup.mk' (CFSG.solvableRadical (Halpha D hC.alpha)) c) →
      ∀ n ∈ oddLineImage hC ε, y * n * y⁻¹ ∈ oddLineImage hC ε := by
  intro y hy hcomm n hn
  obtain ⟨y0, hy0, hy0eq⟩ := hy
  rw [← hy0eq] at hcomm
  obtain ⟨y', hy'eq, hcomm'⟩ := exists_commuting_preimage h hε hc hcomm
  obtain ⟨u, hu, hnu⟩ := Subgroup.mem_map.mp hn
  rw [Subgroup.mem_subgroupOf] at hu
  have hmem : ((y' * u * y'⁻¹ : Halpha D hC.alpha) : G) ∈
      rBlock D ε ⊓ lineGroup D hC.alpha ε :=
    conj_mem_rBlock_inf_lineGroup hε hc hcomm' hu
  have hsub : y' * u * y'⁻¹ ∈
      (rBlock D ε ⊓ lineGroup D hC.alpha ε).subgroupOf (Halpha D hC.alpha) := by
    rw [Subgroup.mem_subgroupOf]
    exact hmem
  have hkey : y * n * y⁻¹ = QuotientGroup.mk' (CFSG.solvableRadical (Halpha D hC.alpha))
      (y' * u * y'⁻¹) := by
    rw [← hnu, map_mul, map_mul, map_inv, hy'eq, hy0eq]
  exact Subgroup.mem_map.mpr ⟨_, hsub, hkey.symm⟩

end MainHyp

end CFSG.OddTranspositions.PartThree.ElevenThree
