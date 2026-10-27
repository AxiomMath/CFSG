module

public import CFSG.LocalAnalysis.StandardType.GGF4QGeFourOpp
public import CFSG.LocalAnalysis.StandardType.GGF4QGeFourEndsOriginal
import CFSG.LocalAnalysis.StandardType.GGF4AbsorbConj
import CFSG.LocalAnalysis.StandardType.GGF4EndpointType
import CFSG.LocalAnalysis.StandardType.GGF4Absorption
import CFSG.LocalAnalysis.StandardType.GGSecFiveRestOriginalWeyl
import CFSG.LocalAnalysis.StandardType.GGAutomizerJoinInduced
import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyAut
import CFSG.LocalAnalysis.StandardType.GGCoxeterLabelTypeAAssembly
import CFSG.LocalAnalysis.StandardType.GGF4ReflLin
import CFSG.LocalAnalysis.StandardType.GGFieldCaseTableBIrred
import CFSG.LocalAnalysis.StandardType.GGSecFiveBNbrCompare
import CFSG.LocalAnalysis.StandardType.GGSecFiveMaxJoin

public section

namespace CFSG.StandardType

open CFSG.Open CFSG.Assembly

section Absorb


theorem ggF4QGeFourEnds_conj_L_or_opp
    (hX : GGResXDichotomyInput) (hTCJ : GGTCJKnown) (hRig : GGLabelRigidInput)
    (hTBF : GGTBFixInput) (hWI : GGNbrInnerWeylInput) (hTPn : GGNbrTablePNbrInputNarrow)
    (hA8 : GGForkA8NotReflInput) (hraw : GGRawInnFieldInput) (hiso : GGRawInndiagIsoInput)
    (hFC : GGResNbrFixCentralizesInput)
    {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    {y : G} {K : Subgroup G} (hNb : GGNbr p B x D J y K)
    (hRC : GGSecFiveRouteCfg p B Bs x L D J {K}) (hT1 : ¬ GGSecFiveTier1Region p B Bs x L D J)
    (hWK : GGWeylOfType p CoxeterMatrix.F₄ (ggAutomizer L Bs ⊔ ggAutomizer K Bs))
    {z : G} {A : Subgroup G}
    (hA : GGF4QGeFourOppEnd p Bs x (ggAutomizer L Bs ⊔ ggAutomizer K Bs) z A) :
    ∃ h ∈ L ⊔ K, h ∈ Subgroup.normalizer (Bs : Set G) ∧
      (L = K.map (MulAut.conj h).toMonoidHom ∨ A = K.map (MulAut.conj h).toMonoidHom) := by
  have hR : GGSecFiveRestHyp p B Bs x L D J := hRC.1
  have hW : GGSecFiveWeylCase' p B Bs x D J := hRC.2.1
  obtain ⟨hp, hBs, -, -, h4⟩ := hR.1.tableB_facts
  have : Fact p.Prime := ⟨hp⟩
  have hp2 : p ≠ 2 := hR.1.1.2.2.2.2.2.1.2.1
  have hNT : GGNoTransvection p Bs := hR.2.2.2.1
  obtain ⟨-, -, hB, -⟩ := ggF4QGeFourEnds_bstar_types hX hTCJ hRig hTBF hWI hNb hRC hT1 hWK
  have hJ : ggAutomizerJoin L Bs {K} = ggAutomizer L Bs ⊔ ggAutomizer K Bs :=
    ggAutomizerJoin_singleton L Bs K
  obtain ⟨e, he⟩ := hWK
  let e' : CoxeterMatrix.F₄.Group ≃* ↥(ggAutomizerJoin L Bs {K}) :=
    e.trans (MulEquiv.subgroupCongr hJ.symm)
  have hP : GGCoxeterPres p (ggAutomizerJoin L Bs {K}) CoxeterMatrix.F₄ e' :=
    ⟨Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨Equiv.refl _,
      (ggCoxeterMatrix_reindex_refl _).symm⟩)))), fun i => he i⟩
  have hF4 : GGIsWeylMatrixF4 CoxeterMatrix.F₄ :=
    ⟨Equiv.refl _, (ggCoxeterMatrix_reindex_refl _).symm⟩
  have hAind : ∀ φ ∈ ggAutomizerJoin L Bs {K}, φ ∈ ggInduced ⊤ Bs := fun φ hφ =>
    ggAutomizerJoin_le_ggInduced_top L {K} hφ
  have hAH : ggAutomizerJoin L Bs {K} ≤ ggAutomizer (L ⊔ K) Bs := by
    rw [hJ]
    exact sup_le (ggAutomizer_mono Bs le_sup_left) (ggAutomizer_mono Bs le_sup_right)
  have hLfix : GGFixLineComp Bs x L := GGSecFiveRestHyp.fixLineComp_L hTBF hR hW
  have hKfix : GGFixLineComp Bs y K := GGSecFiveRestHyp.fixLineComp_nbr hFC hR hW hB hNb
  have hF1 : ∀ y' K', GGNbr p B x D J y' K' → ∀ b : ↥Bs,
      (∀ a ∈ ggAutomizer K' Bs, a b = b) → (b : G) ∈ Subgroup.centralizer (K' : Set G) :=
    fun y' K' hn b hb =>
      hFC G p B Bs x L D J y' K' ⟨hR.1, hR.2.1, hR.2.2.1, hR.2.2.2.1, hn, hW y' K' hn, Or.inr hW⟩
        b hb
  have hfixA : ∀ b : ↥Bs, (∀ a ∈ ggAutomizerJoin L Bs {K}, a b = b) → b = 1 :=
    ggF4_join_fix_one hRC (fun b hb => (hLfix.fix_iff b).1 hb) hF1 (Finset.singleton_nonempty K)
  have hx1 : x ≠ 1 := hR.1.1.2.2.2.2.2.2.1.2.2.1
  have hy1 : y ≠ 1 := fun h => GGConfig.not_mem_zpowers_of_ggNbr hR.1 hNb (h ▸ Subgroup.one_mem _)
  have hLA : ggAutomizer L Bs ≤ ggAutomizerJoin L Bs {K} := hJ ▸ le_sup_left
  have hKA : ggAutomizer K Bs ≤ ggAutomizerJoin L Bs {K} := hJ ▸ le_sup_right
  obtain ⟨hAfix, hz1, hBA, hAW, hWA, horb⟩ := hA
  have hAA : ggAutomizer A Bs ≤ ggAutomizerJoin L Bs {K} := hJ ▸ hAW
  obtain ⟨tL, htLA, htL, htLx, htLc, hLcard⟩ :=
    ggF4_exists_endpointRefl hp2 hBs h4 hNT hAind hP hF4 hfixA hLA
      (GGSecFiveRestHyp.weylReflectionGroup_L hX hTCJ hRig hR hW) hLfix.mem hx1 hLfix.fix_iff
  obtain ⟨tK, htKA, htK, htKy, htKc, hKcard⟩ :=
    ggF4_exists_endpointRefl hp2 hBs h4 hNT hAind hP hF4 hfixA hKA
      (GGSecFiveRestHyp.weylReflectionGroup_nbr hX hTCJ hRig hTPn hA8 hraw hiso hR hW hNb)
      hKfix.mem hy1 hKfix.fix_iff
  obtain ⟨tA, htAA, htA, htAz, htAc, hAcard⟩ :=
    ggF4_exists_endpointRefl hp2 hBs h4 hNT hAind hP hF4 hfixA hAA hWA hAfix.mem hz1 hAfix.fix_iff
  have hnot : ∀ w ∈ ggAutomizerJoin L Bs {K}, w * tA * w⁻¹ ≠ tL := by
    intro w hw hwt
    have hinv : tL (w ⟨z, hAfix.mem⟩) = (w ⟨z, hAfix.mem⟩)⁻¹ := by
      calc tL (w ⟨z, hAfix.mem⟩) = (w * tA * w⁻¹) (w ⟨z, hAfix.mem⟩) := by rw [hwt]
        _ = w (tA (w⁻¹ (w ⟨z, hAfix.mem⟩))) := rfl
        _ = w (tA ⟨z, hAfix.mem⟩) := by rw [MulAut.inv_apply_self]
        _ = w (⟨z, hAfix.mem⟩⁻¹) := by rw [htAz]
        _ = (w ⟨z, hAfix.mem⟩)⁻¹ := map_inv w _
    have hx1' : (⟨x, hLfix.mem⟩ : ↥Bs) ≠ 1 := fun h1 => hx1 (by simpa using congrArg Subtype.val h1)
    have hmem : w ⟨z, hAfix.mem⟩ ∈ Subgroup.zpowers (⟨x, hLfix.mem⟩ : ↥Bs) :=
      GGIsReflection.mem_zpowers_of_apply_eq_inv hp2 hBs htL hx1' htLx hinv
    have hmemG : ((w ⟨z, hAfix.mem⟩ : ↥Bs) : G) ∈ Subgroup.zpowers x := by
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hmem
      exact Subgroup.mem_zpowers_iff.mpr ⟨k, by rw [← hk]; simp⟩
    exact horb w (hJ ▸ hw) ⟨z, hAfix.mem⟩ rfl hmemG
  obtain ⟨w, hwA, hw | hw⟩ :=
    ggF4_exists_conj_of_not_conj hp2 hBs hNT hAind hP hF4 htLA htKA htAA htL htK htA hnot
  · obtain ⟨h, hhH, hhN, hXK⟩ :=
      GGFixLineComp.exists_eq_map_conj_of_conj_endpointRefl (H := L ⊔ K) hp2 hBs hLfix hKfix
        hR.2.2.1.1.le_normalizer hx1 hy1 hAH hwA hw htL htLx htKy hLA hKA htLc htKc hLcard
        hKcard (ggF4_card_inf_centralizer_le hp2 hBs hNT hAind hP hF4 htLA htL)
    exact ⟨h, hhH, hhN, Or.inl hXK⟩
  · obtain ⟨h, hhH, hhN, hXK⟩ :=
      GGFixLineComp.exists_eq_map_conj_of_conj_endpointRefl (H := L ⊔ K) hp2 hBs hAfix hKfix
        hBA hz1 hy1 hAH hwA hw htA htAz htKy hAA hKA htAc htKc hAcard hKcard
        (ggF4_card_inf_centralizer_le hp2 hBs hNT hAind hP hF4 htAA htA)
    exact ⟨h, hhH, hhN, Or.inr hXK⟩

theorem GGCentralImage.of_eq_map_conj {G : Type} [Group G] {t : StatedLieTag} {n f : ℕ}
    {X K : Subgroup G} {h : G} (hXK : X = K.map (MulAut.conj h).toMonoidHom)
    (hX : GGCentralImage t n f X) : GGCentralImage t n f K := by
  obtain ⟨ψ, hadm, hker, hrange⟩ := hX
  refine ⟨(MulAut.conj h⁻¹).toMonoidHom.comp ψ, hadm, fun k hk => hker ?_, ?_⟩
  · rw [MonoidHom.mem_ker] at hk ⊢
    have hk' : h⁻¹ * ψ k * h = 1 := by simpa using hk
    calc ψ k = h * (h⁻¹ * ψ k * h) * h⁻¹ := by group
      _ = 1 := by rw [hk', mul_one, mul_inv_cancel]
  · have hid : (MulAut.conj h⁻¹).toMonoidHom.comp (MulAut.conj h).toMonoidHom =
        MonoidHom.id G := by
      ext g
      simp [mul_assoc]
    rw [MonoidHom.range_comp, hrange, hXK, Subgroup.map_map, hid, Subgroup.map_id]

end Absorb

section Ends


theorem ggF4QGeFourEndsInput_of_opp
    (hX : GGResXDichotomyInput) (hTCJ : GGTCJKnown) (hRig : GGLabelRigidInput)
    (hTBF : GGTBFixInput) (hWI : GGNbrInnerWeylInput) (hTPn : GGNbrTablePNbrInputNarrow)
    (hA8 : GGForkA8NotReflInput) (hraw : GGRawInnFieldInput) (hiso : GGRawInndiagIsoInput)
    (hLB : GGLBalanceInput) (hFC : GGResNbrFixCentralizesInput)
    (hSp : GGF4QGeFourOppSpInput) (hOm : GGF4QGeFourOppOmegaInput)
    (hPl : GGF4QGeFourOppPlusInput) : GGF4QGeFourEndsInput := by
  intro G _ _ p B Bs x L D J hR hW hq y K hNb hRC hT1 hWK
  have habs : ∀ {z : G} {A : Subgroup G},
      GGF4QGeFourOppEnd p Bs x (ggAutomizer L Bs ⊔ ggAutomizer K Bs) z A →
      ∀ {t s : StatedLieTag} {n m f f' : ℕ}, GGCentralImage t n f L →
        GGCentralImage s m f' A → GGCentralImage t n f K ∨ GGCentralImage s m f' K := by
    intro z A hA t s n m f f' hL hA'
    obtain ⟨h, -, -, hLK | hAK⟩ :=
      ggF4QGeFourEnds_conj_L_or_opp hX hTCJ hRig hTBF hWI hTPn hA8 hraw hiso hFC hNb hRC hT1 hWK hA
    · exact Or.inl (GGCentralImage.of_eq_map_conj hLK hL)
    · exact Or.inr (GGCentralImage.of_eq_map_conj hAK hA')
  rcases ggF4QGeFourEnds_originalRow hX hTCJ hRig hTBF hWI hTPn hA8 hraw hiso hLB hq hNb hRC hT1
      hWK with ⟨f, hf, hp, hL⟩ | ⟨f, hf, hp, hL⟩ | ⟨f, hf, hp, hL⟩
  · obtain ⟨z, A, hA, hAc⟩ := hSp G p B Bs x L D J hR hW hq y K hNb hRC hT1 hWK f hf hp hL
    exact Or.inl ⟨f, hf, hp, hL, (habs hA hL hAc).elim id id⟩
  · obtain ⟨z, A, hA, hAc⟩ := hOm G p B Bs x L D J hR hW hq y K hNb hRC hT1 hWK f hf hp hL
    exact Or.inr (Or.inl ⟨f, hf, hp, hL, (habs hA hL hAc).symm⟩)
  · obtain ⟨rfl, rfl, z, A, hA, hAc⟩ :=
      hPl G p B Bs x L D J hR hW hq y K hNb hRC hT1 hWK f hf hp hL
    exact Or.inr (Or.inr ⟨rfl, hL, (habs hA hL hAc).symm⟩)

end Ends

end CFSG.StandardType

end
