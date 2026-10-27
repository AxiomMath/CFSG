module

public import CFSG.LocalAnalysis.StandardType.GGE0ShapeDefs
public import CFSG.LocalAnalysis.StandardType.GGOTwoStarFrame
public import CFSG.LocalAnalysis.StandardType.GGSteinbergCorrection
public import CFSG.LocalAnalysis.StandardType.GGE0ShapeConjAux
public import CFSG.LocalAnalysis.StandardType.GGE0ShapeConjAux2

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Universal
  CFSG.LieType.RootSystem CFSG.LieType.Chevalley CFSG.HardMathSupport.Timmesfeld.Torality
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.Assembly.LowTwoRank CFSG.RankThree.PartTwo.Sec21
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

theorem ggSixCtxV2_conj
    {G : Type} [Group G] [Finite G]
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {t : StatedLieTag} {n f : ℕ}
    {ψ : (ggU t n f).K →* G}
    (hctx : GGSixCtxV2 3 B Bs x L D J (ggU t n f).D t n f ψ) (g : G) :
    GGSixCtxV2 3 (B.map (MulAut.conj g).toMonoidHom) (Bs.map (MulAut.conj g).toMonoidHom)
      (g * x * g⁻¹) (L.map (MulAut.conj g).toMonoidHom) (D.map (MulAut.conj g).toMonoidHom)
      (J.map (MulAut.conj g).toMonoidHom) (ggU t n f).D t n f
      ((MulAut.conj g).toMonoidHom.comp ψ) := by
  obtain ⟨hI, hcore⟩ := hctx
  exact ⟨shapeConj_ggThmIHyp_map_conj g hI, shapeConj_ggSixHypV2Core_map_conj g hcore⟩

theorem ggSixStepOne_conj {G : Type} [Group G] [Finite G]
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    (s1 : GGSixStepOne 3 B Bs x L D J) (g : G) :
    GGSixStepOne 3 (B.map (MulAut.conj g).toMonoidHom) (Bs.map (MulAut.conj g).toMonoidHom)
      (g * x * g⁻¹) (L.map (MulAut.conj g).toMonoidHom) (D.map (MulAut.conj g).toMonoidHom)
      (J.map (MulAut.conj g).toMonoidHom) := by
  obtain ⟨hC, hfus, hcop, hSyl, hTr⟩ := s1
  have hgg0 := shapeConj_ggG0_map_conj 3 (B := B) (x := x) (L := L) (D := D) (J := J) g
  have hggM := shapeConj_ggM_map_conj (p := 3) (B := B) (x := x) (L := L) (D := D) (J := J) g
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [hgg0, ← shapeConj_map_centralizer (ggG0 3 B x L D J) g, hC, Subgroup.map_bot]
  · rw [hggM]
    exact (shapeConj_ggControlsStrongFusion_map_conj g).mpr hfus
  · intro Q' hDQ' hcop'
    have hQ : Q'.map (MulAut.conj g⁻¹).toMonoidHom ≤ ggM 3 B x L D J := by
      apply hcop
      · intro d hd
        have h1 : g * d * g⁻¹ ∈ Subgroup.normalizer (Q' : Set G) := hDQ' ⟨d, hd, rfl⟩
        have h2 := shapeConj_mem_normalizer_map_conj
          (H := Q') (b := g * d * g⁻¹) (g := g⁻¹) h1
        convert h2 using 1
        group
      · rwa [Subgroup.card_map_of_injective (MulAut.conj g⁻¹).injective]
    rw [← shapeConj_map_conj_inv_cancel' Q' g, hggM]
    exact Subgroup.map_mono hQ
  · obtain ⟨P, hBsP, huniq⟩ := hSyl
    let M : Subgroup G := ggM 3 B x L D J
    let e : ↥M ≃* ↥(ggM 3 (B.map (MulAut.conj g).toMonoidHom) (g * x * g⁻¹)
        (L.map (MulAut.conj g).toMonoidHom) (D.map (MulAut.conj g).toMonoidHom)
        (J.map (MulAut.conj g).toMonoidHom)) :=
      (conjEquivMap M g).trans (MulEquiv.subgroupCongr hggM).symm
    let P' : Sylow 3 ↥(ggM 3 (B.map (MulAut.conj g).toMonoidHom) (g * x * g⁻¹)
        (L.map (MulAut.conj g).toMonoidHom) (D.map (MulAut.conj g).toMonoidHom)
        (J.map (MulAut.conj g).toMonoidHom)) :=
      { toSubgroup := (P : Subgroup M).map e.toMonoidHom
        isPGroup' := P.isPGroup'.map e.toMonoidHom
        is_maximal' := by
          intro Q hQ hle
          have hQ' : IsPGroup 3 ↥(Q.map e.symm.toMonoidHom) := hQ.map e.symm.toMonoidHom
          have hle' : (P : Subgroup M) ≤ Q.map e.symm.toMonoidHom := by
            have h1 : (P.map e.toMonoidHom).map e.symm.toMonoidHom ≤
                Q.map e.symm.toMonoidHom := Subgroup.map_mono hle
            rwa [Subgroup.map_map,
              show e.symm.toMonoidHom.comp e.toMonoidHom = MonoidHom.id ↥M from
                MonoidHom.ext fun y => e.symm_apply_apply y,
              Subgroup.map_id] at h1
          have hmax := P.is_maximal' hQ' hle'
          rw [← hmax, Subgroup.map_map,
            show e.toMonoidHom.comp e.symm.toMonoidHom = MonoidHom.id _ from
              MonoidHom.ext fun y => e.apply_symm_apply y,
            Subgroup.map_id] }
    have hcoe : (P' : Subgroup ↥(ggM 3 (B.map (MulAut.conj g).toMonoidHom) (g * x * g⁻¹)
          (L.map (MulAut.conj g).toMonoidHom) (D.map (MulAut.conj g).toMonoidHom)
          (J.map (MulAut.conj g).toMonoidHom))).map
        (ggM 3 (B.map (MulAut.conj g).toMonoidHom) (g * x * g⁻¹)
          (L.map (MulAut.conj g).toMonoidHom) (D.map (MulAut.conj g).toMonoidHom)
          (J.map (MulAut.conj g).toMonoidHom)).subtype =
        ((P : Subgroup M).map M.subtype).map (MulAut.conj g).toMonoidHom := by
      change ((P : Subgroup M).map e.toMonoidHom).map
          (ggM 3 (B.map (MulAut.conj g).toMonoidHom) (g * x * g⁻¹)
            (L.map (MulAut.conj g).toMonoidHom) (D.map (MulAut.conj g).toMonoidHom)
            (J.map (MulAut.conj g).toMonoidHom)).subtype = _
      rw [Subgroup.map_map, Subgroup.map_map]
      congr 1
    refine ⟨P', ?_, ?_⟩
    · rw [hcoe]
      exact Subgroup.map_mono hBsP
    · intro E' hE' hel' hcard'
      rw [hcoe] at hE'
      have hE : E'.map (MulAut.conj g⁻¹).toMonoidHom ≤ (P : Subgroup M).map M.subtype := by
        have h1 := Subgroup.map_mono hE' (f := (MulAut.conj g⁻¹).toMonoidHom)
        rwa [Subgroup.map_map,
          show (MulAut.conj g⁻¹).toMonoidHom.comp (MulAut.conj g).toMonoidHom =
              MonoidHom.id G from by
            ext z
            simp only [MonoidHom.comp_apply, MonoidHom.id_apply, MulEquiv.coe_toMonoidHom,
              MulAut.conj_apply]
            group,
          Subgroup.map_id] at h1
      have hcard : Nat.card (E'.map (MulAut.conj g⁻¹).toMonoidHom) = Nat.card Bs := by
        rw [Subgroup.card_map_of_injective (MulAut.conj g⁻¹).injective, hcard',
          Subgroup.card_map_of_injective (MulAut.conj g).injective]
      have hel : IsElemAbelian 3 (E'.map (MulAut.conj g⁻¹).toMonoidHom) :=
        shapeConj_isElemAbelian_map_conj hel' g⁻¹
      have hEq := huniq _ hE hel hcard
      calc E' = (E'.map (MulAut.conj g⁻¹).toMonoidHom).map (MulAut.conj g).toMonoidHom :=
              (shapeConj_map_conj_inv_cancel' E' g).symm
           _ = Bs.map (MulAut.conj g).toMonoidHom := by rw [hEq]
  · intro a' ha'
    have ha'' : a' ∈ (Subgroup.normalizer (Bs : Set G)).map (MulAut.conj g).toMonoidHom := by
      rw [shapeConj_map_normalizer Bs g]
      exact ha'
    obtain ⟨a, ha, rfl⟩ := ha''
    intro htrans
    exact hTr a ha ((shapeConj_ggTransvection_map_conj a g).mp htrans)

theorem ggG0_map_conj {G : Type} [Group G] [Finite G]
    {B : Subgroup G} {x : G} {L D J : Subgroup G} (g : G) :
    ggG0 3 (B.map (MulAut.conj g).toMonoidHom) (g * x * g⁻¹) (L.map (MulAut.conj g).toMonoidHom)
      (D.map (MulAut.conj g).toMonoidHom) (J.map (MulAut.conj g).toMonoidHom) =
      (ggG0 3 B x L D J).map (MulAut.conj g).toMonoidHom := by
  unfold ggG0
  simp only [Subgroup.map_sup, Subgroup.map_iSup]
  congr 1
  apply le_antisymm
  · refine iSup_le fun y => iSup_le fun K => iSup_le fun h => ?_
    have hS : LargeEvenSHat 3 B (g⁻¹ * y * g)
        (K.map (MulAut.conj g⁻¹).toMonoidHom) := by
      have h1 := shapeConj_largeEvenSHat_map_conj h.1 g⁻¹
      have hy : g⁻¹ * y * g⁻¹⁻¹ = g⁻¹ * y * g := by group
      rwa [shapeConj_map_conj_inv_cancel B g, hy] at h1
    have hN : LargeEvenNeighbor 3 x (g⁻¹ * y * g)
        (K.map (MulAut.conj g⁻¹).toMonoidHom) D J := by
      have h1 := shapeConj_largeEvenNeighbor_map_conj h.2 g⁻¹
      have hx : g⁻¹ * (g * x * g⁻¹) * g⁻¹⁻¹ = x := by group
      have hy : g⁻¹ * y * g⁻¹⁻¹ = g⁻¹ * y * g := by group
      rwa [shapeConj_map_conj_inv_cancel D g, shapeConj_map_conj_inv_cancel J g, hx, hy] at h1
    refine le_iSup_of_le (g⁻¹ * y * g) (le_iSup_of_le (K.map (MulAut.conj g⁻¹).toMonoidHom)
      (le_iSup_of_le ⟨hS, hN⟩ ?_))
    exact le_of_eq (shapeConj_map_conj_inv_cancel' K g).symm
  · refine iSup_le fun y => iSup_le fun K => iSup_le fun h => ?_
    have hS : LargeEvenSHat 3 (B.map (MulAut.conj g).toMonoidHom) (g * y * g⁻¹)
        (K.map (MulAut.conj g).toMonoidHom) :=
      shapeConj_largeEvenSHat_map_conj h.1 g
    have hN : LargeEvenNeighbor 3 (g * x * g⁻¹) (g * y * g⁻¹)
        (K.map (MulAut.conj g).toMonoidHom) (D.map (MulAut.conj g).toMonoidHom)
        (J.map (MulAut.conj g).toMonoidHom) :=
      shapeConj_largeEvenNeighbor_map_conj h.2 g
    refine le_iSup_of_le (g * y * g⁻¹) (le_iSup_of_le (K.map (MulAut.conj g).toMonoidHom)
      (le_iSup_of_le ⟨hS, hN⟩ ?_))
    rfl

theorem ggG1_comp_conj_eq
    {G : Type} [Group G] [Finite G]
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {t : StatedLieTag} {n f : ℕ}
    {ψ : (ggU t n f).K →* G}
    (hctx : GGSixCtxV2 3 B Bs x L D J (ggU t n f).D t n f ψ) (hSt : GGSteinbergCorrectionAt t)
    {m : G} (hm : m ∈ ggM 3 B x L D J) :
    ggG1 ((MulAut.conj m).toMonoidHom.comp ψ) = ggG1 ψ := by
  have hP : GGPresentsG0 (ggG0 3 B x L D J) (ggU t n f).D t n f ψ :=
    ⟨hctx.2.2.2.1, ⟨GGSixCtxV2.range_eq hctx, hctx.2.2.2.2.1.2⟩,
      GGSixCtxV2.perfect hctx, GGSixCtxV2.lieModel hctx⟩
  have hSt' : ∀ m ∈ Subgroup.normalizer (ψ.range : Set G), ∃ g ∈ ψ.range,
      GGRootAdmissible (ggU t n f).D ψ (m * g) := by
    intro m hm
    rw [GGSixCtxV2.range_eq hctx] at hm ⊢
    exact hSt G n f ψ _ hP m hm
  have hNorm := ggG1_conj_mem_of_steinberg (GGSixCtxV2.range_eq hctx) hSt'
  have hm' : m ∈ Subgroup.normalizer (ψ.range : Set G) := by
    rw [GGSixCtxV2.range_eq hctx]
    exact hm
  rw [shapeConj_ggG1_comp_conj hm']
  apply le_antisymm
  · rintro c ⟨d, hd, rfl⟩
    exact hNorm m hm d hd
  · intro c hc
    refine ⟨m⁻¹ * c * m, ?_, by
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]; group⟩
    simpa only [inv_inv, SetLike.mem_coe] using
      hNorm m⁻¹ (Subgroup.inv_mem (ggM 3 B x L D J) hm) c hc

end CFSG.StandardType
