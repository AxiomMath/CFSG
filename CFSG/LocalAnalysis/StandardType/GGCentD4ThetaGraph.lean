module

public import CFSG.LocalAnalysis.StandardType.GGNTPlaneInput
public import CFSG.RankThree.Chevalley.SteinbergBID4Restrict
public import CFSG.RankThree.PartOne.KE.D4TranspositionInterface
public import CFSG.HardMathSupport.Lang.D4Three.NormalForm
public import CFSG.LocalAnalysis.StandardType.GGCentD4HomExt
public import CFSG.LocalAnalysis.StandardType.GGCentD4ThetaGraphAux

public section

namespace CFSG.StandardType.NTPlane

open CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.RankThree.Chevalley CFSG.RankThree.PartOne.KE CFSG.HardMathSupport.Lang.D4Three

theorem ntpD4_theta_graph
    {L : Type} [Field L] [CharP L 2] (v : WeylGroup Tag.E6)
    (Y : Subgroup (ModGL Tag.E6 L))
    (hY : Y = rootSpan Tag.E6 L ((fun α => v • α) '' parabolicRoots Tag.E6 (d4Nodes Tag.E6)))
    (Θ : ↥Y ≃* ↥(adjointGroup Tag.D4 L))
    (hΘ : ∀ (y : ↥Y) (k : Fin Tag.D4.rank) (c : L),
      ((y : ModGL Tag.E6 L) = canonicalRep (coxeterSystem Tag.E6) L v *
          xUnit Tag.E6 L (d4Idx k) c * (canonicalRep (coxeterSystem Tag.E6) L v)⁻¹ →
        (Θ y : ModGL Tag.D4 L) = xUnit Tag.D4 L k c) ∧
      ((y : ModGL Tag.E6 L) = canonicalRep (coxeterSystem Tag.E6) L v *
          yUnit Tag.E6 L (d4Idx k) c * (canonicalRep (coxeterSystem Tag.E6) L v)⁻¹ →
        (Θ y : ModGL Tag.D4 L) = yUnit Tag.D4 L k c))
    (z : WeylGroup Tag.E6) (ε : ℕ)
    (hz : ∀ k : Fin Tag.D4.rank, z • (v • (Pi.single (d4Idx k) 1 : Fin Tag.E6.rank → ℤ)) =
      v • (Pi.single (d4Idx ((CFSG.HardMathSupport.Lang.D4Three.d4Rho ^ ε) k)) 1 : Fin Tag.E6.rank → ℤ))
    (y : ModGL Tag.E6 L) (hy : y ∈ Y)
    (hy' : canonicalRep (coxeterSystem Tag.E6) L z * y *
      (canonicalRep (coxeterSystem Tag.E6) L z)⁻¹ ∈ Y) :
    Θ ⟨canonicalRep (coxeterSystem Tag.E6) L z * y *
        (canonicalRep (coxeterSystem Tag.E6) L z)⁻¹, hy'⟩ = d4Graph L ε (Θ ⟨y, hy⟩) := by
  have h2L : (2 : L) = 0 := CharP.cast_eq_zero L 2
  set nv : ModGL Tag.E6 L := canonicalRep (coxeterSystem Tag.E6) L v with hnv
  set nz : ModGL Tag.E6 L := canonicalRep (coxeterSystem Tag.E6) L z with hnz
  have hstab : Y.map (MulAut.conj nz).toMonoidHom = Y := by
    rw [hY]
    exact ntpTG_conj_rootSpan_eq (L := L) v z ε hz
  have hstab' : Y.map (↑(MulAut.conj nz)) = Y := hstab
  let cf : MulAut ↥Y :=
    ((MulAut.conj nz).subgroupMap Y).trans (MulEquiv.subgroupCongr hstab')
  have hcf : ∀ x : ↥Y,
      ((cf x : ↥Y) : ModGL Tag.E6 L) = nz * (x : ModGL Tag.E6 L) * nz⁻¹ := by
    intro x
    simp only [cf, MulEquiv.trans_apply]
    rw [MulEquiv.subgroupCongr_apply, MulEquiv.coe_subgroupMap_apply, MulAut.conj_apply]
  let φ : ↥Y →* ↥(adjointGroup Tag.D4 L) := Θ.toMonoidHom.comp cf.toMonoidHom
  let ψ : ↥Y →* ↥(adjointGroup Tag.D4 L) :=
    (d4Graph L ε).toMonoidHom.comp Θ.toMonoidHom
  have hx : ∀ (y : ↥Y) (k : Fin Tag.D4.rank) (c : L),
      (y : ModGL Tag.E6 L) = nv * xUnit Tag.E6 L (d4Idx k) c * nv⁻¹ → φ y = ψ y := by
    intro y k c hyk
    have hconj : nz * (y : ModGL Tag.E6 L) * nz⁻¹ =
        nv * xUnit Tag.E6 L (d4Idx ((CFSG.HardMathSupport.Lang.D4Three.d4Rho ^ ε) k)) c * nv⁻¹ := by
      rw [hyk]
      exact ntpTG_conj_xUnit h2L v z ε hz k c
    have hΘcf : (Θ (cf y) : ModGL Tag.D4 L) =
        xUnit Tag.D4 L ((CFSG.HardMathSupport.Lang.D4Three.d4Rho ^ ε) k) c :=
      (hΘ (cf y) ((CFSG.HardMathSupport.Lang.D4Three.d4Rho ^ ε) k) c).1 ((hcf y).trans hconj)
    have hΘy : (Θ y : ModGL Tag.D4 L) = xUnit Tag.D4 L k c := (hΘ y k c).1 hyk
    have hφ : φ y = adjX Tag.D4 L ((CFSG.HardMathSupport.Lang.D4Three.d4Rho ^ ε) k) c := by
      show Θ (cf y) = adjX Tag.D4 L ((CFSG.HardMathSupport.Lang.D4Three.d4Rho ^ ε) k) c
      exact Subtype.ext hΘcf
    have hψ : ψ y = adjX Tag.D4 L ((CFSG.HardMathSupport.Lang.D4Three.d4Rho ^ ε) k) c := by
      show d4Graph L ε (Θ y) = adjX Tag.D4 L ((CFSG.HardMathSupport.Lang.D4Three.d4Rho ^ ε) k) c
      rw [show Θ y = adjX Tag.D4 L k c from Subtype.ext hΘy, d4Graph_adjX]
    rw [hφ, hψ]
  have hyY : ∀ (y : ↥Y) (k : Fin Tag.D4.rank) (c : L),
      (y : ModGL Tag.E6 L) = nv * yUnit Tag.E6 L (d4Idx k) c * nv⁻¹ → φ y = ψ y := by
    intro y k c hyk
    have hconj : nz * (y : ModGL Tag.E6 L) * nz⁻¹ =
        nv * yUnit Tag.E6 L (d4Idx ((CFSG.HardMathSupport.Lang.D4Three.d4Rho ^ ε) k)) c * nv⁻¹ := by
      rw [hyk]
      exact ntpTG_conj_yUnit h2L v z ε hz k c
    have hΘcf : (Θ (cf y) : ModGL Tag.D4 L) =
        yUnit Tag.D4 L ((CFSG.HardMathSupport.Lang.D4Three.d4Rho ^ ε) k) c :=
      (hΘ (cf y) ((CFSG.HardMathSupport.Lang.D4Three.d4Rho ^ ε) k) c).2 ((hcf y).trans hconj)
    have hΘy : (Θ y : ModGL Tag.D4 L) = yUnit Tag.D4 L k c := (hΘ y k c).2 hyk
    have hφ : φ y = adjY Tag.D4 L ((CFSG.HardMathSupport.Lang.D4Three.d4Rho ^ ε) k) c := by
      show Θ (cf y) = adjY Tag.D4 L ((CFSG.HardMathSupport.Lang.D4Three.d4Rho ^ ε) k) c
      exact Subtype.ext hΘcf
    have hψ : ψ y = adjY Tag.D4 L ((CFSG.HardMathSupport.Lang.D4Three.d4Rho ^ ε) k) c := by
      show d4Graph L ε (Θ y) = adjY Tag.D4 L ((CFSG.HardMathSupport.Lang.D4Three.d4Rho ^ ε) k) c
      rw [show Θ y = adjY Tag.D4 L k c from Subtype.ext hΘy, d4Graph_adjY]
    rw [hφ, hψ]
  have hφψ : φ = ψ := ntpD4_hom_ext v Y hY Θ hΘ hx hyY
  have hmem : cf ⟨y, hy⟩ = ⟨nz * y * nz⁻¹, hy'⟩ := Subtype.ext (hcf ⟨y, hy⟩)
  have hfinal := DFunLike.congr_fun hφψ ⟨y, hy⟩
  change Θ (cf ⟨y, hy⟩) = d4Graph L ε (Θ ⟨y, hy⟩) at hfinal
  rw [hmem] at hfinal
  exact hfinal

end CFSG.StandardType.NTPlane
