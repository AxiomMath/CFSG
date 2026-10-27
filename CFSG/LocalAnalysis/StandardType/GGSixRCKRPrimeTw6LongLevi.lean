module

public import CFSG.HardMathSupport.Timmesfeld.LangTorus.Defs
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.InnerQuasisimpleRankOne
public import CFSG.RankThree.Chevalley.SteinbergBIRootSL2Tools
public import CFSG.LieType.Chevalley.CoordinateFieldFixedSubgroup
public import CFSG.LieType.Steinberg.Exceptional.Fields
public import CFSG.LocalAnalysis.StandardType.GGSecFiveKGPosDefs
public import CFSG.LocalAnalysis.StandardType.GGInterfaceDefs
import CFSG.LocalAnalysis.SeitzReduction.E6PilotLeviBaseChange
public import CFSG.Sporadic.ThSchreier.GlobalData
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcInnerTwReduction
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcInnerTwTorus
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcVacuous
public import CFSG.HardMathSupport.Timmesfeld.DefChar.LieOuterE
public import CFSG.HardMathSupport.Timmesfeld.LocalTwo.CrossLin
public import CFSG.LieType.Chevalley.C2E6SubsystemBruhat
public import CFSG.LieType.Ree.LargeReeEightTorus
public import CFSG.LieType.Ree.SmallReeModelSchreier
public import CFSG.LocalAnalysis.SectionRank.EvenCover.Catalog
public import CFSG.LocalAnalysis.SectionRank.LargeRee.SuzukiData
public import CFSG.LocalAnalysis.SectionRank.OddCover.CatalogOdd
public import CFSG.LocalAnalysis.SectionRank.SectionAssemblyBase
public import CFSG.LocalAnalysis.SectionRank.Sporadic.J4LocalBase
public import CFSG.LocalAnalysis.SectionRank.Sporadic.MathieuLocalBase
public import CFSG.LocalAnalysis.SectionRank.TitsCover
public import CFSG.Monster.B.Geometry.CoxeterWords
public import CFSG.Quasithin.Background.A3Components
public import CFSG.Quasithin.Background.A3ComponentsAmbient
public import CFSG.Quasithin.Background.A3Structure36BAction
public import CFSG.Quasithin.Background.A3Structure36BBasic
public import CFSG.Quasithin.Background.A3Structure36BPrime
public import CFSG.RankThree.Lattice.SteinbergBIOrbitQuotFull
public import CFSG.RankThree.PartOne.KE.A1SL2
public import CFSG.RankThree.PartOne.KE.A1Torus
public import CFSG.RankThree.PartOne.KE.A2Family
public import CFSG.RankThree.PartOne.KE.A2Shape
public import CFSG.RankThree.PartOne.KE.SigmaUntwisted
public import CFSG.RankThree.PartOne.KLR.Master
public import CFSG.RankThree.PartOne.KLR.SectorAssembly
public import CFSG.RankThree.PartOne.S8.Statements
public import CFSG.Sporadic.ThSchreier.LocalOrbitBase1

public section

namespace CFSG.StandardType.RCKRP

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.Chevalley
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.LieType.Steinberg.Exceptional



theorem rckRootSpan_conj_inf_step_eq {τ : Tag} {Ω : Type} [Field Ω] [IsAlgClosed Ω] {p₀ : ℕ}
    (S : LangSetup τ Ω p₀) (σ : Ω ≃+* Ω) (z : ModGL τ Ω) {γ : Fin τ.rank → ℤ}
    (hγ : IsRoot τ γ)
    (hstep : ∀ g ∈ rootSpan τ Ω ({γ, -γ} : Set (Fin τ.rank → ℤ)),
      S.D.step (z * g * z⁻¹) = z * frobGL σ g * z⁻¹) :
    (rootSpan τ Ω ({γ, -γ} : Set (Fin τ.rank → ℤ))).map (MulAut.conj z).toMonoidHom ⊓
        S.D.step.eqLocus (MonoidHom.id _) =
      ((rootSL2 τ (fixSubfield σ) γ).range.map (baseChangeGL (fixSubfield σ).subtype)).map
        (MulAut.conj z).toMonoidHom := by
  have hspan : rootSpan τ Ω ({γ, -γ} : Set (Fin τ.rank → ℤ)) = (rootSL2 τ Ω γ).range := by
    rw [range_rootSL2_of_isRoot hγ, rootSpan, iSup_insert, iSup_singleton]
  have hfixA : ∀ A : SL2 Ω, z * rootSL2 τ Ω γ A * z⁻¹ ∈ S.D.step.eqLocus (MonoidHom.id _) ↔
      Matrix.SpecialLinearGroup.map σ.toRingHom A = A := by
    intro A
    change S.D.step (z * rootSL2 τ Ω γ A * z⁻¹) = z * rootSL2 τ Ω γ A * z⁻¹ ↔ _
    rw [hstep _ (by rw [hspan]; exact ⟨A, rfl⟩), frobGL_rootSL2 σ hγ, mul_left_inj, mul_right_inj]
    exact (rootSL2_injective_of_field γ).eq_iff
  rw [hspan]
  apply le_antisymm
  · rintro _ ⟨⟨_, ⟨A, rfl⟩, rfl⟩, hfix⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at hfix ⊢
    obtain ⟨B, hB⟩ := CFSG.SeitzReduction.E6Pilot.exists_specialLinearGroup_map_eq_of_map_eq
      (fixSubfield σ).subtype σ.toRingHom (fun c => ⟨fun hc => ⟨⟨c, hc⟩, rfl⟩,
        by rintro ⟨d, rfl⟩; exact d.2⟩) A ((hfixA A).1 hfix)
    refine ⟨baseChangeGL (fixSubfield σ).subtype (rootSL2 τ (fixSubfield σ) γ B),
      ⟨rootSL2 τ (fixSubfield σ) γ B, ⟨B, rfl⟩, rfl⟩, ?_⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    rw [baseChangeGL_rootSL2_of_field, hB]
  · rintro _ ⟨_, ⟨_, ⟨B, rfl⟩, rfl⟩, rfl⟩
    rw [baseChangeGL_rootSL2_of_field]
    refine ⟨⟨_, ⟨_, rfl⟩, rfl⟩, ?_⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    apply (hfixA _).2
    ext i k
    simp only [Matrix.SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply, Matrix.map_apply]
    exact ((B : Matrix (Fin 2) (Fin 2) (fixSubfield σ)) i k).2

theorem rckTw6_longLevi_fixed_image
    {K : Type} [Field K] [Finite K] [CharP K 2] {q : ℕ}
    (S : LangSetup .E7 (AlgebraicClosure K) 5)
    (phi : twistedE6Group 2 q →* ModGL .E7 (AlgebraicClosure K))
    (sigma : AlgebraicClosure K ≃+* AlgebraicClosure K)
    (z : ModGL .E7 (AlgebraicClosure K))
    (gamma : Fin Tag.E7.rank → ℤ) (hgamma : IsRoot .E7 gamma)
    (hstep : ∀ g ∈ rootSpan .E7 (AlgebraicClosure K)
      ({gamma, -gamma} : Set (Fin Tag.E7.rank → ℤ)),
      S.D.step (z * g * z⁻¹) = z * frobGL sigma g * z⁻¹)
    (hpos : ((twistedE6Datum 2 q).rootGroup (Pi.single (0 : Fin 4) 1)).map phi =
      ((rootSubgroup .E7 ↥(fixSubfield sigma) gamma).map
        (baseChangeGL (fixSubfield sigma).subtype)).map (MulAut.conj z).toMonoidHom)
    (hneg : ((twistedE6Datum 2 q).rootGroup (-Pi.single (0 : Fin 4) 1)).map phi =
      ((rootSubgroup .E7 ↥(fixSubfield sigma) (-gamma)).map
        (baseChangeGL (fixSubfield sigma).subtype)).map (MulAut.conj z).toMonoidHom) :
    (ggRootLevi (ggU .twistedE6 0 q).D (Pi.single (0 : Fin 4) 1)).map phi =
      (rootSpan .E7 (AlgebraicClosure K) {gamma, -gamma}).map
        (MulAut.conj z).toMonoidHom ⊓ S.D.step.eqLocus (MonoidHom.id _) := by
  rw [rckRootSpan_conj_inf_step_eq S sigma z hgamma hstep, range_rootSL2_of_isRoot hgamma,
    Subgroup.map_sup, Subgroup.map_sup, ← hpos, ← hneg, ← Subgroup.map_sup]
  rfl

end CFSG.StandardType.RCKRP

end
