module

public import CFSG.HardMathSupport.Timmesfeld.LangTorus.Defs
public import CFSG.Assembly.OrderReductions.InvertedSubgroup
public import CFSG.Assembly.OrderReductions.OddInversion
public import CFSG.Foundations
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcInnerTwReduction
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcInnerTwTorus
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcVacuous
public import CFSG.HardMathSupport.Timmesfeld.DefChar.LieOuterE
public import CFSG.HardMathSupport.Timmesfeld.LocalTwo.CrossLin
public import CFSG.LieType.Chevalley.C2E6SubsystemBruhat
public import CFSG.LieType.Ree.LargeReeEightTorus
public import CFSG.LieType.Ree.SmallReeModelSchreier
public import CFSG.LieType.Simplicity.Finiteness
public import CFSG.LocalAnalysis.ComponentInitial.SylowPointRecovery
public import CFSG.LocalAnalysis.SectionRank.EvenCover.Catalog
public import CFSG.LocalAnalysis.SectionRank.LargeRee.SuzukiData
public import CFSG.LocalAnalysis.SectionRank.OddCover.CatalogOdd
public import CFSG.LocalAnalysis.SectionRank.SectionAssemblyBase
public import CFSG.LocalAnalysis.SectionRank.Sporadic.J4LocalBase
public import CFSG.LocalAnalysis.SectionRank.Sporadic.MathieuLocalBase
public import CFSG.LocalAnalysis.SectionRank.TitsCover
public import CFSG.LocalAnalysis.ZStar.BrauerSylowFusion
public import CFSG.LocalAnalysis.ZStar.PrincipalBlockTraceApplication
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
public import CFSG.Sporadic.J4.Simple
public import CFSG.Sporadic.J4Base
public import CFSG.Sporadic.Mathieu.M12
public import CFSG.Sporadic.Mathieu.M24
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Isaacs.VII.lemma_7_7

public section

namespace CFSG.StandardType.TableCRes

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.HardMathSupport.Timmesfeld.LangTorus

theorem weyl_disc_step
    {τ : Tag} {Ψ : Set (Fin τ.rank → ℤ)} (hroot : ∀ γ ∈ Ψ, IsRoot τ γ)
    (hsl : ∀ γ ∈ Ψ, iform γ γ = 2) {d : ℤ} {γ : Fin τ.rank → ℤ} (hγ : γ ∈ Ψ)
    {y : WeylGroup τ}
    (hy : ∀ x : Fin τ.rank → ℤ, (∀ γ' ∈ Ψ, d ∣ iform x γ') →
      (∀ γ' ∈ Ψ, d ∣ iform (y • x) γ') ∧ ∃ v ∈ Submodule.span ℤ Ψ, y • x - x = d • v)
    (x : Fin τ.rank → ℤ) (hx : ∀ γ' ∈ Ψ, d ∣ iform x γ') :
    (∀ γ' ∈ Ψ, d ∣ iform ((rootReflection γ * y) • x) γ') ∧
      ∃ v ∈ Submodule.span ℤ Ψ, (rootReflection γ * y) • x - x = d • v := by
  obtain ⟨h1, v₂, hv₂, h2⟩ := hy x hx
  obtain ⟨k, hk0⟩ := h1 γ hγ
  have hk : iform γ (y • x) = d * k := by rw [iform_comm]; exact hk0
  have hcor : corootPair γ (y • x) = iform γ (y • x) := by
    unfold corootPair
    rw [hsl γ hγ, Int.mul_ediv_cancel_left _ (by norm_num)]
  have hrs : (rootReflection γ * y) • x = y • x - (d * k) • γ := by
    rw [mul_smul, rootReflection_smul (hroot γ hγ), hcor, hk]
  refine ⟨fun γ' hγ' => ?_, v₂ - k • γ,
    sub_mem hv₂ (Submodule.smul_mem _ _ (Submodule.subset_span hγ)), ?_⟩
  · rw [hrs, iform_sub_left, iform_smul_left]
    exact dvd_sub (h1 γ' hγ') (Dvd.dvd.mul_right (dvd_mul_right d k) _)
  · rw [hrs, smul_sub, smul_smul, ← h2]
    abel

theorem weyl_disc_invariant
    {τ : Tag} {Ψ : Set (Fin τ.rank → ℤ)} (hroot : ∀ γ ∈ Ψ, IsRoot τ γ)
    (hsl : ∀ γ ∈ Ψ, iform γ γ = 2) {d : ℤ} {w : WeylGroup τ}
    (hw : w ∈ Subgroup.closure {s : WeylGroup τ | ∃ γ ∈ Ψ, s = rootReflection γ})
    (x : Fin τ.rank → ℤ) (hx : ∀ γ ∈ Ψ, d ∣ iform x γ) :
    (∀ γ ∈ Ψ, d ∣ iform (w • x) γ) ∧ ∃ v ∈ Submodule.span ℤ Ψ, w • x - x = d • v := by
  induction hw using Subgroup.closure_induction_left generalizing x with
  | one => exact ⟨by simpa using hx, 0, zero_mem _, by simp⟩
  | mul_left s hs y hy ih =>
    obtain ⟨γ, hγ, rfl⟩ := hs
    exact weyl_disc_step hroot hsl hγ ih x hx
  | inv_mul_cancel s hs y hy ih =>
    obtain ⟨γ, hγ, rfl⟩ := hs
    rw [rootReflection_inv (hroot γ hγ)]
    exact weyl_disc_step hroot hsl hγ ih x hx

theorem not_twistInner_of_disc
    {τ : Tag} {Ψ : Set (Fin τ.rank → ℤ)} (hroot : ∀ γ ∈ Ψ, IsRoot τ γ)
    (hsl : ∀ γ ∈ Ψ, iform γ γ = 2) (σ : (Fin τ.rank → ℤ) →+ (Fin τ.rank → ℤ)) {d : ℤ}
    {μ ν : Fin τ.rank → ℤ} (hμ : μ ∈ Submodule.span ℤ Ψ) (hμd : ∀ γ ∈ Ψ, d ∣ iform μ γ)
    (hνd : ∀ γ ∈ Ψ, d ∣ iform ν γ) (hnd : ¬ d * d ∣ iform ν (σ μ - μ)) :
    ¬ twistInner Ψ (σ : (Fin τ.rank → ℤ) → (Fin τ.rank → ℤ)) := by
  rintro ⟨w, hw, hσ⟩
  obtain ⟨-, v, hv, hwv⟩ := weyl_disc_invariant hroot hsl hw μ hμd
  have hσμ : σ μ = w • μ := by
    refine Submodule.span_induction (p := fun z _ => σ z = w • z) ?_ ?_ ?_ ?_ hμ
    · intro z hz
      exact hσ z hz
    · simp
    · intro a b _ _ ha hb
      rw [map_add, smul_add, ha, hb]
    · intro a z _ hz
      rw [map_zsmul, smul_comm, hz]
  have hdv : d ∣ iform ν v := by
    refine Submodule.span_induction (p := fun z _ => d ∣ iform ν z) ?_ ?_ ?_ ?_ hv
    · intro z hz
      exact hνd z hz
    · have h0 : iform ν 0 = 0 := by
        simpa using iform_smul_right (0 : ℤ) ν 0
      show d ∣ iform ν 0
      rw [h0]
      exact dvd_zero d
    · intro a b _ _ ha hb
      rw [iform_add_right]
      exact dvd_add ha hb
    · intro a z _ hz
      rw [iform_smul_right]
      exact Dvd.dvd.mul_left hz a
  apply hnd
  rw [hσμ, hwv, iform_smul_right]
  exact mul_dvd_mul_left d hdv

end CFSG.StandardType.TableCRes

end
