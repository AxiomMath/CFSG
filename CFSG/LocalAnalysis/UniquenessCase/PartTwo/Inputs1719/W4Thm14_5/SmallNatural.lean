module

public import CFSG.Quasithin.Background.SmithB45L2Class
public import CFSG.RankThree.GF2n.Tim81.Sec2.SL2Small
import CFSG.Quasithin.H13.VolIAltCoverUniversal
import CFSG.LocalAnalysis.UniquenessCase.UC22K147L2Br
public import CFSG.Blueprint.SourceClassicalTransport
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenDefs
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.Thm14_5

open CFSG.Quasithin CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22 Subgroup
open CFSG.QuasithinUnique.Setup.Layer CFSG.QuasithinUnique.Setup.SL2Modules
open CFSG.Quasithin.JonesParshall
open scoped MatrixGroups Matrix

variable {I : Type} [CommGroup I] {W : Type} [AddCommGroup W] [Module (ZMod 2) W]

theorem realizes_nat_of_equiv {ι : Type} [Fintype ι] [DecidableEq ι] {K : Type} [Field K]
    {Γ : Subgroup (Matrix.GeneralLinearGroup ι K)} (θ : I ≃* Multiplicative W)
    {L : Subgroup (MulAut I)} (Θ : ↥L ≃* ↥Γ) (ψ : W ≃+ (ι → K))
    (hψ : ∀ (l : ↥L) (w : W), ψ (binPsi θ (l : MulAut I) w) =
      ((Θ l : Matrix.GeneralLinearGroup ι K) : Matrix ι ι K) *ᵥ ψ w) :
    (FFModel.nat Γ).Realizes L ⊤ ⊥ := by
  refine CFSG.Quasithin.H13.VolI.realizes_of_mulEquiv (E := FFModel.nat Γ) rfl Θ.symm.toMonoidHom
    Θ.symm.surjective ((θ.trans (AddEquiv.toMultiplicative ψ)).trans Subgroup.topEquiv.symm) ?_
  intro (γ : ↥Γ) v
  show Multiplicative.ofAdd (ψ (Multiplicative.toAdd (θ (((Θ.symm γ : ↥L) : MulAut I) v)))) =
    Multiplicative.ofAdd (((γ : Matrix.GeneralLinearGroup ι K) : Matrix ι ι K) *ᵥ
      ψ (Multiplicative.toAdd (θ v)))
  rw [← B42L2.toAdd_binPsi, hψ, MulEquiv.apply_symm_apply]

theorem binaryNaturalSL_of_isNaturalModule {F : Type} [Field F] [Finite F] {n : ℕ}
    (hF : Nat.card F = 2 ^ n) (θ : I ≃* Multiplicative W) {L : Subgroup (MulAut I)}
    (φ : ↥L ≃* SL(2, F)) (h : IsNaturalModule (B45L2.repOf θ φ)) : BinaryNaturalSL L ⊤ ⊥ 2 n := by
  obtain ⟨ψ, hψ⟩ := h
  refine ⟨F, inferInstance, inferInstance, hF,
    realizes_nat_of_equiv θ (φ.trans (CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL 2 F))
      ψ fun l w => ?_⟩
  rw [← B45L2.repOf_theta θ φ l w, hψ]
  rfl

theorem natOmegaMinus_of_isOrthModule {F : Type} [Field F] [Fintype F] [CharP F 2] {a : ℕ}
    (ha : 1 ≤ a) (hF : Fintype.card F = 2 ^ (2 * a)) (θ : I ≃* Multiplicative W)
    {L : Subgroup (MulAut I)} (φ : ↥L ≃* SL(2, F))
    (h : CFSG.RankThree.GF2n.Tim81.Sec2.IsOrthModule hF (B45L2.repOf θ φ)) :
    NatOmegaMinus L ⊤ ⊥ 4 a := by
  obtain ⟨j, β, hβ⟩ := h
  obtain ⟨b, c, hbc, Θ, ψ, hψ⟩ := CFSG.LocalAnalysis.UniquenessCase.UC22.K147L2Br.omega_of_orth ha
    hF φ ((B45L2.repOf θ φ).comp φ.toMonoidHom) β j (fun k w => hβ (φ k) w)
  refine ⟨⟨2, rfl⟩, GaloisField 2 a, inferInstance, inferInstance, b, c,
    GaloisField.card 2 a (by omega), hbc, ?_⟩
  exact realizes_nat_of_equiv θ Θ ψ fun l w => by
    rw [← B45L2.repOf_theta θ φ l w]
    exact hψ l w

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.Thm14_5
