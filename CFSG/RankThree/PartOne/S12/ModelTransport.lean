module

public import CFSG.Assembly.LowTwoRankDefs
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.Open.StatedAPI
import CFSG.Adapters.LinearFieldTransport
import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
import CFSG.Open.PGLModelStated

public section

namespace CFSG.RankThree.PartOne

open Matrix CFSG.Assembly.LowTwoRank
open CFSG.Assembly.RankThreeEven (projImage projSL projSU projSp projOmegaMinus)
open CFSG.Adapters.RankTwoModelTransports
  (glCongr glCongr_statedScalars glCongr_statedSU statedProjCongr statedProjEquivMapMk)
open CFSG.ClassicalInvolution.Upgrade
  (glCongr_statedSL glCongr_statedSp map_statedOmega statedQuadMinus_comp irreducible_map)

noncomputable def statedProjEquivOfGLEquiv {ι : Type} [Fintype ι] [DecidableEq ι] {K L : Type}
    [Field K] [Field L] (Φ : GL ι K ≃* GL ι L) {H : Subgroup (GL ι K)}
    {H' : Subgroup (GL ι L)} {P : Subgroup (ProjGenLinGroup ι L)}
    (hH : H.map Φ.toMonoidHom = H')
    (hZ : (StatedScalars ι K).map Φ.toMonoidHom = StatedScalars ι L) (hP : projImage H' = P) :
    StatedProj H ≃* P :=
  (statedProjCongr Φ hH hZ).trans ((statedProjEquivMapMk H').trans (MulEquiv.subgroupCongr hP))

theorem statedSL_eq_det_ker (n : ℕ) (K : Type) [Field K] :
    StatedSL n K = (GeneralLinearGroup.det : GL (Fin n) K →* Kˣ).ker :=
  CFSG.Open.StatedAPI.statedSL_eq_ker_det n K

theorem projImage_statedSL_eq_projSL (n : ℕ) (K : Type) [Field K] :
    projImage (StatedSL n K) = projSL n K :=
  CFSG.PGLModel.projImage_statedSL n K

theorem statedSU_eq_closure_det (n q : ℕ) (K : Type) [Field K] :
    StatedSU n q K = Subgroup.closure {A : GL (Fin n) K | GeneralLinearGroup.det A = 1 ∧
      ((A : Matrix (Fin n) (Fin n) K).map (· ^ q))ᵀ * (A : Matrix (Fin n) (Fin n) K) = 1} :=
  CFSG.PGLModel.statedSU_eq_closure_det n q K

theorem projImage_statedSU_eq_projSU (n p f : ℕ) [Fact p.Prime] :
    projImage (StatedSU n (p ^ f) (GaloisField p (2 * f))) = projSU n p f :=
  CFSG.PGLModel.projImage_statedSU n p f

theorem projImage_statedSp_eq_projSp (n : ℕ) (K : Type) [Field K] :
    projImage (StatedSp n K) = projSp n K :=
  CFSG.PGLModel.projImage_statedSp n K

theorem projImage_statedOmegaMinus_eq_projOmegaMinus (n : ℕ) (K : Type) [Field K] (b c : K) :
    projImage (StatedOmega (StatedQuadMinus n K b c)) = projOmegaMinus (n - 1) K b c :=
  CFSG.PGLModel.projImage_statedOmegaMinus n K b c

theorem projSL_of_statedClassicalModel {G : Type} [Group G] {n f : ℕ}
    (h : StatedClassicalModel G .PSL n 2 f) :
    Nonempty (G ≃* projSL n (GaloisField 2 f)) := by
  obtain ⟨hadm, K, _, _, hK, ⟨e⟩⟩ := h
  have hf : 0 < f := hadm.2.1
  let φ : K ≃+* GaloisField 2 f := CFSG.ClassicalModels.finiteFieldEquivGaloisField K 2 f hf hK
  exact ⟨e.trans (statedProjEquivOfGLEquiv (glCongr φ) (glCongr_statedSL φ n)
    (glCongr_statedScalars φ) (projImage_statedSL_eq_projSL n _))⟩

theorem projSp_of_statedClassicalModel {G : Type} [Group G] {n f : ℕ}
    (h : StatedClassicalModel G .PSp n 2 f) :
    Nonempty (G ≃* projSp n (GaloisField 2 f)) := by
  obtain ⟨hadm, K, _, _, hK, ⟨e⟩⟩ := h
  have hf : 0 < f := hadm.2.1
  let φ : K ≃+* GaloisField 2 f := CFSG.ClassicalModels.finiteFieldEquivGaloisField K 2 f hf hK
  exact ⟨e.trans (statedProjEquivOfGLEquiv (glCongr φ) (glCongr_statedSp φ n)
    (glCongr_statedScalars φ) (projImage_statedSp_eq_projSp n _))⟩

theorem projSU_of_statedClassicalModel {G : Type} [Group G] {n f : ℕ}
    (h : StatedClassicalModel G .PSU n 2 f) :
    Nonempty (G ≃* projSU n 2 f) := by
  obtain ⟨hadm, K, _, _, hK, ⟨e⟩⟩ := h
  have hf1 : 1 ≤ f := hadm.2.1
  have hf : 0 < 2 * f := by omega
  have hK' : Nat.card K = 2 ^ (2 * f) := by rw [hK, ← pow_mul, mul_comm]
  let φ : K ≃+* GaloisField 2 (2 * f) :=
    CFSG.ClassicalModels.finiteFieldEquivGaloisField K 2 (2 * f) hf hK'
  exact ⟨e.trans (statedProjEquivOfGLEquiv (glCongr φ) (glCongr_statedSU φ n (2 ^ f))
    (glCongr_statedScalars φ) (projImage_statedSU_eq_projSU n 2 f))⟩

theorem projOmegaMinus_of_statedClassicalModel {G : Type} [Group G] {n f : ℕ}
    (h : StatedClassicalModel G .POmegaMinus n 2 f) :
    ∃ b c : GaloisField 2 f, (∀ s : GaloisField 2 f, s ^ 2 + b * s + c ≠ 0) ∧
      Nonempty (G ≃* projOmegaMinus (n - 1) (GaloisField 2 f) b c) := by
  obtain ⟨hadm, K, _, _, hK, b, c, hirr, ⟨e⟩⟩ := h
  have hf : 0 < f := hadm.2.1
  let φ : K ≃+* GaloisField 2 f := CFSG.ClassicalModels.finiteFieldEquivGaloisField K 2 f hf hK
  have hΩ := map_statedOmega φ (statedQuadMinus_comp (n := n) (b := b) (c := c) φ rfl rfl)
  exact ⟨φ b, φ c, irreducible_map φ hirr, ⟨e.trans (statedProjEquivOfGLEquiv (glCongr φ) hΩ
    (glCongr_statedScalars φ) (projImage_statedOmegaMinus_eq_projOmegaMinus n _ (φ b) (φ c)))⟩⟩

end CFSG.RankThree.PartOne
