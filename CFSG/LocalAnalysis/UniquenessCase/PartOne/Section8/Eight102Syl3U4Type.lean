module

public import CFSG.ClassicalGroups.UnitaryFlag.HyperbolicData
import CFSG.LocalAnalysis.RankFourTheoremC.InvariantTwo.KFacts.Lemma212InputsProofAutSU

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Syl3

open Matrix CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial

variable {p f : ℕ} {K : Type} [Field K]

private theorem det_conj_map_sub_one_eq_zero_iff {ι : Type} [Fintype ι] [DecidableEq ι]
    (σ : K ≃+* K) (A : GL ι K) (M : Matrix ι ι K) :
    (((A : Matrix ι ι K) * M.map σ * ((A⁻¹ : GL ι K) : Matrix ι ι K)) - 1).det = 0 ↔
      (M - 1).det = 0 := by
  have hmap : (M - 1).map σ = M.map σ - 1 := by
    rw [Matrix.map_sub _ (map_sub σ), Matrix.map_one σ (map_zero σ) (map_one σ)]
  have hsub : (A : Matrix ι ι K) * M.map σ * ((A⁻¹ : GL ι K) : Matrix ι ι K) - 1 =
      (A : Matrix ι ι K) * ((M - 1).map σ) * ((A⁻¹ : GL ι K) : Matrix ι ι K) := by
    rw [hmap, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one]
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hdet : ((M - 1).map σ).det = σ ((M - 1).det) := by
    rw [← RingEquiv.mapMatrix_apply, ← RingEquiv.map_det]
  rw [hsub, Matrix.det_units_conj, hdet]
  exact map_eq_zero_iff σ σ.injective

theorem det_sub_one_map_eq_zero_iff (h : UnitaryFieldData p f K) {m ε : ℕ} (hm : 2 ≤ m)
    (hε : ε ≤ 1) (hZ : hypScalars h m ε = ⊥) (α : MulAut (hypSU h m ε)) (g : hypSU h m ε) :
    ((((α g : hypSU h m ε) : GL (HypIndex m ε) K) : Matrix (HypIndex m ε) (HypIndex m ε) K) -
        1).det = 0 ↔
      (((g : GL (HypIndex m ε) K) : Matrix (HypIndex m ε) (HypIndex m ε) K) - 1).det = 0 := by
  have hker : (hypProj h m ε).ker = ⊥ := by rw [ker_hypProj, hZ]
  have hinj : Function.Injective (hypProj h m ε) := (MonoidHom.ker_eq_bot_iff _).1 hker
  let π : hypSU h m ε ≃* hypPSU h m ε :=
    MulEquiv.ofBijective (hypProj h m ε) ⟨hinj, hypProj_surjective h m ε⟩
  let α' : MulAut (hypPSU h m ε) := (π.symm.trans α).trans π
  have hα' (x : hypSU h m ε) : α' (π x) = π (α x) := by
    simp [α']
  obtain ⟨σ, A, -, hA⟩ :=
    CFSG.LocalAnalysis.RankFourTheoremC.AutSU.exists_isometry_hypPSU_of_two_le h hm hε α'
  obtain ⟨hg, hgα⟩ := hA g
  have hmat : (((α g : hypSU h m ε) : GL (HypIndex m ε) K) :
        Matrix (HypIndex m ε) (HypIndex m ε) K) =
      (A : Matrix (HypIndex m ε) (HypIndex m ε) K) *
        (((g : GL (HypIndex m ε) K) : Matrix (HypIndex m ε) (HypIndex m ε) K).map σ) *
        ((A⁻¹ : GL (HypIndex m ε) K) : Matrix (HypIndex m ε) (HypIndex m ε) K) := by
    have h := congrArg (fun x : hypSU h m ε =>
      (((x : GL (HypIndex m ε) K) : Matrix (HypIndex m ε) (HypIndex m ε) K)))
      (π.injective ((hα' g).symm.trans hgα))
    simpa only [Subtype.coe_mk, Units.val_mul,
      CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.coe_glAut] using h
  rw [hmat]
  exact det_conj_map_sub_one_eq_zero_iff σ A _

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Syl3
