module

public import CFSG.Adapters.RankTwoModelTransports
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenKNormSp
public import CFSG.Open.StatedDefs
public import CFSG.Quasithin.Background.FFC4Zmod
public import CFSG.Quasithin.Background.B5FinOut
public import CFSG.Quasithin.Background.FFC4Real

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Open

theorem s16t3_sp_self_norm {K : Type} [Field K] [Finite K] (hK : Nat.card K = 2) (m : ℕ)
    {M : Matrix.GeneralLinearGroup (Fin m ⊕ Fin m) K}
    (hM : M ∈ Subgroup.normalizer
      (StatedSp m K : Set (Matrix.GeneralLinearGroup (Fin m ⊕ Fin m) K))) :
    M ∈ StatedSp m K := by
  let φ : K ≃+* ZMod 2 := CFSG.Quasithin.FFC.ringEquivZModTwo K hK
  let Φ : Matrix.GeneralLinearGroup (Fin m ⊕ Fin m) K ≃*
      Matrix.GeneralLinearGroup (Fin m ⊕ Fin m) (ZMod 2) :=
    CFSG.Adapters.RankTwoModelTransports.glCongr (ι := Fin m ⊕ Fin m) φ
  have hSp : (StatedSp m K).map Φ.toMonoidHom = StatedSp m (ZMod 2) :=
    CFSG.Adapters.RankTwoModelTransports.glCongr_statedSp (φ := φ) m
  have hnorm : ∀ g ∈ StatedSp m (ZMod 2), Φ M * g * (Φ M)⁻¹ ∈ StatedSp m (ZMod 2) := by
    intro g hg
    have hg' : Φ.symm g ∈ StatedSp m K :=
      Subgroup.mem_map_equiv.mp (hSp.symm ▸ hg)
    have hconj : M * Φ.symm g * M⁻¹ ∈ StatedSp m K :=
      (Subgroup.mem_set_normalizer_iff.mp hM) (Φ.symm g) |>.mp hg'
    rw [← hSp, Subgroup.mem_map_equiv]
    simpa using hconj
  have hmem : Φ M ∈ StatedSp m (ZMod 2) := s15k_norm_sp_zmod2 m (Φ M) hnorm
  rw [← hSp, Subgroup.mem_map_equiv] at hmem
  simpa using hmem

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
