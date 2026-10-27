module

public import CFSG.Open.StatedDefs
public import CFSG.ClassicalGroups.Orthogonal.NormalizerOmega
public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.LieType.Universal.Spin.Forms
public import CFSG.Quasithin.Background.FFC4Zmod
public import CFSG.Fischer.Uniq.CompTau
public import CFSG.LargeExtraspecial.OrthoF2
public import CFSG.LargeExtraspecial.S2Basic
public import CFSG.Quasithin.Background.B5FinOut
public import CFSG.Quasithin.Background.FFC4Real

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Open

theorem s16t3_omplus_isom {K : Type} [Field K] [Finite K] (hK : Nat.card K = 2) {m : ℕ}
    (hm : 3 ≤ m) {M : Matrix.GeneralLinearGroup (Fin m ⊕ Fin m) K}
    (hM : M ∈ Subgroup.normalizer (StatedOmega (StatedQuadPlus m K) :
      Set (Matrix.GeneralLinearGroup (Fin m ⊕ Fin m) K)))
    (v : Fin m ⊕ Fin m → K) :
    StatedQuadPlus m K (Matrix.mulVec (M : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) v) =
      StatedQuadPlus m K v := by
  let φ : K ≃+* ZMod 2 := CFSG.Quasithin.FFC.ringEquivZModTwo K hK
  let Φ : Matrix.GeneralLinearGroup (Fin m ⊕ Fin m) K ≃*
      Matrix.GeneralLinearGroup (Fin m ⊕ Fin m) (ZMod 2) :=
    CFSG.Adapters.RankTwoModelTransports.glCongr (ι := Fin m ⊕ Fin m) φ
  have hmap : (StatedOmega (StatedQuadPlus m K)).map Φ.toMonoidHom =
      StatedOmega (StatedQuadPlus m (ZMod 2)) :=
    CFSG.ClassicalInvolution.Upgrade.map_statedOmega φ
      (CFSG.ClassicalInvolution.Upgrade.statedQuadPlus_comp φ)
  have hM' : Φ M ∈ Subgroup.normalizer
      (StatedOmega (StatedQuadPlus m (ZMod 2)) :
        Set (Matrix.GeneralLinearGroup (Fin m ⊕ Fin m) (ZMod 2))) := by
    have hnorm := Subgroup.map_equiv_normalizer_eq (StatedOmega (StatedQuadPlus m K)) Φ
    rw [hmap] at hnorm
    rw [← hnorm]
    exact ⟨M, hM, rfl⟩
  have h6 : 6 ≤ Fintype.card (Fin m ⊕ Fin m) := by
    simp [Fintype.card_sum]
    omega
  have hpres : ∀ w : Fin m ⊕ Fin m → ZMod 2,
      StatedQuadPlus m (ZMod 2)
        (Matrix.mulVec (Φ M : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) (ZMod 2)) w) =
        StatedQuadPlus m (ZMod 2) w := by
    intro w
    exact CFSG.ClassicalGroups.Orthogonal.isometry_of_normalizes_statedOmega
      (Q := CFSG.LieType.Universal.Spin.quadPlus m (ZMod 2))
      (Q₀ := StatedQuadPlus m (ZMod 2))
      (CFSG.LieType.Universal.Spin.coe_quadPlus m (ZMod 2))
      (CFSG.LieType.Universal.Spin.nondegenerate_polarBilin_quadPlus m (ZMod 2))
      h6
      (fun x hx => (Subgroup.mem_set_normalizer_iff.mp hM' x).1 hx)
      w
  exact (CFSG.ClassicalInvolution.Upgrade.glCongr_preserves_iff φ
    (CFSG.ClassicalInvolution.Upgrade.statedQuadPlus_comp φ) M).1 hpres v

theorem s16t3_omminus_isom {K : Type} [Field K] [Finite K] (hK : Nat.card K = 2) {m : ℕ}
    (hm : 3 ≤ m) {b c : K} (hbc : ∀ s : K, s ^ 2 + b * s + c ≠ 0)
    {M : Matrix.GeneralLinearGroup (Fin (m - 1) ⊕ Fin (m - 1) ⊕ Fin 2) K}
    (hM : M ∈ Subgroup.normalizer (StatedOmega (StatedQuadMinus m K b c) :
      Set (Matrix.GeneralLinearGroup (Fin (m - 1) ⊕ Fin (m - 1) ⊕ Fin 2) K)))
    (v : Fin (m - 1) ⊕ Fin (m - 1) ⊕ Fin 2 → K) :
    StatedQuadMinus m K b c
        (Matrix.mulVec (M : Matrix (Fin (m - 1) ⊕ Fin (m - 1) ⊕ Fin 2)
          (Fin (m - 1) ⊕ Fin (m - 1) ⊕ Fin 2) K) v) =
      StatedQuadMinus m K b c v := by
  let φ : K ≃+* ZMod 2 := CFSG.Quasithin.FFC.ringEquivZModTwo K hK
  let Φ : Matrix.GeneralLinearGroup (Fin (m - 1) ⊕ Fin (m - 1) ⊕ Fin 2) K ≃*
      Matrix.GeneralLinearGroup (Fin (m - 1) ⊕ Fin (m - 1) ⊕ Fin 2) (ZMod 2) :=
    CFSG.Adapters.RankTwoModelTransports.glCongr
      (ι := Fin (m - 1) ⊕ Fin (m - 1) ⊕ Fin 2) φ
  have hmap : (StatedOmega (StatedQuadMinus m K b c)).map Φ.toMonoidHom =
      StatedOmega (StatedQuadMinus m (ZMod 2) (φ b) (φ c)) :=
    CFSG.ClassicalInvolution.Upgrade.map_statedOmega φ
      (CFSG.ClassicalInvolution.Upgrade.statedQuadMinus_comp φ rfl rfl)
  have hM' : Φ M ∈ Subgroup.normalizer
      (StatedOmega (StatedQuadMinus m (ZMod 2) (φ b) (φ c)) :
        Set (Matrix.GeneralLinearGroup (Fin (m - 1) ⊕ Fin (m - 1) ⊕ Fin 2) (ZMod 2))) := by
    have hnorm := Subgroup.map_equiv_normalizer_eq
      (StatedOmega (StatedQuadMinus m K b c)) Φ
    rw [hmap] at hnorm
    rw [← hnorm]
    exact ⟨M, hM, rfl⟩
  have h6 : 6 ≤ Fintype.card (Fin (m - 1) ⊕ Fin (m - 1) ⊕ Fin 2) := by
    simp [Fintype.card_sum]
    omega
  have hφ : ∀ s : ZMod 2, s ^ 2 + φ b * s + φ c ≠ 0 := by
    intro s
    obtain ⟨t, rfl⟩ := φ.surjective s
    have hval : φ t ^ 2 + φ b * φ t + φ c = φ (t ^ 2 + b * t + c) := by
      simp only [← map_pow, ← map_mul, ← map_add]
    rw [hval]
    intro h
    exact hbc t (φ.injective (by rw [h, map_zero]))
  have hpres : ∀ w : Fin (m - 1) ⊕ Fin (m - 1) ⊕ Fin 2 → ZMod 2,
      StatedQuadMinus m (ZMod 2) (φ b) (φ c)
        (Matrix.mulVec (Φ M : Matrix (Fin (m - 1) ⊕ Fin (m - 1) ⊕ Fin 2)
          (Fin (m - 1) ⊕ Fin (m - 1) ⊕ Fin 2) (ZMod 2)) w) =
        StatedQuadMinus m (ZMod 2) (φ b) (φ c) w := by
    intro w
    exact CFSG.ClassicalGroups.Orthogonal.isometry_of_normalizes_statedOmega
      (Q := CFSG.LieType.Universal.Spin.quadMinus m (ZMod 2) (φ b) (φ c))
      (Q₀ := StatedQuadMinus m (ZMod 2) (φ b) (φ c))
      (CFSG.LieType.Universal.Spin.coe_quadMinus m (ZMod 2) (φ b) (φ c))
      (CFSG.LieType.Universal.Spin.nondegenerate_polarBilin_quadMinus_of_finite
        m (ZMod 2) hφ)
      h6
      (fun x hx => (Subgroup.mem_set_normalizer_iff.mp hM' x).1 hx)
      w
  exact (CFSG.ClassicalInvolution.Upgrade.glCongr_preserves_iff φ
    (CFSG.ClassicalInvolution.Upgrade.statedQuadMinus_comp φ rfl rfl) M).1 hpres v

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
