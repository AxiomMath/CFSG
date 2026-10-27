module

public import CFSG.LocalAnalysis.StandardType.GGSecFivePhanNSADefs
import CFSG.ClassicalInvolution.Phan.Standard
import CFSG.ClassicalInvolution.Phan.Center
import CFSG.LocalAnalysis.StandardType.GGSecFiveKGPosBridge
import CFSG.LocalAnalysis.StandardType.GGSecFiveTier1OfPrim
import CFSG.LocalAnalysis.StandardType.GGSecFiveRankOneConj
import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyAut
import CFSG.LocalAnalysis.StandardType.GGSimplyLacedWeyl
import CFSG.LocalAnalysis.StandardType.GGSecFiveRankOneWeyl
import CFSG.LocalAnalysis.StandardType.GGSecFiveTier1Weyl
import CFSG.LieType.Universal.Unitary.Comparison
import CFSG.LieType.Steinberg.CentralExt.SUTwo

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Assembly.LowTwoRank CFSG.Blueprint CFSG.LieType.Universal CFSG.ClassicalInvolution.Phan
  CFSG.LieType.Universal.Unitary CFSG.LieType.BorelTits Matrix

open scoped MatrixGroups

theorem ggMUG1_block_eq (K : Type) [Field K] [Finite K] (p f m : ℕ)
    [Fact p.Prime] [CharP K p] (i : Fin m) :
    ggSuPairBlock K p f (m + 1) (blockIdx (i : ℕ) (by omega) (0 : Fin 2))
        (blockIdx (i : ℕ) (by omega) (1 : Fin 2)) =
      (blockEmb2 K p f m i).range := by
  rw [blockEmb2]
  apply le_antisymm
  ·
    intro A hA
    let Bm : Matrix (Fin 2) (Fin 2) K :=
      Matrix.of fun x y => (((A : GL (Fin (m + 1)) K)) : Matrix (Fin (m + 1)) (Fin (m + 1)) K)
        (blockIdx (i : ℕ) (by omega) x) (blockIdx (i : ℕ) (by omega) y)
    have hAmat : (((A : GL (Fin (m + 1)) K)) : Matrix (Fin (m + 1)) (Fin (m + 1)) K) =
        blockMat (m + 1) (i : ℕ) Bm := by
      ext x y
      rw [blockMat_apply]
      by_cases hxy : ((i : ℕ) ≤ (x : ℕ) ∧ (x : ℕ) < (i : ℕ) + 2) ∧
          ((i : ℕ) ≤ (y : ℕ) ∧ (y : ℕ) < (i : ℕ) + 2)
      · rw [dif_pos hxy]
        obtain ⟨⟨hix, hxi⟩, hyx, hyi⟩ := hxy
        simp only [Bm, Matrix.of_apply]
        refine congrArg₂ _ ?_ ?_
        · apply Fin.ext
          rw [blockIdx_val]
          show (x : ℕ) = (i : ℕ) + ((x : ℕ) - (i : ℕ))
          omega
        · apply Fin.ext
          rw [blockIdx_val]
          show (y : ℕ) = (i : ℕ) + ((y : ℕ) - (i : ℕ))
          omega
      · rw [dif_neg hxy]
        exact hA x y (by
          rcases not_and_or.mp hxy with hx | hy
          · left
            exact ⟨fun hx0 => hx (by rw [hx0, blockIdx_val]; omega),
              fun hx1 => hx (by rw [hx1, blockIdx_val]; omega)⟩
          · right
            exact ⟨fun hy0 => hy (by rw [hy0, blockIdx_val]; omega),
              fun hy1 => hy (by rw [hy1, blockIdx_val]; omega)⟩)
    have hBdet : Bm.det = 1 := by
      have h1 : (blockMat (m + 1) (i : ℕ) Bm).det = 1 := by rw [← hAmat]; exact A.2.1
      rwa [det_blockMat (by omega : (i : ℕ) + 2 ≤ m + 1)] at h1
    have hBiso : conjTr (unitaryInvolution K p f) Bm * Bm = 1 := by
      have h2 := A.2.2
      rw [hAmat, conjTr_blockMat,
        ← blockMat_mul (by omega : (i : ℕ) + 2 ≤ m + 1)] at h2
      rw [← blockMat_one (m := m + 1) (i := (i : ℕ)) (k := 2) (F := K)] at h2
      exact blockMat_injective (by omega : (i : ℕ) + 2 ≤ m + 1) h2
    let B : GL (Fin 2) K := Matrix.GeneralLinearGroup.mkOfDetNeZero Bm (by rw [hBdet]; norm_num)
    have hBval : (B : Matrix (Fin 2) (Fin 2) K) = Bm :=
      Matrix.GeneralLinearGroup.val_mkOfDetNeZero Bm _
    have hBmem : B ∈ SUid (unitaryInvolution K p f) 2 := by
      rw [mem_SUid, hBval]
      exact ⟨hBdet, hBiso⟩
    rw [MonoidHom.mem_range]
    refine ⟨⟨B, hBmem⟩, ?_⟩
    apply Subtype.ext
    apply Units.ext
    rw [coe_coe_blockEmb]
    simp only [Subtype.coe_mk]
    rw [hBval]
    exact hAmat.symm
  ·
    rintro A hA
    obtain ⟨B, rfl⟩ := MonoidHom.mem_range.mp hA
    intro x y hxy
    rw [coe_coe_blockEmb]
    rcases hxy with ⟨hx0, hx1⟩ | ⟨hy0, hy1⟩
    · refine blockMat_apply_of_not_mem_left _ ?_ y
      rintro ⟨h1, h2⟩
      have hx : (x : ℕ) = (i : ℕ) ∨ (x : ℕ) = (i : ℕ) + 1 := by omega
      rcases hx with hx | hx
      · exact hx0 (Fin.ext (by rw [blockIdx_val]; exact hx))
      · exact hx1 (Fin.ext (by rw [blockIdx_val]; exact hx))
    · refine blockMat_apply_of_not_mem_right _ x ?_
      rintro ⟨h1, h2⟩
      have hy : (y : ℕ) = (i : ℕ) ∨ (y : ℕ) = (i : ℕ) + 1 := by omega
      rcases hy with hy | hy
      · exact hy0 (Fin.ext (by rw [blockIdx_val]; exact hy))
      · exact hy1 (Fin.ext (by rw [blockIdx_val]; exact hy))

theorem ggMUG1_card_map (K : Type) [Field K] [Finite K] (p f m : ℕ)
    [Fact p.Prime] [CharP K p] {G : Type} [Group G] (ψ : Su K p f (m + 1) →* G)
    (hK : Nat.card K = (p ^ f) ^ 2) (hker : ψ.ker ≤ Subgroup.center (Su K p f (m + 1)))
    (hm : 3 ≤ m + 1) (i : Fin m) :
    Nat.card ((ggSuPairBlock K p f (m + 1) (blockIdx (i : ℕ) (by omega) (0 : Fin 2))
        (blockIdx (i : ℕ) (by omega) (1 : Fin 2))).map ψ) = Nat.card (Su K p f 2) := by
  rw [ggMUG1_block_eq K p f m i, blockEmb2]
  rw [MonoidHom.map_range ψ (blockEmb K p f (m + 1) 2 (i : ℕ)
    (by omega : (i : ℕ) + 2 ≤ m + 1))]
  rw [MonoidHom.range_eq_map (ψ.comp (blockEmb K p f (m + 1) 2 (i : ℕ)
    (by omega : (i : ℕ) + 2 ≤ m + 1)))]
  have hinj : Function.Injective (ψ.comp (blockEmb K p f (m + 1) 2 (i : ℕ)
      (by omega : (i : ℕ) + 2 ≤ m + 1))) :=
    comp_blockEmb_injective hK hker (by omega) (by omega) (by omega)
  rw [Subgroup.card_map_of_injective (K := ⊤) hinj]
  simp

theorem ggMUG1_card_su_two (K : Type) [Field K] [Finite K] (p f : ℕ)
    [Fact p.Prime] [CharP K p] (hK : Nat.card K = (p ^ f) ^ 2) :
    Nat.card (Su K p f 2) = p ^ f * ((p ^ f) ^ 2 - 1) := by
  obtain ⟨P, hP⟩ := exists_wittMatrix (F := K) (p := p) (f := f) hK 2
  rw [← Nat.card_congr (conjEquiv P hP).toEquiv]
  exact CFSG.LieType.Steinberg.card_SU_two hK

end CFSG.StandardType

end
