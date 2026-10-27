module

public import CFSG.LocalAnalysis.UniquenessCase.UC22S2114E3R880
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight56Spine
import CFSG.LocalAnalysis.UniquenessCase.UC22S218Center
import CFSG.LocalAnalysis.UniquenessCase.UC22P21k
public import CFSG.LocalAnalysis.UniquenessCase.UC22S218NFour

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open Subgroup
open CFSG.Blueprint (LieModel)
open CFSG.RankThree.PartOne (IsStronglyPEmbedded)

variable {G : Type} [Group G] [Finite G]

section

theorem s21_14K2T_of_r885_r891 (hGA : GriessAllModelsStatement) {D : Data G}
    {Ch : Choice2011 G} (h885 : PartOne.Section8.R885 D) (h891 : F08.R891 D)
    (hU4 : S21_14K2TU4 D Ch) : S21_14K2T D Ch := by
  intro hH c L hL hChev hpow hex hk hn3 hn4 hB0 hfaith
  refine hU4 hH c L hL hChev hpow hex ?_ hk hn3 hn4 hB0 hfaith
  obtain ⟨f₀, hf₀, -, hsig⟩ := hex
  have hns : ¬ IsStronglyPEmbedded 3 D.M := fun h => by
    have h1 : D.k = 1 := by
      show CFSG.LocalAnalysis.RankThreeUC.kParam D.M = 1
      rw [CFSG.LocalAnalysis.RankThreeUC.kParam, if_pos h]
    omega
  have h5 : 5 ∉ D.sig := fun h5 => by
    have h5f : 5 ∣ 2 ^ f₀ - 1 :=
      (by norm_num : 5 ∣ 2 ^ 4 - 1).trans (Nat.pow_sub_one_dvd_pow_sub_one 2 hf₀)
    have h5f2 : 5 ∣ 2 ^ (2 * f₀) - 1 :=
      (by norm_num : 5 ∣ 2 ^ 4 - 1).trans (Nat.pow_sub_one_dvd_pow_sub_one 2 (hf₀.mul_left 2))
    have h1 : 1 ≤ 2 ^ f₀ := Nat.one_le_two_pow
    have h2 : 2 ^ f₀ ≤ 2 ^ (2 * f₀) := Nat.pow_le_pow_right (by norm_num) (by omega)
    rcases hsig 5 h5 with h | ⟨-, h⟩ <;> omega
  have hl : ∀ P : Subgroup G, CFSG.ABGLocalTools.IsSylowOf 3 P D.M →
      F08.List880 (Bar2 L) → False := fun P hP hlist => h5 (by
    rw [(h885 L P ⟨hL, hlist, hns, hP⟩).2.1]
    exact Set.mem_singleton 5)
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨P, hP⟩ := CFSG.ABGLocalTools.exists_isSylowOf 3 D.M
  intro f hf
  refine ⟨fun hX => hl P hP ?_, fun hX => hl P hP ?_, fun hX => ?_⟩
  · unfold F08.List880
    iterate 13 right
    exact Or.inl ⟨f, uc22s218n_isSp4_bar2 hGA hL hX⟩
  · have hf2 : 2 ≤ f := by
      have := (CFSG.Blueprint.LieModel.admissible hX).2.1
      omega
    obtain ⟨e⟩ :=
      uc22p21k_barInf_equiv_of_center_bot hL.2.2 (center_bar2_eq_bot_of_isG2 hL hX (by omega))
    unfold F08.List880
    iterate 14 right
    exact Or.inl ⟨f, Or.inr ⟨hf2, CFSG.Blueprint.LieModel.of_mulEquiv e hX⟩⟩
  · obtain ⟨e⟩ :=
      uc22p21k_barInf_equiv_of_center_bot hL.2.2 (center_bar2_eq_bot_of_is3D4 hL hX)
    exact hns (h891 L hL f (CFSG.Blueprint.LieModel.of_mulEquiv e hX))

end

end CFSG.LocalAnalysis.UniquenessCase.UC22
