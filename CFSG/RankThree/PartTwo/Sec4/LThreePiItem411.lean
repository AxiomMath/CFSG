module

public import CFSG.RankThree.PartTwo.Sec4.LThreePiFieldFour

public section

namespace CFSG.RankThree.PartTwo.Sec4

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.LocalAnalysis.ComponentInitial CFSG.Assembly.LowTwoRank
open CFSG.RankThree.PartTwo.KFacts

theorem rank3II_4_11 :
    ∀ (G : Type) [Group G] [Finite G], SectionFourHyp G →
      ∀ L : Subgroup G, L.Normal → IsSLThreePi L → CFSG.IsQuasisimple L →
      ∀ A : Subgroup G, Maximal (fun B : Subgroup G => CFSG.Assembly.IsElemAbelian 3 B) A →
        27 ≤ Nat.card A →
      ∀ c : G, orderOf c = 3 → A ⊓ Subgroup.centralizer (L : Set G) = Subgroup.zpowers c →
        Alt411 L A c := by
  intro G _ _ hG L hLn hL hLq A hA hA27 c hc3 hAc
  obtain ⟨π, p, f, K, _, hK, hq, hq2, ⟨e⟩⟩ := exists_slPi_model hL hLq
  have : Group.IsPerfect L := hLq.1
  have hθ := aschbacherSolvableCore_eq_bot_of_slPi hK hq hLq e
  have hπ : π = false → UnitaryFieldData p f K := fun h => by subst h; exact hK.unitary
  by_cases hpgl : ∀ a ∈ A, ∃ y, IsPGLAt e a y
  · exact alt411_of_pgl hK hq e hA hA27 hc3 hAc hpgl
  push Not at hpgl
  obtain ⟨σ, hσA, hσ⟩ := hpgl
  have hσ3 : (⟨σ, mem_normalizer_of_normal σ⟩ : Subgroup.normalizer (L : Set G)) ^ 3 = 1 :=
    Subtype.ext (by rw [Subgroup.coe_pow]; exact hA.1.2 σ hσA)
  rcases slAct_pgl_or_field hK hq2 hθ e _ hσ3 with ⟨y, hy, hys⟩ |
    ⟨hkind, f₀, hf, ψ, hψpow, g, hg, hσg⟩
  · exact absurd ⟨hy, hys⟩ (hσ y)
  obtain ⟨φ, hφ, hφ3⟩ := exists_frob hK hf
  have hψ := eq_or_eq_sq_of_pow hφ hψpow
  obtain ⟨e', he'⟩ := exists_normalized_field hK hq hf hφ hφ3 hψ e (hA.1.2 σ hσA) hg hσg
  have hσB : σ ∉ L ⊔ Subgroup.centralizer (L : Set G) := by
    intro h
    obtain ⟨l, hl, u, hu, rfl⟩ := Subgroup.mem_sup_of_normal_left.mp h
    exact hσ _ (isPGLAt_mul e (isPGLAt_of_mem e hπ hl) (isPGLAt_of_mem_centralizer e hu))
  obtain ⟨-, -, -, hcard, -, hle⟩ :=
    fieldB_structure hK hq hq2 hθ hf hφ hφ3 hψ e' hA hc3 hAc hσA hσB he'
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hAp : IsPGroup 3 A := fun x =>
    ⟨1, Subtype.ext (by rw [pow_one, Subgroup.coe_pow]; exact hA.1.2 x x.2)⟩
  obtain ⟨n, hn⟩ := hAp.exists_card_eq
  have hn3 : 3 ≤ n := by
    by_contra h
    have : 3 ^ n ≤ 3 ^ 2 := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  have hn4 : n ≤ 4 := by
    by_contra h
    have : 3 ^ 5 ≤ 3 ^ n := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  rcases (show n = 3 ∨ n = 4 by omega) with rfl | rfl
  · exact alt411_field_three hK hq hq2 hθ hf hφ hφ3 hψ e' hA hc3 hAc hσA hσB hkind he'
      (by rw [hn]; norm_num)
  · exact alt411_field_four hG hK hq hq2 hθ hf hφ hφ3 hψ e' hA hc3 hAc hσA hσB hkind he'
      (by rw [hn]; norm_num)

end CFSG.RankThree.PartTwo.Sec4
