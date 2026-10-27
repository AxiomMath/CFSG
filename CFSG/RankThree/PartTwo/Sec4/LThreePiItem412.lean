module

public import CFSG.RankThree.PartTwo.Sec4.LThreePiProjFieldB

public section

namespace CFSG.RankThree.PartTwo.Sec4

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.LocalAnalysis.ComponentInitial CFSG.Assembly.LowTwoRank
open CFSG.Assembly.RankThreeEven (projImage)
open CFSG.RankThree.PartTwo.KFacts

theorem rank3II_4_12 :
    ∀ (G : Type) [Group G] [Finite G], SectionFourHyp G →
      ∀ L : Subgroup G, L.Normal →
      (∃ (p e : ℕ) (_ : Fact p.Prime), 1 ≤ e ∧ IsoLThreePi L p e) → CFSG.IsQuasisimple L →
      ∀ A : Subgroup G, Maximal (fun B : Subgroup G => CFSG.Assembly.IsElemAbelian 3 B) A →
        27 ≤ Nat.card A →
      ∀ c : G, orderOf c = 3 → A ⊓ Subgroup.centralizer (L : Set G) = Subgroup.zpowers c →
        Alt412 L A c := by
  intro G _ _ hG L hLn hL hLq A hA hA27 c hc3 hAc
  obtain ⟨p, ex, _, hex, hLiso⟩ := hL
  obtain ⟨π, K, _, hK, hq, hq2, ⟨e⟩⟩ := exists_pslPi_model hex hLiso hLq
  have : Group.IsPerfect L := hLq.1
  have := isPerfect_projImage_of_equiv e
  have hθ := aschbacherSolvableCore_eq_bot_proj hK hq hLq e
  have hπ : π = false → UnitaryFieldData p ex K := fun h => by subst h; exact hK.unitary
  have hAcomm : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (hA.1.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  by_cases hpgl : ∀ a ∈ A, ∃ y, IsPGLAtP e a y
  · exact alt412_of_pgl hK hq hθ e hA hA27 hc3 hAc hpgl
  obtain ⟨σ, hσA, hσ⟩ : ∃ σ ∈ A, ∀ y, ¬ IsPGLAtP e σ y := by
    by_contra h
    exact hpgl fun a ha => by
      by_contra h'
      exact h ⟨a, ha, fun y hy => h' ⟨y, hy⟩⟩
  have hσ3 : (⟨σ, mem_normalizer_of_normal σ⟩ : Subgroup.normalizer (L : Set G)) ^ 3 = 1 :=
    Subtype.ext (by rw [Subgroup.coe_pow]; exact hA.1.2 σ hσA)
  rcases pslAct_pgl_or_field hK hq2 hθ e _ hσ3 with ⟨y, hy, hys⟩ |
    ⟨hkind, f₀, hf, ψ, hψpow, g, hg, hσg⟩
  · exact absurd ⟨hy, hys⟩ (hσ y)
  obtain ⟨φ, hφ, hφ3⟩ := exists_frob hK hf
  have hψ := eq_or_eq_sq_of_pow hφ hψpow
  obtain ⟨e', he'⟩ := exists_normalized_fieldP hK hq hf hφ hφ3 hψ e (hA.1.2 σ hσA) hg hσg
  have hσB : σ ∉ L ⊔ Subgroup.centralizer (L : Set G) := by
    intro h
    obtain ⟨l, hl, u, hu, rfl⟩ := Subgroup.mem_sup_of_normal_left.mp h
    obtain ⟨s, hs, hse⟩ := Subgroup.mem_map.mp (e ⟨l, hl⟩).2
    exact hσ _ (isPGLAtP_mul e (isPGLAtP_of_mem e hπ hl hs hse.symm)
      (isPGLAtP_of_mem_centralizer e hu))
  obtain ⟨hfixB, hAeq, -, hcard⟩ :=
    fieldB_structureP hK hq hq2 hθ hf hφ hφ3 hψ e' hA hσA hσB he'
  have hLC := inf_centralizer_eq_bot_proj hK hq e'
  have hcardB := card_inf_sup_centralizer hA hLC hc3 hAc
  have hAL9 := card_inf_le_nine hK hq e' hA
  have hcAC : c ∈ A ⊓ Subgroup.centralizer (L : Set G) := hAc ▸ Subgroup.mem_zpowers c
  obtain ⟨hp2, hπ1⟩ := two_and_unitary_of_field hG hK hq hf hφ hψ e' (hA.1.2 σ hσA) hσB he' hc3
    hcAC.2 (hAcomm c hcAC.1 σ hσA)
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hP : IsPGroup 3 (A ⊓ L : Subgroup G) := fun x =>
    ⟨1, Subtype.ext (by rw [pow_one, Subgroup.coe_pow]; exact hA.1.2 _ (Subgroup.mem_inf.mp x.2).1)⟩
  obtain ⟨n, hn⟩ := hP.exists_card_eq
  have h1 : 3 ≤ 3 ^ n := by omega
  have h2 : 3 ^ n ≤ 3 ^ 2 := by omega
  have hn2 : n ≤ 2 := (Nat.pow_le_pow_iff_right (by norm_num)).mp h2
  have hn1 : 1 ≤ n := by
    by_contra h0
    rw [show n = 0 by omega, pow_zero] at h1
    omega
  interval_cases n
  · exact (false_of_field_three hK hq hf hφ hφ3 hψ hA hAc he' hAeq hfixB hn).elim
  · exact alt412_field_four hK hq hθ e' hA hc3 hAc hσA hkind hLiso hp2 hπ1 (by omega) hn

end CFSG.RankThree.PartTwo.Sec4
