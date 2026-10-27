module

public import CFSG.RankThree.PartTwo.Sec4.LThreePiProjFieldB

public section

namespace CFSG.RankThree.PartTwo.Sec13.Ronan138S

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.LocalAnalysis.ComponentInitial CFSG.Assembly.LowTwoRank
open CFSG.Assembly.RankThreeEven (projImage)
open CFSG.RankThree.PartTwo.Sec4


theorem forall_isPGLAtP_of_card_eq {G : Type} [Group G] [Finite G] {L : Subgroup G} [L.Normal]
    {π : Bool} {p f : ℕ} {K : Type} [Field K] (hK : Sec4.PiField π p f K)
    (hq : Sec4.ModThree π (p ^ f)) (hq2 : 2 < p ^ f) (hLq : CFSG.IsQuasisimple L)
    (e : L ≃* CFSG.Assembly.RankThreeEven.projImage (Sec4.slPi π 3 (p ^ f) K))
    {A : Subgroup G} (hA : Maximal (fun B : Subgroup G => CFSG.Assembly.IsElemAbelian 3 B) A)
    (hA27 : Nat.card A = 27) {c : G} (hc3 : orderOf c = 3)
    (hAc : A ⊓ Subgroup.centralizer (L : Set G) = Subgroup.zpowers c) :
    ∀ a ∈ A, ∃ y, Sec4.IsPGLAtP e a y := by
  have : Group.IsPerfect L := hLq.1
  have := isPerfect_projImage_of_equiv e
  have hθ := aschbacherSolvableCore_eq_bot_proj hK hq hLq e
  have hπ : π = false → UnitaryFieldData p f K := fun h => by subst h; exact hK.unitary
  by_cases hpgl : ∀ a ∈ A, ∃ y, IsPGLAtP e a y
  · exact hpgl
  obtain ⟨σ, hσA, hσ⟩ : ∃ σ ∈ A, ∀ y, ¬ IsPGLAtP e σ y := by
    by_contra h
    exact hpgl fun a ha => by
      by_contra h'
      exact h ⟨a, ha, fun y hy => h' ⟨y, hy⟩⟩
  have hσ3 : (⟨σ, mem_normalizer_of_normal σ⟩ : Subgroup.normalizer (L : Set G)) ^ 3 = 1 :=
    Subtype.ext (by rw [Subgroup.coe_pow]; exact hA.1.2 σ hσA)
  rcases pslAct_pgl_or_field hK hq2 hθ e _ hσ3 with ⟨y, hy, hys⟩ |
    ⟨-, f₀, hf, ψ, hψpow, g, hg, hσg⟩
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
  have hAL3 : Nat.card (A ⊓ L : Subgroup G) = 3 := by omega
  exact (false_of_field_three hK hq hf hφ hφ3 hψ hA hAc he' hAeq hfixB hAL3).elim

end CFSG.RankThree.PartTwo.Sec13.Ronan138S
