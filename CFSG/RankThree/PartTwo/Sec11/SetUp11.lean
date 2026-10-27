module

public import CFSG.RankThree.PartTwo.Sec11.Item112
public import CFSG.RankThree.PartTwo.Sec11.Statements

public section

namespace CFSG.RankThree.PartTwo.Sec11

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem exists_zpowers_eq_inf {A : Subgroup G} {L : Subgroup G}
    (h3 : Nat.card (A ⊓ L : Subgroup G) = 3) : ∃ d : G, A ⊓ L = Subgroup.zpowers d := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hcyc : IsCyclic (A ⊓ L : Subgroup G) := isCyclic_of_prime_card h3
  obtain ⟨⟨d, hdmem⟩, hgen⟩ := IsCyclic.exists_generator (α := (A ⊓ L : Subgroup G))
  refine ⟨d, le_antisymm (fun y hy => ?_) (Subgroup.zpowers_le.mpr hdmem)⟩
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp (hgen ⟨y, hy⟩)
  refine Subgroup.mem_zpowers_iff.mpr ⟨k, ?_⟩
  have := congrArg Subtype.val hk
  simpa using this

theorem a_not_mem_closure_of_hyp91 {A : Subgroup G} {c : G} {L : Subgroup G} {a : G}
    {R : Subgroup G} (h : Sec9.Hyp91 G A c L a R) {d : G} (hdA : d ∈ A)
    (hA : A = Subgroup.closure {c, a, d}) : a ∉ Subgroup.closure ({c, d} : Set G) := by
  have hAe := h.mem_partTwoF.1
  have hexp : ∀ y ∈ A, y ^ 3 = 1 := hAe.2
  have hcomm : ∀ y ∈ A, ∀ z ∈ A, y * z = z * y := fun y hy z hz =>
    congrArg Subtype.val (hAe.1.is_comm.comm ⟨y, hy⟩ ⟨z, hz⟩)
  have hcA := h.mem_A
  intro hacd
  have hle : A ≤ Subgroup.closure ({c, d} : Set G) := by
    rw [hA, Subgroup.closure_le]
    intro y hy
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
    rcases hy with rfl | rfl | rfl
    · exact Subgroup.subset_closure (by simp)
    · exact hacd
    · exact Subgroup.subset_closure (by simp)
  have h1 := Subgroup.card_le_of_le hle
  have h2 := Sec10.card_closure_pair_le (hcomm c hcA d hdA) (hexp c hcA) (hexp d hdA)
  rw [h.card_eq] at h1
  omega

theorem setUp11_of (h97 : Sec9.Item97) (h45 : Sec4.Item4_5) (h48 : Sec4.Item4_8) : SetUp11 := by
  intro G _ _ A c L a R h hl
  obtain ⟨h3, hd⟩ := h97 G A c L a R h
  obtain ⟨d, hdL⟩ := exists_zpowers_eq_inf h3
  have hA := hd d hdL
  have hdA : d ∈ A := by
    have : d ∈ A ⊓ L := by
      rw [hdL]
      exact Subgroup.mem_zpowers d
    exact this.1
  exact exists_mem_thetaComponentsAt_sec11K_le_hyp91 h45 h48 h hl hdL hA h.a_mem
    (a_not_mem_closure_of_hyp91 h hdA hA)

end CFSG.RankThree.PartTwo.Sec11
