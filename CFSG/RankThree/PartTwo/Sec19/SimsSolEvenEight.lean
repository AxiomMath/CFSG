module

public import CFSG.RankThree.PartTwo.Sec19.SimsSolEvenEightFus
public import CFSG.RankThree.PartTwo.Sec19.SimsSolEvenEightLen2

public section

namespace CFSG.RankThree.PartTwo.Sec19.SolEven

open CFSG CFSG.QuasithinUnique CFSG.RankThree.PartTwo CFSG.CGT.PushingUpLit.SolK

namespace Eight

variable {G : Type} [Group G] [Finite G] {M X : Subgroup G} {n : ℕ}

theorem fstar_eq (S : Setting G M X n) {z : G} (hzQ : z ∈ CFSG.Open.pCoreOf 2 M) (hz1 : z ≠ 1) :
    CFSG.inSubgroup CFSG.generalizedFitting (Subgroup.centralizer ({z} : Set G)) =
      CFSG.Open.pCoreOf 2 (CGOf z) := by
  rw [CGOf, ← centralizer_singleton_eq_zpowers]
  unfold CFSG.inSubgroup CFSG.Open.pCoreOf
  rw [S.cent z hzQ hz1]

theorem centInM_of {C : Cfg G M X 8} (D : C.PiData) (hR : Nat.card ↥(Rc X) ≤ 2)
    (h4 : ∀ y : ↥(CFSG.Open.pCoreOf 2 M), barLen (Multiplicative.toAdd (D.piQ y)) = 4 →
      CGOf (y : G) ≤ M) :
    ∀ x ∈ CFSG.Open.pCoreOf 2 M, x ≠ 1 → Subgroup.centralizer ({x} : Set G) ≤ M := by
  have h37 : ∀ y : ↥(CFSG.Open.pCoreOf 2 M), barLen (Multiplicative.toAdd (D.piQ y)) = 4 →
      ∀ g : G, g * (y : G) * g⁻¹ ∈ CFSG.Open.pCoreOf 2 M → g ∈ M := by
    intro y hy g hg
    obtain ⟨I, hIc, hI⟩ := exists_supp_of_len (Multiplicative.toAdd (D.piQ y))
    rw [hy] at hIc
    exact mem_M_of_conj_len_four D hR h4 y.2 hIc hI hg
  intro x hx hx1
  rw [centralizer_singleton_eq_zpowers]
  by_cases hl2 : barLen (Multiplicative.toAdd (D.piQ ⟨x, hx⟩)) = 2
  · obtain ⟨a, b, hab, hab'⟩ := (Comb.barLen_eq_two_iff (by norm_num)).1 hl2
    exact centralizer_le_M_of_len_two D hR h37 hx hab hab'
  by_cases hl4 : barLen (Multiplicative.toAdd (D.piQ ⟨x, hx⟩)) = 4
  · exact h4 ⟨x, hx⟩ hl4
  rw [← centralizer_singleton_eq_zpowers]
  exact (D.centralizer_le_of_len hR ⟨x, hx⟩ hx1 ⟨hl2, hl4⟩).1

end Eight

end CFSG.RankThree.PartTwo.Sec19.SolEven
