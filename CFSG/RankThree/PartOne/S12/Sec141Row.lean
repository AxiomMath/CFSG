module

public import CFSG.RankThree.PartOne.S12.Sec137
public import CFSG.RankThree.PartOne.KF.Reduction123
public import CFSG.Timmesfeld.Orders.Distinct
public import CFSG.Timmesfeld.Orders.Classical

public section

namespace CFSG.RankThree.PartOne

open CFSG.Assembly CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.GroupTheory
open CFSG.Assembly.LowTwoRank (StatedClassicalModel)
open CFSG.LocalAnalysis.ComponentInitial (SchreierFor)

namespace Sec141Row

theorem not_psl_three_and_psu_five {Q : Type} [Group Q] {a g : ℕ}
    (h1 : StatedClassicalModel Q .PSL 3 2 a) (h2 : StatedClassicalModel Q .PSU 5 2 g) : False := by
  have c1 := (CFSG.Timmesfeld.card_statedClassicalModel_two h1).1 rfl
  have c2 := (CFSG.Timmesfeld.card_statedClassicalModel_two h2).2.1 rfl
  obtain ⟨⟨-, ha, -, -, -⟩, -⟩ := h1
  obtain ⟨⟨-, hg, -, -⟩, -⟩ := h2
  exact CFSG.Timmesfeld.Orders.ordA_ne_ordTwistedA (n := 2) (u := 4) (by norm_num) ha
    (by norm_num) hg (c1.symm.trans c2)

variable {G : Type} [Group G] [Finite G]

theorem rowOne_data (hRow1 : KF123Row 1) (h107 : InSec10Seven) (h109 : InSec10Nine)
    (h122 : Node122) {p : ℕ} {B : Subgroup G} {c : G} {X E : Subgroup G}
    (h : Sec12Hyp G p B c X E) (hm : RowModel p X 1) :
    Sec12TwoGeneric p c X E ∧ RowWeylIso E (torusImage E X) 1 ∧ Nat.card E = p ^ 3 := by
  rcases Sec12Hyp.table123_hyp h107 h109 h122 h with ⟨hG, hT⟩ | ⟨hS, hT⟩
  · obtain ⟨-, hcard, hweyl, -, -, -⟩ := hRow1 G p X (B ⊓ X) (E ⊓ X) hT hm
    have R := h.restr_of_generic hG
    have hcL := h.c_not_mem_of_generic hG
    have hEcard := R.card_E h.prime (Sec12Three.orderOf_c h) hcL
    refine ⟨hG, R.rowWeylIso hweyl, ?_⟩
    rw [hEcard, hcard, Sec12Three.rowRank_eq_two (by norm_num) (by norm_num)]
    ring
  · exfalso
    obtain ⟨f', -, hmod5⟩ := hS.model
    obtain ⟨f, -, -, hmod1⟩ := hm
    exact not_psl_three_and_psu_five hmod1 hmod5

theorem orderOf_perm_three_le (σ : Equiv.Perm (Fin 3)) : orderOf σ ≤ 3 := by
  have h : ∀ σ : Equiv.Perm (Fin 3), σ ^ 1 = 1 ∨ σ ^ 2 = 1 ∨ σ ^ 3 = 1 := by decide
  rcases h σ with h1 | h1 | h1
  · exact (orderOf_le_of_pow_eq_one (by norm_num) h1).trans (by norm_num)
  · exact (orderOf_le_of_pow_eq_one (by norm_num) h1).trans (by norm_num)
  · exact orderOf_le_of_pow_eq_one (by norm_num) h1

end Sec141Row

theorem threeTranspD_of_pair (hpair : KF134Pair) (hRow1 : KF123Row 1) (h107 : InSec10Seven)
    (h109 : InSec10Nine) (h122 : Node122) {G : Type} [Group G] [Finite G] {p : ℕ}
    {A : Subgroup G} {c : G} {L E : Subgroup G} (h : Sec12Hyp G p A c L E)
    (hF12 : Sec12Facts G p A c L E) (hF13 : Sec13Facts G p A c L E)
    (hT : ¬ Outcome152Five p E A (lieGenerated p E)) (hEA : E = A)
    (hall : ∀ J : Subgroup G, J ∈ sectionTenZeroStar p A → IsLThreeTypeAt p J) :
    ThreeTranspD p E := by
  intro s hs t ht
  by_cases hcomm : s * t = t * s
  · have hs2 : s * s = 1 := RefFacts.mul_self_eq_one hs.1
    have ht2 : t * t = 1 := RefFacts.mul_self_eq_one ht.1
    have h2 : (s * t) ^ 2 = 1 := by
      rw [Commute.mul_pow hcomm, pow_two s, hs2, pow_two t, ht2, one_mul]
    exact (orderOf_le_of_pow_eq_one (by norm_num) h2).trans (by norm_num)
  · obtain ⟨I, hI, hsI, htI⟩ :=
      hpair G p A c L E h hF12 hF13 hT (Or.inr ⟨hEA, hall⟩) s hs t ht hcomm
    obtain ⟨B, c', hB, hc'B, hc'1, h', -⟩ := hF13.reinstantiate I hI
    have hBA : B = A := by
      refine Subgroup.eq_of_le_of_card_ge (hEA ▸ hB.1) (le_of_eq ?_)
      rw [h.A_card, hB.2.2.1]
    have hIz : I ∈ sectionTenZeroStar p A := hBA ▸ Sec12Three.L_mem_zeroStar h'
    obtain ⟨-, hweyl, -⟩ := Sec141Row.rowOne_data hRow1 h107 h109 h122 h' (hall I hIz)
    obtain ⟨ψ⟩ := hweyl
    have h1 : orderOf (s * t) =
        orderOf ((⟨s, hsI⟩ : ↥(torusImage E I)) * ⟨t, htI⟩) := by
      rw [← Subgroup.orderOf_coe]
      rfl
    rw [h1, ← MulEquiv.orderOf_eq ψ]
    exact Sec141Row.orderOf_perm_three_le _

end CFSG.RankThree.PartOne
