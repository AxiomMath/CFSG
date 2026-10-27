module

public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps13ThrNDefs
public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps13ThrNE
public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps13ThrNA
public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps13ThrFiveN
public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps13ThrSixN
public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps13ThrCases
public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps13ThrEightX
public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps13ThrEightA
public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps13ThrXN
public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps13ThrXO
public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps13TwoZ

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.LocalAnalysis.UniquenessCase.PartTwo CFSG.Quasithin CFSG.Open Subgroup
open scoped commutatorElement

variable {W : Type} [CommGroup W] [Finite W]
variable {A : Subgroup (MulAut W)} {t : MulAut W}

private def w16g_Row (A : Subgroup (MulAut W)) (t : MulAut W) (p : ℕ) : Prop :=
  ∃ L N : Subgroup (MulAut W), L ≤ N ∧ N ≤ pCoreOf p A ∧ (N.subgroupOf A).Normal ∧
    (∀ n ∈ N, ∀ w ∈ commSub ⊤ L, n w ∈ commSub ⊤ L) ∧
    (∀ g ∈ A, (commSub ⊤ L).map g.toMonoidHom = commSub ⊤ L →
      L.map (MulAut.conj g).toMonoidHom = L) ∧
    Conc4_133 A t L

private theorem w16g_normal_subgroupOf_pCoreOf (A : Subgroup (MulAut W)) (p : ℕ) :
    ((pCoreOf p A).subgroupOf A).Normal := by
  rw [Subgroup.normal_subgroupOf_iff (s13_pCore_facts A p).2.1]
  intro h k hh hk
  exact (s13_pCore_facts A p).1 k hk h hh

private theorem w16g_normal_subgroupOf_of_conj {A N : Subgroup (MulAut W)}
    (hNA : ∀ g ∈ A, ∀ x ∈ N, g * x * g⁻¹ ∈ N) (hNle : N ≤ A) :
    (N.subgroupOf A).Normal := by
  rw [Subgroup.normal_subgroupOf_iff hNle]
  intro h k hh hk
  exact hNA k hk h hh

private theorem w16g_row_three_ab (h : Cfg133 A t 3)
    (hab : ∀ x ∈ ⁅pCoreOf 3 A, Subgroup.zpowers t⁆, ∀ y ∈ ⁅pCoreOf 3 A, Subgroup.zpowers t⁆,
      x * y = y * x) :
    w16g_Row A t 3 := by
  by_cases hXab : ∀ a ∈ conjClosure A (omegaOne 3 ⁅pCoreOf 3 A, Subgroup.zpowers t⁆),
      ∀ b ∈ conjClosure A (omegaOne 3 ⁅pCoreOf 3 A, Subgroup.zpowers t⁆), a * b = b * a
  · let X : Subgroup (MulAut W) := conjClosure A (omegaOne 3 ⁅pCoreOf 3 A, Subgroup.zpowers t⁆)
    have hH : HAb A X (omegaOne 3 ⁅pCoreOf 3 A, Subgroup.zpowers t⁆) t 3 :=
      s13_HAb_three h hab hXab
    obtain ⟨L, hLX, hConc, hcl⟩ := s13_abelian_branch hH
    exact ⟨L, X, hLX, hH.hXO,
      w16g_normal_subgroupOf_of_conj (A := A) (N := X) (fun g hg x hx => hH.hXA g hg x hx)
        (hH.hXO.trans (s13_pCore_facts A 3).2.1),
      s13_U1_abelian hH hLX, s13_U3_abelian hH hLX hcl, hConc⟩
  · push Not at hXab
    obtain ⟨L, hLO, hConc, hLe, hLr, hnorm⟩ := s13_case_three_nonab_N h hab hXab
    exact ⟨L, pCoreOf 3 A, hLO, le_rfl, w16g_normal_subgroupOf_pCoreOf A 3,
      s13_commSub_invariant_of_normalizes hnorm, s13_U3_three h hLO hLe hLr, hConc⟩

private theorem w16g_row_three_six (h : Cfg133 A t 3)
    (hP : IsPOnePlusTwo 3 ↥(⁅pCoreOf 3 A, Subgroup.zpowers t⁆))
    (hr : rk ↥(commSub ⊤ (⁅pCoreOf 3 A, Subgroup.zpowers t⁆)) = 6) :
    w16g_Row A t 3 := by
  obtain ⟨L, hLO, hConc, hLe, hLr, hnorm⟩ := s13_case_three_six_N h hP hr
  exact ⟨L, pCoreOf 3 A, hLO, le_rfl, w16g_normal_subgroupOf_pCoreOf A 3,
    s13_commSub_invariant_of_normalizes hnorm, s13_U3_three h hLO hLe hLr, hConc⟩

private theorem w16g_row_three_four (h : Cfg133 A t 3)
    (h4 : IsZ3TimesPOnePlusTwo ↥(⁅pCoreOf 3 A, Subgroup.zpowers t⁆) ∨
      IsZ3WrZ3 ↥(⁅pCoreOf 3 A, Subgroup.zpowers t⁆)) :
    w16g_Row A t 3 := by
  obtain ⟨L, hLO, hConc, hLe, hLr, hnorm⟩ := s13_case_four_N h h4
  exact ⟨L, pCoreOf 3 A, hLO, le_rfl, w16g_normal_subgroupOf_pCoreOf A 3,
    s13_commSub_invariant_of_normalizes hnorm, s13_U3_three h hLO hLe hLr, hConc⟩

private theorem w16g_row_three (h : Cfg133 A t 3) (hI : IsIndivisible A) : w16g_Row A t 3 := by
  obtain ⟨-, hPp, hPne, hPn, hPc, -⟩ := s13_P_facts h
  have htord : orderOf t = 2 := orderOf_eq_prime h.ht2 h.ht1
  have hW2 : ∀ w : W, w ^ 2 = 1 := fun w => by rw [pow_two]; exact h.hW w
  rcases w4Lem13_2_holds W hW2 t htord h.hrk 3 _
      Nat.prime_three hPp hPne hPn hPc with
    ⟨hcyc, -⟩ | ⟨n, -, hn⟩ | ⟨hP3, hr⟩ | ⟨h4, -⟩
  · have hab : ∀ x ∈ ⁅pCoreOf 3 A, Subgroup.zpowers t⁆,
        ∀ y ∈ ⁅pCoreOf 3 A, Subgroup.zpowers t⁆, x * y = y * x := by
      haveI : IsCyclic ↥(⁅pCoreOf 3 A, Subgroup.zpowers t⁆) := hcyc
      letI : CommGroup ↥(⁅pCoreOf 3 A, Subgroup.zpowers t⁆) := IsCyclic.commGroup
      intro x hx y hy
      exact congrArg Subtype.val (mul_comm (⟨x, hx⟩ :
        ↥(⁅pCoreOf 3 A, Subgroup.zpowers t⁆)) ⟨y, hy⟩)
    exact w16g_row_three_ab h hab
  · have hab : ∀ x ∈ ⁅pCoreOf 3 A, Subgroup.zpowers t⁆,
        ∀ y ∈ ⁅pCoreOf 3 A, Subgroup.zpowers t⁆, x * y = y * x := fun x hx y hy =>
      congrArg Subtype.val ((w16g_isElemAbelianOfRank_comm_pow hn).1 ⟨x, hx⟩ ⟨y, hy⟩)
    exact w16g_row_three_ab h hab
  · rcases hr with hr | hr
    · exact w16g_row_three_six h hP3 hr
    · obtain ⟨z, N, hD⟩ := s13_2_three_rank8 h hP3 hr
      exact (s13_eight_false_of_indivisible h hI hD).elim
  · exact w16g_row_three_four h h4

private theorem w16g_row_five (h : Cfg133 A t 5) : w16g_Row A t 5 := by
  obtain ⟨L, hLO, hConc, hL5, hLr, hnorm⟩ := s13_case_five_N h
  exact ⟨L, pCoreOf 5 A, hLO, le_rfl, w16g_normal_subgroupOf_pCoreOf A 5,
    s13_commSub_invariant_of_normalizes hnorm, s13_U3_five h hLO hL5 hLr, hConc⟩

private theorem w16g_row_seven (h : Cfg133 A t 7) : w16g_Row A t 7 := by
  let X : Subgroup (MulAut W) := conjClosure A ⁅pCoreOf 7 A, Subgroup.zpowers t⁆
  have hH : HAb A X ⁅pCoreOf 7 A, Subgroup.zpowers t⁆ t 7 := s13_HAb_seven h
  obtain ⟨L, hLX, hConc, hcl⟩ := s13_abelian_branch hH
  exact ⟨L, X, hLX, hH.hXO,
    w16g_normal_subgroupOf_of_conj (A := A) (N := X) (fun g hg x hx => hH.hXA g hg x hx)
      (hH.hXO.trans (s13_pCore_facts A 7).2.1),
    s13_U1_abelian hH hLX, s13_U3_abelian hH hLX hcl, hConc⟩

theorem w4Lem13_3N_holds : R4_133N := by
  intro W _ _ hW A t htA ht2 ht1 hrk hO2 hI p hp hP
  have h : Cfg133 A t p := ⟨hW, htA, ht2, ht1, hrk, hO2, hp, hP⟩
  obtain ⟨hp2, hp7⟩ := s13_p_facts h
  have hp357 : p = 3 ∨ p = 5 ∨ p = 7 := by
    have h2 := hp.two_le
    have h4 : p ≠ 4 := fun e => by rw [e] at hp; norm_num at hp
    have h6 : p ≠ 6 := fun e => by rw [e] at hp; norm_num at hp
    omega
  rcases hp357 with rfl | rfl | rfl
  · change w16g_Row A t 3
    exact w16g_row_three h hI
  · change w16g_Row A t 5
    exact w16g_row_five h
  · change w16g_Row A t 7
    exact w16g_row_seven h

end CFSG.LocalAnalysis.WeakClosure81
