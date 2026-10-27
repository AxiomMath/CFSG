module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.CaseTwoSylow
public import CFSG.RankThree.LocalRank.ThetaPlaneAlpha
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.CaseTwoFixedEnd
import CFSG.GroupTheory.QuasisimpleCommutingProductBound

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.SCZeroAlpha

open CFSG Subgroup
open CFSG.RankThree.LocalRank
open CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82

private theorem thetaJ_eq_bot_of_thetaAlpha_eq_bot {X : Type} [Group X] {p : ℕ} {E : Subgroup X}
    (h : thetaAlpha p E = ⊥) : thetaJ p E = ⊥ := by
  rw [thetaAlpha] at h
  exact le_bot_iff.mp (le_sup_left.trans h.le)

theorem inSubgroup_le_centralizer_of_thetaJ_eq_bot {X : Type} [Group X] {E : Subgroup X}
    (hE : thetaJ 3 E = ⊥) {e : X} (he : e ∈ E) (he1 : e ≠ 1) :
    inSubgroup (aschbacherSolvableCore 3) (centralizer ({e} : Set X)) ≤
      centralizer (E : Set X) := by
  rw [← Subgroup.commutator_eq_bot_iff_le_centralizer]
  have hle : ⁅inSubgroup (aschbacherSolvableCore 3) (centralizer ({e} : Set X)), E⁆ ≤
      thetaJ 3 E := by
    rw [thetaJ]
    exact le_iSup_of_le e (le_iSup_of_le he (le_iSup_of_le he1 le_rfl))
  rw [hE] at hle
  exact le_bot_iff.mp hle

private theorem zpowers_sup_A {G : Type} [Group G] [Finite G] (d : SylowThreeData G)
    {i j l : Fin 3} (hli : l ≠ i) (hlj : l ≠ j) (hij : i ≠ j) {b : G}
    (hb : b ∈ d.A i ⊔ d.A j) (hb1 : b ≠ 1) :
    Subgroup.zpowers b ⊔ d.A l ≤ d.AA ∧ Nat.card ↥(Subgroup.zpowers b ⊔ d.A l) = 9 := by
  have hA_le_AA : ∀ k : Fin 3, d.A k ≤ d.AA := fun k x hx =>
    d.mem_AA_of_pow_eq_one (d.A_le_S k hx) (((d.mem_A_iff k).mp hx).2)
  have hbAA : b ∈ d.AA := (sup_le (hA_le_AA i) (hA_le_AA j)) hb
  have hb3 : b ^ 3 = 1 := d.isElemAbelian_AA.2 b hbAA
  refine ⟨sup_le (Subgroup.zpowers_le_of_mem hbAA) (hA_le_AA l), ?_⟩
  have hcomm : ∀ x ∈ Subgroup.zpowers b, ∀ y ∈ d.A l, x * y = y * x := fun x hx y hy =>
    d.S_commute x y (d.AA_le_S (Subgroup.zpowers_le_of_mem hbAA hx)) (d.AA_le_S (hA_le_AA l hy))
  have hinf : Subgroup.zpowers b ⊓ d.A l = ⊥ := by
    rw [Subgroup.eq_bot_iff_forall]
    intro x hx
    exact d.eq_one_of_mem_Lf_of_mem_sup (i := l) (j := i) (k := j) hli hlj hij
      (d.A_le_S l hx.2) ((d.A_le_H l).trans (d.H_le_Lf l) hx.2)
      (sup_le_sup ((d.A_le_H i).trans (d.H_le_Lf i)) ((d.A_le_H j).trans (d.H_le_Lf j))
        (Subgroup.zpowers_le_of_mem hb hx.1))
  have hord : orderOf b = 3 := by
    rcases (Nat.dvd_prime Nat.prime_three).mp (orderOf_dvd_of_pow_eq_one hb3) with h | h
    · exact absurd h (fun h1 => hb1 (orderOf_eq_one_iff.mp h1))
    · exact h
  have hcardb : Nat.card ↥(Subgroup.zpowers b) = 3 := by
    rw [Nat.card_zpowers, hord]
  obtain ⟨hcard, -⟩ :=
    CFSG.GroupTheory.card_sup_mul_card_inf_of_commute (Subgroup.zpowers b) (d.A l) hcomm
  rw [hinf, Subgroup.card_bot, mul_one, hcardb, d.card_A l] at hcard
  simpa using hcard

theorem inSubgroup_le_centralizer_AA_of_thetaAlpha_eq_bot {G : Type} [Group G] [Finite G]
    (d : SylowThreeData G) {i j : Fin 3} (hij : i ≠ j) {b : G} (hb : b ∈ d.A i ⊔ d.A j)
    (hb1 : b ≠ 1)
    (hAlpha : ∀ E : Subgroup G, E ≤ d.AA → Nat.card E = 9 → thetaAlpha 3 E = ⊥) :
    inSubgroup (aschbacherSolvableCore 3) (centralizer ({b} : Set G)) ≤
      centralizer (d.AA : Set G) := by
  have hA_le_AA : ∀ k : Fin 3, d.A k ≤ d.AA := fun k x hx =>
    d.mem_AA_of_pow_eq_one (d.A_le_S k hx) (((d.mem_A_iff k).mp hx).2)
  have hle₁ : d.A i ⊔ d.A j ≤ d.AA := sup_le (hA_le_AA i) (hA_le_AA j)
  have hcard₁ : Nat.card ↥(d.A i ⊔ d.A j) = 9 := by
    rw [d.card_A_sup_A hij]; norm_num
  have hU₁ : inSubgroup (aschbacherSolvableCore 3) (centralizer ({b} : Set G)) ≤
      centralizer ((d.A i ⊔ d.A j : Subgroup G) : Set G) :=
    inSubgroup_le_centralizer_of_thetaJ_eq_bot
      (thetaJ_eq_bot_of_thetaAlpha_eq_bot (hAlpha (d.A i ⊔ d.A j) hle₁ hcard₁)) hb hb1
  have hA_le : ∀ l : Fin 3,
      inSubgroup (aschbacherSolvableCore 3) (centralizer ({b} : Set G)) ≤
        centralizer (d.A l : Set G) := by
    intro l
    by_cases hli : l = i
    · rw [hli]
      exact hU₁.trans (Subgroup.centralizer_le (le_sup_left : d.A i ≤ d.A i ⊔ d.A j))
    by_cases hlj : l = j
    · rw [hlj]
      exact hU₁.trans (Subgroup.centralizer_le (le_sup_right : d.A j ≤ d.A i ⊔ d.A j))
    · obtain ⟨hE₂_le, hcard₂⟩ := zpowers_sup_A d hli hlj hij hb hb1
      have hbE₂ : b ∈ Subgroup.zpowers b ⊔ d.A l :=
        Subgroup.mem_sup_left (Subgroup.mem_zpowers b)
      exact (inSubgroup_le_centralizer_of_thetaJ_eq_bot
        (thetaJ_eq_bot_of_thetaAlpha_eq_bot
          (hAlpha (Subgroup.zpowers b ⊔ d.A l) hE₂_le hcard₂)) hbE₂ hb1).trans
        (Subgroup.centralizer_le (le_sup_right : d.A l ≤ Subgroup.zpowers b ⊔ d.A l))
  rw [Subgroup.le_centralizer_iff, d.AA_def]
  exact sup_le (sup_le (Subgroup.le_centralizer_iff.mp (hA_le 0))
    (Subgroup.le_centralizer_iff.mp (hA_le 1))) (Subgroup.le_centralizer_iff.mp (hA_le 2))

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.SCZeroAlpha
