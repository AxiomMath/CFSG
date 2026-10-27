module

public import CFSG.RankThree.PartOne.CTP.KF1214U5
public import CFSG.RankThree.PartOne.CTP.Phan5False

public section

namespace CFSG.RankThree.PartOne.CTP

open CFSG.Assembly.LowTwoRank (StatedClassicalModel)
open CFSG.RankThree.PartOne

structure Frame1214Data {G : Type} [Group G] (c : G) (E : Subgroup G) (f : ℕ)
    (N B : Subgroup G) (M : Fin 4 → Subgroup G) : Prop where
  two_le : 2 ≤ f
  dvd5 : 5 ∣ 2 ^ f + 1
  dvd25 : 25 ∣ 2 ^ f + 1
  le_N : ∀ i, M i ≤ N
  gen : (⨆ i, M i) = N
  B_le_N : B ≤ N
  model : ∀ i, StatedClassicalModel ↥(M i) .PSL 2 2 f
  comm : ∀ i j, i ≠ j → ¬ chainAdj i j →
    M i ≤ Subgroup.centralizer (M j : Set G) ∧ M i ⊓ M j = ⊥
  adj : ∀ i j, chainAdj i j → CentrallyUThree f ↥(M i ⊔ M j)
  B_elem : IsElementaryAbelian 5 B
  B_card : Nat.card B = 5 ^ 3
  torus : CTTorusCondition 5 B M
  B_le_E : B ≤ E
  E_card : Nat.card E = 5 * Nat.card B
  E_gen : E = Subgroup.zpowers c ⊔ B
  c_normalizes : ∀ i, c ∈ Subgroup.normalizer (M i : Set G)
  c_outer : c ∉ M 0 ⊔ Subgroup.centralizer (M 0 : Set G)

@[expose] def Frame1214 {G : Type} [Group G] (c : G) (E : Subgroup G) : Prop :=
  ∃ (f : ℕ) (N B : Subgroup G) (M : Fin 4 → Subgroup G), Frame1214Data c E f N B M

section Maximal

variable {G : Type} [Group G] [Finite G] {p : ℕ} {A : Subgroup G} {c : G} {L E : Subgroup G}

theorem _root_.CFSG.RankThree.PartOne.Sec12Hyp.mem_of_centralizes
    (h : Sec12Hyp G p A c L E) {z : G} (hz : z ^ p = 1)
    (hcent : ∀ e ∈ E, e * z = z * e) : z ∈ E := by
  have hzel : IsElementaryAbelian p (Subgroup.zpowers z) :=
    IsElementaryAbelian.zpowers_of_pow_eq_one hz
  have hle : Subgroup.zpowers z ≤ Subgroup.centralizer (E : Set G) := by
    rw [Subgroup.zpowers_le, Subgroup.mem_centralizer_iff]
    intro e he
    exact hcent e he
  have hEel : IsElementaryAbelian p E := h.E_elem
  have hsup := IsElementaryAbelian.sup_of_le_centralizer (p := p) hle
  have hF : E ⊔ Subgroup.zpowers z = E := h.E_max_global _ hsup le_sup_left
  rw [← hF]
  exact Subgroup.mem_sup_right (Subgroup.mem_zpowers z)

end Maximal

section Contradiction

variable {G : Type} [Group G] [Finite G]

theorem Frame1214.false
    {p : ℕ} {A : Subgroup G} {c : G} {L E : Subgroup G}
    (h : Sec12Hyp G p A c L E) (hp5 : p = 5) (hF : Frame1214 c E) : False := by
  subst hp5
  obtain ⟨f, N, B, M, d⟩ := hF
  refine phan5_false d.two_le d.dvd5 d.dvd25 d.le_N d.gen d.B_le_N d.model d.comm d.adj d.B_elem
    d.B_card d.torus h.E_elem d.B_le_E d.E_card d.E_gen d.c_normalizes d.c_outer ?_
  intro z hz5 hcent
  exact h.mem_of_centralizes (by rw [← hz5]; exact pow_orderOf_eq_one z) hcent

end Contradiction

@[expose] def Kf1214U5Frame : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (A : Subgroup G) (c : G) (L E : Subgroup G),
    Fus12Ctx G p A c L E → RowModel p L 12 →
      ∀ (b : G) (K I X P Q : Subgroup G), Layer1212 p A c L E b K I →
        Choice1212 p E b I X P Q → Field1213 p A c L b K I → Frame1214 c E

theorem kf1214U5Core_of_frame
    (hF : Kf1214U5Frame) : Kf1214U5Core := by
  intro G _ _ p A c L E ctx hrow b K I X P Q hL hC hF13
  exact Frame1214.false ctx.hyp hrow.1 (hF G p A c L E ctx hrow b K I X P Q hL hC hF13)

end CFSG.RankThree.PartOne.CTP
