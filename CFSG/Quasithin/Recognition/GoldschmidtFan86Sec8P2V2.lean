module

public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec8P2V1

public section

namespace CFSG.Quasithin.Fan86

open SimpleGraph CFSG.Quasithin.F6.GoldAmL3T

variable {V G : Type*} [Group G] [MulAction G V] {Γ : SimpleGraph V}

namespace D10Set

variable {L : ZLab Γ G} {α : V} (D : D10Set L α)

theorem y_fixes_alpha_start (F : FanTree Γ G) (h : Fan71c F L) (h81 : Fan81 F L) {δ' : V}
    (hY : D.IsYPair δ') (k : Fin 5) : D.y δ' k • α = α := by
  refine (D.y_fixed_iff F h h81 hY k (by rw [SimpleGraph.dist_self]; norm_num)).2 (Or.inl ?_)
  rw [SimpleGraph.dist_comm, D.dist_start_alpha F k]

theorem y_smul_smul (F : FanTree Γ G) (h : Fan71c F L) {δ' : V} (hY : D.IsYPair δ') (k : Fin 5)
    (x : V) : D.y δ' k • D.y δ' k • x = x := by
  rw [← mul_smul, D.y_mul_self' F h hY k, one_smul]

theorem y_moves_alpha (F : FanTree Γ G) (h : Fan71c F L) (h81 : Fan81 F L) {δ' : V}
    (hY : D.IsYPair δ') {i j : Fin 5} (hij : i ≠ j) : D.y δ' j • D.alpha i ≠ D.alpha i := by
  intro hfix
  have := (D.y_fixed_iff F h h81 hY j (by rw [D.dist_start_alpha F i]; norm_num)).1 hfix
  have h1 : Γ.dist (D.alpha j) (D.alpha i) = 4 := D.dist_alpha_alpha F h hij.symm
  have h2 : Γ.dist (D.beta j) (D.alpha i) = 3 := D.dist_beta_alpha_ne F h hij
  omega

theorem y_moves_conj (F : FanTree Γ G) (h : Fan71c F L) (h81 : Fan81 F L) {δ' : V}
    (hY : D.IsYPair δ') {i j : Fin 5} (hij : i ≠ j) :
    D.y δ' i • D.y δ' j • D.delta i ≠ D.y δ' j • D.delta i := by
  intro hfix
  set p := D.y δ' j • D.delta i with hp
  have hα := D.y_fixes_alpha_start F h h81 hY j
  have hβ := D.y_fixes_beta F h h81 hY j i
  have hpα' : Γ.dist α p = 4 := by
    have := dist_smul F (D.y δ' j) α (D.delta i)
    rw [hα, D.dist_delta F i] at this
    exact this
  have hpα : Γ.dist α p ≤ 4 := hpα'.le
  have h1 := (D.y_fixed_iff F h h81 hY i hpα).1 hfix
  have hdβ : Γ.dist (D.beta i) p = 3 := by
    have := dist_smul F (D.y δ' j) (D.beta i) (D.delta i)
    rw [hβ, D.dist_beta_delta F i] at this
    exact this
  have hadj : Γ.Adj (D.beta i) (D.y δ' j • D.alpha i) := by
    have := (F.adj_smul (D.y δ' j) (D.beta i) (D.alpha i)).2 (D.adj_beta_alpha i)
    rwa [hβ] at this
  have hne : D.alpha i ≠ D.y δ' j • D.alpha i := fun e =>
    D.y_moves_alpha F h h81 hY hij e.symm
  have hd4 : Γ.dist (D.delta i) (D.y δ' j • D.alpha i) = 4 := by
    have h2 : Γ.dist (D.delta i) (D.alpha i) = 2 := by
      rw [SimpleGraph.dist_comm, D.dist_alpha_delta F i]
    have h3 : Γ.dist (D.delta i) (D.beta i) = 3 := by
      rw [SimpleGraph.dist_comm, D.dist_beta_delta F i]
    have := IsTree.dist_succ_of_ne F.isTree (D.adj_beta_alpha i) hadj hne
      (w := D.delta i) (by omega)
    omega
  have hyy : D.y δ' j • p = D.delta i := D.y_smul_smul F h hY j _
  have hdα : Γ.dist (D.alpha i) p = 4 := by
    have := dist_smul F (D.y δ' j) (D.alpha i) p
    rw [hyy, SimpleGraph.dist_comm] at this
    omega
  omega

theorem fcomm_y_eq (F : FanTree Γ G) (h : Fan71c F L) {δ' : V} (hY : D.IsYPair δ') (i j : Fin 5) :
    fcomm (D.y δ' i) (D.y δ' j) = D.y δ' i * D.y δ' j * D.y δ' i * D.y δ' j := by
  have hi : (D.y δ' i)⁻¹ = D.y δ' i := inv_eq_of_mul_eq_one_right (D.y_mul_self' F h hY i)
  have hj : (D.y δ' j)⁻¹ = D.y δ' j := inv_eq_of_mul_eq_one_right (D.y_mul_self' F h hY j)
  unfold fcomm
  rw [hi, hj]

theorem fcomm_y_moves_delta_left (F : FanTree Γ G) (h : Fan71c F L) (h81 : Fan81 F L) {δ' : V}
    (hY : D.IsYPair δ') {i j : Fin 5} (hij : i ≠ j) :
    fcomm (D.y δ' i) (D.y δ' j) • D.delta i ≠ D.delta i := by
  intro hfix
  rw [D.fcomm_y_eq F h hY, mul_smul, mul_smul, mul_smul] at hfix
  have hyδ : D.y δ' i • D.delta i = D.delta i :=
    (D.y_fixed_iff F h h81 hY i (by rw [D.dist_delta F i])).2
      (Or.inl (by rw [D.dist_alpha_delta F i]))
  have h1 : D.y δ' j • D.y δ' i • D.y δ' j • D.delta i = D.delta i := by
    have := congrArg (D.y δ' i • ·) hfix
    simpa [D.y_smul_smul F h hY i, hyδ] using this
  have h2 : D.y δ' i • D.y δ' j • D.delta i = D.y δ' j • D.delta i := by
    have := congrArg (D.y δ' j • ·) h1
    simpa [D.y_smul_smul F h hY j] using this
  exact D.y_moves_conj F h h81 hY hij h2

theorem fcomm_y_moves_delta_right (F : FanTree Γ G) (h : Fan71c F L) (h81 : Fan81 F L) {δ' : V}
    (hY : D.IsYPair δ') {i j : Fin 5} (hij : i ≠ j) :
    fcomm (D.y δ' i) (D.y δ' j) • D.delta j ≠ D.delta j := by
  intro hfix
  have hinv : fcomm (D.y δ' i) (D.y δ' j) = (fcomm (D.y δ' j) (D.y δ' i))⁻¹ := by
    unfold fcomm
    group
  have h1 : fcomm (D.y δ' j) (D.y δ' i) • D.delta j = D.delta j := by
    rw [hinv] at hfix
    exact (inv_smul_eq_iff.1 hfix).symm
  exact D.fcomm_y_moves_delta_left F h h81 hY hij.symm h1

end D10Set

end CFSG.Quasithin.Fan86
