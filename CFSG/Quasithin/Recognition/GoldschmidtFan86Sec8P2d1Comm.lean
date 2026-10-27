module

public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec8P2cA

public section

namespace CFSG.Quasithin.Fan86.P2d1

open SimpleGraph CFSG.Quasithin.F6.GoldAmL3T

variable {V G : Type*} [Group G] [MulAction G V] {Γ : SimpleGraph V}
  {F : FanTree Γ G} {L : ZLab Γ G} {α : V} (D : D10Set L α)

theorem pair_fix_ball (h81 : Fan81 F L) {i : Fin 5} {l₁ l₂ : V}
    (hZ : IsZ2Pair Γ G α (D.alpha i) (D.beta i) l₁ l₂ 2) {w : V}
    (hw : Γ.dist (D.beta i) w ≤ 2) : (L.z l₁ * L.z l₂) • w = w := by
  refine (P2c.pair_fixed_iff D h81 hZ ?_).2 (Or.inr hw)
  have := F.isTree.connected.dist_triangle (u := α) (v := D.beta i) (w := w)
  have := D.dist_start_beta F i
  omega

theorem pair_fix_alpha (h81 : Fan81 F L) {i : Fin 5} {l₁ l₂ : V}
    (hZ : IsZ2Pair Γ G α (D.alpha i) (D.beta i) l₁ l₂ 2) : (L.z l₁ * L.z l₂) • α = α :=
  MulAction.mem_stabilizer_iff.1 (F.nbrStab_le_stabilizer α (P2c.pair_mem_nbrStab D h81 hZ))

theorem fcomm_invol {a b : G} (ha : a * a = 1) (hb : b * b = 1) : fcomm a b = a * b * a * b := by
  unfold fcomm
  rw [inv_eq_of_mul_eq_one_right ha, inv_eq_of_mul_eq_one_right hb]

theorem four_smul_eq {Y Y' : G} {w : V} (h1 : Y • (Y' • w) = Y' • w)
    (h2 : Y' • (Y' • w) = w) (h3 : Y • w = w) : (Y * Y' * Y * Y') • w = w := by
  simp only [mul_smul]
  rw [h1, h2, h3]

theorem comm_fix_ball (h71c : Fan71c F L) (h81 : Fan81 F L) {i j : Fin 5} {l₁ l₂ m₁ m₂ : V}
    (hZ : IsZ2Pair Γ G α (D.alpha i) (D.beta i) l₁ l₂ 2)
    (hZ' : IsZ2Pair Γ G α (D.alpha j) (D.beta j) m₁ m₂ 2) {w : V}
    (hw : Γ.dist (D.beta i) w ≤ 2) : fcomm (L.z l₁ * L.z l₂) (L.z m₁ * L.z m₂) • w = w := by
  have hYsq := P2c.pair_sq D h71c hZ
  have hY'sq := P2c.pair_sq D h71c hZ'
  have hβ' := P2c.pair_fix_beta D h81 hZ' i
  have hd : Γ.dist (D.beta i) ((L.z m₁ * L.z m₂) • w) ≤ 2 := by
    have := dist_smul F (L.z m₁ * L.z m₂) (D.beta i) w
    rw [hβ'] at this
    omega
  have h1 := pair_fix_ball D h81 hZ hd
  have h2 : (L.z m₁ * L.z m₂) • ((L.z m₁ * L.z m₂) • w) = w := by
    rw [← mul_smul, hY'sq, one_smul]
  have h3 := pair_fix_ball D h81 hZ hw
  rw [fcomm_invol hYsq hY'sq]
  exact four_smul_eq h1 h2 h3

theorem comm_mem_ballStab_two (h71c : Fan71c F L) (h81 : Fan81 F L) {i j : Fin 5}
    {l₁ l₂ m₁ m₂ : V} (hZ : IsZ2Pair Γ G α (D.alpha i) (D.beta i) l₁ l₂ 2)
    (hZ' : IsZ2Pair Γ G α (D.alpha j) (D.beta j) m₁ m₂ 2) :
    fcomm (L.z l₁ * L.z l₂) (L.z m₁ * L.z m₂) ∈ ballStab Γ G 2 (D.beta i) ∧
      fcomm (L.z l₁ * L.z l₂) (L.z m₁ * L.z m₂) ∈ ballStab Γ G 2 (D.beta j) := by
  refine ⟨mem_ballStab.2 fun w hw => comm_fix_ball D h71c h81 hZ hZ' hw, ?_⟩
  rw [← F87.fcomm_inv_eq]
  exact (ballStab Γ G 2 (D.beta j)).inv_mem
    (mem_ballStab.2 fun w hw => comm_fix_ball D h71c h81 hZ' hZ hw)

end CFSG.Quasithin.Fan86.P2d1
