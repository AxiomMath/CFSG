module

public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec8P2d1Cls
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec8P2d1Mov

public section

namespace CFSG.Quasithin.Fan86

open SimpleGraph CFSG.Quasithin.F6.GoldAmL3T

variable {V G : Type*} [Group G] [MulAction G V] {Γ : SimpleGraph V}

theorem fan_8_3d1 {F : FanTree Γ G} {L : ZLab Γ G} (h7 : Fan7 F L) (h81 : Fan81 F L)
    (h512 : Fan512 F L) :
    ∀ (α : V) (D : D10Set L α) (i j : Fin 5), i ≠ j → ∀ l₁ l₂ m₁ m₂ : V,
      IsZ2Pair Γ G α (D.alpha i) (D.beta i) l₁ l₂ 2 →
      IsZ2Pair Γ G α (D.alpha j) (D.beta j) m₁ m₂ 2 →
      ∃ e : Fin 2, fcomm (L.z l₁ * L.z l₂) (L.z m₁ * L.z m₂) =
        L.z (D.alpha (kstar i j)) * L.z (D.alpha (kstar j i)) * L.z α ^ (e : ℕ) := by
  intro α D i j hij l₁ l₂ m₁ m₂ hZ hZ'
  have h71c : Fan71c F L := h7.2.2.1
  have h73a := h7.2.2.2.2.2.1
  have hYK := P2c.pair_mem_nbrStab D h81 hZ
  have hY'K := P2c.pair_mem_nbrStab D h81 hZ'
  have hH : fcomm (L.z l₁ * L.z l₂) (L.z m₁ * L.z m₂) ∈ ballStab Γ G 2 α := by
    have := (h73a α D.val).2.2.1 _ (inv_mem hYK) _ (inv_mem hY'K)
    simpa [fcomm] using this
  have hξj : fcomm (L.z l₁ * L.z l₂) (L.z m₁ * L.z m₂) • D.xi j = D.xi j := by
    have h := P2d1.comm_fix_ball D h71c h81 hZ' hZ (w := D.xi j) (by
      rw [D.dist_beta_xi F j])
    rw [← F87.fcomm_inv_eq]
    exact inv_smul_eq_iff.2 h.symm
  exact P2d1.classify_comm D h7 h512 hij hH (P2d1.comm_mem_ballStab_two D h71c h81 hZ hZ').1
    (P2d1.comm_fix_ball D h71c h81 hZ hZ' (w := D.xi i) (by rw [D.dist_beta_xi F i])) hξj
    (P2d1.comm_moves_delta D h71c h81 hZ hZ' hij) (P2d1.comm_moves_delta' D h71c h81 hZ hZ' hij)

end CFSG.Quasithin.Fan86
