module

public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec8P3F92Card

public section

namespace CFSG.Quasithin.Fan86

open SimpleGraph CFSG.Quasithin.F6.GoldAmL3T

variable {V G : Type*} [Group G] [MulAction G V] {Γ : SimpleGraph V}

namespace Sec9Cfg

variable {L : ZLab Γ G} (S : Sec9Cfg L) {F : FanTree Γ G}

theorem card_nbrStab_beta (h65 : Fan65 F) (h71c : Fan71c F L) :
    Nat.card (nbrStab Γ G S.beta) = 512 * Nat.card S.D.calpha := by
  have hαβ : Γ.Adj S.α S.beta := S.D.adj_start_beta 2
  have hα5 : Fan86.valence Γ S.α = 5 := S.D.val
  have hβ3 : Fan86.valence Γ S.beta = 3 := S.D.valence_beta F 2
  have hcard := F.card_stabilizer_eq h65 h71c S.D
  have hE : (MulAction.stabilizer G S.α ⊓ MulAction.stabilizer G S.beta).relIndex
      (MulAction.stabilizer G S.α) = 5 := by
    rw [Subgroup.inf_relIndex_left, F.relIndex_stabilizer_eq_valence hαβ le_rfl
      (fun u w hu hw => F.loc_trans S.α u w hu hw), hα5]
  have h1 := Subgroup.relIndex_mul_card
    (H := MulAction.stabilizer G S.α ⊓ MulAction.stabilizer G S.beta)
    (K := MulAction.stabilizer G S.α)
  rw [hE, inf_of_le_left inf_le_left] at h1
  have h2 := F.relIndex_nbrStab_eq_two hαβ.symm hβ3
  have hle : nbrStab Γ G S.beta ≤ MulAction.stabilizer G S.beta ⊓ MulAction.stabilizer G S.α :=
    fun g hg => ⟨F.nbrStab_le_stabilizer _ hg,
      MulAction.mem_stabilizer_iff.2 (mem_nbrStab.1 hg S.α hαβ.symm)⟩
  have h3 := Subgroup.relIndex_mul_card (H := nbrStab Γ G S.beta)
    (K := MulAction.stabilizer G S.beta ⊓ MulAction.stabilizer G S.α)
  rw [h2, inf_of_le_left hle, inf_comm (MulAction.stabilizer G S.beta)] at h3
  omega

theorem ballStab_four_beta (h7 : Fan7 F L) : ballStab Γ G 4 S.beta = ⊥ := by
  have h71c : Fan71c F L := h7.2.2.1
  obtain ⟨P, -, h4, -, -, -⟩ := S.D.exists_arc8 F h71c (i := 2) (j := 0) (by decide)
  have hv : Fan86.valence Γ (P.vert 4) = 5 := by rw [h4]; exact S.D.val
  exact (h7.2.2.2.2.2.2.2.1 P hv).2.2.2 S.beta (by rw [h4]; exact S.D.adj_start_beta 2)

end Sec9Cfg

end CFSG.Quasithin.Fan86
