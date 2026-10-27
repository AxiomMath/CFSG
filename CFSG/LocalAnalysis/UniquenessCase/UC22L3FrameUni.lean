module

public import CFSG.LocalAnalysis.UniquenessCase.UC22L3FrameSplit
import CFSG.LocalAnalysis.UniquenessCase.UC22L3UniBlock
import CFSG.LocalAnalysis.UniquenessCase.UC22L3UniModel
import CFSG.LocalAnalysis.UniquenessCase.UC22L3UniAut
import CFSG.LocalAnalysis.UniquenessCase.UC22L3UniRho
import CFSG.LocalAnalysis.UniquenessCase.UC22L3UniUnipotent
import CFSG.LocalAnalysis.UniquenessCase.UC22L3UniLinear
import CFSG.GH74.KGroups.L3EpsUni
public import Certificates.Certificate43

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open Subgroup CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open scoped MatrixGroups

theorem l3FrameExists_psu : L3FrameExists .PSU := by
  intro X _ _ p hp hp5 hX
  obtain ⟨F, _, h, ⟨e₀⟩⟩ := L3Uni.exists_model hX
  have : Finite F := h.finite
  have : CharP F p := h.charP
  have hp2 : p ≠ 2 := by omega
  have hp3 : p ≠ 3 := by omega
  have hq : Odd (p ^ 1) := (hp.odd_of_ne_two hp2).pow
  have h5 : 5 ≤ p ^ 1 := by simpa using hp5
  have h2 : (2 : F) ≠ 0 := CFSG.GH74.KGroups.L3Eps.Uni.two_ne_zero_of_odd_pow h hq
  have hZ : Subgroup.center (primeFormP h ((1 : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F)) = ⊥ :=
    CFSG.GH74.KGroups.L3Eps.center_primeFormP_three_eq_bot h h5
  refine ⟨?_, F, inferInstance, inferInstance, inferInstance, ?_⟩
  · have he := Subgroup.map_center_eq e₀
    rw [hZ] at he
    rw [eq_bot_iff]
    intro x hx
    change x = 1
    have hxe : e₀ x ∈ (⊥ : Subgroup _) := he ▸ ⟨x, hx, rfl⟩
    exact (map_eq_one_iff e₀ e₀.injective).1 hxe
  · let Fr : L3Frame
        (MulAut (primeFormP h ((1 : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F))) p F :=
      { I := L3Uni.I h
        P := L3Uni.P h
        e := L3Uni.e h
        r := L3Uni.r h
        Kb := L3Uni.Kb h hq
        Zb := L3Uni.Zb h
        ρ := L3Uni.rho h h2
        I_normal := CFSG.ComponentClassification.OuterAutomorphisms.inner_normal _
        P_normal := L3Uni.P_normal h h5
        I_le_P := L3Uni.I_le_P h
        mul_mem_of_not_mem := fun g g' hg hg' => L3Uni.mul_mem_P_of_not_mem h rfl g g' hg hg' h5
        mem_I_of_two := L3Uni.mem_I_of_two h h5
        e_mem := L3Uni.e_mem_I h
        r_mem := L3Uni.r_mem_I h
        e_pow_four := L3Uni.e_pow_four h
        r_sq := L3Uni.r_sq h
        r_e := L3Uni.r_e h
        e_sq_ne := L3Uni.e_sq_ne h hq
        isCyclic_cent := L3Uni.isCyclic_cent h hq
        isPGroup_D8 := L3Uni.isPGroup_D8 h
        Kb_le := L3Uni.Kb_le h hq
        conj_mem_Kb := L3Uni.conj_mem_Kb h rfl h2 hq h5
        mem_Zb := L3Uni.mem_Zb h
        isCyclic_Zb := L3Uni.isCyclic_Zb h h2 h5
        eq_one_of_mem_Kb_Zb := fun _ hx hz ho => L3Uni.eq_one_of_mem_Kb_Zb h h2 hq h5 hx hz ho
        ρ_eq_one := L3Uni.rho_eq_one h h2 h5
        eight_dvd := L3Uni.eight_dvd h h2 hq
        ρ_ne := L3Uni.rho_ne h h2
        isPGroup_of_comm := L3Uni.isPGroup_of_comm h h2
        not_unip := L3Uni.not_unip h h2
        mem_Kb_of_inv := L3Uni.mem_Kb_of_inv h h2 hq
        comm_of_comm_Kb := fun _ hx hx1 hc _ hg hcomm => L3Uni.comm_of_comm_Kb h h5 hq hx hx1 hc hg hcomm
        comm_of_comm_Zb := fun _ hx hx1 _ _ hg hcomm => L3Uni.comm_of_comm_Zb h h5 h2 hx hx1 hg hcomm
        not_inv_Zb := fun _ hx hx1 ho _ hg => L3Uni.not_inv_Zb h h5 h2 hx hx1 ho hg
        comm_of_abelian := fun _ _ hAB hBP hBab h3B _ h6 he hr =>
          L3Uni.comm_of_abelian h h5 h2 hp3 hAB hBP hBab h3B h6 he hr
        exists_conj_Kb := L3Uni.exists_conj_Kb h rfl h2 hq h5
        comm_of_coprime_six := fun y _ hy R hR hn => L3Uni.comm_of_coprime_six h hp2 h5 hy hR hn }
    obtain ⟨Fr', hI, K', hK', hc, hKb⟩ := L3Uni.exists_frame_of_model e₀ Fr rfl
      (K := L3Uni.K₀ h hq) (L3Uni.perfect_K₀ h hq h5)
      (by simpa using L3Uni.card_K₀ h hq) rfl
    exact ⟨Fr', hI, K', hK', hc, hKb⟩

end CFSG.LocalAnalysis.UniquenessCase.UC22
