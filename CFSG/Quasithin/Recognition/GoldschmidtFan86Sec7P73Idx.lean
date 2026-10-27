module

public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec7P73Coord
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec7P73Cnt
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec7P72Cnt3
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec8P1D10Cal

public section

namespace CFSG.Quasithin.Fan86

open SimpleGraph CFSG.Quasithin.F6.GoldAmL3T

namespace P73

variable {V G : Type*} [Group G] [MulAction G V] {Γ : SimpleGraph V}
variable {F : FanTree Γ G} {L : ZLab Γ G} {α : V} (D : D10Set L α)

theorem ballStab_le_nbrStab (F : FanTree Γ G) (α : V) : ballStab Γ G 2 α ≤ nbrStab Γ G α :=
  fun _ hg => ((F.mem_ballStab_two_iff).1 hg).1

theorem relIndex_ne_zero (F : FanTree Γ G) (α : V) {H K : Subgroup G}
    (hK : K ≤ MulAction.stabilizer G α) : H.relIndex K ≠ 0 := by
  have : Finite (MulAction.stabilizer G α) := F.loc_finite α
  have : Finite K := Finite.of_injective (Subgroup.inclusion hK) (Subgroup.inclusion_injective hK)
  exact (Subgroup.finiteIndex_of_finite (H := H.subgroupOf K)).index_ne_zero

theorem calpha_le_ballStab (F : FanTree Γ G) (h71a : Fan71a F L) (h71c : Fan71c F L) :
    D.calpha ≤ ballStab Γ G 2 α := by
  intro c hc
  have hcA : c ∈ nbrStab Γ G α := (Subgroup.mem_inf.1 hc).1
  have hcα : c • α = α := MulAction.mem_stabilizer_iff.1 (F.nbrStab_le_stabilizer α hcA)
  rw [F.mem_ballStab_two_iff]
  refine ⟨hcA, fun γ hγ => ?_⟩
  obtain ⟨i, rfl⟩ := beta_surj D F h71c γ hγ
  have h1 : c • D.alpha i = D.alpha i := D.fix_of_mem_calpha F h71a h71c hc i (m := 2) (by norm_num)
  exact (mem_nbrStab_iff_fix F (D.adj_start_beta i).symm (D.adj_beta_alpha i)
    (D.alpha_ne_start i).symm hcα).2 h1

theorem zGroup_le_ballStab (F : FanTree Γ G) (h71c : Fan71c F L) (α : V) :
    L.zGroup 2 α ≤ ballStab Γ G 2 α := by
  refine (Subgroup.closure_le _).2 ?_
  rintro _ ⟨δ, hd, hv, rfl⟩
  refine mem_ballStab.2 fun w hw => (h71c.z_smul_eq_iff hv w).2 ?_
  have h1 := F.isTree.connected.dist_triangle (u := δ) (v := α) (w := w)
  have h2 : Γ.dist δ α = Γ.dist α δ := SimpleGraph.dist_comm
  omega

theorem index_CV (F : FanTree Γ G) (h71c : Fan71c F L) (h40 : Fan40 F) (h64 : Fan64 F) :
    2 ^ 4 ≤ D.calpha.relIndex (L.zGroup 2 α) := by
  have hα := D.val
  have hxs := D.x_mem_stabilizer F h71c
  have hx5 := D.orderOf_x F
  have hBst : ballStab Γ G 2 α ≤ MulAction.stabilizer G α :=
    (ballStab_le_nbrStab F α).trans (F.nbrStab_le_stabilizer α)
  have hVst : L.zGroup 2 α ≤ MulAction.stabilizer G α :=
    (zGroup_le_ballStab F h71c α).trans hBst
  have hCZ : D.calpha ≤ Subgroup.centralizer ({D.x} : Set G) := inf_le_right
  have hc := L.isCentral α hα
  have hcin : L.z α ∈ Cinv G α := ⟨hc.2.1, hc.2.2.1, hc.1, hc.2.2.2⟩
  obtain ⟨-, -, hidx⟩ := h64 h40 α (L.z α) hcin
  have hV : Subgroup.closure (zBall Γ α (L.z α) 2) = L.zGroup 2 α := by
    rw [← P72.zSet_eq_zBall F hα]
    rfl
  have hVZ : (Subgroup.centralizer ({D.x} : Set G)).relIndex (L.zGroup 2 α) = 2 ^ 4 := by
    have := hidx D.x hxs (by rw [hx5, hα])
    rwa [hV] at this
  have h1 : (Subgroup.centralizer ({D.x} : Set G)).relIndex (L.zGroup 2 α) ≤
      D.calpha.relIndex (L.zGroup 2 α) :=
    Subgroup.relIndex_le_of_le_left hCZ (relIndex_ne_zero F α hVst)
  omega

theorem index_data (F : FanTree Γ G) (h71a : Fan71a F L) (h71c : Fan71c F L) (h40 : Fan40 F)
    (h64 : Fan64 F) (h65 : Fan65 F) :
    D.calpha.relIndex (ballStab Γ G 2 α) * (ballStab Γ G 2 α).relIndex (nbrStab Γ G α) = 2 ^ 8 ∧
      2 ^ 4 ≤ D.calpha.relIndex (ballStab Γ G 2 α) ∧
      D.calpha.relIndex (ballStab Γ G 2 α) ≤ 2 ^ 6 := by
  have hα := D.val
  have hxs := D.x_mem_stabilizer F h71c
  have hx5 := D.orderOf_x F
  have hB := calpha_le_ballStab D F h71a h71c
  have hBA := ballStab_le_nbrStab F α
  have hBst : ballStab Γ G 2 α ≤ MulAction.stabilizer G α := hBA.trans (F.nbrStab_le_stabilizer α)
  have hVB := zGroup_le_ballStab F h71c α
  have hAC : D.calpha.relIndex (nbrStab Γ G α) = 2 ^ 8 := by
    have h := h65.1 α hα D.x hxs hx5
    have : D.calpha.relIndex (nbrStab Γ G α) =
        (Subgroup.centralizer ({D.x} : Set G)).relIndex (nbrStab Γ G α) :=
      Subgroup.inf_relIndex_left _ _
    rw [this]
    exact h
  have hVst : L.zGroup 2 α ≤ MulAction.stabilizer G α := hVB.trans hBst
  have hb16 : 2 ^ 4 ≤ D.calpha.relIndex (ballStab Γ G 2 α) := by
    have h1 := index_CV D F h71c h40 h64
    have h2 : D.calpha.relIndex (L.zGroup 2 α) ≤ D.calpha.relIndex (ballStab Γ G 2 α) :=
      Subgroup.relIndex_le_of_le_right hVB (relIndex_ne_zero F α hBst)
    omega
  have hb64 : D.calpha.relIndex (ballStab Γ G 2 α) ≤ 2 ^ 6 := by
    obtain ⟨P, -, h4, -, hP⟩ := D.calpha_eq_stab F h71a h71c
    have := stab_relIndex_le F hα P h4
    rw [← hP] at this
    omega
  refine ⟨?_, hb16, hb64⟩
  rw [Subgroup.relIndex_mul_relIndex _ _ _ hB hBA]
  exact hAC

theorem relIndex_AB (F : FanTree Γ G) (h71a : Fan71a F L) (h71c : Fan71c F L) (h40 : Fan40 F)
    (h64 : Fan64 F) (h65 : Fan65 F) :
    (ballStab Γ G 2 α).relIndex (nbrStab Γ G α) = 2 ^ 4 ∧ ∀ w, SigSet D w ↔ Wev w := by
  classical
  obtain ⟨hmul, hlo, hhi⟩ := index_data D F h71a h71c h40 h64 h65
  set a := (ballStab Γ G 2 α).relIndex (nbrStab Γ G α) with ha
  set b := D.calpha.relIndex (ballStab Γ G 2 α) with hb
  have ha4 : 4 ≤ a := by
    by_contra hlt
    push Not at hlt
    have : b * a ≤ 2 ^ 6 * 3 := Nat.mul_le_mul hhi (by omega)
    omega
  have ha16 : a ≤ 16 := by
    have : 2 ^ 4 * a ≤ b * a := Nat.mul_le_mul_right a hlo
    omega
  have hcard := relIndex_eq_card D F h71c
  rw [← ha] at hcard
  have hne : ∃ v, SigSet D v ∧ ∃ i j, v i ≠ v j := by
    by_contra hcon
    push Not at hcon
    have hsub : Finset.univ.filter (SigSet D) ⊆ {(0 : Fin 5 → ZMod 2), 1} := by
      intro v hv
      rw [Finset.mem_filter] at hv
      have := const_cases v (fun i j => hcon v hv.2 i j)
      simpa using this
    have := Finset.card_le_card hsub
    have h2 : ({(0 : Fin 5 → ZMod 2), 1} : Finset (Fin 5 → ZMod 2)).card ≤ 2 := Finset.card_le_two
    omega
  obtain ⟨v, hv, hvne⟩ := hne
  have hiff := eq_Wev (SigSet D) (SigSet_zero D) (fun a b => SigSet_add D F)
    (fun a => SigSet_sh D F h71c) hv hvne (by omega)
  have : (Finset.univ.filter (SigSet D)) = Finset.univ.filter Wev := by
    ext w
    simp [hiff w]
  rw [this, Wev_card] at hcard
  exact ⟨by omega, hiff⟩

theorem relIndex_CB (F : FanTree Γ G) (h71a : Fan71a F L) (h71c : Fan71c F L) (h40 : Fan40 F)
    (h64 : Fan64 F) (h65 : Fan65 F) : D.calpha.relIndex (ballStab Γ G 2 α) = 2 ^ 4 := by
  obtain ⟨hmul, -, -⟩ := index_data D F h71a h71c h40 h64 h65
  have := (relIndex_AB D F h71a h71c h40 h64 h65).1
  rw [this] at hmul
  omega

end P73

end CFSG.Quasithin.Fan86
