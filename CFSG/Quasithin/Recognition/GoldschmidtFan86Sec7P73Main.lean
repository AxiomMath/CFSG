module

public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec7P73A

public section

namespace CFSG.Quasithin.Fan86

open SimpleGraph CFSG.Quasithin.F6.GoldAmL3T

namespace P73

variable {V G : Type*} [Group G] [MulAction G V] {Γ : SimpleGraph V}
variable {F : FanTree Γ G} {L : ZLab Γ G}

@[expose] def rightHalf (P : Arc Γ 8) : Arc Γ 4 where
  vert m := P.vert (4 + m)
  adj i hi := P.adj (4 + i) (by omega)
  nb i hi := P.nb (4 + i) (by omega)

@[expose] def leftHalf (P : Arc Γ 8) : Arc Γ 4 where
  vert m := P.vert (4 - m)
  adj i hi := by
    have h := (P.adj (4 - (i + 1)) (by omega)).symm
    rwa [show 4 - (i + 1) + 1 = 4 - i by omega] at h
  nb i hi := by
    have h := (P.nb (4 - (i + 2)) (by omega)).symm
    rwa [show 4 - (i + 2) + 2 = 4 - i by omega] at h

theorem exists_D_of_arc (F : FanTree Γ G) (h71a : Fan71a F L) (h71c : Fan71c F L) (P : Arc Γ 8)
    (hα : valence Γ (P.vert 4) = 5) :
    ∃ D : D10Set L (P.vert 4), D.calpha = L.calpha P := by
  have hne : (rightHalf P).vert 1 ≠ (leftHalf P).vert 1 := fun e => P.nb 3 (by norm_num) e.symm
  obtain ⟨D, hD0, hD2⟩ := P4X.exists_d10Set_arcs h71a h71c hα (rightHalf P) (leftHalf P) rfl rfl
    hne
  have h8 : D.delta 0 = P.vert 8 := hD0 4 le_rfl
  have h0 : D.delta 2 = P.vert 0 := hD2 4 le_rfl
  refine ⟨D, ?_⟩
  show nbrStab Γ G (P.vert 4) ⊓ Subgroup.centralizer ({L.z (D.delta 2) * L.z (D.delta 0)} : Set G)
    = nbrStab Γ G (P.vert 4) ⊓ Subgroup.centralizer ({L.z (P.vert 0) * L.z (P.vert 8)} : Set G)
  rw [h0, h8]

theorem fan73b_at {α : V} (D : D10Set L α) (F : FanTree Γ G) (h71a : Fan71a F L)
    (h71c : Fan71c F L) (h72b : Fan72b F L) (h40 : Fan40 F) (h64 : Fan64 F) (h65 : Fan65 F) :
    ballStab Γ G 2 α = L.zGroup 2 α ⊔ D.calpha ∧
      L.zGroup 2 α ⊓ D.calpha = Subgroup.zpowers (L.z α) := by
  have hα := D.val
  have hxs := D.x_mem_stabilizer F h71c
  have hBA := ballStab_le_nbrStab F α
  have hBst : ballStab Γ G 2 α ≤ MulAction.stabilizer G α := hBA.trans (F.nbrStab_le_stabilizer α)
  have hVB := zGroup_le_ballStab F h71c α
  have hCB := calpha_le_ballStab D F h71a h71c
  have hCV := index_CV D F h71c h40 h64
  have hb := relIndex_CB D F h71a h71c h40 h64 h65
  have hVst : L.zGroup 2 α ≤ MulAction.stabilizer G α := hVB.trans hBst
  constructor
  ·
    have hWB : L.zGroup 2 α ⊔ D.calpha ≤ ballStab Γ G 2 α := sup_le hVB hCB
    have hWst : L.zGroup 2 α ⊔ D.calpha ≤ MulAction.stabilizer G α := hWB.trans hBst
    have h1 : D.calpha.relIndex (L.zGroup 2 α) ≤ D.calpha.relIndex (L.zGroup 2 α ⊔ D.calpha) :=
      Subgroup.relIndex_le_of_le_right le_sup_left (relIndex_ne_zero F α hWst)
    have h2 := Subgroup.relIndex_mul_relIndex D.calpha (L.zGroup 2 α ⊔ D.calpha)
      (ballStab Γ G 2 α) le_sup_right hWB
    have h3 : (L.zGroup 2 α ⊔ D.calpha).relIndex (ballStab Γ G 2 α) ≠ 0 :=
      relIndex_ne_zero F α hBst
    have h4 : (L.zGroup 2 α ⊔ D.calpha).relIndex (ballStab Γ G 2 α) ≤ 1 := by
      by_contra hlt
      push Not at hlt
      have : 2 ^ 4 * 2 ≤ D.calpha.relIndex (L.zGroup 2 α ⊔ D.calpha) *
          (L.zGroup 2 α ⊔ D.calpha).relIndex (ballStab Γ G 2 α) :=
        Nat.mul_le_mul (by omega) hlt
      omega
    have h5 : (L.zGroup 2 α ⊔ D.calpha).relIndex (ballStab Γ G 2 α) = 1 := by omega
    exact le_antisymm (Subgroup.relIndex_eq_one.1 h5) hWB
  ·
    have hc := L.isCentral α hα
    have hzV : L.z α ∈ L.zGroup 2 α := P72.z_mem_zGroup (by rw [SimpleGraph.dist_self]; omega) hα
    have hzC : L.z α ∈ D.calpha := by
      refine Subgroup.mem_inf.2 ⟨P72.z_mem_nbrStab h71c hα (by rw [SimpleGraph.dist_self]; omega),
        ?_⟩
      rw [Subgroup.mem_centralizer_iff]
      intro g hg
      rw [Set.mem_singleton_iff] at hg
      rw [hg]
      exact hc.2.2.2 D.x hxs
    have hle : Subgroup.zpowers (L.z α) ≤ L.zGroup 2 α ⊓ D.calpha :=
      (Subgroup.zpowers_le).2 (Subgroup.mem_inf.2 ⟨hzV, hzC⟩)
    have hfin : Finite ↥(L.zGroup 2 α ⊓ D.calpha) := by
      have : Finite (MulAction.stabilizer G α) := F.loc_finite α
      have : Finite ↥(L.zGroup 2 α) :=
        Finite.of_injective (Subgroup.inclusion hVst) (Subgroup.inclusion_injective hVst)
      exact Finite.of_injective (Subgroup.inclusion (inf_le_left : L.zGroup 2 α ⊓ D.calpha ≤
        L.zGroup 2 α)) (Subgroup.inclusion_injective _)
    have hVcard := h72b α hα
    have hmul := Subgroup.card_mul_index ((L.zGroup 2 α ⊓ D.calpha).subgroupOf (L.zGroup 2 α))
    have hsub : Nat.card ↥((L.zGroup 2 α ⊓ D.calpha).subgroupOf (L.zGroup 2 α)) =
        Nat.card ↥(L.zGroup 2 α ⊓ D.calpha) :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv
    have hidx : ((L.zGroup 2 α ⊓ D.calpha).subgroupOf (L.zGroup 2 α)).index =
        D.calpha.relIndex (L.zGroup 2 α) := Subgroup.inf_relIndex_left _ _
    rw [hsub, hidx, hVcard] at hmul
    have hord : orderOf (L.z α) = 2 := by
      have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
      exact orderOf_eq_prime (by rw [pow_two]; exact L.z_mul_self hα) hc.2.1
    have hzcard : Nat.card ↥(Subgroup.zpowers (L.z α)) = 2 := by rw [Nat.card_zpowers, hord]
    have hq : Nat.card ↥(L.zGroup 2 α ⊓ D.calpha) ≤ Nat.card ↥(Subgroup.zpowers (L.z α)) := by
      rw [hzcard]
      by_contra hlt
      push Not at hlt
      have : 3 * 2 ^ 4 ≤ Nat.card ↥(L.zGroup 2 α ⊓ D.calpha) *
          D.calpha.relIndex (L.zGroup 2 α) := Nat.mul_le_mul hlt hCV
      omega
    exact (Subgroup.eq_of_le_of_card_ge hle hq).symm

theorem fan73b_of (F : FanTree Γ G) (h71a : Fan71a F L) (h71c : Fan71c F L) (h72b : Fan72b F L)
    (h40 : Fan40 F) (h64 : Fan64 F) (h65 : Fan65 F) : Fan73b F L := by
  intro P hα
  obtain ⟨D, hD⟩ := exists_D_of_arc F h71a h71c P hα
  rw [← hD]
  exact fan73b_at D F h71a h71c h72b h40 h64 h65

end P73

theorem fan_7_3 {V G : Type*} [Group G] [MulAction G V] {Γ : SimpleGraph V} {F : FanTree Γ G}
    {L : ZLab Γ G} (h71a : Fan71a F L) (h71c : Fan71c F L) (h72b : Fan72b F L) (h40 : Fan40 F)
    (h64 : Fan64 F) (h65 : Fan65 F) : Fan73a F ∧ Fan73b F L :=
  ⟨P73.fan73a_of F h71a h71c h40 h64 h65, P73.fan73b_of F h71a h71c h72b h40 h64 h65⟩

end CFSG.Quasithin.Fan86
