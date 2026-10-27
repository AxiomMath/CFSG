module

public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec7P74VN
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec7P74Arc

public section

namespace CFSG.Quasithin.Fan86

namespace P74

open SimpleGraph CFSG.Quasithin.F6.GoldAmL3T

variable {V G : Type*} [Group G] [MulAction G V] {Γ : SimpleGraph V}
variable {F : FanTree Γ G} {L : ZLab Γ G}

theorem eq_one_or_self_of_mem_zpowers {g y : G} (hg : g * g = 1) (hy : y ∈ Subgroup.zpowers g) :
    y = 1 ∨ y = g := by
  obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 hy
  have h2 : g ^ (2 : ℤ) = 1 := by rw [zpow_two, hg]
  rcases Int.even_or_odd' n with ⟨k, hk | hk⟩
  · left; rw [hk, zpow_mul, h2, one_zpow]
  · right; rw [hk, zpow_add_one, zpow_mul, h2, one_zpow, one_mul]

theorem zGroup_le_stabilizer (h71c : Fan71c F L) {α : V} :
    L.zGroup 2 α ≤ MulAction.stabilizer G α := by
  refine (Subgroup.closure_le _).2 ?_
  rintro _ ⟨δ, hd, h5, rfl⟩
  rw [SetLike.mem_coe, h71c.z_mem_stabilizer_iff h5, dist_comm]
  omega

theorem commute_of_ballStab_three (h71c : Fan71c F L) {α : V} (hα : valence Γ α = 5) {x : G}
    (hxmem : x ∈ MulAction.stabilizer G α) (hx5 : x ^ 5 = 1) {C : Subgroup G}
    (hCst : C ≤ MulAction.stabilizer G α) (hCx : ∀ c ∈ C, x * c = c * x)
    (hB : ballStab Γ G 2 α ≤ L.zGroup 2 α ⊔ C)
    (hVN : L.zGroup 2 α ⊓ ballStab Γ G 3 α = Subgroup.zpowers (L.z α)) {n : G}
    (hn : n ∈ ballStab Γ G 3 α) : x * n = n * x := by
  have hxα : x • α = α := MulAction.mem_stabilizer_iff.1 hxmem
  have hxz : x * L.z α = L.z α * x := L.comm_z_of_mem_stabilizer hα hxmem
  let Q : Subgroup G :=
    { carrier := {g | g ∈ MulAction.stabilizer G α ∧ x * g * x⁻¹ * g⁻¹ ∈ L.zGroup 2 α}
      one_mem' := ⟨one_mem _, by simp⟩
      mul_mem' := fun {a b} ha hb => by
        refine ⟨mul_mem ha.1 hb.1, ?_⟩
        have e : x * (a * b) * x⁻¹ * (a * b)⁻¹ =
            (x * a * x⁻¹ * a⁻¹) * (a * (x * b * x⁻¹ * b⁻¹) * a⁻¹) := by group
        rw [e]
        exact mul_mem ha.2 (zGroup_conj F L (MulAction.mem_stabilizer_iff.1 ha.1) hb.2)
      inv_mem' := fun {a} ha => by
        refine ⟨inv_mem ha.1, ?_⟩
        have e : x * a⁻¹ * x⁻¹ * a⁻¹⁻¹ = a⁻¹ * (x * a * x⁻¹ * a⁻¹)⁻¹ * a := by group
        rw [e]
        have := zGroup_conj F L (MulAction.mem_stabilizer_iff.1 (inv_mem ha.1)) (inv_mem ha.2)
        rwa [inv_inv] at this }
  have hVQ : L.zGroup 2 α ≤ Q := fun v hv =>
    ⟨zGroup_le_stabilizer h71c hv, mul_mem (zGroup_conj F L hxα hv) (inv_mem hv)⟩
  have hCQ : C ≤ Q := fun c hc => by
    refine ⟨hCst hc, ?_⟩
    have : x * c * x⁻¹ * c⁻¹ = 1 := by rw [hCx c hc]; group
    rw [this]; exact one_mem _
  have hnB : n ∈ ballStab Γ G 2 α := fixSet_anti (fun w hw => by
    show Γ.dist α w ≤ 3
    have : Γ.dist α w ≤ 2 := hw
    omega) hn
  have hcomm : x * n * x⁻¹ * n⁻¹ ∈ L.zGroup 2 α ⊓ ballStab Γ G 3 α :=
    Subgroup.mem_inf.2 ⟨(sup_le hVQ hCQ (hB hnB)).2,
      mul_mem (ballStab_conj_stab F hxα hn) (inv_mem hn)⟩
  rw [hVN] at hcomm
  rcases eq_one_or_self_of_mem_zpowers (L.z_mul_self hα) hcomm with h | h
  · calc x * n = x * n * x⁻¹ * n⁻¹ * n * x := by group
      _ = n * x := by rw [h]; group
  · exfalso
    have h1 : x * n * x⁻¹ = L.z α * n := by
      calc x * n * x⁻¹ = (x * n * x⁻¹ * n⁻¹) * n := by group
        _ = L.z α * n := by rw [h]
    have h2 : x * (x * n * x⁻¹) * x⁻¹ = n := by
      rw [h1]
      calc x * (L.z α * n) * x⁻¹ = (x * L.z α) * n * x⁻¹ := by group
        _ = L.z α * (x * n * x⁻¹) := by rw [hxz]; group
        _ = L.z α * (L.z α * n) := by rw [h1]
        _ = (L.z α * L.z α) * n := by group
        _ = n := by rw [L.z_mul_self hα, one_mul]
    have h5n : x * (x * (x * (x * (x * n * x⁻¹) * x⁻¹) * x⁻¹) * x⁻¹) * x⁻¹ = L.z α * n := by
      rw [h2, h2, h1]
    have hx' : x * x * x * x * x = 1 := by simpa [pow_succ, mul_assoc] using hx5
    have h5n' : x * (x * (x * (x * (x * n * x⁻¹) * x⁻¹) * x⁻¹) * x⁻¹) * x⁻¹ = n := by
      calc _ = (x * x * x * x * x) * n * (x * x * x * x * x)⁻¹ := by group
        _ = n := by rw [hx']; simp
    have h6 : L.z α * n = 1 * n := (h5n.symm.trans h5n').trans (one_mul n).symm
    exact L.z_ne_one hα (mul_right_cancel h6)

theorem ballStab_three_le_calpha (h40 : Fan40 F) (h64 : Fan64 F) (h71a : Fan71a F L)
    (h71c : Fan71c F L) (h72b : Fan72b F L) (h73b : Fan73b F L) {P : Arc Γ 8}
    (h5 : valence Γ (P.vert 4) = 5) : ballStab Γ G 3 (P.vert 4) ≤ L.calpha P := by
  intro n hn
  have hCst : L.calpha P ≤ MulAction.stabilizer G (P.vert 4) := fun c hc =>
    F.nbrStab_le_stabilizer _ (show c ∈ nbrStab Γ G (P.vert 4) ⊓
      Subgroup.centralizer ({xe L P} : Set G) from hc).1
  have hCx : ∀ c ∈ L.calpha P, xe L P * c = c * xe L P := fun c hc =>
    Subgroup.mem_centralizer_iff.1 (show c ∈ nbrStab Γ G (P.vert 4) ⊓
      Subgroup.centralizer ({xe L P} : Set G) from hc).2 _ (Set.mem_singleton _)
  have hxn := commute_of_ballStab_three h71c h5 (xe_mem_stabilizer h71c h5)
    (xe_pow_five h71a h5) hCst hCx (by rw [(h73b P h5).1]) 
    (zGroup_inf_ballStab_three h40 h64 h71a h71c h72b h5) hn
  rw [ZLab.calpha, Subgroup.mem_inf]
  refine ⟨fun w hw => hn w (by
    show Γ.dist (P.vert 4) w ≤ 3
    rw [dist_eq_one_iff_adj.2 hw]; norm_num), ?_⟩
  rw [Subgroup.mem_centralizer_iff]
  intro h hh
  rw [Set.mem_singleton_iff.1 hh]
  exact hxn

theorem ballStab_three_le_four (h40 : Fan40 F) (h64 : Fan64 F) (h71a : Fan71a F L)
    (h71c : Fan71c F L) (h72b : Fan72b F L) (h73b : Fan73b F L) {α : V}
    (hα : valence Γ α = 5) : ballStab Γ G 3 α ≤ ballStab Γ G 4 α := by
  intro n hn
  refine mem_ballStab.2 fun w hw => ?_
  by_cases hw3 : Γ.dist α w ≤ 3
  · exact mem_ballStab.1 hn w hw3
  · have hd : Γ.dist α w = 4 := by omega
    obtain ⟨P, hP4, hP8⟩ := exists_arc8_between F hd (i := 4) (by norm_num)
    have h5 : valence Γ (P.vert 4) = 5 := by rw [hP4]; exact hα
    have hle := ballStab_three_le_calpha h40 h64 h71a h71c h72b h73b h5
    rw [hP4] at hle
    have hnP := hle hn
    rw [calpha_eq_stab h71a h71c h5, Arc.mem_stab] at hnP
    have := hnP 8 le_rfl
    have hP8' : P.vert 8 = w := hP8
    rwa [hP8'] at this

end P74

end CFSG.Quasithin.Fan86
