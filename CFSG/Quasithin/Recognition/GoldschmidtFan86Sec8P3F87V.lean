module

public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec8P1D10Cal

public section

namespace CFSG.Quasithin.Fan86.F87

open SimpleGraph CFSG.Quasithin.F6.GoldAmL3T
open scoped Pointwise

variable {V G : Type*} [Group G] [MulAction G V] {Γ : SimpleGraph V}
  {F : FanTree Γ G} {L : ZLab Γ G} {α : V}

theorem fan73b_dset (h7 : Fan7 F L) (D : D10Set L α) :
    ballStab Γ G 2 α = L.zGroup 2 α ⊔ D.calpha ∧
      L.zGroup 2 α ⊓ D.calpha = Subgroup.zpowers (L.z α) := by
  obtain ⟨-, -, h71c, -, -, -, h73b, -⟩ := h7
  obtain ⟨P, h0, h4, h8, -, -⟩ := D.exists_arc8 F h71c (i := 2) (j := 0) (by decide)
  have hP : L.calpha P = D.calpha := by
    show nbrStab Γ G (P.vert 4) ⊓
        Subgroup.centralizer ({L.z (P.vert 0) * L.z (P.vert 8)} : Set G) =
      nbrStab Γ G α ⊓ Subgroup.centralizer ({D.x} : Set G)
    rw [h0, h8, h4]
    rfl
  have := h73b P (by rw [h4]; exact D.val)
  rw [h4, hP] at this
  exact this

theorem zSet_comm (h71c : Fan71c F L) {a b : G} (ha : a ∈ L.zSet 2 α) (hb : b ∈ L.zSet 2 α) :
    a * b = b * a := by
  obtain ⟨δ, hδ, hδ5, rfl⟩ := ha
  obtain ⟨δ', hδ', hδ'5, rfl⟩ := hb
  refine h71c.z_comm_of_dist_le hδ5 hδ'5 ?_
  have := F.isTree.connected.dist_triangle (u := δ) (v := α) (w := δ')
  have hc : Γ.dist δ α = Γ.dist α δ := SimpleGraph.dist_comm
  omega

theorem isMulCommutative_zGroup (h71c : Fan71c F L) : IsMulCommutative (L.zGroup 2 α) :=
  Subgroup.isMulCommutative_closure fun _ ha _ hb _ => zSet_comm h71c ha hb

theorem zGroup_comm (h71c : Fan71c F L) {a b : G} (ha : a ∈ L.zGroup 2 α)
    (hb : b ∈ L.zGroup 2 α) : a * b = b * a := by
  have := isMulCommutative_zGroup (α := α) h71c
  exact setLike_mul_comm ha hb

theorem zGroup_sq (h71c : Fan71c F L) {v : G} (hv : v ∈ L.zGroup 2 α) : v * v = 1 := by
  induction hv using Subgroup.closure_induction with
  | mem x hx =>
    obtain ⟨δ, -, hδ5, rfl⟩ := hx
    exact L.z_mul_self hδ5
  | one => simp
  | mul x y hx hy ihx ihy =>
    have hxy := zGroup_comm h71c hx hy
    calc x * y * (x * y) = x * (y * x) * y := by group
      _ = x * x * (y * y) := by rw [← hxy]; group
      _ = 1 := by rw [ihx, ihy, one_mul]
  | inv x hx ih => rw [← mul_inv_rev, ih, inv_one]

theorem z_mem_zGroup {δ : V} (hδ : Γ.dist α δ ≤ 2) (hv : valence Γ δ = 5) :
    L.z δ ∈ L.zGroup 2 α :=
  Subgroup.subset_closure ⟨δ, hδ, hv, rfl⟩

theorem zGroup_le_ballStab (h7 : Fan7 F L) (D : D10Set L α) :
    L.zGroup 2 α ≤ ballStab Γ G 2 α := by
  rw [(fan73b_dset h7 D).1]
  exact le_sup_left

theorem calpha_le_ballStab (h7 : Fan7 F L) (D : D10Set L α) : D.calpha ≤ ballStab Γ G 2 α := by
  rw [(fan73b_dset h7 D).1]
  exact le_sup_right

theorem ballStab_comm (h71c : Fan71c F L) {h v : G} (hh : h ∈ ballStab Γ G 2 α)
    (hv : v ∈ L.zGroup 2 α) : h * v = v * h := by
  have key : Commute h v := by
    induction hv using Subgroup.closure_induction with
    | mem x hx =>
      obtain ⟨δ, hδ, hδ5, rfl⟩ := hx
      exact (h71c.comm_z_iff hδ5 h).2 (mem_ballStab.1 hh δ hδ)
    | one => exact Commute.one_right h
    | mul x y _ _ ihx ihy => exact ihx.mul_right ihy
    | inv x _ ih => exact ih.inv_right
  exact key.eq

end CFSG.Quasithin.Fan86.F87
