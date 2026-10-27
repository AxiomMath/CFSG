module

public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec7Stmt

public section

namespace CFSG.Quasithin.Fan86

open SimpleGraph

variable {V G : Type*} [Group G] [MulAction G V] {Γ : SimpleGraph V}

theorem valence_smul (F : FanTree Γ G) (g : G) (v : V) :
    valence Γ (g • v) = valence Γ v := by
  unfold valence
  refine Nat.card_congr (Equiv.subtypeEquiv (MulAction.toPerm g⁻¹) fun w => ?_)
  have := F.adj_smul g⁻¹ (g • v) w
  simp only [inv_smul_smul] at this
  simp only [mem_neighborSet, MulAction.toPerm_apply]
  exact this.symm

namespace ZLab

variable (L : ZLab Γ G)

theorem z_mem_stabilizer {v : V} (hv : valence Γ v = 5) : L.z v ∈ MulAction.stabilizer G v :=
  (L.isCentral v hv).1

theorem z_ne_one {v : V} (hv : valence Γ v = 5) : L.z v ≠ 1 := (L.isCentral v hv).2.1

theorem z_mul_self {v : V} (hv : valence Γ v = 5) : L.z v * L.z v = 1 :=
  (L.isCentral v hv).2.2.1

theorem z_inv {v : V} (hv : valence Γ v = 5) : (L.z v)⁻¹ = L.z v :=
  inv_eq_of_mul_eq_one_right (L.z_mul_self hv)

theorem z_smul_self {v : V} (hv : valence Γ v = 5) : L.z v • v = v :=
  MulAction.mem_stabilizer_iff.1 (L.z_mem_stabilizer hv)

theorem comm_z_of_mem_stabilizer {v : V} (hv : valence Γ v = 5) {g : G}
    (hg : g ∈ MulAction.stabilizer G v) : g * L.z v = L.z v * g :=
  (L.isCentral v hv).2.2.2 g hg

theorem z_inv_smul (g : G) {v : V} (hv : valence Γ v = 5) :
    L.z (g⁻¹ • v) = g⁻¹ * L.z v * g := by
  simpa using L.equivariant g⁻¹ v hv

end ZLab

namespace Fan71c

variable {F : FanTree Γ G} {L : ZLab Γ G}

theorem z_smul_eq_iff (h : Fan71c F L) {l : V} (hl : valence Γ l = 5) (w : V) :
    L.z l • w = w ↔ Γ.dist l w ≤ 4 := by
  have h1 := h.1 l hl
  have h2 : w ∈ fixedPts (V := V) (L.z l) ↔ w ∈ {v | Γ.dist l v ≤ 4} := by rw [h1]
  exact h2

theorem z_mem_stabilizer_iff (h : Fan71c F L) {l : V} (hl : valence Γ l = 5) (w : V) :
    L.z l ∈ MulAction.stabilizer G w ↔ Γ.dist l w ≤ 4 := by
  rw [MulAction.mem_stabilizer_iff, h.z_smul_eq_iff hl]

theorem z_injective (h : Fan71c F L) {a b : V} (ha : valence Γ a = 5) (hb : valence Γ b = 5)
    (hab : L.z a = L.z b) : a = b := by
  by_contra hne
  exact h.2.1 a b ha hb hne hab

theorem z_comm_of_dist_le (h : Fan71c F L) {a b : V} (ha : valence Γ a = 5)
    (hb : valence Γ b = 5) (hab : Γ.dist a b ≤ 4) : L.z a * L.z b = L.z b * L.z a :=
  L.comm_z_of_mem_stabilizer hb ((h.z_mem_stabilizer_iff ha b).2 hab)

theorem comm_z_iff (h : Fan71c F L) {l : V} (hl : valence Γ l = 5) (g : G) :
    g * L.z l = L.z l * g ↔ g • l = l := by
  constructor
  · intro hc
    have h1 : L.z (g • l) = L.z l := by
      rw [L.equivariant g l hl, hc]
      group
    exact h.z_injective (by rw [valence_smul F]; exact hl) hl h1
  · intro hg
    exact L.comm_z_of_mem_stabilizer hl (MulAction.mem_stabilizer_iff.2 hg)

theorem mul_z_smul_ne (h : Fan71c F L) {a b : V} (hb : valence Γ b = 5) {w : V}
    (hw : L.z a • w = w) (hbw : 4 < Γ.dist b w) : (L.z a * L.z b) • w ≠ w := by
  intro h1
  rw [mul_smul] at h1
  have h2 : L.z b • w = w := by
    have h3 : L.z a • (L.z b • w) = L.z a • w := by rw [h1, hw]
    exact MulAction.injective (L.z a) h3
  exact absurd ((h.z_smul_eq_iff hb w).1 h2) (by omega)

end Fan71c

end CFSG.Quasithin.Fan86
