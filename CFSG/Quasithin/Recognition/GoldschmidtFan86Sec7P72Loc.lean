module

public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec7P72Geo

public section

namespace CFSG.Quasithin.Fan86

open SimpleGraph

namespace P72

variable {V G : Type*} [Group G] [MulAction G V] {Γ : SimpleGraph V}

@[expose] def Lab3 (_ : FanTree Γ G) (L : ZLab Γ G) : Prop :=
  ∀ β a b c : V, valence Γ β = 3 → Γ.neighborSet β = {a, b, c} → a ≠ b → a ≠ c → b ≠ c →
    L.z a * L.z b * L.z c = 1

variable {F : FanTree Γ G} {L : ZLab Γ G}

theorem z_fix (h : Fan71c F L) {l : V} (hl : valence Γ l = 5) {w : V} (hw : Γ.dist l w ≤ 4) :
    L.z l • w = w :=
  (Fan71c.z_smul_eq_iff h hl w).2 hw

theorem z_move (h : Fan71c F L) {l : V} (hl : valence Γ l = 5) {w : V} (hw : 4 < Γ.dist l w) :
    L.z l • w ≠ w := fun hh => by
  have := (Fan71c.z_smul_eq_iff h hl w).1 hh
  omega

theorem z_mem_inf (h : Fan71c F L) {l : V} (hl : valence Γ l = 5) {u w : V}
    (hu : Γ.dist l u ≤ 4) (hw : Γ.dist l w ≤ 4) :
    L.z l ∈ MulAction.stabilizer G u ⊓ MulAction.stabilizer G w :=
  ⟨MulAction.mem_stabilizer_iff.2 (z_fix h hl hu), MulAction.mem_stabilizer_iff.2 (z_fix h hl hw)⟩

theorem z_mem_nbrStab (h : Fan71c F L) {l : V} (hl : valence Γ l = 5) {v : V}
    (hv : Γ.dist l v ≤ 3) : L.z l ∈ nbrStab Γ G v := by
  rw [mem_nbrStab]
  intro w hw
  apply z_fix h hl
  have h1 : Γ.dist v w = 1 := dist_eq_one_iff_adj.mpr hw
  have := F.isTree.connected.dist_triangle (u := l) (v := v) (w := w)
  omega

theorem z_not_mem_nbrStab (h : Fan71c F L) {l : V} (hl : valence Γ l = 5) {v w : V}
    (hvw : Γ.Adj v w) (hw : 4 < Γ.dist l w) : L.z l ∉ nbrStab Γ G v := fun hh =>
  z_move h hl hw (mem_nbrStab.1 hh w hvw)

theorem mul_mem_nbrStab (h : Fan71c F L) {v a w w' l l' : V} (hva : Γ.Adj v a)
    (hl : valence Γ l = 5) (hl' : valence Γ l' = 5) (hv : Γ.dist l v ≤ 4) (ha : Γ.dist l a ≤ 4)
    (hv' : Γ.dist l' v ≤ 4) (ha' : Γ.dist l' a ≤ 4) (hw : Γ.Adj v w) (hdw : 4 < Γ.dist l w)
    (hw' : Γ.Adj v w') (hdw' : 4 < Γ.dist l' w') : L.z l * L.z l' ∈ nbrStab Γ G v :=
  F.mul_mem_nbrStab_of_sq_eq_one hva (z_mem_inf h hl hv ha) (z_mem_inf h hl' hv' ha')
    (L.z_mul_self hl) (L.z_mul_self hl') (z_not_mem_nbrStab h hl hw hdw)
    (z_not_mem_nbrStab h hl' hw' hdw')

theorem nbrStab_fix {g : G} {v w : V} (hg : g ∈ nbrStab Γ G v) (hw : Γ.Adj v w) : g • w = w :=
  mem_nbrStab.1 hg w hw

theorem smul_eq_of_mul_mem {z z' : G} (hz2 : z * z = 1) {v w : V}
    (h : z * z' ∈ nbrStab Γ G v) (hw : Γ.Adj v w) : z' • w = z • w := by
  have h1 : z • (z' • w) = w := by
    have := nbrStab_fix h hw
    rwa [mul_smul] at this
  have h3 : z⁻¹ = z := inv_eq_of_mul_eq_one_right hz2
  have := eq_inv_smul_iff.2 h1
  rwa [h3] at this

theorem s_facts (h : Fan71c F L) {x0 x1 x2 x3 x4 : V} (h01 : Γ.Adj x0 x1) (h12 : Γ.Adj x1 x2)
    (h23 : Γ.Adj x2 x3) (h34 : Γ.Adj x3 x4) (n02 : x0 ≠ x2) (n13 : x1 ≠ x3) (n24 : x2 ≠ x4)
    (h0 : valence Γ x0 = 5) :
    L.z x4 • x0 = x0 ∧ L.z x4 • x1 = x1 ∧ ∀ ν, Γ.Adj x0 ν → x1 ≠ ν → L.z x4 • ν ≠ ν := by
  have hv4 := (val_arc4 F h01 h12 h23 h34 h0).2.2.2
  obtain ⟨-, -, a3, a4⟩ := dist_arc4 F.isTree h01 h12 h23 h34 n02 n13 n24
  exact ⟨z_fix h hv4 (by omega), z_fix h hv4 (by omega), fun ν hν hne =>
    z_move h hv4 (by rw [dist_arc4_ext F.isTree h01 h12 h23 h34 n02 n13 n24 hν hne]; omega)⟩

end P72

end CFSG.Quasithin.Fan86
