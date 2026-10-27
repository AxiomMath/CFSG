module

public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec6P62Br

public section

namespace CFSG.Quasithin.Fan86

namespace P518

open SimpleGraph CFSG.Quasithin.F6.GoldAmL3T P62

variable {V G : Type*} [Group G] [MulAction G V] {Γ : SimpleGraph V}

@[expose] def ActsTriv (B N : Subgroup G) (y : G) : Prop :=
  ∀ g ∈ B, y * g * y⁻¹ * g⁻¹ ∈ N

section Generic

variable {S B N : Subgroup G}

theorem ActsTriv.mul (hN : ∀ g ∈ S, ∀ h ∈ N, g * h * g⁻¹ ∈ N) {y y' : G} (hy : y ∈ S)
    (h1 : ActsTriv B N y) (h2 : ActsTriv B N y') : ActsTriv B N (y * y') := by
  intro g hg
  have e : y * y' * g * (y * y')⁻¹ * g⁻¹ =
      (y * (y' * g * y'⁻¹ * g⁻¹) * y⁻¹) * (y * g * y⁻¹ * g⁻¹) := by group
  rw [e]
  exact N.mul_mem (hN y hy _ (h2 g hg)) (h1 g hg)

theorem ActsTriv.inv (hB : ∀ g ∈ S, ∀ b ∈ B, g * b * g⁻¹ ∈ B) {y : G} (hy : y ∈ S)
    (h : ActsTriv B N y) : ActsTriv B N y⁻¹ := by
  intro g hg
  have hg' : y⁻¹ * g * y ∈ B := by simpa using hB y⁻¹ (S.inv_mem hy) g hg
  have h1 := h _ hg'
  have e : y⁻¹ * g * y⁻¹⁻¹ * g⁻¹ = (y * (y⁻¹ * g * y) * y⁻¹ * (y⁻¹ * g * y)⁻¹)⁻¹ := by group
  rw [e]
  exact N.inv_mem h1

theorem ActsTriv.conj (hB : ∀ g ∈ S, ∀ b ∈ B, g * b * g⁻¹ ∈ B)
    (hN : ∀ g ∈ S, ∀ h ∈ N, g * h * g⁻¹ ∈ N) {y h : G} (hh : h ∈ S) (hy : ActsTriv B N y) :
    ActsTriv B N (h * y * h⁻¹) := by
  intro g hg
  have hg' : h⁻¹ * g * h ∈ B := by simpa using hB h⁻¹ (S.inv_mem hh) g hg
  have e : h * y * h⁻¹ * g * (h * y * h⁻¹)⁻¹ * g⁻¹ =
      h * (y * (h⁻¹ * g * h) * y⁻¹ * (h⁻¹ * g * h)⁻¹) * h⁻¹ := by group
  rw [e]
  exact hN h hh _ (hy _ hg')

theorem ActsTriv.pow (hN : ∀ g ∈ S, ∀ h ∈ N, g * h * g⁻¹ ∈ N) {y : G} (hy : y ∈ S)
    (h : ActsTriv B N y) (n : ℕ) : ActsTriv B N (y ^ n) := by
  induction n with
  | zero =>
    intro g hg
    simp
  | succ n ih =>
    rw [pow_succ]
    exact ih.mul hN (S.pow_mem hy n) h

theorem ActsTriv.comm (hB : ∀ g ∈ S, ∀ b ∈ B, g * b * g⁻¹ ∈ B)
    (hN : ∀ g ∈ S, ∀ h ∈ N, g * h * g⁻¹ ∈ N) {x q : G} (hx : x ∈ S) (hq : q ∈ S)
    (h : ActsTriv B N x) : ActsTriv B N (x * q * x⁻¹ * q⁻¹) := by
  have h1 : ActsTriv B N (q * x * q⁻¹) := h.conj hB hN hq
  have h2 : ActsTriv B N (q * x * q⁻¹)⁻¹ :=
    h1.inv hB (S.mul_mem (S.mul_mem hq hx) (S.inv_mem hq))
  have h3 := ActsTriv.mul hN hx h h2
  have e : x * q * x⁻¹ * q⁻¹ = x * (q * x * q⁻¹)⁻¹ := by group
  rw [e]
  exact h3

end Generic

section Geometry

variable {F : FanTree Γ G} {L : ZLab Γ G} {T : Track Γ G} {a : ℤ}

theorem exists_nbr_not_nbrStab (F : FanTree Γ G) {v : V} {z : G} (hzK : z ∈ nbrStab Γ G v)
    (hz : z ∉ ballStab Γ G 2 v) : ∃ ν, Γ.Adj v ν ∧ z ∉ nbrStab Γ G ν := by
  by_contra hcon
  push Not at hcon
  apply hz
  rw [mem_ballStab]
  intro w hw
  have hconn := F.isTree.connected
  rcases (by omega : Γ.dist v w = 0 ∨ Γ.dist v w = 1 ∨ Γ.dist v w = 2) with h0 | h1 | h2
  · have : v = w := ((hconn.preconnected v w).dist_eq_zero_iff).1 h0
    subst this
    exact MulAction.mem_stabilizer_iff.1 (F.nbrStab_le_stabilizer v hzK)
  · exact mem_nbrStab.1 hzK w (SimpleGraph.dist_eq_one_iff_adj.1 h1)
  · obtain ⟨ν, hbr⟩ := exists_br F h2
    exact mem_nbrStab.1 (hcon ν hbr.1) w hbr.2.1

theorem smul_ne_of_not_nbrStab (F : FanTree Γ G) {v ν u : V} {y : G} (hyv : y • v = v)
    (hνv : Γ.Adj ν v) (hνu : Γ.Adj ν u) (huv : u ≠ v) (hy : y ∉ nbrStab Γ G ν) :
    y • u ≠ u := fun h => hy (F.fix_two_nbrs hνv hνu huv.symm hyv h)

end Geometry

end P518

end CFSG.Quasithin.Fan86
