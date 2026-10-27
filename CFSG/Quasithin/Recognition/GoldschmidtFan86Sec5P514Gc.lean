module

public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec5P514Lbl0
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec8P1Z2Loc

public section

namespace CFSG.Quasithin.Fan86

namespace P514

open SimpleGraph

variable {V G : Type*} [Group G] [MulAction G V] {Γ : SimpleGraph V}

theorem gcirc_cases' (F : FanTree Γ G) {v q : V} (hvq : Γ.Adj v q) {h : G}
    (hh : h ∈ Gcirc Γ G v q) (hhn : h ∉ nbrStab Γ G v) {g : G} (hg : g ∈ Gcirc Γ G v q) :
    g ∈ nbrStab Γ G v ∨ h⁻¹ * g ∈ nbrStab Γ G v := by
  obtain ⟨φ, hφ, -⟩ := F.exists_edge_char hvq
  let e : ↥(MulAction.stabilizer G v ⊓ MulAction.stabilizer G q) := ⟨g, hg.1⟩
  let e' : ↥(MulAction.stabilizer G v ⊓ MulAction.stabilizer G q) := ⟨h, hh.1⟩
  have hp : Fan86.valence Γ v = 3 ∨ Fan86.valence Γ v = 5 := F.valence v
  have h2 : φ e * φ e = 1 := by
    rw [← map_mul]
    exact (hφ (e * e)).1 hg.2
  have h2' : φ e' * φ e' = 1 := by
    rw [← map_mul]
    exact (hφ (e' * e')).1 hh.2
  have h1' : φ e' ≠ 1 := fun h' => hhn ((hφ e').2 h')
  by_cases h1 : φ e = 1
  · exact Or.inl ((hφ e).2 h1)
  · right
    have h3 := units_sq_eq_one_unique hp (φ e) (φ e') h1 h2 h1' h2'
    have h4 : φ (e'⁻¹ * e) = 1 := by
      rw [map_mul, map_inv, ← h3, inv_mul_cancel]
    exact (hφ (e'⁻¹ * e)).2 h4

theorem cen_gcirc_of (F : FanTree Γ G) {v q : V} (hvq : Γ.Adj v q) {h W : G}
    (hh : h ∈ Gcirc Γ G v q) (hhn : h ∉ nbrStab Γ G v) (hWK : W ∈ nbrStab Γ G v)
    (hK : ∀ k ∈ nbrStab Γ G v, k * W = W * k) (hc : h * W = W * h) :
    W ∈ Cen (Gcirc Γ G v q) := by
  refine ⟨F.nbrStab_le_gcirc hvq hWK, fun g hg => ?_⟩
  rcases gcirc_cases' F hvq hh hhn hg with hg1 | hg1
  · exact hK g hg1
  · have hk := hK _ hg1
    calc g * W = h * (h⁻¹ * g) * W := by rw [mul_inv_cancel_left]
      _ = h * ((h⁻¹ * g) * W) := by rw [mul_assoc]
      _ = h * (W * (h⁻¹ * g)) := by rw [hk]
      _ = (h * W) * (h⁻¹ * g) := by rw [mul_assoc]
      _ = (W * h) * (h⁻¹ * g) := by rw [hc]
      _ = W * g := by rw [mul_assoc, mul_inv_cancel_left]

theorem comm_nbrStab_Lb (F : FanTree Γ G) {z : G} {α o u : V} (hz : z ∈ Cinv G α)
    (h1 : Γ.Adj α o) (h2 : Γ.Adj o u) {k : G} (hk : k ∈ nbrStab Γ G o) :
    k * Lb z α u = Lb z α u * k :=
  (Lb_cinv hz (exists_conj_of_adj F h1 h2)).2.2.2 k
    (MulAction.mem_stabilizer_iff.2 (mem_nbrStab.1 hk u h2))

end P514

end CFSG.Quasithin.Fan86
