module

public import CFSG.Quasithin.Background.F918Z6Def

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique

section Swap

variable {V : Type} [CommGroup V] {D X : Subgroup (MulAut V)} {s : MulAut V}

theorem map_conj_sup_of_swap (h1 : X = D.map (MulAut.conj s).toMonoidHom)
    (h2 : D = X.map (MulAut.conj s).toMonoidHom) :
    (D ⊔ X).map (MulAut.conj s).toMonoidHom = D ⊔ X := by
  rw [Subgroup.map_sup, ← h1, ← h2, sup_comm]

theorem conj_inv_mem_sup_of_swap (h1 : X = D.map (MulAut.conj s).toMonoidHom)
    (h2 : D = X.map (MulAut.conj s).toMonoidHom) {y : MulAut V} (hy : y ∈ D ⊔ X) :
    s⁻¹ * y * s ∈ D ⊔ X := by
  have e : (MulAut.conj s).toMonoidHom (s⁻¹ * y * s) = y := by
    simp [MulAut.conj_apply, mul_assoc]
  have h : (MulAut.conj s).toMonoidHom (s⁻¹ * y * s) ∈
      (D ⊔ X).map (MulAut.conj s).toMonoidHom := by
    rw [e, map_conj_sup_of_swap h1 h2]
    exact hy
  exact (Subgroup.mem_map_iff_mem (MulAut.conj s).injective).mp h

theorem map_mem_fixV_of_swap (h1 : X = D.map (MulAut.conj s).toMonoidHom)
    (h2 : D = X.map (MulAut.conj s).toMonoidHom) {c : V} (hc : c ∈ fixV (D ⊔ X)) :
    s c ∈ fixV (D ⊔ X) := by
  intro y hy
  have h3 := hc (s⁻¹ * y * s) (conj_inv_mem_sup_of_swap h1 h2 hy)
  have e : y (s c) = s ((s⁻¹ * y * s) c) := by simp [MulAut.mul_apply]
  rw [e, h3]

theorem le_centSec_of_swap {C : Subgroup V} (h1 : X = D.map (MulAut.conj s).toMonoidHom)
    (hs : ∀ c ∈ C, s c ∈ C) (hD : D ≤ centSec ⊤ C) : X ≤ centSec ⊤ C := by
  intro x hx
  have hx' : x ∈ D.map (MulAut.conj s).toMonoidHom := h1 ▸ hx
  obtain ⟨d, hd, rfl⟩ := hx'
  refine ⟨fun _ => Iff.rfl, fun w _ => ?_⟩
  have h3 := (hD hd).2 (s⁻¹ w) trivial
  have h4 := hs _ h3
  have e : (MulAut.conj s).toMonoidHom d w * w⁻¹ = s (d (s⁻¹ w) * (s⁻¹ w)⁻¹) := by
    simp [MulAut.conj_apply, MulAut.mul_apply]
  rw [e]
  exact h4

theorem sup_le_centSec_of_swap (h1 : X = D.map (MulAut.conj s).toMonoidHom)
    (h2 : D = X.map (MulAut.conj s).toMonoidHom)
    (h : D ≤ centSec ⊤ (fixV (D ⊔ X)) ∨ X ≤ centSec ⊤ (fixV (D ⊔ X))) :
    D ⊔ X ≤ centSec ⊤ (fixV (D ⊔ X)) := by
  have hs : ∀ c ∈ fixV (D ⊔ X), s c ∈ fixV (D ⊔ X) := fun c hc => map_mem_fixV_of_swap h1 h2 hc
  rcases h with h | h
  · exact sup_le h (le_centSec_of_swap h1 hs h)
  · exact sup_le (le_centSec_of_swap h2 hs h) h

theorem commV_le_of_le_centSec {Y : Subgroup (MulAut V)} {C : Subgroup V}
    (h : Y ≤ centSec ⊤ C) : commV Y ≤ C := by
  rw [commV, Subgroup.closure_le]
  rintro _ ⟨x, hx, v, rfl⟩
  exact (h hx).2 v trivial

theorem false_of_swap_of_le_centSec [Nontrivial V]
    (h1 : X = D.map (MulAut.conj s).toMonoidHom) (h2 : D = X.map (MulAut.conj s).toMonoidHom)
    (hc : commV (D ⊔ X) = ⊤)
    (h : D ≤ centSec ⊤ (fixV (D ⊔ X)) ∨ X ≤ centSec ⊤ (fixV (D ⊔ X))) : False := by
  have hle := commV_le_of_le_centSec (sup_le_centSec_of_swap h1 h2 h)
  rw [hc] at hle
  have hbot : commV (D ⊔ X) = ⊥ := by
    rw [commV_eq_commSub, commSub_eq_bot_iff]
    exact hle
  rw [hc] at hbot
  obtain ⟨a, ha⟩ := exists_ne (1 : V)
  have : a ∈ (⊥ : Subgroup V) := hbot ▸ Subgroup.mem_top a
  exact ha (Subgroup.mem_bot.mp this)

end Swap

section IrrFromZ1

variable {V : Type} [CommGroup V] [Finite V] {D X : Subgroup (MulAut V)} {s : MulAut V}

theorem irr_of_Z1 (hZ1 : Z1Stmt) [Nontrivial V] (hexp : ∀ v : V, v ^ 2 = 1)
    (hcomm : ∀ g ∈ D, ∀ x ∈ X, g * x = x * g) (h1 : X = D.map (MulAut.conj s).toMonoidHom)
    (h2 : D = X.map (MulAut.conj s).toMonoidHom) (hc : commV (D ⊔ X) = ⊤)
    (hirrC : ∀ U : Subgroup V, (∀ g ∈ D ⊔ X, ∀ u ∈ U, g u ∈ U) → fixV (D ⊔ X) ≤ U →
      U = fixV (D ⊔ X) ∨ U = ⊤) :
    ∀ U : Subgroup V, (∀ g ∈ D ⊔ X, ∀ u ∈ U, g u ∈ U) → U = ⊥ ∨ U = ⊤ := by
  have hbot : fixV (D ⊔ X) = ⊥ :=
    hZ1 V hexp D X hcomm hc hirrC (fun h => false_of_swap_of_le_centSec h1 h2 hc (Or.inl h))
      (fun h => false_of_swap_of_le_centSec h1 h2 hc (Or.inr h))
  intro U hU
  rcases hirrC U hU (by rw [hbot]; exact bot_le) with h | h
  · exact Or.inl (h.trans hbot)
  · exact Or.inr h

end IrrFromZ1

end CFSG.Quasithin
