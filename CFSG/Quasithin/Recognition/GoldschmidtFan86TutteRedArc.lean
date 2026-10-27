module

public import CFSG.Quasithin.Background.GoldschmidtAmalgamL3TArc
public import Mathlib.Data.Set.Card

public section

namespace CFSG.Quasithin.Fan86.Tutte.Red

open CFSG.Quasithin.F6.GoldAmL3T

variable {W : Type} {Γ : SimpleGraph W}

theorem exists_two_others {x y : W} (hcard : Nat.card (Γ.neighborSet x) = 3)
    (hxy : Γ.Adj x y) :
    ∃ a b : W, a ≠ b ∧ Γ.Adj x a ∧ a ≠ y ∧ Γ.Adj x b ∧ b ≠ y ∧
      ∀ c, Γ.Adj x c → c ≠ y → c = a ∨ c = b := by
  have hn : (Γ.neighborSet x).ncard = 3 := by
    rw [← Nat.card_coe_set_eq]
    exact hcard
  have hfin : (Γ.neighborSet x).Finite := Set.finite_of_ncard_ne_zero (by omega)
  have hmem : y ∈ Γ.neighborSet x := hxy
  have h2 : (Γ.neighborSet x \ {y}).ncard = 2 := by
    rw [Set.ncard_sdiff_singleton_of_mem hmem, hn]
  obtain ⟨a, b, hab, hset⟩ := Set.ncard_eq_two.mp h2
  have ha : a ∈ Γ.neighborSet x \ {y} := by rw [hset]; simp
  have hb : b ∈ Γ.neighborSet x \ {y} := by rw [hset]; simp
  refine ⟨a, b, hab, ha.1, ha.2, hb.1, hb.2, fun c hc hcy => ?_⟩
  have hc' : c ∈ Γ.neighborSet x \ {y} := ⟨hc, hcy⟩
  rw [hset] at hc'
  simpa using hc'

theorem exists_other {x y : W} (hcard : Nat.card (Γ.neighborSet x) = 3) (hxy : Γ.Adj x y) :
    ∃ w, Γ.Adj x w ∧ w ≠ y := by
  obtain ⟨a, -, -, ha, hay, -⟩ := exists_two_others hcard hxy
  exact ⟨a, ha, hay⟩

theorem swap_of_moves {x y c : W} (hcard : Nat.card (Γ.neighborSet x) = 3) (hxy : Γ.Adj x y)
    (σ : W → W) (hσ : Function.Injective σ) (hσx : σ x = x) (hσy : σ y = y)
    (hadj : ∀ u v, Γ.Adj u v → Γ.Adj (σ u) (σ v))
    (hc : Γ.Adj x c) (hcy : c ≠ y) (hmove : σ c ≠ c)
    {a b : W} (ha : Γ.Adj x a) (hay : a ≠ y) (hb : Γ.Adj x b) (hby : b ≠ y) (hab : a ≠ b) :
    σ a = b := by
  obtain ⟨d, e, hde, hd, hdy, he, hey, hall⟩ := exists_two_others hcard hxy
  have hmaps : ∀ u, Γ.Adj x u → u ≠ y → σ u = d ∨ σ u = e := by
    intro u hu huy
    have h1 : Γ.Adj x (σ u) := by
      have := hadj x u hu
      rwa [hσx] at this
    exact hall _ h1 (fun h => huy (hσ (h.trans hσy.symm)))
  have hdd := hmaps d hd hdy
  have hee := hmaps e he hey
  have hsw : σ d = e ∧ σ e = d := by
    rcases hall c hc hcy with hcd | hce
    · rw [hcd] at hmove
      have h1 : σ d = e := hdd.resolve_left hmove
      refine ⟨h1, ?_⟩
      refine hee.resolve_right fun h => hde (hσ (h1.trans h.symm))
    · rw [hce] at hmove
      have h1 : σ e = d := hee.resolve_right hmove
      refine ⟨?_, h1⟩
      refine hdd.resolve_left fun h => hde (hσ (h.trans h1.symm))
  rcases hall a ha hay with had | hae <;> rcases hall b hb hby with hbd | hbe
  · exact absurd (had.trans hbd.symm) hab
  · rw [had, hbe]
    exact hsw.1
  · rw [hae, hbd]
    exact hsw.2
  · exact absurd (hae.trans hbe.symm) hab

end CFSG.Quasithin.Fan86.Tutte.Red
