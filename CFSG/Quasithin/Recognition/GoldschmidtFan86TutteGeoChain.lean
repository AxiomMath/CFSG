module

public import CFSG.Quasithin.Recognition.GoldschmidtFan86TutteGeoTrans
public import Mathlib.Algebra.Group.Subgroup.Actions
public import Mathlib.GroupTheory.GroupAction.Defs

public section

namespace CFSG.Quasithin.Fan86.Tutte.Geo

open CFSG.Quasithin.F6.GoldAmL3T CFSG.Quasithin.Fan86.Tutte.Red

variable {W : Type} {Γ : SimpleGraph W} {H : Type} [Group H] [MulAction H W] {s : ℕ}

@[expose] def chain (a : Arc Γ s) (H : Type) [Group H] [MulAction H W] (i : ℕ) : Subgroup H :=
  ⨅ j : Fin (s - i + 1), MulAction.stabilizer H (a.vert j)

theorem mem_chain {a : Arc Γ s} {i : ℕ} {g : H} :
    g ∈ chain a H i ↔ ∀ j, j ≤ s - i → g • a.vert j = a.vert j := by
  simp only [chain, Subgroup.mem_iInf, MulAction.mem_stabilizer_iff]
  exact ⟨fun h j hj => h ⟨j, by omega⟩, fun h j => h j (by omega)⟩

theorem chain_mono (a : Arc Γ s) (i : ℕ) : chain a H i ≤ chain a H (i + 1) := by
  intro g hg
  rw [mem_chain] at hg ⊢
  exact fun j hj => hg j (by omega)

theorem chain_zero (R : RegData Γ H s) (a : Arc Γ s) : chain a H 0 = ⊥ := by
  rw [Subgroup.eq_bot_iff_forall]
  intro g hg
  rw [mem_chain] at hg
  exact R.faith a g fun j hj => hg j (by omega)

theorem chain_eq_inf {a : Arc Γ s} {i : ℕ} (hi : i + 1 ≤ s) :
    chain a H i = chain a H (i + 1) ⊓ MulAction.stabilizer H (a.vert (s - (i + 1) + 1)) := by
  ext g
  rw [Subgroup.mem_inf, mem_chain, mem_chain, MulAction.mem_stabilizer_iff]
  constructor
  · intro h
    exact ⟨fun j hj => h j (by omega), h _ (by omega)⟩
  · rintro ⟨h1, h2⟩ j hj
    by_cases hj' : j ≤ s - (i + 1)
    · exact h1 j hj'
    · have : j = s - (i + 1) + 1 := by omega
      rw [this]
      exact h2

namespace RegData

variable (R : RegData Γ H s)

include R

theorem orbit_chain (a : Arc Γ s) {n : ℕ} (hn : n < s) :
    MulAction.orbit ↥(chain a H (s - n)) (a.vert (n + 1)) = extSet (truncTo a n (by omega)) := by
  have hmem : a.vert (n + 1) ∈ extSet (truncTo a n (by omega)) := by
    refine ⟨a.adj n hn, fun hn1 h => ?_⟩
    have := a.nb (n - 1) (by omega)
    rw [show n - 1 + 2 = n + 1 by omega] at this
    exact this h.symm
  ext w
  constructor
  · rintro ⟨g, rfl⟩
    have hg : ∀ i, i ≤ n →
        (g : H) • (truncTo a n (by omega)).vert i = (truncTo a n (by omega)).vert i := by
      intro i hi
      exact (mem_chain.1 g.2) i (by omega)
    exact R.smul_mem_extSet _ hg hmem
  · intro hw
    obtain ⟨h, hh, hw'⟩ := R.ext_trans hn (truncTo a n (by omega)) hmem hw
    refine ⟨⟨h, mem_chain.2 fun j hj => ?_⟩, hw'⟩
    exact hh j (by omega)

end RegData

end CFSG.Quasithin.Fan86.Tutte.Geo
