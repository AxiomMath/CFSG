module

public import CFSG.Quasithin.Recognition.GoldschmidtFan86TreeBasic

public section

namespace CFSG.Quasithin.Fan86

open SimpleGraph CFSG.Quasithin.F6.GoldAmL3T

variable {V : Type*} {Γ : SimpleGraph V}

structure Line (Γ : SimpleGraph V) where
  vert : ℤ → V
  adj : ∀ i, Γ.Adj (vert i) (vert (i + 1))
  nb : ∀ i, vert i ≠ vert (i + 2)

namespace Line

@[expose] def arc (ℓ : Line Γ) (a : ℤ) (n : ℕ) : Arc Γ n where
  vert k := ℓ.vert (a + k)
  adj k _ := by
    have e : a + ((k + 1 : ℕ) : ℤ) = a + k + 1 := by push_cast; omega
    rw [e]
    exact ℓ.adj _
  nb k _ := by
    have e : a + ((k + 2 : ℕ) : ℤ) = a + k + 2 := by push_cast; omega
    rw [e]
    exact ℓ.nb _

@[expose] def rev (ℓ : Line Γ) : Line Γ where
  vert i := ℓ.vert (-i)
  adj i := by
    have := (ℓ.adj (-i - 1)).symm
    rwa [sub_add_cancel, show -i - 1 = -(i + 1) by omega] at this
  nb i := by
    have := (ℓ.nb (-i - 2)).symm
    rwa [show -i - 2 + 2 = -i by omega, show -i - 2 = -(i + 2) by omega] at this

@[simp] theorem rev_vert (ℓ : Line Γ) (i : ℤ) : ℓ.rev.vert i = ℓ.vert (-i) := rfl

@[expose] def smul {G : Type*} [Group G] [MulAction G V]
    (hadj : ∀ (g : G) (u v : V), Γ.Adj (g • u) (g • v) ↔ Γ.Adj u v) (g : G) (ℓ : Line Γ) :
    Line Γ where
  vert i := g • ℓ.vert i
  adj i := (hadj g _ _).2 (ℓ.adj i)
  nb i h := ℓ.nb i (MulAction.injective g h)

theorem arc_vert_zero (ℓ : Line Γ) (a : ℤ) (n : ℕ) : (ℓ.arc a n).vert 0 = ℓ.vert a := by
  simp [arc]

theorem arc_vert_last (ℓ : Line Γ) {a b : ℤ} (hab : a ≤ b) :
    (ℓ.arc a (b - a).toNat).vert (b - a).toNat = ℓ.vert b := by
  simp only [arc]
  congr 1
  omega

theorem dist_eq (hT : Γ.IsTree) (ℓ : Line Γ) {i j : ℤ} (hij : i ≤ j) :
    Γ.dist (ℓ.vert i) (ℓ.vert j) = (j - i).toNat := by
  have := Arc.dist_eq hT (ℓ.arc i (j - i).toNat) (j - i).toNat le_rfl
  rwa [arc_vert_zero, arc_vert_last ℓ hij] at this

theorem vert_injective (hT : Γ.IsTree) (ℓ : Line Γ) : Function.Injective ℓ.vert := by
  intro i j h
  wlog hij : i ≤ j generalizing i j
  · exact (this h.symm (by omega)).symm
  have := dist_eq hT ℓ hij
  rw [h, dist_self] at this
  omega

section Action

variable {G : Type*} [Group G] [MulAction G V]

theorem fixes_between (hT : Γ.IsTree)
    (hadj : ∀ (g : G) (u v : V), Γ.Adj (g • u) (g • v) ↔ Γ.Adj u v) (ℓ : Line Γ) {g : G}
    {i j k : ℤ} (hik : i ≤ k) (hkj : k ≤ j) (hi : g • ℓ.vert i = ℓ.vert i)
    (hj : g • ℓ.vert j = ℓ.vert j) : g • ℓ.vert k = ℓ.vert k := by
  have h0 : g • (ℓ.arc i (j - i).toNat).vert 0 = (ℓ.arc i (j - i).toNat).vert 0 := by
    rwa [arc_vert_zero]
  have hn : g • (ℓ.arc i (j - i).toNat).vert (j - i).toNat =
      (ℓ.arc i (j - i).toNat).vert (j - i).toNat := by
    rwa [arc_vert_last ℓ (hik.trans hkj)]
  have := Arc.fixes_of_ends hT hadj (ℓ.arc i (j - i).toNat) h0 hn (k - i).toNat (by omega)
  simp only [arc] at this
  rwa [show i + ((k - i).toNat : ℤ) = k by omega] at this

end Action

end Line

end CFSG.Quasithin.Fan86
