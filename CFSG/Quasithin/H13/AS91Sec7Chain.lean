module

public import CFSG.Quasithin.H13.AS91Sec7Delta

public section

namespace CFSG.Quasithin.H13.AS91

open Subgroup CFSG.Open MulAction CFSG.Quasithin.Asc94
open scoped Pointwise

namespace Loc49

variable {G : Type} [Group G] [Finite G] {z : G} (c : Loc49 G z)

abbrev OnL (a : G ⧸ c.G1) (m : G ⧸ c.G2) : Prop := CInc c.G1 c.G2 a m

abbrev OnP (a : G ⧸ c.G1) (σ : G ⧸ c.G3) : Prop := CInc c.G1 c.G3 a σ

abbrev LnP (m : G ⧸ c.G2) (σ : G ⧸ c.G3) : Prop := CInc c.G2 c.G3 m σ

@[expose] def CoL (m n : G ⧸ c.G2) : Prop := ∃ σ, c.LnP m σ ∧ c.LnP n σ

theorem CoL.symm {m n : G ⧸ c.G2} (h : c.CoL m n) : c.CoL n m := by
  obtain ⟨σ, h1, h2⟩ := h
  exact ⟨σ, h2, h1⟩

@[expose] def Rh : ℕ → (G ⧸ c.G1) → (G ⧸ c.G1) → (G ⧸ c.G1) → Prop
  | 0, x, u, y => c.Delta.Adj x u ∧ c.Delta.Adj u y ∧ c.Delta.Adj x y
  | 1, x, u, y => (c.Delta.Adj x u ∧ c.Delta.Adj u y ∧ c.Delta.Adj x y) ∨
      (c.Delta.Adj x u ∧ c.Delta.Adj u y ∧ x ≠ y ∧
        ∃ m n, c.OnL u m ∧ c.OnL x m ∧ c.OnL u n ∧ c.OnL y n ∧ c.CoL m n)
  | 2, x, u, y => ((c.Delta.Adj x u ∧ c.Delta.Adj u y ∧ c.Delta.Adj x y) ∨
      (c.Delta.Adj x u ∧ c.Delta.Adj u y ∧ x ≠ y ∧
        ∃ m n, c.OnL u m ∧ c.OnL x m ∧ c.OnL u n ∧ c.OnL y n ∧ c.CoL m n)) ∨
      (c.Delta.Adj x u ∧ c.Delta.Adj u y ∧ x ≠ y ∧
        ∃ m n, c.OnL u m ∧ c.OnL x m ∧ c.OnL u n ∧ c.OnL y n ∧ n ∈ c.deltaAt 3 u m)
  | _, x, u, y => c.Delta.Adj x u ∧ c.Delta.Adj u y ∧ x ≠ y

theorem rh_one_iff {x u y : G ⧸ c.G1} : c.Rh 1 x u y ↔ c.Rh 0 x u y ∨
    (c.Delta.Adj x u ∧ c.Delta.Adj u y ∧ x ≠ y ∧
      ∃ m n, c.OnL u m ∧ c.OnL x m ∧ c.OnL u n ∧ c.OnL y n ∧ c.CoL m n) := Iff.rfl

theorem rh_two_iff {x u y : G ⧸ c.G1} : c.Rh 2 x u y ↔ c.Rh 1 x u y ∨
    (c.Delta.Adj x u ∧ c.Delta.Adj u y ∧ x ≠ y ∧
      ∃ m n, c.OnL u m ∧ c.OnL x m ∧ c.OnL u n ∧ c.OnL y n ∧ n ∈ c.deltaAt 3 u m) := Iff.rfl

theorem rh_three_iff {x u y : G ⧸ c.G1} :
    c.Rh 3 x u y ↔ c.Delta.Adj x u ∧ c.Delta.Adj u y ∧ x ≠ y := Iff.rfl

theorem hypB_of
    (hδ : ∀ (u : G ⧸ c.G1) (m n : G ⧸ c.G2), c.OnL u m → c.OnL u n →
      n ∈ c.deltaAt 3 u m → m ∈ c.deltaAt 3 u n)
    (hb2 : ∀ k < 3, ∀ x u y v z, c.Rh (k + 1) x u y → ¬ c.Rh 0 x u y → c.Rh 3 x v z →
      ¬ c.Rh 0 x v z →
        ∃ a b, dSet c.Delta c.Rh k x u y a ∧ comp c.Delta x v z b ∧
          induced c.Delta c.Rh (min k 1) a b)
    (hb3 : ∀ x y w, induced c.Delta c.Rh 1 x y → Dist2 c.Delta x y → c.Delta.Adj y w →
      Dist2 c.Delta x w → ∃ a, c.Delta.Adj x a ∧ c.Delta.Adj y a ∧ Perp c.Delta a w) :
    HypB c.Delta 3 c.Rh where
  symm k x u y h := by
    have tri : ∀ {x u y : G ⧸ c.G1}, (c.Delta.Adj x u ∧ c.Delta.Adj u y ∧ c.Delta.Adj x y) →
        (c.Delta.Adj y u ∧ c.Delta.Adj u x ∧ c.Delta.Adj y x) :=
      fun ⟨h1, h2, h3⟩ => ⟨h2.symm, h1.symm, h3.symm⟩
    have co : ∀ {x u y : G ⧸ c.G1}, (c.Delta.Adj x u ∧ c.Delta.Adj u y ∧ x ≠ y ∧
        ∃ m n, c.OnL u m ∧ c.OnL x m ∧ c.OnL u n ∧ c.OnL y n ∧ c.CoL m n) →
        (c.Delta.Adj y u ∧ c.Delta.Adj u x ∧ y ≠ x ∧
          ∃ m n, c.OnL u m ∧ c.OnL y m ∧ c.OnL u n ∧ c.OnL x n ∧ c.CoL m n) := by
      rintro x u y ⟨h1, h2, h3, m, n, h4, h5, h6, h7, σ, h8, h9⟩
      exact ⟨h2.symm, h1.symm, Ne.symm h3, n, m, h6, h7, h4, h5, σ, h9, h8⟩
    have d3 : ∀ {x u y : G ⧸ c.G1}, (c.Delta.Adj x u ∧ c.Delta.Adj u y ∧ x ≠ y ∧
        ∃ m n, c.OnL u m ∧ c.OnL x m ∧ c.OnL u n ∧ c.OnL y n ∧ n ∈ c.deltaAt 3 u m) →
        (c.Delta.Adj y u ∧ c.Delta.Adj u x ∧ y ≠ x ∧
          ∃ m n, c.OnL u m ∧ c.OnL y m ∧ c.OnL u n ∧ c.OnL x n ∧ n ∈ c.deltaAt 3 u m) := by
      rintro x u y ⟨h1, h2, h3, m, n, h4, h5, h6, h7, h8⟩
      exact ⟨h2.symm, h1.symm, Ne.symm h3, n, m, h6, h7, h4, h5, hδ u m n h4 h6 h8⟩
    match k, h with
    | 0, h => exact tri h
    | 1, Or.inl h => exact Or.inl (tri h)
    | 1, Or.inr h => exact Or.inr (co h)
    | 2, Or.inl (Or.inl h) => exact Or.inl (Or.inl (tri h))
    | 2, Or.inl (Or.inr h) => exact Or.inl (Or.inr (co h))
    | 2, Or.inr h => exact Or.inr (d3 h)
    | k + 3, h =>
      obtain ⟨h1, h2, h3⟩ := h
      exact ⟨h2.symm, h1.symm, Ne.symm h3⟩
  mono k hk x u y h := by
    match k, hk, h with
    | 0, _, h => exact Or.inl h
    | 1, _, h => exact Or.inl h
    | 2, _, Or.inl (Or.inl ⟨h1, h2, h3⟩) => exact ⟨h1, h2, h3.ne⟩
    | 2, _, Or.inl (Or.inr ⟨h1, h2, h3, _⟩) => exact ⟨h1, h2, h3⟩
    | 2, _, Or.inr ⟨h1, h2, h3, _⟩ => exact ⟨h1, h2, h3⟩
    | k + 3, hk, _ => exact absurd hk (by omega)
  zero x u y := Iff.rfl
  top x u y := Iff.rfl
  b2 := hb2
  b3 := hb3

theorem exists_frame {a : G ⧸ c.G1} {m : G ⧸ c.G2} (hm : c.OnL a m) :
    ∃ g : G, g • c.x0 = a ∧ g • c.l0 = m := by
  obtain ⟨g, hg1, hg2⟩ := hm
  refine ⟨g, ?_, ?_⟩
  · rw [← hg1]
    simp [Loc49.x0, basePt, MulAction.Quotient.smul_mk]
  · rw [← hg2]
    simp [Loc49.l0, basePt, MulAction.Quotient.smul_mk]

theorem onL_x0_inv_smul {g : G} {a : G ⧸ c.G1} (hg : g • c.x0 = a) {m : G ⧸ c.G2}
    (hm : c.OnL a m) : c.OnL c.x0 (g⁻¹ • m) := by
  rw [Loc49.OnL, ← cInc_smul c.G1 c.G2 g, smul_inv_smul, hg]
  exact hm

end Loc49

namespace ResM24

variable {G : Type} [Group G] [Finite G] {z : G} {c : Loc49 G z} (ρ : ResM24 c)

include ρ in
theorem deltaAt_symm (i : Fin 5)
    {u : G ⧸ c.G1} {m n : G ⧸ c.G2} (hm : c.OnL u m) (hn : c.OnL u n)
    (h : n ∈ c.deltaAt i u m) : m ∈ c.deltaAt i u n := by
  obtain ⟨g, hg, -⟩ := c.exists_frame hm
  rw [ρ.mem_deltaAt_iff i hg hm hn] at h
  rw [ρ.mem_deltaAt_iff i hg hn hm]
  exact M24G.delta_symm (ρ.isTrio_trio (c.onL_x0_inv_smul hg hm))
    (ρ.isTrio_trio (c.onL_x0_inv_smul hg hn)) h

include ρ in
theorem hypB_of
    (hb2 : ∀ k < 3, ∀ x u y v z, c.Rh (k + 1) x u y → ¬ c.Rh 0 x u y → c.Rh 3 x v z →
      ¬ c.Rh 0 x v z →
        ∃ a b, dSet c.Delta c.Rh k x u y a ∧ comp c.Delta x v z b ∧
          induced c.Delta c.Rh (min k 1) a b)
    (hb3 : ∀ x y w, induced c.Delta c.Rh 1 x y → Dist2 c.Delta x y → c.Delta.Adj y w →
      Dist2 c.Delta x w → ∃ a, c.Delta.Adj x a ∧ c.Delta.Adj y a ∧ Perp c.Delta a w) :
    HypB c.Delta 3 c.Rh :=
  c.hypB_of (fun _ _ _ hm hn h => ρ.deltaAt_symm 3 hm hn h) hb2 hb3

end ResM24

end CFSG.Quasithin.H13.AS91
