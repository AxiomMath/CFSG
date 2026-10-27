module

public import CFSG.LocalAnalysis.StandardType.GGResIISubB

public section

namespace CFSG.StandardType

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

@[expose] def GGResIIShapeOK {n : ℕ} (C : Matrix (Fin n) (Fin n) ℤ) (ib ic : Fin n) : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (V : Type) [AddCommGroup V] [Module (ZMod p) V]
    [Module.Finite (ZMod p) V] (g : Fin (n + 1) → (V ≃ₗ[ZMod p] V)) (h : Fin (n + 1) → V)
    (α : Fin (n + 1) → Module.Dual (ZMod p) V) (x y : V) (u v : ZMod p),
    p ≠ 2 → (∀ k w, g k w = w - α k w • h k) → (∀ k, α k (h k) = 2) →
    GGFTable (RingHom.id (ZMod p)) (ggStdTable (Int.cast) C ib ic u v) h x α →
    (∀ w : V, (∀ k, α k w = 0) → w = 0) →
    LinearIndependent (ZMod p) (fun i : Fin n => h i.castSucc) →
    (∀ w : V, (∀ i : Fin n, α i.castSucc w = 0) → w ∈ Submodule.span (ZMod p) {x}) →
    h (Fin.last n) ∈ Submodule.span (ZMod p) (Set.range fun i : Fin n => h i.castSucc) →
    (∀ k : Fin (n + 1), k ≠ ib.castSucc → α k y = 0) → y ∉ Submodule.span (ZMod p) {x} →
    (((C.det : ℤ) : ZMod p) ≠ 0 → Module.finrank (ZMod p) V = n + 1) →
    GGResIIConcl g h α ib

@[expose] def GGSubBData (q : ℕ) [NeZero q] {n : ℕ} (C : Matrix (Fin n) (Fin n) ℤ)
    (ib ic : Fin n) : Prop :=
  (∃ (κ : List ℤ) (v₀ : ℕ) (wits : List (ℕ × List (List ℕ) × GGCellWit n)),
      GGSubBCheck q C ib ic κ v₀ wits) ∨
    ∃ (κ : List ℤ) (i₀ : Fin n), GGSubBVac q C ib κ i₀

theorem ggResII_shape_ok {n : ℕ} {C : Matrix (Fin n) (Fin n) ℤ} (hsymm : ∀ i j, C i j = C j i)
    {ib ic : Fin n} (hbc : ib ≠ ic) {adj : Matrix (Fin n) (Fin n) ℤ} {d : ℤ}
    (hadj : adj * C = d • (1 : Matrix (Fin n) (Fin n) ℤ)) {L : List ℕ} (hL : ∀ q ∈ L, q.Prime)
    {Tr : GGTree n}
    (hchk : checkTree ((L.map (· ^ 20)).prod) (ggStdTableSym C ib ic) ib [conicPoly adj d ib ic] Tr
      = true)
    (hcells : ∀ q ∈ L, q ≠ 2 → ∀ [NeZero q], ((C.det : ℤ) : ZMod q) ≠ 0 →
      ∃ wits : List (ℕ × ℕ × GGCellWit n), GGCellCheck q C ib ic adj d wits)
    (hB : ∀ q : ℕ, q.Prime → q ≠ 2 → ∀ [NeZero q], ((C.det : ℤ) : ZMod q) = 0 →
      GGSubBData q C ib ic) :
    GGResIIShapeOK C ib ic := by
  intro p _ V _ _ _ g h α x y u v hp2 hg h2 hT hsep hLI hfix hdep hyK hyx hdimA
  by_cases hdetp : ((C.det : ℤ) : ZMod p) = 0
  · rcases hB p Fact.out hp2 hdetp with ⟨κ, v₀, wits, hsub⟩ | ⟨κ, i₀, hvac⟩
    · exact ggResII_subB_sound hsymm hbc hsub hp2 hg h2 hT hsep hLI hfix hdep hyK hyx
    · exact (ggResII_subB_vacuous hsymm hbc hvac hT hLI hfix hdep).elim
  · have hdim := hdimA hdetp
    by_cases hpL : p ∈ L
    · obtain ⟨wits, hcell⟩ := hcells p hpL hp2 hdetp
      exact ggResII_cell_sound hbc hadj hcell hp2 hdim hg h2 hT hsep hdep
    · exact ggResII_shape_sound hbc hadj hchk hp2 (ggResII_prod_ne_zero hL 20 hpL) hg h2 hT hsep
        hdep

end CFSG.StandardType
