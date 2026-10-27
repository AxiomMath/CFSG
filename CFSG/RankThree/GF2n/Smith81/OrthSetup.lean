module

public import CFSG.RankThree.GF2n.Smith81.Sec115Dim
public import CFSG.RankThree.GF2n.Smith81.Bridge

public section

namespace CFSG.RankThree.GF2n.Smith81

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
  CFSG.RankThree.GF2n CFSG.RankThree.GF2n.Stroth80
open scoped commutatorElement

variable {G : Type} [Group G]

structure SmithOrthCfg (M Q Z B : Subgroup G) : Prop extends Cfg M Q Z B where
  orth : OrthCase M Q Z B

theorem SmithOrthCfg.toRemCfg {M Q Z B : Subgroup G} (h : SmithOrthCfg M Q Z B) : RemCfg M Q Z B :=
  ⟨h.toCfg, Or.inl h.orth⟩

section Width

variable {M Q Z B : Subgroup G} {t : G}

theorem CaseE1.width (h : CaseE1 M Q Z B t) : Width Q Z 4 := h.1

theorem CaseE2.width {m : ℕ} (h : CaseE2 M Q Z B t m) : Width Q Z (2 * m) := by
  have h1 := h.2.1
  unfold Width
  rw [h1]
  congr 1
  ring

theorem OrthCase.exists_width (h : OrthCase M Q Z B) :
    ∃ n : ℕ, Width Q Z n ∧ Even n ∧ 4 ≤ n := by
  obtain ⟨t, -, h1 | ⟨m, hm⟩⟩ := h
  · exact ⟨4, h1.width, by decide, le_rfl⟩
  · exact ⟨2 * m, hm.width, even_two_mul m, by have := hm.1; omega⟩

theorem width_unique (H : StrothHyp M Q Z) {n n' : ℕ} (h : Width Q Z n) (h' : Width Q Z n') :
    n = n' := by
  have h4 := H.q4
  unfold Width at h h'
  have := Nat.pow_right_injective (by omega : 2 ≤ Nat.card Z) (h.symm.trans h')
  omega

end Width

section Gamma

variable [Finite G] {M Q Z X : Subgroup G} {x : G} {n : ℕ}

theorem hasDim_of_even (hs : Sit M Q Z X x) (hw : Width Q Z n) (hn : Even n)
    (hQ : Q ⊓ QB X = ⊥) : HasDim Q Z n x := by
  rcases (smith115Statement_holds G M Q Z X x hs n hw hQ).2.2.2 with h | ⟨hodd, -⟩
  · exact h
  · exact absurd hn (Nat.not_even_iff_odd.mpr hodd)

end Gamma

end CFSG.RankThree.GF2n.Smith81
