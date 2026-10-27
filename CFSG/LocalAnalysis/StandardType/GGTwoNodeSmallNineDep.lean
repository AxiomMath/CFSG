module

public import CFSG.LocalAnalysis.StandardType.GGTwoNodeSmallClosed
public import CFSG.LocalAnalysis.StandardType.GGTwoNodeSmallTransport
public import CFSG.LocalAnalysis.StandardType.GGTwoNodeSmallNineDepK
public import CFSG.LocalAnalysis.StandardType.GGTwoNodeSmallNineDepCoord
public import Certificates.Certificate708603

public section

namespace CFSG.StandardType

open CFSG.TwoNodeSmall

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

private theorem tnsNine_pts_bound : ∀ P ∈ pts8 () ++ pts9 () ++ pts9m (), P.bound = bound9 := by
  intro P hP
  simp only [List.mem_append, pts8, pts9, pts9m, List.mem_flatMap, List.mem_map, List.mem_filterMap] at hP
  rcases hP with (⟨e, -, o, -, q, -, rfl⟩ | ⟨e, -, o, -, us, -, q, -, rfl⟩) | ⟨e, -, o, -, q, -, rfl⟩ <;> rfl

theorem lr6NineDepPos_of_closed (hcl : ∀ P ∈ pts8 () ++ pts9 () ++ pts9m (), ∀ [Fact P.p.Prime], P.Closed) :
    LR6NineDepPos := by
  intro V _ _ hV h α x r ha αa t hF hr ht hha hx hK hnt hcard
  obtain ⟨S, MK, CK, ⟨s, hs, hS⟩, hW, hC, hpair, hc, -⟩ := hK
  have hchain : ∀ i j : ↥S, ((CK (some i) (some j) : ℤ) : ZMod 3) =
      ((CartanMatrix.A 8 (i : Fin 8) (j : Fin 8) : ℤ) : ZMod 3) := by
    intro i j
    rw [hpair (some i) (some j)]
    exact hF.pair i j
  have hself : ((CK none none : ℤ) : ZMod 3) = 2 := by
    rw [hpair none none]
    exact hha
  obtain ⟨o, ho, hoCK⟩ := ninedep_kopts s hs S hS MK CK hW hC hchain hself hc
  have hH : ∀ j : Fin 8, s ≤ (j : ℕ) → (j : ℕ) < s + 6 →
      α j ha = (((if (j : ℕ) - s = o.1 then o.2.1 else 0 : ℕ)) : ZMod 3) := by
    intro j h1 h2
    have hj : j ∈ S := (hS j).2 ⟨h1, h2⟩
    have h3 := (hoCK ⟨j, hj⟩).1
    rw [hpair (some ⟨j, hj⟩) none] at h3
    exact h3
  have hA : ∀ j : Fin 8, s ≤ (j : ℕ) → (j : ℕ) < s + 6 →
      αa (h j) = (((if (j : ℕ) - s = o.1 then o.2.2 else 0 : ℕ)) : ZMod 3) := by
    intro j h1 h2
    have hj : j ∈ S := (hS j).2 ⟨h1, h2⟩
    have h3 := (hoCK ⟨j, hj⟩).2
    rw [hpair none (some ⟨j, hj⟩)] at h3
    exact h3
  obtain ⟨D, nF, gens, x', b, hmem, e, hM⟩ :=
    ninedep_model hV h α x ha αa hF hha hx s hs o ho hH hA
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hb : b = bound9 := tnsNine_pts_bound _ hmem
  rcases Pt.facts_transport (⟨3, D, nF, gens, x', b⟩ : Pt) h α x r ha αa t hr ht e hM
      (hcl _ hmem) with ⟨g, hg, hgt⟩ | hlt | ⟨v, hv, hvx⟩ | hweyl
  · exact absurd hgt (hnt g hg)
  · exfalso
    have : bound9 < Nat.card ↥(lr6Group r t) := hb ▸ hlt
    rw [bound9_eq] at this
    exact absurd hcard (not_le.mpr this)
  · exact absurd (hF.fix v hv) hvx
  · exact hweyl

theorem lr6NineDepPos_of_certificate :
    LR6NineDepPos :=
  lr6NineDepPos_of_closed Certificates.certificate708603

end CFSG.StandardType
