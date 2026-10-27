module

public import CFSG.RankThree.PartTwo.Sec4.T444.ONanItem434SporJ4Sound
public import CFSG.RankThree.PartTwo.Sec4.T444.Item434SporWords
public import CFSG.RankThree.PartTwo.Sec4.T444.Item434SporProof
public import Certificates.Certificate9715

public section

namespace CFSG.RankThree.PartTwo.Sec4

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.Blueprint
open CFSG.ComponentClassification.OuterAutomorphisms (Outer equivalence)
open scoped commutatorElement

namespace ONanJ4Nine

open Item434SporGen

theorem fixGen_mono {X : Type*} [Group X] {P Q : Subgroup X} (h : FixGen P) (hPQ : P ≤ Q) :
    FixGen Q := by
  obtain ⟨S, hS, hgen⟩ := h
  refine ⟨S, hS, fun σ hσ => ?_⟩
  obtain ⟨h3, p, hp, hp1, hpσ⟩ := hgen σ hσ
  exact ⟨h3, p, hPQ hp, hp1, hpσ⟩

theorem fixGen_of_conj_mem {X : Type*} [Group X] {a b g : X} {Q : Subgroup X}
    (h : FixGen (Subgroup.closure ({a, b} : Set X))) (ha : g * a * g⁻¹ ∈ Q)
    (hb : g * b * g⁻¹ ∈ Q) : FixGen Q := by
  refine fixGen_mono (h.map_conj g) ?_
  rw [MonoidHom.map_closure, Subgroup.closure_le]
  rintro _ ⟨t, ht, rfl⟩
  rcases ht with rfl | rfl
  · simpa using ha
  · simpa [Set.mem_singleton_iff] using hb

theorem fixGen_nine_of_core {Y : Type*} [Group Y] [Finite Y] {x y : Y} (hx : x ^ 3 = 1)
    (hy : y ^ 3 = 1) (hzx : Commute ⁅x, y⁆ x) (hzy : Commute ⁅x, y⁆ y) (hz1 : ⁅x, y⁆ ≠ 1)
    (hL : (Nat.card Y).factorization 3 = 3) (h0 : FixGen (Subgroup.closure ({⁅x, y⁆, x} : Set Y)))
    (h1 : ∃ g : Y, g * ⁅x, y⁆ * g⁻¹ ∈ Subgroup.closure ({⁅x, y⁆, x * y ^ 2} : Set Y) ∧
      g * x * g⁻¹ ∈ Subgroup.closure ({⁅x, y⁆, x * y ^ 2} : Set Y))
    (h2 : ∃ g : Y, g * ⁅x, y⁆ * g⁻¹ ∈ Subgroup.closure ({⁅x, y⁆, x * y} : Set Y) ∧
      g * x * g⁻¹ ∈ Subgroup.closure ({⁅x, y⁆, x * y} : Set Y))
    (h3 : ∃ g : Y, g * ⁅x, y⁆ * g⁻¹ ∈ Subgroup.closure ({⁅x, y⁆, y} : Set Y) ∧
      g * x * g⁻¹ ∈ Subgroup.closure ({⁅x, y⁆, y} : Set Y))
    (P : Subgroup Y) (hP9 : Nat.card P = 9) : FixGen P := by
  refine kill9_of_ex27 hx hy hzx hzy hz1 hL (fun i => ?_) P hP9
  fin_cases i
  · simpa [Asc83Table.ex27Rep] using h0
  · obtain ⟨g, hg1, hg2⟩ := h3
    simpa [Asc83Table.ex27Rep] using fixGen_of_conj_mem h0 hg1 hg2
  · obtain ⟨g, hg1, hg2⟩ := h2
    simpa [Asc83Table.ex27Rep] using fixGen_of_conj_mem h0 hg1 hg2
  · obtain ⟨g, hg1, hg2⟩ := h1
    simpa [Asc83Table.ex27Rep] using fixGen_of_conj_mem h0 hg1 hg2

theorem fixGen_j4 [Finite NativeSporadic.J4]
    (hL : (Nat.card NativeSporadic.J4).factorization 3 = 3) (P : Subgroup NativeSporadic.J4)
    (hP9 : Nat.card P = 9) : FixGen P := by
  obtain ⟨x, y, hx, hy, hzx, hzy, hz1, h0, h1, h2, h3⟩ :=
    fixSpec_sound (CFSG.SectionRank.spec2 112) Certificates.certificate9715
  exact fixGen_nine_of_core hx hy hzx hzy hz1 hL h0 h1 h2 h3 P hP9

end ONanJ4Nine

section Families


theorem item434Spor_J4_9 :
    Item434Spor_J4_9 := by
  obtain ⟨b⟩ := CFSG.Sporadic.Bridge.J4.nonempty_mulEquiv
  have b' : NativeSporadic.Carrier .J4 ≃* Spor .J4 := b
  have hcard : Nat.card (NativeSporadic.Carrier .J4) = 86775571046077562880 :=
    CFSG.Sporadic.J4.card_J4
  have hcard' : Nat.card NativeSporadic.J4 = 86775571046077562880 := hcard
  have : Finite NativeSporadic.J4 := Nat.finite_of_card_ne_zero (by rw [hcard']; norm_num)
  have hL : (Nat.card NativeSporadic.J4).factorization 3 = 3 := by
    rw [hcard', show (86775571046077562880 : ℕ) = 3 ^ 3 * 3213910038743613440 by norm_num,
      Item434AltPerm.factorization_three_pow_mul 3 (by norm_num)]
  refine Item434SporGen.item434SporAtCard_nine_of_kill9 b' inputs47Core_outJ4 ?_ ?_
  · rw [hcard]
    norm_num
  · intro P _ hP9
    exact Or.inl (ONanJ4Nine.fixGen_j4 hL P hP9)

end Families

end CFSG.RankThree.PartTwo.Sec4
