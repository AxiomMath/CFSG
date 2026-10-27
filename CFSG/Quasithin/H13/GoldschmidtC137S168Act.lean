module

public import CFSG.Quasithin.H13.GoldschmidtC137S168Syl

public section

namespace CFSG.Quasithin.H13.U3.GC137.SQ.S168

open MulAction

structure Frame (S : Type) [Group S] : Type where
  P : Sylow 7 S
  x : S
  y : S
  Q₀ : Sylow 7 S
  hx : x ∈ (P : Subgroup S)
  hy : y ∈ Subgroup.normalizer (P : Set S)
  hxo : orderOf x = 7
  hyo : orderOf y = 3
  hrel : y * x * y⁻¹ = x ^ 2
  hQP : Q₀ ≠ P
  hyQ : y • Q₀ = Q₀

theorem nonempty_frame {S : Type} [Group S] [Finite S] [IsSimpleGroup S]
    (hcard : Nat.card S = 168) : Nonempty (Frame S) := by
  have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  have : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  obtain ⟨P⟩ : Nonempty (Sylow 7 S) := inferInstance
  obtain ⟨x, y, hx, hy, hxo, hyo, hrel⟩ := exists_frobenius hcard P
  have hp3 : IsPGroup 3 (Subgroup.zpowers y) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hyo, pow_one])
  have hmod := hp3.card_modEq_card_fixedPoints (Sylow 7 S)
  rw [card_sylow_eight hcard P] at hmod
  have hyP : y • P = P := Sylow.smul_eq_iff_mem_normalizer.2 hy
  have hPfix : P ∈ fixedPoints (Subgroup.zpowers y) (Sylow 7 S) := by
    intro g
    have hg : (g : S) ∈ stabilizer S P :=
      (Subgroup.zpowers_le.2 (mem_stabilizer_iff.2 hyP)) g.2
    exact mem_stabilizer_iff.1 hg
  have hpos : 0 < Nat.card ↥(fixedPoints (Subgroup.zpowers y) (Sylow 7 S)) := by
    have : Nonempty ↥(fixedPoints (Subgroup.zpowers y) (Sylow 7 S)) := ⟨⟨P, hPfix⟩⟩
    exact Nat.card_pos
  have h2 : 1 < Nat.card ↥(fixedPoints (Subgroup.zpowers y) (Sylow 7 S)) := by
    unfold Nat.ModEq at hmod
    omega
  have hnt : Nontrivial ↥(fixedPoints (Subgroup.zpowers y) (Sylow 7 S)) :=
    Finite.one_lt_card_iff_nontrivial.1 h2
  obtain ⟨⟨Q₀, hQ₀⟩, hne⟩ := exists_ne (⟨P, hPfix⟩ : ↥(fixedPoints (Subgroup.zpowers y)
    (Sylow 7 S)))
  refine ⟨⟨P, x, y, Q₀, hx, hy, hxo, hyo, hrel, fun h => hne (Subtype.ext h), ?_⟩⟩
  exact hQ₀ ⟨y, Subgroup.mem_zpowers y⟩

end CFSG.Quasithin.H13.U3.GC137.SQ.S168
