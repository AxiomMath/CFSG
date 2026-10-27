module

public import CFSG.LocalAnalysis.SectionRank.Sporadic.MathieuLocal
public import CFSG.LocalAnalysis.SectionRank.Sporadic.J2Local
public import CFSG.LocalAnalysis.SectionRank.Sporadic.HSLocal
public import CFSG.LocalAnalysis.SectionRank.Sporadic.HeLocal
public import CFSG.LocalAnalysis.SectionRank.Sporadic.RuLocal
public import CFSG.LocalAnalysis.SectionRank.Sporadic.J4Local
public import CFSG.LocalAnalysis.SectionRank.Sporadic.TitsLocal
public import CFSG.Sporadic.Schreier.TitsOuter
public import CFSG.Quasithin.Background.A3FactsRank

public section

namespace CFSG.Quasithin

namespace A3Facts

open CFSG.Open CFSG.SectionRank CFSG.Blueprint CFSG.LieType.Ree


theorem oddRankTwo_M12
    [Finite NativeSporadic.M12] : OddRankTwo NativeSporadic.M12 := by
  obtain ⟨x, y, -, -, -, hxy, -, -, hcard, -⟩ := M12_sylow3_cubic_witness
  have := Fact.mk Nat.prime_three
  exact ⟨3, Nat.prime_three, by norm_num, two_le_pRank_of_cubic (by norm_num) hxy hcard⟩

theorem oddRankTwo_M24
    [Finite NativeSporadic.M24] : OddRankTwo NativeSporadic.M24 := by
  obtain ⟨x, y, -, -, -, hxy, -, -, hcard, -⟩ := M24_sylow3_cubic_witness
  have := Fact.mk Nat.prime_three
  exact ⟨3, Nat.prime_three, by norm_num, two_le_pRank_of_cubic (by norm_num) hxy hcard⟩

theorem oddRankTwo_J2
    [Finite NativeSporadic.J2] : OddRankTwo NativeSporadic.J2 := by
  obtain ⟨x, y, -, -, -, hxy, -, -, hcard, -⟩ := J2_sylow3_cubic_witness
  have := Fact.mk Nat.prime_three
  exact ⟨3, Nat.prime_three, by norm_num, two_le_pRank_of_cubic (by norm_num) hxy hcard⟩

theorem oddRankTwo_HS
    [Finite NativeSporadic.HS] : OddRankTwo NativeSporadic.HS := by
  obtain ⟨x, y, -, hx, hy, hxy, hcard, -⟩ := HS_sylow3_square_witness
  have := Fact.mk Nat.prime_three
  exact ⟨3, Nat.prime_three, by norm_num, two_le_pRank_of_square hx hy hxy hcard⟩

theorem oddRankTwo_He
    [Finite NativeSporadic.He] : OddRankTwo NativeSporadic.He := by
  obtain ⟨x, y, -, -, -, hxy, -, -, hcard, -⟩ := He_sylow3_cubic_witness
  have := Fact.mk Nat.prime_three
  exact ⟨3, Nat.prime_three, by norm_num, two_le_pRank_of_cubic (by norm_num) hxy hcard⟩

theorem oddRankTwo_Ru
    [Finite NativeSporadic.Ru] : OddRankTwo NativeSporadic.Ru := by
  obtain ⟨x, y, -, -, -, hxy, -, -, hcard, -⟩ := Ru_sylow3_cubic_witness
  have := Fact.mk Nat.prime_three
  exact ⟨3, Nat.prime_three, by norm_num, two_le_pRank_of_cubic (by norm_num) hxy hcard⟩

theorem oddRankTwo_J4
    [Finite NativeSporadic.J4] : OddRankTwo NativeSporadic.J4 := by
  obtain ⟨x, y, -, -, -, hxy, -, -, hcard, -⟩ := J4_sylow3_cubic_witness
  have := Fact.mk Nat.prime_three
  exact ⟨3, Nat.prime_three, by norm_num, two_le_pRank_of_cubic (by norm_num) hxy hcard⟩
abbrev m11GenA : NativeSporadic.M11 :=
  ⟨List.formPerm [1, 9] * List.formPerm [3, 10] * List.formPerm [4, 6] *
    List.formPerm [7, 8],
    Subgroup.subset_closure (Set.mem_insert _ _)⟩

abbrev m11GenB : NativeSporadic.M11 :=
  ⟨List.formPerm [0, 3, 2, 7] * List.formPerm [1, 4, 5, 8],
    Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)⟩

@[expose] def m11WordX : String :=
    "BaBabaB"

@[expose] def m11WordY : String :=
    "aBababb"

abbrev m22GenA : NativeSporadic.M22 :=
  ⟨List.formPerm [0, 12] * List.formPerm [1, 7] * List.formPerm [2, 15] *
    List.formPerm [3, 11] * List.formPerm [5, 21] * List.formPerm [6, 16] *
    List.formPerm [8, 9] * List.formPerm [10, 13],
    Subgroup.subset_closure (Set.mem_insert _ _)⟩

abbrev m22GenB : NativeSporadic.M22 :=
  ⟨List.formPerm [0, 21, 2, 20] * List.formPerm [1, 17, 3, 12] * List.formPerm [4, 11] *
    List.formPerm [5, 10, 6, 14] * List.formPerm [7, 13, 19, 9] * List.formPerm [16, 18],
    Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)⟩

@[expose] def m22WordX : String :=
    "BaBababa"

@[expose] def m22WordY : String :=
    "abaBaBababbaBababaB"

abbrev m23GenA : NativeSporadic.M23 :=
  ⟨List.formPerm [0, 1] * List.formPerm [2, 3] * List.formPerm [6, 7] *
    List.formPerm [8, 9] * List.formPerm [12, 13] * List.formPerm [14, 15] *
    List.formPerm [18, 19] * List.formPerm [20, 21],
    Subgroup.subset_closure (Set.mem_insert _ _)⟩

abbrev m23GenB : NativeSporadic.M23 :=
  ⟨List.formPerm [0, 15, 10, 2] * List.formPerm [1, 8, 20, 11] *
    List.formPerm [3, 4, 7, 22] * List.formPerm [5, 21, 13, 17] * List.formPerm [12, 19] *
    List.formPerm [14, 16],
    Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)⟩

@[expose] def m23WordX : String :=
    "BabbaB"

@[expose] def m23WordY : String :=
    "ababbaBabbababbaBabb"

theorem oddRankTwo_M11 [Finite NativeSporadic.M11] : OddRankTwo NativeSporadic.M11 := by
  set x := mathieuWord m11GenA m11GenB m11WordX.toList
  set y := mathieuWord m11GenA m11GenB m11WordY.toList
  have hx : x ^ 3 = 1 := by decide +kernel
  have hy : y ^ 3 = 1 := by decide +kernel
  have hxy : x * y = y * x := by decide +kernel
  have hx1 : x ≠ 1 := by decide +kernel
  have hy1 : y ≠ 1 := by decide +kernel
  have hyx : y ≠ x := by decide +kernel
  have hyx2 : y ≠ x ^ 2 := by decide +kernel
  have := Fact.mk Nat.prime_three
  refine ⟨3, Nat.prime_three, by norm_num, two_le_pRank_of_gens hx hy hxy hx1 fun n h => ?_⟩
  rcases (by omega : n % 3 = 0 ∨ n % 3 = 1 ∨ n % 3 = 2) with h0 | h1 | h2
  · rw [← Nat.mod_add_div n 3, pow_add, pow_mul, hx, one_pow, mul_one, h0, pow_zero] at h
    exact hy1 h.symm
  · rw [← Nat.mod_add_div n 3, pow_add, pow_mul, hx, one_pow, mul_one, h1, pow_one] at h
    exact hyx h.symm
  · rw [← Nat.mod_add_div n 3, pow_add, pow_mul, hx, one_pow, mul_one, h2] at h
    exact hyx2 h.symm

theorem oddRankTwo_M22 [Finite NativeSporadic.M22] : OddRankTwo NativeSporadic.M22 := by
  set x := mathieuWord m22GenA m22GenB m22WordX.toList
  set y := mathieuWord m22GenA m22GenB m22WordY.toList
  have hx : x ^ 3 = 1 := by decide +kernel
  have hy : y ^ 3 = 1 := by decide +kernel
  have hxy : x * y = y * x := by decide +kernel
  have hx1 : x ≠ 1 := by decide +kernel
  have hy1 : y ≠ 1 := by decide +kernel
  have hyx : y ≠ x := by decide +kernel
  have hyx2 : y ≠ x ^ 2 := by decide +kernel
  have := Fact.mk Nat.prime_three
  refine ⟨3, Nat.prime_three, by norm_num, two_le_pRank_of_gens hx hy hxy hx1 fun n h => ?_⟩
  rcases (by omega : n % 3 = 0 ∨ n % 3 = 1 ∨ n % 3 = 2) with h0 | h1 | h2
  · rw [← Nat.mod_add_div n 3, pow_add, pow_mul, hx, one_pow, mul_one, h0, pow_zero] at h
    exact hy1 h.symm
  · rw [← Nat.mod_add_div n 3, pow_add, pow_mul, hx, one_pow, mul_one, h1, pow_one] at h
    exact hyx h.symm
  · rw [← Nat.mod_add_div n 3, pow_add, pow_mul, hx, one_pow, mul_one, h2] at h
    exact hyx2 h.symm

theorem oddRankTwo_M23 [Finite NativeSporadic.M23] : OddRankTwo NativeSporadic.M23 := by
  set x := mathieuWord m23GenA m23GenB m23WordX.toList
  set y := mathieuWord m23GenA m23GenB m23WordY.toList
  have hx : x ^ 3 = 1 := by decide +kernel
  have hy : y ^ 3 = 1 := by decide +kernel
  have hxy : x * y = y * x := by decide +kernel
  have hx1 : x ≠ 1 := by decide +kernel
  have hy1 : y ≠ 1 := by decide +kernel
  have hyx : y ≠ x := by decide +kernel
  have hyx2 : y ≠ x ^ 2 := by decide +kernel
  have := Fact.mk Nat.prime_three
  refine ⟨3, Nat.prime_three, by norm_num, two_le_pRank_of_gens hx hy hxy hx1 fun n h => ?_⟩
  rcases (by omega : n % 3 = 0 ∨ n % 3 = 1 ∨ n % 3 = 2) with h0 | h1 | h2
  · rw [← Nat.mod_add_div n 3, pow_add, pow_mul, hx, one_pow, mul_one, h0, pow_zero] at h
    exact hy1 h.symm
  · rw [← Nat.mod_add_div n 3, pow_add, pow_mul, hx, one_pow, mul_one, h1, pow_one] at h
    exact hyx h.symm
  · rw [← Nat.mod_add_div n 3, pow_add, pow_mul, hx, one_pow, mul_one, h2] at h
    exact hyx2 h.symm

theorem oddRankTwo_tits
    {G : Type} [Group G] [Finite G]
    (h : CFSG.Blueprint.ReeTitsModel G .Tits 2 1) : OddRankTwo G := by
  obtain ⟨e⟩ := CFSG.Sporadic.Schreier.Tits.titsModelEquiv G 2 1 h
  have : Fact (Nat.card (ZMod 2) = 2) := ⟨by simp⟩
  have : CharP (ZMod 2) ReeTag.F4.prime := inferInstanceAs (CharP (ZMod 2) 2)
  let e' := e.trans (CFSG.Sporadic.Schreier.Tits.titsDerivedIso (K := ZMod 2)).symm
  obtain ⟨x, y, -, -, -, hxy, -, -, hcard, -⟩ :=
    Tits_sylow3_cubic_witness (K := ZMod 2) (by simp)
  have := Fact.mk Nat.prime_three
  have : Finite (commutator (reeFixed ReeTag.F4 (ZMod 2) 0)) := Finite.of_equiv G e'.toEquiv
  exact OddRankTwo.of_mulEquiv e'
    ⟨3, Nat.prime_three, by norm_num, two_le_pRank_of_cubic (by norm_num) hxy hcard⟩

end A3Facts

end CFSG.Quasithin
