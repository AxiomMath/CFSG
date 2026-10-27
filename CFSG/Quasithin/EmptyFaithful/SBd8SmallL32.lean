module

public import CFSG.Quasithin.EmptyFaithful.SBd8Trio
public import CFSG.Quasithin.EmptyFaithful.SzN2Lin
public import CFSG.Quasithin.Background.GoldschmidtS146RLatSmall
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A312ListFlag5
public import CFSG.LieType.SteinbergBROddLinearThreeParabolic

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits

namespace SBd8

section Sl3

open Matrix CFSG.LocalAnalysis.ComponentInitial.LinearFlag

theorem eq_or_card_of_card_168 {X : Type} [Group X] [Finite X] [IsSimpleGroup X]
    (hcard : Nat.card X = 168) {U : Subgroup X} (hU : IsSylowTwoOf U ⊤) {Y : Subgroup X} (hUY : U ≤ Y)
    (hYtop : Y ≠ ⊤) : Y = U ∨ Nat.card ↥Y = 3 * Nat.card ↥U := by
  have hUc : Nat.card U = 8 :=
    CFSG.Quasithin.GoldS146R.card_eq_of_isSylowTwoOf_top (a := 3) (m := 21) (by omega) (by norm_num) hU
  have hdvd : Nat.card Y ∣ 168 := hcard ▸ Subgroup.card_subgroup_dvd_card Y
  have h8 : 8 ∣ Nat.card Y := hUc ▸ Subgroup.card_dvd_of_le hUY
  have hle : Nat.card Y ≤ 168 := Nat.le_of_dvd (by norm_num) hdvd
  have hcases : ∀ n < 169, n ∣ 168 → 8 ∣ n → n = 8 ∨ n = 24 ∨ n = 56 ∨ n = 168 := by
    decide +kernel
  have hmul := Subgroup.card_mul_index Y
  rw [hcard] at hmul
  rcases hcases _ (by omega) hdvd h8 with h | h | h | h
  · left
    exact (Subgroup.eq_of_le_of_card_ge hUY (by omega)).symm
  · right
    omega
  · exfalso
    have h3 : Y.index = 3 := by
      rw [h] at hmul
      omega
    apply hYtop
    refine CFSG.Quasithin.GoldS146R.eq_top_of_not_dvd_factorial_index Y ?_
    rw [h3, hcard]
    decide
  · exfalso
    exact hYtop ((Subgroup.card_eq_iff_eq_top Y).1 (by rw [h, hcard]))

variable {F : Type} [Field F] [Finite F]

theorem trioShape_sl3_unitriangular (hF : Nat.card F = 2) :
    TrioShape (SpecialLinearGroup (Fin 3) F) (unitriangular 3 F) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fintype F := Fintype.ofFinite F
  have hFc : Fintype.card F = 2 := by rw [← Nat.card_eq_fintype_card, hF]
  have : CharP F 2 := charP_of_card_eq_prime_pow (f := 1) (by rw [hFc, pow_one])
  have hK : ∃ k : ℕ, Nat.card F = 2 ^ k := ⟨1, by rw [hF, pow_one]⟩
  have hsimple : IsSimpleGroup (SpecialLinearGroup (Fin 3) F) :=
    CFSG.QuasithinUnique.Vol2Native.A312L.sl_isSimple_of_card_two hF le_rfl
  have hcard : Nat.card (SpecialLinearGroup (Fin 3) F) = 168 := by
    rw [CFSG.LieType.SteinbergBR.BlockPar.card_SL_three', hF]
    norm_num
  have hU : IsSylowTwoOf (unitriangular 3 F) ⊤ := CFSG.Quasithin.SzN2.isSylowTwoOf_unitriangular (by norm_num)
  have hN : Subgroup.normalizer (unitriangular 3 F : Set (SpecialLinearGroup (Fin 3) F)) =
      unitriangular 3 F := by
    rw [normalizer_unitriangular]
    exact le_antisymm (CFSG.QuasithinUnique.Vol2Native.A312L.upperTriangular_le_unitriangular hF)
      (unitriangular_le_upperTriangular 3 F)
  obtain ⟨P, hne, hmax, hnorm⟩ := CFSG.Quasithin.SzN2.sl3_rankTwoData hK (unitriangular 3 F) hU
  have hUP : ∀ j, unitriangular 3 F ≤ P j := fun j => Subgroup.le_normalizer.trans (hnorm j)
  have hcov : ∀ j, P j ⋖ ⊤ := fun j => (hmax (P j) (hUP j)).2 ⟨j, rfl⟩
  have hPtop : ∀ j, P j ≠ ⊤ := fun j => (hcov j).ne
  have hUlt : ∀ j, unitriangular 3 F < P j := by
    have key : ∀ j j' : Fin 2, P j ≠ P j' → unitriangular 3 F = P j → False := by
      intro j j' hjj h
      have hlt : P j < P j' := lt_of_le_of_ne (by rw [← h]; exact hUP j') hjj
      exact (hcov j).2 hlt (lt_top_iff_ne_top.2 (hPtop j'))
    intro j
    refine lt_of_le_of_ne (hUP j) fun h => ?_
    fin_cases j
    · exact key 0 1 hne h
    · exact key 1 0 hne.symm h
  have hcardP : ∀ j, Nat.card ↥(P j) = 3 * Nat.card ↥(unitriangular 3 F) := fun j => by
    rcases eq_or_card_of_card_168 hcard hU (hUP j) (hPtop j) with h | h
    · exact absurd h (hUlt j).ne'
    · exact h
  refine ⟨hN, P 0, P 1, hne, hPtop 0, hPtop 1, hUlt 0, hUlt 1, hcardP 0, hcardP 1, ?_⟩
  intro Y hUY
  by_cases hYtop : Y = ⊤
  · exact Or.inr (Or.inr (Or.inr hYtop))
  rcases eq_or_card_of_card_168 hcard hU hUY hYtop with h | h
  · exact Or.inl h
  rcases eq_top_or_exists_le_coatom Y with h' | ⟨M, hM, hYM⟩
  · exact absurd h' hYtop
  obtain ⟨j, rfl⟩ := (hmax M (hUY.trans hYM)).1 (covBy_top_iff.2 hM)
  have hYj : Y = P j := Subgroup.eq_of_le_of_card_ge hYM (by rw [h, hcardP j])
  fin_cases j
  · exact Or.inr (Or.inl hYj)
  · exact Or.inr (Or.inr (Or.inl hYj))

end Sl3

section L32

variable {X : Type} [Group X] [Finite X]

theorem trioShape_L32 {F : Type} [Field F] [Finite F] (hF : Nat.card F = 2)
    (e : X ≃* ↥(CFSG.Assembly.LowTwoRank.StatedSL 3 F)) {U : Subgroup X} (hU : IsSylowTwoOf U ⊤) :
    TrioShape X U := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fintype F := Fintype.ofFinite F
  have hFc : Fintype.card F = 2 := by rw [← Nat.card_eq_fintype_card, hF]
  have : CharP F 2 := charP_of_card_eq_prime_pow (f := 1) (by rw [hFc, pow_one])
  exact TrioShape.of_equiv_sylow
    ((CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL 3 F).trans e.symm)
    (CFSG.Quasithin.SzN2.isSylowTwoOf_unitriangular (by norm_num)) (trioShape_sl3_unitriangular hF) hU

end L32

end SBd8

end CFSG.Quasithin
