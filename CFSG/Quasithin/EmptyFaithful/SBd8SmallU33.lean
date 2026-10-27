module

public import CFSG.Quasithin.EmptyFaithful.SBd8Trio
public import CFSG.Quasithin.EmptyFaithful.LRed3FourB
public import CFSG.Quasithin.Background.GoldschmidtS146RLatSmall
public import CFSG.Quasithin.H13.U3U33Fixed
public import CFSG.Quasithin.Background.B5FinG2U33
public import CFSG.Quasithin.Vol2.Ch3Sec2Lem328Cases
public import CFSG.CharacterTheory.Blocks.BrauerInduction
public import CFSG.CharacterTheory.Semidihedral.Principal.PrimeOrderSylowColumn
public import CFSG.CharacterTheory.TwoRankLowerBound.BrauerCharacterCriterion
public import CFSG.CharacterTheory.TwoRankLowerBound.NormalComplementCharacterSpace
public import CFSG.Quasithin.Background.A1cA132Action
public import CFSG.Quasithin.Background.A1cA133Three
public import CFSG.Quasithin.Background.B69Core
public import CFSG.Quasithin.Background.D2
public import CFSG.Quasithin.Background.D2Dihedral
public import CFSG.Quasithin.Background.E3
public import CFSG.Quasithin.Background.E3Nprime
public import CFSG.Quasithin.Background.E3OffenderB
public import CFSG.Quasithin.Background.E3Uniq
public import CFSG.Quasithin.Background.E4Solv
public import CFSG.Quasithin.Background.FFC7G
public import CFSG.Quasithin.Background.FFC8A
public import CFSG.Quasithin.Background.InternalSecB56B
public import CFSG.Quasithin.Background.ThreePrimeGroup
public import CFSG.Quasithin.EmptyFaithful.S14110
public import CFSG.Quasithin.EmptyFaithful.S152UGen
public import CFSG.Quasithin.EmptyFaithful.S153D44
public import CFSG.Quasithin.EmptyFaithful.S153Nine
public import CFSG.Quasithin.EmptyFaithful.SBd8NS
public import CFSG.Sporadic.Schreier.J4SSylow

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits

namespace SBd8

section U33G


theorem trioShape_u33G : TrioShape U33G u33Data.T := by
  have hA : Nat.card u33Data.A = 3 * Nat.card u33Data.T := by
    rw [CFSG.Quasithin.H13.U3.card_u33_A, u33_card_T]
  have hB : Nat.card u33Data.B = 3 * Nat.card u33Data.T := by
    rw [CFSG.Quasithin.H13.U3.card_u33_B, u33_card_T]
  have hAB : u33Data.A ≠ u33Data.B := by
    intro h
    have h1 := u33Data.inf_AB
    rw [h, inf_idem] at h1
    exact u33Data.T_ne_B h1.symm
  refine ⟨u33Extra.normalizer_T, u33Data.A, u33Data.B, hAB, ?_, ?_,
    lt_of_le_of_ne u33Data.T_le_A u33Data.T_ne_A, lt_of_le_of_ne u33Data.T_le_B u33Data.T_ne_B,
    hA, hB, fun Y hY => u33Data.lattice Y hY⟩
  · intro h
    have h1 := hA
    rw [h, Subgroup.card_top, CFSG.Quasithin.H13.U3.card_u33G, u33_card_T] at h1
    omega
  · intro h
    have h1 := hB
    rw [h, Subgroup.card_top, CFSG.Quasithin.H13.U3.card_u33G, u33_card_T] at h1
    omega

end U33G

section U33Abstract

variable {X : Type} [Group X] [Finite X]


theorem trioShape_U33
    (h : ∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = 2 ∧
      Nonempty (X ≃* ↥⁅CFSG.Open.quasithinG2 F, CFSG.Open.quasithinG2 F⁆))
    {U : Subgroup X} (hU : IsSylowTwoOf U ⊤) : TrioShape X U := by
  obtain ⟨F, _, _, hF, ⟨e⟩⟩ := h
  obtain ⟨g⟩ := CFSG.Quasithin.H13.nonempty_g2Two_commutator_equiv hF
  exact TrioShape.of_equiv_sylow (e.trans (g.trans u33EquivSubG2.symm)).symm
    CFSG.Quasithin.GoldS146R.isSylowTwoOf_u33_T trioShape_u33G hU

omit [Finite X] in
theorem trioIsPSU33
    (h : ∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = 2 ∧
      Nonempty (X ≃* ↥⁅CFSG.Open.quasithinG2 F, CFSG.Open.quasithinG2 F⁆)) : IsPSU 3 3 1 X := by
  obtain ⟨F, _, _, hF, ⟨e⟩⟩ := h
  obtain ⟨eP⟩ := lred3_equiv_g2derived_psu33 hF
  have hK9 : Nat.card (GaloisField 3 (2 * 1)) = (3 ^ 1) ^ 2 := by
    rw [GaloisField.card 3 (2 * 1) (by norm_num)]
    norm_num
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hne : ((3 : ℕ), 3 ^ 1) ≠ (3, 2) := fun h => absurd (congrArg Prod.snd h) (by norm_num)
  exact ⟨⟨Nat.prime_three, le_rfl, le_rfl, hne⟩, GaloisField 3 (2 * 1), inferInstance, inferInstance, hK9,
    ⟨e.trans eP.symm⟩⟩

end U33Abstract

end SBd8

end CFSG.Quasithin
