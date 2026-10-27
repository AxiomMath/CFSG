module

public import CFSG.RankThree.PartOne.KS.HNFiveCheck
public import CFSG.RankThree.PartOne.S11c.HNFiveKernel
public import CFSG.Sporadic.HN
public import CFSG.RankThree.PartOne.KS.HNFiveInterface

public section

namespace CFSG.RankThree.PartOne.KS

open CFSG.RankThree.PartOne.KS.HNFive CFSG.Sporadic.GLQ CFSG.Sporadic.GLQ.HNTwoRank
  CFSG.Blueprint

theorem factorization_card_HN_five :
    (Nat.card NativeSporadic.HN).factorization 5 = 6 := by
  rw [CFSG.Sporadic.HN.card_HN,
    show 273030912000000 = 5 ^ 6 * (2 ^ 14 * 3 ^ 6 * 7 * 11 * 19) by norm_num,
    Nat.factorization_mul (by positivity) (by positivity), Finsupp.add_apply,
    Nat.Prime.factorization_pow Nat.prime_five, Finsupp.single_eq_same,
    Nat.factorization_eq_zero_of_not_dvd (by norm_num)]

theorem hnFiveLocalInterface_holds :
    HNRed.HNFiveLocalInterface := by
  let e : NativeSporadic.HN ≃* J := hnEquivJ
  let ι : NativeSporadic.HN →* GLHN := J.subtype.comp (e : NativeSporadic.HN →* J)
  have hι : Function.Injective ι := Subtype.val_injective.comp e.injective
  have hιe : ∀ r, ι (e.symm ⟨Rg r, Rg_mem r⟩) = Rg r := fun r => by
    show ((e (e.symm ⟨Rg r, Rg_mem r⟩) : J) : GLHN) = Rg r
    rw [MulEquiv.apply_symm_apply]
  have hrel : Rel (fun j => e.symm ⟨Rg (iQ j), Rg_mem _⟩) (e.symm ⟨Rg iZ, Rg_mem _⟩)
      (e.symm ⟨Rg iX, Rg_mem _⟩) (fun j => e.symm ⟨Rg (iR j), Rg_mem _⟩) Mm XU cx BU cr := by
    apply Rel.of_injective ι hι
    simp only [hιe]
    exact hnFive_rel
  have hfin : Finite NativeSporadic.HN :=
    Nat.finite_of_card_ne_zero (by rw [CFSG.Sporadic.HN.card_HN]; norm_num)
  exact hrel.interface Tsub XU_ne_one Tsub_isPGroup BU_mem XU_mem_normalizer BU_exists_neg_one
    forms factorization_card_HN_five

end CFSG.RankThree.PartOne.KS
