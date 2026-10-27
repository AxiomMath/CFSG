module

public import CFSG.RankThree.Chevalley.SteinbergCFPrimeFieldG2LocalCores

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8

open CFSG.ComponentClassification.OuterAutomorphisms (Outer)
open CFSG.Blueprint.Chevalley (adjointGroup)
open CFSG.LieType.Chevalley (odd_F4_and_nonexceptional_G2_automorphism_normal_form)
open CFSG.RankThree.Chevalley (ringEquiv_eq_one_of_card_eq_prime)

theorem card_outer_adjointGroup_G2_zmod_prime
    (p : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) (hp3 : p ≠ 3) :
    Nat.card (CFSG.ComponentClassification.OuterAutomorphisms.Outer
      (@CFSG.Blueprint.Chevalley.adjointGroup .G2 (ZMod p)
        (by
          letI : Fact p.Prime := ⟨hp⟩
          infer_instance))) = 1 := by
  letI : Fact p.Prime := ⟨hp⟩
  obtain ⟨-, Θ, -, -, hΘker, -⟩ :=
    odd_F4_and_nonexceptional_G2_automorphism_normal_form (p := p) (f := 1) hp hp2 le_rfl
      (ZMod p) (by rw [Nat.card_zmod, pow_one]) .G2 (Or.inr ⟨rfl, hp3⟩)
  haveI : Subsingleton (ZMod p ≃+* ZMod p) :=
    ⟨fun σ τ => by
      rw [ringEquiv_eq_one_of_card_eq_prime hp (Nat.card_zmod p) σ,
        ringEquiv_eq_one_of_card_eq_prime hp (Nat.card_zmod p) τ]⟩
  have htop : CFSG.ComponentClassification.OuterAutomorphisms.inner
      (adjointGroup .G2 (ZMod p)) = ⊤ := by
    change (MulAut.conj : adjointGroup .G2 (ZMod p) →*
      MulAut (adjointGroup .G2 (ZMod p))).range = ⊤
    rw [← hΘker, eq_top_iff]
    intro α _
    rw [MonoidHom.mem_ker]
    exact Subsingleton.elim _ _
  haveI : Subsingleton (Outer (adjointGroup .G2 (ZMod p))) :=
    QuotientGroup.subsingleton_iff.mpr htop
  exact Nat.card_of_subsingleton (1 : Outer (adjointGroup .G2 (ZMod p)))

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8
