module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection12.lemma_12_1_c

namespace CFSG
end CFSG
open CFSG

open scoped Pointwise

/-!
# lemma_12_1_d
-/

section Section12

variable {G : Type*} [Group G] [Finite G] [IsMinCE G]

/-- Lemma 12.1(d). -/
public theorem CFSG.lemma_12_1_d
    {M E E₁₂ E₁ E₂ E₃ : Subgroup G}
    (hM : M ∈ section9MaximalSubgroups G)
    (hE : section12EData M E E₁₂ E₁ E₂ E₃) :
    IsCyclic E₁ ∧ IsCyclic E₃ := by
  classical
  rcases hE with ⟨hcomp, hE12, hE1, hE2, hE3⟩
  rcases hE12 with ⟨hE12E, hHallE12⟩
  rcases hE1 with ⟨hE1E12, hHallE1⟩
  rcases hE3 with ⟨hE3E, hHallE3⟩
  constructor
  · have hE1Z : IsZGroup E₁ := by
      refine section12_isZGroup_of_prime_support_rank_le_one
        (E := E) (K := E₁) (π := section12Tau1Primes M)
        (hE1E12.trans hE12E) ?_ ?_
      · intro p hpE1
        exact hHallE1.p_in_pi_of_p_dvd_card p
          (by simpa [natCard_subgroupOf_eq _ _ hE1E12] using hpE1)
      · intro p hpτ1
        exact section12_tau1_primeRank_E_le_one hcomp hpτ1
    have hE1commutator : ⁅E₁, E₁⁆ = ⊥ :=
      section12_E1_commutator_eq_bot
        (M := M) (E := E) (E₁₂ := E₁₂) (E₁ := E₁) hcomp
        ⟨hE12E, hHallE12⟩ ⟨hE1E12, hHallE1⟩
    have hE1comm : IsMulCommutative E₁ :=
      section12_isMulCommutative_of_commutator_eq_bot hE1commutator
    letI : IsZGroup E₁ := hE1Z
    letI : CommGroup E₁ := IsMulCommutative.instCommGroup
    haveI : Group.IsNilpotent E₁ := inferInstance
    infer_instance
  · have hE3Z : IsZGroup E₃ := by
      refine section12_isZGroup_of_prime_support_rank_le_one
        (E := E) (K := E₃) (π := section12Tau3Primes M) hE3E ?_ ?_
      · intro p hpE3
        exact hHallE3.p_in_pi_of_p_dvd_card p
          (by simpa [natCard_subgroupOf_eq _ _ hE3E] using hpE3)
      · intro p hpτ3
        exact section12_tau3_primeRank_E_le_one hcomp hpτ3
    have hE3_le_der : E₃ ≤ ambientDerivedSubgroup E :=
      (lemma_12_1_b (M := M) (E := E) (E₁₂ := E₁₂) (E₁ := E₁) (E₂ := E₂)
        (E₃ := E₃) hM
        ⟨hcomp, ⟨hE12E, hHallE12⟩, ⟨hE1E12, hHallE1⟩, hE2,
          ⟨hE3E, hHallE3⟩⟩).1
    have hnil_der : Group.IsNilpotent (ambientDerivedSubgroup E) :=
      lemma_12_1_a (M := M) (E := E) (E₁₂ := E₁₂) (E₁ := E₁) (E₂ := E₂)
        (E₃ := E₃) hM
        ⟨hcomp, ⟨hE12E, hHallE12⟩, ⟨hE1E12, hHallE1⟩, hE2,
          ⟨hE3E, hHallE3⟩⟩
    have hnil_E3 : Group.IsNilpotent E₃ := by
      let e : E₃.subgroupOf (ambientDerivedSubgroup E) ≃* E₃ :=
        Subgroup.subgroupOfEquivOfLe (H := E₃) (K := ambientDerivedSubgroup E) hE3_le_der
      haveI : Group.IsNilpotent (ambientDerivedSubgroup E) := hnil_der
      have hsubnil : Group.IsNilpotent (E₃.subgroupOf (ambientDerivedSubgroup E)) :=
        inferInstance
      exact Group.nilpotent_of_mulEquiv
        (G := E₃.subgroupOf (ambientDerivedSubgroup E)) (G' := E₃) e
    letI : IsZGroup E₃ := hE3Z
    haveI : Group.IsNilpotent E₃ := hnil_E3
    infer_instance

end Section12
