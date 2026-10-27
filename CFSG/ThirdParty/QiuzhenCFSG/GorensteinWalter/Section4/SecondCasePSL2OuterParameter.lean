module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCasePSL2NormalizerSylowNoncyclic
import Mathlib.Tactic

namespace CFSG
end CFSG
open CFSG

/-!
# The ambient dihedral parameter is at least two

In the aligned PSL₂ setup, if the ambient Sylow is not contained in the
selected component, then the dihedral parameter cannot be the order-four
case.  Indeed, in that case the aligned component Sylow is a noncyclic
subgroup of an order-four group, forcing equality and hence containment.
-/

noncomputable section

namespace CFSG.GorensteinWalter

universe u

/-- Failure of `S ≤ E` in the aligned PSL₂ setup forces the ambient
dihedral parameter to satisfy `2 ≤ m`. -/
public theorem secondCase_psl2_parameter_ge_two_of_aligned_not_le_component
    {G : Type u} [Group G] [Finite G]
    (c : CentralizerSetup G)
    (w : SecondCaseWitness c)
    (d : SecondCaseComponentData w)
    (K : Type u) [Field K] [Finite K]
    (hK : IsOddPrimePower (Nat.card K))
    (e : Nonempty ((d.E ⧸ Subgroup.center d.E) ≃* PSL2 K))
    (SM : Sylow 2 (↥w.M))
    (hSMleS : (SM : Subgroup w.M).map w.M.subtype ≤ (c.S : Subgroup G))
    (SE : Sylow 2 (↥d.E))
    (hSEamb : (SE : Subgroup d.E).map d.E.subtype =
      ((SM : Subgroup w.M).map w.M.subtype) ⊓ d.E)
    (hSnotE : ¬ (c.S : Subgroup G) ≤ d.E) :
    2 ≤ c.m := by
  classical
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_contra hm
  have hm_lt : c.m < 2 := Nat.lt_of_not_ge hm
  have hmge : 1 ≤ c.m := c.one_le_m
  have hm1 : c.m = 1 := by omega
  have hScard : Nat.card (c.S : Subgroup G) = 4 := by
    rcases c.dihedralEquiv with ⟨eS⟩
    calc
      Nat.card (c.S : Subgroup G) = Nat.card (DihedralGroup (2 ^ c.m)) :=
        Nat.card_congr eS.toEquiv
      _ = 4 := by rw [hm1, DihedralGroup.nat_card]; norm_num
  have hSEnc : ¬ IsCyclic SE :=
    secondCase_psl2_sylow_not_cyclic_of_component_le
      c w d K hK e d.E le_rfl SE
  obtain ⟨n, hn⟩ := (IsPGroup.iff_card.mp SE.isPGroup')
  let A : Subgroup G := (SE : Subgroup d.E).map d.E.subtype
  have hAleS : A ≤ (c.S : Subgroup G) := by
    intro x hx
    change x ∈ (SE : Subgroup d.E).map d.E.subtype at hx
    rw [hSEamb] at hx
    exact hSMleS hx.1
  have hAcardSE : Nat.card A = Nat.card (SE : Subgroup d.E) := by
    dsimp [A]
    exact Subgroup.card_map_of_injective d.E.subtype_injective
  have hAcardle : Nat.card A ≤ Nat.card (c.S : Subgroup G) :=
    Nat.le_of_dvd Nat.card_pos (Subgroup.card_dvd_of_le hAleS)
  have hSEge4 : 4 ≤ Nat.card (SE : Subgroup d.E) := by
    by_contra hlt
    have hSElt : Nat.card (SE : Subgroup d.E) < 4 :=
      Nat.lt_of_not_ge hlt
    have hnlt : n < 2 := by
      apply (Nat.pow_lt_pow_iff_right (by norm_num : 1 < (2 : ℕ))).mp
      simpa [hn] using hSElt
    rcases Nat.eq_zero_or_pos n with rfl | hnpos
    · apply hSEnc
      apply isCyclic_of_card_dvd_prime (p := 2)
      rw [hn]
      norm_num
    · have hn1 : n = 1 := by omega
      apply hSEnc
      apply isCyclic_of_card_dvd_prime (p := 2)
      rw [hn, hn1]
      norm_num
  have hAcard4 : Nat.card A = 4 := by
    have hAcardge : 4 ≤ Nat.card A := by
      rw [hAcardSE]
      exact hSEge4
    apply Nat.le_antisymm
    · rw [hScard] at hAcardle
      exact hAcardle
    · exact hAcardge
  have hAS : A = (c.S : Subgroup G) := by
    apply Subgroup.eq_of_le_of_card_ge hAleS
    rw [hScard, hAcard4]
  have hAleE : A ≤ d.E := by
    dsimp [A]
    exact Subgroup.map_subtype_le (SE : Subgroup d.E)
  apply hSnotE
  rw [← hAS]
  exact hAleE

end CFSG.GorensteinWalter
