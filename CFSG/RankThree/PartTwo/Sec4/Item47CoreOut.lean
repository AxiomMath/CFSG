module

public import CFSG.LocalAnalysis.ComponentClassification.OuterAutomorphisms
public import CFSG.Blueprint.Catalog
public import CFSG.Sporadic.J4
import CFSG.RankThree.PartTwo.Sec4.Item47Bridges
import CFSG.LieType.Chevalley.G2ThreeAutomorphismNormalForm
import CFSG.Sporadic.ONOddCore.OuterOrder
import CFSG.Sporadic.Schreier.J4SThree
public import CFSG.LocalAnalysis.ComponentInitial.SelfCentralizingCoreAutomorphisms
public import CFSG.Sporadic.Schreier.J4SSylowBase1

public section

namespace CFSG.RankThree.PartTwo.Sec4

open CFSG CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.ComponentClassification.OuterAutomorphisms (Outer inner equivalence)

namespace Item47CoreOut

theorem card_outer_eq_of_ker_eq_inner {C Q : Type*} [Group C] [Group Q] (Θ : MulAut C →* Q)
    (hs : Function.Surjective Θ) (hker : Θ.ker = inner C) :
    Nat.card (Outer C) = Nat.card Q :=
  Nat.card_congr ((QuotientGroup.quotientMulEquivOfEq hker.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective Θ hs)).toEquiv

open CFSG.Sporadic.J4 CFSG.Sporadic.J4Schreier CFSG.LocalAnalysis.ComponentInitial in
theorem not_three_dvd_card_outer_J :
    ¬ 3 ∣ Nat.card (Outer J) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hCp : ¬ 3 ∣ Nat.card (pointwiseFixingAut H) := by
    intro h
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp
      CTU_J4_pointwise_local_binary_subgroup_automorphism_kernel_is_two_group.2
    rw [hk] at h
    exact absurd (Nat.prime_three.dvd_of_dvd_pow h) (by norm_num)
  exact not_dvd_card_outer_of_sylow_bound (by norm_num : 3 ≠ 2) S0Sylow N H
    (by rw [S0Sylow_coe]; exact N_le_S0) (by rw [S0Sylow_coe]; exact S0_le_H) isPGroup_N
    normalizer_N QT_unique_J4_local_normal_module_irreducible.2.2.2.2.2.2.2.2.2.le hCp
    (R3E_J4_Sylow_two_automorphism_group_is_two_group S0Sylow).2

end Item47CoreOut

open CFSG.LieType.Ree (ReeTag) in
theorem inputs47Core_outG23 :
    ∀ (X : Type) [Group X], Blueprint.ChevalleyExceptionalModel X .G2 3 1 →
      ¬ 3 ∣ Nat.card (Outer X) := by
  intro X _ hX
  obtain ⟨K, _, _, hK, ⟨e⟩⟩ := exists_mulEquiv_adjointGroup_G2 hX
  have : CharP K ReeTag.G2.prime :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic Nat.prime_three
      le_rfl hK
  obtain ⟨-, -, ⟨Θ, -, hs, hker⟩, -⟩ := G2_three_exact_automorphism_normal_form le_rfl K hK
  have hC : Nat.card (Outer (adjointGroup Tag.G2 K)) =
      Nat.card (Multiplicative (ZMod (2 * 1))) :=
    Item47CoreOut.card_outer_eq_of_ker_eq_inner Θ hs hker
  rw [Nat.card_congr (equivalence e).toEquiv, hC, Nat.card_congr Multiplicative.toAdd,
    Nat.card_zmod]
  norm_num

theorem inputs47Core_outJ4 :
    ¬ 3 ∣ Nat.card (Outer (Blueprint.NativeSporadic.Carrier .J4)) := by
  have h := @CFSG.Sporadic.J4Schreier.card_outer_congr NativeSporadic.J4 CFSG.Sporadic.J4.J _
    (Subgroup.toGroup CFSG.Sporadic.J4.J)
    (CFSG.Sporadic.J4.seedEquiv CFSG.Sporadic.J4.j4Facts.mat)
  change ¬ 3 ∣ Nat.card (Outer NativeSporadic.J4)
  rw [h]
  exact Item47CoreOut.not_three_dvd_card_outer_J

theorem inputs47Core_outON :
    ¬ 3 ∣ Nat.card (Outer (Blueprint.NativeSporadic.Carrier .ONan)) := by
  have h : Nat.card (Outer NativeSporadic.ON) ∣ 4 :=
    CFSG.Sporadic.ONOddCore.r3e_on_outer_order_divides_four.1
  intro h3
  exact absurd (h3.trans h) (by norm_num)

end CFSG.RankThree.PartTwo.Sec4
