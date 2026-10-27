module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4RowM4MSylow
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4RowM4MTwoA
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4RowM4MTwoB
public import CFSG.LocalAnalysis.EvenSporadicStandard.Solomon78.LocMFacts

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Row

open CFSG.Quasithin CFSG.HardMathSupport.Meierfrankenfeld.FFToolkit Subgroup ArithmeticFunction

private theorem m4_card_centralizer_of_isConj {G : Type*} [Group G] {a b : G} (h : IsConj a b) :
    Nat.card (Subgroup.centralizer ({a} : Set G)) =
      Nat.card (Subgroup.centralizer ({b} : Set G)) := by
  obtain ⟨c, rfl⟩ := isConj_iff.1 h
  refine Nat.card_congr (Equiv.subtypeEquiv (MulAut.conj c).toEquiv fun g => ?_)
  rw [Subgroup.mem_centralizer_singleton_iff, Subgroup.mem_centralizer_singleton_iff]
  simp only [MulEquiv.toEquiv_eq_coe, MulEquiv.coe_toEquiv, MulAut.conj_apply]
  constructor
  · intro hg
    calc c * g * c⁻¹ * (c * a * c⁻¹) = c * (g * a) * c⁻¹ := by group
      _ = c * (a * g) * c⁻¹ := by rw [hg]
      _ = c * a * c⁻¹ * (c * g * c⁻¹) := by group
  · intro hg
    have h2 : c * (g * a) * c⁻¹ = c * (a * g) * c⁻¹ :=
      calc c * (g * a) * c⁻¹ = c * g * c⁻¹ * (c * a * c⁻¹) := by group
        _ = c * a * c⁻¹ * (c * g * c⁻¹) := hg
        _ = c * (a * g) * c⁻¹ := by group
    simpa using h2

theorem two_pow_four_le_index_of_two_classes {W : Type} [CommGroup W] [Finite W]
    (hW : ∀ w : W, w * w = 1) {G : Type} [Group G] [Finite G]
    [IsSimpleGroup CFSG.Blueprint.NativeSporadic.B] (ι : G →* MulAut W)
    (hι : Function.Injective ι) {c x : G} (hc2 : orderOf c = 2)
    (hcx : ∀ t : G, orderOf t = 2 → IsConj c t ∨ IsConj x t)
    (hord : (Nat.card (Subgroup.centralizer ({c} : Set G))).factorization 2 <
      (Nat.card G).factorization 2)
    (hA : CFSG.Monster.Existence.IsTwoACentralizer c)
    (hΩ : cardFactors (Nat.card ↥(Subgroup.centralizer ({c} : Set G))) ≤ 70)
    (hgen : ∃ cs : List G, cs.length ≤ 20 ∧
      Subgroup.closure {v : G | ∃ g ∈ cs, v = g * c * g⁻¹} = ⊤)
    (hcfg : ∃ (x y : Fin 4 → G) (z : G), HeisCfg 3 4 x y z)
    (hB : ∃ (x y : Fin 4 → CFSG.Blueprint.NativeSporadic.B)
      (z u : CFSG.Blueprint.NativeSporadic.B), HeisCfg 3 4 x y z ∧ (∀ i, y i ^ 3 = 1) ∧
        u ∈ Subgroup.closure (Set.range x ∪ Set.range y ∪ {z}) ∧
        u ∉ Subgroup.zpowers z ∧ IsConj u z) :
    ∀ g : G, orderOf g = 2 → 2 ^ 4 ≤ (fixV (zpowers (ι g))).index := by
  intro g hg2
  by_cases hcg : IsConj c g
  · obtain ⟨x, y, z, h⟩ := hcfg
    exact two_pow_four_le_index_of_gen hW ι hι hcg hgen h
  · obtain ⟨a, hca, hag, hat⟩ := exists_commute_isConj_of_not_isConj hcx hc2 hord g hg2 hcg
    have ha2 : orderOf a = 2 := by
      obtain ⟨k, rfl⟩ := isConj_iff.1 hca
      rw [← hc2]
      simpa using MulEquiv.orderOf_eq (MulAut.conj k) c
    have hAa : CFSG.Monster.Existence.IsTwoACentralizer a := by
      obtain ⟨k, rfl⟩ := isConj_iff.1 hca
      simpa using CFSG.EvenSporadicStandard.Solomon78.IsTwoACentralizer.map (MulAut.conj k) hA
    have hΩa : cardFactors (Nat.card ↥(Subgroup.centralizer ({a} : Set G))) ≤ 70 := by
      rw [← m4_card_centralizer_of_isConj hca]
      exact hΩ
    exact two_pow_four_le_index_of_twoB hW ι hι ha2 hg2 hat hag.symm hAa hΩa hB

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Row
