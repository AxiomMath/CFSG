module

import CFSG.Adapters.StatedClassicalSmallOrders
public import CFSG.Quasithin.EmptyFaithful.SBd14Mid

public section

namespace CFSG.Quasithin.SBd14

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.LieType.BorelTits CFSG.Blueprint
open CFSG.Assembly.LowTwoRank (projectiveSpecialLinearGroupEquivStatedProj)

theorem card_of_isPSL_three_four {X : Type} [Group X] (h : IsPSL 3 2 2 X) : Nat.card X = 20160 :=
  CFSG.Open.StatedAPI.card_of_statedClassicalModel_psl_three_four h

variable {G : Type} [Group G] [Finite G] {T Mc M V₁ V₂ Yp I L : Subgroup G} {t : G}

theorem RestHyp.card_center_L (r : RestHyp T Mc M V₁ V₂ Yp I L t) (h113 : StageLemma14113) :
    Nat.card ↥(Subgroup.center ↥L) = 4 := by
  have h1 : V₁ = centerOf L := r.V₁_eq_center h113
  have h2 : Nat.card ↥(centerOf L) = Nat.card ↥(Subgroup.center ↥L) := by
    rw [SBd9.centerOf_eq_map]
    exact Nat.card_congr ((Subgroup.center ↥L).equivMapOfInjective L.subtype L.subtype_injective).symm
  rw [← h2, ← h1]
  exact r.ctx.hyp.decomp.card₁

theorem RestHyp.pCoreOf_eq_V₁_of_psl (r : RestHyp T Mc M V₁ V₂ Yp I L t) (h113 : StageLemma14113)
    {Hv : Subgroup G} (hLH : L ≤ Hv) (hΩ : pCoreOf 2 Hv ≤ V₁)
    (hpsl : IsPSL 3 2 2 ↥(modO2Image Hv L)) : pCoreOf 2 Hv = V₁ := by
  classical
  have D0 := r.ctx.hyp.decomp
  have hV₁L : V₁ ≤ L := by
    rw [r.V₁_eq_center h113]
    exact fun x hx => hx.1
  let f : ↥L →* (↥Hv ⧸ CFSG.pCore 2 ↥Hv) :=
    (QuotientGroup.mk' (CFSG.pCore 2 ↥Hv)).comp (Subgroup.inclusion hLH)
  have hrange : f.range = modO2Image Hv L := by
    rw [MonoidHom.range_comp, Subgroup.inclusion_range]
    rfl
  have hker : ∀ x : ↥L, x ∈ f.ker ↔ (x : G) ∈ pCoreOf 2 Hv := by
    intro x
    rw [MonoidHom.mem_ker]
    have h1 : f x = 1 ↔ (⟨(x : G), hLH x.2⟩ : ↥Hv) ∈ CFSG.pCore 2 ↥Hv := by
      simp only [f, MonoidHom.comp_apply, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
      exact Iff.rfl
    rw [h1, S153D.mem_pCore_iff]
  have hcardL : Nat.card ↥L = 4 * 20160 := by
    have h1 := (Subgroup.center ↥L).card_eq_card_quotient_mul_card_subgroup
    rw [card_of_isPSL_three_four r.hn2, r.card_center_L h113] at h1
    omega
  have hrangecard : Nat.card ↥f.range = 20160 := by
    rw [hrange]
    exact card_of_isPSL_three_four hpsl
  have hkercard : Nat.card ↥f.ker = 4 := by
    have h1 := Subgroup.card_ker_mul_card_range f
    rw [hrangecard, hcardL] at h1
    omega
  have hkereq : f.ker = (pCoreOf 2 Hv).subgroupOf L := by
    ext x
    rw [hker, Subgroup.mem_subgroupOf]
  have hOcard : Nat.card ↥(pCoreOf 2 Hv) = 4 := by
    have hOL : pCoreOf 2 Hv ≤ L := hΩ.trans hV₁L
    rw [← hkercard, hkereq]
    exact (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hOL).toEquiv).symm
  exact Subgroup.eq_of_le_of_card_ge hΩ (by rw [D0.card₁, hOcard])

end CFSG.Quasithin.SBd14
