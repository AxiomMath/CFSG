module

public import CFSG.RankThree.PartTwo.Sec4.E27.ReeEightPlane
public import CFSG.RankThree.PartTwo.Sec4.E27.FixG2
public import CFSG.RankThree.PartOne.S11c.Sec66F4ReeK1

public section

namespace CFSG.RankThree.PartTwo.Sec4.E27

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Ree
  CFSG.LieType.Ree.ReeTag CFSG.RankThree.PartOne CFSG.RankThree.PartOne.CTP CFSG.Open
  CFSG.LieType.SeitzGeneration CFSG.RankThree.PartTwo.Sec4.E27.ReeEight
open CFSG.RankThree.PartOne.Sec66T (fixSub)

open CFSG.Sporadic.Schreier.Tits (titsA titsIso)

open CFSG.ComponentClassification.UnbalancedCatalog
  (large_Ree_full_inner_field_automorphism_normal_form)

variable
  {K : Type} [Field K] [Finite K] [CharP K F4.prime]

theorem fixPlaneGen_reeF4_eight_of_checks (hc : ReeEightChecks)
    (hK : Nat.card K = 2 ^ (2 * 1 + 1)) : FixPlaneGen (F4.reeGamma K 1) 3 := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hfin : Finite (F4.reeGamma K 1) := Subtype.finite
  obtain ⟨-, hNF, ⟨Ψ, hΨ⟩, hcyc, -⟩ :=
    large_Ree_full_inner_field_automorphism_normal_form 1 (by omega) K hK
  refine fixPlaneGen_of_standard (MulAut.conj : F4.reeGamma K 1 →* MulAut _).range
    {g | ∃ β : K ≃+* K, orderOf β = 3 ∧ g = F4.reeGammaFieldAut K 1 β} ?_ ?_
  · intro α hα
    obtain ⟨hord, hout⟩ := hα
    have hαp : α ^ 3 = 1 := hord ▸ pow_orderOf_eq_one α
    obtain ⟨⟨x, β⟩, hxβ, -⟩ := hNF α
    let Θ : MulAut (F4.reeGamma K 1) →* (K ≃+* K) :=
      SemidirectProduct.rightHom.comp Ψ.symm.toMonoidHom
    have hΨα : Ψ ⟨x, β⟩ = α := by rw [hΨ x β]; exact hxβ.symm
    have hΘα : Θ α = β := by
      show SemidirectProduct.rightHom (Ψ.symm α) = β
      rw [← hΨα, MulEquiv.symm_apply_apply]
      rfl
    have hβp : β ^ 3 = 1 := by rw [← hΘα, ← map_pow, hαp, map_one]
    have hone : F4.reeGammaFieldAut K 1 1 = 1 := by
      rw [← reeGammaFieldAutHom_apply, map_one]
    have hβ1 : β ≠ 1 := by
      intro h
      apply hout x
      rw [h, hone, mul_one] at hxβ
      exact hxβ
    have hβord : orderOf β = 3 := orderOf_eq_prime hβp hβ1
    obtain ⟨g, hg⟩ := RF4.largeRee_fieldAut_coset_conj 1 hK Nat.prime_three β hβord α hαp ⟨x, hxβ⟩
    exact ⟨MulAut.conj g, ⟨g, rfl⟩, F4.reeGammaFieldAut K 1 β, ⟨β, hβord, rfl⟩, hg⟩
  · rintro _ ⟨β, hβ, rfl⟩ A hA hAa hAc
    obtain ⟨b, hbp, hbcard, hchar, ⟨eC⟩⟩ :=
      CFSG.RankThree.PartOne.Sec66T.reeF4_fixed_data_odd hK Nat.prime_three (by norm_num) hβ
    have hb : b = 0 := by omega
    subst hb
    haveI : Fact (Nat.card (fixSubfield β) = 2) := ⟨by rw [hbcard]; norm_num⟩
    let e : ↥(fixSub (F4.reeGammaFieldAut K 1 β)) ≃* ↥titsA :=
      eC.trans ((reeFixedEquivReeGamma (fixSubfield β) 0).symm.trans
        (titsIso (K := fixSubfield β)))
    have hfix : fixSub (F4.reeGammaFieldAut K 1 β) = fixedSubgroup (F4.reeGammaFieldAut K 1 β) :=
      Subgroup.ext fun _ => Iff.rfl
    rw [← hfix] at hA ⊢
    refine le_closure_centralizers_of_equiv hA e ?_
    exact titsA_plane_closure hc
      (CFSG.Open.IsElemAbelian.map (CFSG.Open.IsElemAbelian.subgroupOf hAa _) _)
      (by
        rw [Subgroup.card_map_of_injective e.injective,
          Nat.card_congr (Subgroup.subgroupOfEquivOfLe hA).toEquiv, hAc]
        norm_num)

end CFSG.RankThree.PartTwo.Sec4.E27
