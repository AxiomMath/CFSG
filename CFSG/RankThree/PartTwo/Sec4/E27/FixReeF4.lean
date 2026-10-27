module

public import CFSG.RankThree.PartTwo.Sec4.E27.FixG2
public import CFSG.RankThree.PartTwo.Sec4.E27.FamilyReeF4
public import CFSG.RankThree.PartTwo.Sec19.SeitzG2F4ReeF4Three
public import CFSG.RankThree.PartOne.S11c.Sec66F4ReeK1

public section

namespace CFSG.RankThree.PartTwo.Sec4.E27

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Ree
  CFSG.LieType.Ree.ReeTag CFSG.RankThree.PartOne CFSG.RankThree.PartOne.CTP CFSG.Open
  CFSG.LieType.SeitzGeneration
open CFSG.RankThree.PartOne.Sec66T (fixSub)

open CFSG.ComponentClassification.UnbalancedCatalog
  (large_Ree_full_inner_field_automorphism_normal_form)

variable {a : ℕ} {K : Type} [Field K] [Finite K]
  [CharP K F4.prime]

theorem fixPlaneGen_reeF4_three (ha : 2 ≤ a) (hK : Nat.card K = 2 ^ (2 * a + 1)) :
    FixPlaneGen (F4.reeGamma K a) 3 := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hfin : Finite (F4.reeGamma K a) := Subtype.finite
  obtain ⟨-, hNF, ⟨Ψ, hΨ⟩, hcyc, -⟩ :=
    large_Ree_full_inner_field_automorphism_normal_form a (by omega) K hK
  refine fixPlaneGen_of_standard (MulAut.conj : F4.reeGamma K a →* MulAut _).range
    {g | ∃ β : K ≃+* K, orderOf β = 3 ∧ g = F4.reeGammaFieldAut K a β} ?_ ?_
  · intro α hα
    obtain ⟨hord, hout⟩ := hα
    have hαp : α ^ 3 = 1 := hord ▸ pow_orderOf_eq_one α
    obtain ⟨⟨x, β⟩, hxβ, -⟩ := hNF α
    let Θ : MulAut (F4.reeGamma K a) →* (K ≃+* K) :=
      SemidirectProduct.rightHom.comp Ψ.symm.toMonoidHom
    have hΨα : Ψ ⟨x, β⟩ = α := by rw [hΨ x β]; exact hxβ.symm
    have hΘα : Θ α = β := by
      show SemidirectProduct.rightHom (Ψ.symm α) = β
      rw [← hΨα, MulEquiv.symm_apply_apply]
      rfl
    have hβp : β ^ 3 = 1 := by rw [← hΘα, ← map_pow, hαp, map_one]
    have hone : F4.reeGammaFieldAut K a 1 = 1 := by
      rw [← reeGammaFieldAutHom_apply, map_one]
    have hβ1 : β ≠ 1 := by
      intro h
      apply hout x
      rw [h, hone, mul_one] at hxβ
      exact hxβ
    have hβord : orderOf β = 3 := orderOf_eq_prime hβp hβ1
    obtain ⟨g, hg⟩ := RF4.largeRee_fieldAut_coset_conj a hK Nat.prime_three β hβord α hαp ⟨x, hxβ⟩
    exact ⟨MulAut.conj g, ⟨g, rfl⟩, F4.reeGammaFieldAut K a β, ⟨β, hβord, rfl⟩, hg⟩
  · rintro _ ⟨β, hβ, rfl⟩ A hA hAa hAc
    obtain ⟨b, hbp, hbcard, hchar, ⟨eC⟩⟩ :=
      CFSG.RankThree.PartOne.Sec66T.reeF4_fixed_data_odd hK Nat.prime_three (by norm_num) hβ
    have hb : 1 ≤ b := by omega
    have hfix : fixSub (F4.reeGammaFieldAut K a β) = fixedSubgroup (F4.reeGammaFieldAut K a β) :=
      Subgroup.ext fun _ => Iff.rfl
    rw [← hfix] at hA ⊢
    refine le_closure_centralizers_of_equiv hA eC ?_
    exact CFSG.RankThree.PartTwo.Sec19.reeF4_cenGen_eq_top_three hb hbcard _
      (CFSG.Open.IsElemAbelian.map (CFSG.Open.IsElemAbelian.subgroupOf hAa _) _)
      (by
        rw [Subgroup.card_map_of_injective eC.injective,
          Nat.card_congr (Subgroup.subgroupOfEquivOfLe hA).toEquiv, hAc]
        norm_num)

theorem seitz27_reeF4
    (ha : 2 ≤ a)
    (hK : Nat.card K = 2 ^ (2 * a + 1)) : Seitz27 (F4.reeGamma K a) :=
  seitz27_reeF4_of_plane (by omega) hK
    (fixPlaneGen_reeF4_three ha hK)

end CFSG.RankThree.PartTwo.Sec4.E27
