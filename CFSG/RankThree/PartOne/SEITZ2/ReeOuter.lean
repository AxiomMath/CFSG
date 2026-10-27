module

public import CFSG.RankThree.PartOne.SEITZ2.Common
public import CFSG.RankThree.PartOne.SEITZX.ReeSplit
import CFSG.RankThree.PartOne.S11c.Sec66F4ReeK1
public import CFSG.RankThree.PartOne.CTP.SeitzMaxAbstract
import CFSG.RankThree.PartOne.RF4.Descent

public section

namespace CFSG.RankThree.PartOne.SEITZ2

open Subgroup CFSG CFSG.LieType.Ree CFSG.LieType.Ree.ReeTag CFSG.RankThree.PartOne.CTP
open CFSG.RankThree.PartOne.Census3 (IsoLie)

open CFSG.ComponentClassification.OuterAutomorphisms (Outer inner)

open CFSG.RankThree.PartOne.Sec66T (fixSub)

open CFSG.ComponentClassification.UnbalancedCatalog
  (large_Ree_full_inner_field_automorphism_normal_form)
open CFSG.LieType.Chevalley (fixSubfield)


@[expose] def SubfieldPairReeF4 : Prop :=
  ∀ (a : ℕ), 1 ≤ a → ∀ (K : Type) [Field K] [Finite K] [CharP K F4.prime],
    Nat.card K = 2 ^ (2 * a + 1) → ∀ (β : K ≃+* K) (p : ℕ), p.Prime → 5 ≤ p → orderOf β = p →
      ∀ g : F4.reeGamma K a,
        (fixedSubgroup (F4.reeGammaFieldAut K a β)).map (MulAut.conj g).toMonoidHom ≠
          fixedSubgroup (F4.reeGammaFieldAut K a β) →
        Subgroup.closure ((fixedSubgroup (F4.reeGammaFieldAut K a β) : Set (F4.reeGamma K a)) ∪
          ((fixedSubgroup (F4.reeGammaFieldAut K a β)).map (MulAut.conj g).toMonoidHom :
            Set (F4.reeGamma K a))) = ⊤ ∨
          ¬ p ∣ Nat.card (fixedSubgroup (F4.reeGammaFieldAut K a β))

section Main

variable {a : ℕ} {K : Type} [Field K] [Finite K] [CharP K F4.prime]

theorem fieldAutData_reeF4_odd {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (ha : 1 ≤ a)
    (hK : Nat.card K = 2 ^ (2 * a + 1))
    (hpair : ∀ β : K ≃+* K, orderOf β = p → ∀ g : F4.reeGamma K a,
      (fixedSubgroup (F4.reeGammaFieldAut K a β)).map (MulAut.conj g).toMonoidHom ≠
          fixedSubgroup (F4.reeGammaFieldAut K a β) →
        Subgroup.closure ((fixedSubgroup (F4.reeGammaFieldAut K a β) : Set (F4.reeGamma K a)) ∪
          ((fixedSubgroup (F4.reeGammaFieldAut K a β)).map (MulAut.conj g).toMonoidHom :
            Set (F4.reeGamma K a))) = ⊤ ∨
          ¬ p ∣ Nat.card (fixedSubgroup (F4.reeGammaFieldAut K a β))) :
    FieldAutData (F4.reeGamma K a) p := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have hfin : Finite (F4.reeGamma K a) := Subtype.finite
  obtain ⟨-, hNF, ⟨Ψ, hΨ⟩, hcyc, -⟩ := large_Ree_full_inner_field_automorphism_normal_form a ha K hK
  refine fieldAutData_of_standard (MulAut.conj : F4.reeGamma K a →* MulAut _).range
    {g | ∃ β : K ≃+* K, orderOf β = p ∧ g = F4.reeGammaFieldAut K a β} ?_ ?_ ?_ ?_ ?_
  · intro E hE hEc
    have := hE
    exact exists_conj_mem_of_plane_of_cyclic_outer hp hcyc E hEc
  · intro α hα
    obtain ⟨hord, hout⟩ := hα
    have hαp : α ^ p = 1 := hord ▸ pow_orderOf_eq_one α
    obtain ⟨⟨x, β⟩, hxβ, -⟩ := hNF α
    let Θ : MulAut (F4.reeGamma K a) →* (K ≃+* K) :=
      SemidirectProduct.rightHom.comp Ψ.symm.toMonoidHom
    have hΨα : Ψ ⟨x, β⟩ = α := by rw [hΨ x β]; exact hxβ.symm
    have hΘα : Θ α = β := by
      show SemidirectProduct.rightHom (Ψ.symm α) = β
      rw [← hΨα, MulEquiv.symm_apply_apply]
      rfl
    have hβp : β ^ p = 1 := by rw [← hΘα, ← map_pow, hαp, map_one]
    have hone : F4.reeGammaFieldAut K a 1 = 1 := by
      rw [← reeGammaFieldAutHom_apply, map_one]
    have hβ1 : β ≠ 1 := by
      intro h
      apply hout x
      rw [h, hone, mul_one] at hxβ
      exact hxβ
    have hβord : orderOf β = p := orderOf_eq_prime hβp hβ1
    obtain ⟨g, hg⟩ := RF4.largeRee_fieldAut_coset_conj a hK hp β hβord α hαp ⟨x, hxβ⟩
    exact ⟨MulAut.conj g, ⟨g, rfl⟩, F4.reeGammaFieldAut K a β, ⟨β, hβord, rfl⟩, hg⟩
  · rintro _ ⟨β, hβ, rfl⟩ _ ⟨τ, hτ, rfl⟩
    have hzp := zpowers_ringEquiv_eq_of_orderOf Nat.prime_two (by omega : 1 ≤ 2 * a + 1) hK hβ hτ
    exact fixedSubgroup_eq_of_zpowers_eq (F4.reeGammaFieldAutHom K a) hzp
  · rintro _ ⟨β, hβ, rfl⟩ _ x hx hc
    obtain ⟨b, hbp, hbcard, hchar, ⟨eC⟩⟩ :=
      CFSG.RankThree.PartOne.Sec66T.reeF4_fixed_data_odd hK hp hp2 hβ
    have hz : eC ⟨x, hx⟩ ∈ Subgroup.center (F4.reeGamma (fixSubfield β) b) := by
      rw [Subgroup.mem_center_iff]
      intro g
      obtain ⟨y, hy⟩ : ∃ y : ↥(fixSub (F4.reeGammaFieldAut K a β)), eC y = g :=
        ⟨eC.symm g, by simp⟩
      rw [← hy, ← map_mul, ← map_mul]
      congr 1
      exact Subtype.ext (hc y.1 y.2).symm
    rw [large_Ree_fixed_group_center_trivial b (fixSubfield β) hbcard, Subgroup.mem_bot] at hz
    have h1 : (⟨x, hx⟩ : ↥(fixSub (F4.reeGammaFieldAut K a β))) = 1 :=
      eC.injective (by rw [hz, map_one])
    exact congrArg Subtype.val h1
  · rintro _ ⟨β, hβ, rfl⟩ d ⟨g, rfl⟩ hne
    exact hpair β hβ g hne

theorem fieldAutData_reeF4 (hpair : SubfieldPairReeF4) {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    (ha : 1 ≤ a) (hK : Nat.card K = 2 ^ (2 * a + 1)) :
    FieldAutData (F4.reeGamma K a) p :=
  fieldAutData_reeF4_odd hp (by omega) ha hK fun β hβ g hne =>
    hpair a ha K hK β p hp hp5 hβ g hne

end Main

section Index


theorem extSeitzAtOuter_reeF4_of_pair (hpair : SubfieldPairReeF4) (m : ℕ) :
    ExtSeitzAtOuter (.reeF4 m) := by
  intro K _ _ _ hnab hiso p hp hp5 hpd E hE hc hout
  obtain ⟨X, _, _, _, ha, hX, ⟨e⟩⟩ := SEITZX.exists_reeGamma_model hiso
  have hd : FieldAutData K p := (fieldAutData_reeF4 hpair hp hp5 ha hX).of_mulEquiv e hp
  left
  exact closure_fixUnion_eq_top_of_fieldAutData hnab hp hd E hc hout

end Index

end CFSG.RankThree.PartOne.SEITZ2
