module

public import CFSG.OddTranspositions.PartFour.ThirteenListThreeFischerFi23

public section

namespace CFSG.OddTranspositions.FischerMarked24

open CFSG.Fischer.Classification CFSG.OddTranspositions.FischerMarkedY
open CFSG.Sporadic.Fi24 CFSG.YGroups CFSG.YGroups.Y443
open CFSG.LieType.Multipliers.O73
open scoped commutatorElement

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

attribute [local irreducible] sevenForm coordinates fi23EquivJMR

theorem exists_local_product_embedding :
    ∃ η : Multiplicative (ZMod 2) × CFSG.Sporadic.Fi23.J →* R,
      Function.Injective η ∧ ∀ x : CFSG.Sporadic.Fi23.J,
        η (Multiplicative.ofAdd 1, x) = ((fi23EquivJMR.symm x : MR) : R) * tR := by
  let τ : Multiplicative (ZMod 2) →* R := z2Hom tR tR_mul_tR
  have hτ : Function.Injective τ := by
    rw [injective_iff_map_eq_one]
    intro a ha
    rcases z2_cases a with rfl | rfl
    · rfl
    · exact (tR_ne_one (by simpa only [τ, z2Hom_ofAdd_one] using ha)).elim
  have hcomm : ∀ a x, Commute (τ a) (fromFi23 x) := by
    intro a x
    rcases z2_cases a with rfl | rfl
    · simp
    · rw [show τ (Multiplicative.ofAdd 1) = tR from z2Hom_ofAdd_one .., fromFi23_apply]
      exact (commute_tR_of_mem_MR (fi23EquivJMR.symm x).2).symm
  have hτrange : τ.range ≤ Subgroup.zpowers tR := by
    rintro _ ⟨a, rfl⟩
    rcases z2_cases a with rfl | rfl
    · exact Subgroup.one_mem _
    · change tR ∈ Subgroup.zpowers tR
      exact Subgroup.mem_zpowers _
  have hμrange : fromFi23.range ≤ MR := by
    rintro _ ⟨x, rfl⟩
    rw [fromFi23_apply]
    exact (fi23EquivJMR.symm x).2
  have hdisj : Disjoint τ.range fromFi23.range := by
    rw [disjoint_iff]
    apply le_antisymm _ bot_le
    have hle := inf_le_inf hτrange hμrange
    rw [zpowers_tR_inf_MR] at hle
    exact hle
  refine ⟨τ.noncommCoprod fromFi23 hcomm,
    (MonoidHom.noncommCoprod_injective ..).mpr ⟨hτ, fromFi23_injective, hdisj⟩, fun x => ?_⟩
  rw [MonoidHom.noncommCoprod_apply, show τ (Multiplicative.ofAdd 1) = tR from z2Hom_ofAdd_one ..,
    fromFi23_apply]
  exact (commute_tR_of_mem_MR (fi23EquivJMR.symm x).2).symm


theorem exists_fi24_linear_refl_embedding :
    ∃ κ : CFSG.Fischer.Classification.F3.reflGroup sevenForm →* R,
      Function.Injective κ ∧ ∃ i : Fin 8,
        κ (reflElt sevenForm (coordinates (vecs i))) ∈ D24 := by
  obtain ⟨e, hegen, hef⟩ := exists_y322_reflEquiv
  obtain ⟨μ, hμ, i, hi⟩ := exists_fi23_refl_embedding
  let q := QuotientGroup.mk' (Subgroup.center (F3.reflGroup sevenForm))
  let χ : F3.reflGroup sevenForm →* Multiplicative (ZMod 2) :=
    y322Parity.comp e.symm.toMonoidHom
  let μ' : F3.reflGroup sevenForm →* CFSG.Sporadic.Fi23.J := μ.comp q
  have hpair : Function.Injective (χ.prod μ') := by
    rw [injective_iff_map_eq_one]
    intro r hr
    have hχ : χ r = 1 := congrArg Prod.fst hr
    have hμr : μ' r = 1 := congrArg Prod.snd hr
    have hqr : q r = 1 := hμ (hμr.trans (map_one μ).symm)
    have hcent : r ∈ Subgroup.center (F3.reflGroup sevenForm) :=
      (QuotientGroup.eq_one_iff _).mp hqr
    rcases F3.coe_eq_of_mem_center isF3Form_sevenForm (by decide) hcent with h | h
    · exact Subtype.ext h
    · have hrF : r = e y322F1 := Subtype.ext (h.trans hef.symm)
      have hpar : χ r = Multiplicative.ofAdd 1 := by
        change y322Parity (e.symm r) = _
        rw [hrF, e.symm_apply_apply, y322Parity_F1]
      have hbad := hχ.symm.trans hpar
      exact (by decide : (1 : Multiplicative (ZMod 2)) ≠ Multiplicative.ofAdd 1) hbad |>.elim
  obtain ⟨η, hη, hηgen⟩ := exists_local_product_embedding
  let κ : F3.reflGroup sevenForm →* R := η.comp (χ.prod μ')
  refine ⟨κ, hη.comp hpair, i, ?_⟩
  have hχgen : χ (reflElt sevenForm (coordinates (vecs i))) = Multiplicative.ofAdd 1 := by
    change y322Parity (e.symm (reflElt sevenForm (coordinates (vecs i)))) = _
    rw [← hegen, e.symm_apply_apply, y322Parity_yGen i.2]
  have hκgen : κ (reflElt sevenForm (coordinates (vecs i))) =
      ((fi23EquivJMR.symm (μ (reflBar sevenForm (coordinates (vecs i)))) : MR) : R) * tR := by
    change η (χ _, μ' _) = _
    rw [hχgen, hηgen]
    rfl
  rw [hκgen]
  let a : MR := fi23EquivJMR.symm (μ (reflBar sevenForm (coordinates (vecs i))))
  have ha : ((a : R) * tR) * tR ∈ MR := by
    rw [mul_assoc, tR_mul_tR, mul_one]
    exact a.2
  apply mem_D24_of_mul_tR ha
  have heqval : ((a : R) * tR) * tR = (a : R) := by
    rw [mul_assoc, tR_mul_tR, mul_one]
  have heq : (⟨((a : R) * tR) * tR, ha⟩ : MR) = a := Subtype.ext heqval
  rw [heq]
  change IsConj CFSG.Sporadic.Fi23.d (fi23EquivJMR (fi23EquivJMR.symm _))
  rw [fi23EquivJMR.apply_symm_apply]
  exact hi

end CFSG.OddTranspositions.FischerMarked24
