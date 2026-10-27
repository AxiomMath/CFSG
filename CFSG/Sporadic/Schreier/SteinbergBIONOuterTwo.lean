module

public import CFSG.Sporadic.Schreier.SteinbergBIONOuterFour
public import CFSG.Sporadic.ONOddCore.Nonext

public section

namespace CFSG.Sporadic.SteinbergBI

open CFSG.ONSchreier CFSG.Sporadic.ONOddCore CFSG.ComponentClassification.OuterAutomorphisms
  CFSG.ComponentClassification.CatalogueSchreierTwoCentralizers

theorem outerPvToM_outerPvEquiv_mk
    (ψ : stabilizer Mv) :
    outerPvToM (outerPvEquiv (ψ : InnerQuotient Mv)) =
      ((MulAut.congr (Subgroup.subgroupOfEquivOfLe onM_le) (restrict Mv ψ) : MulAut onM) :
        Outer onM) := by
  simp only [outerPvToM, MonoidHom.coe_comp, Function.comp_apply, MulEquiv.coe_toMonoidHom,
    MulEquiv.symm_apply_apply]
  rfl

theorem coe_congr_restrict_apply
    (ψ : stabilizer Mv) (m : onM) :
    ((MulAut.congr (Subgroup.subgroupOfEquivOfLe onM_le) (restrict Mv ψ) m : onM) :
        Equiv.Perm (Fin N)) =
      (((ψ : MulAut Pv) (toP m) : Pv) : Equiv.Perm (Fin N)) :=
  rfl

theorem range_outerPvToM_ne_top :
    outerPvToM.range ≠ ⊤ := by
  obtain ⟨k, hk, he, hβ⟩ := exists_betaAut (r := 2) (by norm_num)
  intro htop
  obtain ⟨o, ho⟩ : ((liftAut hk he : MulAut onM) : Outer onM) ∈ outerPvToM.range := by
    rw [htop]
    exact Subgroup.mem_top _
  obtain ⟨ψ, hψ⟩ := QuotientGroup.mk_surjective (outerPvEquiv.symm o)
  have ho' : o = outerPvEquiv (ψ : InnerQuotient Mv) := by
    rw [hψ, MulEquiv.apply_symm_apply]
  rw [ho', outerPvToM_outerPvEquiv_mk] at ho
  obtain ⟨m, hm⟩ := QuotientGroup.eq.1 ho
  have hβm := inv_mul_eq_iff_eq_mul.1 hm.symm
  refine not_extend (r := 2) (by decide) ((ψ : MulAut Pv) * MulAut.conj (toP m)) fun y => ?_
  have h1 : betaFun 2 y =
      MulAut.congr (Subgroup.subgroupOfEquivOfLe onM_le) (restrict Mv ψ) (m * y * m⁻¹) := by
    rw [← hβ, hβm, MulAut.mul_apply, MulAut.conj_apply]
  rw [h1, coe_congr_restrict_apply]
  rfl

theorem card_outer_Pv_dvd_two :
    Nat.card (Outer Pv) ∣ 2 := by
  have : Finite (Outer onM) := Nat.finite_of_card_ne_zero (by rw [card_outer_M]; norm_num)
  have h2 : Nat.card outerPvToM.range ∣ 4 := card_outer_M ▸ Subgroup.card_subgroup_dvd_card _
  have h3 : Nat.card outerPvToM.range ≠ 4 := fun h =>
    range_outerPvToM_ne_top (Subgroup.eq_top_of_card_eq _ (h.trans card_outer_M.symm))
  rw [Nat.card_congr (MonoidHom.ofInjective outerPvToM_injective).toEquiv]
  have hle := Nat.le_of_dvd (by norm_num) h2
  generalize Nat.card outerPvToM.range = c at h2 h3 hle ⊢
  interval_cases c <;> revert h2 h3 <;> decide

theorem cti_on_outer_order_divides_two
    {T : Type*} [Group T]
    (hT : Nonempty (T ≃* Blueprint.NativeSporadic.ON)) : Nat.card (Outer T) ∣ 2 := by
  obtain ⟨e⟩ := hT
  rw [card_outer_eq_of_mulEquiv (e.trans onEquivPv)]
  exact card_outer_Pv_dvd_two

end CFSG.Sporadic.SteinbergBI
