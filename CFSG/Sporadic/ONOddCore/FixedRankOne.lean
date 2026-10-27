module

public import CFSG.Sporadic.ONOddCore.SylowEight
public import CFSG.LocalAnalysis.ComponentInitial.CharacteristicEightFixed
import CFSG.GroupTheory.ElementaryAbelianTransport

public noncomputable section

namespace CFSG.Sporadic.ONOddCore

open CFSG.ONSchreier CFSG.Blueprint
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)

theorem isElementaryAbelian_of_mulEquiv {p : ℕ} {A B : Type*} [Group A] [Group B] (e : A ≃* B)
    [hB : CFSG.IsElementaryAbelian p B] : CFSG.IsElementaryAbelian p A :=
  CFSG.IsElementaryAbelian.of_mulEquiv e.symm inferInstance

abbrev sylT :
    Subgroup Pv := (onTSylow : Subgroup Pv)

@[expose] def sylTEquiv :
    sylT ≃* onT :=
  (MulEquiv.subgroupCongr onTSylow_coe).trans (Subgroup.subgroupOfEquivOfLe onT_le)

abbrev omegaS :
    Subgroup sylT :=
  Subgroup.closure {x : sylT | x ∈ Subgroup.closure {x : sylT | ∃ t, t ^ 2 = x} ∧ x ^ 2 = 1}

theorem omegaS_map :
    omegaS.map sylTEquiv.toMonoidHom = omegaT := by
  rw [map_closure_involutions _ sylTEquiv.injective, map_closure_squares,
    MonoidHom.range_eq_top.2 sylTEquiv.surjective]
  have e : {y : onT | ∃ s ∈ (⊤ : Subgroup onT), s ^ 2 = y} = {y | ∃ t, t ^ 2 = y} :=
    Set.ext fun y => ⟨fun ⟨s, _, h⟩ => ⟨s, h⟩, fun ⟨s, h⟩ => ⟨s, Subgroup.mem_top s, h⟩⟩
  rw [e]

@[expose] def omegaSEquiv :
    omegaS ≃* omegaP :=
  ((omegaS.equivMapOfInjective _ sylTEquiv.injective).trans
    (MulEquiv.subgroupCongr omegaS_map)).trans omegaPEquiv.symm

theorem omegaS_elementary :
    CFSG.IsElementaryAbelian 2 omegaS := by
  have := omegaP_elementary
  exact isElementaryAbelian_of_mulEquiv omegaSEquiv

theorem card_omegaS :
    Nat.card omegaS = 8 := by
  rw [Nat.card_congr omegaSEquiv.toEquiv, card_omegaP]

theorem glq_sporadic_outer_involution_fixed_rank_one_ON_exclusion
    {L : Type*} [Group L]
    (hL : Nonempty (L ≃* NativeSporadic.ON)) (α : MulAut L) (hα : α * α = 1) :
    (∃ V : Subgroup L, V ≤ fixedSubgroup α ∧ CFSG.IsElementaryAbelian 2 V ∧ Nat.card V = 4) ∧
      2 ≤ CFSG.pRank 2 (fixedSubgroup α) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨ψ⟩ := hL
  let φ : L ≃* Pv := ψ.trans onEquivPv
  have : Finite L := Finite.of_equiv _ φ.symm.toEquiv
  let α' : MulAut Pv := (φ.symm.trans α).trans φ
  have hα' : α' * α' = 1 := by
    refine MulEquiv.ext fun x => ?_
    have h := congrArg (fun β : MulAut L => β (φ.symm x)) hα
    simp only [MulAut.mul_apply, MulAut.one_apply] at h
    show φ (α (φ.symm (φ (α (φ.symm x))))) = x
    rw [MulEquiv.symm_apply_apply, h, MulEquiv.apply_symm_apply]
  have : omegaS.Characteristic := characteristic_omega_squares
  have hAel := omegaS_elementary
  obtain ⟨⟨V', hV'fix, hV'el, hV'card⟩, -⟩ :=
    CFSG.LocalAnalysis.ComponentInitial.characteristic_Sylow_eight_subgroup_fixed_four_group
      onTSylow hAel (by rw [card_omegaS]) α' hα'
  set V := V'.map φ.symm.toMonoidHom with hVdef
  have hVfix : V ≤ fixedSubgroup α := by
    rintro _ ⟨v, hv, rfl⟩
    have h := hV'fix hv
    change α' v = v at h
    change α (φ.symm v) = φ.symm v
    have h2 := congrArg φ.symm h
    simpa [α'] using h2
  have hVel : CFSG.IsElementaryAbelian 2 V := by
    have := hV'el
    exact CFSG.IsElementaryAbelian.map _
  have hVcard : Nat.card V = 4 := by
    rw [hVdef, Subgroup.card_map_of_injective φ.symm.injective, hV'card]
  refine ⟨⟨V, hVfix, hVel, hVcard⟩, ?_⟩
  rw [CFSG.SectionRank.pRank_eq_open_pRank_top]
  have hpow : ∀ v : V, v ^ 2 = 1 := fun v =>
    Subtype.ext (by
      simpa using CFSG.elemPow_eq_one_of_isElementaryAbelian (p := 2) (A := V) (v : L) v.2)
  exact CFSG.SectionRank.le_pRank_of_injective (by norm_num) (fun u v => mul_comm' u v) hpow
    (by rw [hVcard]; norm_num) (Subgroup.inclusion hVfix) (Subgroup.inclusion_injective hVfix)
    le_top

end CFSG.Sporadic.ONOddCore
