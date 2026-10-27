module

public import CFSG.Sporadic.ONOddCore.MOddCore
public import CFSG.Sporadic.ONOddCore.Involutions

public noncomputable section

namespace CFSG.Sporadic.ONOddCore

open CFSG.ONSchreier CFSG.LocalAnalysis.ComponentInitial CFSG.ComponentClassification
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open UnbalancedCatalog.EvenCatalog (oddCore_eq_bot_of_mulEquiv)

theorem induced_sq
    {γ : MulAut Pv} (hγ2 : γ * γ = 1)
    (hLm : ∀ x : Pv, ((γ x : Pv) : Equiv.Perm (Fin N)) ∈ onL ↔ (x : Equiv.Perm (Fin N)) ∈ onL)
    {γbar : MulAut S3}
    (hc : ∀ a a' : onL, (a' : Equiv.Perm (Fin N)) =
      ((γ ⟨a, onM_le (onL_le_M a.2)⟩ : Pv) : Equiv.Perm (Fin N)) → lToS a' = γbar (lToS a)) :
    γbar * γbar = 1 := by
  ext s
  obtain ⟨a, rfl⟩ := lToS_surjective s
  set a' : onL := ⟨γ ⟨a, onM_le (onL_le_M a.2)⟩, (hLm _).2 a.2⟩ with ha'
  set a'' : onL := ⟨γ ⟨a', onM_le (onL_le_M a'.2)⟩, (hLm _).2 a'.2⟩ with ha''
  have h1 := hc a a' (Subtype.coe_mk _ _)
  have h2 := hc a' a'' (Subtype.coe_mk _ _)
  have h3 : a'' = a := by
    apply Subtype.ext
    rw [ha'', Subtype.coe_mk]
    have e : (⟨((a' : onL) : Equiv.Perm (Fin N)), onM_le (onL_le_M a'.2)⟩ : Pv) =
        γ ⟨a, onM_le (onL_le_M a.2)⟩ := Subtype.ext (by rw [ha', Subtype.coe_mk, Subtype.coe_mk])
    rw [e, ← MulAut.mul_apply, hγ2, MulAut.one_apply]
  rw [MulAut.mul_apply, ← h1, ← h2, h3, MulAut.one_apply]

theorem oddCore_fixed_outer
    {γ : MulAut Pv} (hout : γ ∉ (MulAut.conj : Pv →* MulAut Pv).range)
    (hγ2 : γ * γ = 1) (hz : γ zP = zP) : CFSG.oddCore (fixedSubgroup (resM γ hz)) = ⊥ := by
  obtain ⟨-, hLm, -, A, hA⟩ := ctuc_on_outer_local_quotient_is_graph_or_field.2.2 γ hout hz
  rcases hA with hA | hA
  · exact oddCore_fixed_M hz hA (oddCore_fixed_S (induced_sq hγ2 hLm hA) (Or.inl ⟨A, rfl⟩))
  · exact oddCore_fixed_M hz hA (oddCore_fixed_S (induced_sq hγ2 hLm hA) (Or.inr ⟨A, rfl⟩))

theorem fixedCent_map {G G' : Type*} [Group G] [Group G'] (φ : G ≃* G') (β : MulAut G) (a : G) :
    (fixedSubgroup β ⊓ Subgroup.centralizer {a}).map φ.toMonoidHom =
      fixedSubgroup (MulAut.congr φ β) ⊓ Subgroup.centralizer {φ a} := by
  rw [Subgroup.map_inf_eq _ _ φ.toMonoidHom φ.injective, fixedSubgroup_map_congr]
  congr 1
  ext y
  simp only [Subgroup.mem_map, Subgroup.mem_centralizer_singleton_iff, MulEquiv.coe_toMonoidHom]
  constructor
  · rintro ⟨x, hx, rfl⟩
    rw [← map_mul, hx, map_mul]
  · intro hy
    refine ⟨φ.symm y, ?_, by simp⟩
    apply φ.injective
    simp only [map_mul, MulEquiv.apply_symm_apply, hy]

@[expose] def fixedCentCongr {G G' : Type*} [Group G] [Group G'] (φ : G ≃* G') (β : MulAut G)
    (a : G) : ↥(fixedSubgroup β ⊓ Subgroup.centralizer {a}) ≃*
      ↥(fixedSubgroup (MulAut.congr φ β) ⊓ Subgroup.centralizer {φ a}) :=
  (Subgroup.equivMapOfInjective _ φ.toMonoidHom φ.injective).trans
    (MulEquiv.subgroupCongr (fixedCent_map φ β a))

theorem mem_centralizer_zP_iff
    {x : Pv} :
    x ∈ Subgroup.centralizer {zP} ↔ (x : Equiv.Perm (Fin N)) ∈ onM := by
  rw [Subgroup.mem_centralizer_singleton_iff, mem_M_iff_P]

theorem map_fixed_resM
    {γ : MulAut Pv} (hz : γ zP = zP) :
    (fixedSubgroup (resM γ hz)).map (Subgroup.inclusion onM_le) =
      fixedSubgroup γ ⊓ Subgroup.centralizer {zP} := by
  ext x
  constructor
  · rintro ⟨m, hm, rfl⟩
    refine Subgroup.mem_inf.2 ⟨?_, ?_⟩
    · have hm' : resM γ hz m = m := hm
      show γ (toP m) = toP m
      apply Subtype.ext
      rw [← resM_val γ hz, hm', coe_toP]
    · rw [mem_centralizer_zP_iff, Subgroup.coe_inclusion]
      exact m.2
  · intro hx
    obtain ⟨hx1, hx2⟩ := Subgroup.mem_inf.1 hx
    have hM : (x : Equiv.Perm (Fin N)) ∈ onM := mem_centralizer_zP_iff.1 hx2
    have hx1' : γ x = x := hx1
    refine ⟨⟨x, hM⟩, ?_, Subtype.ext ?_⟩
    · show resM γ hz ⟨x, hM⟩ = ⟨x, hM⟩
      apply Subtype.ext
      rw [resM_val]
      have e : toP ⟨(x : Equiv.Perm (Fin N)), hM⟩ = x := rfl
      rw [e, hx1']
    · rw [Subgroup.coe_inclusion]

@[expose] def fixedMEquiv
    {γ : MulAut Pv} (hz : γ zP = zP) :
    fixedSubgroup (resM γ hz) ≃* ↥(fixedSubgroup γ ⊓ Subgroup.centralizer {zP}) :=
  (Subgroup.equivMapOfInjective _ _ (Subgroup.inclusion_injective onM_le)).trans
    (MulEquiv.subgroupCongr (map_fixed_resM hz))

theorem not_inner_congr
    {α : MulAut Pv} (hout : α ∉ (MulAut.conj : Pv →* MulAut Pv).range)
    (φ : Pv ≃* Pv) : MulAut.congr φ α ∉ (MulAut.conj : Pv →* MulAut Pv).range := by
  rintro ⟨h, hh⟩
  apply hout
  refine ⟨φ.symm h, ?_⟩
  have := OuterAutomorphisms.congr_conj φ.symm h
  rw [hh] at this
  rw [← this]
  ext x
  simp [MulAut.congr_apply]

theorem oddCore_fixed_centralizer
    {α : MulAut Pv}
    (hout : α ∉ (MulAut.conj : Pv →* MulAut Pv).range) (hα2 : α * α = 1) {a : Pv}
    (ha : orderOf a = 2) (hαa : α a = a) :
    CFSG.oddCore ↥(fixedSubgroup α ⊓ Subgroup.centralizer {a}) = ⊥ := by
  obtain ⟨g, hg, hga⟩ := cti_on_all_involutions_conjugate (a : Equiv.Perm (Fin N)) a.2
    (by rw [Subgroup.orderOf_coe]; exact ha)
  set gP : Pv := ⟨g, hg⟩
  set φ : Pv ≃* Pv := MulAut.conj gP⁻¹
  have hφa : φ a = zP := by
    apply Subtype.ext
    show (g⁻¹ * (a : Equiv.Perm (Fin N)) * g⁻¹⁻¹) = onz
    rw [hga]
    group
  set γ := MulAut.congr φ α with hγ
  have hz : γ zP = zP := by
    rw [← hφa, hγ, MulAut.congr_apply, MulEquiv.trans_apply, MulEquiv.trans_apply,
      MulEquiv.symm_apply_apply, hαa]
  have hγ2 : γ * γ = 1 := by
    rw [hγ, ← map_mul, hα2, map_one]
  have hcore := oddCore_fixed_outer (not_inner_congr hout φ) hγ2 hz
  have e1 := fixedCentCongr φ α a
  rw [hφa] at e1
  exact oddCore_eq_bot_of_mulEquiv (e1.trans (fixedMEquiv hz).symm).symm hcore

end CFSG.Sporadic.ONOddCore
