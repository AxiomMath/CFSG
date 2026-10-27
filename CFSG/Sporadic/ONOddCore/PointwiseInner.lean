module

public import CFSG.Sporadic.Schreier.ONR3E
public import CFSG.Sporadic.Schreier.ONTwoCentralizer

public noncomputable section

namespace CFSG.Sporadic.ONOddCore

open CFSG.ONSchreier

theorem conj_c_mem_P
    {x : Equiv.Perm (Fin N)} (hx : x ∈ Pv) : onc * x * onc⁻¹ ∈ Pv :=
  mul_mem (mul_mem onc_mem hx) (inv_mem onc_mem)

theorem conj_cinv_mem_P
    {x : Equiv.Perm (Fin N)} (hx : x ∈ Pv) : onc⁻¹ * x * onc ∈ Pv :=
  mul_mem (mul_mem (inv_mem onc_mem) hx) onc_mem

@[expose] def cP :
    Pv := ⟨onc, onc_mem⟩

@[expose] def tPv :
    Pv := ⟨ont, onM_le ont_mem_M⟩

theorem mem_M1_iff_P
    {x : Pv} : (x : Equiv.Perm (Fin N)) ∈ onM1 ↔ x * tPv = tPv * x := by
  rw [onM1_eq_centralizer_t, Subgroup.mem_inf, Subgroup.mem_centralizer_singleton_iff]
  constructor
  · rintro ⟨-, h⟩
    exact Subtype.ext h
  · intro h
    exact ⟨x.2, congrArg Subtype.val h⟩

theorem mem_M1_of_fix
    {α : MulAut Pv} (ht : α tPv = tPv) {x : Pv}
    (hx : (x : Equiv.Perm (Fin N)) ∈ onM1) : ((α x : Pv) : Equiv.Perm (Fin N)) ∈ onM1 := by
  rw [mem_M1_iff_P] at hx ⊢
  calc α x * tPv = α (x * tPv) := by rw [map_mul, ht]
    _ = α (tPv * x) := by rw [hx]
    _ = tPv * α x := by rw [map_mul, ht]

@[expose] def cmc
    (m : onM) : Pv := ⟨onc * m * onc⁻¹, conj_c_mem_P (onM_le m.2)⟩

theorem cmc_mem_M1
    (m : onM) : ((cmc m : Pv) : Equiv.Perm (Fin N)) ∈ onM1 := by
  rw [mem_M1_iff]
  show onc⁻¹ * (onc * m * onc⁻¹) * onc ∈ onM
  rw [show onc⁻¹ * (onc * (m : Equiv.Perm (Fin N)) * onc⁻¹) * onc = m by group]
  exact m.2

@[expose] def transportFun
    (α : MulAut Pv) (ht : α tPv = tPv) (m : onM) : onM :=
  ⟨onc⁻¹ * ((α (cmc m) : Pv) : Equiv.Perm (Fin N)) * onc,
    mem_M1_iff.1 (mem_M1_of_fix ht (cmc_mem_M1 m))⟩

theorem transportFun_val
    (α : MulAut Pv) (ht : α tPv = tPv) (m : onM) :
    ((transportFun α ht m : onM) : Equiv.Perm (Fin N)) =
      onc⁻¹ * ((α (cmc m) : Pv) : Equiv.Perm (Fin N)) * onc := rfl

theorem inv_fix
    {α : MulAut Pv} (ht : α tPv = tPv) : α⁻¹ tPv = tPv := by
  rw [MulAut.inv_apply, MulEquiv.symm_apply_eq, ht]

theorem cmc_transportFun
    (α : MulAut Pv) (ht : α tPv = tPv) (m : onM) :
    cmc (transportFun α ht m) = α (cmc m) := by
  apply Subtype.ext
  show onc * (onc⁻¹ * ((α (cmc m) : Pv) : Equiv.Perm (Fin N)) * onc) * onc⁻¹ = _
  group

@[expose] def transportAut
    (α : MulAut Pv) (ht : α tPv = tPv) : MulAut onM where
  toFun := transportFun α ht
  invFun := transportFun α⁻¹ (inv_fix ht)
  left_inv m := by
    apply Subtype.ext
    rw [transportFun_val, cmc_transportFun, MulAut.inv_apply, MulEquiv.symm_apply_apply]
    show onc⁻¹ * (onc * m * onc⁻¹) * onc = m
    group
  right_inv m := by
    apply Subtype.ext
    rw [transportFun_val, cmc_transportFun, MulAut.inv_apply, MulEquiv.apply_symm_apply]
    show onc⁻¹ * (onc * m * onc⁻¹) * onc = m
    group
  map_mul' m n := by
    apply Subtype.ext
    have e : cmc (m * n) = cmc m * cmc n := by
      apply Subtype.ext
      show onc * (m * n : Equiv.Perm (Fin N)) * onc⁻¹ =
        (onc * m * onc⁻¹) * (onc * n * onc⁻¹)
      group
    rw [Subgroup.coe_mul, transportFun_val, transportFun_val, transportFun_val, e, map_mul,
      Subgroup.coe_mul]
    group

theorem transportAut_apply
    (α : MulAut Pv) (ht : α tPv = tPv) (m : onM) :
    ((transportAut α ht m : onM) : Equiv.Perm (Fin N)) =
      onc⁻¹ * ((α (cmc m) : Pv) : Equiv.Perm (Fin N)) * onc := rfl

theorem closure_M_M1 :
    Subgroup.closure {x : Pv | (x : Equiv.Perm (Fin N)) ∈ onM ∨
      (x : Equiv.Perm (Fin N)) ∈ onM1} = ⊤ := by
  apply Subgroup.map_injective Pv.subtype_injective
  rw [MonoidHom.map_closure, ← MonoidHom.range_eq_map, Subgroup.range_subtype]
  have hS : (Pv.subtype '' {x : Pv | (x : Equiv.Perm (Fin N)) ∈ onM ∨
      (x : Equiv.Perm (Fin N)) ∈ onM1}) = (onM : Set (Equiv.Perm (Fin N))) ∪ onM1 := by
    ext x
    simp only [Set.mem_image, Set.mem_ofPred_eq, Subgroup.coe_subtype, Set.mem_union,
      SetLike.mem_coe]
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact hy
    · rintro (hx | hx)
      · exact ⟨⟨x, onM_le hx⟩, Or.inl hx, rfl⟩
      · exact ⟨⟨x, onM1_le_P hx⟩, Or.inr hx, rfl⟩
  rw [hS, Subgroup.closure_union, Subgroup.closure_eq, Subgroup.closure_eq, onM_sup_M1]

theorem mulAut_ext_M_M1
    {α γ : MulAut Pv}
    (hM : ∀ x : Pv, (x : Equiv.Perm (Fin N)) ∈ onM → α x = γ x)
    (hM1 : ∀ x : Pv, (x : Equiv.Perm (Fin N)) ∈ onM1 → α x = γ x) : α = γ := by
  apply MulEquiv.toMonoidHom_injective
  apply MonoidHom.eq_of_eqOn_dense closure_M_M1
  rintro x (hx | hx)
  · exact hM x hx
  · exact hM1 x hx

theorem conj_zP_fixes_M
    (x : Pv) (hx : (x : Equiv.Perm (Fin N)) ∈ onM) :
    MulAut.conj zP x = x := by
  apply Subtype.ext
  show onz * x * onz⁻¹ = x
  rw [← onz_comm_M hx, mul_assoc, mul_inv_cancel, mul_one]

theorem onz_eq_cvc :
    onz = onc * onv * onc⁻¹ := by
  rw [onv]
  group

theorem pointwise_M_cases
    (α : MulAut Pv)
    (hα : ∀ m : Pv, (m : Equiv.Perm (Fin N)) ∈ onM → α m = m) :
    α = 1 ∨ α = MulAut.conj zP := by
  have ht : α tPv = tPv := hα tPv ont_mem_M
  set β := transportAut α ht with hβ
  have hβD : ∀ d : onM, (d : Equiv.Perm (Fin N)) ∈ onD → β d = d := by
    intro d hd
    rw [onD, Subgroup.mem_map] at hd
    obtain ⟨e, he, hde⟩ := hd
    have heM : e ∈ onM := (onD0_le he).1
    have hcmc : cmc d = ⟨e, onM_le heM⟩ := by
      apply Subtype.ext
      show onc * d * onc⁻¹ = e
      rw [← hde]
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
      group
    apply Subtype.ext
    rw [hβ, transportAut_apply, hcmc, hα _ heM]
    show onc⁻¹ * e * onc = d
    rw [← hde]
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
  have hcases : β = 1 ∨ β = MulAut.conj vM := by
    have hmem : β ∈ {β : MulAut onM | ∀ d : onM, (d : Equiv.Perm (Fin N)) ∈ onD → β d = d} :=
      hβD
    rw [pointwise_eq] at hmem
    simpa using hmem
  have hM1 : ∀ (x : Pv) (hx : (x : Equiv.Perm (Fin N)) ∈ onM1),
      x = cmc ⟨onc⁻¹ * x * onc, mem_M1_iff.1 hx⟩ := by
    intro x hx
    apply Subtype.ext
    show (x : Equiv.Perm (Fin N)) = onc * (onc⁻¹ * x * onc) * onc⁻¹
    group
  rcases hcases with h1 | hv
  · left
    refine mulAut_ext_M_M1 (fun x hx => hα x hx) fun x hx => ?_
    rw [hM1 x hx]
    set m : onM := ⟨onc⁻¹ * x * onc, mem_M1_iff.1 hx⟩
    have e1 : (β m : Equiv.Perm (Fin N)) = m := by rw [h1]; rfl
    rw [hβ, transportAut_apply] at e1
    apply Subtype.ext
    show ((α (cmc m) : Pv) : Equiv.Perm (Fin N)) = onc * m * onc⁻¹
    rw [← e1]
    group
  · right
    refine mulAut_ext_M_M1 (fun x hx => (hα x hx).trans (conj_zP_fixes_M x hx).symm)
      fun x hx => ?_
    rw [hM1 x hx]
    set m : onM := ⟨onc⁻¹ * x * onc, mem_M1_iff.1 hx⟩
    have e1 : (β m : Equiv.Perm (Fin N)) = onv * m * onv⁻¹ := by rw [hv]; rfl
    rw [hβ, transportAut_apply] at e1
    apply Subtype.ext
    show ((α (cmc m) : Pv) : Equiv.Perm (Fin N)) = onz * (onc * m * onc⁻¹) * onz⁻¹
    have e2 : ((α (cmc m) : Pv) : Equiv.Perm (Fin N)) = onc * (onv * m * onv⁻¹) * onc⁻¹ := by
      rw [← e1]
      group
    rw [e2, onz_eq_cvc]
    group

theorem conj_zP_ne_one :
    MulAut.conj zP ≠ 1 := by
  intro h
  have ht : MulAut.conj zP tPv = tPv := conj_zP_fixes_M tPv ont_mem_M
  apply conj_v_ne_one
  refine MulEquiv.ext fun m => Subtype.ext ?_
  have e : ((MulAut.conj zP (cmc m) : Pv) : Equiv.Perm (Fin N)) = onc * m * onc⁻¹ := by
    rw [h]
    rfl
  have e' : ((MulAut.conj zP (cmc m) : Pv) : Equiv.Perm (Fin N)) =
      onz * (onc * m * onc⁻¹) * onz⁻¹ := rfl
  rw [e', onz_eq_cvc] at e
  show onv * m * onv⁻¹ = m
  calc onv * m * onv⁻¹ = onc⁻¹ * ((onc * onv * onc⁻¹) * (onc * m * onc⁻¹) *
        (onc * onv * onc⁻¹)⁻¹) * onc := by group
    _ = onc⁻¹ * (onc * m * onc⁻¹) * onc := by rw [e]
    _ = m := by group

theorem r3e_on_involution_centralizer_pointwise_automorphisms_inner :
    {α : MulAut Pv | ∀ m : Pv, (m : Equiv.Perm (Fin N)) ∈ onM → α m = m} =
        {1, MulAut.conj zP} ∧ (1 : MulAut Pv) ≠ MulAut.conj zP ∧
      ∀ α : MulAut Pv, (∀ m : Pv, (m : Equiv.Perm (Fin N)) ∈ onM → α m = m) →
        α ∈ (MulAut.conj : Pv →* MulAut Pv).range := by
  refine ⟨?_, fun h => conj_zP_ne_one h.symm, fun α hα => ?_⟩
  · ext α
    simp only [Set.mem_ofPred_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · exact pointwise_M_cases α
    · rintro (rfl | rfl)
      · intro m _
        rfl
      · exact conj_zP_fixes_M
  · rcases pointwise_M_cases α hα with rfl | rfl
    · exact ⟨1, map_one _⟩
    · exact ⟨zP, rfl⟩

end CFSG.Sporadic.ONOddCore
