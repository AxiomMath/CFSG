module

public import CFSG.Quasithin.Vol2.Ch10SecQ1M12Card
public import CFSG.Quasithin.Vol2.Ch10SecQ1Base

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecA

namespace C10P01

open CFSG.Monster.Code CFSG.Quasithin CFSG.Blueprint

theorem m24Fix_permAct {p : Equiv.Perm (Fin 24)} (hp : p ∈ AutPerm) (e : G6.PermMod 24) :
    m24Fix (G6.permAct 24 p e) = (m24Fix e).map (MulAut.conj p).toMonoidHom := by
  ext σ
  simp only [Subgroup.mem_map, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  constructor
  · rintro ⟨hσ, hfix⟩
    refine ⟨p⁻¹ * σ * p, ⟨AutPerm.mul_mem (AutPerm.mul_mem (AutPerm.inv_mem hp) hσ) hp, ?_⟩,
      by group⟩
    show G6.permAct 24 (p⁻¹ * σ * p) e = e
    rw [map_mul, map_mul, MulAut.mul_apply, MulAut.mul_apply, hfix, ← MulAut.mul_apply,
      ← map_mul, inv_mul_cancel, map_one, MulAut.one_apply]
  · rintro ⟨ρ, ⟨hρ, hfix⟩, rfl⟩
    refine ⟨AutPerm.mul_mem (AutPerm.mul_mem hp hρ) (AutPerm.inv_mem hp), ?_⟩
    show G6.permAct 24 (p * ρ * p⁻¹) (G6.permAct 24 p e) = G6.permAct 24 p e
    have hinv : G6.permAct 24 p⁻¹ (G6.permAct 24 p e) = e := by
      rw [← MulAut.mul_apply, ← map_mul, inv_mul_cancel, map_one, MulAut.one_apply]
    rw [map_mul, MulAut.mul_apply, hinv, map_mul, MulAut.mul_apply, hfix]

attribute [local instance] arrowAction

theorem mem_stabilizer_dodecadW_iff (p : ↥AutPerm) :
    p ∈ MulAction.stabilizer ↥AutPerm dodecadW ↔ (p : Equiv.Perm (Fin 24)) ∈ m24Fix dodecadE := by
  rw [MulAction.mem_stabilizer_iff]
  constructor
  · intro h
    exact ⟨p.2, (permAct_dodecadE_eq_iff _).2 fun y => congrFun h y⟩
  · rintro ⟨-, h⟩
    funext y
    exact (permAct_dodecadE_eq_iff _).1 h y

theorem card_stabilizer_dodecadW :
    Nat.card (MulAction.stabilizer ↥AutPerm dodecadW) = 95040 := by
  rw [← m24Fix_dodecadE_props.2]
  exact Nat.card_congr
    { toFun := fun s => ⟨s.1.1, (mem_stabilizer_dodecadW_iff s.1).1 s.2⟩
      invFun := fun t => ⟨⟨t.1, t.2.1⟩, (mem_stabilizer_dodecadW_iff ⟨t.1, t.2.1⟩).2 t.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }

theorem exists_permAct_eq
    {eY : G6.PermMod 24} (hY : eY ∈ golayC) (hw : hammingNorm (Multiplicative.toAdd eY) = 12) :
    ∃ p ∈ AutPerm, G6.permAct 24 p dodecadE = eY := by
  classical
  set S : Finset (Fin 24 → ZMod 2) :=
    (Finset.univ.filter (· ∈ C)).filter fun x => hammingNorm x = 12 with hS
  have hS12 : S.card = 2576 := by rw [hS, card_filter_wt, wtCount_twelve]
  have h1 := Subgroup.index_mul_card (MulAction.stabilizer ↥AutPerm dodecadW)
  rw [MulAction.index_stabilizer, card_stabilizer_dodecadW, card_AutPerm] at h1
  have horb : (MulAction.orbit ↥AutPerm dodecadW).ncard = 2576 := by
    have h2 : (MulAction.orbit ↥AutPerm dodecadW).ncard * 95040 = 2576 * 95040 := by
      rw [h1]
    exact Nat.eq_of_mul_eq_mul_right (by norm_num) h2
  have hsub : MulAction.orbit ↥AutPerm dodecadW ⊆ (S : Set (Fin 24 → ZMod 2)) := by
    rintro _ ⟨p, rfl⟩
    have he : p • dodecadW = dodecadW ∘ ⇑((p : Equiv.Perm (Fin 24))⁻¹) := rfl
    have hmem : p • dodecadW ∈ C := by
      rw [he]
      exact comp_mem_of_mem_AutPerm (AutPerm.inv_mem p.2) dodecadW_mem_C
    have hwt : hammingNorm (p • dodecadW) = 12 := by
      rw [he, hammingNorm_comp_perm, hammingNorm_dodecadW]
    simp [hS, hmem, hwt]
  have heq : MulAction.orbit ↥AutPerm dodecadW = (S : Set (Fin 24 → ZMod 2)) :=
    Set.eq_of_subset_of_ncard_le hsub (by rw [Set.ncard_coe_finset, hS12, horb]) (Set.toFinite _)
  have hYS : Multiplicative.toAdd eY ∈ (S : Set (Fin 24 → ZMod 2)) := by
    have hYC : Multiplicative.toAdd eY ∈ C := hY
    simp [hS, hYC, hw]
  rw [← heq] at hYS
  obtain ⟨p, hp⟩ := hYS
  refine ⟨p, p.2, ?_⟩
  apply Multiplicative.toAdd.injective
  rw [← hp]
  rfl

end C10P01

open C10P01 CFSG.Monster.Code CFSG.Blueprint

theorem factB4aM12_holds :
    FactB4aM12 := by
  intro eY hY hw X _ hX π
  obtain ⟨p, hp, hpe⟩ := exists_permAct_eq hY hw
  have hmap : (m24Fix dodecadE).map (MulAut.conj p).toMonoidHom = m24Fix eY := by
    rw [← hpe, m24Fix_permAct hp]
  let e1 : ↥(m24Fix dodecadE) ≃* ↥(m24Fix eY) :=
    ((m24Fix dodecadE).equivMapOfInjective _ (MulAut.conj p).injective).trans
      (MulEquiv.subgroupCongr hmap)
  obtain ⟨⟨e2⟩, -⟩ := m24Fix_dodecadE_props
  have hs : IsSimpleGroup NativeSporadic.M12 := CFSG.Sporadic.Mathieu.fam_m12_simplicity.2.2
  exact not_surjective_of_mulEquiv (e1.symm.trans e2) hs
    (by rw [CFSG.Sporadic.Mathieu.card_M12]; exact not_shapeCard_95040) hX π

end CFSG.Quasithin.Vol2.Ch10.SecA
