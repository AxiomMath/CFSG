module

public import CFSG.RankThree.GF2n.Stroth78.QuadraticForm
public import CFSG.RankThree.GF2n.Stroth78.Sec2Defs

public section

namespace CFSG.RankThree.GF2n.Stroth78

open CFSG CFSG.Open CFSG.RankThree.GF2n.Tim79a CFSG.LargeExtraspecial.Timmesfeld
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {z : G} {E F : Subgroup G}

noncomputable abbrev qS (S : Setting z E F) :
    QuadraticForm (ZMod 2) (Additive (QbarOf S)) :=
  letI := modAbF S
  q S

noncomputable def conjAutQ (S : Setting z E F) (h : ↥(H z)) : MulAut ↥(Q z) :=
  (Subgroup.subgroupOfEquivOfLe (Q_le_H S)).symm.trans
    ((MulAut.conjNormal (H := (Q z).subgroupOf (H z)) h).trans
      (Subgroup.subgroupOfEquivOfLe (Q_le_H S)))

theorem conjAutQ_apply (S : Setting z E F) (h : ↥(H z)) (x : ↥(Q z)) :
    ((conjAutQ S h x : ↥(Q z)) : G) = (h : G) * (x : G) * (h : G)⁻¹ := by
  simp [conjAutQ, Subgroup.subgroupOfEquivOfLe, MulAut.conjNormal_apply]

theorem conjAutQ_one (S : Setting z E F) : conjAutQ S 1 = 1 := by
  ext x
  rw [conjAutQ_apply]
  simp

theorem conjAutQ_mul (S : Setting z E F) (h h' : ↥(H z)) :
    conjAutQ S (h * h') = conjAutQ S h * conjAutQ S h' := by
  ext x
  rw [MulAut.mul_apply, conjAutQ_apply, conjAutQ_apply, conjAutQ_apply]
  simp only [Subgroup.coe_mul, Subgroup.coe_inv]
  group

theorem ZQ_subgroupOf_eq_center (z : G) :
    (ZQ z).subgroupOf (Q z) = Subgroup.center ↥(Q z) := by
  rw [ZQ, centerIn_eq_map_center]
  change Subgroup.comap (Q z).subtype ((Subgroup.center ↥(Q z)).map (Q z).subtype) =
    Subgroup.center ↥(Q z)
  exact Subgroup.comap_map_eq_self_of_injective (Q z).subtype_injective _

private theorem map_center_conjAutQ (S : Setting z E F) (h : ↥(H z)) :
    ((ZQ z).subgroupOf (Q z)).map (conjAutQ S h) = (ZQ z).subgroupOf (Q z) := by
  rw [ZQ_subgroupOf_eq_center z]
  change (Subgroup.center ↥(Q z)).map (conjAutQ S h).toMonoidHom = Subgroup.center ↥(Q z)
  exact (Subgroup.characteristic_iff_map_eq.mp inferInstance) (conjAutQ S h)

private noncomputable def conjQbarMul (S : Setting z E F) (h : ↥(H z)) :
    QbarOf S ≃* QbarOf S :=
  QuotientGroup.congr ((ZQ z).subgroupOf (Q z)) ((ZQ z).subgroupOf (Q z))
    (conjAutQ S h) (map_center_conjAutQ S h)

noncomputable def conjQbar (S : Setting z E F) (h : ↥(H z)) :
    Additive (QbarOf S) ≃ₗ[ZMod 2] Additive (QbarOf S) :=
  (MulEquiv.toAdditive (conjQbarMul S h)).toLinearEquiv (by
    intro c x
    rcases CFSG.RankThree.Literature.FSmith.zmod2_cases c with rfl | rfl <;> simp)

theorem conjQbar_apply_mk (S : Setting z E F) (h : ↥(H z)) (x : ↥(Q z)) :
    conjQbar S h (Additive.ofMul (QuotientGroup.mk x)) =
      Additive.ofMul (QuotientGroup.mk (conjAutQ S h x)) := by
  rfl

theorem conjQbar_one (S : Setting z E F) : conjQbar S 1 = 1 := by
  refine LinearEquiv.ext fun v => ?_
  obtain ⟨x, rfl⟩ := Additive.ofMul.surjective v
  obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective x
  simp [conjQbar_apply_mk, conjAutQ_one]

theorem conjQbar_mul (S : Setting z E F) (h h' : ↥(H z)) :
    conjQbar S (h * h') = conjQbar S h * conjQbar S h' := by
  refine LinearEquiv.ext fun v => ?_
  obtain ⟨x, rfl⟩ := Additive.ofMul.surjective v
  obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective x
  simp [conjQbar_apply_mk, conjAutQ_mul]

theorem conjQbar_mem_orthogonal (S : Setting z E F) (h : ↥(H z)) :
    conjQbar S h ∈ TauCeti.QuadraticMap.orthogonalGroup (qS S) := by
  letI := modAbF S
  change conjQbar S h ∈ TauCeti.QuadraticMap.orthogonalGroup (q S)
  rw [TauCeti.QuadraticMap.mem_orthogonalGroup_iff]
  intro v
  obtain ⟨x, rfl⟩ := Additive.ofMul.surjective v
  obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective x
  rw [conjQbar_apply_mk]
  change q S (QuotientGroup.mk (conjAutQ S h y)) = q S (QuotientGroup.mk y)
  have hsq : ((conjAutQ S h y : ↥(Q z)) : G) ^ 2 = 1 ↔ (y : G) ^ 2 = 1 := by
    rw [conjAutQ_apply, conj_pow]
    constructor
    · intro hh
      have h2 : (h : G) * (y : G) ^ 2 = (h : G) * 1 := by
        calc
          (h : G) * (y : G) ^ 2 = ((h : G) * (y : G) ^ 2 * (h : G)⁻¹) * (h : G) := by
            group
          _ = 1 * (h : G) := by rw [hh]
          _ = (h : G) * 1 := by group
      exact mul_left_cancel h2
    · intro hh
      rw [hh]
      group
  have hzero : q S (QuotientGroup.mk (conjAutQ S h y)) = 0 ↔
      q S (QuotientGroup.mk y) = 0 := by
    rw [q_eq_zero_iff, q_eq_zero_iff]
    exact hsq
  rcases CFSG.RankThree.Literature.FSmith.zmod2_cases
      (q S (QuotientGroup.mk (conjAutQ S h y))) with h1 | h1 <;>
    rcases CFSG.RankThree.Literature.FSmith.zmod2_cases
      (q S (QuotientGroup.mk y)) with h2 | h2
  · rw [h1, h2]
  · exfalso
    have : q S (QuotientGroup.mk y) = 0 := hzero.mp h1
    rw [h2] at this
    norm_num at this
  · exfalso
    have : q S (QuotientGroup.mk (conjAutQ S h y)) = 0 := hzero.mpr h2
    rw [h1] at this
    norm_num at this
  · rw [h1, h2]

noncomputable def rho (S : Setting z E F) :
    ↥(H z) →* TauCeti.QuadraticMap.orthogonalGroup (qS S) :=
  { toFun := fun h => ⟨conjQbar S h, conjQbar_mem_orthogonal S h⟩
    map_one' := by
      apply Subtype.ext
      exact conjQbar_one S
    map_mul' := by
      intro h h'
      apply Subtype.ext
      exact conjQbar_mul S h h' }

private theorem mem_subgroupOf_of_rho_eq_one (S : Setting z E F) {h : ↥(H z)}
    (hh : rho S h = 1) : h ∈ (Q z).subgroupOf (H z) := by
  rw [Subgroup.mem_subgroupOf]
  refine (S.hyp.centralizer_quotient (h : G)).mp ⟨h.2, ?_⟩
  intro x hx
  have hfix : ∀ y : ↥(Q z), (conjAutQ S h y) * y⁻¹ ∈ (ZQ z).subgroupOf (Q z) := by
    intro y
    have hq : conjQbar S h (Additive.ofMul (QuotientGroup.mk y)) =
        Additive.ofMul (QuotientGroup.mk y) := by
      rw [show conjQbar S h = 1 from congrArg Subtype.val hh]
      rfl
    rw [conjQbar_apply_mk] at hq
    have hq' : (QuotientGroup.mk (conjAutQ S h y) : QbarOf S) = QuotientGroup.mk y :=
      Additive.ofMul.injective hq
    have hmem := (QuotientGroup.eq_iff_div_mem).mp hq'
    simpa [div_eq_mul_inv] using hmem
  have hmem : ((conjAutQ S h ⟨x, hx⟩ * ⟨x, hx⟩⁻¹ : ↥(Q z)) : G) ∈ ZQ z :=
    Subgroup.mem_subgroupOf.mp (hfix ⟨x, hx⟩)
  simpa [conjAutQ_apply] using hmem

private theorem rho_eq_one_of_mem_Q (S : Setting z E F) {h : ↥(H z)}
    (hh : (h : G) ∈ Q z) : rho S h = 1 := by
  apply Subtype.ext
  refine LinearEquiv.ext fun v => ?_
  obtain ⟨x, rfl⟩ := Additive.ofMul.surjective v
  obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective x
  change conjQbar S h (Additive.ofMul (QuotientGroup.mk y)) =
    (1 : Additive (QbarOf S) ≃ₗ[ZMod 2] Additive (QbarOf S))
      (Additive.ofMul (QuotientGroup.mk y))
  rw [conjQbar_apply_mk]
  have hmem : conjAutQ S h y * y⁻¹ ∈ (ZQ z).subgroupOf (Q z) := by
    rw [Subgroup.mem_subgroupOf]
    have hcomm : ⁅(h : G), (y : G)⁆ ∈ ⁅Q z, Q z⁆ :=
      Subgroup.commutator_mem_commutator hh y.2
    rw [Q_deriv_eq S] at hcomm
    rw [ZQ_eq S]
    exact Subgroup.mem_sup_right (by
      simpa [conjAutQ_apply, commutatorElement_def] using hcomm)
  have hq : (QuotientGroup.mk (conjAutQ S h y) : QbarOf S) = QuotientGroup.mk y := by
    rw [QuotientGroup.eq_iff_div_mem]
    simpa [div_eq_mul_inv] using hmem
  rw [hq]
  simp

theorem rho_ker (S : Setting z E F) : (rho S).ker = (Q z).subgroupOf (H z) := by
  ext h
  rw [MonoidHom.mem_ker]
  constructor
  · intro hh
    exact mem_subgroupOf_of_rho_eq_one S hh
  · intro hh
    exact rho_eq_one_of_mem_Q S (Subgroup.mem_subgroupOf.mp hh)

@[expose] noncomputable def rhoBar (S : Setting z E F) :
    Hbar z →* TauCeti.QuadraticMap.orthogonalGroup (qS S) :=
  QuotientGroup.lift ((Q z).subgroupOf (H z)) (rho S) (le_of_eq (rho_ker S).symm)

theorem rhoBar_apply_mk (S : Setting z E F) (h : ↥(H z)) :
    rhoBar S (QuotientGroup.mk h) = rho S h :=
  QuotientGroup.lift_mk (N := (Q z).subgroupOf (H z)) (φ := rho S)
    (le_of_eq (rho_ker S).symm) h

theorem rhoBar_injective (S : Setting z E F) : Function.Injective (rhoBar S) := by
  intro a b hab
  obtain ⟨a', rfl⟩ := QuotientGroup.mk_surjective a
  obtain ⟨b', rfl⟩ := QuotientGroup.mk_surjective b
  rw [rhoBar_apply_mk, rhoBar_apply_mk] at hab
  have h1 : rho S (a' * b'⁻¹) = 1 := by
    rw [map_mul, map_inv, hab, mul_inv_cancel]
  have h2 : a' * b'⁻¹ ∈ (rho S).ker := by
    rw [MonoidHom.mem_ker]
    exact h1
  rw [rho_ker S] at h2
  rw [QuotientGroup.eq_iff_div_mem]
  simpa [div_eq_mul_inv] using h2


theorem rho_apply_mk (S : Setting z E F) (h : ↥(H z)) :
    (rho S h : TauCeti.QuadraticMap.orthogonalGroup (qS S)) =
      ⟨conjQbar S h, conjQbar_mem_orthogonal S h⟩ := by
  apply Subtype.ext
  rfl

end CFSG.RankThree.GF2n.Stroth78
