module

public import CFSG.Monster.B.Cbar.LocalAux

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.B

open CFSG.Monster CFSG.Monster.Code CFSG.Monster.Spin CFSG.Monster.SpinLattice
  CFSG.Monster.Griess CFSG.Monster.Visible CFSG.Monster.Generated CFSG.Monster.B.Short

theorem coordOf_zQ' : coordOf zQ = 0 :=
  (congrArg coordOf (mul_one zQ).symm).trans ((coordOf_zQ_mul 1).trans coordOf_one')

theorem zQ_ne_rStar : zQ ≠ rStar := by
  intro h
  have hs := isShortCoord_rStar
  rw [← h, coordOf_zQ'] at hs
  exact not_isShortCoord_zero hs

theorem xmat_ne_tStar : xmat ≠ tStar := fun h => zQ_ne_rStar (rhoEquiv_injective h)

theorem spinΩC_ne_zero : Spin.ΩC ≠ 0 := by
  intro h
  have h1 := congrArg (fun c : C => (c : Fin 24 → ZMod 2) 0) h
  simp [Code.Ω] at h1

theorem coordOf_wQ_fst : (coordOf wQ).1 = Spin.ΩC := by
  change (spinEquiv.symm wQ).a = Spin.ΩC
  rw [symm_wQ]

theorem rStar_ne_wQ : rStar ≠ wQ := by
  intro h
  have h1 : (0 : C) = Spin.ΩC :=
    (congrArg Prod.fst coordOf_rStar).symm.trans
      ((congrArg (fun r => (coordOf r).1) h).trans coordOf_wQ_fst)
  exact spinΩC_ne_zero h1.symm

theorem rStar_ne_zQ_mul_wQ : rStar ≠ zQ * wQ := by
  intro h
  have h1 : (0 : C) = Spin.ΩC :=
    (congrArg Prod.fst coordOf_rStar).symm.trans
      ((congrArg (fun r => (coordOf r).1) h).trans
        ((congrArg Prod.fst (coordOf_zQ_mul wQ)).trans coordOf_wQ_fst))
  exact spinΩC_ne_zero h1.symm

theorem tStar_not_mem_Vmat : tStar ∉ Vmat := by
  intro h
  rcases mem_fourGroupB.1 h with h1 | h1 | h1 | h1
  · exact tStar_ne_one h1
  · exact zQ_ne_rStar (rhoEquiv_injective (h1.trans xmat_eq_xB.symm)).symm
  · exact rStar_ne_zQ_mul_wQ (rhoEquiv_injective (h1.trans rhoEquiv_zQ_wQ.symm))
  · exact rStar_ne_wQ (rhoEquiv_injective (h1.trans rhoEquiv_wQ.symm))

theorem xmatTau_mem_Cgen : xmatTau ∈ Cgen :=
  Cgen.mul_mem (Cgen.mul_mem tauB_mem_Cgen xmat_mem_Cgen) (Cgen.inv_mem tauB_mem_Cgen)

theorem xmatTau2_mem_Cgen : xmatTau2 ∈ Cgen :=
  Cgen.mul_mem (Cgen.mul_mem (Cgen.pow_mem tauB_mem_Cgen 2) xmat_mem_Cgen)
    (Cgen.inv_mem (Cgen.pow_mem tauB_mem_Cgen 2))

theorem Vmat_le_Cgen : Vmat ≤ Cgen := by
  intro g hg
  rcases mem_fourGroupB.1 hg with rfl | rfl | rfl | rfl
  · exact Cgen.one_mem
  · exact xmat_eq_xB ▸ xmat_mem_Cgen
  · exact xmatTau_eq ▸ xmatTau_mem_Cgen
  · exact xmatTau2_eq ▸ xmatTau2_mem_Cgen

@[expose] noncomputable def yC : Cgen := ⟨xmatTau, xmatTau_mem_Cgen⟩

@[expose] noncomputable def zC : Cgen := ⟨xmatTau2, xmatTau2_mem_Cgen⟩

@[expose] noncomputable def ybar : Cbar := kappa yC

@[expose] noncomputable def zbar : Cbar := kappa zC

@[expose] noncomputable def Vbar : Subgroup Cbar := (Vmat.subgroupOf Cgen).map kappa

theorem kappa_injOn_Vmat {u u' : Cgen} (hu : (u : SpaceB ≃ₗ[ℚ] SpaceB) ∈ Vmat)
    (hu' : (u' : SpaceB ≃ₗ[ℚ] SpaceB) ∈ Vmat) (h : kappa u = kappa u') : u = u' := by
  have h1 : kappa (u⁻¹ * u') = 1 := by rw [map_mul, map_inv, h, inv_mul_cancel]
  rcases (kappa_eq_one_iff _).1 h1 with h2 | h2
  · exact inv_mul_eq_one.1 h2
  · exfalso
    apply tStar_not_mem_Vmat
    have h3 : (u : SpaceB ≃ₗ[ℚ] SpaceB)⁻¹ * u' = tStar := congrArg Subtype.val h2
    exact mem_of_eq' h3 (Vmat.mul_mem (Vmat.inv_mem hu) hu')

theorem xC_mem_Vmat : (xC : SpaceB ≃ₗ[ℚ] SpaceB) ∈ Vmat :=
  mem_fourGroupB.2 (.inr (.inl xmat_eq_xB))

theorem yC_mem_Vmat : (yC : SpaceB ≃ₗ[ℚ] SpaceB) ∈ Vmat :=
  mem_fourGroupB.2 (.inr (.inr (.inl xmatTau_eq)))

theorem zC_mem_Vmat : (zC : SpaceB ≃ₗ[ℚ] SpaceB) ∈ Vmat :=
  mem_fourGroupB.2 (.inr (.inr (.inr xmatTau2_eq)))

theorem one_mem_Vmat' : ((1 : Cgen) : SpaceB ≃ₗ[ℚ] SpaceB) ∈ Vmat := Vmat.one_mem

theorem mem_Vbar_iff (c : Cbar) : c ∈ Vbar ↔ c = 1 ∨ c = xbar ∨ c = ybar ∨ c = zbar := by
  constructor
  · rintro ⟨g, hg, rfl⟩
    have hg' : (g : SpaceB ≃ₗ[ℚ] SpaceB) ∈ Vmat := hg
    rcases mem_fourGroupB.1 hg' with h | h | h | h
    · left
      rw [show g = 1 from Subtype.ext h, map_one]
    · right; left
      exact congrArg kappa (Subtype.ext (h.trans xmat_eq_xB.symm))
    · right; right; left
      exact congrArg kappa (Subtype.ext (h.trans xmatTau_eq.symm))
    · right; right; right
      exact congrArg kappa (Subtype.ext (h.trans xmatTau2_eq.symm))
  · rintro (rfl | rfl | rfl | rfl)
    · exact Vbar.one_mem
    · exact ⟨xC, xC_mem_Vmat, rfl⟩
    · exact ⟨yC, yC_mem_Vmat, rfl⟩
    · exact ⟨zC, zC_mem_Vmat, rfl⟩

theorem xbar_mem_Vbar : xbar ∈ Vbar := (mem_Vbar_iff _).2 (.inr (.inl rfl))

theorem ybar_mem_Vbar : ybar ∈ Vbar := (mem_Vbar_iff _).2 (.inr (.inr (.inl rfl)))

theorem zbar_mem_Vbar : zbar ∈ Vbar := (mem_Vbar_iff _).2 (.inr (.inr (.inr rfl)))

theorem kappa_ne_of_val_ne {u u' : Cgen} (hu : (u : SpaceB ≃ₗ[ℚ] SpaceB) ∈ Vmat)
    (hu' : (u' : SpaceB ≃ₗ[ℚ] SpaceB) ∈ Vmat)
    (h : (u : SpaceB ≃ₗ[ℚ] SpaceB) ≠ u') : kappa u ≠ kappa u' := fun h1 =>
  h (congrArg Subtype.val (kappa_injOn_Vmat hu hu' h1))

theorem xbar_ne_one : xbar ≠ 1 := by
  have h := kappa_ne_of_val_ne xC_mem_Vmat one_mem_Vmat'
    (fun h => one_ne_xB (h.symm.trans xmat_eq_xB))
  rwa [map_one] at h

theorem ybar_ne_one : ybar ≠ 1 := by
  have h := kappa_ne_of_val_ne yC_mem_Vmat one_mem_Vmat'
    (fun h => one_ne_yB (h.symm.trans xmatTau_eq))
  rwa [map_one] at h

theorem zbar_ne_one : zbar ≠ 1 := by
  have h := kappa_ne_of_val_ne zC_mem_Vmat one_mem_Vmat'
    (fun h => one_ne_zB (h.symm.trans xmatTau2_eq))
  rwa [map_one] at h

theorem xbar_ne_ybar : xbar ≠ ybar :=
  kappa_ne_of_val_ne xC_mem_Vmat yC_mem_Vmat fun h =>
    xB_ne_yB (xmat_eq_xB.symm.trans (h.trans xmatTau_eq))

theorem ybar_ne_zbar : ybar ≠ zbar :=
  kappa_ne_of_val_ne yC_mem_Vmat zC_mem_Vmat fun h =>
    yB_ne_zB (xmatTau_eq.symm.trans (h.trans xmatTau2_eq))

theorem zbar_ne_xbar : zbar ≠ xbar :=
  kappa_ne_of_val_ne zC_mem_Vmat xC_mem_Vmat fun h =>
    xB_ne_zB (xmat_eq_xB.symm.trans (h.symm.trans xmatTau2_eq))

theorem xC_mul_self : xC * xC = 1 :=
  Subtype.ext ((congrArg (fun f => f * f) xmat_eq_xB).trans xB_mul_self)

theorem yC_mul_self : yC * yC = 1 :=
  Subtype.ext ((congrArg (fun f => f * f) xmatTau_eq).trans yB_mul_self)

theorem zC_mul_self : zC * zC = 1 :=
  Subtype.ext ((congrArg (fun f => f * f) xmatTau2_eq).trans zB_mul_self)

theorem xbar_mul_self : xbar * xbar = 1 := by
  rw [xbar, ← map_mul, xC_mul_self, map_one]

theorem ybar_mul_self : ybar * ybar = 1 := by
  rw [ybar, ← map_mul, yC_mul_self, map_one]

theorem zbar_mul_self : zbar * zbar = 1 := by
  rw [zbar, ← map_mul, zC_mul_self, map_one]

theorem orderOf_xbar : orderOf xbar = 2 :=
  orderOf_eq_prime (by rw [pow_two]; exact xbar_mul_self) xbar_ne_one

theorem mul_self_of_mem_Vbar {c : Cbar} (hc : c ∈ Vbar) : c * c = 1 := by
  rcases (mem_Vbar_iff c).1 hc with rfl | rfl | rfl | rfl
  · exact one_mul 1
  · exact xbar_mul_self
  · exact ybar_mul_self
  · exact zbar_mul_self

theorem natCard_Vbar : Nat.card Vbar = 4 := by
  have hs : (Vbar : Set Cbar) = {1, xbar, ybar, zbar} := by
    ext c
    exact mem_Vbar_iff c
  rw [← SetLike.coe_sort_coe, Nat.card_coe_set_eq, hs,
    Set.ncard_insert_of_notMem, Set.ncard_insert_of_notMem, Set.ncard_pair ybar_ne_zbar]
  · rintro (h | h)
    · exact xbar_ne_ybar h
    · exact zbar_ne_xbar h.symm
  · rintro (h | h | h)
    · exact xbar_ne_one h.symm
    · exact ybar_ne_one h.symm
    · exact zbar_ne_one h.symm

theorem isKleinFour_Vbar : IsKleinFour Vbar := by
  have : Nontrivial Vbar :=
    ⟨⟨⟨xbar, xbar_mem_Vbar⟩, 1, fun h => xbar_ne_one (congrArg Subtype.val h)⟩⟩
  refine ⟨natCard_Vbar, (Monoid.exponent_eq_prime_iff Nat.prime_two).2 fun g hg => ?_⟩
  have h1 : g ^ 2 = 1 := Subtype.ext (by
    rw [Subgroup.coe_pow, pow_two]
    exact mul_self_of_mem_Vbar g.2)
  exact orderOf_eq_prime h1 hg

theorem tauC_pow_three : tauC ^ 3 = 1 := Subtype.ext (by
  rw [Subgroup.coe_pow]
  exact tauB_pow_three)

theorem taubar_pow_three : taubar ^ 3 = 1 := by
  rw [taubar, ← map_pow, tauC_pow_three, map_one]

theorem tauB_ne_tStar : tauB ≠ tStar := by
  intro h
  have h3 : tStar ^ 3 = tStar := by
    rw [pow_succ, pow_two, tStar_mul_self, one_mul]
  apply tStar_ne_one
  rw [← h3, ← h]
  exact tauB_pow_three

theorem taubar_ne_one : taubar ≠ 1 := by
  intro h
  rcases (kappa_eq_one_iff tauC).1 h with h1 | h1
  · exact tauB_ne_one (congrArg Subtype.val h1)
  · exact tauB_ne_tStar (congrArg Subtype.val h1)

theorem orderOf_taubar : orderOf taubar = 3 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  exact orderOf_eq_prime taubar_pow_three taubar_ne_one

theorem conj_conj_eq_sq {G : Type*} [Group G] (t x : G) :
    t * (t * x * t⁻¹) * t⁻¹ = t ^ 2 * x * (t ^ 2)⁻¹ := by
  rw [pow_two, mul_inv_rev]
  simp only [mul_assoc]

theorem conj_sq_eq_of_pow_three {G : Type*} [Group G] {t : G} (ht : t ^ 3 = 1) (x : G) :
    t * (t ^ 2 * x * (t ^ 2)⁻¹) * t⁻¹ = x := by
  have h : t * t ^ 2 = 1 := (pow_succ' t 2).symm.trans ht
  calc t * (t ^ 2 * x * (t ^ 2)⁻¹) * t⁻¹ = t * t ^ 2 * x * (t * t ^ 2)⁻¹ := by group
    _ = x := by rw [h, one_mul, inv_one, mul_one]

theorem inv_conj_eq_of_conj_eq {G : Type*} [Group G] {t a b : G} (h : t * a * t⁻¹ = b) :
    t⁻¹ * b * t = a := by
  rw [← h]
  group

theorem taubar_conj_xbar : taubar * xbar * taubar⁻¹ = ybar := by
  have h : tauC * xC * tauC⁻¹ = yC := Subtype.ext rfl
  rw [taubar, xbar, ybar, ← map_inv, ← map_mul, ← map_mul, h]

theorem taubar_conj_ybar : taubar * ybar * taubar⁻¹ = zbar := by
  have h : tauC * yC * tauC⁻¹ = zC := Subtype.ext (conj_conj_eq_sq tauB xmat)
  rw [taubar, ybar, zbar, ← map_inv, ← map_mul, ← map_mul, h]

theorem taubar_conj_zbar : taubar * zbar * taubar⁻¹ = xbar := by
  have h : tauC * zC * tauC⁻¹ = xC := Subtype.ext (conj_sq_eq_of_pow_three tauB_pow_three xmat)
  rw [taubar, zbar, xbar, ← map_inv, ← map_mul, ← map_mul, h]

theorem taubar_conj_mem_Vbar {e : Cbar} (he : e ∈ Vbar) : taubar * e * taubar⁻¹ ∈ Vbar := by
  rcases (mem_Vbar_iff e).1 he with rfl | rfl | rfl | rfl
  · rw [mul_one, mul_inv_cancel]
    exact Vbar.one_mem
  · rw [taubar_conj_xbar]; exact ybar_mem_Vbar
  · rw [taubar_conj_ybar]; exact zbar_mem_Vbar
  · rw [taubar_conj_zbar]; exact xbar_mem_Vbar

theorem taubar_inv_conj_mem_Vbar {e : Cbar} (he : e ∈ Vbar) : taubar⁻¹ * e * taubar ∈ Vbar := by
  rcases (mem_Vbar_iff e).1 he with rfl | rfl | rfl | rfl
  · rw [mul_one, inv_mul_cancel]
    exact Vbar.one_mem
  · rw [inv_conj_eq_of_conj_eq taubar_conj_zbar]; exact zbar_mem_Vbar
  · rw [inv_conj_eq_of_conj_eq taubar_conj_xbar]; exact xbar_mem_Vbar
  · rw [inv_conj_eq_of_conj_eq taubar_conj_ybar]; exact ybar_mem_Vbar

theorem taubar_conj_ne {e : Cbar} (he : e ∈ Vbar) (he1 : e ≠ 1) : taubar * e * taubar⁻¹ ≠ e := by
  rcases (mem_Vbar_iff e).1 he with rfl | rfl | rfl | rfl
  · exact absurd rfl he1
  · rw [taubar_conj_xbar]; exact xbar_ne_ybar.symm
  · rw [taubar_conj_ybar]; exact ybar_ne_zbar.symm
  · rw [taubar_conj_zbar]; exact zbar_ne_xbar.symm

theorem taubar_inv_conj_ne {e : Cbar} (he : e ∈ Vbar) (he1 : e ≠ 1) :
    taubar⁻¹ * e * taubar ≠ e := by
  rcases (mem_Vbar_iff e).1 he with rfl | rfl | rfl | rfl
  · exact absurd rfl he1
  · rw [inv_conj_eq_of_conj_eq taubar_conj_zbar]; exact zbar_ne_xbar
  · rw [inv_conj_eq_of_conj_eq taubar_conj_xbar]; exact xbar_ne_ybar
  · rw [inv_conj_eq_of_conj_eq taubar_conj_ybar]; exact ybar_ne_zbar

theorem xC_mul_zC : xC * zC = zC * xC :=
  Subtype.ext (mul_comm_of_mem_fourGroupB xC_mem_Vmat zC_mem_Vmat)

theorem taubar_inv_conj_xbar : taubar⁻¹ * xbar * taubar = zbar :=
  inv_conj_eq_of_conj_eq taubar_conj_zbar

theorem xbar_commute_taubar_inv_conj :
    xbar * (taubar⁻¹ * xbar * taubar) = (taubar⁻¹ * xbar * taubar) * xbar := by
  rw [taubar_inv_conj_xbar, xbar, zbar, ← map_mul, ← map_mul, xC_mul_zC]

theorem mul_comm_of_mem_Vbar {c d : Cbar} (hc : c ∈ Vbar) (hd : d ∈ Vbar) : c * d = d * c := by
  obtain ⟨g, hg, rfl⟩ := hc
  obtain ⟨h, hh, rfl⟩ := hd
  rw [← map_mul, ← map_mul]
  exact congrArg kappa (Subtype.ext (mul_comm_of_mem_fourGroupB hg hh))

end CFSG.Monster.B
