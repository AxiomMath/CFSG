module

public import CFSG.OddTranspositions.PartThree.Eleven.Wong.RootData
public import CFSG.OddTranspositions.PartThree.Eleven.Wong.CentBasic
public import CFSG.OddTranspositions.PartThree.Eleven.Wong.CentDiag
public import CFSG.GroupTheory.ABGLocalTools.Constraint

public section

namespace CFSG.OddTranspositions.PartThree.Wong.RootData

open Subgroup

variable {G : Type} [Group G] (D : RootData G)

theorem q1_ofAdd (a : ZMod 5) : D.q1 (.ofAdd a) = D.i1 (thetaM a) := rfl

theorem q2_ofAdd (a : ZMod 5) : D.q2 (.ofAdd a) = D.i2 (thetaM a) := rfl

theorem q12_ofAdd (a : ZMod 5) : D.q12 (.ofAdd a) = D.q1 (.ofAdd a) * D.q2 (.ofAdd (-a)) := rfl

theorem q3_ofAdd (a : ZMod 5) : D.q3 (.ofAdd a) = D.y⁻¹ * D.q12 (.ofAdd a) * D.y := by
  simp [q3, MulAut.conj_apply]

theorem q4_ofAdd (a : ZMod 5) : D.q4 (.ofAdd a) = D.c2⁻¹ * D.q3 (.ofAdd a) * D.c2 := by
  simp [q4, MulAut.conj_apply]

private theorem hM_conj_thetaM (a : ZMod 5) :
    hM⁻¹ * thetaM a * hM = thetaM (4 * a) := by
  revert a
  decide

private theorem thetaM_eq_zero_of_eq_one_or_neg_one {a : ZMod 5}
    (h : thetaM a = 1 ∨ thetaM a = -1) : a = 0 := by
  rcases h with h | h
  · have h' := congrArg (fun x : SL5 => (x : Matrix (Fin 2) (Fin 2) (ZMod 5)) 1 0) h
    simpa [thetaM] using h'
  · have h' := congrArg (fun x : SL5 => (x : Matrix (Fin 2) (Fin 2) (ZMod 5)) 1 0) h
    simpa [thetaM] using h'

theorem thetaHom_injective : Function.Injective thetaHom := by
  intro a b hab
  have h : (thetaM a.toAdd : Matrix (Fin 2) (Fin 2) (ZMod 5)) 1 0 =
      (thetaM b.toAdd : Matrix (Fin 2) (Fin 2) (ZMod 5)) 1 0 :=
    congrArg (fun x : SL5 => (x : Matrix (Fin 2) (Fin 2) (ZMod 5)) 1 0) hab
  exact Multiplicative.toAdd.injective (by simpa [thetaM] using h)

theorem q1_injective : Function.Injective D.q1 :=
  D.inj1.comp thetaHom_injective

theorem q2_injective : Function.Injective D.q2 :=
  D.inj2.comp thetaHom_injective

theorem q12_injective : Function.Injective D.q12 := by
  intro a b hab
  have h1 : D.q12 (a * b⁻¹) = 1 := by
    rw [map_mul, map_inv, hab, mul_inv_cancel]
  have h2 : D.q1 (a * b⁻¹) = D.q2 (a * b⁻¹) := by
    have h3 : D.q1 (a * b⁻¹) * (D.q2 (a * b⁻¹))⁻¹ = 1 := by
      simpa [q12] using h1
    exact mul_inv_eq_one.mp h3
  have hq : D.i1 (thetaM (a * b⁻¹).toAdd) = D.i2 (thetaM (a * b⁻¹).toAdd) := h2
  have hθ : thetaM (a * b⁻¹).toAdd = 1 ∨ thetaM (a * b⁻¹).toAdd = -1 := by
    rcases (i1_eq_i2_iff D.inj1 D.inj2 D.orderOf_t D.range_inf).mp hq with hx | hx
    exacts [Or.inl hx.1, Or.inr hx.1]
  have h0 := thetaM_eq_zero_of_eq_one_or_neg_one hθ
  have h4 : (a * b⁻¹ : Multiplicative (ZMod 5)) = 1 :=
    Multiplicative.toAdd.injective (by simpa using h0)
  exact mul_inv_eq_one.mp h4

theorem q3_injective : Function.Injective D.q3 :=
  (MulAut.conj D.y⁻¹).injective.comp D.q12_injective

theorem q4_injective : Function.Injective D.q4 :=
  (MulAut.conj D.c2⁻¹).injective.comp D.q3_injective

private theorem card_range_eq_five {H : Type} [Group H]
    {f : Multiplicative (ZMod 5) →* H} (hf : Function.Injective f) :
    Nat.card f.range = 5 := by
  rw [← Nat.card_congr (MonoidHom.ofInjective hf).toEquiv]
  rw [Nat.card_eq_fintype_card, Fintype.card_multiplicative, ZMod.card]

theorem card_P1 : Nat.card D.P1 = 5 :=
  card_range_eq_five D.q1_injective

theorem card_P2 : Nat.card D.P2 = 5 :=
  card_range_eq_five D.q2_injective

theorem card_P3 : Nat.card D.P3 = 5 :=
  card_range_eq_five D.q3_injective

theorem card_P4 : Nat.card D.P4 = 5 :=
  card_range_eq_five D.q4_injective

theorem card_D2 : Nat.card D.D2 = 5 :=
  card_range_eq_five D.q12_injective

theorem D1_eq_range : D.D1 = (D.d.comp thetaHom).range := by
  change closure (Set.range fun q : ZMod 5 => D.d (thetaM q)) =
    (D.d.comp thetaHom).range
  refine le_antisymm ?_ ?_
  · refine (closure_le _).mpr ?_
    rintro _ ⟨q, rfl⟩
    exact MonoidHom.mem_range.mpr ⟨Multiplicative.ofAdd q, rfl⟩
  · intro x hx
    obtain ⟨a, rfl⟩ := MonoidHom.mem_range.mp hx
    exact subset_closure ⟨a.toAdd, rfl⟩

private theorem d_theta_eq_one {a : ZMod 5} (h : D.d (thetaM a) = 1) : a = 0 := by
  rw [D.d_apply] at h
  exact thetaM_eq_zero_of_eq_one_or_neg_one
    ((diag_eq_one_iff D.inj1 D.inj2 D.orderOf_t D.range_inf).mp h)

private theorem d_theta_injective : Function.Injective (D.d.comp thetaHom) := by
  intro a b hab
  have h1 : (D.d.comp thetaHom) (a * b⁻¹) = 1 := by
    rw [map_mul, map_inv, hab, mul_inv_cancel]
  have h2 : (a * b⁻¹ : Multiplicative (ZMod 5)) = 1 := by
    apply Multiplicative.toAdd.injective
    simpa using d_theta_eq_one D h1
  exact mul_inv_eq_one.mp h2

theorem card_D1 : Nat.card D.D1 = 5 := by
  rw [D.D1_eq_range]
  exact card_range_eq_five (d_theta_injective D)

theorem commute_q1_q2 (a b : Multiplicative (ZMod 5)) : Commute (D.q1 a) (D.q2 b) :=
  D.commute _ _

private theorem conj_i1_i2 (x y : SL5) :
    (D.i1 x)⁻¹ * D.i2 y * D.i1 x = D.i2 y :=
  (D.commute x y).inv_mul_cancel

private theorem conj_i2_i1 (x y : SL5) :
    (D.i2 x)⁻¹ * D.i1 y * D.i2 x = D.i1 y :=
  (D.commute y x).symm.inv_mul_cancel

theorem t_conj_q1 (a : Multiplicative (ZMod 5)) : D.t⁻¹ * D.q1 a * D.t = D.q1 a := by
  rw [show D.t = D.i1 (-1) from D.t_eq_i1]
  exact ((Commute.neg_one_left (thetaM a.toAdd)).map D.i1).inv_mul_cancel

theorem t_conj_q2 (a : Multiplicative (ZMod 5)) : D.t⁻¹ * D.q2 a * D.t = D.q2 a := by
  rw [show D.t = D.i2 (-1) from D.t_eq_i2]
  exact ((Commute.neg_one_left (thetaM a.toAdd)).map D.i2).inv_mul_cancel

theorem u_conj_q1 (a : Multiplicative (ZMod 5)) : D.u⁻¹ * D.q1 a * D.u = D.q2 a := by
  show D.u⁻¹ * D.i1 (thetaM a.toAdd) * D.u = D.i2 (thetaM a.toAdd)
  exact D.swap (thetaM a.toAdd)

theorem u_conj_q2 (a : Multiplicative (ZMod 5)) : D.u⁻¹ * D.q2 a * D.u = D.q1 a := by
  show D.u⁻¹ * D.i2 (thetaM a.toAdd) * D.u = D.i1 (thetaM a.toAdd)
  exact D.u_conj_i2 (thetaM a.toAdd)

theorem h1_conj_q1 (a : ZMod 5) : D.h1⁻¹ * D.q1 (.ofAdd a) * D.h1 = D.q1 (.ofAdd (4 * a)) := by
  rw [q1_ofAdd]
  rw [show D.h1 = D.i1 hM from rfl, ← map_inv, ← map_mul, ← map_mul, hM_conj_thetaM]
  rw [q1_ofAdd]

theorem h1_conj_q2 (a : Multiplicative (ZMod 5)) : D.h1⁻¹ * D.q2 a * D.h1 = D.q2 a := by
  rw [show D.h1 = D.i1 hM from rfl]
  exact conj_i1_i2 D hM (thetaM a.toAdd)

theorem h2_conj_q1 (a : Multiplicative (ZMod 5)) : D.h2⁻¹ * D.q1 a * D.h2 = D.q1 a := by
  rw [show D.h2 = D.i2 hM from rfl]
  exact conj_i2_i1 D hM (thetaM a.toAdd)

theorem h2_conj_q2 (a : ZMod 5) : D.h2⁻¹ * D.q2 (.ofAdd a) * D.h2 = D.q2 (.ofAdd (4 * a)) := by
  rw [q2_ofAdd]
  rw [show D.h2 = D.i2 hM from rfl, ← map_inv, ← map_mul, ← map_mul, hM_conj_thetaM]
  rw [q2_ofAdd]

theorem c2_conj_q1 (a : Multiplicative (ZMod 5)) : D.c2⁻¹ * D.q1 a * D.c2 = D.q1 a := by
  rw [show D.c2 = D.i2 cM from rfl]
  exact conj_i2_i1 D cM (thetaM a.toAdd)

theorem y_commute_u : Commute D.y D.u := by
  have hs : Commute D.s D.u := by
    simpa [D.outer.sq] using (Commute.refl D.s).pow_right 2
  have hw : Commute D.w D.u := D.d_commute_u cM
  show Commute (D.s * D.w) D.u
  exact hs.mul_left hw

private theorem y_mul_t : D.y * D.t = D.t * D.u * D.y := by
  have hty : D.t * D.y = D.y * D.t * D.u := by
    calc D.t * D.y = D.y * (D.y⁻¹ * D.t * D.y) := by group
      _ = D.y * (D.t * D.u) := by
            rw [show D.y = D.s * D.w from rfl, D.outer.y_conj_t]
      _ = D.y * D.t * D.u := by group
  have h3 : D.t * D.y * D.u = D.y * D.t := by
    calc D.t * D.y * D.u = (D.y * D.t * D.u) * D.u := by rw [hty]
      _ = D.y * D.t := by rw [mul_assoc (D.y * D.t) D.u D.u, D.u_mul_u, mul_one]
  rw [← h3, mul_assoc, D.y_commute_u.eq, mul_assoc]

private theorem q12_conj_t (a : Multiplicative (ZMod 5)) :
    D.t⁻¹ * D.q12 a * D.t = D.q12 a := by
  change D.t⁻¹ * (D.q1 a * D.q2 a⁻¹) * D.t = D.q1 a * D.q2 a⁻¹
  calc D.t⁻¹ * (D.q1 a * D.q2 a⁻¹) * D.t
      = (D.t⁻¹ * D.q1 a * D.t) * (D.t⁻¹ * D.q2 a⁻¹ * D.t) := by group
    _ = D.q1 a * D.q2 a⁻¹ := by rw [t_conj_q1, t_conj_q2]

private theorem q12_conj_u (a : Multiplicative (ZMod 5)) :
    D.u⁻¹ * D.q12 a * D.u = D.q12 a⁻¹ := by
  have hR : D.q12 a⁻¹ = D.q1 a⁻¹ * D.q2 a := by
    change D.q1 a⁻¹ * D.q2 (a⁻¹)⁻¹ = D.q1 a⁻¹ * D.q2 a
    rw [inv_inv]
  rw [hR]
  change D.u⁻¹ * (D.q1 a * D.q2 a⁻¹) * D.u = D.q1 a⁻¹ * D.q2 a
  calc D.u⁻¹ * (D.q1 a * D.q2 a⁻¹) * D.u
      = (D.u⁻¹ * D.q1 a * D.u) * (D.u⁻¹ * D.q2 a⁻¹ * D.u) := by group
    _ = D.q2 a * D.q1 a⁻¹ := by rw [u_conj_q1, u_conj_q2]
    _ = D.q1 a⁻¹ * D.q2 a :=
      (D.commute (thetaM (a⁻¹).toAdd) (thetaM a.toAdd)).symm.eq

theorem t_conj_q3 (a : ZMod 5) : D.t⁻¹ * D.q3 (.ofAdd a) * D.t = D.q3 (.ofAdd (-a)) := by
  rw [q3_ofAdd, q3_ofAdd]
  have hR : D.q12 ((.ofAdd a)⁻¹) = D.q12 (.ofAdd (-a)) := by
    rw [ofAdd_neg]
  calc D.t⁻¹ * (D.y⁻¹ * D.q12 (.ofAdd a) * D.y) * D.t
      = (D.y * D.t)⁻¹ * D.q12 (.ofAdd a) * (D.y * D.t) := by group
    _ = (D.t * D.u * D.y)⁻¹ * D.q12 (.ofAdd a) * (D.t * D.u * D.y) := by
          rw [y_mul_t]
    _ = D.y⁻¹ * (D.u⁻¹ * (D.t⁻¹ * D.q12 (.ofAdd a) * D.t) * D.u) * D.y := by group
    _ = D.y⁻¹ * (D.u⁻¹ * D.q12 (.ofAdd a) * D.u) * D.y := by rw [q12_conj_t]
    _ = D.y⁻¹ * D.q12 ((.ofAdd a)⁻¹) * D.y := by rw [q12_conj_u]
    _ = D.y⁻¹ * D.q12 (.ofAdd (-a)) * D.y := by rw [hR]

theorem u_conj_q3 (a : ZMod 5) : D.u⁻¹ * D.q3 (.ofAdd a) * D.u = D.q3 (.ofAdd (-a)) := by
  rw [q3_ofAdd, q3_ofAdd]
  have hR : D.q12 ((.ofAdd a)⁻¹) = D.q12 (.ofAdd (-a)) := by
    rw [ofAdd_neg]
  calc D.u⁻¹ * (D.y⁻¹ * D.q12 (.ofAdd a) * D.y) * D.u
      = (D.y * D.u)⁻¹ * D.q12 (.ofAdd a) * (D.y * D.u) := by group
    _ = (D.u * D.y)⁻¹ * D.q12 (.ofAdd a) * (D.u * D.y) := by rw [D.y_commute_u.eq]
    _ = D.y⁻¹ * (D.u⁻¹ * D.q12 (.ofAdd a) * D.u) * D.y := by group
    _ = D.y⁻¹ * D.q12 ((.ofAdd a)⁻¹) * D.y := by rw [q12_conj_u]
    _ = D.y⁻¹ * D.q12 (.ofAdd (-a)) * D.y := by rw [hR]

theorem h2_conj_d_thetaM (a : ZMod 5) :
    D.h2⁻¹ * D.d (thetaM a) * D.h2 = D.q12 (.ofAdd a) := by
  have h4 : (4 : ZMod 5) * a = -a := by
    revert a
    decide
  rw [D.d_apply, show D.h2 = D.i2 hM from rfl, q12_ofAdd, q1_ofAdd, q2_ofAdd]
  calc (D.i2 hM)⁻¹ * (D.i1 (thetaM a) * D.i2 (thetaM a)) * D.i2 hM
      = D.i1 (thetaM a) * (D.i2 hM⁻¹ * D.i2 (thetaM a) * D.i2 hM) := by
          rw [← map_inv, ← mul_assoc (D.i2 hM⁻¹) (D.i1 (thetaM a)) (D.i2 (thetaM a)),
            (D.commute (thetaM a) hM⁻¹).symm.eq]
          group
    _ = D.i1 (thetaM a) * D.i2 ((hM⁻¹ * thetaM a) * hM) := by
          rw [← map_mul, ← map_mul]
    _ = D.i1 (thetaM a) * D.i2 (thetaM (4 * a)) := by rw [hM_conj_thetaM]
    _ = D.i1 (thetaM a) * D.i2 (thetaM (-a)) := by rw [h4]

theorem D2_eq_map_D1 : D.D2 = D.D1.map (MulAut.conj D.h2⁻¹).toMonoidHom := by
  have hcomp : (MulAut.conj D.h2⁻¹).toMonoidHom.comp (D.d.comp thetaHom) = D.q12 := by
    apply MonoidHom.ext
    intro a
    simpa [MulAut.conj_apply, thetaHom] using D.h2_conj_d_thetaM a.toAdd
  rw [D.D1_eq_range, ← MonoidHom.range_comp, hcomp]
  rfl

theorem P3_eq_map_D2 : D.P3 = D.D2.map (MulAut.conj D.y⁻¹).toMonoidHom := by
  change ((MulAut.conj D.y⁻¹).toMonoidHom.comp D.q12).range =
    D.q12.range.map (MulAut.conj D.y⁻¹).toMonoidHom
  rw [MonoidHom.range_comp]

theorem P4_eq_map_P3 : D.P4 = D.P3.map (MulAut.conj D.c2⁻¹).toMonoidHom := by
  change ((MulAut.conj D.c2⁻¹).toMonoidHom.comp D.q3).range =
    D.q3.range.map (MulAut.conj D.c2⁻¹).toMonoidHom
  rw [MonoidHom.range_comp]

theorem map_D1_y : D.D1.map (MulAut.conj D.y⁻¹).toMonoidHom = D.D1 :=
  Subgroup.mem_normalizer_iff_map_conj_eq.mp (inv_mem D.outer.y_mem_normalizer)

theorem Q_le_centralizer : D.Q ≤ centralizer (D.D1 : Set G) :=
  Subgroup.map_subtype_le _

theorem odd_card_Q [Finite G] : Odd (Nat.card D.Q) := by
  change Odd (Nat.card ((CFSG.oddCore (centralizer (D.D1 : Set G))).map
    (centralizer (D.D1 : Set G)).subtype))
  rw [Subgroup.card_map_of_injective (Subgroup.subtype_injective _)]
  exact CFSG.ABGLocalTools.odd_card_oddCore

theorem V_le_centralizer : D.V ≤ centralizer (D.P1 : Set G) :=
  Subgroup.map_subtype_le _

theorem odd_card_V [Finite G] : Odd (Nat.card D.V) := by
  change Odd (Nat.card ((CFSG.oddCore (centralizer (D.P1 : Set G))).map
    (centralizer (D.P1 : Set G)).subtype))
  rw [Subgroup.card_map_of_injective (Subgroup.subtype_injective _)]
  exact CFSG.ABGLocalTools.odd_card_oddCore

end CFSG.OddTranspositions.PartThree.Wong.RootData
