module

public import CFSG.Timmesfeld.ARS.CaseHNeg
public import CFSG.Timmesfeld.RankTwo.ModelD43Words
public import CFSG.Timmesfeld.ARS.CaseHN4

public section

namespace CFSG.Timmesfeld.ARS

open scoped commutatorElement
open CFSG.LieType.Universal CFSG.Timmesfeld.RankOne Matrix NaturalModule FrameSL3 Sec8Field
open CFSG.Timmesfeld.RankTwo CFSG.Timmesfeld.GradedPresentation CFSG.LieType.Steinberg.TwistedD4

variable {G : Type*} [Group G] {R : Set (Subgroup G)}

namespace CaseH

section Fixed

variable {F E : Type} [Field F] [Field E] [Finite F] [Finite E] (e : F →+* E) {σ : E →+* E}
  {q : ℕ} (hF : Nat.card F = q) (hσ : ∀ c, σ c = c ^ q)
include hF hσ

omit [Finite E] in
theorem e_mem_fixedField (u : F) : e u ∈ fixedField σ := by
  have := Fintype.ofFinite F
  rw [mem_fixedField_iff, hσ, ← map_pow, ← hF, Nat.card_eq_fintype_card, FiniteField.pow_card]

theorem exists_e_eq (hq : 1 < q) {c : E} (hc : σ c = c) : ∃ u, e u = c := by
  classical
  have := Fintype.ofFinite F
  have := Fintype.ofFinite E
  by_contra hne
  simp only [not_exists] at hne
  set T : Finset E := insert c (Finset.univ.image e) with hT
  have hcT : c ∉ Finset.univ.image e := by
    simp only [Finset.mem_image, Finset.mem_univ, true_and, not_exists]
    exact hne
  have hcard : T.card = q + 1 := by
    rw [hT, Finset.card_insert_of_notMem hcT, Finset.card_image_of_injective _ e.injective,
      Finset.card_univ, ← Nat.card_eq_fintype_card, hF]
  have hroot : ∀ x : T, (Polynomial.X ^ q - Polynomial.X : Polynomial E).eval (x : E) = 0 := by
    rintro ⟨x, hx⟩
    simp only [Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X]
    rw [sub_eq_zero]
    rcases Finset.mem_insert.1 hx with rfl | hx
    · rw [← hσ, hc]
    · obtain ⟨u, -, rfl⟩ := Finset.mem_image.1 hx
      rw [← hσ]
      exact e_mem_fixedField e hF hσ u
  have hP := Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero
    (Polynomial.X ^ q - Polynomial.X : Polynomial E) (f := fun x : T => (x : E))
    Subtype.val_injective hroot (by
      rw [FiniteField.X_pow_card_sub_X_natDegree_eq E hq, Fintype.card_coe, hcard]
      omega)
  have hdeg := FiniteField.X_pow_card_sub_X_natDegree_eq E hq
  rw [hP, Polynomial.natDegree_zero] at hdeg
  omega

@[expose] noncomputable def fixedEquiv (hq : 1 < q) : F ≃+* fixedField σ :=
  RingEquiv.ofBijective (e.codRestrict (fixedField σ) (e_mem_fixedField e hF hσ))
    ⟨fun u v h => e.injective (congrArg Subtype.val h), fun c => by
      obtain ⟨u, hu⟩ := exists_e_eq e hF hσ hq c.2
      exact ⟨u, Subtype.ext hu⟩⟩

@[expose] noncomputable def fixedInv (hq : 1 < q) : fixedField σ →+* F :=
  (fixedEquiv e hF hσ hq).symm.toRingHom

theorem e_fixedInv (hq : 1 < q) (c : fixedField σ) : e (fixedInv e hF hσ hq c) = c := by
  have h := (fixedEquiv e hF hσ hq).apply_symm_apply c
  exact congrArg Subtype.val h

theorem fixedInv_surjective (hq : 1 < q) : Function.Surjective (fixedInv e hF hσ hq) :=
  (fixedEquiv e hF hσ hq).symm.surjective

end Fixed

variable {A A₀ P P' : Subgroup G}

namespace Coords

variable {S : Setup R A A₀ P P'} {F E : Type} [Field F] [Field E] (c : Coords S F E) [CharP E 2]
  {σ : E →+* E}

@[expose] noncomputable def d4PosS : Fin 6 → E → G
  | 0 => c.x1
  | 2 => c.x3
  | 4 => c.x5
  | _ => fun _ => 1

@[expose] noncomputable def d4NegS : Fin 6 → E → G
  | 0 => c.xm1
  | 2 => c.xm3
  | 4 => c.xm5
  | _ => fun _ => 1

@[expose] noncomputable def d4PosL (ι : fixedField σ →+* F) (τ : F) : Fin 6 → fixedField σ → G
  | 1 => fun t => c.x2 (τ * ι t)
  | 3 => fun t => c.x4 (τ * ι t)
  | 5 => fun t => c.x6 (ι t)
  | _ => fun _ => 1

@[expose] noncomputable def d4NegL (ι : fixedField σ →+* F) : Fin 6 → fixedField σ → G
  | 1 => fun t => c.xm2 (ι t)
  | 3 => fun t => c.xm4 (ι t)
  | 5 => fun t => c.xmb (ι t)
  | _ => fun _ => 1

@[expose] noncomputable def d4Pos (ι : fixedField σ →+* F) (τ : F) : (Σ i, d43Par σ i) → G
  | ⟨0, t⟩ => c.d4PosS 0 t
  | ⟨1, t⟩ => c.d4PosL ι τ 1 t
  | ⟨2, t⟩ => c.d4PosS 2 t
  | ⟨3, t⟩ => c.d4PosL ι τ 3 t
  | ⟨4, t⟩ => c.d4PosS 4 t
  | ⟨5, t⟩ => c.d4PosL ι τ 5 t

variable [CharP F 2] [Finite F] [Finite E] (e : F →+* E) (he : ∀ s u, c.c5 s u = c.c5 (e u * s) 1)
  {τ : F} (hτ0 : τ ≠ 0) (hτ : ∀ u, c.m * c.x6 u * c.m⁻¹ = c.x2 (τ * u))
include he hτ0 hτ

theorem d4_rels (hσ3 : ∀ x, σ (σ (σ x)) = x) (hsq : ∀ s, c.sharp s = σ s * σ (σ s))
    (hβ : ∀ s, c.beta s = s) (hNt : ∀ s, c.Nt s = c.N s) (ι : fixedField σ →+* F)
    (heι : ∀ t, e (ι t) = t) :
    ∀ r ∈ rels (d43Cm hσ3), FreeGroup.lift (c.d4Pos ι τ) r = 1 := by
  have := S.hyp.finite
  obtain ⟨hN, hF3, hF2, hT⟩ := c.D4_structure e he hτ0 hτ σ hσ3 hsq
  obtain ⟨-, hU1P', hU1A, hU5P, hU3P, -⟩ :=
    positive_relations S.hyp S.hH S.hT S.hA S.h3 S.hA₀ S.hP S.hP' S.hPP'
  have key : ∀ {X : F} {Y : fixedField σ}, e (τ⁻¹ * X) = (Y : E) → X = τ * ι Y := fun {X Y} h => by
    rw [← heι Y] at h
    rw [← e.injective h, ← mul_assoc, mul_inv_cancel₀ hτ0, one_mul]
  have T_eq : ∀ s t : E, c.T s t = τ * ι (d43Tr hσ3 (s * t)) := fun s t =>
    key (by rw [hT, coe_d43Tr]; rfl)
  have F2_eq : ∀ s t : E, c.F2 s t = τ * ι (d43Tr hσ3 (d43Sharp σ s * t)) := fun s t =>
    key (by rw [hF2, coe_d43Tr, hsq]; rfl)
  have N_eq' : ∀ s : E, c.N s = τ * ι (d43Norm hσ3 s) := fun s =>
    key (by rw [hN, coe_d43Norm])
  refine rels_d43Cm_of hσ3 (φ := c.d4Pos ι τ)
    (d43_add_of (fun a b => c.x1_add a b)
      (fun a b => by
        change c.x2 (τ * ι (a + b)) = c.x2 (τ * ι a) * c.x2 (τ * ι b)
        rw [_root_.map_add, mul_add, c.x2_add])
      (fun a b => c.x3_add a b)
      (fun a b => by
        change c.x4 (τ * ι (a + b)) = c.x4 (τ * ι a) * c.x4 (τ * ι b)
        rw [_root_.map_add, mul_add, c.x4_add])
      (fun a b => c.x5_add a b)
      (fun a b => by
        change c.x6 (ι (a + b)) = c.x6 (ι a) * c.x6 (ι b)
        rw [_root_.map_add, c.x6_add]))
    (fun s t => ?_) (fun s t => ?_) (fun s t => ?_) (fun s t => ?_) (fun s t => ?_)
    (fun s t => hU1P' _ (c.x1_mem _) _ (c.x2_mem _)) (fun s t => hU1A _ (c.x1_mem _) _ (c.x4_mem _))
    (fun s t => c.commute_x2_x3 _ _) (fun s t => (c.commute_x4 _ (S.P'_le_M (c.x2_mem _))).symm)
    (fun s t => c.commute_x2_x5 _ _)
    (fun s t => (c.commute_x4 _ (Setup.U3_le_M (c.x3_mem _))).symm)
    (fun s t => hU3P _ (c.x3_mem _) _ (c.x6_mem _))
    (fun s t => c.commute_x4 _ (Setup.U5_le_M (c.x5_mem _)))
    (fun s t => c.commute_x4 _ (S.P_le_M (c.x6_mem _)))
    (fun s t => hU5P _ (c.x5_mem _) _ (c.x6_mem _))
  · change ⁅c.x1 s, c.x3 t⁆ = c.x2 (τ * ι (d43Tr hσ3 (s * t)))
    rw [← c.x2_T, T_eq]
  · change ⁅c.x3 s, c.x5 t⁆ = c.x4 (τ * ι (d43Tr hσ3 (s * t)))
    rw [← c.x4_Tp, c.Tp_eq e he, T_eq, mul_comm t s]
  · change ⁅c.x2 (τ * ι s), c.x6 (ι t)⁆ = c.x4 (τ * ι (s * t))
    rw [c.comm_x2_x6, _root_.map_mul, mul_assoc]
  · change ⁅c.x1 s, c.x5 t⁆ = c.x2 (τ * ι (d43Tr hσ3 (d43Sharp σ s * t))) *
      c.x3 (d43Cross σ s t) * c.x4 (τ * ι (d43Tr hσ3 (s * d43Sharp σ t)))
    rw [c.comm15_eq, y, F2_eq, hF3, (c.F4_F3 hβ _ _).1, F2_eq, mul_comm (d43Sharp σ t) s]
    rfl
  · change ⁅c.x1 s, c.x6 (ι t)⁆ = c.x2 (τ * ι (t * d43Norm hσ3 s)) * c.x3 ((t : E) * d43Sharp σ s) *
      c.x4 (τ * ι (t ^ 2 * d43Norm hσ3 s)) * c.x5 ((t : E) * s)
    rw [c.comm16_eq_nf e he hNt, nf, y, N_eq', heι, hsq, _root_.map_mul, _root_.map_mul,
      _root_.map_pow, show ι t * (τ * ι (d43Norm hσ3 s)) = τ * (ι t * ι (d43Norm hσ3 s)) by ring,
      show ι t * ι t * (τ * ι (d43Norm hσ3 s)) = τ * (ι t ^ 2 * ι (d43Norm hσ3 s)) by ring]
    rfl

end Coords

end CaseH

end CFSG.Timmesfeld.ARS
