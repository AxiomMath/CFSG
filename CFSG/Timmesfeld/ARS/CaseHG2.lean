module

public import CFSG.Timmesfeld.ARS.CaseHNeg
public import CFSG.Timmesfeld.RankTwo.ModelG2Words
public import CFSG.Timmesfeld.ARS.CaseHN4

public section

namespace CFSG.Timmesfeld.ARS

open scoped commutatorElement
open CFSG.LieType.Universal CFSG.Timmesfeld.RankOne Matrix NaturalModule FrameSL3 Sec8Field
open CFSG.Timmesfeld.RankTwo CFSG.Timmesfeld.GradedPresentation

variable {G : Type*} [Group G] {R : Set (Subgroup G)}

namespace CaseH

variable {A A₀ P P' : Subgroup G}

namespace Coords

variable {S : Setup R A A₀ P P'} {F E : Type} [Field F] [Field E] (c : Coords S F E) [CharP E 2]

@[expose] noncomputable def g2Pos (e : F →+* E) (τ : F) : Fin 6 → F → G
  | 0 => fun t => c.x1 (e t)
  | 1 => fun t => c.x2 (τ * t)
  | 2 => fun t => c.x3 (e t)
  | 3 => fun t => c.x4 (τ * t)
  | 4 => fun t => c.x5 (e t)
  | 5 => fun t => c.x6 t

@[expose] noncomputable def g2Neg (e : F →+* E) : Fin 6 → F → G
  | 0 => fun t => c.xm1 (e t)
  | 1 => fun t => c.xm2 t
  | 2 => fun t => c.xm3 (e t)
  | 3 => fun t => c.xm4 t
  | 4 => fun t => c.xm5 (e t)
  | 5 => fun t => c.xmb t

variable [CharP F 2] [Finite F] [Finite E] (e : F →+* E) (he : ∀ s u, c.c5 s u = c.c5 (e u * s) 1)
  {τ : F} (hτ0 : τ ≠ 0) (hτ : ∀ u, c.m * c.x6 u * c.m⁻¹ = c.x2 (τ * u))
include he hτ0 hτ

theorem g2_rels (hsq : ∀ s, c.sharp s = s ^ 2) (hβ : ∀ s, c.beta s = s)
    (hNt : ∀ s, c.Nt s = c.N s) :
    ∀ r ∈ rels (g2Cm (K := F)),
      FreeGroup.lift (fun g : Σ _ : Fin 6, F => c.g2Pos e τ g.1 g.2) r = 1 := by
  have := S.hyp.finite
  obtain ⟨hN, hF3, hF2, hT⟩ := c.G2_structure e he hτ0 hτ hsq
  obtain ⟨-, hU1P', hU1A, hU5P, hU3P, -⟩ :=
    positive_relations S.hyp S.hH S.hT S.hA S.h3 S.hA₀ S.hP S.hP' S.hPP'
  have key : ∀ {X : F} {Y : F}, e (τ⁻¹ * X) = e Y → X = τ * Y := fun h => by
    rw [← e.injective h, ← mul_assoc, mul_inv_cancel₀ hτ0, one_mul]
  have T_e : ∀ s t : F, c.T (e s) (e t) = τ * (s * t) := fun s t =>
    key (by rw [hT, map_mul])
  have F2_e : ∀ s t : F, c.F2 (e s) (e t) = τ * (s ^ 2 * t) := fun s t =>
    key (by rw [hF2, map_mul, map_pow])
  have N_e : ∀ s : F, c.N (e s) = τ * s ^ 3 := fun s => key (by rw [hN, map_pow])
  have sharp_e : ∀ s : F, c.sharp (e s) = e (s ^ 2) := fun s => by rw [hsq, map_pow]
  refine rels_g2Cm_of (φ := fun g : Σ _ : Fin 6, F => c.g2Pos e τ g.1 g.2) (fun i a b => ?_)
    (fun s t => ?_) (fun s t => ?_) (fun s t => ?_) (fun s t => ?_) (fun s t => ?_)
    (fun s t => hU1P' _ (c.x1_mem _) _ (c.x2_mem _)) (fun s t => hU1A _ (c.x1_mem _) _ (c.x4_mem _))
    (fun s t => c.commute_x2_x3 _ _) (fun s t => (c.commute_x4 _ (S.P'_le_M (c.x2_mem _))).symm)
    (fun s t => c.commute_x2_x5 _ _)
    (fun s t => (c.commute_x4 _ (Setup.U3_le_M (c.x3_mem _))).symm)
    (fun s t => hU3P _ (c.x3_mem _) _ (c.x6_mem _))
    (fun s t => c.commute_x4 _ (Setup.U5_le_M (c.x5_mem _)))
    (fun s t => c.commute_x4 _ (S.P_le_M (c.x6_mem _)))
    (fun s t => hU5P _ (c.x5_mem _) _ (c.x6_mem _))
  · fin_cases i <;> simp only [g2Pos, _root_.map_add, mul_add]
    exacts [c.x1_add _ _, c.x2_add _ _, c.x3_add _ _, c.x4_add _ _, c.x5_add _ _, c.x6_add _ _]
  · change ⁅c.x1 (e s), c.x3 (e t)⁆ = c.x2 (τ * (s * t))
    rw [← c.x2_T, T_e]
  · change ⁅c.x3 (e s), c.x5 (e t)⁆ = c.x4 (τ * (s * t))
    rw [← c.x4_Tp, c.Tp_eq e he, T_e, mul_comm t s]
  · change ⁅c.x2 (τ * s), c.x6 t⁆ = c.x4 (τ * (s * t))
    rw [c.comm_x2_x6, mul_assoc]
  · change ⁅c.x1 (e s), c.x5 (e t)⁆ = c.x2 (τ * (s ^ 2 * t)) * c.x4 (τ * (s * t ^ 2))
    rw [c.comm15_eq, y, hF3, c.x3_zero, mul_one, F2_e, (c.F4_F3 hβ _ _).1, F2_e, mul_comm (t ^ 2) s]
  · change ⁅c.x1 (e s), c.x6 t⁆ = c.x2 (τ * (t * s ^ 3)) * c.x3 (e (t * s ^ 2)) *
      c.x4 (τ * (t ^ 2 * s ^ 3)) * c.x5 (e (t * s))
    rw [c.comm16_eq_nf e he hNt, nf, y, N_e, sharp_e, ← map_mul, ← map_mul,
      show t * (τ * s ^ 3) = τ * (t * s ^ 3) by ring,
      show t * t * (τ * s ^ 3) = τ * (t ^ 2 * s ^ 3) by ring]

end Coords

end CaseH

end CFSG.Timmesfeld.ARS
