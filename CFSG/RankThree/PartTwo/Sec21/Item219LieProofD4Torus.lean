module

public import CFSG.LieType.Chevalley.TrialityAllCharTorusCoordinates
public import CFSG.RankThree.Chevalley.SteinbergBTTrialitySplitPrimePlane
import CFSG.RankThree.Chevalley.SteinbergCBTrialityOpposition
import CFSG.RankThree.PartTwo.Sec4.Item417Res8ProofD4Plane
import CFSG.RankThree.PartOne.K128.D4Syl

public section

set_option linter.unusedSectionVars false

namespace CFSG.RankThree.PartTwo.Sec21.Item219LieProof

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.Chevalley
  CFSG.RankThree.Chevalley.SteinbergBT.TrialityPlane CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley Subgroup


variable {K : Type} [Field K] {σ : K ≃+* K}

theorem trialityOuterTorus_eq_outerTuple (ζ : (trialityFixedField K σ.toRingHom)ˣ) :
    trialityOuterTorus K σ (trialityFixedUnit K σ ζ) =
      rootDiagUnit TwistTag.D4.tag (outerTuple (trialityFixedUnit K σ ζ)) := by
  have hσz := units_map_trialityFixedUnit (σ := σ) ζ
  have hx₁ : trialityOuterTorus K σ (trialityFixedUnit K σ ζ ^ (1 : ℤ)) *
      trialityMiddleTorus K σ (ζ ^ (0 : ℤ)) =
      rootDiagUnit TwistTag.D4.tag (outerTuple (trialityFixedUnit K σ ζ)) := by
    simp only [trialityOuter_mul_middle_eq, zpow_one, zpow_zero, map_one, hσz, one_pow,
      inv_one, mul_one]
    congr 1
    refine vec4_eq ?_ ?_ ?_ ?_ <;> group
  rwa [zpow_one, zpow_zero, trialityMiddleTorus, map_one, torusElt_one, mul_one] at hx₁

theorem trialityMiddleTorus_eq_middleTuple (ζ : (trialityFixedField K σ.toRingHom)ˣ) :
    trialityMiddleTorus K σ ζ =
      rootDiagUnit TwistTag.D4.tag (middleTuple (trialityFixedUnit K σ ζ)) := by
  have hx₂ : trialityOuterTorus K σ (trialityFixedUnit K σ ζ ^ (0 : ℤ)) *
      trialityMiddleTorus K σ (ζ ^ (1 : ℤ)) =
      rootDiagUnit TwistTag.D4.tag (middleTuple (trialityFixedUnit K σ ζ)) := by
    simp only [trialityOuter_mul_middle_eq, zpow_one, zpow_zero, map_one, one_pow, inv_one,
      mul_one, one_mul]
    congr 1
    refine vec4_eq ?_ ?_ ?_ ?_ <;> group
  have h1 : trialityOuterTorus K σ 1 = 1 := by
    rw [trialityOuterTorus_eq]
    simp only [map_one, torusElt_one, mul_one]
  rwa [zpow_zero, zpow_one, h1, one_mul] at hx₂

theorem mem_graphFixedRootTorus_of_commute {ζ : (trialityFixedField K σ.toRingHom)ˣ}
    (hζ : orderOf (trialityFixedUnit K σ ζ) = 3) {g : ModGL TwistTag.D4.tag K}
    (hg : g ∈ graphFixedRootGroup TwistTag.D4 K σ.toRingHom)
    (h1 : g * trialityOuterTorus K σ (trialityFixedUnit K σ ζ) =
      trialityOuterTorus K σ (trialityFixedUnit K σ ζ) * g)
    (h2 : g * trialityMiddleTorus K σ ζ = trialityMiddleTorus K σ ζ * g) :
    g ∈ graphFixedRootTorus TwistTag.D4 K σ.toRingHom := by
  set z := trialityFixedUnit K σ ζ with hz
  set d₁ := rootDiagUnit TwistTag.D4.tag (outerTuple z) with hd₁
  set d₂ := rootDiagUnit TwistTag.D4.tag (middleTuple z) with hd₂
  have e₁ : trialityOuterTorus K σ z = d₁ := trialityOuterTorus_eq_outerTuple ζ
  have e₂ : trialityMiddleTorus K σ ζ = d₂ := trialityMiddleTorus_eq_middleTuple ζ
  rw [e₁] at h1
  rw [e₂] at h2
  have hT₁ : d₁ ∈ torusGroup TwistTag.D4.tag K := by
    rw [← e₁, trialityOuterTorus_eq]
    exact mul_mem (mul_mem (torusElt_mem_torusGroup _ _) (torusElt_mem_torusGroup _ _))
      (torusElt_mem_torusGroup _ _)
  have hT₂ : d₂ ∈ torusGroup TwistTag.D4.tag K := by
    rw [← e₂]
    exact torusElt_mem_torusGroup _ _
  set V := zpowers d₁ ⊔ zpowers d₂ with hV
  have hVT : V ≤ torusGroup TwistTag.D4.tag K :=
    sup_le (zpowers_le.2 hT₁) (zpowers_le.2 hT₂)
  have hcV : V ≤ centralizer ({g} : Set (ModGL TwistTag.D4.tag K)) :=
    sup_le (zpowers_le.2 (mem_centralizer_singleton_iff.mpr h1.symm))
      (zpowers_le.2 (mem_centralizer_singleton_iff.mpr h2.symm))
  have hgV : g ∈ normalizer (V : Set (ModGL TwistTag.D4.tag K)) := by
    rw [mem_normalizer_iff]
    intro x
    constructor
    · intro hx
      have hc := mem_centralizer_singleton_iff.mp (hcV hx)
      rw [← hc, mul_inv_cancel_right]
      exact hx
    · intro hx
      have hc := mem_centralizer_singleton_iff.mp (hcV hx)
      have h3 : g * (g * x * g⁻¹) = g * x := by
        rw [← hc]
        group
      rw [mul_left_cancel h3] at hx
      exact hx
  obtain ⟨h, hh, w, hw, rfl⟩ := exists_eq_mul_canonicalRep_of_mem_normalizer σ
    (Sec4.Res417Eight.rootCharKernel_outer_inter_middle_three hζ) hVT
    (mem_sup_left (mem_zpowers _)) (mem_sup_right (mem_zpowers _)) hg hgV
  have hhT : h ∈ torusGroup TwistTag.D4.tag K :=
    (Subgroup.mem_inf.1 (Subgroup.mem_inf.1 hh).1).1
  have hfix : ∀ d ∈ torusGroup TwistTag.D4.tag K,
      h * canonicalRep (coxeterSystem TwistTag.D4.tag) K w * d =
        d * (h * canonicalRep (coxeterSystem TwistTag.D4.tag) K w) →
      d * canonicalRep (coxeterSystem TwistTag.D4.tag) K w * d⁻¹ =
        canonicalRep (coxeterSystem TwistTag.D4.tag) K w := by
    intro d hd hc
    have hhd : h * d = d * h := mul_comm_of_mem_torusGroup' hhT hd
    have h4 : canonicalRep (coxeterSystem TwistTag.D4.tag) K w * d =
        d * canonicalRep (coxeterSystem TwistTag.D4.tag) K w := by
      apply mul_left_cancel (a := h)
      calc h * (canonicalRep (coxeterSystem TwistTag.D4.tag) K w * d) =
          h * canonicalRep (coxeterSystem TwistTag.D4.tag) K w * d := by group
        _ = d * (h * canonicalRep (coxeterSystem TwistTag.D4.tag) K w) := hc
        _ = (d * h) * canonicalRep (coxeterSystem TwistTag.D4.tag) K w := by group
        _ = (h * d) * canonicalRep (coxeterSystem TwistTag.D4.tag) K w := by rw [hhd]
        _ = h * (d * canonicalRep (coxeterSystem TwistTag.D4.tag) K w) := by group
    rw [← h4, mul_inv_cancel_right]
  have hs₁ := (conj_canonicalRep_eq_iff (outerTuple z) w).1 (hfix d₁ hT₁ h1)
  have hs₂ := (conj_canonicalRep_eq_iff (middleTuple z) w).1 (hfix d₂ hT₂ h2)
  have hw1 := Sec4.Res417Eight.eq_one_of_mem_rootCharStabilizer_three hζ hw hs₁ hs₂
  rw [hw1, canonicalRep_one, mul_one]
  exact hh

@[expose] noncomputable def rotT (K : Type) [Field K] : ModGL TwistTag.D4.tag K :=
  (trialityMiddleRep K * trialityOuterRep K) ^ 2

theorem rotT_mem : rotT K ∈ graphFixedRootGroup TwistTag.D4 K σ.toRingHom :=
  pow_mem (mul_mem (trialityMiddleRep_mem_graphFixedRootGroup _)
    (trialityOuterRep_mem_graphFixedRootGroup _)) 2

theorem trialityTorusHom_one_right (a : Kˣ) :
    trialityTorusHom σ (a, 1) = trialityOuterTorus K σ a := by
  change trialityOuterTorus K σ a * trialityMiddleTorus K σ 1 = _
  rw [trialityMiddleTorus, map_one, torusElt_one, mul_one]

theorem trialityTorusHom_one_left (b : (trialityFixedField K σ.toRingHom)ˣ) :
    trialityTorusHom σ (1, b) = trialityMiddleTorus K σ b := by
  change trialityOuterTorus K σ 1 * trialityMiddleTorus K σ b = _
  rw [trialityOuterTorus_eq]
  simp only [map_one, torusElt_one, one_mul]

theorem trialityNorm_fixedUnit (hσ3 : σ ^ 3 = 1) (b : (trialityFixedField K σ.toRingHom)ˣ) :
    trialityNorm σ hσ3 (trialityFixedUnit K σ b) = b ^ 3 := by
  have hinj : Function.Injective (trialityFixedUnit K σ) :=
    Units.map_injective (f := (trialityFixedField K σ.toRingHom).subtype.toMonoidHom)
      Subtype.val_injective
  apply hinj
  rw [trialityFixedUnit_norm, units_map_trialityFixedUnit, units_map_trialityFixedUnit, map_pow,
    pow_succ, pow_two]

theorem reps_conj_trialityTorusHom (hσ3 : σ ^ 3 = 1) (a : Kˣ)
    (b : (trialityFixedField K σ.toRingHom)ˣ) :
    trialityOuterRep K * trialityTorusHom σ (a, b) * (trialityOuterRep K)⁻¹ =
        trialityTorusHom σ (a⁻¹ * trialityFixedUnit K σ b, b) ∧
      trialityMiddleRep K * trialityTorusHom σ (a, b) * (trialityMiddleRep K)⁻¹ =
        trialityTorusHom σ (a, trialityNorm σ hσ3 a * b⁻¹) := by
  obtain ⟨-, -, -, -, -, hoo, hmm, hom, hmo⟩ :=
    triality_all_characteristic_faithful_torus_coordinates K σ hσ3
  have hsplit : ∀ (x : Kˣ) (y : (trialityFixedField K σ.toRingHom)ˣ),
      trialityTorusHom σ (x, y) = trialityOuterTorus K σ x * trialityMiddleTorus K σ y :=
    fun _ _ => rfl
  have hconj : ∀ (n u v : ModGL TwistTag.D4.tag K), n * (u * v) * n⁻¹ =
      (n * u * n⁻¹) * (n * v * n⁻¹) := fun n u v => by group
  constructor
  · rw [hsplit, hconj, hoo, hom, ← trialityTorusHom_one_right, ← trialityTorusHom_one_right,
      ← trialityTorusHom_one_left, ← map_mul, ← map_mul]
    congr 1
    simp only [Prod.mk_mul_mk, one_mul, mul_one]
  · rw [hsplit, hconj, hmo, hmm, ← trialityTorusHom_one_right, ← trialityTorusHom_one_left,
      ← trialityTorusHom_one_left, ← map_mul, ← map_mul]
    congr 1
    simp only [Prod.mk_mul_mk, one_mul, mul_one]

theorem rotT_conj (hσ3 : σ ^ 3 = 1) (a : Kˣ) (b : (trialityFixedField K σ.toRingHom)ˣ) :
    rotT K * trialityTorusHom σ (a, b) * (rotT K)⁻¹ =
      trialityTorusHom σ (a * trialityFixedUnit K σ ((trialityNorm σ hσ3 a)⁻¹ * b),
        (trialityNorm σ hσ3 a)⁻¹ * b) := by
  have hg : ∀ (x : Kˣ) (y : (trialityFixedField K σ.toRingHom)ˣ),
      (trialityMiddleRep K * trialityOuterRep K) * trialityTorusHom σ (x, y) *
          (trialityMiddleRep K * trialityOuterRep K)⁻¹ =
        trialityTorusHom σ (x⁻¹ * trialityFixedUnit K σ y,
          (trialityNorm σ hσ3 x)⁻¹ * y ^ 2) := by
    intro x y
    have e : (trialityMiddleRep K * trialityOuterRep K) * trialityTorusHom σ (x, y) *
        (trialityMiddleRep K * trialityOuterRep K)⁻¹ = trialityMiddleRep K *
          (trialityOuterRep K * trialityTorusHom σ (x, y) * (trialityOuterRep K)⁻¹) *
            (trialityMiddleRep K)⁻¹ := by group
    rw [e, (reps_conj_trialityTorusHom hσ3 x y).1, (reps_conj_trialityTorusHom hσ3 _ y).2]
    congr 2
    rw [map_mul, map_inv, trialityNorm_fixedUnit]
    group
  have e : rotT K * trialityTorusHom σ (a, b) * (rotT K)⁻¹ =
      (trialityMiddleRep K * trialityOuterRep K) *
        ((trialityMiddleRep K * trialityOuterRep K) * trialityTorusHom σ (a, b) *
          (trialityMiddleRep K * trialityOuterRep K)⁻¹) *
        (trialityMiddleRep K * trialityOuterRep K)⁻¹ := by
    rw [rotT, pow_two]
    group
  rw [e, hg, hg]
  have hinj : Function.Injective (trialityFixedUnit K σ) :=
    Units.map_injective (f := (trialityFixedField K σ.toRingHom).subtype.toMonoidHom)
      Subtype.val_injective
  congr 1
  refine Prod.ext ?_ ?_
  · simp only [map_mul, map_inv, map_pow]
    refine Units.ext ?_
    simp only [Units.val_mul, Units.val_inv_eq_inv_val, Units.val_pow_eq_pow_val]
    have h0 : ((trialityFixedUnit K σ b : Kˣ) : K) ≠ 0 := Units.ne_zero _
    have h0' : ((trialityFixedUnit K σ (trialityNorm σ hσ3 a) : Kˣ) : K) ≠ 0 := Units.ne_zero _
    have ha0 : (a : K) ≠ 0 := Units.ne_zero _
    field_simp
  · simp only [map_mul, map_inv, trialityNorm_fixedUnit]
    apply hinj
    simp only [map_mul, map_inv, map_pow]
    refine Units.ext ?_
    simp only [Units.val_mul, Units.val_inv_eq_inv_val, Units.val_pow_eq_pow_val]
    have h0 : ((trialityFixedUnit K σ b : Kˣ) : K) ≠ 0 := Units.ne_zero _
    have h0' : ((trialityFixedUnit K σ (trialityNorm σ hσ3 a) : Kˣ) : K) ≠ 0 := Units.ne_zero _
    field_simp

end CFSG.RankThree.PartTwo.Sec21.Item219LieProof
