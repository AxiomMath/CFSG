module

public import CFSG.Quasithin.Background.SmithB45HM22Class
public import CFSG.Quasithin.Background.SmithB45HM22Chk

public section

namespace CFSG.Quasithin.HM22

open CFSG.CharacterTheory.SteinbergBY CFSG.CharacterTheory.SteinbergBY.FieldFour
  CFSG.Quasithin.HatM22 CFSG.Quasithin.B45Mat CFSG.Sporadic.Mathieu CFSG.Sporadic.Schreier
  Matrix

@[expose] noncomputable def tΓ (k : ℕ) : ↥hatM22Γ₀ := wordΓ (cosetW.getD k [])

@[expose] noncomputable def genb (b : Bool) : ↥hatM22Γ₀ := genΓ (gcode b)

theorem wordΓ_hword (b : Bool) (k : ℕ) :
    wordΓ (hword b k) = (tΓ (sigF b k))⁻¹ * genb b * tΓ k := by
  rw [hword, wordΓ_append, wordΓ_append, wordΓ_invW]
  simp only [wordΓ, mul_one]
  rfl

theorem tΓ_mul_hword (b : Bool) (k : ℕ) :
    tΓ (sigF b k) * wordΓ (hword b k) = genb b * tΓ k := by
  rw [wordΓ_hword]
  group

theorem isLetters_hword : ∀ b : Bool, ∀ k : Fin 22, IsLetters (hword b k) := by
  unfold IsLetters
  decide +kernel

theorem hword_act : ∀ b : Bool, ∀ k : Fin 22, evalCodes [m22gA, m22gB] (hword b k) 0 = 0 := by
  decide +kernel

theorem hword_mem (b : Bool) (k : Fin 22) : wordΓ (hword b k) ∈ hatH :=
  wordΓ_mem_hatH (isLetters_hword b k) (hword_act b k)

theorem sigF_lt : ∀ b : Bool, ∀ k : Fin 22, sigF b k < 22 := by decide

theorem tΓ_zero : tΓ 0 = 1 := rfl

theorem getD_flatMap_range {α : Type*} (d n : ℕ) (f : ℕ → List α) (hf : ∀ k, (f k).length = d)
    (dflt : α) {k c : ℕ} (hk : k < n) (hc : c < d) :
    ((List.range n).flatMap f).getD (d * k + c) dflt = (f k).getD c dflt := by
  induction n with
  | zero => omega
  | succ n ih =>
    rw [List.range_succ, List.flatMap_append, List.flatMap_singleton]
    have hlen : ((List.range n).flatMap f).length = d * n := by
      rw [List.length_flatMap]
      simp only [hf, List.map_const', List.length_range, List.sum_replicate, smul_eq_mul]
      ring
    by_cases hkn : k < n
    · rw [List.getD_append _ _ _ _ (by rw [hlen]; nlinarith), ih hkn]
    · have hkn' : k = n := by omega
      subst hkn'
      rw [List.getD_append_right _ _ _ _ (by rw [hlen]; exact Nat.le_add_right _ _), hlen,
        Nat.add_sub_cancel_left]

theorem col_indP (blk : List ℤ → PM) (d : ℕ) (b : Bool) {k c : ℕ} (hk : k < 22) (hc : c < d) :
    PM.col (indP blk d b) (d * k + c) =
      PV.shl ((PM.col (blk (hword b k)) c).trunc d) (d * sigF b k) := by
  unfold PM.col indP
  rw [getD_flatMap_range d 22 _ (fun k => by simp) _ hk hc,
    List.getD_eq_getElem _ _ (by simpa using hc), List.getElem_map, List.getElem_range]
  rfl

theorem length_indP (blk : List ℤ → PM) (d : ℕ) (b : Bool) :
    (indP blk d b).length = 22 * d := by
  unfold indP
  rw [List.length_flatMap]
  simp only [List.length_map, List.length_range, List.map_const', List.sum_replicate,
    smul_eq_mul]

theorem get_col_indP (blk : List ℤ → PM) (d : ℕ) (b : Bool) {k c : ℕ} (hk : k < 22)
    (hc : c < d) {k' c' : ℕ} (hc' : c' < d) :
    (PM.col (indP blk d b) (d * k + c)).get (d * k' + c') =
      if k' = sigF b k then (PM.col (blk (hword b k)) c).get c' else 0 := by
  rw [col_indP blk d b hk hc, PV.get_shl]
  split_ifs with h1 h2 h2
  · subst h2
    rw [Nat.add_sub_cancel_left, PV.get_trunc, ite_eq_left hc']
  · rw [PV.get_trunc, ite_eq_right]
    intro hlt2
    rcases Nat.lt_or_gt_of_ne h2 with hlt | hgt
    · have : d * (k' + 1) ≤ d * sigF b k := Nat.mul_le_mul_left _ hlt
      rw [Nat.mul_succ] at this
      omega
    · have : d * (sigF b k + 1) ≤ d * k' := Nat.mul_le_mul_left _ hgt
      rw [Nat.mul_succ] at this
      omega
  · exfalso
    apply h1
    rw [h2]
    exact Nat.le_add_right _ _
  · rfl

section Frob

variable {W : Type*} [AddCommGroup W] [Module FieldFour W]
  (ρ : Representation FieldFour ↥hatM22Γ₀ W) {d : ℕ}

@[expose] noncomputable def frobMap (ψ : (Fin d → FieldFour) →ₗ[FieldFour] W) :
    (Fin (22 * d) → FieldFour) →ₗ[FieldFour] W :=
  ∑ k : Fin 22, ∑ c : Fin d, (LinearMap.proj (finProdFinEquiv (k, c))).smulRight
    (ρ (tΓ k) (ψ (Pi.single c 1)))

theorem frobMap_apply (ψ : (Fin d → FieldFour) →ₗ[FieldFour] W) (x : Fin (22 * d) → FieldFour) :
    frobMap ρ ψ x = ∑ k : Fin 22, ∑ c : Fin d,
      x (finProdFinEquiv (k, c)) • ρ (tΓ k) (ψ (Pi.single c 1)) := by
  simp [frobMap, LinearMap.sum_apply]

theorem finProdFinEquiv_val (k : Fin 22) (c : Fin d) :
    ((finProdFinEquiv (k, c) : Fin (22 * d)) : ℕ) = d * k + c := by
  simp [finProdFinEquiv, Nat.add_comm]

theorem frobMap_block (ψ : (Fin d → FieldFour) →ₗ[FieldFour] W) {s : ℕ} (hs : s < 22)
    (y : Fin (22 * d) → FieldFour) (v : Fin d → FieldFour)
    (hy : ∀ (k : Fin 22) (c : Fin d), y (finProdFinEquiv (k, c)) =
      if (k : ℕ) = s then v c else 0) :
    frobMap ρ ψ y = ρ (tΓ s) (ψ v) := by
  rw [frobMap_apply, Finset.sum_eq_single (⟨s, hs⟩ : Fin 22)]
  · have hv : v = ∑ c : Fin d, v c • (Pi.single c 1 : Fin d → FieldFour) := by
      funext i
      simp [Finset.sum_apply, Pi.single_apply]
    conv_rhs => rw [hv, map_sum, map_sum]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [hy, ite_eq_left rfl, map_smul, map_smul]
  · intro k _ hk
    refine Finset.sum_eq_zero fun c _ => ?_
    have hk' : (k : ℕ) ≠ s := fun h => hk (Fin.ext h)
    rw [hy, ite_eq_right hk', zero_smul]
  · intro h
    exact absurd (Finset.mem_univ _) h

variable {X : ↥hatH →* Matrix (Fin d) (Fin d) FieldFour} {blk : List ℤ → PM}

theorem frobMap_gen (hblk : ∀ (w : List ℤ) (hw : wordΓ w ∈ hatH),
      PM.toMat d d (blk w) = X (Blk.hOf hw))
    (ψ : (Fin d → FieldFour) →ₗ[FieldFour] W)
    (hψ : ∀ (h : ↥hatH) (y : Fin d → FieldFour), ψ (X h *ᵥ y) = ρ h (ψ y)) (b : Bool)
    (x : Fin (22 * d) → FieldFour) :
    frobMap ρ ψ (PM.toMat (22 * d) (22 * d) (indP blk d b) *ᵥ x) =
      ρ (genb b) (frobMap ρ ψ x) := by
  have hlin : (frobMap ρ ψ).comp (Matrix.toLin' (PM.toMat (22 * d) (22 * d) (indP blk d b))) =
      (ρ (genb b)).comp (frobMap ρ ψ) := by
    apply LinearMap.pi_ext'
    intro j
    apply LinearMap.ext_ring
    obtain ⟨⟨k, c⟩, rfl⟩ := finProdFinEquiv.surjective j
    simp only [LinearMap.coe_comp, Function.comp_apply, LinearMap.coe_single,
      Matrix.toLin'_apply]
    rw [toMat_mulVec_single]
    have hσ := sigF_lt b k
    set h := Blk.hOf (hword_mem b k) with hh
    rw [frobMap_block ρ ψ hσ _ (fun c' => X h c' c)]
    · rw [show (fun c' => X h c' c) = X h *ᵥ Pi.single c 1 from
          (Matrix.mulVec_single_one _ _).symm, hψ, ← Module.End.mul_apply, ← map_mul]
      have e1 : tΓ (sigF b k) * (h : ↥hatM22Γ₀) = genb b * tΓ k := tΓ_mul_hword b k
      have e2 : ((tΓ (sigF b k) * (h : ↥hatM22Γ₀) : ↥hatM22Γ₀)) = tΓ (sigF b k) * h := rfl
      rw [show ρ (tΓ (sigF b k) * (h : ↥hatM22Γ₀)) = ρ (genb b * tΓ k) by rw [e1],
        map_mul, Module.End.mul_apply]
      congr 1
      have := frobMap_block ρ ψ k.isLt (Pi.single (finProdFinEquiv (k, c)) 1)
        (Pi.single c 1) (fun k' c' => by
          simp only [Pi.single_apply, (Equiv.injective finProdFinEquiv).eq_iff, Prod.mk.injEq]
          by_cases hk : k' = k
          · subst hk
            simp
          · have hk' : (k' : ℕ) ≠ k := fun e => hk (Fin.ext e)
            simp [hk, hk'])
      rw [this]
    · intro k' c'
      change (PM.col (indP blk d b) _).get _ = _
      rw [finProdFinEquiv_val, finProdFinEquiv_val,
        get_col_indP blk d b k.isLt c.isLt c'.isLt]
      split_ifs with hk'
      · rw [← hblk _ (hword_mem b k)]
        rfl
      · rfl
  have := congrArg (fun f => f x) hlin
  simpa using this

end Frob

end CFSG.Quasithin.HM22
