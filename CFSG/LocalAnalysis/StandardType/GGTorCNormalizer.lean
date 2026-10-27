module

public import CFSG.LocalAnalysis.StandardType.GGTorCPlane
public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentySpCoord

public section

namespace CFSG.StandardType.TorC

open CFSG.Open CFSG.StandardType.SpJoin CFSG.LocalAnalysis.ComponentInitial.SymplecticTorusWeyl
  Matrix Multiplicative

variable {F : Type} [Field F]

theorem add_inv_eq_trace_smul (A : SpecialLinearGroup (Fin 2) F) :
    (A : Matrix (Fin 2) (Fin 2) F) + ((A⁻¹ : SpecialLinearGroup (Fin 2) F) :
      Matrix (Fin 2) (Fin 2) F) = (A : Matrix (Fin 2) (Fin 2) F).trace • 1 := by
  rw [Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two, Matrix.trace_fin_two]
  ext a b
  fin_cases a <;> fin_cases b <;> simp
  ring

theorem trace_eq_of_mul_eq {A B : SpecialLinearGroup (Fin 2) F} {X : Matrix (Fin 2) (Fin 2) F}
    (hX : X ≠ 0) (h : X * (A : Matrix (Fin 2) (Fin 2) F) = (B : Matrix (Fin 2) (Fin 2) F) * X) :
    (A : Matrix (Fin 2) (Fin 2) F).trace = (B : Matrix (Fin 2) (Fin 2) F).trace := by
  have hAi : (A : Matrix (Fin 2) (Fin 2) F) * ((A⁻¹ : SpecialLinearGroup (Fin 2) F) :
      Matrix (Fin 2) (Fin 2) F) = 1 := by
    rw [← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel, Matrix.SpecialLinearGroup.coe_one]
  have hBi : ((B⁻¹ : SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) *
      (B : Matrix (Fin 2) (Fin 2) F) = 1 := by
    rw [← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel, Matrix.SpecialLinearGroup.coe_one]
  have h' : X * ((A⁻¹ : SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) =
      ((B⁻¹ : SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) * X := by
    calc X * ((A⁻¹ : SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F)
        = ((B⁻¹ : SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) *
            (B : Matrix (Fin 2) (Fin 2) F) * X *
            ((A⁻¹ : SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) := by
          rw [hBi, Matrix.one_mul]
      _ = ((B⁻¹ : SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) *
            (X * (A : Matrix (Fin 2) (Fin 2) F)) *
            ((A⁻¹ : SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) := by
          rw [h, Matrix.mul_assoc _ (B : Matrix (Fin 2) (Fin 2) F) X]
      _ = ((B⁻¹ : SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) * X := by
          rw [Matrix.mul_assoc, Matrix.mul_assoc, hAi, Matrix.mul_one]
  have h2 : (A : Matrix (Fin 2) (Fin 2) F).trace • X =
      (B : Matrix (Fin 2) (Fin 2) F).trace • X := by
    calc (A : Matrix (Fin 2) (Fin 2) F).trace • X
        = X * ((A : Matrix (Fin 2) (Fin 2) F).trace • 1) := by rw [Matrix.mul_smul, Matrix.mul_one]
      _ = X * ((A : Matrix (Fin 2) (Fin 2) F) + ((A⁻¹ : SpecialLinearGroup (Fin 2) F) :
            Matrix (Fin 2) (Fin 2) F)) := by rw [add_inv_eq_trace_smul]
      _ = ((B : Matrix (Fin 2) (Fin 2) F) + ((B⁻¹ : SpecialLinearGroup (Fin 2) F) :
            Matrix (Fin 2) (Fin 2) F)) * X := by rw [Matrix.mul_add, h, h', Matrix.add_mul]
      _ = (B : Matrix (Fin 2) (Fin 2) F).trace • X := by
          rw [add_inv_eq_trace_smul, Matrix.smul_mul, Matrix.one_mul]
  have h3 : ((A : Matrix (Fin 2) (Fin 2) F).trace -
      (B : Matrix (Fin 2) (Fin 2) F).trace) • X = 0 := by
    rw [sub_smul, h2, sub_self]
  rcases smul_eq_zero.mp h3 with h4 | h4
  · exact sub_eq_zero.mp h4
  · exact absurd h4 hX

theorem det_sub_one_eq_trace [CharP F 2] (C : SpecialLinearGroup (Fin 2) F) :
    ((C : Matrix (Fin 2) (Fin 2) F) - 1).det = (C : Matrix (Fin 2) (Fin 2) F).trace := by
  have hC := Matrix.SpecialLinearGroup.det_coe C
  rw [Matrix.det_fin_two] at hC
  rw [Matrix.det_fin_two, Matrix.trace_fin_two]
  simp only [Matrix.sub_apply, Matrix.one_apply_eq,
    Matrix.one_apply_ne (by decide : (0 : Fin 2) ≠ 1),
    Matrix.one_apply_ne (by decide : (1 : Fin 2) ≠ 0), sub_zero]
  have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
  linear_combination hC + h2 * (1 - (C : Matrix (Fin 2) (Fin 2) F) 0 0 -
    (C : Matrix (Fin 2) (Fin 2) F) 1 1)

theorem eq_or_eq_inv_of_trace_eq [CharP F 2] {p : ℕ} (hp : Odd p)
    {A B : SpecialLinearGroup (Fin 2) F} (hAB : A * B = B * A) (hp1 : (A⁻¹ * B) ^ p = 1)
    (htr : (A : Matrix (Fin 2) (Fin 2) F).trace = (B : Matrix (Fin 2) (Fin 2) F).trace) :
    B = A ∨ B = A⁻¹ := by
  by_cases hBA : B = A
  · exact Or.inl hBA
  right
  have hne : A⁻¹ * B ≠ 1 := fun h =>
    hBA (by rw [← mul_left_cancel_iff (a := A⁻¹), h, inv_mul_cancel])
  have htr' := trace_ne_zero_of_pow_eq_one hne hp hp1
  have hdet : ((B : Matrix (Fin 2) (Fin 2) F) - A).det ≠ 0 := by
    have e : (B : Matrix (Fin 2) (Fin 2) F) - A =
        (A : Matrix (Fin 2) (Fin 2) F) * (((A⁻¹ * B : SpecialLinearGroup (Fin 2) F) :
          Matrix (Fin 2) (Fin 2) F) - 1) := by
      rw [Matrix.mul_sub, Matrix.mul_one, ← Matrix.SpecialLinearGroup.coe_mul, ← mul_assoc,
        mul_inv_cancel, one_mul]
    rw [e, Matrix.det_mul, Matrix.SpecialLinearGroup.det_coe, one_mul, det_sub_one_eq_trace]
    exact htr'
  have hprod : ((B : Matrix (Fin 2) (Fin 2) F) - A) *
      ((B : Matrix (Fin 2) (Fin 2) F) - ((A⁻¹ : SpecialLinearGroup (Fin 2) F) :
        Matrix (Fin 2) (Fin 2) F)) = 0 := by
    have hAi : (A : Matrix (Fin 2) (Fin 2) F) * ((A⁻¹ : SpecialLinearGroup (Fin 2) F) :
        Matrix (Fin 2) (Fin 2) F) = 1 := by
      rw [← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel, Matrix.SpecialLinearGroup.coe_one]
    have hBi : (B : Matrix (Fin 2) (Fin 2) F) * ((B⁻¹ : SpecialLinearGroup (Fin 2) F) :
        Matrix (Fin 2) (Fin 2) F) = 1 := by
      rw [← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel, Matrix.SpecialLinearGroup.coe_one]
    have hAB' : (A : Matrix (Fin 2) (Fin 2) F) * B = (B : Matrix (Fin 2) (Fin 2) F) * A := by
      rw [← Matrix.SpecialLinearGroup.coe_mul, ← Matrix.SpecialLinearGroup.coe_mul, hAB]
    have hsumA := add_inv_eq_trace_smul A
    have hsumB := add_inv_eq_trace_smul B
    calc ((B : Matrix (Fin 2) (Fin 2) F) - A) *
          ((B : Matrix (Fin 2) (Fin 2) F) - ((A⁻¹ : SpecialLinearGroup (Fin 2) F) :
            Matrix (Fin 2) (Fin 2) F))
        = (B : Matrix (Fin 2) (Fin 2) F) * ((B : Matrix (Fin 2) (Fin 2) F) +
            ((B⁻¹ : SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) -
            ((A : Matrix (Fin 2) (Fin 2) F) + ((A⁻¹ : SpecialLinearGroup (Fin 2) F) :
              Matrix (Fin 2) (Fin 2) F))) := by
          rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_add,
            Matrix.mul_add, hBi, hAi, hAB']
          abel
      _ = 0 := by rw [hsumA, hsumB, htr, sub_self, Matrix.mul_zero]
  have hunit : IsUnit ((B : Matrix (Fin 2) (Fin 2) F) - A) :=
    (Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr hdet)
  have h0 : (B : Matrix (Fin 2) (Fin 2) F) - ((A⁻¹ : SpecialLinearGroup (Fin 2) F) :
      Matrix (Fin 2) (Fin 2) F) = 0 := by
    obtain ⟨u, hu⟩ := hunit
    have := congrArg (fun Y => (u⁻¹ : (Matrix (Fin 2) (Fin 2) F)ˣ).val * Y) hprod
    simp only [← hu, ← Matrix.mul_assoc, Units.inv_mul, Matrix.one_mul, Matrix.mul_zero] at this
    exact this
  exact Subtype.ext (sub_eq_zero.mp h0)

@[expose] def blk {n : ℕ} (G : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) (y x : Fin n) :
    Matrix (Fin 2) (Fin 2) F :=
  Matrix.of fun a b => G (WitSpNs.coord a y) (WitSpNs.coord b x)

theorem mul_planeMat_coord {n : ℕ} (G : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F)
    (M : Fin n → Matrix (Fin 2) (Fin 2) F) (r : Fin n ⊕ Fin n) (x : Fin n) (b : Fin 2) :
    (G * WitSpNs.planeMat M) r (WitSpNs.coord b x) =
      ∑ d : Fin 2, G r (WitSpNs.coord d x) * M x d b := by
  classical
  rw [Matrix.mul_apply, Fintype.sum_sum_type, Fin.sum_univ_two]
  simp only [WitSpNs.planeMat_apply, WitSpNs.plane_inl, WitSpNs.plane_inr, WitSpNs.plane_coord,
    WitSpNs.side_inl, WitSpNs.side_inr, WitSpNs.side_coord, mul_ite, mul_zero,
    Finset.sum_ite_eq', Finset.mem_univ, if_true]
  simp [WitSpNs.coord]

theorem planeMat_mul_coord {n : ℕ} (M : Fin n → Matrix (Fin 2) (Fin 2) F)
    (G : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) (y : Fin n) (a : Fin 2)
    (c : Fin n ⊕ Fin n) :
    (WitSpNs.planeMat M * G) (WitSpNs.coord a y) c =
      ∑ d : Fin 2, M y a d * G (WitSpNs.coord d y) c := by
  classical
  rw [Matrix.mul_apply, Fintype.sum_sum_type, Fin.sum_univ_two]
  simp only [WitSpNs.planeMat_apply, WitSpNs.plane_inl, WitSpNs.plane_inr, WitSpNs.plane_coord,
    WitSpNs.side_inl, WitSpNs.side_inr, WitSpNs.side_coord, ite_mul, zero_mul,
    Finset.sum_ite_eq, Finset.mem_univ, if_true]
  simp [WitSpNs.coord]

theorem blk_mul_eq {n : ℕ} {G : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F}
    {M M' : Fin n → Matrix (Fin 2) (Fin 2) F}
    (h : G * WitSpNs.planeMat M = WitSpNs.planeMat M' * G) (y x : Fin n) :
    blk G y x * M x = M' y * blk G y x := by
  ext a b
  rw [Matrix.mul_apply, Matrix.mul_apply]
  simp only [blk, Matrix.of_apply]
  rw [← mul_planeMat_coord, h, planeMat_mul_coord]

theorem exists_signedPerm_of_normalizes_gl [CharP F 2] {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {ζ : Multiplicative (ZMod p) →* SpecialLinearGroup (Fin 2) F} (hζ : Function.Injective ζ)
    {n : ℕ} (g : GL (Fin n ⊕ Fin n) F)
    (hg : ∀ f, ∃ f', g * (spPlaneTorus n ζ f : GL (Fin n ⊕ Fin n) F) * g⁻¹ =
      (spPlaneTorus n ζ f' : GL (Fin n ⊕ Fin n) F)) :
    ∃ (π : Equiv.Perm (Fin n)) (ε : Fin n → ZMod p), (∀ i, ε i = 1 ∨ ε i = -1) ∧
      ∀ f f', g * (spPlaneTorus n ζ f : GL (Fin n ⊕ Fin n) F) * g⁻¹ =
          (spPlaneTorus n ζ f' : GL (Fin n ⊕ Fin n) F) →
        ∀ i, Multiplicative.toAdd (f' (π i)) = ε i * Multiplicative.toAdd (f i) := by
  classical
  have : Fact (1 < p) := ⟨hp.one_lt⟩
  have hpodd : Odd p := hp.odd_of_ne_two hp2
  have hD := spPlaneTorus_injective hζ n
  choose σ hσ using hg
  have hσuniq : ∀ f f', g * (spPlaneTorus n ζ f : GL (Fin n ⊕ Fin n) F) * g⁻¹ =
      (spPlaneTorus n ζ f' : GL (Fin n ⊕ Fin n) F) → f' = σ f := by
    intro f f' h
    exact hD (Subtype.ext (h.symm.trans (hσ f)))
  have hσmul : ∀ f₁ f₂, σ (f₁ * f₂) = σ f₁ * σ f₂ := by
    intro f₁ f₂
    have h1 : g * (spPlaneTorus n ζ (f₁ * f₂) : GL (Fin n ⊕ Fin n) F) * g⁻¹ =
        (spPlaneTorus n ζ (σ (f₁ * f₂)) : GL (Fin n ⊕ Fin n) F) := hσ (f₁ * f₂)
    have h2 : g * (spPlaneTorus n ζ (f₁ * f₂) : GL (Fin n ⊕ Fin n) F) * g⁻¹ =
        (spPlaneTorus n ζ (σ f₁ * σ f₂) : GL (Fin n ⊕ Fin n) F) := by
      rw [map_mul, Subgroup.coe_mul]
      calc g * ((spPlaneTorus n ζ f₁ : GL (Fin n ⊕ Fin n) F) *
            (spPlaneTorus n ζ f₂ : GL (Fin n ⊕ Fin n) F)) * g⁻¹
          = (g * (spPlaneTorus n ζ f₁ : GL (Fin n ⊕ Fin n) F) * g⁻¹) *
              (g * (spPlaneTorus n ζ f₂ : GL (Fin n ⊕ Fin n) F) * g⁻¹) := by group
        _ = (spPlaneTorus n ζ (σ f₁) : GL (Fin n ⊕ Fin n) F) *
              (spPlaneTorus n ζ (σ f₂) : GL (Fin n ⊕ Fin n) F) := by rw [hσ f₁, hσ f₂]
        _ = (spPlaneTorus n ζ (σ f₁ * σ f₂) : GL (Fin n ⊕ Fin n) F) := by
              rw [map_mul, Subgroup.coe_mul]
    exact hD (Subtype.ext (h1.symm.trans h2))
  have hpow : ∀ y : Multiplicative (ZMod p), y ^ p = 1 := fun y => by
    obtain ⟨z, rfl⟩ : ∃ z : ZMod p, ofAdd z = y := ⟨toAdd y, rfl⟩
    rw [← ofAdd_nsmul, nsmul_eq_mul, ZMod.natCast_self, zero_mul, ofAdd_zero]
  set G : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F :=
    ((g : GL (Fin n ⊕ Fin n) F) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) with hG
  have hblk : ∀ f x y, blk G y x *
      ((ζ (f x) : SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) =
      ((ζ (σ f y) : SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) * blk G y x := by
    intro f x y
    have h1 : g * (spPlaneTorus n ζ f : GL (Fin n ⊕ Fin n) F) =
        (spPlaneTorus n ζ (σ f) : GL (Fin n ⊕ Fin n) F) * g := by
      rw [← hσ]
      group
    have h2 := congrArg (fun z : GL (Fin n ⊕ Fin n) F =>
      (z : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F)) h1
    simp only [Units.val_mul, coe_spPlaneTorus] at h2
    exact blk_mul_eq h2 y x
  have hcol : ∀ x : Fin n, ∃ y : Fin n, blk G y x ≠ 0 := by
    intro x
    by_contra hne
    push Not at hne
    have hz : ∀ r, G r (Sum.inl x) = 0 := fun r => by
      have h := congrFun (congrFun (hne (WitSpNs.plane r)) (WitSpNs.side r)) 0
      simp only [blk, Matrix.of_apply, Matrix.zero_apply] at h
      rcases r with i | i <;> simpa [WitSpNs.coord] using h
    have hinv : ((g⁻¹ : GL (Fin n ⊕ Fin n) F) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) *
        G = 1 := by
      rw [hG, ← Units.val_mul, inv_mul_cancel, Units.val_one]
    have h := congrFun (congrFun hinv (Sum.inl x)) (Sum.inl x)
    rw [Matrix.mul_apply, Matrix.one_apply_eq] at h
    simp [hz] at h
  choose j hj using hcol
  have hsign : ∀ f x, σ f (j x) = f x ∨ σ f (j x) = (f x)⁻¹ := by
    intro f x
    have htr := trace_eq_of_mul_eq (hj x) (hblk f x (j x))
    have hcomm : ζ (f x) * ζ (σ f (j x)) = ζ (σ f (j x)) * ζ (f x) := by
      rw [← map_mul, ← map_mul, mul_comm]
    have hp1 : ((ζ (f x))⁻¹ * ζ (σ f (j x))) ^ p = 1 := by
      rw [← map_inv, ← map_mul, ← map_pow, hpow, map_one]
    rcases eq_or_eq_inv_of_trace_eq hpodd hcomm hp1 htr with h | h
    · exact Or.inl (hζ h)
    · exact Or.inr (hζ (by rw [h]; exact (map_inv ζ (f x)).symm))
  have hsq : ∀ y : Multiplicative (ZMod p), y = y⁻¹ → y = 1 := by
    intro y hy
    have h1 : toAdd y = -toAdd y := by rw [← toAdd_inv, ← hy]
    have h2 := SpCoord.coord_eq_zero_of_eq_neg hp hp2 h1
    exact toAdd.injective (by rw [h2, toAdd_one])
  have hunif : ∀ x, (∀ f, σ f (j x) = f x) ∨ (∀ f, σ f (j x) = (f x)⁻¹) := by
    intro x
    by_contra hne
    push Not at hne
    obtain ⟨⟨a, ha⟩, ⟨b, hb⟩⟩ := hne
    have ha' := (hsign a x).resolve_left ha
    have hb' := (hsign b x).resolve_right hb
    rcases hsign (a * b) x with h | h
    · simp only [hσmul, Pi.mul_apply, ha', hb'] at h
      have h1 : a x = (a x)⁻¹ := (mul_right_cancel h).symm
      exact ha (by rw [ha', ← h1])
    · simp only [hσmul, Pi.mul_apply, ha', hb'] at h
      rw [_root_.mul_inv_rev, mul_comm ((b x)⁻¹)] at h
      have h1 : b x = (b x)⁻¹ := mul_left_cancel h
      have hb1 : b x = 1 := hsq _ h1
      exact hb (by rw [hb', hb1]; simp)
  have hjinj : Function.Injective j := by
    intro x x' hxx'
    by_contra hne
    set f : Fin n → Multiplicative (ZMod p) := Pi.mulSingle x (ofAdd (1 : ZMod p)) with hf
    have h1 : f x' = 1 := Pi.mulSingle_eq_of_ne (Ne.symm hne) _
    have h2 : f x ≠ 1 := by
      rw [hf, Pi.mulSingle_eq_same]
      intro h
      exact one_ne_zero (ofAdd_eq_one.mp h)
    have h3 : σ f (j x') = 1 := by
      rcases hsign f x' with h | h <;> rw [h, h1]
      exact inv_one
    rcases hsign f x with h | h
    · rw [hxx', h3] at h
      exact h2 h.symm
    · rw [hxx', h3] at h
      exact h2 (inv_eq_one.mp h.symm)
  let π : Equiv.Perm (Fin n) := Equiv.ofBijective j (Finite.injective_iff_bijective.mp hjinj)
  refine ⟨π, fun x => if ∀ f, σ f (j x) = f x then (1 : ZMod p) else -1, fun x => ?_, ?_⟩
  · by_cases h : ∀ f, σ f (j x) = f x
    · exact Or.inl (if_pos h)
    · exact Or.inr (if_neg h)
  · intro f f' hff' x
    rw [hσuniq f f' hff']
    change toAdd (σ f (j x)) =
      (if ∀ f, σ f (j x) = f x then (1 : ZMod p) else -1) * toAdd (f x)
    split_ifs with h
    · rw [one_mul, h f]
    · rw [((hunif x).resolve_left h) f, toAdd_inv, _root_.neg_one_mul]

theorem exists_signedPerm_of_normalizes [CharP F 2] {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {ζ : Multiplicative (ZMod p) →* SpecialLinearGroup (Fin 2) F} (hζ : Function.Injective ζ)
    {n : ℕ} (g : StatedSp n F)
    (hg : ∀ f, ∃ f', g * spPlaneTorus n ζ f * g⁻¹ = spPlaneTorus n ζ f') :
    ∃ (π : Equiv.Perm (Fin n)) (ε : Fin n → ZMod p), (∀ i, ε i = 1 ∨ ε i = -1) ∧
      ∀ f f', g * spPlaneTorus n ζ f * g⁻¹ = spPlaneTorus n ζ f' →
        ∀ i, toAdd (f' (π i)) = ε i * toAdd (f i) := by
  have hg' : ∀ f, ∃ f', (g : GL (Fin n ⊕ Fin n) F) *
      (spPlaneTorus n ζ f : GL (Fin n ⊕ Fin n) F) * (g : GL (Fin n ⊕ Fin n) F)⁻¹ =
      (spPlaneTorus n ζ f' : GL (Fin n ⊕ Fin n) F) := by
    intro f
    obtain ⟨f', h⟩ := hg f
    exact ⟨f', by
      simpa only [Subgroup.coe_mul, Subgroup.coe_inv] using
        congrArg (fun z : StatedSp n F => (z : GL (Fin n ⊕ Fin n) F)) h⟩
  obtain ⟨π, ε, hε, hπ⟩ := exists_signedPerm_of_normalizes_gl hp hp2 hζ
    (g : GL (Fin n ⊕ Fin n) F) hg'
  exact ⟨π, ε, hε, fun f f' hff' i => hπ f f' (by
    simpa only [Subgroup.coe_mul, Subgroup.coe_inv] using
      congrArg (fun z : StatedSp n F => (z : GL (Fin n ⊕ Fin n) F)) hff') i⟩

end CFSG.StandardType.TorC

end
