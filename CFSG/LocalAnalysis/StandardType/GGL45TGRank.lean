module

public import CFSG.LocalAnalysis.StandardType.GGL45TGCount

public section

namespace CFSG.StandardType.GGL45TG

open CFSG CFSG.Assembly CFSG.LocalAnalysis.GLTheoremA Matrix
open GGL45TA (scalar_mem_center coe_scalar_mul)

namespace GSetting

variable {d : ℕ} {k : Type} [Field k] [Finite k] {K : Type} [Group K] {D : GData d k} {p q₀ : ℕ}
  {ψ : MulAut K} {E : Subgroup (MulAut K)}

theorem tau_fix (S : GSetting p q₀ d k D K ψ E) {c : k} (hc : c ^ p = 1) : S.τ c = c := by
  obtain ⟨ω, hω⟩ := TypeA.exists_isPrimitiveRoot S.hp S.dvd_card_sub_one
  exact LinModel.fieldAut_fixes_root S.hp hω (k := 1) (by rw [pow_one]; exact S.tau_pow) hc

theorem card_fixedLifts_le (S : GSetting p q₀ d k D K ψ E) {x₀ : GL (Fin d) k}
    (hx₀ : S.IsLift x₀) {ζ : kˣ} (hζ : IsPrimitiveRoot ζ p)
    (hτx₀ : Matrix.GeneralLinearGroup.map S.τ.toRingHom x₀ =
      Matrix.GeneralLinearGroup.scalar (Fin d) ζ * x₀) :
    Nat.card {x : GL (Fin d) k //
      S.IsLift x ∧ Matrix.GeneralLinearGroup.map S.τ.toRingHom x = x} ≤ p ^ (d / p) := by
  classical
  haveI : NeZero p := ⟨S.hp.ne_zero⟩
  set k₀ := FQ.fixF S.τ with hk₀
  set ι₀ : GL (Fin d) k₀ →* GL (Fin d) k := Matrix.GeneralLinearGroup.map k₀.subtype with hι₀
  have hι₀inj : Function.Injective ι₀ := FQ.glMap_subtype_injective S.τ
  set L₀ := {x : GL (Fin d) k // S.IsLift x ∧ Matrix.GeneralLinearGroup.map S.τ.toRingHom x = x}
  let L0 : Set (GL (Fin d) k₀) := {A | S.IsLift (ι₀ A)}
  have hdesc : ∀ x : L₀, ∃ A ∈ L0, ι₀ A = x.1 := fun x => by
    obtain ⟨A, hA⟩ := FQ.exists_descend S.τ x.1 x.2.2
    exact ⟨A, by simp only [L0, Set.mem_setOf_eq]; rw [hA]; exact x.2.1, hA⟩
  have hcomm : ∀ A ∈ L0, ∀ B ∈ L0, A * B = B * A := fun A hA B hB =>
    hι₀inj (by rw [map_mul, map_mul]; exact S.isLift_comm hA hB)
  have hpow : ∀ A ∈ L0, A ^ p = 1 := fun A hA => hι₀inj (by rw [map_pow, hA.2.1, map_one])
  obtain ⟨ω, hω⟩ := TypeA.exists_isPrimitiveRoot S.hp S.dvd_card_sub_one
  let ω₀ : k₀ := ⟨ω, S.tau_fix hω.pow_eq_one⟩
  have hω₀ : IsPrimitiveRoot ω₀ p := by
    refine ⟨Subtype.ext (by simp [ω₀, hω.pow_eq_one]), fun l hl => hω.dvd_of_pow_eq_one l ?_⟩
    have := congrArg Subtype.val hl
    simpa [ω₀] using this
  haveI : Finite L0 := Set.toFinite L0
  obtain ⟨P, hP⟩ := TypeA.PGLTor.exists_conj_diagonal hω₀ L0 hcomm hpow
  set P' : GL (Fin d) k := ι₀ P with hP'
  have hP'fix : Matrix.GeneralLinearGroup.map S.τ.toRingHom P' = P' := FQ.glMap_subtype_fixed S.τ P
  let D : L₀ → Fin d → k := fun x i =>
    ((P' * x.1 * P'⁻¹ : GL (Fin d) k) : Matrix (Fin d) (Fin d) k) i i
  have hdiag : ∀ x : L₀, ((P' * x.1 * P'⁻¹ : GL (Fin d) k) : Matrix (Fin d) (Fin d) k) =
      diagonal (D x) := by
    intro x
    obtain ⟨A, hA, hAx⟩ := hdesc x
    ext i j
    by_cases hij : i = j
    · subst hij; rw [diagonal_apply_eq]
    · rw [diagonal_apply_ne _ hij, ← hAx, hP', ← map_inv, ← map_mul, ← map_mul]
      change k₀.subtype ((P * A * P⁻¹ : GL (Fin d) k₀) i j) = 0
      rw [show ((P * A * P⁻¹ : GL (Fin d) k₀) : Matrix (Fin d) (Fin d) k₀) i j = 0 from by
        rw [Units.val_mul, Units.val_mul]; exact hP A hA i j hij, map_zero]
  set Mg : GL (Fin d) k := P' * x₀ * P'⁻¹ with hMg
  set M : Matrix (Fin d) (Fin d) k := (Mg : Matrix (Fin d) (Fin d) k) with hM
  let w : Fin d → L₀ → k := fun i x => D x i
  have hblock : TypeA.PGLTor.IsBlockDiag w M := by
    intro i j hij
    obtain ⟨x, hx⟩ : ∃ x, D x i ≠ D x j := by
      by_contra h
      push Not at h
      exact hij (funext h)
    have hcom : M * diagonal (D x) = diagonal (D x) * M := by
      rw [← hdiag x, hM, ← Units.val_mul, ← Units.val_mul]
      congr 1
      rw [hMg]
      have hc : x₀ * x.1 = x.1 * x₀ := S.isLift_comm hx₀ x.2.1
      calc P' * x₀ * P'⁻¹ * (P' * x.1 * P'⁻¹) = P' * (x₀ * x.1) * P'⁻¹ := by group
        _ = P' * (x.1 * x₀) * P'⁻¹ := by rw [hc]
        _ = P' * x.1 * P'⁻¹ * (P' * x₀ * P'⁻¹) := by group
    exact TypeA.PGLTor.isBlockDiag_of_commute_diagonal hcom i j hx
  have hτM : M.map S.τ = (ζ : k) • M := by
    have h1 : Matrix.GeneralLinearGroup.map S.τ.toRingHom Mg =
        Matrix.GeneralLinearGroup.scalar (Fin d) ζ * Mg := by
      rw [hMg, map_mul, map_mul, map_inv, hP'fix, hτx₀]
      have hcen := Subgroup.mem_center_iff.mp (scalar_mem_center (d := d) (k := k) ⟨ζ, rfl⟩)
      calc P' * (Matrix.GeneralLinearGroup.scalar (Fin d) ζ * x₀) * P'⁻¹
          = P' * Matrix.GeneralLinearGroup.scalar (Fin d) ζ * x₀ * P'⁻¹ := by group
        _ = Matrix.GeneralLinearGroup.scalar (Fin d) ζ * P' * x₀ * P'⁻¹ := by rw [hcen P']
        _ = Matrix.GeneralLinearGroup.scalar (Fin d) ζ * (P' * x₀ * P'⁻¹) := by group
    have h2 := congrArg (fun g : GL (Fin d) k => (g : Matrix (Fin d) (Fin d) k)) h1
    simp only [YS09Field.coe_glMap, coe_scalar_mul] at h2
    exact h2
  have hMp : M ^ p = 1 := by
    rw [hM, ← Units.val_pow_eq_pow_val, hMg, conj_pow, hx₀.2.1, mul_one, mul_inv_cancel,
      Units.val_one]
  have hdvd : ∀ b : L₀ → k, (∃ i, w i = b) → p ∣ Fintype.card {i // w i = b} := by
    intro b _
    set B := M.toSquareBlock w b with hB
    have hBp : B ^ p = 1 := by
      rw [hB, ← TypeA.PGLTor.toSquareBlock_pow_of_isBlockDiag hblock, hMp,
        TypeA.PGLTor.toSquareBlock_one]
    have hBτ : B.map S.τ = (ζ : k) • B := by
      ext ⟨i, hi⟩ ⟨j, hj⟩
      have := congrFun (congrFun hτM i) j
      simp only [Matrix.map_apply, Matrix.smul_apply] at this
      simp only [hB, Matrix.toSquareBlock_def, Matrix.map_apply, Matrix.of_apply,
        Matrix.smul_apply]
      exact this
    have hdetp : B.det ^ p = 1 := by rw [← det_pow, hBp, det_one]
    have hdet0 : B.det ≠ 0 := fun h0 => by
      rw [h0, zero_pow S.hp.ne_zero] at hdetp
      exact zero_ne_one hdetp
    have hdetτ : S.τ B.det = B.det := S.tau_fix hdetp
    have h1 : S.τ B.det = (ζ : k) ^ Fintype.card {i // w i = b} * B.det := by
      rw [RingEquiv.map_det, RingEquiv.mapMatrix_apply, hBτ, det_smul]
    rw [hdetτ] at h1
    have hζn : (ζ : k) ^ Fintype.card {i // w i = b} = 1 := by
      have := mul_right_cancel₀ hdet0 (h1.symm.trans (one_mul _).symm)
      exact this
    have hζn' : ζ ^ Fintype.card {i // w i = b} = 1 :=
      Units.ext (by rw [Units.val_pow_eq_pow_val, hζn, Units.val_one])
    exact (hζ.pow_eq_one_iff_dvd _).mp hζn'
  set T := Finset.univ.image w with hT
  have hTcard : T.card * p ≤ d := by
    have hsum := Finset.card_eq_sum_card_image w (Finset.univ : Finset (Fin d))
    rw [Finset.card_univ, Fintype.card_fin] at hsum
    rw [hsum, ← smul_eq_mul, ← Finset.sum_const]
    refine Finset.sum_le_sum fun b hb => ?_
    obtain ⟨i, -, hi⟩ := Finset.mem_image.mp hb
    have h1 := hdvd b ⟨i, hi⟩
    have h2 : Fintype.card {j // w j = b} = (Finset.univ.filter (fun a => w a = b)).card :=
      Fintype.card_subtype _
    have hpos : 0 < (Finset.univ.filter (fun a => w a = b)).card :=
      Finset.card_pos.mpr ⟨i, by simp [hi]⟩
    rw [h2] at h1
    exact Nat.le_of_dvd hpos h1
  have hTle : T.card ≤ d / p := (Nat.le_div_iff_mul_le S.hp.pos).mpr hTcard
  have hrep : ∀ b : T, ∃ i, w i = b := fun b => by
    obtain ⟨i, -, hi⟩ := Finset.mem_image.mp b.2
    exact ⟨i, hi⟩
  choose rep hrep using hrep
  have hroot : ∀ (x : L₀) (i : Fin d), D x i ^ p = 1 := by
    intro x i
    have h1 : (P' * x.1 * P'⁻¹) ^ p = 1 := by rw [conj_pow, x.2.1.2.1, mul_one, mul_inv_cancel]
    have h2 := congrArg (fun g : GL (Fin d) k => (g : Matrix (Fin d) (Fin d) k) i i) h1
    simp only [Units.val_pow_eq_pow_val, hdiag x, diagonal_pow, diagonal_apply_eq,
      Units.val_one, one_apply_eq] at h2
    exact h2
  have hne : ∀ (x : L₀) (i : Fin d), D x i ≠ 0 := fun x i h0 => by
    have := hroot x i
    rw [h0, zero_pow S.hp.ne_zero] at this
    exact zero_ne_one this
  let F : L₀ → T → rootsOfUnity p k := fun x b =>
    ⟨Units.mk0 (D x (rep b)) (hne x (rep b)), by
      rw [mem_rootsOfUnity]
      exact Units.ext (by rw [Units.val_pow_eq_pow_val, Units.val_mk0, hroot, Units.val_one])⟩
  have hF : Function.Injective F := by
    intro x y hxy
    have hD : D x = D y := by
      funext i
      have hmem : w i ∈ T := Finset.mem_image_of_mem w (Finset.mem_univ i)
      have h1 := congrArg (fun f => ((f ⟨w i, hmem⟩ : rootsOfUnity p k) : kˣ)) hxy
      simp only [F, Units.mk0_inj] at h1
      have hx : D x i = D x (rep ⟨w i, hmem⟩) := by
        change w i x = w (rep ⟨w i, hmem⟩) x
        rw [hrep]
      have hy : D y i = D y (rep ⟨w i, hmem⟩) := by
        change w i y = w (rep ⟨w i, hmem⟩) y
        rw [hrep]
      rw [hx, hy, h1]
    have h1 : P' * x.1 * P'⁻¹ = P' * y.1 * P'⁻¹ := Units.ext (by rw [hdiag, hdiag, hD])
    exact Subtype.ext (by simpa using h1)
  calc Nat.card L₀ ≤ Nat.card (T → rootsOfUnity p k) := Nat.card_le_card_of_injective F hF
    _ = Nat.card (rootsOfUnity p k) ^ Nat.card T := Nat.card_fun
    _ ≤ p ^ Nat.card T := Nat.pow_le_pow_left (card_rootsOfUnity k p) _
    _ = p ^ T.card := by rw [Nat.card_eq_fintype_card, Fintype.card_coe]
    _ ≤ p ^ (d / p) := Nat.pow_le_pow_right S.hp.pos hTle

end GSetting

end CFSG.StandardType.GGL45TG
