module

public import CFSG.LocalAnalysis.WeakClosure81.EightThirteenPGapKill

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.QuasithinUnique Subgroup
open CFSG.LocalAnalysis.UniquenessCase.UC22 (IsSp4)
open CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag
open CFSG.LocalAnalysis.ComponentInitial.SymplecticFour
open CFSG.LocalAnalysis.ComponentInitial.SymplecticTorusWeyl
  (statedSp_ext leviSp coe_leviSp torusHom coe_torusHom torusHom_mem_torus)
open CFSG.Assembly.LowTwoRank (StatedSp)
open Matrix

variable {F : Type} [Field F]

private noncomputable def wcgaps6Z (b c : F) : StatedSp 2 F :=
  tau (sym2_transpose b c 0)

private theorem wcgaps6Z_mem_unipotent (b c : F) : wcgaps6Z b c ∈ unipotent 2 F :=
  tau_mem_unipotent (sym2_transpose b c 0)

private theorem wcgaps6Z_zero : wcgaps6Z (0 : F) 0 = 1 := by
  apply statedSp_ext
  rw [wcgaps6Z, coe_tau]
  rw [show sym2 (0 : F) 0 0 = 0 from by
        ext i j
        fin_cases i <;> fin_cases j <;> simp [sym2],
    fromBlocks_one]
  rfl

private theorem wcgaps6_tau_zero : tau (sym2_transpose (0 : F) 0 0) = 1 :=
  wcgaps6Z_zero

private theorem wcgaps6Z_add (b c b' c' : F) :
    wcgaps6Z b c * wcgaps6Z b' c' = wcgaps6Z (b + b') (c + c') := by
  rw [wcgaps6Z, wcgaps6Z, wcgaps6Z, tau_mul_tau]
  refine tau_congr _ _ ?_
  ext i j
  fin_cases i <;> fin_cases j <;> simp [sym2, add_comm, add_left_comm]

private theorem wcgaps6Z_injective {b c b' c' : F} (h : wcgaps6Z b c = wcgaps6Z b' c') :
    b = b' ∧ c = c' := by
  have h' : sym2 b c 0 = sym2 b' c' 0 := by
    apply tau_injective (sym2_transpose b c 0) (sym2_transpose b' c' 0)
    show wcgaps6Z b c = wcgaps6Z b' c'
    exact h
  exact ⟨by simpa [sym2] using congrFun₂ h' 0 0,
    by simpa [sym2] using congrFun₂ h' 0 1⟩

private theorem wcgaps6Z_mem_center_iff [Finite F] [CharP F 2] (hF : Nat.card F = 4)
    {g : StatedSp 2 F} :
    g ∈ unipotent 2 F ⊓ centralizer ((unipotent 2 F : Subgroup (StatedSp 2 F)) :
        Set (StatedSp 2 F)) ↔ ∃ b c : F, g = wcgaps6Z b c := by
  have hcenter := (unique_symplectic_four_Sylow_center (K := F) 4 hF).2.2.2.2.2.2.2.1
  constructor
  · rintro ⟨hU, hC⟩
    have hmem : (⟨g, hU⟩ : unipotent 2 F) ∈ Subgroup.center (unipotent 2 F) := by
      rw [Subgroup.mem_center_iff]
      intro y
      exact Subtype.ext (Subgroup.mem_centralizer_iff.mp hC y y.2)
    obtain ⟨b, c, hbc⟩ := (hcenter ⟨g, hU⟩).mp hmem
    exact ⟨b, c, hbc⟩
  · rintro ⟨b, c, rfl⟩
    refine ⟨wcgaps6Z_mem_unipotent b c, Subgroup.mem_centralizer_iff.mpr ?_⟩
    intro y hy
    have hmem : (⟨wcgaps6Z b c, wcgaps6Z_mem_unipotent b c⟩ : unipotent 2 F) ∈
        Subgroup.center (unipotent 2 F) := (hcenter _).mpr ⟨b, c, rfl⟩
    exact congrArg Subtype.val (Subgroup.mem_center_iff.mp hmem ⟨y, hy⟩)

private theorem wcgaps6Z_mem_center [Finite F] [CharP F 2] (hF : Nat.card F = 4) (b c : F) :
    wcgaps6Z b c ∈ unipotent 2 F ⊓ centralizer ((unipotent 2 F : Subgroup (StatedSp 2 F)) :
      Set (StatedSp 2 F)) :=
  (wcgaps6Z_mem_center_iff hF).mpr ⟨b, c, rfl⟩

theorem wcgaps6_card_center [Finite F] [CharP F 2] (hF : Nat.card F = 4) :
    Nat.card ↥(unipotent 2 F ⊓ centralizer ((unipotent 2 F : Subgroup (StatedSp 2 F)) :
        Set (StatedSp 2 F))) = 16 := by
  have hbij : Function.Bijective (fun x : F × F =>
      (⟨wcgaps6Z x.1 x.2, wcgaps6Z_mem_center hF x.1 x.2⟩ :
        ↥(unipotent 2 F ⊓ centralizer ((unipotent 2 F : Subgroup (StatedSp 2 F)) :
          Set (StatedSp 2 F))))) := by
    refine ⟨?_, ?_⟩
    · rintro ⟨b, c⟩ ⟨b', c'⟩ h
      obtain ⟨hb, hc⟩ := wcgaps6Z_injective (congrArg Subtype.val h)
      exact Prod.ext hb hc
    · rintro ⟨g, hg⟩
      obtain ⟨b, c, rfl⟩ := (wcgaps6Z_mem_center_iff hF).mp hg
      exact ⟨(b, c), rfl⟩
  rw [← Nat.card_congr (Equiv.ofBijective _ hbij), Nat.card_prod, hF]

private theorem wcgaps6_leviSp_mul_tau_mul_inv (A : GL (Fin 2) F)
    {C : Matrix (Fin 2) (Fin 2) F} (hC : Cᵀ = C) :
    leviSp A * tau hC * (leviSp A)⁻¹ =
      tau (C := (A : Matrix (Fin 2) (Fin 2) F) * C * (A : Matrix (Fin 2) (Fin 2) F)ᵀ)
        (by rw [transpose_mul, transpose_mul, transpose_transpose, hC, Matrix.mul_assoc]) := by
  apply statedSp_ext
  have hA : (A : Matrix (Fin 2) (Fin 2) F) *
      ((A⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) = 1 := by
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  rw [← map_inv, Subgroup.coe_mul, Subgroup.coe_mul, Units.val_mul, Units.val_mul,
    coe_leviSp, coe_leviSp, coe_tau, coe_tau,
    fromBlocks_multiply, fromBlocks_multiply, inv_inv]
  simp only [Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add, Matrix.mul_one]
  rw [hA, ← transpose_mul, hA, transpose_one]

private theorem wcgaps6_torus_mul_Z_mul_inv (t : Fin 2 → Fˣ) (b c : F) :
    torusHom t * wcgaps6Z b c * (torusHom t)⁻¹ =
      wcgaps6Z ((t 0 : F) ^ 2 * b) ((t 0 : F) * (t 1 : F) * c) := by
  rw [show torusHom t = leviSp (TauCeti.diagGL t) from rfl, wcgaps6Z]
  rw [wcgaps6_leviSp_mul_tau_mul_inv]
  refine tau_congr _ _ ?_
  rw [TauCeti.diagGL_coe, diagonal_transpose]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [sym2] <;> ring

private theorem wcgaps6_lam_sq [CharP F 2] (a : F) : lam a * lam a = 1 := by
  rw [lam_mul, CharTwo.add_self_eq_zero, lam_zero]

private theorem wcgaps6_lam_mul_tau (a : F) {C : Matrix (Fin 2) (Fin 2) F} (hC : Cᵀ = C) :
    lam a * tau hC =
      tau (C := unitri a * C * (unitri a)ᵀ)
        (by rw [transpose_mul, transpose_mul, transpose_transpose, hC, Matrix.mul_assoc]) *
        lam a := by
  calc lam a * tau hC = lam a * tau hC * (lam a)⁻¹ * lam a := by group
    _ = tau (C := unitri a * C * (unitri a)ᵀ)
          (by rw [transpose_mul, transpose_mul, transpose_transpose, hC, Matrix.mul_assoc]) *
          lam a := by rw [lam_mul_tau_mul_inv]

private theorem wcgaps6_mul_tau_lam {C C' : Matrix (Fin 2) (Fin 2) F}
    (hC : Cᵀ = C) (hC' : C'ᵀ = C') (a a' : F) :
    (tau hC * lam a) * (tau hC' * lam a') =
      tau (C := C + unitri a * C' * (unitri a)ᵀ)
        (by rw [transpose_add, transpose_mul, transpose_mul, transpose_transpose, hC', hC,
          Matrix.mul_assoc]) * lam (a + a') := by
  have h1 : (tau hC * lam a) * (tau hC' * lam a') =
      (tau hC * (lam a * tau hC' * (lam a)⁻¹)) * (lam a * lam a') := by group
  rw [h1, lam_mul_tau_mul_inv, tau_mul_tau, lam_mul]

private theorem wcgaps6_inv_tau_lam [CharP F 2] {C : Matrix (Fin 2) (Fin 2) F}
    (hC : Cᵀ = C) (a : F) : (tau hC * lam a)⁻¹ = lam a * tau hC := by
  refine inv_eq_of_mul_eq_one_right ?_
  rw [show tau hC * lam a * (lam a * tau hC) =
      tau hC * (lam a * lam a) * tau hC by group, wcgaps6_lam_sq, mul_one]
  simpa [pow_two] using tau_sq hC

private theorem wcgaps6_comm_aux [CharP F 2] {A B : Matrix (Fin 2) (Fin 2) F}
    (hA : Aᵀ = A) (hB : Bᵀ = B) (α β : F) (hαβ : α = β) :
    (tau hA * lam α) * (tau hB * lam β)⁻¹ =
      tau (C := A + B) (by rw [transpose_add, hA, hB]) := by
  rw [hαβ, wcgaps6_inv_tau_lam]
  rw [show (tau hA * lam β) * (lam β * tau hB) =
      tau hA * (lam β * lam β) * tau hB by group, wcgaps6_lam_sq, mul_one]
  rw [tau_mul_tau]

private theorem wcgaps6_sym2_sum [CharP F 2] (a a' b c d b' c' d' : F) :
    (sym2 b c d + unitri a * sym2 b' c' d' * (unitri a)ᵀ) +
        (sym2 b' c' d' + unitri a' * sym2 b c d * (unitri a')ᵀ) =
      sym2 (a ^ 2 * d' + a' ^ 2 * d) (a * d' + a' * d) 0 := by
  have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
  rw [unitri_mul_sym2_mul_transpose, unitri_mul_sym2_mul_transpose]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [sym2] <;>
    first
      | linear_combination (b + b') * h2
      | linear_combination (c + c') * h2
      | linear_combination (d + d') * h2
      | ring

private theorem wcgaps6_comm [CharP F 2] (a a' b c d b' c' d' : F) :
    (tau (sym2_transpose b c d) * lam a) * (tau (sym2_transpose b' c' d') * lam a') *
      (tau (sym2_transpose b c d) * lam a)⁻¹ *
      (tau (sym2_transpose b' c' d') * lam a')⁻¹ =
      wcgaps6Z (a ^ 2 * d' + a' ^ 2 * d) (a * d' + a' * d) := by
  have hA : (sym2 b c d + unitri a * sym2 b' c' d' * (unitri a)ᵀ)ᵀ =
      sym2 b c d + unitri a * sym2 b' c' d' * (unitri a)ᵀ := by
    rw [transpose_add, transpose_mul, transpose_mul, transpose_transpose, sym2_transpose,
      sym2_transpose, Matrix.mul_assoc]
  have hB : (sym2 b' c' d' + unitri a' * sym2 b c d * (unitri a')ᵀ)ᵀ =
      sym2 b' c' d' + unitri a' * sym2 b c d * (unitri a')ᵀ := by
    rw [transpose_add, transpose_mul, transpose_mul, transpose_transpose, sym2_transpose,
      sym2_transpose, Matrix.mul_assoc]
  have hxy := wcgaps6_mul_tau_lam (C := sym2 b c d) (C' := sym2 b' c' d')
    (sym2_transpose b c d) (sym2_transpose b' c' d') a a'
  have hyx := wcgaps6_mul_tau_lam (C := sym2 b' c' d') (C' := sym2 b c d)
    (sym2_transpose b' c' d') (sym2_transpose b c d) a' a
  rw [show (tau (sym2_transpose b c d) * lam a) * (tau (sym2_transpose b' c' d') * lam a') *
        (tau (sym2_transpose b c d) * lam a)⁻¹ *
        (tau (sym2_transpose b' c' d') * lam a')⁻¹ =
      ((tau (sym2_transpose b c d) * lam a) * (tau (sym2_transpose b' c' d') * lam a')) *
        ((tau (sym2_transpose b' c' d') * lam a') *
          (tau (sym2_transpose b c d) * lam a))⁻¹ by group]
  rw [hxy, hyx]
  refine (wcgaps6_comm_aux hA hB (a + a') (a' + a) (add_comm a a')).trans ?_
  rw [wcgaps6Z]
  refine tau_congr _ _ ?_
  exact wcgaps6_sym2_sum a a' b c d b' c' d'

private theorem wcgaps6_comm' [CharP F 2] {C C' : Matrix (Fin 2) (Fin 2) F}
    (hC : Cᵀ = C) (hC' : C'ᵀ = C') (a a' : F) :
    (tau hC * lam a) * (tau hC' * lam a') * (tau hC * lam a)⁻¹ *
      (tau hC' * lam a')⁻¹ =
      wcgaps6Z (a ^ 2 * C' 1 1 + a' ^ 2 * C 1 1) (a * C' 1 1 + a' * C 1 1) := by
  rw [show tau hC = tau (sym2_transpose (C 0 0) (C 0 1) (C 1 1)) from
        tau_congr hC (sym2_transpose (C 0 0) (C 0 1) (C 1 1)) (eq_sym2 hC),
      show tau hC' = tau (sym2_transpose (C' 0 0) (C' 0 1) (C' 1 1)) from
        tau_congr hC' (sym2_transpose (C' 0 0) (C' 0 1) (C' 1 1)) (eq_sym2 hC')]
  exact wcgaps6_comm a a' (C 0 0) (C 0 1) (C 1 1) (C' 0 0) (C' 0 1) (C' 1 1)

private theorem wcgaps6_scale_mem [Finite F] [CharP F 2] (hF : Nat.card F = 4)
    (Z' : Subgroup (StatedSp 2 F))
    (hZinv : ∀ b ∈ normalizer (unipotent 2 F : Set (StatedSp 2 F)), ∀ z ∈ Z',
      b * z * b⁻¹ ∈ Z')
    {s t : F} (hst : wcgaps6Z s t ∈ Z') (ν₀ ν₁ : Fˣ) :
    wcgaps6Z ((ν₀ : F) * s) ((ν₁ : F) * t) ∈ Z' := by
  have hcard : Nat.card Fˣ = 3 := by rw [Nat.card_units, hF]
  have h3 : ν₀ ^ 3 = 1 := by
    have h := pow_card_eq_one' (x := ν₀)
    rw [hcard] at h
    exact h
  have hsq : (ν₀ ^ 2) ^ 2 = ν₀ := by
    rw [← pow_mul, show 2 * 2 = 3 + 1 by norm_num, pow_add, h3, one_mul, pow_one]
  let tt : Fin 2 → Fˣ := fun i => if i = 0 then ν₀ ^ 2 else (ν₀ ^ 2)⁻¹ * ν₁
  have h0 : tt 0 = ν₀ ^ 2 := by simp [tt]
  have h1 : tt 1 = (ν₀ ^ 2)⁻¹ * ν₁ := by simp [tt]
  have hmem : torusHom tt ∈
      normalizer (unipotent 2 F : Set (StatedSp 2 F)) := by
    rw [CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher.normalizer_unipotent]
    exact torus_le_borelSubgroup (torusHom_mem_torus tt)
  have hmemZ := hZinv _ hmem _ hst
  rw [wcgaps6_torus_mul_Z_mul_inv] at hmemZ
  rw [h0, h1] at hmemZ
  have hsqF : ((ν₀ ^ 2 : Fˣ) : F) ^ 2 = (ν₀ : F) := by
    rw [← Units.val_pow_eq_pow_val (a := ν₀ ^ 2) 2, hsq]
  have hmulF : ((ν₀ ^ 2 : Fˣ) : F) * (((ν₀ ^ 2)⁻¹ * ν₁ : Fˣ) : F) = (ν₁ : F) := by
    rw [← Units.val_mul]
    congr 1
    rw [← mul_assoc, mul_inv_cancel, one_mul]
  rw [hsqF, hmulF] at hmemZ
  exact hmemZ

private theorem wcgaps6_all_first [Finite F] [CharP F 2] (hF : Nat.card F = 4)
    (Z' : Subgroup (StatedSp 2 F))
    (hZinv : ∀ b ∈ normalizer (unipotent 2 F : Set (StatedSp 2 F)), ∀ z ∈ Z',
      b * z * b⁻¹ ∈ Z')
    {s t : F} (hst : wcgaps6Z s t ∈ Z') (hs : s ≠ 0) (b : F) :
    wcgaps6Z b 0 ∈ Z' := by
  classical
  have hcard : Nat.card Fˣ = 3 := by rw [Nat.card_units, hF]
  obtain ⟨ν, hν⟩ : ∃ ν : Fˣ, ν ≠ 1 := by
    haveI : Fintype F := Fintype.ofFinite F
    have h : 1 < Fintype.card Fˣ := by
      rw [← Nat.card_eq_fintype_card, hcard]
      norm_num
    obtain ⟨ν, hν⟩ := Fintype.exists_ne_of_one_lt_card h (1 : Fˣ)
    exact ⟨ν, hν⟩
  have hν1 : (ν : F) + 1 ≠ 0 := by
    intro h
    apply hν
    apply Units.ext
    have h' : (ν : F) = -1 := by
      rw [add_eq_zero_iff_eq_neg] at h
      exact h
    rw [h', CharTwo.neg_eq, Units.val_one]
  have hs0 : ((ν : F) + 1) * s ≠ 0 := mul_ne_zero hν1 hs
  have hprod : wcgaps6Z (((ν : F) + 1) * s) 0 ∈ Z' := by
    have h1 := wcgaps6_scale_mem hF Z' hZinv hst ν 1
    have h2 := wcgaps6_scale_mem hF Z' hZinv hst 1 1
    have hthis := mul_mem h1 h2
    rw [wcgaps6Z_add] at hthis
    simp only [Units.val_one, one_mul] at hthis
    rw [show (ν : F) * s + s = ((ν : F) + 1) * s by rw [add_mul, one_mul],
      CharTwo.add_self_eq_zero] at hthis
    exact hthis
  rcases eq_or_ne b 0 with rfl | hb
  · rw [wcgaps6Z_zero]
    exact Z'.one_mem
  · let u : Fˣ := Units.mk0 (b * (((ν : F) + 1) * s)⁻¹)
      (mul_ne_zero hb (inv_ne_zero hs0))
    have h := wcgaps6_scale_mem hF Z' hZinv hprod u 1
    have hu : (u : F) * (((ν : F) + 1) * s) = b := by
      show (b * (((ν : F) + 1) * s)⁻¹) * (((ν : F) + 1) * s) = b
      rw [mul_assoc, inv_mul_cancel₀ hs0, mul_one]
    rw [hu, Units.val_one, one_mul] at h
    exact h

private theorem wcgaps6_all_second [Finite F] [CharP F 2] (hF : Nat.card F = 4)
    (Z' : Subgroup (StatedSp 2 F))
    (hZinv : ∀ b ∈ normalizer (unipotent 2 F : Set (StatedSp 2 F)), ∀ z ∈ Z',
      b * z * b⁻¹ ∈ Z')
    {s t : F} (hst : wcgaps6Z s t ∈ Z') (ht : t ≠ 0) (c : F) :
    wcgaps6Z 0 c ∈ Z' := by
  classical
  have hcard : Nat.card Fˣ = 3 := by rw [Nat.card_units, hF]
  obtain ⟨ν, hν⟩ : ∃ ν : Fˣ, ν ≠ 1 := by
    haveI : Fintype F := Fintype.ofFinite F
    have h : 1 < Fintype.card Fˣ := by
      rw [← Nat.card_eq_fintype_card, hcard]
      norm_num
    obtain ⟨ν, hν⟩ := Fintype.exists_ne_of_one_lt_card h (1 : Fˣ)
    exact ⟨ν, hν⟩
  have hν1 : (ν : F) + 1 ≠ 0 := by
    intro h
    apply hν
    apply Units.ext
    have h' : (ν : F) = -1 := by
      rw [add_eq_zero_iff_eq_neg] at h
      exact h
    rw [h', CharTwo.neg_eq, Units.val_one]
  have ht0 : ((ν : F) + 1) * t ≠ 0 := mul_ne_zero hν1 ht
  have hprod : wcgaps6Z 0 (((ν : F) + 1) * t) ∈ Z' := by
    have h1 := wcgaps6_scale_mem hF Z' hZinv hst 1 ν
    have h2 := wcgaps6_scale_mem hF Z' hZinv hst 1 1
    have hthis := mul_mem h1 h2
    rw [wcgaps6Z_add] at hthis
    simp only [Units.val_one, one_mul] at hthis
    rw [show s + s = 0 from CharTwo.add_self_eq_zero s,
      show (ν : F) * t + t = ((ν : F) + 1) * t by rw [add_mul, one_mul]] at hthis
    exact hthis
  rcases eq_or_ne c 0 with rfl | hc
  · rw [wcgaps6Z_zero]
    exact Z'.one_mem
  · let u : Fˣ := Units.mk0 (c * (((ν : F) + 1) * t)⁻¹)
      (mul_ne_zero hc (inv_ne_zero ht0))
    have h := wcgaps6_scale_mem hF Z' hZinv hprod 1 u
    have hu : (u : F) * (((ν : F) + 1) * t) = c := by
      show (c * (((ν : F) + 1) * t)⁻¹) * (((ν : F) + 1) * t) = c
      rw [mul_assoc, inv_mul_cancel₀ ht0, mul_one]
    rw [hu, Units.val_one, one_mul] at h
    exact h

theorem wcgaps6_centerIrred [Finite F] [CharP F 2] (hF : Nat.card F = 4) :
    CenterIrred (unipotent 2 F : Subgroup (StatedSp 2 F)) := by
  intro x hxU hxc Z' hZle hZinv hZcomm
  obtain ⟨C, hC, a, rfl⟩ := mem_unipotent_iff.mp hxU
  have hnot : ¬(a = 0 ∧ C 1 1 = 0) := by
    rintro ⟨ha, hd⟩
    apply hxc
    have hCeq : C = sym2 (C 0 0) (C 0 1) 0 := by
      have h1 := eq_sym2 hC
      rw [hd] at h1
      exact h1
    have htau : tau hC = wcgaps6Z (C 0 0) (C 0 1) :=
      tau_congr hC (sym2_transpose (C 0 0) (C 0 1) 0) hCeq
    rw [ha, lam_zero, mul_one, htau]
    exact (wcgaps6Z_mem_center hF (C 0 0) (C 0 1)).2
  have hac : a ≠ 0 ∨ C 1 1 ≠ 0 := by
    rcases eq_or_ne a 0 with ha | ha
    · right; intro hd; exact hnot ⟨ha, hd⟩
    · left; exact ha
  have hex : ∃ s t : F, s ≠ 0 ∧ t ≠ 0 ∧ wcgaps6Z s t ∈ Z' := by
    rcases hac with ha | hd
    · refine ⟨a ^ 2, a, pow_ne_zero 2 ha, ha, ?_⟩
      have hcomm := hZcomm (tau (sym2_transpose (0 : F) 0 1)) (tau_mem_unipotent _)
      rw [show tau (sym2_transpose (0 : F) 0 1) =
          tau (sym2_transpose (0 : F) 0 1) * lam 0 by rw [lam_zero, mul_one]] at hcomm
      rw [wcgaps6_comm' hC (sym2_transpose (0 : F) 0 1) a 0] at hcomm
      simpa [sym2] using hcomm
    · refine ⟨C 1 1, C 1 1, hd, hd, ?_⟩
      have hcomm := hZcomm (lam (1 : F)) (lam_mem_unipotent 1)
      rw [show lam (1 : F) = tau (sym2_transpose (0 : F) 0 0) * lam 1 by
        rw [wcgaps6_tau_zero, one_mul]] at hcomm
      rw [wcgaps6_comm' hC (sym2_transpose (0 : F) 0 0) a 1] at hcomm
      simpa [sym2] using hcomm
  obtain ⟨s, t, hs, ht, hst⟩ := hex
  apply le_antisymm hZle
  intro z hz
  obtain ⟨b, c, rfl⟩ := (wcgaps6Z_mem_center_iff hF).mp hz
  have hfirst := wcgaps6_all_first hF Z' hZinv hst hs
  have hsecond := wcgaps6_all_second hF Z' hZinv hst ht
  have hsplit : wcgaps6Z b c = wcgaps6Z b 0 * wcgaps6Z 0 c := by
    rw [wcgaps6Z_add, add_zero, zero_add]
  rw [hsplit]
  exact mul_mem (hfirst b) (hsecond c)

theorem wcgaps6_card_inf_centralizer_map {M M' : Type} [Group M] [Group M']
    (e : M ≃* M') (S : Subgroup M) :
    Nat.card ↥((S.map e.toMonoidHom) ⊓
        centralizer (((S.map e.toMonoidHom : Subgroup M')) : Set M')) =
      Nat.card ↥(S ⊓ centralizer (S : Set M)) := by
  have hmap : (S ⊓ centralizer (S : Set M)).map e.toMonoidHom =
      S.map e.toMonoidHom ⊓
        centralizer (((S.map e.toMonoidHom : Subgroup M')) : Set M') := by
    apply le_antisymm
    · rw [Subgroup.map_inf S (centralizer (S : Set M)) e.toMonoidHom e.injective]
      exact inf_le_inf_left _
        (Subgroup.map_centralizer_le_centralizer_image (S : Set M) e.toMonoidHom)
    · rintro x ⟨hxS, hxC⟩
      obtain ⟨s, hs, rfl⟩ := Subgroup.mem_map.mp hxS
      refine Subgroup.mem_map.mpr ⟨s, ⟨hs, ?_⟩, rfl⟩
      refine Subgroup.mem_centralizer_iff.mpr ?_
      intro u hu
      apply e.injective
      rw [map_mul, map_mul]
      exact (Subgroup.mem_centralizer_iff.mp hxC) (e.toMonoidHom u)
        (Subgroup.mem_map.mpr ⟨u, hu, rfl⟩)
  rw [← hmap, Subgroup.card_map_of_injective e.injective]

end CFSG.LocalAnalysis.WeakClosure81

end
