module

public import CFSG.Quasithin.Background.SmithB45L2Row
public import CFSG.Quasithin.Vol2.Ch9H11Norm

public section

noncomputable section

namespace CFSG.Quasithin.H13.H11M

open CFSG.Quasithin (fixV mem_fixV rk rkIdx frobPow hermSub)
open CFSG.Quasithin.JonesParshall (hermA mem_hermA sig sig_apply frobPow_eq_map hermA_apply
  frobPow_mul frobPow_transpose frobPow_frobPow twist_mem)
open CFSG.Quasithin.H13.H11P (Mat uu dd ww ul coe_uu coe_dd coe_ww coe_ul coe_inv_mul
  coe_mul_inv eq_one_of_sq_eq_one exists_conj_of_hom)
open CFSG.RankThree.PartOne.KCRootAxis (SL₂ slFieldAut slFieldAut_apply)
open scoped Matrix

variable {F : Type} [Field F] [CharP F 2] {a : ℕ}

abbrev VH (a : ℕ) (F : Type) [Field F] [CharP F 2] : Type := ↥(hermSub a (Fin 2) F)

abbrev hm (v : VH a F) : Mat F := Multiplicative.toAdd (v : Multiplicative (Mat F))

theorem hm_mem (v : VH a F) : hm v ∈ hermA a F := v.2

abbrev mkH (X : Mat F) (hX : X ∈ hermA a F) : VH a F := ⟨Multiplicative.ofAdd X, hX⟩

theorem hm_mkH (X : Mat F) (hX : X ∈ hermA a F) : hm (mkH X hX) = X := rfl

theorem hm_injective : Function.Injective (hm (a := a) (F := F)) := fun _ _ h =>
  Subtype.ext (Multiplicative.toAdd.injective h)

theorem hm_mul (v w : VH a F) : hm (v * w) = hm v + hm w := rfl

theorem hm_one : hm (1 : VH a F) = 0 := rfl

abbrev SigInv (a : ℕ) (F : Type) [Field F] [CharP F 2] : Prop := ∀ x : F, sig a (sig a x) = x

theorem frobPow_one : frobPow a (1 : Mat F) = 1 := by
  rw [frobPow_eq_map]
  exact map_one (sig a).mapMatrix

variable (hσ : SigInv a F)

theorem frobPow_inv_mul (g : SL₂ F) :
    (frobPow a ((g⁻¹ : SL₂ F) : Mat F))ᵀ * (frobPow a (g : Mat F))ᵀ = 1 := by
  rw [← Matrix.transpose_mul, ← frobPow_mul, coe_mul_inv, frobPow_one, Matrix.transpose_one]

theorem frobPow_mul_inv (g : SL₂ F) :
    (frobPow a (g : Mat F))ᵀ * (frobPow a ((g⁻¹ : SL₂ F) : Mat F))ᵀ = 1 := by
  rw [← Matrix.transpose_mul, ← frobPow_mul, coe_inv_mul, frobPow_one, Matrix.transpose_one]

@[expose] def rhoH : SL₂ F →* MulAut (VH a F) where
  toFun g :=
    { toFun := fun v => mkH ((g : Mat F) * hm v * (frobPow a (g : Mat F))ᵀ)
        (twist_mem a hσ v.2 _)
      invFun := fun v => mkH (((g⁻¹ : SL₂ F) : Mat F) * hm v *
        (frobPow a ((g⁻¹ : SL₂ F) : Mat F))ᵀ) (twist_mem a hσ v.2 _)
      left_inv := fun v => hm_injective (by
        show ((g⁻¹ : SL₂ F) : Mat F) * ((g : Mat F) * hm v * (frobPow a (g : Mat F))ᵀ) *
          (frobPow a ((g⁻¹ : SL₂ F) : Mat F))ᵀ = hm v
        rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, coe_inv_mul, Matrix.one_mul,
          Matrix.mul_assoc, frobPow_mul_inv, Matrix.mul_one])
      right_inv := fun v => hm_injective (by
        show (g : Mat F) * (((g⁻¹ : SL₂ F) : Mat F) * hm v *
          (frobPow a ((g⁻¹ : SL₂ F) : Mat F))ᵀ) * (frobPow a (g : Mat F))ᵀ = hm v
        rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, coe_mul_inv, Matrix.one_mul,
          Matrix.mul_assoc, frobPow_inv_mul, Matrix.mul_one])
      map_mul' := fun v w => hm_injective (by
        show (g : Mat F) * (hm v + hm w) * (frobPow a (g : Mat F))ᵀ =
          (g : Mat F) * hm v * (frobPow a (g : Mat F))ᵀ +
            (g : Mat F) * hm w * (frobPow a (g : Mat F))ᵀ
        rw [Matrix.mul_add, Matrix.add_mul]) }
  map_one' := by
    refine MulEquiv.ext fun v => hm_injective ?_
    show ((1 : SL₂ F) : Mat F) * hm v * (frobPow a ((1 : SL₂ F) : Mat F))ᵀ = hm v
    rw [Matrix.SpecialLinearGroup.coe_one, frobPow_one, Matrix.transpose_one,
      Matrix.one_mul, Matrix.mul_one]
  map_mul' g h := by
    refine MulEquiv.ext fun v => hm_injective ?_
    show ((g * h : SL₂ F) : Mat F) * hm v * (frobPow a ((g * h : SL₂ F) : Mat F))ᵀ =
      (g : Mat F) * ((h : Mat F) * hm v * (frobPow a (h : Mat F))ᵀ) * (frobPow a (g : Mat F))ᵀ
    rw [Matrix.SpecialLinearGroup.coe_mul, frobPow_mul, Matrix.transpose_mul]
    simp only [Matrix.mul_assoc]

theorem hm_rhoH (g : SL₂ F) (v : VH a F) :
    hm (rhoH hσ g v) = (g : Mat F) * hm v * (frobPow a (g : Mat F))ᵀ := rfl

abbrev LH : Subgroup (MulAut (VH a F)) := (rhoH hσ).range

omit [CharP F 2] in
theorem frobPow_lit (w x y z : F) :
    frobPow a !![w, x; y, z] = !![w ^ 2 ^ a, x ^ 2 ^ a; y ^ 2 ^ a, z ^ 2 ^ a] := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

include hσ in
theorem mem_hermA_lit {w x z : F} (hw : sig a w = w) (hz : sig a z = z) :
    !![w, x; sig a x, z] ∈ hermA a F := by
  rw [mem_hermA, frobPow_lit]
  have hσx := hσ x
  simp only [sig_apply] at hw hz hσx
  ext i j
  fin_cases i <;> fin_cases j <;> simp [hw, hz, hσx, sig_apply]

omit [CharP F 2] in
theorem frobPow_apply (M : Mat F) (i j : Fin 2) : frobPow a M i j = M i j ^ 2 ^ a := rfl

theorem twist_apply (g X : Mat F) (i j : Fin 2) :
    (g * X * (frobPow a g)ᵀ) i j = g i 0 * X 0 0 * sig a (g j 0) + g i 0 * X 0 1 * sig a (g j 1) +
      g i 1 * X 1 0 * sig a (g j 0) + g i 1 * X 1 1 * sig a (g j 1) := by
  simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.transpose_apply, frobPow_apply,
    sig_apply]
  ring

theorem nsig_eq_zero {x : F} (h : x * sig a x = 0) : x = 0 := by
  rcases mul_eq_zero.mp h with h | h
  · exact h
  · rw [sig_apply] at h
    exact (pow_eq_zero_iff (by positivity)).mp h

theorem sig_injective : Function.Injective (fun x : F => sig a x) := by
  intro x y h
  simp only [sig_apply] at h
  have h1 : (x - y) ^ (2 ^ a) = 0 := by rw [sub_pow_char_pow, h, sub_self]
  exact sub_eq_zero.mp ((pow_eq_zero_iff (by positivity)).mp h1)

theorem sig_one : sig a (1 : F) = 1 := map_one (sig a)

abbrev E11 (F : Type) [Field F] : Mat F := !![1, 0; 0, 0]

abbrev E22 (F : Type) [Field F] : Mat F := !![0, 0; 0, 1]

include hσ in
theorem E11_mem : E11 F ∈ hermA a F := by
  simpa using mem_hermA_lit hσ (w := (1 : F)) (x := 0) (z := 0) (map_one _) (map_zero _)

include hσ in
theorem E22_mem : E22 F ∈ hermA a F := by
  simpa using mem_hermA_lit hσ (w := (0 : F)) (x := 0) (z := 1) (map_zero _) (map_one _)

include hσ in
theorem Z_mem : (!![0, 1; 1, 0] : Mat F) ∈ hermA a F := by
  simpa using mem_hermA_lit hσ (w := (0 : F)) (x := 1) (z := 0) (map_zero _) (map_zero _)

include hσ in
theorem eq_one_of_twist_eq_smul {g : SL₂ F} {l : F}
    (h : ∀ X ∈ hermA a F, (g : Mat F) * X * (frobPow a (g : Mat F))ᵀ = l • X) :
    g = 1 ∧ l = 1 := by
  have h1 := h _ (E11_mem hσ)
  have h2 := h _ (E22_mem hσ)
  have h3 := h _ (Z_mem hσ)
  have e100 := congrFun (congrFun h1 0) 0
  have e111 := congrFun (congrFun h1 1) 1
  have e200 := congrFun (congrFun h2 0) 0
  have e211 := congrFun (congrFun h2 1) 1
  have e301 := congrFun (congrFun h3 0) 1
  simp only [twist_apply, Matrix.smul_apply, Matrix.of_apply, Matrix.cons_val',
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one,
    smul_eq_mul] at e100 e111 e200 e211 e301
  have hg10 : (g : Mat F) 1 0 = 0 := nsig_eq_zero (by linear_combination e111)
  have hg01 : (g : Mat F) 0 1 = 0 := nsig_eq_zero (by linear_combination e200)
  have hdet : (g : Mat F) 0 0 * (g : Mat F) 1 1 = 1 := by
    have := g.2
    rw [Matrix.det_fin_two, hg10, hg01, mul_zero, sub_zero] at this
    exact this
  have hg00 : (g : Mat F) 0 0 ≠ 0 := left_ne_zero_of_mul_eq_one hdet
  rw [hg01, hg10] at e301
  have e4 : (g : Mat F) 0 0 * sig a ((g : Mat F) 0 0) =
      (g : Mat F) 0 0 * sig a ((g : Mat F) 1 1) := by
    linear_combination e100 - e301
  have e5 := sig_injective (mul_left_cancel₀ hg00 e4)
  rw [← e5] at hdet
  have hg1 : (g : Mat F) 0 0 = 1 := eq_one_of_sq_eq_one (by rw [sq]; exact hdet)
  have hg2 : (g : Mat F) 1 1 = 1 := by rw [← e5, hg1]
  refine ⟨Subtype.ext ?_, ?_⟩
  · ext i j
    fin_cases i <;> fin_cases j
    · exact hg1
    · exact hg01
    · exact hg10
    · exact hg2
  · rw [hg1, map_one] at e100
    linear_combination -e100

include hσ in
theorem rhoH_injective : Function.Injective (rhoH (a := a) (F := F) hσ) := by
  rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
  intro g hg
  rw [MonoidHom.mem_ker] at hg
  have key : ∀ X ∈ hermA a F, (g : Mat F) * X * (frobPow a (g : Mat F))ᵀ = (1 : F) • X := by
    intro X hX
    have := congrArg (fun φ : MulAut (VH a F) => hm (φ (mkH X hX))) hg
    rw [one_smul]
    exact this
  rw [Subgroup.mem_bot]
  exact (eq_one_of_twist_eq_smul hσ key).1

theorem fix_uu_eqs {s : F} {v : VH a F} (h : rhoH hσ (uu s) v = v) :
    s * hm v 1 1 = 0 ∧ s * hm v 1 0 + sig a s * hm v 0 1 + s * sig a s * hm v 1 1 = 0 := by
  have h' := congrArg hm h
  rw [hm_rhoH] at h'
  have e00 := congrFun (congrFun h' 0) 0
  have e01 := congrFun (congrFun h' 0) 1
  simp only [twist_apply, coe_uu, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one, map_one, map_zero] at e00 e01
  refine ⟨?_, ?_⟩
  · linear_combination e01
  · linear_combination e00

theorem eq_E11_of_fix_uu {θ : F} (hθ : sig a θ ≠ θ) {v : VH a F}
    (h : ∀ s, rhoH hσ (uu s) v = v) : hm v = hm v 0 0 • E11 F := by
  have h2 : (2 : F) = 0 := CharP.cast_eq_zero F 2
  obtain ⟨e1, e2⟩ := fix_uu_eqs hσ (h 1)
  obtain ⟨-, e3⟩ := fix_uu_eqs hσ (h θ)
  rw [one_mul] at e1
  rw [sig_one, one_mul, one_mul, one_mul, e1, mul_zero, add_zero] at e2
  rw [e1, mul_zero, add_zero] at e3
  have h10 : hm v 1 0 = hm v 0 1 := by linear_combination e2 - hm v 0 1 * h2
  have h01 : hm v 0 1 = 0 := by
    have e4 : (θ + sig a θ) * hm v 0 1 = 0 := by
      rw [← h10] at e3 ⊢
      linear_combination e3
    have hne : θ + sig a θ ≠ 0 := by
      intro h0
      apply hθ
      linear_combination h0 - θ * h2
    exact (mul_eq_zero.mp e4).resolve_left hne
  ext i j
  fin_cases i <;> fin_cases j <;> simp [h01, h10, e1]

@[expose] def trF (a : ℕ) (F : Type) [Field F] [CharP F 2] : F →+ F where
  toFun θ := θ + sig a θ
  map_zero' := by rw [map_zero, add_zero]
  map_add' x y := by rw [map_add]; ring

theorem trF_apply (θ : F) : trF a F θ = θ + sig a θ := rfl

include hσ in
theorem sig_trF (θ : F) : sig a (trF a F θ) = trF a F θ := by
  rw [trF_apply, map_add, hσ, add_comm]

theorem trF_eq_zero_iff {θ : F} : trF a F θ = 0 ↔ sig a θ = θ := by
  rw [trF_apply]
  constructor
  · intro h
    have h2 : θ + θ = 0 := CharTwo.add_self_eq_zero θ
    exact (add_left_cancel (h.trans h2.symm))
  · intro h
    rw [h]
    exact CharTwo.add_self_eq_zero θ

include hσ in
theorem exists_trF_eq [Fintype F] (ha : 1 ≤ a) (hF : Fintype.card F = 2 ^ (2 * a)) {x : F}
    (hx : sig a x = x) : ∃ θ, trF a F θ = x := by
  classical
  have hker : Nat.card (trF a F).ker = 2 ^ a := by
    rw [← CFSG.Quasithin.B45L2.card_frob_fixed ha hF]
    exact Nat.card_congr (Equiv.subtypeEquivRight fun θ => by
      rw [AddMonoidHom.mem_ker, trF_eq_zero_iff, sig_apply])
  have hrange := AddSubgroup.card_ker_mul_card_range (trF a F)
  rw [hker, show Nat.card F = 2 ^ (2 * a) by rw [Nat.card_eq_fintype_card, hF]] at hrange
  have hr : Nat.card (trF a F).range = 2 ^ a := by
    have h2 : 2 ^ (2 * a) = 2 ^ a * 2 ^ a := by rw [two_mul, pow_add]
    rw [h2] at hrange
    exact Nat.eq_of_mul_eq_mul_left (by positivity) hrange
  have hsub : ((trF a F).range : Set F) ⊆ {y | y ^ 2 ^ a = y} := by
    rintro _ ⟨θ, rfl⟩
    have := sig_trF hσ θ
    rwa [sig_apply] at this
  have hK : Nat.card {y : F // y ^ 2 ^ a = y} = 2 ^ a := CFSG.Quasithin.B45L2.card_frob_fixed ha hF
  have heq : ((trF a F).range : Set F) = {y | y ^ 2 ^ a = y} := by
    apply Set.eq_of_subset_of_ncard_le hsub
    · rw [← Nat.card_coe_set_eq, ← Nat.card_coe_set_eq]
      have e1 : Nat.card ((trF a F).range : Set F) = 2 ^ a := hr
      have e2 : Nat.card ({y | y ^ 2 ^ a = y} : Set F) = 2 ^ a := hK
      omega
  have hxm : x ∈ {y : F | y ^ 2 ^ a = y} := by
    show x ^ 2 ^ a = x
    rwa [sig_apply] at hx
  rw [← heq] at hxm
  obtain ⟨θ, hθ⟩ := hxm
  exact ⟨θ, hθ⟩

theorem twist_E11 (g : Mat F) : g * E11 F * (frobPow a g)ᵀ =
    !![g 0 0 * sig a (g 0 0), g 0 0 * sig a (g 1 0); g 1 0 * sig a (g 0 0),
      g 1 0 * sig a (g 1 0)] := by
  ext i j
  rw [twist_apply]
  fin_cases i <;> fin_cases j <;> simp

abbrev e11 : VH a F := mkH (E11 F) (E11_mem hσ)

theorem sig_diag {X : Mat F} (hX : X ∈ hermA a F) (i : Fin 2) : sig a (X i i) = X i i :=
  hermA_apply hX i i

theorem sig_offdiag {X : Mat F} (hX : X ∈ hermA a F) : X 1 0 = sig a (X 0 1) :=
  (hermA_apply hX 1 0).symm

theorem herm_eq {X : Mat F} (hX : X ∈ hermA a F) :
    X = !![X 0 0, X 0 1; sig a (X 0 1), X 1 1] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [sig_offdiag hX]

include hσ in
theorem eq_smul_of_comm [Fintype F] (ha : 1 ≤ a) (hF : Fintype.card F = 2 ^ (2 * a))
    {θ₀ : F} (hθ₀ : sig a θ₀ ≠ θ₀) {ψ : MulAut (VH a F)}
    (hψ : ∀ g, ψ * rhoH hσ g = rhoH hσ g * ψ) :
    ∃ c : F, sig a c = c ∧ ∀ v, hm (ψ v) = c • hm v := by
  have h2 : (2 : F) = 0 := CharP.cast_eq_zero F 2
  have hψ' : ∀ g v, ψ (rhoH hσ g v) = rhoH hσ g (ψ v) := fun g v =>
    congrArg (fun φ : MulAut (VH a F) => φ v) (hψ g)
  have hfix : ∀ s, rhoH hσ (uu s) (ψ (e11 hσ)) = ψ (e11 hσ) := by
    intro s
    rw [← hψ']
    congr 1
    apply hm_injective
    rw [hm_rhoH, hm_mkH, twist_E11]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [coe_uu, sig_one]
  have hc := eq_E11_of_fix_uu hσ hθ₀ hfix
  set c := hm (ψ (e11 hσ)) 0 0 with hcdef
  have hcK : sig a c = c := sig_diag (hm_mem _) 0
  refine ⟨c, hcK, ?_⟩
  set S : Set (VH a F) := {v | hm (ψ v) = c • hm v} with hS
  have hSmul : ∀ v w, v ∈ S → w ∈ S → v * w ∈ S := by
    intro v w hv hw
    show hm (ψ (v * w)) = c • hm (v * w)
    rw [map_mul, hm_mul, hm_mul, hv, hw, smul_add]
  have hS1 : (1 : VH a F) ∈ S := by
    show hm (ψ 1) = c • hm 1
    rw [map_one, hm_one, smul_zero]
  have horb : ∀ g, rhoH hσ g (e11 hσ) ∈ S := by
    intro g
    show hm (ψ (rhoH hσ g (e11 hσ))) = c • hm (rhoH hσ g (e11 hσ))
    rw [hψ', hm_rhoH, hm_rhoH, hc, Matrix.mul_smul, Matrix.smul_mul]
    rfl
  have hNE11 : ∀ μ : F, ∃ u ∈ S, hm u = (μ * sig a μ) • E11 F := by
    intro μ
    by_cases hμ : μ = 0
    · exact ⟨1, hS1, by rw [hm_one, hμ, zero_mul, zero_smul]⟩
    · refine ⟨_, horb (dd μ hμ), ?_⟩
      rw [hm_rhoH, hm_mkH, twist_E11]
      ext i j
      fin_cases i <;> fin_cases j <;> simp [coe_dd]
  have hNE22 : ∀ ν : F, ∃ u ∈ S, hm u = (ν * sig a ν) • E22 F := by
    intro ν
    by_cases hν : ν = 0
    · exact ⟨1, hS1, by rw [hm_one, hν, zero_mul, zero_smul]⟩
    · refine ⟨_, horb (ww ν hν), ?_⟩
      rw [hm_rhoH, hm_mkH, twist_E11]
      ext i j
      fin_cases i <;> fin_cases j <;> simp [coe_ww]
  have hK11 : ∀ x : F, sig a x = x → ∃ u ∈ S, hm u = x • E11 F := by
    intro x hx
    obtain ⟨θ, hθ⟩ := exists_trF_eq hσ ha hF hx
    obtain ⟨u₁, hu₁, e₁⟩ := hNE11 (1 + θ)
    obtain ⟨u₂, hu₂, e₂⟩ := hNE11 θ
    obtain ⟨u₃, hu₃, e₃⟩ := hNE11 1
    refine ⟨u₁ * u₂ * u₃, hSmul _ _ (hSmul _ _ hu₁ hu₂) hu₃, ?_⟩
    rw [hm_mul, hm_mul, e₁, e₂, e₃, ← add_smul, ← add_smul, ← hθ, trF_apply]
    congr 1
    rw [map_add, sig_one]
    linear_combination (1 + θ * sig a θ) * h2
  have hK22 : ∀ z : F, sig a z = z → ∃ u ∈ S, hm u = z • E22 F := by
    intro z hz
    obtain ⟨θ, hθ⟩ := exists_trF_eq hσ ha hF hz
    obtain ⟨u₁, hu₁, e₁⟩ := hNE22 (1 + θ)
    obtain ⟨u₂, hu₂, e₂⟩ := hNE22 θ
    obtain ⟨u₃, hu₃, e₃⟩ := hNE22 1
    refine ⟨u₁ * u₂ * u₃, hSmul _ _ (hSmul _ _ hu₁ hu₂) hu₃, ?_⟩
    rw [hm_mul, hm_mul, e₁, e₂, e₃, ← add_smul, ← add_smul, ← hθ, trF_apply]
    congr 1
    rw [map_add, sig_one]
    linear_combination (1 + θ * sig a θ) * h2
  have hZ : ∀ y : F, ∃ u ∈ S, hm u = !![0, y; sig a y, 0] := by
    intro y
    obtain ⟨u₂, hu₂, e₂⟩ := hNE22 (sig a y)
    refine ⟨rhoH hσ (ul (sig a y)) (e11 hσ) * e11 hσ * u₂,
      hSmul _ _ (hSmul _ _ (horb _) (by simpa using horb 1)) hu₂, ?_⟩
    rw [hm_mul, hm_mul, e₂, hm_rhoH, hm_mkH, twist_E11]
    have hy := hσ y
    ext i j
    fin_cases i <;> fin_cases j <;> simp [coe_ul, hy, sig_one] <;>
      first
      | linear_combination (1 - sig a y * y) * h2
      | linear_combination (sig a y * y) * h2
      | linear_combination h2
  intro v
  have hv := herm_eq (hm_mem v)
  obtain ⟨u₁, hu₁, e₁⟩ := hK11 _ (sig_diag (hm_mem v) 0)
  obtain ⟨u₂, hu₂, e₂⟩ := hK22 _ (sig_diag (hm_mem v) 1)
  obtain ⟨u₃, hu₃, e₃⟩ := hZ (hm v 0 1)
  have hvu : v = u₁ * u₂ * u₃ := by
    apply hm_injective
    rw [hm_mul, hm_mul, e₁, e₂, e₃]
    conv_lhs => rw [hv]
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  rw [hvu]
  exact hSmul _ _ (hSmul _ _ hu₁ hu₂) hu₃

omit [CharP F 2] in
theorem frobPow_mapMatrix (τ : F ≃+* F) (X : Mat F) :
    frobPow a (τ.mapMatrix X) = τ.mapMatrix (frobPow a X) := by
  ext i j
  simp [frobPow_apply, map_pow]

theorem sig_map (τ : F ≃+* F) (x : F) : sig a (τ x) = τ (sig a x) := by
  rw [sig_apply, sig_apply, map_pow]

theorem mapMatrix_mem (τ : F ≃+* F) {X : Mat F} (hX : X ∈ hermA a F) :
    τ.mapMatrix X ∈ hermA a F := by
  rw [mem_hermA] at hX ⊢
  rw [frobPow_mapMatrix, ← H11P.mapMatrix_transpose, hX]

@[expose] def fA (τ : F ≃+* F) : MulAut (VH a F) where
  toFun v := mkH (τ.mapMatrix (hm v)) (mapMatrix_mem τ v.2)
  invFun v := mkH (τ.symm.mapMatrix (hm v)) (mapMatrix_mem τ.symm v.2)
  left_inv v := hm_injective (H11P.symm_mapMatrix_apply τ (hm v))
  right_inv v := hm_injective (H11P.mapMatrix_symm_apply τ (hm v))
  map_mul' v w := hm_injective (by
    show τ.mapMatrix (hm v + hm w) = τ.mapMatrix (hm v) + τ.mapMatrix (hm w)
    rw [map_add])

theorem hm_fA (τ : F ≃+* F) (v : VH a F) : hm (fA τ v) = τ.mapMatrix (hm v) := rfl

theorem fA_mul_rhoH (τ : F ≃+* F) (g : SL₂ F) :
    fA τ * rhoH hσ g = rhoH hσ (slFieldAut F τ g) * fA τ := by
  refine MulEquiv.ext fun v => hm_injective ?_
  show τ.mapMatrix ((g : Mat F) * hm v * (frobPow a (g : Mat F))ᵀ) =
    ((slFieldAut F τ g : SL₂ F) : Mat F) * τ.mapMatrix (hm v) *
      (frobPow a ((slFieldAut F τ g : SL₂ F) : Mat F))ᵀ
  rw [H11P.coe_slFieldAut, map_mul, map_mul, H11P.mapMatrix_transpose, frobPow_mapMatrix]

include hσ in
theorem normal_form [Fintype F] (ha : 1 ≤ a) (hF : Fintype.card F = 2 ^ (2 * a))
    {θ₀ : F} (hθ₀ : sig a θ₀ ≠ θ₀) {x : MulAut (VH a F)}
    (hx : x ∈ Subgroup.normalizer ((LH hσ : Subgroup (MulAut (VH a F))) : Set _)) :
    ∃ c : F, sig a c = c ∧ c ≠ 0 ∧ ∃ (M : SL₂ F) (τ : F ≃+* F),
      ∀ v, hm (x v) = c • ((M : Mat F) * τ.mapMatrix (hm v) * (frobPow a (M : Mat F))ᵀ) := by
  have hinj := rhoH_injective (a := a) hσ
  have hmem : ∀ g : SL₂ F, x * rhoH hσ g * x⁻¹ ∈ LH hσ := fun g =>
    (Subgroup.mem_normalizer_iff.mp hx _).mp ⟨g, rfl⟩
  choose α hα using hmem
  have hconj : ∀ u v : MulAut (VH a F), x * (u * v) * x⁻¹ = (x * u * x⁻¹) * (x * v * x⁻¹) :=
    fun u v => by group
  have hαmul : ∀ g g', α (g * g') = α g * α g' := fun g g' => hinj (by
    rw [hα, map_mul, map_mul, hconj, hα, hα])
  have hαinj : Function.Injective α := fun g g' h => by
    have h1 : x * rhoH hσ g * x⁻¹ = x * rhoH hσ g' * x⁻¹ := by rw [← hα, ← hα, h]
    exact hinj (mul_left_cancel (mul_right_cancel h1))
  have : Finite F := Finite.of_fintype F
  obtain ⟨M, τ, hMτ⟩ := exists_conj_of_hom hαmul hαinj
  set ψ := (rhoH hσ M)⁻¹ * x with hψ
  have hψρ : ∀ g, ψ * rhoH hσ g = rhoH hσ (slFieldAut F τ g) * ψ := by
    intro g
    have h1 : x * rhoH hσ g * x⁻¹ = rhoH hσ M * rhoH hσ (slFieldAut F τ g) * (rhoH hσ M)⁻¹ := by
      rw [← hα, hMτ, map_mul, map_mul, map_inv]
    calc ψ * rhoH hσ g = (rhoH hσ M)⁻¹ * (x * rhoH hσ g * x⁻¹) * x := by rw [hψ]; group
      _ = rhoH hσ (slFieldAut F τ g) * ψ := by rw [h1, hψ]; group
  set ψ' := fA τ⁻¹ * ψ with hψ'
  have hψ'ρ : ∀ g, ψ' * rhoH hσ g = rhoH hσ g * ψ' := by
    intro g
    have e1 : slFieldAut F τ⁻¹ (slFieldAut F τ g) = g := by
      rw [← MulAut.mul_apply, ← map_mul, inv_mul_cancel, map_one, MulAut.one_apply]
    calc ψ' * rhoH hσ g = fA τ⁻¹ * (ψ * rhoH hσ g) := by rw [hψ']; group
      _ = (fA τ⁻¹ * rhoH hσ (slFieldAut F τ g)) * ψ := by rw [hψρ]; group
      _ = rhoH hσ g * ψ' := by rw [fA_mul_rhoH, e1, hψ']; group
  obtain ⟨c', hc'K, hc'⟩ := eq_smul_of_comm hσ ha hF hθ₀ hψ'ρ
  have hxψ : x = rhoH hσ M * fA τ * ψ' := by
    rw [hψ', hψ, ← mul_assoc, mul_assoc (rhoH hσ M), show fA τ * fA τ⁻¹ = 1 from ?_, mul_one,
      ← mul_assoc, mul_inv_cancel, one_mul]
    refine MulEquiv.ext fun v => hm_injective ?_
    show τ.mapMatrix (τ⁻¹.mapMatrix (hm v)) = hm v
    exact H11P.mapMatrix_symm_apply τ (hm v)
  have hform : ∀ v, hm (x v) = τ c' • ((M : Mat F) * τ.mapMatrix (hm v) *
      (frobPow a (M : Mat F))ᵀ) := by
    intro v
    rw [hxψ, MulAut.mul_apply, MulAut.mul_apply, hm_rhoH, hm_fA, hc', H11P.mapMatrix_smul,
      Matrix.mul_smul, Matrix.smul_mul]
  have hcK : sig a (τ c') = τ c' := by rw [sig_map, hc'K]
  have hc0 : τ c' ≠ 0 := by
    intro h0
    have h1 := hform (e11 hσ)
    rw [h0, zero_smul] at h1
    have h2 : x (e11 hσ) = x 1 := hm_injective (by rw [h1, map_one]; rfl)
    have h3 := congrArg hm (x.injective h2)
    have h4 : (E11 F) 0 0 = (0 : Mat F) 0 0 := congrFun (congrFun h3 0) 0
    simp at h4
  exact ⟨τ c', hcK, hc0, M, τ, hform⟩

end CFSG.Quasithin.H13.H11M

end
