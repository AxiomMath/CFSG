module

public import CFSG.Milestones.ASVolI.F429.aR5
public import CFSG.Milestones.ASVolI.F429.Corr
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherIsotropicCentralizer
import all CFSG.Milestones.ASVolI.F4

public section

namespace CFSG.ASVolI

section Generic

open CFSG.Open CFSG.ASVolI.ChF CFSG.Quasithin

variable {E : Type} [Group E]

theorem burnsideF429a_inf_sup_inf_eq {Gp M₁ M₂ : Subgroup E} [Gp.Normal] (hgen : M₁ ⊔ M₂ = ⊤)
    (hsplit : ∀ e : E, ∃ n ∈ Gp, ∃ x ∈ M₁ ⊓ M₂, e = n * x) :
    (Gp ⊓ M₁) ⊔ (Gp ⊓ M₂) = Gp := by
  set X := (Gp ⊓ M₁) ⊔ (Gp ⊓ M₂) with hX
  have hXG : X ≤ Gp := sup_le inf_le_left inf_le_left
  have hconj : ∀ {M : Subgroup E} {b : E}, b ∈ M →
      b ∈ Subgroup.normalizer ((Gp ⊓ M : Subgroup E) : Set E) := by
    intro M b hbM
    rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · rintro ⟨hxG, hxM⟩
      exact ⟨(inferInstance : Gp.Normal).conj_mem x hxG b,
        M.mul_mem (M.mul_mem hbM hxM) (M.inv_mem hbM)⟩
    · rintro ⟨hxG, hxM⟩
      refine ⟨?_, ?_⟩
      · have := (inferInstance : Gp.Normal).conj_mem _ hxG b⁻¹
        simpa [mul_assoc] using this
      · have := M.mul_mem (M.mul_mem (M.inv_mem hbM) hxM) hbM
        simpa [mul_assoc] using this
  have hXn : M₁ ⊓ M₂ ≤ Subgroup.normalizer (X : Set E) := by
    intro b hb
    rw [Subgroup.mem_normalizer_iff_map_conj_eq, hX, Subgroup.map_sup,
      Subgroup.mem_normalizer_iff_map_conj_eq.mp (hconj hb.1),
      Subgroup.mem_normalizer_iff_map_conj_eq.mp (hconj hb.2)]
  have hY : ∀ {M : Subgroup E}, M₁ ⊓ M₂ ≤ M → Gp ⊓ M ≤ X → M ≤ X ⊔ (M₁ ⊓ M₂) := by
    intro M hM12 hMX m hm
    obtain ⟨n, hn, x, hx, rfl⟩ := hsplit m
    have hnM : n ∈ M := by
      have := M.mul_mem hm (M.inv_mem (hM12 hx))
      simpa using this
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left (hMX ⟨hn, hnM⟩)) (Subgroup.mem_sup_right hx)
  have htop : X ⊔ (M₁ ⊓ M₂) = ⊤ := by
    rw [eq_top_iff, ← hgen]
    exact sup_le (hY inf_le_left le_sup_left) (hY inf_le_right le_sup_right)
  refine le_antisymm hXG fun g hg => ?_
  have hgY : g ∈ X ⊔ (M₁ ⊓ M₂) := by
    rw [htop]
    exact Subgroup.mem_top g
  obtain ⟨x, hx, b, hb, rfl⟩ := burnsideF429a_exists_mul_eq_of_mem_sup hXn hgY
  have hbG : b ∈ Gp := by
    have := Gp.mul_mem (Gp.inv_mem (hXG hx)) hg
    simpa using this
  exact X.mul_mem hx (Subgroup.mem_sup_left ⟨hbG, hb.1⟩)

theorem burnsideF429a_relIndex_sup_zpowers [Finite E] {Q : Subgroup E} {t : E}
    (htN : t ∈ Subgroup.normalizer (Q : Set E)) (htQ : t ∉ Q) (ht2 : t * t = 1) :
    Q.relIndex (Q ⊔ Subgroup.zpowers t) = 2 := by
  set Z := Subgroup.zpowers t with hZ
  have hZN : Z ≤ Subgroup.normalizer (Q : Set E) :=
    (Subgroup.zpowers_le (H := Subgroup.normalizer _)).mpr htN
  have ht1 : t ≠ 1 := fun h1 => htQ (h1 ▸ Q.one_mem)
  have hord : orderOf t = 2 := orderOf_eq_prime (by rw [sq, ht2]) ht1
  have hZcard : Nat.card Z = 2 := by rw [hZ, Nat.card_zpowers, hord]
  have hQZ : Q ⊓ Z = ⊥ := by
    rw [eq_bot_iff]
    rintro x ⟨hxQ, hxZ⟩
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hxZ
    rw [Subgroup.mem_bot]
    rw [← zpow_mod_orderOf, hord] at hxQ ⊢
    rcases Int.emod_two_eq_zero_or_one n with h0 | h1
    · rw [Nat.cast_ofNat, h0, zpow_zero]
    · rw [Nat.cast_ofNat, h1, zpow_one] at hxQ
      exact absurd hxQ htQ
  have h1 := burnsideF429a_relIndex_sup hZN
  rw [hQZ, Subgroup.relIndex_bot_left] at h1
  have hc1 := Subgroup.relIndex_mul_card Q (Q ⊔ Z)
  rw [inf_eq_left.2 le_sup_left] at hc1
  have hc2 := Subgroup.relIndex_mul_card Z (Q ⊔ Z)
  rw [inf_eq_left.2 le_sup_right, h1, hZcard] at hc2
  have hpos : 0 < Nat.card Q := Nat.card_pos
  have : Q.relIndex (Q ⊔ Z) * Nat.card Q = 2 * Nat.card Q := by rw [hc1, ← hc2, mul_comm]
  exact Nat.eq_of_mul_eq_mul_right hpos this

end Generic

section SL2

theorem burnsideF429a_sl2_trace_eq_zero {F : Type} [Field F] (h2 : (2 : F) = 0)
    (X : Matrix.SpecialLinearGroup (Fin 2) F) {k : ℕ} (hX : X ^ 2 ^ k = 1) :
    (X : Matrix (Fin 2) (Fin 2) F) 0 0 + (X : Matrix (Fin 2) (Fin 2) F) 1 1 = 0 := by
  have hsq : ∀ Y : Matrix (Fin 2) (Fin 2) F, (Y + 1) ^ 2 = Y ^ 2 + 1 := by
    intro Y
    have hYY : Y + Y = 0 := by rw [← two_smul F Y, h2, zero_smul]
    calc (Y + 1) ^ 2 = Y * Y + (Y + Y) + 1 := by
          rw [sq, add_mul, mul_add, mul_add, mul_one, one_mul, one_mul]
          abel
      _ = Y ^ 2 + 1 := by rw [hYY, add_zero, sq]
  have hpow : ∀ j : ℕ, ((X : Matrix (Fin 2) (Fin 2) F) + 1) ^ 2 ^ j =
      (X : Matrix (Fin 2) (Fin 2) F) ^ 2 ^ j + 1 := by
    intro j
    induction j with
    | zero => simp
    | succ j ih => rw [pow_succ, pow_mul, ih, hsq, ← pow_mul]
  have hXk : (X : Matrix (Fin 2) (Fin 2) F) ^ 2 ^ k = 1 := by
    rw [← Matrix.SpecialLinearGroup.coe_pow, hX, Matrix.SpecialLinearGroup.coe_one]
  have h11 : (1 : Matrix (Fin 2) (Fin 2) F) + 1 = 0 := by
    rw [← two_smul F (1 : Matrix (Fin 2) (Fin 2) F), h2, zero_smul]
  have h0 : ((X : Matrix (Fin 2) (Fin 2) F) + 1) ^ 2 ^ k = 0 := by rw [hpow, hXk, h11]
  have hdet0 : ((X : Matrix (Fin 2) (Fin 2) F) + 1).det = 0 := by
    have := congrArg Matrix.det h0
    rw [Matrix.det_pow, Matrix.det_zero] at this
    exact (pow_eq_zero_iff (pow_ne_zero k two_ne_zero)).mp this
  have hdetX := X.2
  rw [Matrix.det_fin_two] at hdet0 hdetX
  simp only [Matrix.add_apply, Matrix.one_apply_eq,
    Matrix.one_apply_ne (show (0 : Fin 2) ≠ 1 by decide),
    Matrix.one_apply_ne (show (1 : Fin 2) ≠ 0 by decide), add_zero] at hdet0
  linear_combination hdet0 - hdetX - h2

theorem burnsideF429a_sl2_eq_one_of_two {F : Type} [Field F] (h2 : (2 : F) = 0)
    (A N₁ N₂ : Matrix.SpecialLinearGroup (Fin 2) F)
    (hN₁ : (N₁ : Matrix (Fin 2) (Fin 2) F) = !![1, 1; 0, 1])
    (hN₂ : (N₂ : Matrix (Fin 2) (Fin 2) F) = !![1, 0; 1, 1])
    {k₀ k₁ k₂ : ℕ} (hA : A ^ 2 ^ k₀ = 1) (hA₁ : (A * N₁ * A * N₁) ^ 2 ^ k₁ = 1)
    (hA₂ : (A * N₂ * A * N₂) ^ 2 ^ k₂ = 1) : A = 1 := by
  have t0 := burnsideF429a_sl2_trace_eq_zero h2 A hA
  have t1 := burnsideF429a_sl2_trace_eq_zero h2 _ hA₁
  have t2 := burnsideF429a_sl2_trace_eq_zero h2 _ hA₂
  simp only [Matrix.SpecialLinearGroup.coe_mul, hN₁, hN₂, Matrix.mul_apply, Fin.sum_univ_two,
    Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.head_cons, Matrix.head_fin_const,
    one_mul, mul_one, zero_mul, mul_zero, add_zero, zero_add] at t1 t2
  have hdet := A.2
  rw [Matrix.det_fin_two] at hdet
  set a := (A : Matrix (Fin 2) (Fin 2) F) 0 0
  set b := (A : Matrix (Fin 2) (Fin 2) F) 0 1
  set c := (A : Matrix (Fin 2) (Fin 2) F) 1 0
  set d := (A : Matrix (Fin 2) (Fin 2) F) 1 1
  have hc : c = 0 := by
    have : c ^ 2 = 0 := by
      linear_combination t1 - (a + d) * t0 + (a * d - a * c - b * c - c * d) * h2
    exact pow_eq_zero_iff two_ne_zero |>.mp this
  have hb : b = 0 := by
    have : b ^ 2 = 0 := by
      linear_combination t2 - (a + d) * t0 + (a * d - a * b - b * c - b * d) * h2
    exact pow_eq_zero_iff two_ne_zero |>.mp this
  have ha : a = 1 := by
    have : (a - 1) ^ 2 = 0 := by
      linear_combination a * t0 - hdet - c * hb - a * h2
    exact sub_eq_zero.mp (pow_eq_zero_iff two_ne_zero |>.mp this)
  have hd : d = 1 := by linear_combination t0 - ha - h2
  ext i j
  fin_cases i <;> fin_cases j
  · exact ha
  · exact hb
  · exact hc
  · exact hd

end SL2

section U4Model

open Matrix CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
  CFSG.Quasithin.H13.U4Par CFSG.Quasithin.H13.Sec53F.Unit CFSG.ASVolI.ChF CFSG.Open
  CFSG.Quasithin

variable {m : ℕ} {K : Type} [Field K] (h : UnitaryFieldData 2 m K)

theorem burnsideF429a_U4_two_fixedField : (2 : h.fixedField) = 0 := by
  have := h.charP
  have e : (2 : h.fixedField) = 1 + 1 := one_add_one_eq_two.symm
  rw [e]
  apply Subtype.ext
  show ((1 : h.fixedField) : K) + ((1 : h.fixedField) : K) = ((0 : h.fixedField) : K)
  rw [OneMemClass.coe_one, ZeroMemClass.coe_zero, one_add_one_eq_two]
  exact CharTwo.two_eq_zero

theorem burnsideF429a_U4_pCoreOf_oPPrime_eq : pCoreOf 2 (oPPrime 2 (parP h)) = radQ h := by
  have := h.charP
  have h2F := burnsideF429a_U4_two_fixedField h
  set L := oPPrime 2 (parP h) with hLdef
  have hQP : radQ h ≤ parP h :=
    (radQ_le_pCoreOf_parP h).trans (CFSG.LieType.BorelTits.pCoreOf_le 2 _)
  have hQL : radQ h ≤ L := by
    intro q hq
    obtain ⟨k, hk⟩ := radQ_isPGroup h ⟨q, hq⟩
    exact burnsideF4gU4Inv_mem_oPPrime (hQP hq) (k := k) (by simpa using congrArg Subtype.val hk)
  apply le_antisymm
  · intro x hx
    have hxL : x ∈ L := CFSG.LieType.BorelTits.pCoreOf_le 2 L hx
    have hxH : x ∈ parH h := burnsideF429a_U4_oPPrime_le_parH h hxL
    have h2el : ∀ y ∈ pCoreOf 2 L, ∃ k : ℕ, y ^ 2 ^ k = 1 := fun y hy => by
      obtain ⟨k, hk⟩ := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 L ⟨y, hy⟩
      exact ⟨k, by simpa using congrArg Subtype.val hk⟩
    have h11 : (1 : h.fixedField) + 1 = 0 := one_add_one_eq_two.trans h2F
    let N₁ : Matrix.SpecialLinearGroup (Fin 2) h.fixedField :=
      ⟨!![1, 1; 0, 1], by simp [Matrix.det_fin_two]⟩
    let N₂ : Matrix.SpecialLinearGroup (Fin 2) h.fixedField :=
      ⟨!![1, 0; 1, 1], by simp [Matrix.det_fin_two]⟩
    have hN₁ : N₁ * N₁ = 1 := by
      apply Subtype.ext
      show (!![1, 1; 0, 1] : Matrix (Fin 2) (Fin 2) h.fixedField) * !![1, 1; 0, 1] = 1
      ext i j
      fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, h11]
    have hN₂ : N₂ * N₂ = 1 := by
      apply Subtype.ext
      show (!![1, 0; 1, 1] : Matrix (Fin 2) (Fin 2) h.fixedField) * !![1, 0; 1, 1] = 1
      ext i j
      fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, h11]
    have hlL : ∀ N : Matrix.SpecialLinearGroup (Fin 2) h.fixedField, N * N = 1 →
        levHom h N ∈ L := fun N hN =>
      burnsideF4gU4Inv_mem_oPPrime (levHom_le_parP h ⟨N, rfl⟩) (k := 1)
        (by rw [pow_one, pow_two, ← map_mul, hN, map_one])
    have hprod : ∀ N : Matrix.SpecialLinearGroup (Fin 2) h.fixedField, N * N = 1 →
        ∃ k : ℕ, (rhoF h ⟨x, hxH⟩ * N * rhoF h ⟨x, hxH⟩ * N) ^ 2 ^ k = 1 := by
      intro N hN
      have hlH : levHom h N ∈ parH h := levHom_range_le_parH h ⟨N, rfl⟩
      have hmem : x * (levHom h N * x * (levHom h N)⁻¹) ∈ pCoreOf 2 L :=
        (pCoreOf 2 L).mul_mem hx ((Subgroup.mem_normalizer_iff.mp
          (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 L (hlL N hN)) x).mp hx)
      obtain ⟨k, hk⟩ := h2el _ hmem
      have hNi : N⁻¹ = N := inv_eq_of_mul_eq_one_left hN
      have e : rhoF h ⟨x, hxH⟩ * N * rhoF h ⟨x, hxH⟩ * N =
          rhoF h (⟨x, hxH⟩ * (⟨levHom h N, hlH⟩ * ⟨x, hxH⟩ * ⟨levHom h N, hlH⟩⁻¹)) := by
        rw [map_mul, map_mul, map_mul, map_inv, rhoF_levHom, hNi, mul_assoc, mul_assoc,
          mul_assoc]
      refine ⟨k, ?_⟩
      rw [e, ← map_pow]
      have hk' : (⟨x, hxH⟩ * (⟨levHom h N, hlH⟩ * ⟨x, hxH⟩ * ⟨levHom h N, hlH⟩⁻¹) : parH h) ^
          2 ^ k = 1 := Subtype.ext (by simpa using hk)
      rw [hk', map_one]
    obtain ⟨k₀, hk₀⟩ := h2el x hx
    have hA : rhoF h ⟨x, hxH⟩ ^ 2 ^ k₀ = 1 := by
      rw [← map_pow]
      have : (⟨x, hxH⟩ : parH h) ^ 2 ^ k₀ = 1 := Subtype.ext (by simpa using hk₀)
      rw [this, map_one]
    obtain ⟨k₁, hk₁⟩ := hprod N₁ hN₁
    obtain ⟨k₂, hk₂⟩ := hprod N₂ hN₂
    have hX : rhoF h ⟨x, hxH⟩ = 1 :=
      burnsideF429a_sl2_eq_one_of_two h2F _ N₁ N₂ rfl rfl hA hk₁ hk₂
    exact CFSG.Quasithin.H13.U4V.mem_radQ_of_rhoF_eq_one h hX
  · refine CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 hQL ?_ (radQ_isPGroup h)
    exact (burnsideF429a_oPPrime_le _).trans (parP_le_normalizer_radQ h)

theorem burnsideF429a_U4_fieldAut_frobElt (τ : K ≃+* K) (g : hypSU h 2 0) :
    fieldAut h τ (frobElt h g) = frobElt h (fieldAut h τ g) := by
  apply hypSU_ext h
  rw [fieldAut_apply, fieldAut_apply, mat_fieldHom, coe_frobElt, coe_frobElt, mat_fieldHom]
  ext i j
  simp only [Matrix.map_apply, burnsideF429a_U4_bar_comm h]

theorem burnsideF429a_U4_rho_fieldAut (τ : K ≃+* K) (g : hypSU h 2 0) :
    rho h (fieldAut h τ g) = (rho h g).map τ := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

theorem burnsideF429a_U4_refl_or_bar {g : hypSU h 2 0} (hg : g ∈ parP h) {τ : K ≃+* K}
    (hc : ∀ l ∈ oPPrime 2 (parP h), g * fieldAut h τ l * g⁻¹ * l⁻¹ ∈ radQ h) :
    τ = RingEquiv.refl K ∨ ∀ c, τ c = h.bar c := by
  have := h.charP
  have h2F := burnsideF429a_U4_two_fixedField h
  have h11 : (1 : h.fixedField) + 1 = 0 := one_add_one_eq_two.trans h2F
  have hkey : ∀ N : Matrix.SpecialLinearGroup (Fin 2) h.fixedField, N * N = 1 →
      rho h g * (slMat h N).map τ = slMat h N * rho h g := by
    intro N hN
    have hlP : levHom h N ∈ parP h := levHom_le_parP h ⟨N, rfl⟩
    have hl : levHom h N ∈ oPPrime 2 (parP h) :=
      burnsideF4gU4Inv_mem_oPPrime hlP (k := 1) (by rw [pow_one, pow_two, ← map_mul, hN, map_one])
    have hq := hc _ hl
    have h1 := (chi_rho_of_mem_radQ h hq).2
    have hτl : fieldAut h τ (levHom h N) ∈ parP h := burnsideF429a_U4_fieldAut_mem_parP h τ hlP
    rw [rho_mul h ((parP h).mul_mem ((parP h).mul_mem hg hτl) ((parP h).inv_mem hg))
        ((parP h).inv_mem hlP),
      rho_mul h ((parP h).mul_mem hg hτl) ((parP h).inv_mem hg), rho_mul h hg hτl,
      burnsideF429a_U4_rho_fieldAut, rho_levHom] at h1
    have hRR : rho h g⁻¹ * rho h g = 1 := mul_eq_one_comm.mp (rho_mul_inv h hg)
    have hLL : rho h (levHom h N)⁻¹ * slMat h N = 1 := by
      rw [← rho_levHom]
      exact mul_eq_one_comm.mp (rho_mul_inv h hlP)
    have hX : rho h g * (slMat h N).map τ * rho h g⁻¹ = slMat h N := by
      calc rho h g * (slMat h N).map τ * rho h g⁻¹
          = rho h g * (slMat h N).map τ * rho h g⁻¹ * (rho h (levHom h N)⁻¹ * slMat h N) := by
            rw [hLL, Matrix.mul_one]
        _ = (rho h g * (slMat h N).map τ * rho h g⁻¹ * rho h (levHom h N)⁻¹) * slMat h N := by
            simp only [Matrix.mul_assoc]
        _ = slMat h N := by rw [h1, Matrix.one_mul]
    calc rho h g * (slMat h N).map τ = rho h g * (slMat h N).map τ * (rho h g⁻¹ * rho h g) := by
          rw [hRR, Matrix.mul_one]
      _ = (rho h g * (slMat h N).map τ * rho h g⁻¹) * rho h g := by simp only [Matrix.mul_assoc]
      _ = slMat h N * rho h g := by rw [hX]
  let Nc : h.fixedField → Matrix.SpecialLinearGroup (Fin 2) h.fixedField := fun c =>
    ⟨!![1, c; 0, 1], by simp [Matrix.det_fin_two]⟩
  have hNc : ∀ c, Nc c * Nc c = 1 := by
    intro c
    apply Subtype.ext
    show (!![1, c; 0, 1] : Matrix (Fin 2) (Fin 2) h.fixedField) * !![1, c; 0, 1] = 1
    have hcc : c + c = 0 := by rw [← two_mul, h2F, zero_mul]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, hcc]
  let N₂ : Matrix.SpecialLinearGroup (Fin 2) h.fixedField :=
    ⟨!![1, 0; 1, 1], by simp [Matrix.det_fin_two]⟩
  have hN₂ : N₂ * N₂ = 1 := by
    apply Subtype.ext
    show (!![1, 0; 1, 1] : Matrix (Fin 2) (Fin 2) h.fixedField) * !![1, 0; 1, 1] = 1
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, h11]
  have e1 := hkey (Nc 1) (hNc 1)
  have e2 := hkey N₂ hN₂
  have eNc : ∀ c : h.fixedField, slMat h (Nc c) = !![1, (c : K); 0, 1] := by
    intro c
    ext i j
    fin_cases i <;> fin_cases j <;> simp [slMat, Nc]
  have eN₂ : slMat h N₂ = !![1, 0; 1, 1] := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [slMat, N₂]
  rw [eNc, OneMemClass.coe_one] at e1
  rw [eN₂] at e2
  have hm1 : (!![1, 1; 0, 1] : Matrix (Fin 2) (Fin 2) K).map τ = !![1, 1; 0, 1] := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  have hm2 : (!![1, 0; 1, 1] : Matrix (Fin 2) (Fin 2) K).map τ = !![1, 0; 1, 1] := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  rw [hm1] at e1
  rw [hm2] at e2
  have f00 := congrFun (congrFun e1 0) 0
  have f01 := congrFun (congrFun e1 0) 1
  have g00 := congrFun (congrFun e2 0) 0
  simp [Matrix.mul_apply, Fin.sum_univ_two] at f00 f01 g00
  have hdet : (rho h g).det ≠ 0 := by
    intro h0
    have := congrArg Matrix.det (rho_mul_inv h hg)
    rw [Matrix.det_mul, h0, zero_mul, Matrix.det_one] at this
    exact zero_ne_one this
  rw [Matrix.det_fin_two] at hdet
  have hr10 : rho h g 1 0 = 0 := by linear_combination f00
  have hr01 : rho h g 0 1 = 0 := by linear_combination g00
  have hr11 : rho h g 1 1 = rho h g 0 0 := by linear_combination -f01
  have hr00 : rho h g 0 0 ≠ 0 := by
    intro h0
    apply hdet
    rw [hr10, hr11, h0]
    ring
  refine UnitaryHigher.ringEquiv_eq_refl_or_bar_of_fixes h fun c hc => ?_
  have e := hkey (Nc ⟨c, hc⟩) (hNc ⟨c, hc⟩)
  rw [eNc] at e
  have e01 := congrFun (congrFun e 0) 1
  simp [Matrix.mul_apply, Fin.sum_univ_two, hr10, hr01, hr11] at e01
  have := mul_left_cancel₀ hr00 (e01.trans (mul_comm _ _))
  exact this

end U4Model

section Transport

open Matrix CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher CFSG.Quasithin.H13.U4Par
  CFSG.ASVolI.ChF CFSG.ASVolI.ChF.ClassicalRoots

theorem burnsideF429a_matrix_frob {K ι : Type} [Field K] [Fintype ι] [DecidableEq ι]
    (σ : K →+* K) (Bm Bi : Matrix (Fin 4) (Fin 4) K) (hBiBm : Bi * Bm = 1)
    (P : Matrix (Fin 4) ι K) (Q : Matrix ι (Fin 4) K) (hPs : P.map σ = P) (hQs : Q.map σ = Q)
    (g : Matrix ι ι K) :
    Bm * (Bi * (Bm * P * g * (Q * Bi)) * Bm).map σ * Bi = Bm * P * g.map σ * (Q * Bi) := by
  have e1 : Bi * (Bm * P * g * (Q * Bi)) * Bm = P * g * Q := by
    rw [show Bi * (Bm * P * g * (Q * Bi)) * Bm = (Bi * Bm) * P * g * Q * (Bi * Bm) by
      simp only [Matrix.mul_assoc], hBiBm, Matrix.one_mul, Matrix.mul_one]
  rw [e1, Matrix.map_mul, Matrix.map_mul, hPs, hQs]
  simp only [Matrix.mul_assoc]

variable {f : ℕ} {H : Type} [Group H] (mk : Marking .U4 2 f H)

theorem burnsideF429a_U4_T_frob (sigma : mk.field →+* mk.field)
    (hsig : ∀ p, sigma p = p ^ (2 ^ f)) (g : hypSU (burnsideF4gU4_fieldData mk) 2 0) :
    mk.basis * Matrix.GeneralLinearGroup.map sigma
        (mk.basis⁻¹ * ((burnsideF4gU4_T mk g : nativeGroup .U4 (2 ^ f) mk.field) :
          GL (Coord .U4) mk.field) * mk.basis) * mk.basis⁻¹ =
      ((burnsideF4gU4_T mk (frobElt (burnsideF4gU4_fieldData mk) g) :
        nativeGroup .U4 (2 ^ f) mk.field) : GL (Coord .U4) mk.field) := by
  have hBiBm : ((mk.basis⁻¹ : GL (Coord .U4) mk.field) : Matrix (Fin 4) (Fin 4) mk.field) *
      (mk.basis : Matrix (Fin 4) (Fin 4) mk.field) = 1 := by
    rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  have hBmBi : (mk.basis : Matrix (Fin 4) (Fin 4) mk.field) *
      ((mk.basis⁻¹ : GL (Coord .U4) mk.field) : Matrix (Fin 4) (Fin 4) mk.field) = 1 := by
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hR := burnsideF4gU4_marking_isHypTransport mk
  have h1 := transportInv_mul hR
  have hRP : burnsideF4gU4_R (mk.basis : Matrix (Fin 4) (Fin 4) mk.field) =
      (mk.basis : Matrix (Fin 4) (Fin 4) mk.field) *
        (1 : Matrix (Fin 4) (Fin 4) mk.field).submatrix id burnsideF4gU4_equiv := by
    ext i a
    simp only [burnsideF4gU4_R, Matrix.submatrix_apply, Matrix.mul_apply, Matrix.one_apply, id,
      mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  have hPQ : (1 : Matrix (Fin 4) (Fin 4) mk.field).submatrix id burnsideF4gU4_equiv *
      (1 : Matrix (Fin 4) (Fin 4) mk.field).submatrix burnsideF4gU4_equiv id = 1 := by
    rw [Matrix.submatrix_mul_equiv, Matrix.mul_one]
    ext i j
    simp [Matrix.one_apply]
  have hRinv : transportInv (burnsideF4gU4_fieldData mk)
      (burnsideF4gU4_R (mk.basis : Matrix (Fin 4) (Fin 4) mk.field)) =
      (1 : Matrix (Fin 4) (Fin 4) mk.field).submatrix burnsideF4gU4_equiv id *
        ((mk.basis⁻¹ : GL (Coord .U4) mk.field) : Matrix (Fin 4) (Fin 4) mk.field) := by
    set Rinv := transportInv (burnsideF4gU4_fieldData mk)
      (burnsideF4gU4_R (mk.basis : Matrix (Fin 4) (Fin 4) mk.field))
    have hq : Rinv * (mk.basis : Matrix (Fin 4) (Fin 4) mk.field) =
        (1 : Matrix (Fin 4) (Fin 4) mk.field).submatrix burnsideF4gU4_equiv id := by
      calc Rinv * (mk.basis : Matrix (Fin 4) (Fin 4) mk.field)
          = Rinv * (mk.basis : Matrix (Fin 4) (Fin 4) mk.field) *
              ((1 : Matrix (Fin 4) (Fin 4) mk.field).submatrix id burnsideF4gU4_equiv *
                (1 : Matrix (Fin 4) (Fin 4) mk.field).submatrix burnsideF4gU4_equiv id) := by
            rw [hPQ, Matrix.mul_one]
        _ = Rinv * ((mk.basis : Matrix (Fin 4) (Fin 4) mk.field) *
              (1 : Matrix (Fin 4) (Fin 4) mk.field).submatrix id burnsideF4gU4_equiv) *
              (1 : Matrix (Fin 4) (Fin 4) mk.field).submatrix burnsideF4gU4_equiv id := by
            simp only [Matrix.mul_assoc]
        _ = _ := by rw [← hRP, h1, Matrix.one_mul]
    calc Rinv = Rinv * ((mk.basis : Matrix (Fin 4) (Fin 4) mk.field) *
          ((mk.basis⁻¹ : GL (Coord .U4) mk.field) : Matrix (Fin 4) (Fin 4) mk.field)) := by
          rw [hBmBi, Matrix.mul_one]
      _ = _ := by rw [← Matrix.mul_assoc, hq]
  have hPs : ((1 : Matrix (Fin 4) (Fin 4) mk.field).submatrix id burnsideF4gU4_equiv).map sigma =
      (1 : Matrix (Fin 4) (Fin 4) mk.field).submatrix id burnsideF4gU4_equiv := by
    ext i a
    simp only [Matrix.map_apply, Matrix.submatrix_apply, Matrix.one_apply, id]
    split_ifs <;> simp
  have hQs : ((1 : Matrix (Fin 4) (Fin 4) mk.field).submatrix burnsideF4gU4_equiv id).map sigma =
      (1 : Matrix (Fin 4) (Fin 4) mk.field).submatrix burnsideF4gU4_equiv id := by
    ext a i
    simp only [Matrix.map_apply, Matrix.submatrix_apply, Matrix.one_apply, id]
    split_ifs <;> simp
  have hbar : ((g : GL (HypIndex 2 0) mk.field) :
      Matrix (HypIndex 2 0) (HypIndex 2 0) mk.field).map sigma =
      ((g : GL (HypIndex 2 0) mk.field) :
        Matrix (HypIndex 2 0) (HypIndex 2 0) mk.field).map (burnsideF4gU4_fieldData mk).bar := by
    ext a b
    simp only [Matrix.map_apply, hsig, (burnsideF4gU4_fieldData mk).bar_apply]
  apply Units.ext
  have hT := burnsideF4gU4_coe_T mk g
  have hT' := burnsideF4gU4_coe_T mk (frobElt (burnsideF4gU4_fieldData mk) g)
  rw [coe_frobElt, ← hbar, hRinv, hRP] at hT'
  rw [hRinv, hRP] at hT
  change (mk.basis : Matrix (Fin 4) (Fin 4) mk.field) *
      ((((mk.basis⁻¹ : GL (Coord .U4) mk.field) : Matrix (Fin 4) (Fin 4) mk.field) *
        (((burnsideF4gU4_T mk g : nativeGroup .U4 (2 ^ f) mk.field) : GL (Coord .U4) mk.field) :
          Matrix (Fin 4) (Fin 4) mk.field) *
        (mk.basis : Matrix (Fin 4) (Fin 4) mk.field)).map sigma) *
      ((mk.basis⁻¹ : GL (Coord .U4) mk.field) : Matrix (Fin 4) (Fin 4) mk.field) = _
  rw [hT, hT']
  exact burnsideF429a_matrix_frob sigma _ _ hBiBm _ _ hPs hQs _

theorem burnsideF429a_U4_payload_eq {E : Type} [Group E] {Gp M₁ M₂ : Subgroup E}
    (hyp : HypF_4_4g .U4 2 f Gp M₁ M₂) :
    ∃ mk : Marking .U4 2 f ↥Gp,
      hyp.chart.coordinatePayload = NativeCoordinates.classical .U4 rfl mk ∧
      Gp ⊓ M₁ = (mk.parabolic false).map Gp.subtype ∧
      Gp ⊓ M₂ = (mk.parabolic true).map Gp.subtype := by
  have hfits := hyp.chart.coordinatePayload_fits
  have hm := hyp.chart_matches
  generalize hcp : hyp.chart.coordinatePayload = cp at hfits
  cases cp with
  | classical c hk mk =>
    obtain rfl : c = .U4 := by
      cases c <;> first | rfl | exact absurd hk (by decide)
    obtain ⟨-, hpts, hlns, -, -⟩ := hfits
    refine ⟨mk, rfl, ?_, ?_⟩
    · rw [hm.2.1]
      exact hpts
    · rw [hm.2.2]
      exact hlns
  | g2 kind_eq => exact absurd kind_eq (by decide)
  | g2Derived kind_eq => exact absurd kind_eq (by decide)
  | triality kind_eq => exact absurd kind_eq (by decide)
  | ree kind_eq => exact absurd kind_eq (by decide)
  | tits kind_eq => exact absurd kind_eq (by decide)

theorem burnsideF429a_U4_subgroupOf_eq {E : Type} [Group E] {Gp M : Subgroup E}
    (mk : Marking .U4 2 f ↥Gp) {b : Bool} (hM : Gp ⊓ M = (mk.parabolic b).map Gp.subtype) :
    M.subgroupOf Gp = (if b then parP2 (burnsideF4gU4_fieldData mk)
      else parP (burnsideF4gU4_fieldData mk)).map (burnsideF4gU4_Phi mk).toMonoidHom := by
  have e : M.subgroupOf Gp = mk.parabolic b := by
    rw [← Subgroup.inf_subgroupOf_left M Gp, hM]
    exact Subgroup.comap_map_eq_self_of_injective Gp.subtype_injective _
  rw [e]
  cases b
  · show (nativeParabolic .U4 (2 ^ f) mk.field mk.basis false).map mk.transport = _
    rw [burnsideF4gU4_parabolic_false, Subgroup.map_map, burnsideF4gU4_Phi_toMonoidHom]
    rfl
  · show (nativeParabolic .U4 (2 ^ f) mk.field mk.basis true).map mk.transport = _
    rw [burnsideF4gU4_parabolic_true, Subgroup.map_map, burnsideF4gU4_Phi_toMonoidHom]
    rfl

theorem burnsideF429a_U4_rep_action {E : Type} [Group E] {Gp : Subgroup E}
    (mk : Marking .U4 2 f ↥Gp) {t : E} (a : hypSU (burnsideF4gU4_fieldData mk) 2 0)
    (ha : ∀ x, ((burnsideF4gU4_Phi mk (a * frobElt (burnsideF4gU4_fieldData mk) x * a⁻¹) :
      ↥Gp) : E) = t * ((burnsideF4gU4_Phi mk (a * x * a⁻¹) : ↥Gp) : E) * t⁻¹)
    (A : nativeGroup .U4 (2 ^ f) mk.field) :
    ∃ B : nativeGroup .U4 (2 ^ f) mk.field,
      (B : GL (Coord .U4) mk.field) = mk.basis *
        Matrix.GeneralLinearGroup.map (burnsideF4gU4_fieldData mk).bar
          (mk.basis⁻¹ * (A : GL (Coord .U4) mk.field) * mk.basis) * mk.basis⁻¹ ∧
      ((MulAut.conj (burnsideF4gU4_Phi mk a) (mk.transport B) : ↥Gp) : E) =
        t * ((MulAut.conj (burnsideF4gU4_Phi mk a) (mk.transport A) : ↥Gp) : E) * t⁻¹ := by
  have hPhi : ∀ g, burnsideF4gU4_Phi mk g = mk.transport (burnsideF4gU4_T mk g) := fun g =>
    congrArg (fun φ : hypSU (burnsideF4gU4_fieldData mk) 2 0 →* ↥Gp => φ g)
      (burnsideF4gU4_Phi_toMonoidHom mk)
  obtain ⟨x, rfl⟩ := (burnsideF4gU4_T mk).surjective A
  refine ⟨burnsideF4gU4_T mk (frobElt _ x),
    (burnsideF429a_U4_T_frob mk _ (burnsideF4gU4_fieldData mk).bar_apply x).symm, ?_⟩
  rw [← hPhi, ← hPhi, MulAut.conj_apply, MulAut.conj_apply, ← map_inv, ← map_mul, ← map_mul,
    ← map_mul, ← map_mul]
  exact ha x

theorem burnsideF429a_U4_innerDiagonal {E : Type} [Group E] {Gp : Subgroup E}
    (mk : Marking .U4 2 f ↥Gp) (a : hypSU (burnsideF4gU4_fieldData mk) 2 0) :
    (NativeCoordinates.classical .U4 rfl mk : NativeCoordinates .U4 2 f ↥Gp).InnerDiagonal
      (MulAut.conj (burnsideF4gU4_Phi mk a)) := by
  have hPhi : ∀ g, burnsideF4gU4_Phi mk g = mk.transport (burnsideF4gU4_T mk g) := fun g =>
    congrArg (fun φ : hypSU (burnsideF4gU4_fieldData mk) 2 0 →* ↥Gp => φ g)
      (burnsideF4gU4_Phi_toMonoidHom mk)
  refine ⟨(burnsideF4gU4_T mk a : GL (Coord .U4) mk.field), ?_, fun rep => ?_⟩
  · exact Subgroup.mem_normalizer_iff_map_conj_eq.mp
      (Subgroup.le_normalizer (burnsideF4gU4_T mk a).2)
  · refine ⟨burnsideF4gU4_T mk a * rep * (burnsideF4gU4_T mk a)⁻¹, rfl, ?_⟩
    rw [map_mul, map_mul, map_inv, ← hPhi]
    rfl

theorem burnsideF429a_U4_graphAction {E : Type} [Group E] {Gp : Subgroup E}
    (mk : Marking .U4 2 f ↥Gp) {t : E} (a : hypSU (burnsideF4gU4_fieldData mk) 2 0)
    (ha : ∀ x, ((burnsideF4gU4_Phi mk (a * frobElt (burnsideF4gU4_fieldData mk) x * a⁻¹) :
      ↥Gp) : E) = t * ((burnsideF4gU4_Phi mk (a * x * a⁻¹) : ↥Gp) : E) * t⁻¹) :
    (NativeCoordinates.classical .U4 rfl mk : NativeCoordinates .U4 2 f ↥Gp).GraphAction t :=
  ⟨MulAut.conj (burnsideF4gU4_Phi mk a), burnsideF429a_U4_innerDiagonal mk a,
    Or.inl rfl, (burnsideF4gU4_fieldData mk).bar, (burnsideF4gU4_fieldData mk).bar_apply,
    burnsideF429a_U4_rep_action mk a ha⟩

theorem burnsideF429a_U4_payload {E : Type} [Group E] {Gp M₁ M₂ : Subgroup E}
    (hyp : HypF_4_4g .U4 2 f Gp M₁ M₂) :
    ∃ mk : Marking .U4 2 f ↥Gp,
      M₁.subgroupOf Gp = (parP (burnsideF4gU4_fieldData mk)).map
        (burnsideF4gU4_Phi mk).toMonoidHom ∧
      M₂.subgroupOf Gp = (parP2 (burnsideF4gU4_fieldData mk)).map
        (burnsideF4gU4_Phi mk).toMonoidHom ∧
      ∀ t : E, t ∉ Gp → t * t = 1 → ∀ a : hypSU (burnsideF4gU4_fieldData mk) 2 0,
        (∀ x, ((burnsideF4gU4_Phi mk (a * frobElt (burnsideF4gU4_fieldData mk) x * a⁻¹) :
          ↥Gp) : E) = t * ((burnsideF4gU4_Phi mk (a * x * a⁻¹) : ↥Gp) : E) * t⁻¹) →
        hyp.chart.IsGraphInv t := by
  obtain ⟨mk, hcp, h1, h2⟩ := burnsideF429a_U4_payload_eq hyp
  refine ⟨mk, burnsideF429a_U4_subgroupOf_eq mk h1, burnsideF429a_U4_subgroupOf_eq mk h2,
    fun t htG ht2 a ha => ?_⟩
  have key : hyp.chart.IsGraphInv t ↔
      t ∉ Gp ∧ t * t = 1 ∧ 0 < f ∧ hyp.chart.coordinatePayload.GraphAction t := Iff.rfl
  rw [key, hcp]
  exact ⟨htG, ht2, mk.exponent_pos, burnsideF429a_U4_graphAction mk a ha⟩

end Transport

section Model

open Matrix CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
  CFSG.Quasithin.H13.U4Par CFSG.Quasithin.H13.Sec53F.Unit CFSG.ASVolI.ChF CFSG.Open
  CFSG.Quasithin

theorem burnsideF429a_U4_graph_elt {E : Type} [Group E] [Finite E] {Gp M₁ M₂ : Subgroup E}
    [Gp.Normal] (hc : Subgroup.centralizer (Gp : Set E) = ⊥)
    (hsplit : ∀ e : E, ∃ n ∈ Gp, ∃ x ∈ M₁ ⊓ M₂, e = n * x)
    {m : ℕ} {K : Type} [Field K] (h : UnitaryFieldData 2 m K) (Φ : hypSU h 2 0 ≃* ↥Gp)
    (hP₁ : M₁.subgroupOf Gp = (parP h).map Φ.toMonoidHom)
    (hP₂ : M₂.subgroupOf Gp = (parP2 h).map Φ.toMonoidHom)
    (hev : ¬ Odd Gp.index) {T : Subgroup E} (hT : ChF.IsSylowOf 2 T (M₁ ⊓ M₂)) :
    ∃ t ∈ T, t ∉ Gp ∧ t * t = 1 ∧ ∃ a ∈ parP h, ∀ x : hypSU h 2 0,
      ((Φ (a * frobElt h x * a⁻¹) : ↥Gp) : E) = t * ((Φ (a * x * a⁻¹) : ↥Gp) : E) * t⁻¹ := by
  have := h.finite
  set φ : hypSU h 2 0 →* E := Gp.subtype.comp Φ.toMonoidHom with hφdef
  have hφ : Function.Injective φ := Gp.subtype_injective.comp Φ.injective
  have hφx : ∀ x, φ x = ((Φ x : ↥Gp) : E) := fun x => rfl
  have hB : (M₁ ⊓ M₂).subgroupOf Gp = (parP h ⊓ parP2 h).map Φ.toMonoidHom := by
    rw [burnsideF429a_subgroupOf_inf, hP₁, hP₂, Subgroup.map_inf_eq _ _ _ Φ.injective]
  have hGB : Gp ⊓ (M₁ ⊓ M₂) = (parP h ⊓ parP2 h).map φ := burnsideF429_inf_eq_map Φ hB
  obtain ⟨t, htT, htG, ht2⟩ := burnsideF429a_exists_two_elt_not_mem hsplit hT hev
  have htM : t ∈ M₁ ⊓ M₂ := hT.1 htT
  obtain ⟨g, hg, τ, hgτ⟩ := burnsideF429a_U4_nf h Φ hP₁ hP₂ htM
  have hτ1 : τ ≠ 1 := by
    rintro rfl
    apply htG
    have e1 : ∀ x, ((Φ (g * x * g⁻¹) : ↥Gp) : E) = t * ((Φ x : ↥Gp) : E) * t⁻¹ := by
      intro x
      have := hgτ x
      rwa [fieldAut_apply, fieldHom_one] at this
    rw [burnsideF429a_eq_of_conj hc Φ e1]
    exact (Φ g).2
  have hτ2 : τ * τ = 1 := by
    obtain ⟨w, hw⟩ : ∃ w : hypSU h 2 0, φ w = t * t := ⟨Φ.symm ⟨t * t, ht2⟩, by simp [hφx]⟩
    apply burnsideF429a_U4_fieldAut_eq_one_of_inner h
    refine ⟨(g * fieldAut h τ g)⁻¹ * w, MulEquiv.ext fun x => ?_⟩
    have e1 : φ (g * fieldAut h τ (g * fieldAut h τ x * g⁻¹) * g⁻¹) = φ (w * x * w⁻¹) := by
      rw [hφx, hgτ, hgτ, map_mul, map_mul, map_inv, hw, hφx]
      group
    have e2 := hφ e1
    rw [map_mul, map_mul, map_inv] at e2
    have e3 : fieldAut h (τ * τ) x = fieldAut h τ (fieldAut h τ x) := fieldHom_mul h τ τ x
    show (g * fieldAut h τ g)⁻¹ * w * x * ((g * fieldAut h τ g)⁻¹ * w)⁻¹ = fieldAut h (τ * τ) x
    rw [e3]
    calc (g * fieldAut h τ g)⁻¹ * w * x * ((g * fieldAut h τ g)⁻¹ * w)⁻¹
        = (g * fieldAut h τ g)⁻¹ * (w * x * w⁻¹) * (g * fieldAut h τ g) := by group
      _ = (g * fieldAut h τ g)⁻¹ * (g * (fieldAut h τ g * fieldAut h τ (fieldAut h τ x) *
          (fieldAut h τ g)⁻¹) * g⁻¹) * (g * fieldAut h τ g) := by rw [← e2]
      _ = fieldAut h τ (fieldAut h τ x) := by group
  have hτb : ∀ c, τ c = h.bar c := by
    rcases UnitaryHigher.ringEquiv_eq_refl_or_bar h hτ2 with h1 | h1
    · exact absurd h1 hτ1
    · exact h1
  set y : E := (φ g)⁻¹ * t with hydef
  have hgB : g ∈ parP h ⊓ parP2 h := burnsideF429a_U4_normalizer_le_borel h hg
  have hφg : φ g ∈ M₁ ⊓ M₂ := by
    have : φ g ∈ Gp ⊓ (M₁ ⊓ M₂) := by rw [hGB]; exact ⟨g, hgB, rfl⟩
    exact this.2
  have hyM : y ∈ M₁ ⊓ M₂ := (M₁ ⊓ M₂).mul_mem ((M₁ ⊓ M₂).inv_mem hφg) htM
  have hyact : ∀ x, φ (frobElt h x) = y * φ x * y⁻¹ := by
    intro x
    have e1 := hgτ x
    rw [burnsideF429a_U4_fieldAut_eq_frob h hτb] at e1
    rw [← hφx, ← hφx, map_mul, map_mul, map_inv] at e1
    rw [hydef]
    calc φ (frobElt h x) = (φ g)⁻¹ * (φ g * φ (frobElt h x) * (φ g)⁻¹) * φ g := by group
      _ = (φ g)⁻¹ * t * φ x * ((φ g)⁻¹ * t)⁻¹ := by rw [e1]; group
  have hyG : y ∉ Gp := by
    intro hy
    apply htG
    have : t = φ g * y := by rw [hydef]; group
    rw [this]
    exact Gp.mul_mem (Φ g).2 hy
  have hy2 : y ^ 2 ^ 1 = 1 := by
    have hcent : y * y ∈ Subgroup.centralizer (Gp : Set E) := by
      rw [Subgroup.mem_centralizer_iff]
      intro z hz
      obtain ⟨x, rfl⟩ : ∃ x, φ x = z := ⟨Φ.symm ⟨z, hz⟩, by simp [hφx]⟩
      have e1 : φ x = y * y * φ x * (y * y)⁻¹ := by
        have := hyact (frobElt h x)
        rw [frobElt_frobElt, hyact x] at this
        calc φ x = y * (y * φ x * y⁻¹) * y⁻¹ := this
          _ = y * y * φ x * (y * y)⁻¹ := by group
      calc φ x * (y * y) = (y * y * φ x * (y * y)⁻¹) * (y * y) := by rw [← e1]
        _ = y * y * φ x := by group
    rw [hc, Subgroup.mem_bot] at hcent
    rw [pow_one, pow_two]
    exact hcent
  have hyy : y * y = 1 := by
    rw [← pow_two]
    simpa using hy2
  obtain ⟨p, hp, hle⟩ := F7.isSylowTwoOf_exists_conj_le hT
    ((Subgroup.zpowers_le (H := M₁ ⊓ M₂)).mpr hyM) (isPGroup_zpowers_of_pow hy2)
  have hy'T : p⁻¹ * y * p ∈ T := mem_conjSub.1 (hle (Subgroup.mem_zpowers y))
  have hy'G : p⁻¹ * y * p ∉ Gp := by
    intro h'
    apply hyG
    have := (inferInstance : Gp.Normal).conj_mem _ h' p
    simpa [mul_assoc] using this
  have hy'2 : p⁻¹ * y * p * (p⁻¹ * y * p) = 1 := by
    calc p⁻¹ * y * p * (p⁻¹ * y * p) = p⁻¹ * (y * y) * p := by group
      _ = 1 := by rw [hyy]; group
  obtain ⟨gp, hgp, τp, hgτp⟩ := burnsideF429a_U4_nf h Φ hP₁ hP₂ hp
  have hgpP : gp ∈ parP h := burnsideF429a_U4_normalizer_le_parP h hgp
  set a := fieldAut h τp⁻¹ gp⁻¹ with hadef
  have haP : a ∈ parP h := burnsideF429a_U4_fieldAut_mem_parP h τp⁻¹ ((parP h).inv_mem hgpP)
  have hτa : fieldAut h τp a = gp⁻¹ := by
    rw [hadef, fieldAut_apply, fieldAut_apply, ← fieldHom_mul, mul_inv_cancel, fieldHom_one]
  have hkey : ∀ w, φ (fieldAut h τp w) = p * φ (a * w * a⁻¹) * p⁻¹ := by
    intro w
    have hinner : gp * fieldAut h τp (a * w * a⁻¹) * gp⁻¹ = fieldAut h τp w := by
      rw [map_mul, map_mul, map_inv, hτa]
      group
    rw [hφx, hφx, ← hgτp (a * w * a⁻¹), hinner]
  refine ⟨p⁻¹ * y * p, hy'T, hy'G, hy'2, a, haP, fun x => ?_⟩
  have e1 : p * φ (a * x * a⁻¹) * p⁻¹ = φ (fieldAut h τp x) := (hkey x).symm
  have e2 : y * φ (fieldAut h τp x) * y⁻¹ = φ (frobElt h (fieldAut h τp x)) :=
    (hyact _).symm
  have e3 : frobElt h (fieldAut h τp x) = fieldAut h τp (frobElt h x) :=
    (burnsideF429a_U4_fieldAut_frobElt h τp x).symm
  have e4 : φ (fieldAut h τp (frobElt h x)) = p * φ (a * frobElt h x * a⁻¹) * p⁻¹ := hkey _
  rw [← hφx, ← hφx]
  calc φ (a * frobElt h x * a⁻¹) = p⁻¹ * (p * φ (a * frobElt h x * a⁻¹) * p⁻¹) * p := by group
    _ = p⁻¹ * (y * (p * φ (a * x * a⁻¹) * p⁻¹) * y⁻¹) * p := by rw [← e4, ← e3, ← e2, e1]
    _ = p⁻¹ * y * p * φ (a * x * a⁻¹) * (p⁻¹ * y * p)⁻¹ := by group

theorem burnsideF429a_U4_corr_O2 {E : Type} [Group E] [Finite E] {Gp M₁ M₂ : Subgroup E}
    [Gp.Normal] (hc : Subgroup.centralizer (Gp : Set E) = ⊥)
    {m : ℕ} {K : Type} [Field K] (h : UnitaryFieldData 2 m K) (Φ : hypSU h 2 0 ≃* ↥Gp)
    (hP₁ : M₁.subgroupOf Gp = (parP h).map Φ.toMonoidHom)
    (hP₂ : M₂.subgroupOf Gp = (parP2 h).map Φ.toMonoidHom)
    {T : Subgroup E} (hT : ChF.IsSylowOf 2 T (M₁ ⊓ M₂)) {t : E} (htT : t ∈ T) (htG : t ∉ Gp)
    (ht2 : t * t = 1) {a : hypSU h 2 0} (haP : a ∈ parP h)
    (hta : ∀ x : hypSU h 2 0, ((Φ (a * frobElt h x * a⁻¹) : ↥Gp) : E) =
      t * ((Φ (a * x * a⁻¹) : ↥Gp) : E) * t⁻¹) :
    (pCoreOf 2 (oPPrime 2 (Gp ⊓ M₁))).relIndex (pCoreOf 2 (oPPrime 2 (Gp ⊓ M₁) ⊔ T)) = 2 ∧
      pCoreOf 2 (oPPrime 2 (Gp ⊓ M₁) ⊔ T) =
        pCoreOf 2 (oPPrime 2 (Gp ⊓ M₁)) ⊔ Subgroup.zpowers t := by
  have := h.finite
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set φ : hypSU h 2 0 →* E := Gp.subtype.comp Φ.toMonoidHom with hφdef
  have hφ : Function.Injective φ := Gp.subtype_injective.comp Φ.injective
  have hφx : ∀ x, φ x = ((Φ x : ↥Gp) : E) := fun x => rfl
  have hG₁ : Gp ⊓ M₁ = (parP h).map φ := burnsideF429_inf_eq_map Φ hP₁
  have hL : oPPrime 2 (Gp ⊓ M₁) = (oPPrime 2 (parP h)).map φ := by
    rw [hG₁, burnsideF4gU4Inv_oPPrime_map hφ]
  have hSG : ChF.IsSylowOf 2 (pCoreOf 2 (Gp ⊓ (M₁ ⊓ M₂))) Gp :=
    burnsideF429a_U4_sylow_of_model h Φ hP₁ hP₂
  obtain ⟨hST, hTinf⟩ := burnsideF429a_T_inf_Gp hSG hT
  set S := pCoreOf 2 (Gp ⊓ (M₁ ⊓ M₂)) with hSdef
  set L := oPPrime 2 (Gp ⊓ M₁) with hLdef
  set Q : Subgroup E := (radQ h).map φ with hQdef
  have hOL : pCoreOf 2 L = Q := by
    rw [hL, CFSG.Quasithin.H13.U4Par.pCoreOf_map_of_inj hφ,
      burnsideF429a_U4_pCoreOf_oPPrime_eq h]
  have hta' : ∀ x, t * φ x * t⁻¹ = φ (a * frobElt h (a⁻¹ * x * a) * a⁻¹) := by
    intro x
    have e := hta (a⁻¹ * x * a)
    rw [← hφx, ← hφx] at e
    rw [e]
    congr 2
    group
  have hSGM : S ≤ Gp ⊓ M₁ :=
    (CFSG.LieType.BorelTits.pCoreOf_le 2 _).trans (inf_le_inf_left _ inf_le_left)
  have hSyl : ChF.IsSylowOf 2 S (Gp ⊓ M₁) := burnsideF429_isSylowOf_of_le hSG hSGM inf_le_left
  have hSL : S ≤ L := burnsideF429a_sbar_le_oPPrime hSGM
  have hLP : L ≤ Gp ⊓ M₁ := burnsideF429a_oPPrime_le _
  have hSylL : ChF.IsSylowOf 2 S L := burnsideF429_isSylowOf_of_le hSyl hSL hLP
  have hTP : T ≤ Subgroup.normalizer ((Gp ⊓ M₁ : Subgroup E) : Set E) := by
    intro s hs
    have hsM : s ∈ M₁ := (hT.1 hs).1
    rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · rintro ⟨hxG, hxM⟩
      exact ⟨(inferInstance : Gp.Normal).conj_mem x hxG s,
        M₁.mul_mem (M₁.mul_mem hsM hxM) (M₁.inv_mem hsM)⟩
    · rintro ⟨hxG, hxM⟩
      refine ⟨?_, ?_⟩
      · have := (inferInstance : Gp.Normal).conj_mem _ hxG s⁻¹
        simpa [mul_assoc] using this
      · have := M₁.mul_mem (M₁.mul_mem (M₁.inv_mem hsM) hxM) hsM
        simpa [mul_assoc] using this
  have hTL : T ≤ Subgroup.normalizer ((L : Subgroup E) : Set E) :=
    burnsideF429a_le_normalizer_oPPrime hTP
  have hLT : L ⊓ T = S := by
    refine le_antisymm (fun x hx => ?_) (le_inf hSL hST)
    rw [← hTinf]
    exact ⟨hx.2, (hLP hx.1).1⟩
  have hTsyl : ChF.IsSylowOf 2 T (L ⊔ T) := by
    refine ⟨le_sup_right, hT.2.1, ?_⟩
    rw [burnsideF429a_relIndex_sup hTL, hLT]
    exact hSylL.2.2
  set R := pCoreOf 2 (L ⊔ T) with hRdef
  have hRT : R ≤ T := F7.isSylowTwoOf_pCoreOf_le hTsyl
  have hRnorm : L ⊔ T ≤ Subgroup.normalizer ((R : Subgroup E) : Set E) :=
    CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 _
  have hRL : R ⊓ L ≤ pCoreOf 2 L := by
    refine CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 inf_le_right ?_
      ((CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _).to_le inf_le_left)
    intro l hl
    rw [Subgroup.mem_normalizer_iff]
    intro x
    have h1 := Subgroup.mem_normalizer_iff.1 (hRnorm (Subgroup.mem_sup_left hl)) x
    constructor
    · rintro ⟨hxR, hxL⟩
      exact ⟨h1.1 hxR, L.mul_mem (L.mul_mem hl hxL) (L.inv_mem hl)⟩
    · rintro ⟨hxR, hxL⟩
      refine ⟨h1.2 hxR, ?_⟩
      have := L.mul_mem (L.mul_mem (L.inv_mem hl) hxL) hl
      simpa [mul_assoc] using this
  have hOR : pCoreOf 2 L ≤ R := by
    refine CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2
      ((CFSG.LieType.BorelTits.pCoreOf_le 2 _).trans le_sup_left) ?_
      (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _)
    exact sup_le (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 _)
      (hTL.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 _))
  have hQconj : ∀ e ∈ M₁ ⊓ M₂, ∀ q ∈ Q, e * q * e⁻¹ ∈ Q := by
    rintro e he _ ⟨q, hq, rfl⟩
    obtain ⟨g, hg, τ, hgτ⟩ := burnsideF429a_U4_nf h Φ hP₁ hP₂ he
    rw [hφx, ← hgτ q]
    refine ⟨g * fieldAut h τ q * g⁻¹, ?_, rfl⟩
    exact (Subgroup.mem_normalizer_iff.mp (parP_le_normalizer_radQ h
      (burnsideF429a_U4_normalizer_le_parP h hg)) _).mp (burnsideF429a_U4_fieldAut_mem_radQ h τ hq)
  have hQn : ∀ e ∈ M₁ ⊓ M₂, e ∈ Subgroup.normalizer (Q : Set E) := by
    intro e he
    rw [Subgroup.mem_normalizer_iff]
    intro q
    refine ⟨hQconj e he q, fun hq => ?_⟩
    have := hQconj e⁻¹ ((M₁ ⊓ M₂).inv_mem he) _ hq
    simpa [mul_assoc] using this
  have hTQ : T ≤ Subgroup.normalizer (Q : Set E) := fun s hs => hQn s (hT.1 hs)
  have hLQ : L ≤ Subgroup.normalizer (Q : Set E) := by
    rw [hL]
    rintro _ ⟨l, hl, rfl⟩
    exact Subgroup.le_normalizer_map φ (Subgroup.map_mono (parP_le_normalizer_radQ h)
      ⟨l, burnsideF429a_oPPrime_le _ hl, rfl⟩)
  have hQ2 : IsPGroup 2 Q := (radQ_isPGroup h).map φ
  have hZ : ∀ x ∈ L, (∀ l ∈ L, x * l * x⁻¹ * l⁻¹ ∈ Q) → x ∈ Q := by
    intro x hx hxc
    rw [hL] at hx
    obtain ⟨x', hx', rfl⟩ := hx
    refine ⟨x', burnsideF429a_U4_mem_radQ_of_comm h hx' fun l hl => ?_, rfl⟩
    have h1 := hxc (φ l) (by rw [hL]; exact ⟨l, hl, rfl⟩)
    rw [← map_inv, ← map_inv, ← map_mul, ← map_mul, ← map_mul] at h1
    exact (Subgroup.mem_map_iff_mem hφ).mp h1
  have hPn : parP h ≤ Subgroup.normalizer ((oPPrime 2 (parP h) : Subgroup _) : Set _) :=
    burnsideF429a_le_normalizer_oPPrime Subgroup.le_normalizer
  have htc : ∀ l ∈ L, t * l * t⁻¹ * l⁻¹ ∈ Q := by
    intro l hl
    rw [hL] at hl
    obtain ⟨l', hl', rfl⟩ := hl
    have hw : a⁻¹ * l' * a ∈ oPPrime 2 (parP h) := by
      have := (Subgroup.mem_normalizer_iff.mp (hPn ((parP h).inv_mem haP)) l').mp hl'
      simpa using this
    rw [hta', ← map_inv, ← map_mul]
    refine ⟨a * (frobElt h (a⁻¹ * l' * a) * (a⁻¹ * l' * a)⁻¹) * a⁻¹, ?_, ?_⟩
    · exact (Subgroup.mem_normalizer_iff.mp (parP_le_normalizer_radQ h haP) _).mp
        (burnsideF429a_U4_frob_mul_inv_mem_radQ h hw)
    · congr 1
      group
  have htR : t ∈ R := burnsideF429a_mem_pCoreOf_sup hTL hTQ hLQ hQ2 hT.2.1 hZ htT htc
  have hfin : ∀ v ∈ R, v ∈ Gp → v ∈ Q := by
    intro v hvR hvG
    rw [← hOL]
    refine hRL ⟨hvR, hSL ?_⟩
    rw [← hTinf]
    exact ⟨hRT hvR, hvG⟩
  have hup : R ≤ Q ⊔ Subgroup.zpowers t := by
    intro u hu
    have huT : u ∈ T := hRT hu
    have huM : u ∈ M₁ ⊓ M₂ := hT.1 huT
    obtain ⟨gu, hgu, τu, hgτu⟩ := burnsideF429a_U4_nf h Φ hP₁ hP₂ huM
    have hguP : gu ∈ parP h := burnsideF429a_U4_normalizer_le_parP h hgu
    have hcu : ∀ l ∈ L, u * l * u⁻¹ * l⁻¹ ∈ Q := by
      intro l hl
      rw [← hOL]
      refine hRL ⟨?_, ?_⟩
      · have hb : l * u⁻¹ * l⁻¹ ∈ R :=
          (Subgroup.mem_normalizer_iff.1 (hRnorm (Subgroup.mem_sup_left hl)) _).1 (R.inv_mem hu)
        have := R.mul_mem hu hb
        simpa [mul_assoc] using this
      · exact L.mul_mem ((Subgroup.mem_normalizer_iff.1 (hTL huT) l).1 hl) (L.inv_mem hl)
    have hmod : ∀ l ∈ oPPrime 2 (parP h), gu * fieldAut h τu l * gu⁻¹ * l⁻¹ ∈ radQ h := by
      intro l hl
      have h1 := hcu (φ l) (by rw [hL]; exact ⟨l, hl, rfl⟩)
      have e : u * φ l * u⁻¹ * (φ l)⁻¹ = φ (gu * fieldAut h τu l * gu⁻¹ * l⁻¹) := by
        rw [map_mul, map_inv, hφx (gu * fieldAut h τu l * gu⁻¹), hgτu l, hφx l]
      rw [e] at h1
      exact (Subgroup.mem_map_iff_mem hφ).mp h1
    rcases burnsideF429a_U4_refl_or_bar h hguP hmod with hτ | hτ
    ·
      have e1 : ∀ x, ((Φ (gu * x * gu⁻¹) : ↥Gp) : E) = u * ((Φ x : ↥Gp) : E) * u⁻¹ := by
        intro x
        have := hgτu x
        have hid : fieldAut h τu x = x := by
          rw [hτ]
          exact fieldHom_one h x
        rwa [hid] at this
      have huG : u ∈ Gp := by
        rw [burnsideF429a_eq_of_conj hc Φ e1]
        exact (Φ gu).2
      exact Subgroup.mem_sup_left (hfin u hu huG)
    ·
      have hf : ∀ y z : hypSU h 2 0, frobElt h (y * z) = frobElt h y * frobElt h z :=
        fun y z => map_mul (frob h) y z
      have hfi : ∀ y : hypSU h 2 0, frobElt h y⁻¹ = (frobElt h y)⁻¹ := fun y => map_inv (frob h) y
      set n := gu * frobElt h a * a⁻¹ with hn
      have e1 : ∀ x, ((Φ (n * x * n⁻¹) : ↥Gp) : E) = (u * t) * ((Φ x : ↥Gp) : E) * (u * t)⁻¹ := by
        intro x
        rw [← hφx, ← hφx]
        have e2 : n * x * n⁻¹ = gu * fieldAut h τu (a * frobElt h (a⁻¹ * x * a) * a⁻¹) * gu⁻¹ := by
          rw [burnsideF429a_U4_fieldAut_eq_frob h hτ]
          simp only [hf, hfi, frobElt_frobElt, hn]
          group
        calc φ (n * x * n⁻¹)
            = φ (gu * fieldAut h τu (a * frobElt h (a⁻¹ * x * a) * a⁻¹) * gu⁻¹) := by rw [e2]
          _ = u * φ (a * frobElt h (a⁻¹ * x * a) * a⁻¹) * u⁻¹ := hgτu _
          _ = u * (t * φ x * t⁻¹) * u⁻¹ := by rw [hta']
          _ = (u * t) * φ x * (u * t)⁻¹ := by group
      have hutG : u * t ∈ Gp := by
        rw [burnsideF429a_eq_of_conj hc Φ e1]
        exact (Φ n).2
      have hutQ := hfin (u * t) (R.mul_mem hu htR) hutG
      have e2 : u = (u * t) * t := by rw [mul_assoc, ht2, mul_one]
      rw [e2]
      exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hutQ)
        (Subgroup.mem_sup_right (Subgroup.mem_zpowers t))
  have heq : R = pCoreOf 2 L ⊔ Subgroup.zpowers t := by
    apply le_antisymm
    · rw [hOL]
      exact hup
    · exact sup_le hOR ((Subgroup.zpowers_le (H := R)).mpr htR)
  refine ⟨?_, heq⟩
  rw [heq]
  refine burnsideF429a_relIndex_sup_zpowers ?_ ?_ ht2
  · exact CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 _ (hTL htT)
  · intro htO
    exact htG (hLP (CFSG.LieType.BorelTits.pCoreOf_le 2 L htO)).1

end Model

section Main

open CFSG.Open CFSG.ASVolI.ChF CFSG.Quasithin CFSG.Quasithin.H13.U4Par

theorem burnsideF429a_c5corr_U4 {f : ℕ} {E : Type} [Group E] {Gp M₁ M₂ : Subgroup E}
    (hyp : HypF_4_4 .U4 2 f Gp M₁ M₂) (hev : ¬ Odd Gp.index) {T : Subgroup E}
    (hT : ChF.IsSylowOf 2 T (M₁ ⊓ M₂)) : burnsideF429_C5corr .U4 Gp M₁ M₂ hyp T := by
  haveI := hyp.finite
  haveI := hyp.normal
  obtain ⟨mk, hP₁, hP₂, hG⟩ := burnsideF429a_U4_payload hyp.toHypF_4_4g
  obtain ⟨t, htT, htG, ht2, a, haP, hta⟩ := burnsideF429a_U4_graph_elt hyp.centralizer_trivial
    hyp.split _ (burnsideF4gU4_Phi mk) hP₁ hP₂ hev hT
  obtain ⟨hr, heq⟩ := burnsideF429a_U4_corr_O2 hyp.centralizer_trivial _ (burnsideF4gU4_Phi mk)
    hP₁ hP₂ hT htT htG ht2 haP hta
  have hgen := burnsideF429a_inf_sup_inf_eq hyp.gen hyp.split
  have htM := hT.1 htT
  have htN : t ∈ Subgroup.normalizer (Gp : Set E) := by
    rw [Subgroup.mem_normalizer_iff]
    intro x
    exact ⟨fun hx => hyp.normal.conj_mem x hx t, fun hx => by
      have := hyp.normal.conj_mem _ hx t⁻¹
      simpa [mul_assoc] using this⟩
  refine Or.inr ⟨rfl, Gp ⊔ Subgroup.zpowers t, le_sup_left,
    burnsideF429a_relIndex_sup_zpowers htN htG ht2, ?_, t, htT,
    Subgroup.mem_sup_right (Subgroup.mem_zpowers t), hG t htG ht2 a hta, hr, heq,
    burnsideF429a_r5_line hyp hev hT⟩
  refine le_antisymm (sup_le inf_le_left inf_le_left) (sup_le ?_ ?_)
  · calc Gp = (Gp ⊓ M₁) ⊔ (Gp ⊓ M₂) := hgen.symm
      _ ≤ _ := sup_le_sup (inf_le_inf_right _ le_sup_left) (inf_le_inf_right _ le_sup_left)
  · rw [Subgroup.zpowers_le]
    exact Subgroup.mem_sup_left ⟨Subgroup.mem_sup_right (Subgroup.mem_zpowers t), htM.1⟩

end Main

end CFSG.ASVolI
