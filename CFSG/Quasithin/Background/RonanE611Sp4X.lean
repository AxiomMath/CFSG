module

public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_2BorelSp4
public import CFSG.Quasithin.Background.ONanE68Sp4Roots

public section

namespace CFSG.Quasithin.RonanE611

open Matrix CFSG.ComponentClassification.UnbalancedCatalog.SpChain CFSG.QuasithinUnique.Setup.X7b
  CFSG.Quasithin.SteinbergBS CFSG.Quasithin.E6.E68Proof CFSG.Quasithin.E6.E68Proof.Sp4
  CFSG.RankThree.PartOne.KCRootAxis

namespace Sp4X

section Dichotomy

variable {K : Type} [Field K] [Finite K] [CharP K 2]

theorem uElt_center_mul (b c : K) : uElt (0 : K) b c 0 = uElt 0 b 0 0 * uElt 0 0 c 0 := by
  rw [uElt_mul]
  congr 1 <;> ring

theorem uElt_center_mul' (b c : K) : uElt (0 : K) b c 0 = uElt 0 0 c 0 * uElt 0 b 0 0 := by
  rw [uElt_mul]
  congr 1 <;> ring

theorem le_of_singer {W R R' : Subgroup (antiSp K)}
    (hWn : ∀ b ∈ Subgroup.normalizer (antiUnipotent K : Set (antiSp K)), ∀ w ∈ W, b * w * b⁻¹ ∈ W)
    (hRn : ∀ b ∈ Subgroup.normalizer (antiUnipotent K : Set (antiSp K)), ∀ z ∈ R, b * z * b⁻¹ ∈ R)
    {x : antiSp K} (hxB : x ∈ Subgroup.normalizer (antiUnipotent K : Set (antiSp K)))
    (hxc : ∀ z ∈ R', x * z = z * x)
    (hxt : ∀ z ∈ R, z ≠ 1 → ∀ w ∈ R, w ≠ 1 → ∃ j : ℕ, x ^ j * z * (x ^ j)⁻¹ = w)
    (h3 : ∀ p ∈ R, p ≠ 1 → ∃ p' ∈ R, p' ≠ 1 ∧ p' ≠ p)
    {p q : antiSp K} (hp : p ∈ R) (hq : q ∈ R') (hp1 : p ≠ 1) (hpq : p * q ∈ W) : R ≤ W := by
  have hmove : ∃ j : ℕ, x ^ j * p * (x ^ j)⁻¹ ≠ p := by
    by_contra hfix
    push Not at hfix
    obtain ⟨p', hp', hp'1, hp'p⟩ := h3 p hp hp1
    obtain ⟨j, hj⟩ := hxt p hp hp1 p' hp' hp'1
    exact hp'p (hj.symm.trans (hfix j))
  obtain ⟨j₀, hj₀⟩ := hmove
  have hyB : x ^ j₀ ∈ Subgroup.normalizer (antiUnipotent K : Set (antiSp K)) :=
    Subgroup.pow_mem _ hxB j₀
  have hyq : x ^ j₀ * q * (x ^ j₀)⁻¹ = q :=
    mul_inv_eq_iff_eq_mul.2 (Commute.pow_left (hxc q hq) j₀)
  have hW1 : x ^ j₀ * (p * q) * (x ^ j₀)⁻¹ ∈ W := hWn _ hyB _ hpq
  have hεW : (x ^ j₀ * p * (x ^ j₀)⁻¹) * p⁻¹ ∈ W := by
    have h1 : (x ^ j₀ * (p * q) * (x ^ j₀)⁻¹) * (p * q)⁻¹ ∈ W := W.mul_mem hW1 (W.inv_mem hpq)
    have h2 : (x ^ j₀ * (p * q) * (x ^ j₀)⁻¹) * (p * q)⁻¹ =
        (x ^ j₀ * p * (x ^ j₀)⁻¹) * p⁻¹ := by
      have e1 : x ^ j₀ * (p * q) * (x ^ j₀)⁻¹ =
          (x ^ j₀ * p * (x ^ j₀)⁻¹) * (x ^ j₀ * q * (x ^ j₀)⁻¹) := by group
      rw [e1, hyq]
      group
    rwa [h2] at h1
  have hεR : (x ^ j₀ * p * (x ^ j₀)⁻¹) * p⁻¹ ∈ R :=
    R.mul_mem (hRn _ hyB p hp) (R.inv_mem hp)
  have hε1 : (x ^ j₀ * p * (x ^ j₀)⁻¹) * p⁻¹ ≠ 1 := fun h =>
    hj₀ (mul_inv_eq_one.1 h)
  intro r hr
  by_cases hr1 : r = 1
  · rw [hr1]
    exact W.one_mem
  · obtain ⟨j, hj⟩ := hxt _ hεR hε1 r hr hr1
    rw [← hj]
    exact hWn _ (Subgroup.pow_mem _ hxB j) _ hεW

theorem exists_ne_ne (hK : 4 ≤ Nat.card K) (b : K) : ∃ t : K, t ≠ 0 ∧ t ≠ b := by
  classical
  by_contra h
  push Not at h
  haveI : Fintype K := Fintype.ofFinite K
  have hsub : (Finset.univ : Finset K) ⊆ {0, b} := fun t _ => by
    by_cases ht : t = 0
    · simp [ht]
    · simp [h t ht]
  have hle := Finset.card_le_card hsub
  have h2 : ({0, b} : Finset K).card ≤ 2 := Finset.card_le_two
  rw [Finset.card_univ, ← Nat.card_eq_fintype_card] at hle
  omega

theorem eq_rootShort_or_rootLong {n : ℕ} (hK : Nat.card K = 2 ^ n) (hn : 2 ≤ n)
    {W : Subgroup (antiSp K)} (hWU : W ≤ antiUnipotent K)
    (hWc : ∀ w ∈ W, ∀ s ∈ antiUnipotent K, w * s = s * w)
    (hWn : ∀ b ∈ Subgroup.normalizer (antiUnipotent K : Set (antiSp K)), ∀ w ∈ W, b * w * b⁻¹ ∈ W)
    (hWcard : Nat.card W = 2 ^ n) : W = rootShort K ∨ W = rootLong K := by
  classical
  have h4 : 4 ≤ Nat.card K := by
    rw [hK]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  have hWZ : ∀ w ∈ W, ∃ b c : K, w = uElt 0 b c 0 := fun w hw =>
    (mem_antiUnipotentCenter_iff_central w).2 ⟨hWU hw, fun h hh => hWc w hw h hh⟩
  by_cases hs : W ≤ rootShort K
  · left
    exact Subgroup.eq_of_le_of_card_ge hs (by rw [card_rootShort, hK, hWcard])
  by_cases hl : W ≤ rootLong K
  · right
    exact Subgroup.eq_of_le_of_card_ge hl (by rw [card_rootLong, hK, hWcard])
  exfalso
  have hboth : ∃ b c : K, b ≠ 0 ∧ c ≠ 0 ∧ uElt (0 : K) b c 0 ∈ W := by
    obtain ⟨w₁, hw₁, hw₁s⟩ := SetLike.not_le_iff_exists.1 hs
    obtain ⟨w₂, hw₂, hw₂l⟩ := SetLike.not_le_iff_exists.1 hl
    obtain ⟨b₁, c₁, rfl⟩ := hWZ w₁ hw₁
    obtain ⟨b₂, c₂, rfl⟩ := hWZ w₂ hw₂
    have hc₁ : c₁ ≠ 0 := fun h => hw₁s ⟨b₁, by rw [h]⟩
    have hb₂ : b₂ ≠ 0 := fun h => hw₂l ⟨c₂, by rw [h]⟩
    by_cases hb₁ : b₁ = 0
    · by_cases hc₂ : c₂ = 0
      · refine ⟨b₂, c₁, hb₂, hc₁, ?_⟩
        have hprod : uElt (0 : K) b₁ c₁ 0 * uElt 0 b₂ c₂ 0 = uElt 0 b₂ c₁ 0 := by
          rw [uElt_mul, hb₁, hc₂]
          congr 1 <;> ring
        rw [← hprod]
        exact W.mul_mem hw₁ hw₂
      · exact ⟨b₂, c₂, hb₂, hc₂, hw₂⟩
    · exact ⟨b₁, c₁, hb₁, hc₁, hw₁⟩
  obtain ⟨b₀, c₀, hb₀, hc₀, hw₀⟩ := hboth
  have hne : ∀ (b c : K), (uElt (0 : K) b 0 0 : antiSp K) = 1 → b = 0 := fun b c h => by
    rw [← uElt_zero_eq_one] at h
    exact (uElt_inj h).2.1
  have hne' : ∀ (c : K), (uElt (0 : K) 0 c 0 : antiSp K) = 1 → c = 0 := fun c h => by
    rw [← uElt_zero_eq_one] at h
    exact (uElt_inj h).2.2.1
  have hRs : ∀ b ∈ Subgroup.normalizer (antiUnipotent K : Set (antiSp K)), ∀ z ∈ rootShort K,
      b * z * b⁻¹ ∈ rootShort K := fun b hb z hz =>
    conj_mem_rootShort (mem_normalizer_iff_upper.2 (upper_of_mem_normalizer hb)) hz
  have hRl : ∀ b ∈ Subgroup.normalizer (antiUnipotent K : Set (antiSp K)), ∀ z ∈ rootLong K,
      b * z * b⁻¹ ∈ rootLong K := fun b hb z hz =>
    conj_mem_rootLong (mem_normalizer_iff_upper.2 (upper_of_mem_normalizer hb)) hz
  have hZs : rootShort K ≤ W := by
    obtain ⟨xs, hxsB, hxsc, hxst⟩ := exists_singer_short (K := K)
    refine le_of_singer hWn hRs hxsB hxsc hxst ?_ (p := uElt 0 b₀ 0 0) (q := uElt 0 0 c₀ 0)
      ⟨b₀, rfl⟩ ⟨c₀, rfl⟩ (fun h => hb₀ (hne b₀ c₀ h)) (by rw [← uElt_center_mul]; exact hw₀)
    rintro _ ⟨b, rfl⟩ hb1
    have hb : b ≠ 0 := fun h => hb1 (by rw [h]; exact uElt_zero_eq_one)
    obtain ⟨t, ht0, htb⟩ := exists_ne_ne h4 b
    refine ⟨uElt 0 t 0 0, ⟨t, rfl⟩, fun h => ht0 (hne t 0 h), fun h => htb (uElt_inj h).2.1⟩
  have hZl : rootLong K ≤ W := by
    obtain ⟨xl, hxlB, hxlc, hxlt⟩ := exists_singer_long (K := K)
    refine le_of_singer hWn hRl hxlB hxlc hxlt ?_ (p := uElt 0 0 c₀ 0) (q := uElt 0 b₀ 0 0)
      ⟨c₀, rfl⟩ ⟨b₀, rfl⟩ (fun h => hc₀ (hne' c₀ h)) (by rw [← uElt_center_mul']; exact hw₀)
    rintro _ ⟨c, rfl⟩ hc1
    have hc : c ≠ 0 := fun h => hc1 (by rw [h]; exact uElt_zero_eq_one)
    obtain ⟨t, ht0, htc⟩ := exists_ne_ne h4 c
    refine ⟨uElt 0 0 t 0, ⟨t, rfl⟩, fun h => ht0 (hne' t h), fun h => htc (uElt_inj h).2.2.1⟩
  have hZW : antiUnipotentCenter K ≤ W := by
    rintro _ ⟨b, c, rfl⟩
    rw [uElt_center_mul]
    exact W.mul_mem (hZs ⟨b, rfl⟩) (hZl ⟨c, rfl⟩)
  have hcardZ : Nat.card (antiUnipotentCenter K) = Nat.card K * Nat.card K := by
    rw [← omegaCenter_eq]
    exact card_omegaCenter
  have := Subgroup.card_le_of_le hZW
  rw [hcardZ, hWcard, ← hK] at this
  nlinarith

end Dichotomy

section Parabolic

variable {K : Type} [Field K] [Finite K] [CharP K 2]

@[expose] def tv1 : SL₂ K := ⟨!![1, 1; 0, 1], by simp [Matrix.det_fin_two_of]⟩

@[expose] def tv2 : SL₂ K := ⟨!![1, 0; 1, 1], by simp [Matrix.det_fin_two_of]⟩

theorem tv1_mul_self : tv1 * tv1 = (1 : SL₂ K) := by
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_one]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [tv1, Matrix.mul_apply, Fin.sum_univ_two, one_add_one_eq_two, h2]

theorem tv2_mul_self : tv2 * tv2 = (1 : SL₂ K) := by
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_one]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [tv2, Matrix.mul_apply, Fin.sum_univ_two, one_add_one_eq_two, h2]

theorem eq_one_of_commute_tv {M : SL₂ K} (h1 : M * tv1 = tv1 * M) (h2 : M * tv2 = tv2 * M) :
    M = 1 := by
  have h2' : (2 : K) = 0 := CharTwo.two_eq_zero
  have e1 := congrArg (fun A : SL₂ K => (A : Matrix (Fin 2) (Fin 2) K)) h1
  have e2 := congrArg (fun A : SL₂ K => (A : Matrix (Fin 2) (Fin 2) K)) h2
  simp only [Matrix.SpecialLinearGroup.coe_mul] at e1 e2
  have a00 := congrFun (congrFun e1 0) 0
  have a01 := congrFun (congrFun e1 0) 1
  have a10 := congrFun (congrFun e1 1) 0
  have a11 := congrFun (congrFun e1 1) 1
  have b00 := congrFun (congrFun e2 0) 0
  have b01 := congrFun (congrFun e2 0) 1
  have b10 := congrFun (congrFun e2 1) 0
  have b11 := congrFun (congrFun e2 1) 1
  simp [tv1, tv2, Matrix.mul_apply, Fin.sum_univ_two] at a00 a01 a10 a11 b00 b01 b10 b11
  have hdet := M.2
  rw [Matrix.det_fin_two] at hdet
  have hr : (M : Matrix (Fin 2) (Fin 2) K) 1 0 = 0 := by linear_combination a00
  have hq : (M : Matrix (Fin 2) (Fin 2) K) 0 1 = 0 := by linear_combination b00
  have hps : (M : Matrix (Fin 2) (Fin 2) K) 0 0 = (M : Matrix (Fin 2) (Fin 2) K) 1 1 := by
    linear_combination a01
  rw [hr, hq, ← hps] at hdet
  have hp : (M : Matrix (Fin 2) (Fin 2) K) 0 0 = 1 := by
    have : ((M : Matrix (Fin 2) (Fin 2) K) 0 0 - 1) ^ 2 = 0 := by
      linear_combination hdet + (1 - (M : Matrix (Fin 2) (Fin 2) K) 0 0) * h2'
    have := pow_eq_zero_iff (two_ne_zero) |>.1 this
    linear_combination this
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j <;> simp [hp, hq, hr, ← hps]

theorem units_eq_one_of_sq_eq_one {l : Kˣ} (h : (l : K) ^ 2 = 1) : l = 1 := by
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  have h1 : ((l : K) - 1) ^ 2 = 0 := by linear_combination h + (1 - (l : K)) * h2
  have := pow_eq_zero_iff (two_ne_zero) |>.1 h1
  exact Units.ext (by rw [Units.val_one]; linear_combination this)

end Parabolic

section RootAxis

variable {K : Type} [Field K] [Finite K] [CharP K 2] {n : ℕ}

theorem rootCoord_injective (i : Axis) : Function.Injective (rootCoord K i) := by
  cases i
  · intro x y h
    exact (uElt_inj h).2.1
  · intro x y h
    exact (uElt_inj h).2.2.1

theorem rootCoord_mul_self (i : Axis) (x : K) : rootCoord K i x * rootCoord K i x = 1 := by
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  cases i
  · show uElt (0 : K) x 0 0 * uElt 0 x 0 0 = 1
    rw [uElt_mul, ← uElt_zero_eq_one]
    congr 1 <;> first | ring1 | linear_combination x * h2
  · show uElt (0 : K) 0 x 0 * uElt 0 0 x 0 = 1
    rw [uElt_mul, ← uElt_zero_eq_one]
    congr 1 <;> first | ring1 | linear_combination x * h2

theorem mem_rootU_of_commute_two_elements (hK : Nat.card K = 2 ^ n) (hn : 2 ≤ n) (i : Axis)
    {z : antiSp K} (hzN : z ∈ rootN K i)
    (hz : ∀ y ∈ rootN K i, (∃ k : ℕ, y ^ 2 ^ k = 1) → z * y = y * z) : z ∈ rootU K i := by
  have hs := even_symplectic_four_root_axis_centralizer_structure hK hn i
  obtain ⟨a, ha, l, M, rfl⟩ := hs.N_decomp z hzN
  have hsN : ∀ T : SL₂ K, sHom K i T ∈ rootN K i := fun T => by
    have := hs.ds_mem_N 1 T
    rwa [map_one, one_mul] at this
  have key : ∀ T : SL₂ K, T * T = 1 →
      a = sHom K i T * a * (sHom K i T)⁻¹ ∧ M * T = T * M := by
    intro T hT
    have h1 := hz (sHom K i T) (hsN T) ⟨1, by
      rw [show (2 : ℕ) ^ 1 = 2 from rfl, pow_two, ← map_mul, hT, map_one]⟩
    have hA' : sHom K i T * a * (sHom K i T)⁻¹ ∈ rootA K i := hs.A_normal_N _ (hsN T) a ha
    have hc := hs.s_comm_d T l
    have e : a * (dHom K i l * sHom K i (M * T)) =
        (sHom K i T * a * (sHom K i T)⁻¹) * (dHom K i l * sHom K i (T * M)) := by
      rw [map_mul, map_mul]
      calc a * (dHom K i l * (sHom K i M * sHom K i T))
          = a * (dHom K i l * sHom K i M) * sHom K i T := by group
        _ = sHom K i T * (a * (dHom K i l * sHom K i M)) := h1
        _ = (sHom K i T * a * (sHom K i T)⁻¹) * (sHom K i T * dHom K i l * sHom K i M) := by group
        _ = (sHom K i T * a * (sHom K i T)⁻¹) * (dHom K i l * sHom K i T * sHom K i M) := by
          rw [hc]
        _ = (sHom K i T * a * (sHom K i T)⁻¹) * (dHom K i l * (sHom K i T * sHom K i M)) := by
          group
    obtain ⟨h1', -, h3'⟩ := hs.N_unique a ha _ hA' l l (M * T) (T * M) e
    exact ⟨h1', h3'⟩
  have hM : M = 1 := eq_one_of_commute_tv (key tv1 tv1_mul_self).2 (key tv2 tv2_mul_self).2
  have hvec : ∀ T : SL₂ K, T * T = 1 →
      vecOf K i a = (T : Matrix (Fin 2) (Fin 2) K) *ᵥ vecOf K i a := fun T hT => by
    have h1 := hs.vec_conj T a ha
    rw [← (key T hT).1] at h1
    exact h1
  have hv1 := congrFun (hvec tv1 tv1_mul_self) 0
  have hv2 := congrFun (hvec tv2 tv2_mul_self) 1
  simp [tv1, tv2, Matrix.mulVec, dotProduct, Fin.sum_univ_two] at hv1 hv2
  have haU : a ∈ rootU K i := by
    refine (hs.vec_ker a ha).1 ?_
    funext j
    fin_cases j
    · simpa using hv2
    · simpa using hv1
  subst hM
  have hu : rootCoord K i 1 ∈ rootN K i := Subgroup.le_normalizer (hs.coord_mem 1)
  have h' := hz _ hu ⟨1, by
    rw [show (2 : ℕ) ^ 1 = 2 from rfl, pow_two]
    exact rootCoord_mul_self i 1⟩
  rw [map_one, mul_one] at h'
  have hu' : rootCoord K i ((l : K) ^ 2 * 1) ∈ rootU K i := hs.coord_mem _
  have hcomm : rootCoord K i ((l : K) ^ 2 * 1) * a = a * rootCoord K i ((l : K) ^ 2 * 1) :=
    Subgroup.mem_centralizer_iff.1 (hs.A_le_C ha) _ hu'
  have h3 : a * rootCoord K i ((l : K) ^ 2 * 1) * a⁻¹ = rootCoord K i ((l : K) ^ 2 * 1) :=
    mul_inv_eq_iff_eq_mul.2 hcomm.symm
  have h4 : (a * dHom K i l) * rootCoord K i 1 * (a * dHom K i l)⁻¹ = rootCoord K i 1 :=
    mul_inv_eq_iff_eq_mul.2 h'
  have h5 : (a * dHom K i l) * rootCoord K i 1 * (a * dHom K i l)⁻¹ =
      a * (dHom K i l * rootCoord K i 1 * (dHom K i l)⁻¹) * a⁻¹ := by group
  rw [h5, hs.d_coord l 1, h3] at h4
  have h6 : (l : K) ^ 2 * 1 = 1 := rootCoord_injective i h4
  have hl : l = 1 := units_eq_one_of_sq_eq_one (by simpa using h6)
  subst hl
  simpa using haU

theorem rootN_lt_top (hK : Nat.card K = 2 ^ n) (hn : 2 ≤ n) (i : Axis) : rootN K i < ⊤ := by
  have hd := CFSG.QuasithinUnique.Borel252.Sp4.borelData_Sp hn hK
  have hs := even_symplectic_four_root_axis_centralizer_structure hK hn i
  have h : rootN K i = Subgroup.normalizer (rootA K i : Set (antiSp K)) := hs.N_eq
  rw [h]
  cases i
  · exact hd.lt_top₁
  · exact hd.lt_top₂

theorem rootU_le_center (i : Axis) : rootU K i ≤ antiUnipotentCenter K := by
  cases i
  · rintro _ ⟨b, rfl⟩
    exact ⟨b, 0, rfl⟩
  · rintro _ ⟨c, rfl⟩
    exact ⟨0, c, rfl⟩

theorem rootU_le_antiUnipotent (i : Axis) : rootU K i ≤ antiUnipotent K :=
  (rootU_le_center i).trans (antiUnipotentCenter_le)

theorem rootU_comm (i : Axis) {w s : antiSp K} (hw : w ∈ rootU K i) (hs : s ∈ antiUnipotent K) :
    w * s = s * w :=
  antiUnipotentCenter_comm (rootU_le_center i hw) hs

theorem rootC_perfect (hK : Nat.card K = 2 ^ n) (hn : 2 ≤ n) (i : Axis) :
    ⁅rootC K i, rootC K i⁆ = rootC K i :=
  Subgroup.isPerfect_iff.1 (even_symplectic_four_root_axis_centralizer_structure hK hn i).C_perfect

theorem rootC_le_rootN (i : Axis) : rootC K i ≤ rootN K i := fun g hg =>
  Subgroup.centralizer_le_normalizer _ hg

theorem exists_complement (hK : Nat.card K = 2 ^ n) (hn : 2 ≤ n) (i : Axis) :
    ∃ X₀ : Subgroup (antiSp K), X₀ ≤ rootN K i ∧ IsCyclic ↥X₀ ∧ Nat.card ↥X₀ = 2 ^ n - 1 ∧
      ∀ p ∈ rootN K i, ∃ c ∈ rootC K i, ∃ x ∈ X₀, p = c * x := by
  have hs := even_symplectic_four_root_axis_centralizer_structure hK hn i
  refine ⟨(dHom K i).range, ?_, ?_, ?_, ?_⟩
  · rintro _ ⟨l, rfl⟩
    have := hs.ds_mem_N l 1
    rwa [map_one, mul_one] at this
  · exact isCyclic_of_surjective (dHom K i).rangeRestrict (MonoidHom.rangeRestrict_surjective _)
  · have hinj : Function.Injective (dHom K i) := by
      intro l l' h
      have := hs.N_unique 1 (one_mem _) 1 (one_mem _) l l' 1 1 (by simpa using h)
      exact this.2.1
    rw [← Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv, Nat.card_units, hK]
  · intro p hp
    obtain ⟨a, ha, l, M, rfl⟩ := hs.N_decomp p hp
    refine ⟨a * sHom K i M, Subgroup.mul_mem _ (hs.A_le_C ha) (hs.s_mem_C M), dHom K i l,
      ⟨l, rfl⟩, ?_⟩
    calc a * (dHom K i l * sHom K i M) = a * (sHom K i M * dHom K i l) := by
          rw [hs.s_comm_d M l]
      _ = a * sHom K i M * dHom K i l := by group

end RootAxis

end Sp4X

end CFSG.Quasithin.RonanE611
