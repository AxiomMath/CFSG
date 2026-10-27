module

public import CFSG.LocalAnalysis.ComponentInitial.FieldUnitaryNorm
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_7FinSp4
public import CFSG.RankThree.PartOne.KC.EvenSymplecticFourRootAxisAutClass

public section

namespace CFSG.LocalAnalysis.SymplecticFourStandard

namespace FieldInvolution

open Matrix CFSG.ComponentClassification.UnbalancedCatalog.SpChain
  CFSG.RankThree.PartOne.KCRootAxis CFSG.QuasithinUnique.Fin257 CFSG.LocalAnalysis.ComponentInitial
open CFSG.QuasithinUnique.Setup.X7b (radA2 radA2_le_antiUnipotent)

section Aut

variable {X : Type*} [Group X]

theorem aut_mul_conj (σ : MulAut X) (x : X) :
    σ * MulAut.conj x = MulAut.conj (σ x) * σ := by
  ext y
  simp [MulAut.conj_apply, map_mul, map_inv]

theorem conj_inv_mul_conj_mul_conj (σ : MulAut X) (e j : X) (hj : j = e * (σ e)⁻¹) :
    (MulAut.conj e)⁻¹ * (MulAut.conj j * σ) * MulAut.conj e = σ := by
  rw [mul_assoc, mul_assoc, aut_mul_conj, ← mul_assoc (MulAut.conj j), ← map_mul, ← map_inv,
    ← mul_assoc, ← map_mul, hj]
  simp

theorem conj_mul_sq (σ : MulAut X) (j : X) :
    (MulAut.conj j * σ) ^ 2 = MulAut.conj (j * σ j) * σ ^ 2 := by
  rw [pow_two, pow_two, mul_assoc, ← mul_assoc σ, aut_mul_conj, map_mul]
  simp only [mul_assoc]

end Aut

section Matrix

variable {K : Type} [Field K] [CharP K 2]

theorem mat_frobAut_pow [Finite K] (k : ℕ) (g : antiSp K) :
    mat ((frobAut K ^ k) g) = (mat g).map fun x => x ^ 2 ^ k := by
  induction k generalizing g with
  | zero =>
    ext i j
    simp
  | succ k ih =>
    rw [pow_succ, MulAut.mul_apply, ih, mat_frobAut]
    ext i j
    simp only [Matrix.map_apply]
    rw [← pow_mul, ← pow_succ']

theorem frobAut_pow_eq_one [Finite K] {n : ℕ} (hK : Nat.card K = 2 ^ n) : frobAut K ^ n = 1 := by
  have := Fintype.ofFinite K
  refine MulEquiv.ext fun g => mat_ext ?_
  rw [mat_frobAut_pow, MulAut.one_apply]
  ext i j
  rw [Matrix.map_apply, ← hK, Nat.card_eq_fintype_card, FiniteField.pow_card]

theorem frobAut_pow_dSp [Finite K] (k : ℕ) (r s : Kˣ) :
    (frobAut K ^ k) (Sp4.dSp r s) = Sp4.dSp (r ^ 2 ^ k) (s ^ 2 ^ k) := by
  apply mat_ext
  rw [mat_frobAut_pow]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [mat, Sp4.glMat_dSp, Sp4.dSpMat]

theorem frobAut_pow_uElt [Finite K] (k : ℕ) (a b c d : K) :
    (frobAut K ^ k) (uElt a b c d) = uElt (a ^ 2 ^ k) (b ^ 2 ^ k) (c ^ 2 ^ k) (d ^ 2 ^ k) := by
  induction k generalizing a b c d with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, MulAut.mul_apply, frobAut_uElt, ih]
    simp only [← pow_mul, ← pow_succ']

theorem frobAut_pow_eq_self [Finite K] (k : ℕ) {g : antiSp K}
    (hg : ∀ i j, mat g i j = 0 ∨ mat g i j = 1) : (frobAut K ^ k) g = g := by
  apply mat_ext
  rw [mat_frobAut_pow]
  ext i j
  rcases hg i j with h | h <;> simp [Matrix.map_apply, h]

theorem eq_one_of_dSp_mem_antiUnipotent {r s : Kˣ} (h : Sp4.dSp r s ∈ antiUnipotent K) :
    r = 1 ∧ s = 1 := by
  rw [mem_antiUnipotent_iff_upper] at h
  have h0 := h.2 0
  have h1 := h.2 1
  simp [Sp4.glMat_dSp, Sp4.dSpMat] at h0 h1
  exact ⟨h0, h1⟩

theorem dSp_eq_one_of_mul_self {r s : Kˣ} (h : Sp4.dSp r s * Sp4.dSp r s = 1) :
    Sp4.dSp r s = 1 := by
  have key : ∀ x : Kˣ, x * x = 1 → x = 1 := fun x hx => by
    have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
    have hx' : (x : K) * x = 1 := by simpa using congrArg Units.val hx
    have hsq : ((x : K) - 1) ^ 2 = 0 := by linear_combination hx' + (1 - (x : K)) * h2
    exact Units.ext (sub_eq_zero.1 (pow_eq_zero_iff two_ne_zero |>.1 hsq))
  rw [Sp4.dSp_mul] at h
  obtain ⟨hr, hs⟩ := Sp4.dSp_eq_one h
  rw [key r hr, key s hs, Sp4.dSp_one]

theorem dSp_conj_mem_antiUnipotent (r s : Kˣ) {x : antiSp K} (hx : x ∈ antiUnipotent K) :
    Sp4.dSp r s * x * (Sp4.dSp r s)⁻¹ ∈ antiUnipotent K := by
  obtain ⟨a, b, c, d, rfl⟩ := hx
  rw [Sp4.dSp_conj_uElt]
  exact uElt_mem_antiUnipotent _ _ _ _

theorem dSp_conj_mem_radA2 (r s : Kˣ) {x : antiSp K} (hx : x ∈ radA2 K) :
    Sp4.dSp r s * x * (Sp4.dSp r s)⁻¹ ∈ radA2 K := by
  obtain ⟨a, b, c, rfl⟩ := hx
  rw [Sp4.dSp_conj_uElt, mul_zero]
  exact ⟨_, _, _, rfl⟩

theorem lower_eq_zero_of_conj_mem (l : Kˣ) (M : SL₂ K)
    (h : dElt l * sElt M * uElt 0 0 0 1 * (dElt l * sElt M)⁻¹ ∈ antiUnipotent K) :
    (M : Matrix (Fin 2) (Fin 2) K) 1 0 = 0 := by
  have hinv : (dElt l * sElt M)⁻¹ = sElt M⁻¹ * dElt l⁻¹ := by
    rw [_root_.mul_inv_rev, ← sHom₂_apply, ← sHom₂_apply, ← dHom₂_apply, ← dHom₂_apply, map_inv,
      map_inv]
  rw [hinv, mem_antiUnipotent_iff_upper] at h
  have h21 := h.1 2 1 (by decide)
  change (mat (dElt l * sElt M * uElt 0 0 0 1 * (sElt M⁻¹ * dElt l⁻¹))) 2 1 = 0 at h21
  rw [mat_mul, mat_mul, mat_mul, mat_mul, mat_dElt, mat_sElt, mat_sElt, mat_dElt,
    Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two] at h21
  simp [dMat, sMat, uMat, mat, glMat_uElt, Matrix.mul_apply, Fin.sum_univ_four] at h21
  have hsq : ((M : Matrix (Fin 2) (Fin 2) K) 1 0) ^ 2 = 0 := by linear_combination -h21
  exact pow_eq_zero_iff two_ne_zero |>.1 hsq

theorem exists_dElt_mul_sElt_eq (l : Kˣ) (M : SL₂ K)
    (hM : (M : Matrix (Fin 2) (Fin 2) K) 1 0 = 0) :
    ∃ (x : Kˣ) (w : K), dElt l * sElt M = uElt 0 0 0 w * Sp4.dSp l x := by
  have hdet := M.det_coe
  rw [Matrix.det_fin_two, hM, mul_zero, sub_zero] at hdet
  have hx : (M : Matrix (Fin 2) (Fin 2) K) 0 0 ≠ 0 := left_ne_zero_of_mul_eq_one hdet
  refine ⟨Units.mk0 _ hx, (M : Matrix (Fin 2) (Fin 2) K) 0 0 * (M : Matrix (Fin 2) (Fin 2) K) 0 1,
    mat_ext ?_⟩
  rw [mat_mul, mat_mul, mat_dElt, mat_sElt]
  change _ = uMat 0 0 0 _ * Sp4.dSpMat _ _
  have h11 : (M : Matrix (Fin 2) (Fin 2) K) 1 1 = ((M : Matrix (Fin 2) (Fin 2) K) 0 0)⁻¹ :=
    eq_inv_of_mul_eq_one_right hdet
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [dMat, sMat, uMat, Sp4.dSpMat, Matrix.mul_apply, Fin.sum_univ_four, hM, h11]
  field_simp

theorem exists_conj_mul_dSp_frobAut_pow [Finite K] {n : ℕ} (hn : 2 ≤ n) (hK : Nat.card K = 2 ^ n)
    (α : MulAut (antiSp K)) (hA : ∀ x, α x ∈ radA2 K ↔ x ∈ radA2 K)
    (hU : ∀ x ∈ antiUnipotent K, α x ∈ antiUnipotent K) :
    ∃ p ∈ antiUnipotent K, ∃ r s : Kˣ, ∃ k < n,
      α = MulAut.conj (p * Sp4.dSp r s) * frobAut K ^ k := by
  obtain ⟨g, hg, k, hk, rfl⟩ := exists_conj_mul_frobAut_pow hn hK Axis.two α hA
  obtain ⟨a, ha, l, M, rfl⟩ :=
    (even_symplectic_four_root_axis_centralizer_structure hK hn Axis.two).N_decomp g hg
  change a ∈ radA2 K at ha
  change ∀ x ∈ antiUnipotent K,
    (MulAut.conj (a * (dElt l * sElt M)) * frobAut K ^ k) x ∈ antiUnipotent K at hU
  have hM : (M : Matrix (Fin 2) (Fin 2) K) 1 0 = 0 := by
    refine lower_eq_zero_of_conj_mem l M ?_
    have h1 := hU _ (uElt_mem_antiUnipotent 0 0 0 1)
    rw [MulAut.mul_apply, frobAut_pow_uElt, MulAut.conj_apply] at h1
    simp only [ne_eq, pow_eq_zero_iff', OfNat.ofNat_ne_zero, false_and, not_false_eq_true,
      zero_pow, one_pow] at h1
    have haU : a ∈ antiUnipotent K := radA2_le_antiUnipotent ha
    have h2 := mul_mem (mul_mem (inv_mem haU) h1) haU
    convert h2 using 1
    group
  obtain ⟨x, w, hxw⟩ := exists_dElt_mul_sElt_eq l M hM
  refine ⟨a * uElt 0 0 0 w, mul_mem (radA2_le_antiUnipotent ha) (uElt_mem_antiUnipotent _ _ _ _),
    l, x, k, hk, ?_⟩
  show MulAut.conj (a * (dElt l * sElt M)) * frobAut K ^ k = _
  rw [hxw, mul_assoc]

theorem eq_one_of_conj_eq_sq [Finite K] {n : ℕ} (hn : 1 ≤ n) (hK : Nat.card K = 2 ^ n)
    {r s : Kˣ} {k : ℕ} (hk : k < n) {y : antiSp K} (hy : y ∈ antiUnipotent K)
    (h : MulAut.conj y = (MulAut.conj (Sp4.dSp r s) * frobAut K ^ k) ^ 2) :
    y = 1 ∧ Sp4.dSp r s * (frobAut K ^ k) (Sp4.dSp r s) = 1 ∧ (k = 0 ∨ n = 2 * k) := by
  rw [conj_mul_sq, ← pow_mul] at h
  set j' := Sp4.dSp r s * (frobAut K ^ k) (Sp4.dSp r s) with hj'def
  have hj' : j' = Sp4.dSp (r * r ^ 2 ^ k) (s * s ^ 2 ^ k) := by
    rw [hj'def, frobAut_pow_dSp, Sp4.dSp_mul]
  have key : y = j' ∧ (k = 0 ∨ n = 2 * k) := by
    by_cases h2k : 2 * k < n
    · have h' : MulAut.conj y * frobAut K ^ 0 = MulAut.conj j' * frobAut K ^ (2 * k) := by
        rw [pow_zero, mul_one, h, mul_comm k 2]
      obtain ⟨h1, h2⟩ := conj_mul_frobAut_pow_inj hn hK (by omega) h2k h'
      exact ⟨h1, Or.inl (by omega)⟩
    · have h' : MulAut.conj y * frobAut K ^ 0 = MulAut.conj j' * frobAut K ^ (2 * k - n) := by
        rw [pow_zero, mul_one, h, show k * 2 = (2 * k - n) + n by omega, pow_add,
          frobAut_pow_eq_one hK, mul_one]
      obtain ⟨h1, h2⟩ := conj_mul_frobAut_pow_inj hn hK (by omega) (by omega) h'
      exact ⟨h1, Or.inr (by omega)⟩
  obtain ⟨hyj, hkn⟩ := key
  have hU' : j' ∈ antiUnipotent K := hyj ▸ hy
  rw [hj'] at hU'
  obtain ⟨h1, h2⟩ := eq_one_of_dSp_mem_antiUnipotent hU'
  have hj1 : j' = 1 := by rw [hj', h1, h2, Sp4.dSp_one]
  exact ⟨hyj.trans hj1, hj1, hkn⟩

theorem exists_dSp_eq_mul_frob_inv [Finite K] {m : ℕ} (hm : 1 ≤ m)
    (hK : Nat.card K = 2 ^ (2 * m)) {r s : Kˣ}
    (h : Sp4.dSp r s * (frobAut K ^ m) (Sp4.dSp r s) = 1) :
    ∃ b c : Kˣ, Sp4.dSp r s = Sp4.dSp b c * ((frobAut K ^ m) (Sp4.dSp b c))⁻¹ := by
  have hD : UnitaryFieldData 2 m K := ⟨Nat.prime_two, hm, hK⟩
  rw [frobAut_pow_dSp, Sp4.dSp_mul] at h
  obtain ⟨hr, hs⟩ := Sp4.dSp_eq_one h
  have hnorm : ∀ x : Kˣ, x * x ^ 2 ^ m = 1 → ∃ b : Kˣ, x = b * (b ^ 2 ^ m)⁻¹ := by
    intro x hx
    have hx' : hD.norm x = 1 := by
      rw [UnitaryFieldData.norm, UnitaryFieldData.bar_apply]
      simpa using congrArg Units.val hx
    obtain ⟨b, hb0, hb⟩ := hD.exists_div_bar_eq hx'
    refine ⟨Units.mk0 b hb0, Units.ext ?_⟩
    rw [UnitaryFieldData.bar_apply] at hb
    simp [← hb, div_eq_mul_inv]
  obtain ⟨b, rfl⟩ := hnorm r hr
  obtain ⟨c, rfl⟩ := hnorm s hs
  exact ⟨b, c, by rw [frobAut_pow_dSp, Sp4.dSp_inv, Sp4.dSp_mul]⟩

theorem conj_mul_frobAut_pow_ne_conj [Finite K] {n : ℕ} (hn : 1 ≤ n) (hK : Nat.card K = 2 ^ n)
    {k : ℕ} (hk0 : k ≠ 0) (hk : k < n) (j y : antiSp K) :
    MulAut.conj j * frobAut K ^ k ≠ MulAut.conj y := by
  intro h
  have h' : MulAut.conj j * frobAut K ^ k = MulAut.conj y * frobAut K ^ 0 := by
    rw [pow_zero, mul_one, h]
  exact hk0 (conj_mul_frobAut_pow_inj hn hK hk (by omega) h').2

end Matrix

section Group

variable {G : Type*} [Group G]

theorem mem_normalizer_of_conj_mem_of_inv {S : Set G} {g : G} (h1 : ∀ x ∈ S, g * x * g⁻¹ ∈ S)
    (h2 : ∀ x ∈ S, g⁻¹ * x * g ∈ S) : g ∈ Subgroup.normalizer S := by
  rw [Subgroup.mem_set_normalizer_iff]
  refine fun x => ⟨h1 x, fun hx => ?_⟩
  have := h2 _ hx
  rwa [show g⁻¹ * (g * x * g⁻¹) * g = x by group] at this

theorem sup_zpowers_inf_le {t : G} (ht : t ^ 2 = 1) {A L : Subgroup G} (hAL : A ≤ L)
    (htL : t ∉ L) (hcomm : ∀ a ∈ A, a * t = t * a) : (Subgroup.zpowers t ⊔ A) ⊓ L ≤ A := by
  have htt : t * t = 1 := by rw [← pow_two, ht]
  have hconj : ∀ x, t * x ∈ A → t * x * t = x := fun x hx => by
    have h1 := hcomm _ hx
    calc t * x * t = t * (t * x) := h1
      _ = x := by rw [← mul_assoc, htt, one_mul]
  let M : Subgroup G :=
    { carrier := {x | x ∈ A ∨ t * x ∈ A}
      mul_mem' := by
        rintro x y (hx | hx) (hy | hy)
        · exact Or.inl (A.mul_mem hx hy)
        · refine Or.inr ?_
          rw [show t * (x * y) = x * (t * y) by rw [← mul_assoc, ← hcomm x hx, mul_assoc]]
          exact A.mul_mem hx hy
        · exact Or.inr (by rw [← mul_assoc]; exact A.mul_mem hx hy)
        · refine Or.inl ?_
          rw [show x * y = t * x * (t * y) by rw [← mul_assoc, hconj x hx]]
          exact A.mul_mem hx hy
      one_mem' := Or.inl A.one_mem
      inv_mem' := by
        rintro x (hx | hx)
        · exact Or.inl (A.inv_mem hx)
        · refine Or.inr ?_
          have h1 := A.inv_mem hx
          have e : t * x⁻¹ = (t * x)⁻¹ :=
            calc t * x⁻¹ = t * (t * x * t)⁻¹ := by rw [hconj x hx]
              _ = (t * x)⁻¹ := by group
          rw [e]
          exact h1 }
  have htM : t ∈ M := Or.inr (by rw [htt]; exact A.one_mem)
  have hle : Subgroup.zpowers t ⊔ A ≤ M :=
    sup_le ((Subgroup.zpowers_le).2 htM) fun a ha => Or.inl ha
  rintro x ⟨hx, hxL⟩
  rcases hle hx with h | h
  · exact h
  · exact absurd (by simpa using L.mul_mem (hAL h) (L.inv_mem hxL)) htL

end Group

section Transport

variable {G : Type*} [Group G] {K : Type} [Field K] {L : Subgroup G}

@[expose] noncomputable def transAct (φ : L ≃* antiSp K) :
    Subgroup.normalizer (L : Set G) →* MulAut (antiSp K) :=
  (MulAut.congr φ).toMonoidHom.comp L.normalizerMonoidHom

theorem coe_symm_transAct (φ : L ≃* antiSp K) (x : Subgroup.normalizer (L : Set G))
    (y : antiSp K) : ((φ.symm (transAct φ x y) : L) : G) = x * φ.symm y * (x : G)⁻¹ := by
  simp [transAct, MulAut.congr_apply, Subgroup.normalizerMonoidHom_apply_apply_coe]

theorem transAct_of_mem (φ : L ≃* antiSp K) (x : Subgroup.normalizer (L : Set G))
    (hx : (x : G) ∈ L) : transAct φ x = MulAut.conj (φ ⟨x, hx⟩) := by
  refine MulEquiv.ext fun y => φ.symm.injective (Subtype.ext ?_)
  rw [coe_symm_transAct, MulAut.conj_apply, map_mul, map_mul, map_inv, MulEquiv.symm_apply_apply]
  rfl

theorem transAct_eq_one_iff (φ : L ≃* antiSp K) (x : Subgroup.normalizer (L : Set G)) :
    transAct φ x = 1 ↔ (x : G) ∈ Subgroup.centralizer (L : Set G) := by
  constructor
  · intro h
    rw [Subgroup.mem_centralizer_iff]
    intro l hl
    have h1 := coe_symm_transAct φ x (φ ⟨l, hl⟩)
    rw [h, MulAut.one_apply, MulEquiv.symm_apply_apply] at h1
    change l = x * l * (x : G)⁻¹ at h1
    calc l * x = x * l * (x : G)⁻¹ * x := by rw [← h1]
      _ = x * l := by group
  · intro h
    refine MulEquiv.ext fun y => φ.symm.injective (Subtype.ext ?_)
    rw [coe_symm_transAct, MulAut.one_apply]
    have h1 := Subgroup.mem_centralizer_iff.1 h _ (φ.symm y).2
    rw [← h1]
    group

theorem coe_symm_mem_map_iff (φ : L ≃* antiSp K) (H : Subgroup (antiSp K)) (y : antiSp K) :
    ((φ.symm y : L) : G) ∈ H.map (L.subtype.comp φ.symm.toMonoidHom) ↔ y ∈ H := by
  constructor
  · rintro ⟨z, hz, hzy⟩
    have : z = y := φ.symm.injective (Subtype.ext hzy)
    rwa [← this]
  · exact fun hy => ⟨y, hy, rfl⟩

end Transport

end FieldInvolution

open Matrix CFSG.ComponentClassification.UnbalancedCatalog.SpChain
  CFSG.RankThree.PartOne.KCRootAxis CFSG.QuasithinUnique.Fin257 FieldInvolution
open CFSG.QuasithinUnique.Setup.X7b (radA2)

theorem symplectic_normalizer_quotient_field_involution_representative {G : Type*} [Group G]
    {n : ℕ} (hn : 2 ≤ n) {K : Type} [Field K] [CharP K 2] [Finite K] (hK : Nat.card K = 2 ^ n)
    (L : Subgroup G) (φ : L ≃* antiSp K) (t : G) (ht : t ^ 2 = 1) (htL : t ∉ L)
    (htLc : t ∈ Subgroup.centralizer (L : Set G))
    (hLn : Subgroup.centralizer ({t} : Set G) ≤ Subgroup.normalizer (L : Set G))
    (hCL : Subgroup.centralizer ({t} : Set G) ⊓ Subgroup.centralizer (L : Set G) =
      Subgroup.zpowers t)
    (V : Subgroup G)
    (hJ₀V : ∀ r s : Kˣ, ((φ.symm (Sp4.dSp r⁻¹ s⁻¹) : L) : G) ∈ Subgroup.normalizer (V : Set G))
    (hVP : V ⊓ Subgroup.centralizer ({t} : Set G) =
      (antiUnipotent K).map (L.subtype.comp φ.symm.toMonoidHom))
    (hclass : {x | ∃ g : G, x = g⁻¹ * t * g} ∩ ((V ⊔ Subgroup.zpowers t : Subgroup G) : Set G) =
      {x | ∃ a ∈ V, x = a⁻¹ * t * a})
    (hgen : Subgroup.closure {x | ∃ a ∈ V, x = a⁻¹ * t * a} =
      Subgroup.zpowers t ⊔ (radA2 K).map (L.subtype.comp φ.symm.toMonoidHom))
    (u : G) (huS : u ∈ Subgroup.normalizer ((V ⊔ Subgroup.zpowers t : Subgroup G) : Set G))
    (huV : u ∈ Subgroup.normalizer (V : Set G)) (hu : u ∉ V ⊔ Subgroup.zpowers t)
    (hu2 : u ^ 2 ∈ V) :
    Even n ∧ ∃ v d : G,
      u⁻¹ * v ∈ V ∧ v ∈ Subgroup.centralizer ({t} : Set G) ∧ v ^ 2 = 1 ∧ v ≠ 1 ∧
      (∃ r s : Kˣ, d = φ.symm (Sp4.dSp r⁻¹ s⁻¹)) ∧
      (∀ l : L, ((φ.symm ((frobAut K ^ (n / 2)) (φ l)) : L) : G) =
        d⁻¹ * v * d * l * (d⁻¹ * v * d)⁻¹) ∧
      (∀ w ∈ ({v, d⁻¹ * v * d} : Set G),
        w ∈ Subgroup.normalizer ((V ⊔ Subgroup.zpowers t : Subgroup G) : Set G) ∧
        w ∈ Subgroup.normalizer (V : Set G) ∧ w ∈ Subgroup.centralizer ({t} : Set G) ∧
        ¬ ∃ l ∈ L, ∃ c ∈ Subgroup.centralizer (L : Set G), w = l * c) ∧
      d ∈ Subgroup.centralizer ({t} : Set G) ∧
      d ∈ Subgroup.normalizer
        (((antiUnipotent K).map (L.subtype.comp φ.symm.toMonoidHom) : Subgroup G) : Set G) ∧
      d ∈ Subgroup.normalizer
        (((radA2 K).map (L.subtype.comp φ.symm.toMonoidHom) : Subgroup G) : Set G) ∧
      d ∈ Subgroup.normalizer {x : G | ∃ r s : Kˣ, x = φ.symm (Sp4.dSp r⁻¹ s⁻¹)} ∧
      d ∈ Subgroup.normalizer (V : Set G) ∧
      d ∈ Subgroup.normalizer ((V ⊔ Subgroup.zpowers t : Subgroup G) : Set G) ∧
      (fun x => d⁻¹ * x * d) '' {x | u⁻¹ * x ∈ V} = {y | (d⁻¹ * u * d)⁻¹ * y ∈ V} ∧
      (d⁻¹ * u * d)⁻¹ * (d⁻¹ * v * d) ∈ V ∧
      ∀ l : L, (∀ i j, mat (φ l) i j = 0 ∨ mat (φ l) i j = 1) →
        d⁻¹ * v * d * l = l * (d⁻¹ * v * d) := by
  have hn1 : 1 ≤ n := by omega
  set ι : antiSp K →* G := L.subtype.comp φ.symm.toMonoidHom
  set C := Subgroup.centralizer ({t} : Set G)
  set S := V ⊔ Subgroup.zpowers t
  set P := (antiUnipotent K).map ι
  set A₂ := (radA2 K).map ι
  set α := transAct (G := G) φ
  have hιL : ∀ y, ι y ∈ L := fun y => (φ.symm y).2
  have hιmem : ∀ (H : Subgroup (antiSp K)) (y : antiSp K), ι y ∈ H.map ι ↔ y ∈ H :=
    fun H y => coe_symm_mem_map_iff φ H y
  have hLC : L ≤ C := fun l hl =>
    Subgroup.mem_centralizer_singleton_iff.2 (Subgroup.mem_centralizer_iff.1 htLc l hl)
  have hPVC : ∀ x, x ∈ P ↔ x ∈ V ∧ x ∈ C := fun x => by
    rw [← Subgroup.mem_inf, hVP]
  have hA₂L : A₂ ≤ L := by
    rintro _ ⟨y, -, rfl⟩
    exact hιL y
  have htS : t ∈ S := Subgroup.mem_sup_right (Subgroup.mem_zpowers t)
  have hVS : V ≤ S := le_sup_left
  have hCN : ∀ y ∈ C, y ∈ Subgroup.normalizer (L : Set G) := fun y hy => hLn hy
  have hιP : ∀ y, ι y ∈ P ↔ y ∈ antiUnipotent K := hιmem (antiUnipotent K)
  have hιA : ∀ y, ι y ∈ A₂ ↔ y ∈ radA2 K := hιmem (radA2 K)
  have hconjP : ∀ y ∈ C, y ∈ Subgroup.normalizer (V : Set G) → ∀ x ∈ P, y * x * y⁻¹ ∈ P := by
    intro y hyC hyV x hx
    obtain ⟨hxV, hxC⟩ := (hPVC x).1 hx
    exact (hPVC _).2 ⟨(Subgroup.mem_normalizer_iff.1 hyV x).1 hxV,
      C.mul_mem (C.mul_mem hyC hxC) (C.inv_mem hyC)⟩
  have hconjA : ∀ y ∈ C, y ∈ Subgroup.normalizer (V : Set G) → ∀ x ∈ A₂, y * x * y⁻¹ ∈ A₂ := by
    intro y hyC hyV x hx
    have hyt : y * t * y⁻¹ = t := by
      rw [Subgroup.mem_centralizer_singleton_iff.1 hyC, mul_inv_cancel_right]
    have hcl : Subgroup.closure {x | ∃ a ∈ V, x = a⁻¹ * t * a} ≤
        (Subgroup.closure {x | ∃ a ∈ V, x = a⁻¹ * t * a}).comap (MulAut.conj y).toMonoidHom := by
      rw [Subgroup.closure_le]
      rintro _ ⟨a, ha, rfl⟩
      apply Subgroup.subset_closure
      refine ⟨y * a * y⁻¹, (Subgroup.mem_normalizer_iff.1 hyV a).1 ha, ?_⟩
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      calc y * (a⁻¹ * t * a) * y⁻¹ = (y * a * y⁻¹)⁻¹ * (y * t * y⁻¹) * (y * a * y⁻¹) := by
            group
        _ = _ := by rw [hyt]
    have hxB : x ∈ Subgroup.closure {x | ∃ a ∈ V, x = a⁻¹ * t * a} := by
      rw [hgen]
      exact Subgroup.mem_sup_right hx
    have h1 : y * x * y⁻¹ ∈ Subgroup.zpowers t ⊔ A₂ := by
      rw [← hgen]
      exact hcl hxB
    have h2 : y * x * y⁻¹ ∈ L := (Subgroup.mem_normalizer_iff.1 (hCN y hyC) x).1 (hA₂L hx)
    exact sup_zpowers_inf_le ht hA₂L htL
      (fun a ha => Subgroup.mem_centralizer_singleton_iff.1 (hLC (hA₂L ha))) ⟨h1, h2⟩
  obtain ⟨a, haV, hta⟩ : ∃ a ∈ V, u⁻¹ * t * u = a⁻¹ * t * a := by
    have hmem : u⁻¹ * t * u ∈ {x | ∃ g : G, x = g⁻¹ * t * g} ∩ (S : Set G) :=
      ⟨⟨u, rfl⟩, (Subgroup.mem_normalizer_iff''.1 huS t).1 htS⟩
    rw [hclass] at hmem
    exact hmem
  set h := u * a⁻¹ with hhdef
  have hhC : h ∈ C := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    have e : t * u = u * (a⁻¹ * t * a) := by rw [← hta]; group
    calc u * a⁻¹ * t = u * (a⁻¹ * t * a) * a⁻¹ := by group
      _ = t * u * a⁻¹ := by rw [← e]
      _ = t * (u * a⁻¹) := by group
  have haN : a ∈ Subgroup.normalizer (V : Set G) := Subgroup.le_normalizer haV
  have hhV : h ∈ Subgroup.normalizer (V : Set G) := mul_mem huV (inv_mem haN)
  have hhS : h ∈ Subgroup.normalizer (S : Set G) :=
    mul_mem huS (inv_mem (Subgroup.le_normalizer (hVS haV)))
  have hhN := hCN h hhC
  have hαh : ∀ y, ι (α ⟨h, hhN⟩ y) = h * ι y * h⁻¹ := fun y => coe_symm_transAct φ ⟨h, hhN⟩ y
  have hαA : ∀ x, α ⟨h, hhN⟩ x ∈ radA2 K ↔ x ∈ radA2 K := by
    intro x
    rw [← hιA, hαh, ← hιA x]
    refine ⟨fun hx => ?_, hconjA h hhC hhV _⟩
    have := hconjA _ (C.inv_mem hhC) (inv_mem hhV) _ hx
    rwa [show h⁻¹ * (h * ι x * h⁻¹) * h⁻¹⁻¹ = ι x by group] at this
  have hαU : ∀ x ∈ antiUnipotent K, α ⟨h, hhN⟩ x ∈ antiUnipotent K := by
    intro x hx
    rw [← hιP, hαh]
    exact hconjP h hhC hhV _ ((hιP x).2 hx)
  obtain ⟨p', hp'U, r, s, k, hk, hαh'⟩ := exists_conj_mul_dSp_frobAut_pow hn hK _ hαA hαU
  set j := Sp4.dSp r s
  set p : G := ι p'
  have hpP : p ∈ P := (hιP p').2 hp'U
  obtain ⟨hpV, hpC⟩ := (hPVC p).1 hpP
  have hpL : p ∈ L := hιL p'
  have hpN : p ∈ Subgroup.normalizer (L : Set G) := Subgroup.le_normalizer hpL
  have hαp : α ⟨p, hpN⟩ = MulAut.conj p' := by
    rw [transAct_of_mem φ ⟨p, hpN⟩ hpL]
    have e : (⟨p, hpL⟩ : L) = φ.symm p' := rfl
    rw [e, MulEquiv.apply_symm_apply]
  set v := p⁻¹ * h with hvdef
  have hvN : v ∈ Subgroup.normalizer (L : Set G) := mul_mem (inv_mem hpN) hhN
  have hαv : α ⟨v, hvN⟩ = MulAut.conj j * frobAut K ^ k := by
    have e : (⟨v, hvN⟩ : Subgroup.normalizer (L : Set G)) = ⟨p, hpN⟩⁻¹ * ⟨h, hhN⟩ := rfl
    rw [e, map_mul, map_inv, hαp, hαh', map_mul]
    group
  have huv : u⁻¹ * v ∈ V := by
    rw [show u⁻¹ * v = u⁻¹ * p⁻¹ * u * a⁻¹ by rw [hvdef, hhdef]; group]
    exact V.mul_mem ((Subgroup.mem_normalizer_iff''.1 huV _).1 (V.inv_mem hpV)) (V.inv_mem haV)
  have hvC : v ∈ C := C.mul_mem (C.inv_mem hpC) hhC
  have hvS : v ∈ Subgroup.normalizer (S : Set G) :=
    mul_mem (inv_mem (Subgroup.le_normalizer (hVS hpV))) hhS
  have hvV : v ∈ Subgroup.normalizer (V : Set G) :=
    mul_mem (inv_mem (Subgroup.le_normalizer hpV)) hhV
  have hv2V : v ^ 2 ∈ V := by
    rw [pow_two, show v * v = u ^ 2 * (u⁻¹ * (u⁻¹ * v) * u) * (u⁻¹ * v) by group]
    exact V.mul_mem (V.mul_mem hu2 ((Subgroup.mem_normalizer_iff''.1 huV _).1 huv)) huv
  have hv2P : v ^ 2 ∈ P := (hPVC _).2 ⟨hv2V, C.pow_mem hvC 2⟩
  obtain ⟨y, hyU, hyv⟩ := hv2P
  have hαv2 : MulAut.conj y = (MulAut.conj j * frobAut K ^ k) ^ 2 := by
    have hv2L : v ^ 2 ∈ L := hyv ▸ hιL y
    have e : (⟨v, hvN⟩ : Subgroup.normalizer (L : Set G)) ^ 2 = ⟨v ^ 2, pow_mem hvN 2⟩ :=
      Subtype.ext (Subgroup.coe_pow _ _ 2)
    rw [← hαv, ← map_pow, e, transAct_of_mem φ _ hv2L]
    have e' : (⟨v ^ 2, hv2L⟩ : L) = φ.symm y := Subtype.ext hyv.symm
    rw [e', MulEquiv.apply_symm_apply]
  obtain ⟨hy1, hjj, hkn⟩ := eq_one_of_conj_eq_sq hn1 hK hk hyU hαv2
  have hv2 : v ^ 2 = 1 := by rw [← hyv, hy1, map_one]
  have huS' : ∀ w, u⁻¹ * w ∈ V → w ∉ S := by
    intro w hw hwS
    apply hu
    rw [show u = w * (u⁻¹ * w)⁻¹ by group]
    exact S.mul_mem hwS (S.inv_mem (hVS hw))
  have hk0 : k ≠ 0 := by
    rintro rfl
    rw [pow_zero, MulAut.one_apply] at hjj
    have hj1 : j = 1 := dSp_eq_one_of_mul_self hjj
    have hα1 : α ⟨v, hvN⟩ = 1 := by rw [hαv, hj1, map_one, pow_zero, mul_one]
    have hvt : v ∈ Subgroup.zpowers t := by
      rw [← hCL]
      exact ⟨hvC, (transAct_eq_one_iff φ _).1 hα1⟩
    exact huS' v huv (Subgroup.mem_sup_right hvt)
  have hnk : n = 2 * k := hkn.resolve_left hk0
  have hn2 : n / 2 = k := by omega
  obtain ⟨b, c, hjbc⟩ := exists_dSp_eq_mul_frob_inv (m := k) (by omega) (by rw [hK, hnk]) hjj
  set e := Sp4.dSp b c with hedef
  set d : G := ι e with hddef
  have hdL : d ∈ L := hιL e
  have hdN : d ∈ Subgroup.normalizer (L : Set G) := Subgroup.le_normalizer hdL
  have hdC : d ∈ C := hLC hdL
  have hαd : α ⟨d, hdN⟩ = MulAut.conj e := by
    rw [transAct_of_mem φ _ hdL]
    have e' : (⟨d, hdL⟩ : L) = φ.symm e := rfl
    rw [e', MulEquiv.apply_symm_apply]
  set vd := d⁻¹ * v * d
  have hvdN : vd ∈ Subgroup.normalizer (L : Set G) := mul_mem (mul_mem (inv_mem hdN) hvN) hdN
  have hαvd : α ⟨vd, hvdN⟩ = frobAut K ^ k := by
    have e' : (⟨vd, hvdN⟩ : Subgroup.normalizer (L : Set G)) =
        ⟨d, hdN⟩⁻¹ * ⟨v, hvN⟩ * ⟨d, hdN⟩ := rfl
    rw [e', map_mul, map_mul, map_inv, hαd, hαv]
    exact conj_inv_mul_conj_mul_conj _ e j hjbc
  have hfrob : ∀ l : L, ((φ.symm ((frobAut K ^ (n / 2)) (φ l)) : L) : G) = vd * l * vd⁻¹ := by
    intro l
    have h1 := coe_symm_transAct φ ⟨vd, hvdN⟩ (φ l)
    rw [hαvd, MulEquiv.symm_apply_apply] at h1
    rw [hn2]
    exact h1
  have hnotLC : ∀ w (hw : w ∈ Subgroup.normalizer (L : Set G)),
      (∀ g : antiSp K, α ⟨w, hw⟩ ≠ MulAut.conj g) →
      ¬ ∃ l ∈ L, ∃ c ∈ Subgroup.centralizer (L : Set G), w = l * c := by
    rintro w hw hne ⟨l, hl, c, hc, rfl⟩
    have hlN : l ∈ Subgroup.normalizer (L : Set G) := Subgroup.le_normalizer hl
    have hcN : c ∈ Subgroup.normalizer (L : Set G) := Subgroup.centralizer_le_normalizer _ hc
    have e' : (⟨l * c, hw⟩ : Subgroup.normalizer (L : Set G)) = ⟨l, hlN⟩ * ⟨c, hcN⟩ := rfl
    apply hne (φ ⟨l, hl⟩)
    rw [e', map_mul, transAct_of_mem φ _ hl, (transAct_eq_one_iff φ _).2 hc, mul_one]
  have hconjT : ∀ (b' c' : Kˣ) (H : Subgroup (antiSp K)),
      (∀ z ∈ H, Sp4.dSp b' c' * z * (Sp4.dSp b' c')⁻¹ ∈ H) →
      ∀ x ∈ H.map ι, ι (Sp4.dSp b' c') * x * (ι (Sp4.dSp b' c'))⁻¹ ∈ H.map ι := by
    rintro b' c' H hH _ ⟨z, hz, rfl⟩
    rw [← map_inv, ← map_mul, ← map_mul]
    exact ⟨_, hH z hz, rfl⟩
  have hdinv : d⁻¹ = ι (Sp4.dSp b⁻¹ c⁻¹) := by rw [hddef, hedef, ← map_inv, Sp4.dSp_inv]
  have hdmap : ∀ H : Subgroup (antiSp K),
      (∀ b' c' : Kˣ, ∀ z ∈ H, Sp4.dSp b' c' * z * (Sp4.dSp b' c')⁻¹ ∈ H) →
      d ∈ Subgroup.normalizer ((H.map ι : Subgroup G) : Set G) := by
    intro H hH
    refine mem_normalizer_of_conj_mem_of_inv (fun x hx => hconjT b c H (hH b c) x hx) fun x hx => ?_
    have := hconjT b⁻¹ c⁻¹ H (hH b⁻¹ c⁻¹) x hx
    rwa [← hdinv, inv_inv] at this
  have hdP : d ∈ Subgroup.normalizer (P : Set G) :=
    hdmap _ fun b' c' _ hz => dSp_conj_mem_antiUnipotent b' c' hz
  have hdA : d ∈ Subgroup.normalizer (A₂ : Set G) :=
    hdmap _ fun b' c' _ hz => dSp_conj_mem_radA2 b' c' hz
  have hdJ : d ∈ Subgroup.normalizer {x : G | ∃ r s : Kˣ, x = φ.symm (Sp4.dSp r⁻¹ s⁻¹)} := by
    have hcomm : ∀ b' c' r' s' : Kˣ,
        ι (Sp4.dSp b' c') * ι (Sp4.dSp r' s') * (ι (Sp4.dSp b' c'))⁻¹ = ι (Sp4.dSp r' s') := by
      intro b' c' r' s'
      rw [← map_inv, ← map_mul, ← map_mul, Sp4.dSp_inv, Sp4.dSp_mul, Sp4.dSp_mul, mul_comm b' r',
        mul_comm c' s', mul_inv_cancel_right, mul_inv_cancel_right]
    refine mem_normalizer_of_conj_mem_of_inv ?_ ?_
    · rintro _ ⟨r', s', rfl⟩
      exact ⟨r', s', hcomm b c r'⁻¹ s'⁻¹⟩
    · rintro _ ⟨r', s', rfl⟩
      refine ⟨r', s', ?_⟩
      have := hcomm b⁻¹ c⁻¹ r'⁻¹ s'⁻¹
      rwa [← hdinv, inv_inv] at this
  have hdV : d ∈ Subgroup.normalizer (V : Set G) := by
    have := hJ₀V b⁻¹ c⁻¹
    simp only [inv_inv] at this
    exact this
  have hdS : d ∈ Subgroup.normalizer (S : Set G) := by
    have key : ∀ g ∈ C, g ∈ Subgroup.normalizer (V : Set G) → ∀ x ∈ S, g * x * g⁻¹ ∈ S := by
      intro g hgC hgV x hx
      have hle : S ≤ S.comap (MulAut.conj g).toMonoidHom := by
        refine sup_le (fun y hy => hVS ((Subgroup.mem_normalizer_iff.1 hgV y).1 hy))
          ((Subgroup.zpowers_le).2 ?_)
        show g * t * g⁻¹ ∈ S
        rw [Subgroup.mem_centralizer_singleton_iff.1 hgC, mul_inv_cancel_right]
        exact htS
      exact hle hx
    refine mem_normalizer_of_conj_mem_of_inv (key d hdC hdV) fun x hx => ?_
    have := key d⁻¹ (C.inv_mem hdC) (inv_mem hdV) x hx
    rwa [inv_inv] at this
  have hcoset : (fun x => d⁻¹ * x * d) '' {x | u⁻¹ * x ∈ V} = {y | (d⁻¹ * u * d)⁻¹ * y ∈ V} := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      show (d⁻¹ * u * d)⁻¹ * (d⁻¹ * x * d) ∈ V
      rw [show (d⁻¹ * u * d)⁻¹ * (d⁻¹ * x * d) = d⁻¹ * (u⁻¹ * x) * d by group]
      exact (Subgroup.mem_normalizer_iff''.1 hdV _).1 hx
    · intro hy
      refine ⟨d * y * d⁻¹, ?_, by group⟩
      show u⁻¹ * (d * y * d⁻¹) ∈ V
      rw [show u⁻¹ * (d * y * d⁻¹) = d * ((d⁻¹ * u * d)⁻¹ * y) * d⁻¹ by group]
      exact (Subgroup.mem_normalizer_iff.1 hdV _).1 hy
  have hvdcoset : (d⁻¹ * u * d)⁻¹ * (d⁻¹ * v * d) ∈ V := by
    rw [show (d⁻¹ * u * d)⁻¹ * (d⁻¹ * v * d) = d⁻¹ * (u⁻¹ * v) * d by group]
    exact (Subgroup.mem_normalizer_iff''.1 hdV _).1 huv
  have hcent01 : ∀ l : L, (∀ i j, mat (φ l) i j = 0 ∨ mat (φ l) i j = 1) → vd * l = l * vd := by
    intro l hl
    have h1 := hfrob l
    rw [frobAut_pow_eq_self _ hl, MulEquiv.symm_apply_apply] at h1
    calc vd * l = vd * l * vd⁻¹ * vd := by group
      _ = l * vd := by rw [← h1]
  refine ⟨⟨k, by omega⟩, v, d, huv, hvC, hv2, ?_, ⟨b⁻¹, c⁻¹, by simp only [inv_inv]; rfl⟩,
    hfrob, ?_, hdC, hdP, hdA, hdJ, hdV, hdS, hcoset, hvdcoset, hcent01⟩
  · intro hv1
    refine huS' 1 ?_ S.one_mem
    rw [← hv1]
    exact huv
  · rintro w (rfl | rfl)
    · refine ⟨hvS, hvV, hvC, hnotLC _ hvN fun g => ?_⟩
      rw [hαv]
      exact conj_mul_frobAut_pow_ne_conj hn1 hK hk0 hk j g
    · refine ⟨mul_mem (mul_mem (inv_mem hdS) hvS) hdS, mul_mem (mul_mem (inv_mem hdV) hvV) hdV,
        C.mul_mem (C.mul_mem (C.inv_mem hdC) hvC) hdC, hnotLC _ hvdN fun g => ?_⟩
      rw [hαvd]
      have := conj_mul_frobAut_pow_ne_conj hn1 hK hk0 hk 1 g
      rwa [map_one, one_mul] at this


end CFSG.LocalAnalysis.SymplecticFourStandard

