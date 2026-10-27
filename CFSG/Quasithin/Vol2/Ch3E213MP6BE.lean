module

public import CFSG.Quasithin.SteinbergBSSymplecticRoots
public import CFSG.Quasithin.Vol2.Ch3E213MP6BB
public import CFSG.Quasithin.Vol2.Ch3E213MP6CA
public import CFSG.Quasithin.Vol2.Ch3E213MP6CC

public section

namespace CFSG.Quasithin.Ch3E213M.P6B

open CFSG.ComponentClassification.UnbalancedCatalog.SpChain (antiSp glMat uElt antiSp_ext
  antiUnipotent antiUnipotentCenter minorAut uElt_mem_antiUnipotent)
open CFSG.Quasithin.SteinbergBS (rootLong conj_uElt_coords upper_relations upper_diag_ne_zero
  minorAut_uElt minorAut_odd_pow_uElt zero_pow_two_pow upper_of_mem_normalizer
  map_minorAut_pow_antiUnipotent)
open CFSG.QuasithinUnique.Setup.X7b (uElt_inj uElt_zero_eq_one)

variable {k : Type} [Field k] [CharP k 2]

theorem conj_uElt_center {h : antiSp k} (hh : IsUpper h) (b c : k) :
    h * uElt 0 b c 0 * h⁻¹ =
      uElt 0 (glMat (h : GL (Fin 4) k) 0 0 * glMat (h : GL (Fin 4) k) 1 1 * b)
        (glMat (h : GL (Fin 4) k) 0 0 ^ 2 * c) 0 := by
  obtain ⟨a', b', c', d', he⟩ :=
    (Subgroup.mem_normalizer_iff.mp (mem_normalizer_of_isUpper hh) _).mp
      (uElt_mem_antiUnipotent 0 b c 0)
  obtain ⟨e1, e2, e3, e4⟩ := conj_uElt_coords hh he
  obtain ⟨r1, r2, r3⟩ := upper_relations hh
  obtain ⟨-, d1, d2, -⟩ := upper_diag_ne_zero hh
  set M := glMat (h : GL (Fin 4) k) with hM
  have ha' : a' = 0 := by
    rw [mul_zero] at e1
    exact (mul_eq_zero.1 e1).resolve_right d1
  have hd' : d' = 0 := by
    rw [mul_zero] at e2
    exact (mul_eq_zero.1 e2).resolve_right d2
  subst ha' hd'
  have hb3 : b' * M 2 2 = M 0 0 * b := by linear_combination e3
  have hb' : b' = M 0 0 * M 1 1 * b := by
    linear_combination M 1 1 * hb3 - b' * r2
  have hc3 : c' * M 3 3 = M 0 0 * c := by
    rw [hb'] at e4
    linear_combination e4 + M 0 0 * b * r3 - M 0 1 * b * r1
  have hc' : c' = M 0 0 ^ 2 * c := by
    linear_combination M 0 0 * hc3 - c' * r1
  rw [he, hb', hc']

theorem sigma_uElt_center [Finite k] {h : antiSp k} (hh : IsUpper h) (r : ℕ) (b c : k) :
    (MulAut.conj h * minorAut k ^ (2 * r + 1)) (uElt 0 b c 0) =
      uElt 0 (glMat (h : GL (Fin 4) k) 0 0 * glMat (h : GL (Fin 4) k) 1 1 * c ^ 2 ^ r)
        (glMat (h : GL (Fin 4) k) 0 0 ^ 2 * (b ^ 2 ^ r) ^ 2) 0 := by
  rw [MulAut.mul_apply, minorAut_odd_pow_uElt]
  simp only [zero_pow_two_pow, zero_mul, mul_zero, add_zero, ne_eq, OfNat.ofNat_ne_zero,
    not_false_eq_true, zero_pow]
  rw [MulAut.conj_apply, conj_uElt_center hh]

omit [CharP k 2] in
theorem eq_of_pow_two_pow_eq [CharP k 2] {x y : k} {r : ℕ} (h : x ^ 2 ^ r = y ^ 2 ^ r) :
    x = y := by
  have h1 : (x - y) ^ 2 ^ r = 0 := by rw [sub_pow_char_pow, h, sub_self]
  exact sub_eq_zero.mp (pow_eq_zero_iff (pow_ne_zero r two_ne_zero) |>.mp h1)

theorem eq_zero_of_long_mem {W : Subgroup (antiSp k)} (hl : W ⊓ rootLong k = ⊥) {c : k}
    (hc : uElt 0 0 c 0 ∈ W) : c = 0 := by
  have h1 : uElt 0 0 c 0 ∈ W ⊓ rootLong k := ⟨hc, c, rfl⟩
  rw [hl, Subgroup.mem_bot, ← uElt_zero_eq_one] at h1
  exact (uElt_inj h1).2.2.1

omit [CharP k 2] in
theorem quad_key {X Y ν b c : k} {r : ℕ} (hX : X ≠ 0) (hb : b ≠ 0) (hc : c = ν * b ^ 2)
    (e : X ^ 2 * (b ^ 2 ^ r) ^ 2 = ν * (X * Y * c ^ 2 ^ r) ^ 2) :
    ν * Y ^ 2 * (ν ^ 2 ^ r) ^ 2 * (b ^ 2 ^ r) ^ 2 = 1 := by
  have hc' : c ^ 2 ^ r = ν ^ 2 ^ r * (b ^ 2 ^ r) ^ 2 := by
    rw [hc, mul_pow, ← pow_mul, ← pow_mul, mul_comm 2 (2 ^ r)]
  rw [hc'] at e
  have hB : X ^ 2 * (b ^ 2 ^ r) ^ 2 ≠ 0 := mul_ne_zero (pow_ne_zero _ hX)
    (pow_ne_zero _ (pow_ne_zero _ hb))
  have e' : X ^ 2 * (b ^ 2 ^ r) ^ 2 * (ν * Y ^ 2 * (ν ^ 2 ^ r) ^ 2 * (b ^ 2 ^ r) ^ 2 - 1) = 0 := by
    linear_combination -e
  exact sub_eq_zero.mp ((mul_eq_zero.mp e').resolve_left hB)

theorem false_of_quad [Finite k] {W : Subgroup (antiSp k)} (hWZ : W ≤ antiUnipotentCenter k)
    (hsp : SpansCenter W) {h : antiSp k} (hh : IsUpper h) {r : ℕ}
    (hσ : ∀ w ∈ W, (MulAut.conj h * minorAut k ^ (2 * r + 1)) w ∈ W) {ν : k}
    (hν : ∀ b c : k, uElt 0 b c 0 ∈ W → c = ν * b ^ 2) : False := by
  obtain ⟨b₁, c₁, b₂, c₂, h₁, h₂, hb₁, hdet⟩ := exists_indep hWZ hsp
  have e₁ := hν _ _ h₁
  have e₂ := hν _ _ h₂
  set M := glMat (h : GL (Fin 4) k) with hM
  obtain ⟨d0, d1, -, -⟩ := upper_diag_ne_zero hh
  have hb₂ : b₂ ≠ 0 := by
    rintro rfl
    apply hdet
    rw [e₂]
    ring
  have hν0 : ν ≠ 0 := by
    rintro rfl
    apply hdet
    rw [e₁, e₂]
    ring
  have key : ∀ b c : k, uElt 0 b c 0 ∈ W → b ≠ 0 →
      ν * M 1 1 ^ 2 * (ν ^ 2 ^ r) ^ 2 * ((b ^ 2 ^ r) ^ 2) = 1 := by
    intro b c hz hb
    have hσz := hσ _ hz
    rw [sigma_uElt_center hh, ← hM] at hσz
    exact quad_key d0 hb (hν _ _ hz) (hν _ _ hσz)
  have k₁ := key _ _ h₁ hb₁
  have k₂ := key _ _ h₂ hb₂
  have hκ : ν * M 1 1 ^ 2 * (ν ^ 2 ^ r) ^ 2 ≠ 0 :=
    mul_ne_zero (mul_ne_zero hν0 (pow_ne_zero _ d1)) (pow_ne_zero _ (pow_ne_zero _ hν0))
  have hsq : (b₁ ^ 2 ^ r) ^ 2 = (b₂ ^ 2 ^ r) ^ 2 :=
    mul_left_cancel₀ hκ (k₁.trans k₂.symm)
  have hb : b₁ = b₂ := by
    rw [← pow_mul, ← pow_mul, ← pow_succ] at hsq
    exact eq_of_pow_two_pow_eq hsq
  apply hdet
  rw [e₁, e₂, hb]
  ring

theorem eq_of_mem_orth {Q : QuadraticForm k (Fin 4 → k)}
    (hQ : ∀ x y, QuadraticMap.polar Q x y = spBil x y) {b c : k} (hb : b ≠ 0)
    (hz : ∀ x, Q (natAct (uElt 0 b c 0 : antiSp k) x) = Q x) :
    c = Q (Pi.single 1 1) * b ^ 2 := by
  have hpol : ∀ x y, Q (x + y) = Q x + Q y + spBil x y := fun x y => by
    rw [← hQ]
    unfold QuadraticMap.polar
    ring
  have hz2 : natAct (uElt 0 b c 0 : antiSp k) (Pi.single 2 1) =
      Pi.single 2 1 + b • Pi.single 0 1 := by
    rw [natAct_uElt_center]
    funext i
    fin_cases i <;> simp
  have hz3 : natAct (uElt 0 b c 0 : antiSp k) (Pi.single 3 1) =
      Pi.single 3 1 + c • Pi.single 0 1 + b • Pi.single 1 1 := by
    rw [natAct_uElt_center]
    funext i
    fin_cases i <;> simp
  have hs2 : spBil (Pi.single 2 1 : Fin 4 → k) (b • Pi.single 0 1) = 0 := by
    simp [spBil_apply]
  have hs3 : spBil (Pi.single 3 1 : Fin 4 → k) (c • Pi.single 0 1) = c := by
    simp [spBil_apply]
  have hs3' : spBil (Pi.single 3 1 + c • Pi.single 0 1 : Fin 4 → k) (b • Pi.single 1 1) = 0 := by
    simp [spBil_apply]
  have q2 := hz (Pi.single 2 1)
  rw [hz2, hpol, QuadraticMap.map_smul, hs2, add_zero] at q2
  have h0 : Q (Pi.single 0 1) = 0 := by
    have : b * b * Q (Pi.single 0 1) = 0 := by linear_combination q2
    exact (mul_eq_zero.mp this).resolve_left (mul_ne_zero hb hb)
  have q3 := hz (Pi.single 3 1)
  rw [hz3, hpol, hpol, QuadraticMap.map_smul, QuadraticMap.map_smul, hs3, hs3', h0] at q3
  have h2 : (2 : k) = 0 := CharTwo.two_eq_zero
  linear_combination q3 - b ^ 2 * Q (Pi.single 1 1) * h2

theorem not_g41Orth_of_inv [Finite k] {W : Subgroup (antiSp k)} (hWZ : W ≤ antiUnipotentCenter k)
    (hl : W ⊓ rootLong k = ⊥) (hsp : SpansCenter W) {h : antiSp k} (hh : IsUpper h) {r : ℕ}
    (hσ : ∀ w ∈ W, (MulAut.conj h * minorAut k ^ (2 * r + 1)) w ∈ W) {G₀ : Subgroup (antiSp k)}
    (hWG : W ≤ G₀) : ¬ G41OrthW G₀ := by
  rintro ⟨Q, hQ, hG⟩
  refine false_of_quad hWZ hsp hh hσ (ν := Q (Pi.single 1 1)) fun b c hz => ?_
  by_cases hb : b = 0
  · subst hb
    rw [eq_zero_of_long_mem hl hz]
    ring
  · exact eq_of_mem_orth hQ hb (hG _ (hWG hz))

section Minor

variable [Finite k]

theorem minorAut_uElt_center (b c : k) :
    minorAut k (uElt 0 b c 0) = uElt 0 c (b ^ 2) 0 := by
  rw [minorAut_uElt]
  congr 1 <;> ring

theorem map_minorAut_le_center {W : Subgroup (antiSp k)} (hWZ : W ≤ antiUnipotentCenter k) :
    W.map (minorAut k).toMonoidHom ≤ antiUnipotentCenter k := by
  rintro _ ⟨w, hw, rfl⟩
  obtain ⟨b, c, rfl⟩ := hWZ hw
  exact ⟨c, b ^ 2, minorAut_uElt_center b c⟩

theorem eq_zero_of_short_mem {W : Subgroup (antiSp k)} (hl : W ⊓ rootLong k = ⊥) {h : antiSp k}
    (hh : IsUpper h) {r : ℕ} (hσ : ∀ w ∈ W, (MulAut.conj h * minorAut k ^ (2 * r + 1)) w ∈ W)
    {b : k} (hb : uElt 0 b 0 0 ∈ W) : b = 0 := by
  have h1 := hσ _ hb
  rw [sigma_uElt_center hh, zero_pow (pow_ne_zero _ two_ne_zero), mul_zero] at h1
  have h2 := eq_zero_of_long_mem hl h1
  obtain ⟨d0, -, -, -⟩ := upper_diag_ne_zero hh
  have h3 : (b ^ 2 ^ r) ^ 2 = 0 := (mul_eq_zero.mp h2).resolve_left (pow_ne_zero _ d0)
  exact pow_eq_zero_iff (pow_ne_zero r two_ne_zero) |>.mp (pow_eq_zero_iff two_ne_zero |>.mp h3)

theorem map_minorAut_inf_rootLong {W : Subgroup (antiSp k)} (hWZ : W ≤ antiUnipotentCenter k)
    (hl : W ⊓ rootLong k = ⊥) {h : antiSp k} (hh : IsUpper h) {r : ℕ}
    (hσ : ∀ w ∈ W, (MulAut.conj h * minorAut k ^ (2 * r + 1)) w ∈ W) :
    W.map (minorAut k).toMonoidHom ⊓ rootLong k = ⊥ := by
  rw [eq_bot_iff]
  rintro _ ⟨⟨w, hw, rfl⟩, t, ht⟩
  obtain ⟨b, c, rfl⟩ := hWZ hw
  change minorAut k (uElt 0 b c 0) = uElt 0 0 t 0 at ht
  rw [minorAut_uElt_center] at ht
  obtain ⟨-, hc, -, -⟩ := uElt_inj ht
  subst hc
  rw [eq_zero_of_short_mem hl hh hσ hw]
  rw [Subgroup.mem_bot, MulEquiv.coe_toMonoidHom, uElt_zero_eq_one, map_one]

theorem spansCenter_map_minorAut {W : Subgroup (antiSp k)} (hWZ : W ≤ antiUnipotentCenter k)
    (hsp : SpansCenter W) {h : antiSp k} (hh : IsUpper h) {r : ℕ}
    (hσ : ∀ w ∈ W, (MulAut.conj h * minorAut k ^ (2 * r + 1)) w ∈ W) :
    SpansCenter (W.map (minorAut k).toMonoidHom) := by
  intro α β hαβ hle
  have hco : ∀ b c : k, uElt 0 b c 0 ∈ W → ∃ t : k, c = t * β ∧ b ^ 2 = t * α := by
    intro b c hz
    obtain ⟨t, ht⟩ := hle ⟨_, hz, rfl⟩
    change minorAut k (uElt 0 b c 0) = _ at ht
    rw [minorAut_uElt_center] at ht
    obtain ⟨-, h1, h2, -⟩ := uElt_inj ht
    exact ⟨t, h1, h2⟩
  by_cases hα : α = 0
  ·
    refine hsp 1 0 (Or.inl one_ne_zero) fun w hw => ?_
    obtain ⟨b, c, rfl⟩ := hWZ hw
    obtain ⟨t, -, ht⟩ := hco b c hw
    rw [hα, mul_zero, pow_eq_zero_iff two_ne_zero] at ht
    exact ⟨c, by rw [ht, mul_zero, mul_one]⟩
  · refine false_of_quad hWZ hsp hh hσ (ν := β / α) fun b c hz => ?_
    obtain ⟨t, h1, h2⟩ := hco b c hz
    rw [h1, h2]
    field_simp

theorem isUpper_minorAut {h : antiSp k} (hh : IsUpper h) : IsUpper (minorAut k h) := by
  have hN := mem_normalizer_of_isUpper hh
  have hU := map_minorAut_pow_antiUnipotent (F := k) 1
  rw [pow_one] at hU
  apply upper_of_mem_normalizer
  rw [Subgroup.mem_normalizer_iff] at hN ⊢
  intro u
  constructor
  · intro hu
    rw [← hU] at hu ⊢
    obtain ⟨u', hu', rfl⟩ := hu
    exact ⟨h * u' * h⁻¹, (hN u').mp hu', by simp⟩
  · intro hu
    rw [← hU] at hu ⊢
    obtain ⟨u', hu', hu'e⟩ := hu
    refine ⟨(minorAut k).symm u, (hN _).mpr ?_, by simp⟩
    have : h * (minorAut k).symm u * h⁻¹ = u' := by
      apply (minorAut k).injective
      simp only [MulEquiv.coe_toMonoidHom] at hu'e
      rw [hu'e, map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply]
    rw [this]
    exact hu'

theorem minorAut_inv_map {W : Subgroup (antiSp k)} {h : antiSp k} {j : ℕ}
    (hσ : ∀ w ∈ W, (MulAut.conj h * minorAut k ^ j) w ∈ W) :
    ∀ w ∈ W.map (minorAut k).toMonoidHom,
      (MulAut.conj (minorAut k h) * minorAut k ^ j) w ∈ W.map (minorAut k).toMonoidHom := by
  rintro _ ⟨w, hw, rfl⟩
  refine ⟨(MulAut.conj h * minorAut k ^ j) w, hσ w hw, ?_⟩
  simp only [MulEquiv.coe_toMonoidHom, MulAut.mul_apply, MulAut.conj_apply, map_mul, map_inv]
  rw [← MulAut.mul_apply, ← pow_succ', pow_succ, MulAut.mul_apply]

theorem minorAut_wLong : minorAut k wLong = wLong := by
  refine antiSp_ext ?_
  rw [CFSG.ComponentClassification.UnbalancedCatalog.SpChain.glMat_minorAut, glMat_wLong]
  ext A B
  fin_cases A <;> fin_cases B <;>
    simp [CFSG.ComponentClassification.UnbalancedCatalog.SpChain.minorMap_apply,
      CFSG.ComponentClassification.UnbalancedCatalog.SpChain.minorIdx_zero,
      CFSG.ComponentClassification.UnbalancedCatalog.SpChain.minorIdx_one,
      CFSG.ComponentClassification.UnbalancedCatalog.SpChain.minorIdx_two,
      CFSG.ComponentClassification.UnbalancedCatalog.SpChain.minorIdx_three,
      CFSG.ComponentClassification.UnbalancedCatalog.SpChain.minorJ_apply, CharTwo.neg_eq]

theorem map_minorAut_sup_conj (W : Subgroup (antiSp k)) (g : antiSp k) :
    (W ⊔ W.map (MulAut.conj g).toMonoidHom).map (minorAut k).toMonoidHom =
      W.map (minorAut k).toMonoidHom ⊔
        (W.map (minorAut k).toMonoidHom).map (MulAut.conj (minorAut k g)).toMonoidHom := by
  rw [Subgroup.map_sup, Subgroup.map_map, Subgroup.map_map]
  congr 2
  ext x
  simp

end Minor

end CFSG.Quasithin.Ch3E213M.P6B
