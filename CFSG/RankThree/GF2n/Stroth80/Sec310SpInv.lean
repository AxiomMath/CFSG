module

public import CFSG.ClassicalGroups.Alternating.PointRadicalFixedCard
public import CFSG.ClassicalGroups.Symplectic.StandardForm

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG.ClassicalGroups.Symplectic CFSG.ClassicalGroups.Alternating CFSG.Open
open Matrix

namespace LspNorm

section Basic

variable {m : ℕ} {K : Type} [Field K]

@[expose] noncomputable def siegelMap (u w : Fin m ⊕ Fin m → K) (c : K) (x : Fin m ⊕ Fin m → K) :
    Fin m ⊕ Fin m → K :=
  x + spForm m K x u • w + spForm m K x w • u + (c * spForm m K x u) • u

abbrev InSub (L : Subgroup (GL (Fin m ⊕ Fin m) K)) (u w : Fin m ⊕ Fin m → K)
    (c : K) : Prop :=
  ∃ l ∈ L, ∀ x : Fin m ⊕ Fin m → K,
    (l : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) *ᵥ x = siegelMap u w c x

theorem gl_eq_of_mulVec {g h : GL (Fin m ⊕ Fin m) K}
    (H : ∀ x : Fin m ⊕ Fin m → K, (g : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) *ᵥ x =
      (h : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) *ᵥ x) : g = h :=
  Units.ext (Matrix.toLin'.injective (LinearMap.ext H))

theorem mulVec_units_mul (g h : GL (Fin m ⊕ Fin m) K) (x : Fin m ⊕ Fin m → K) :
    ((g * h : GL (Fin m ⊕ Fin m) K) : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) *ᵥ x =
      (g : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) *ᵥ
        ((h : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) *ᵥ x) := by
  rw [Units.val_mul, Matrix.mulVec_mulVec]

theorem vec_add_self [CharP K 2] (v : Fin m ⊕ Fin m → K) : v + v = 0 := by
  rw [← two_smul K v, CharTwo.two_eq_zero, zero_smul]

theorem smul_add_self_char2 [CharP K 2] (a : K) (v : Fin m ⊕ Fin m → K) :
    a • v + a • v = 0 := by
  rw [← add_smul, CharTwo.add_self_eq_zero, zero_smul]

theorem spForm_symm_char2 [CharP K 2] (x y : Fin m ⊕ Fin m → K) :
    spForm m K x y = spForm m K y x := by
  have h := spForm_isAlt.neg_eq x y
  rwa [CharTwo.neg_eq] at h

theorem spForm_zero_symm {u w : Fin m ⊕ Fin m → K} (h : spForm m K u w = 0) :
    spForm m K w u = 0 := by
  rw [← spForm_isAlt.neg_eq u w, h, neg_zero]

theorem siegelMap_comp {u w w' : Fin m ⊕ Fin m → K} {c c' : K}
    (hw : spForm m K u w = 0) (hw' : spForm m K u w' = 0) (x : Fin m ⊕ Fin m → K) :
    siegelMap u w c (siegelMap u w' c' x) =
      siegelMap u (w + w') (c + c' + spForm m K w' w) x := by
  have hw'u := spForm_zero_symm hw'
  have hwu := spForm_zero_symm hw
  simp only [siegelMap, map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply,
    smul_eq_mul, spForm_self, hw, hw', hwu, hw'u, mul_zero, zero_mul, add_zero, zero_add,
    smul_zero, zero_smul]
  module

theorem inSub_comp {L : Subgroup (GL (Fin m ⊕ Fin m) K)} {u w w' : Fin m ⊕ Fin m → K}
    {c c' : K} (hw : spForm m K u w = 0) (hw' : spForm m K u w' = 0)
    (h : InSub L u w c) (h' : InSub L u w' c') :
    InSub L u (w + w') (c + c' + spForm m K w' w) := by
  obtain ⟨l, hl, hlx⟩ := h
  obtain ⟨l', hl', hlx'⟩ := h'
  refine ⟨l * l', L.mul_mem hl hl', fun x => ?_⟩
  rw [mulVec_units_mul, hlx', hlx, siegelMap_comp hw hw' x]

theorem siegelMap_smul_u [CharP K 2] (u : Fin m ⊕ Fin m → K) (a c : K) :
    siegelMap u (a • u) c = siegelMap u 0 c := by
  funext x
  have h := smul_add_self_char2 (a * spForm m K x u) u
  simp only [siegelMap, map_smul, smul_eq_mul, map_zero, LinearMap.zero_apply, smul_zero,
    zero_smul, add_zero, zero_add]
  linear_combination (norm := module) h

theorem mulVec_inv_of_invol (τ : GL (Fin m ⊕ Fin m) K)
    (hinv : ∀ v : Fin m ⊕ Fin m → K, (τ : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) *ᵥ
      ((τ : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) *ᵥ v) = v)
    (v : Fin m ⊕ Fin m → K) :
    ((τ⁻¹ : GL (Fin m ⊕ Fin m) K) : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) *ᵥ v =
      (τ : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) *ᵥ v := by
  have h1 : ((τ⁻¹ : GL (Fin m ⊕ Fin m) K) : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) *ᵥ
      ((τ : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) *ᵥ
        ((τ : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) *ᵥ v)) =
      (τ : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) *ᵥ v := by
    rw [← mulVec_units_mul, inv_mul_cancel, Units.val_one, Matrix.one_mulVec]
  rwa [hinv v] at h1

theorem tsp_transv_apply (z : Fin m ⊕ Fin m → K) (e : K) (v : Fin m ⊕ Fin m → K) :
    ((((spEquiv (m := m) (K := K)).symm (Tsp spForm_isAlt z e) : StatedSp m K) :
      GL (Fin m ⊕ Fin m) K) : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) *ᵥ v =
      v + (e * spForm m K v z) • z := by
  have h := spEquiv_app ((spEquiv (m := m) (K := K)).symm (Tsp spForm_isAlt z e)) v
  rw [MulEquiv.apply_symm_apply] at h
  exact h.symm.trans (Tsp_app spForm_isAlt z e v)

theorem exists_transv [CharP K 2] (z : Fin m ⊕ Fin m → K) (e : K) :
    ∃ τ : GL (Fin m ⊕ Fin m) K, τ ∈ StatedSp m K ∧
      (∀ v : Fin m ⊕ Fin m → K, (τ : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) *ᵥ v =
        v + (e * spForm m K v z) • z) ∧
      ∀ v : Fin m ⊕ Fin m → K,
        ((τ⁻¹ : GL (Fin m ⊕ Fin m) K) : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) *ᵥ v =
          (τ : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) *ᵥ v := by
  let A : GL (Fin m ⊕ Fin m) K :=
    ((spEquiv (m := m) (K := K)).symm (Tsp spForm_isAlt z e) : StatedSp m K)
  have hA : A ∈ StatedSp m K := ((spEquiv (m := m) (K := K)).symm (Tsp spForm_isAlt z e)).2
  have hv : ∀ v : Fin m ⊕ Fin m → K,
      (A : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) *ᵥ v = v + (e * spForm m K v z) • z :=
    fun v => tsp_transv_apply z e v
  have hinv : ∀ v : Fin m ⊕ Fin m → K,
      (A : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) *ᵥ
        ((A : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) *ᵥ v) = v := by
    intro v
    rw [hv, hv]
    simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul,
      spForm_self, mul_zero, add_zero, smul_zero]
    linear_combination (norm := module) smul_add_self_char2 (e * spForm m K v z) z
  refine ⟨A, hA, fun v => hv v, fun v => ?_⟩
  exact mulVec_inv_of_invol A hinv v

theorem inSub_conj [CharP K 2] {L : Subgroup (GL (Fin m ⊕ Fin m) K)}
    {u : Fin m ⊕ Fin m → K}
    (hN : ∀ A ∈ StatedSp m K, (∃ c : K,
      (A : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) *ᵥ u = c • u) →
        ∀ l ∈ L, A * l * A⁻¹ ∈ L)
    {w z : Fin m ⊕ Fin m → K} {c e : K} (hw : spForm m K u w = 0)
    (hz : spForm m K u z = 0) (h : InSub L u w c) :
    InSub L u (w + (e * spForm m K w z) • z) c := by
  obtain ⟨l, hl, hlx⟩ := h
  obtain ⟨τ, hτS, hτv, hτinv⟩ := exists_transv (K := K) z e
  have hτu : (τ : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) *ᵥ u = (1 : K) • u := by
    rw [hτv, hz, mul_zero, zero_smul, add_zero, one_smul]
  refine ⟨τ * l * τ⁻¹, hN τ hτS ⟨1, hτu⟩ l hl, fun x => ?_⟩
  rw [mulVec_units_mul, mulVec_units_mul, hτinv, hlx]
  have hzw := spForm_symm_char2 z w
  have hzu := spForm_zero_symm hz
  simp only [siegelMap, hτv, map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply,
    smul_eq_mul, spForm_self, hz, hzu, hw, hzw, mul_zero, zero_mul, add_zero, zero_add,
    smul_zero, zero_smul]
  linear_combination (norm := module) smul_add_self_char2 (e * spForm m K x z) z

theorem inSub_of_ne_zero [CharP K 2] {L : Subgroup (GL (Fin m ⊕ Fin m) K)}
    {u : Fin m ⊕ Fin m → K}
    (hN : ∀ A ∈ StatedSp m K, (∃ c : K,
      (A : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) *ᵥ u = c • u) →
        ∀ l ∈ L, A * l * A⁻¹ ∈ L)
    {w z : Fin m ⊕ Fin m → K} {c : K} (hw : spForm m K u w = 0)
    (hz : spForm m K u z = 0) (h : InSub L u w c) (ha : spForm m K w z ≠ 0) :
    InSub L u z (spForm m K w z) := by
  have h1 := inSub_conj hN hw hz h (e := (spForm m K w z)⁻¹)
  rw [inv_mul_cancel₀ ha, one_smul] at h1
  have hwz : spForm m K u (w + z) = 0 := by
    rw [map_add, hw, hz, add_zero]
  have h2 := inSub_comp hwz hw h1 h
  have hv : w + z + w = z := by
    rw [add_right_comm, vec_add_self, zero_add]
  have hval : c + c + spForm m K w (w + z) = spForm m K w z := by
    rw [CharTwo.add_self_eq_zero, zero_add, map_add, spForm_self, zero_add]
  rw [hv, hval] at h2
  exact h2

theorem inSub_zero_scale {L : Subgroup (GL (Fin m ⊕ Fin m) K)} {u : Fin m ⊕ Fin m → K}
    (hN : ∀ A ∈ StatedSp m K, (∃ c : K,
      (A : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) *ᵥ u = c • u) →
        ∀ l ∈ L, A * l * A⁻¹ ∈ L)
    (hu : u ≠ 0) {lam c : K} (hlam : lam ≠ 0) (h : InSub L u 0 c) :
    InSub L u 0 (lam ^ 2 * c) := by
  obtain ⟨A, hA, hAu⟩ := exists_statedSp_mulVec_eq (x := u) (y := lam • u) hu
    (smul_ne_zero hlam hu)
  obtain ⟨l, hl, hlx⟩ := h
  have hAinv : ∀ x : Fin m ⊕ Fin m → K,
      (A : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) *ᵥ
        ((A⁻¹ : GL (Fin m ⊕ Fin m) K) : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) *ᵥ x = x := by
    intro x
    rw [Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one,
      Matrix.one_mulVec]
  have hBy : ∀ x : Fin m ⊕ Fin m → K,
      spForm m K
        (((A⁻¹ : GL (Fin m ⊕ Fin m) K) : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) *ᵥ x) u =
        lam * spForm m K x u := by
    intro x
    have h := (mem_statedSp_iff_forall A).mp hA
      (((A⁻¹ : GL (Fin m ⊕ Fin m) K) : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) *ᵥ x) u
    rw [hAinv x, hAu, map_smul, smul_eq_mul] at h
    exact h.symm
  refine ⟨A * l * A⁻¹, hN A hA ⟨lam, hAu⟩ l hl, fun x => ?_⟩
  rw [mulVec_units_mul, mulVec_units_mul, hlx]
  simp only [siegelMap, map_zero, LinearMap.zero_apply, smul_zero, zero_smul, add_zero,
    zero_add, hBy, Matrix.mulVec_add, Matrix.mulVec_smul, hAu, hAinv]
  module

theorem inSub_zero_all [Finite K] [CharP K 2] {L : Subgroup (GL (Fin m ⊕ Fin m) K)}
    {u : Fin m ⊕ Fin m → K}
    (hN : ∀ A ∈ StatedSp m K, (∃ c : K,
      (A : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) *ᵥ u = c • u) →
        ∀ l ∈ L, A * l * A⁻¹ ∈ L)
    (hu : u ≠ 0) (h1 : InSub L u 0 1) (c : K) : InSub L u 0 c := by
  by_cases hc : c = 0
  · subst hc
    exact ⟨1, L.one_mem, fun x => by simp [siegelMap]⟩
  · obtain ⟨s, hs⟩ := FiniteField.isSquare_of_char_two (ringChar.eq K 2) c
    have hs0 : s ≠ 0 := by
      rintro rfl
      exact hc (by rw [hs, zero_mul])
    have h := inSub_zero_scale hN hu hs0 h1
    have e : s ^ 2 * 1 = c := by
      rw [hs]
      ring
    rwa [e] at h

theorem inSub_adjust [CharP K 2] {L : Subgroup (GL (Fin m ⊕ Fin m) K)}
    {u : Fin m ⊕ Fin m → K} (hzero : ∀ c : K, InSub L u 0 c)
    {w : Fin m ⊕ Fin m → K} {d : K} (hw : spForm m K u w = 0) (h : InSub L u w d) (c : K) :
    InSub L u w c := by
  have h0 : spForm m K u 0 = 0 := by simp
  have h' := inSub_comp hw h0 h (hzero (c + d))
  have hval : d + (c + d) + spForm m K 0 w = c := by
    simp only [map_zero, LinearMap.zero_apply, add_zero]
    linear_combination d * (CharTwo.two_eq_zero (R := K))
  rw [add_zero, hval] at h'
  exact h'

theorem exists_lam_ne_zero_one [Finite K] (h4 : 4 ≤ Nat.card K) :
    ∃ lam : K, lam ≠ 0 ∧ lam ≠ 1 := by
  classical
  by_contra h
  push Not at h
  have hinj : Function.Injective (fun x : K => if x = 0 then (0 : Fin 2) else 1) := by
    intro x y hxy
    by_cases hx : x = 0 <;> by_cases hy : y = 0
    · rw [hx, hy]
    · simp [hx, hy] at hxy
    · simp [hx, hy] at hxy
    · rw [h x hx, h y hy]
  have h2 := Nat.card_le_card_of_injective _ hinj
  have h3 : Nat.card (Fin 2) = 2 := by simp
  omega

theorem inSub_zero_one [Finite K] [CharP K 2] {L : Subgroup (GL (Fin m ⊕ Fin m) K)}
    {u : Fin m ⊕ Fin m → K}
    (hN : ∀ A ∈ StatedSp m K, (∃ c : K,
      (A : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) *ᵥ u = c • u) →
        ∀ l ∈ L, A * l * A⁻¹ ∈ L)
    (h4 : 4 ≤ Nat.card K) {w0 w1 : Fin m ⊕ Fin m → K} {c0 : K}
    (hw0u : spForm m K u w0 = 0) (hw0L : InSub L u w0 c0) (hw1u : spForm m K u w1 = 0)
    (hw1 : spForm m K w0 w1 = 1) : InSub L u 0 1 := by
  obtain ⟨lam, hl0, hl1⟩ := exists_lam_ne_zero_one h4
  have hz2u : spForm m K u (lam • w1 + w0) = 0 := by
    simp only [map_add, map_smul, hw1u, hw0u, smul_zero, add_zero]
  have hz12u : spForm m K u (w1 + (lam • w1 + w0)) = 0 := by
    rw [map_add, hw1u, hz2u, add_zero]
  have hw0z2 : spForm m K w0 (lam • w1 + w0) = lam := by
    simp only [map_add, map_smul, hw1, spForm_self, smul_eq_mul, mul_one, add_zero]
  have hw0z12 : spForm m K w0 (w1 + (lam • w1 + w0)) = 1 + lam := by
    rw [map_add, hw1, hw0z2]
  have hz2z1 : spForm m K (lam • w1 + w0) w1 = 1 := by
    simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul,
      spForm_self, mul_zero, zero_add, hw1]
  have hone : 1 + lam ≠ 0 := fun h =>
    hl1 (by linear_combination h - (CharTwo.two_eq_zero (R := K)))
  have hA1 : InSub L u w1 1 := by
    have h := inSub_of_ne_zero hN hw0u hw1u hw0L (by rw [hw1]; exact one_ne_zero)
    rwa [hw1] at h
  have hA2 : InSub L u (lam • w1 + w0) lam := by
    have h := inSub_of_ne_zero hN hw0u hz2u hw0L (by rw [hw0z2]; exact hl0)
    rwa [hw0z2] at h
  have hA3 : InSub L u (w1 + (lam • w1 + w0)) (1 + lam) := by
    have h := inSub_of_ne_zero hN hw0u hz12u hw0L (by rw [hw0z12]; exact hone)
    rwa [hw0z12] at h
  have hB1 := inSub_comp hw1u hz2u hA1 hA2
  rw [hz2z1] at hB1
  have hz12z12 : spForm m K (w1 + (lam • w1 + w0)) (w1 + (lam • w1 + w0)) = 0 :=
    spForm_self _
  have hB2 := inSub_comp hz12u hz12u hB1 hA3
  rw [vec_add_self, hz12z12] at hB2
  have hval : (1 + lam + 1 + (1 + lam) + 0 : K) = 1 := by
    linear_combination (1 + lam) * (CharTwo.two_eq_zero (R := K))
  rwa [hval] at hB2

theorem exists_nontrans [Finite K] [CharP K 2] {L : Subgroup (GL (Fin m ⊕ Fin m) K)}
    {u : Fin m ⊕ Fin m → K} (hLU : L ≤ LspGL m K u) (hcard : Nat.card K < Nat.card L) :
    ∃ w0 : Fin m ⊕ Fin m → K, ∃ c0 : K, spForm m K u w0 = 0 ∧ InSub L u w0 c0 ∧
      ¬∃ a : K, w0 = a • u := by
  by_contra hcon
  push Not at hcon
  have hf : ∀ l : L, ∃ c : K, ∀ x : Fin m ⊕ Fin m → K,
      ((l : GL (Fin m ⊕ Fin m) K) : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) *ᵥ x =
        siegelMap u 0 c x := by
    rintro ⟨l, hl⟩
    obtain ⟨-, w, c, hw, hx⟩ := mem_LspGL_iff_siegel.mp (hLU hl)
    obtain ⟨a, rfl⟩ := hcon w c hw ⟨l, hl, hx⟩
    exact ⟨c, fun x => (hx x).trans (congrFun (siegelMap_smul_u u a c) x)⟩
  choose f hf using hf
  have hinj : Function.Injective f := by
    intro l l' h
    apply Subtype.ext
    apply gl_eq_of_mulVec
    intro x
    rw [hf l x, hf l' x, h]
  have h2 := Nat.card_le_card_of_injective f hinj
  omega

theorem exists_w1 {u w0 : Fin m ⊕ Fin m → K} (hu : u ≠ 0)
    (hw0 : ¬∃ a : K, w0 = a • u) :
    ∃ w1 : Fin m ⊕ Fin m → K, spForm m K u w1 = 0 ∧ spForm m K w0 w1 = 1 := by
  obtain ⟨y', hy'⟩ : ∃ y : Fin m ⊕ Fin m → K, spForm m K u y ≠ 0 := by
    by_contra h
    push Not at h
    exact hu (spForm_nondegenerate.1 u h)
  obtain ⟨y0, hBy0⟩ : ∃ y0 : Fin m ⊕ Fin m → K, spForm m K u y0 = 1 := by
    refine ⟨(spForm m K u y')⁻¹ • y', ?_⟩
    simp only [map_smul, smul_eq_mul]
    exact inv_mul_cancel₀ hy'
  have hex : ∃ y : Fin m ⊕ Fin m → K, spForm m K u y = 0 ∧ spForm m K w0 y ≠ 0 := by
    by_contra h
    push Not at h
    apply hw0
    refine ⟨spForm m K w0 y0, ?_⟩
    have hz : w0 - (spForm m K w0 y0) • u = 0 := by
      apply spForm_nondegenerate.1
      intro n
      have h1 := h (n - (spForm m K u n) • y0) (by simp [hBy0])
      simp only [map_sub, map_smul, LinearMap.sub_apply, LinearMap.smul_apply,
        smul_eq_mul] at h1 ⊢
      linear_combination h1
    exact sub_eq_zero.mp hz
  obtain ⟨y, hy1, hy2⟩ := hex
  refine ⟨(spForm m K w0 y)⁻¹ • y, ?_, ?_⟩
  · simp only [map_smul, smul_eq_mul, hy1, mul_zero]
  · simp only [map_smul, smul_eq_mul]
    exact inv_mul_cancel₀ hy2

theorem inSub_all [Finite K] [CharP K 2] {L : Subgroup (GL (Fin m ⊕ Fin m) K)}
    {u : Fin m ⊕ Fin m → K}
    (hN : ∀ A ∈ StatedSp m K, (∃ c : K,
      (A : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) *ᵥ u = c • u) →
        ∀ l ∈ L, A * l * A⁻¹ ∈ L)
    (hu : u ≠ 0) (hLU : L ≤ LspGL m K u) (h4 : 4 ≤ Nat.card K)
    (hcard : Nat.card K < Nat.card L) {w : Fin m ⊕ Fin m → K} (hw : spForm m K u w = 0)
    (c : K) : InSub L u w c := by
  obtain ⟨w0, c0, hw0u, hw0L, hw0n⟩ := exists_nontrans hLU hcard
  obtain ⟨w1, hw1u, hw1⟩ := exists_w1 hu hw0n
  have h01 : InSub L u 0 1 := inSub_zero_one hN h4 hw0u hw0L hw1u hw1
  have hzero : ∀ c : K, InSub L u 0 c := fun c => inSub_zero_all hN hu h01 c
  have hex : ∃ d : K, InSub L u w d := by
    by_cases hB : spForm m K w0 w = 0
    · have hwu1 : spForm m K u (w + w1) = 0 := by
        simp only [map_add, hw, hw1u, add_zero]
      have hB' : spForm m K w0 (w + w1) ≠ 0 := by
        rw [map_add, hB, hw1, zero_add]
        exact one_ne_zero
      have h1 : InSub L u w1 1 := by
        have h := inSub_of_ne_zero hN hw0u hw1u hw0L (by rw [hw1]; exact one_ne_zero)
        rwa [hw1] at h
      have h2 : InSub L u (w + w1) 1 := by
        have h := inSub_of_ne_zero hN hw0u hwu1 hw0L hB'
        have hv : spForm m K w0 (w + w1) = 1 := by
          rw [map_add, hB, hw1, zero_add]
        rwa [hv] at h
      have h3 := inSub_comp hw1u hwu1 h1 h2
      have hvec : w1 + (w + w1) = w := by
        calc w1 + (w + w1) = w + (w1 + w1) := by abel
          _ = w := by rw [vec_add_self, add_zero]
      rw [hvec] at h3
      exact ⟨_, h3⟩
    · exact ⟨_, inSub_of_ne_zero hN hw0u hw hw0L hB⟩
  obtain ⟨d, hd⟩ := hex
  exact inSub_adjust hzero hw hd c

end Basic

end LspNorm

open LspNorm in
theorem sp_eq_LspGL_of_normalized {K : Type} [Field K] [Finite K] [CharP K 2] {m : ℕ}
    (h4 : 4 ≤ Nat.card K) {u : Fin m ⊕ Fin m → K} (hu : u ≠ 0)
    (L : Subgroup (GL (Fin m ⊕ Fin m) K)) (hLU : L ≤ LspGL m K u)
    (hN : ∀ A ∈ StatedSp m K,
      (∃ c : K, (A : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) *ᵥ u = c • u) →
        ∀ l ∈ L, A * l * A⁻¹ ∈ L)
    (hcard : Nat.card K < Nat.card L) : L = LspGL m K u := by
  refine le_antisymm hLU ?_
  intro A hA
  obtain ⟨-, w, c, hw, hx⟩ := mem_LspGL_iff_siegel.mp hA
  obtain ⟨l, hl, hlx⟩ := inSub_all hN hu hLU h4 hcard hw c
  have hAl : A = l := gl_eq_of_mulVec fun x => (hx x).trans (hlx x).symm
  rw [hAl]
  exact hl

end CFSG.RankThree.GF2n.Stroth80
