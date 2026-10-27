module

public import CFSG.RankThree.GF2n.Stroth80.Ext1D4Potential
public import Mathlib.Data.Matrix.Basic
public import Mathlib.Algebra.CharP.Two
public import Mathlib.Algebra.EuclideanDomain.Field
public import Mathlib.Algebra.Field.IsField
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.Tactic.ContinuousFunctionalCalculus
public import Mathlib.Tactic.NormNum.Abs
public import Mathlib.Tactic.NormNum.DivMod
public import Mathlib.Tactic.NormNum.OfScientific
public import Mathlib.Tactic.Ring.RingNF

public section

namespace CFSG.RankThree.GF2n.Stroth80.Ext1D4

open Matrix

variable {K : Type*} [Field K] {W : Finset (Fin 4 → ℤ)}

@[expose] def rootMat (W : Finset (Fin 4 → ℤ)) (β : Fin 4 → ℤ) : Matrix W W K :=
  Matrix.of fun ψ χ => if (ψ : Fin 4 → ℤ) = χ + β then 1 else 0

@[expose] def rootElt (W : Finset (Fin 4 → ℤ)) (β : Fin 4 → ℤ) (t : K) : Matrix W W K :=
  1 + t • rootMat W β

@[expose] def ent (M : Matrix W W K) (a b : Fin 4 → ℤ) : K :=
  if h : a ∈ W ∧ b ∈ W then M ⟨a, h.1⟩ ⟨b, h.2⟩ else 0

theorem ent_coe (M : Matrix W W K) (ψ χ : W) : ent M ψ χ = M ψ χ := by
  rw [ent, dif_pos ⟨ψ.2, χ.2⟩]

theorem ent_of_not_mem_left (M : Matrix W W K) {a : Fin 4 → ℤ} (b : Fin 4 → ℤ) (ha : a ∉ W) :
    ent M a b = 0 := by
  rw [ent, dif_neg fun h => ha h.1]

theorem ent_of_not_mem_right (M : Matrix W W K) (a : Fin 4 → ℤ) {b : Fin 4 → ℤ} (hb : b ∉ W) :
    ent M a b = 0 := by
  rw [ent, dif_neg fun h => hb h.2]

theorem ent_zero (a b : Fin 4 → ℤ) : ent (0 : Matrix W W K) a b = 0 := by
  unfold ent
  split_ifs <;> rfl

theorem ent_add (M N : Matrix W W K) (a b : Fin 4 → ℤ) :
    ent (M + N) a b = ent M a b + ent N a b := by
  unfold ent
  split_ifs <;> simp

theorem ent_smul (c : K) (M : Matrix W W K) (a b : Fin 4 → ℤ) :
    ent (c • M) a b = c * ent M a b := by
  unfold ent
  split_ifs <;> simp

theorem ent_rootMat_mul (β : Fin 4 → ℤ) (M : Matrix W W K) {a : Fin 4 → ℤ} (ha : a ∈ W)
    (b : Fin 4 → ℤ) : ent (rootMat W β * M) a b = ent M (a - β) b := by
  classical
  by_cases hb : b ∈ W
  · rw [ent, dif_pos ⟨ha, hb⟩, Matrix.mul_apply]
    by_cases hab : a - β ∈ W
    · rw [ent, dif_pos ⟨hab, hb⟩, Finset.sum_eq_single ⟨a - β, hab⟩]
      · simp [rootMat]
      · intro φ _ hφ
        have hne : a ≠ (φ : Fin 4 → ℤ) + β := fun e => hφ (Subtype.ext (eq_sub_of_add_eq e.symm))
        simp [rootMat, hne]
      · intro h
        exact absurd (Finset.mem_univ _) h
    · rw [ent_of_not_mem_left M b hab]
      refine Finset.sum_eq_zero fun φ _ => ?_
      have hne : a ≠ (φ : Fin 4 → ℤ) + β := fun e =>
        hab (by rw [e, add_sub_cancel_right]; exact φ.2)
      simp [rootMat, hne]
  · rw [ent_of_not_mem_right _ _ hb, ent_of_not_mem_right _ _ hb]

theorem ent_mul_rootMat (β : Fin 4 → ℤ) (M : Matrix W W K) (a : Fin 4 → ℤ) {b : Fin 4 → ℤ}
    (hb : b ∈ W) : ent (M * rootMat W β) a b = ent M a (b + β) := by
  classical
  by_cases ha : a ∈ W
  · rw [ent, dif_pos ⟨ha, hb⟩, Matrix.mul_apply]
    by_cases hab : b + β ∈ W
    · rw [ent, dif_pos ⟨ha, hab⟩, Finset.sum_eq_single ⟨b + β, hab⟩]
      · simp [rootMat]
      · intro φ _ hφ
        have hne : (φ : Fin 4 → ℤ) ≠ b + β := fun e => hφ (Subtype.ext e)
        simp [rootMat, hne]
      · intro h
        exact absurd (Finset.mem_univ _) h
    · rw [ent_of_not_mem_right M a hab]
      refine Finset.sum_eq_zero fun φ _ => ?_
      have hne : (φ : Fin 4 → ℤ) ≠ b + β := fun e => hab (e ▸ φ.2)
      simp [rootMat, hne]
  · rw [ent_of_not_mem_left _ _ ha, ent_of_not_mem_left _ _ ha]

theorem ent_rootElt_mul (β : Fin 4 → ℤ) (t : K) (M : Matrix W W K) {a : Fin 4 → ℤ} (ha : a ∈ W)
    (b : Fin 4 → ℤ) : ent (rootElt W β t * M) a b = ent M a b + t * ent M (a - β) b := by
  rw [rootElt, add_mul, one_mul, smul_mul_assoc, ent_add, ent_smul, ent_rootMat_mul β M ha]

theorem ent_mul_rootElt (β : Fin 4 → ℤ) (t : K) (M : Matrix W W K) (a : Fin 4 → ℤ)
    {b : Fin 4 → ℤ} (hb : b ∈ W) :
    ent (M * rootElt W β t) a b = ent M a b + t * ent M a (b + β) := by
  rw [rootElt, mul_add, mul_one, mul_smul_comm, ent_add, ent_smul, ent_mul_rootMat β M a hb]

theorem rootElt_zero (β : Fin 4 → ℤ) : rootElt W β (0 : K) = 1 := by
  rw [rootElt, zero_smul, add_zero]

theorem exists_two_ne_zero_ne_neg_one [Fintype K] (hq : 4 ≤ Fintype.card K) :
    ∃ r₁ r₂ : K, r₁ ≠ 0 ∧ r₁ + 1 ≠ 0 ∧ r₂ ≠ 0 ∧ r₂ + 1 ≠ 0 ∧ r₁ ≠ r₂ := by
  classical
  set S : Finset K := ((Finset.univ : Finset K).erase 0).erase (-1)
  have hS : 1 < S.card := by
    have h1 : (-1 : K) ∈ (Finset.univ : Finset K).erase 0 :=
      Finset.mem_erase.2 ⟨neg_ne_zero.2 one_ne_zero, Finset.mem_univ _⟩
    rw [Finset.card_erase_of_mem h1, Finset.card_erase_of_mem (Finset.mem_univ _),
      Finset.card_univ]
    omega
  obtain ⟨r₁, h₁, r₂, h₂, h12⟩ := Finset.one_lt_card.1 hS
  simp only [S, Finset.mem_erase, Finset.mem_univ, and_true] at h₁ h₂
  exact ⟨r₁, r₂, h₁.2, fun e => h₁.1 (eq_neg_of_add_eq_zero_left e), h₂.2,
    fun e => h₂.1 (eq_neg_of_add_eq_zero_left e), h12⟩

theorem vec_ne_of_sub_ne {u v : Fin 4 → ℤ} (h : u - v ≠ 0) : u ≠ v :=
  fun e => h (by rw [e, sub_self])

theorem posRoot_ne_zero : ∀ β ∈ posRoot, β ≠ 0 := by decide

theorem minuscule_sub_add (hW : W = natWt ∨ W = evenWt ∨ W = oddWt) :
    ∀ β ∈ posRoot, ∀ χ ∈ W, χ - β ∈ W → χ + β ∉ W := by
  rcases hW with rfl | rfl | rfl <;> decide

theorem minuscule_triangle (hW : W = natWt ∨ W = evenWt ∨ W = oddWt) :
    ∀ β ∈ posRoot, ∀ γ ∈ posRoot, β + γ ∈ posRoot → ∀ χ ∈ W, χ + β ∈ W → χ + β + γ ∈ W →
      χ + γ ∉ W := by
  rcases hW with rfl | rfl | rfl <;> decide

theorem exists_diagonal_of_rootCocycle [Fintype K] [CharP K 2] (hq : 4 ≤ Fintype.card K)
    (hW : W = natWt ∨ W = evenWt ∨ W = oddWt) {Z : Type*} (D : Z → W → Kˣ)
    (bh : (Fin 4 → ℤ) → Z → Kˣ)
    (hD : ∀ β ∈ posRoot, ∀ z, ∀ ψ χ : W, (ψ : Fin 4 → ℤ) = χ + β → D z ψ = bh β z * D z χ)
    (hbh : ∀ β ∈ posRoot, ∀ c : Kˣ, ∃ z, bh β z = c)
    (hsep : ∀ β ∈ posRoot, ∀ ψ χ : W, ψ ≠ χ → (ψ : Fin 4 → ℤ) ≠ χ + β →
      (χ : Fin 4 → ℤ) ≠ ψ + β → ∃ z, bh β z = 1 ∧ D z ψ ≠ D z χ)
    (δ : (Fin 4 → ℤ) → K → Matrix W W K)
    (hδT : ∀ β ∈ posRoot, ∀ z t, diagonal (fun χ => (D z χ : K)) * δ β t =
      δ β ((bh β z : K) * t) * diagonal (fun χ => (D z χ : K)))
    (hδ₁ : ∀ β ∈ posRoot, ∀ s t, δ β (s + t) = rootElt W β s * δ β t + δ β s * rootElt W β t)
    (hδ₂ : ∀ β ∈ posRoot, ∀ γ ∈ posRoot, β + γ ∉ posRoot →
      rootElt W β 1 * δ γ 1 + δ β 1 * rootElt W γ 1 =
        rootElt W γ 1 * δ β 1 + δ γ 1 * rootElt W β 1)
    (hδ₃ : ∀ β ∈ posRoot, ∀ γ ∈ posRoot, β + γ ∈ posRoot →
      rootElt W β 1 * δ γ 1 + δ β 1 * rootElt W γ 1 =
        rootElt W (β + γ) 1 * rootElt W γ 1 * δ β 1 +
          rootElt W (β + γ) 1 * δ γ 1 * rootElt W β 1 +
            δ (β + γ) 1 * rootElt W γ 1 * rootElt W β 1) :
    ∃ l : W → K, ∀ β ∈ posRoot, ∀ t,
      δ β t = diagonal l * rootElt W β t - rootElt W β t * diagonal l := by
  classical
  have hβ0 := posRoot_ne_zero
  have hT : ∀ β ∈ posRoot, ∀ z t (ψ χ : W),
      (D z ψ : K) * δ β t ψ χ = δ β ((bh β z : K) * t) ψ χ * D z χ := by
    intro β hβ z t ψ χ
    have h := congrFun (congrFun (hδT β hβ z t) ψ) χ
    rwa [Matrix.diagonal_mul, Matrix.mul_diagonal] at h
  have hδ0 : ∀ β ∈ posRoot, δ β 0 = 0 := by
    intro β hβ
    have h := hδ₁ β hβ 0 0
    rw [add_zero, rootElt_zero, one_mul, mul_one] at h
    simpa using h
  have hA1 : ∀ β ∈ posRoot, ∀ t (ψ χ : W), ψ ≠ χ → (ψ : Fin 4 → ℤ) ≠ χ + β →
      (χ : Fin 4 → ℤ) ≠ ψ + β → δ β t ψ χ = 0 := by
    intro β hβ t ψ χ h1 h2 h3
    obtain ⟨z, hz1, hz2⟩ := hsep β hβ ψ χ h1 h2 h3
    have e := hT β hβ z t ψ χ
    rw [hz1, Units.val_one, one_mul] at e
    have hne : (D z ψ : K) - D z χ ≠ 0 := sub_ne_zero.2 fun h => hz2 (Units.ext h)
    have h0 : ((D z ψ : K) - D z χ) * δ β t ψ χ = 0 := by rw [sub_mul, e]; ring
    exact (mul_eq_zero.1 h0).resolve_left hne
  have hA2 : ∀ β ∈ posRoot, ∀ t (ψ χ : W), (ψ : Fin 4 → ℤ) = χ + β →
      δ β t ψ χ = t * δ β 1 ψ χ := by
    intro β hβ t ψ χ h
    rcases eq_or_ne t 0 with rfl | ht
    · rw [hδ0 β hβ, zero_mul]
      rfl
    obtain ⟨z, hz⟩ := hbh β hβ (Units.mk0 t ht)
    have e := hT β hβ z 1 ψ χ
    rw [hD β hβ z ψ χ h, Units.val_mul, hz, Units.val_mk0, mul_one] at e
    apply mul_right_cancel₀ (Units.ne_zero (D z χ))
    rw [← e]
    ring
  have hA3 : ∀ β ∈ posRoot, ∀ t (ψ χ : W), (χ : Fin 4 → ℤ) = ψ + β →
      δ β t ψ χ = t⁻¹ * δ β 1 ψ χ := by
    intro β hβ t ψ χ h
    rcases eq_or_ne t 0 with rfl | ht
    · rw [hδ0 β hβ, inv_zero, zero_mul]
      rfl
    obtain ⟨z, hz⟩ := hbh β hβ (Units.mk0 t ht)
    have e := hT β hβ z 1 ψ χ
    rw [hD β hβ z χ ψ h, Units.val_mul, hz, Units.val_mk0, mul_one] at e
    have h1 : δ β 1 ψ χ = δ β t ψ χ * t :=
      mul_left_cancel₀ (Units.ne_zero (D z ψ)) (by rw [e]; ring)
    rw [h1, mul_comm (δ β t ψ χ) t, ← mul_assoc, inv_mul_cancel₀ ht, one_mul]
  have hA4 : ∀ β ∈ posRoot, ∀ t (χ : W), t ≠ 0 → δ β t χ χ = δ β 1 χ χ := by
    intro β hβ t χ ht
    obtain ⟨z, hz⟩ := hbh β hβ (Units.mk0 t ht)
    have e := hT β hβ z 1 χ χ
    rw [hz, Units.val_mk0, mul_one] at e
    exact mul_right_cancel₀ (Units.ne_zero (D z χ)) (by rw [← e, mul_comm])
  have eA1 : ∀ β ∈ posRoot, ∀ t (a b : Fin 4 → ℤ), a ≠ b → a ≠ b + β → b ≠ a + β →
      ent (δ β t) a b = 0 := by
    intro β hβ t a b h1 h2 h3
    unfold ent
    split_ifs with h
    · exact hA1 β hβ t _ _ (fun e => h1 (congrArg Subtype.val e)) h2 h3
    · rfl
  have eA2 : ∀ β ∈ posRoot, ∀ t (a b : Fin 4 → ℤ), a = b + β →
      ent (δ β t) a b = t * ent (δ β 1) a b := by
    intro β hβ t a b h
    unfold ent
    split_ifs with hab
    · exact hA2 β hβ t _ _ h
    · rw [mul_zero]
  have eA3 : ∀ β ∈ posRoot, ∀ t (a b : Fin 4 → ℤ), b = a + β →
      ent (δ β t) a b = t⁻¹ * ent (δ β 1) a b := by
    intro β hβ t a b h
    unfold ent
    split_ifs with hab
    · exact hA3 β hβ t _ _ h
    · rw [mul_zero]
  have eA4 : ∀ β ∈ posRoot, ∀ t (a : Fin 4 → ℤ), t ≠ 0 →
      ent (δ β t) a a = ent (δ β 1) a a := by
    intro β hβ t a ht
    unfold ent
    split_ifs with ha
    · exact hA4 β hβ t _ ht
    · rfl
  obtain ⟨r₁, r₂, h₁0, h₁1, h₂0, h₂1, h12⟩ := exists_two_ne_zero_ne_neg_one hq
  have mini₁ := minuscule_sub_add hW
  have hB : ∀ β ∈ posRoot, ∀ χ ∈ W, ent (δ β 1) χ χ = 0 ∧ ent (δ β 1) (χ - β) χ = 0 := by
    intro β hβ χ hχ
    have key : ∀ r : K, r ≠ 0 → r + 1 ≠ 0 → ent (δ β 1) χ χ + r * ent (δ β 1) (χ - β) χ +
        r⁻¹ * ent (δ β 1) χ (χ + β) = 0 := by
      intro r hr hr1
      have e := congrArg (fun M => ent M χ χ) (hδ₁ β hβ r 1)
      simp only [ent_add] at e
      rw [ent_rootElt_mul β r _ hχ, ent_mul_rootElt β 1 _ χ hχ, eA4 β hβ _ χ hr1,
        eA4 β hβ _ χ hr, eA3 β hβ r χ (χ + β) rfl, one_mul] at e
      linear_combination -e
    have k₁ := key r₁ h₁0 h₁1
    have k₂ := key r₂ h₂0 h₂1
    by_cases hm : χ - β ∈ W
    · have hp : ent (δ β 1) χ (χ + β) = 0 := ent_of_not_mem_right _ _ (mini₁ β hβ χ hχ hm)
      rw [hp, mul_zero, add_zero] at k₁ k₂
      have hP : ent (δ β 1) (χ - β) χ = 0 := by
        have h : (r₁ - r₂) * ent (δ β 1) (χ - β) χ = 0 := by linear_combination k₁ - k₂
        exact (mul_eq_zero.1 h).resolve_left (sub_ne_zero.2 h12)
      refine ⟨?_, hP⟩
      rw [hP, mul_zero, add_zero] at k₁
      exact k₁
    · have hP : ent (δ β 1) (χ - β) χ = 0 := ent_of_not_mem_left _ _ hm
      rw [hP, mul_zero, add_zero] at k₁ k₂
      have hP' : ent (δ β 1) χ (χ + β) = 0 := by
        have h : (r₁⁻¹ - r₂⁻¹) * ent (δ β 1) χ (χ + β) = 0 := by linear_combination k₁ - k₂
        exact (mul_eq_zero.1 h).resolve_left (sub_ne_zero.2 fun e => h12 (inv_injective e))
      refine ⟨?_, hP⟩
      rw [hP', mul_zero, add_zero] at k₁
      exact k₁
  have hNF : ∀ β ∈ posRoot, ∀ t (a b : Fin 4 → ℤ),
      ent (δ β t) a b = if a = b + β then t * ent (δ β 1) (b + β) b else 0 := by
    intro β hβ t a b
    split_ifs with hab
    · subst hab
      exact eA2 β hβ t _ b rfl
    · by_cases ha : a ∈ W
      swap
      · exact ent_of_not_mem_left _ _ ha
      by_cases hb : b ∈ W
      swap
      · exact ent_of_not_mem_right _ _ hb
      by_cases h1 : a = b
      · subst h1
        rcases eq_or_ne t 0 with rfl | ht
        · rw [hδ0 β hβ, ent_zero]
        · rw [eA4 β hβ t a ht]
          exact (hB β hβ a ha).1
      · by_cases h3 : b = a + β
        · rw [eA3 β hβ t a b h3]
          have ha' : a = b - β := by rw [h3, add_sub_cancel_right]
          rw [ha', (hB β hβ b hb).2, mul_zero]
        · exact eA1 β hβ t a b h1 hab h3
  obtain ⟨ν, hν⟩ : ∃ ν : (Fin 4 → ℤ) → (Fin 4 → ℤ) → K,
      ∀ β χ, ν β χ = ent (δ β 1) (χ + β) χ := ⟨_, fun _ _ => rfl⟩
  have hN : ∀ β ∈ posRoot, ∀ a b, ent (δ β 1) a b = if a = b + β then ν β b else 0 := by
    intro β hβ a b
    rw [hNF β hβ 1 a b, one_mul, hν]
  have hsq : ∀ β ∈ posRoot, ∀ γ ∈ posRoot, β + γ ∉ posRoot → ∀ χ ∈ W, χ + β ∈ W →
      χ + γ ∈ W → χ + β + γ ∈ W → ν β χ + ν γ (χ + β) = ν γ χ + ν β (χ + γ) := by
    intro β hβ γ hγ hβγ χ hχ h1 h2 h3
    have e := congrArg (fun M => ent M (χ + β + γ) χ) (hδ₂ β hβ γ hγ hβγ)
    simp only [ent_add] at e
    rw [ent_rootElt_mul β 1 _ h3, ent_mul_rootElt γ 1 _ _ hχ, ent_rootElt_mul γ 1 _ h3,
      ent_mul_rootElt β 1 _ _ hχ] at e
    have n1 : ent (δ γ 1) (χ + β + γ) χ = 0 := by
      rw [hN γ hγ, if_neg (vec_ne_of_sub_ne (by
        rw [show χ + β + γ - (χ + γ) = β by abel]; exact hβ0 β hβ))]
    have n2 : ent (δ γ 1) (χ + β + γ - β) χ = ν γ χ := by
      rw [show χ + β + γ - β = χ + γ by abel, hN γ hγ, if_pos rfl]
    have n3 : ent (δ β 1) (χ + β + γ) χ = 0 := by
      rw [hN β hβ, if_neg (vec_ne_of_sub_ne (by
        rw [show χ + β + γ - (χ + β) = γ by abel]; exact hβ0 γ hγ))]
    have n4 : ent (δ β 1) (χ + β + γ) (χ + γ) = ν β (χ + γ) := by
      rw [hN β hβ, if_pos (by abel)]
    have n5 : ent (δ β 1) (χ + β + γ - γ) χ = ν β χ := by
      rw [show χ + β + γ - γ = χ + β by abel, hN β hβ, if_pos rfl]
    have n6 : ent (δ γ 1) (χ + β + γ) (χ + β) = ν γ (χ + β) := by
      rw [hN γ hγ, if_pos rfl]
    rw [n1, n2, n3, n4, n5, n6] at e
    linear_combination -e
  have mini₂ := minuscule_triangle hW
  have htri : ∀ β ∈ posRoot, ∀ γ ∈ posRoot, β + γ ∈ posRoot → ∀ χ ∈ W, χ + β ∈ W →
      χ + β + γ ∈ W → ν β χ + ν γ (χ + β) = ν (β + γ) χ := by
    intro β hβ γ hγ hβγ χ hχ h1 h3
    have h2 : χ + γ ∉ W := mini₂ β hβ γ hγ hβγ χ hχ h1 h3
    have hδ0' : β + γ ≠ 0 := hβ0 _ hβγ
    have e := congrArg (fun M => ent M (χ + β + γ) χ) (hδ₃ β hβ γ hγ hβγ)
    simp only [ent_add] at e
    have l1 : ent (rootElt W β 1 * δ γ 1) (χ + β + γ) χ = 0 := by
      rw [ent_rootElt_mul β 1 _ h3, show χ + β + γ - β = χ + γ by abel,
        ent_of_not_mem_left _ _ h2, hN γ hγ, if_neg (vec_ne_of_sub_ne (by
          rw [show χ + β + γ - (χ + γ) = β by abel]; exact hβ0 β hβ))]
      ring
    have l2 : ent (δ β 1 * rootElt W γ 1) (χ + β + γ) χ = 0 := by
      rw [ent_mul_rootElt γ 1 _ _ hχ, ent_of_not_mem_right _ _ h2, hN β hβ,
        if_neg (vec_ne_of_sub_ne (by
          rw [show χ + β + γ - (χ + β) = γ by abel]; exact hβ0 γ hγ))]
      ring
    have t1 : ent (rootElt W (β + γ) 1 * rootElt W γ 1 * δ β 1) (χ + β + γ) χ = ν β χ := by
      rw [Matrix.mul_assoc, ent_rootElt_mul (β + γ) 1 _ h3, ent_rootElt_mul γ 1 _ h3,
        show χ + β + γ - (β + γ) = χ by abel, ent_rootElt_mul γ 1 _ hχ,
        show χ + β + γ - γ = χ + β by abel, hN β hβ, hN β hβ, hN β hβ, hN β hβ,
        if_neg (vec_ne_of_sub_ne (by
          rw [show χ + β + γ - (χ + β) = γ by abel]; exact hβ0 γ hγ)), if_pos rfl,
        if_neg (vec_ne_of_sub_ne (by
          rw [show χ - (χ + β) = -β by abel]; exact neg_ne_zero.2 (hβ0 β hβ))),
        if_neg (vec_ne_of_sub_ne (by
          rw [show χ - γ - (χ + β) = -(β + γ) by abel]; exact neg_ne_zero.2 hδ0'))]
      ring
    have t2 : ent (rootElt W (β + γ) 1 * δ γ 1 * rootElt W β 1) (χ + β + γ) χ =
        ν γ (χ + β) := by
      rw [Matrix.mul_assoc, ent_rootElt_mul (β + γ) 1 _ h3,
        show χ + β + γ - (β + γ) = χ by abel, ent_mul_rootElt β 1 _ _ hχ,
        ent_mul_rootElt β 1 _ _ hχ, hN γ hγ, hN γ hγ, hN γ hγ, hN γ hγ,
        if_neg (vec_ne_of_sub_ne (by
          rw [show χ + β + γ - (χ + γ) = β by abel]; exact hβ0 β hβ)), if_pos rfl,
        if_neg (vec_ne_of_sub_ne (by
          rw [show χ - (χ + γ) = -γ by abel]; exact neg_ne_zero.2 (hβ0 γ hγ))),
        if_neg (vec_ne_of_sub_ne (by
          rw [show χ - (χ + β + γ) = -(β + γ) by abel]; exact neg_ne_zero.2 hδ0'))]
      ring
    have t3 : ent (δ (β + γ) 1 * rootElt W γ 1 * rootElt W β 1) (χ + β + γ) χ =
        ν (β + γ) χ := by
      rw [ent_mul_rootElt β 1 _ _ hχ, ent_mul_rootElt γ 1 _ _ hχ, ent_mul_rootElt γ 1 _ _ h1,
        ent_of_not_mem_right _ _ h2, hN _ hβγ, hN _ hβγ, hN _ hβγ,
        if_pos (by abel),
        if_neg (vec_ne_of_sub_ne (by
          rw [show χ + β + γ - (χ + β + (β + γ)) = -β by abel]; exact neg_ne_zero.2 (hβ0 β hβ))),
        if_neg (vec_ne_of_sub_ne (by
          rw [show χ + β + γ - (χ + β + γ + (β + γ)) = -(β + γ) by abel];
          exact neg_ne_zero.2 hδ0'))]
      ring
    rw [l1, l2, t1, t2, t3] at e
    have h2' : (2 : K) = 0 := CharTwo.two_eq_zero
    linear_combination -e - ν (β + γ) χ * h2'
  have hcoc : IsCocycle W ν := ⟨hsq, htri⟩
  obtain ⟨l, hl⟩ : ∃ l : (Fin 4 → ℤ) → K, ∀ β ∈ posRoot, ∀ χ ∈ W, χ + β ∈ W →
      l (χ + β) = l χ + ν β χ := by
    rcases hW with rfl | rfl | rfl
    · exact exists_potential_nat hcoc
    · exact exists_potential_even hcoc
    · exact exists_potential_odd hcoc
  refine ⟨fun χ => l χ, fun β hβ t => ?_⟩
  ext ψ χ
  have hX : rootElt W β t ψ χ =
      (1 : Matrix W W K) ψ χ + t * (if (ψ : Fin 4 → ℤ) = χ + β then 1 else 0) := rfl
  rw [Matrix.sub_apply, Matrix.diagonal_mul, Matrix.mul_diagonal, ← ent_coe (δ β t) ψ χ,
    hNF β hβ t, hX]
  by_cases h1 : (ψ : Fin 4 → ℤ) = χ + β
  · have hne : ψ ≠ χ := fun e => hβ0 β hβ (by
      have h := h1
      rw [e] at h
      simpa using h)
    have hlψ : l ψ = l χ + ν β χ := by
      rw [h1]
      exact hl β hβ χ χ.2 (h1 ▸ ψ.2)
    simp only [if_pos h1, Matrix.one_apply_ne hne, hlψ, hν]
    ring
  · simp only [if_neg h1, mul_zero, add_zero]
    by_cases h2 : ψ = χ
    · subst h2
      rw [Matrix.one_apply_eq]
      ring
    · rw [Matrix.one_apply_ne h2]
      ring

theorem rootCocycle_eq_zero_of_sep {W₁ W₂ : Finset (Fin 4 → ℤ)} {Z : Type*} (D₁ : Z → W₁ → Kˣ)
    (D₂ : Z → W₂ → Kˣ) (bh : (Fin 4 → ℤ) → Z → Kˣ)
    (hsep : ∀ β ∈ posRoot, ∀ (ψ : W₁) (χ : W₂), ∃ z, bh β z = 1 ∧ D₁ z ψ ≠ D₂ z χ)
    (δ : (Fin 4 → ℤ) → K → Matrix W₁ W₂ K)
    (hδT : ∀ β ∈ posRoot, ∀ z t, diagonal (fun ψ => (D₁ z ψ : K)) * δ β t =
      δ β ((bh β z : K) * t) * diagonal (fun χ => (D₂ z χ : K))) :
    ∀ β ∈ posRoot, ∀ t, δ β t = 0 := by
  intro β hβ t
  ext ψ χ
  obtain ⟨z, hz1, hz2⟩ := hsep β hβ ψ χ
  have e := congrFun (congrFun (hδT β hβ z t) ψ) χ
  rw [Matrix.diagonal_mul, Matrix.mul_diagonal, hz1, Units.val_one, one_mul] at e
  have hne : (D₁ z ψ : K) - D₂ z χ ≠ 0 := sub_ne_zero.2 fun h => hz2 (Units.ext h)
  have h0 : ((D₁ z ψ : K) - D₂ z χ) * δ β t ψ χ = 0 := by rw [sub_mul, e]; ring
  exact (mul_eq_zero.1 h0).resolve_left hne

end CFSG.RankThree.GF2n.Stroth80.Ext1D4
