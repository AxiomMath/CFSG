module

public import CFSG.RankThree.GF2n.Stroth80.Ext1D4Complement
public import Mathlib.FieldTheory.Finite.Basic

public section

namespace CFSG.RankThree.GF2n.Stroth80.Ext1D4

open Matrix

variable {K : Type*} [Field K] {W : Finset (Fin 4 → ℤ)}

theorem minuscule_out (hW : W = natWt ∨ W = evenWt ∨ W = oddWt) :
    ∀ β ∈ posRoot, ∀ γ ∈ posRoot, ∀ χ ∈ W, χ + β ∈ W → χ + γ ∈ W → β + γ ∉ posRoot := by
  rcases hW with rfl | rfl | rfl <;> decide +kernel

theorem posRoot_add_self_ne_zero : ∀ β ∈ posRoot, β + β ≠ 0 := by decide

theorem posRoot_pair_facts : ∀ β ∈ posRoot, ∀ γ ∈ posRoot, β ≠ γ →
    (β - γ ≠ γ ∧ β - γ ≠ -γ ∧ β - γ ≠ 0 ∧ β - γ ≠ β ∧ β - γ ≠ -β) ∧
    (β - γ - γ ≠ β ∧ β - γ - γ ≠ -β ∧ β - γ - γ ≠ 0) ∧
    (β + β - γ ≠ γ ∧ β + β - γ ≠ -γ ∧ β + β - γ ≠ 0) ∧ γ + γ ≠ 0 := by
  decide +kernel

theorem exists_diagonal_of_rootCocycle_twist4 [Fintype K] [CharP K 2]
    (hq : Fintype.card K = 4) (hW : W = natWt ∨ W = evenWt ∨ W = oddWt) {Z : Type*}
    (D : Z → W → Kˣ) (bh : (Fin 4 → ℤ) → Z → Kˣ)
    (hD : ∀ β ∈ posRoot, ∀ z, ∀ ψ χ : W, (ψ : Fin 4 → ℤ) = χ + β → D z ψ = bh β z * D z χ)
    (hbh : ∀ β ∈ posRoot, ∀ c : Kˣ, ∃ z, bh β z = c)
    (hsep : ∀ β ∈ posRoot, ∀ ψ χ : W, ψ ≠ χ → (ψ : Fin 4 → ℤ) ≠ χ + β →
      (χ : Fin 4 → ℤ) ≠ ψ + β → ∃ z, bh β z = 1 ∧ D z ψ ≠ D z χ)
    (δ : (Fin 4 → ℤ) → K → Matrix W W K)
    (hδT : ∀ β ∈ posRoot, ∀ z t, diagonal (fun χ => (D z χ : K)) * δ β t =
      δ β ((bh β z : K) * t) * diagonal (fun χ => (D z χ : K)))
    (hδ₁ : ∀ β ∈ posRoot, ∀ s t,
      δ β (s + t) = rootElt W β s * δ β t + δ β s * rootElt W (-β) (t ^ 2))
    (hδ₂ : ∀ β ∈ posRoot, ∀ γ ∈ posRoot, β + γ ∉ posRoot →
      rootElt W β 1 * δ γ 1 + δ β 1 * rootElt W (-γ) 1 =
        rootElt W γ 1 * δ β 1 + δ γ 1 * rootElt W (-β) 1) :
    ∃ l : W → K, ∀ β ∈ posRoot, ∀ t,
      δ β t = diagonal l * rootElt W (-β) (t ^ 2) - rootElt W β t * diagonal l := by
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
    rw [add_zero, zero_pow two_ne_zero, rootElt_zero, rootElt_zero, one_mul, mul_one] at h
    simpa using h
  have eA1 : ∀ β ∈ posRoot, ∀ t (a b : Fin 4 → ℤ), a ≠ b → a ≠ b + β → b ≠ a + β →
      ent (δ β t) a b = 0 := by
    intro β hβ t a b h1 h2 h3
    unfold ent
    split_ifs with h
    · obtain ⟨z, hz1, hz2⟩ := hsep β hβ ⟨a, h.1⟩ ⟨b, h.2⟩ (fun e => h1 (congrArg Subtype.val e))
        h2 h3
      have e := hT β hβ z t ⟨a, h.1⟩ ⟨b, h.2⟩
      rw [hz1, Units.val_one, one_mul] at e
      have hne : (D z ⟨a, h.1⟩ : K) - D z ⟨b, h.2⟩ ≠ 0 := sub_ne_zero.2 fun h => hz2 (Units.ext h)
      have h0 : ((D z ⟨a, h.1⟩ : K) - D z ⟨b, h.2⟩) * δ β t ⟨a, h.1⟩ ⟨b, h.2⟩ = 0 := by
        rw [sub_mul, e]; ring
      exact (mul_eq_zero.1 h0).resolve_left hne
    · rfl
  have eA2 : ∀ β ∈ posRoot, ∀ t (a b : Fin 4 → ℤ), a = b + β →
      ent (δ β t) a b = t * ent (δ β 1) a b := by
    intro β hβ t a b h
    unfold ent
    split_ifs with hab
    · rcases eq_or_ne t 0 with rfl | ht
      · rw [hδ0 β hβ, zero_mul]; rfl
      obtain ⟨z, hz⟩ := hbh β hβ (Units.mk0 t ht)
      have e := hT β hβ z 1 ⟨a, hab.1⟩ ⟨b, hab.2⟩
      rw [hD β hβ z ⟨a, hab.1⟩ ⟨b, hab.2⟩ h, Units.val_mul, hz, Units.val_mk0, mul_one] at e
      apply mul_right_cancel₀ (Units.ne_zero (D z ⟨b, hab.2⟩))
      rw [← e]
      ring
    · rw [mul_zero]
  have eA3 : ∀ β ∈ posRoot, ∀ t (a b : Fin 4 → ℤ), b = a + β →
      ent (δ β t) a b = t⁻¹ * ent (δ β 1) a b := by
    intro β hβ t a b h
    unfold ent
    split_ifs with hab
    · rcases eq_or_ne t 0 with rfl | ht
      · rw [hδ0 β hβ, _root_.inv_zero, zero_mul]; rfl
      obtain ⟨z, hz⟩ := hbh β hβ (Units.mk0 t ht)
      have e := hT β hβ z 1 ⟨a, hab.1⟩ ⟨b, hab.2⟩
      rw [hD β hβ z ⟨b, hab.2⟩ ⟨a, hab.1⟩ h, Units.val_mul, hz, Units.val_mk0, mul_one] at e
      have h1 : δ β 1 ⟨a, hab.1⟩ ⟨b, hab.2⟩ = δ β t ⟨a, hab.1⟩ ⟨b, hab.2⟩ * t :=
        mul_left_cancel₀ (Units.ne_zero (D z ⟨a, hab.1⟩)) (by rw [e]; ring)
      rw [h1, mul_comm (δ β t _ _) t, ← mul_assoc, inv_mul_cancel₀ ht, one_mul]
    · rw [mul_zero]
  have eA4 : ∀ β ∈ posRoot, ∀ t (a : Fin 4 → ℤ), t ≠ 0 →
      ent (δ β t) a a = ent (δ β 1) a a := by
    intro β hβ t a ht
    unfold ent
    split_ifs with ha
    · obtain ⟨z, hz⟩ := hbh β hβ (Units.mk0 t ht)
      have e := hT β hβ z 1 ⟨a, ha.1⟩ ⟨a, ha.2⟩
      rw [hz, Units.val_mk0, mul_one] at e
      exact mul_right_cancel₀ (Units.ne_zero (D z ⟨a, ha.1⟩)) (by rw [← e, mul_comm])
    · rfl
  obtain ⟨r₁, r₂, h₁0, h₁1, h₂0, h₂1, h12⟩ :=
    exists_two_ne_zero_ne_neg_one (K := K) (by rw [hq])
  have hB : ∀ β ∈ posRoot, ∀ χ ∈ W, ent (δ β 1) χ χ = 0 ∧
      ent (δ β 1) (χ - β) χ = ent (δ β 1) χ (χ + -β) := by
    intro β hβ χ hχ
    have key : ∀ r : K, r ≠ 0 → r + 1 ≠ 0 → ent (δ β 1) χ χ +
        r * (ent (δ β 1) (χ - β) χ + ent (δ β 1) χ (χ + -β)) = 0 := by
      intro r hr hr1
      have e := congrArg (fun M => ent M χ χ) (hδ₁ β hβ r 1)
      simp only [ent_add] at e
      rw [one_pow, ent_rootElt_mul β r _ hχ, ent_mul_rootElt (-β) 1 _ χ hχ, eA4 β hβ _ χ hr1,
        eA4 β hβ _ χ hr, eA2 β hβ r χ (χ + -β) (by abel), one_mul] at e
      linear_combination -e
    have k₁ := key r₁ h₁0 h₁1
    have k₂ := key r₂ h₂0 h₂1
    have hS : ent (δ β 1) (χ - β) χ + ent (δ β 1) χ (χ + -β) = 0 := by
      have h : (r₁ - r₂) * (ent (δ β 1) (χ - β) χ + ent (δ β 1) χ (χ + -β)) = 0 := by
        linear_combination k₁ - k₂
      exact (mul_eq_zero.1 h).resolve_left (sub_ne_zero.2 h12)
    refine ⟨by linear_combination k₁ - r₁ * hS, ?_⟩
    have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
    linear_combination hS - ent (δ β 1) χ (χ + -β) * h2
  obtain ⟨ν, hν⟩ : ∃ ν : (Fin 4 → ℤ) → (Fin 4 → ℤ) → K,
      ∀ β χ, ν β χ = ent (δ β 1) (χ + β) χ := ⟨_, fun _ _ => rfl⟩
  have hNF : ∀ β ∈ posRoot, ∀ t (a b : Fin 4 → ℤ), ent (δ β t) a b =
      if a = b + β then t * ν β b else if b = a + β then t⁻¹ * ν β a else 0 := by
    intro β hβ t a b
    split_ifs with h1 h2
    · subst h1
      rw [eA2 β hβ t _ b rfl, hν]
    · rw [eA3 β hβ t a b h2, hν]
      by_cases hb : b ∈ W
      · have := (hB β hβ b hb).2
        rw [show b - β = a by rw [h2, add_sub_cancel_right]] at this
        rw [this, show b + -β = a by rw [h2]; abel, h2]
      · rw [ent_of_not_mem_right _ _ hb, ← h2, ent_of_not_mem_left _ _ hb]
    · by_cases ha : a ∈ W
      swap
      · exact ent_of_not_mem_left _ _ ha
      by_cases h3 : a = b
      · subst h3
        rcases eq_or_ne t 0 with rfl | ht
        · rw [hδ0 β hβ, ent_zero]
        · rw [eA4 β hβ t a ht]
          exact (hB β hβ a ha).1
      · exact eA1 β hβ t a b h3 h1 h2
  have hZ : ∀ β ∈ posRoot, ∀ t (a b d : Fin 4 → ℤ), a - b = d → d ≠ β → d ≠ -β → d ≠ 0 →
      ent (δ β t) a b = 0 := by
    intro β hβ t a b d hd h1 h2 h3
    rw [hNF β hβ t a b, if_neg fun h => h1 (by rw [← hd, h]; abel),
      if_neg fun h => h2 (by rw [← hd, h]; abel)]
  have hcomm : ∀ β ∈ posRoot, ∀ γ ∈ posRoot, β ≠ γ → β + γ ∉ posRoot → ∀ φ ∈ W, φ + β ∈ W →
      φ + γ ∈ W → ν β φ = ν γ φ := by
    intro β hβ γ hγ hne hβγ φ hφ h1 h2
    obtain ⟨⟨f1, f2, f3, f4, f5⟩, ⟨f6, f7, f8⟩, ⟨f9, f10, f11⟩, f12⟩ :=
      posRoot_pair_facts β hβ γ hγ hne
    have e := congrArg (fun M => ent M (φ + β) (φ + γ)) (hδ₂ β hβ γ hγ hβγ)
    simp only [ent_add] at e
    rw [ent_rootElt_mul β 1 _ h1, ent_mul_rootElt (-γ) 1 _ _ h2, ent_rootElt_mul γ 1 _ h1,
      ent_mul_rootElt (-β) 1 _ _ h2] at e
    have z1 : ent (δ γ 1) (φ + β) (φ + γ) = 0 := hZ γ hγ 1 _ _ (β - γ) (by abel) f1 f2 f3
    have z2 : ent (δ β 1) (φ + β) (φ + γ) = 0 := hZ β hβ 1 _ _ (β - γ) (by abel) f4 f5 f3
    have z3 : ent (δ β 1) (φ + β - γ) (φ + γ) = 0 :=
      hZ β hβ 1 _ _ (β - γ - γ) (by abel) f6 f7 f8
    have z4 : ent (δ γ 1) (φ + β) (φ + γ + -β) = 0 :=
      hZ γ hγ 1 _ _ (β + β - γ) (by abel) f9 f10 f11
    have n1 : ent (δ γ 1) (φ + β - β) (φ + γ) = ν γ φ := by
      rw [add_sub_cancel_right, hNF γ hγ 1 φ (φ + γ), if_neg (vec_ne_of_sub_ne (by
        rw [show φ - (φ + γ + γ) = -(γ + γ) by abel]; exact neg_ne_zero.2 f12)), if_pos rfl,
        inv_one, one_mul]
    have n2 : ent (δ β 1) (φ + β) (φ + γ + -γ) = ν β φ := by
      rw [show φ + γ + -γ = φ by abel, hNF β hβ 1 (φ + β) φ, if_pos rfl, one_mul]
    rw [z1, z2, z3, z4, n1, n2] at e
    have h2' : (2 : K) = 0 := CharTwo.two_eq_zero
    linear_combination e - ν γ φ * h2'
  have hmin := minuscule_out hW
  set l : (Fin 4 → ℤ) → K := fun χ =>
    if h : ∃ β ∈ posRoot, χ + β ∈ W then ν h.choose χ else 0 with hl_def
  have hl : ∀ β ∈ posRoot, ∀ χ ∈ W, χ + β ∈ W → l χ = ν β χ := by
    intro β hβ χ hχ hχβ
    have h : ∃ β ∈ posRoot, χ + β ∈ W := ⟨β, hβ, hχβ⟩
    have hspec := h.choose_spec
    simp only [hl_def, dif_pos h]
    by_cases heq : h.choose = β
    · rw [heq]
    · exact hcomm _ hspec.1 β hβ heq (hmin _ hspec.1 β hβ χ hχ hspec.2 hχβ) χ hχ hspec.2 hχβ
  have hinv : ∀ t : K, t⁻¹ = t ^ 2 := by
    intro t
    rcases eq_or_ne t 0 with rfl | ht
    · rw [_root_.inv_zero, zero_pow two_ne_zero]
    · have h3 : t ^ 3 = 1 := by
        have := FiniteField.pow_card_sub_one_eq_one t ht
        rwa [hq] at this
      refine (eq_inv_of_mul_eq_one_right ?_).symm
      rw [← pow_succ', h3]
  refine ⟨fun χ => l χ, fun β hβ t => ?_⟩
  ext ψ χ
  have hXa : rootElt W β t ψ χ =
      (1 : Matrix W W K) ψ χ + t * (if (ψ : Fin 4 → ℤ) = χ + β then 1 else 0) := rfl
  have hXb : rootElt W (-β) (t ^ 2) ψ χ =
      (1 : Matrix W W K) ψ χ + t ^ 2 * (if (ψ : Fin 4 → ℤ) = χ + -β then 1 else 0) := rfl
  rw [Matrix.sub_apply, Matrix.diagonal_mul, Matrix.mul_diagonal, ← ent_coe (δ β t) ψ χ,
    hNF β hβ t, hXa, hXb]
  have hβ' := hβ0 β hβ
  have hββ : β + β ≠ 0 := posRoot_add_self_ne_zero β hβ
  have h2' : (2 : K) = 0 := CharTwo.two_eq_zero
  by_cases h1 : (ψ : Fin 4 → ℤ) = χ + β
  · have hne : ψ ≠ χ := fun e => hβ' (by
      have h := h1
      rw [e] at h
      simpa using h)
    have hn : ¬ (ψ : Fin 4 → ℤ) = χ + -β := fun h => hββ (by
      have h3 : β = -β := add_left_cancel (h1.symm.trans h)
      rw [show β + β = β - -β by abel, ← h3, sub_self])
    simp only [if_pos h1, if_neg hn, Matrix.one_apply_ne hne]
    rw [hl β hβ χ χ.2 (h1 ▸ ψ.2)]
    linear_combination t * ν β χ * h2'
  · by_cases h2 : (χ : Fin 4 → ℤ) = ψ + β
    · have hne : ψ ≠ χ := fun e => hβ' (by
        have h := h2
        rw [e] at h
        simpa using h.symm)
      have hn : (ψ : Fin 4 → ℤ) = χ + -β := by rw [h2]; abel
      simp only [if_neg h1, if_pos h2, if_pos hn, Matrix.one_apply_ne hne]
      rw [hl β hβ ψ ψ.2 (h2 ▸ χ.2), hinv]
      ring
    · have hn : ¬ (ψ : Fin 4 → ℤ) = χ + -β := fun h => h2 (by rw [h]; abel)
      simp only [if_neg h1, if_neg h2, if_neg hn]
      by_cases h3 : ψ = χ
      · subst h3
        rw [Matrix.one_apply_eq]
        ring
      · rw [Matrix.one_apply_ne h3]
        ring

variable {E : Type*} [AddCommGroup E] [Module K E]

theorem exists_invariant_compl_of_blocks_twist4 [Fintype K] [CharP K 2]
    (hq : Fintype.card K = 4) (hW : W = natWt ∨ W = evenWt ∨ W = oddWt) {G : Type*} [Group G]
    (ρ : G →* Module.End K E) (A : Submodule K E) (hAinv : ∀ g, ∀ a ∈ A, ρ g a ∈ A)
    (b : Module.Basis (W ⊕ W) K E) (hA : ∀ v, v ∈ A ↔ ∀ χ, b.repr v (Sum.inr χ) = 0)
    (x : (Fin 4 → ℤ) → K → G) {Z : Type*} (hz : Z → G) (D : Z → W → Kˣ)
    (bh : (Fin 4 → ℤ) → Z → Kˣ)
    (hD : ∀ β ∈ posRoot, ∀ z, ∀ ψ χ : W, (ψ : Fin 4 → ℤ) = χ + β → D z ψ = bh β z * D z χ)
    (hbh : ∀ β ∈ posRoot, ∀ c : Kˣ, ∃ z, bh β z = c)
    (hsep : ∀ β ∈ posRoot, ∀ ψ χ : W, ψ ≠ χ → (ψ : Fin 4 → ℤ) ≠ χ + β →
      (χ : Fin 4 → ℤ) ≠ ψ + β → ∃ z, bh β z = 1 ∧ D z ψ ≠ D z χ)
    (hR1 : ∀ β ∈ posRoot, ∀ s t, x β (s + t) = x β s * x β t)
    (hR2 : ∀ β ∈ posRoot, ∀ γ ∈ posRoot, β + γ ∉ posRoot → x β 1 * x γ 1 = x γ 1 * x β 1)
    (hR4 : ∀ β ∈ posRoot, ∀ z t, hz z * x β t = x β ((bh β z : K) * t) * hz z)
    (δ : (Fin 4 → ℤ) → K → Matrix W W K)
    (hx : ∀ β ∈ posRoot, ∀ t, LinearMap.toMatrix b b (ρ (x β t)) =
      fromBlocks (rootElt W β t) (δ β t) 0 (rootElt W (-β) (t ^ 2)))
    (hh : ∀ z, LinearMap.toMatrix b b (ρ (hz z)) =
      fromBlocks (diagonal fun χ => (D z χ : K)) 0 0 (diagonal fun χ => (D z χ : K)))
    (H : Subgroup G) [H.FiniteIndex] (hH : (H.index : K) ≠ 0)
    (hHgen : ∀ C : Submodule K E, (∀ β ∈ posRoot, ∀ t, ∀ c ∈ C, ρ (x β t) c ∈ C) →
      (∀ z, ∀ c ∈ C, ρ (hz z) c ∈ C) → ∀ g ∈ H, ∀ c ∈ C, ρ g c ∈ C) :
    ∃ C : Submodule K E, IsCompl A C ∧ ∀ g, ∀ c ∈ C, ρ g c ∈ C := by
  classical
  have hM : ∀ g g' : G, LinearMap.toMatrix b b (ρ (g * g')) =
      LinearMap.toMatrix b b (ρ g) * LinearMap.toMatrix b b (ρ g') := fun g g' => by
    rw [map_mul, LinearMap.toMatrix_mul]
  have hδT : ∀ β ∈ posRoot, ∀ z t, diagonal (fun χ => (D z χ : K)) * δ β t =
      δ β ((bh β z : K) * t) * diagonal (fun χ => (D z χ : K)) := by
    intro β hβ z t
    have h := congrArg (fun g => LinearMap.toMatrix b b (ρ g)) (hR4 β hβ z t)
    simp only [hM, hh, hx β hβ, fromBlocks_ext_mul] at h
    simpa using (fromBlocks_inj.1 h).2.1
  have hδ₁ : ∀ β ∈ posRoot, ∀ s t,
      δ β (s + t) = rootElt W β s * δ β t + δ β s * rootElt W (-β) (t ^ 2) := by
    intro β hβ s t
    have h := congrArg (fun g => LinearMap.toMatrix b b (ρ g)) (hR1 β hβ s t)
    simp only [hM, hx β hβ, fromBlocks_ext_mul] at h
    exact (fromBlocks_inj.1 h).2.1
  have hδ₂ : ∀ β ∈ posRoot, ∀ γ ∈ posRoot, β + γ ∉ posRoot →
      rootElt W β 1 * δ γ 1 + δ β 1 * rootElt W (-γ) 1 =
        rootElt W γ 1 * δ β 1 + δ γ 1 * rootElt W (-β) 1 := by
    intro β hβ γ hγ hβγ
    have h := congrArg (fun g => LinearMap.toMatrix b b (ρ g)) (hR2 β hβ γ hγ hβγ)
    simp only [hM, hx β hβ, hx γ hγ, fromBlocks_ext_mul, one_pow] at h
    exact (fromBlocks_inj.1 h).2.1
  obtain ⟨l, hl⟩ :=
    exists_diagonal_of_rootCocycle_twist4 hq hW D bh hD hbh hsep δ hδT hδ₁ hδ₂
  have hgx : ∀ β ∈ posRoot, ∀ t, ∀ c ∈ graphSub b (diagonal l), ρ (x β t) c ∈
      graphSub b (diagonal l) := fun β hβ t =>
    graphSub_invariant b _ _ (rootElt W β t) (rootElt W (-β) (t ^ 2))
      (by rw [hx β hβ t, hl β hβ t])
  have hgh : ∀ z, ∀ c ∈ graphSub b (diagonal l), ρ (hz z) c ∈ graphSub b (diagonal l) := by
    intro z
    refine graphSub_invariant b _ _ (diagonal fun χ => (D z χ : K))
      (diagonal fun χ => (D z χ : K)) ?_
    have e : diagonal l * diagonal (fun χ => (D z χ : K)) -
        diagonal (fun χ => (D z χ : K)) * diagonal l = 0 := by
      rw [diagonal_mul_diagonal, diagonal_mul_diagonal, sub_eq_zero]
      congr 1
      funext χ
      exact mul_comm _ _
    rw [hh z, e]
  exact exists_invariant_compl_of_index ρ A _ hAinv (isCompl_graphSub b _ hA) H hH
    (hHgen _ hgx hgh)

end CFSG.RankThree.GF2n.Stroth80.Ext1D4
