module

public import CFSG.RankThree.PartTwo.Sec14.Item148Res8ProofUniTop
public import CFSG.RankThree.PartTwo.KFacts.K71SU3

public section

namespace CFSG.RankThree.PartTwo.Sec14.Item148Res8

open Matrix CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
open CFSG.GH74.GLS.IVK (fixedField mem_fixedField_iff)

variable {n f : ℕ} {K : Type} [Field K]

theorem extract_fixed [CharP K 2] {σ : K ≃+* K} {ω : K} (hω : ω ^ 2 + ω + 1 = 0)
    (hσω : σ ω = ω) {α β γ δ : K}
    (h1 : σ ((α + 1 * β) * (γ + 1 * δ)) = (α + 1 * β) * (γ + 1 * δ))
    (h2 : σ ((α + ω * β) * (γ + ω ^ 2 * δ)) = (α + ω * β) * (γ + ω ^ 2 * δ))
    (h3 : σ ((α + ω ^ 2 * β) * (γ + ω * δ)) = (α + ω ^ 2 * β) * (γ + ω * δ)) :
    σ (α * δ) = α * δ ∧ σ (β * γ) = β * γ ∧ σ (α * γ + β * δ) = α * γ + β * δ := by
  have h2K : (2 : K) = 0 := CharP.cast_eq_zero K 2
  set Q₁ := (α + 1 * β) * (γ + 1 * δ) with hQ₁
  set Q₂ := (α + ω * β) * (γ + ω ^ 2 * δ) with hQ₂
  set Q₃ := (α + ω ^ 2 * β) * (γ + ω * δ) with hQ₃
  have eb : α * δ = Q₁ + ω * Q₂ + ω ^ 2 * Q₃ := by
    rw [hQ₁, hQ₂, hQ₃]
    linear_combination (-(α * γ) - (1 + ω ^ 2 - ω) * (β * γ) - (ω ^ 3 - ω + 1) * (β * δ)) * hω +
      (-(ω ^ 3) * (α * δ)) * h2K
  have ec : β * γ = Q₁ + ω ^ 2 * Q₂ + ω * Q₃ := by
    rw [hQ₁, hQ₂, hQ₃]
    linear_combination (-(α * γ) - (1 + ω ^ 2 - ω) * (α * δ) - (ω ^ 3 - ω + 1) * (β * δ)) * hω +
      (-(ω ^ 3) * (β * γ)) * h2K
  have ea : α * γ + β * δ = Q₁ + Q₂ + Q₃ := by
    rw [hQ₁, hQ₂, hQ₃]
    linear_combination (-(α * δ) - β * γ) * hω + (-(α * γ) - ω ^ 3 * (β * δ)) * h2K
  clear_value Q₁ Q₂ Q₃
  refine ⟨?_, ?_, ?_⟩
  · rw [eb, map_add, map_add, map_mul, map_mul, map_pow, hσω, h1, h2, h3]
  · rw [ec, map_add, map_add, map_mul, map_mul, map_pow, hσω, h1, h2, h3]
  · rw [ea, map_add, map_add, h1, h2, h3]

theorem barVec_add (h : UnitaryFieldData 2 f K) (x y : Fin 3 → K) :
    barVec h (x + y) = barVec h x + barVec h y := by
  ext i
  simp [barVec_apply, map_add]

theorem barVec_single (h : UnitaryFieldData 2 f K) (i : Fin 3) :
    barVec h (Pi.single i 1) = Pi.single i 1 := by
  ext k
  by_cases hk : k = i
  · subst hk
    simp [barVec_apply]
  · simp [barVec_apply, Pi.single_eq_of_ne hk]

theorem testVec_facts [CharP K 2] (h : UnitaryFieldData 2 f K) {σ : K ≃+* K} {i j : Fin 3}
    (hij : i ≠ j) {t : K} (hσt : σ t = t) (htt : h.bar t * t = 1) (v : Fin 3 → K) :
    (∀ k, σ ((Pi.single i 1 + t • Pi.single j 1 : Fin 3 → K) k) =
      (Pi.single i 1 + t • Pi.single j 1 : Fin 3 → K) k) ∧
    barVec h (Pi.single i 1 + t • Pi.single j 1) ⬝ᵥ (Pi.single i 1 + t • Pi.single j 1) = 0 ∧
    barVec h v ⬝ᵥ (Pi.single i 1 + t • Pi.single j 1) = h.bar (v i) + t * h.bar (v j) := by
  have h2 : (2 : K) = 0 := CharP.cast_eq_zero K 2
  have hs : ∀ l k : Fin 3, σ ((Pi.single l (1 : K) : Fin 3 → K) k) =
      (Pi.single l (1 : K) : Fin 3 → K) k := by
    intro l k
    by_cases hk : k = l
    · subst hk
      simp
    · simp [Pi.single_eq_of_ne hk]
  refine ⟨fun k => ?_, ?_, ?_⟩
  · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, map_add, map_mul, hs, hσt]
  · rw [barVec_add, barVec_smul, barVec_single, barVec_single]
    simp only [add_dotProduct, dotProduct_add, smul_dotProduct, dotProduct_smul,
      single_dotProduct, Pi.single_eq_same, Pi.single_eq_of_ne hij, Pi.single_eq_of_ne hij.symm,
      smul_eq_mul, mul_zero, mul_one, add_zero, zero_add]
    linear_combination htt + h2
  · rw [dotProduct_add, dotProduct_smul, dotProduct_single, dotProduct_single, barVec_apply,
      barVec_apply, smul_eq_mul, mul_one, mul_one]

theorem norm_mem_of_rootGroups [CharP K 2]
    (h : UnitaryFieldData 2 (3 * n) K) (hn : 2 ≤ n) {σ : K ≃+* K} (hσ : orderOf σ = 3)
    (H : Subgroup (SpecialLinearGroup (Fin 3) K)) (hHU : H ≤ (suToSL h).range)
    {a : Fin 3 → K} (ha : barVec h a ⬝ᵥ a = 0)
    (hTa : ∀ c ∈ (fixedField σ ⊓ h.fixedField : Subfield K), rankOneSL a (barVec h a) ha c ∈ H)
    (hS : ∀ c, rankOneSL a (barVec h a) ha c ∈ H →
      c ∈ (fixedField σ ⊓ h.fixedField : Subfield K))
    {w : Fin 3 → K} (hw : barVec h w ⬝ᵥ w = 0)
    (hTw : ∀ b ∈ (fixedField σ ⊓ h.fixedField : Subfield K), rankOneSL w (barVec h w) hw b ∈ H)
    {g : SpecialLinearGroup (Fin 3) K} (hg : g ∈ H) :
    (barVec h ((g : Matrix (Fin 3) (Fin 3) K) *ᵥ a) ⬝ᵥ w) *
      h.bar (barVec h ((g : Matrix (Fin 3) (Fin 3) K) *ᵥ a) ⬝ᵥ w) ∈
        (fixedField σ ⊓ h.fixedField : Subfield K) := by
  have := h.finite
  have hcardFq := card_inf_barFixed h hσ
  have hK : Nat.card K = 2 ^ (2 * (3 * n)) := h.card
  have key := rootPair_pow (fixedField σ ⊓ h.fixedField) hn hcardFq (f := 2 * (3 * n)) (by omega)
    hK H ha hw hTa hS hTw hg
  rw [barVec_vecMul_inv h (hHU hg),
    barVec_dot_comm h ((g : Matrix (Fin 3) (Fin 3) K) *ᵥ a) w] at key
  refine Subfield.mem_inf.mpr ⟨?_, ?_⟩
  · obtain ⟨f₀, hf, -, hcard⟩ :=
      CFSG.RankThree.PartTwo.KFacts.exists_card_fixedField_of_orderOf_eq_three h hσ
    have hf₀ : f₀ = n := by omega
    rw [hf₀] at hcard
    exact mem_of_pow_eq_self (fixedField σ) hcard (Nat.one_lt_two_pow (by omega)) key
  · rw [UnitaryFieldData.mem_fixedField, map_mul, UnitaryFieldData.bar_bar, mul_comm]

theorem entry_fixed_of_rootGroups [CharP K 2]
    (h : UnitaryFieldData 2 (3 * n) K) (hn : 2 ≤ n) {σ : K ≃+* K} (hσ : orderOf σ = 3) {ω : K}
    (hω : ω ^ 2 + ω + 1 = 0) (hωbar : h.bar ω = ω ^ 2) (hσω : σ ω = ω)
    (H : Subgroup (SpecialLinearGroup (Fin 3) K)) (hHU : H ≤ (suToSL h).range)
    (hrat : ∀ w : Fin 3 → K, (∀ i, σ (w i) = w i) → ∀ hw : barVec h w ⬝ᵥ w = 0,
      ∀ b ∈ (fixedField σ ⊓ h.fixedField : Subfield K), rankOneSL w (barVec h w) hw b ∈ H)
    {a : Fin 3 → K} (ha : barVec h a ⬝ᵥ a = 0) (haσ : ∀ i, σ (a i) = a i)
    (hS : ∀ c, rankOneSL a (barVec h a) ha c ∈ H →
      c ∈ (fixedField σ ⊓ h.fixedField : Subfield K))
    {g : SpecialLinearGroup (Fin 3) K} (hg : g ∈ H) (r s : Fin 3) :
    σ (((g : Matrix (Fin 3) (Fin 3) K) *ᵥ a) r *
        h.bar (((g : Matrix (Fin 3) (Fin 3) K) *ᵥ a) s)) =
      ((g : Matrix (Fin 3) (Fin 3) K) *ᵥ a) r *
        h.bar (((g : Matrix (Fin 3) (Fin 3) K) *ᵥ a) s) := by
  obtain ⟨hω3, -, hω4⟩ := omega_facts hω
  set v := (g : Matrix (Fin 3) (Fin 3) K) *ᵥ a with hv
  have hFqσ : ∀ x ∈ (fixedField σ ⊓ h.fixedField : Subfield K), σ x = x := fun x hx =>
    (mem_fixedField_iff σ x).mp (Subfield.mem_inf.mp hx).1
  have hnorm : ∀ w : Fin 3 → K, (∀ i, σ (w i) = w i) → ∀ hw : barVec h w ⬝ᵥ w = 0,
      σ ((barVec h v ⬝ᵥ w) * h.bar (barVec h v ⬝ᵥ w)) =
        (barVec h v ⬝ᵥ w) * h.bar (barVec h v ⬝ᵥ w) :=
    fun w hwσ hw => hFqσ _ (norm_mem_of_rootGroups h hn hσ H hHU ha (hrat a haσ ha) hS hw
      (hrat w hwσ hw) hg)
  have hvv : barVec h v ⬝ᵥ v = 0 := by
    have hgi : ((g⁻¹ : SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *
        (g : Matrix (Fin 3) (Fin 3) K) = 1 := by
      have : ((g⁻¹ * g : SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = 1 := by
        rw [inv_mul_cancel]; rfl
      exact this
    rw [hv, ← barVec_vecMul_inv h (hHU hg), ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec,
      hgi, Matrix.one_mulVec, ha]
  have hQ : ∀ i j : Fin 3, i ≠ j → ∀ t tb : K, σ t = t → h.bar t = tb → tb * t = 1 →
      σ ((h.bar (v i) + t * h.bar (v j)) * (v i + tb * v j)) =
        (h.bar (v i) + t * h.bar (v j)) * (v i + tb * v j) := by
    intro i j hij t tb hσt htb htt
    obtain ⟨hwσ, hw, hy⟩ := testVec_facts h hij hσt (by rw [htb]; exact htt) v
    have := hnorm _ hwσ hw
    have hyb : h.bar (h.bar (v i) + t * h.bar (v j)) = v i + tb * v j := by
      rw [map_add, map_mul, UnitaryFieldData.bar_bar, UnitaryFieldData.bar_bar, htb]
    rwa [hy, hyb] at this
  have hb2 : h.bar (ω ^ 2) = ω := by
    rw [map_pow, hωbar]
    linear_combination hω4
  have hpair : ∀ i j : Fin 3, i ≠ j →
      σ (v i * h.bar (v j)) = v i * h.bar (v j) ∧
        σ (h.bar (v i) * v i + h.bar (v j) * v j) = h.bar (v i) * v i + h.bar (v j) * v j := by
    intro i j hij
    obtain ⟨-, hx, hA⟩ := extract_fixed hω hσω
      (hQ i j hij 1 1 (map_one σ) (map_one h.bar) (one_mul 1))
      (hQ i j hij ω (ω ^ 2) hσω hωbar (by linear_combination hω3))
      (hQ i j hij (ω ^ 2) ω (by rw [map_pow, hσω]) hb2 (by linear_combination hω3))
    refine ⟨?_, hA⟩
    rw [mul_comm]
    exact hx
  by_cases hrs : r = s
  swap
  · exact (hpair r s hrs).1
  subst hrs
  simp only [dotProduct, Fin.sum_univ_three, barVec_apply] at hvv
  fin_cases r
  · have e : v 0 * h.bar (v 0) = -(h.bar (v 1) * v 1 + h.bar (v 2) * v 2) := by
      linear_combination hvv
    rw [show ((⟨0, by decide⟩ : Fin 3)) = 0 from rfl, e, map_neg,
      (hpair 1 2 (by decide)).2]
  · have e : v 1 * h.bar (v 1) = -(h.bar (v 0) * v 0 + h.bar (v 2) * v 2) := by
      linear_combination hvv
    rw [show ((⟨1, by decide⟩ : Fin 3)) = 1 from rfl, e, map_neg,
      (hpair 0 2 (by decide)).2]
  · have e : v 2 * h.bar (v 2) = -(h.bar (v 0) * v 0 + h.bar (v 1) * v 1) := by
      linear_combination hvv
    rw [show ((⟨2, by decide⟩ : Fin 3)) = 2 from rfl, e, map_neg,
      (hpair 0 1 (by decide)).2]

theorem exists_map_eq_smul_uni [CharP K 2]
    (h : UnitaryFieldData 2 (3 * n) K) (hn : 2 ≤ n) {σ : K ≃+* K} (hσ : orderOf σ = 3) {ω : K}
    (hω : ω ^ 2 + ω + 1 = 0) (hωbar : h.bar ω = ω ^ 2) (hσω : σ ω = ω)
    (H : Subgroup (SpecialLinearGroup (Fin 3) K)) (hHU : H ≤ (suToSL h).range)
    (hrat : ∀ w : Fin 3 → K, (∀ i, σ (w i) = w i) → ∀ hw : barVec h w ⬝ᵥ w = 0,
      ∀ b ∈ (fixedField σ ⊓ h.fixedField : Subfield K), rankOneSL w (barVec h w) hw b ∈ H)
    (ha₀ : barVec h ![1, 1, 0] ⬝ᵥ ![1, 1, 0] = 0)
    (hS : ∀ c, rankOneSL ![1, 1, 0] (barVec h ![1, 1, 0]) ha₀ c ∈ H →
      c ∈ (fixedField σ ⊓ h.fixedField : Subfield K))
    (D₁ D₂ P : SpecialLinearGroup (Fin 3) K) (hD₁ : D₁ ∈ H) (hD₂ : D₂ ∈ H) (hP : P ∈ H)
    (hD₁M : (D₁ : Matrix (Fin 3) (Fin 3) K) = diagonal ![1, ω, ω ^ 2])
    (hD₂M : (D₂ : Matrix (Fin 3) (Fin 3) K) = diagonal ![1, ω ^ 2, ω])
    (hPM : (P : Matrix (Fin 3) (Fin 3) K) = !![0, 0, 1; 1, 0, 0; 0, 1, 0])
    {g : SpecialLinearGroup (Fin 3) K} (hg : g ∈ H) :
    ∃ ζ : K, ζ ^ 3 = 1 ∧
      ((SpecialLinearGroup.map σ.toRingHom g : SpecialLinearGroup (Fin 3) K) :
        Matrix (Fin 3) (Fin 3) K) = ζ • (g : Matrix (Fin 3) (Fin 3) K) := by
  obtain ⟨hω3, -, hω4⟩ := omega_facts hω
  have ha₀σ : ∀ i, σ ((![1, 1, 0] : Fin 3 → K) i) = (![1, 1, 0] : Fin 3 → K) i := by
    intro i
    fin_cases i <;> simp
  have hb2 : h.bar (ω ^ 2) = ω := by
    rw [map_pow, hωbar]
    linear_combination hω4
  have hent := fun (x : SpecialLinearGroup (Fin 3) K) (hx : x ∈ H) =>
    entry_fixed_of_rootGroups h hn hσ hω hωbar hσω H hHU hrat ha₀ ha₀σ hS hx
  have h01 : ∀ x ∈ H, ∀ r s : Fin 3,
      σ ((x : Matrix (Fin 3) (Fin 3) K) r 0 * h.bar ((x : Matrix (Fin 3) (Fin 3) K) s 1)) =
        (x : Matrix (Fin 3) (Fin 3) K) r 0 * h.bar ((x : Matrix (Fin 3) (Fin 3) K) s 1) ∧
      σ ((x : Matrix (Fin 3) (Fin 3) K) r 1 * h.bar ((x : Matrix (Fin 3) (Fin 3) K) s 0)) =
        (x : Matrix (Fin 3) (Fin 3) K) r 1 * h.bar ((x : Matrix (Fin 3) (Fin 3) K) s 0) := by
    intro x hx r s
    have hv : ∀ (t : K) (u : Fin 3 → K), u = ![1, t, 0] → ∀ k,
        ((x : Matrix (Fin 3) (Fin 3) K) *ᵥ u) k =
          (x : Matrix (Fin 3) (Fin 3) K) k 0 + t * (x : Matrix (Fin 3) (Fin 3) K) k 1 := by
      intro t u hu k
      rw [hu]
      simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three]
      ring
    have hbarv : ∀ (t tb : K), h.bar t = tb → ∀ (u : Fin 3 → K), u = ![1, t, 0] → ∀ k,
        h.bar (((x : Matrix (Fin 3) (Fin 3) K) *ᵥ u) k) =
          h.bar ((x : Matrix (Fin 3) (Fin 3) K) k 0) +
            tb * h.bar ((x : Matrix (Fin 3) (Fin 3) K) k 1) := by
      intro t tb htb u hu k
      rw [hv t u hu k, map_add, map_mul, htb]
    have e1 := hent x hx r s
    have e2 := hent (x * D₁) (H.mul_mem hx hD₁) r s
    have e3 := hent (x * D₂) (H.mul_mem hx hD₂) r s
    have hD₁v : ((x * D₁ : SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ
        ![1, 1, 0] = (x : Matrix (Fin 3) (Fin 3) K) *ᵥ ![1, ω, 0] := by
      have : ((x * D₁ : SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
          (x : Matrix (Fin 3) (Fin 3) K) * (D₁ : Matrix (Fin 3) (Fin 3) K) := rfl
      rw [this, ← Matrix.mulVec_mulVec, hD₁M]
      congr 1
      ext i
      fin_cases i <;> simp [mulVec_diagonal]
    have hD₂v : ((x * D₂ : SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ
        ![1, 1, 0] = (x : Matrix (Fin 3) (Fin 3) K) *ᵥ ![1, ω ^ 2, 0] := by
      have : ((x * D₂ : SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
          (x : Matrix (Fin 3) (Fin 3) K) * (D₂ : Matrix (Fin 3) (Fin 3) K) := rfl
      rw [this, ← Matrix.mulVec_mulVec, hD₂M]
      congr 1
      ext i
      fin_cases i <;> simp [mulVec_diagonal]
    rw [hv 1 ![1, 1, 0] rfl r, hbarv 1 1 (map_one h.bar) ![1, 1, 0] rfl s] at e1
    rw [hD₁v, hv ω _ rfl r, hbarv ω (ω ^ 2) hωbar _ rfl s] at e2
    rw [hD₂v, hv (ω ^ 2) _ rfl r, hbarv (ω ^ 2) ω hb2 _ rfl s] at e3
    obtain ⟨hx1, hx2, -⟩ := extract_fixed hω hσω e1 e2 e3
    exact ⟨hx1, hx2⟩
  have hcols : ∀ x ∈ H, ∀ i j : Fin 3, i ≠ j → ∀ r s : Fin 3,
      σ ((x : Matrix (Fin 3) (Fin 3) K) r i * h.bar ((x : Matrix (Fin 3) (Fin 3) K) s j)) =
        (x : Matrix (Fin 3) (Fin 3) K) r i * h.bar ((x : Matrix (Fin 3) (Fin 3) K) s j) := by
    intro x hx i j hij r s
    have hxP : ((x * P : SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
        (x : Matrix (Fin 3) (Fin 3) K) * (P : Matrix (Fin 3) (Fin 3) K) := rfl
    have hxPP : ((x * P * P : SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
        (x : Matrix (Fin 3) (Fin 3) K) * (P : Matrix (Fin 3) (Fin 3) K) *
          (P : Matrix (Fin 3) (Fin 3) K) := rfl
    have hP0 : ∀ k, ((x : Matrix (Fin 3) (Fin 3) K) * (P : Matrix (Fin 3) (Fin 3) K)) k 0 =
        (x : Matrix (Fin 3) (Fin 3) K) k 1 := by
      intro k
      rw [hPM]
      simp [Matrix.mul_apply, Fin.sum_univ_three]
    have hP1 : ∀ k, ((x : Matrix (Fin 3) (Fin 3) K) * (P : Matrix (Fin 3) (Fin 3) K)) k 1 =
        (x : Matrix (Fin 3) (Fin 3) K) k 2 := by
      intro k
      rw [hPM]
      simp [Matrix.mul_apply, Fin.sum_univ_three]
    have hPP0 : ∀ k, ((x : Matrix (Fin 3) (Fin 3) K) * (P : Matrix (Fin 3) (Fin 3) K) *
        (P : Matrix (Fin 3) (Fin 3) K)) k 0 = (x : Matrix (Fin 3) (Fin 3) K) k 2 := by
      intro k
      rw [hPM]
      simp [Matrix.mul_apply, Fin.sum_univ_three]
    have hPP1 : ∀ k, ((x : Matrix (Fin 3) (Fin 3) K) * (P : Matrix (Fin 3) (Fin 3) K) *
        (P : Matrix (Fin 3) (Fin 3) K)) k 1 = (x : Matrix (Fin 3) (Fin 3) K) k 0 := by
      intro k
      rw [hPM]
      simp [Matrix.mul_apply, Fin.sum_univ_three]
    have g1 := h01 x hx r s
    have g2 := h01 (x * P) (H.mul_mem hx hP) r s
    have g3 := h01 (x * P * P) (H.mul_mem (H.mul_mem hx hP) hP) r s
    rw [hxP, hP0, hP1, hP0, hP1] at g2
    rw [hxPP, hPP0, hPP1, hPP0, hPP1] at g3
    fin_cases i <;> fin_cases j
    · exact absurd rfl hij
    · exact g1.1
    · exact g3.2
    · exact g1.2
    · exact absurd rfl hij
    · exact g2.1
    · exact g3.1
    · exact g2.2
    · exact absurd rfl hij
  set hM := (g : Matrix (Fin 3) (Fin 3) K) with hhM
  set hiM := ((g⁻¹ : SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) with hhiM
  have hhi : hiM * hM = 1 := by
    have : ((g⁻¹ * g : SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = 1 := by
      rw [inv_mul_cancel]; rfl
    exact this
  have hih : hM * hiM = 1 := by
    have : ((g * g⁻¹ : SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = 1 := by
      rw [mul_inv_cancel]; rfl
    exact this
  have hiM_eq : hiM = (hM.map h.bar)ᵀ := inv_eq_of_mem_range h (hHU hg)
  set sM := hM.map σ with hsM
  set siM := hiM.map σ with hsiM
  have hsi : siM * sM = 1 := by
    rw [hsM, hsiM, ← Matrix.map_mul, hhi, Matrix.map_one σ (map_zero σ) (map_one σ)]
  have hmap : ((SpecialLinearGroup.map σ.toRingHom g : SpecialLinearGroup (Fin 3) K) :
      Matrix (Fin 3) (Fin 3) K) = sM := by
    rw [SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply]
    rfl
  set X := hiM * sM with hX
  have hcomm : Pairwise fun i j : Fin 3 => Commute (single i j (1 : K)) X := by
    intro i j hij
    have hfix : (hM * single i j (1 : K) * hiM).map σ = hM * single i j (1 : K) * hiM := by
      ext r c
      rw [Matrix.map_apply, mul_single_mul, vecMulVec_apply]
      show σ (hM r i * hiM j c) = hM r i * hiM j c
      rw [hiM_eq]
      exact hcols g hg i j hij r c
    have hsingle : (single i j (1 : K)).map σ = single i j (1 : K) := by
      ext r c
      simp [Matrix.single_apply]
    rw [Matrix.map_mul, Matrix.map_mul, hsingle] at hfix
    show single i j 1 * X = X * single i j 1
    calc single i j (1 : K) * X = hiM * (hM * single i j 1 * hiM) * sM := by
          rw [hX]
          simp only [← Matrix.mul_assoc, hhi, Matrix.one_mul]
      _ = hiM * (sM * single i j 1 * siM) * sM := by rw [hfix]
      _ = X * single i j 1 := by
          rw [hX]
          simp only [Matrix.mul_assoc, hsi, Matrix.mul_one]
  obtain ⟨ζ, hζ⟩ := Matrix.mem_range_scalar_of_commute_single hcomm
  refine ⟨ζ, ?_, ?_⟩
  · have hdet : X.det = 1 := by
      have e : (hM.map σ).det = σ hM.det := (RingHom.map_det σ.toRingHom hM).symm
      have hd1 : hM.det = 1 := g.2
      have hd2 : hiM.det = 1 := g⁻¹.2
      rw [hX, Matrix.det_mul, hsM, e, hd1, hd2, map_one, one_mul]
    rw [← hζ, Matrix.scalar_apply, Matrix.det_diagonal, Finset.prod_const, Finset.card_univ,
      Fintype.card_fin] at hdet
    exact hdet
  · rw [hmap]
    have e : sM = hM * X := by
      rw [hX, ← Matrix.mul_assoc, hih, Matrix.one_mul]
    rw [e, ← hζ, Matrix.scalar_apply, ← Matrix.smul_one_eq_diagonal, Matrix.mul_smul,
      Matrix.mul_one]

end CFSG.RankThree.PartTwo.Sec14.Item148Res8
