module

public import CFSG.RankThree.GF2n.Stroth80.Ext1D4Bridge
public import CFSG.RankThree.GF2n.Stroth80.Ext1D4Twist4
public import CFSG.RankThree.GF2n.Stroth80.Ext1D4TorusTwist

public section

namespace CFSG.RankThree.GF2n.Stroth80.Ext1D4

open Matrix

section Frob

variable {K : Type*} [Field K] [Fintype K] [CharP K 2]

theorem add_pow_two_pow (k : ℕ) (s t : K) : (s + t) ^ 2 ^ k = s ^ 2 ^ k + t ^ 2 ^ k :=
  add_pow_char_pow (x := s) (y := t) (n := k) (p := 2)

theorem pow_two_pow_card {f : ℕ} (hf : Fintype.card K = 2 ^ f) (t : K) : t ^ 2 ^ f = t := by
  rw [← hf]
  exact FiniteField.pow_card t

theorem pow_two_pow_pow_two_pow {f : ℕ} (hf : Fintype.card K = 2 ^ f) {k : ℕ} (hk : k ≤ f)
    (t : K) : (t ^ 2 ^ (f - k)) ^ 2 ^ k = t := by
  rw [← pow_mul, ← pow_add, Nat.sub_add_cancel hk, pow_two_pow_card hf]

theorem units_pow_two_pow_card {f : ℕ} (hf : Fintype.card K = 2 ^ f) (u : Kˣ) :
    u ^ 2 ^ f = u :=
  Units.ext (by rw [Units.val_pow_eq_pow_val, pow_two_pow_card hf])

theorem wtChar_add_twist (m k j : ℕ) (v : Fin 4 → ℤ) (z : Fin 4 → Kˣ) :
    wtChar m (k + j) v z = wtChar m k v z ^ 2 ^ j := by
  rw [wtChar, wtChar, pow_add, pow_mul]

theorem wtChar_twist_card {f : ℕ} (hf : Fintype.card K = 2 ^ f) (m k : ℕ) (v : Fin 4 → ℤ)
    (z : Fin 4 → Kˣ) : wtChar m (k + f) v z = wtChar m k v z := by
  rw [wtChar_add_twist, units_pow_two_pow_card hf]

end Frob

section Sep

variable {K : Type*} [Field K] [Fintype K] [CharP K 2]

theorem torusSep_general {f m : ℕ} (hf : Fintype.card K = 2 ^ f) (hm : 2 * m = Fintype.card K)
    (hq : 4 ≤ Fintype.card K) {W₁ W₂ : Finset (Fin 4 → ℤ)} (hW₁ : IsMinWt W₁)
    (hW₂ : IsMinWt W₂) {a₁ a₂ : ℕ} (ha₁ : a₁ < f) (ha₂ : a₂ < f)
    (hne : W₁ = W₂ → a₁ ≠ a₂ ∧ 8 ≤ Fintype.card K) :
    ∀ β ∈ posRoot, ∀ (ψ : W₁) (χ : W₂), ∃ z : Fin 4 → Kˣ, wtChar m 0 β z = 1 ∧
      wtChar m a₁ (ψ : Fin 4 → ℤ) z ≠ wtChar m a₂ (χ : Fin 4 → ℤ) z := by
  intro β hβ ψ χ
  set c := if a₂ ≤ a₁ then a₁ - a₂ else a₁ + f - a₂ with hc
  have hcf : c < f := by rw [hc]; split_ifs <;> omega
  have hshift : ∀ (v : Fin 4 → ℤ) (z : Fin 4 → Kˣ),
      wtChar m (a₁ + (f - a₂)) v z = wtChar m c v z := by
    intro v z
    rw [hc]
    split_ifs with h
    · rw [show a₁ + (f - a₂) = (a₁ - a₂) + f by omega, wtChar_twist_card hf]
    · rw [show a₁ + (f - a₂) = a₁ + f - a₂ by omega]
  have hne' : W₁ = W₂ → c ≠ 0 ∧ 8 ≤ Fintype.card K := fun h => by
    obtain ⟨h1, h2⟩ := hne h
    refine ⟨fun hc0 => h1 ?_, h2⟩
    rw [hc] at hc0
    split_ifs at hc0 <;> omega
  obtain ⟨z, hz1, hz2⟩ := torusSep_twist hf hm hq hW₁ hW₂ hcf hne' β hβ ψ χ
  refine ⟨z, hz1, fun heq => hz2 ?_⟩
  have := congrArg (fun u : Kˣ => u ^ 2 ^ (f - a₂)) heq
  rw [← wtChar_add_twist, ← wtChar_add_twist, hshift, show a₂ + (f - a₂) = 0 + f by omega,
    wtChar_twist_card hf] at this
  exact this

end Sep

section Blocks

variable {K : Type*} [Field K] [Fintype K] [CharP K 2] {E : Type*} [AddCommGroup E]
  [Module K E] {W₁ W₂ : Finset (Fin 4 → ℤ)}

theorem natCard_torus_ne_zero : ((Nat.card (Fin 4 → Kˣ) : ℕ) : K) ≠ 0 := by
  rw [Nat.card_fun, Nat.card_units, Nat.card_eq_fintype_card, Nat.card_eq_fintype_card,
    Fintype.card_fin, Ne, CharP.cast_eq_zero_iff K 2]
  obtain ⟨n, -, hn⟩ := FiniteField.card K 2
  rw [hn]
  have hodd : Odd (2 ^ (n : ℕ) - 1) :=
    Nat.Even.sub_odd Nat.one_le_two_pow (by rw [Nat.even_pow]; exact ⟨even_two, n.ne_zero⟩)
      odd_one
  exact fun h => (Nat.not_even_iff_odd.2 (hodd.pow (n := 4))) (even_iff_two_dvd.2 h)

theorem sum_diagonal_smul {ι V : Type*} [Fintype ι] [DecidableEq ι] [AddCommGroup V] [Module K V]
    (d : ι → K) (v : ι → V) (j : ι) : ∑ i, diagonal d i j • v i = d j • v j := by
  rw [Finset.sum_eq_single j (fun i _ hij => by rw [diagonal_apply_ne _ hij, zero_smul])
    (fun h => absurd (Finset.mem_univ j) h), diagonal_apply_eq]

theorem exists_blocks {G : Type*} [Group G] (ρ : G →* Module.End K E) (A : Submodule K E)
    (hAinv : ∀ g, ∀ a ∈ A, ρ g a ∈ A) (x : (Fin 4 → ℤ) → K → G) (hz : (Fin 4 → Kˣ) →* G)
    (P₁ : (Fin 4 → ℤ) → K → Matrix W₁ W₁ K) (P₂ : (Fin 4 → ℤ) → K → Matrix W₂ W₂ K)
    (D₁ : (Fin 4 → Kˣ) → W₁ → K) (D₂ : (Fin 4 → Kˣ) → W₂ → K) (bA : Module.Basis W₁ K A)
    (hbAx : ∀ β ∈ posRoot, ∀ t χ, ρ (x β t) (bA χ) = ∑ ψ, P₁ β t ψ χ • (bA ψ : E))
    (hbAh : ∀ z χ, ρ (hz z) (bA χ) = D₁ z χ • (bA χ : E)) (bQ : Module.Basis W₂ K (E ⧸ A))
    (hbQx : ∀ β ∈ posRoot, ∀ t χ (e : E), A.mkQ e = bQ χ →
      A.mkQ (ρ (x β t) e) = ∑ ψ, P₂ β t ψ χ • bQ ψ)
    (hbQh : ∀ z χ (e : E), A.mkQ e = bQ χ → A.mkQ (ρ (hz z) e) = D₂ z χ • bQ χ) :
    ∃ b : Module.Basis (W₁ ⊕ W₂) K E, (∀ v, v ∈ A ↔ ∀ χ, b.repr v (Sum.inr χ) = 0) ∧
      (∀ β ∈ posRoot, ∀ t, LinearMap.toMatrix b b (ρ (x β t)) =
        fromBlocks (P₁ β t) (LinearMap.toMatrix b b (ρ (x β t))).toBlocks₁₂ 0 (P₂ β t)) ∧
      ∀ z, LinearMap.toMatrix b b (ρ (hz z)) =
        fromBlocks (diagonal (D₁ z)) 0 0 (diagonal (D₂ z)) := by
  classical
  obtain ⟨f, hf, hfeig⟩ := exists_weight_lifts natCard_torus_ne_zero (ρ.comp hz) A
    (fun z a ha => hAinv _ a ha) bQ D₂ (fun z j e he => hbQh z j e he)
  refine ⟨basisOfLifts bA bQ f hf, mem_iff_basisOfLifts_repr_inr bA bQ f hf,
    fun β hβ t => toMatrix_basisOfLifts bA bQ f hf _ (hAinv _) _ (hbAx β hβ t) _
      fun χ => hbQx β hβ t χ (f χ) (hf χ), fun z => ?_⟩
  have h1 := toMatrix_basisOfLifts bA bQ f hf (ρ (hz z)) (hAinv _) (diagonal (D₁ z))
    (fun χ => by rw [sum_diagonal_smul, hbAh]) (diagonal (D₂ z))
    (fun χ => by rw [sum_diagonal_smul, hbQh z χ (f χ) (hf χ)])
  rw [h1, toBlocks₁₂_basisOfLifts_eq_zero bA bQ f hf (ρ (hz z)) (D₂ z) fun χ => hfeig z χ]

end Blocks

section Neg

theorem minWt_neg {W : Finset (Fin 4 → ℤ)} (hW : IsMinWt W) : ∀ χ ∈ W, -χ ∈ W := by
  rcases hW with rfl | rfl | rfl <;> decide

@[expose] def negWt {W : Finset (Fin 4 → ℤ)} (hW : IsMinWt W) : W ≃ W where
  toFun χ := ⟨-(χ : Fin 4 → ℤ), minWt_neg hW _ χ.2⟩
  invFun χ := ⟨-(χ : Fin 4 → ℤ), minWt_neg hW _ χ.2⟩
  left_inv χ := Subtype.ext (neg_neg _)
  right_inv χ := Subtype.ext (neg_neg _)

theorem rootElt_negWt {K : Type*} [Field K] {W : Finset (Fin 4 → ℤ)} (hW : IsMinWt W)
    (β : Fin 4 → ℤ) (u : K) (ψ χ : W) :
    rootElt W β u (negWt hW ψ) (negWt hW χ) = rootElt W (-β) u ψ χ := by
  classical
  have h1 : (negWt hW ψ = negWt hW χ) ↔ ψ = χ := (negWt hW).injective.eq_iff
  have h2 : ((negWt hW ψ : W) : Fin 4 → ℤ) = (negWt hW χ : Fin 4 → ℤ) + β ↔
      (ψ : Fin 4 → ℤ) = χ + -β := by
    change -(ψ : Fin 4 → ℤ) = -(χ : Fin 4 → ℤ) + β ↔ _
    constructor <;> intro h
    · rw [show (ψ : Fin 4 → ℤ) = -(-(ψ : Fin 4 → ℤ)) by rw [neg_neg], h]; abel
    · rw [h]; abel
  simp only [rootElt, Matrix.add_apply, Matrix.one_apply, Matrix.smul_apply, rootMat,
    Matrix.of_apply, h1, h2, smul_eq_mul]

end Neg

section Four

variable {K : Type*} [Field K] [Fintype K] [CharP K 2]

theorem wtChar_succ_of_card_four (hq : Fintype.card K = 4) (m k : ℕ) (v : Fin 4 → ℤ)
    (z : Fin 4 → Kˣ) : wtChar m (k + 1) v z = wtChar m k (-v) z := by
  have hu : ∀ u : Kˣ, u ^ 2 = u⁻¹ := by
    intro u
    have h4 : u ^ 4 = u := by
      have := units_pow_two_pow_card (f := 2) (by rw [hq]; rfl) u
      simpa using this
    have h3 : u ^ 2 * u = 1 := by
      have : u ^ 2 * u * u = 1 * u := by rw [one_mul, ← pow_succ, ← pow_succ]; exact h4
      exact mul_right_cancel this
    exact eq_inv_of_mul_eq_one_left h3
  have hneg : wtChar m k (-v) z = (wtChar m k v z)⁻¹ := by
    refine eq_inv_of_mul_eq_one_left ?_
    rw [← wtChar_add, neg_add_cancel]
    simp [wtChar]
  rw [wtChar_add_twist, pow_one, hu, hneg]

end Four

section Main

variable {K : Type*} [Field K] [Fintype K] [CharP K 2] {E : Type*} [AddCommGroup E]
  [Module K E]

theorem exists_invariant_compl_of_minuscule {f m : ℕ} (hf : Fintype.card K = 2 ^ f)
    (hm : 2 * m = Fintype.card K) (hq : 4 ≤ Fintype.card K) {G : Type*} [Group G]
    (ρ : G →* Module.End K E) (A : Submodule K E) (hAinv : ∀ g, ∀ a ∈ A, ρ g a ∈ A)
    (x : (Fin 4 → ℤ) → K → G) (hz : (Fin 4 → Kˣ) →* G)
    (hR1 : ∀ β ∈ posRoot, ∀ s t, x β (s + t) = x β s * x β t)
    (hR2 : ∀ β ∈ posRoot, ∀ γ ∈ posRoot, β + γ ∉ posRoot → x β 1 * x γ 1 = x γ 1 * x β 1)
    (hR3 : ∀ β ∈ posRoot, ∀ γ ∈ posRoot, β + γ ∈ posRoot →
      x β 1 * x γ 1 = x (β + γ) 1 * x γ 1 * x β 1)
    (hR4 : ∀ β ∈ posRoot, ∀ z t, hz z * x β t = x β ((wtChar m 0 β z : K) * t) * hz z)
    (H : Subgroup G) [H.FiniteIndex] (hH : (H.index : K) ≠ 0)
    (hHgen : ∀ C : Submodule K E, (∀ β ∈ posRoot, ∀ t, ∀ c ∈ C, ρ (x β t) c ∈ C) →
      (∀ z, ∀ c ∈ C, ρ (hz z) c ∈ C) → ∀ g ∈ H, ∀ c ∈ C, ρ g c ∈ C)
    {W₁ W₂ : Finset (Fin 4 → ℤ)} (hW₁ : IsMinWt W₁) (hW₂ : IsMinWt W₂) {a₁ a₂ : ℕ}
    (ha₁ : a₁ < f) (ha₂ : a₂ < f) (bA : Module.Basis W₁ K A)
    (hbAx : ∀ β ∈ posRoot, ∀ t χ,
      ρ (x β t) (bA χ) = ∑ ψ, rootElt W₁ β (t ^ 2 ^ a₁) ψ χ • (bA ψ : E))
    (hbAh : ∀ z χ, ρ (hz z) (bA χ) = (wtChar m a₁ (χ : Fin 4 → ℤ) z : K) • (bA χ : E))
    (bQ : Module.Basis W₂ K (E ⧸ A))
    (hbQx : ∀ β ∈ posRoot, ∀ t χ (e : E), A.mkQ e = bQ χ →
      A.mkQ (ρ (x β t) e) = ∑ ψ, rootElt W₂ β (t ^ 2 ^ a₂) ψ χ • bQ ψ)
    (hbQh : ∀ z χ (e : E), A.mkQ e = bQ χ →
      A.mkQ (ρ (hz z) e) = (wtChar m a₂ (χ : Fin 4 → ℤ) z : K) • bQ χ) :
    ∃ C : Submodule K E, IsCompl A C ∧ ∀ g, ∀ c ∈ C, ρ g c ∈ C := by
  classical
  by_cases hcase : W₁ = W₂ → a₁ ≠ a₂ ∧ 8 ≤ Fintype.card K
  ·
    obtain ⟨b, hA, hx, hh⟩ := exists_blocks ρ A hAinv x hz
      (fun β t => rootElt W₁ β (t ^ 2 ^ a₁)) (fun β t => rootElt W₂ β (t ^ 2 ^ a₂))
      (fun z χ => (wtChar m a₁ (χ : Fin 4 → ℤ) z : K))
      (fun z χ => (wtChar m a₂ (χ : Fin 4 → ℤ) z : K))
      bA hbAx hbAh bQ hbQx hbQh
    exact exists_invariant_compl_of_sep ρ A hAinv b hA x hz
      (fun z ψ => wtChar m a₁ (ψ : Fin 4 → ℤ) z) (fun z χ => wtChar m a₂ (χ : Fin 4 → ℤ) z)
      (fun β z => wtChar m 0 β z) (torusSep_general hf hm hq hW₁ hW₂ ha₁ ha₂ hcase) hR4 _ _ _
      hx hh H hH hHgen
  obtain ⟨hW, hsmall⟩ : W₁ = W₂ ∧ (a₁ ≠ a₂ → Fintype.card K < 8) := by
    refine ⟨by_contra fun h => hcase fun h' => absurd h' h, fun ha => ?_⟩
    by_contra h8
    exact hcase fun _ => ⟨ha, by omega⟩
  clear hcase
  subst hW
  obtain ⟨φ, hφ⟩ : ∃ φ : K → K, ∀ t, φ t = t ^ 2 ^ (f - a₁) := ⟨_, fun _ => rfl⟩
  have hφa : ∀ t, φ t ^ 2 ^ a₁ = t := fun t => by
    rw [hφ]
    exact pow_two_pow_pow_two_pow hf ha₁.le t
  have hφinv : ∀ t, φ (t ^ 2 ^ a₁) = t := fun t => by
    rw [hφ, ← pow_mul, ← pow_add, Nat.add_sub_cancel' ha₁.le, pow_two_pow_card hf]
  have hφ1 : φ 1 = 1 := by rw [hφ, one_pow]
  have hφadd : ∀ s t, φ (s + t) = φ s + φ t := fun s t => by
    rw [hφ, hφ, hφ, add_pow_two_pow]
  have hφmul : ∀ s t, φ (s * t) = φ s * φ t := fun s t => by
    rw [hφ, hφ, hφ, mul_pow]
  obtain ⟨x', hx'⟩ : ∃ x' : (Fin 4 → ℤ) → K → G, ∀ β t, x' β t = x β (φ t) :=
    ⟨_, fun _ _ => rfl⟩
  have hR1' : ∀ β ∈ posRoot, ∀ s t, x' β (s + t) = x' β s * x' β t := fun β hβ s t => by
    simp only [hx', hφadd]
    exact hR1 β hβ _ _
  have hR2' : ∀ β ∈ posRoot, ∀ γ ∈ posRoot, β + γ ∉ posRoot →
      x' β 1 * x' γ 1 = x' γ 1 * x' β 1 := fun β hβ γ hγ h => by
    simp only [hx', hφ1]
    exact hR2 β hβ γ hγ h
  have hR3' : ∀ β ∈ posRoot, ∀ γ ∈ posRoot, β + γ ∈ posRoot →
      x' β 1 * x' γ 1 = x' (β + γ) 1 * x' γ 1 * x' β 1 := fun β hβ γ hγ h => by
    simp only [hx', hφ1]
    exact hR3 β hβ γ hγ h
  have hR4' : ∀ β ∈ posRoot, ∀ (z : Fin 4 → Kˣ) t,
      hz z * x' β t = x' β ((wtChar m a₁ β z : K) * t) * hz z := fun β hβ z t => by
    have e : φ (wtChar m a₁ β z : K) = (wtChar m 0 β z : K) := by
      rw [hφ, ← Units.val_pow_eq_pow_val, ← wtChar_add_twist,
        show a₁ + (f - a₁) = 0 + f by omega, wtChar_twist_card hf]
    rw [hx', hx', hR4 β hβ z (φ t), hφmul, e]
  have hHgen' : ∀ C : Submodule K E, (∀ β ∈ posRoot, ∀ t, ∀ c ∈ C, ρ (x' β t) c ∈ C) →
      (∀ z, ∀ c ∈ C, ρ (hz z) c ∈ C) → ∀ g ∈ H, ∀ c ∈ C, ρ g c ∈ C := fun C hxC hzC =>
    hHgen C (fun β hβ t c hc => by
      have := hxC β hβ (t ^ 2 ^ a₁) c hc
      rwa [hx', hφinv] at this) hzC
  obtain ⟨-, hbh0, hsep0⟩ := torusData_self (K := K) hm hq hW₁
  have hD : ∀ β ∈ posRoot, ∀ z : Fin 4 → Kˣ, ∀ ψ χ : W₁, (ψ : Fin 4 → ℤ) = χ + β →
      wtChar m a₁ (ψ : Fin 4 → ℤ) z = wtChar m a₁ β z * wtChar m a₁ (χ : Fin 4 → ℤ) z :=
    fun β _ z ψ χ h => by rw [h, wtChar_add, mul_comm]
  have hbh : ∀ β ∈ posRoot, ∀ c : Kˣ, ∃ z : Fin 4 → Kˣ, wtChar m a₁ β z = c :=
    fun β hβ c => by
      obtain ⟨z, hz'⟩ := hbh0 β hβ (c ^ 2 ^ (f - a₁))
      refine ⟨z, ?_⟩
      rw [show a₁ = 0 + a₁ by omega, wtChar_add_twist, hz', ← pow_mul, ← pow_add,
        Nat.sub_add_cancel ha₁.le, units_pow_two_pow_card hf]
  have hsep : ∀ β ∈ posRoot, ∀ ψ χ : W₁, ψ ≠ χ → (ψ : Fin 4 → ℤ) ≠ χ + β →
      (χ : Fin 4 → ℤ) ≠ ψ + β → ∃ z : Fin 4 → Kˣ, wtChar m a₁ β z = 1 ∧
        wtChar m a₁ (ψ : Fin 4 → ℤ) z ≠ wtChar m a₁ (χ : Fin 4 → ℤ) z :=
    fun β hβ ψ χ h1 h2 h3 => by
      obtain ⟨z, hz1, hz2⟩ := hsep0 β hβ ψ χ h1 h2 h3
      refine ⟨z, by rw [show a₁ = 0 + a₁ by omega, wtChar_add_twist, hz1, one_pow],
        fun heq => hz2 ?_⟩
      have := congrArg (fun u : Kˣ => u ^ 2 ^ (f - a₁)) heq
      rwa [← wtChar_add_twist, ← wtChar_add_twist, show a₁ + (f - a₁) = 0 + f by omega,
        wtChar_twist_card hf, wtChar_twist_card hf] at this
  have hbAx' : ∀ β ∈ posRoot, ∀ t χ,
      ρ (x' β t) (bA χ) = ∑ ψ, rootElt W₁ β t ψ χ • (bA ψ : E) := fun β hβ t χ => by
    rw [hx', hbAx β hβ, hφa]
  by_cases ha12 : a₁ = a₂
  ·
    have hbQx' : ∀ β ∈ posRoot, ∀ t χ (e : E), A.mkQ e = bQ χ →
        A.mkQ (ρ (x' β t) e) = ∑ ψ, rootElt W₁ β t ψ χ • bQ ψ := fun β hβ t χ e he => by
      rw [hx', hbQx β hβ _ χ e he, ← ha12, hφa]
    have hbQh' : ∀ z χ (e : E), A.mkQ e = bQ χ →
        A.mkQ (ρ (hz z) e) = (wtChar m a₁ (χ : Fin 4 → ℤ) z : K) • bQ χ :=
      fun z χ e he => by rw [hbQh z χ e he, ha12]
    obtain ⟨b, hA, hx, hh⟩ := exists_blocks ρ A hAinv x' hz (fun β t => rootElt W₁ β t)
      (fun β t => rootElt W₁ β t) (fun z χ => (wtChar m a₁ (χ : Fin 4 → ℤ) z : K))
      (fun z χ => (wtChar m a₁ (χ : Fin 4 → ℤ) z : K)) bA hbAx' hbAh bQ hbQx' hbQh'
    exact exists_invariant_compl_of_blocks hq hW₁ ρ A hAinv b hA x' hz
      (fun z χ => wtChar m a₁ (χ : Fin 4 → ℤ) z) (fun β z => wtChar m a₁ β z) hD hbh hsep
      hR1' hR2' hR3' hR4' _ hx hh H hH hHgen'
  ·
    have h8 := hsmall ha12
    have hf2 : f = 2 := by
      have h1 : 2 ^ f < 2 ^ 3 := by rw [← hf]; norm_num; omega
      have h2 : 2 ^ 2 ≤ 2 ^ f := by rw [← hf]; norm_num; omega
      have h3 := (pow_lt_pow_iff_right₀ (by norm_num : (1 : ℕ) < 2)).1 h1
      have h4 := (pow_le_pow_iff_right₀ (by norm_num : (1 : ℕ) < 2)).1 h2
      omega
    subst hf2
    have hq4 : Fintype.card K = 4 := by rw [hf]; norm_num
    have hcases : (a₁ = 0 ∧ a₂ = 1) ∨ (a₁ = 1 ∧ a₂ = 0) := by omega
    have hφa₂ : ∀ t, φ t ^ 2 ^ a₂ = t ^ 2 := fun t => by
      rw [hφ]
      rcases hcases with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · rw [← pow_mul, show (2 : ℕ) ^ (2 - 0) * 2 ^ 1 = 2 ^ 2 * 2 by norm_num, pow_mul,
          pow_two_pow_card hf]
      · norm_num
    have hchar : ∀ (z : Fin 4 → Kˣ) (ψ : W₁),
        wtChar m a₂ ((negWt hW₁ ψ : W₁) : Fin 4 → ℤ) z = wtChar m a₁ (ψ : Fin 4 → ℤ) z := by
      intro z ψ
      change wtChar m a₂ (-(ψ : Fin 4 → ℤ)) z = _
      rcases hcases with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · simpa using wtChar_succ_of_card_four hq4 m 0 (-(ψ : Fin 4 → ℤ)) z
      · simpa using (wtChar_succ_of_card_four hq4 m 0 (ψ : Fin 4 → ℤ) z).symm
    obtain ⟨bQ', hbQ'⟩ : ∃ bQ' : Module.Basis W₁ K (E ⧸ A), ∀ ψ, bQ' ψ = bQ (negWt hW₁ ψ) :=
      ⟨bQ.reindex (negWt hW₁), fun ψ => by rw [Module.Basis.reindex_apply]; rfl⟩
    have hbQx' : ∀ β ∈ posRoot, ∀ t χ (e : E), A.mkQ e = bQ' χ →
        A.mkQ (ρ (x' β t) e) = ∑ ψ, rootElt W₁ (-β) (t ^ 2) ψ χ • bQ' ψ :=
      fun β hβ t χ e he => by
        rw [hbQ'] at he
        rw [hx', hbQx β hβ _ _ e he, hφa₂, ← (negWt hW₁).sum_comp]
        refine Finset.sum_congr rfl fun ψ _ => ?_
        rw [rootElt_negWt, hbQ']
    have hbQh' : ∀ z χ (e : E), A.mkQ e = bQ' χ →
        A.mkQ (ρ (hz z) e) = (wtChar m a₁ (χ : Fin 4 → ℤ) z : K) • bQ' χ :=
      fun z χ e he => by
        rw [hbQ'] at he ⊢
        rw [hbQh z _ e he, hchar]
    obtain ⟨b, hA, hx, hh⟩ := exists_blocks ρ A hAinv x' hz (fun β t => rootElt W₁ β t)
      (fun β t => rootElt W₁ (-β) (t ^ 2)) (fun z χ => (wtChar m a₁ (χ : Fin 4 → ℤ) z : K))
      (fun z χ => (wtChar m a₁ (χ : Fin 4 → ℤ) z : K)) bA hbAx' hbAh bQ' hbQx' hbQh'
    exact exists_invariant_compl_of_blocks_twist4 hq4 hW₁ ρ A hAinv b hA x' hz
      (fun z χ => wtChar m a₁ (χ : Fin 4 → ℤ) z) (fun β z => wtChar m a₁ β z) hD hbh hsep
      hR1' hR2' hR4' _ hx hh H hH hHgen'

end Main

end CFSG.RankThree.GF2n.Stroth80.Ext1D4
