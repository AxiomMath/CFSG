module

public import CFSG.RankThree.GF2n.Stroth80.Sec715TriBilWt

public section

namespace CFSG.RankThree.GF2n.Stroth80.Tri

open CFSG.LieType.D4Small

theorem bil_coeff4 {K : Type*} [Field K] [Finite K] {V : Type*} [AddCommGroup V] [Module K V]
    {n₁ n₂ n₃ n₄ : ℕ} (h₁ : n₁ < Nat.card K) (h₂ : n₂ < Nat.card K) (h₃ : n₃ < Nat.card K)
    (h₄ : n₄ < Nat.card K) {v₁ v₂ v₃ v₄ : V}
    (h : ∀ c : K, c ^ n₁ • v₁ + c ^ n₂ • v₂ + c ^ n₃ • v₃ + c ^ n₄ • v₄ = 0) (m : ℕ) :
    (if n₁ = m then v₁ else 0) + (if n₂ = m then v₂ else 0) + (if n₃ = m then v₃ else 0) +
      (if n₄ = m then v₄ else 0) = 0 := by
  classical
  letI : Fintype K := Fintype.ofFinite K
  rw [← Module.forall_dual_apply_eq_zero_iff K]
  intro φ
  set P : Polynomial K := Polynomial.C (φ v₁) * Polynomial.X ^ n₁ +
    Polynomial.C (φ v₂) * Polynomial.X ^ n₂ + Polynomial.C (φ v₃) * Polynomial.X ^ n₃ +
    Polynomial.C (φ v₄) * Polynomial.X ^ n₄ with hP
  have hcard : Fintype.card K = Nat.card K := (Nat.card_eq_fintype_card).symm
  have hdeg : P.natDegree < (Finset.univ : Finset K).card := by
    rw [Finset.card_univ, hcard]
    have hle : ∀ (x : K) (n : ℕ), n < Nat.card K →
        (Polynomial.C x * Polynomial.X ^ n).natDegree < Nat.card K := fun x n hn =>
      lt_of_le_of_lt (Polynomial.natDegree_C_mul_X_pow_le x n) hn
    have h12 := Polynomial.natDegree_add_le (Polynomial.C (φ v₁) * Polynomial.X ^ n₁)
      (Polynomial.C (φ v₂) * Polynomial.X ^ n₂)
    have h123 := Polynomial.natDegree_add_le (Polynomial.C (φ v₁) * Polynomial.X ^ n₁ +
      Polynomial.C (φ v₂) * Polynomial.X ^ n₂) (Polynomial.C (φ v₃) * Polynomial.X ^ n₃)
    have h1234 := Polynomial.natDegree_add_le (Polynomial.C (φ v₁) * Polynomial.X ^ n₁ +
      Polynomial.C (φ v₂) * Polynomial.X ^ n₂ + Polynomial.C (φ v₃) * Polynomial.X ^ n₃)
      (Polynomial.C (φ v₄) * Polynomial.X ^ n₄)
    have e1 := hle (φ v₁) n₁ h₁
    have e2 := hle (φ v₂) n₂ h₂
    have e3 := hle (φ v₃) n₃ h₃
    have e4 := hle (φ v₄) n₄ h₄
    rw [hP]
    omega
  have heval : ∀ c ∈ (Finset.univ : Finset K), P.eval c = 0 := by
    intro c _
    have h1 := congrArg φ (h c)
    simp only [map_add, map_smul, smul_eq_mul, map_zero] at h1
    simp only [hP, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C,
      Polynomial.eval_pow, Polynomial.eval_X]
    linear_combination h1
  have hP0 : P = 0 := Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero' P Finset.univ
    heval hdeg
  have hm := congrArg (fun p : Polynomial K => p.coeff m) hP0
  simp only [hP, Polynomial.coeff_add, Polynomial.coeff_C_mul_X_pow, Polynomial.coeff_zero] at hm
  simp only [map_add, apply_ite φ, map_zero]
  simpa only [eq_comm] using hm

section Weights

variable {G : Type*} [Group G] {K : Type*} [Field K] [Finite K] [CharP K 2] {D : D4Datum G K}
  {X : Type*} [AddCommGroup X] [Module K X] {ρ : Representation K G X} {j : ℕ}
  {C : Finset (Fin 4 → ZMod (Nat.card Kˣ))} {b : (Fin 4 → ZMod (Nat.card Kˣ)) → X}

theorem NF.exists_smul_of_mem_wtSpace (h : NF D ρ j C b) {a : Fin 4 → ZMod (Nat.card Kˣ)}
    {x : X} (hx : x ∈ D.wtSpace ρ a) : ∃ c : K, x = c • b a := by
  have hle : Submodule.span K (b '' C) ≤
      (Submodule.span K {b a}).comap (D4Datum.wtProj D ρ a) := by
    rw [Submodule.span_le]
    rintro _ ⟨a', ha', rfl⟩
    show D4Datum.wtProj D ρ a (b a') ∈ Submodule.span K {b a}
    rw [D4Datum.wtProj_of_mem D ρ (h.mem_wtSpace a' ha')]
    by_cases haa : a = a'
    · rw [if_pos haa, ← haa]
      exact Submodule.mem_span_singleton_self _
    · rw [if_neg haa]
      exact Submodule.zero_mem _
  have hx1 : x ∈ Submodule.span K (b '' C) := by
    rw [h.span_eq]
    trivial
  have hx2 := hle hx1
  rw [Submodule.mem_comap, D4Datum.wtProj_of_mem D ρ hx, if_pos rfl] at hx2
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hx2
  exact ⟨c, hc.symm⟩

theorem NF.eq_zero_of_mem_wtSpace (h : NF D ρ j C b) {a : Fin 4 → ZMod (Nat.card Kˣ)}
    (ha : a ∉ C) {x : X} (hx : x ∈ D.wtSpace ρ a) : x = 0 := by
  have hle : Submodule.span K (b '' C) ≤
      (⊥ : Submodule K X).comap (D4Datum.wtProj D ρ a) := by
    rw [Submodule.span_le]
    rintro _ ⟨a', ha', rfl⟩
    show D4Datum.wtProj D ρ a (b a') ∈ (⊥ : Submodule K X)
    rw [D4Datum.wtProj_of_mem D ρ (h.mem_wtSpace a' ha'),
      if_neg (fun (haa : a = a') => ha (haa ▸ ha'))]
    exact Submodule.zero_mem _
  have hx1 : x ∈ Submodule.span K (b '' C) := by
    rw [h.span_eq]
    trivial
  have hx2 := hle hx1
  rw [Submodule.mem_comap, D4Datum.wtProj_of_mem D ρ hx, if_pos rfl] at hx2
  exact (Submodule.mem_bot K).mp hx2

end Weights

section Bil

variable {G : Type*} [Group G] {K : Type*} [Field K] [Finite K] [CharP K 2]
  {D : D4Datum G K} {X Y V : Type*} [AddCommGroup X] [Module K X] [AddCommGroup Y] [Module K Y]
  [AddCommGroup V] [Module K V] {ρX : Representation K G X} {ρY : Representation K G Y}
  {ρV : Representation K G V} {jX jY : ℕ} {CX CY CV : Finset (Fin 4 → ZMod (Nat.card Kˣ))}
  {bX : (Fin 4 → ZMod (Nat.card Kˣ)) → X} {bY : (Fin 4 → ZMod (Nat.card Kˣ)) → Y}
  {bV : (Fin 4 → ZMod (Nat.card Kˣ)) → V} {β : X →ₗ[K] Y →ₗ[K] V}

theorem bil_mem_wtSpace (hX : NF D ρX jX CX bX) (hY : NF D ρY jY CY bY)
    (hβ : ∀ (g : G) (x : X) (y : Y), β (ρX g x) (ρY g y) = ρV g (β x y))
    {a b : Fin 4 → ZMod (Nat.card Kˣ)} (ha : a ∈ CX) (hb : b ∈ CY) :
    β (bX a) (bY b) ∈ D.wtSpace ρV (a + b) := by
  rw [D4Datum.mem_wtSpace]
  intro t
  have h1 := hβ (D.h t) (bX a) (bY b)
  rw [(D4Datum.mem_wtSpace D ρX).mp (hX.mem_wtSpace a ha) t,
    (D4Datum.mem_wtSpace D ρY).mp (hY.mem_wtSpace b hb) t] at h1
  rw [← h1]
  simp only [map_smul, LinearMap.smul_apply, smul_smul]
  rw [D4Datum.wtChar_add, Units.val_mul, mul_comm]

theorem bil_exists_l (hX : NF D ρX jX CX bX) (hY : NF D ρY jY CY bY) (hV : NF D ρV 0 CV bV)
    (hβ : ∀ (g : G) (x : X) (y : Y), β (ρX g x) (ρY g y) = ρV g (β x y)) :
    ∃ l : (Fin 4 → ZMod (Nat.card Kˣ)) → (Fin 4 → ZMod (Nat.card Kˣ)) → K,
      ∀ a ∈ CX, ∀ b ∈ CY,
        β (bX a) (bY b) = if a + b ∈ CV then l a b • bV (a + b) else 0 := by
  have hex : ∀ a b : Fin 4 → ZMod (Nat.card Kˣ), ∃ l : K, a ∈ CX → b ∈ CY →
      β (bX a) (bY b) = if a + b ∈ CV then l • bV (a + b) else 0 := by
    intro a b
    by_cases hab : a ∈ CX ∧ b ∈ CY
    · have hmem := bil_mem_wtSpace hX hY hβ hab.1 hab.2
      by_cases hv : a + b ∈ CV
      · obtain ⟨c, hc⟩ := hV.exists_smul_of_mem_wtSpace hmem
        exact ⟨c, fun _ _ => by rw [if_pos hv]; exact hc⟩
      · exact ⟨0, fun _ _ => by rw [if_neg hv]; exact hV.eq_zero_of_mem_wtSpace hv hmem⟩
    · exact ⟨0, fun h1 h2 => absurd ⟨h1, h2⟩ hab⟩
  choose l hl using hex
  exact ⟨l, fun a ha b hb => hl a b ha hb⟩

theorem bil_expand (hX : NF D ρX jX CX bX) (hY : NF D ρY jY CY bY)
    (hβ : ∀ (g : G) (x : X) (y : Y), β (ρX g x) (ρY g y) = ρV g (β x y))
    {a b A B : Fin 4 → ZMod (Nat.card Kˣ)} (ha : a ∈ CX) (hb : b ∈ CY) {γ : Fin 4 → ℤ}
    (hγ : IsD4Root γ) (c : K)
    (hA : A = a + (2 : ZMod (Nat.card Kˣ)) ^ jX • castW (Nat.card Kˣ) γ)
    (hB : B = b + (2 : ZMod (Nat.card Kˣ)) ^ jY • castW (Nat.card Kˣ) γ) :
    β (bX a) (bY b) + c ^ 2 ^ jX • (if A ∈ CX then β (bX A) (bY b) else 0) +
      c ^ 2 ^ jY • (if B ∈ CY then β (bX a) (bY B) else 0) +
      c ^ (2 ^ jX + 2 ^ jY) • (if A ∈ CX ∧ B ∈ CY then β (bX A) (bY B) else 0) =
    ρV (D.x γ c) (β (bX a) (bY b)) := by
  have h := hβ (D.x γ c) (bX a) (bY b)
  rw [hX.root γ hγ c a ha, hY.root γ hγ c b hb, ← hA, ← hB] at h
  rw [← h]
  have hpow : c ^ (2 ^ jX + 2 ^ jY) = c ^ 2 ^ jY * c ^ 2 ^ jX := by rw [pow_add, mul_comm]
  rw [hpow]
  by_cases h1 : A ∈ CX <;> by_cases h2 : B ∈ CY <;>
    simp [h1, h2, map_add, LinearMap.add_apply, map_smul, LinearMap.smul_apply,
      smul_smul] <;> abel

theorem bil_rho_V (hV : NF D ρV 0 CV bV) {l : K} {w : Fin 4 → ZMod (Nat.card Kˣ)} {γ : Fin 4 → ℤ}
    (hγ : IsD4Root γ) (c : K) (hw : w ∈ CV) :
    ρV (D.x γ c) (l • bV w) = l • bV w +
      c • (if w + castW (Nat.card Kˣ) γ ∈ CV then l • bV (w + castW (Nat.card Kˣ) γ) else 0) := by
  have h := hV.root γ hγ c w hw
  simp only [pow_zero, one_smul, pow_one] at h
  rw [map_smul, h]
  by_cases h1 : w + castW (Nat.card Kˣ) γ ∈ CV <;> simp [h1, smul_add, smul_comm l c]

theorem bil_key (hX : NF D ρX jX CX bX) (hY : NF D ρY jY CY bY) (hV : NF D ρV 0 CV bV)
    (hβ : ∀ (g : G) (x : X) (y : Y), β (ρX g x) (ρY g y) = ρV g (β x y))
    {l : (Fin 4 → ZMod (Nat.card Kˣ)) → (Fin 4 → ZMod (Nat.card Kˣ)) → K}
    (hl : ∀ a ∈ CX, ∀ b ∈ CY, β (bX a) (bY b) = if a + b ∈ CV then l a b • bV (a + b) else 0)
    {a b A B : Fin 4 → ZMod (Nat.card Kˣ)} (ha : a ∈ CX) (hb : b ∈ CY) {γ : Fin 4 → ℤ}
    (hγ : IsD4Root γ) (c : K)
    (hA : A = a + (2 : ZMod (Nat.card Kˣ)) ^ jX • castW (Nat.card Kˣ) γ)
    (hB : B = b + (2 : ZMod (Nat.card Kˣ)) ^ jY • castW (Nat.card Kˣ) γ) :
    c ^ 2 ^ jX • (if A ∈ CX then β (bX A) (bY b) else 0) +
      c ^ 2 ^ jY • (if B ∈ CY then β (bX a) (bY B) else 0) +
      c ^ (2 ^ jX + 2 ^ jY) • (if A ∈ CX ∧ B ∈ CY then β (bX A) (bY B) else 0) +
      c ^ 1 • -(if a + b ∈ CV ∧ a + b + castW (Nat.card Kˣ) γ ∈ CV then
        l a b • bV (a + b + castW (Nat.card Kˣ) γ) else 0) = 0 := by
  have hexp := bil_expand hX hY hβ ha hb hγ c hA hB
  have hrho : ρV (D.x γ c) (β (bX a) (bY b)) = β (bX a) (bY b) +
      c • (if a + b ∈ CV ∧ a + b + castW (Nat.card Kˣ) γ ∈ CV then
        l a b • bV (a + b + castW (Nat.card Kˣ) γ) else 0) := by
    by_cases hv : a + b ∈ CV
    · rw [hl a ha b hb, if_pos hv, bil_rho_V hV hγ c hv]
      by_cases hv' : a + b + castW (Nat.card Kˣ) γ ∈ CV <;> simp [hv, hv']
    · rw [hl a ha b hb, if_neg hv]
      simp [hv]
  rw [hrho] at hexp
  rw [pow_one, smul_neg]
  rw [← sub_eq_zero] at hexp
  exact Eq.trans (by abel) hexp

theorem bil_eq_zero_of_basis (hX : NF D ρX jX CX bX) (hY : NF D ρY jY CY bY)
    (h : ∀ a ∈ CX, ∀ b ∈ CY, β (bX a) (bY b) = 0) : β = 0 := by
  refine LinearMap.ext_on hX.span_eq fun x hx => ?_
  obtain ⟨a, ha, rfl⟩ := hx
  refine LinearMap.ext_on hY.span_eq fun y hy => ?_
  obtain ⟨b, hb, rfl⟩ := hy
  simpa using h a ha b hb

theorem bil_coeff (hX : NF D ρX jX CX bX) (hY : NF D ρY jY CY bY) (hV : NF D ρV 0 CV bV)
    (hβ : ∀ (g : G) (x : X) (y : Y), β (ρX g x) (ρY g y) = ρV g (β x y))
    {l : (Fin 4 → ZMod (Nat.card Kˣ)) → (Fin 4 → ZMod (Nat.card Kˣ)) → K}
    (hl : ∀ a ∈ CX, ∀ b ∈ CY, β (bX a) (bY b) = if a + b ∈ CV then l a b • bV (a + b) else 0)
    {a b A B : Fin 4 → ZMod (Nat.card Kˣ)} (ha : a ∈ CX) (hb : b ∈ CY) {γ : Fin 4 → ℤ}
    (hγ : IsD4Root γ)
    (hA : A = a + (2 : ZMod (Nat.card Kˣ)) ^ jX • castW (Nat.card Kˣ) γ)
    (hB : B = b + (2 : ZMod (Nat.card Kˣ)) ^ jY • castW (Nat.card Kˣ) γ)
    (h1 : 2 ^ jX < Nat.card K) (h2 : 2 ^ jY < Nat.card K) (h3 : 2 ^ jX + 2 ^ jY < Nat.card K)
    (h4 : 1 < Nat.card K) (m : ℕ) :
    (if 2 ^ jX = m then (if A ∈ CX then β (bX A) (bY b) else 0) else 0) +
      (if 2 ^ jY = m then (if B ∈ CY then β (bX a) (bY B) else 0) else 0) +
      (if 2 ^ jX + 2 ^ jY = m then (if A ∈ CX ∧ B ∈ CY then β (bX A) (bY B) else 0) else 0) +
      (if 1 = m then -(if a + b ∈ CV ∧ a + b + castW (Nat.card Kˣ) γ ∈ CV then
        l a b • bV (a + b + castW (Nat.card Kˣ) γ) else 0) else 0) = 0 :=
  bil_coeff4 h1 h2 h3 h4 (fun c => bil_key hX hY hV hβ hl ha hb hγ c hA hB) m

end Bil

theorem bil_card_facts {K : Type*} [Field K] [Finite K] [CharP K 2] (hK : 4 ≤ Nat.card K) :
    3 ≤ Nat.card Kˣ ∧ Odd (Nat.card Kˣ) ∧ Nat.card K = Nat.card Kˣ + 1 ∧
      ∃ f : ℕ, Nat.card K = 2 ^ f := by
  have hq : Nat.card K = Nat.card Kˣ + 1 := by
    rw [Nat.card_units]
    omega
  obtain ⟨f, hf⟩ : ∃ f : ℕ, Nat.card K = 2 ^ f := by
    letI : Fintype K := Fintype.ofFinite K
    obtain ⟨n, -, hn⟩ := FiniteField.card K 2
    exact ⟨n, by rw [Nat.card_eq_fintype_card, hn]⟩
  refine ⟨by omega, ?_, hq, f, hf⟩
  have hf2 : 2 ≤ f := by
    by_contra hf2
    have : f ≤ 1 := by omega
    have : 2 ^ f ≤ 2 ^ 1 := Nat.pow_le_pow_right (by norm_num) this
    omega
  obtain ⟨g, rfl⟩ : ∃ g, f = g + 1 := ⟨f - 1, by omega⟩
  have hg : 0 < 2 ^ g := by positivity
  refine ⟨2 ^ g - 1, ?_⟩
  rw [pow_succ] at hf
  omega

theorem bil_pow_card {K : Type*} [Field K] [Finite K] (c : K) : c ^ Nat.card K = c := by
  letI : Fintype K := Fintype.ofFinite K
  rw [Nat.card_eq_fintype_card, FiniteField.pow_card]

section Cases

variable {G : Type*} [Group G] {K : Type*} [Field K] [Finite K] [CharP K 2]
  {D : D4Datum G K} {X Y V : Type*} [AddCommGroup X] [Module K X] [AddCommGroup Y] [Module K Y]
  [AddCommGroup V] [Module K V] {ρX : Representation K G X} {ρY : Representation K G Y}
  {ρV : Representation K G V} {jX jY : ℕ} {CX CY CV : Finset (Fin 4 → ZMod (Nat.card Kˣ))}
  {bX : (Fin 4 → ZMod (Nat.card Kˣ)) → X} {bY : (Fin 4 → ZMod (Nat.card Kˣ)) → Y}
  {bV : (Fin 4 → ZMod (Nat.card Kˣ)) → V} {β : X →ₗ[K] Y →ₗ[K] V}
  (hK : 4 ≤ Nat.card K) (hX : NF D ρX jX CX bX) (hY : NF D ρY jY CY bY) (hV : NF D ρV 0 CV bV)
  (hVt : ∀ a, a ∈ CV ↔ IsNatWt (1 : ZMod (Nat.card Kˣ)) a)
  (hβ : ∀ (g : G) (x : X) (y : Y), β (ρX g x) (ρY g y) = ρV g (β x y))
include hK hX hY hV hVt hβ

theorem bil_eq_zero_jX_zero (hYt : NFType jY CY) (hjY : 2 ^ jY < Nat.card Kˣ) (hjX0 : jX = 0)
    (hjY1 : 1 ≤ jY) : β = 0 := by
  obtain ⟨h3, hodd, hq, f, hf⟩ := bil_card_facts hK
  obtain ⟨l, hl⟩ := bil_exists_l hX hY hV hβ
  refine bil_eq_zero_of_basis hX hY fun a ha b' hb' => ?_
  obtain ⟨b, hb, γ, hγ, hbb'⟩ := bil_reach hodd h3 hYt hb'
  have hsY : 2 ≤ 2 ^ jY := Nat.one_lt_two_pow (by omega)
  subst hjX0
  have hlt1 : 2 ^ 0 < Nat.card K := by rw [pow_zero]; omega
  have hlt2 : 2 ^ jY < Nat.card K := by omega
  have hlt3 : 2 ^ 0 + 2 ^ jY < Nat.card K := by rw [pow_zero]; omega
  have hco := bil_coeff hX hY hV hβ hl ha hb hγ (A := a + (2 : ZMod (Nat.card Kˣ)) ^ 0 •
    castW (Nat.card Kˣ) γ) (B := b') rfl hbb' hlt1 hlt2 hlt3 (by omega) (2 ^ jY)
  have e1 : ¬ (2 ^ 0 = 2 ^ jY) := by rw [pow_zero]; omega
  have e2 : ¬ (2 ^ 0 + 2 ^ jY = 2 ^ jY) := by rw [pow_zero]; omega
  have e3 : ¬ (1 = 2 ^ jY) := by omega
  rw [if_neg e1, if_pos rfl, if_neg e2, if_neg e3, zero_add, add_zero, add_zero, if_pos hb'] at hco
  exact hco

theorem bil_eq_zero_jY_zero (hXt : NFType jX CX) (hjX : 2 ^ jX < Nat.card Kˣ) (hjY0 : jY = 0)
    (hjX1 : 1 ≤ jX) : β = 0 := by
  obtain ⟨h3, hodd, hq, f, hf⟩ := bil_card_facts hK
  obtain ⟨l, hl⟩ := bil_exists_l hX hY hV hβ
  refine bil_eq_zero_of_basis hX hY fun a' ha' b hb => ?_
  obtain ⟨a, ha, γ, hγ, haa'⟩ := bil_reach hodd h3 hXt ha'
  have hsX : 2 ≤ 2 ^ jX := Nat.one_lt_two_pow (by omega)
  subst hjY0
  have hlt1 : 2 ^ jX < Nat.card K := by omega
  have hlt2 : 2 ^ 0 < Nat.card K := by rw [pow_zero]; omega
  have hlt3 : 2 ^ jX + 2 ^ 0 < Nat.card K := by rw [pow_zero]; omega
  have hco := bil_coeff hX hY hV hβ hl ha hb hγ (A := a') (B := b + (2 : ZMod (Nat.card Kˣ)) ^ 0 •
    castW (Nat.card Kˣ) γ) haa' rfl hlt1 hlt2 hlt3 (by omega) (2 ^ jX)
  have e1 : ¬ (2 ^ 0 = 2 ^ jX) := by rw [pow_zero]; omega
  have e2 : ¬ (2 ^ jX + 2 ^ 0 = 2 ^ jX) := by rw [pow_zero]; omega
  have e3 : ¬ (1 = 2 ^ jX) := by omega
  rw [if_pos rfl, if_neg e1, if_neg e2, if_neg e3, add_zero, add_zero, add_zero, if_pos ha'] at hco
  exact hco

theorem bil_eq_zero_of_small (hjX1 : 1 ≤ jX) (hjY1 : 1 ≤ jY) (hjX : 2 ^ jX < Nat.card Kˣ)
    (hjY : 2 ^ jY < Nat.card Kˣ) (hlt : 2 ^ jX + 2 ^ jY < Nat.card K) : β = 0 := by
  obtain ⟨h3, hodd, hq, f, hf⟩ := bil_card_facts hK
  obtain ⟨l, hl⟩ := bil_exists_l hX hY hV hβ
  refine bil_eq_zero_of_basis hX hY fun a ha b hb => ?_
  by_cases hv : a + b ∈ CV
  swap
  · rw [hl a ha b hb, if_neg hv]
  obtain ⟨γ, hγ, hw'⟩ := bil_natWt_add_step ((hVt _).mp hv)
  have hw'CV : a + b + castW (Nat.card Kˣ) γ ∈ CV := (hVt _).mpr hw'
  have hsX : 2 ≤ 2 ^ jX := Nat.one_lt_two_pow (by omega)
  have hsY : 2 ≤ 2 ^ jY := Nat.one_lt_two_pow (by omega)
  have hco := bil_coeff hX hY hV hβ hl ha hb hγ rfl rfl (by omega) (by omega) hlt (by omega) 1
  have e1 : ¬ (2 ^ jX = 1) := by omega
  have e2 : ¬ (2 ^ jY = 1) := by omega
  have e3 : ¬ (2 ^ jX + 2 ^ jY = 1) := by omega
  rw [if_neg e1, if_neg e2, if_neg e3, if_pos rfl, zero_add, zero_add, zero_add,
    if_pos ⟨hv, hw'CV⟩, neg_eq_zero, smul_eq_zero] at hco
  rcases hco with h | h
  · rw [hl a ha b hb, if_pos hv, h, zero_smul]
  · exact absurd h (hV.ne_zero _ hw'CV)

theorem bil_eq_zero_of_half (hXt : NFType jX CX) (hYt : NFType jY CY) (hj : jX = jY)
    (hjX1 : 1 ≤ jX) (hq2 : 2 * 2 ^ jX = Nat.card K) : β = 0 := by
  subst hj
  obtain ⟨h3, hodd, hq, f, hf⟩ := bil_card_facts hK
  obtain ⟨l, hl⟩ := bil_exists_l hX hY hV hβ
  refine bil_eq_zero_of_basis hX hY fun a ha b hb => ?_
  by_cases hv : a + b ∈ CV
  swap
  · rw [hl a ha b hb, if_neg hv]
  obtain ⟨γ, hγ, hAmem, hBnot⟩ := bil_pair_step_out hodd h3 hXt hYt ha hb ((hVt _).mp hv)
  have hsX : 2 ≤ 2 ^ jX := Nat.one_lt_two_pow (by omega)
  have hlt1 : 2 ^ jX < Nat.card K := by omega
  have hco := bil_coeff4 hlt1 hlt1 (by omega : 1 < Nat.card K) (by omega : 1 < Nat.card K)
    (fun c => by
      have h := bil_key hX hY hV hβ hl hAmem hb hγ c
        (A := a) (B := b + (2 : ZMod (Nat.card Kˣ)) ^ jX • castW (Nat.card Kˣ) γ)
        (sub_add_cancel a _).symm rfl
      have hpow : c ^ (2 ^ jX + 2 ^ jX) = c ^ 1 := by
        rw [show 2 ^ jX + 2 ^ jX = Nat.card K by omega, bil_pow_card, pow_one]
      rw [hpow] at h
      exact h) (2 ^ jX)
  have e : ¬ (1 = 2 ^ jX) := by omega
  rw [if_pos rfl, if_pos rfl, if_neg e, if_neg e, add_zero, add_zero, if_pos ha,
    if_neg hBnot, add_zero] at hco
  exact hco

theorem bil_untwisted_sq (hjX : jX = 0) (hjY : jY = 0) {a b : Fin 4 → ZMod (Nat.card Kˣ)}
    (ha : a ∈ CX) (hb : b ∈ CY) {γ : Fin 4 → ℤ} (hγ : IsD4Root γ)
    (hA : a + castW (Nat.card Kˣ) γ ∈ CX) (hB : b + castW (Nat.card Kˣ) γ ∈ CY) :
    β (bX (a + castW (Nat.card Kˣ) γ)) (bY (b + castW (Nat.card Kˣ) γ)) = 0 := by
  subst hjX
  subst hjY
  obtain ⟨l, hl⟩ := bil_exists_l hX hY hV hβ
  have hlt1 : 2 ^ 0 < Nat.card K := by rw [pow_zero]; omega
  have hlt3 : 2 ^ 0 + 2 ^ 0 < Nat.card K := by rw [pow_zero]; omega
  have hco := bil_coeff hX hY hV hβ hl ha hb hγ (A := a + castW (Nat.card Kˣ) γ)
    (B := b + castW (Nat.card Kˣ) γ) (by rw [pow_zero, one_smul]) (by rw [pow_zero, one_smul])
    hlt1 hlt1 hlt3 (by omega) 2
  have e1 : ¬ (2 ^ 0 = 2) := by norm_num
  have e3 : 2 ^ 0 + 2 ^ 0 = 2 := by norm_num
  have e4 : ¬ (1 = 2) := by norm_num
  have hAB : a + castW (Nat.card Kˣ) γ ∈ CX ∧ b + castW (Nat.card Kˣ) γ ∈ CY := ⟨hA, hB⟩
  rw [if_neg e1, if_neg e1, if_pos e3, if_neg e4, zero_add, zero_add, add_zero,
    if_pos hAB] at hco
  exact hco

theorem bil_untwisted_eq (hjX : jX = 0) (hjY : jY = 0)
    {l : (Fin 4 → ZMod (Nat.card Kˣ)) → (Fin 4 → ZMod (Nat.card Kˣ)) → K}
    (hl : ∀ a ∈ CX, ∀ b ∈ CY, β (bX a) (bY b) = if a + b ∈ CV then l a b • bV (a + b) else 0)
    {a b : Fin 4 → ZMod (Nat.card Kˣ)} (ha : a ∈ CX) (hb : b ∈ CY) {γ : Fin 4 → ℤ}
    (hγ : IsD4Root γ) (hab : a + b ∈ CV) (hab' : a + b + castW (Nat.card Kˣ) γ ∈ CV) :
    (if a + castW (Nat.card Kˣ) γ ∈ CX then l (a + castW (Nat.card Kˣ) γ) b else 0) +
      (if b + castW (Nat.card Kˣ) γ ∈ CY then l a (b + castW (Nat.card Kˣ) γ) else 0) =
    l a b := by
  subst hjX
  subst hjY
  have hlt1 : 2 ^ 0 < Nat.card K := by rw [pow_zero]; omega
  have hlt3 : 2 ^ 0 + 2 ^ 0 < Nat.card K := by rw [pow_zero]; omega
  have hco := bil_coeff hX hY hV hβ hl ha hb hγ (A := a + castW (Nat.card Kˣ) γ)
    (B := b + castW (Nat.card Kˣ) γ) (by rw [pow_zero, one_smul]) (by rw [pow_zero, one_smul])
    hlt1 hlt1 hlt3 (by omega) 1
  have e1 : 2 ^ 0 = 1 := by norm_num
  have e3 : ¬ (2 ^ 0 + 2 ^ 0 = 1) := by norm_num
  have e5 : (1 : ℕ) = 1 := rfl
  have hABV : a + b ∈ CV ∧ a + b + castW (Nat.card Kˣ) γ ∈ CV := ⟨hab, hab'⟩
  rw [if_pos e1, if_pos e1, if_neg e3, if_pos e5, add_zero, if_pos hABV] at hco
  have hw0 : bV (a + b + castW (Nat.card Kˣ) γ) ≠ 0 := hV.ne_zero _ hab'
  have hT1 : (if a + castW (Nat.card Kˣ) γ ∈ CX then
      β (bX (a + castW (Nat.card Kˣ) γ)) (bY b) else 0) =
      (if a + castW (Nat.card Kˣ) γ ∈ CX then l (a + castW (Nat.card Kˣ) γ) b else 0) •
        bV (a + b + castW (Nat.card Kˣ) γ) := by
    by_cases hA : a + castW (Nat.card Kˣ) γ ∈ CX
    · rw [if_pos hA, if_pos hA, hl _ hA b hb, add_right_comm, if_pos hab']
    · rw [if_neg hA, if_neg hA, zero_smul]
  have hT2 : (if b + castW (Nat.card Kˣ) γ ∈ CY then
      β (bX a) (bY (b + castW (Nat.card Kˣ) γ)) else 0) =
      (if b + castW (Nat.card Kˣ) γ ∈ CY then l a (b + castW (Nat.card Kˣ) γ) else 0) •
        bV (a + b + castW (Nat.card Kˣ) γ) := by
    by_cases hB : b + castW (Nat.card Kˣ) γ ∈ CY
    · rw [if_pos hB, if_pos hB, hl a ha _ hB, ← add_assoc, if_pos hab']
    · rw [if_neg hB, if_neg hB, zero_smul]
  rw [hT1, hT2] at hco
  generalize (if a + castW (Nat.card Kˣ) γ ∈ CX then l (a + castW (Nat.card Kˣ) γ) b else 0) = x
    at hco ⊢
  generalize (if b + castW (Nat.card Kˣ) γ ∈ CY then l a (b + castW (Nat.card Kˣ) γ) else 0) = y
    at hco ⊢
  have h5 : (x + y - l a b) • bV (a + b + castW (Nat.card Kˣ) γ) = 0 := by
    rw [sub_smul, add_smul, sub_eq_add_neg]
    exact hco
  rcases smul_eq_zero.mp h5 with h | h
  · exact sub_eq_zero.mp h
  · exact absurd h hw0

theorem bil_untwisted (hXt : NFType jX CX) (hYt : NFType jY CY) (hjX : jX = 0) (hjY : jY = 0)
    (hβ0 : β ≠ 0) :
    ∃ (b₀ : ZMod (Nat.card Kˣ)) (e : ℕ), 2 * b₀ = 1 ∧ e < 2 ∧ (∀ a, a ∈ CX ↔ IsSpinWt b₀ e a) ∧
      (∀ a, a ∈ CY ↔ IsSpinWt b₀ (1 - e) a) ∧ ∃ lam : K, lam ≠ 0 ∧ ∀ a ∈ CX, ∀ b ∈ CY,
        β (bX a) (bY b) = if a + b ∈ CV then lam • bV (a + b) else 0 := by
  obtain ⟨h3, hodd, hq, f, hf⟩ := bil_card_facts hK
  haveI := bil_nontrivial h3
  obtain ⟨l, hl⟩ := bil_exists_l hX hY hV hβ
  obtain ⟨x₀, hx₀, y₀, hy₀, hne⟩ : ∃ a ∈ CX, ∃ b ∈ CY, β (bX a) (bY b) ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact hβ0 (bil_eq_zero_of_basis hX hY hcon)
  have hxy₀ : x₀ + y₀ ∈ CV := by
    by_contra hv
    apply hne
    rw [hl x₀ hx₀ y₀ hy₀, if_neg hv]
  have hl0 : l x₀ y₀ ≠ 0 := by
    intro h
    apply hne
    rw [hl x₀ hx₀ y₀ hy₀, if_pos hxy₀, h, zero_smul]
  have hnat : IsNatWt (1 : ZMod (Nat.card Kˣ)) (x₀ + y₀) := (hVt _).mp hxy₀
  have hE : ∀ a ∈ CX, ∀ b ∈ CY, ∀ γ : Fin 4 → ℤ, IsD4Root γ → a + b ∈ CV →
      a + b + castW (Nat.card Kˣ) γ ∈ CV →
      (if a + castW (Nat.card Kˣ) γ ∈ CX then l (a + castW (Nat.card Kˣ) γ) b else 0) +
        (if b + castW (Nat.card Kˣ) γ ∈ CY then l a (b + castW (Nat.card Kˣ) γ) else 0) =
      l a b := fun a ha b hb γ hγ hab hab' =>
    bil_untwisted_eq hK hX hY hV hVt hβ hjX hjY hl ha hb hγ hab hab'
  have hsq := fun {a b : Fin 4 → ZMod (Nat.card Kˣ)} (ha : a ∈ CX) (hb : b ∈ CY)
    {γ : Fin 4 → ℤ} (hγ : IsD4Root γ) (hA : a + castW (Nat.card Kˣ) γ ∈ CX)
    (hB : b + castW (Nat.card Kˣ) γ ∈ CY) =>
    bil_untwisted_sq hK hX hY hV hVt hβ hjX hjY ha hb hγ hA hB
  subst hjX
  subst hjY
  rcases hXt with hXn | ⟨b₀, e, hb₀, he, hXs⟩ <;>
    rcases hYt with hYn | ⟨b₁, e', hb₁, he', hYs⟩
  · exfalso
    simp only [pow_zero] at hXn hYn
    obtain ⟨γ, hγ, hx1, hy1, -⟩ := bil_nat_pair_step hodd h3 one_ne_zero one_ne_zero hXn hYn hx₀ hy₀
      hnat
    rw [one_smul] at hx1 hy1
    have h := hsq hx1 hy1 hγ (by rwa [sub_add_cancel]) (by rwa [sub_add_cancel])
    rw [sub_add_cancel, sub_add_cancel] at h
    exact hne h
  · exfalso
    rw [pow_zero] at hb₁
    have hu : IsUnit (2 * b₁) := by rw [hb₁]; exact isUnit_one
    exact bil_not_natWt_add_spin (bil_ne_zero_of_isUnit_two_mul h3 hu) ((hXn x₀).mp hx₀)
      ((hYs y₀).mp hy₀) hnat
  · exfalso
    rw [pow_zero] at hb₀
    have hu : IsUnit (2 * b₀) := by rw [hb₀]; exact isUnit_one
    exact bil_not_natWt_spin_add (bil_ne_zero_of_isUnit_two_mul h3 hu) ((hXs x₀).mp hx₀)
      ((hYn y₀).mp hy₀) hnat
  · rw [pow_zero] at hb₀ hb₁
    obtain ⟨hbb, hee⟩ := bil_spin_spin_parity hodd h3 hb₀ hb₁ he he' ((hXs x₀).mp hx₀)
      ((hYs y₀).mp hy₀) hnat
    subst hbb
    subst hee
    refine ⟨b₁, e, hb₀, he, hXs, hYs, l x₀ y₀, hl0, ?_⟩
    intro a ha b hb
    rw [hl a ha b hb]
    by_cases hv : a + b ∈ CV
    · rw [if_pos hv, if_pos hv]
      congr 1
      exact bil_conn hodd h3 hb₀ (by omega) hXs hYs hVt l hE ha hb hv hx₀ hy₀ hxy₀
    · rw [if_neg hv, if_neg hv]

end Cases

theorem bil_of_nf {G : Type*} [Group G] {K : Type*} [Field K] [Finite K] [CharP K 2]
    (hK : 4 ≤ Nat.card K) (D : D4Datum G K)
    {X Y V : Type*} [AddCommGroup X] [Module K X] [AddCommGroup Y] [Module K Y]
    [AddCommGroup V] [Module K V] {ρX : Representation K G X} {ρY : Representation K G Y}
    {ρV : Representation K G V} {jX jY : ℕ} {CX CY CV : Finset (Fin 4 → ZMod (Nat.card Kˣ))}
    {bX : (Fin 4 → ZMod (Nat.card Kˣ)) → X} {bY : (Fin 4 → ZMod (Nat.card Kˣ)) → Y}
    {bV : (Fin 4 → ZMod (Nat.card Kˣ)) → V}
    (hX : NF D ρX jX CX bX) (hXt : NFType jX CX) (hjX : 2 ^ jX < Nat.card Kˣ)
    (hY : NF D ρY jY CY bY) (hYt : NFType jY CY) (hjY : 2 ^ jY < Nat.card Kˣ)
    (hV : NF D ρV 0 CV bV) (hVt : ∀ a, a ∈ CV ↔ IsNatWt (1 : ZMod (Nat.card Kˣ)) a)
    (β : X →ₗ[K] Y →ₗ[K] V) (hβ : ∀ (g : G) (x : X) (y : Y), β (ρX g x) (ρY g y) = ρV g (β x y))
    (hβ0 : β ≠ 0) :
    jX = 0 ∧ jY = 0 ∧ ∃ (b₀ : ZMod (Nat.card Kˣ)) (e : ℕ), 2 * b₀ = 1 ∧ e < 2 ∧
      (∀ a, a ∈ CX ↔ IsSpinWt b₀ e a) ∧ (∀ a, a ∈ CY ↔ IsSpinWt b₀ (1 - e) a) ∧
      ∃ l : K, l ≠ 0 ∧ ∀ a ∈ CX, ∀ b ∈ CY,
        β (bX a) (bY b) = if a + b ∈ CV then l • bV (a + b) else 0 := by
  obtain ⟨h3, hodd, hq, f, hf⟩ := bil_card_facts hK
  have hjXf : jX < f := by
    have h : 2 ^ jX < 2 ^ f := by omega
    exact (Nat.pow_lt_pow_iff_right (by norm_num)).mp h
  have hjYf : jY < f := by
    have h : 2 ^ jY < 2 ^ f := by omega
    exact (Nat.pow_lt_pow_iff_right (by norm_num)).mp h
  have h2X : 2 * 2 ^ jX ≤ Nat.card K := by
    rw [hf, ← pow_succ']
    exact Nat.pow_le_pow_right (by norm_num) hjXf
  have h2Y : 2 * 2 ^ jY ≤ Nat.card K := by
    rw [hf, ← pow_succ']
    exact Nat.pow_le_pow_right (by norm_num) hjYf
  by_cases hX0 : jX = 0
  · by_cases hY0 : jY = 0
    · exact ⟨hX0, hY0, bil_untwisted hK hX hY hV hVt hβ hXt hYt hX0 hY0 hβ0⟩
    · exact absurd (bil_eq_zero_jX_zero hK hX hY hV hVt hβ hYt hjY hX0 (Nat.one_le_iff_ne_zero.mpr
        hY0)) hβ0
  · by_cases hY0 : jY = 0
    · exact absurd (bil_eq_zero_jY_zero hK hX hY hV hVt hβ hXt hjX hY0 (Nat.one_le_iff_ne_zero.mpr
        hX0)) hβ0
    · refine absurd ?_ hβ0
      have hX1 : 1 ≤ jX := Nat.one_le_iff_ne_zero.mpr hX0
      have hY1 : 1 ≤ jY := Nat.one_le_iff_ne_zero.mpr hY0
      by_cases hlt : 2 ^ jX + 2 ^ jY < Nat.card K
      · exact bil_eq_zero_of_small hK hX hY hV hVt hβ hX1 hY1 hjX hjY hlt
      · have hje : 2 ^ jX = 2 ^ jY := by omega
        have hj : jX = jY := Nat.pow_right_injective (le_refl 2) hje
        exact bil_eq_zero_of_half hK hX hY hV hVt hβ hXt hYt hj hX1 (by omega)

end CFSG.RankThree.GF2n.Stroth80.Tri

end
