module

public import CFSG.Quasithin.H13.NQS1312K

public section

namespace CFSG.Quasithin.H13.U3.NLine

open Subgroup

section CommMap

variable {W : Type} [CommGroup W]

@[expose] def commMap (σ : MulAut W) : W →* W where
  toFun w := σ w * w⁻¹
  map_one' := by simp
  map_mul' a b := by
    simp only [map_mul, mul_inv]
    exact mul_mul_mul_comm _ _ _ _

theorem commMap_apply (σ : MulAut W) (w : W) : commMap σ w = σ w * w⁻¹ := rfl

theorem commMap_mul_apply (σ τ : MulAut W) (w : W) :
    commMap (σ * τ) w = σ (commMap τ w) * commMap σ w := by
  simp only [commMap_apply, MulAut.mul_apply, map_mul, map_inv]
  group

theorem commMap_inv_apply (σ : MulAut W) (w : W) :
    commMap σ⁻¹ w = σ⁻¹ (commMap σ w)⁻¹ := by
  simp only [commMap_apply, mul_inv_rev, inv_inv, map_mul, map_inv, MulAut.inv_apply_self]

theorem commMap_conj_apply (σ τ : MulAut W) (w : W) :
    commMap (τ * σ * τ⁻¹) w = τ (commMap σ (τ⁻¹ w)) := by
  simp only [commMap_apply, MulAut.mul_apply, map_mul, map_inv, MulAut.apply_inv_self]

end CommMap

section Three

variable {W : Type} [CommGroup W]

theorem card_eq_of_three (hW : ∀ w : W, w * w = 1) (σ τ : MulAut W) (X : Subgroup W)
    (hσX : ∀ x ∈ X, σ x ∈ X) (hτX : ∀ x ∈ X, τ x ∈ X) (hστ : ∀ w, τ (σ w) = σ (τ w))
    (hσ3 : ∀ w, σ (σ (σ w)) = w) (hτ3 : ∀ w, τ (τ (τ w)) = w)
    (hX : ∀ x ∈ X, x * σ x * σ (σ x) = 1) :
    Nat.card X = Nat.card {x : W // x ∈ X ∧ τ x = x} * Nat.card {x : W // x ∈ X ∧ σ (τ x) = x} *
      Nat.card {x : W // x ∈ X ∧ σ (σ (τ x)) = x} := by
  classical
  have hX' : ∀ x ∈ X, x * σ (σ x) * σ x = 1 := fun x hx => by
    rw [mul_right_comm]; exact hX x hx
  have hcube : ∀ w : W, w * w * w = w := fun w => by rw [hW, one_mul]
  have hσ4 : ∀ w, σ (σ (σ (σ w))) = σ w := fun w => by rw [hσ3]
  let P₀ : W → W := fun x => x * τ x * τ (τ x)
  let P₁ : W → W := fun x => x * σ (τ x) * σ (σ (τ (τ x)))
  let P₂ : W → W := fun x => x * σ (σ (τ x)) * σ (τ (τ x))
  have hP₀X : ∀ x ∈ X, P₀ x ∈ X := fun x hx =>
    X.mul_mem (X.mul_mem hx (hτX x hx)) (hτX _ (hτX x hx))
  have hP₁X : ∀ x ∈ X, P₁ x ∈ X := fun x hx =>
    X.mul_mem (X.mul_mem hx (hσX _ (hτX x hx)))
      (hσX _ (hσX _ (hτX _ (hτX x hx))))
  have hP₂X : ∀ x ∈ X, P₂ x ∈ X := fun x hx =>
    X.mul_mem (X.mul_mem hx (hσX _ (hσX _ (hτX x hx)))) (hσX _ (hτX _ (hτX x hx)))
  have hP₀f : ∀ x, τ (P₀ x) = P₀ x := fun x => by
    simp only [P₀, map_mul, hτ3]
    ac_rfl
  have hP₁f : ∀ x, σ (τ (P₁ x)) = P₁ x := fun x => by
    simp only [P₁, map_mul, hστ, hσ3, hτ3]
    ac_rfl
  have hP₂f : ∀ x, σ (σ (τ (P₂ x))) = P₂ x := fun x => by
    simp only [P₂, map_mul, hστ, hσ3, hτ3]
    ac_rfl
  have hP₀m : ∀ a b, P₀ (a * b) = P₀ a * P₀ b := fun a b => by
    simp only [P₀, map_mul]; ac_rfl
  have hP₁m : ∀ a b, P₁ (a * b) = P₁ a * P₁ b := fun a b => by
    simp only [P₁, map_mul]; ac_rfl
  have hP₂m : ∀ a b, P₂ (a * b) = P₂ a * P₂ b := fun a b => by
    simp only [P₂, map_mul]; ac_rfl
  have hdec : ∀ x ∈ X, P₀ x * P₁ x * P₂ x = x := by
    intro x hx
    have h1 := hX (τ x) (hτX x hx)
    have h2 := hX' (τ (τ x)) (hτX _ (hτX x hx))
    calc P₀ x * P₁ x * P₂ x = x * x * x * (τ x * σ (τ x) * σ (σ (τ x))) *
          (τ (τ x) * σ (σ (τ (τ x))) * σ (τ (τ x))) := by simp only [P₀, P₁, P₂]; ac_rfl
      _ = x := by rw [h1, h2, mul_one, mul_one, hcube]
  have hfix₀ : ∀ a ∈ X, τ a = a → P₀ a = a ∧ P₁ a = 1 ∧ P₂ a = 1 := by
    intro a ha h
    refine ⟨?_, ?_, ?_⟩
    · simp only [P₀, h, hcube]
    · simp only [P₁, h]; exact hX a ha
    · simp only [P₂, h]; exact hX' a ha
  have hfix₁ : ∀ a ∈ X, σ (τ a) = a → P₀ a = 1 ∧ P₁ a = a ∧ P₂ a = 1 := by
    intro a ha h
    have h' : τ a = σ (σ a) := by
      calc τ a = σ (σ (σ (τ a))) := (hσ3 _).symm
        _ = σ (σ a) := by rw [h]
    refine ⟨?_, ?_, ?_⟩
    · simp only [P₀, h', hστ, hσ4]; exact hX' a ha
    · simp only [P₁, h', hστ, hσ3, hcube]
    · simp only [P₂, h', hστ, hσ3]
      exact hX a ha
  have hfix₂ : ∀ a ∈ X, σ (σ (τ a)) = a → P₀ a = 1 ∧ P₁ a = 1 ∧ P₂ a = a := by
    intro a ha h
    have h' : τ a = σ a := by
      calc τ a = σ (σ (σ (τ a))) := (hσ3 _).symm
        _ = σ a := by rw [h]
    refine ⟨?_, ?_, ?_⟩
    · simp only [P₀, h', hστ]; exact hX a ha
    · simp only [P₁, h', hστ, hσ3]; exact hX' a ha
    · simp only [P₂, h', hστ, hσ3, hcube]
  let e : ({x : W // x ∈ X ∧ τ x = x} × {x : W // x ∈ X ∧ σ (τ x) = x} ×
      {x : W // x ∈ X ∧ σ (σ (τ x)) = x}) ≃ X :=
    { toFun := fun p => ⟨p.1.1 * p.2.1.1 * p.2.2.1,
        X.mul_mem (X.mul_mem p.1.2.1 p.2.1.2.1) p.2.2.2.1⟩
      invFun := fun x => (⟨P₀ x, hP₀X x x.2, hP₀f x⟩, ⟨P₁ x, hP₁X x x.2, hP₁f x⟩,
        ⟨P₂ x, hP₂X x x.2, hP₂f x⟩)
      left_inv := by
        rintro ⟨⟨a, haX, ha⟩, ⟨b, hbX, hb⟩, ⟨c, hcX, hc⟩⟩
        obtain ⟨a0, a1, a2⟩ := hfix₀ a haX ha
        obtain ⟨b0, b1, b2⟩ := hfix₁ b hbX hb
        obtain ⟨c0, c1, c2⟩ := hfix₂ c hcX hc
        simp only [Prod.mk.injEq, Subtype.mk.injEq]
        refine ⟨?_, ?_, ?_⟩
        · rw [hP₀m, hP₀m, a0, b0, c0, mul_one, mul_one]
        · rw [hP₁m, hP₁m, a1, b1, c1, one_mul, mul_one]
        · rw [hP₂m, hP₂m, a2, b2, c2, one_mul, one_mul]
      right_inv := fun x => Subtype.ext (hdec x x.2) }
  rw [← Nat.card_congr e, Nat.card_prod, Nat.card_prod, mul_assoc]

end Three

theorem eq_one_of_card_commMap_le_four {Γ W : Type} [Group Γ] [CommGroup W] [Finite W]
    (hW : ∀ w : W, w * w = 1) (ρ : Γ →* MulAut W) {k y : Γ} (hy3 : y ^ 3 = 1)
    (hzk : k * y * k⁻¹ * y⁻¹ * k = k * (k * y * k⁻¹ * y⁻¹))
    (hzy : k * y * k⁻¹ * y⁻¹ * y = y * (k * y * k⁻¹ * y⁻¹))
    (hz3 : (k * y * k⁻¹ * y⁻¹) ^ 3 = 1)
    (hk : Nat.card (Set.range fun w : W => ρ k w * w⁻¹) ≤ 4) :
    ρ (k * y * k⁻¹ * y⁻¹) = 1 := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set z := k * y * k⁻¹ * y⁻¹ with hz
  set σ := ρ z with hσ
  set τ := ρ y with hτ
  set κ := ρ k with hκ
  have hσ3 : ∀ w, σ (σ (σ w)) = w := fun w => by
    have h : (σ ^ 3) w = w := by rw [hσ, ← map_pow, hz3, map_one, MulAut.one_apply]
    rwa [pow_three, MulAut.mul_apply, MulAut.mul_apply] at h
  have hτ3 : ∀ w, τ (τ (τ w)) = w := fun w => by
    have h : (τ ^ 3) w = w := by rw [hτ, ← map_pow, hy3, map_one, MulAut.one_apply]
    rwa [pow_three, MulAut.mul_apply, MulAut.mul_apply] at h
  have hστ : ∀ w, τ (σ w) = σ (τ w) := fun w => by
    have h := congrArg (fun g => ρ g w) hzy
    simp only [map_mul, MulAut.mul_apply] at h
    exact h.symm
  have hκσ : ∀ w, κ (σ w) = σ (κ w) := fun w => by
    have h := congrArg (fun g => ρ g w) hzk
    simp only [map_mul, MulAut.mul_apply] at h
    exact h.symm
  have hky : k * y = z * y * k := by rw [hz]; group
  have hκτ : ∀ w, κ (τ w) = σ (τ (κ w)) := fun w => by
    have h := congrArg (fun g => ρ g w) hky
    simp only [map_mul, MulAut.mul_apply] at h
    exact h
  set X := (commMap σ).range with hXdef
  have hmemX : ∀ w, commMap σ w ∈ X := fun w => ⟨w, rfl⟩
  have hcomm : ∀ (φ : MulAut W), (∀ w, φ (σ w) = σ (φ w)) → ∀ x ∈ X, φ x ∈ X := by
    rintro φ hφ _ ⟨w, rfl⟩
    refine ⟨φ w, ?_⟩
    simp only [commMap_apply, map_mul, map_inv, hφ]
  have hσX : ∀ x ∈ X, σ x ∈ X := hcomm σ fun _ => rfl
  have hτX : ∀ x ∈ X, τ x ∈ X := hcomm τ hστ
  have hκX : ∀ x ∈ X, κ x ∈ X := hcomm κ hκσ
  have h1σ : ∀ x ∈ X, x * σ x * σ (σ x) = 1 := by
    rintro _ ⟨w, rfl⟩
    simp only [commMap_apply, map_mul, map_inv, hσ3]
    calc σ w * w⁻¹ * (σ (σ w) * (σ w)⁻¹) * (w * (σ (σ w))⁻¹) =
        (σ w * (σ w)⁻¹) * (w⁻¹ * w) * (σ (σ w) * (σ (σ w))⁻¹) := by ac_rfl
      _ = 1 := by simp
  have hdecomp : ∀ w, commMap σ w = κ (τ (κ⁻¹ (commMap κ (τ⁻¹ w))⁻¹)) * commMap κ w := by
    intro w
    have hσeq : σ = κ * (τ * κ⁻¹ * τ⁻¹) := by
      rw [hσ, hκ, hτ, ← map_inv, ← map_inv, ← map_mul, ← map_mul, ← map_mul, hz]
      congr 1
      group
    rw [hσeq, commMap_mul_apply, commMap_conj_apply, commMap_inv_apply]
  set A := Set.range (commMap κ) with hA
  have hA4 : Nat.card A ≤ 4 := hk
  let Φ : ↥A × ↥A → W := fun p => κ (τ (κ⁻¹ ((p.1 : W))⁻¹)) * p.2
  have hsub : (X : Set W) ⊆ Set.range Φ := by
    rintro _ ⟨w, rfl⟩
    exact ⟨(⟨commMap κ (τ⁻¹ w), ⟨_, rfl⟩⟩, ⟨commMap κ w, ⟨_, rfl⟩⟩), (hdecomp w).symm⟩
  have hcard16 : Nat.card X ≤ 16 := by
    calc Nat.card X = Nat.card (X : Set W) := rfl
      _ ≤ Nat.card (Set.range Φ) := Nat.card_mono (Set.toFinite _) hsub
      _ ≤ Nat.card (↥A × ↥A) :=
        Nat.card_le_card_of_surjective (Set.rangeFactorization Φ) Set.rangeFactorization_surjective
      _ = Nat.card A * Nat.card A := Nat.card_prod _ _
      _ ≤ 4 * 4 := Nat.mul_le_mul hA4 hA4
      _ = 16 := by norm_num
  have hmod3 : Nat.card X % 3 = 1 := by
    let φ : Function.End ↥X := fun x => ⟨σ x, hσX x x.2⟩
    have hφ3 : φ ^ 3 = 1 := by
      funext x
      apply Subtype.ext
      show σ (σ (σ x)) = x
      exact hσ3 x
    have : Fintype ↥X := Fintype.ofFinite _
    have hcong := Equiv.Perm.card_fixedPoints_modEq (p := 3) (n := 1) (f := φ)
      (by simpa using hφ3)
    have hfix : ∀ x : ↥X, φ x = x → x = 1 := by
      intro x hx
      have h1 : σ x = x := congrArg Subtype.val hx
      have h2 := h1σ x x.2
      rw [h1, h1, hW, one_mul] at h2
      exact Subtype.ext h2
    have hfp : Nat.card (Function.fixedPoints φ) = 1 := by
      rw [Nat.card_eq_one_iff_unique]
      refine ⟨⟨fun a b => Subtype.ext ((hfix a a.2).trans (hfix b b.2).symm)⟩, ⟨⟨1, ?_⟩⟩⟩
      show φ 1 = 1
      apply Subtype.ext
      show σ 1 = 1
      exact map_one σ
    have hcong' : Nat.card ↥X ≡ Nat.card (Function.fixedPoints φ) [MOD 3] := by
      convert hcong using 1 <;> exact Nat.card_eq_fintype_card
    rw [hfp] at hcong'
    exact hcong'
  have hdec := card_eq_of_three hW σ τ X hσX hτX hστ hσ3 hτ3 h1σ
  have hκ01 : Nat.card {x : W // x ∈ X ∧ τ x = x} ≤
      Nat.card {x : W // x ∈ X ∧ σ (τ x) = x} :=
    Nat.card_le_card_of_injective (fun a => ⟨κ a, hκX a a.2.1, by rw [← hκτ, a.2.2]⟩)
      fun a b h => Subtype.ext (κ.injective (congrArg Subtype.val h))
  have hκ12 : Nat.card {x : W // x ∈ X ∧ σ (τ x) = x} ≤
      Nat.card {x : W // x ∈ X ∧ σ (σ (τ x)) = x} :=
    Nat.card_le_card_of_injective (fun a => ⟨κ a, hκX a a.2.1, by
        rw [← hκτ, ← hκσ, a.2.2]⟩)
      fun a b h => Subtype.ext (κ.injective (congrArg Subtype.val h))
  have hκ20 : Nat.card {x : W // x ∈ X ∧ σ (σ (τ x)) = x} ≤
      Nat.card {x : W // x ∈ X ∧ τ x = x} :=
    Nat.card_le_card_of_injective (fun a => ⟨κ a, hκX a a.2.1, by
        have h := hκτ a
        calc τ (κ a) = σ (σ (σ (τ (κ a)))) := (hσ3 _).symm
          _ = σ (σ (κ (τ a))) := by rw [← h]
          _ = κ (σ (σ (τ a))) := by rw [hκσ, hκσ]
          _ = κ a := by rw [a.2.2]⟩)
      fun a b h => Subtype.ext (κ.injective (congrArg Subtype.val h))
  set c := Nat.card {x : W // x ∈ X ∧ τ x = x}
  have hc : Nat.card X = c * c * c := by
    rw [hdec]
    have h1 : Nat.card {x : W // x ∈ X ∧ σ (τ x) = x} = c := by omega
    have h2 : Nat.card {x : W // x ∈ X ∧ σ (σ (τ x)) = x} = c := by omega
    rw [h1, h2]
  have hc1 : c = 1 := by
    rw [hc] at hcard16 hmod3
    rcases Nat.lt_or_ge c 3 with h | h
    · interval_cases c <;> omega
    · have : 27 ≤ c * c * c := by
        calc 27 = 3 * 3 * 3 := by norm_num
          _ ≤ c * c * c := Nat.mul_le_mul (Nat.mul_le_mul h h) h
      omega
  have hX1 : X = ⊥ := by
    rw [← Subgroup.card_eq_one, hc, hc1]
  ext w
  have h := hmemX w
  rw [hX1, Subgroup.mem_bot, commMap_apply, mul_inv_eq_one] at h
  rw [h, MulAut.one_apply]

@[expose] noncomputable def jw (w : List (Fin 5)) : ↥J6 := ⟨rho6 (wordElem w), ⟨wordElem w, rfl⟩⟩

theorem jw_append (w w' : List (Fin 5)) : jw (w ++ w') = jw w * jw w' := by
  apply Subtype.ext
  simp only [jw, Subgroup.coe_mul, wordElem, List.map_append, List.prod_append, map_mul]

theorem jw_eq_jw {w w' : List (Fin 5)} (h : wordMat w = wordMat w') : jw w = jw w' := by
  apply Subtype.ext
  apply Units.ext
  show ((rho6 (wordElem w) : GL (Fin 6) (ZMod 2)) : Matrix (Fin 6) (Fin 6) (ZMod 2)) =
    ((rho6 (wordElem w') : GL (Fin 6) (ZMod 2)) : Matrix (Fin 6) (Fin 6) (ZMod 2))
  rw [coe_rho6_wordElem, coe_rho6_wordElem, h]

theorem jw_nil : jw [] = 1 := by
  apply Subtype.ext
  simp [jw, wordElem]

theorem jw_inv {w w' : List (Fin 5)} (h : wordMat (w ++ w') = wordMat []) : (jw w)⁻¹ = jw w' := by
  have h1 : jw w * jw w' = 1 := by rw [← jw_append, jw_eq_jw h, jw_nil]
  exact (eq_inv_of_mul_eq_one_right h1).symm

@[expose] def yW : List (Fin 5) := [1, 4, 3, 1, 4]

@[expose] def yiW : List (Fin 5) := [0, 4, 3, 2, 0, 4]

@[expose] def kiW : List (Fin 5) := [3, 3, 1]

@[expose] def zW : List (Fin 5) := [0, 3, 0] ++ yW ++ kiW ++ yiW

@[expose] def ziW : List (Fin 5) := [4, 3, 4, 3, 1, 4, 0]

theorem wordMat_data :
    wordMat (yW ++ yiW) = wordMat [] ∧ wordMat ([0, 3, 0] ++ kiW) = wordMat [] ∧
      wordMat (zW ++ ziW) = wordMat [] ∧ wordMat (yW ++ yW ++ yW) = wordMat [] ∧
      wordMat (zW ++ [0, 3, 0]) = wordMat ([0, 3, 0] ++ zW) ∧
      wordMat (zW ++ yW) = wordMat (yW ++ zW) ∧ wordMat (zW ++ zW ++ zW) = wordMat [] ∧
      wordMat ([3] ++ [3, 3]) = wordMat [] ∧ wordMat ([0, 0] ++ [0, 0]) = wordMat [] ∧
      wordMat ([3, 3] ++ [3]) = wordMat [] ∧ wordMat ([2] ++ [2]) = wordMat [] ∧
      wordMat [0, 3, 0] = wordMat ([3] ++ ziW ++ [3, 3] ++ ([0, 0] ++ ziW ++ [0, 0]) ++
        ([3, 3] ++ ziW ++ [3]) ++ ([2] ++ ziW ++ [2])) := by
  decide +kernel

@[expose] noncomputable def kJ : ↥J6 := jw [0, 3, 0]

@[expose] noncomputable def yJ : ↥J6 := jw yW

theorem zJ_eq : kJ * yJ * kJ⁻¹ * yJ⁻¹ = jw zW := by
  rw [kJ, yJ, jw_inv wordMat_data.2.1, jw_inv wordMat_data.1, zW, jw_append, jw_append,
    jw_append]

theorem yJ_pow_three : yJ ^ 3 = 1 := by
  rw [pow_three', yJ, ← jw_append, ← jw_append, jw_eq_jw wordMat_data.2.2.2.1, jw_nil]

theorem zJ_mul_kJ : kJ * yJ * kJ⁻¹ * yJ⁻¹ * kJ = kJ * (kJ * yJ * kJ⁻¹ * yJ⁻¹) := by
  rw [zJ_eq, kJ, ← jw_append, ← jw_append, jw_eq_jw wordMat_data.2.2.2.2.1]

theorem zJ_mul_yJ : kJ * yJ * kJ⁻¹ * yJ⁻¹ * yJ = yJ * (kJ * yJ * kJ⁻¹ * yJ⁻¹) := by
  rw [zJ_eq, yJ, ← jw_append, ← jw_append, jw_eq_jw wordMat_data.2.2.2.2.2.1]

theorem zJ_pow_three : (kJ * yJ * kJ⁻¹ * yJ⁻¹) ^ 3 = 1 := by
  rw [zJ_eq, pow_three', ← jw_append, ← jw_append, jw_eq_jw wordMat_data.2.2.2.2.2.2.1, jw_nil]

theorem kJ_eq : kJ = (jw [3] * (kJ * yJ * kJ⁻¹ * yJ⁻¹)⁻¹ * (jw [3])⁻¹) *
    (jw [0, 0] * (kJ * yJ * kJ⁻¹ * yJ⁻¹)⁻¹ * (jw [0, 0])⁻¹) *
    (jw [3, 3] * (kJ * yJ * kJ⁻¹ * yJ⁻¹)⁻¹ * (jw [3, 3])⁻¹) *
    (jw [2] * (kJ * yJ * kJ⁻¹ * yJ⁻¹)⁻¹ * (jw [2])⁻¹) := by
  obtain ⟨-, -, hz, -, -, -, -, h3, h00, h33, h2, hk⟩ := wordMat_data
  rw [zJ_eq, jw_inv hz, jw_inv h3, jw_inv h00, jw_inv h33, jw_inv h2, ← jw_append, ← jw_append,
    ← jw_append, ← jw_append, ← jw_append, ← jw_append, ← jw_append, ← jw_append,
    ← jw_append, ← jw_append, ← jw_append, kJ]
  exact jw_eq_jw hk

end CFSG.Quasithin.H13.U3.NLine

namespace CFSG.Quasithin.H13.U3

open NLine

theorem u33CommDimFact_holds : U33CommDimFact := by
  intro W _ _ hW ρ _ hcard
  exfalso
  have hW' : ∀ w : W, w * w = 1 := fun w => by rw [← pow_two]; exact hW w
  have hz := eq_one_of_card_commMap_le_four hW' ρ (k := kJ) (y := yJ) yJ_pow_three zJ_mul_kJ
    zJ_mul_yJ zJ_pow_three (by rw [show kJ = ⟨kGL, kGL_mem_J6⟩ from rfl, hcard])
  have hk1 : ρ kJ = 1 := by
    rw [kJ_eq]
    simp only [map_mul, map_inv, hz, inv_one, mul_one, mul_inv_cancel]
  have h1 : (Set.range fun w : W => ρ ⟨kGL, kGL_mem_J6⟩ w * w⁻¹) = {1} := by
    ext x
    simp only [Set.mem_range, Set.mem_singleton_iff]
    constructor
    · rintro ⟨w, rfl⟩
      rw [show (⟨kGL, kGL_mem_J6⟩ : ↥J6) = kJ from rfl, hk1, MulAut.one_apply, mul_inv_cancel]
    · rintro rfl
      exact ⟨1, by simp⟩
  rw [h1, Nat.card_unique] at hcard
  omega

end CFSG.Quasithin.H13.U3
