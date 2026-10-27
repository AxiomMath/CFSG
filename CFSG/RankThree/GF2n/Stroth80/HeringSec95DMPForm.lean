module

public import CFSG.RankThree.GF2n.Stroth80.HeringSec95DM1A

public section

namespace CFSG.RankThree.GF2n.Stroth80.HS9.MP

open CFSG.RankThree.GF2n.Stroth80.HS9.M1
open scoped Matrix MatrixGroups

section Single

variable {K : Type} [Field K] {Y : Type} [AddCommGroup Y] [Module K Y]

private theorem s95b_smulVec_u_zero (y : Y) :
    smulVec (uMat (1 : K)) (Pi.single 0 y : Fin 2 → Y) = Pi.single 0 y := by
  ext i
  fin_cases i <;> simp [smulVec, uMat]

private theorem s95b_smulVec_u_one (y : Y) :
    smulVec (uMat (1 : K)) (Pi.single 1 y : Fin 2 → Y) = Pi.single 0 y + Pi.single 1 y := by
  ext i
  fin_cases i <;> simp [smulVec, uMat]

private theorem s95b_smulVec_l_zero (y : Y) :
    smulVec (lMat (1 : K)) (Pi.single 0 y : Fin 2 → Y) = Pi.single 0 y + Pi.single 1 y := by
  ext i
  fin_cases i <;> simp [smulVec, lMat]

private theorem s95b_smulVec_l_one (y : Y) :
    smulVec (lMat (1 : K)) (Pi.single 1 y : Fin 2 → Y) = Pi.single 1 y := by
  ext i
  fin_cases i <;> simp [smulVec, lMat]

private theorem s95b_smulVec_t_zero (μ : K) (y : Y) :
    smulVec (tMat μ) (Pi.single 0 y : Fin 2 → Y) = Pi.single 0 (μ • y) := by
  ext i
  fin_cases i <;> simp [smulVec, tMat]

private theorem s95b_smulVec_t_one (μ : K) (y : Y) :
    smulVec (tMat μ) (Pi.single 1 y : Fin 2 → Y) = Pi.single 1 (μ⁻¹ • y) := by
  ext i
  fin_cases i <;> simp [smulVec, tMat]

private theorem s95b_single_smul (i : Fin 2) (c : K) (y : Y) :
    (Pi.single i (c • y) : Fin 2 → Y) = c • Pi.single i y := by
  ext j
  by_cases h : j = i
  · subst h
    simp
  · simp [h]

private theorem s95b_split (u : Fin 2 → Y) : u = Pi.single 0 (u 0) + Pi.single 1 (u 1) := by
  ext i
  fin_cases i <;> simp

private theorem s95b_exists_ne_zero_ne_one [Finite K] (hK : 4 ≤ Nat.card K) :
    ∃ μ : K, μ ≠ 0 ∧ μ ≠ 1 := by
  by_contra hcon
  push Not at hcon
  have hsurj : Function.Surjective (fun i : Fin 2 => if i = 0 then (0 : K) else 1) := by
    intro y
    by_cases hy : y = 0
    · exact ⟨0, by simp [hy]⟩
    · exact ⟨1, by simp [hcon y hy]⟩
  have hle := Nat.card_le_card_of_surjective _ hsurj
  simp only [Nat.card_fin] at hle
  omega

private theorem s95b_exists_sq_ne_one [Finite K] [CharP K 2] (hK : 4 ≤ Nat.card K) :
    ∃ μ : K, μ ≠ 0 ∧ μ ^ 2 ≠ 1 := by
  obtain ⟨μ, h0, h1⟩ := s95b_exists_ne_zero_ne_one hK
  refine ⟨μ, h0, fun h => h1 ?_⟩
  have h2 : (2 : K) = 0 := by exact_mod_cast CharP.cast_eq_zero K 2
  have h3 : (μ - 1) ^ 2 = 0 := by linear_combination h + (1 - μ) * h2
  exact sub_eq_zero.mp ((pow_eq_zero_iff two_ne_zero).mp h3)

private theorem s95b_inv_zero (φ : (Fin 2 → Y) →ₗ[K] K)
    (hu : ∀ u, φ (smulVec (uMat (1 : K)) u) = φ u)
    (hl : ∀ u, φ (smulVec (lMat (1 : K)) u) = φ u) (u : Fin 2 → Y) : φ u = 0 := by
  have h1 : ∀ y : Y, φ (Pi.single 0 y) = 0 := fun y => by
    have h := hu (Pi.single 1 y)
    rw [s95b_smulVec_u_one, map_add] at h
    linear_combination h
  have h2 : ∀ y : Y, φ (Pi.single 1 y) = 0 := fun y => by
    have h := hl (Pi.single 0 y)
    rw [s95b_smulVec_l_zero, map_add] at h
    linear_combination h
  rw [s95b_split u, map_add, h1, h2, add_zero]

private theorem s95b_single_form [CharP K 2] (b : (Fin 2 → Y) →ₗ[K] (Fin 2 → Y) →ₗ[K] K)
    (hu : ∀ u u', b (smulVec (uMat (1 : K)) u) (smulVec (uMat (1 : K)) u') = b u u')
    (hl : ∀ u u', b (smulVec (lMat (1 : K)) u) (smulVec (lMat (1 : K)) u') = b u u') :
    ∃ β : Y →ₗ[K] Y →ₗ[K] K, (∀ y y', β y y' = b (Pi.single 0 y) (Pi.single 1 y')) ∧
      ∀ u u', b u u' = β (u 0) (u' 1) + β (u 1) (u' 0) := by
  have h2 : (2 : K) = 0 := by exact_mod_cast CharP.cast_eq_zero K 2
  have e00 : ∀ y y' : Y, b (Pi.single 0 y) (Pi.single 0 y') = 0 := fun y y' => by
    have h := hu (Pi.single 1 y) (Pi.single 0 y')
    rw [s95b_smulVec_u_one, s95b_smulVec_u_zero, map_add, LinearMap.add_apply] at h
    linear_combination h
  have e11 : ∀ y y' : Y, b (Pi.single 1 y) (Pi.single 1 y') = 0 := fun y y' => by
    have h := hl (Pi.single 0 y) (Pi.single 1 y')
    rw [s95b_smulVec_l_zero, s95b_smulVec_l_one, map_add, LinearMap.add_apply] at h
    linear_combination h
  have e10 : ∀ y y' : Y,
      b (Pi.single 1 y) (Pi.single 0 y') = b (Pi.single 0 y) (Pi.single 1 y') := fun y y' => by
    have h := hu (Pi.single 1 y) (Pi.single 1 y')
    rw [s95b_smulVec_u_one, s95b_smulVec_u_one] at h
    simp only [map_add, LinearMap.add_apply] at h
    linear_combination h - e00 y y' - b (Pi.single 0 y) (Pi.single 1 y') * h2
  refine ⟨b.compl₁₂ (LinearMap.single K (fun _ : Fin 2 => Y) 0)
    (LinearMap.single K (fun _ : Fin 2 => Y) 1), fun y y' => rfl, fun u u' => ?_⟩
  have hexp : b u u' = b (Pi.single 0 (u 0) + Pi.single 1 (u 1))
      (Pi.single 0 (u' 0) + Pi.single 1 (u' 1)) := by
    rw [← s95b_split u, ← s95b_split u']
  rw [hexp]
  simp only [map_add, LinearMap.add_apply, e00, e11, e10 (u 1) (u' 0), LinearMap.compl₁₂_apply,
    LinearMap.single_apply]
  ring

private theorem s95b_single_alt [Finite K] [CharP K 2] (hK : 4 ≤ Nat.card K)
    (b : (Fin 2 → Y) →ₗ[K] (Fin 2 → Y) →ₗ[K] K) (q : (Fin 2 → Y) → K)
    (hqs : ∀ (c : K) u, q (c • u) = c ^ 2 * q u)
    (hqp : ∀ u u', q (u + u') = q u + q u' + b u u')
    (hqt : ∀ μ : K, μ ≠ 0 → ∀ u, q (smulVec (tMat μ) u) = q u)
    (hql : ∀ u, q (smulVec (lMat (1 : K)) u) = q u) (y : Y) :
    b (Pi.single 0 y) (Pi.single 1 y) = 0 := by
  obtain ⟨μ, hμ0, hμ2⟩ := s95b_exists_sq_ne_one hK
  have hμ' : μ ^ 2 - 1 ≠ 0 := sub_ne_zero.mpr hμ2
  have hν' : μ⁻¹ ^ 2 - 1 ≠ 0 := by
    rw [sub_ne_zero, inv_pow]
    exact fun h => hμ2 (inv_eq_one.mp h)
  have h0 : q (Pi.single 0 y) = 0 := by
    have h := hqt μ hμ0 (Pi.single 0 y)
    rw [s95b_smulVec_t_zero, s95b_single_smul, hqs] at h
    have h' : (μ ^ 2 - 1) * q (Pi.single 0 y) = 0 := by linear_combination h
    exact (mul_eq_zero.mp h').resolve_left hμ'
  have h1 : q (Pi.single 1 y) = 0 := by
    have h := hqt μ hμ0 (Pi.single 1 y)
    rw [s95b_smulVec_t_one, s95b_single_smul, hqs] at h
    have h' : (μ⁻¹ ^ 2 - 1) * q (Pi.single 1 y) = 0 := by linear_combination h
    exact (mul_eq_zero.mp h').resolve_left hν'
  have h2 : q (Pi.single 0 y + Pi.single 1 y) = 0 := by
    rw [← s95b_smulVec_l_zero (K := K), hql, h0]
  have h3 := hqp (Pi.single 0 y) (Pi.single 1 y)
  rw [h2, h0, h1] at h3
  linear_combination -h3

private theorem s95b_factor [Finite K] [CharP K 2] (hK : 4 ≤ Nat.card K)
    (b : (Fin 2 → Y) →ₗ[K] (Fin 2 → Y) →ₗ[K] K) (q : (Fin 2 → Y) → K)
    (hb : ∀ g : SL(2, K), ∀ u u', b (smulVec (g : Matrix (Fin 2) (Fin 2) K) u)
      (smulVec (g : Matrix (Fin 2) (Fin 2) K) u') = b u u')
    (hqs : ∀ (c : K) u, q (c • u) = c ^ 2 * q u)
    (hqp : ∀ u u', q (u + u') = q u + q u' + b u u')
    (hq : ∀ g : SL(2, K), ∀ u, q (smulVec (g : Matrix (Fin 2) (Fin 2) K) u) = q u) :
    ∃ β : Y →ₗ[K] Y →ₗ[K] K, (∀ y, β y y = 0) ∧
      (∀ y y', β y y' = b (Pi.single 0 y) (Pi.single 1 y')) ∧
      ∀ u u', b u u' = β (u 0) (u' 1) + β (u 1) (u' 0) := by
  obtain ⟨β, hβ, hform⟩ := s95b_single_form b (fun u u' => hb (uSL 1) u u')
    (fun u u' => hb (lSL 1) u u')
  refine ⟨β, fun y => ?_, hβ, hform⟩
  rw [hβ]
  exact s95b_single_alt hK b q hqs hqp
    (fun μ hμ u => hq (tSL (Units.mk0 μ hμ)) u) (fun u => hq (lSL 1) u) y

end Single

theorem step95_form (K : Type) [Field K] [Finite K] [CharP K 2] (hK : 4 ≤ Nat.card K)
    {Y₁ Y₂ : Type} [AddCommGroup Y₁] [Module K Y₁] [AddCommGroup Y₂] [Module K Y₂]
    (B : Wd K Y₁ Y₂ →ₗ[K] Wd K Y₁ Y₂ →ₗ[K] K) (Q : Wd K Y₁ Y₂ → K)
    (hnd : ∀ w, (∀ w', B w w' = 0) → w = 0)
    (hinv : ∀ (g h : SL(2, K)) w w', B (actW (g : Matrix (Fin 2) (Fin 2) K)
      (h : Matrix (Fin 2) (Fin 2) K) w) (actW (g : Matrix (Fin 2) (Fin 2) K)
      (h : Matrix (Fin 2) (Fin 2) K) w') = B w w')
    (hQs : ∀ (c : K) w, Q (c • w) = c ^ 2 * Q w) (hQp : ∀ w w', Q (w + w') = Q w + Q w' + B w w')
    (hQinv : ∀ (g h : SL(2, K)) w, Q (actW (g : Matrix (Fin 2) (Fin 2) K)
      (h : Matrix (Fin 2) (Fin 2) K) w) = Q w) :
    ∃ (β₁ : Y₁ →ₗ[K] Y₁ →ₗ[K] K) (β₂ : Y₂ →ₗ[K] Y₂ →ₗ[K] K),
      (∀ y, β₁ y y = 0) ∧ (∀ y, (∀ y', β₁ y y' = 0) → y = 0) ∧
      (∀ y, β₂ y y = 0) ∧ (∀ y, (∀ y', β₂ y y' = 0) → y = 0) ∧
      ∀ w w', B w w' = formW β₁ β₂ w w' := by
  have hsymm : ∀ w w', B w w' = B w' w := fun w w' => by
    have h1 := hQp w w'
    have h2 := hQp w' w
    rw [add_comm w' w] at h2
    linear_combination h2 - h1
  have hb₁ : ∀ g : SL(2, K), ∀ u u' : Fin 2 → Y₁,
      B (smulVec (g : Matrix (Fin 2) (Fin 2) K) u, 0)
        (smulVec (g : Matrix (Fin 2) (Fin 2) K) u', 0) = B (u, 0) (u', 0) := by
    intro g u u'
    simpa [actW, smulVec_one, smulVec_zero] using hinv g 1 (u, 0) (u', 0)
  have hq₁ : ∀ g : SL(2, K), ∀ u : Fin 2 → Y₁,
      Q (smulVec (g : Matrix (Fin 2) (Fin 2) K) u, 0) = Q (u, 0) := by
    intro g u
    simpa [actW, smulVec_one, smulVec_zero] using hQinv g 1 (u, 0)
  have hqs₁ : ∀ (c : K) (u : Fin 2 → Y₁), Q (c • u, 0) = c ^ 2 * Q (u, 0) := by
    intro c u
    simpa using hQs c (u, 0)
  have hqp₁ : ∀ u u' : Fin 2 → Y₁, Q (u + u', 0) = Q (u, 0) + Q (u', 0) + B (u, 0) (u', 0) := by
    intro u u'
    simpa using hQp (u, 0) (u', 0)
  have hb₂ : ∀ g : SL(2, K), ∀ v v' : Fin 2 → Y₂,
      B (0, smulVec (g : Matrix (Fin 2) (Fin 2) K) v)
        (0, smulVec (g : Matrix (Fin 2) (Fin 2) K) v') = B (0, v) (0, v') := by
    intro g v v'
    simpa [actW, smulVec_one, smulVec_zero] using hinv 1 g (0, v) (0, v')
  have hq₂ : ∀ g : SL(2, K), ∀ v : Fin 2 → Y₂,
      Q (0, smulVec (g : Matrix (Fin 2) (Fin 2) K) v) = Q (0, v) := by
    intro g v
    simpa [actW, smulVec_one, smulVec_zero] using hQinv 1 g (0, v)
  have hqs₂ : ∀ (c : K) (v : Fin 2 → Y₂), Q (0, c • v) = c ^ 2 * Q (0, v) := by
    intro c v
    simpa using hQs c (0, v)
  have hqp₂ : ∀ v v' : Fin 2 → Y₂, Q (0, v + v') = Q (0, v) + Q (0, v') + B (0, v) (0, v') := by
    intro v v'
    simpa using hQp (0, v) (0, v')
  obtain ⟨β₁, hβ₁a, hβ₁d, hβ₁f⟩ := s95b_factor hK
    (B.compl₁₂ (LinearMap.inl K (Fin 2 → Y₁) (Fin 2 → Y₂))
      (LinearMap.inl K (Fin 2 → Y₁) (Fin 2 → Y₂))) (fun u => Q (u, 0)) hb₁ hqs₁ hqp₁ hq₁
  obtain ⟨β₂, hβ₂a, hβ₂d, hβ₂f⟩ := s95b_factor hK
    (B.compl₁₂ (LinearMap.inr K (Fin 2 → Y₁) (Fin 2 → Y₂))
      (LinearMap.inr K (Fin 2 → Y₁) (Fin 2 → Y₂))) (fun v => Q (0, v)) hb₂ hqs₂ hqp₂ hq₂
  have hmix : ∀ (u : Fin 2 → Y₁) (v : Fin 2 → Y₂), B (u, 0) (0, v) = 0 := by
    intro u v
    have key := s95b_inv_zero ((B.flip (0, v)).comp (LinearMap.inl K (Fin 2 → Y₁) (Fin 2 → Y₂)))
      (fun u' => by
        simpa [actW, smulVec_one, smulVec_zero, coe_uSL] using hinv (uSL 1) 1 (u', 0) (0, v))
      (fun u' => by
        simpa [actW, smulVec_one, smulVec_zero, coe_lSL] using hinv (lSL 1) 1 (u', 0) (0, v)) u
    simpa using key
  have hform : ∀ w w', B w w' = formW β₁ β₂ w w' := by
    intro w w'
    have hw : w = (w.1, 0) + (0, w.2) := by simp
    have hw' : w' = (w'.1, 0) + (0, w'.2) := by simp
    have hexp : B w w' = B (w.1, 0) (w'.1, 0) + B (w.1, 0) (0, w'.2) +
        (B (0, w.2) (w'.1, 0) + B (0, w.2) (0, w'.2)) := by
      conv_lhs => rw [hw, hw']
      simp only [map_add, LinearMap.add_apply]
      abel
    have e1 := hβ₁f w.1 w'.1
    have e2 := hβ₂f w.2 w'.2
    simp only [LinearMap.compl₁₂_apply, LinearMap.inl_apply, LinearMap.inr_apply] at e1 e2
    rw [hexp, hmix w.1 w'.2, hsymm (0, w.2) (w'.1, 0), hmix w'.1 w.2, e1, e2]
    unfold formW
    ring
  refine ⟨β₁, β₂, hβ₁a, fun y hy => ?_, hβ₂a, fun z hz => ?_, hform⟩
  · have h0 : ∀ w', B ((Pi.single 0 y : Fin 2 → Y₁), (0 : Fin 2 → Y₂)) w' = 0 := by
      intro w'
      rw [hform]
      simp [formW, hy]
    have h := congrArg (fun w : Wd K Y₁ Y₂ => w.1 0) (hnd _ h0)
    simpa using h
  · have h0 : ∀ w', B ((0 : Fin 2 → Y₁), (Pi.single 0 z : Fin 2 → Y₂)) w' = 0 := by
      intro w'
      rw [hform]
      simp [formW, hz]
    have h := congrArg (fun w : Wd K Y₁ Y₂ => w.2 0) (hnd _ h0)
    simpa using h

end CFSG.RankThree.GF2n.Stroth80.HS9.MP
