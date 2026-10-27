module

import CFSG.RankThree.PartTwo.Sec14.Ronan148WFieldE27Cyc
public import CFSG.RankThree.PartTwo.Sec4.LThreePiFixed
public import CFSG.RankThree.PartTwo.Sec4.LThreePiProj

public section

namespace CFSG.RankThree.PartTwo.Sec14.Ronan148W

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec4
open CFSG.LocalAnalysis.ComponentInitial CFSG.Assembly.LowTwoRank
open CFSG.Assembly.RankThreeEven (projImage)
open Matrix

section Group

variable {Γ : Type*} [Group Γ]

theorem pow_three_eq_one_of_central_comm {x y c : Γ} (hyx : y * x = c * (x * y))
    (hc : ∀ g : Γ, g * c = c * g) (hx3 : ∀ g : Γ, g * x ^ 3 = x ^ 3 * g) : c ^ 3 = 1 := by
  have h1 : y * x * y⁻¹ = c * x := by rw [hyx]; group
  have h2 : y * x ^ 3 * y⁻¹ = (y * x * y⁻¹) ^ 3 := (conj_pow).symm
  rw [h1, (Commute.mul_pow (hc x).symm 3), hx3 y, mul_inv_cancel_right] at h2
  exact mul_eq_right.mp h2.symm

theorem mul_pow_three_of_central_comm {x y c : Γ} (hyx : y * x = c * (x * y))
    (hc : ∀ g : Γ, g * c = c * g) (hc3 : c ^ 3 = 1) : (x * y) ^ 3 = x ^ 3 * y ^ 3 := by
  have hc' : ∀ g h : Γ, g * (c * h) = c * (g * h) := fun g h => by
    rw [← mul_assoc, hc g, mul_assoc]
  have h1 : y * x * y⁻¹ = c * x := by rw [hyx]; group
  have h2 : y ^ 2 * x * (y ^ 2)⁻¹ = c * (c * x) := by
    have e : y ^ 2 * x * (y ^ 2)⁻¹ = y * (y * x * y⁻¹) * y⁻¹ := by rw [pow_two]; group
    rw [e, h1, hc' y x, mul_assoc c, h1]
  have e3 : (x * y) ^ 3 = x * (y * x * y⁻¹) * (y ^ 2 * x * (y ^ 2)⁻¹) * y ^ 3 := by
    simp only [pow_succ, pow_zero, one_mul]
    group
  rw [e3, h1, h2, hc' x x, mul_assoc c, hc' (x * x), hc' (x * x), mul_assoc c, mul_assoc c]
  have e4 : c * (c * (c * (x * x * x) * y ^ 3)) = c ^ 3 * (x ^ 3 * y ^ 3) := by
    simp only [pow_succ, pow_zero, one_mul, mul_assoc]
  rw [e4, hc3, one_mul]

end Group

section Lifts

variable {G : Type} [Group G] {L : Subgroup G} [hLn : L.Normal]
  {K : Type} [Field K] {p f : ℕ} {π : Bool}

theorem pow_three_mem_statedScalars_of_isPGLAtP (hK : PiField π p f K) (hq : ModThree π (p ^ f))
    [Group.IsPerfect (projImage (slPi π 3 (p ^ f) K))]
    {e : L ≃* projImage (slPi π 3 (p ^ f) K)} {b : G} (hb : b ^ 3 = 1) {y : GL (Fin 3) K}
    (hy : IsPGLAtP e b y) : y ^ 3 ∈ StatedScalars (Fin 3) K := by
  have h1 := isPGLAtP_pow hy 3
  rw [hb] at h1
  have h2 := isPGLAtP_inv_mul_mem hK hq
    (isPGLAtP_of_mem_centralizer e (Subgroup.one_mem _)) h1
  rwa [inv_one, one_mul] at h2

theorem comm_mem_statedScalars_of_isPGLAtP (hK : PiField π p f K) (hq : ModThree π (p ^ f))
    [Group.IsPerfect (projImage (slPi π 3 (p ^ f) K))]
    {e : L ≃* projImage (slPi π 3 (p ^ f) K)} {b₁ b₂ : G} (h : b₁ * b₂ = b₂ * b₁)
    {y₁ y₂ : GL (Fin 3) K} (hy₁ : IsPGLAtP e b₁ y₁) (hy₂ : IsPGLAtP e b₂ y₂) :
    y₂ * y₁ * (y₁ * y₂)⁻¹ ∈ StatedScalars (Fin 3) K := by
  have h12 := isPGLAtP_mul e hy₁ hy₂
  have h21 := isPGLAtP_mul e hy₂ hy₁
  rw [← h] at h21
  have h3 := isPGLAtP_inv_mul_mem hK hq h12 h21
  have h4 := (StatedScalars.normal (Fin 3) K).conj_mem _ h3 (y₁ * y₂)
  convert h4 using 1
  group

theorem mul_pow_three_of_isPGLAtP (hK : PiField π p f K) (hq : ModThree π (p ^ f))
    [Group.IsPerfect (projImage (slPi π 3 (p ^ f) K))]
    {e : L ≃* projImage (slPi π 3 (p ^ f) K)} {b₁ b₂ : G} (h : b₁ * b₂ = b₂ * b₁)
    (hb₁ : b₁ ^ 3 = 1) {y₁ y₂ : GL (Fin 3) K} (hy₁ : IsPGLAtP e b₁ y₁)
    (hy₂ : IsPGLAtP e b₂ y₂) : (y₁ * y₂) ^ 3 = y₁ ^ 3 * y₂ ^ 3 := by
  set c := y₂ * y₁ * (y₁ * y₂)⁻¹ with hcdef
  have hcS : c ∈ StatedScalars (Fin 3) K := comm_mem_statedScalars_of_isPGLAtP hK hq h hy₁ hy₂
  have hc : ∀ g, g * c = c * g := fun g => commute_of_mem_statedScalars hcS g
  have hyx : y₂ * y₁ = c * (y₁ * y₂) := by rw [hcdef]; group
  have hx3 : ∀ g, g * y₁ ^ 3 = y₁ ^ 3 * g := fun g =>
    commute_of_mem_statedScalars (pow_three_mem_statedScalars_of_isPGLAtP hK hq hb₁ hy₁) g
  exact mul_pow_three_of_central_comm hyx hc (pow_three_eq_one_of_central_comm hyx hc hx3)

end Lifts

theorem pow_piCard_eq_self_of_pow_qSubPi {M : Type*} [Monoid M] {π : Bool} {q₀ : ℕ}
    (hq₀ : 1 ≤ q₀) {x : M} (hx : x ^ qSubPi π q₀ = 1) : x ^ piCard π q₀ = x := by
  obtain ⟨k, rfl⟩ : ∃ k, q₀ = k + 1 := ⟨q₀ - 1, by omega⟩
  cases π
  · change x ^ ((k + 1) ^ 2) = x
    change x ^ (k + 1 + 1) = 1 at hx
    have e : (k + 1) ^ 2 = (k + 1 + 1) * k + 1 := by ring
    rw [e, pow_succ, pow_mul, hx, one_pow, one_mul]
  · change x ^ (k + 1) = x
    change x ^ (k + 1 - 1) = 1 at hx
    rw [Nat.add_sub_cancel] at hx
    rw [pow_succ, hx, one_mul]

section Split

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} [hLn : L.Normal]
  {K : Type} [Field K] {p f : ℕ} {π : Bool}

theorem exists_cube_scalar_of_fixed (hK : PiField π p f K) (hq : ModThree π (p ^ f))
    [Group.IsPerfect (projImage (slPi π 3 (p ^ f) K))] {f₀ : ℕ} (hf : f = 3 * f₀)
    {φ : K ≃+* K} (hφ : ∀ c, φ c = c ^ piCard π (p ^ f₀)) (hφ3 : orderOf φ = 3)
    {ψ : K ≃+* K} (hψ : ψ = φ ∨ ψ = φ ^ 2) {e : L ≃* projImage (slPi π 3 (p ^ f) K)} {b : G}
    (hb : b ^ 3 = 1) {y : GL (Fin 3) K} (hy : IsPGLAtP e b y) (hyψ : frobGL ψ y = y) :
    ∃ ℓ : Kˣ, ℓ ∈ rootsOfUnity (qSubPi π (p ^ f₀)) K ∧
      y ^ 3 = GeneralLinearGroup.scalar (Fin 3) ℓ := by
  obtain ⟨ℓ, hℓ⟩ := pow_three_mem_statedScalars_of_isPGLAtP hK hq hb hy
  refine ⟨ℓ, ?_, hℓ.symm⟩
  have hℓT : ℓ ∈ rootsOfUnity (qSubPi π (p ^ f)) K := by
    rw [← scalar_mem_glPi_iff hK, hℓ]
    exact pow_mem hy.1 3
  have hψℓ : ψ (ℓ : K) = ℓ := by
    have h1 : frobGL ψ (y ^ 3) = y ^ 3 := by rw [map_pow, hyψ]
    rw [← hℓ, frobGL_scalar] at h1
    have h2 := congrArg (fun A : GL (Fin 3) K => (A : Matrix (Fin 3) (Fin 3) K) 0 0) h1
    simpa [GeneralLinearGroup.coe_scalar, Matrix.scalar_apply] using h2
  have hφℓ : (ℓ : K) ^ piCard π (p ^ f₀) = ℓ := by
    rw [← hφ]
    exact (fixed_iff_of_sq hφ3 hψ _).mp hψℓ
  have hqq : p ^ f = (p ^ f₀) ^ 3 := by rw [hf, pow_mul']
  have hq₀1 : 1 ≤ p ^ f₀ := Nat.one_le_pow _ _ hK.prime.pos
  rw [mem_rootsOfUnity]
  apply Units.ext
  rw [Units.val_pow_eq_pow_val, Units.val_one]
  have hℓN := congrArg Units.val ((mem_rootsOfUnity _ _).mp hℓT)
  rw [Units.val_pow_eq_pow_val, Units.val_one, hqq] at hℓN
  exact pow_qSubPi_eq_one_of_fixed hq₀1 ℓ.ne_zero hφℓ hℓN

theorem exists_split_lift (hK : PiField π p f K) (hq : ModThree π (p ^ f))
    [Group.IsPerfect (projImage (slPi π 3 (p ^ f) K))] {f₀ : ℕ} (hf : f = 3 * f₀)
    {φ : K ≃+* K} (hφ : ∀ c, φ c = c ^ piCard π (p ^ f₀)) (hφ3 : orderOf φ = 3)
    {ψ : K ≃+* K} (hψ : ψ = φ ∨ ψ = φ ^ 2) {e : L ≃* projImage (slPi π 3 (p ^ f) K)}
    {B : Subgroup G} (hB : CFSG.Assembly.IsElemAbelian 3 B) (hB9 : Nat.card B = 9)
    (hlift : ∀ b ∈ B, ∃ y, IsPGLAtP e b y ∧ frobGL ψ y = y) :
    ∃ x ∈ B, x ≠ 1 ∧ ∃ y, IsPGLAtP e x y ∧ frobGL ψ y = y ∧ y ^ 3 = 1 := by
  classical
  have := hK.finite
  have hqq : p ^ f = (p ^ f₀) ^ 3 := by rw [hf, pow_mul']
  have hq₀1 : 1 ≤ p ^ f₀ := Nat.one_le_pow _ _ hK.prime.pos
  have hq₀ : ModThree π (p ^ f₀) := modThree_of_cube (hqq ▸ hq)
  have hdvd : qSubPi π (p ^ f₀) ∣ qSubPi π (p ^ f) := by
    rw [hqq, qSubPi_cube_eq hq₀]
    exact dvd_mul_right _ _
  have hN0 : qSubPi π (p ^ f) ≠ 0 := qSubPi_ne_zero hK hq
  have hN₀0 : qSubPi π (p ^ f₀) ≠ 0 := fun h0 => hN0 (Nat.eq_zero_of_zero_dvd (h0 ▸ hdvd))
  haveI : NeZero (qSubPi π (p ^ f₀)) := ⟨hN₀0⟩
  haveI : IsCyclic (rootsOfUnity (qSubPi π (p ^ f₀)) K) := rootsOfUnity.isCyclic K _
  have hHcard : Nat.card (rootsOfUnity (qSubPi π (p ^ f₀)) K) = qSubPi π (p ^ f₀) :=
    CFSG.LinearGroups.card_rootsOfUnity_of_dvd (dvd_trans hdvd (qSubPi_dvd hK))
  have h3H : 3 ∣ Nat.card (rootsOfUnity (qSubPi π (p ^ f₀)) K) := by
    rw [hHcard]
    exact three_dvd_qSubPi hq₀
  have hHT : ∀ μ ∈ rootsOfUnity (qSubPi π (p ^ f₀)) K, μ ∈ rootsOfUnity (qSubPi π (p ^ f)) K :=
    fun μ hμ => rootsOfUnity_le_of_dvd hdvd hμ
  have hHψ : ∀ μ ∈ rootsOfUnity (qSubPi π (p ^ f₀)) K, ψ (μ : K) = μ := by
    intro μ hμ
    rw [fixed_iff_of_sq hφ3 hψ, hφ]
    apply pow_piCard_eq_self_of_pow_qSubPi hq₀1
    have := congrArg Units.val ((mem_rootsOfUnity _ _).mp hμ)
    rwa [Units.val_pow_eq_pow_val, Units.val_one] at this
  have hadj : ∀ x : G, ∀ y, IsPGLAtP e x y → frobGL ψ y = y →
      ∀ μ ∈ rootsOfUnity (qSubPi π (p ^ f₀)) K,
      y ^ 3 = GeneralLinearGroup.scalar (Fin 3) (μ ^ 3) →
      ∃ y', IsPGLAtP e x y' ∧ frobGL ψ y' = y' ∧ y' ^ 3 = 1 := by
    intro x y hy hyψ μ hμ hy3
    refine ⟨y * GeneralLinearGroup.scalar (Fin 3) μ⁻¹,
      isPGLAtP_mul_scalar hy ((scalar_mem_glPi_iff hK _).mpr (inv_mem (hHT μ hμ))), ?_, ?_⟩
    · rw [map_mul, hyψ, frobGL_scalar]
      congr 2
      apply Units.ext
      rw [Units.coe_map]
      exact hHψ _ (inv_mem hμ)
    · rw [(show Commute y (GeneralLinearGroup.scalar (Fin 3) μ⁻¹) from
          commute_of_mem_statedScalars ⟨μ⁻¹, rfl⟩ y).mul_pow, hy3, ← map_pow, ← map_mul,
        inv_pow, mul_inv_cancel, map_one]
  have hfin : ∀ x ∈ B, x ≠ 1 → ∀ y, IsPGLAtP e x y → frobGL ψ y = y → ∀ ℓ : Kˣ,
      y ^ 3 = GeneralLinearGroup.scalar (Fin 3) ℓ →
      (∃ μ ∈ rootsOfUnity (qSubPi π (p ^ f₀)) K, μ ^ 3 = ℓ) →
      ∃ x ∈ B, x ≠ 1 ∧ ∃ y, IsPGLAtP e x y ∧ frobGL ψ y = y ∧ y ^ 3 = 1 := by
    rintro x hx hx1 y hy hyψ ℓ hy3 ⟨μ, hμ, rfl⟩
    obtain ⟨y', h1, h2, h3⟩ := hadj x y hy hyψ μ hμ hy3
    exact ⟨x, hx, hx1, y', h1, h2, h3⟩
  have hcube : ∀ (ℓ : Kˣ) (hℓ : ℓ ∈ rootsOfUnity (qSubPi π (p ^ f₀)) K),
      (∃ c : rootsOfUnity (qSubPi π (p ^ f₀)) K, c ^ 3 = ⟨ℓ, hℓ⟩) →
      ∃ μ ∈ rootsOfUnity (qSubPi π (p ^ f₀)) K, μ ^ 3 = ℓ := by
    rintro ℓ hℓ ⟨c, hc⟩
    exact ⟨c, c.2, by simpa using congrArg Subtype.val hc⟩
  have hcomm : ∀ a ∈ B, ∀ b ∈ B, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (hB.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  obtain ⟨b₁, hb₁, hb₁1⟩ : ∃ b ∈ B, b ≠ 1 := by
    by_contra h
    push Not at h
    have hbot : B = ⊥ := (Subgroup.eq_bot_iff_forall _).mpr h
    rw [hbot, Subgroup.card_bot] at hB9
    omega
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hb₁o : orderOf b₁ = 3 := orderOf_eq_prime (hB.2 b₁ hb₁) hb₁1
  obtain ⟨b₂, hb₂, hb₂Z⟩ : ∃ b ∈ B, b ∉ Subgroup.zpowers b₁ := by
    by_contra h
    push Not at h
    have hle := Subgroup.card_le_of_le (show B ≤ Subgroup.zpowers b₁ from h)
    rw [hB9, Nat.card_zpowers, hb₁o] at hle
    omega
  have hb₂1 : b₂ ≠ 1 := fun h => hb₂Z (h ▸ Subgroup.one_mem _)
  obtain ⟨y₁, hy₁, hy₁ψ⟩ := hlift b₁ hb₁
  obtain ⟨y₂, hy₂, hy₂ψ⟩ := hlift b₂ hb₂
  obtain ⟨ℓ₁, hℓ₁, hy₁3⟩ := exists_cube_scalar_of_fixed hK hq hf hφ hφ3 hψ (hB.2 b₁ hb₁) hy₁ hy₁ψ
  obtain ⟨ℓ₂, hℓ₂, hy₂3⟩ := exists_cube_scalar_of_fixed hK hq hf hφ hφ3 hψ (hB.2 b₂ hb₂) hy₂ hy₂ψ
  by_cases h1 : ∃ c : rootsOfUnity (qSubPi π (p ^ f₀)) K, c ^ 3 = ⟨ℓ₁, hℓ₁⟩
  · exact hfin b₁ hb₁ hb₁1 y₁ hy₁ hy₁ψ ℓ₁ hy₁3 (hcube ℓ₁ hℓ₁ h1)
  by_cases h2 : ∃ c : rootsOfUnity (qSubPi π (p ^ f₀)) K, c ^ 3 = ⟨ℓ₂, hℓ₂⟩
  · exact hfin b₂ hb₂ hb₂1 y₂ hy₂ hy₂ψ ℓ₂ hy₂3 (hcube ℓ₂ hℓ₂ h2)
  rcases cube_mul_or_cube_mul_sq h3H h1 h2 with h | h
  ·
    refine hfin (b₁ * b₂) (mul_mem hb₁ hb₂) ?_ (y₁ * y₂) (isPGLAtP_mul e hy₁ hy₂)
      (by rw [map_mul, hy₁ψ, hy₂ψ]) (ℓ₁ * ℓ₂) ?_ (hcube _ (mul_mem hℓ₁ hℓ₂) h)
    · intro h12
      apply hb₂Z
      rw [eq_inv_of_mul_eq_one_right h12]
      exact inv_mem (Subgroup.mem_zpowers b₁)
    · rw [mul_pow_three_of_isPGLAtP hK hq (hcomm _ hb₁ _ hb₂) (hB.2 b₁ hb₁) hy₁ hy₂, hy₁3, hy₂3,
        map_mul]
  ·
    have hb₂3 : b₂ ^ 3 = 1 := hB.2 b₂ hb₂
    refine hfin (b₁ * b₂ ^ 2) (mul_mem hb₁ (pow_mem hb₂ 2)) ?_ (y₁ * y₂ ^ 2)
      (isPGLAtP_mul e hy₁ (isPGLAtP_pow hy₂ 2)) (by rw [map_mul, map_pow, hy₁ψ, hy₂ψ])
      (ℓ₁ * ℓ₂ ^ 2) ?_ (hcube _ (mul_mem hℓ₁ (pow_mem hℓ₂ 2)) h)
    · intro h12
      apply hb₂Z
      have e1 : b₂ ^ 2 = b₁⁻¹ := eq_inv_of_mul_eq_one_right h12
      have e2 : b₂ = (b₂ ^ 2) ^ 2 := by
        rw [← pow_mul, show 2 * 2 = 3 + 1 by rfl, pow_succ, hb₂3, one_mul]
      rw [e2, e1]
      exact pow_mem (inv_mem (Subgroup.mem_zpowers b₁)) 2
    · rw [mul_pow_three_of_isPGLAtP hK hq (hcomm _ hb₁ _ (pow_mem hb₂ 2)) (hB.2 b₁ hb₁) hy₁
        (isPGLAtP_pow hy₂ 2), hy₁3, ← pow_mul, mul_comm 2 3, pow_mul, hy₂3, map_mul, map_pow]

end Split

end CFSG.RankThree.PartTwo.Sec14.Ronan148W
