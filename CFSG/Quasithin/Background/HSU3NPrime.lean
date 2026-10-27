module

public import CFSG.Quasithin.Background.HSU3Borel
public import CFSG.Quasithin.Background.HSL3PairNPrime
public import CFSG.Quasithin.Background.HTriU3

public section

namespace CFSG.Quasithin

namespace H

namespace SU3

open CFSG.Open CFSG.Assembly.LowTwoRank Matrix CFSG.LocalAnalysis.ComponentInitial
open scoped Matrix Pointwise

variable {K : Type} [Field K] [Finite K] [CharP K 2] {n : ℕ}

omit [Finite K] [CharP K 2] in
theorem normalizes_of_mem_natNorm {A : GL (Fin 3) K}
    (hA : matAut A ∈ natNorm (StatedSU 3 (2 ^ n) K)) :
    ∀ l ∈ StatedSU 3 (2 ^ n) K, A * l * A⁻¹ ∈ StatedSU 3 (2 ^ n) K := by
  intro l hl
  have hl' : natAut (StatedSU 3 (2 ^ n) K) ⟨l, hl⟩ ∈ natImage (StatedSU 3 (2 ^ n) K) := ⟨_, rfl⟩
  obtain ⟨l', hl'eq⟩ := (Subgroup.mem_normalizer_iff.mp hA _).mp hl'
  have h2 : matHom (A * l * A⁻¹) = matHom (l' : GL (Fin 3) K) := by
    rw [map_mul, map_mul, map_inv, matHom_apply, matHom_apply]
    exact hl'eq.symm
  rw [matHom_injective h2]
  exact l'.2

theorem gram_pow {A : Matrix (Fin 3) (Fin 3) K} {μ : K} (h : (conjM n A)ᵀ * A = μ • 1)
    (k : ℕ) : (conjM n (A ^ k))ᵀ * A ^ k = μ ^ k • 1 := by
  induction k with
  | zero => simp [conjM_one]
  | succ k ih =>
    rw [pow_succ, conjM_mul, Matrix.transpose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc _ (A ^ k),
      ih, Matrix.smul_mul, Matrix.one_mul, Matrix.mul_smul, h, smul_smul, pow_succ, mul_comm]

theorem mem_natImage_of_two_pow (hn : 1 ≤ n) (hK : Nat.card K = (2 ^ n) ^ 2)
    {s : MulAut (StdMod (Fin 3) K)} (hsN : s ∈ natNorm (StatedSU 3 (2 ^ n) K))
    (hsL : s ∈ linSub) {j : ℕ} (hs : s ^ 2 ^ j = 1) :
    s ∈ natImage (StatedSU 3 (2 ^ n) K) := by
  obtain ⟨A, rfl⟩ := exists_matAut_of_mem_linSub hsL
  have hA : A ^ 2 ^ j = 1 := matHom_injective (by
    rw [map_pow, map_one]
    exact hs)
  obtain ⟨μ, hμ⟩ := exists_gram_scalar hn hK (normalizes_of_mem_natNorm hsN)
  have h1 := gram_pow hμ (2 ^ j)
  rw [← Units.val_pow_eq_pow_val, hA, Units.val_one, conjM_one, Matrix.transpose_one,
    Matrix.one_mul] at h1
  have hμ1 : μ = 1 := by
    have h2 := congrFun (congrFun h1 0) 0
    simp only [Matrix.one_apply_eq, Matrix.smul_apply, smul_eq_mul, mul_one] at h2
    exact SL3Pair.eq_one_of_pow_two_pow h2.symm
  have hdet : (A : Matrix (Fin 3) (Fin 3) K).det = 1 := by
    refine SL3Pair.eq_one_of_pow_two_pow (j := j) ?_
    rw [← Matrix.det_pow, ← Units.val_pow_eq_pow_val, hA, Units.val_one, Matrix.det_one]
  have hmem : A ∈ StatedSU 3 (2 ^ n) K := by
    refine mem_statedSU hdet ?_
    rw [← conjM_eq_map_pow, hμ, hμ1, one_smul]
  exact ⟨⟨A, hmem⟩, rfl⟩

theorem permute_linSub (hn : 1 ≤ n) (hK : Nat.card K = (2 ^ n) ^ 2)
    {B S : Subgroup (MulAut (StdMod (Fin 3) K))} (hBN : B ≤ natNorm (StatedSU 3 (2 ^ n) K))
    (hSN : S ≤ natNorm (StatedSU 3 (2 ^ n) K)) (hBodd : Odd (Nat.card B)) (hS : IsPGroup 2 S)
    (hBS : (B : Set (MulAut (StdMod (Fin 3) K))) * S = S * B) :
    ((B ⊓ linSub : Subgroup (MulAut (StdMod (Fin 3) K))) : Set (MulAut (StdMod (Fin 3) K))) *
        ((S ⊓ natImage (StatedSU 3 (2 ^ n) K) : Subgroup (MulAut (StdMod (Fin 3) K))) :
          Set (MulAut (StdMod (Fin 3) K))) =
      ((S ⊓ natImage (StatedSU 3 (2 ^ n) K) : Subgroup (MulAut (StdMod (Fin 3) K))) :
          Set (MulAut (StdMod (Fin 3) K))) *
        ((B ⊓ linSub : Subgroup (MulAut (StdMod (Fin 3) K))) :
          Set (MulAut (StdMod (Fin 3) K))) := by
  classical
  have hΓ := hasScalarCommutant' hn hK
  apply SL3Pair.mul_comm_of_subset
  rintro _ ⟨u, hu, b, hb, rfl⟩
  have huL : u ∈ linSub := natImage_le_linSub _ hu.2
  have hub : u * b ∈ (S : Set (MulAut (StdMod (Fin 3) K))) * B := Set.mul_mem_mul hu.1 hb.1
  rw [← hBS] at hub
  obtain ⟨b', hb', s, hs, hbs⟩ := hub
  have hbs' : b' * s = u * b := hbs
  have hubL : u * b ∈ linSub := linSub.mul_mem huL hb.2
  have hb'k : b' ^ Nat.card B = 1 :=
    orderOf_dvd_iff_pow_eq_one.mp (Subgroup.orderOf_dvd_natCard B hb')
  obtain ⟨j, hj⟩ := hS ⟨s, hs⟩
  have hsj : s ^ 2 ^ j = 1 := congrArg Subtype.val hj
  have hse' : s = b'⁻¹ * (u * b) := by rw [← hbs']; group
  obtain ⟨σ, hσ⟩ := exists_semilinear hΓ (hBN hb')
  obtain ⟨τ, hτ⟩ := exists_semilinear hΓ (hSN hs)
  have hστ : σ * τ = 1 := by
    have h' := hσ.mul hτ
    rw [hbs'] at h'
    exact h'.unique hubL
  have hσk : σ ^ Nat.card B = 1 := by
    have h2 := hσ.pow (Nat.card B)
    rw [hb'k] at h2
    exact h2.unique isSemilinear_one
  have hτj : τ ^ 2 ^ j = 1 := by
    have h2 := hτ.pow (2 ^ j)
    rw [hsj] at h2
    exact h2.unique isSemilinear_one
  have hσ1 : σ = 1 := by
    have hτσ : τ = σ⁻¹ := eq_inv_of_mul_eq_one_right hστ
    have hσj : σ ^ 2 ^ j = 1 := by
      rw [hτσ, inv_pow, inv_eq_one] at hτj
      exact hτj
    have hcop : Nat.Coprime (Nat.card B) (2 ^ j) :=
      Nat.Coprime.pow_right j (Nat.coprime_two_right.mpr hBodd)
    exact orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes hcop
      (orderOf_dvd_of_pow_eq_one hσk) (orderOf_dvd_of_pow_eq_one hσj))
  rw [hσ1] at hσ
  have hb'L : b' ∈ linSub := hσ
  have hsL : s ∈ linSub := by
    rw [hse']
    exact linSub.mul_mem (linSub.inv_mem hb'L) hubL
  exact ⟨b', ⟨hb', hb'L⟩, s, ⟨hs, mem_natImage_of_two_pow hn hK (hSN hs) hsL hsj⟩, hbs⟩

theorem le_of_permutes (hn : 2 ≤ n) (hK : Nat.card K = (2 ^ n) ^ 2)
    {X : Subgroup (MulAut (StdMod (Fin 3) K))} (hX1 : natImage (StatedSU 3 (2 ^ n) K) ≤ X)
    (hX2 : X ≤ natNorm (StatedSU 3 (2 ^ n) K)) {Y B S : Subgroup (MulAut (StdMod (Fin 3) K))}
    {c : ℕ} (hYB : Y ≤ B) (hBX : B ≤ X) (hY : IsCyclic Y) (hYc : Nat.card Y = 2 ^ c - 1)
    (hBab : ∀ a ∈ B, ∀ b ∈ B, a * b = b * a) (hBodd : Odd (Nat.card B)) (hS : IsSylowIn 2 S X)
    (hBS : (B : Set (MulAut (StdMod (Fin 3) K))) * S = S * B) : c ≤ 2 * n := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Finite (MulAut (StdMod (Fin 3) K)) := MulEquiv.finite_left
  have hn1 : 1 ≤ n := by omega
  have hq : 4 ≤ 2 ^ n :=
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  have hK4 : 4 ≤ Nat.card K := by
    rw [hK]
    nlinarith
  have hBN : B ≤ natNorm (StatedSU 3 (2 ^ n) K) := hBX.trans hX2
  have hSN : S ≤ natNorm (StatedSU 3 (2 ^ n) K) := hS.le.trans hX2
  have hperm := permute_linSub hn1 hK hBN hSN hBodd hS.isPGroup hBS
  set ν := natAut (StatedSU 3 (2 ^ n) K) with hν
  have hνinj : Function.Injective ν := natAut_injective _
  have hLnX : ((natImage (StatedSU 3 (2 ^ n) K)).subgroupOf X).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hX1).mpr hX2
  have hU := hS.inf_normal hX1 hLnX
  set U' := (S ⊓ natImage (StatedSU 3 (2 ^ n) K)).comap ν with hU'
  have hU'map : U'.map ν = S ⊓ natImage (StatedSU 3 (2 ^ n) K) :=
    Subgroup.map_comap_eq_self (by exact inf_le_right)
  have htopmap : (⊤ : Subgroup ↥(StatedSU 3 (2 ^ n) K)).map ν =
      natImage (StatedSU 3 (2 ^ n) K) := by
    rw [← MonoidHom.range_eq_map]
  have hU'syl : IsSylowIn 2 U' ⊤ := by
    rw [← E1.isSylowIn_map_of_injective hνinj, hU'map, htopmap]
    exact hU
  let P' : Sylow 2 ↥(StatedSU 3 (2 ^ n) K) :=
    hU'syl.isPGroup.toSylow (by
      have := hU'syl.not_dvd_relIndex
      rwa [Subgroup.relIndex_top_right] at this)
  have hsylUI := isSylowIn_uiSub hn1 hK
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq ↥(StatedSU 3 (2 ^ n) K) P' hsylUI.toSylow
  have hgU : U'.map (MulAut.conj g).toMonoidHom = (uiSub n K).subgroupOf (StatedSU 3 (2 ^ n) K) :=
    by
    rw [← IsSylowIn.coe_toSylow hsylUI, ← hg, LinearFlag.coe_sylow_smul]
    rfl
  set c₀ := ν g with hc₀
  set U₁ := ((uiSub n K).subgroupOf (StatedSU 3 (2 ^ n) K)).map ν with hU₁def
  have hU₁ : (S ⊓ natImage (StatedSU 3 (2 ^ n) K)).map (MulAut.conj c₀).toMonoidHom = U₁ := by
    rw [hU₁def, ← hgU, ← hU'map, Subgroup.map_map, Subgroup.map_map]
    congr 1
    refine MonoidHom.ext fun x => ?_
    change c₀ * ν x * c₀⁻¹ = ν (g * x * g⁻¹)
    rw [hc₀, map_mul, map_mul, map_inv]
  set B₁ := (B ⊓ linSub).map (MulAut.conj c₀).toMonoidHom with hB₁
  have hc₀L : c₀ ∈ linSub := natImage_le_linSub _ ⟨g, rfl⟩
  have hc₀N : c₀ ∈ natNorm (StatedSU 3 (2 ^ n) K) := Subgroup.le_normalizer ⟨g, rfl⟩
  have hB₁L : B₁ ≤ linSub := by
    rintro _ ⟨b, hb, rfl⟩
    exact linSub.mul_mem (linSub.mul_mem hc₀L hb.2) (linSub.inv_mem hc₀L)
  have hB₁ab : ∀ a ∈ B₁, ∀ b ∈ B₁, a * b = b * a := by
    rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    rw [← map_mul, ← map_mul, hBab a ha.1 b hb.1]
  have hperm₁ : (B₁ : Set (MulAut (StdMod (Fin 3) K))) * (U₁ : Set (MulAut (StdMod (Fin 3) K))) =
      (U₁ : Set (MulAut (StdMod (Fin 3) K))) * B₁ := by
    rw [← hU₁, hB₁, Subgroup.coe_map, Subgroup.coe_map, ← Set.image_mul, hperm, Set.image_mul]
  have hU₁eq : U₁ = (uiSub n K).map matHom := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨x, hx, rfl⟩
    · rintro ⟨x, hx, rfl⟩
      exact ⟨⟨x, uiSub_le hx⟩, hx, rfl⟩
  set B₂ := B₁.comap matHom with hB₂
  have hB₂map : B₂.map matHom = B₁ := Subgroup.map_comap_eq_self (by
    intro z hz
    obtain ⟨A, rfl⟩ := exists_matAut_of_mem_linSub (hB₁L hz)
    exact ⟨A, rfl⟩)
  have hperm₂ : (B₂ : Set (GL (Fin 3) K)) * (uiSub n K : Set (GL (Fin 3) K)) =
      (uiSub n K : Set (GL (Fin 3) K)) * B₂ := by
    apply (Set.image_injective.mpr (matHom_injective (ι := Fin 3) (K := K)))
    rw [Set.image_mul, Set.image_mul, ← Subgroup.coe_map, ← Subgroup.coe_map, hB₂map, ← hU₁eq,
      hperm₁]
  set ω := (MulAut.conj (wittGL⁻¹ : GL (Fin 3) K)).toMonoidHom with hω
  set B₃ := B₂.map ω with hB₃
  have hU₃ : (uiSub n K).map ω = ujSub n K := by
    rw [uiSub, Subgroup.map_map]
    convert Subgroup.map_id (ujSub n K)
    refine MonoidHom.ext fun x => ?_
    change wittGL⁻¹ * (wittGL * x * wittGL⁻¹) * wittGL⁻¹⁻¹ = x
    group
  have hperm₃ : (B₃ : Set (GL (Fin 3) K)) * (ujSub n K : Set (GL (Fin 3) K)) =
      (ujSub n K : Set (GL (Fin 3) K)) * B₃ := by
    rw [← hU₃, hB₃, Subgroup.coe_map, Subgroup.coe_map, ← Set.image_mul, hperm₂, Set.image_mul]
  have hB₃ab : ∀ a ∈ B₃, ∀ b ∈ B₃, a * b = b * a := by
    rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    rw [← map_mul, ← map_mul]
    congr 1
    apply matHom_injective
    rw [map_mul, map_mul]
    exact hB₁ab _ ha _ hb
  have hB₃odd : Odd (Nat.card B₃) := by
    have h1 : Nat.card B₃ = Nat.card B₂ :=
      Subgroup.card_map_of_injective (MulAut.conj (wittGL⁻¹ : GL (Fin 3) K)).injective
    have h2 : Nat.card B₂ = Nat.card B₁ := by
      rw [← hB₂map]
      exact (Subgroup.card_map_of_injective matHom_injective).symm
    have h3 : Nat.card B₁ = Nat.card ↥(B ⊓ linSub) :=
      Subgroup.card_map_of_injective (MulAut.conj c₀).injective
    have h4 : Nat.card ↥(B ⊓ linSub) ∣ Nat.card B := Subgroup.card_dvd_of_le inf_le_left
    rw [h1, h2, h3]
    exact Odd.of_dvd_nat hBodd h4
  have htri : B₃ ≤ Tri.borGL 3 K :=
    Tri.triangular_three_of hK4 ujSub_le_uni3 (exists_ujSub_zero_one hn1 hK)
      (exists_ujSub_one_two hn1 hK) inf_le_left inf_le_right
      (le_trans hq (card_ujSub_inf_rootGL hn1 hK)) hB₃ab hB₃odd hperm₃
  have hz : ∀ z ∈ B₁, z ^ (Nat.card K - 1) = 1 := by
    intro z hz
    obtain ⟨A, rfl⟩ := exists_matAut_of_mem_linSub (hB₁L hz)
    have hA2 : A ∈ B₂ := hz
    have hA3 : ω A ∈ B₃ := ⟨A, hA2, rfl⟩
    have hodd : Odd (orderOf (ω A)) := Odd.of_dvd_nat hB₃odd (Subgroup.orderOf_dvd_natCard B₃ hA3)
    have h1 := Tri.pow_card_sub_one_eq_one (htri hA3) hodd
    rw [← map_pow] at h1
    have h2 : A ^ (Nat.card K - 1) = 1 :=
      (MulAut.conj (wittGL⁻¹ : GL (Fin 3) K)).injective (h1.trans (map_one _).symm)
    rw [← matHom_apply, ← map_pow, h2, map_one]
  obtain ⟨y, hy⟩ := hY.exists_generator
  have hyo : orderOf (y : MulAut (StdMod (Fin 3) K)) = 2 ^ c - 1 := by
    rw [Subgroup.orderOf_coe, orderOf_eq_card_of_forall_mem_zpowers hy, hYc]
  have hyB : (y : MulAut (StdMod (Fin 3) K)) ∈ B := hYB y.2
  obtain ⟨σ, hσ⟩ := exists_semilinear (hasScalarCommutant' hn1 hK) (hBN hyB)
  have : Finite (K ≃+* K) := Finite.of_injective (fun τ : K ≃+* K => (τ : K → K))
    (fun _ _ h => RingEquiv.ext (congrFun h))
  set m := orderOf σ with hm
  have hmn : m ∣ 2 * n := by
    obtain ⟨-, -, -, -, hcard, -⟩ :=
      finite_field_automorphism_fixed_field_cardinality Nat.prime_two (by omega)
        (card_eq_two_pow hK)
    rw [← hcard]
    exact orderOf_dvd_natCard σ
  have hm0 : 0 < m := orderOf_pos σ
  have hym : (y : MulAut (StdMod (Fin 3) K)) ^ m ∈ B ⊓ linSub := by
    refine ⟨B.pow_mem hyB m, ?_⟩
    have h' := hσ.pow m
    rw [hm, pow_orderOf_eq_one] at h'
    exact h'
  have hypow : (y : MulAut (StdMod (Fin 3) K)) ^ (m * (Nat.card K - 1)) = 1 := by
    have h1 := hz _ ⟨_, hym, rfl⟩
    change (c₀ * (y : MulAut (StdMod (Fin 3) K)) ^ m * c₀⁻¹) ^ (Nat.card K - 1) = 1 at h1
    rw [conj_pow, conj_eq_one_iff] at h1
    rw [pow_mul]
    exact h1
  have hdvd : 2 ^ c - 1 ∣ m * (2 ^ (2 * n) - 1) := by
    rw [← hyo, ← card_eq_two_pow hK]
    exact orderOf_dvd_of_pow_eq_one hypow
  exact SL3Pair.le_of_dvd_mul_pow_sub_one (by omega) hm0 (Nat.le_of_dvd (by omega) hmn) hdvd

theorem nPrime_le (hn : 2 ≤ n) (hK : Nat.card K = (2 ^ n) ^ 2)
    {X : Subgroup (MulAut (StdMod (Fin 3) K))} (hX1 : natImage (StatedSU 3 (2 ^ n) K) ≤ X)
    (hX2 : X ≤ natNorm (StatedSU 3 (2 ^ n) K)) : E3.nPrime X ≤ 2 * n := by
  have : Finite (MulAut (StdMod (Fin 3) K)) := MulEquiv.finite_left
  unfold E3.nPrime
  refine csSup_le ⟨1, ⊥, ⊥, (E1.exists_isSylowIn_two X).choose, bot_le, bot_le, inferInstance,
    by simp, fun a ha b hb => ?_, by simp, (E1.exists_isSylowIn_two X).choose_spec, by simp⟩ ?_
  · rw [Subgroup.mem_bot.1 ha, Subgroup.mem_bot.1 hb]
  · rintro c ⟨Y, B, S, hYB, hBX, hY, hYc, hBab, hBodd, hS, hBS⟩
    exact le_of_permutes hn hK hX1 hX2 hYB hBX hY hYc hBab hBodd hS hBS

end SU3

end H

end CFSG.Quasithin
