module

public import CFSG.Quasithin.Vol2.Ch11G2Q8ParG2
public import CFSG.Quasithin.Background.HSL3PairNPrime
public import CFSG.Quasithin.Vol2.Ch11SecBK5Base11

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecB.K5

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.H CFSG.Quasithin.JonesParshall
  CFSG.Quasithin.Explicit CFSG.Quasithin.Vol2.KGNat CFSG.Quasithin.Vol2.Ch11.G2Q8
open scoped Pointwise

variable {K : Type} [Field K] [CharP K 2]


theorem exists_smul_of_mem_linSub [Finite K] {n : ℕ} (hK : Nat.card K = 2 ^ n) (hn : 2 ≤ n)
    {x : MulAut (StdMod Ix3 K)} (hxN : x ∈ natNorm (g2Gam K)) (hxL : x ∈ linSub) :
    ∃ (c : K) (g : ↥(cayleyGroup K)), c ≠ 0 ∧ ∀ v, toAddMap x v = c • g2Act g v := by
  have hxL' : IsSemilinear x (RingEquiv.refl K) := hxL
  let T : (Ix3 → K) ≃ₗ[K] (Ix3 → K) :=
    { toFun := toAddMap x
      invFun := toAddMap x⁻¹
      map_add' := toAddMap_add x
      map_smul' := fun c v => hxL' c v
      left_inv := toAddMap_apply_inv x
      right_inv := toAddMap_inv_apply x }
  refine exists_eq_smul_of_normG2 hK hn T fun γ => ?_
  have hmem : x * g2Rho γ * x⁻¹ ∈ natImage (g2Gam K) :=
    (Subgroup.mem_normalizer_iff.mp hxN _).mp (g2Rho_mem_natImage γ)
  rw [← range_g2Rho] at hmem
  obtain ⟨γ', hγ'⟩ := hmem
  refine ⟨γ', fun w => ?_⟩
  have h1 : x * g2Rho γ = g2Rho γ' * x := by
    rw [hγ']
    group
  have h2 := congrArg (fun y => toAddMap y w) h1
  simp only [toAddMap_mul, toAddMap_g2Rho] at h2
  exact h2

theorem toAddMap_pow_of_smul {x : MulAut (StdMod Ix3 K)} {c : K} {g : ↥(cayleyGroup K)}
    (hx : ∀ v, toAddMap x v = c • g2Act g v) (k : ℕ) (v : Ix3 → K) :
    toAddMap (x ^ k) v = c ^ k • g2Act (g ^ k) v := by
  induction k generalizing v with
  | zero =>
    rw [pow_zero, pow_zero, pow_zero, one_smul, map_one, toAddMap_one]
    rfl
  | succ k ih =>
    calc toAddMap (x ^ (k + 1)) v = toAddMap (x ^ k) (toAddMap x v) := by
          rw [pow_succ, toAddMap_mul]
      _ = c ^ k • g2Act (g ^ k) (c • g2Act g v) := by rw [hx, ih]
      _ = c ^ (k + 1) • g2Act (g ^ (k + 1)) v := by
          rw [JonesParshall.g2Act_smul, smul_smul, pow_succ, pow_succ, g2Act_mul_apply]

theorem mem_natImage_of_pow_two [Finite K] {n : ℕ} (hK : Nat.card K = 2 ^ n) (hn : 2 ≤ n)
    {s : MulAut (StdMod Ix3 K)} (hsN : s ∈ natNorm (g2Gam K)) (hsL : s ∈ linSub) {j : ℕ}
    (hsj : s ^ 2 ^ j = 1) : s ∈ natImage (g2Gam K) := by
  obtain ⟨c, g, hc, hsg⟩ := exists_smul_of_mem_linSub hK hn hsN hsL
  have hcj : c ^ 2 ^ j ≠ 0 := pow_ne_zero _ hc
  have h1 : ∀ v, g2Act (g ^ 2 ^ j) v = (c ^ 2 ^ j)⁻¹ • v := by
    intro v
    have h0 := toAddMap_pow_of_smul hsg (2 ^ j) v
    rw [hsj, toAddMap_one] at h0
    calc g2Act (g ^ 2 ^ j) v = (c ^ 2 ^ j)⁻¹ • (c ^ 2 ^ j • g2Act (g ^ 2 ^ j) v) := by
          rw [smul_smul, inv_mul_cancel₀ hcj, one_smul]
      _ = (c ^ 2 ^ j)⁻¹ • v := by rw [← h0]
  have h3 : c ^ 2 ^ j = 1 := inv_eq_one.mp (scalar_eq_one h1)
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h4 : (c - 1) ^ 2 ^ j = 0 := by rw [sub_pow_char_pow, h3, one_pow, sub_self]
  have hc1 : c = 1 := sub_eq_zero.mp ((pow_eq_zero_iff (by positivity)).mp h4)
  have hsg' : s = g2Rho g := toAddMap_injective fun v => by
    rw [hsg, hc1, one_smul, toAddMap_g2Rho]
  rw [hsg']
  exact g2Rho_mem_natImage g

theorem permute_lin_G2 [Finite K] {n : ℕ} (hK : Nat.card K = 2 ^ n) (hn : 2 ≤ n)
    {B S : Subgroup (MulAut (StdMod Ix3 K))}
    (hBN : B ≤ natNorm (g2Gam K)) (hSN : S ≤ natNorm (g2Gam K))
    (hBodd : Odd (Nat.card B)) (hS : IsPGroup 2 S)
    (hBS : (B : Set (MulAut (StdMod Ix3 K))) * S = S * B) :
    ((B ⊓ linSub : Subgroup (MulAut (StdMod Ix3 K))) : Set (MulAut (StdMod Ix3 K))) *
        ((S ⊓ natImage (g2Gam K) : Subgroup (MulAut (StdMod Ix3 K))) :
          Set (MulAut (StdMod Ix3 K))) =
      ((S ⊓ natImage (g2Gam K) : Subgroup (MulAut (StdMod Ix3 K))) :
          Set (MulAut (StdMod Ix3 K))) *
        ((B ⊓ linSub : Subgroup (MulAut (StdMod Ix3 K))) : Set (MulAut (StdMod Ix3 K))) := by
  classical
  have hΓ := hasScalarCommutant_g2Gam (K := K)
  have : Finite (MulAut (StdMod Ix3 K)) := MulEquiv.finite_left
  apply SL3Pair.mul_comm_of_subset
  rintro _ ⟨u, hu, b, hb, rfl⟩
  have huL : u ∈ linSub := natImage_le_linSub _ hu.2
  have hub : u * b ∈ (S : Set (MulAut (StdMod Ix3 K))) * B := Set.mul_mem_mul hu.1 hb.1
  rw [← hBS] at hub
  obtain ⟨b', hb', s, hs, hbs⟩ := hub
  have hbs' : b' * s = u * b := hbs
  have hubL : u * b ∈ linSub := linSub.mul_mem huL hb.2
  let φ := fieldHom hΓ
  have hb'k : b' ^ Nat.card B = 1 :=
    orderOf_dvd_iff_pow_eq_one.mp (Subgroup.orderOf_dvd_natCard B hb')
  obtain ⟨j, hj⟩ := hS ⟨s, hs⟩
  have hsj : s ^ 2 ^ j = 1 := congrArg Subtype.val hj
  have hσ1 : φ ⟨b', hBN hb'⟩ = 1 := by
    have h1 : φ ⟨b', hBN hb'⟩ * φ ⟨s, hSN hs⟩ = 1 := by
      rw [← map_mul]
      have hm : u * b ∈ natNorm (g2Gam K) := by
        rw [← hbs']
        exact (natNorm _).mul_mem (hBN hb') (hSN hs)
      have : (⟨b', hBN hb'⟩ * ⟨s, hSN hs⟩ : ↥(natNorm (g2Gam K))) = ⟨u * b, hm⟩ :=
        Subtype.ext hbs'
      rw [this]
      exact (fieldHom_eq_one_iff hΓ _).mpr hubL
    have h2 : φ ⟨b', hBN hb'⟩ ^ Nat.card B = 1 := by
      rw [← map_pow]
      have : (⟨b', hBN hb'⟩ : ↥(natNorm (g2Gam K))) ^ Nat.card B = 1 :=
        Subtype.ext (by simpa using hb'k)
      rw [this, map_one]
    have h3 : φ ⟨b', hBN hb'⟩ ^ 2 ^ j = 1 := by
      have h4 : φ ⟨s, hSN hs⟩ ^ 2 ^ j = 1 := by
        rw [← map_pow]
        have : (⟨s, hSN hs⟩ : ↥(natNorm (g2Gam K))) ^ 2 ^ j = 1 :=
          Subtype.ext (by simpa using hsj)
        rw [this, map_one]
      rw [eq_inv_of_mul_eq_one_left h1, inv_pow, h4, inv_one]
    have hcop : Nat.Coprime (Nat.card B) (2 ^ j) :=
      Nat.Coprime.pow_right j (Nat.coprime_two_right.mpr hBodd)
    exact orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes hcop
      (orderOf_dvd_of_pow_eq_one h2) (orderOf_dvd_of_pow_eq_one h3))
  have hb'L : b' ∈ linSub := (fieldHom_eq_one_iff hΓ _).mp hσ1
  have hse : s = b'⁻¹ * (u * b) := by rw [← hbs']; group
  have hsL : s ∈ linSub := by
    rw [hse]
    exact linSub.mul_mem (linSub.inv_mem hb'L) hubL
  exact ⟨b', ⟨hb', hb'L⟩, s, ⟨hs, mem_natImage_of_pow_two hK hn (hSN hs) hsL hsj⟩, hbs⟩

end CFSG.Quasithin.Vol2.Ch11.SecB.K5
