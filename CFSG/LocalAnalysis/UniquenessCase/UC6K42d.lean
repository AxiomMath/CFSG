module

public import CFSG.LocalAnalysis.UniquenessCase.UC6K42c
public import CFSG.ThirdParty.QiuzhenCFSG.Theory.Representation.ExtraspecialFixedPoints
public import CFSG.ThirdParty.QiuzhenCFSG.Theory.Representation.RepEquiv
public import CFSG.LocalAnalysis.UniquenessCase.UC6S9

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC6

open Subgroup CFSG.Open
open CFSG.LocalAnalysis.UniquenessCase.UCK (fixV)

theorem shult_card_uc6 {G : Type} [Group G] [Finite G] {ℓ : ℕ} [Fact ℓ.Prime] {V : Type}
    [AddCommGroup V] [Module (ZMod ℓ) V] [Finite V] (K R : Subgroup G) [K.Normal]
    (hKR : K.IsComplement' R) (hcop : Nat.Coprime (Nat.card K) (Nat.card R))
    (hR : (Nat.card R).Prime) (hℓ : ¬ ℓ ∣ Nat.card G) (ρ : Representation (ZMod ℓ) G V)
    (hfaith : Function.Injective ρ) (hirr : ρ.IsIrreducible) (hfix : fixV ρ R = ⊥)
    (hcent : ∀ x ∈ R, x ≠ 1 → ∀ y ∈ K, x * y = y * x → y ∈ (center ↥K).map K.subtype)
    (hZ : ∀ x ∈ R, ∀ z ∈ (center ↥K).map K.subtype, x * z = z * x)
    [CFSG.IsExtraspecial 2 ↥K] {n : ℕ} (hcardK : Nat.card K = 2 ^ (2 * n + 1)) :
    Nat.card R = 2 ^ n + 1 := by
  by_contra hne
  have hRK : R ≤ Subgroup.normalizer (K : Set G) := Subgroup.le_normalizer_of_normal (H := K)
  let φ : R →* MulAut K :=
    K.normalizerMonoidHom.comp (Subgroup.inclusion (K.normalizer_eq_top ▸ le_top))
  let e : K ⋊[φ] R ≃* G := SemidirectProduct.mulEquivSubgroup hKR
  let σ : Representation (ZMod ℓ) (K ⋊[φ] R) V := ρ.comp e.toMonoidHom
  have hσirr : Representation.IsIrreducible σ :=
    (Theory.Representation.RepEquiv.irreducible_iff_group_iso (ρ := σ) (σ := ρ) e
      (by intro g v; rfl)).2 hirr
  haveI : FiniteDimensional (ZMod ℓ) V := Module.Finite.of_finite
  have hσfaith : Function.Injective σ := by
    intro x y hxy
    exact e.injective (hfaith (by simpa [σ] using hxy))
  have hq_dvdK : 2 ∣ Nat.card K := by
    rw [hcardK]
    exact dvd_pow_self 2 (by positivity)
  haveI : Fact (Nat.card R).Prime := ⟨hR⟩
  haveI : IsCyclic ↥R := isCyclic_of_prime_card (p := Nat.card R) rfl
  have hyconj : ∀ (x : R) (y : K), φ x y = y → (x : G) * (y : G) = (y : G) * (x : G) := by
    intro x y hy
    have hyconj : (x : G) * (y : G) * (x : G)⁻¹ = y := by
      simpa [φ, Subgroup.conjMulDistribMulActionOfLeNormalizer_smul_coe, hRK]
        using congrArg Subtype.val hy
    have hmul := congrArg (fun t : G => t * (x : G)) hyconj
    simpa [mul_assoc] using hmul
  have hcentralizer : ∀ x : R, x ≠ 1 → {p : K | φ x p = p} = Subgroup.center (↥K) := by
    intro x hx
    ext y
    constructor
    · intro hy
      have hx1 : (x : G) ≠ 1 := fun h => hx (Subtype.ext h)
      rcases hcent x x.2 hx1 y y.2 (hyconj x y hy) with ⟨z, hz, hz_eq⟩
      have hzy : z = y := K.subtype_injective hz_eq
      simpa [hzy] using hz
    · intro hy
      apply Subtype.ext
      have hmul : (y : G) * (x : G) = (x : G) * (y : G) :=
        (hZ x x.2 y ⟨y, hy, rfl⟩).symm
      have hyconj : (x : G) * (y : G) * (x : G)⁻¹ = y := by
        calc
          (x : G) * (y : G) * (x : G)⁻¹ = ((y : G) * (x : G)) * (x : G)⁻¹ := by
            rw [hmul.symm]
          _ = y := by simp [mul_assoc]
      simpa [φ, Subgroup.conjMulDistribMulActionOfLeNormalizer_smul_coe, hRK] using hyconj
  have hcardG : Nat.card G = Nat.card R * 2 ^ (2 * n + 1) := by
    rw [← hKR.card_mul, hcardK, mul_comm]
  have hc : ¬ ringChar (ZMod ℓ) ∣ Nat.card R * 2 ^ (2 * n + 1) := by
    rw [ZMod.ringChar_zmod_n, ← hcardG]
    exact hℓ
  have hfixed_nonzero : {v | ∀ h : R, σ ⟨1, h⟩ v = v} ≠ ({0} : Set V) :=
    CFSG.theorem_2_5_b (p := 2) (n := n) (P := ↥K) hcardK (h := Nat.card R) (H := ↥R) rfl
      (Nat.Coprime.symm (Nat.Coprime.of_dvd_left hq_dvdK hcop)) (φ := φ) hcentralizer hc hne
      (ρ := σ) hσfaith
  have hfixed_eq : {v | ∀ h : R, σ ⟨1, h⟩ v = v} = {v : V | ∀ h : R, ρ h v = v} := by
    have he_inr : ∀ h : R, e (SemidirectProduct.inr h) = (h : G) := by
      intro h
      simp [e, SemidirectProduct.mulEquivSubgroup, SemidirectProduct.monoidHomSubgroup]
    ext v
    constructor
    · intro hv h
      simpa [σ, he_inr h] using hv h
    · intro hv h
      simpa [σ, he_inr h] using hv h
  have hfix_zero : {v : V | ∀ h : R, ρ h v = v} = ({0} : Set V) := by
    ext v
    constructor
    · intro hv
      have : v ∈ fixV ρ R := fun a ha => hv ⟨a, ha⟩
      rw [hfix] at this
      exact (Submodule.mem_bot _).1 this
    · intro hv h
      rw [Set.mem_singleton_iff.1 hv, map_zero]
  exact hfixed_nonzero (hfixed_eq.trans hfix_zero)

theorem fermat_pow_two_uc6 {r n : ℕ} (hr : r.Prime) (hr2 : r ≠ 2) (h : r = 2 ^ n + 1) :
    ∃ k : ℕ, orderOf (2 : ZMod r) = 2 ^ k := by
  have hn : n ≠ 0 := by
    rintro rfl
    exact hr2 (by simpa using h)
  obtain ⟨m, hm⟩ := Nat.pow_of_pow_add_prime (by norm_num : 1 < 2) hn (h ▸ hr)
  have hneg : (2 : ZMod r) ^ n = -1 := by
    have h0 : ((2 ^ n + 1 : ℕ) : ZMod r) = 0 := by
      rw [← h]
      exact ZMod.natCast_self r
    push_cast at h0
    exact eq_neg_of_add_eq_zero_left h0
  have hpow : (2 : ZMod r) ^ (2 ^ (m + 1)) = 1 := by
    have : 2 ^ (m + 1) = n * 2 := by rw [hm, pow_succ]
    rw [this, pow_mul, hneg]
    norm_num
  obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 (orderOf_dvd_of_pow_eq_one hpow)
  exact ⟨k, hk⟩

end CFSG.LocalAnalysis.UniquenessCase.UC6
