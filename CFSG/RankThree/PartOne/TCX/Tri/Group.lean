module

public import CFSG.RankThree.PartOne.TCX.Tri.E2Sector
public import CFSG.RankThree.PartOne.TCX.Tri.E36Sector
public import CFSG.RankThree.PartOne.TCX.Tri.PlaneSplit
public import CFSG.RankThree.PartOne.TCX.Tri.Shintani
public import CFSG.RankThree.PartOne.TCX.Generator
public import CFSG.RankThree.PartOne.K128.D4Arith

public section

namespace CFSG.RankThree.PartOne.TCX.Tri

open Subgroup CFSG CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.RankThree.PartOne CFSG.RankThree.PartOne.K128 CFSG.RankThree.PartOne.KLCE
open CFSG.RankThree.PartOne.TCX


section Context

theorem tri_sector_context {K : Type} [Field K] [Finite K] {p f₀ : ℕ} (hp : p.Prime)
    (hp5 : 5 ≤ p) (hf₀ : 1 ≤ f₀) (hK : Nat.card K = (2 ^ (p * f₀)) ^ 3) {σ δ₀ : K ≃+* K}
    (hσ : ∀ c, σ c = c ^ 2 ^ (p * f₀)) (hδ₀ : ∀ c, δ₀ c = c ^ 2 ^ (3 * f₀))
    (hδ₀ord : orderOf δ₀ = p) :
    ∃ (L : Type) (_ : Field L) (_ : Algebra K L) (_ : CharP L 2) (_ : IsAlgClosed L)
      (_ : IsAlgClosure K L) (α₀ : MulAut (graphFixedRootGroup TwistTag.D4 K σ.toRingHom))
      (k : Type) (_ : Field k) (_ : Finite k) (_ : Algebra k L) (_ : IsAlgClosure k L)
      (σk : k ≃+* k),
      IsShintani p (triIota L p σ) (triF0 L f₀) (triPhi L p f₀) α₀ ∧ α₀ ^ p = 1 ∧
        Subgroup.zpowers α₀ = Subgroup.zpowers (fieldActor (t := TwistTag.D4) σ δ₀) ∧
        (∀ t ∈ torusGroup TwistTag.D4.tag L, ∃ m : ℕ, Odd m ∧ t ^ m = 1) ∧
        Nat.card k = (2 ^ f₀) ^ 3 ∧ (∀ c, σk c = c ^ 2 ^ f₀) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hp3 : p % 3 = 1 ∨ p % 3 = 2 := by
    have h3 : ¬ 3 ∣ p := fun h => by
      have := (Nat.prime_dvd_prime_iff_eq Nat.prime_three hp).1 h
      omega
    omega
  have hpf : 1 ≤ p * f₀ := Nat.mul_pos hp.pos hf₀
  have hK' : Nat.card K = 2 ^ (3 * (p * f₀)) := by rw [hK, ← pow_mul, mul_comm]
  have : CharP K 2 :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic Nat.prime_two
      (by omega : 1 ≤ 3 * (p * f₀)) hK'
  let L := AlgebraicClosure K
  have : CharP L 2 := charP_of_injective_algebraMap (algebraMap K L).injective 2
  have : IsAlgClosed L := IsAlgClosure.isAlgClosed K
  have : Algebra.IsAlgebraic K L := IsAlgClosure.isAlgebraic
  obtain ⟨ε, hα, hεp, hzp⟩ := tri_setup hp hp5 hf₀ hK σ δ₀ hσ hδ₀ hδ₀ord L
  have hsh := triShintani (L := L) hp3 hpf hK σ hσ (α₀ := fieldActor σ ε) hα
  have hK'' : Nat.card K = 2 ^ (p * (3 * f₀)) := by rw [hK', show 3 * (p * f₀) = p * (3 * f₀) by ring]
  obtain ⟨k, _, _, _, hk⟩ := exists_subfield_of_frobenius hp (by omega : 1 ≤ 3 * f₀) hK'' hδ₀ord
  obtain ⟨_, hst, hac⟩ := exists_tower_algebra (K₀ := k) (K := K) (L := L)
  have : CharP k 2 := ⟨fun x => by
    rw [← (algebraMap k K).injective.eq_iff, map_natCast, map_zero]
    exact CharP.cast_eq_zero_iff K 2 x⟩
  let σk : k ≃+* k := RingEquiv.ofBijective (iterateFrobenius k 2 f₀)
    ⟨(iterateFrobenius k 2 f₀).injective, Finite.surjective_of_injective
      (iterateFrobenius k 2 f₀).injective⟩
  refine ⟨L, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
    fieldActor σ ε, k, inferInstance, inferInstance, inferInstance, hac, σk, hsh, hεp, hzp,
    fun t ht => exists_odd_pow_eq_one_of_mem_torusGroup (K := K) ht, ?_, fun c => ?_⟩
  · rw [hk, ← pow_mul, mul_comm]
  · exact iterateFrobenius_def 2 f₀ c

end Context


section Cases


theorem tri_group_cases {K : Type} [Field K] [Finite K] {p f₀ : ℕ} (hp : p.Prime)
    (hp5 : 5 ≤ p) (hf₀ : 1 ≤ f₀) (hK : Nat.card K = (2 ^ (p * f₀)) ^ 3) {σ δ₀ : K ≃+* K}
    (hσ : ∀ c, σ c = c ^ 2 ^ (p * f₀)) (hδ₀ : ∀ c, δ₀ c = c ^ 2 ^ (3 * f₀))
    (hδ₀ord : orderOf δ₀ = p) {m : ℕ} (hm : m = 1 ∨ m = 2 ∨ m = 3 ∨ m = 6)
    (hpd : p ∣ phiNat m (2 ^ f₀)) {x : graphFixedRootGroup TwistTag.D4 K σ.toRingHom}
    (hx : orderOf x = p) (hxα : fieldActor (t := TwistTag.D4) σ δ₀ x = x) :
    (∃ R U : Subgroup (graphFixedRootGroup TwistTag.D4 K σ.toRingHom),
        IsElementaryAbelian p ↥R ∧ Nat.card ↥R = p ^ 2 ∧
          (∀ r ∈ R, fieldActor (t := TwistTag.D4) σ δ₀ r = r) ∧ U ≠ ⊥ ∧ IsPGroup 2 ↥U ∧
          (∀ u ∈ U, fieldActor (t := TwistTag.D4) σ δ₀ u ∈ U) ∧
          R ≤ Subgroup.normalizer (U : Set (graphFixedRootGroup TwistTag.D4 K σ.toRingHom))) ∨
      RegularShape (2 ^ (p * f₀)) x ∨
        SingleLayerData p (fieldActor (t := TwistTag.D4) σ δ₀)
          (Subgroup.centralizer ({x} : Set (graphFixedRootGroup TwistTag.D4 K σ.toRingHom))) := by
  classical
  have h2f : 1 ≤ 2 ^ f₀ := Nat.one_le_two_pow
  have hle : 2 ^ f₀ ≤ (2 ^ f₀) ^ 2 := Nat.le_self_pow (by norm_num) _
  rcases hm with rfl | rfl | rfl | rfl
  ·
    left
    simp only [phiNat] at hpd
    exact tri_plane_split hp hf₀ hK hσ hδ₀ hpd
  ·
    right
    simp only [phiNat] at hpd
    obtain ⟨L, _, _, _, _, _, α₀, k, _, _, _, _, σk, hsh, hα₀p, hzp, hodd, hkc, hσk⟩ :=
      tri_sector_context hp hp5 hf₀ hK hσ hδ₀ hδ₀ord
    have hxα₀ : α₀ x = x := fixed_of_zpowers_eq hzp hxα
    have hpq : (p : ℤ) ∣ ((2 ^ f₀ : ℕ) : ℤ) + 1 := by
      have := Int.natCast_dvd_natCast.2 hpd
      push_cast at this ⊢
      exact this
    rcases tri_sector_e2 hsh hp hp5 hf₀ hodd σk hkc hσk hpq hx hxα₀ with h | h
    · exact Or.inl h
    · exact Or.inr (singleLayerData_of_zpowers_eq hp.pos hzp.symm hα₀p h)
  ·
    right
    simp only [phiNat] at hpd
    obtain ⟨L, _, _, _, _, _, α₀, k, _, _, _, _, σk, hsh, hα₀p, hzp, hodd, hkc, hσk⟩ :=
      tri_sector_context hp hp5 hf₀ hK hσ hδ₀ hδ₀ord
    have hxα₀ : α₀ x = x := fixed_of_zpowers_eq hzp hxα
    have hpd' : (p : ℤ) ∣ ((2 ^ f₀ : ℕ) : ℤ) ^ 2 + 1 * ((2 ^ f₀ : ℕ) : ℤ) + 1 := by
      have := Int.natCast_dvd_natCast.2 hpd
      push_cast at this
      rw [one_mul]
      exact this
    rcases tri_sector_e36 hsh hp hp5 hf₀ hodd σ hK hσ σk hkc hσk (ε := 1) (Or.inl rfl) hpd' hx
      hxα₀ with h | h
    · exact Or.inl h
    · exact Or.inr (singleLayerData_of_zpowers_eq hp.pos hzp.symm hα₀p h)
  ·
    right
    simp only [phiNat] at hpd
    obtain ⟨L, _, _, _, _, _, α₀, k, _, _, _, _, σk, hsh, hα₀p, hzp, hodd, hkc, hσk⟩ :=
      tri_sector_context hp hp5 hf₀ hK hσ hδ₀ hδ₀ord
    have hxα₀ : α₀ x = x := fixed_of_zpowers_eq hzp hxα
    have hpd' : (p : ℤ) ∣ ((2 ^ f₀ : ℕ) : ℤ) ^ 2 + (-1) * ((2 ^ f₀ : ℕ) : ℤ) + 1 := by
      have h1 := Int.natCast_dvd_natCast.2 hpd
      have h2 : (((2 ^ f₀) ^ 2 - 2 ^ f₀ + 1 : ℕ) : ℤ) =
          ((2 ^ f₀ : ℕ) : ℤ) ^ 2 + (-1) * ((2 ^ f₀ : ℕ) : ℤ) + 1 := by
        push_cast [Nat.cast_sub hle]
        ring
      rwa [h2] at h1
    rcases tri_sector_e36 hsh hp hp5 hf₀ hodd σ hK hσ σk hkc hσk (ε := -1) (Or.inr rfl) hpd' hx
      hxα₀ with h | h
    · exact Or.inl h
    · exact Or.inr (singleLayerData_of_zpowers_eq hp.pos hzp.symm hα₀p h)

end Cases

end CFSG.RankThree.PartOne.TCX.Tri
