module

public import CFSG.Permutation.UnitaryThreeRecognition.HeisMain
public import CFSG.Permutation.UnitaryThreeRecognition.HeisCoord

public section

namespace CFSG.UnitaryThreeRecognition.Heisenberg

open CFSG.UnitaryThreeRecognition.Model CFSG.BenderSuzuki.MatrixGroups

theorem units_inv_pow_eq {K : Type*} [Field K] (J : HermitianForm 3 K) {q : ℕ} (hq : 1 ≤ q)
    (hconj : ∀ x, J.conj x = x ^ q) (k : Kˣ) :
    (((k ^ (2 * q - 1))⁻¹ : Kˣ) : K) = (k : K) * (J.conj (k : K))⁻¹ ^ 2 := by
  have hk : (k : K) ≠ 0 := Units.ne_zero k
  have e : (k : K) ^ (2 * q - 1) * (k : K) = ((k : K) ^ q) ^ 2 := by
    rw [← pow_succ, ← pow_mul, show 2 * q - 1 + 1 = q * 2 by omega]
  rw [hconj, Units.val_inv_eq_inv_val, Units.val_pow_eq_pow_val, inv_pow, ← e]
  field_simp

namespace Hyp

variable {G : Type*} [Group G] [Finite G] {Q T Z W : Subgroup G} {p f d : ℕ} [Fact p.Prime]
  (S : Hyp Q T Z W p f d)
include S

theorem exists_torus_param {K : Type*} [Field K] [Finite K] (J : HermitianForm 3 K)
    (hK : Nat.card K = (p ^ f) ^ 2) (hconj : ∀ x, J.conj x = x ^ (p ^ f)) (ψ : S.A ≃+* K) :
    (∀ t : T, ∃ k : Kˣ, ψ (S.tau t : S.A) = (k : K) * (J.conj (k : K))⁻¹ ^ 2) ∧
      (∀ k : Kˣ, ∃ t : T, ψ (S.tau t : S.A) = (k : K) * (J.conj (k : K))⁻¹ ^ 2) := by
  have hq3 := S.three_le_q
  let u : S.Aˣ →* Kˣ := Units.map ψ.toRingHom.toMonoidHom
  have hu : Function.Injective u := fun a b h =>
    Units.ext (ψ.injective (congrArg Units.val h))
  have hRcard : Nat.card (S.tau.range.map u) = Nat.card T := by
    rw [Subgroup.card_map_of_injective hu,
      Nat.card_congr (MonoidHom.ofInjective S.tau_injective).toEquiv.symm]
  have hKu : Nat.card Kˣ = (p ^ f) ^ 2 - 1 := by rw [Nat.card_units, hK]
  have hgcd : Nat.gcd (Nat.card Kˣ) (2 * p ^ f - 1) = d := by
    rw [hKu, gcd_sq_sub_one_two_mul_sub_one (p ^ f) (by omega), S.hd]
  have hT : Nat.card T = ((p ^ f) ^ 2 - 1) / d := by
    have h := S.hTcard
    rw [pow_mul'] at h
    exact (Nat.div_eq_of_eq_mul_left S.d_pos h.symm).symm
  have hR : S.tau.range.map u = (powMonoidHom (2 * p ^ f - 1) : Kˣ →* Kˣ).range :=
    eq_range_powMonoidHom _ _ (by rw [hRcard, hT, hgcd, hKu])
  have key := units_inv_pow_eq J (by omega) hconj
  constructor
  · intro t
    have hmem : (u (S.tau t))⁻¹ ∈ S.tau.range.map u :=
      Subgroup.inv_mem _ (Subgroup.mem_map_of_mem u ⟨t, rfl⟩)
    rw [hR] at hmem
    obtain ⟨k, hk⟩ := hmem
    refine ⟨k, ?_⟩
    rw [← key]
    have h1 : u (S.tau t) = (k ^ (2 * p ^ f - 1))⁻¹ := by
      rw [powMonoidHom_apply] at hk
      rw [hk, inv_inv]
    exact congrArg Units.val h1
  · intro k
    have hmem : (k ^ (2 * p ^ f - 1))⁻¹ ∈ S.tau.range.map u := by
      rw [hR]
      exact Subgroup.inv_mem _ ⟨k, rfl⟩
    obtain ⟨τ', ⟨t, rfl⟩, ht⟩ := hmem
    refine ⟨t, ?_⟩
    rw [← key, ← ht]
    rfl

end Hyp

theorem heisenberg_coordinates
    {G : Type*} [Group G] [Finite G] (Q T Z W : Subgroup G)
    {p f d : ℕ} [Fact p.Prime] (hpodd : p ≠ 2) (hf : 1 ≤ f) (hd : d = Nat.gcd (p ^ f + 1) 3)
    (hTQ : ∀ t ∈ T, ∀ x ∈ Q, t * x * t⁻¹ ∈ Q)
    (hTcomm : ∀ t₁ ∈ T, ∀ t₂ ∈ T, t₁ * t₂ = t₂ * t₁)
    (hZQ : Z ≤ Q) (hZcent : ∀ x ∈ Q, ∀ z ∈ Z, x * z = z * x)
    (hcomm : ∀ x ∈ Q, ∀ y ∈ Q, x * y * x⁻¹ * y⁻¹ ∈ Z)
    (hexp : ∀ x ∈ Q, x ^ p = 1)
    (hnonab : ∃ x ∈ Q, ∃ y ∈ Q, x * y ≠ y * x)
    (hTZ : ∀ t ∈ T, ∀ z ∈ Z, t * z * t⁻¹ ∈ Z)
    (hfree : ∀ t ∈ T, t ≠ 1 → ∀ x ∈ Q, t * x = x * t → x ∈ Z)
    (hTZtrans : ∀ z₁ ∈ Z, ∀ z₂ ∈ Z, z₁ ≠ 1 → z₂ ≠ 1 → ∃ t ∈ T, t * z₁ * t⁻¹ = z₂)
    (hWT : W ≤ T) (hWZ : ∀ w ∈ W, ∀ z ∈ Z, w * z = z * w)
    (hirr : ∀ N : Subgroup G, Z ≤ N → N ≤ Q → (∀ t ∈ T, ∀ x ∈ N, t * x * t⁻¹ ∈ N) →
      N = Z ∨ N = Q)
    (hQcard : Nat.card Q = p ^ (3 * f)) (hZcard : Nat.card Z = p ^ f)
    (hTcard : Nat.card T * d = p ^ (2 * f) - 1) (hWcard : Nat.card W * d = p ^ f + 1)
    {K : Type} [Field K] [Finite K] (J : HermitianForm 3 K)
    (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0])
    (hK : Nat.card K = (p ^ f) ^ 2) (hconj : ∀ x, J.conj x = x ^ (p ^ f)) :
    ∃ φ : Q ≃* Coord J,
      (∀ t (ht : t ∈ T), ∃ k : Kˣ, ∀ x : Q,
        φ ⟨t * x * t⁻¹, hTQ t ht x x.2⟩ =
          CFSG.BenderSuzuki.External.hermitianTorusAction J k (φ x)) ∧
      (∀ k : Kˣ, ∃ t, ∃ ht : t ∈ T, ∀ x : Q,
        φ ⟨t * x * t⁻¹, hTQ t ht x x.2⟩ =
          CFSG.BenderSuzuki.External.hermitianTorusAction J k (φ x)) ∧
      (∀ z : Q, (z : G) ∈ Z ↔ (φ z : K × K).1 = 0) := by
  have _ := hJ
  have S : Hyp Q T Z W p f d := ⟨hpodd, hf, hd, hTQ, hTcomm, hZQ, hZcent, hcomm, hexp, hnonab,
    hTZ, hfree, hTZtrans, hWT, hWZ, hirr, hQcard, hZcard, hTcard, hWcard⟩
  have := S.charP_A
  let : Fintype S.A := Fintype.ofFinite _
  let : Fintype K := Fintype.ofFinite _
  have hcardAK : Fintype.card S.A = Fintype.card K := by
    rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, S.card_A, hK]
  let ψ : S.A ≃+* K := FiniteField.ringEquivOfCardEq hcardAK
  have hψconj : ∀ c : S.A, ψ (c ^ p ^ f) = J.conj (ψ c) := fun c => by rw [map_pow, hconj]
  have h2K : (2 : K) ≠ 0 := by
    rw [← map_ofNat ψ 2]
    exact (map_ne_zero ψ).mpr S.two_ne_zero_A
  obtain ⟨φ, hφ⟩ := exists_mulEquiv_coord J h2K (fun x => ψ (S.aA x)) (fun x => ψ (S.cA x))
    (fun x y => by simp only [S.aA_mul, map_add])
    (fun x y => by
      rw [S.cA_mul, map_add, map_add, map_div₀, map_sub, map_mul, map_mul, hψconj, hψconj,
        map_ofNat])
    (fun x => by rw [← hψconj, S.cA_frob, map_neg])
    (fun x ha hc => S.eq_one_of_aA_cA x ((map_eq_zero_iff ψ ψ.injective).mp ha)
      ((map_eq_zero_iff ψ ψ.injective).mp hc))
    (fun a₀ c₀ hc₀ => by
      have hc₀' : (ψ.symm c₀) ^ p ^ f = -ψ.symm c₀ := by
        apply ψ.injective
        rw [hψconj, RingEquiv.apply_symm_apply, map_neg, RingEquiv.apply_symm_apply, hc₀]
      obtain ⟨x, hxa, hxc⟩ := S.exists_aA_cA (ψ.symm a₀) (ψ.symm c₀) hc₀'
      exact ⟨x, by simp only [hxa, RingEquiv.apply_symm_apply],
        by simp only [hxc, RingEquiv.apply_symm_apply]⟩)
  have htorus : ∀ (t : G) (ht : t ∈ T) (k : Kˣ),
      ψ (S.tau ⟨t, ht⟩ : S.A) = (k : K) * (J.conj (k : K))⁻¹ ^ 2 → ∀ x : Q,
        φ ⟨t * x * t⁻¹, hTQ t ht x x.2⟩ =
          CFSG.BenderSuzuki.External.hermitianTorusAction J k (φ x) := by
    intro t ht k hk x
    have hx : (⟨t * x * t⁻¹, hTQ t ht x x.2⟩ : Q) = S.conjQ ⟨t, ht⟩ x := rfl
    apply eq_hermitianTorusAction J (ψ (S.tau ⟨t, ht⟩ : S.A)) hk
    · rw [hx, hφ, hφ]
      simp only
      rw [S.aA_conjQ, map_mul, mul_comm]
    · rw [hx, hφ, hφ]
      simp only
      rw [S.cA_conjQ, S.aA_conjQ, map_mul, map_mul, map_mul, map_mul, hψconj]
      ring
  obtain ⟨hT1, hT2⟩ := S.exists_torus_param J hK hconj ψ
  refine ⟨φ, ?_, ?_, ?_⟩
  · intro t ht
    obtain ⟨k, hk⟩ := hT1 ⟨t, ht⟩
    exact ⟨k, htorus t ht k hk⟩
  · intro k
    obtain ⟨⟨t, ht⟩, hk⟩ := hT2 k
    exact ⟨t, ht, htorus t ht k hk⟩
  · intro z
    rw [hφ, S.mem_Z_iff]
    exact (map_eq_zero_iff ψ ψ.injective).symm

end CFSG.UnitaryThreeRecognition.Heisenberg
