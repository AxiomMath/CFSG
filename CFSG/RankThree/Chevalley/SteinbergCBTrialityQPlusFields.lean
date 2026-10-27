module

public import CFSG.RankThree.Chevalley.SteinbergCBTrialityOrbitSemilinear
public import CFSG.RankThree.Chevalley.SteinbergCBTrialityQuadraticDescent
public import CFSG.RankThree.Chevalley.SteinbergCFTrialityToralMain

public noncomputable section

namespace CFSG.RankThree.Chevalley

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley

@[expose] def orbitFieldFixed {K₂ : Type} [Field K₂] (σ₂ τ : K₂ →+* K₂)
    (b : Fin TwistTag.D4.foldedTag.rank) : Subfield (orbitField TwistTag.D4 K₂ σ₂ b) :=
  (RingHom.eqLocusField τ (RingHom.id K₂)).comap (orbitField TwistTag.D4 K₂ σ₂ b).subtype

theorem mem_orbitFieldFixed {K₂ : Type} [Field K₂] {σ₂ τ : K₂ →+* K₂}
    {b : Fin TwistTag.D4.foldedTag.rank} {c : orbitField TwistTag.D4 K₂ σ₂ b} :
    c ∈ orbitFieldFixed σ₂ τ b ↔ τ (c : K₂) = c :=
  Iff.rfl

section Fields

variable {ℓ f : ℕ} (hℓ : ℓ.Prime) (hf : 1 ≤ f) {K K₂ : Type} [Field K] [Field K₂] [Algebra K K₂]
  (hK : Nat.card K = (ℓ ^ f) ^ 3) (hK₂ : Nat.card K₂ = (ℓ ^ f) ^ 6) {σ₂ : K₂ ≃+* K₂}
  (hσ₂ : ∀ c, σ₂ c = c ^ ((ℓ ^ f) ^ 4)) {τ : K₂ ≃+* K₂} (hτ : ∀ c, τ c = c ^ ((ℓ ^ f) ^ 3))

theorem natCard_map_subfield {F E : Type*} [Field F] [Field E] (s : Subfield F) (φ : F →+* E) :
    Nat.card (s.map φ) = Nat.card s := by
  rw [← SetLike.coe_sort_coe, Subfield.coe_map, Nat.card_image_of_injective φ.injective,
    SetLike.coe_sort_coe]

theorem natCard_fieldRange {F E : Type*} [Field F] [Field E] (φ : F →+* E) :
    Nat.card φ.fieldRange = Nat.card F := by
  rw [← SetLike.coe_sort_coe, RingHom.coe_fieldRange, Nat.card_range_of_injective φ.injective]

include hℓ hK₂ hσ₂ in
theorem pow_q_sq_eq_of_sigma_fixed {c : K₂} (hc : σ₂ c = c) : c ^ ((ℓ ^ f) ^ 2) = c := by
  have h6 := pow_q_six_eq hK₂ hℓ c
  rw [hσ₂] at hc
  calc c ^ ((ℓ ^ f) ^ 2) = (c ^ ((ℓ ^ f) ^ 4)) ^ ((ℓ ^ f) ^ 2) := by rw [hc]
    _ = c := by rw [← pow_mul, ← pow_add, show 4 + 2 = 6 by rfl, h6]

include hℓ hf hK₂ hσ₂ in
theorem natCard_orbitField_K₂ (b : Fin TwistTag.D4.foldedTag.rank) :
    Nat.card (orbitField TwistTag.D4 K₂ σ₂.toRingHom b) =
      ((ℓ ^ f) ^ 2) ^ (TwistTag.D4.orbit b).card := by
  have hK₂' : Nat.card K₂ = (ℓ ^ (2 * f)) ^ 3 := by
    rw [hK₂]
    ring
  have hσ₂' : ∀ c, σ₂.toRingHom c = c ^ ((ℓ ^ (2 * f)) ^ 2) := fun c => by
    change σ₂ c = _
    rw [hσ₂]
    congr 1
    ring
  rw [card_orbitField_D4_orientation hℓ (by omega : 1 ≤ 2 * f) hK₂' (Or.inr rfl) hσ₂' b]
  congr 1
  ring

include hℓ hK hK₂ hσ₂ hτ in
theorem map_orbitFieldFixed_zero :
    (orbitFieldFixed σ₂.toRingHom τ.toRingHom ⟨0, by decide⟩).map
        (orbitField TwistTag.D4 K₂ σ₂.toRingHom ⟨0, by decide⟩).subtype =
      (algebraMap K K₂).fieldRange := by
  have : Finite K := Nat.finite_of_card_ne_zero (by
    rw [hK]
    exact pow_ne_zero _ (pow_ne_zero _ hℓ.ne_zero))
  have : Fintype K := Fintype.ofFinite K
  have hσ3 : ∀ c, σ₂ (σ₂ (σ₂ c)) = c := fun c => by
    rw [hσ₂, hσ₂, hσ₂, ← pow_mul, ← pow_mul,
      show (ℓ ^ f) ^ 4 * ((ℓ ^ f) ^ 4 * (ℓ ^ f) ^ 4) = (ℓ ^ f) ^ 6 * (ℓ ^ f) ^ 6 by ring, pow_mul,
      pow_q_six_eq hK₂ hℓ, pow_q_six_eq hK₂ hℓ]
  have htop := orbitField_D4_zero_eq_top σ₂ hσ3
  ext c
  rw [Subfield.mem_map, RingHom.mem_fieldRange]
  constructor
  · rintro ⟨c', hc', rfl⟩
    rw [mem_orbitFieldFixed] at hc'
    change τ (c' : K₂) = c' at hc'
    rw [hτ] at hc'
    obtain ⟨k, hk⟩ := mem_range_algebraMap_of_pow_card_eq (k := K) (by rw [hK]; exact hc')
    exact ⟨k, hk⟩
  · rintro ⟨k, rfl⟩
    refine ⟨⟨algebraMap K K₂ k, by rw [htop]; trivial⟩, ?_, rfl⟩
    rw [mem_orbitFieldFixed]
    change τ (algebraMap K K₂ k) = algebraMap K K₂ k
    rw [hτ, ← map_pow, ← hK, Nat.card_eq_fintype_card, FiniteField.pow_card]

include hℓ hK hK₂ hσ₂ hτ in
theorem natCard_orbitFieldFixed_zero :
    Nat.card (orbitFieldFixed σ₂.toRingHom τ.toRingHom ⟨0, by decide⟩) = (ℓ ^ f) ^ 3 := by
  have hmap := map_orbitFieldFixed_zero hℓ hK hK₂ (σ₂ := σ₂) hσ₂ hτ
  rw [← hK, ← natCard_map_subfield _
    (orbitField TwistTag.D4 K₂ σ₂.toRingHom ⟨0, by decide⟩).subtype, hmap, natCard_fieldRange]

include hτ hσ₂ in
theorem tau_comm_sigma₂ (c : K₂) : τ (σ₂.toRingHom c) = σ₂.toRingHom (τ c) := by
  change τ (σ₂ c) = σ₂ (τ c)
  rw [hτ, hσ₂, hσ₂, hτ, pow_right_comm]

theorem pow_pow_eq_self_of_pow_eq {M : Type*} [Monoid M] {k : M} {q : ℕ} (hk : k ^ q = k)
    (n : ℕ) : k ^ (q ^ n) = k := by
  induction n with
  | zero => rw [pow_zero, pow_one]
  | succ n ih => rw [pow_succ, pow_mul, ih, hk]

include hℓ hf hK hσ₂ hτ in
theorem natCard_orbitFieldFixed_one (σ : K →+* K) (hσ : ∀ c, σ c = c ^ (ℓ ^ f)) :
    Nat.card (orbitFieldFixed σ₂.toRingHom τ.toRingHom ⟨1, by decide⟩) = ℓ ^ f := by
  have : Finite K := Nat.finite_of_card_ne_zero (by
    rw [hK]
    exact pow_ne_zero _ (pow_ne_zero _ hℓ.ne_zero))
  have : Fintype K := Fintype.ofFinite K
  set q := ℓ ^ f
  set ι := algebraMap K K₂
  have hqK : ∀ k : K, k ^ (q ^ 3) = k := fun k => by
    rw [← hK, Nat.card_eq_fintype_card, FiniteField.pow_card]
  have hcardK := card_orbitField_D4_orientation hℓ hf hK (r := 1) (Or.inl rfl) (σ := σ)
    (by simpa using hσ) ⟨1, by decide⟩
  rw [show (TwistTag.D4.orbit ⟨1, by decide⟩).card = 1 by decide, pow_one] at hcardK
  have hmemK : ∀ k : K, k ∈ orbitField TwistTag.D4 K σ ⟨1, by decide⟩ ↔ k ^ q = k := fun k => by
    rw [mem_orbitField, show (TwistTag.D4.orbit ⟨1, by decide⟩).card = 1 by decide, pow_one, hσ]
  have h1 : ∀ k : orbitField TwistTag.D4 K σ ⟨1, by decide⟩,
      ι k ∈ orbitField TwistTag.D4 K₂ σ₂.toRingHom ⟨1, by decide⟩ := fun k => by
    rw [mem_orbitField_D4_one, hσ₂, ← map_pow, pow_pow_eq_self_of_pow_eq ((hmemK k).1 k.2)]
  have h2 : ∀ k : orbitField TwistTag.D4 K σ ⟨1, by decide⟩,
      Subtype.mk (ι k) (h1 k) ∈ orbitFieldFixed σ₂.toRingHom τ.toRingHom _ := fun k => by
    rw [mem_orbitFieldFixed]
    change τ (ι k) = ι k
    rw [hτ, ← map_pow, hqK]
  let φ : orbitField TwistTag.D4 K σ ⟨1, by decide⟩ →
      orbitFieldFixed σ₂.toRingHom τ.toRingHom ⟨1, by decide⟩ := fun k => ⟨⟨ι k, h1 k⟩, h2 k⟩
  have hφ : Function.Bijective φ := by
    refine ⟨fun k k' h => Subtype.ext (ι.injective (congrArg
      (fun y : orbitFieldFixed σ₂.toRingHom τ.toRingHom ⟨1, by decide⟩ => ((y : _) : K₂)) h)),
      fun c => ?_⟩
    obtain ⟨⟨c₀, hc₁⟩, hc₂⟩ := c
    rw [mem_orbitFieldFixed] at hc₂
    change τ c₀ = c₀ at hc₂
    have hσc : σ₂ c₀ = c₀ := (mem_orbitField_D4_one σ₂).1 hc₁
    rw [hτ] at hc₂
    rw [hσ₂] at hσc
    have hcq : c₀ ^ q = c₀ := by
      calc c₀ ^ q = (c₀ ^ (q ^ 3)) ^ q := by rw [hc₂]
        _ = c₀ := by rw [← pow_mul, ← pow_succ, hσc]
    obtain ⟨k, hk⟩ := mem_range_algebraMap_of_pow_card_eq (k := K) (by rw [hK]; exact hc₂)
    have hkq : k ^ q = k := ι.injective (by
      change ι (k ^ q) = ι k
      rw [map_pow, hk, hcq])
    exact ⟨⟨k, (hmemK k).2 hkq⟩, Subtype.ext (Subtype.ext hk)⟩
  rw [← Nat.card_congr (Equiv.ofBijective φ hφ), hcardK]

include hℓ hf hK hK₂ hσ₂ hτ in
theorem orbitFieldFixed_data (σ : K →+* K) (hσ : ∀ c, σ c = c ^ (ℓ ^ f))
    (b : Fin TwistTag.D4.foldedTag.rank) :
    Finite (orbitFieldFixed σ₂.toRingHom τ.toRingHom b) ∧
    Module.finrank (orbitFieldFixed σ₂.toRingHom τ.toRingHom b)
      (orbitField TwistTag.D4 K₂ σ₂.toRingHom b) = 2 ∧
    ∀ c, orbitFieldRestrict τ (tau_comm_sigma₂ hσ₂ hτ) b c =
      c ^ Nat.card (orbitFieldFixed σ₂.toRingHom τ.toRingHom b) := by
  have : Finite K₂ := Nat.finite_of_card_ne_zero (by
    rw [hK₂]
    exact pow_ne_zero _ (pow_ne_zero _ hℓ.ne_zero))
  have hq2 : 2 ≤ ℓ ^ f := le_trans hℓ.two_le (Nat.le_self_pow (by omega) ℓ)
  have hLcard := natCard_orbitField_K₂ hℓ hf hK₂ hσ₂ b
  refine ⟨inferInstance, ?_, ?_⟩
  · have h := Module.natCard_eq_pow_finrank (K := orbitFieldFixed σ₂.toRingHom τ.toRingHom b)
      (V := orbitField TwistTag.D4 K₂ σ₂.toRingHom b)
    rw [hLcard] at h
    rcases foldedD4_cases b with rfl | rfl
    · rw [natCard_orbitFieldFixed_zero hℓ hK hK₂ hσ₂ hτ,
        show (TwistTag.D4.orbit ⟨0, by decide⟩).card = 3 by decide,
        show ((ℓ ^ f) ^ 2) ^ 3 = ((ℓ ^ f) ^ 3) ^ 2 by ring] at h
      exact (Nat.pow_right_injective (le_trans hq2 (Nat.le_self_pow (by norm_num) _)) h).symm
    · rw [natCard_orbitFieldFixed_one hℓ hf hK hσ₂ hτ σ hσ,
        show (TwistTag.D4.orbit ⟨1, by decide⟩).card = 1 by decide, pow_one] at h
      exact (Nat.pow_right_injective hq2 h).symm
  · intro c
    apply Subtype.ext
    rw [coe_orbitFieldRestrict, SubmonoidClass.coe_pow, hτ]
    rcases foldedD4_cases b with rfl | rfl
    · rw [natCard_orbitFieldFixed_zero hℓ hK hK₂ hσ₂ hτ]
    · rw [natCard_orbitFieldFixed_one hℓ hf hK hσ₂ hτ σ hσ]
      have hc2 := pow_q_sq_eq_of_sigma_fixed hℓ hK₂ hσ₂ ((mem_orbitField_D4_one σ₂).1 c.2)
      rw [show (ℓ ^ f) ^ 3 = (ℓ ^ f) ^ 2 * ℓ ^ f by ring, pow_mul, hc2]

end Fields

end CFSG.RankThree.Chevalley
