module

public import CFSG.Quasithin.EmptyFaithful.SBc13Gen
public import CFSG.Quasithin.EmptyFaithful.S146P4
public import CFSG.Quasithin.Background.C1PackS15212B

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.F7

namespace SBc15

section Card

theorem card_sup_eq_mul_of_commute {P : Type*} [Group P] {A B : Subgroup P}
    (hc : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a) (hd : Disjoint A B) :
    Nat.card ↥(A ⊔ B) = Nat.card ↥A * Nat.card ↥B := by
  have comm : ∀ (a : ↥A) (b : ↥B), Commute (A.subtype a) (B.subtype b) := fun a b =>
    hc a a.2 b b.2
  have hinj : Function.Injective (MonoidHom.noncommCoprod A.subtype B.subtype comm) := by
    rw [MonoidHom.noncommCoprod_injective]
    refine ⟨A.subtype_injective, B.subtype_injective, ?_⟩
    rw [Subgroup.range_subtype, Subgroup.range_subtype]
    exact hd
  have hrange := MonoidHom.noncommCoprod_range A.subtype B.subtype comm
  rw [Subgroup.range_subtype, Subgroup.range_subtype] at hrange
  rw [← hrange, ← Nat.card_prod]
  exact (Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv).symm

end Card

section Dec

variable {G : Type} [Group G] {T M H : Subgroup G} {p : ℕ} {H₀ H₁ H₂ : Subgroup G} {t : G}

theorem card_imageOTwoQuot_oTwoUpper [Finite G] {PQ : Subgroup G} (hp : p = 3)
    (hred : IsRedCE T M H PQ p) (h : IsDecP T M H p H₀ H₁ H₂ t) :
    Nat.card ↥(imageOTwoQuot H (oTwoUpper H₁)) = 3 := by
  subst hp
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨z, hz1, hzQ, hzodd⟩ := h.exists_odd_notin hred.prime hred.odd
  have hzX : z ∈ oTwoUpper H₁ := mem_oTwoUpper_of_odd hz1 hzodd
  have hzH : z ∈ H := (h.le₁.trans h.le) hz1
  obtain ⟨φ, -, hφ⟩ := h.exists_phiP
  have hz3 : z ^ 3 ∈ pCoreOf 2 H := by
    obtain ⟨hzH₁, i, hi⟩ := IsDecP.mem_rotation (φ := φ) hzX
    have h3 : (((3 : ℕ) : ZMod 3)) = 0 := ZMod.natCast_self 3
    have h1 : φ (⟨z, hzH₁⟩ ^ 3) = 1 := by
      rw [map_pow, hi, SBc13.rot_pow, h3, zero_mul]
      exact DihedralGroup.r_zero
    exact (hφ _).mp h1
  set u : OTwoQuot H := QuotientGroup.mk ⟨z, hzH⟩ with hu
  have hu3 : u ^ 3 = 1 := by
    rw [hu, ← QuotientGroup.mk_pow]
    exact (mk_eq_one_iff_mem_pCoreOf (⟨z, hzH⟩ ^ 3 : ↥H)).mpr hz3
  have hu1 : u ≠ 1 := fun h1 => hzQ ((mk_eq_one_iff_mem_pCoreOf (⟨z, hzH⟩ : ↥H)).mp h1)
  have hord : orderOf u = 3 := orderOf_eq_prime hu3 hu1
  have hA : imageOTwoQuot H (oTwoUpper H₁) = Subgroup.zpowers u := by
    apply le_antisymm
    · intro v hv
      obtain ⟨y, hyH, hyX, rfl⟩ := mem_imageOTwoQuot_iff.mp hv
      obtain ⟨m, hm⟩ := h.exists_pow_of_notin hred.prime hzX hzQ hyX
      have h1 : (QuotientGroup.mk (⟨y, hyH⟩ * (⟨z, hzH⟩ ^ m)⁻¹ : ↥H) : OTwoQuot H) = 1 :=
        (mk_eq_one_iff_mem_pCoreOf _).mpr hm
      rw [QuotientGroup.mk_mul, QuotientGroup.mk_inv, QuotientGroup.mk_pow,
        mul_inv_eq_one] at h1
      exact Subgroup.mem_zpowers_iff.mpr ⟨(m : ℤ), (zpow_natCast u m).trans h1.symm⟩
    · rw [Subgroup.zpowers_le]
      exact mem_imageOTwoQuot_iff.mpr ⟨z, hzH, hzX, rfl⟩
  rw [hA, Nat.card_zpowers, hord]

theorem commute_imageOTwoQuot (h : IsDecP T M H p H₀ H₁ H₂ t) :
    ∀ a ∈ imageOTwoQuot H (oTwoUpper H₁), ∀ b ∈ imageOTwoQuot H (oTwoUpper H₂), a * b = b * a := by
  intro a ha b hb
  have hle := imageOTwoQuot_le_centralizer (M := H) (X := oTwoUpper H₁) (C := oTwoUpper H₂)
    fun x hx c hc =>
      h.comm (Subgroup.commutator_mem_commutator (oTwoUpper_le H₁ hx) (oTwoUpper_le H₂ hc))
  exact (Subgroup.mem_centralizer_iff.mp (hle ha) b hb).symm

theorem disjoint_imageOTwoQuot (h : IsDecP T M H p H₀ H₁ H₂ t) :
    Disjoint (imageOTwoQuot H (oTwoUpper H₁)) (imageOTwoQuot H (oTwoUpper H₂)) := by
  rw [Subgroup.disjoint_def]
  intro u hu1 hu2
  obtain ⟨x, hxH, hx, rfl⟩ := mem_imageOTwoQuot_iff.mp hu1
  obtain ⟨c, hcH, hc, hcx⟩ := mem_imageOTwoQuot_iff.mp hu2
  have hq1 : (QuotientGroup.mk ((⟨c, hcH⟩ : ↥H)⁻¹ * ⟨x, hxH⟩) : OTwoQuot H) = 1 := by
    rw [QuotientGroup.mk_mul, QuotientGroup.mk_inv, hcx, inv_mul_cancel]
  have hq : c⁻¹ * x ∈ pCoreOf 2 H := (mk_eq_one_iff_mem_pCoreOf _).mp hq1
  have hcH₁ : c ∈ H₁ := by
    have hx₁ : x ∈ H₁ := oTwoUpper_le H₁ hx
    have : x * (c⁻¹ * x)⁻¹ ∈ H₁ := H₁.mul_mem hx₁ (H₁.inv_mem (h.Q₁ hq))
    simpa using this
  have hcQ : c ∈ pCoreOf 2 H := by
    rw [← h.inf]
    exact ⟨hcH₁, oTwoUpper_le H₂ hc⟩
  have hc1 : (QuotientGroup.mk (⟨c, hcH⟩ : ↥H) : OTwoQuot H) = 1 :=
    (mk_eq_one_iff_mem_pCoreOf (⟨c, hcH⟩ : ↥H)).mpr hcQ
  rw [← hcx, hc1]

theorem relIndex_pCoreOf_oTwoUpper_eq_nine [Finite G] (S : Setting146 G T M) {PQ : Subgroup G}
    (hred : IsRedCE T M H PQ p) (hp : p = 3) (h : IsDecP T M H p H₀ H₁ H₂ t) :
    (pCoreOf 2 (oTwoUpper H)).relIndex (oTwoUpper H) = 9 := by
  have hXH : oTwoUpper H ≤ H := oTwoUpper_le H
  have hX₁ : oTwoUpper H₁ ≤ H := (oTwoUpper_le H₁).trans (h.le₁.trans h.le)
  have hX₂ : oTwoUpper H₂ ≤ H := (oTwoUpper_le H₂).trans (h.le₂.trans h.le)
  have hmul : Nat.card ↥(imageOTwoQuot H (oTwoUpper H)) = 3 * 3 := by
    rw [h.oTwoUpper_eq S hred, imageOTwoQuot_sup hX₁ hX₂,
      card_sup_eq_mul_of_commute (commute_imageOTwoQuot h) (disjoint_imageOTwoQuot h),
      card_imageOTwoQuot_oTwoUpper hp hred h, card_imageOTwoQuot_oTwoUpper hp hred h.swap]
  rw [S152Y.pCoreOf_eq_inf_of_normalizer hXH (le_normalizer_oTwoUpper H),
    C1Pack12.relIndex_inf_pCoreOf_eq_card hXH, hmul]

end Dec

end SBc15

end CFSG.Quasithin
