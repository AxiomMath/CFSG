module

public import CFSG.Quasithin.EmptyFaithful.SBc15C2Dec

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.F7

namespace SBc16

variable {G : Type} [Group G] [Finite G] {T M H : Subgroup G} {p : ℕ} {H₀ H₁ H₂ : Subgroup G} {t : G}

theorem mem_pCoreOf_oTwoUpper_iff (H : Subgroup G) {x : G} :
    x ∈ pCoreOf 2 (oTwoUpper H) ↔ x ∈ oTwoUpper H ∧ x ∈ pCoreOf 2 H := by
  rw [S152Y.pCoreOf_eq_inf_of_normalizer (oTwoUpper_le H) (le_normalizer_oTwoUpper H)]
  exact Subgroup.mem_inf

theorem card_imageOTwoQuot_K {PQ : Subgroup G} (hred : IsRedCE T M H PQ p)
    (h : IsDecP T M H p H₀ H₁ H₂ t) :
    Nat.card ↥(imageOTwoQuot (oTwoUpper H) (oTwoUpper H₁)) = p := by
  have : Fact (Nat.Prime p) := ⟨hred.prime⟩
  have : NeZero p := ⟨hred.prime.ne_zero⟩
  obtain ⟨z, hz1, hzQ, hzodd⟩ := h.exists_odd_notin hred.prime hred.odd
  have hzX : z ∈ oTwoUpper H₁ := mem_oTwoUpper_of_odd hz1 hzodd
  have hX₁K : oTwoUpper H₁ ≤ oTwoUpper H := oTwoUpper_mono (h.le₁.trans h.le)
  have hzK : z ∈ oTwoUpper H := hX₁K hzX
  obtain ⟨φ, -, hφ⟩ := h.exists_phiP
  have hzp : z ^ p ∈ pCoreOf 2 H := by
    obtain ⟨hzH₁, i, hi⟩ := IsDecP.mem_rotation (φ := φ) hzX
    have h1 : φ (⟨z, hzH₁⟩ ^ p) = 1 := by
      rw [map_pow, hi, SBc13.rot_pow, ZMod.natCast_self, zero_mul]
      exact DihedralGroup.r_zero
    exact (hφ _).mp h1
  set u : OTwoQuot (oTwoUpper H) := QuotientGroup.mk ⟨z, hzK⟩ with hu
  have hup : u ^ p = 1 := by
    rw [hu, ← QuotientGroup.mk_pow]
    exact (mk_eq_one_iff_mem_pCoreOf (⟨z, hzK⟩ ^ p : ↥(oTwoUpper H))).mpr
      ((mem_pCoreOf_oTwoUpper_iff H).mpr ⟨(oTwoUpper H).pow_mem hzK p, hzp⟩)
  have hu1 : u ≠ 1 := fun h1 =>
    hzQ (((mem_pCoreOf_oTwoUpper_iff H).mp
      ((mk_eq_one_iff_mem_pCoreOf (⟨z, hzK⟩ : ↥(oTwoUpper H))).mp h1)).2)
  have hord : orderOf u = p := orderOf_eq_prime hup hu1
  have hA : imageOTwoQuot (oTwoUpper H) (oTwoUpper H₁) = Subgroup.zpowers u := by
    apply le_antisymm
    · intro v hv
      obtain ⟨y, hyK, hyX, rfl⟩ := mem_imageOTwoQuot_iff.mp hv
      obtain ⟨m, hm⟩ := h.exists_pow_of_notin hred.prime hzX hzQ hyX
      have h1 : (QuotientGroup.mk (⟨y, hyK⟩ * (⟨z, hzK⟩ ^ m)⁻¹ : ↥(oTwoUpper H)) :
          OTwoQuot (oTwoUpper H)) = 1 :=
        (mk_eq_one_iff_mem_pCoreOf _).mpr ((mem_pCoreOf_oTwoUpper_iff H).mpr
          ⟨(oTwoUpper H).mul_mem hyK ((oTwoUpper H).inv_mem ((oTwoUpper H).pow_mem hzK m)), hm⟩)
      rw [QuotientGroup.mk_mul, QuotientGroup.mk_inv, QuotientGroup.mk_pow, mul_inv_eq_one] at h1
      exact Subgroup.mem_zpowers_iff.mpr ⟨(m : ℤ), (zpow_natCast u m).trans h1.symm⟩
    · rw [Subgroup.zpowers_le]
      exact mem_imageOTwoQuot_iff.mpr ⟨z, hzK, hzX, rfl⟩
  rw [hA, Nat.card_zpowers, hord]

theorem commute_imageOTwoQuot_K (h : IsDecP T M H p H₀ H₁ H₂ t) :
    ∀ a ∈ imageOTwoQuot (oTwoUpper H) (oTwoUpper H₁),
      ∀ b ∈ imageOTwoQuot (oTwoUpper H) (oTwoUpper H₂), a * b = b * a := by
  intro a ha b hb
  have hX₁K : oTwoUpper H₁ ≤ oTwoUpper H := oTwoUpper_mono (h.le₁.trans h.le)
  have hX₂K : oTwoUpper H₂ ≤ oTwoUpper H := oTwoUpper_mono (h.le₂.trans h.le)
  have hle := imageOTwoQuot_le_centralizer (M := oTwoUpper H) (X := oTwoUpper H₁)
    (C := oTwoUpper H₂) fun x hx c hc =>
      (mem_pCoreOf_oTwoUpper_iff H).mpr
        ⟨(oTwoUpper H).mul_mem ((oTwoUpper H).mul_mem ((oTwoUpper H).mul_mem (hX₁K hx) (hX₂K hc))
          ((oTwoUpper H).inv_mem (hX₁K hx))) ((oTwoUpper H).inv_mem (hX₂K hc)),
          h.comm (Subgroup.commutator_mem_commutator (oTwoUpper_le H₁ hx) (oTwoUpper_le H₂ hc))⟩
  exact (Subgroup.mem_centralizer_iff.mp (hle ha) b hb).symm

theorem disjoint_imageOTwoQuot_K (h : IsDecP T M H p H₀ H₁ H₂ t) :
    Disjoint (imageOTwoQuot (oTwoUpper H) (oTwoUpper H₁))
      (imageOTwoQuot (oTwoUpper H) (oTwoUpper H₂)) := by
  rw [Subgroup.disjoint_def]
  intro u hu1 hu2
  obtain ⟨x, hxK, hx, rfl⟩ := mem_imageOTwoQuot_iff.mp hu1
  obtain ⟨c, hcK, hc, hcx⟩ := mem_imageOTwoQuot_iff.mp hu2
  have hq1 : (QuotientGroup.mk ((⟨c, hcK⟩ : ↥(oTwoUpper H))⁻¹ * ⟨x, hxK⟩) :
      OTwoQuot (oTwoUpper H)) = 1 := by
    rw [QuotientGroup.mk_mul, QuotientGroup.mk_inv, hcx, inv_mul_cancel]
  have hq : c⁻¹ * x ∈ pCoreOf 2 (oTwoUpper H) := (mk_eq_one_iff_mem_pCoreOf _).mp hq1
  have hcH₁ : c ∈ H₁ := by
    have hx₁ : x ∈ H₁ := oTwoUpper_le H₁ hx
    have : x * (c⁻¹ * x)⁻¹ ∈ H₁ :=
      H₁.mul_mem hx₁ (H₁.inv_mem (h.Q₁ ((mem_pCoreOf_oTwoUpper_iff H).mp hq).2))
    simpa using this
  have hcQ : c ∈ pCoreOf 2 H := by
    rw [← h.inf]
    exact ⟨hcH₁, oTwoUpper_le H₂ hc⟩
  have hc1 : (QuotientGroup.mk (⟨c, hcK⟩ : ↥(oTwoUpper H)) : OTwoQuot (oTwoUpper H)) = 1 :=
    (mk_eq_one_iff_mem_pCoreOf (⟨c, hcK⟩ : ↥(oTwoUpper H))).mpr
      ((mem_pCoreOf_oTwoUpper_iff H).mpr ⟨hcK, hcQ⟩)
  rw [← hcx, hc1]

theorem imageOTwoQuot_sup_eq_top (S : Setting146 G T M) {PQ : Subgroup G}
    (hred : IsRedCE T M H PQ p) (h : IsDecP T M H p H₀ H₁ H₂ t) :
    imageOTwoQuot (oTwoUpper H) (oTwoUpper H₁) ⊔ imageOTwoQuot (oTwoUpper H) (oTwoUpper H₂) = ⊤ := by
  have hX₁K : oTwoUpper H₁ ≤ oTwoUpper H := oTwoUpper_mono (h.le₁.trans h.le)
  have hX₂K : oTwoUpper H₂ ≤ oTwoUpper H := oTwoUpper_mono (h.le₂.trans h.le)
  rw [← imageOTwoQuot_sup hX₁K hX₂K, ← h.oTwoUpper_eq S hred, eq_top_iff]
  intro v _
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective v
  exact mem_imageOTwoQuot_iff.mpr ⟨x, x.2, x.2, rfl⟩

theorem card_OTwoQuot_K (S : Setting146 G T M) {PQ : Subgroup G} (hp5 : p = 5)
    (hred : IsRedCE T M H PQ p) (h : IsDecP T M H p H₀ H₁ H₂ t) :
    Nat.card (OTwoQuot (oTwoUpper H)) = 25 := by
  have h1 := SBc15.card_sup_eq_mul_of_commute (commute_imageOTwoQuot_K h)
    (disjoint_imageOTwoQuot_K h)
  rw [imageOTwoQuot_sup_eq_top S hred h, Subgroup.card_top, card_imageOTwoQuot_K hred h,
    card_imageOTwoQuot_K hred h.swap, hp5] at h1
  rw [h1]

theorem mul_comm_OTwoQuot_K (S : Setting146 G T M) {PQ : Subgroup G} (hp5 : p = 5)
    (hred : IsRedCE T M H PQ p) (h : IsDecP T M H p H₀ H₁ H₂ t) :
    ∀ a b : OTwoQuot (oTwoUpper H), a * b = b * a := by
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have hcard : Nat.card (OTwoQuot (oTwoUpper H)) = 5 ^ 2 := by
    rw [card_OTwoQuot_K S hp5 hred h]
    norm_num
  intro a b
  exact (IsPGroup.isMulCommutative_of_card_eq_prime_sq hcard).is_comm.comm a b

end SBc16

end CFSG.Quasithin
