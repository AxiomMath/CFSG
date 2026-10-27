module

public import CFSG.LocalAnalysis.QuasithinUnique.Defs
public import CFSG.LocalAnalysis.ComponentClassification.OuterAutomorphisms

public section

namespace CFSG.Quasithin.H13.FiveNorm

open CFSG.QuasithinUnique CFSG.ComponentClassification.OuterAutomorphisms

@[expose] def FiveInner (W : Type) [Group W] : Prop :=
  ∀ α : MulAut W, α ^ 5 = 1 → ∃ x : W, α = MulAut.conj x

@[expose] def NoFiveOver (W : Type) [Group W] : Prop :=
  ∀ S H : Subgroup W, IsSylowTwoOf S ⊤ → S ≤ H → Nat.card H ≠ 5 * Nat.card S

@[expose] def FiveRigid (W : Type) [Group W] : Prop :=
  Subgroup.center W = ⊥ ∧ FiveInner W ∧ NoFiveOver W

theorem fiveInner_of_oddInner {W : Type} [Group W]
    (h : ∀ α : MulAut W, Odd (orderOf α) → ∃ x : W, α = MulAut.conj x) : FiveInner W :=
  fun α hα => h α (Odd.of_dvd_nat (by decide) (orderOf_dvd_of_pow_eq_one hα))

theorem fiveInner_of_card_outer_le_two {W : Type} [Group W] [Finite W]
    (h : Nat.card (Outer W) ≤ 2) : FiveInner W := by
  intro α hα
  have : Finite (MulAut W) := Finite.of_injective _ DFunLike.coe_injective
  have : Finite (Outer W) := Finite.of_surjective _ (QuotientGroup.mk'_surjective (inner W))
  have h1 : (QuotientGroup.mk' (inner W) α) ^ 5 = 1 := by rw [← map_pow, hα, map_one]
  have h2 : orderOf (QuotientGroup.mk' (inner W) α) ∣ Nat.card (Outer W) :=
    orderOf_dvd_natCard _
  have h3 := orderOf_dvd_of_pow_eq_one h1
  have hpos : 0 < Nat.card (Outer W) := Nat.card_pos
  have h4 : orderOf (QuotientGroup.mk' (inner W) α) = 1 := by
    have h5 := (Nat.le_of_dvd hpos h2).trans h
    rcases (Nat.dvd_prime (by norm_num : Nat.Prime 5)).mp h3 with h6 | h6
    · exact h6
    · omega
  rw [orderOf_eq_one_iff, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h4
  obtain ⟨x, hx⟩ := h4
  exact ⟨x, hx.symm⟩

theorem center_eq_bot_of_isSimpleGroup {W : Type*} [Group W] [IsSimpleGroup W] {a b : W}
    (hab : a * b ≠ b * a) : Subgroup.center W = ⊥ := by
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center W) with h | h
  · exact h
  · have ha : a ∈ Subgroup.center W := by
      rw [h]
      exact Subgroup.mem_top a
    exact absurd (Subgroup.mem_center_iff.mp ha b).symm hab

theorem center_eq_bot_of_card_not_prime {W : Type*} [Group W] [IsSimpleGroup W]
    (h : ¬ (Nat.card W).Prime) : Subgroup.center W = ⊥ := by
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center W) with hc | hc
  · exact hc
  · have hmem : ∀ b : W, b ∈ Subgroup.center W := fun b => by
      rw [hc]
      exact Subgroup.mem_top b
    have : IsMulCommutative W := ⟨⟨fun a b => Subgroup.mem_center_iff.mp (hmem b) a⟩⟩
    exact absurd (Group.is_simple_iff_prime_card.mp inferInstance) h

theorem nonempty_quotCenter_equiv {X W : Type*} [Group X] [Group W] (e : X ≃* W)
    (hW : Subgroup.center W = ⊥) :
    Subgroup.center X = ⊥ ∧ Nonempty (X ⧸ Subgroup.center X ≃* W) := by
  have hZ : Subgroup.center X = ⊥ := by
    have h1 := Subgroup.map_center_eq e
    rw [hW] at h1
    exact (Subgroup.map_eq_bot_iff_of_injective _ e.injective).mp h1
  exact ⟨hZ, ⟨(QuotientGroup.quotientMulEquivOfEq hZ).trans (QuotientGroup.quotientBot.trans e)⟩⟩

theorem isSylowTwoOf_top_index {W : Type*} [Group W] {S : Subgroup W} (hS : IsSylowTwoOf S ⊤) :
    IsPGroup 2 S ∧ ¬ 2 ∣ S.index := by
  have h : (S.subgroupOf ⊤).index = S.index := Subgroup.relIndex_top_right S
  exact ⟨hS.2.1, h ▸ hS.2.2⟩

theorem card_eq_of_isSylowTwoOf_top {W : Type*} [Group W] [Finite W] {S : Subgroup W}
    (hS : IsSylowTwoOf S ⊤) {k m : ℕ} (hW : Nat.card W = 2 ^ k * m) (hm : ¬ 2 ∣ m) :
    Nat.card S = 2 ^ k := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hS2, hSi⟩ := isSylowTwoOf_top_index hS
  obtain ⟨j, hj⟩ := hS2.exists_card_eq
  have h1 := Subgroup.card_mul_index S
  rw [hj, hW] at h1
  have hm0 : m ≠ 0 := fun h => by simp [h] at hm
  have hi0 : S.index ≠ 0 := Subgroup.index_ne_zero_of_finite
  have h2 := congrArg (padicValNat 2) h1
  rw [padicValNat.mul (by positivity) hi0, padicValNat.prime_pow,
    padicValNat.eq_zero_of_not_dvd hSi, padicValNat.mul (by positivity) hm0,
    padicValNat.prime_pow, padicValNat.eq_zero_of_not_dvd hm] at h2
  simp only [add_zero] at h2
  rw [hj, h2]

theorem isSylowTwoOf_map_mulEquiv {W W' : Type*} [Group W] [Group W'] (e : W ≃* W')
    {S : Subgroup W} (hS : IsSylowTwoOf S ⊤) : IsSylowTwoOf (S.map e.toMonoidHom) ⊤ := by
  refine ⟨le_top, hS.2.1.map _, ?_⟩
  have h1 : ((S.map e.toMonoidHom).subgroupOf ⊤).index = (S.map e.toMonoidHom).index :=
    Subgroup.relIndex_top_right _
  have h2 : (S.subgroupOf ⊤).index = S.index := Subgroup.relIndex_top_right S
  rw [h1, Subgroup.index_map_of_bijective e.bijective, ← h2]
  exact hS.2.2

theorem fiveRigid_of_mulEquiv {W W' : Type} [Group W] [Group W'] (e : W ≃* W')
    (h : FiveRigid W) : FiveRigid W' := by
  obtain ⟨hZ, hinn, hno⟩ := h
  refine ⟨?_, fun α hα => ?_, fun S H hS hSH hcard => ?_⟩
  · rw [← Subgroup.map_center_eq e, hZ, Subgroup.map_bot]
  · obtain ⟨x, hx⟩ := hinn ((MulAut.congr e).symm α) (by rw [← map_pow, hα, map_one])
    have h1 : ∀ z : W, e.symm (α (e z)) = x * z * x⁻¹ := fun z => DFunLike.congr_fun hx z
    refine ⟨e x, MulEquiv.ext fun y => ?_⟩
    have h2 := h1 (e.symm y)
    rw [MulEquiv.apply_symm_apply] at h2
    rw [MulAut.conj_apply, ← e.apply_symm_apply (α y), h2, map_mul, map_mul, map_inv,
      MulEquiv.apply_symm_apply]
  · refine hno _ _ (isSylowTwoOf_map_mulEquiv e.symm hS) (Subgroup.map_mono hSH) ?_
    rw [Subgroup.card_map_of_injective e.symm.injective,
      Subgroup.card_map_of_injective e.symm.injective]
    exact hcard

theorem mem_normalizer_of_commute {G : Type*} [Group G] {H : Subgroup G} {g : G}
    (h : ∀ x ∈ H, x * g = g * x) : g ∈ Subgroup.normalizer (H : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · intro hx
    have h1 : g * x * g⁻¹ = x := by rw [← h x hx]; group
    rw [h1]
    exact hx
  · intro hx
    have h1 := h _ hx
    have h2 : g * x = g * (g * x * g⁻¹) := by
      calc g * x = g * x * g⁻¹ * g := by group
        _ = g * (g * x * g⁻¹) := h1
    rw [mul_left_cancel h2]
    exact hx

end CFSG.Quasithin.H13.FiveNorm
