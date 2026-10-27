module

public import CFSG.RankThree.GF2n.Tim78S48PhaseGen
import CFSG.RankThree.GF2n.Tim78S48PairQuot
import CFSG.GroupTheory.ElemAbelianClosure

public section

namespace CFSG.RankThree.GF2n.Tim78

open CFSG CFSG.Open

variable {G : Type} [Group G] [Finite G]

theorem card_le_of_frobenius {T₀ T K₁ E : Subgroup G} {n : ℕ} (hT₀T : T₀ ≤ T)
    (hTN : T ≤ Subgroup.normalizer (T₀ : Set G)) (hT₀e : Assembly.IsElemAbelian 2 T₀)
    (hK₁T : K₁ ≤ Subgroup.normalizer (T : Set G))
    (hK₁T₀ : K₁ ≤ Subgroup.normalizer (T₀ : Set G))
    (hrel : T₀.relIndex T = 2 ^ n) (hK₁card : Nat.card K₁ = 2 ^ n - 1)
    (hK₁c : ∀ a ∈ K₁, ∀ b ∈ K₁, a * b = b * a) (hK₁inf : K₁ ⊓ T₀ = ⊥)
    (hfrob : ∀ k ∈ K₁, k ≠ 1 → ∀ t ∈ T, (k * t * k⁻¹)⁻¹ * t ∈ T₀ → t ∈ T₀)
    (hET : E ≤ T) (hEe : Assembly.IsElemAbelian 2 E) (hEcard : Nat.card E = Nat.card T₀)
    (hEne : E ≠ T₀) :
    Nat.card T₀ ≤ 2 ^ n * Nat.card (T₀ ⊓ Subgroup.centralizer (T : Set G) : Subgroup G) := by
  classical
  set R : Subgroup G := T ⊔ K₁ with hR
  have hRN : R ≤ Subgroup.normalizer (T₀ : Set G) := sup_le hTN hK₁T₀
  have hT₀R : T₀ ≤ R := hT₀T.trans le_sup_left
  have hTR : T ≤ R := le_sup_left
  have hK₁R : K₁ ≤ R := le_sup_right
  haveI : (T₀.subgroupOf R).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hT₀R).mpr hRN
  set π := QuotientGroup.mk' (T₀.subgroupOf R) with hπ
  have hmem : ∀ r : ↥R, π r = 1 ↔ (r : G) ∈ T₀ := fun r => by
    rw [hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
  have hT₀c : ∀ a ∈ T₀, ∀ b ∈ T₀, a * b = b * a := fun a ha b hb =>
    comm_of_isElemAbelian hT₀e ha hb
  let ρ₀ : ↥R →* MulAut ↥T₀ := (Subgroup.normalizerMonoidHom T₀).comp (Subgroup.inclusion hRN)
  have hρ₀ : ∀ (r : ↥R) (v : ↥T₀), ((ρ₀ r v : ↥T₀) : G) = (r : G) * v * (r : G)⁻¹ :=
    fun _ _ => rfl
  have hker : T₀.subgroupOf R ≤ ρ₀.ker := by
    intro r hr
    rw [MonoidHom.mem_ker]
    ext v
    have hc := hT₀c _ (Subgroup.mem_subgroupOf.mp hr) v v.2
    rw [hρ₀, MulAut.one_apply, hc]
    group
  let ρ : (↥R ⧸ T₀.subgroupOf R) →* MulAut ↥T₀ := QuotientGroup.lift _ ρ₀ hker
  have hρ : ∀ (r : ↥R) (v : ↥T₀), ((ρ (π r) v : ↥T₀) : G) = (r : G) * v * (r : G)⁻¹ :=
    fun r v => rfl
  have hV2 : ∀ a : ↥T₀, a * a = 1 := fun a =>
    Subtype.ext (CFSG.Open.IsElemAbelian.mul_self_eq_one hT₀e a.2)
  have hVc : ∀ a b : ↥T₀, a * b = b * a := fun a b => Subtype.ext (hT₀c a a.2 b b.2)
  set L : Subgroup (↥R ⧸ T₀.subgroupOf R) := (T.subgroupOf R).map π with hL
  set Kb : Subgroup (↥R ⧸ T₀.subgroupOf R) := (K₁.subgroupOf R).map π with hKb
  have hLcard : Nat.card L = 2 ^ n := by
    have h := relIndex_eq_card_map_mk (G := G) (X := R) (N := T₀) (S := T) hTR
    rw [inf_of_le_right hT₀T] at h
    rw [← hrel]
    exact h.symm
  have hKcard : Nat.card Kb = Nat.card L - 1 := by
    have h := relIndex_eq_card_map_mk (G := G) (X := R) (N := T₀) (S := K₁) hK₁R
    rw [hK₁inf, Subgroup.relIndex_bot_left] at h
    rw [hLcard, ← hK₁card]
    exact h.symm
  have hKL : Kb ≤ Subgroup.normalizer (L : Set (↥R ⧸ T₀.subgroupOf R)) := by
    rintro _ ⟨k, hk, rfl⟩
    refine Subgroup.mem_normalizer_fintype fun x hx => ?_
    obtain ⟨t, ht, rfl⟩ := hx
    refine ⟨k * t * k⁻¹, ?_, by simp [map_mul, map_inv]⟩
    refine Subgroup.mem_subgroupOf.mpr ?_
    have := (Subgroup.mem_normalizer_iff.mp (hK₁T (Subgroup.mem_subgroupOf.mp hk)) (t : G)).mp
      (Subgroup.mem_subgroupOf.mp ht)
    simpa using this
  have hfrob' : ∀ k ∈ Kb, k ≠ 1 → ∀ x ∈ L, k * x * k⁻¹ = x → x = 1 := by
    rintro _ ⟨k, hk, rfl⟩ hk1 _ ⟨t, ht, rfl⟩ hkt
    have hkK : (k : G) ∈ K₁ := Subgroup.mem_subgroupOf.mp hk
    have htT : (t : G) ∈ T := Subgroup.mem_subgroupOf.mp ht
    have hk1' : (k : G) ≠ 1 := fun h => hk1 (by rw [show k = 1 from Subtype.ext h, map_one])
    rw [← map_inv, ← map_mul, ← map_mul, hπ, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply,
      QuotientGroup.eq, Subgroup.mem_subgroupOf] at hkt
    have := hfrob k hkK hk1' t htT (by simpa using hkt)
    exact (hmem t).mpr this
  have hKc' : ∀ a ∈ Kb, ∀ b ∈ Kb, a * b = b * a := by
    rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (hK₁c a (Subgroup.mem_subgroupOf.mp ha) b (Subgroup.mem_subgroupOf.mp hb))
  have hA : ∃ A : Subgroup (↥R ⧸ T₀.subgroupOf R), A ≤ L ∧ A ≠ ⊥ ∧
      Nat.card ↥T₀ ≤ Nat.card A * Nat.card (fixedSub ρ A) := by
    refine ⟨(E.subgroupOf R).map π, Subgroup.map_mono fun x hx =>
      Subgroup.mem_subgroupOf.mpr (hET (Subgroup.mem_subgroupOf.mp hx)), ?_, ?_⟩
    · intro hbot
      apply hEne
      have hle : E ≤ T₀ := by
        intro e he
        have hER : e ∈ R := hTR (hET he)
        have : π ⟨e, hER⟩ ∈ (E.subgroupOf R).map π :=
          ⟨⟨e, hER⟩, Subgroup.mem_subgroupOf.mpr he, rfl⟩
        rw [hbot, Subgroup.mem_bot, hmem] at this
        exact this
      exact Subgroup.eq_of_le_of_card_ge hle (by rw [hEcard])
    · have hAcard : Nat.card ((E.subgroupOf R).map π) = (E ⊓ T₀).relIndex E :=
        (relIndex_eq_card_map_mk (G := G) (X := R) (N := T₀) (S := E) (hET.trans hTR)).symm
      have hfix : Nat.card ↥(E ⊓ T₀ : Subgroup G) ≤
          Nat.card (fixedSub ρ ((E.subgroupOf R).map π)) := by
        have hle : (E ⊓ T₀).subgroupOf T₀ ≤ fixedSub ρ ((E.subgroupOf R).map π) := by
          intro v hv
          rw [mem_fixedSub]
          rintro _ ⟨e, he, rfl⟩
          apply Subtype.ext
          rw [hρ]
          have hc := comm_of_isElemAbelian hEe (Subgroup.mem_subgroupOf.mp he)
            (Subgroup.mem_subgroupOf.mp hv).1
          rw [hc]
          group
        calc Nat.card ↥(E ⊓ T₀ : Subgroup G)
            = Nat.card ((E ⊓ T₀).subgroupOf T₀) :=
              (Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_right).toEquiv).symm
          _ ≤ _ := Subgroup.card_le_of_le hle
      have hmul : T₀.relIndex E * Nat.card ↥(T₀ ⊓ E : Subgroup G) = Nat.card E :=
        Subgroup.relIndex_mul_card T₀ E
      have hrelE : (E ⊓ T₀).relIndex E = T₀.relIndex E := Subgroup.inf_relIndex_left E T₀
      calc Nat.card ↥T₀ = Nat.card E := hEcard.symm
        _ = (E ⊓ T₀).relIndex E * Nat.card ↥(E ⊓ T₀ : Subgroup G) := by
          rw [hrelE, ← hmul, inf_comm]
        _ ≤ _ := by
          rw [hAcard]
          exact Nat.mul_le_mul_left _ hfix
  have key := tim78_2_4_acting ρ hVc hV2 (L := L) (K := Kb) (n := n) hLcard hKcard hKL hfrob'
    hKc' hA
  have hfixL : Nat.card (fixedSub ρ L) ≤
      Nat.card ↥(T₀ ⊓ Subgroup.centralizer (T : Set G) : Subgroup G) := by
    have hle : fixedSub ρ L ≤ (T₀ ⊓ Subgroup.centralizer (T : Set G)).subgroupOf T₀ := by
      intro v hv
      rw [Subgroup.mem_subgroupOf]
      refine ⟨v.2, Subgroup.mem_centralizer_iff.mpr fun t ht => ?_⟩
      have h1 := mem_fixedSub.mp hv (π ⟨t, hTR ht⟩)
        ⟨⟨t, hTR ht⟩, Subgroup.mem_subgroupOf.mpr ht, rfl⟩
      have h2 := congrArg Subtype.val h1
      rw [hρ] at h2
      calc t * (v : G) = (t * v * t⁻¹) * t := by group
        _ = (v : G) * t := by
          have : t * (v : G) * t⁻¹ = (v : G) := h2
          rw [this]
    calc Nat.card (fixedSub ρ L)
        ≤ Nat.card ((T₀ ⊓ Subgroup.centralizer (T : Set G)).subgroupOf T₀) :=
          Subgroup.card_le_of_le hle
      _ = Nat.card ↥(T₀ ⊓ Subgroup.centralizer (T : Set G) : Subgroup G) :=
          Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv
  calc Nat.card ↥T₀ ≤ Nat.card L * Nat.card (fixedSub ρ L) := key
    _ = 2 ^ n * Nat.card (fixedSub ρ L) := by rw [hLcard]
    _ ≤ 2 ^ n * Nat.card ↥(T₀ ⊓ Subgroup.centralizer (T : Set G) : Subgroup G) :=
        Nat.mul_le_mul_left _ hfixL

end CFSG.RankThree.GF2n.Tim78
