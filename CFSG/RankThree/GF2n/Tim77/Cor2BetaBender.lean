module

public import CFSG.Timmesfeld.Bridge.Asc72Bender
public import CFSG.Goldschmidt.Steps.StrongEmb
public import CFSG.CGT.PushingUpLit.A78.BenderTIBasic
public import CFSG.Goldschmidt.Steps.GoldType
public import CFSG.Timmesfeld.Bridge.NoPolarConnected
public import CFSG.Holt.PointHullTwoGroupBasic
public import CFSG.GH74.Uniqueness.Bender.OuterFinal

public section

namespace CFSG.RankThree.GF2n.Tim77

open CFSG.Open Subgroup
open scoped commutatorElement MatrixGroups

section BenderCriterionCerts


theorem cor2Beta_isBender_of_wcl {L : Type} [Group L] [Finite L] [IsSimpleGroup L]
    (hL : goldschmidtSimpleType L) (T : Sylow 2 L) {s : L} (hs1 : s ≠ 1)
    (hs : s ∈ (T : Subgroup L))
    (hstar : ∀ y : L, (∃ m : L, y = m * s * m⁻¹) → y * s = s * y → y ∈ (T : Subgroup L)) :
    CFSG.BenderSuzuki.IsBenderGroup L := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_cases hB : CFSG.Open.fusionIsBenderGroup L
  · exact CFSG.Timmesfeld.Bridge.isBenderGroup_of_fusionIsBenderGroup hB
  have hK : (∃ p f : ℕ, ∃ _hp : Fact p.Prime, Odd p ∧ 0 < f ∧ 5 ≤ p ^ f ∧
        (p ^ f % 8 = 3 ∨ p ^ f % 8 = 5) ∧ Nonempty (L ≃* PSL(2, GaloisField p f))) ∨
      (∃ m : ℕ, 1 ≤ m ∧ Nat.card L = ordRee (3 ^ (2 * m + 1))) ∨
      Nonempty (L ≃* goldschmidtJ1) := by
    rcases hL with ⟨f, hf, ⟨e⟩⟩ | ⟨n, hn, ⟨e⟩⟩ | ⟨f, hf, ⟨e⟩⟩ | h4 | h5 | h6
    · exact absurd (Or.inl ⟨f, by omega, ⟨e⟩⟩) hB
    · exact absurd (Or.inr (Or.inr ⟨n, hn, ⟨e⟩⟩)) hB
    · exact absurd (Or.inr (Or.inl ⟨f, hf, ⟨e⟩⟩)) hB
    · exact Or.inl h4
    · exact Or.inr (Or.inl h5)
    · exact Or.inr (Or.inr h6)
  obtain ⟨hTab, hT2, hT4, htrans⟩ := CFSG.Goldschmidt.GoldType.elementary_of_clauses (K := L) hK T
  have hcomm : ∀ a ∈ (T : Subgroup L), ∀ b ∈ (T : Subgroup L), a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (hTab.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  have hsq : ∀ y ∈ (T : Subgroup L), y * y = 1 := fun y hy => by
    have := hT2 y hy
    rwa [sq] at this
  have hs2 : orderOf s = 2 := orderOf_eq_prime (by rw [sq]; exact hsq s hs) hs1
  have hconj : ∀ y : L, orderOf y = 2 → ∃ m : L, y = m * s * m⁻¹ := by
    intro y hy2
    have hy1 : y ≠ 1 := by
      intro h
      rw [h, orderOf_one] at hy2
      exact absurd hy2 (by decide)
    obtain ⟨g, -, hg⟩ :=
      CFSG.Holt.PointHull.exists_inv_mul_mul_mem_sylow (P := T) le_top (Subgroup.mem_top y) hy2
    have hg1 : g⁻¹ * y * g ≠ 1 := by
      intro h
      apply hy1
      have := congrArg (fun w => g * w * g⁻¹) h
      simpa [mul_assoc] using this
    obtain ⟨n, hn, hns⟩ := htrans _ hg s hs hg1 hs1
    refine ⟨g * n, ?_⟩
    have : y = g * (g⁻¹ * y * g) * g⁻¹ := by group
    rw [this, ← hns]
    group
  have hSE : CFSG.BenderSuzuki.IsStronglyEmbeddedOrder
      (normalizer ((T : Subgroup L) : Set L)) := by
    refine ⟨?_, ?_, ?_⟩
    · intro htop
      have hn : (T : Subgroup L).Normal := Subgroup.normalizer_eq_top_iff.mp htop
      rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (T : Subgroup L) with h | h
      · apply hs1
        have : s ∈ (T : Subgroup L) := hs
        rwa [h, Subgroup.mem_bot] at this
      ·
        have hLc : ∀ a b : L, a * b = b * a := fun a b =>
          hcomm a (h ▸ Subgroup.mem_top a) b (h ▸ Subgroup.mem_top b)
        have hnz : (Subgroup.zpowers s).Normal :=
          ⟨fun n hn g => by rw [hLc g n, mul_inv_cancel_right]; exact hn⟩
        rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.zpowers s) with h' | h'
        · apply hs1
          have : s ∈ Subgroup.zpowers s := Subgroup.mem_zpowers s
          rwa [h', Subgroup.mem_bot] at this
        · have hc : Nat.card L = 2 := by
            rw [← Subgroup.card_top (G := L), ← h', Nat.card_zpowers, hs2]
          have h4 : 4 ≤ Nat.card L := by
            have := hT4
            rwa [h, Subgroup.card_top] at this
          omega
    · have hdvd : Nat.card (T : Subgroup L) ∣ Nat.card (normalizer ((T : Subgroup L) : Set L)) :=
        Subgroup.card_dvd_of_le Subgroup.le_normalizer
      obtain ⟨k, hk⟩ := T.isPGroup'.exists_card_eq
      have hk' : 2 ∣ Nat.card (T : Subgroup L) := by
        rw [hk]
        have : k ≠ 0 := by
          rintro rfl
          rw [pow_zero] at hk
          omega
        exact dvd_pow_self 2 this
      exact even_iff_two_dvd.mpr (hk'.trans hdvd)
    · intro g hg
      by_contra hodd
      have hev : 2 ∣ Nat.card ↥(normalizer ((T : Subgroup L) : Set L) ⊓
          (normalizer ((T : Subgroup L) : Set L)).map (MulAut.conj g).toMonoidHom) := by
        rw [← even_iff_two_dvd]
        exact Nat.not_odd_iff_even.mp hodd
      obtain ⟨u, hu⟩ :=
        exists_prime_orderOf_dvd_card' (G := ↥(normalizer ((T : Subgroup L) : Set L) ⊓
          (normalizer ((T : Subgroup L) : Set L)).map (MulAut.conj g).toMonoidHom)) 2 hev
      have hu2 : orderOf (u : L) = 2 := by rw [Subgroup.orderOf_coe]; exact hu
      obtain ⟨huM, m, hmM, hmu⟩ := Subgroup.mem_inf.mp u.2
      have huT : (u : L) ∈ (T : Subgroup L) :=
        CFSG.CGT.PushingUpLit.A78.mem_sylow_of_mem_normalizer T huM
          ⟨1, by simpa [hu2] using pow_orderOf_eq_one (u : L)⟩
      have hmu' : m = g⁻¹ * (u : L) * g := by
        have : (u : L) = g * m * g⁻¹ := by
          rw [← hmu]; simp [MulAut.conj_apply]
        rw [this]; group
      have hmo : orderOf m = 2 := by
        rw [hmu']
        have := (MulEquiv.orderOf_eq (MulAut.conj g⁻¹) (u : L)).trans hu2
        simpa [MulAut.conj_apply] using this
      have hmT : m ∈ (T : Subgroup L) :=
        CFSG.CGT.PushingUpLit.A78.mem_sylow_of_mem_normalizer T hmM
          ⟨1, by simpa [hmo] using pow_orderOf_eq_one m⟩
      have hu1 : (u : L) ≠ 1 := by
        intro h
        rw [h, orderOf_one] at hu2
        exact absurd hu2 (by decide)
      obtain ⟨n₁, hn₁, hn₁u⟩ := htrans _ hs (u : L) huT hs1 hu1
      have hmem : ∀ y : L, y ∈ ((g • T : Sylow 2 L) : Subgroup L) ↔
          g⁻¹ * y * g ∈ (T : Subgroup L) := by
        intro y
        rw [Sylow.coe_subgroup_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem]
        simp [MulAut.smul_def]
      have hle : ((g • T : Sylow 2 L) : Subgroup L) ≤ (T : Subgroup L) := by
        intro y hy
        have hy' := (hmem y).mp hy
        by_cases hy1 : y = 1
        · rw [hy1]; exact Subgroup.one_mem _
        have hyo : orderOf y = 2 := by
          have := hsq _ hy'
          have hy2 : y * y = 1 := by
            have e : y * y = g * ((g⁻¹ * y * g) * (g⁻¹ * y * g)) * g⁻¹ := by group
            rw [e, this]; group
          exact orderOf_eq_prime (by rw [sq]; exact hy2) hy1
        have hyu : y * (u : L) = (u : L) * y := by
          have hc := hcomm _ hy' m hmT
          have e1 : y * (u : L) = g * ((g⁻¹ * y * g) * m) * g⁻¹ := by rw [hmu']; group
          have e2 : (u : L) * y = g * (m * (g⁻¹ * y * g)) * g⁻¹ := by rw [hmu']; group
          rw [e1, e2, hc]
        obtain ⟨m', hm'⟩ := hconj y hyo
        have hs' : s = n₁ * (u : L) * n₁⁻¹ := by rw [← hn₁u]; group
        have hys : (n₁ * y * n₁⁻¹) * s = s * (n₁ * y * n₁⁻¹) := by
          calc (n₁ * y * n₁⁻¹) * s = n₁ * (y * (n₁⁻¹ * s * n₁)) * n₁⁻¹ := by group
            _ = n₁ * (y * (u : L)) * n₁⁻¹ := by rw [hn₁u]
            _ = n₁ * ((u : L) * y) * n₁⁻¹ := by rw [hyu]
            _ = (n₁ * (u : L) * n₁⁻¹) * (n₁ * y * n₁⁻¹) := by group
            _ = s * (n₁ * y * n₁⁻¹) := by rw [← hs']
        have hŷ := hstar (n₁ * y * n₁⁻¹) ⟨n₁ * m', by rw [hm']; group⟩ hys
        have hn₁inv : n₁⁻¹ ∈ normalizer ((T : Subgroup L) : Set L) := Subgroup.inv_mem _ hn₁
        have : y = n₁⁻¹ * (n₁ * y * n₁⁻¹) * n₁ := by group
        rw [this]
        have := (Subgroup.mem_normalizer_iff.mp hn₁inv (n₁ * y * n₁⁻¹)).mp hŷ
        simpa using this
      have hSeq : (g • T : Sylow 2 L) = T :=
        Sylow.ext (((g • T : Sylow 2 L).is_maximal' T.isPGroup' hle).symm)
      exact hg (Sylow.smul_eq_iff_mem_normalizer.mp hSeq)
  exact CFSG.BenderSuzuki.bender_suzuki _ hSE

end BenderCriterionCerts

section OuterInvolutionCerts


theorem cor2Beta_outer_excluded
    {L : Type} [Group L] [Finite L] (hL : CFSG.BenderSuzuki.IsBenderGroup L) (σ : MulAut L)
    (hσ : σ * σ = 1) (hout : ¬ ∃ g : L, ∀ x : L, σ x = g * x * g⁻¹) {s : L} (hs1 : s ≠ 1)
    (hs2 : s * s = 1) (hσs : σ s = s)
    (hstar : ∀ x : L, σ x = x → (x * s * x⁻¹) * s = s * (x * s * x⁻¹)) : False := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hs2' : orderOf s = 2 := orderOf_eq_prime (by rw [sq]; exact hs2) hs1
  obtain ⟨S, hsS⟩ : ∃ S : Sylow 2 L, s ∈ (S : Subgroup L) := by
    have hp : IsPGroup 2 (Subgroup.zpowers s) := by
      intro g
      obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.1 g.2
      refine ⟨1, Subtype.ext ?_⟩
      have hs2'' : s ^ 2 = 1 := by rw [sq]; exact hs2
      rw [Subgroup.coe_pow, ← hn, pow_one, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul]
      simp [hs2'']
    obtain ⟨S, hS⟩ := hp.exists_le_sylow
    exact ⟨S, hS (Subgroup.mem_zpowers s)⟩
  have hsZ := CFSG.Timmesfeld.Bridge.Asc72.IsBenderGroup.commute_of_mul_self_eq_one hL S hsS hs2
  obtain ⟨-, hx⟩ := CFSG.GH74.Uniqueness.Bender.bender_outer_involution hL σ hσ hout
  obtain ⟨x, hσx, hxN⟩ := hx S
  have hSE := CFSG.Timmesfeld.Bridge.Asc72.IsBenderGroup.isStronglyEmbeddedOrder_normalizer hL S
  have hsN : s ∈ normalizer ((S : Subgroup L) : Set L) := Subgroup.le_normalizer hsS
  have hCs := CFSG.Goldschmidt.centralizer_le_of_stronglyEmbedded hSE hs2' hsN
  have hzs := hstar x hσx
  have hz2 : (x * s * x⁻¹) * (x * s * x⁻¹) = 1 := by
    calc (x * s * x⁻¹) * (x * s * x⁻¹) = x * (s * s) * x⁻¹ := by group
      _ = 1 := by rw [hs2]; group
  have hz1 : x * s * x⁻¹ ≠ 1 := by
    intro h
    apply hs1
    have := congrArg (fun w => x⁻¹ * w * x) h
    simpa [mul_assoc] using this
  have hz2' : orderOf (x * s * x⁻¹) = 2 := orderOf_eq_prime (by rw [sq]; exact hz2) hz1
  have hzN : x * s * x⁻¹ ∈ normalizer ((S : Subgroup L) : Set L) :=
    hCs (Subgroup.mem_centralizer_singleton_iff.mpr hzs)
  have hCz := CFSG.Goldschmidt.centralizer_le_of_stronglyEmbedded hSE hz2' hzN
  have hmem : ∀ y : L, y ∈ ((x • S : Sylow 2 L) : Subgroup L) ↔ x⁻¹ * y * x ∈ (S : Subgroup L) := by
    intro y
    rw [Sylow.coe_subgroup_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem]
    simp [MulAut.smul_def]
  have hle : ((x • S : Sylow 2 L) : Subgroup L) ≤ (S : Subgroup L) := by
    intro y hy
    have hy' := (hmem y).mp hy
    have hc : y ∈ Subgroup.centralizer ({x * s * x⁻¹} : Set L) := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      have h1 := (hsZ _ hy').eq
      calc y * (x * s * x⁻¹) = x * ((x⁻¹ * y * x) * s) * x⁻¹ := by group
        _ = x * (s * (x⁻¹ * y * x)) * x⁻¹ := by rw [← h1]
        _ = (x * s * x⁻¹) * y := by group
    have hyN := hCz hc
    refine CFSG.CGT.PushingUpLit.A78.mem_sylow_of_mem_normalizer S hyN ?_
    obtain ⟨k, hk⟩ := (x • S : Sylow 2 L).isPGroup' ⟨y, hy⟩
    exact ⟨k, by simpa using congrArg Subtype.val hk⟩
  have hSeq : (x • S : Sylow 2 L) = S :=
    Sylow.ext (((x • S : Sylow 2 L).is_maximal' S.isPGroup' hle).symm)
  exact hxN (Sylow.smul_eq_iff_mem_normalizer.mp hSeq)

end OuterInvolutionCerts

end CFSG.RankThree.GF2n.Tim77
