module

public import CFSG.Quasithin.Vol2.KGFact12614
public import CFSG.Quasithin.Background.InternalSecB51
public import CFSG.Quasithin.Background.FFC4Ord3
public import CFSG.Quasithin.EmptyFaithful.Insp9Ord

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin
open scoped IsMulCommutative

namespace KG12614

section Group

variable {Γ : Type*} [Group Γ]

theorem le_or_inf_eq_bot {K N : Subgroup Γ} (hK : IsSimpleGroup ↥K)
    (hKN : K ≤ Subgroup.normalizer (N : Set Γ)) : K ≤ N ∨ K ⊓ N = ⊥ := by
  have : (N.subgroupOf K).Normal := Subgroup.normal_subgroupOf_of_le_normalizer hKN
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (N.subgroupOf K) with h | h
  · right
    rw [Subgroup.subgroupOf_eq_bot] at h
    exact disjoint_iff.1 h.symm
  · exact Or.inl (Subgroup.subgroupOf_eq_top.1 h)

theorem le_normalizer_of_commute {H₁ H₂ : Subgroup Γ} (h : ∀ a ∈ H₁, ∀ b ∈ H₂, a * b = b * a) :
    H₁ ≤ Subgroup.normalizer (H₂ : Set Γ) := by
  intro a ha
  rw [Subgroup.mem_normalizer_iff]
  intro b
  constructor
  · intro hb
    rw [h a ha b hb, mul_inv_cancel_right]
    exact hb
  · intro hb
    have e := h a⁻¹ (H₁.inv_mem ha) _ hb
    have e2 : b = a⁻¹ * (a * b * a⁻¹) * a := by group
    rw [e2, e, inv_mul_cancel_right]
    exact hb

theorem eq_one_of_pow_two_pow {x : Γ} {k : ℕ} (h2 : x ^ 2 ^ k = 1) (h3 : x ^ 3 = 1) : x = 1 := by
  have h := Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one h2) (orderOf_dvd_of_pow_eq_one h3)
  rw [(Nat.Coprime.pow_left k (by norm_num : Nat.Coprime 2 3)).gcd_eq_one, Nat.dvd_one,
    orderOf_eq_one_iff] at h
  exact h

end Group

end KG12614

open KG12614

theorem factM22M23NoFF_of
    (h56 : AsB56) : FactM22M23NoFF := by
  intro G _ _ W X K _ hW2 hXW hS hO2 hKX hXK hiso hpow hFF
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hV : ∀ w : ↥W, w ^ 2 = 1 := fun w => Subtype.ext (by simpa using hW2 w w.2)
  set A := autOn X W with hA
  set Kb := autOn K W with hKbdef
  set J := ffJ A with hJdef
  have hJ1 : J ≠ ⊥ := InternalSec.ffJ_ne_bot_of_isFFModule hV hFF
  have hB : B53Hyp J := InternalSec.b53Hyp_ffJ_autOn hXW hS hO2
  have hcases := h56 ↥W hV J hJ1 hB
  have hJA : J ≤ A := B6.ffJ_le A
  have hAJ : A ≤ Subgroup.normalizer (J : Set (MulAut ↥W)) := B6.le_normalizer_ffJ A
  have hKbA : Kb ≤ A := InternalSec.autOn_le_autOn_of_le hKX
  have hAKb : A ≤ Subgroup.normalizer (Kb : Set (MulAut ↥W)) := by
    intro a ha
    rw [Subgroup.mem_normalizer_iff]
    intro b
    refine ⟨fun hb => InternalSec.autOn_normal_of hXK a ha b hb, fun hb => ?_⟩
    have := InternalSec.autOn_normal_of hXK a⁻¹ (A.inv_mem ha) _ hb
    rwa [show a⁻¹ * (a * b * a⁻¹) * a⁻¹⁻¹ = b by group] at this
  have hpowA : ∀ a ∈ A, ∃ k : ℕ, a ^ 2 ^ k ∈ Kb := by
    intro a ha
    obtain ⟨⟨x, hxN⟩, hxX, rfl⟩ := QuasithinUnique.Setup.mem_autOn_iff.1 ha
    obtain ⟨k, hk⟩ := hpow x hxX
    refine ⟨k, ?_⟩
    rw [← map_pow]
    exact QuasithinUnique.Setup.mem_autOn_iff.2 ⟨_, by simpa using hk, rfl⟩
  have hKbs : IsSimpleGroup ↥Kb := by
    rcases hiso with he | he
    · obtain ⟨e⟩ := he
      exact (MulEquiv.isSimpleGroup_congr e).2 CFSG.Sporadic.Mathieu.fam_m22_simplicity.2.2
    · obtain ⟨e⟩ := he
      exact (MulEquiv.isSimpleGroup_congr e).2 CFSG.Sporadic.Mathieu.fam_m23_simplicity.2.2
  have hKbc : Nat.card ↥Kb = 443520 ∨ Nat.card ↥Kb = 10200960 := by
    rcases hiso with he | he
    · obtain ⟨e⟩ := he
      left
      rw [Nat.card_congr e.toEquiv, CFSG.Sporadic.Mathieu.card_M22]
    · obtain ⟨e⟩ := he
      right
      rw [Nat.card_congr e.toEquiv, CFSG.Sporadic.Mathieu.nativeM23_eq]
      exact (Nat.card_eq_fintype_card (α := CFSG.M23.M23Group.H0)).trans
        CFSG.M23.M23Group.card_M23
  have hno3 : ∀ H : Subgroup (MulAut ↥W), H ≤ A → Kb ⊓ H = ⊥ → ∀ x : ↥H, x ^ 3 = 1 → x = 1 := by
    intro H hHA hH x hx3
    obtain ⟨k, hk⟩ := hpowA x (hHA x.2)
    have hk1 : (x : MulAut ↥W) ^ 2 ^ k ∈ Kb ⊓ H := ⟨hk, H.pow_mem x.2 _⟩
    rw [hH, Subgroup.mem_bot] at hk1
    have hx3' : (x : MulAut ↥W) ^ 3 = 1 := by simpa using congrArg Subtype.val hx3
    exact Subtype.ext (eq_one_of_pow_two_pow hk1 hx3')
  have hKbJ : Kb ≤ J := by
    rcases le_or_inf_eq_bot hKbs (hKbA.trans hAJ) with h | h
    · exact h
    · exfalso
      apply hJ1
      have h2 : IsPGroup 2 ↥J := by
        rintro ⟨j, hj⟩
        obtain ⟨k, hk⟩ := hpowA j (hJA hj)
        have hk1 : j ^ 2 ^ k ∈ Kb ⊓ J := ⟨hk, J.pow_mem hj _⟩
        rw [h, Subgroup.mem_bot] at hk1
        exact ⟨k, Subtype.ext (by simpa using hk1)⟩
      have hle := le_pCoreOf_of_le_normalizer hJA hAJ h2
      rw [hO2] at hle
      exact le_bot_iff.1 hle
  have hKb1 : ¬ Kb ≤ ⊥ := by
    intro h
    have := Subgroup.card_le_of_le h
    rw [Subgroup.card_bot] at this
    rcases hKbc with h' | h' <;> omega
  rcases hcases with h1 | ⟨⟨e⟩, -, -⟩ | ⟨G₁, G₂, hsup, hinf, hcomm, hf₁, hf₂, -⟩ |
      ⟨G₁, G₂, t, hJt, -, hcomm, -, hc₂, -, -, -, -, -, -, ht₂, -, -⟩ |
      ⟨G₁, G₂, hsup, hinf, hcomm, -, ⟨e₁⟩, -⟩
  ·
    obtain ⟨hq, -, hlist⟩ := h1
    set L := quasithinGenFitting J with hLdef
    have hLJ : L ≤ J := quasithinGenFitting_le J
    have hJL : J ≤ Subgroup.normalizer (L : Set (MulAut ↥W)) := le_normalizer_quasithinGenFitting J
    have hKbL : Kb ≤ L := by
      rcases le_or_inf_eq_bot hKbs (hKbJ.trans hJL) with h | h
      · exact h
      · exfalso
        have h2 : IsPGroup 2 ↥L := by
          rintro ⟨l, hl⟩
          obtain ⟨k, hk⟩ := hpowA l (hJA (hLJ hl))
          have hk1 : l ^ 2 ^ k ∈ Kb ⊓ L := ⟨hk, L.pow_mem hl _⟩
          rw [h, Subgroup.mem_bot] at hk1
          exact ⟨k, Subtype.ext (by simpa using hk1)⟩
        have hle := le_pCoreOf_of_le_normalizer hLJ hJL h2
        rw [hB.1] at hle
        obtain ⟨-, -, a, b, hab⟩ := hq
        apply hab
        induction a using QuotientGroup.induction_on with
        | H a =>
          have ha : a = 1 := Subtype.ext (Subgroup.mem_bot.1 (hle a.2))
          rw [ha, QuotientGroup.mk_one, one_mul, mul_one]
    have hLKb : L ≤ Kb := by
      have hperf : Group.IsPerfect ↥L := hq.1
      have hn : (Kb.subgroupOf L).Normal :=
        Subgroup.normal_subgroupOf_of_le_normalizer (hLJ.trans (hJA.trans hAKb))
      have hQ : IsPGroup 2 (↥L ⧸ Kb.subgroupOf L) := by
        intro q
        induction q using QuotientGroup.induction_on with
        | H l =>
          obtain ⟨k, hk⟩ := hpowA l (hJA (hLJ l.2))
          refine ⟨k, ?_⟩
          rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
          simpa using hk
      by_contra hne
      have : Nontrivial (↥L ⧸ Kb.subgroupOf L) := by
        rw [← not_subsingleton_iff_nontrivial, QuotientGroup.subsingleton_iff]
        intro htop
        exact hne (Subgroup.subgroupOf_eq_top.1 htop)
      have : Group.IsNilpotent (↥L ⧸ Kb.subgroupOf L) := hQ.isNilpotent
      have : Group.IsPerfect (↥L ⧸ Kb.subgroupOf L) :=
        Group.IsPerfect.ofSurjective (f := QuotientGroup.mk' (Kb.subgroupOf L))
          (QuotientGroup.mk'_surjective _)
      exact Group.IsPerfect.not_isSolvable (↥L ⧸ Kb.subgroupOf L) inferInstance
    have hcard : Nat.card ↥L = Nat.card ↥Kb := by rw [le_antisymm hLKb hKbL]
    have h8 : ¬ 2 ^ 8 ∣ Nat.card ↥L := by
      rw [hcard]
      rcases hKbc with h | h <;> rw [h] <;> decide
    have hc := Insp9.b56QL_card_le7 hlist h8
    rw [hcard] at hc
    rcases hKbc with h | h <;> rw [h] at hc <;> revert hc <;> decide
  ·
    have h6 := Subgroup.card_le_of_le hKbJ
    rw [Nat.card_congr e.toEquiv, Nat.card_perm, Nat.card_fin] at h6
    rcases hKbc with h | h <;> rw [h] at h6 <;> revert h6 <;> decide
  ·
    have hG₁J : G₁ ≤ J := by rw [← hsup]; exact le_sup_left
    have hG₂J : G₂ ≤ J := by rw [← hsup]; exact le_sup_right
    have hN₁ : J ≤ Subgroup.normalizer (G₁ : Set (MulAut ↥W)) := by
      rw [← hsup]
      exact sup_le Subgroup.le_normalizer
        (le_normalizer_of_commute fun b hb a ha => (hcomm a ha b hb).symm)
    have hN₂ : J ≤ Subgroup.normalizer (G₂ : Set (MulAut ↥W)) := by
      rw [← hsup]
      exact sup_le (le_normalizer_of_commute hcomm) Subgroup.le_normalizer
    have hK₁ : Kb ≤ G₁ := by
      rcases le_or_inf_eq_bot hKbs (hKbJ.trans hN₁) with h | h
      · exact h
      · obtain ⟨x, hx1, hx3⟩ := FFC.exists_order_three_of_factorList hf₁
        exact absurd (hno3 G₁ (hG₁J.trans hJA) h x hx3) hx1
    have hK₂ : Kb ≤ G₂ := by
      rcases le_or_inf_eq_bot hKbs (hKbJ.trans hN₂) with h | h
      · exact h
      · obtain ⟨x, hx1, hx3⟩ := FFC.exists_order_three_of_factorList hf₂
        exact absurd (hno3 G₂ (hG₂J.trans hJA) h x hx3) hx1
    exact hKb1 (hinf ▸ le_inf hK₁ hK₂)
  ·
    have hG₂J : G₂ ≤ J := by rw [hJt]; exact le_sup_right.trans le_sup_left
    have hN₂ : J ≤ Subgroup.normalizer (G₂ : Set (MulAut ↥W)) := by
      rw [hJt]
      exact sup_le (sup_le (le_normalizer_of_commute hcomm) Subgroup.le_normalizer)
        ((Subgroup.zpowers_le (H := Subgroup.normalizer (G₂ : Set (MulAut ↥W)))).2 ht₂)
    rcases le_or_inf_eq_bot hKbs (hKbJ.trans hN₂) with h | h
    · have h3 := Subgroup.card_le_of_le h
      rw [hc₂] at h3
      rcases hKbc with h' | h' <;> omega
    · have : Nontrivial ↥G₂ := Finite.one_lt_card_iff_nontrivial.1 (by rw [hc₂]; norm_num)
      obtain ⟨x, hx1⟩ := exists_ne (1 : ↥G₂)
      have hx3 : x ^ 3 = 1 := by rw [← hc₂]; exact pow_card_eq_one'
      exact hx1 (hno3 G₂ (hG₂J.trans hJA) h x hx3)
  ·
    have hG₁J : G₁ ≤ J := by rw [← hsup]; exact le_sup_left
    have hN₁ : J ≤ Subgroup.normalizer (G₁ : Set (MulAut ↥W)) := by
      rw [← hsup]
      exact sup_le Subgroup.le_normalizer
        (le_normalizer_of_commute fun b hb a ha => (hcomm a ha b hb).symm)
    rcases le_or_inf_eq_bot hKbs (hKbJ.trans hN₁) with h | h
    · have h168 := Subgroup.card_le_of_le h
      rw [Nat.card_congr e₁.toEquiv, card_statedSL_three1527d, Nat.card_zmod] at h168
      rcases hKbc with h' | h' <;> rw [h'] at h168 <;> revert h168 <;> decide
    · have hf : B56FactorList ↥G₁ :=
        Or.inr (Or.inr ⟨1, ZMod 2, inferInstance, inferInstance, le_rfl, odd_one,
          by rw [Nat.card_zmod, pow_one], ⟨e₁⟩⟩)
      obtain ⟨x, hx1, hx3⟩ := FFC.exists_order_three_of_factorList hf
      exact hx1 (hno3 G₁ (hG₁J.trans hJA) h x hx3)

end CFSG.Quasithin.H13
