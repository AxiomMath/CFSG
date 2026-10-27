module

public import CFSG.Open.LocalVocabulary
public import CFSG.GroupTheory.ABGLocalTools.Basic

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.TwelveThirteen

open Subgroup CFSG.Open CFSG.ABGLocalTools
open scoped Pointwise

variable {K : Type} [Group K] [Finite K]

private theorem card_setMul_mul_card_inf (A B : Subgroup K) :
    Nat.card ↥((A : Set K) * (B : Set K)) * Nat.card ↥(A ⊓ B) = Nat.card ↥A * Nat.card ↥B := by
  have h1 := Subgroup.card_mul_eq_card_subgroup_mul_card_quotient B (A : Set K)
  have himg : Nat.card ↥((A : Set K).image ((↑) : K → K ⧸ B)) = B.relIndex A := by
    have horb : MulAction.orbit ↥A ((1 : K) : K ⧸ B) = (A : Set K).image ((↑) : K → K ⧸ B) := by
      ext y
      constructor
      · rintro ⟨a, rfl⟩
        exact ⟨(a : K), a.2, by simp [Subgroup.smul_def]⟩
      · rintro ⟨a, ha, rfl⟩
        exact ⟨⟨a, ha⟩, by simp [Subgroup.smul_def]⟩
    have hstab : MulAction.stabilizer ↥A ((1 : K) : K ⧸ B) = B.subgroupOf A := by
      ext a
      rw [MulAction.mem_stabilizer_iff, Subgroup.mem_subgroupOf]
      have : (a • ((1 : K) : K ⧸ B)) = ((a : K) : K ⧸ B) := by
        simp [Subgroup.smul_def]
      rw [this, QuotientGroup.eq]
      constructor
      · intro h
        simpa using B.inv_mem h
      · intro h
        simpa using B.inv_mem h
    have := MulAction.index_stabilizer ↥A ((1 : K) : K ⧸ B)
    rw [hstab] at this
    rw [← horb, Nat.card_coe_set_eq, ← this]
    rfl
  have h2 := Subgroup.relIndex_mul_card (H := B) (K := A)
  rw [inf_comm B A] at h2
  rw [h1, himg]
  calc Nat.card ↥B * B.relIndex A * Nat.card ↥(A ⊓ B)
      = Nat.card ↥B * (B.relIndex A * Nat.card ↥(A ⊓ B)) := by ring
    _ = Nat.card ↥A * Nat.card ↥B := by rw [h2, mul_comm]

private theorem exists_mem_conj {p : ℕ} [Fact p.Prime] {P P' J : Subgroup K}
    (h : IsSylowOf p P J) (h' : IsSylowOf p P' J) :
    ∃ k ∈ J, ∀ x : K, x ∈ P' ↔ k⁻¹ * x * k ∈ P := by
  obtain ⟨Q, rfl⟩ := h
  obtain ⟨Q', rfl⟩ := h'
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq J Q Q'
  have key : ∀ y : J, y ∈ (Q' : Subgroup J) ↔ g⁻¹ * y * g ∈ (Q : Subgroup J) := by
    intro y
    rw [← hg]
    change y ∈ MulAut.conj g • (Q : Subgroup J) ↔ _
    rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem, MulAut.smul_def, MulAut.conj_inv_apply]
  refine ⟨g, g.2, fun x => ?_⟩
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨g⁻¹ * y * g, (key y).mp hy, by simp⟩
  · rintro ⟨z, hz, hzx⟩
    have hzx' : (z : K) = (g : K)⁻¹ * x * g := hzx
    have hx : x = (g : K) * z * (g : K)⁻¹ := by rw [hzx']; group
    have hxK : x ∈ J := by
      rw [hx]
      exact J.mul_mem (J.mul_mem g.2 z.2) (J.inv_mem g.2)
    refine ⟨⟨x, hxK⟩, (key _).mpr ?_, rfl⟩
    have : g⁻¹ * ⟨x, hxK⟩ * g = z := Subtype.ext (by
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      exact hzx'.symm)
    rw [this]
    exact hz

theorem coe_sup_eq_mul {Γ T J C : Subgroup K} (hT : IsSylowOf 2 T Γ) (hJ : J ≤ Γ)
    (hTJ : T ≤ normalizer (J : Set K))
    (h23 : ∀ p : ℕ, p.Prime → p ∣ Nat.card J → p = 2 ∨ p = 3) (hC : IsSylowOf 3 C J) :
    ((J ⊔ T : Subgroup K) : Set K) = (C : Set K) * (T : Set K) ∧
      (C : Set K) * (T : Set K) = (T : Set K) * (C : Set K) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hset : ((J ⊔ T : Subgroup K) : Set K) = (J : Set K) * (T : Set K) :=
    coe_mul_of_right_le_normalizer_left J T hTJ
  have hTH : IsSylowOf 2 T (J ⊔ T) := hT.of_le le_sup_right (sup_le hJ hT.le)
  have hCT : C ⊓ T = ⊥ :=
    disjoint_iff.1 (IsPGroup.disjoint_of_ne 3 2 (by norm_num) C T hC.isPGroup hT.isPGroup)
  have hJT := card_setMul_mul_card_inf J T
  rw [← hset] at hJT
  change Nat.card ↥(J ⊔ T) * Nat.card ↥(J ⊓ T) = Nat.card J * Nat.card T at hJT
  have hCTc := card_setMul_mul_card_inf C T
  rw [hCT] at hCTc
  simp only [Subgroup.card_bot, mul_one] at hCTc
  obtain ⟨a, ha⟩ := IsPGroup.iff_card.1 (hT.isPGroup.to_le (inf_le_right : J ⊓ T ≤ T))
  have hpos : ∀ H : Subgroup K, Nat.card H ≠ 0 := fun H => Nat.card_pos.ne'
  have hv3 : (Nat.card ↥(J ⊔ T)).factorization 3 = (Nat.card J).factorization 3 := by
    have h1 : (Nat.card ↥(J ⊔ T) * Nat.card ↥(J ⊓ T)).factorization 3 =
        (Nat.card J * Nat.card T).factorization 3 := by rw [hJT]
    rw [Nat.factorization_mul (hpos _) (hpos _), Nat.factorization_mul (hpos _) (hpos _),
      ha, hT.card_eq] at h1
    simpa [Nat.Prime.factorization_pow, Nat.prime_two.factorization] using h1
  have hprimes : ∀ p : ℕ, p.Prime → p ∣ Nat.card ↥(J ⊔ T) → p = 2 ∨ p = 3 := by
    intro p hp hdvd
    have : p ∣ Nat.card J * Nat.card T := hJT ▸ dvd_mul_of_dvd_left hdvd _
    rcases (Nat.Prime.dvd_mul hp).1 this with h | h
    · exact h23 p hp h
    · left
      rw [hT.card_eq] at h
      exact (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 (hp.dvd_of_dvd_pow h)
  have hcardH : Nat.card ↥(J ⊔ T) = Nat.card C * Nat.card T := by
    rw [hC.card_eq, hTH.card_eq, ← hv3]
    have hsupp : (Nat.card ↥(J ⊔ T)).factorization.support ⊆ {2, 3} := by
      intro p hp
      rw [Nat.support_factorization] at hp
      rcases hprimes p (Nat.prime_of_mem_primeFactors hp) (Nat.dvd_of_mem_primeFactors hp) with
        h | h <;> simp [h]
    conv_lhs => rw [← Nat.factorization_prod_pow_eq_self (hpos (J ⊔ T))]
    rw [Finsupp.prod_of_support_subset _ hsupp _ (fun _ _ => pow_zero _),
      Finset.prod_pair (by norm_num), mul_comm]
  have hsub : (C : Set K) * (T : Set K) ⊆ ((J ⊔ T : Subgroup K) : Set K) := by
    rw [hset]
    exact Set.mul_subset_mul_right (fun x hx => hC.le hx)
  have heq : (C : Set K) * (T : Set K) = ((J ⊔ T : Subgroup K) : Set K) := by
    refine Set.eq_of_subset_of_ncard_le hsub ?_ (Set.toFinite _)
    rw [← Nat.card_coe_set_eq, ← Nat.card_coe_set_eq, hCTc]
    exact hcardH.le
  refine ⟨heq.symm, ?_⟩
  have h1 : ((J ⊔ T : Subgroup K) : Set K)⁻¹ = ((J ⊔ T : Subgroup K) : Set K) := inv_coe_set
  rw [heq, ← h1, ← heq, mul_inv_rev, inv_coe_set, inv_coe_set]

theorem exists_inv_mul_mem_normalizer {p : ℕ} [Fact p.Prime] {J C : Subgroup K}
    (hC : IsSylowOf p C J) {t : K} (ht : t ∈ normalizer (J : Set K)) :
    ∃ j ∈ J, j⁻¹ * t ∈ normalizer (C : Set K) := by
  set C' : Subgroup K := C.map (MulAut.conj t).toMonoidHom with hC'
  have hC'J : C' ≤ J := by
    rintro _ ⟨c, hc, rfl⟩
    exact (mem_normalizer_iff.1 ht c).1 (hC.le hc)
  have hC'card : Nat.card C' = Nat.card C :=
    Subgroup.card_map_of_injective (MulAut.conj t).injective
  have hsyl : IsSylowOf p C' J := isSylowOf_of_card hC'J (hC'card.trans hC.card_eq)
  obtain ⟨k, hkJ, hk⟩ := exists_mem_conj hC hsyl
  refine ⟨k, hkJ, mem_normalizer_iff.2 fun h => ?_⟩
  have hmem : t * h * t⁻¹ ∈ C' ↔ h ∈ C := by
    constructor
    · rintro ⟨c, hc, hch⟩
      have hch' : t * c * t⁻¹ = t * h * t⁻¹ := hch
      have : c = h := by simpa using hch'
      rwa [← this]
    · intro hh
      exact ⟨h, hh, rfl⟩
  have e : k⁻¹ * (t * h * t⁻¹) * k = k⁻¹ * t * h * (k⁻¹ * t)⁻¹ := by group
  rw [← hmem, hk, e]

private theorem mem_of_zpow_mem {W : Subgroup K} {c : K} (h : c ^ 3 = 1) {m : ℤ}
    (hm : c ^ m ∈ W) (hm1 : c ^ m ≠ 1) : c ∈ W := by
  have h3 : c ^ (3 : ℕ) = 1 := h
  rw [zpow_eq_zpow_emod' m h3] at hm hm1
  have : m % ((3 : ℕ) : ℤ) = 0 ∨ m % ((3 : ℕ) : ℤ) = 1 ∨ m % ((3 : ℕ) : ℤ) = 2 := by omega
  rcases this with h0 | h1 | h2
  · rw [h0, zpow_zero] at hm1
    exact absurd rfl hm1
  · rw [h1, zpow_one] at hm
    exact hm
  · rw [h2] at hm
    have hc : c = (c ^ (2 : ℤ)) ^ (2 : ℤ) := by
      rw [← zpow_mul]
      have : c ^ ((2 : ℤ) * 2) = c ^ (3 : ℕ) * c := by
        rw [show ((2 : ℤ) * 2) = ((3 : ℕ) : ℤ) + 1 by norm_num, zpow_add, zpow_natCast, zpow_one]
      rw [this, h3, one_mul]
    rw [hc]
    exact W.zpow_mem hm 2

private theorem exists_zpow_mul_zpow {c₁ c₂ w : K} (hc : c₁ * c₂ = c₂ * c₁)
    (hw : w ∈ closure ({c₁, c₂} : Set K)) : ∃ m n : ℤ, c₁ ^ m * c₂ ^ n = w := by
  have hcomm : Commute c₁ c₂ := hc
  have hle : zpowers c₁ ≤ normalizer ((zpowers c₂ : Subgroup K) : Set K) := by
    refine le_trans ?_ (centralizer_le_normalizer _)
    rw [zpowers_le, mem_centralizer_iff]
    intro y hy
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 hy
    exact (hcomm.symm.zpow_left k).eq
  have hcl : closure ({c₁, c₂} : Set K) = zpowers c₁ ⊔ zpowers c₂ := by
    rw [← Set.singleton_union, Subgroup.closure_union, ← zpowers_eq_closure, ← zpowers_eq_closure]
  rw [hcl] at hw
  have hw' : w ∈ ((zpowers c₁ ⊔ zpowers c₂ : Subgroup K) : Set K) := hw
  rw [coe_mul_of_left_le_normalizer_right _ _ hle] at hw'
  obtain ⟨a, ha, b, hb, rfl⟩ := Set.mem_mul.1 hw'
  obtain ⟨m, rfl⟩ := mem_zpowers_iff.1 ha
  obtain ⟨n, rfl⟩ := mem_zpowers_iff.1 hb
  exact ⟨m, n, rfl⟩

theorem irrOn_of_witnesses {N : Subgroup K} {c₁ c₂ t₁ t₂ : K} (h₁ : c₁ ^ 3 = 1)
    (h₂ : c₂ ^ 3 = 1) (hc : c₁ * c₂ = c₂ * c₁) (ht₁ : t₁ ∈ N) (ht₂ : t₂ ∈ N)
    (h21 : t₂ * c₁ * t₂⁻¹ = c₁⁻¹) (h22 : t₂ * c₂ * t₂⁻¹ = c₂)
    (h11 : t₁ * c₁ * t₁⁻¹ ∈ zpowers c₂) (h12 : t₁ * c₂ * t₁⁻¹ ∈ zpowers c₁) :
    ∀ W : Subgroup K, W ≤ closure {c₁, c₂} → N ≤ normalizer (W : Set K) →
      W = ⊥ ∨ W = closure {c₁, c₂} := by
  intro W hW hN
  have hconjW : ∀ t ∈ N, ∀ w ∈ W, t * w * t⁻¹ ∈ W := fun t ht w hw =>
    (mem_normalizer_iff.1 (hN ht) w).1 hw
  have hsplit : ∀ m n : ℤ, c₁ ^ m * c₂ ^ n ∈ W → c₁ ^ m ∈ W ∧ c₂ ^ n ∈ W := by
    intro m n hw
    have hconj : t₂ * (c₁ ^ m * c₂ ^ n) * t₂⁻¹ = c₁ ^ (-m) * c₂ ^ n := by
      have := map_mul (MulAut.conj t₂) (c₁ ^ m) (c₂ ^ n)
      rw [map_zpow, map_zpow, MulAut.conj_apply, MulAut.conj_apply, MulAut.conj_apply, h21,
        h22, inv_zpow', ] at this
      exact this
    have h2m : c₁ ^ (2 * m) ∈ W := by
      have hmem := W.mul_mem hw (W.inv_mem (hconjW t₂ ht₂ _ hw))
      rw [hconj] at hmem
      have e : c₁ ^ m * c₂ ^ n * (c₁ ^ (-m) * c₂ ^ n)⁻¹ = c₁ ^ (2 * m) := by
        rw [mul_inv_rev, zpow_neg, inv_inv, two_mul, zpow_add, mul_assoc, mul_inv_cancel_left]
      rwa [e] at hmem
    have hm : c₁ ^ m ∈ W := by
      have h4 : (c₁ ^ (2 * m)) ^ (2 : ℤ) = c₁ ^ m := by
        rw [← zpow_mul, show 2 * m * 2 = 3 * m + m by ring, zpow_add, zpow_mul,
          show c₁ ^ (3 : ℤ) = 1 from by exact_mod_cast h₁, one_zpow, one_mul]
      rw [← h4]
      exact W.zpow_mem h2m 2
    refine ⟨hm, ?_⟩
    have := W.mul_mem (W.inv_mem hm) hw
    rwa [← mul_assoc, inv_mul_cancel, one_mul] at this
  have h12W : c₁ ∈ W → c₁ ≠ 1 → c₂ ∈ W := by
    intro hc₁ hne
    obtain ⟨k, hk⟩ := mem_zpowers_iff.1 h11
    refine mem_of_zpow_mem h₂ (m := k) ?_ ?_
    · rw [hk]
      exact hconjW t₁ ht₁ c₁ hc₁
    · rw [hk]
      intro h
      apply hne
      have := congrArg (fun x => t₁⁻¹ * x * t₁) h
      simpa [mul_assoc] using this
  have h21W : c₂ ∈ W → c₂ ≠ 1 → c₁ ∈ W := by
    intro hc₂ hne
    obtain ⟨k, hk⟩ := mem_zpowers_iff.1 h12
    refine mem_of_zpow_mem h₁ (m := k) ?_ ?_
    · rw [hk]
      exact hconjW t₁ ht₁ c₂ hc₂
    · rw [hk]
      intro h
      apply hne
      have := congrArg (fun x => t₁⁻¹ * x * t₁) h
      simpa [mul_assoc] using this
  rcases W.bot_or_exists_ne_one with hbot | ⟨w, hwW, hw1⟩
  · exact Or.inl hbot
  right
  obtain ⟨m, n, hmn⟩ := exists_zpow_mul_zpow hc (hW hwW)
  have hmn' : c₁ ^ m * c₂ ^ n ∈ W := hmn ▸ hwW
  obtain ⟨hm, hn⟩ := hsplit m n hmn'
  have hboth : c₁ ∈ W ∧ c₂ ∈ W := by
    by_cases hm1 : c₁ ^ m = 1
    · have hn1 : c₂ ^ n ≠ 1 := by
        intro hn1
        apply hw1
        rw [← hmn, hm1, hn1, one_mul]
      have hc₂ : c₂ ∈ W := mem_of_zpow_mem h₂ hn hn1
      have hc₂1 : c₂ ≠ 1 := fun h => hn1 (by rw [h, one_zpow])
      exact ⟨h21W hc₂ hc₂1, hc₂⟩
    · have hc₁ : c₁ ∈ W := mem_of_zpow_mem h₁ hm hm1
      have hc₁1 : c₁ ≠ 1 := fun h => hm1 (by rw [h, one_zpow])
      exact ⟨hc₁, h12W hc₁ hc₁1⟩
  refine le_antisymm hW ?_
  rw [closure_le]
  intro x hx
  rcases hx with rfl | rfl
  · exact hboth.1
  · exact hboth.2

variable {L : Type} [Group L] [Finite L]

theorem card_comap_of_injective {ρ : K →* L} (hρ : Function.Injective ρ) {P : Subgroup L}
    (hP : P ≤ ρ.range) : Nat.card (P.comap ρ) = Nat.card P := by
  rw [← Subgroup.card_map_of_injective hρ, Subgroup.map_comap_eq_self hP]

theorem isElemAbelian_comap_of_injective {ρ : K →* L} (hρ : Function.Injective ρ) {p : ℕ}
    {P : Subgroup L} (hP : IsElemAbelian p P) : IsElemAbelian p (P.comap ρ) := by
  refine ⟨⟨⟨fun a b => Subtype.ext (hρ ?_)⟩⟩, fun x hx => hρ ?_⟩
  · have := hP.1.is_comm.comm ⟨ρ a, a.2⟩ ⟨ρ b, b.2⟩
    simpa [map_mul] using congrArg Subtype.val this
  · rw [map_pow, hP.2 _ hx, map_one]

theorem mul_comm_comap_of_injective {ρ : K →* L} (hρ : Function.Injective ρ) {P : Subgroup L}
    (hP : P ≤ ρ.range) {T : Subgroup K}
    (hPT : (P : Set L) * (T.map ρ : Set L) = (T.map ρ : Set L) * (P : Set L)) :
    ((P.comap ρ : Subgroup K) : Set K) * (T : Set K) = (T : Set K) * (P.comap ρ : Set K) := by
  have lift : ∀ {A B : Set L} {A' B' : Set K}, (∀ a ∈ A, ∃ a' ∈ A', ρ a' = a) →
      (∀ b ∈ B, ∃ b' ∈ B', ρ b' = b) → ∀ g, ρ g ∈ A * B → g ∈ A' * B' := by
    intro A B A' B' hA hB g hg
    obtain ⟨a, ha, b, hb, hab⟩ := Set.mem_mul.1 hg
    obtain ⟨a', ha', rfl⟩ := hA a ha
    obtain ⟨b', hb', rfl⟩ := hB b hb
    exact Set.mem_mul.2 ⟨a', ha', b', hb', hρ (by rw [map_mul, hab])⟩
  have hPr : ∀ a ∈ (P : Set L), ∃ a' ∈ ((P.comap ρ : Subgroup K) : Set K), ρ a' = a := by
    intro a ha
    obtain ⟨a', rfl⟩ := hP ha
    exact ⟨a', ha, rfl⟩
  have hTr : ∀ b ∈ (T.map ρ : Set L), ∃ b' ∈ (T : Set K), ρ b' = b := by
    rintro _ ⟨b', hb', rfl⟩
    exact ⟨b', hb', rfl⟩
  ext g
  constructor
  · intro hg
    obtain ⟨x, hx, y, hy, rfl⟩ := Set.mem_mul.1 hg
    refine lift hTr hPr _ ?_
    rw [← hPT, map_mul]
    exact Set.mem_mul.2 ⟨ρ x, hx, ρ y, ⟨y, hy, rfl⟩, rfl⟩
  · intro hg
    obtain ⟨x, hx, y, hy, rfl⟩ := Set.mem_mul.1 hg
    refine lift hPr hTr _ ?_
    rw [hPT, map_mul]
    exact Set.mem_mul.2 ⟨ρ x, ⟨x, hx, rfl⟩, ρ y, hy, rfl⟩

theorem irr_comap_of_injective {ρ : K →* L} (hρ : Function.Injective ρ) {P : Subgroup L}
    (hP : P ≤ ρ.range) {T : Subgroup K}
    (hirr : ∀ W : Subgroup L, W ≤ P → normalizer (P : Set L) ⊓ T.map ρ ≤ normalizer (W : Set L) →
      W = ⊥ ∨ W = P) :
    ∀ W : Subgroup K, W ≤ P.comap ρ →
      normalizer ((P.comap ρ : Subgroup K) : Set K) ⊓ T ≤ normalizer (W : Set K) →
        W = ⊥ ∨ W = P.comap ρ := by
  intro W hW hN
  have hWP : W.map ρ ≤ P := (Subgroup.map_mono hW).trans (Subgroup.map_comap_le _ _)
  have hN' : normalizer (P : Set L) ⊓ T.map ρ ≤ normalizer ((W.map ρ : Subgroup L) : Set L) := by
    rintro y ⟨hyP, t, ht, rfl⟩
    have htN : t ∈ normalizer ((P.comap ρ : Subgroup K) : Set K) := by
      rw [mem_normalizer_iff]
      intro x
      change ρ x ∈ P ↔ ρ (t * x * t⁻¹) ∈ P
      rw [map_mul, map_mul, map_inv]
      exact mem_normalizer_iff.1 hyP (ρ x)
    have htW := hN ⟨htN, ht⟩
    rw [mem_normalizer_iff]
    intro z
    constructor
    · rintro ⟨w, hw, rfl⟩
      exact ⟨t * w * t⁻¹, (mem_normalizer_iff.1 htW w).1 hw, by simp [map_mul, map_inv]⟩
    · rintro ⟨w, hw, hwz⟩
      have hzP : z ∈ P := by
        have hz : ρ t * z * (ρ t)⁻¹ ∈ P := hwz ▸ hWP ⟨w, hw, rfl⟩
        exact (mem_normalizer_iff.1 hyP z).2 hz
      obtain ⟨z', rfl⟩ := hP hzP
      refine ⟨z', (mem_normalizer_iff.1 htW z').2 ?_, rfl⟩
      have : t * z' * t⁻¹ = w := hρ (by rw [hwz]; simp [map_mul, map_inv])
      rw [this]
      exact hw
  rcases hirr _ hWP hN' with h | h
  · left
    exact (Subgroup.map_eq_bot_iff_of_injective W hρ).1 h
  · right
    rw [← h, Subgroup.comap_map_eq_self_of_injective hρ]

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.TwelveThirteen
