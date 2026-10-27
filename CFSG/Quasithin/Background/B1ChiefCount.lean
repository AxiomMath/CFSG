module

public import CFSG.Quasithin.Background.B1MoreChief

public section

namespace CFSG.Quasithin.ChiefCount

open scoped commutatorElement Pointwise

variable {G : Type*} [Group G]

theorem commutator_le_of_le_normalizer {A X : Subgroup G}
    (h : X ≤ Subgroup.normalizer (A : Set G)) : ⁅A, X⁆ ≤ A := by
  rw [Subgroup.commutator_le]
  intro a ha x hx
  have h1 : x * a⁻¹ * x⁻¹ ∈ A := (Subgroup.mem_normalizer_iff.mp (h hx) a⁻¹).mp (A.inv_mem ha)
  have e : ⁅a, x⁆ = a * (x * a⁻¹ * x⁻¹) := by
    rw [commutatorElement_def]
    group
  rw [e]
  exact A.mul_mem ha h1

theorem mem_normalizer_sup {A B : Subgroup G} {g : G}
    (hA : g ∈ Subgroup.normalizer (A : Set G)) (hB : g ∈ Subgroup.normalizer (B : Set G)) :
    g ∈ Subgroup.normalizer ((A ⊔ B : Subgroup G) : Set G) := by
  rw [Subgroup.mem_normalizer_iff_map_conj_eq] at hA hB ⊢
  rw [Subgroup.map_sup, hA, hB]

theorem mem_normalizer_inf {A B : Subgroup G} {g : G}
    (hA : g ∈ Subgroup.normalizer (A : Set G)) (hB : g ∈ Subgroup.normalizer (B : Set G)) :
    g ∈ Subgroup.normalizer ((A ⊓ B : Subgroup G) : Set G) :=
  Subgroup.inf_normalizer_le_normalizer_inf ⟨hA, hB⟩

theorem inf_sup_le {H K J : Subgroup G} (hHK : H ≤ K)
    (hHJ : H ≤ Subgroup.normalizer (J : Set G)) : K ⊓ (H ⊔ J) ≤ H ⊔ (K ⊓ J) := by
  rintro g ⟨hgK, hgHJ⟩
  have hg : g ∈ (H : Set G) * (J : Set G) := by
    rw [← Subgroup.coe_mul_of_left_le_normalizer_right H J hHJ]
    exact hgHJ
  obtain ⟨h, hh, j, hj, rfl⟩ := Set.mem_mul.mp hg
  have hjK : j ∈ K := by
    have := K.mul_mem (K.inv_mem (hHK hh)) hgK
    simpa using this
  exact Subgroup.mul_mem_sup hh ⟨hjK, hj⟩

theorem commutator_sup_le {H B X : Subgroup G} (hH : ⁅H, X⁆ ≤ B)
    (hXB : X ≤ Subgroup.normalizer (B : Set G)) (hHB : H ≤ Subgroup.normalizer (B : Set G)) :
    ⁅H ⊔ B, X⁆ ≤ B := by
  rw [Subgroup.commutator_le]
  intro y hy x hx
  have hy' : y ∈ (H : Set G) * (B : Set G) := by
    rw [← Subgroup.coe_mul_of_left_le_normalizer_right H B hHB]
    exact hy
  obtain ⟨h, hh, b, hb, rfl⟩ := Set.mem_mul.mp hy'
  have hbx : ⁅b, x⁆ ∈ B := by
    have h1 : x * b⁻¹ * x⁻¹ ∈ B :=
      (Subgroup.mem_normalizer_iff.mp (hXB hx) b⁻¹).mp (B.inv_mem hb)
    have e : ⁅b, x⁆ = b * (x * b⁻¹ * x⁻¹) := by
      rw [commutatorElement_def]
      group
    rw [e]
    exact B.mul_mem hb h1
  have hhx : ⁅h, x⁆ ∈ B := hH (Subgroup.commutator_mem_commutator hh hx)
  have hc : h * ⁅b, x⁆ * h⁻¹ ∈ B := (Subgroup.mem_normalizer_iff.mp (hHB hh) _).mp hbx
  have e : ⁅h * b, x⁆ = h * ⁅b, x⁆ * h⁻¹ * ⁅h, x⁆ := by
    simp only [commutatorElement_def]
    group
  rw [e]
  exact B.mul_mem hc hhx

@[expose] def HasNCBetween (X N₁ N₂ : Subgroup G) (k : ℕ) : Prop :=
  ∃ A B : Fin k → Subgroup G, (∀ i, IsTwoChiefFactor X (A i) (B i) ∧ ¬ ⁅A i, X⁆ ≤ B i ∧
    N₁ ≤ B i ∧ A i ≤ N₂) ∧ ∀ i j, i < j → A i ≤ B j

@[expose] def NCAtMost (X N₁ N₂ : Subgroup G) (c : ℕ) : Prop :=
  ¬ HasNCBetween X N₁ N₂ (c + 1)

theorem HasNCBetween.of_le {X N₁ N₂ : Subgroup G} {k k' : ℕ} (h : HasNCBetween X N₁ N₂ k)
    (hk : k' ≤ k) : HasNCBetween X N₁ N₂ k' := by
  obtain ⟨A, B, hAB, hle⟩ := h
  refine ⟨fun i => A (Fin.castLE hk i), fun i => B (Fin.castLE hk i), fun i => hAB _,
    fun i j hij => hle _ _ ?_⟩
  rw [Fin.lt_def] at hij ⊢
  simpa using hij

theorem HasNCBetween.mono {X N₁ N₂ N₁' N₂' : Subgroup G} {k : ℕ} (h : HasNCBetween X N₁ N₂ k)
    (h₁ : N₁' ≤ N₁) (h₂ : N₂ ≤ N₂') : HasNCBetween X N₁' N₂' k := by
  obtain ⟨A, B, hAB, hle⟩ := h
  exact ⟨A, B, fun i => ⟨(hAB i).1, (hAB i).2.1, h₁.trans (hAB i).2.2.1,
    (hAB i).2.2.2.trans h₂⟩, hle⟩

theorem NCAtMost.mono {X N₁ N₂ : Subgroup G} {c c' : ℕ} (h : NCAtMost X N₁ N₂ c)
    (hc : c ≤ c') : NCAtMost X N₁ N₂ c' := fun h' => h (h'.of_le (by omega))

theorem inf_factor {X A B N : Subgroup G} (hc : IsTwoChiefFactor X A B) (hn : ¬ ⁅A, X⁆ ≤ B)
    (hXN : X ≤ Subgroup.normalizer (N : Set G)) (hin : ¬ A ⊓ N ≤ B) :
    IsTwoChiefFactor X (A ⊓ N) (B ⊓ N) ∧ ¬ ⁅A ⊓ N, X⁆ ≤ B ⊓ N := by
  obtain ⟨hBA, hAX, hXA, hXB, hmin, h2⟩ := hc
  have hXAN : X ≤ Subgroup.normalizer ((A ⊓ N : Subgroup G) : Set G) := fun x hx =>
    mem_normalizer_inf (hXA hx) (hXN hx)
  have hXBN : X ≤ Subgroup.normalizer ((B ⊓ N : Subgroup G) : Set G) := fun x hx =>
    mem_normalizer_inf (hXB hx) (hXN hx)
  have hANB : A ⊓ N ≤ Subgroup.normalizer (B : Set G) := (inf_le_left.trans hAX).trans hXB
  have hAB : (A ⊓ N) ⊔ B = A := by
    by_contra hne
    refine hmin ((A ⊓ N) ⊔ B) (lt_of_le_of_ne le_sup_right fun h => hin ?_)
      (lt_of_le_of_ne (sup_le inf_le_left hBA.le) hne) fun x hx =>
        mem_normalizer_sup (hXAN hx) (hXB hx)
    rw [h]
    exact le_sup_left
  refine ⟨⟨lt_of_le_of_ne (inf_le_inf_right N hBA.le) fun h => hin (h ▸ inf_le_left),
    inf_le_left.trans hAX, hXAN, hXBN, fun C hC1 hC2 hXC => ?_, fun a ha => ?_⟩, fun hle => ?_⟩
  ·
    have hCN : C ≤ N := hC2.le.trans inf_le_right
    have hCB : C ≤ Subgroup.normalizer (B : Set G) :=
      hC2.le.trans (inf_le_left.trans (hAX.trans hXB))
    by_cases h1 : C ⊔ B = B
    · exact (not_le_of_gt hC1) (le_inf (h1 ▸ le_sup_left) hCN)
    by_cases h3 : C ⊔ B = A
    · apply (not_le_of_gt hC2)
      have h4 : N ⊓ (C ⊔ B) ≤ C ⊔ (N ⊓ B) := inf_sup_le hCN hCB
      rw [h3, inf_comm N A, inf_comm N B] at h4
      exact h4.trans (sup_le le_rfl hC1.le)
    exact hmin (C ⊔ B) (lt_of_le_of_ne le_sup_right (Ne.symm h1))
      (lt_of_le_of_ne (sup_le (hC2.le.trans inf_le_left) hBA.le) h3) fun x hx =>
        mem_normalizer_sup (hXC hx) (hXB hx)
  ·
    obtain ⟨k, hk⟩ := h2 a ha.1
    exact ⟨k, hk, N.pow_mem ha.2 _⟩
  ·
    apply hn
    rw [← hAB]
    exact commutator_sup_le (hle.trans inf_le_left) hXB hANB

theorem pow_mul_mem {N : Subgroup G} {a n : G} (ha : a ∈ Subgroup.normalizer (N : Set G))
    (hn : n ∈ N) : ∀ m : ℕ, ∃ n' ∈ N, (a * n) ^ m = a ^ m * n'
  | 0 => ⟨1, N.one_mem, by simp⟩
  | m + 1 => by
    obtain ⟨n', hn', e⟩ := pow_mul_mem ha hn m
    refine ⟨a⁻¹ * n' * a * n, N.mul_mem ?_ hn, ?_⟩
    · have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ ha) n').mp hn'
      simpa using this
    · rw [pow_succ, e, pow_succ]
      group

theorem sup_factor {X A B N : Subgroup G} (hc : IsTwoChiefFactor X A B) (hn : ¬ ⁅A, X⁆ ≤ B)
    (hXN : X ≤ Subgroup.normalizer (N : Set G)) (hNX : N ≤ X) (hab : A ⊓ N ≤ B) :
    IsTwoChiefFactor X (A ⊔ N) (B ⊔ N) ∧ ¬ ⁅A ⊔ N, X⁆ ≤ B ⊔ N := by
  obtain ⟨hBA, hAX, hXA, hXB, hmin, h2⟩ := hc
  have hAN : A ≤ Subgroup.normalizer (N : Set G) := hAX.trans hXN
  have hBN : B ≤ Subgroup.normalizer (N : Set G) := hBA.le.trans hAN
  have hNA : N ≤ Subgroup.normalizer (A : Set G) := hNX.trans hXA
  have hded : A ⊓ (B ⊔ N) ≤ B := (inf_sup_le hBA.le hBN).trans (sup_le le_rfl hab)
  refine ⟨⟨lt_of_le_of_ne (sup_le_sup_right hBA.le N) fun h => ?_, sup_le hAX hNX,
    fun x hx => mem_normalizer_sup (hXA hx) (hXN hx),
    fun x hx => mem_normalizer_sup (hXB hx) (hXN hx), fun C hC1 hC2 hXC => ?_,
    fun x hx => ?_⟩, fun hle => ?_⟩
  ·
    apply (not_le_of_gt hBA)
    refine le_trans ?_ hded
    exact le_inf le_rfl (h ▸ le_sup_left)
  ·
    have hNC : N ≤ C := le_sup_right.trans hC1.le
    have hBC : B ≤ C := le_sup_left.trans hC1.le
    have hNC' : N ≤ Subgroup.normalizer (A : Set G) := hNA
    by_cases h1 : C ⊓ A = B
    · apply (not_le_of_gt hC1)
      have h3 : C ⊓ (N ⊔ A) ≤ N ⊔ (C ⊓ A) := inf_sup_le hNC hNC'
      rw [sup_comm N A, inf_of_le_left hC2.le, h1, sup_comm] at h3
      exact h3
    by_cases h4 : C ⊓ A = A
    · apply (not_le_of_gt hC2)
      exact sup_le (h4 ▸ inf_le_left) hNC
    exact hmin (C ⊓ A) (lt_of_le_of_ne (le_inf hBC hBA.le) (Ne.symm h1))
      (lt_of_le_of_ne inf_le_right h4) fun x hx => mem_normalizer_inf (hXC hx) (hXA hx)
  ·
    have hx' : x ∈ (A : Set G) * (N : Set G) := by
      rw [← Subgroup.coe_mul_of_left_le_normalizer_right A N hAN]
      exact hx
    obtain ⟨a, ha, n, hn', rfl⟩ := Set.mem_mul.mp hx'
    obtain ⟨k, hk⟩ := h2 a ha
    obtain ⟨n', hn'', e⟩ := pow_mul_mem (hAN ha) hn' (2 ^ k)
    refine ⟨k, ?_⟩
    rw [e]
    exact Subgroup.mul_mem_sup hk hn''
  ·
    apply hn
    refine le_trans (le_inf ?_ ?_) hded
    · exact commutator_le_of_le_normalizer hXA
    · exact (Subgroup.commutator_mono le_sup_left le_rfl).trans hle

theorem split {X N₁ N N₂ : Subgroup G} (hN₁ : N₁ ≤ N) (hN₂ : N ≤ N₂) (hN₂X : N₂ ≤ X)
    (hXN : X ≤ Subgroup.normalizer (N : Set G)) {a b : ℕ}
    (h : HasNCBetween X N₁ N₂ (a + b + 1)) :
    HasNCBetween X N₁ N (a + 1) ∨ HasNCBetween X N N₂ (b + 1) := by
  classical
  obtain ⟨A, B, hAB, hle⟩ := h
  set s : Finset (Fin (a + b + 1)) := Finset.univ.filter fun i => ¬ A i ⊓ N ≤ B i with hs
  by_cases hcard : a + 1 ≤ s.card
  · left
    let g : Fin (a + 1) → Fin (a + b + 1) := fun j => s.orderEmbOfFin rfl (Fin.castLE hcard j)
    have hg : ∀ j, g j ∈ s := fun j => s.orderEmbOfFin_mem rfl _
    have hgm : StrictMono g := fun i j hij =>
      (s.orderEmbOfFin rfl).strictMono (by rw [Fin.lt_def] at hij ⊢; simpa using hij)
    refine ⟨fun j => A (g j) ⊓ N, fun j => B (g j) ⊓ N, fun j => ?_, fun i j hij =>
      inf_le_inf_right N (hle _ _ (hgm hij))⟩
    have hj : ¬ A (g j) ⊓ N ≤ B (g j) := (Finset.mem_filter.mp (hg j)).2
    obtain ⟨hc, hn, h1, -⟩ := hAB (g j)
    obtain ⟨hc', hn'⟩ := inf_factor hc hn hXN hj
    exact ⟨hc', hn', le_inf h1 hN₁, inf_le_right⟩
  · right
    have hcard' : b + 1 ≤ sᶜ.card := by
      rw [Finset.card_compl, Fintype.card_fin]
      omega
    let g : Fin (b + 1) → Fin (a + b + 1) := fun j => sᶜ.orderEmbOfFin rfl (Fin.castLE hcard' j)
    have hg : ∀ j, g j ∈ sᶜ := fun j => sᶜ.orderEmbOfFin_mem rfl _
    have hgm : StrictMono g := fun i j hij =>
      (sᶜ.orderEmbOfFin rfl).strictMono (by rw [Fin.lt_def] at hij ⊢; simpa using hij)
    refine ⟨fun j => A (g j) ⊔ N, fun j => B (g j) ⊔ N, fun j => ?_, fun i j hij =>
      sup_le_sup_right (hle _ _ (hgm hij)) N⟩
    have hj : A (g j) ⊓ N ≤ B (g j) := by
      have := hg j
      rw [Finset.mem_compl, Finset.mem_filter] at this
      push Not at this
      exact this (Finset.mem_univ _)
    obtain ⟨hc, hn, -, h2⟩ := hAB (g j)
    obtain ⟨hc', hn'⟩ := sup_factor hc hn hXN (hN₂.trans hN₂X) hj
    exact ⟨hc', hn', le_sup_right, sup_le h2 hN₂⟩

theorem NCAtMost.add {X N₁ N N₂ : Subgroup G} {a b : ℕ} (h₁ : NCAtMost X N₁ N a)
    (h₂ : NCAtMost X N N₂ b) (hN₁ : N₁ ≤ N) (hN₂ : N ≤ N₂) (hN₂X : N₂ ≤ X)
    (hXN : X ≤ Subgroup.normalizer (N : Set G)) : NCAtMost X N₁ N₂ (a + b) := fun h =>
  (split hN₁ hN₂ hN₂X hXN h).elim h₁ h₂

theorem ncAtMost_zero_of_commutator_le {X N₁ N₂ : Subgroup G} (h : ⁅N₂, X⁆ ≤ N₁) :
    NCAtMost X N₁ N₂ 0 := by
  rintro ⟨A, B, hAB, -⟩
  obtain ⟨-, hn, h1, h2⟩ := hAB 0
  exact hn (((Subgroup.commutator_mono h2 le_rfl).trans h).trans h1)

theorem ncAtMost_zero_top {X N : Subgroup G}
    (hB : ∀ B : Subgroup G, N ≤ B → B ≤ X → X ≤ Subgroup.normalizer (B : Set G) →
      B = N ∨ B = X)
    (hX : ¬ ∀ x ∈ X, ∃ k : ℕ, x ^ 2 ^ k ∈ N) : NCAtMost X N X 0 := by
  rintro ⟨A, B, hAB, -⟩
  obtain ⟨⟨hBA, hAX, hXA, hXB, -, h2⟩, -, hNB, -⟩ := hAB 0
  rcases hB (B 0) hNB (hBA.le.trans hAX) hXB with hB0 | hB0
  · rcases hB (A 0) (hNB.trans hBA.le) hAX hXA with hA0 | hA0
    · exact absurd (hA0.trans hB0.symm) (ne_of_gt hBA)
    · apply hX
      intro x hx
      rw [← hA0] at hx
      rw [← hB0]
      exact h2 x hx
  · exact absurd (hAX.trans hB0.symm.le) (not_le_of_gt hBA)

theorem four_dvd_relIndex [Finite G] {X A B : Subgroup G} (hc : IsTwoChiefFactor X A B)
    (hn : ¬ ⁅A, X⁆ ≤ B) : 4 ∣ B.relIndex A := by
  obtain ⟨hBA, hAX, hXA, hXB, -, h2⟩ := hc
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hBn : (B.subgroupOf A).Normal :=
    Subgroup.normal_subgroupOf_of_le_normalizer (hAX.trans hXB)
  have hp : IsPGroup 2 (↥A ⧸ B.subgroupOf A) := by
    intro q
    induction q using QuotientGroup.induction_on with
    | H a =>
      obtain ⟨k, hk⟩ := h2 a a.2
      refine ⟨k, ?_⟩
      rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
      simpa using hk
  obtain ⟨m, hm⟩ := hp.exists_card_eq
  have hrel : B.relIndex A = 2 ^ m := hm
  rcases m with _ | _ | m
  · rw [pow_zero, Subgroup.relIndex_eq_one] at hrel
    exact absurd hrel (not_le_of_gt hBA)
  · exfalso
    apply hn
    rw [Subgroup.commutator_le]
    intro a ha x hx
    have hidx : (B.subgroupOf A).index = 2 := hrel
    have hxa : x * a⁻¹ * x⁻¹ ∈ A :=
      (Subgroup.mem_normalizer_iff.mp (hXA hx) a⁻¹).mp (A.inv_mem ha)
    have key := (Subgroup.mul_mem_iff_of_index_two hidx (a := ⟨a, ha⟩)
      (b := ⟨_, hxa⟩)).mpr (by
        rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
        show a ∈ B ↔ x * a⁻¹ * x⁻¹ ∈ B
        rw [← (Subgroup.mem_normalizer_iff.mp (hXB hx) a⁻¹), inv_mem_iff])
    rw [Subgroup.mem_subgroupOf] at key
    have e : ⁅a, x⁆ = a * (x * a⁻¹ * x⁻¹) := by
      rw [commutatorElement_def]
      group
    rw [e]
    exact key
  · rw [hrel]
    exact ⟨2 ^ m, by ring⟩

theorem pow_dvd_relIndex_of [Finite G] {X N₁ N₂ : Subgroup G} {k d : ℕ}
    (hd : ∀ A B : Subgroup G, IsTwoChiefFactor X A B → ¬ ⁅A, X⁆ ≤ B → N₁ ≤ B → A ≤ N₂ →
      d ∣ B.relIndex A)
    (h : HasNCBetween X N₁ N₂ k) : d ^ k ∣ N₁.relIndex N₂ := by
  obtain ⟨A, B, hAB, hle⟩ := h
  rcases k with _ | k
  · simp
  have key : ∀ i (hi : i < k + 1), d ^ (i + 1) ∣ N₁.relIndex (A ⟨i, hi⟩) := by
    intro i
    induction i with
    | zero =>
      intro hi
      obtain ⟨hc, hn, h1, h2⟩ := hAB ⟨0, hi⟩
      rw [← Subgroup.relIndex_mul_relIndex N₁ _ _ h1 hc.1.le, zero_add, pow_one]
      exact Dvd.dvd.mul_left (hd _ _ hc hn h1 h2) _
    | succ i ih =>
      intro hi
      obtain ⟨hc, hn, h1, h2⟩ := hAB ⟨i + 1, hi⟩
      have hlt : A ⟨i, by omega⟩ ≤ B ⟨i + 1, hi⟩ :=
        hle _ _ (Fin.mk_lt_mk.mpr (Nat.lt_succ_self i))
      have hN₁A : N₁ ≤ A ⟨i, by omega⟩ := (hAB ⟨i, by omega⟩).2.2.1.trans
        (hAB ⟨i, by omega⟩).1.1.le
      rw [← Subgroup.relIndex_mul_relIndex N₁ _ _ h1 hc.1.le,
        ← Subgroup.relIndex_mul_relIndex N₁ _ _ hN₁A hlt, pow_succ]
      exact Nat.mul_dvd_mul (Dvd.dvd.mul_right (ih (by omega)) _) (hd _ _ hc hn h1 h2)
  obtain ⟨hc, -, h1, h2⟩ := hAB ⟨k, Nat.lt_succ_self k⟩
  rw [← Subgroup.relIndex_mul_relIndex N₁ _ _ (h1.trans hc.1.le) h2]
  exact Dvd.dvd.mul_right (key k (Nat.lt_succ_self k)) _

theorem four_pow_dvd_relIndex [Finite G] {X N₁ N₂ : Subgroup G} {k : ℕ}
    (h : HasNCBetween X N₁ N₂ k) : 4 ^ k ∣ N₁.relIndex N₂ :=
  pow_dvd_relIndex_of (fun _ _ hc hn _ _ => four_dvd_relIndex hc hn) h

theorem ncAtMost_of_relIndex_lt_pow [Finite G] {X N₁ N₂ : Subgroup G} {c d : ℕ}
    (hd : ∀ A B : Subgroup G, IsTwoChiefFactor X A B → ¬ ⁅A, X⁆ ≤ B → N₁ ≤ B → A ≤ N₂ →
      d ∣ B.relIndex A)
    (h : N₁.relIndex N₂ < d ^ (c + 1)) : NCAtMost X N₁ N₂ c := by
  intro hc
  have h0 : N₁.relIndex N₂ ≠ 0 := Subgroup.index_ne_zero_of_finite
  exact absurd (Nat.le_of_dvd (Nat.pos_of_ne_zero h0) (pow_dvd_relIndex_of hd hc))
    (not_le.mpr h)

theorem ncAtMost_of_relIndex_lt [Finite G] {X N₁ N₂ : Subgroup G} {c : ℕ}
    (h : N₁.relIndex N₂ < 4 ^ (c + 1)) : NCAtMost X N₁ N₂ c :=
  ncAtMost_of_relIndex_lt_pow (fun _ _ hc hn _ _ => four_dvd_relIndex hc hn) h

theorem exists_ker_section [Finite G] {X A B : Subgroup G}
    (hAB : A ≤ Subgroup.normalizer (B : Set G)) (hXA : X ≤ Subgroup.normalizer (A : Set G))
    (hXB : X ≤ Subgroup.normalizer (B : Set G)) :
    ∃ C : Subgroup G, C ≤ X ∧ X ≤ Subgroup.normalizer (C : Set G) ∧
      (∀ x ∈ X, x ∈ C ↔ ∀ a ∈ A, ⁅a, x⁆ ∈ B) ∧ C.relIndex X ∣ (B.relIndex A).factorial := by
  classical
  have : (B.subgroupOf A).Normal := Subgroup.normal_subgroupOf_of_le_normalizer hAB
  let c : ↥X →* MulAut ↥A := A.normalizerMonoidHom.comp (Subgroup.inclusion hXA)
  have hcx : ∀ (x : ↥X) (a : ↥A), ((c x a : ↥A) : G) = (x : G) * a * (x : G)⁻¹ :=
    fun _ _ => rfl
  have hmemB : ∀ (x : ↥X) (a : ↥A), (c x a : ↥A) ∈ B.subgroupOf A ↔ a ∈ B.subgroupOf A := by
    intro x a
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf, hcx]
    exact (Subgroup.mem_normalizer_iff.mp (hXB x.2) a).symm
  have hc : ∀ x : ↥X, (B.subgroupOf A).map (c x : ↥A →* ↥A) = B.subgroupOf A := by
    intro x
    ext a
    constructor
    · rintro ⟨b, hb, rfl⟩
      exact (hmemB x b).mpr hb
    · intro ha
      refine ⟨(c x).symm a, ?_, (c x).apply_symm_apply a⟩
      show (c x).symm a ∈ B.subgroupOf A
      rw [← hmemB x, MulEquiv.apply_symm_apply]
      exact ha
  let φ : ↥X →* MulAut (↥A ⧸ B.subgroupOf A) :=
    { toFun := fun x => QuotientGroup.congr _ _ (c x) (hc x)
      map_one' := by
        ext q
        induction q using QuotientGroup.induction_on with
        | H a =>
          rw [QuotientGroup.congr_mk]
          simp
      map_mul' := fun x y => by
        ext q
        induction q using QuotientGroup.induction_on with
        | H a =>
          rw [MulAut.mul_apply, QuotientGroup.congr_mk, QuotientGroup.congr_mk,
            QuotientGroup.congr_mk, map_mul, MulAut.mul_apply] }
  have hφ : ∀ (x : ↥X) (a : ↥A), φ x (a : ↥A ⧸ B.subgroupOf A) = ((c x a : ↥A) :
      ↥A ⧸ B.subgroupOf A) := fun x a => QuotientGroup.congr_mk _ _ _ (hc x) a
  refine ⟨φ.ker.map X.subtype, Subgroup.map_subtype_le _, ?_, ?_, ?_⟩
  · have : (φ.ker.map X.subtype).subgroupOf X = φ.ker :=
      Subgroup.comap_map_eq_self_of_injective X.subtype_injective _
    rw [← Subgroup.normal_subgroupOf_iff_le_normalizer (Subgroup.map_subtype_le _), this]
    infer_instance
  · intro x hx
    have hmem : x ∈ φ.ker.map X.subtype ↔ (⟨x, hx⟩ : ↥X) ∈ φ.ker := by
      constructor
      · rintro ⟨y, hy, rfl⟩
        exact hy
      · intro h
        exact ⟨⟨x, hx⟩, h, rfl⟩
    rw [hmem, MonoidHom.mem_ker]
    constructor
    · intro h a ha
      have h1 := hφ ⟨x, hx⟩ ⟨a⁻¹, A.inv_mem ha⟩
      rw [h, MulAut.one_apply, QuotientGroup.eq, Subgroup.mem_subgroupOf] at h1
      have e : ⁅a, x⁆ = (((⟨a⁻¹, A.inv_mem ha⟩ : ↥A)⁻¹ * c ⟨x, hx⟩ ⟨a⁻¹, A.inv_mem ha⟩ : ↥A) :
          G) := by
        rw [Subgroup.coe_mul, Subgroup.coe_inv, hcx]
        simp only [commutatorElement_def, inv_inv]
        group
      rw [e]
      exact h1
    · intro h
      ext q
      induction q using QuotientGroup.induction_on with
      | H a =>
        rw [hφ, MulAut.one_apply, QuotientGroup.eq, Subgroup.mem_subgroupOf]
        have h1 := B.inv_mem (h _ (A.inv_mem a.2))
        have e : (((c ⟨x, hx⟩ a)⁻¹ * a : ↥A) : G) = (⁅(a : G)⁻¹, x⁆)⁻¹ := by
          rw [Subgroup.coe_mul, Subgroup.coe_inv, hcx]
          simp only [commutatorElement_def]
          group
        rw [e]
        exact h1
  · have hidx : (φ.ker.map X.subtype).relIndex X = Nat.card φ.range := by
      rw [Subgroup.relIndex, show (φ.ker.map X.subtype).subgroupOf X = φ.ker from
        Subgroup.comap_map_eq_self_of_injective X.subtype_injective _, Subgroup.index_ker]
    rw [hidx]
    have h1 : Nat.card φ.range ∣ Nat.card (MulAut (↥A ⧸ B.subgroupOf A)) :=
      Subgroup.card_subgroup_dvd_card _
    have hinj : Function.Injective (MulAut.toPerm (↥A ⧸ B.subgroupOf A)) := fun f g hfg => by
      ext q
      exact congrArg (fun σ : Equiv.Perm (↥A ⧸ B.subgroupOf A) => σ q) hfg
    have h2 : Nat.card (MulAut (↥A ⧸ B.subgroupOf A)) ∣
        Nat.card (Equiv.Perm (↥A ⧸ B.subgroupOf A)) := by
      rw [Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv]
      exact Subgroup.card_subgroup_dvd_card _
    rw [Nat.card_perm] at h2
    exact h1.trans h2

end CFSG.Quasithin.ChiefCount
