module

public import CFSG.RankThree.GroupTheory.SteinbergBMRelativeMinimalFrattini
public import CFSG.GroupTheory.HyperplaneGeneration

public section

namespace CFSG.RankThree.GroupTheory.SteinbergBM

open Subgroup CFSG.LocalAnalysis.ComponentInitial

theorem actionCommutator_mono {A X : Type*} [Group A] [Group X] [MulDistribMulAction A X]
    {K K' : Subgroup X} (h : K ≤ K') : actionCommutator A K ≤ actionCommutator A K' :=
  closure_mono fun _ ⟨k, hk, a, hka⟩ => ⟨k, h hk, a, hka⟩

theorem card_inf_of_index_eq_prime {p : ℕ} (hp : p.Prime) {A : Type*} [Group A] [Finite A]
    (hcomm : ∀ x y : A, x * y = y * x) (hA : Nat.card A = p ^ 3) {K K' : Subgroup A}
    (hK : K.index = p) (hK' : K'.index = p) (hne : K ≠ K') :
    Nat.card (K ⊓ K' : Subgroup A) = p := by
  have hKn : K.Normal := ⟨fun n hn g => by rwa [hcomm g n, mul_inv_cancel_right]⟩
  have hcardK : ∀ L : Subgroup A, L.index = p → Nat.card L = p ^ 2 := fun L hL => by
    have h := L.card_mul_index
    rw [hL, hA] at h
    have hp0 : 0 < p := hp.pos
    exact Nat.eq_of_mul_eq_mul_right hp0 (by rw [h]; ring)
  have hsup : K ⊔ K' = ⊤ := by
    have hdvd : (K ⊔ K').index ∣ p := hK ▸ index_dvd_of_le le_sup_left
    rcases (Nat.dvd_prime hp).mp hdvd with h | h
    · exact index_eq_one.mp h
    · exfalso
      have h1 := relIndex_mul_index (le_sup_left : K ≤ K ⊔ K')
      rw [h, hK] at h1
      have h2 : K.relIndex (K ⊔ K') = 1 := by
        have hp0 : 0 < p := hp.pos
        exact Nat.eq_of_mul_eq_mul_right hp0 (by rw [h1, one_mul])
      have hK'K : K' ≤ K := le_sup_right.trans (relIndex_eq_one.mp h2)
      exact hne (eq_of_le_of_card_ge hK'K (by rw [hcardK K hK, hcardK K' hK'])).symm
  have hrel : (K ⊓ K').relIndex K' = p := by
    rw [inf_relIndex_right, ← relIndex_sup_right K' K, sup_comm, hsup, relIndex_top_right, hK]
  have hidx : (K ⊓ K').index = p ^ 2 := by
    rw [← relIndex_mul_index (inf_le_right : K ⊓ K' ≤ K'), hrel, hK', sq]
  have h := (K ⊓ K').card_mul_index
  rw [hidx, hA] at h
  have hp0 : 0 < p ^ 2 := pow_pos hp.pos 2
  exact Nat.eq_of_mul_eq_mul_right hp0 (by rw [h]; ring)

theorem faithful_rank_three_two_action_prescribed_actor_line_kernel_witness {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) {A S : Type*} [Group A] [Group S] [Finite A] [Finite S]
    [MulDistribMulAction A S] (hAe : CFSG.IsElementaryAbelian p A) (hAcard : Nat.card A = p ^ 3)
    (hS : IsPGroup 2 S) (hfaith : ∀ c : A, (∀ s : S, c • s = s) → c = 1) {a : A}
    (ha : a ≠ 1) :
    ∃ b : A, b ∉ zpowers a ∧
      (actionCommutator A (actionCommutator A (CFSG.fixedPointSubgroup (zpowers b) S)) =
        actionCommutator A (CFSG.fixedPointSubgroup (zpowers b) S)) ∧
      (∀ c : A, (∀ x ∈ actionCommutator A (CFSG.fixedPointSubgroup (zpowers b) S), c • x = x) ↔
        c ∈ zpowers b) ∧
      (∃ x ∈ actionCommutator A (CFSG.fixedPointSubgroup (zpowers b) S), a • x ≠ x) ∧
      actionCommutator A (CFSG.fixedPointSubgroup (zpowers b) S) ≠ ⊥ ∧
      (∀ c : A, ∀ x ∈ actionCommutator A (CFSG.fixedPointSubgroup (zpowers b) S),
        c • x ∈ actionCommutator A (CFSG.fixedPointSubgroup (zpowers b) S)) ∧
      actionCommutator A (CFSG.fixedPointSubgroup (zpowers b) S) ≤
        CFSG.fixedPointSubgroup (zpowers b) S ∧
      IsPGroup 2 (actionCommutator A (CFSG.fixedPointSubgroup (zpowers b) S)) := by
  have : Fact p.Prime := ⟨hp⟩
  have : CFSG.IsElementaryAbelian p A := hAe
  have hcomm : ∀ x y : A, x * y = y * x := fun x y => hAe.is_comm.comm x y
  have hpow : ∀ x : A, x ^ p = 1 := fun x =>
    Monoid.exponent_dvd_iff_forall_pow_eq_one.mp (CFSG.IsElementaryAbelian.exponent_dvd_p p A) x
  have h2A : ¬ 2 ∣ Nat.card A := by
    rw [hAcard]
    intro h
    exact hp2 ((Nat.prime_dvd_prime_iff_eq Nat.prime_two hp).mp
      (Nat.prime_two.dvd_of_dvd_pow h)).symm
  have hpS : ¬ p ∣ Nat.card S := by
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hS
    rw [hk]
    intro h
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp (hp.dvd_of_dvd_pow h))
  have hAnt : Nontrivial A := by
    rw [← Finite.one_lt_card_iff_nontrivial, hAcard]
    exact Nat.one_lt_pow (by norm_num) hp.one_lt
  have hline : ∀ x : A, x ≠ 1 → Nat.card (zpowers x) = p := fun x hx => by
    rw [Nat.card_zpowers, orderOf_eq_prime (hpow x) hx]
  have hCinv : ∀ K : Subgroup A, ∀ c : A, ∀ s ∈ CFSG.fixedPointSubgroup K S,
      c • s ∈ CFSG.fixedPointSubgroup K S := by
    intro K c s hs k
    change (k : A) • c • s = c • s
    rw [smul_smul, hcomm, mul_smul]
    exact congrArg (c • ·) (hs k)
  have hWinv : ∀ K : Subgroup A, ∀ c : A, ∀ x ∈ actionCommutator A (CFSG.fixedPointSubgroup K S),
      c • x ∈ actionCommutator A (CFSG.fixedPointSubgroup K S) := fun K c x hx =>
    smul_mem_actionCommutator_of_invariant (hCinv K) c hx
  have hWW : ∀ K : Subgroup A, actionCommutator A (actionCommutator A
      (CFSG.fixedPointSubgroup K S)) = actionCommutator A (CFSG.fixedPointSubgroup K S) :=
    fun K => actionCommutator_actionCommutator_of_isPGroup Nat.prime_two
      (hS.to_subgroup _) h2A (hCinv K)
  have hWC : ∀ K : Subgroup A, actionCommutator A (CFSG.fixedPointSubgroup K S) ≤
      CFSG.fixedPointSubgroup K S := fun K => actionCommutator_le_of_invariant (hCinv K)
  have hkernel : ∀ K : Subgroup A, K.index = p →
      actionCommutator A (CFSG.fixedPointSubgroup K S) ≠ ⊥ →
      ∀ c : A, (∀ x ∈ actionCommutator A (CFSG.fixedPointSubgroup K S), c • x = x) → c ∈ K := by
    intro K hK hW c hc
    set F := fixingSubgroup A ((actionCommutator A (CFSG.fixedPointSubgroup K S) : Subgroup S) :
      Set S) with hFdef
    have hKF : K ≤ F := fun k hk => (mem_fixingSubgroup_iff A).mpr fun x hx =>
      hWC K hx ⟨k, hk⟩
    have hFtop : F ≠ ⊤ := by
      intro h
      apply hW
      rw [← hWW K, eq_bot_iff]
      refine (closure_le _).2 ?_
      rintro _ ⟨x, hx, d, rfl⟩
      have hdF : d ∈ F := by
        rw [h]
        exact mem_top d
      have hd : d • x = x := (mem_fixingSubgroup_iff A).mp hdF x hx
      rw [hd, inv_mul_cancel]
      exact one_mem _
    have hFK : F = K := by
      have hdvd : F.index ∣ p := hK ▸ index_dvd_of_le hKF
      rcases (Nat.dvd_prime hp).mp hdvd with h | h
      · exact absurd (index_eq_one.mp h) hFtop
      · symm
        refine eq_of_le_of_card_ge hKF ?_
        have h1 := F.card_mul_index
        have h2 := K.card_mul_index
        rw [h] at h1
        rw [hK] at h2
        have hp0 : 0 < p := hp.pos
        exact (Nat.eq_of_mul_eq_mul_right hp0 (h1.trans h2.symm)).le
    rw [← hFK]
    exact (mem_fixingSubgroup_iff A).mpr hc
  have htriv : ∀ c : A, (∀ K : Subgroup A, K.index = p →
      actionCommutator A (CFSG.fixedPointSubgroup K S) ≠ ⊥ → c ∈ K) → c = 1 := by
    intro c hc
    apply hfaith c
    have hgen := CFSG.SolvableHall.coprime_hyperplane_generation (p := p) (A := A) (H := S) hpS
    have hle : (⨆ (B : Subgroup A) (_ : B.index = p), CFSG.fixedPointSubgroup B S) ≤
        CFSG.fixedPointSubgroup (zpowers c) S := by
      refine iSup₂_le fun B hB s hs => ?_
      rw [CFSG.SolvableHall.mem_fixedPointSubgroup_zpowers_iff]
      by_cases hW : actionCommutator A (CFSG.fixedPointSubgroup B S) = ⊥
      · have h := gen_mem_actionCommutator (A := A) hs c
        rw [hW, mem_bot, inv_mul_eq_one] at h
        exact h.symm
      · exact hs ⟨c, hc B hB hW⟩
    intro s
    have hs : s ∈ CFSG.fixedPointSubgroup (zpowers c) S := hle (hgen ▸ mem_top s)
    exact (CFSG.SolvableHall.mem_fixedPointSubgroup_zpowers_iff c s).mp hs
  have hcardK : ∀ K : Subgroup A, K.index = p → Nat.card K = p ^ 2 := fun K hK => by
    have h := K.card_mul_index
    rw [hK, hAcard] at h
    exact Nat.eq_of_mul_eq_mul_right hp.pos (by rw [h]; ring)
  obtain ⟨K₁, hK₁, hW₁⟩ : ∃ K : Subgroup A, K.index = p ∧
      actionCommutator A (CFSG.fixedPointSubgroup K S) ≠ ⊥ := by
    by_contra hcon
    simp only [not_exists, not_and, not_not] at hcon
    obtain ⟨x, hx⟩ := exists_ne (1 : A)
    exact hx (htriv x fun K hK hW => absurd (hcon K hK) hW)
  obtain ⟨K₂, hK₂, hW₂, h12⟩ : ∃ K : Subgroup A, K.index = p ∧
      actionCommutator A (CFSG.fixedPointSubgroup K S) ≠ ⊥ ∧ K ≠ K₁ := by
    by_contra hcon
    simp only [not_exists, not_and, not_not] at hcon
    have hb : K₁ = ⊥ := eq_bot_iff.mpr fun x hx => mem_bot.mpr (htriv x fun K hK hW =>
      (hcon K hK hW) ▸ hx)
    have := hcardK K₁ hK₁
    rw [hb, card_bot] at this
    have : 1 < p ^ 2 := Nat.one_lt_pow two_ne_zero hp.one_lt
    omega
  have hℓ := card_inf_of_index_eq_prime hp hcomm hAcard hK₁ hK₂ (Ne.symm h12)
  obtain ⟨K₃, hK₃, hW₃, h3⟩ : ∃ K : Subgroup A, K.index = p ∧
      actionCommutator A (CFSG.fixedPointSubgroup K S) ≠ ⊥ ∧ ¬ K₁ ⊓ K₂ ≤ K := by
    by_contra hcon
    simp only [not_exists, not_and, not_not] at hcon
    have hb : K₁ ⊓ K₂ = ⊥ := eq_bot_iff.mpr fun x hx => mem_bot.mpr (htriv x fun K hK hW =>
      hcon K hK hW hx)
    rw [hb, card_bot] at hℓ
    exact hp.one_lt.ne hℓ
  have h13 : K₁ ≠ K₃ := fun h => h3 (h ▸ inf_le_left)
  have hℓ' := card_inf_of_index_eq_prime hp hcomm hAcard hK₁ hK₃ h13
  obtain ⟨M₁, M₂, hM₁, hM₂, hWM₁, hWM₂, hMa, hMcard⟩ : ∃ M₁ M₂ : Subgroup A, M₁.index = p ∧
      M₂.index = p ∧ actionCommutator A (CFSG.fixedPointSubgroup M₁ S) ≠ ⊥ ∧
      actionCommutator A (CFSG.fixedPointSubgroup M₂ S) ≠ ⊥ ∧ M₁ ⊓ M₂ ≠ zpowers a ∧
      Nat.card (M₁ ⊓ M₂ : Subgroup A) = p := by
    by_cases h : K₁ ⊓ K₂ = zpowers a
    · refine ⟨K₁, K₃, hK₁, hK₃, hW₁, hW₃, fun h' => h3 ?_, hℓ'⟩
      rw [h, ← h']
      exact inf_le_right
    · exact ⟨K₁, K₂, hK₁, hK₂, hW₁, hW₂, h, hℓ⟩
  have hne : M₁ ⊓ M₂ ≠ ⊥ := fun h => by
    rw [h, card_bot] at hMcard
    exact hp.one_lt.ne hMcard
  obtain ⟨⟨b, hb⟩, hb1'⟩ := ne_bot_iff_exists_ne_one.mp hne
  have hb1 : b ≠ 1 := fun h => hb1' (Subtype.ext h)
  have hbline : zpowers b = M₁ ⊓ M₂ :=
    eq_of_le_of_card_ge (zpowers_le.mpr hb) (by rw [hMcard, hline b hb1])
  have hab : ∀ x : A, x ≠ 1 → ∀ y : A, y ∈ zpowers x → y ≠ 1 → zpowers y = zpowers x :=
    fun x hx y hy hy1 => eq_of_le_of_card_ge (zpowers_le.mpr hy) (by rw [hline x hx, hline y hy1])
  have hbna : b ∉ zpowers a := fun h => hMa (by rw [← hbline, hab a ha b h hb1])
  have hanb : a ∉ zpowers b := fun h => hbna (by rw [hab b hb1 a h ha]; exact mem_zpowers b)
  have hWMQ : ∀ M : Subgroup A, zpowers b ≤ M → actionCommutator A (CFSG.fixedPointSubgroup M S) ≤
      actionCommutator A (CFSG.fixedPointSubgroup (zpowers b) S) := fun M hM =>
    actionCommutator_mono fun s hs k => hs ⟨k, hM k.2⟩
  have hQiff : ∀ c : A, (∀ x ∈ actionCommutator A (CFSG.fixedPointSubgroup (zpowers b) S),
      c • x = x) ↔ c ∈ zpowers b := by
    intro c
    constructor
    · intro hc
      rw [hbline]
      exact ⟨hkernel M₁ hM₁ hWM₁ c fun x hx => hc x (hWMQ M₁ (hbline ▸ inf_le_left) hx),
        hkernel M₂ hM₂ hWM₂ c fun x hx => hc x (hWMQ M₂ (hbline ▸ inf_le_right) hx)⟩
    · intro hc x hx
      exact hWC (zpowers b) hx ⟨c, hc⟩
  refine ⟨b, hbna, hWW (zpowers b), hQiff, ?_, ?_, hWinv (zpowers b), hWC (zpowers b),
    hS.to_subgroup _⟩
  · by_contra hcon
    simp only [not_exists, not_and, not_not] at hcon
    exact hanb ((hQiff a).mp hcon)
  · exact fun h => hWM₁ (le_bot_iff.mp (h ▸ hWMQ M₁ (hbline ▸ inf_le_left)))

end CFSG.RankThree.GroupTheory.SteinbergBM
