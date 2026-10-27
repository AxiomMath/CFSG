module

public import CFSG.RankThree.PartOne.AUTSL.SpWeights

public section

namespace CFSG.RankThree.PartOne.AUTSL

open scoped _root_.Classical

section Omega

theorem three_dvd_sum {α : Type*} (σ : α → α) (U : Finset α)
    (hσ3 : ∀ x ∈ U, σ (σ (σ x)) = x) (hfix : ∀ x ∈ U, σ x ≠ x) (N : α → ℕ)
    (hN : ∀ x ∈ U, N (σ x) = N x) :
    ∀ T : Finset α, T ⊆ U → (∀ x ∈ T, σ x ∈ T) → 3 ∣ ∑ x ∈ T, N x := by
  intro T
  induction' h : T.card using Nat.strong_induction_on with n ih generalizing T
  intro hTU hT
  by_cases hne : T.Nonempty
  · obtain ⟨x, hx⟩ := hne
    have hxU : x ∈ U := hTU hx
    have h1 : σ x ∈ T := hT x hx
    have h2 : σ (σ x) ∈ T := hT _ h1
    have hxs : x ≠ σ x := fun h => hfix x hxU h.symm
    have hsss : σ x ≠ σ (σ x) := fun h => hfix (σ x) (hTU h1) h.symm
    have hxss : x ≠ σ (σ x) := fun h => hfix x hxU (by
      have := hσ3 x hxU
      rw [← h] at this
      exact this)
    set O : Finset α := {x, σ x, σ (σ x)} with hO
    have hOT : O ⊆ T := by
      intro y hy
      simp only [hO, Finset.mem_insert, Finset.mem_singleton] at hy
      rcases hy with rfl | rfl | rfl <;> assumption
    have hOsum : ∑ y ∈ O, N y = 3 * N x := by
      rw [hO, Finset.sum_insert (by simp [hxs, hxss]), Finset.sum_insert (by simp [hsss]),
        Finset.sum_singleton, hN _ hxU, hN _ (hTU h1), hN _ hxU]
      ring
    have hcard : (T \ O).card < n := by
      rw [← h]
      exact Finset.card_lt_card (Finset.sdiff_ssubset hOT ⟨x, by simp [hO]⟩)
    have hclosed : ∀ y ∈ T \ O, σ y ∈ T \ O := by
      intro y hy
      rw [Finset.mem_sdiff] at hy ⊢
      have hyU : y ∈ U := hTU hy.1
      refine ⟨hT y hy.1, fun hyO => hy.2 ?_⟩
      simp only [hO, Finset.mem_insert, Finset.mem_singleton] at hyO ⊢
      rcases hyO with h | h | h
      ·
        right; right
        have := hσ3 y hyU
        rw [h] at this
        rw [← this]
      ·
        left
        have h3 := hσ3 y hyU
        have h4 := hσ3 x hxU
        rw [h] at h3
        rw [← h3, h4]
      ·
        right; left
        have h3 := hσ3 y hyU
        rw [h] at h3
        rw [← h3]
        exact hσ3 (σ x) (hTU h1)
    have hIH := ih _ hcard (T \ O) rfl ((Finset.sdiff_subset).trans hTU) hclosed
    rw [← Finset.sum_sdiff hOT, hOsum]
    exact dvd_add hIH (dvd_mul_right 3 _) |>.trans (by rw [add_comm])
  · rw [Finset.not_nonempty_iff_eq_empty.1 hne]
    simp

variable {B X ι : Type*} [CommGroup B] [CommGroup X] [Fintype ι]

theorem six_orbit_card (hB5 : ∀ b : B, b ^ 5 = 1) (θ : B ≃* B)
    (hθ : ∀ b, b * θ b * θ (θ b) = 1) (m : ℕ) (hm : ¬ 5 ∣ m) {a : B →* X} (ha : a ≠ 1) :
    ({a, twist θ m a, twist θ m (twist θ m a), a⁻¹, (twist θ m a)⁻¹,
      (twist θ m (twist θ m a))⁻¹} : Finset (B →* X)).card = 6 := by
  set b : B →* X := twist θ m a with hb_def
  set c : B →* X := twist θ m b with hc_def
  have hb1 : b ≠ 1 := fun h => ha (twist_eq_one hB5 θ hθ m hm h)
  have hc1 : c ≠ 1 := fun h => hb1 (twist_eq_one hB5 θ hθ m hm h)
  have ha5 : a ^ 5 = 1 := chars_pow_five hB5 a
  have hb5 : b ^ 5 = 1 := chars_pow_five hB5 b
  have hc5 : c ^ 5 = 1 := chars_pow_five hB5 c
  have hai : a⁻¹ = a ^ 4 := inv_eq_pow_four ha5
  have hbi : b⁻¹ = b ^ 4 := inv_eq_pow_four hb5
  have hci : c⁻¹ = c ^ 4 := inv_eq_pow_four hc5
  have kb : ∀ l, b ≠ a ^ l := fun l => twist_ne_pow hB5 θ hθ m hm ha l
  have kca : ∀ l, c ≠ a ^ l := fun l => twist_twist_ne_pow hB5 θ hθ m hm ha l
  have kcb : ∀ l, c ≠ b ^ l := fun l => twist_ne_pow hB5 θ hθ m hm hb1 l
  have hab : a ≠ b := fun h => kb 1 (by rw [pow_one]; exact h.symm)
  have hac : a ≠ c := fun h => kca 1 (by rw [pow_one]; exact h.symm)
  have hbc : b ≠ c := fun h => kcb 1 (by rw [pow_one]; exact h.symm)
  have haa : a ≠ a⁻¹ := fun h => pow_ne_self hB5 ha (n := 4) (by norm_num)
    (by rw [← hai]; exact h.symm)
  have hbb : b ≠ b⁻¹ := fun h => pow_ne_self hB5 hb1 (n := 4) (by norm_num)
    (by rw [← hbi]; exact h.symm)
  have hcc : c ≠ c⁻¹ := fun h => pow_ne_self hB5 hc1 (n := 4) (by norm_num)
    (by rw [← hci]; exact h.symm)
  have hab' : a ≠ b⁻¹ := fun h => kb 4 ((inv_eq_iff_eq_inv.1 h.symm).trans hai)
  have hba' : b ≠ a⁻¹ := fun h => kb 4 (h.trans hai)
  have hac' : a ≠ c⁻¹ := fun h => kca 4 ((inv_eq_iff_eq_inv.1 h.symm).trans hai)
  have hca' : c ≠ a⁻¹ := fun h => kca 4 (h.trans hai)
  have hbc' : b ≠ c⁻¹ := fun h => kcb 4 ((inv_eq_iff_eq_inv.1 h.symm).trans hbi)
  have hcb' : c ≠ b⁻¹ := fun h => kcb 4 (h.trans hbi)
  have hab'' : a⁻¹ ≠ b⁻¹ := fun h => hab (inv_injective h)
  have hac'' : a⁻¹ ≠ c⁻¹ := fun h => hac (inv_injective h)
  have hbc'' : b⁻¹ ≠ c⁻¹ := fun h => hbc (inv_injective h)
  exact card_six hab hac haa hab' hac' hbc hba' hbb hbc' hca' hcb' hcc hab'' hac'' hbc''

theorem six_orbit_facts (hB5 : ∀ b : B, b ^ 5 = 1) (θ : B ≃* B)
    (hθ : ∀ b, b * θ b * θ (θ b) = 1) (m : ℕ) (hm : ¬ 5 ∣ m) {a : B →* X} (ha : a ≠ 1) :
    twist θ m a ≠ 1 ∧ twist θ m (twist θ m a) ≠ 1 ∧ a ≠ twist θ m a ∧
      a ≠ twist θ m (twist θ m a) ∧ twist θ m a ≠ twist θ m (twist θ m a) ∧
      a ≠ (twist θ m a)⁻¹ ∧ a ≠ (twist θ m (twist θ m a))⁻¹ ∧
      twist θ m a ≠ (twist θ m (twist θ m a))⁻¹ := by
  set b : B →* X := twist θ m a with hb_def
  set c : B →* X := twist θ m b with hc_def
  have hb1 : b ≠ 1 := fun h => ha (twist_eq_one hB5 θ hθ m hm h)
  have hc1 : c ≠ 1 := fun h => hb1 (twist_eq_one hB5 θ hθ m hm h)
  have ha5 : a ^ 5 = 1 := chars_pow_five hB5 a
  have hb5 : b ^ 5 = 1 := chars_pow_five hB5 b
  have hai : a⁻¹ = a ^ 4 := inv_eq_pow_four ha5
  have hbi : b⁻¹ = b ^ 4 := inv_eq_pow_four hb5
  have kb : ∀ l, b ≠ a ^ l := fun l => twist_ne_pow hB5 θ hθ m hm ha l
  have kca : ∀ l, c ≠ a ^ l := fun l => twist_twist_ne_pow hB5 θ hθ m hm ha l
  have kcb : ∀ l, c ≠ b ^ l := fun l => twist_ne_pow hB5 θ hθ m hm hb1 l
  refine ⟨hb1, hc1, fun h => kb 1 (by rw [pow_one]; exact h.symm),
    fun h => kca 1 (by rw [pow_one]; exact h.symm),
    fun h => kcb 1 (by rw [pow_one]; exact h.symm),
    fun h => kb 4 ((inv_eq_iff_eq_inv.1 h.symm).trans hai),
    fun h => kca 4 ((inv_eq_iff_eq_inv.1 h.symm).trans hai),
    fun h => kcb 4 ((inv_eq_iff_eq_inv.1 h.symm).trans hbi)⟩

theorem omega_weight_lemma (hB5 : ∀ b : B, b ^ 5 = 1) (θ : B ≃* B)
    (hθ : ∀ b, b * θ b * θ (θ b) = 1) (f : ι → (B →* X)) (hcard : Fintype.card ι = 8) (m : ℕ)
    (hm : ¬ 5 ∣ m) (hf1 : ∃ i, f i ≠ 1) (H1 : ∀ χ, mult f χ ≤ mult f (twist θ m χ))
    (H2 : ∀ χ, mult f χ ≤ mult f χ⁻¹) :
    ∃ χ₀ : B →* X, χ₀ ≠ 1 ∧ χ₀ ∈ Set.range f ∧ twist θ m χ₀ ∈ Set.range f ∧
      twist θ m (twist θ m χ₀) ∈ Set.range f ∧
      (∀ ψ ∈ Set.range f, ψ ≠ 1 → ψ = χ₀ ∨ ψ = twist θ m χ₀ ∨
        ψ = twist θ m (twist θ m χ₀) ∨ ψ = χ₀⁻¹ ∨ ψ = (twist θ m χ₀)⁻¹ ∨
        ψ = (twist θ m (twist θ m χ₀))⁻¹) ∧
      (∀ i k, f i = f k → f i ≠ 1 → i = k) ∧
      (Finset.univ.filter fun i => f i = 1).card = 2 := by
  obtain ⟨i₀, hi₀⟩ := hf1
  set a : B →* X := f i₀ with ha_def
  set b : B →* X := twist θ m a with hb_def
  set c : B →* X := twist θ m b with hc_def
  have hrange : ∀ χ, χ ∈ Set.range f → twist θ m χ ∈ Set.range f := fun χ hχ =>
    (mult_pos_iff f _).1 (lt_of_lt_of_le ((mult_pos_iff f χ).2 hχ) (H1 χ))
  have hrangeinv : ∀ χ, χ ∈ Set.range f → χ⁻¹ ∈ Set.range f := fun χ hχ =>
    (mult_pos_iff f _).1 (lt_of_lt_of_le ((mult_pos_iff f χ).2 hχ) (H2 χ))
  have haR : a ∈ Set.range f := ⟨i₀, rfl⟩
  have hbR : b ∈ Set.range f := hrange a haR
  have hcR : c ∈ Set.range f := hrange b hbR
  have hb1 : b ≠ 1 := fun h => hi₀ (twist_eq_one hB5 θ hθ m hm h)
  have hc1 : c ≠ 1 := fun h => hb1 (twist_eq_one hB5 θ hθ m hm h)
  have hS6 := six_orbit_card hB5 θ hθ m hm hi₀
  set S : Finset (B →* X) := {a, b, c, a⁻¹, b⁻¹, c⁻¹} with hSdef
  have hSR : ∀ χ ∈ S, χ ∈ Set.range f := by
    intro χ hχ
    simp only [hSdef, Finset.mem_insert, Finset.mem_singleton] at hχ
    rcases hχ with rfl | rfl | rfl | rfl | rfl | rfl
    · exact haR
    · exact hbR
    · exact hcR
    · exact hrangeinv _ haR
    · exact hrangeinv _ hbR
    · exact hrangeinv _ hcR
  have hS1 : ∀ χ ∈ S, χ ≠ 1 := by
    intro χ hχ
    simp only [hSdef, Finset.mem_insert, Finset.mem_singleton] at hχ
    rcases hχ with rfl | rfl | rfl | rfl | rfl | rfl
    · exact hi₀
    · exact hb1
    · exact hc1
    · exact inv_ne_one.2 hi₀
    · exact inv_ne_one.2 hb1
    · exact inv_ne_one.2 hc1
  set lam : ℕ := m * m * m with hlam_def
  have hlam : ¬ 5 ∣ lam := by
    have h5 : Nat.Prime 5 := by norm_num
    intro h
    rcases h5.dvd_mul.1 h with h | h
    · rcases h5.dvd_mul.1 h with h | h <;> exact hm h
    · exact hm h
  have hM3 : ∀ χ : B →* X, twist θ m (twist θ m (twist θ m χ)) = χ ^ lam :=
    fun χ => twist_three θ hθ m χ
  have hNlam : ∀ ψ : B →* X, mult f ψ ≤ mult f (ψ ^ lam) := fun ψ => by
    have := (H1 ψ).trans ((H1 _).trans (H1 _))
    rwa [hM3] at this
  set σ : (B →* X) → (B →* X) := fun χ => (twist θ m χ) ^ lam with hσdef
  have hNσle : ∀ χ, mult f χ ≤ mult f (σ χ) := fun χ => (H1 χ).trans (hNlam _)
  have hσ3 : ∀ χ : B →* X, σ (σ (σ χ)) = χ := fun χ => by
    simp only [hσdef, twist_pow, hM3, ← pow_mul]
    have h4 : lam * (lam * lam) * lam = lam ^ 4 := by ring
    rw [h4]
    exact pow_fourth_eq_self (chars_pow_five hB5 χ) hlam
  have hNσ : ∀ χ, mult f (σ χ) = mult f χ := fun χ => by
    refine le_antisymm ?_ (hNσle χ)
    calc mult f (σ χ) ≤ mult f (σ (σ χ)) := hNσle _
      _ ≤ mult f (σ (σ (σ χ))) := hNσle _
      _ = mult f χ := by rw [hσ3]
  have hσfix : ∀ χ : B →* X, χ ≠ 1 → σ χ ≠ χ := fun χ hχ h => by
    apply twist_ne_pow hB5 θ hθ m hm hχ (lam ^ 3)
    have h1 : (σ χ) ^ (lam ^ 3) = χ ^ (lam ^ 3) := by rw [h]
    have h2 : (σ χ) ^ (lam ^ 3) = twist θ m χ := by
      simp only [hσdef]
      rw [← pow_mul, show lam * lam ^ 3 = lam ^ 4 by ring]
      exact pow_fourth_eq_self (chars_pow_five hB5 _) hlam
    rw [← h2, h1]
  set T : Finset (B →* X) := (Finset.univ.image f).erase 1 with hTdef
  have hTmem : ∀ χ, χ ∈ T ↔ χ ∈ Set.range f ∧ χ ≠ 1 := fun χ => by
    simp only [hTdef, Finset.mem_erase, Finset.mem_image, Finset.mem_univ, true_and,
      Set.mem_range]
    tauto
  have hσT : ∀ χ ∈ T, σ χ ∈ T := fun χ hχ => by
    obtain ⟨hr, h1⟩ := (hTmem χ).1 hχ
    refine (hTmem _).2 ⟨(mult_pos_iff f _).1 (lt_of_lt_of_le ((mult_pos_iff f χ).2 hr)
      (hNσle χ)), fun h => ?_⟩
    have hM1 : twist θ m χ ≠ 1 := fun h' => h1 (twist_eq_one hB5 θ hθ m hm h')
    apply hM1
    refine char_pow_inj hB5 hlam (χ := twist θ m χ) (χ' := 1) ?_
    rw [one_pow]
    exact h
  have h3dvd : 3 ∣ ∑ χ ∈ T, mult f χ :=
    three_dvd_sum σ T (fun χ _ => hσ3 χ) (fun χ hχ => hσfix χ ((hTmem χ).1 hχ).2) (mult f)
      (fun χ _ => hNσ χ) T (Finset.Subset.refl T) hσT
  have hsumT : ∑ χ ∈ T, mult f χ = (Finset.univ.filter fun j => ¬ f j = 1).card := by
    rw [← sum_mult_eq f T]
    congr 1
    ext j
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rw [hTmem]
    simp
  have hsplit : (Finset.univ.filter fun j => ¬ f j = 1).card +
      (Finset.univ.filter fun j => f j = 1).card = 8 := by
    have := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset ι))
      (fun j => f j = 1)
    rw [Finset.card_univ, hcard] at this
    omega
  have hST : S ⊆ T := fun χ hχ => (hTmem χ).2 ⟨hSR χ hχ, hS1 χ hχ⟩
  have hSsum : 6 ≤ ∑ χ ∈ S, mult f χ := by
    calc 6 = S.card := hS6.symm
      _ = ∑ _ ∈ S, 1 := by simp
      _ ≤ ∑ χ ∈ S, mult f χ :=
        Finset.sum_le_sum fun χ hχ => (mult_pos_iff f χ).2 (hSR χ hχ)
  have hSTle : ∑ χ ∈ S, mult f χ ≤ ∑ χ ∈ T, mult f χ :=
    Finset.sum_le_sum_of_subset hST
  have hT6 : ∑ χ ∈ T, mult f χ = 6 := by omega
  have hTS : T ⊆ S := by
    intro χ hχ
    by_contra hnot
    have hmem := (hTmem χ).1 hχ
    have hpos : 0 < mult f χ := (mult_pos_iff f χ).2 hmem.1
    have h1 : mult f χ ≤ ∑ y ∈ T \ S, mult f y :=
      Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_sdiff.2 ⟨hχ, hnot⟩)
    have h2 := Finset.sum_sdiff hST (f := mult f)
    omega
  have hSeq : ∑ χ ∈ S, mult f χ = 6 := by omega
  have hmult1 : ∀ χ ∈ S, mult f χ = 1 := by
    intro χ hχ
    by_contra hne
    have hpos := (mult_pos_iff f χ).2 (hSR χ hχ)
    have hlt : ∑ _ ∈ S, 1 < ∑ y ∈ S, mult f y :=
      Finset.sum_lt_sum (fun y hy => (mult_pos_iff f y).2 (hSR y hy)) ⟨χ, hχ, by omega⟩
    simp only [Finset.sum_const, smul_eq_mul, mul_one, hS6] at hlt
    omega
  refine ⟨a, hi₀, haR, hbR, hcR, ?_, ?_, ?_⟩
  · intro ψ hψ hψ1
    have hψS : ψ ∈ S := hTS ((hTmem ψ).2 ⟨hψ, hψ1⟩)
    simpa only [hSdef, Finset.mem_insert, Finset.mem_singleton] using hψS
  · intro i k hik hne
    by_contra hik'
    have h2 := two_le_mult_of_ne f hik' hik
    have hmem : f i ∈ S := hTS ((hTmem _).2 ⟨⟨i, rfl⟩, hne⟩)
    have := hmult1 _ hmem
    omega
  · omega

theorem omega_scalar_lemma (hB5 : ∀ b : B, b ^ 5 = 1) (θ : B ≃* B)
    (hθ : ∀ b, b * θ b * θ (θ b) = 1) (f : ι → (B →* X)) (m : ℕ) (hm : ¬ 5 ∣ m)
    {χ₀ : B →* X} (hχ₀ : χ₀ ≠ 1) (h0 : χ₀ ∈ Set.range f)
    (hall : ∀ ψ ∈ Set.range f, ψ ≠ 1 → ψ = χ₀ ∨ ψ = twist θ m χ₀ ∨
        ψ = twist θ m (twist θ m χ₀) ∨ ψ = χ₀⁻¹ ∨ ψ = (twist θ m χ₀)⁻¹ ∨
        ψ = (twist θ m (twist θ m χ₀))⁻¹)
    (m' : ℕ) (hm' : ¬ 5 ∣ m') (H' : ∀ χ, mult f χ ≤ mult f (χ ^ m')) :
    m' % 5 = 1 ∨ m' % 5 = 4 := by
  have hmem : χ₀ ^ m' ∈ Set.range f :=
    (mult_pos_iff f _).1 (lt_of_lt_of_le ((mult_pos_iff f χ₀).2 h0) (H' χ₀))
  have hne1 : χ₀ ^ m' ≠ 1 := fun h =>
    hχ₀ (char_pow_inj hB5 hm' (χ := χ₀) (χ' := 1) (by rw [one_pow]; exact h))
  have h5 : χ₀ ^ 5 = 1 := chars_pow_five hB5 χ₀
  have hinv : χ₀⁻¹ = χ₀ ^ 4 := inv_eq_pow_four h5
  rcases hall _ hmem hne1 with h | h | h | h | h | h
  · left
    by_contra hne
    exact pow_ne_self hB5 hχ₀ hne h
  · exact absurd h.symm (twist_ne_pow hB5 θ hθ m hm hχ₀ m')
  · exact absurd h.symm (twist_twist_ne_pow hB5 θ hθ m hm hχ₀ m')
  · right
    by_contra hne
    have h4 : (χ₀ ^ m') ^ 4 = χ₀ := by
      rw [h, hinv, ← pow_mul, pow_eq_pow_mod (4 * 4) h5]
      norm_num
    have h4' : χ₀ ^ (m' * 4) = χ₀ := by rw [pow_mul]; exact h4
    exact pow_ne_self hB5 hχ₀ (n := m' * 4) (by omega) h4'
  · exact absurd ((inv_eq_iff_eq_inv.1 h.symm).trans
      ((inv_eq_pow_four (chars_pow_five hB5 (χ₀ ^ m'))).trans (by rw [← pow_mul])))
      (twist_ne_pow hB5 θ hθ m hm hχ₀ (m' * 4))
  · exact absurd ((inv_eq_iff_eq_inv.1 h.symm).trans
      ((inv_eq_pow_four (chars_pow_five hB5 (χ₀ ^ m'))).trans (by rw [← pow_mul])))
      (twist_twist_ne_pow hB5 θ hθ m hm hχ₀ (m' * 4))

end Omega

end CFSG.RankThree.PartOne.AUTSL
