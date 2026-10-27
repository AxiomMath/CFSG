module

public import CFSG.Quasithin.Background.D2X1

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.LieType.BorelTits

variable {V : Type*} [CommGroup V] [Finite V]

theorem eq_of_swap (hV : ∀ v : V, v ^ 2 = 1) {X : Subgroup (MulAut V)} (c : CycCtx X)
    {t : MulAut V} (ht : t ∈ TInv X) {Y₁ Y₂ : Subgroup (MulAut V)} (hY₁ : Y₁ ∈ Xk X 1)
    (hY₂ : Y₂ ∈ Xk X 1) (hne12 : Y₁ ≠ Y₂) (h12 : conjBy t Y₁ = Y₂)
    (hcen : ∀ Q ∈ Xk X 1, Q ≠ Y₁ → Q ≠ Y₂ → ∀ y ∈ Q, t * y = y * t) :
    ∀ Q ∈ Xk X 1, Q = Y₁ ∨ Q = Y₂ := by
  have hk : (1 : ℕ) = 1 ∨ (1 : ℕ) = 2 := Or.inl rfl
  have hfact := fact_prime_two_mul_add_one hk
  have ht2 : t ^ 2 = 1 := ht.2.2.1
  have htt : t * t = 1 := by rw [← pow_two]; exact ht2
  have hti : t⁻¹ = t := inv_eq_of_mul_eq_one_right htt
  intro Q hQ
  by_contra hcon
  push Not at hcon
  obtain ⟨hQ1, hQ2⟩ := hcon
  have h3₁ : Nat.card Y₁ = 3 := by simpa using hY₁.2.1
  have h3₂ : Nat.card Y₂ = 3 := by simpa using hY₂.2.1
  have h3Q : Nat.card Q = 3 := by simpa using hQ.2.1
  obtain ⟨y₁, hy₁, hy₁1, hy₁z, hy₁ord⟩ := exists_generator_of_prime_card hY₁.2.1
  have hy₁3 : y₁ ^ 3 = 1 := by
    have := pow_orderOf_eq_one y₁
    rwa [hy₁ord] at this
  set z := t * y₁ * t⁻¹ with hz
  have hzY₂ : z ∈ Y₂ := by
    have : z ∈ conjBy t Y₁ := mem_conjBy_of_mem hy₁
    rwa [h12] at this
  have hcomm12 : ∀ a ∈ Y₁, ∀ b ∈ Y₂, a * b = b * a := Xk_commute hV hk Y₁ hY₁ Y₂ hY₂
  have hz3 : z ^ 3 = 1 := by
    have := pow_card_eq_one' (G := ↥Y₂) (x := ⟨z, hzY₂⟩)
    have h' := congrArg Subtype.val this
    simpa [h3₂] using h'
  have hz1 : z ≠ 1 := by
    intro h
    apply hy₁1
    have : t * y₁ * t⁻¹ = 1 := h
    have h2 : y₁ = t⁻¹ * (t * y₁ * t⁻¹) * t := by group
    rw [h2, this]; group
  have hbot : Y₁ ⊓ Y₂ = ⊥ := inf_eq_bot_of_card_prime h3₁ h3₂ hne12
  have hcz : y₁ * z = z * y₁ := hcomm12 y₁ hy₁ z hzY₂
  obtain ⟨u, hu⟩ : ∃ u : MulAut V, u = y₁ * z := ⟨_, rfl⟩
  have hu1 : u ≠ 1 := by
    intro h
    have h' : y₁ * z = 1 := hu ▸ h
    have h2 : y₁ = z⁻¹ := mul_eq_one_iff_eq_inv.mp h'
    have : y₁ ∈ Y₁ ⊓ Y₂ := ⟨hy₁, by rw [h2]; exact Y₂.inv_mem hzY₂⟩
    rw [hbot, Subgroup.mem_bot] at this
    exact hy₁1 this
  have hu3 : u ^ 3 = 1 := by
    rw [hu, (show Commute y₁ z from hcz).mul_pow, hy₁3, hz3, one_mul]
  have huord : orderOf u = 3 := orderOf_eq_prime hu3 hu1
  have htz : t * z * t⁻¹ = y₁ := by
    rw [hz, hti]
    calc t * (t * y₁ * t) * t = (t * t) * y₁ * (t * t) := by group
      _ = y₁ := by rw [htt]; group
  have htu : t * u * t⁻¹ = u := by
    calc t * u * t⁻¹ = (t * y₁ * t⁻¹) * (t * z * t⁻¹) := by rw [hu]; group
      _ = z * y₁ := by rw [htz]
      _ = u := by rw [hu, hcz]
  have htu' : t * u = u * t := mul_inv_eq_iff_eq_mul.mp htu
  have hcardD : Nat.card (Subgroup.zpowers u) = 3 := by rw [Nat.card_zpowers, huord]
  have huX : u ∈ X := by
    rw [hu]
    exact X.mul_mem ((hY₁.1.trans (fittingOf_le X)) hy₁) ((hY₂.1.trans (fittingOf_le X)) hzY₂)
  have hDX : Subgroup.zpowers u ≤ X := Subgroup.zpowers_le.mpr huX
  have hDQ : Subgroup.zpowers u ≠ Q := by
    intro hDQ
    have huQ : u ∈ Q := hDQ ▸ Subgroup.mem_zpowers u
    have hy₁mem : y₁ ∈ Q ⊔ Y₂ := by
      have : y₁ = u * z⁻¹ := by rw [hu]; group
      rw [this]
      exact Subgroup.mul_mem_sup huQ (Y₂.inv_mem hzY₂)
    have hdisj := disjoint_biSup hV hk (S := Xk X 1) subset_rfl (Xk_commute hV hk) hY₁
    have hle : Q ⊔ Y₂ ≤ ⨆ Z ∈ Xk X 1, ⨆ (_ : Z ≠ Y₁), Z :=
      sup_le (le_iSup₂_of_le Q hQ (le_iSup_of_le hQ1 le_rfl))
        (le_iSup₂_of_le Y₂ hY₂ (le_iSup_of_le (Ne.symm hne12) le_rfl))
    have : y₁ ∈ Y₁ ⊓ (⨆ Z ∈ Xk X 1, ⨆ (_ : Z ≠ Y₁), Z) := ⟨hy₁, hle hy₁mem⟩
    rw [hdisj.eq_bot, Subgroup.mem_bot] at this
    exact hy₁1 this
  have hcommQ : ∀ y ∈ Q, ∀ d ∈ Subgroup.zpowers u, y * d = d * y := by
    intro y hy d hd
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hd
    have h1 : y * y₁ = y₁ * y := Xk_commute hV hk Q hQ Y₁ hY₁ y hy y₁ hy₁
    have h2 : y * z = z * y := Xk_commute hV hk Q hQ Y₂ hY₂ y hy z hzY₂
    have : Commute y u := by
      show y * u = u * y
      rw [hu, ← mul_assoc, h1, mul_assoc, h2, ← mul_assoc]
    exact (this.zpow_right k).eq
  have htD : ∀ d ∈ Subgroup.zpowers u, t * d = d * t := by
    intro d hd
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hd
    exact (((show Commute t u from htu').zpow_right k)).eq
  have hge := pRank_three_ge_two (X := X) (t := t) (Q₁ := Q) (Q₂ := Subgroup.zpowers u) h3Q hcardD
    (fun h => hDQ h.symm) (hQ.1.trans (fittingOf_le X)) hDX hcommQ (hcen Q hQ hQ1 hQ2) htD
  have hA := c.zpowers_mem_qhatStar hV ht
  have hle := D2_21 c.hyp hA (c.faithful_zpowers hV ht) (Subgroup.mem_zpowers t) ht.2.1
  omega

omit [Finite V] in
theorem conjBy_eq_of_forall_mem [Finite V] {P : Subgroup (MulAut V)} {g : MulAut V}
    (hn : ∀ y ∈ P, g * y * g⁻¹ ∈ P) : conjBy g P = P := by
  have hle : conjBy g P ≤ P := by
    rintro _ ⟨y, hy, rfl⟩
    simpa [MulAut.conj_apply] using hn y hy
  exact Subgroup.eq_of_le_of_card_ge hle (by rw [card_conjBy])

theorem commute_of_normalizes_three_odd {A : Subgroup (MulAut V)} (hA : Nat.card A = 3)
    {y : MulAut V} (hy : Odd (orderOf y)) (hn : ∀ a ∈ A, y * a * y⁻¹ ∈ A)
    (hn' : ∀ a ∈ A, y⁻¹ * a * y ∈ A) : ∀ a ∈ A, y * a = a * y := by
  have : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  have hmem : y ∈ Subgroup.normalizer (A : Set (MulAut V)) := by
    rw [Subgroup.mem_normalizer_iff]
    intro h
    refine ⟨hn h, fun h' => ?_⟩
    have := hn' _ h'
    simpa [mul_assoc] using this
  have hcyc : IsCyclic A := isCyclic_of_prime_card hA
  set ψ := A.normalizerMonoidHom ⟨y, hmem⟩ with hψ
  have h1 : orderOf ψ ∣ orderOf y := by
    have := orderOf_map_dvd A.normalizerMonoidHom
      (⟨y, hmem⟩ : Subgroup.normalizer (A : Set (MulAut V)))
    rwa [Subgroup.orderOf_mk] at this
  have h2 : orderOf ψ ∣ 2 := by
    have := orderOf_dvd_natCard ψ
    rw [IsCyclic.card_mulAut, hA, Nat.totient_prime Fact.out] at this
    simpa using this
  have h3 : orderOf ψ = 1 := by
    have hodd : Odd (orderOf ψ) := Odd.of_dvd_nat hy h1
    rcases (Nat.dvd_prime Nat.prime_two).mp h2 with h | h
    · exact h
    · rw [h] at hodd; exact absurd hodd (by decide)
  have hψ1 : ψ = 1 := orderOf_eq_one_iff.mp h3
  intro a ha
  have := congrArg (fun φ : MulAut A => ((φ ⟨a, ha⟩ : A) : MulAut V)) hψ1
  simp only [hψ, MulAut.one_apply] at this
  have h4 : y * a * y⁻¹ = a := this
  rw [mul_inv_eq_iff_eq_mul] at h4
  exact h4

theorem tinv_normalizes (hV : ∀ v : V, v ^ 2 = 1) {X : Subgroup (MulAut V)} (c : CycCtx X)
    (hne : (Xk X 1).Nonempty)
    (hβ : ¬ ∃ t ∈ TInv X, ∃ Y₁ ∈ Xk X 1, ∃ Y₂ ∈ Xk X 1, Y₁ ≠ Y₂ ∧ conjBy t Y₁ = Y₂ ∧
      ∀ Q ∈ Xk X 1, Q ≠ Y₁ → Q ≠ Y₂ → ∀ y ∈ Q, t * y = y * t) :
    ∀ t ∈ TInv X, ∀ P ∈ Xk X 1, conjBy t P = P := by
  push Not at hβ
  intro t ht P hP
  obtain ⟨P₁, hP₁, P₂, hP₂, hne12, hmv, hcen⟩ := exists_moved_pair hV c hne ht
  rcases hmv with ⟨h12, h21⟩ | ⟨hi₁, hi₂⟩
  · exfalso
    obtain ⟨Q, hQ, hQ1, hQ2, y, hy, hne'⟩ := hβ t ht P₁ hP₁ P₂ hP₂ hne12 h12
    exact hne' (hcen Q hQ hQ1 hQ2 y hy)
  · by_cases h1 : P = P₁
    · subst h1
      exact conjBy_eq_of_forall_mem fun y hy => by rw [hi₁ y hy]; exact P.inv_mem hy
    · by_cases h2 : P = P₂
      · subst h2
        exact conjBy_eq_of_forall_mem fun y hy => by rw [hi₂ y hy]; exact P.inv_mem hy
      · refine conjBy_eq_of_forall_mem fun y hy => ?_
        have : t * y = y * t := hcen P hP h1 h2 y hy
        rw [mul_inv_eq_iff_eq_mul.mpr this]
        exact hy

theorem tinv_normalizes_X {X : Subgroup (MulAut V)} (c : CycCtx X)
    (hTnorm : ∀ t ∈ TInv X, ∀ P ∈ Xk X 1, conjBy t P = P) :
    ∀ g ∈ X, ∀ P ∈ Xk X 1, conjBy g P = P := by
  refine c.induction (P := fun g => ∀ P ∈ Xk X 1, conjBy g P = P) ?_ ?_ ?_ hTnorm
  · intro P _; exact conjBy_one P
  · intro a b ha hb P hP
    rw [← conjBy_conjBy, hb P hP, ha P hP]
  · intro a ha P hP
    have := ha P hP
    calc conjBy a⁻¹ P = conjBy a⁻¹ (conjBy a P) := by rw [this]
      _ = P := by rw [conjBy_conjBy, inv_mul_cancel, conjBy_one]

theorem no_card_four (hV : ∀ v : V, v ^ 2 = 1) {X : Subgroup (MulAut V)} (c : CycCtx X)
    (hne : (Xk X 1).Nonempty) :
    ¬ ∃ E : Subgroup (MulAut V), E ≤ X ∧ IsElemAbelian2 E ∧ Nat.card E = 4 := by
  rintro ⟨E, hEX, hE, hcard⟩
  have hk : (1 : ℕ) = 1 ∨ (1 : ℕ) = 2 := Or.inl rfl
  have hn3 := card_Xk_le_three hV c hne
  have hrkV : rk V = 2 * Nat.card (Xk X 1) := by
    have := rk_commV_Gk hV (X := X)
    rwa [commV_Gk_eq_top hV c hne, rk_top] at this
  have hE4 := c.rk_fixV_add_four_le hV hE hEX hcard
  have hE2 : IsPGroup 2 E := hE.isPGroup
  have hnpos : 0 < Nat.card (Xk X 1) := by
    obtain ⟨P, hP⟩ := hne
    exact Nat.card_pos_iff.mpr ⟨⟨⟨P, hP⟩⟩, inferInstance⟩
  by_cases hβ : ∃ t ∈ TInv X, ∃ Y₁ ∈ Xk X 1, ∃ Y₂ ∈ Xk X 1, Y₁ ≠ Y₂ ∧ conjBy t Y₁ = Y₂ ∧
      ∀ Q ∈ Xk X 1, Q ≠ Y₁ → Q ≠ Y₂ → ∀ y ∈ Q, t * y = y * t
  · obtain ⟨t, ht, Y₁, hY₁, Y₂, hY₂, hne12, h12, hcen⟩ := hβ
    have hsub : Xk X 1 ⊆ {Y₁, Y₂} := fun Q hQ => by
      rcases eq_of_swap hV c ht hY₁ hY₂ hne12 h12 hcen Q hQ with h | h <;> simp [h]
    have hle2 : Nat.card (Xk X 1) ≤ 2 := by
      calc Nat.card (Xk X 1) = (Xk X 1).ncard := Nat.card_coe_set_eq _
        _ ≤ ({Y₁, Y₂} : Set (Subgroup (MulAut V))).ncard :=
          Set.ncard_le_ncard hsub (Set.toFinite _)
        _ = 2 := Set.ncard_pair hne12
    have hpos := rk_fixV_pos_of_isPGroup_two hV hE2 (by omega : 0 < rk V)
    omega
  · have hTnorm := tinv_normalizes hV c hne hβ
    have hXnorm := tinv_normalizes_X c hTnorm
    have hEn : ∀ g ∈ E, ∀ P ∈ Xk X 1, ∀ y ∈ P, g * y * g⁻¹ ∈ P := by
      intro g hg P hP y hy
      have := mem_conjBy_of_mem (g := g) hy
      rwa [hXnorm g (hEX hg) P hP] at this
    have := card_Xk_le_rk_fixV hV hE2 hEn
    omega

theorem odd_orderOf_mul (hV : ∀ v : V, v ^ 2 = 1) {X : Subgroup (MulAut V)} (c : CycCtx X)
    (hne : (Xk X 1).Nonempty) {t t' : MulAut V} (ht : t ∈ TInv X) (ht' : t' ∈ TInv X) :
    Odd (orderOf (t * t')) := by
  by_cases hteq : t = t'
  · subst hteq
    have : t * t = 1 := by rw [← pow_two]; exact ht.2.2.1
    rw [this, orderOf_one]
    exact odd_one
  · by_contra hodd
    have heven : Even (orderOf (t * t')) := Nat.not_odd_iff_even.mp hodd
    obtain ⟨E, hEle, hE, hcard, -⟩ := exists_card_four_of_even ht.2.1 ht.2.2.1 ht'.2.1 ht'.2.2.1
      hteq heven
    refine no_card_four hV c hne ⟨E, hEle.trans ?_, hE, hcard⟩
    rw [Subgroup.closure_le]
    rintro x (rfl | rfl)
    · exact ht.1
    · exact ht'.1

theorem card_Xk_le_two_of_swap (hV : ∀ v : V, v ^ 2 = 1) {X : Subgroup (MulAut V)}
    (c : CycCtx X)
    (hβ : ∃ t ∈ TInv X, ∃ Y₁ ∈ Xk X 1, ∃ Y₂ ∈ Xk X 1, Y₁ ≠ Y₂ ∧ conjBy t Y₁ = Y₂ ∧
      ∀ Q ∈ Xk X 1, Q ≠ Y₁ → Q ≠ Y₂ → ∀ y ∈ Q, t * y = y * t) :
    Nat.card (Xk X 1) ≤ 2 := by
  obtain ⟨t, ht, Y₁, hY₁, Y₂, hY₂, hne12, h12, hcen⟩ := hβ
  have hsub : Xk X 1 ⊆ {Y₁, Y₂} := fun Q hQ => by
    rcases eq_of_swap hV c ht hY₁ hY₂ hne12 h12 hcen Q hQ with h | h <;> simp [h]
  calc Nat.card (Xk X 1) = (Xk X 1).ncard := Nat.card_coe_set_eq _
    _ ≤ ({Y₁, Y₂} : Set (Subgroup (MulAut V))).ncard := Set.ncard_le_ncard hsub (Set.toFinite _)
    _ = 2 := Set.ncard_pair hne12

theorem act_eq_of_normalizes (hV : ∀ v : V, v ^ 2 = 1) {X : Subgroup (MulAut V)} (c : CycCtx X)
    (hne : (Xk X 1).Nonempty) {t t' : MulAut V} (ht : t ∈ TInv X) (ht' : t' ∈ TInv X)
    {P : Subgroup (MulAut V)} (hP : P ∈ Xk X 1) (hn : conjBy t P = P) (hn' : conjBy t' P = P) :
    ∀ y ∈ P, t' * y * t'⁻¹ = t * y * t⁻¹ := by
  have ht2 : t ^ 2 = 1 := ht.2.2.1
  have htt : t * t = 1 := by rw [← pow_two]; exact ht2
  have hti : t⁻¹ = t := inv_eq_of_mul_eq_one_right htt
  have hodd := odd_orderOf_mul hV c hne ht ht'
  have hnu : conjBy (t * t') P = P := by rw [← conjBy_conjBy, hn', hn]
  have h3 : Nat.card P = 3 := by simpa using hP.2.1
  have hcomm := commute_of_normalizes_three_odd h3 hodd
    (fun a ha => by
      have := mem_conjBy_of_mem (g := t * t') ha
      rwa [hnu] at this)
    (fun a ha => by
      have h1 : a ∈ conjBy (t * t') P := by rw [hnu]; exact ha
      exact mem_conjBy_iff.mp h1)
  intro y hy
  have hu : (t * t') * y = y * (t * t') := hcomm y hy
  have ht'eq : t' = t * (t * t') := by rw [← mul_assoc, htt, one_mul]
  calc t' * y * t'⁻¹ = t * ((t * t') * y * (t * t')⁻¹) * t⁻¹ := by
        conv_lhs => rw [ht'eq]
        group
    _ = t * y * t⁻¹ := by rw [hu]; group

theorem card_Xk_ne_three (hV : ∀ v : V, v ^ 2 = 1) {X : Subgroup (MulAut V)} (c : CycCtx X)
    (hne : (Xk X 1).Nonempty) : Nat.card (Xk X 1) ≠ 3 := by
  classical
  intro h3
  have hk : (1 : ℕ) = 1 ∨ (1 : ℕ) = 2 := Or.inl rfl
  have hβ : ¬ ∃ t ∈ TInv X, ∃ Y₁ ∈ Xk X 1, ∃ Y₂ ∈ Xk X 1, Y₁ ≠ Y₂ ∧ conjBy t Y₁ = Y₂ ∧
      ∀ Q ∈ Xk X 1, Q ≠ Y₁ → Q ≠ Y₂ → ∀ y ∈ Q, t * y = y * t := by
    intro h
    have := card_Xk_le_two_of_swap hV c h
    omega
  have hTnorm := tinv_normalizes hV c hne hβ
  obtain ⟨A, hA⟩ := QhatStar_nonempty c.hyp.qhat c.hyp.le_two
  obtain ⟨t₀, ht₀, -⟩ := c.exists_tinv hA
  obtain ⟨P₁, hP₁, P₂, hP₂, hne12, hmv, hcen⟩ := exists_moved_pair hV c hne ht₀
  have hinv : (∀ y ∈ P₁, t₀ * y * t₀⁻¹ = y⁻¹) ∧ ∀ y ∈ P₂, t₀ * y * t₀⁻¹ = y⁻¹ := by
    rcases hmv with ⟨h12, h21⟩ | h
    · exfalso
      exact hβ ⟨t₀, ht₀, P₁, hP₁, P₂, hP₂, hne12, h12, hcen⟩
    · exact h
  have : Fintype (Xk X 1) := Fintype.ofFinite _
  obtain ⟨Q, hQ, hQ1, hQ2⟩ : ∃ Q ∈ Xk X 1, Q ≠ P₁ ∧ Q ≠ P₂ := by
    by_contra hcon
    push Not at hcon
    have hsub : Xk X 1 ⊆ {P₁, P₂} := fun Q hQ => by
      by_cases h1 : Q = P₁
      · simp [h1]
      · simp [hcon Q hQ h1]
    have : Nat.card (Xk X 1) ≤ 2 := by
      calc Nat.card (Xk X 1) = (Xk X 1).ncard := Nat.card_coe_set_eq _
        _ ≤ ({P₁, P₂} : Set (Subgroup (MulAut V))).ncard :=
          Set.ncard_le_ncard hsub (Set.toFinite _)
        _ = 2 := Set.ncard_pair hne12
    omega
  have hall : ∀ t ∈ TInv X, ∀ y ∈ Q, t * y = y * t := by
    intro t ht y hy
    have h1 := act_eq_of_normalizes hV c hne ht₀ ht hQ (hTnorm t₀ ht₀ Q hQ) (hTnorm t ht Q hQ) y hy
    have h2 : t₀ * y = y * t₀ := hcen Q hQ hQ1 hQ2 y hy
    have h3' : t₀ * y * t₀⁻¹ = y := mul_inv_eq_iff_eq_mul.mpr h2
    rw [h3'] at h1
    exact mul_inv_eq_iff_eq_mul.mp h1
  have hbot : commV Q = ⊥ := by
    refine c.fixV_T hV fun t ht w hw => ?_
    exact mem_fixV_zpowers_iff.mp (commV_le_fixV_of_commutes hV hk ht.2.2.1 hQ (hall t ht) hw)
  have h2 : rk (commV Q) = 2 * 1 := hQ.2.2
  rw [hbot, rk_bot] at h2
  omega

section Two

variable {X : Subgroup (MulAut V)} {P₁ P₂ : Subgroup (MulAut V)}

theorem conjBy_eq_of_odd (hP₁ : P₁ ∈ Xk X 1) (hP₂ : P₂ ∈ Xk X 1) (hne12 : P₁ ≠ P₂)
    (hall : ∀ Q ∈ Xk X 1, Q = P₁ ∨ Q = P₂) {g : MulAut V} (hg : g ∈ X)
    (hodd : Odd (orderOf g)) : conjBy g P₁ = P₁ ∧ conjBy g P₂ = P₂ := by
  have key : ∀ A B : Subgroup (MulAut V), A ∈ Xk X 1 → B ∈ Xk X 1 → A ≠ B →
      (∀ Q ∈ Xk X 1, Q = A ∨ Q = B) → conjBy g A = A := by
    intro A B hA hB hAB hAB'
    by_contra hcon
    have h1 : conjBy g A = B := (hAB' _ (conjBy_mem_Xk hg hA)).resolve_left hcon
    have h2 : conjBy g B = A := by
      rcases hAB' _ (conjBy_mem_Xk hg hB) with h | h
      · exact h
      · exfalso
        apply hAB
        apply conjBy_injective g
        rw [h1, h]
    have hgg : conjBy (g * g) A = A := by rw [← conjBy_conjBy, h1, h2]
    obtain ⟨k, hk⟩ := hodd
    have hgg' : g = (g * g) ^ (k + 1) := by
      have e : orderOf g + 1 = 2 * (k + 1) := by omega
      calc g = g ^ (orderOf g + 1) := by rw [pow_succ, pow_orderOf_eq_one, one_mul]
        _ = g ^ (2 * (k + 1)) := by rw [e]
        _ = (g * g) ^ (k + 1) := by rw [pow_mul, sq]
    apply hcon
    conv_lhs => rw [hgg']
    exact conjBy_pow_eq hgg (k + 1)
  exact ⟨key P₁ P₂ hP₁ hP₂ hne12 hall,
    key P₂ P₁ hP₂ hP₁ hne12.symm (fun Q hQ => (hall Q hQ).symm)⟩

theorem sup_commV_eq_top (hV : ∀ v : V, v ^ 2 = 1) (c : CycCtx X) (hne : (Xk X 1).Nonempty)
    (hall : ∀ Q ∈ Xk X 1, Q = P₁ ∨ Q = P₂) (hP₁ : P₁ ∈ Xk X 1) (hP₂ : P₂ ∈ Xk X 1) :
    commV P₁ ⊔ commV P₂ = ⊤ := by
  have hk : (1 : ℕ) = 1 ∨ (1 : ℕ) = 2 := Or.inl rfl
  have h1 := commV_Gk_eq_top hV c hne
  rw [(D2_12_2 (X := X) hV hk).1] at h1
  refine top_le_iff.mp ?_
  rw [← h1]
  refine iSup₂_le fun Q hQ => ?_
  rcases hall Q hQ with rfl | rfl
  · exact le_sup_left
  · exact le_sup_right

theorem mem_sup_of_odd (hV : ∀ v : V, v ^ 2 = 1) (c : CycCtx X) (hne : (Xk X 1).Nonempty)
    (hP₁ : P₁ ∈ Xk X 1) (hP₂ : P₂ ∈ Xk X 1) (hne12 : P₁ ≠ P₂)
    (hall : ∀ Q ∈ Xk X 1, Q = P₁ ∨ Q = P₂) {g : MulAut V} (hg : g ∈ X)
    (hodd : Odd (orderOf g)) : g ∈ P₁ ⊔ P₂ := by
  have hk : (1 : ℕ) = 1 ∨ (1 : ℕ) = 2 := Or.inl rfl
  obtain ⟨hn₁, hn₂⟩ := conjBy_eq_of_odd hP₁ hP₂ hne12 hall hg hodd
  have hcomm : ∀ (A : Subgroup (MulAut V)), A ∈ Xk X 1 → conjBy g A = A → ∀ a ∈ A, g * a = a * g := by
    intro A hA hnA
    refine commute_of_normalizes_three_odd (by simpa using hA.2.1) hodd (fun a ha => ?_)
      (fun a ha => ?_)
    · have := mem_conjBy_of_mem (g := g) ha
      rwa [hnA] at this
    · have h1 : a ∈ conjBy g A := by rw [hnA]; exact ha
      exact mem_conjBy_iff.mp h1
  have hc₁ := hcomm P₁ hP₁ hn₁
  have hc₂ := hcomm P₂ hP₂ hn₂
  obtain ⟨p₁, hp₁P, hp₁⟩ := exists_pow_eq_on_commV hV hP₁ hc₁
    (fun v hv => commV_smul_mem (fun y hy => by
      have := mem_conjBy_of_mem (g := g) hy
      rwa [hn₁] at this) hv)
  obtain ⟨p₂, hp₂P, hp₂⟩ := exists_pow_eq_on_commV hV hP₂ hc₂
    (fun v hv => commV_smul_mem (fun y hy => by
      have := mem_conjBy_of_mem (g := g) hy
      rwa [hn₂] at this) hv)
  have hcomm12 : ∀ a ∈ P₁, ∀ b ∈ P₂, a * b = b * a := Xk_commute hV hk P₁ hP₁ P₂ hP₂
  have hfix₂₁ : ∀ v ∈ commV P₁, p₂ v = v :=
    Xk_centralizes hV hk hP₁ hP₂ hne12 hcomm12 p₂ hp₂P
  have hfix₁₂ : ∀ v ∈ commV P₂, p₁ v = v :=
    Xk_centralizes hV hk hP₂ hP₁ hne12.symm (fun a ha b hb => (hcomm12 b hb a ha).symm) p₁ hp₁P
  have hgeq : g = p₁ * p₂ := by
    ext v
    have hv : v ∈ commV P₁ ⊔ commV P₂ := by
      rw [sup_commV_eq_top hV c hne hall hP₁ hP₂]; exact Subgroup.mem_top v
    obtain ⟨v₁, hv₁, v₂, hv₂, rfl⟩ := Subgroup.mem_sup.mp hv
    have hp₂v₂ : p₂ v₂ ∈ commV P₂ := commV_smul_mem (fun y hy =>
      P₂.mul_mem (P₂.mul_mem hp₂P hy) (P₂.inv_mem hp₂P)) hv₂
    rw [map_mul, hp₁ v₁ hv₁, hp₂ v₂ hv₂]
    show p₁ v₁ * p₂ v₂ = p₁ (p₂ (v₁ * v₂))
    rw [map_mul, hfix₂₁ v₁ hv₁, map_mul, hfix₁₂ _ hp₂v₂]
  rw [hgeq]
  exact Subgroup.mul_mem_sup hp₁P hp₂P

omit [Finite V] in
theorem comm_of_card_three {Q : Subgroup (MulAut V)} (hQ : Nat.card Q = 3) :
    ∀ a ∈ Q, ∀ b ∈ Q, a * b = b * a := fun a ha b hb =>
  congrArg Subtype.val (mul_comm_of_card_prime (p := 3) hQ ⟨a, ha⟩ ⟨b, hb⟩)

theorem sup_structure (h₁ : Nat.card P₁ = 3) (h₂ : Nat.card P₂ = 3) (hne : P₁ ≠ P₂)
    (hcomm : ∀ a ∈ P₁, ∀ b ∈ P₂, a * b = b * a) :
    Nat.card (P₁ ⊔ P₂ : Subgroup (MulAut V)) = 9 ∧
      ∀ y ∈ P₁ ⊔ P₂, ∃ a ∈ P₁, ∃ b ∈ P₂, y = a * b := by
  have : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  have hbot := inf_eq_bot_of_card_prime h₁ h₂ hne
  let f : ↥P₁ × ↥P₂ →* MulAut V :=
    (P₁.subtype).noncommCoprod (P₂.subtype) (fun x y => hcomm x x.2 y y.2)
  have hf : Function.Injective f := by
    rw [injective_iff_map_eq_one]
    rintro ⟨x, y⟩ h
    have h1 : (x : MulAut V) * y = 1 := h
    have hx : (x : MulAut V) ∈ P₁ ⊓ P₂ := by
      refine ⟨x.2, ?_⟩
      have : (x : MulAut V) = (y : MulAut V)⁻¹ := mul_eq_one_iff_eq_inv.mp h1
      rw [this]
      exact P₂.inv_mem y.2
    rw [hbot, Subgroup.mem_bot] at hx
    have hy : (y : MulAut V) = 1 := by
      rw [hx, one_mul] at h1
      exact h1
    exact Prod.ext (Subtype.ext hx) (Subtype.ext hy)
  have hrange : f.range = P₁ ⊔ P₂ := by
    apply le_antisymm
    · rintro _ ⟨⟨a, b⟩, rfl⟩
      exact Subgroup.mul_mem_sup a.2 b.2
    · refine sup_le (fun a ha => ⟨(⟨a, ha⟩, 1), ?_⟩) (fun b hb => ⟨(1, ⟨b, hb⟩), ?_⟩)
      · show a * 1 = a
        exact mul_one a
      · show 1 * b = b
        exact one_mul b
  refine ⟨?_, ?_⟩
  · rw [← hrange]
    rw [← Nat.card_congr (MonoidHom.ofInjective hf).toEquiv, Nat.card_prod, h₁, h₂]
  · intro y hy
    rw [← hrange] at hy
    obtain ⟨⟨a, b⟩, rfl⟩ := hy
    exact ⟨a, a.2, b, b.2, rfl⟩

theorem sup_comm_elements (h₁ : Nat.card P₁ = 3) (h₂ : Nat.card P₂ = 3) (hne : P₁ ≠ P₂)
    (hcomm : ∀ a ∈ P₁, ∀ b ∈ P₂, a * b = b * a) :
    ∀ a ∈ P₁ ⊔ P₂, ∀ b ∈ P₁ ⊔ P₂, a * b = b * a := by
  obtain ⟨-, hprod⟩ := sup_structure h₁ h₂ hne hcomm
  intro a ha b hb
  obtain ⟨a₁, ha₁, a₂, ha₂, rfl⟩ := hprod a ha
  obtain ⟨b₁, hb₁, b₂, hb₂, rfl⟩ := hprod b hb
  have h11 : Commute a₁ b₁ := comm_of_card_three h₁ a₁ ha₁ b₁ hb₁
  have h12 : Commute a₁ b₂ := hcomm a₁ ha₁ b₂ hb₂
  have h21 : Commute a₂ b₁ := (hcomm b₁ hb₁ a₂ ha₂).symm
  have h22 : Commute a₂ b₂ := comm_of_card_three h₂ a₂ ha₂ b₂ hb₂
  exact (Commute.mul_left (Commute.mul_right h11 h12) (Commute.mul_right h21 h22)).eq

theorem no_swap_two (hV : ∀ v : V, v ^ 2 = 1) (c : CycCtx X) (hne : (Xk X 1).Nonempty)
    (hP₁ : P₁ ∈ Xk X 1) (hP₂ : P₂ ∈ Xk X 1) (hne12 : P₁ ≠ P₂)
    (hall : ∀ Q ∈ Xk X 1, Q = P₁ ∨ Q = P₂) {t₀ : MulAut V} (ht₀ : t₀ ∈ TInv X)
    (h12 : conjBy t₀ P₁ = P₂) : False := by
  have hk : (1 : ℕ) = 1 ∨ (1 : ℕ) = 2 := Or.inl rfl
  have h3₁ : Nat.card P₁ = 3 := by simpa using hP₁.2.1
  have h3₂ : Nat.card P₂ = 3 := by simpa using hP₂.2.1
  have ht2 : t₀ ^ 2 = 1 := ht₀.2.2.1
  have htt : t₀ * t₀ = 1 := by rw [← pow_two]; exact ht2
  have hti : t₀⁻¹ = t₀ := inv_eq_of_mul_eq_one_right htt
  have hcomm12 : ∀ a ∈ P₁, ∀ b ∈ P₂, a * b = b * a := Xk_commute hV hk P₁ hP₁ P₂ hP₂
  have hYc := sup_comm_elements h3₁ h3₂ hne12 hcomm12
  set Y := P₁ ⊔ P₂ with hY
  have hYF : Y ≤ fittingOf X := sup_le hP₁.1 hP₂.1
  have hYX : Y ≤ X := hYF.trans (fittingOf_le X)
  have hT : ∀ t ∈ TInv X, ∃ i ∈ Y, t₀ * i * t₀⁻¹ = i⁻¹ ∧ t = t₀ * i := by
    intro t ht
    have hodd := odd_orderOf_mul hV c hne ht₀ ht
    have hiY : t₀ * t ∈ Y := mem_sup_of_odd hV c hne hP₁ hP₂ hne12 hall (X.mul_mem ht₀.1 ht.1) hodd
    have htt' : t * t = 1 := by rw [← pow_two]; exact ht.2.2.1
    have hti' : t⁻¹ = t := inv_eq_of_mul_eq_one_right htt'
    refine ⟨t₀ * t, hiY, ?_, ?_⟩
    · calc t₀ * (t₀ * t) * t₀⁻¹ = (t₀ * t₀) * t * t₀⁻¹ := by group
        _ = t * t₀ := by rw [htt, one_mul, hti]
        _ = (t₀ * t)⁻¹ := by rw [mul_inv_rev, hti, hti']
    · rw [← mul_assoc, htt, one_mul]
  have hI_mul : ∀ a b : MulAut V, a ∈ Y → t₀ * a * t₀⁻¹ = a⁻¹ → b ∈ Y → t₀ * b * t₀⁻¹ = b⁻¹ →
      a * b ∈ Y ∧ t₀ * (a * b) * t₀⁻¹ = (a * b)⁻¹ := by
    intro a b ha hai hb hbi
    refine ⟨Y.mul_mem ha hb, ?_⟩
    calc t₀ * (a * b) * t₀⁻¹ = (t₀ * a * t₀⁻¹) * (t₀ * b * t₀⁻¹) := by group
      _ = a⁻¹ * b⁻¹ := by rw [hai, hbi]
      _ = (b * a)⁻¹ := by rw [mul_inv_rev]
      _ = (a * b)⁻¹ := by rw [hYc b hb a ha]
  have hI_inv : ∀ a : MulAut V, a ∈ Y → t₀ * a * t₀⁻¹ = a⁻¹ →
      a⁻¹ ∈ Y ∧ t₀ * a⁻¹ * t₀⁻¹ = (a⁻¹)⁻¹ := by
    intro a ha hai
    refine ⟨Y.inv_mem ha, ?_⟩
    calc t₀ * a⁻¹ * t₀⁻¹ = (t₀ * a * t₀⁻¹)⁻¹ := by group
      _ = (a⁻¹)⁻¹ := by rw [hai]
  have hI_swap : ∀ a : MulAut V, a ∈ Y → t₀ * a * t₀⁻¹ = a⁻¹ → a * t₀ = t₀ * a⁻¹ := by
    intro a ha hai
    obtain ⟨-, h⟩ := hI_inv a ha hai
    rw [inv_inv] at h
    have h' : t₀ * a⁻¹ = a * t₀ := mul_inv_eq_iff_eq_mul.mp h
    exact h'.symm
  have hPred : ∀ g ∈ X, (g ∈ Y ∧ t₀ * g * t₀⁻¹ = g⁻¹) ∨
      ∃ i ∈ Y, t₀ * i * t₀⁻¹ = i⁻¹ ∧ g = t₀ * i := by
    refine c.induction (P := fun g => (g ∈ Y ∧ t₀ * g * t₀⁻¹ = g⁻¹) ∨
      ∃ i ∈ Y, t₀ * i * t₀⁻¹ = i⁻¹ ∧ g = t₀ * i) ?_ ?_ ?_ ?_
    · exact Or.inl ⟨Y.one_mem, by simp⟩
    · rintro a b (⟨ha, hai⟩ | ⟨i, hi, hii, rfl⟩) (⟨hb, hbi⟩ | ⟨j, hj, hjj, rfl⟩)
      · exact Or.inl (hI_mul a b ha hai hb hbi)
      ·
        right
        obtain ⟨hm, hmi⟩ := hI_mul a⁻¹ j (hI_inv a ha hai).1 (hI_inv a ha hai).2 hj hjj
        refine ⟨a⁻¹ * j, hm, hmi, ?_⟩
        calc a * (t₀ * j) = (a * t₀) * j := by rw [mul_assoc]
          _ = (t₀ * a⁻¹) * j := by rw [hI_swap a ha hai]
          _ = t₀ * (a⁻¹ * j) := by rw [mul_assoc]
      · right
        obtain ⟨hm, hmi⟩ := hI_mul i b hi hii hb hbi
        exact ⟨i * b, hm, hmi, by rw [mul_assoc]⟩
      · left
        have hi' := hI_inv i hi hii
        obtain ⟨hm, hmi⟩ := hI_mul i⁻¹ j hi'.1 hi'.2 hj hjj
        have heq : t₀ * i * (t₀ * j) = i⁻¹ * j := by
          calc t₀ * i * (t₀ * j) = (t₀ * i * t₀⁻¹) * j := by rw [hti]; group
            _ = i⁻¹ * j := by rw [hii]
        rw [heq]
        exact ⟨hm, hmi⟩
    · rintro a (⟨ha, hai⟩ | ⟨i, hi, hii, rfl⟩)
      · exact Or.inl (hI_inv a ha hai)
      · right
        refine ⟨i, hi, hii, ?_⟩
        have hi' := hI_inv i hi hii
        have h1 : i⁻¹ * t₀ = t₀ * i := by
          have := hI_swap i⁻¹ hi'.1 hi'.2
          rwa [inv_inv] at this
        calc (t₀ * i)⁻¹ = i⁻¹ * t₀⁻¹ := by rw [mul_inv_rev]
          _ = i⁻¹ * t₀ := by rw [hti]
          _ = t₀ * i := h1
    · intro t ht
      right
      exact hT t ht
  have hYinv : ∀ y ∈ Y, t₀ * y * t₀⁻¹ = y⁻¹ := by
    intro y hy
    rcases hPred y (hYX hy) with ⟨-, h⟩ | ⟨i, hi, hii, hyi⟩
    · exact h
    · exfalso
      have ht₀Y : t₀ ∈ Y := by
        have : t₀ = y * i⁻¹ := by rw [hyi]; group
        rw [this]
        exact Y.mul_mem hy (Y.inv_mem hi)
      have ht₀R : t₀ ∈ pCoreOf 3 X := by rw [← c.fittingOf_eq hV]; exact hYF ht₀Y
      obtain ⟨a, ha⟩ := exists_orderOf_eq_pow (pCoreOf_isPGroup 3 X) ht₀R
      have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
      rw [orderOf_eq_prime ht2 ht₀.2.1] at ha
      rcases a with _ | a
      · simp at ha
      · have := Nat.one_le_pow a 3 (by norm_num)
        rw [pow_succ] at ha
        omega
  have hnorm : conjBy t₀ P₁ = P₁ := by
    refine conjBy_eq_of_forall_mem fun y hy => ?_
    rw [hYinv y (Subgroup.mem_sup_left hy)]
    exact P₁.inv_mem hy
  exact hne12 (hnorm.symm.trans h12)

theorem tinv_inverts_both (hV : ∀ v : V, v ^ 2 = 1) (c : CycCtx X) (hne : (Xk X 1).Nonempty)
    (hP₁ : P₁ ∈ Xk X 1) (hP₂ : P₂ ∈ Xk X 1) (hne12 : P₁ ≠ P₂)
    (hall : ∀ Q ∈ Xk X 1, Q = P₁ ∨ Q = P₂) {t : MulAut V} (ht : t ∈ TInv X) :
    (∀ y ∈ P₁, t * y * t⁻¹ = y⁻¹) ∧ ∀ y ∈ P₂, t * y * t⁻¹ = y⁻¹ := by
  obtain ⟨Q₁, hQ₁, Q₂, hQ₂, hne', hmv, -⟩ := exists_moved_pair hV c hne ht
  have hcases : (Q₁ = P₁ ∧ Q₂ = P₂) ∨ (Q₁ = P₂ ∧ Q₂ = P₁) := by
    rcases hall Q₁ hQ₁ with h1 | h1 <;> rcases hall Q₂ hQ₂ with h2 | h2
    · exact absurd (h1.trans h2.symm) hne'
    · exact Or.inl ⟨h1, h2⟩
    · exact Or.inr ⟨h1, h2⟩
    · exact absurd (h1.trans h2.symm) hne'
  rcases hmv with ⟨h12, h21⟩ | ⟨hi₁, hi₂⟩
  · exfalso
    rcases hcases with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact no_swap_two hV c hne hP₁ hP₂ hne12 hall ht h12
    · exact no_swap_two hV c hne hP₂ hP₁ hne12.symm (fun Q hQ => (hall Q hQ).symm) ht h12
  · rcases hcases with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact ⟨hi₁, hi₂⟩
    · exact ⟨hi₂, hi₁⟩

end Two

theorem D2_25 (hV : ∀ v : V, v ^ 2 = 1) {X : Subgroup (MulAut V)} (c : CycCtx X)
    (hne : (Xk X 1).Nonempty) :
    IsElemAbelian 3 (fittingOf X) ∧ Nat.card (fittingOf X) = 9 ∧
      (∃ t ∈ X, orderOf t = 2 ∧ (∀ f ∈ fittingOf X, t * f * t⁻¹ = f⁻¹) ∧
        X = fittingOf X ⊔ Subgroup.zpowers t) ∧ rk V = 4 := by
  have hk : (1 : ℕ) = 1 ∨ (1 : ℕ) = 2 := Or.inl rfl
  have hn3 := card_Xk_le_three hV c hne
  have hn3' := card_Xk_ne_three hV c hne
  obtain ⟨A, hA⟩ := QhatStar_nonempty c.hyp.qhat c.hyp.le_two
  obtain ⟨t₀, ht₀, -⟩ := c.exists_tinv hA
  obtain ⟨P₁, hP₁, P₂, hP₂, hne12, -, -⟩ := exists_moved_pair hV c hne ht₀
  have hsub : ({P₁, P₂} : Set (Subgroup (MulAut V))) ⊆ Xk X 1 := by
    intro Q hQ
    rcases hQ with rfl | rfl
    · exact hP₁
    · exact hP₂
  have hn2 : (Xk X 1).ncard = 2 := by
    have h1 : ({P₁, P₂} : Set (Subgroup (MulAut V))).ncard ≤ (Xk X 1).ncard :=
      Set.ncard_le_ncard hsub (Set.toFinite _)
    rw [Set.ncard_pair hne12] at h1
    have h2 : (Xk X 1).ncard = Nat.card (Xk X 1) := (Nat.card_coe_set_eq _).symm
    omega
  have hset : ({P₁, P₂} : Set (Subgroup (MulAut V))) = Xk X 1 :=
    Set.eq_of_subset_of_ncard_le hsub (by rw [hn2, Set.ncard_pair hne12]) (Set.toFinite _)
  have hall : ∀ Q ∈ Xk X 1, Q = P₁ ∨ Q = P₂ := by
    intro Q hQ
    rw [← hset] at hQ
    exact hQ
  have hcardX : Nat.card (Xk X 1) = 2 := by rw [Nat.card_coe_set_eq]; exact hn2
  have hrkV : rk V = 4 := by
    have := rk_commV_Gk hV (X := X)
    rwa [commV_Gk_eq_top hV c hne, rk_top, hcardX] at this
  have h3₁ : Nat.card P₁ = 3 := by simpa using hP₁.2.1
  have h3₂ : Nat.card P₂ = 3 := by simpa using hP₂.2.1
  have hcomm12 : ∀ a ∈ P₁, ∀ b ∈ P₂, a * b = b * a := Xk_commute hV hk P₁ hP₁ P₂ hP₂
  obtain ⟨hcard9, hprod⟩ := sup_structure h3₁ h3₂ hne12 hcomm12
  have hYc := sup_comm_elements h3₁ h3₂ hne12 hcomm12
  have hYF : P₁ ⊔ P₂ ≤ fittingOf X := sup_le hP₁.1 hP₂.1
  have hYX : P₁ ⊔ P₂ ≤ X := hYF.trans (fittingOf_le X)
  have hFY : fittingOf X = P₁ ⊔ P₂ := by
    apply le_antisymm _ hYF
    intro g hg
    rw [c.fittingOf_eq hV] at hg
    obtain ⟨a, ha⟩ := exists_orderOf_eq_pow (pCoreOf_isPGroup 3 X) hg
    have hodd : Odd (orderOf g) := by
      rw [ha]; exact Odd.pow (by decide)
    exact mem_sup_of_odd hV c hne hP₁ hP₂ hne12 hall (pCoreOf_le 3 X hg) hodd
  have hexp : ∀ x ∈ fittingOf X, x ^ 3 = 1 := by
    intro x hx
    rw [hFY] at hx
    obtain ⟨a, ha, b, hb, rfl⟩ := hprod x hx
    have ha3 : a ^ 3 = 1 := by
      have := pow_card_eq_one' (G := ↥P₁) (x := ⟨a, ha⟩)
      have h' := congrArg Subtype.val this
      simpa [h3₁] using h'
    have hb3 : b ^ 3 = 1 := by
      have := pow_card_eq_one' (G := ↥P₂) (x := ⟨b, hb⟩)
      have h' := congrArg Subtype.val this
      simpa [h3₂] using h'
    rw [(show Commute a b from hcomm12 a ha b hb).mul_pow, ha3, hb3, one_mul]
  refine ⟨⟨⟨⟨fun a b => Subtype.ext (by
      have := hYc a (hFY ▸ a.2) b (hFY ▸ b.2)
      exact this)⟩⟩, hexp⟩, ?_, ?_, hrkV⟩
  · rw [hFY]; exact hcard9
  · refine ⟨t₀, ht₀.1, orderOf_eq_prime ht₀.2.2.1 ht₀.2.1, ?_, ?_⟩
    · intro f hf
      rw [hFY] at hf
      obtain ⟨a, ha, b, hb, rfl⟩ := hprod f hf
      obtain ⟨hi₁, hi₂⟩ := tinv_inverts_both hV c hne hP₁ hP₂ hne12 hall ht₀
      calc t₀ * (a * b) * t₀⁻¹ = (t₀ * a * t₀⁻¹) * (t₀ * b * t₀⁻¹) := by group
        _ = a⁻¹ * b⁻¹ := by rw [hi₁ a ha, hi₂ b hb]
        _ = (b * a)⁻¹ := by rw [mul_inv_rev]
        _ = (a * b)⁻¹ := by rw [hcomm12 a ha b hb]
    · apply le_antisymm
      · have hcl : Subgroup.closure (TInv X) ≤ fittingOf X ⊔ Subgroup.zpowers t₀ := by
          rw [Subgroup.closure_le]
          intro t ht
          have hodd := odd_orderOf_mul hV c hne ht₀ ht
          have hiY : t₀ * t ∈ P₁ ⊔ P₂ :=
            mem_sup_of_odd hV c hne hP₁ hP₂ hne12 hall (X.mul_mem ht₀.1 ht.1) hodd
          have htt : t₀ * t₀ = 1 := by rw [← pow_two]; exact ht₀.2.2.1
          have : t = t₀ * (t₀ * t) := by rw [← mul_assoc, htt, one_mul]
          show t ∈ fittingOf X ⊔ Subgroup.zpowers t₀
          rw [this, hFY]
          exact Subgroup.mul_mem _ (Subgroup.mem_sup_right (Subgroup.mem_zpowers t₀))
            (Subgroup.mem_sup_left hiY)
        calc X = Subgroup.closure (TInv X) := c.closure_eq.symm
          _ ≤ _ := hcl
      · exact sup_le (fittingOf_le X) (Subgroup.zpowers_le.mpr ht₀.1)

end CFSG.Quasithin
