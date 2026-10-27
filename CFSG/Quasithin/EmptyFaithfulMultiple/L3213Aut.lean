module

public import CFSG.Quasithin.EmptyFaithfulMultiple.L3213Basic
public import CFSG.Quasithin.EmptyFaithfulMultiple.Lemma1543

public section

namespace CFSG.Quasithin.EmptyFaithfulMultiple.L3213

open CFSG.Open CFSG.Quasithin CFSG.LieType.BorelTits
open scoped commutatorElement

variable {V : Type*} [CommGroup V] [Finite V]

theorem d2_13_data (hV : ∀ v : V, v ^ 2 = 1) {Xb Xs : Subgroup (MulAut V)} {p : ℕ}
    [Fact p.Prime] (hp2 : p ≠ 2) (hq : qhatOf Xb ≤ 2) (hO2 : pCoreOf 2 Xb = ⊥)
    (hXsXb : Xs ≤ Xb) (hXbN : Xb ≤ Subgroup.normalizer (Xs : Set (MulAut V)))
    (hXsp : IsPGroup p Xs) (hXb2 : ∀ b ∈ Xb, ∃ k : ℕ, b ^ 2 ^ k ∈ Xs) :
    (p = 3 ∨ p = 5) ∧ (p = 5 → ∃ A : Subgroup (MulAut V), A ∈ QhatStar Xb ∧
      Nat.card (⁅pCoreOf p Xb, A⁆ : Subgroup (MulAut V)) = 5 ∧
      rk (commV ⁅pCoreOf p Xb, A⁆) = 4) := by
  classical
  obtain ⟨r, hr⟩ : ∃ r : ℚ, qhatOf Xb = r := by
    obtain ⟨r, hr⟩ := WithTop.ne_top_iff_exists.mp (ne_top_of_le_ne_top (by simp) hq)
    exact ⟨r, hr.symm⟩
  have hr2 : r ≤ 2 := by
    rw [hr] at hq
    exact WithTop.coe_le_coe.mp (by simpa using hq)
  obtain ⟨⟨A, hA, hAk, hAr⟩, -⟩ := kq_eq_coe_iff.mp hr
  have hAS : A ∈ kRle Xb 3 r := ⟨⟨hA, hAr.le⟩, hAk⟩
  obtain ⟨A₀, -, hA₀⟩ := (Set.toFinite (kRle Xb 3 r)).exists_le_minimal hAS
  have hA₀Q : A₀ ∈ QhatStar Xb :=
    ⟨r, hr, hr2, hA₀.1, fun B hB hBA => le_antisymm hBA (hA₀.2 hB hBA)⟩
  have hXsP : Xs ≤ pCoreOf p Xb := le_pCoreOf_of_le_normalizer p hXsXb hXbN hXsp
  have hD : ⁅pCoreOf p Xb, A₀⁆ ≠ ⊥ := by
    intro hbot
    have hA₀C : A₀ ≤ Subgroup.centralizer (Xs : Set (MulAut V)) := by
      rw [Subgroup.commutator_eq_bot_iff_le_centralizer] at hbot
      exact Subgroup.le_centralizer_iff.mp (hXsP.trans hbot)
    exact hA₀.1.1.1.2.1 (eq_bot_of_le_centralizer_of_pow hO2 hXbN hXb2 hA₀.1.1.1.1
      hA₀.1.1.1.2.2.isPGroup hA₀C)
  obtain ⟨h35, h5, -⟩ := D2_13 hV hr hA₀Q hp2 rfl hD
  exact ⟨h35, fun hp5 => ⟨A₀, hA₀Q, (h5 hp5).2.2.1, (h5 hp5).2.2.2.2.2⟩⟩

theorem disjoint_of_mem_Xk (hV : ∀ v : V, v ^ 2 = 1) {Xb : Subgroup (MulAut V)}
    {Y₁ Y₂ Y₃ : Subgroup (MulAut V)} (h₁ : Y₁ ∈ Xk Xb 2) (h₂ : Y₂ ∈ Xk Xb 2)
    (h₃ : Y₃ ∈ Xk Xb 2) (h13 : Y₁ ≠ Y₃) (h23 : Y₂ ≠ Y₃) : Disjoint Y₃ (Y₁ ⊔ Y₂) := by
  have hind := (D2_12_1 (X := Xb) hV (Or.inr rfl)).2 ⟨Y₃, h₃⟩
  refine hind.mono_right (sup_le ?_ ?_)
  · exact le_iSup₂_of_le (f := fun (j : Xk Xb 2) (_ : j ≠ ⟨Y₃, h₃⟩) => (j : Subgroup (MulAut V)))
      ⟨Y₁, h₁⟩ (fun h => h13 (congrArg Subtype.val h)) le_rfl
  · exact le_iSup₂_of_le (f := fun (j : Xk Xb 2) (_ : j ≠ ⟨Y₃, h₃⟩) => (j : Subgroup (MulAut V)))
      ⟨Y₂, h₂⟩ (fun h => h23 (congrArg Subtype.val h)) le_rfl

theorem false_of_three_mem_Xk (hV : ∀ v : V, v ^ 2 = 1) {Xb Xs : Subgroup (MulAut V)}
    (hXs5 : IsPGroup 5 Xs) (hcard : Nat.card Xs ≤ 125)
    (hnab : Nat.card Xs = 125 → ∃ a ∈ Xs, ∃ b ∈ Xs, a * b ≠ b * a)
    {Y₁ Y₂ Y₃ : Subgroup (MulAut V)} (h₁ : Y₁ ∈ Xk Xb 2) (h₂ : Y₂ ∈ Xk Xb 2)
    (h₃ : Y₃ ∈ Xk Xb 2) (hY₁ : Y₁ ≤ Xs) (hY₂ : Y₂ ≤ Xs) (hY₃ : Y₃ ≤ Xs) (h12 : Y₁ ≠ Y₂)
    (h13 : Y₁ ≠ Y₃) (h23 : Y₂ ≠ Y₃) : False := by
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have hc := Xk_commute (X := Xb) hV (Or.inr rfl)
  have hd21 : Disjoint Y₂ (Y₁ ⊔ Y₁) := disjoint_of_mem_Xk hV h₁ h₁ h₂ h12 h12
  rw [sup_idem] at hd21
  have hd3 : Disjoint Y₃ (Y₁ ⊔ Y₂) := disjoint_of_mem_Xk hV h₁ h₂ h₃ h13 h23
  have hcard5 : ∀ {Y : Subgroup (MulAut V)}, Y ∈ Xk Xb 2 → Nat.card Y = 5 := fun h => h.2.1
  have hne : ∀ {Y : Subgroup (MulAut V)}, Y ∈ Xk Xb 2 → Y ≠ ⊥ := fun h hY => by
    have := hcard5 h
    rw [hY, Subgroup.card_bot] at this
    omega
  set W₂ := Y₁ ⊔ Y₂ with hW₂
  set W₃ := W₂ ⊔ Y₃ with hW₃
  have hW₃Xs : W₃ ≤ Xs := sup_le (sup_le hY₁ hY₂) hY₃
  have hlt₁ : Y₁ < W₂ := by
    refine lt_of_le_of_ne le_sup_left fun h => hne h₂ ?_
    have h2le : Y₂ ≤ Y₁ := h ▸ le_sup_right
    exact disjoint_self.mp (hd21.mono_right h2le)
  have hlt₂ : W₂ < W₃ := by
    refine lt_of_le_of_ne le_sup_left fun h => hne h₃ ?_
    have h3le : Y₃ ≤ W₂ := h ▸ le_sup_right
    exact disjoint_self.mp (hd3.mono_right h3le)
  have hc1 := mul_card_le_card_of_lt (hXs5.to_le (le_sup_left.trans hW₃Xs)) hlt₁
  have hc2 := mul_card_le_card_of_lt (hXs5.to_le hW₃Xs) hlt₂
  rw [hcard5 h₁] at hc1
  have hW₃le := Subgroup.card_le_of_le hW₃Xs
  have hXsW : W₃ = Xs := Subgroup.eq_of_le_of_card_ge hW₃Xs (by omega)
  have hXsc : Nat.card Xs = 125 := by omega
  have hcomm : ∀ {A B : Subgroup (MulAut V)}, A ∈ Xk Xb 2 → B ∈ Xk Xb 2 →
      A ≤ Subgroup.centralizer (B : Set (MulAut V)) := fun hA hB a ha =>
    Subgroup.mem_centralizer_iff.mpr fun b hb => hc _ hB _ hA b hb a ha
  have hYW : ∀ {A : Subgroup (MulAut V)}, A ∈ Xk Xb 2 →
      A ≤ Subgroup.centralizer (W₃ : Set (MulAut V)) := fun hA =>
    Subgroup.le_centralizer_iff.mpr (sup_le (sup_le (hcomm h₁ hA) (hcomm h₂ hA)) (hcomm h₃ hA))
  have hWW : W₃ ≤ Subgroup.centralizer (W₃ : Set (MulAut V)) :=
    sup_le (sup_le (hYW h₁) (hYW h₂)) (hYW h₃)
  obtain ⟨a, ha, b, hb, hab⟩ := hnab hXsc
  rw [← hXsW] at ha hb
  exact hab (Subgroup.mem_centralizer_iff.mp (hWW hb) a ha)

theorem commute_of_mem_Xk {Xb Xs : Subgroup (MulAut V)} (hXsF : Xs ≤ fittingOf Xb)
    (hno3 : ∀ Y₁ Y₂ Y₃ : Subgroup (MulAut V), Y₁ ∈ Xk Xb 2 → Y₂ ∈ Xk Xb 2 → Y₃ ∈ Xk Xb 2 →
      Y₁ ≤ Xs → Y₂ ≤ Xs → Y₃ ≤ Xs → Y₁ ≠ Y₂ → Y₁ ≠ Y₃ → Y₂ ≠ Y₃ → False)
    {g : MulAut V} (hgo : Odd (orderOf g)) (hgXs : ∀ y ∈ Xs, g * y * g⁻¹ ∈ Xs)
    {Y : Subgroup (MulAut V)} (hY : Y ∈ Xk Xb 2) (hYXs : Y ≤ Xs) :
    ∀ y ∈ Y, g * y = y * g := by
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have hconj : ∀ {Z : Subgroup (MulAut V)}, Z ∈ Xk Xb 2 → Z ≤ Xs →
      conjBy g Z ∈ Xk Xb 2 ∧ conjBy g Z ≤ Xs := by
    intro Z hZ hZXs
    have hle : conjBy g Z ≤ Xs := by
      intro x hx
      have h := hgXs _ (hZXs (mem_conjBy_iff.mp hx))
      simpa [mul_assoc] using h
    exact ⟨⟨hle.trans hXsF, by rw [card_conjBy]; exact hZ.2.1,
      by rw [rk_commV_conjBy]; exact hZ.2.2⟩, hle⟩
  have hfix : conjBy g Y = Y := by
    by_contra hne
    obtain ⟨h1, h1'⟩ := hconj hY hYXs
    obtain ⟨h2, h2'⟩ := hconj h1 h1'
    have hne2 : conjBy g (conjBy g Y) ≠ conjBy g Y := fun h => hne (conjBy_injective g h)
    have hne3 : conjBy g (conjBy g Y) ≠ Y := by
      intro h
      rw [conjBy_conjBy] at h
      apply hne
      obtain ⟨n, hn⟩ := hgo
      have e : g = (g * g) ^ (n + 1) := by
        rw [← pow_two, ← pow_mul, show 2 * (n + 1) = orderOf g + 1 by omega, pow_succ,
          pow_orderOf_eq_one, one_mul]
      rw [e]
      exact conjBy_pow_eq h (n + 1)
    exact hno3 Y _ _ hY h1 h2 hYXs h1' h2' (Ne.symm hne) (Ne.symm hne3) (Ne.symm hne2)
  have hcop : Nat.Coprime (orderOf g) (5 - 1) := by
    rw [show 5 - 1 = 2 ^ 2 by norm_num]
    exact Nat.Coprime.pow_right 2 (Nat.coprime_two_right.mpr hgo)
  exact commute_of_normalizes_of_coprime (hY.2.1.trans (by norm_num)) hcop
    (mem_normalizer_of_conjBy_eq hfix)

omit [Finite V] in
theorem eq_bot_of_le_commutator {Xb Xs A : Subgroup (MulAut V)} (hXs : pCoreOf 5 Xb = Xs)
    (hA : IsA2 Xb A) (hexp : ∀ y ∈ Xs, y ^ 5 = 1)
    (hcen : ∀ a ∈ Xs, ∀ b ∈ ⁅Xs, Xs⁆, a * b = b * a)
    (hle : ⁅pCoreOf 5 Xb, A⁆ ≤ ⁅Xs, Xs⁆) : ⁅pCoreOf 5 Xb, A⁆ = ⊥ := by
  rw [hXs] at hle ⊢
  have hbot : ∀ g : MulAut V,
      g ∈ Subgroup.normalizer ((⊥ : Subgroup (MulAut V)) : Set (MulAut V)) := fun g => by
    rw [Subgroup.mem_normalizer_iff]
    intro h
    simp
  have key : ∀ a ∈ A, ∀ d ∈ Xs, a * d * a⁻¹ * d⁻¹ ∈ (⊥ : Subgroup (MulAut V)) := by
    intro a ha
    refine commutator_mem_of_frattini_coprime (m := 2) (n := 5) (by norm_num)
      (hA.isElemAbelian2.2 a ha) bot_le (fun g _ => hbot g) (hbot a) (fun d hd => ?_)
      (fun d hd b hb => ?_) (fun d hd => ?_)
    · rw [Subgroup.mem_bot]
      exact hexp d hd
    · rw [sup_bot_eq] at hb
      rw [Subgroup.mem_bot, hcen d hd b hb]
      group
    · rw [sup_bot_eq]
      apply hle
      have h2 := Subgroup.commutator_mem_commutator ha hd
      rw [Subgroup.commutator_comm] at h2
      rwa [commutatorElement_def] at h2
  rw [eq_bot_iff, Subgroup.commutator_le]
  intro d hd a ha
  have h1 := key a ha d hd
  rw [Subgroup.mem_bot] at h1 ⊢
  have e : ⁅d, a⁆ = (a * d * a⁻¹ * d⁻¹)⁻¹ := by
    rw [commutatorElement_def]
    group
  rw [e, h1, inv_one]

end CFSG.Quasithin.EmptyFaithfulMultiple.L3213
