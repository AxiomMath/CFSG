module

public import CFSG.Quasithin.Background.ConjTransport
public import CFSG.Quasithin.Vol2.Ch9H11Fix

public section

noncomputable section

namespace CFSG.Quasithin.H13.H11P

open CFSG.Quasithin (fixV mem_fixV rk rkIdx IsElemAbelian2)
open CFSG.RankThree.PartOne.KCRootAxis (SL₂)
open scoped Matrix

variable {K : Type} [Field K] [CharP K 2] [Finite K]

omit [Finite K] in
theorem not_presF_and_swapF {x : MulAut (VM K)} (hP : PresF x) (hS : SwapF x) : False := by
  obtain ⟨g', hg'⟩ := hP.1 (uu 1)
  obtain ⟨g'', hg''⟩ := hS.1 (uu 1)
  have h := rho_injective (hg'.symm.trans hg'')
  have h1 : g' = 1 := congrArg Prod.fst h
  rw [h1, show ((1 : SL₂ K), (1 : SL₂ K)) = 1 from rfl, map_one, mul_inv_eq_one,
    mul_eq_left] at hg'
  have h2 := rho_injective (hg'.trans (map_one rho).symm)
  have h3 : uu (1 : K) = uu 0 := by rw [uu_zero]; exact congrArg Prod.fst h2
  exact one_ne_zero (uu_injective h3)

omit [CharP K 2] [Finite K] in
theorem conj_swap_form {x : MulAut (VM K)} {c : K} {P Q : SL₂ K}
    (h : ∀ X, addMap x X = c • ((P : Mat K) * Xᵀ * (Q : Mat K)ᵀ)) (g g' : SL₂ K) :
    x * rho (g, g') * x⁻¹ = rho (P * g' * P⁻¹, Q * g * Q⁻¹) := by
  rw [mul_inv_eq_iff_eq_mul]
  refine eq_of_addMap fun X => ?_
  rw [addMap_mul, addMap_mul, addMap_rho, h, h, addMap_rho, Matrix.mul_smul, Matrix.smul_mul]
  congr 1
  have hP : ((P⁻¹ : SL₂ K) : Mat K) * (P : Mat K) = 1 := coe_inv_mul P
  have hQ : (Q : Mat K)ᵀ * ((Q⁻¹ : SL₂ K) : Mat K)ᵀ = 1 := by
    rw [← Matrix.transpose_mul, coe_inv_mul, Matrix.transpose_one]
  simp only [Matrix.SpecialLinearGroup.coe_mul, Matrix.transpose_mul, Matrix.transpose_transpose,
    Matrix.mul_assoc]
  rw [← Matrix.mul_assoc ((P⁻¹ : SL₂ K) : Mat K) (P : Mat K), hP, Matrix.one_mul,
    ← Matrix.mul_assoc (Q : Mat K)ᵀ ((Q⁻¹ : SL₂ K) : Mat K)ᵀ, hQ, Matrix.one_mul]

omit [CharP K 2] [Finite K] in
theorem swapF_of_swap_form {x : MulAut (VM K)} {c : K} {P Q : SL₂ K}
    (h : ∀ X, addMap x X = c • ((P : Mat K) * Xᵀ * (Q : Mat K)ᵀ)) : SwapF x := by
  refine ⟨fun g => ⟨Q * g * Q⁻¹, ?_⟩, fun g' => ⟨P * g' * P⁻¹, ?_⟩⟩
  · rw [conj_swap_form h, mul_one, mul_inv_cancel]
  · rw [conj_swap_form h, mul_one, mul_inv_cancel]

omit [CharP K 2] [Finite K] in
theorem presF_mul_of_swapF {x y : MulAut (VM K)} (hx : SwapF x) (hy : SwapF y) :
    PresF (x * y) := by
  have hc : ∀ u : MulAut (VM K), x * y * u * (x * y)⁻¹ = x * (y * u * y⁻¹) * x⁻¹ := fun u => by
    group
  refine ⟨fun g => ?_, fun h => ?_⟩
  · obtain ⟨g', hg'⟩ := hy.1 g
    obtain ⟨g'', hg''⟩ := hx.2 g'
    exact ⟨g'', by rw [hc, hg', hg'']⟩
  · obtain ⟨h', hh'⟩ := hy.2 h
    obtain ⟨h'', hh''⟩ := hx.1 h'
    exact ⟨h'', by rw [hc, hh', hh'']⟩

theorem mem_Lm_of_presF (h4 : 4 ≤ Nat.card K) {x : MulAut (VM K)} (hx : x ∈ NLm K)
    (hK : x ∈ kLin K) (hxx : x * x = 1) (hP : PresF x) : x ∈ Lm K := by
  rcases mem_Lm_or_swap h4 hx hK hxx with h | ⟨c, -, P, Q, h⟩
  · exact h
  · exact (not_presF_and_swapF hP (swapF_of_swap_form h)).elim

theorem swapF_of_not_mem_Lm (h4 : 4 ≤ Nat.card K) {x : MulAut (VM K)} (hx : x ∈ NLm K)
    (hK : x ∈ kLin K) (hxx : x * x = 1) (hL : x ∉ Lm K) :
    SwapF x ∧ ∃ (c : K) (_ : c ≠ 0) (P Q : SL₂ K),
      ∀ X, addMap x X = c • ((P : Mat K) * Xᵀ * (Q : Mat K)ᵀ) := by
  rcases mem_Lm_or_swap h4 hx hK hxx with h | ⟨c, hc, P, Q, h⟩
  · exact (hL h).elim
  · exact ⟨swapF_of_swap_form h, c, hc, P, Q, h⟩

omit [CharP K 2] [Finite K] in
theorem memM_fixV_of_index_two {A H : Subgroup (MulAut (VM K))} (hHA : H ≤ A) {a : MulAut (VM K)}
    (haA : a ∈ A) (haa : a * a = 1) (hout : ∀ g ∈ A, g ∉ H → a * g ∈ H) (X : Mat K) :
    MemM (fixV A) X ↔ MemM (fixV H) X ∧ addMap a X = X := by
  simp only [memM_fixV]
  constructor
  · intro h
    exact ⟨fun g hg => h g (hHA hg), h a haA⟩
  · rintro ⟨hH, ha⟩ g hg
    by_cases hgH : g ∈ H
    · exact hH g hgH
    · have h1 := hH _ (hout g hg hgH)
      have hg' : g = a * (a * g) := by rw [← mul_assoc, haa, one_mul]
      rw [hg', addMap_mul, h1, ha]

instance : Finite (MulAut (VM K)) :=
  Finite.of_injective (fun x : MulAut (VM K) => (x : VM K → VM K)) DFunLike.coe_injective

theorem caseI {n : ℕ} (hn : 1 < n) (hK : Nat.card K = 2 ^ n) {A : Subgroup (MulAut (VM K))}
    (hAN : A ≤ NLm K) (hAK : A ≤ kLin K) (hA1 : A ≠ ⊥) (hA : IsElemAbelian2 A)
    (hB : A ⊓ Lm K ≤ UU K) :
    Nat.card A * Nat.card (fixV A) * Nat.card K ≤ 2 * Nat.card K ^ 4 ∧
    (Nat.card A * Nat.card (fixV A) * 4 ≤ Nat.card K ^ 4 ∨
      (n = 2 ∧ ∃ t ∈ A, Nat.card (fixV (Subgroup.zpowers t)) * Nat.card K = Nat.card K ^ 4)) ∧
    (A ≤ Lm K → Nat.card A * Nat.card (fixV A) * Nat.card K ≤ Nat.card K ^ 4) ∧
    Nat.card A ≤ 2 * Nat.card K ^ 2 := by
  have h4 : 4 ≤ Nat.card K := by
    rw [hK]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  have hq0 : 0 < Nat.card K := Nat.card_pos
  have hsq : ∀ a ∈ A, a * a = 1 := fun a ha => by rw [← sq]; exact hA.2 a ha
  by_cases hAB : A ≤ Lm K
  ·
    have hBA : A ⊓ Lm K = A := inf_eq_left.mpr hAB
    rw [hBA] at hB
    obtain ⟨hb1, hb2⟩ := card_fix_le_of_uu hB hA1
    refine ⟨by nlinarith, Or.inl ?_, fun _ => hb1, by nlinarith⟩
    calc Nat.card A * Nat.card (fixV A) * 4 ≤ Nat.card A * Nat.card (fixV A) * Nat.card K :=
          Nat.mul_le_mul_left _ h4
      _ ≤ Nat.card K ^ 4 := hb1
  · obtain ⟨a, haA, haL⟩ := Set.not_subset.mp hAB
    obtain ⟨-, c, hc, P, Q, hform⟩ :=
      swapF_of_not_mem_Lm h4 (hAN haA) (hAK haA) (hsq a haA) haL
    set B := A ⊓ Lm K with hBdef
    have haB : a ∉ B := fun h => haL h.2
    have hout : ∀ g ∈ A, g ∉ B → a * g ∈ B := by
      intro g hg hgB
      have hgL : g ∉ Lm K := fun h => hgB ⟨hg, h⟩
      obtain ⟨hga, -⟩ := swapF_of_not_mem_Lm h4 (hAN hg) (hAK hg) (hsq g hg) hgL
      obtain ⟨haa', -⟩ := swapF_of_not_mem_Lm h4 (hAN haA) (hAK haA) (hsq a haA) haL
      have hag : a * g ∈ A := A.mul_mem haA hg
      exact ⟨hag, mem_Lm_of_presF h4 (hAN hag) (hAK hag) (hsq _ hag)
        (presF_mul_of_swapF haa' hga)⟩
    have hcomm : ∀ g ∈ A, a * g = g * a := fun g hg => hA.1 a haA g hg
    have hcard : Nat.card A = 2 * Nat.card B :=
      card_eq_two_mul inf_le_left haA haB hcomm hout
    have hfixA := memM_fixV_of_index_two inf_le_left haA (hsq a haA) hout
    have ha1 : a ≠ 1 := fun h => haL (h ▸ (Lm K).one_mem)
    have hAL : ¬ A ≤ Lm K := hAB
    by_cases hB1 : B = ⊥
    ·
      have hcB : Nat.card B = 1 := by rw [hB1, Subgroup.card_bot]
      have hfa : Nat.card (fixV A) = Nat.card (fixV (Subgroup.zpowers a)) := by
        rw [card_eq_card_memM, card_eq_card_memM]
        refine Nat.card_congr (Equiv.subtypeEquivRight fun X => ?_)
        rw [hfixA, memM_fixV_zpowers, ← hBdef, hB1]
        simp only [memM_fixV, Subgroup.mem_bot, forall_eq, addMap_one, true_and]
      have haK : a ∈ kLin K := hAK haA
      have hzK : Subgroup.zpowers a ≤ kLin K := Subgroup.zpowers_le.mpr haK
      have hlt : fixV (Subgroup.zpowers a) < ⊤ := by
        refine lt_top_iff_ne_top.mpr fun htop => ha1 (eq_of_addMap fun X => ?_)
        have : MemM (fixV (Subgroup.zpowers a)) X := by rw [htop]; exact Subgroup.mem_top _
        rw [memM_fixV_zpowers] at this
        rw [this, addMap_one]
      have hup := card_mul_le_of_lt (kClosed_fixV hzK) (fun _ _ _ => Subgroup.mem_top _) hlt
      rw [Subgroup.card_top, card_VM] at hup
      rw [hcard, hcB, hfa]
      refine ⟨by nlinarith, ?_, fun h => (hAL h).elim, by nlinarith⟩
      by_cases hn2 : n = 2
      · by_cases htr : Nat.card (fixV (Subgroup.zpowers a)) * Nat.card K = Nat.card K ^ 4
        · exact Or.inr ⟨hn2, a, haA, htr⟩
        · left
          obtain ⟨j, -, hj⟩ := card_kClosed (kClosed_fixV hzK)
          have hq4 : Nat.card K = 4 := by rw [hK, hn2]; norm_num
          rw [hj, hq4] at hup htr ⊢
          have hj3 : j < 3 := by
            by_contra hj3
            push Not at hj3
            have : 4 ^ 3 ≤ 4 ^ j := Nat.pow_le_pow_right (by norm_num) hj3
            have h4j : 4 ^ j * 4 ≤ 4 ^ 4 := by linarith
            have : 4 ^ j ≤ 4 ^ 3 := by nlinarith
            have hj' : 4 ^ j = 4 ^ 3 := le_antisymm this (by assumption)
            exact htr (by rw [hj']; norm_num)
          interval_cases j <;> norm_num
      · left
        have hq8 : 8 ≤ Nat.card K := by
          rw [hK]
          calc 8 = 2 ^ 3 := by norm_num
            _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) (by omega)
        nlinarith
    ·
      have hBU : B ≤ UU K := hB
      obtain ⟨hb1, hb2⟩ := card_fix_le_of_uu hBU hB1
      have hle : Nat.card (fixV A) ≤ Nat.card (fixV B) := by
        rw [card_eq_card_memM, card_eq_card_memM]
        exact Nat.card_le_card_of_injective (fun X => ⟨X.1, ((hfixA X.1).mp X.2).1⟩)
          fun X Y h => Subtype.ext (Subtype.mk.inj h)
      have hle' : Nat.card B * Nat.card (fixV A) * Nat.card K ≤
          Nat.card B * Nat.card (fixV B) * Nat.card K := by gcongr
      rw [hcard]
      refine ⟨by linarith, ?_, fun h => (hAL h).elim, by linarith⟩
      by_cases hn2 : n = 2
      · have hq4 : Nat.card K = 4 := by rw [hK, hn2]; norm_num
        by_cases hfixB : ∀ X, MemM (fixV B) X → addMap a X = X
        · exact Or.inr ⟨hn2, a, haA, card_fix_swap hBU hB1 hc hform (hsq a haA) ha1
            (fun b hb => hcomm b hb.1) hfixB⟩
        · left
          push Not at hfixB
          obtain ⟨X, hXB, hXa⟩ := hfixB
          have hlt : fixV A < fixV B := by
            refine lt_of_le_of_ne (fun v hv => ?_) fun h => hXa ?_
            · have := (hfixA (Multiplicative.toAdd v)).mp hv
              exact this.1
            · have : MemM (fixV A) X := by rw [h]; exact hXB
              exact ((hfixA X).mp this).2
          have hgap := card_mul_le_of_lt (kClosed_fixV hAK)
            (kClosed_fixV (inf_le_left.trans hAK)) hlt
          rw [hq4] at hgap hb1 ⊢
          have h1 : Nat.card B * (4 * Nat.card (fixV A)) ≤ Nat.card B * Nat.card (fixV B) :=
            Nat.mul_le_mul_left _ hgap
          linarith
      · left
        have hq8 : 8 ≤ Nat.card K := by
          rw [hK]
          calc 8 = 2 ^ 3 := by norm_num
            _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) (by omega)
        have h1 : Nat.card B * Nat.card (fixV A) * 8 ≤ Nat.card B * Nat.card (fixV A) *
            Nat.card K := Nat.mul_le_mul_left _ hq8
        linarith

theorem caseII {n : ℕ} (hn : 1 < n) (hK : Nat.card K = 2 ^ n) {A : Subgroup (MulAut (VM K))}
    (hAN : A ≤ NLm K) (hA1 : A ≠ ⊥) (hA : IsElemAbelian2 A) (hB : A ⊓ Lm K ≤ UU K) :
    Nat.card A * Nat.card (fixV A) * Nat.card K ≤ 2 * Nat.card K ^ 4 ∧
    (Nat.card A * Nat.card (fixV A) * 4 ≤ Nat.card K ^ 4 ∨
      (n = 2 ∧ ∃ t ∈ A, Nat.card (fixV (Subgroup.zpowers t)) * Nat.card K = Nat.card K ^ 4)) ∧
    (A ≤ Lm K → Nat.card A * Nat.card (fixV A) * Nat.card K ≤ Nat.card K ^ 4) := by
  have h4 : 4 ≤ Nat.card K := by
    rw [hK]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  have hq0 : 0 < Nat.card K := Nat.card_pos
  have hsq : ∀ a ∈ A, a * a = 1 := fun a ha => by rw [← sq]; exact hA.2 a ha
  by_cases hAK : A ≤ kLin K
  · obtain ⟨h1, h2, h3, -⟩ := caseI hn hK hAN hAK hA1 hA hB
    exact ⟨h1, h2, h3⟩
  obtain ⟨f, hfA, hfK⟩ := Set.not_subset.mp hAK
  obtain ⟨σ, hσ⟩ := isSemi_of_normal h4 (hAN hfA)
  have hσ1 : σ ≠ 1 := fun h => hfK (by rw [h] at hσ; exact hσ)
  have hσσ : ∀ {g : MulAut (VM K)} {τ : K ≃+* K}, g ∈ A → IsSemi g τ → τ * τ = 1 := by
    intro g τ hg hτ
    have h1 := hτ.mul hτ
    rw [hsq g hg] at h1
    exact h1.unique (fun l X => rfl)
  set AK := A ⊓ kLin K with hAKdef
  have hfAK : f ∉ AK := fun h => hfK h.2
  have hout : ∀ g ∈ A, g ∉ AK → f * g ∈ AK := by
    intro g hg hgAK
    have hgK : g ∉ kLin K := fun h => hgAK ⟨hg, h⟩
    obtain ⟨τ, hτ⟩ := isSemi_of_normal h4 (hAN hg)
    have hτ1 : τ ≠ 1 := fun h => hgK (by rw [h] at hτ; exact hτ)
    have hστ : σ = τ := ringAut_invol_unique hK hσ1 hτ1 (hσσ hfA hσ) (hσσ hg hτ)
    subst hστ
    refine ⟨A.mul_mem hfA hg, ?_⟩
    have := hσ.mul hτ
    rwa [hσσ hfA hσ] at this
  have hcomm : ∀ g ∈ A, f * g = g * f := fun g hg => hA.1 f hfA g hg
  have hcard : Nat.card A = 2 * Nat.card AK := card_eq_two_mul inf_le_left hfA hfAK hcomm hout
  have hfixA := memM_fixV_of_index_two inf_le_left hfA (hsq f hfA) hout
  have hAKK : AK ≤ kLin K := inf_le_right
  have hdesc : Nat.card (fixV A) * Nat.card (fixV A) = Nat.card (fixV AK) := by
    have hfY : ∀ X, MemM (fixV AK) X → MemM (fixV AK) (addMap f X) := by
      intro X hX
      rw [memM_fixV] at hX ⊢
      intro g hg
      rw [← addMap_mul, ← hcomm g hg.1, addMap_mul, hX g hg]
    have h := card_fix_sq (kClosed_fixV hAKK) hσ hσ1 (hsq f hfA) hfY
    rw [card_eq_card_memM, card_eq_card_memM, ← h]
    have e : Nat.card {X : Mat K // MemM (fixV A) X} =
        Nat.card {X : Mat K // MemM (fixV AK) X ∧ addMap f X = X} :=
      Nat.card_congr (Equiv.subtypeEquivRight fun X => hfixA X)
    rw [e]
  have hAL : ¬ A ≤ Lm K := fun h => hfK (Lm_le_kLin (h hfA))
  by_cases hAK1 : AK = ⊥
  · have hcAK : Nat.card AK = 1 := by rw [hAK1, Subgroup.card_bot]
    have htop : fixV AK = ⊤ := by
      rw [hAK1, eq_top_iff]
      intro v _ x hx
      rw [Subgroup.mem_bot] at hx
      rw [hx]
      rfl
    have hfix0 : Nat.card (fixV AK) = Nat.card K ^ 4 := by
      rw [htop, Subgroup.card_top, card_VM]
    rw [hfix0] at hdesc
    have hcA : Nat.card (fixV A) = Nat.card K ^ 2 := by
      have h1 : Nat.card (fixV A) ^ 2 = (Nat.card K ^ 2) ^ 2 := by rw [sq, hdesc]; ring
      exact (Nat.pow_left_injective (by norm_num)) h1
    rw [hcard, hcAK, hcA]
    have h16 : 8 ≤ Nat.card K ^ 2 :=
      le_trans (by norm_num) (Nat.pow_le_pow_left h4 2)
    refine ⟨?_, Or.inl ?_, fun h => (hAL h).elim⟩
    · calc 2 * 1 * Nat.card K ^ 2 * Nat.card K = 2 * Nat.card K ^ 3 := by ring
        _ ≤ 2 * Nat.card K ^ 4 := Nat.mul_le_mul_left _ (Nat.pow_le_pow_right hq0 (by norm_num))
    · calc 2 * 1 * Nat.card K ^ 2 * 4 = Nat.card K ^ 2 * 8 := by ring
        _ ≤ Nat.card K ^ 2 * Nat.card K ^ 2 := Nat.mul_le_mul_left _ h16
        _ = Nat.card K ^ 4 := by ring
  · have hAKN : AK ≤ NLm K := inf_le_left.trans hAN
    have hAKe : IsElemAbelian2 AK :=
      ⟨fun a ha b hb => hA.1 a ha.1 b hb.1, fun a ha => hA.2 a ha.1⟩
    have hBK : AK ⊓ Lm K ≤ UU K := fun x hx => hB ⟨hx.1.1, hx.2⟩
    obtain ⟨k1, k2, -, k4⟩ := caseI hn hK hAKN hAKK hAK1 hAKe hBK
    rw [hcard]
    obtain ⟨j, -, hj⟩ := card_kClosed (kClosed_fixV hAKK)
    set m := Nat.card AK with hm
    set cA := Nat.card (fixV A) with hcAdef
    set q := Nat.card K with hqdef
    have hcA2 : 2 ≤ cA ∨ cA = 1 := by
      rcases j with _ | j
      · right
        rw [pow_zero] at hj
        rw [hj] at hdesc
        exact Nat.eq_one_of_mul_eq_one_right hdesc
      · left
        by_contra hlt
        push Not at hlt
        have h1 : cA ≤ 1 := by omega
        have h2 : cA * cA ≤ 1 := by nlinarith
        rw [hdesc, hj] at h2
        have : q ≤ q ^ (j + 1) := Nat.le_self_pow (by omega) _
        omega
    have hkA : m * cA * cA = m * Nat.card (fixV AK) := by rw [mul_assoc, hdesc]
    have hone : 2 * m * cA * q ≤ 2 * q ^ 4 := by
      rcases hcA2 with h2 | h1
      · calc 2 * m * cA * q = m * cA * q * 2 := by ring
          _ ≤ m * cA * q * cA := Nat.mul_le_mul_left _ h2
          _ = m * cA * cA * q := by ring
          _ = m * Nat.card (fixV AK) * q := by rw [hkA]
          _ ≤ 2 * q ^ 4 := k1
      · rw [h1]
        calc 2 * m * 1 * q = 2 * (m * q) := by ring
          _ ≤ 2 * (2 * q ^ 2 * q) := Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ k4)
          _ = 2 * q ^ 3 * 2 := by ring
          _ ≤ 2 * q ^ 3 * q := Nat.mul_le_mul_left _ (by omega)
          _ = 2 * q ^ 4 := by ring
    refine ⟨hone, ?_, fun h => (hAL h).elim⟩
    by_cases hn2 : n = 2
    · have hq4 : q = 4 := by rw [hK, hn2]; norm_num
      rcases k2 with k2 | ⟨hn2', t, htAK, ht⟩
      · left
        rcases hcA2 with h2 | h1
        · calc 2 * m * cA * 4 = m * cA * 4 * 2 := by ring
            _ ≤ m * cA * 4 * cA := Nat.mul_le_mul_left _ h2
            _ = m * cA * cA * 4 := by ring
            _ = m * Nat.card (fixV AK) * 4 := by rw [hkA]
            _ ≤ q ^ 4 := k2
        · rw [h1, hq4]
          rw [hq4] at k4
          omega
      · exact Or.inr ⟨hn2', t, htAK.1, ht⟩
    · left
      have hq8 : 8 ≤ q := by
        rw [hK]
        calc 8 = 2 ^ 3 := by norm_num
          _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) (by omega)
      have h1 : 2 * m * cA * 8 ≤ 2 * m * cA * q := Nat.mul_le_mul_left _ hq8
      omega

abbrev conjSub (g : MulAut (VM K)) (A : Subgroup (MulAut (VM K))) : Subgroup (MulAut (VM K)) :=
  A.map (MulAut.conj g).toMonoidHom

omit [CharP K 2] [Finite K] in
theorem card_conjSub (g : MulAut (VM K)) (A : Subgroup (MulAut (VM K))) :
    Nat.card (conjSub g A) = Nat.card A :=
  Subgroup.card_map_of_injective (MulAut.conj g).injective

omit [CharP K 2] [Finite K] in
theorem card_fixV_conjSub (g : MulAut (VM K)) (A : Subgroup (MulAut (VM K))) :
    Nat.card (fixV (conjSub g A)) = Nat.card (fixV A) :=
  CFSG.Quasithin.ConjTransport.card_fixV_map_conj A g

theorem exists_conj_std {n : ℕ} (hn : 1 ≤ n) (hK : Nat.card K = 2 ^ n)
    {A : Subgroup (MulAut (VM K))} (hA : IsElemAbelian2 A) :
    ∃ g ∈ Lm K, conjSub g A ⊓ Lm K ≤ UU K := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set B' : Subgroup (SL₂ K × SL₂ K) := (A ⊓ Lm K).comap rho with hB'
  have hB'2 : IsPGroup 2 B' := by
    rintro ⟨x, hx⟩
    refine ⟨1, Subtype.ext (rho_injective ?_)⟩
    have h := hA.2 _ hx.1
    simpa using h
  obtain ⟨g₁, hg₁⟩ := exists_conj_le_Uu hn hK (hB'2.map (MonoidHom.fst _ _))
  obtain ⟨g₂, hg₂⟩ := exists_conj_le_Uu hn hK (hB'2.map (MonoidHom.snd _ _))
  refine ⟨rho (g₁, g₂), ⟨_, rfl⟩, ?_⟩
  rintro _ ⟨⟨a, ha, rfl⟩, hxL⟩
  have haL : a ∈ Lm K := by
    have e : a = (rho (g₁, g₂))⁻¹ * (MulAut.conj (rho (g₁, g₂))).toMonoidHom a *
        rho (g₁, g₂) := by
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      group
    rw [e]
    exact (Lm K).mul_mem ((Lm K).mul_mem ((Lm K).inv_mem ⟨_, rfl⟩) hxL) ⟨_, rfl⟩
  obtain ⟨p, rfl⟩ := haL
  have hp : p ∈ B' := ⟨ha, ⟨p, rfl⟩⟩
  refine ⟨(g₁ * p.1 * g₁⁻¹, g₂ * p.2 * g₂⁻¹), ⟨hg₁ ⟨p.1, ⟨p, hp, rfl⟩, rfl⟩,
    hg₂ ⟨p.2, ⟨p, hp, rfl⟩, rfl⟩⟩, ?_⟩
  simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  rw [← map_inv, ← map_mul, ← map_mul]
  rfl

theorem h11_card {n : ℕ} (hn : 1 < n) (hK : Nat.card K = 2 ^ n) {A : Subgroup (MulAut (VM K))}
    (hAN : A ≤ NLm K) (hA1 : A ≠ ⊥) (hA : IsElemAbelian2 A) :
    Nat.card A * Nat.card (fixV A) * Nat.card K ≤ 2 * Nat.card K ^ 4 ∧
    (Nat.card A * Nat.card (fixV A) * 4 ≤ Nat.card K ^ 4 ∨
      (n = 2 ∧ ∃ t ∈ A, Nat.card (fixV (Subgroup.zpowers t)) * Nat.card K = Nat.card K ^ 4)) ∧
    (A ≤ Lm K → Nat.card A * Nat.card (fixV A) * Nat.card K ≤ Nat.card K ^ 4) := by
  obtain ⟨g, hgL, hstd⟩ := exists_conj_std (by omega) hK hA
  have hgN : g ∈ NLm K := Subgroup.le_normalizer hgL
  have hA'N : conjSub g A ≤ NLm K := by
    rintro _ ⟨a, ha, rfl⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    exact (NLm K).mul_mem ((NLm K).mul_mem hgN (hAN ha)) ((NLm K).inv_mem hgN)
  have hA'1 : conjSub g A ≠ ⊥ := fun h =>
    hA1 ((Subgroup.map_eq_bot_iff_of_injective _ (MulAut.conj g).injective).mp h)
  have hA'e : IsElemAbelian2 (conjSub g A) := by
    refine ⟨?_, ?_⟩
    · rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
      rw [← map_mul, ← map_mul, hA.1 a ha b hb]
    · rintro _ ⟨a, ha, rfl⟩
      rw [← map_pow, hA.2 a ha, map_one]
  obtain ⟨c1, c2, c3⟩ := caseII hn hK hA'N hA'1 hA'e hstd
  rw [card_conjSub, card_fixV_conjSub] at c1 c2 c3
  refine ⟨c1, ?_, fun hAL => c3 ?_⟩
  · rcases c2 with c2 | ⟨hn2, t, ht, htc⟩
    · exact Or.inl c2
    · obtain ⟨a, ha, rfl⟩ := ht
      refine Or.inr ⟨hn2, a, ha, ?_⟩
      rw [← card_fixV_conjSub g (Subgroup.zpowers a), conjSub, MonoidHom.map_zpowers]
      exact htc
  · rintro _ ⟨a, ha, rfl⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    exact (Lm K).mul_mem ((Lm K).mul_mem hgL (hAL ha)) ((Lm K).inv_mem hgL)

theorem h11_model {n : ℕ} (hn : 1 < n) (hK : Nat.card K = 2 ^ n) {A : Subgroup (MulAut (VM K))}
    (hAN : A ≤ NLm K) (hA1 : A ≠ ⊥) (hA : IsElemAbelian2 A) :
    rk A + n ≤ rkIdx (fixV A) + 1 ∧
      (rk A + 2 ≤ rkIdx (fixV A) ∨ (n = 2 ∧ ∃ t ∈ A, rkIdx (fixV (Subgroup.zpowers t)) = n)) ∧
      (A ≤ Lm K → rk A + n ≤ rkIdx (fixV A)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨c1, c2, c3⟩ := h11_card hn hK hAN hA1 hA
  have hV : Nat.card (VM K) = 2 ^ (4 * n) := by rw [card_VM, hK, ← pow_mul, mul_comm]
  have hVp : IsPGroup 2 (VM K) := IsPGroup.of_card hV
  have hAp : IsPGroup 2 A := by
    rintro ⟨x, hx⟩
    exact ⟨1, Subtype.ext (by simpa using hA.2 x hx)⟩
  obtain ⟨r, hr⟩ := hAp.exists_card_eq
  obtain ⟨k, hk⟩ := (hVp.to_subgroup (fixV A)).exists_card_eq
  have hkV : k ≤ 4 * n := by
    have h1 := Subgroup.card_le_card_group (fixV A)
    rw [hk, hV] at h1
    exact (Nat.pow_le_pow_iff_right (by norm_num)).mp h1
  rw [rk_eq_of_card hr, rkIdx_eq_of_card hk hV]
  rw [hr, hk, hK] at c1 c2 c3
  have hpow : ∀ a b : ℕ, 2 ^ a ≤ 2 ^ b → a ≤ b := fun a b h =>
    (Nat.pow_le_pow_iff_right (by norm_num)).mp h
  refine ⟨?_, ?_, fun hAL => ?_⟩
  · have := hpow (r + k + n) (1 + 4 * n) (by
      calc 2 ^ (r + k + n) = 2 ^ r * 2 ^ k * 2 ^ n := by rw [pow_add, pow_add]
        _ ≤ 2 * (2 ^ n) ^ 4 := c1
        _ = 2 ^ (1 + 4 * n) := by rw [pow_add, pow_one, ← pow_mul, mul_comm n 4])
    omega
  · rcases c2 with c2 | ⟨hn2, t, ht, htc⟩
    · left
      have := hpow (r + k + 2) (4 * n) (by
        calc 2 ^ (r + k + 2) = 2 ^ r * 2 ^ k * 4 := by rw [pow_add, pow_add]; norm_num
          _ ≤ (2 ^ n) ^ 4 := c2
          _ = 2 ^ (4 * n) := by rw [← pow_mul, mul_comm n 4])
      omega
    · right
      refine ⟨hn2, t, ht, ?_⟩
      obtain ⟨j, hj⟩ := (hVp.to_subgroup (fixV (Subgroup.zpowers t))).exists_card_eq
      rw [rkIdx_eq_of_card hj hV]
      rw [hj] at htc
      have h1 : 2 ^ (j + n) = 2 ^ (4 * n) := by
        rw [pow_add, htc, ← pow_mul, mul_comm n 4]
      have h2 := Nat.pow_right_injective (le_refl 2) h1
      omega
  · have := hpow (r + k + n) (4 * n) (by
      calc 2 ^ (r + k + n) = 2 ^ r * 2 ^ k * 2 ^ n := by rw [pow_add, pow_add]
        _ ≤ (2 ^ n) ^ 4 := c3 hAL
        _ = 2 ^ (4 * n) := by rw [← pow_mul, mul_comm n 4])
    omega

end CFSG.Quasithin.H13.H11P

end
