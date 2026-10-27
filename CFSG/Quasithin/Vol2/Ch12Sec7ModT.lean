module

public import CFSG.Quasithin.Vol2.Ch12Sec7ModS

public section

namespace CFSG.Quasithin.H13.S127.Mod

open CFSG.Open CFSG.Blueprint CFSG.Quasithin
open scoped IsMulCommutative

@[expose] def IsLin (B : B6) : Prop := ∀ v < 64, B.app (wV v) = wV (B.app v)

@[expose] def IsSemi (B : B6) : Prop := ∀ v < 64, B.app (wV v) = wV (wV (B.app v))

theorem wV_ne_wV_wV : ∀ x < 64, x ≠ 0 → wV x ≠ wV (wV x) := by decide

theorem sV_one : ∀ x < 64, sV 1 x = x := by decide

theorem sV_two : ∀ x < 64, sV 2 x = wV x := by decide

theorem sV_three : ∀ x < 64, sV 3 x = x ^^^ wV x := by decide

theorem wV_wV_eq : ∀ x < 64, wV (wV x) = x ^^^ wV x := by decide

theorem not_lin_and_semi {B : B6} (hv : B.Valid) (h1 : B.app 1 ≠ 0) (hl : IsLin B)
    (hs : IsSemi B) : False := by
  have := (hl 1 (by norm_num)).symm.trans (hs 1 (by norm_num))
  exact wV_ne_wV_wV _ (B6.app_lt hv 1) h1 this

theorem app_sV_scal {B : B6} (hv : B.Valid) (hB : IsLin B ∨ IsSemi B) {c : ℕ} (hc : c < 4)
    (hc0 : c ≠ 0) {v : ℕ} (hvl : v < 64) :
    ∃ c' < 4, c' ≠ 0 ∧ B.app (sV c v) = sV c' (B.app v) := by
  have hx := B6.app_lt hv v
  have hw := wV_lt v hvl
  interval_cases c
  · exact absurd rfl hc0
  · exact ⟨1, by norm_num, by norm_num, by rw [sV_one _ hvl, sV_one _ hx]⟩
  · rcases hB with hl | hs
    · exact ⟨2, by norm_num, by norm_num, by rw [sV_two _ hvl, sV_two _ hx, hl v hvl]⟩
    · exact ⟨3, by norm_num, by norm_num, by rw [sV_two _ hvl, sV_three _ hx, hs v hvl,
        wV_wV_eq _ hx]⟩
  · rcases hB with hl | hs
    · exact ⟨3, by norm_num, by norm_num, by
        rw [sV_three _ hvl, sV_three _ hx, B6.app_xor, hl v hvl]⟩
    · refine ⟨2, by norm_num, by norm_num, ?_⟩
      rw [sV_three _ hvl, sV_two _ hx, B6.app_xor, hs v hvl, wV_wV_eq _ hx, ← Nat.xor_assoc,
        Nat.xor_self, Nat.zero_xor]

theorem pn_app_pn {B : B6} (hv : B.Valid) (hB : IsLin B ∨ IsSemi B) {v : ℕ} (hvl : v < 64)
    (hv0 : v ≠ 0) : pn (B.app (pn v)) = pn (B.app v) := by
  obtain ⟨c, hc, hc0, he⟩ := pn_scal_of_ne v hvl hv0
  obtain ⟨c', hc', hc'0, he'⟩ := app_sV_scal hv hB hc hc0 hvl
  rw [he, he', pn_sV _ (B6.app_lt hv v) _ hc' hc'0]

theorem isLin_comp {B D : B6} (hB : IsLin B) (hD : IsLin D) (hDv : D.Valid) :
    IsLin (B.comp D) := by
  intro v hv
  rw [B6.app_comp, B6.app_comp, hD v hv, hB _ (B6.app_lt hDv v)]

theorem isLin_comp_semi {B D : B6} (hB : IsSemi B) (hD : IsSemi D) (hDv : D.Valid)
    (hBv : B.Valid) : IsLin (B.comp D) := by
  intro v hv
  have hx := B6.app_lt hDv v
  rw [B6.app_comp, B6.app_comp, hD v hv, hB _ (wV_lt _ hx), hB _ hx,
    wV_cube _ (B6.app_lt hBv _)]

theorem isSemi_comp_lin {B D : B6} (hB : IsSemi B) (hD : IsLin D) (hDv : D.Valid) :
    IsSemi (B.comp D) := by
  intro v hv
  rw [B6.app_comp, B6.app_comp, hD v hv, hB _ (B6.app_lt hDv v)]

theorem isSemi_comp {B D : B6} (hB : IsLin B) (hD : IsSemi D) (hDv : D.Valid) :
    IsSemi (B.comp D) := by
  intro v hv
  have hx := B6.app_lt hDv v
  rw [B6.app_comp, B6.app_comp, hD v hv, hB _ (wV_lt _ hx), hB _ hx]

theorem sign_eq_one_of_odd {α : Type} [Fintype α] [DecidableEq α] {σ : Equiv.Perm α}
    (h : Odd (orderOf σ)) : Equiv.Perm.sign σ = 1 := by
  have h1 : (Equiv.Perm.sign σ) ^ orderOf σ = 1 := by
    rw [← map_pow, pow_orderOf_eq_one, map_one]
  rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h2 | h2
  · exact h2
  · rw [h2, h.neg_one_pow] at h1
    exact absurd h1 (by decide)

theorem no_normal_three {α : Type} [Fintype α] [DecidableEq α] (hα : Fintype.card α = 6)
    {N : Subgroup (Equiv.Perm α)} (hN : N.Normal) (h3 : IsPGroup 3 N) : N = ⊥ := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Nontrivial α := Fintype.one_lt_card_iff_nontrivial.1 (by rw [hα]; norm_num)
  have hsimple : IsSimpleGroup (alternatingGroup α) :=
    alternatingGroup.isSimpleGroup (by rw [Nat.card_eq_fintype_card, hα]; norm_num)
  have hNA : N ≤ alternatingGroup α := by
    intro σ hσ
    obtain ⟨k, hk⟩ := h3 ⟨σ, hσ⟩
    have hk' : σ ^ 3 ^ k = 1 := by simpa using congrArg Subtype.val hk
    have hodd : Odd (orderOf σ) := by
      have hd := orderOf_dvd_of_pow_eq_one hk'
      obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_three).1 hd
      rw [hj]
      exact Odd.pow (by decide)
    exact Equiv.Perm.mem_alternatingGroup.2 (sign_eq_one_of_odd hodd)
  have hNn : (N.subgroupOf (alternatingGroup α)).Normal := hN.subgroupOf _
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (N.subgroupOf (alternatingGroup α)) with hb | ht
  · apply le_antisymm _ bot_le
    intro σ hσ
    have : (⟨σ, hNA hσ⟩ : alternatingGroup α) ∈ N.subgroupOf (alternatingGroup α) := hσ
    rw [hb] at this
    have := Subgroup.mem_bot.1 this
    exact Subgroup.mem_bot.2 (congrArg Subtype.val this)
  · exfalso
    have hle : alternatingGroup α ≤ N := by
      intro σ hσ
      have : (⟨σ, hσ⟩ : alternatingGroup α) ∈ N.subgroupOf (alternatingGroup α) := by
        rw [ht]
        trivial
      exact this
    obtain ⟨n, hn⟩ := IsPGroup.iff_card.1 h3
    have hdvd : Nat.card (alternatingGroup α) ∣ 3 ^ n := by
      rw [← hn]
      exact Subgroup.card_dvd_of_le hle
    rw [nat_card_alternatingGroup, Nat.card_eq_fintype_card, hα] at hdvd
    have h360 : Nat.factorial 6 / 2 = 360 := by decide
    rw [h360] at hdvd
    obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_three).1 hdvd
    have : 2 ∣ 3 ^ j := hj ▸ (by norm_num : 2 ∣ 360)
    exact absurd (Nat.Prime.dvd_of_dvd_pow Nat.prime_two this) (by decide)

end CFSG.Quasithin.H13.S127.Mod

end
