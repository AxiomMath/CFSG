module

public import CFSG.LocalAnalysis.UniquenessCase.UC22P22qh

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open Subgroup CFSG.ABGLocalTools
open CFSG.CGT.Timmesfeld75 (IsTI)

variable {G : Type} [Group G] [Finite G]

theorem uc22p22qk_mem_normalizer {W : Subgroup G} {n : G} (h : ∀ w ∈ W, n * w * n⁻¹ ∈ W) :
    n ∈ normalizer (W : Set G) :=
  CFSG.Goldschmidt.G310.mem_normalizer_of_map_le (by
    rintro _ ⟨w, hw, rfl⟩
    exact h w hw)

theorem uc22p22qk_mem_sup_iff {A C : Subgroup G} (hAC : A ≤ normalizer (C : Set G)) {x : G} :
    x ∈ A ⊔ C ↔ ∃ a ∈ A, a * x ∈ C := by
  rw [← SetLike.mem_coe, Subgroup.coe_mul_of_left_le_normalizer_right A C hAC]
  constructor
  · rintro ⟨a, ha, c, hc, rfl⟩
    exact ⟨a⁻¹, A.inv_mem ha, by simpa using hc⟩
  · rintro ⟨a, ha, hx⟩
    exact ⟨a⁻¹, A.inv_mem ha, a * x, hx, by group⟩

theorem uc22p22qk_exists_not_mem (D : Data G) {V₀ V : Subgroup G} (hH : F11.Hyp11 D V₀ V) :
    ∃ v ∈ V, v ∉ V₀ := by
  obtain ⟨hV, hV₀V, -, hcase⟩ := uc22p22q_hyp11_unpack D hH
  by_contra hcon
  push Not at hcon
  have hVV₀ : V ≤ V₀ := hcon
  rcases hcase with h0 | ⟨-, hTI₀, -⟩
  · subst h0
    exact hV.1 (le_bot_iff.1 hVV₀)
  · exact hH.2.1 (by rw [le_antisymm hVV₀ hV₀V]; exact hTI₀)

theorem uc22p22qk_frob_unpack (D : Data G) {X Dd : Subgroup G}
    (hfrob : CFSG.Open.uniqueFourIsFrobenius X (pCoreOf 2 D.M) Dd) :
    Dd ≤ D.M ∧ ∀ d ∈ Dd, d ≠ 1 → ∀ r ∈ pCoreOf 2 D.M, d * r * d⁻¹ = r → r = 1 := by
  obtain ⟨-, -, hKX, hKn, hVX, -, -, hfpf⟩ := hfrob
  refine ⟨?_, fun d hd hd1 r hr hdr => hfpf d hd hd1 r hr ?_⟩
  · have hXN : X ≤ normalizer (pCoreOf 2 D.M : Set G) :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer hKX).1 hKn
    have hM : normalizer (pCoreOf 2 D.M : Set G) = D.M :=
      (CFSG.RankThreeCoreUniqueness.Helpers.maxTwoLocal_eq_normalizer_pCoreOf D.M D.maxLocal).symm
    exact fun x hx => hM.le (hXN (hVX hx))
  · exact (mul_inv_eq_iff_eq_mul.1 hdr).symm

theorem uc22p22qk_P1_centralizes_V0 (D : Data G) (h61 : UC6.R6_1 D) {p : ℕ} (hp : p ∈ D.sig) (hp5 : 5 ≤ p)
    {P₁ : Subgroup G} (hP₁M : P₁ ≤ D.M) (hel : IsElemAbelian p P₁) (hnc : ¬ IsCyclic P₁)
    (hirr : IrrOn (D.M ⊓ normalizer (P₁ : Set G)) P₁) {V₀ V : Subgroup G} (hH : F11.Hyp11 D V₀ V) :
    P₁ ≤ centralizer (V₀ : Set G) := by
  obtain ⟨hV, hV₀V, hMV₀, hcase⟩ := uc22p22q_hyp11_unpack D hH
  have hpP : p.Prime := (D.sig_prime p hp).1
  by_cases hbig : 8 ≤ Nat.card V₀
  · have hV₀ : InCalV D.M V₀ := by
      rcases hcase with h0 | ⟨h, -, -⟩
      · subst h0
        simp at hbig
      · exact h
    have hnot : ¬ InCalV1 D.M D.T V₀ := (hH.2.2 hbig).1
    have hW : P₁ ⊓ centralizer (V₀ : Set G) ≠ ⊥ := fun hbot =>
      hnot (uc22p22nc_inCalV1_of_good D h61 hp hV₀ hP₁M (uc22p22e_isPGroup_of_elem hel) hnc hbot)
    have hnorm : D.M ⊓ normalizer (P₁ : Set G) ≤ normalizer ((P₁ ⊓ centralizer (V₀ : Set G) : Subgroup G) : Set G) := by
      rintro n ⟨hnM, hnP⟩
      have h1 := mem_normalizer_iff.1 hnP
      have h2 := mem_normalizer_iff.1 (uc22p22q_mem_normalizer_centralizer (hMV₀ hnM))
      refine mem_normalizer_iff.2 fun x => ?_
      rw [Subgroup.mem_inf, Subgroup.mem_inf, h1 x, h2 x]
    rcases hirr _ inf_le_left hnorm with h | h
    · exact absurd h hW
    · exact inf_eq_left.1 h
  · have hsmall : Nat.card V₀ ≤ 4 := by
      rcases hcase with h0 | ⟨h, -, -⟩
      · subst h0
        simp
      · haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
        obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp (uc22p22e_isPGroup_of_elem h.2.2.2)
        have hk3 : k ≤ 2 := by
          by_contra hk3
          have h8 : 2 ^ 3 ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) (by omega)
          rw [hk] at hbig
          omega
        rw [hk]
        calc 2 ^ k ≤ 2 ^ 2 := Nat.pow_le_pow_right (by norm_num) hk3
          _ = 4 := by norm_num
    intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro w hw
    have hxM : x ∈ D.M := hP₁M hx
    have := uc22p22q_fix_of_card_lt hpP (hel.2 x hx) (fun w hw => (mem_normalizer_iff.1 (hMV₀ hxM) w).1 hw)
      (by omega) w hw
    exact (mul_inv_eq_iff_eq_mul.1 this).symm

theorem uc22p22qk_P1_inf_ctilde (D : Data G) (h61 : UC6.R6_1 D) {p : ℕ} (hp : p ∈ D.sig)
    {P₁ : Subgroup G} (hP₁M : P₁ ≤ D.M) (hel : IsElemAbelian p P₁) (hnc : ¬ IsCyclic P₁)
    (hirr : IrrOn (D.M ⊓ normalizer (P₁ : Set G)) P₁) {V₀ V : Subgroup G} (hH : F11.Hyp11 D V₀ V)
    (h0 : P₁ ≤ centralizer (V₀ : Set G)) : P₁ ⊓ F11.CTilde D.M V₀ V = ⊥ := by
  obtain ⟨hV, hV₀V, hMV₀, hcase⟩ := uc22p22q_hyp11_unpack D hH
  have hMV : D.M ≤ normalizer (V : Set G) := hV.2.2.1
  have hpP : p.Prime := (D.sig_prime p hp).1
  have hp2 : p ≠ 2 := (D.sig_prime p hp).2
  have hnorm : D.M ⊓ normalizer (P₁ : Set G) ≤
      normalizer ((P₁ ⊓ F11.CTilde D.M V₀ V : Subgroup G) : Set G) := by
    rintro n ⟨hnM, hnP⟩
    refine inf_normalizer_le_normalizer_inf ⟨hnP, ?_⟩
    refine uc22p22qk_mem_normalizer fun c hc => uc22p22q_ctilde_conj_mem hMV hMV₀ hnM hc
  rcases hirr _ inf_le_left hnorm with h | h
  · exact h
  · exfalso
    have hP₁C : P₁ ≤ F11.CTilde D.M V₀ V := inf_eq_left.1 h
    have hV₀exp : ∀ w ∈ V₀, w ^ 2 = 1 := fun w hw => hV.2.2.2.2 w (hV₀V hw)
    have hcV : P₁ ≤ centralizer (V : Set G) := by
      intro x hx
      rw [Subgroup.mem_centralizer_iff]
      intro v hv
      have := uc22p22q_conj_eq_of_trivial_action hpP hp2 hV₀exp (hel.2 x hx)
        (fun d hd => (mul_inv_eq_iff_eq_mul.2 ((Subgroup.mem_centralizer_iff.1 (h0 hx)) d hd).symm))
        ((uc22p22q_mem_ctilde.1 (hP₁C hx)).2.2 v hv)
      exact (mul_inv_eq_iff_eq_mul.1 this).symm
    exact hH.2.1 (uc22p22n_isTI_of_noncyclic D h61 hp hV hP₁M (uc22p22e_isPGroup_of_elem hel) hnc hcV)

theorem uc22p22qk_D_inf_ctilde (D : Data G) {Dd V₀ V : Subgroup G} (hH : F11.Hyp11 D V₀ V) (hDM : Dd ≤ D.M)
    (hfpf : ∀ d ∈ Dd, d ≠ 1 → ∀ r ∈ pCoreOf 2 D.M, d * r * d⁻¹ = r → r = 1) :
    Dd ⊓ F11.CTilde D.M V₀ V = ⊥ := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hV, hV₀V, hMV₀, -⟩ := uc22p22q_hyp11_unpack D hH
  have hMV : D.M ≤ normalizer (V : Set G) := hV.2.2.1
  have hRM : pCoreOf 2 D.M ≤ D.M := Subgroup.map_subtype_le _
  have hVR : V ≤ pCoreOf 2 D.M :=
    uc22p22qh_le_pCoreOf hV.2.1 (uc22p22e_isPGroup_of_elem hV.2.2.2)
      (fun k hk x hx => (mem_normalizer_iff.1 (hMV hk) x).1 hx)
  have hV2 : IsPGroup 2 V := uc22p22e_isPGroup_of_elem hV.2.2.2
  obtain ⟨v, hvV, hvV₀⟩ := uc22p22qk_exists_not_mem D hH
  rw [eq_bot_iff]
  rintro d ⟨hdD, hdC⟩
  rw [Subgroup.mem_bot]
  by_contra hd1
  obtain ⟨hdM, hdN, hdv⟩ := uc22p22q_mem_ctilde.1 hdC
  have hodd : Odd (orderOf d) := by
    by_contra hev
    rw [Nat.not_odd_iff_even] at hev
    obtain ⟨k, hk⟩ := hev
    have hpos : 0 < orderOf d := orderOf_pos d
    have hkpos : 0 < k := by omega
    have ht2 : (d ^ k) ^ 2 = 1 := by
      rw [← pow_mul, show k * 2 = orderOf d by omega]
      exact pow_orderOf_eq_one d
    have ht1 : d ^ k ≠ 1 := by
      intro h
      have := Nat.le_of_dvd hkpos (orderOf_dvd_of_pow_eq_one h)
      omega
    have htD : d ^ k ∈ Dd := Subgroup.pow_mem _ hdD k
    obtain ⟨w, hwV, hw1, htw⟩ := uc22p22q_exists_fixed_involution ht2 hV2 hV.1
      (fun w hw => (mem_normalizer_iff.1 (hMV (hDM htD)) w).1 hw)
    exact hw1 (hfpf _ htD ht1 w (hVR hwV) htw)
  obtain ⟨w, hwV, hdw, hwv⟩ := uc22p22q_fixed_in_coset_odd hodd (pow_orderOf_eq_one d)
    (fun a ha b hb => hV.2.2.2.comm ha hb) hV.2.2.2.2
    (fun w hw => (mem_normalizer_iff.1 (hMV hdM) w).1 hw)
    (fun w hw => (mem_normalizer_iff.1 hdN w).1 hw) hvV (hdv v hvV)
  have hw1 : w = 1 := hfpf d hdD hd1 w (hVR hwV) hdw
  rw [hw1, one_mul] at hwv
  exact hvV₀ (by simpa using V₀.inv_mem hwv)

theorem uc22p22qk_comm_mem_pCore (D : Data G) {V₀ V P₁ : Subgroup G} (hH : F11.Hyp11 D V₀ V)
    (hP₁M : P₁ ≤ D.M) (hP₁C : P₁ ⊓ F11.CTilde D.M V₀ V = ⊥)
    (h4b : D.M ≤ normalizer ((P₁ ⊔ pCoreOf 2 D.M : Subgroup G) : Set G)) {c x : G}
    (hc : c ∈ F11.CTilde D.M V₀ V) (hx : x ∈ P₁) : c * x * c⁻¹ * x⁻¹ ∈ pCoreOf 2 D.M := by
  obtain ⟨hV, hV₀V, hMV₀, -⟩ := uc22p22q_hyp11_unpack D hH
  have hMV : D.M ≤ normalizer (V : Set G) := hV.2.2.1
  have hRC : pCoreOf 2 D.M ≤ F11.CTilde D.M V₀ V := uc22p22qh_pCore_le_ctilde D hH
  have hcM : c ∈ D.M := (uc22p22q_mem_ctilde.1 hc).1
  have hxM : x ∈ D.M := hP₁M hx
  have hz1 : c * x * c⁻¹ * x⁻¹ ∈ F11.CTilde D.M V₀ V := by
    have h := uc22p22q_ctilde_conj_mem hMV hMV₀ hxM ((F11.CTilde D.M V₀ V).inv_mem hc)
    have e : c * x * c⁻¹ * x⁻¹ = c * (x * c⁻¹ * x⁻¹) := by group
    rw [e]
    exact (F11.CTilde D.M V₀ V).mul_mem hc h
  have hz2 : c * x * c⁻¹ * x⁻¹ ∈ P₁ ⊔ pCoreOf 2 D.M := by
    have h1 : c * x * c⁻¹ ∈ P₁ ⊔ pCoreOf 2 D.M :=
      (mem_normalizer_iff.1 (h4b hcM) x).1 (Subgroup.mem_sup_left hx)
    exact Subgroup.mul_mem _ h1 (Subgroup.inv_mem _ (Subgroup.mem_sup_left hx))
  have hP₁N : P₁ ≤ normalizer (pCoreOf 2 D.M : Set G) := fun y hy =>
    CFSG.RankThreeCoreUniqueness.Helpers.localGroup_le_normalizer_pCoreOf 2 D.M (hP₁M hy)
  rw [← SetLike.mem_coe, Subgroup.coe_mul_of_left_le_normalizer_right P₁ _ hP₁N] at hz2
  obtain ⟨a, ha, r, hr, hzar⟩ := hz2
  have hzar' : a * r = c * x * c⁻¹ * x⁻¹ := hzar
  have haC : a ∈ F11.CTilde D.M V₀ V := by
    have : a = (c * x * c⁻¹ * x⁻¹) * r⁻¹ := by rw [← hzar']; group
    rw [this]
    exact (F11.CTilde D.M V₀ V).mul_mem hz1 ((F11.CTilde D.M V₀ V).inv_mem (hRC hr))
  have ha1 : a = 1 := by
    have : a ∈ P₁ ⊓ F11.CTilde D.M V₀ V := ⟨ha, haC⟩
    rw [hP₁C] at this
    exact Subgroup.mem_bot.1 this
  rw [← hzar', ha1, one_mul]
  exact hr

end CFSG.LocalAnalysis.UniquenessCase.UC22
