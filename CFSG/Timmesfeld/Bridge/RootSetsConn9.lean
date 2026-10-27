module

public import CFSG.Timmesfeld.Bridge.RootSetsConn8

public section

namespace CFSG.Timmesfeld.Bridge

open CFSG.Timmesfeld CFSG.Timmesfeld.Connectivity

variable {G : Type} [Group G] {D : Set G}

@[expose] def ThreeClasses (D : Set G) (x : G) (P : Subgroup G) : Prop :=
  ∀ e₁ ∈ D, e₁ ∈ P → ∀ e₂ ∈ D, e₂ ∈ P → e₁ * e₂ ∉ qcore D x P → ∀ ℓ ∈ D, ℓ ∈ P →
    ℓ * e₁ ∈ qcore D x P ∨ ℓ * e₂ ∈ qcore D x P ∨ ℓ * e₁ * e₂ ∈ qcore D x P

namespace Step6

variable {a b c x z : G} {P : Subgroup G}

theorem mem_normalizer_of_conj_mem_L (hC : ConnCex D) (h : Step6 D a b c x z P) {g : G}
    (hg : ∀ l ∈ D, l ∈ P → g * l * g⁻¹ ∈ P) : g ∈ Subgroup.normalizer (P : Set G) := by
  have := hC.setting.finite
  have hle : Subgroup.closure {y | y ∈ D ∧ y ∈ P} ≤ P.comap (MulAut.conj g).toMonoidHom := by
    rw [Subgroup.closure_le]
    exact fun l hl => hg l hl.1 hl.2
  apply mem_normalizer_of_conj_mem
  intro p hp
  have hp' : p ∈ Subgroup.closure {y | y ∈ D ∧ y ∈ P} := by
    rw [← h.hPL]
    exact hp
  exact hle hp'

theorem mul_mem_qcore_trans (hC : ConnCex D) {u v w : G} (hv : v ∈ D)
    (huv : u * v ∈ qcore D x P) (hvw : v * w ∈ qcore D x P) : u * w ∈ qcore D x P := by
  have := (qcore D x P).mul_mem huv hvw
  rwa [show u * v * (v * w) = u * (v * v) * w by group, hC.setting.root.mul_self_eq_one hv,
    mul_one] at this

theorem mul_mem_qcore_comm (hC : ConnCex D) {u v : G} (hu : u ∈ D) (hv : v ∈ D)
    (huv : u * v ∈ qcore D x P) : v * u ∈ qcore D x P := by
  have := (qcore D x P).inv_mem huv
  rwa [mul_inv_rev, hC.setting.root.inv_eq hu, hC.setting.root.inv_eq hv] at this

theorem commute_conj_of_isPGroup (hC : ConnCex D) {S : Subgroup G} (hS2 : IsPGroup 2 S) {s ℓ : G}
    (hs : s ∈ D) (hℓ : ℓ ∈ D) (hsS : s ∈ S) (hℓS : ℓ ∈ S) : Commute ℓ (s * ℓ * s⁻¹) := by
  have hD := hC.setting.root
  by_cases hsℓ : Commute s ℓ
  · rw [hsℓ.eq, mul_inv_cancel_right]
  have h4 : orderOf (s * ℓ) = 4 := by
    rcases commute_or_orderOf_mul_eq_four_or_odd hD hs hℓ with h' | h' | ⟨hodd, -⟩
    · exact absurd h' hsℓ
    · exact h'
    · exfalso
      obtain ⟨k, hk⟩ := hS2 ⟨s * ℓ, S.mul_mem hsS hℓS⟩
      have hk' : (s * ℓ) ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
      have h1 : orderOf (s * ℓ) = 1 := by
        have hdvd := orderOf_dvd_of_pow_eq_one hk'
        rcases (Nat.dvd_prime_pow Nat.prime_two).1 hdvd with ⟨j, -, hj⟩
        rcases j with _ | j
        · simpa using hj
        · rw [hj] at hodd
          exact absurd hodd
            (Nat.not_odd_iff_even.2 (Nat.even_pow.2 ⟨even_two, Nat.succ_ne_zero j⟩))
      rw [orderOf_eq_one_iff, mul_eq_one_iff_eq_inv, hD.inv_eq hℓ] at h1
      exact hsℓ (by rw [h1])
  have hsq : (s * ℓ) ^ 2 * (s * ℓ) ^ 2 = 1 := by
    rw [← pow_add, show 2 + 2 = 4 by norm_num, ← h4, pow_orderOf_eq_one]
  have hinv : ℓ * s = (s * ℓ)⁻¹ := by rw [mul_inv_rev, hD.inv_eq hs, hD.inv_eq hℓ]
  have heq : (ℓ * s) ^ 2 = (s * ℓ) ^ 2 := by
    rw [hinv, inv_pow, inv_eq_of_mul_eq_one_right hsq]
  show ℓ * (s * ℓ * s⁻¹) = s * ℓ * s⁻¹ * ℓ
  rw [hD.inv_eq hs]
  calc ℓ * (s * ℓ * s) = (ℓ * s) ^ 2 * s * s := by
        rw [pow_two, mul_assoc, mul_assoc, hD.mul_self_eq_one hs]; group
    _ = (s * ℓ) ^ 2 * s * s := by rw [heq]
    _ = s * ℓ * s * ℓ := by rw [pow_two, mul_assoc _ s s, hD.mul_self_eq_one hs]; group

theorem mem_of_commute_of_threeClasses (hB : OddTranspBender) (h3 : Step6ThreeProductHyp)
    (hC : ConnCex D) (h : Step6 D a b c x z P) (hT : ThreeClasses D x P) {S : Subgroup G}
    (hS2 : IsPGroup 2 S) (hPS : P ≤ S) {e₁ e₂ : G} (he₁ : e₁ ∈ D) (he₂ : e₂ ∈ D)
    (he₁P : e₁ ∈ P) (he₂P : e₂ ∈ P) (h12 : e₁ * e₂ ∉ qcore D x P) {s : G} (hs : s ∈ D)
    (hsS : s ∈ S) (hs₁ : Commute s e₁) (hs₂ : Commute s e₂) : s ∈ P := by
  classical
  have := hC.setting.finite
  have hD := hC.setting.root
  have hN := hC.setting.normal
  suffices key : ∀ n : ℕ, ∀ s ∈ D, s ∈ S → Commute s e₁ → Commute s e₂ →
      {ℓ | ℓ ∈ D ∧ ℓ ∈ P ∧ ¬ Commute s ℓ}.ncard = n → s ∈ P from
    key _ s hs hsS hs₁ hs₂ rfl
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro s hs hsS hs₁ hs₂ hn
  have hsinv : s⁻¹ = s := hD.inv_eq hs
  have hconj : ∀ ℓ ∈ D, ℓ ∈ P → s * ℓ * s⁻¹ ∈ P := by
    intro ℓ hℓ hℓP
    by_cases hsℓ : Commute s ℓ
    · rw [hsℓ.eq, mul_inv_cancel_right]
      exact hℓP
    have hs'D : s * ℓ * s⁻¹ ∈ D := hN s ℓ hℓ
    have hs'S : s * ℓ * s⁻¹ ∈ S := S.mul_mem (S.mul_mem hsS (hPS hℓP)) (S.inv_mem hsS)
    have hℓ₁ : Commute ℓ e₁ := h.commute_of_mem hC hℓ he₁ hℓP he₁P
    have hℓ₂ : Commute ℓ e₂ := h.commute_of_mem hC hℓ he₂ hℓP he₂P
    have hc₁ : Commute (s * ℓ * s⁻¹) e₁ := (hs₁.mul_left hℓ₁).mul_left hs₁.inv_left
    have hc₂ : Commute (s * ℓ * s⁻¹) e₂ := (hs₂.mul_left hℓ₂).mul_left hs₂.inv_left
    have hsub : {ℓ' | ℓ' ∈ D ∧ ℓ' ∈ P ∧ ¬ Commute (s * ℓ * s⁻¹) ℓ'} ⊂
        {ℓ' | ℓ' ∈ D ∧ ℓ' ∈ P ∧ ¬ Commute s ℓ'} := by
      refine ⟨fun ℓ' hℓ' => ⟨hℓ'.1, hℓ'.2.1, fun hc => hℓ'.2.2 ?_⟩, fun hsup => ?_⟩
      · exact ((hc.mul_left (h.commute_of_mem hC hℓ hℓ'.1 hℓP hℓ'.2.1)).mul_left hc.inv_left)
      · have := (hsup ⟨hℓ, hℓP, hsℓ⟩).2.2
        exact this (commute_conj_of_isPGroup hC hS2 hs hℓ hsS (hPS hℓP)).symm
    have hlt := Set.ncard_lt_ncard hsub (Set.toFinite _)
    exact ih _ (hn ▸ hlt) _ hs'D hs'S hc₁ hc₂ rfl
  have hsN : s ∈ Subgroup.normalizer (P : Set G) := h.mem_normalizer_of_conj_mem_L hC hconj
  have hE1 : ∀ u ∈ D, u ∈ P → ∀ v ∈ D, v ∈ P → u * v ∈ qcore D x P →
      s * u * s⁻¹ * (s * v * s⁻¹) ∈ qcore D x P := fun u hu huP v hv hvP huv =>
    h.conj_mul_mem_qcore hB h3 hC hsN hu hv huP hvP huv
  have hfix₁ : s * e₁ * s⁻¹ = e₁ := by rw [hs₁.eq, mul_inv_cancel_right]
  have hfix₂ : s * e₂ * s⁻¹ = e₂ := by rw [hs₂.eq, mul_inv_cancel_right]
  have hss : ∀ u : G, s * (s * u * s⁻¹) * s⁻¹ = u := fun u => by
    rw [hsinv, ← mul_assoc, ← mul_assoc, hD.mul_self_eq_one hs, one_mul, mul_assoc,
      hD.mul_self_eq_one hs, mul_one]
  have he₁Q : e₁ ∉ qcore D x P := h.not_mem_qcore hC he₁
  have he₂Q : e₂ ∉ qcore D x P := h.not_mem_qcore hC he₂
  refine h.hcent s hs fun ℓ hℓ hℓP => ?_
  have hℓsP := hconj ℓ hℓ hℓP
  have hℓsD : s * ℓ * s⁻¹ ∈ D := hN s ℓ hℓ
  apply h.commute_of_mul_conj_mem_qcore hC hs hsN hℓ hℓP
  rcases hT e₁ he₁ he₁P e₂ he₂ he₂P h12 ℓ hℓ hℓP with hq | hq | hq
  · have h1 := hE1 ℓ hℓ hℓP e₁ he₁ he₁P hq
    rw [hfix₁] at h1
    exact mul_mem_qcore_trans hC he₁ hq (mul_mem_qcore_comm hC hℓsD he₁ h1)
  · have h1 := hE1 ℓ hℓ hℓP e₂ he₂ he₂P hq
    rw [hfix₂] at h1
    exact mul_mem_qcore_trans hC he₂ hq (mul_mem_qcore_comm hC hℓsD he₂ h1)
  · rcases hT e₁ he₁ he₁P e₂ he₂ he₂P h12 _ hℓsD hℓsP with hq' | hq' | hq'
    · exfalso
      have h1 := hE1 _ hℓsD hℓsP e₁ he₁ he₁P hq'
      rw [hss, hfix₁] at h1
      apply he₂Q
      have := (qcore D x P).mul_mem ((qcore D x P).inv_mem h1) hq
      rwa [mul_inv_rev, hD.inv_eq hℓ, hD.inv_eq he₁, show e₁ * ℓ * (ℓ * e₁ * e₂) =
        e₁ * (ℓ * ℓ) * e₁ * e₂ by group, hD.mul_self_eq_one hℓ, mul_one,
        hD.mul_self_eq_one he₁, one_mul] at this
    · exfalso
      have h1 := hE1 _ hℓsD hℓsP e₂ he₂ he₂P hq'
      rw [hss, hfix₂] at h1
      apply he₁Q
      have hc12 : Commute e₁ e₂ := h.commute_of_mem hC he₁ he₂ he₁P he₂P
      have := (qcore D x P).mul_mem ((qcore D x P).inv_mem h1) hq
      rwa [mul_inv_rev, hD.inv_eq hℓ, hD.inv_eq he₂, show e₂ * ℓ * (ℓ * e₁ * e₂) =
        e₂ * (ℓ * ℓ) * e₁ * e₂ by group, hD.mul_self_eq_one hℓ, mul_one, ← hc12.eq, mul_assoc,
        hD.mul_self_eq_one he₂, mul_one] at this
    · have := (qcore D x P).mul_mem hq ((qcore D x P).inv_mem hq')
      rwa [mul_inv_rev, mul_inv_rev, hD.inv_eq he₂, hD.inv_eq he₁, hD.inv_eq hℓsD,
        show ℓ * e₁ * e₂ * (e₂ * (e₁ * (s * ℓ * s⁻¹))) =
          ℓ * e₁ * (e₂ * e₂) * e₁ * (s * ℓ * s⁻¹) by group, hD.mul_self_eq_one he₂, mul_one,
        mul_assoc ℓ e₁ e₁, hD.mul_self_eq_one he₁, mul_one] at this

end Step6

end CFSG.Timmesfeld.Bridge
