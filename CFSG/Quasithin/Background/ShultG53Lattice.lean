module

public import CFSG.Quasithin.Background.ShultG53Defs
public import Mathlib.Order.CompletePartialOrder

public section

namespace CFSG.Quasithin.ShultG53

section Top

variable {X A : Type} [AddCommGroup A] (act : X → A → A)

@[expose] def IsTop (N K : AddSubgroup A) : Prop :=
  K < N ∧ InvSub act K ∧ ∀ S : AddSubgroup A, InvSub act S → S ≤ N → S ≠ N → S ≤ K

variable {act}

theorem IsTop.isMaxInvSub {N K : AddSubgroup A} (h : IsTop act N K) : IsMaxInvSub act N K := by
  obtain ⟨hlt, hinv, hall⟩ := h
  refine ⟨hlt, hinv, fun K' hK' hKK' hK'N => ?_⟩
  by_cases hne : K' = N
  · exact Or.inr hne
  · exact Or.inl (le_antisymm (hall K' hK' hK'N hne) hKK')

theorem IsTop.eq_of_isMaxInvSub {N K K' : AddSubgroup A} (h : IsTop act N K)
    (h' : IsMaxInvSub act N K') : K' = K := by
  obtain ⟨hlt, hinv, hall⟩ := h
  obtain ⟨hlt', hinv', hmax'⟩ := h'
  have h1 : K' ≤ K := hall K' hinv' hlt'.le hlt'.ne
  rcases hmax' K hinv h1 hlt.le with h2 | h2
  · exact h2.symm
  · exact absurd h2 hlt.ne

theorem IsTop.jrad_eq {N K : AddSubgroup A} (h : IsTop act N K) : jrad act N = K := by
  have hmax := h.isMaxInvSub
  have hinf : (⨅ (K' : AddSubgroup A) (_ : IsMaxInvSub act N K'), K') = K :=
    le_antisymm (iInf₂_le K hmax) (le_iInf₂ fun K' hK' => (h.eq_of_isMaxInvSub hK').symm.le)
  unfold jrad
  rw [hinf]
  exact inf_eq_right.mpr h.1.le

theorem isTop_bot_of_simple (h0 : ∀ g, act g 0 = 0) {N : AddSubgroup A} (hN : ⊥ < N)
    (hs : ∀ S : AddSubgroup A, InvSub act S → S ≤ N → S ≠ N → S = ⊥) : IsTop act N ⊥ :=
  ⟨hN, fun g a ha => by rw [AddSubgroup.mem_bot.mp ha, h0]; exact zero_mem _,
    fun S hS hSN hne => (hs S hS hSN hne).le⟩

theorem exists_isMaxInvSub_ge [Finite A] {N S : AddSubgroup A} (hS : InvSub act S)
    (hlt : S < N) : ∃ K, IsMaxInvSub act N K ∧ S ≤ K := by
  haveI : Finite (AddSubgroup A) :=
    Finite.of_injective (SetLike.coe : AddSubgroup A → Set A) SetLike.coe_injective
  obtain ⟨K, hSK, hK, hmax⟩ := Set.Finite.exists_le_maximal
    (Set.toFinite {K : AddSubgroup A | InvSub act K ∧ K < N}) (show S ∈ _ from ⟨hS, hlt⟩)
  refine ⟨K, ⟨hK.2, hK.1, fun K' hK' h1 h2 => ?_⟩, hSK⟩
  by_cases hne : K' = N
  · exact Or.inr hne
  · exact Or.inl (le_antisymm (hmax ⟨hK', lt_of_le_of_ne h2 hne⟩ h1) h1)

end Top

section Chain

variable {X A : Type} [AddCommGroup A] {act : X → A → A}

theorem jradPow_eq_chain (M : ℕ → AddSubgroup A) (h : ∀ n < 5, IsTop act (M n) (M (n + 1))) :
    ∀ n ≤ 5, jradPow act n (M 0) = M n := by
  intro n
  induction n with
  | zero => intro _; rfl
  | succ n ih =>
    intro hn
    have h1 : jradPow act (n + 1) (M 0) = jrad act (jradPow act n (M 0)) := by
      unfold jradPow
      rw [Function.iterate_succ_apply']
    rw [h1, ih (by omega)]
    exact (h n (by omega)).jrad_eq

theorem eq_chain_of_invSub (M : ℕ → AddSubgroup A) (h : ∀ n < 5, IsTop act (M n) (M (n + 1)))
    (h5 : M 5 = ⊥) {S : AddSubgroup A} (hS : InvSub act S) (hS0 : S ≤ M 0) :
    ∃ n ≤ 5, S = M n := by
  have key : ∀ j : ℕ, j ≤ 5 → S ≤ M (5 - j) → ∃ n ≤ 5, S = M n := by
    intro j
    induction j with
    | zero =>
      intro _ hle
      exact ⟨5, le_rfl, by rw [h5] at hle ⊢; exact le_bot_iff.mp hle⟩
    | succ j ih =>
      intro hj hle
      by_cases heq : S = M (5 - (j + 1))
      · exact ⟨5 - (j + 1), by omega, heq⟩
      · have hlt := (h (5 - (j + 1)) (by omega)).2.2 S hS hle heq
        have : 5 - (j + 1) + 1 = 5 - j := by omega
        rw [this] at hlt
        exact ih (by omega) hlt
  exact key 5 le_rfl (by simpa using hS0)

end Chain

section Transport

variable {X A A' : Type} [AddCommGroup A] [AddCommGroup A'] {act : X → A → A}
  {act' : X → A' → A'} (e : A ≃+ A') (he : ∀ g a, act' g (e a) = e (act g a))

include he

theorem mem_mapAddSubgroup {S : AddSubgroup A} {x : A'} :
    x ∈ e.mapAddSubgroup S ↔ e.symm x ∈ S :=
  AddSubgroup.mem_map_equiv

theorem invSub_map_iff {S : AddSubgroup A} :
    InvSub act' (e.mapAddSubgroup S) ↔ InvSub act S := by
  constructor
  · intro h g s hs
    have h1 : e s ∈ e.mapAddSubgroup S := (mem_mapAddSubgroup e he).mpr (by simpa using hs)
    have h2 := h g _ h1
    rw [he] at h2
    simpa [mem_mapAddSubgroup e he] using h2
  · intro h g a' ha'
    rw [mem_mapAddSubgroup e he] at ha' ⊢
    have h1 := h g _ ha'
    have : e.symm (act' g a') = act g (e.symm a') := by
      apply e.injective
      rw [← he]
      simp
    rw [this]
    exact h1

theorem isMaxInvSub_map_iff {N K : AddSubgroup A} :
    IsMaxInvSub act' (e.mapAddSubgroup N) (e.mapAddSubgroup K) ↔ IsMaxInvSub act N K := by
  unfold IsMaxInvSub
  rw [(e.mapAddSubgroup).lt_iff_lt, invSub_map_iff e he]
  refine and_congr_right fun _ => and_congr_right fun _ =>
    ⟨fun h K' hK' h1 h2 => ?_, fun h K' hK' h1 h2 => ?_⟩
  · have := h (e.mapAddSubgroup K') ((invSub_map_iff e he).mpr hK')
      ((e.mapAddSubgroup).le_iff_le.mpr h1) ((e.mapAddSubgroup).le_iff_le.mpr h2)
    rcases this with h3 | h3
    · exact Or.inl ((e.mapAddSubgroup).injective h3)
    · exact Or.inr ((e.mapAddSubgroup).injective h3)
  · have h0 : e.mapAddSubgroup (e.mapAddSubgroup.symm K') = K' :=
      (e.mapAddSubgroup).apply_symm_apply K'
    have hinv : InvSub act (e.mapAddSubgroup.symm K') := by
      rw [← invSub_map_iff e he, h0]; exact hK'
    have := h _ hinv (by rw [← (e.mapAddSubgroup).le_iff_le, h0]; exact h1)
      (by rw [← (e.mapAddSubgroup).le_iff_le, h0]; exact h2)
    rcases this with h3 | h3
    · left; rw [← h0, h3]
    · right; rw [← h0, h3]

theorem jrad_map {N : AddSubgroup A} :
    jrad act' (e.mapAddSubgroup N) = e.mapAddSubgroup (jrad act N) := by
  ext x
  unfold jrad
  simp only [AddSubgroup.mem_inf, AddSubgroup.mem_iInf, mem_mapAddSubgroup e he]
  refine and_congr Iff.rfl ⟨fun h K hK => ?_, fun h K' hK' => ?_⟩
  · exact (mem_mapAddSubgroup e he).mp (h (e.mapAddSubgroup K) ((isMaxInvSub_map_iff e he).mpr hK))
  · have h0 : e.mapAddSubgroup (e.mapAddSubgroup.symm K') = K' :=
      (e.mapAddSubgroup).apply_symm_apply K'
    have hK : IsMaxInvSub act N (e.mapAddSubgroup.symm K') :=
      (isMaxInvSub_map_iff e he).mp (by rw [h0]; exact hK')
    have := h _ hK
    rw [← h0]
    exact (mem_mapAddSubgroup e he).mpr this

theorem jradPow_map (n : ℕ) {N : AddSubgroup A} :
    jradPow act' n (e.mapAddSubgroup N) = e.mapAddSubgroup (jradPow act n N) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    unfold jradPow at ih ⊢
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih]
    exact jrad_map e he

end Transport

end CFSG.Quasithin.ShultG53
