module

public import Mathlib.GroupTheory.SpecificGroups.Alternating.Simple
public import Mathlib.GroupTheory.Perm.Cycle.Type
public import Mathlib.GroupTheory.Perm.Support

public section

namespace CFSG.StandardType.FrameRoute.FS81

open Equiv

variable {β : Type*} [Fintype β] [DecidableEq β]

private lemma p9uN7QN_comap_normal {T : Finset β} {M : Subgroup (Perm β)}
    (hnorm : ∀ g : Perm β, (∀ i, i ∉ T → g i = i) → ∀ m ∈ M, g * m * g⁻¹ ∈ M) :
    (M.comap (Equiv.Perm.ofSubtype (p := (· ∈ T)))).Normal := by
  refine ⟨fun n hn g => ?_⟩
  rw [Subgroup.mem_comap] at hn ⊢
  rw [map_mul, map_mul, map_inv]
  exact hnorm _ (fun i hi => Equiv.Perm.ofSubtype_apply_of_not_mem (p := (· ∈ T)) g hi) _ hn

private lemma p9uN7QN_eq_bot_of_comap_eq_bot {T : Finset β} {M : Subgroup (Perm β)}
    (hMT : ∀ m ∈ M, ∀ i, i ∉ T → m i = i)
    (hbot : M.comap (Equiv.Perm.ofSubtype (p := (· ∈ T))) = ⊥) : M = ⊥ := by
  rw [eq_bot_iff]
  intro m hm
  rw [Subgroup.mem_bot]
  have hsupp : (m.support : Set β) ⊆ (T : Set β) := by
    intro i hi
    by_contra hTi
    have hi' : i ∈ m.support := hi
    rw [Equiv.Perm.mem_support] at hi'
    exact hi' (hMT m hm i hTi)
  have hrange : m ∈ (Equiv.Perm.ofSubtype (p := (· ∈ T)) :
      Perm {x // x ∈ T} →* Perm β).range :=
    Equiv.Perm.mem_range_ofSubtype_iff.2 hsupp
  obtain ⟨u, hu⟩ := hrange
  have huM' : u ∈ M.comap (Equiv.Perm.ofSubtype (p := (· ∈ T))) := by
    rw [Subgroup.mem_comap]
    rw [hu]
    exact hm
  have hu1 : u = 1 := by
    rw [hbot, Subgroup.mem_bot] at huM'
    exact huM'
  rw [← hu, hu1, map_one]

theorem perm_eq_bot_of_normal_of_exp_two (T : Finset β) (hT : 5 ≤ T.card)
    {M : Subgroup (Perm β)} (hMT : ∀ m ∈ M, ∀ i, i ∉ T → m i = i)
    (hnorm : ∀ g : Perm β, (∀ i, i ∉ T → g i = i) → ∀ m ∈ M, g * m * g⁻¹ ∈ M)
    (h2 : ∀ m ∈ M, m * m = 1) : M = ⊥ := by
  classical
  have hcard : 5 ≤ Fintype.card {x // x ∈ T} := by
    simpa only [Fintype.card_coe] using hT
  have hnormM' : (M.comap (Equiv.Perm.ofSubtype (p := (· ∈ T)))).Normal :=
    p9uN7QN_comap_normal hnorm
  have hbot : M.comap (Equiv.Perm.ofSubtype (p := (· ∈ T))) = ⊥ := by
    by_contra hne
    haveI : (M.comap (Equiv.Perm.ofSubtype (p := (· ∈ T)))).Normal := hnormM'
    have hle : alternatingGroup {x // x ∈ T}
        ≤ M.comap (Equiv.Perm.ofSubtype (p := (· ∈ T))) :=
      Equiv.Perm.alternatingGroup_le_of_normal (N := _)
        (by simpa only [Nat.card_eq_fintype_card] using hcard)
        ((Subgroup.nontrivial_iff_ne_bot _).2 hne)
    obtain ⟨a, b, c, hab, hac, hbc⟩ :=
      (Fintype.two_lt_card_iff (α := {x // x ∈ T})).1 (by omega)
    set c3 : Perm {x // x ∈ T} := swap a b * swap a c with hc3
    have hc3cyc : Equiv.Perm.IsThreeCycle c3 := by
      rw [hc3]
      exact Equiv.Perm.isThreeCycle_swap_mul_swap_same hab hac hbc
    have hc3A : c3 ∈ alternatingGroup {x // x ∈ T} := hc3cyc.mem_alternatingGroup
    have hc3M' : c3 ∈ M.comap (Equiv.Perm.ofSubtype (p := (· ∈ T))) := hle hc3A
    have hc3M : Equiv.Perm.ofSubtype (p := (· ∈ T)) c3 ∈ M := by
      rwa [Subgroup.mem_comap] at hc3M'
    have hsq : c3 * c3 = 1 := by
      apply Equiv.Perm.ofSubtype_injective (p := (· ∈ T))
      rw [map_mul, map_one]
      exact h2 _ hc3M
    have hdvd : orderOf c3 ∣ 2 :=
      orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact hsq)
    have hord : orderOf c3 = 3 := hc3cyc.orderOf
    rw [hord] at hdvd
    exact absurd hdvd (by norm_num)
  exact p9uN7QN_eq_bot_of_comap_eq_bot hMT hbot

theorem perm_eq_bot_of_normal_of_odd (T : Finset β) (hT : 5 ≤ T.card)
    {M : Subgroup (Perm β)} (hMT : ∀ m ∈ M, ∀ i, i ∉ T → m i = i)
    (hnorm : ∀ g : Perm β, (∀ i, i ∉ T → g i = i) → ∀ m ∈ M, g * m * g⁻¹ ∈ M)
    (hodd : ∀ m ∈ M, ∃ n : ℕ, Odd n ∧ m ^ n = 1) : M = ⊥ := by
  classical
  have hcard : 5 ≤ Fintype.card {x // x ∈ T} := by
    simpa only [Fintype.card_coe] using hT
  have hnormM' : (M.comap (Equiv.Perm.ofSubtype (p := (· ∈ T)))).Normal :=
    p9uN7QN_comap_normal hnorm
  have hbot : M.comap (Equiv.Perm.ofSubtype (p := (· ∈ T))) = ⊥ := by
    by_contra hne
    haveI : (M.comap (Equiv.Perm.ofSubtype (p := (· ∈ T)))).Normal := hnormM'
    have hle : alternatingGroup {x // x ∈ T}
        ≤ M.comap (Equiv.Perm.ofSubtype (p := (· ∈ T))) :=
      Equiv.Perm.alternatingGroup_le_of_normal (N := _)
        (by simpa only [Nat.card_eq_fintype_card] using hcard)
        ((Subgroup.nontrivial_iff_ne_bot _).2 hne)
    obtain ⟨a, b, c, hab, hac, hbc⟩ :=
      (Fintype.two_lt_card_iff (α := {x // x ∈ T})).1 (by omega)
    have hlt : ({a, b, c} : Finset {x // x ∈ T}).card
        < (Finset.univ : Finset {x // x ∈ T}).card := by
      rw [Finset.card_univ]
      exact lt_of_le_of_lt (Finset.card_le_three (a := a) (b := b) (c := c)) (by omega)
    obtain ⟨d, -, hd⟩ := Finset.exists_mem_notMem_of_card_lt_card hlt
    have hda : d ≠ a := fun h => hd (by simp [h])
    have hdb : d ≠ b := fun h => hd (by simp [h])
    have hdc : d ≠ c := fun h => hd (by simp [h])
    have had : a ≠ d := hda.symm
    have hbd : b ≠ d := hdb.symm
    have hcd : c ≠ d := hdc.symm
    have hnodup : [a, b, c, d].Nodup := by
      simp [hab, hac, had, hbc, hbd, hcd]
    set δ : Perm {x // x ∈ T} := swap a b * swap c d with hδ
    have hδA : δ ∈ alternatingGroup {x // x ∈ T} := by
      rw [Equiv.Perm.mem_alternatingGroup, hδ, Equiv.Perm.sign_mul,
        Equiv.Perm.sign_swap hab, Equiv.Perm.sign_swap hcd]
      decide
    have hδM' : δ ∈ M.comap (Equiv.Perm.ofSubtype (p := (· ∈ T))) := hle hδA
    have hδM : Equiv.Perm.ofSubtype (p := (· ∈ T)) δ ∈ M := by
      rwa [Subgroup.mem_comap] at hδM'
    obtain ⟨n, hnodd, hn⟩ := hodd _ hδM
    have hδord : orderOf δ = 2 := by
      rw [hδ, Equiv.Perm.Disjoint.orderOf (Equiv.Perm.disjoint_swap_swap hnodup),
        Equiv.Perm.IsSwap.orderOf (Equiv.Perm.swap_isSwap_iff.mpr hab),
        Equiv.Perm.IsSwap.orderOf (Equiv.Perm.swap_isSwap_iff.mpr hcd)]
      norm_num
    have hpow : δ ^ n = 1 := by
      apply Equiv.Perm.ofSubtype_injective (p := (· ∈ T))
      rw [map_pow, map_one]
      exact hn
    have hdvd : orderOf δ ∣ n := orderOf_dvd_of_pow_eq_one hpow
    rw [hδord] at hdvd
    obtain ⟨k, hk⟩ := hdvd
    obtain ⟨m, hm⟩ := hnodd
    omega
  exact p9uN7QN_eq_bot_of_comap_eq_bot hMT hbot

theorem perm_apply_eq_self_of_preserves_pairs {σ : Perm β} {T : Finset β} (hT : 3 ≤ T.card)
    (h : ∀ i ∈ T, ∀ j ∈ T, i ≠ j → ∀ l, (σ l = i ∨ σ l = j) ↔ (l = i ∨ l = j)) :
    ∀ i ∈ T, σ i = i := by
  intro i hi
  have hcard : 1 < (T.erase i).card := by
    rw [Finset.card_erase_of_mem hi]
    omega
  obtain ⟨j, hj, l, hl, hjl⟩ := Finset.one_lt_card.1 hcard
  rw [Finset.mem_erase] at hj hl
  obtain ⟨hji, hjT⟩ := hj
  obtain ⟨hli, hlT⟩ := hl
  have h1 := (h i hi j hjT (Ne.symm hji) i).2 (Or.inl rfl)
  have h2 := (h i hi l hlT (Ne.symm hli) i).2 (Or.inl rfl)
  rcases h1 with hii | hij
  · exact hii
  · rcases h2 with h2i | hil
    · exact h2i
    · exact absurd (hij.symm.trans hil) hjl

theorem perm_fin_eight_eq_one_of_fixes_card_seven {σ : Perm (Fin 8)} {T : Finset (Fin 8)}
    (hT : T.card = 7) (h : ∀ i ∈ T, σ i = i) : σ = 1 := by
  classical
  have hcompl : (Tᶜ).card = 1 := by
    have h1 : (Tᶜ).card = Fintype.card (Fin 8) - T.card := Finset.card_compl T
    rw [Fintype.card_fin, hT] at h1
    omega
  have hsubset : σ.support ⊆ Tᶜ := by
    intro x hx
    by_contra hxT
    rw [Finset.mem_compl] at hxT
    have hx' : x ∈ σ.support := hx
    rw [Equiv.Perm.mem_support] at hx'
    exact hx' (h x (not_not.mp hxT))
  have hle : σ.support.card ≤ 1 := by
    calc σ.support.card ≤ (Tᶜ).card := Finset.card_le_card hsubset
      _ = 1 := hcompl
  have hne := Equiv.Perm.card_support_ne_one σ
  have hzero : σ.support.card = 0 := by omega
  exact Equiv.Perm.support_eq_empty_iff.1 (Finset.card_eq_zero.1 hzero)

end CFSG.StandardType.FrameRoute.FS81

end
