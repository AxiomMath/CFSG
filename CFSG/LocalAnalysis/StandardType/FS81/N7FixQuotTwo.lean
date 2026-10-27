module

public import CFSG.LocalAnalysis.StandardType.FS81.N7FixQuot
import CFSG.LocalAnalysis.StandardType.FS81.N7FixQuotPerm
import CFSG.LocalAnalysis.StandardType.FS81.N7FixQuotNormal

public section

namespace CFSG.StandardType.FrameRoute.FS81

open scoped Matrix

section PermTwo

open Equiv

variable {β : Type*} [Fintype β] [DecidableEq β]

private lemma p9uN7QT_comap_normal {T : Finset β} {M : Subgroup (Perm β)}
    (hnorm : ∀ g : Perm β, (∀ i, i ∉ T → g i = i) → ∀ m ∈ M, g * m * g⁻¹ ∈ M) :
    (M.comap (Equiv.Perm.ofSubtype (p := (· ∈ T)))).Normal := by
  refine ⟨fun n hn g => ?_⟩
  rw [Subgroup.mem_comap] at hn ⊢
  rw [map_mul, map_mul, map_inv]
  exact hnorm _ (fun i hi => Equiv.Perm.ofSubtype_apply_of_not_mem (p := (· ∈ T)) g hi) _ hn

private lemma p9uN7QT_eq_bot_of_comap_eq_bot {T : Finset β} {M : Subgroup (Perm β)}
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

theorem perm_eq_bot_of_normal_of_two_power (T : Finset β) (hT : 5 ≤ T.card)
    {M : Subgroup (Perm β)} (hMT : ∀ m ∈ M, ∀ i, i ∉ T → m i = i)
    (hnorm : ∀ g : Perm β, (∀ i, i ∉ T → g i = i) → ∀ m ∈ M, g * m * g⁻¹ ∈ M)
    (h2 : ∀ m ∈ M, ∃ k : ℕ, m ^ 2 ^ k = 1) : M = ⊥ := by
  classical
  have hcard : 5 ≤ Fintype.card {x // x ∈ T} := by
    simpa only [Fintype.card_coe] using hT
  have hnormM' : (M.comap (Equiv.Perm.ofSubtype (p := (· ∈ T)))).Normal :=
    p9uN7QT_comap_normal hnorm
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
    obtain ⟨k, hk⟩ := h2 _ hc3M
    have hpow : c3 ^ 2 ^ k = 1 := by
      apply Equiv.Perm.ofSubtype_injective (p := (· ∈ T))
      rw [map_pow, map_one]
      exact hk
    have hdvd : orderOf c3 ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one hpow
    have hord : orderOf c3 = 3 := hc3cyc.orderOf
    rw [hord] at hdvd
    exact absurd (Nat.Prime.dvd_of_dvd_pow Nat.prime_three hdvd) (by norm_num)
  exact p9uN7QT_eq_bot_of_comap_eq_bot hMT hbot

end PermTwo

namespace N7Setup

variable {X : Type} [Group X] [Finite X] (S : N7Setup X)

theorem le_F1_of_normal_two {T : Subgroup X} (hFT : S.F1 ≤ T) (hTH : T ≤ S.H)
    (hnorm : ∀ h ∈ S.H, ∀ t ∈ T, h * t * h⁻¹ ∈ T) (hT : IsPGroup 2 T) : T ≤ S.F1 := by
  let Tset : Finset (Fin 8) := Finset.univ.erase 0
  let M : Subgroup (Equiv.Perm (Fin 8)) := (T.subgroupOf S.H).map S.permHom
  have hM : M = ⊥ := by
    refine perm_eq_bot_of_normal_of_two_power Tset ?_ ?_ ?_ ?_
    · show 5 ≤ Tset.card
      rw [Finset.card_erase_of_mem (Finset.mem_univ 0), Finset.card_univ,
        Fintype.card_fin]
      norm_num
    · intro m hm i hi
      obtain ⟨z, hz, rfl⟩ := Subgroup.mem_map.mp hm
      have hi0 : i = 0 := by
        by_contra h
        exact hi (by simp [Tset, h])
      rw [hi0]
      exact S.permHom_zero z
    · intro g hg m hm
      obtain ⟨z, hz, rfl⟩ := Subgroup.mem_map.mp hm
      have h0T : (0 : Fin 8) ∉ Tset := by simp [Tset]
      have hg0 : g 0 = 0 := hg 0 h0T
      obtain ⟨y, hy, -⟩ := S.exists_permHom_eq hg0
      rw [← hy]
      refine Subgroup.mem_map.mpr ⟨y * z * y⁻¹, ?_, ?_⟩
      · rw [Subgroup.mem_subgroupOf]
        simp only [Subgroup.coe_mul, Subgroup.coe_inv]
        exact hnorm (y : X) y.2 (z : X) ((Subgroup.mem_subgroupOf).mp hz)
      · simp only [map_mul, map_inv]
    · intro m hm
      obtain ⟨z, hz, rfl⟩ := Subgroup.mem_map.mp hm
      have hzX : (z : X) ∈ T := (Subgroup.mem_subgroupOf).mp hz
      obtain ⟨k, hk⟩ := hT ⟨(z : X), hzX⟩
      refine ⟨k, ?_⟩
      have hzX_pow : (z : X) ^ 2 ^ k = 1 := by
        have h := congrArg (fun t : T => (t : X)) hk
        simpa only [Subgroup.coe_pow, Subgroup.coe_one] using h
      have hzpow : z ^ 2 ^ k = 1 := by
        apply Subtype.ext
        rw [Subgroup.coe_pow, Subgroup.coe_one]
        exact hzX_pow
      rw [← map_pow]
      refine (S.permHom_eq_one_iff_mem_F1 (z ^ 2 ^ k)).mpr ?_
      rw [hzpow]
      exact S.F1.one_mem
  intro t ht
  let y : S.H := ⟨t, hTH ht⟩
  have hyM : S.permHom y ∈ M :=
    Subgroup.mem_map.mpr ⟨y, by rw [Subgroup.mem_subgroupOf]; exact ht, rfl⟩
  rw [hM] at hyM
  have hy1 : S.permHom y = 1 := Subgroup.mem_bot.mp hyM
  have hmem := (S.permHom_eq_one_iff_mem_F1 y).mp hy1
  simpa using hmem

end N7Setup

end CFSG.StandardType.FrameRoute.FS81

end
