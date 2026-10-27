module

public import Mathlib.GroupTheory.PGroup

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open Subgroup

variable {𝔾 : Type*} [Group 𝔾]

theorem s16h_top_eq_sup_ker_of_map_eq {𝔾' : Type*} [Group 𝔾']
    (f : 𝔾 →* 𝔾') (S : Subgroup 𝔾) (h : S.map f = (⊤ : Subgroup 𝔾).map f) :
    (⊤ : Subgroup 𝔾) = S ⊔ f.ker := by
  refine le_antisymm (fun x _ => ?_) le_top
  have hx : f x ∈ S.map f := by
    rw [h]
    exact Subgroup.mem_map_of_mem f (Subgroup.mem_top x)
  obtain ⟨s, hs, hsf⟩ := Subgroup.mem_map.mp hx
  have hker : s⁻¹ * x ∈ f.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, hsf, inv_mul_cancel]
  have hx' : x = s * (s⁻¹ * x) := by group
  rw [hx']
  exact Subgroup.mul_mem_sup hs hker

theorem s16h_inf_centralizer_eq_bot_of_center_eq_bot {A : Subgroup 𝔾}
    (hZ : Subgroup.center ↥A = ⊥) :
    A ⊓ Subgroup.centralizer (A : Set 𝔾) = ⊥ := by
  rw [eq_bot_iff]
  intro g hg
  rw [Subgroup.mem_inf] at hg
  rw [Subgroup.mem_bot]
  have hmem : (⟨g, hg.1⟩ : ↥A) ∈ Subgroup.center ↥A := by
    rw [Subgroup.mem_center_iff]
    intro b
    exact Subtype.ext (Subgroup.mem_centralizer_iff.mp hg.2 b b.2)
  rw [hZ] at hmem
  exact congrArg Subtype.val (Subgroup.mem_bot.mp hmem)

theorem s16h_exists_mul_of_mem_of_aut_card [Finite 𝔾]
    {G A : Subgroup 𝔾}
    (hG : IsPGroup 2 G)
    (hGN : G ≤ Subgroup.normalizer (A : Set 𝔾))
    (hZ : A ⊓ Subgroup.centralizer (A : Set 𝔾) = ⊥)
    (hcardAut : Nat.card (MulAut ↥A) = 1512)
    (hcardS : Nat.card ↥(G ⊓ A) = 8) :
    ∀ x ∈ G, ∃ s ∈ G ⊓ A, ∃ c ∈ G ⊓ Subgroup.centralizer (A : Set 𝔾), x = s * c := by
  classical
  let f : ↥G →* MulAut ↥A :=
    (Subgroup.normalizerMonoidHom (H := A)).comp (Subgroup.inclusion hGN)
  have hker : f.ker = (G ⊓ Subgroup.centralizer (A : Set 𝔾)).subgroupOf G := by
    ext x
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, Subgroup.mem_inf]
    show (Subgroup.normalizerMonoidHom (H := A)) (Subgroup.inclusion hGN x) = 1 ↔
      (x : 𝔾) ∈ G ∧ (x : 𝔾) ∈ Subgroup.centralizer (A : Set 𝔾)
    have hx1 : ((Subgroup.inclusion hGN x : ↥(Subgroup.normalizer (A : Set 𝔾))) : 𝔾) =
        (x : 𝔾) := rfl
    constructor
    · intro hx
      refine ⟨x.2, ?_⟩
      have hx' : Subgroup.inclusion hGN x ∈ (Subgroup.normalizerMonoidHom (H := A)).ker :=
        MonoidHom.mem_ker.mpr hx
      rw [Subgroup.normalizerMonoidHom_ker, Subgroup.mem_subgroupOf] at hx'
      rwa [hx1] at hx'
    · rintro ⟨-, hx⟩
      have hx' : Subgroup.inclusion hGN x ∈
          (Subgroup.centralizer (A : Set 𝔾)).subgroupOf (Subgroup.normalizer (A : Set 𝔾)) := by
        rw [Subgroup.mem_subgroupOf, hx1]
        exact hx
      rw [← Subgroup.normalizerMonoidHom_ker, MonoidHom.mem_ker] at hx'
      exact hx'
  have hkerDisj : f.ker ⊓ (G ⊓ A).subgroupOf G = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    rw [Subgroup.mem_inf] at hx
    obtain ⟨hx1, hx2⟩ := hx
    rw [hker, Subgroup.mem_subgroupOf, Subgroup.mem_inf] at hx1
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_inf] at hx2
    rw [Subgroup.mem_bot]
    have hxZ : (x : 𝔾) ∈ A ⊓ Subgroup.centralizer (A : Set 𝔾) := ⟨hx2.2, hx1.2⟩
    rw [hZ, Subgroup.mem_bot] at hxZ
    exact Subtype.ext hxZ
  have hcardK : Nat.card ↥((G ⊓ A).subgroupOf G) = 8 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (inf_le_left : G ⊓ A ≤ G)).toEquiv, hcardS]
  have hcardMapK : Nat.card ↥(((G ⊓ A).subgroupOf G).map f) = 8 := by
    have hrel : f.ker.relIndex ((G ⊓ A).subgroupOf G) =
        Nat.card ↥(((G ⊓ A).subgroupOf G).map f) := Subgroup.relIndex_ker _ f
    have hmul := Subgroup.relIndex_mul_card f.ker ((G ⊓ A).subgroupOf G)
    rw [hkerDisj, Subgroup.card_bot, mul_one] at hmul
    rw [← hrel, hmul, hcardK]
  have hcardRange : Nat.card ↥f.range = 8 := by
    have hPgrp : IsPGroup 2 f.range := by
      rw [← Subgroup.map_top f]
      exact (hG.to_subgroup (⊤ : Subgroup ↥G)).map f
    obtain ⟨k, hk⟩ := hPgrp.exists_card_eq
    have hdvd : 2 ^ k ∣ 1512 := by
      rw [← hk, ← hcardAut]
      exact Subgroup.card_subgroup_dvd_card f.range
    have hdvd8 : 2 ^ k ∣ 8 := by
      rw [show (1512 : ℕ) = 8 * 189 from by norm_num] at hdvd
      exact (Nat.Coprime.pow_left k (by norm_num)).dvd_of_dvd_mul_right hdvd
    have hle1 : Nat.card ↥f.range ≤ 8 := by
      rw [hk]
      exact Nat.le_of_dvd (by norm_num) hdvd8
    have hle2 : 8 ≤ Nat.card ↥f.range := by
      have hle : ((G ⊓ A).subgroupOf G).map f ≤ (⊤ : Subgroup ↥G).map f :=
        Subgroup.map_mono le_top
      have hcard := Subgroup.card_le_of_le hle
      rw [Subgroup.map_top, hcardMapK] at hcard
      exact hcard
    omega
  have hmapEq : ((G ⊓ A).subgroupOf G).map f = (⊤ : Subgroup ↥G).map f := by
    have hle : ((G ⊓ A).subgroupOf G).map f ≤ (⊤ : Subgroup ↥G).map f :=
      Subgroup.map_mono le_top
    refine Subgroup.eq_of_le_of_card_ge hle ?_
    rw [Subgroup.map_top, hcardMapK, hcardRange]
  intro x hx
  have hx' : f ⟨x, hx⟩ ∈ ((G ⊓ A).subgroupOf G).map f := by
    rw [hmapEq]
    exact Subgroup.mem_map_of_mem f (Subgroup.mem_top _)
  obtain ⟨s, hs, hsf⟩ := Subgroup.mem_map.mp hx'
  refine ⟨(s : 𝔾), ?_, ((s⁻¹ * ⟨x, hx⟩ : ↥G) : 𝔾), ?_, ?_⟩
  · rw [Subgroup.mem_subgroupOf] at hs
    exact hs
  · refine ⟨(s⁻¹ * ⟨x, hx⟩).2, ?_⟩
    have hmem : s⁻¹ * ⟨x, hx⟩ ∈ f.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hsf, inv_mul_cancel]
    rw [hker, Subgroup.mem_subgroupOf] at hmem
    exact (Subgroup.mem_inf.mp hmem).2
  · have hgroup : (⟨x, hx⟩ : ↥G) = s * (s⁻¹ * ⟨x, hx⟩) := by group
    simpa using congrArg (fun y : ↥G => (y : 𝔾)) hgroup

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
