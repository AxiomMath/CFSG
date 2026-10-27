module

public import CFSG.LocalAnalysis.StandardType.GGTorusMaxSemiLift
public import CFSG.Open.LocalVocabulary
public import Mathlib.GroupTheory.Commutator.Basic
public import Mathlib.GroupTheory.Perm.Basic

import CFSG.LocalAnalysis.StandardType.GGTorusMaxSemiCore
import CFSG.GroupTheory.Frattini.PSubgroupLift
import CFSG.GroupTheory.WielandtProductAux

public section

namespace CFSG.StandardType.FrameRoute

open CFSG.Open

private theorem pow_three_le_normal_of_index_le_two {M : Type} [Group M] [Finite M]
    (E M0 : Subgroup M) [M0.Normal] (k : ℕ) (hE : Nat.card E = 3 ^ (k + 1))
    (hM0 : M0.index ≤ 2) : E ≤ M0 := by
  apply CFSG.GroupTheory.WielandtProduct.le_of_coprime_index (K := M0) (H := E)
  rw [hE]
  have hpos : 0 < M0.index :=
    Nat.pos_of_ne_zero (Subgroup.index_ne_zero_of_finite (H := M0))
  rcases (by omega : M0.index = 1 ∨ M0.index = 2) with h1 | h2
  · rw [h1]; simp
  · rw [h2]
    exact Nat.Coprime.pow_left _ (by norm_num)

private theorem commutative_subgroupOf {G : Type} [Group G] {N E : Subgroup G} (hEN : E ≤ N)
    (hE : ∀ a b : E, a * b = b * a) :
    ∀ a b : E.subgroupOf N, a * b = b * a := by
  intro a b
  exact (Subgroup.subgroupOfEquivOfLe hEN).injective (by
    rw [map_mul, map_mul, hE _ _])

private theorem exponent_three_subgroupOf {G : Type} [Group G] {N E : Subgroup G}
    (hE : ∀ x : E, (x : G) ^ 3 = 1) :
    ∀ x : E.subgroupOf N, (x : N) ^ 3 = 1 := by
  intro x
  have h := hE ⟨((x : N) : G), x.2⟩
  apply Subtype.ext
  simpa using h

private theorem eq_bot_or_eq_comap_of_irreducible {G M : Type} [Group G] [Group M]
    (N E : Subgroup G) (hEN : E ≤ N) (p : M →* N) (hp : Function.Surjective p)
    (hirr : ∀ F : Subgroup G, F ≤ E →
      (∀ g ∈ N, ∀ f ∈ F, g * f * g⁻¹ ∈ F) → F = ⊥ ∨ F = E)
    (N' : Subgroup M) (hZN' : p.ker ≤ N')
    (hN'E : N' ≤ (E.subgroupOf N).comap p) (hN'normal : N'.Normal) :
    N' = p.ker ∨ N' = (E.subgroupOf N).comap p := by
  classical
  let N'X : Subgroup N := N'.map p
  have hN'X_normal : N'X.Normal := hN'normal.map p hp
  let N'' : Subgroup G := N'X.map N.subtype
  have hN''_le_E : N'' ≤ E := by
    intro f hf
    obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp hf
    obtain ⟨n, hn, hpn⟩ := Subgroup.mem_map.mp hx
    have hxE : x ∈ E.subgroupOf N := by
      rw [← hpn]
      exact hN'E hn
    exact hxE
  have hN''_norm : ∀ g ∈ N, ∀ f ∈ N'', g * f * g⁻¹ ∈ N'' := by
    intro g hg f hf
    obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp hf
    have hconj : (⟨g, hg⟩ : N) * x * (⟨g, hg⟩ : N)⁻¹ ∈ N'X :=
      hN'X_normal.conj_mem x hx ⟨g, hg⟩
    exact Subgroup.mem_map.mpr ⟨_, hconj, rfl⟩
  rcases hirr N'' hN''_le_E hN''_norm with hbot | htop
  · left
    have hN'X_bot : N'X = ⊥ :=
      (Subgroup.map_eq_bot_iff_of_injective (H := N'X) N.subtype_injective).mp hbot
    apply le_antisymm _ hZN'
    intro n hn
    apply MonoidHom.mem_ker.mpr
    have hpn : p n ∈ N'X := Subgroup.mem_map_of_mem p hn
    rw [hN'X_bot] at hpn
    exact Subgroup.mem_bot.mp hpn
  · right
    have hN'X_eq : N'X = E.subgroupOf N := by
      apply Subgroup.map_injective N.subtype_injective
      change N'' = (E.subgroupOf N).map N.subtype
      rw [show N'' = E from htop]
      exact (Subgroup.map_subgroupOf_eq_of_le hEN).symm
    calc N' = (N'.map p).comap p := (Subgroup.comap_map_eq_self hZN').symm
      _ = (E.subgroupOf N).comap p := by
        rw [show N'.map p = N'X from rfl, hN'X_eq]

private theorem mem_comap_of_centralizes_mod_ker {G M : Type} [Group G] [Group M]
    (N E : Subgroup G) (hEN : E ≤ N) (p : M →* N) (hp : Function.Surjective p)
    (hcent : ∀ g ∈ N, (∀ e ∈ E, g * e = e * g) → g ∈ E)
    (x : M) (hx : ∀ e ∈ (E.subgroupOf N).comap p, x * e * x⁻¹ * e⁻¹ ∈ p.ker) :
    x ∈ (E.subgroupOf N).comap p := by
  have hxcent : ∀ e ∈ E, ((p x : N) : G) * e = e * ((p x : N) : G) := by
    intro e he
    have heN : e ∈ N := hEN he
    obtain ⟨m, hm⟩ := hp ⟨e, heN⟩
    have hmE : m ∈ (E.subgroupOf N).comap p := by
      change p m ∈ E.subgroupOf N
      rw [hm]
      exact he
    have h1 : p (x * m * x⁻¹ * m⁻¹) = 1 := MonoidHom.mem_ker.mp (hx m hmE)
    have h2 : (p x) * (p m) * (p x)⁻¹ * (p m)⁻¹ = 1 := by
      simpa [map_mul] using h1
    rw [hm] at h2
    have h3 : ((p x : N) : G) * e * ((p x : N) : G)⁻¹ * e⁻¹ = 1 := by
      have := congrArg (fun y : N => (y : G)) h2
      simpa using this
    calc ((p x : N) : G) * e =
        (((p x : N) : G) * e * ((p x : N) : G)⁻¹ * e⁻¹) * e *
          ((p x : N) : G) := by group
      _ = 1 * e * ((p x : N) : G) := by rw [h3]
      _ = e * ((p x : N) : G) := by group
  change p x ∈ E.subgroupOf N
  exact hcent ((p x : N) : G) (p x).2 hxcent

private theorem commutator_mem_ker_of_commutative {M N : Type} [Group M] [Group N]
    (p : M →* N) (E : Subgroup N) (hE : ∀ a b : E, a * b = b * a)
    {a b : M} (ha : p a ∈ E) (hb : p b ∈ E) : a * b * a⁻¹ * b⁻¹ ∈ p.ker := by
  apply MonoidHom.mem_ker.mpr
  have hcommN : (p a) * (p b) = (p b) * (p a) := by
    have h := congrArg (fun x : E => (x : N)) (hE ⟨p a, ha⟩ ⟨p b, hb⟩)
    simpa using h
  simp only [map_mul, map_inv]
  rw [hcommN]
  group

private theorem cube_mem_ker_of_exponent_three {M N : Type} [Group M] [Group N]
    (p : M →* N) (E : Subgroup N) (hE : ∀ x : E, (x : N) ^ 3 = 1)
    {a : M} (ha : p a ∈ E) : a ^ 3 ∈ p.ker := by
  apply MonoidHom.mem_ker.mpr
  have hpow : (p a) ^ 3 = 1 := by
    have h := hE ⟨p a, ha⟩
    simpa using h
  simpa [map_pow] using hpow

private theorem commute_of_mem_ker_of_scalar_representation {M : Type} [Group M]
    {d : ℕ} {K : Type} [Field K] (M0 : Subgroup M) (ρ : ↥M0 →* GL (Fin d) K)
    (hρ : Function.Injective ρ) (Z E : Subgroup M) (hZE : Z ≤ E) (hEM0 : E ≤ M0)
    (hρZ : ∀ z : ↥M0, (z : M) ∈ Z → ∃ c : K,
      ((ρ z : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) = Matrix.scalar (Fin d) c) :
    ∀ z ∈ Z, ∀ a ∈ E, z * a = a * z := by
  intro z hz a ha
  let zM0 : ↥M0 := ⟨z, hEM0 (hZE hz)⟩
  let aM0 : ↥M0 := ⟨a, hEM0 ha⟩
  obtain ⟨c, hc⟩ := hρZ zM0 (by simpa [zM0] using hz)
  have hcentral : ρ zM0 * ρ aM0 = ρ aM0 * ρ zM0 := by
    apply Units.ext
    simp only [Units.val_mul]
    rw [hc]
    exact Matrix.scalar_comm c (fun r' => Commute.all c r')
      ((ρ aM0 : GL (Fin d) K) : Matrix (Fin d) (Fin d) K)
  have heq : zM0 * aM0 = aM0 * zM0 := hρ (by rw [map_mul, map_mul, hcentral])
  simpa [zM0, aM0] using congrArg (fun x : ↥M0 => (x : M)) heq

theorem tmSemi_transfer {G : Type} [Group G] [Finite G] (d m : ℕ) (hd : 4 ≤ d)
    (hdm : m % 2 = 1 ∨ d < 3 ^ (m / 2))
    {W : Type} [Group W] (hW1 : commutator W ≠ ⊥)
    (hW2 : ∀ n ≤ d, ∀ f : ↥(commutator W) →* Equiv.Perm (Fin n), f = 1)
    (E : Subgroup G) (hE : IsElemAbelian 3 E) (hcard : Nat.card E = 3 ^ m)
    (π : ↥(Subgroup.normalizer (E : Set G)) →* W) (hπs : Function.Surjective π)
    (hπk : π.ker = E.subgroupOf (Subgroup.normalizer (E : Set G)))
    (hcent : ∀ g ∈ Subgroup.normalizer (E : Set G), (∀ e ∈ E, g * e = e * g) → g ∈ E)
    (hirr : ∀ F : Subgroup G, F ≤ E →
      (∀ g ∈ Subgroup.normalizer (E : Set G), ∀ f ∈ F, g * f * g⁻¹ ∈ F) → F = ⊥ ∨ F = E)
    (K : Type) [Field K] [Finite K] [CharP K 2] (hK : Nat.card K = 4)
    (ψ : ↥(Subgroup.normalizer (E : Set G)) →* MulAut (StatedProj (StatedSU d (2 ^ 1) K)))
    (hψ : Function.Injective ψ) : False := by
  classical
  let N : Subgroup G := Subgroup.normalizer (E : Set G)
  have hE_le_N : E ≤ N := Subgroup.le_normalizer
  obtain ⟨M, hMgrp, hMfin, p, M0, ρ, hp_surj, hker_card, hM0_normal, hM0_index,
    hρ_inj, hρ_scalar⟩ :=
    exists_semilinearLift (X := ↥N) hK d hd ψ hψ
  letI : Group M := hMgrp
  letI : Finite M := hMfin
  haveI hEsubN : (E.subgroupOf N).Normal :=
    Subgroup.normal_subgroupOf_of_le_normalizer (H := N) (N := E) le_rfl
  let Z : Subgroup M := p.ker
  let Etilde : Subgroup M := (E.subgroupOf N).comap p
  haveI hEtildeNormal : Etilde.Normal := inferInstanceAs ((E.subgroupOf N).comap p).Normal
  have hZ_card : Nat.card Z = 3 := hker_card
  have hZE : Z ≤ Etilde := by
    intro z hz
    change p z ∈ E.subgroupOf N
    rw [MonoidHom.mem_ker.mp hz]
    exact (E.subgroupOf N).one_mem
  have hEtilde_card : Nat.card Etilde = 3 ^ (m + 1) := by
    rw [show Etilde = (E.subgroupOf N).comap p from rfl,
      CFSG.GroupTheory.card_comap_eq_card_ker_mul_card p hp_surj (E.subgroupOf N)]
    have hsub : Nat.card (E.subgroupOf N) = Nat.card E :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hE_le_N).toEquiv
    rw [show p.ker = Z from rfl, hZ_card, hsub, hcard, pow_succ]
    ring
  have hEtilde_le_M0 : Etilde ≤ M0 :=
    pow_three_le_normal_of_index_le_two Etilde M0 m hEtilde_card hM0_index
  have hE_comm : ∀ a b : E, a * b = b * a := isMulCommutative_iff.mp hE.1
  have hE_exp : ∀ x : E, (x : G) ^ 3 = 1 := fun x => hE.2 (x : G) x.2
  have hZc_core : ∀ z ∈ Z, ∀ a ∈ Etilde, z * a = a * z :=
    commute_of_mem_ker_of_scalar_representation M0 ρ hρ_inj Z Etilde hZE hEtilde_le_M0 hρ_scalar
  have hcomm_core : ∀ a ∈ Etilde, ∀ b ∈ Etilde, a * b * a⁻¹ * b⁻¹ ∈ Z :=
    fun a ha b hb => commutator_mem_ker_of_commutative p (E.subgroupOf N)
      (commutative_subgroupOf hE_le_N hE_comm) ha hb
  have hexp_core : ∀ a ∈ Etilde, a ^ 3 ∈ Z :=
    fun a ha => cube_mem_ker_of_exponent_three p (E.subgroupOf N)
      (exponent_three_subgroupOf hE_exp) ha
  have hirr_core : ∀ N' : Subgroup M, Z ≤ N' → N' ≤ Etilde → N'.Normal →
      N' = Z ∨ N' = Etilde :=
    eq_bot_or_eq_comap_of_irreducible N E hE_le_N p hp_surj hirr
  have hcent_core : ∀ x : M, (∀ e ∈ Etilde, x * e * x⁻¹ * e⁻¹ ∈ Z) → x ∈ Etilde :=
    mem_comap_of_centralizes_mod_ker N E hE_le_N p hp_surj hcent
  let π' : M →* W := π.comp p
  have hπs' : Function.Surjective π' := hπs.comp hp_surj
  have hπk' : π'.ker = Etilde := by
    rw [show π' = π.comp p from rfl, ← MonoidHom.comap_ker π p, hπk]
  exact tmSemi_core (F := K) d m hdm hW1 hW2 Z Etilde M0 hZE hEtilde_le_M0 hM0_index
    hZ_card hEtilde_card hZc_core hcomm_core hexp_core hirr_core hcent_core π' hπs' hπk'
    ρ hρ_inj (fun z hz => hρ_scalar z (MonoidHom.mem_ker.mp hz))

end CFSG.StandardType.FrameRoute
