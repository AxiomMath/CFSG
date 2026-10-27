module

import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.ComplementConjugacy
public import Mathlib.Data.Nat.Totient
public import Mathlib.Data.Rat.Floor
public import Mathlib.Data.Sym.Sym2.Init
public import Mathlib.Tactic.NormNum.GCD

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.KOm

open scoped Pointwise

private lemma conj_mem_of_map_subgroupOf_eq {G : Type*} [Group G] {X B B' : Subgroup G}
    {n : ↥X} (hB'X : B' ≤ X)
    (h : B.subgroupOf X = (B'.subgroupOf X).map (MulAut.conj n).toMonoidHom)
    {b' : G} (hb' : b' ∈ B') : (n : G) * b' * (n : G)⁻¹ ∈ B := by
  have hsub : (⟨b', hB'X hb'⟩ : ↥X) ∈ B'.subgroupOf X := Subgroup.mem_subgroupOf.mpr hb'
  have hmem : (MulAut.conj n) (⟨b', hB'X hb'⟩ : ↥X) ∈ B.subgroupOf X := by
    rw [h]
    exact Subgroup.mem_map_of_mem _ hsub
  simpa [MulAut.conj_apply] using Subgroup.mem_subgroupOf.mp hmem

private lemma conj_eq_pow_of_conj_mem {G : Type*} [Group G] {U B : Subgroup G}
    (hinf : U ⊓ B = ⊥) (hBU : B ≤ Subgroup.normalizer (U : Set G))
    {t₀ n : G} {q : ℕ} (hnU : n ∈ U)
    (hconj : ∀ g ∈ B, t₀ * g * t₀⁻¹ * (g ^ q)⁻¹ ∈ U)
    (hnB : ∀ g ∈ B, n * (t₀ * g * t₀⁻¹) * n⁻¹ ∈ B) :
    ∀ g ∈ B, n * t₀ * g * (n * t₀)⁻¹ = g ^ q := by
  intro g hg
  have hgqB : g ^ q ∈ B := pow_mem hg q
  have hA : t₀ * g * t₀⁻¹ * (g ^ q)⁻¹ ∈ U := hconj g hg
  have hconjn : g ^ q * n⁻¹ * (g ^ q)⁻¹ ∈ U :=
    (Subgroup.mem_normalizer_iff.mp (hBU hgqB) n⁻¹).mp (U.inv_mem hnU)
  have hU : n * t₀ * g * (n * t₀)⁻¹ * (g ^ q)⁻¹ ∈ U := by
    have heq : n * t₀ * g * (n * t₀)⁻¹ * (g ^ q)⁻¹ =
        n * (t₀ * g * t₀⁻¹ * (g ^ q)⁻¹) * (g ^ q * n⁻¹ * (g ^ q)⁻¹) := by group
    rw [heq]
    exact U.mul_mem (U.mul_mem hnU hA) hconjn
  have hB : n * t₀ * g * (n * t₀)⁻¹ * (g ^ q)⁻¹ ∈ B := by
    have heq : n * t₀ * g * (n * t₀)⁻¹ = n * (t₀ * g * t₀⁻¹) * n⁻¹ := by group
    rw [heq]
    exact B.mul_mem (hnB g hg) (B.inv_mem hgqB)
  have hmem : n * t₀ * g * (n * t₀)⁻¹ * (g ^ q)⁻¹ ∈ U ⊓ B := ⟨hU, hB⟩
  rw [hinf] at hmem
  exact mul_inv_eq_one.mp (Subgroup.mem_bot.mp hmem)

theorem exists_mem_conj_eq_pow {G : Type*} [Group G] [Finite G] {U B : Subgroup G}
    (hcop : Nat.Coprime (Nat.card ↥U) (Nat.card ↥B))
    (hBU : B ≤ Subgroup.normalizer (U : Set G)) {t₀ : G} {q : ℕ}
    (hconj : ∀ g ∈ B, t₀ * g * t₀⁻¹ * (g ^ q)⁻¹ ∈ U) :
    ∃ n ∈ U, ∀ g ∈ B, n * t₀ * g * (n * t₀)⁻¹ = g ^ q := by
  classical
  set X : Subgroup G := U ⊔ B with hXdef
  let B' : Subgroup G := B.map (MulAut.conj t₀).toMonoidHom
  have hUX : U ≤ X := by rw [hXdef]; exact le_sup_left
  have hBX : B ≤ X := by rw [hXdef]; exact le_sup_right
  have hinfUB : U ⊓ B = ⊥ := Subgroup.inf_eq_bot_of_coprime hcop
  have hB'X : B' ≤ X := by
    rintro x hx
    obtain ⟨g, hg, rfl⟩ := Subgroup.mem_map.mp hx
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    have h1 : t₀ * g * t₀⁻¹ = (t₀ * g * t₀⁻¹ * (g ^ q)⁻¹) * g ^ q := by group
    rw [h1]
    exact X.mul_mem (hUX (hconj g hg)) (hBX (pow_mem hg q))
  have hXnorm : X ≤ Subgroup.normalizer (U : Set G) := by
    rw [hXdef]
    exact sup_le Subgroup.le_normalizer hBU
  have hNnormal : (U.subgroupOf X).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hUX).mpr hXnorm
  have hcardN : Nat.card ↥(U.subgroupOf X) = Nat.card ↥U :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hUX).toEquiv
  have hcardK : Nat.card ↥(B.subgroupOf X) = Nat.card ↥B :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hBX).toEquiv
  have hcardB' : Nat.card ↥B' = Nat.card ↥B :=
    Subgroup.card_map_of_injective (MulAut.conj t₀).injective
  have hcardH : Nat.card ↥(B'.subgroupOf X) = Nat.card ↥B := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hB'X).toEquiv, hcardB']
  have hdisj : Disjoint (U.subgroupOf X) (B.subgroupOf X) := by
    rw [disjoint_iff]
    refine le_antisymm ?_ bot_le
    rintro x ⟨hxU, hxB⟩
    have hxU' : ((x : ↥X) : G) ∈ U := Subgroup.mem_subgroupOf.mp hxU
    have hxB' : ((x : ↥X) : G) ∈ B := Subgroup.mem_subgroupOf.mp hxB
    have hmem : ((x : ↥X) : G) ∈ (⊥ : Subgroup G) := by
      rw [← hinfUB]
      exact ⟨hxU', hxB'⟩
    exact Subgroup.mem_bot.mpr (Subtype.ext (by simpa using Subgroup.mem_bot.mp hmem))
  have hsup : U.subgroupOf X ⊔ B.subgroupOf X = ⊤ := by
    rw [← Subgroup.subgroupOf_sup hUX hBX, ← hXdef]
    ext x
    simp
  have hmul : ((U.subgroupOf X : Set ↥X) * (B.subgroupOf X : Set ↥X)) = Set.univ := by
    haveI : (U.subgroupOf X).Normal := hNnormal
    rw [← Subgroup.normal_mul (U.subgroupOf X) (B.subgroupOf X), hsup]
    rfl
  have hcompK : (U.subgroupOf X).IsComplement' (B.subgroupOf X) :=
    Subgroup.isComplement'_of_disjoint_and_mul_eq_univ hdisj hmul
  have hcardX : Nat.card ↥U * Nat.card ↥B = Nat.card ↥X := by
    rw [← hcardN, ← hcardK]
    exact hcompK.card_mul_card
  have hcompH : (U.subgroupOf X).IsComplement' (B'.subgroupOf X) :=
    Subgroup.isComplement'_of_coprime (by rw [hcardN, hcardH]; exact hcardX)
      (by rw [hcardN, hcardH]; exact hcop)
  have hidx : (U.subgroupOf X).index = Nat.card ↥B := by
    have h1 := Subgroup.card_mul_index (H := U.subgroupOf X)
    rw [hcardN, ← hcardX] at h1
    exact Nat.eq_of_mul_eq_mul_left Nat.card_pos h1
  have hcop' : Nat.Coprime (Nat.card ↥(U.subgroupOf X)) (U.subgroupOf X).index := by
    rw [hcardN, hidx]
    exact hcop
  obtain ⟨n₀, hn₀⟩ :=
    CFSG.GorensteinWalter.SchurZassenhaus.exists_mem_normal_conjugator_of_coprime
      (U.subgroupOf X) (B'.subgroupOf X) (B.subgroupOf X) hNnormal hcompH hcompK hcop'
  set n : G := ((n₀ : ↥X) : G) with hn
  have hmemU : n ∈ U := by
    rw [hn]
    exact Subgroup.mem_subgroupOf.mp n₀.2
  have hnB : ∀ g ∈ B, n * (t₀ * g * t₀⁻¹) * n⁻¹ ∈ B := by
    intro g hg
    rw [hn]
    exact conj_mem_of_map_subgroupOf_eq hB'X hn₀ (Subgroup.mem_map_of_mem _ hg)
  exact ⟨n, hmemU, conj_eq_pow_of_conj_mem hinfUB hBU hmemU hconj hnB⟩

end CFSG.LocalAnalysis.UniquenessCase.UC22.KOm

end
