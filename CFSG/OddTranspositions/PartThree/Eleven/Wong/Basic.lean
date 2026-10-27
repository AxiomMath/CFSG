module

public import CFSG.OddTranspositions.PartThree.Eleven.Wong.Central
public import CFSG.GroupTheory.ABGLocalTools.Basic
public import CFSG.GroupTheory.ABGLocalTools.SylowNormalizerGrows
public import Mathlib.NumberTheory.Padics.PadicVal.Basic

public section

namespace CFSG.OddTranspositions.PartThree.Wong

open CFSG.ABGLocalTools

variable {G : Type} [Group G] [Finite G] {t : G} {L₁ L₂ : Subgroup G}

namespace WongHyp

private theorem map_conj_centralizer_singleton_aux {X : Type*} [Group X] (g t : X) :
    (Subgroup.centralizer ({t} : Set X)).map (MulAut.conj g) =
      Subgroup.centralizer ({g * t * g⁻¹} : Set X) := by
  apply le_antisymm
  · intro x hx
    obtain ⟨y, hy, rfl⟩ := hx
    change (g * y * g⁻¹) ∈ Subgroup.centralizer ({g * t * g⁻¹} : Set X)
    have hy' : y * t = t * y := Subgroup.mem_centralizer_singleton_iff.mp hy
    exact Subgroup.mem_centralizer_singleton_iff.mpr (by
      calc g * y * g⁻¹ * (g * t * g⁻¹) = g * (y * t) * g⁻¹ := by group
        _ = g * (t * y) * g⁻¹ := by rw [hy']
        _ = (g * t * g⁻¹) * (g * y * g⁻¹) := by group)
  · intro x hx
    have hx' : x * (g * t * g⁻¹) = (g * t * g⁻¹) * x :=
      Subgroup.mem_centralizer_singleton_iff.mp hx
    refine ⟨g⁻¹ * x * g, ?_, ?_⟩
    · change (g⁻¹ * x * g) ∈ Subgroup.centralizer ({t} : Set X)
      exact Subgroup.mem_centralizer_singleton_iff.mpr (by
        calc g⁻¹ * x * g * t = g⁻¹ * (x * (g * t * g⁻¹)) * g := by group
          _ = g⁻¹ * ((g * t * g⁻¹) * x) * g := by rw [hx']
          _ = t * (g⁻¹ * x * g) := by group)
    · change g * (g⁻¹ * x * g) * g⁻¹ = x
      group

private theorem two_pow_factorization_14400 : 2 ^ (14400 : ℕ).factorization 2 = 64 := by
  rw [Nat.factorization_def 14400 Nat.prime_two]
  have h1 : (14400 : ℕ) = 2 ^ 6 * 225 := by norm_num
  rw [h1, padicValNat.mul (by norm_num) (by norm_num), padicValNat.prime_pow,
    padicValNat.eq_zero_of_not_dvd (by norm_num : ¬ (2 : ℕ) ∣ 225)]
  norm_num

theorem centralizer_le_normalizer_sup (h : WongHyp t L₁ L₂) :
    Subgroup.centralizer ({t} : Set G) ≤ Subgroup.normalizer ((L₁ ⊔ L₂ : Subgroup G) : Set G) := by
  have hK : L₁ ⊔ L₂ ≤ Subgroup.centralizer ({t} : Set G) := sup_le_centralizer h
  haveI : ((L₁ ⊔ L₂).subgroupOf (Subgroup.centralizer ({t} : Set G))).Normal :=
    Subgroup.normal_of_index_eq_two h.relIndex_eq
  exact Subgroup.le_normalizer_of_normal_subgroupOf (H := L₁ ⊔ L₂)
    (K := Subgroup.centralizer ({t} : Set G)) hK

theorem sup_zpowers_eq_centralizer (h : WongHyp t L₁ L₂) {n : G}
    (hn : n ∈ Subgroup.centralizer ({t} : Set G)) (hnK : n ∉ L₁ ⊔ L₂) :
    L₁ ⊔ L₂ ⊔ Subgroup.zpowers n = Subgroup.centralizer ({t} : Set G) := by
  have hKleC : L₁ ⊔ L₂ ≤ Subgroup.centralizer ({t} : Set G) := sup_le_centralizer h
  have hHC : L₁ ⊔ L₂ ⊔ Subgroup.zpowers n ≤ Subgroup.centralizer ({t} : Set G) :=
    sup_le hKleC (Subgroup.zpowers_le.mpr hn)
  have hKH : L₁ ⊔ L₂ ≤ L₁ ⊔ L₂ ⊔ Subgroup.zpowers n := le_sup_left
  have hnH : n ∈ L₁ ⊔ L₂ ⊔ Subgroup.zpowers n :=
    Subgroup.mem_sup_right (Subgroup.mem_zpowers n)
  have hnotle : ¬ (L₁ ⊔ L₂ ⊔ Subgroup.zpowers n ≤ L₁ ⊔ L₂) := fun hle => hnK (hle hnH)
  have hprod := Subgroup.relIndex_mul_relIndex (L₁ ⊔ L₂)
    (L₁ ⊔ L₂ ⊔ Subgroup.zpowers n) (Subgroup.centralizer ({t} : Set G)) hKH hHC
  have hdvd : (L₁ ⊔ L₂).relIndex (L₁ ⊔ L₂ ⊔ Subgroup.zpowers n) ∣ 2 := by
    refine ⟨(L₁ ⊔ L₂ ⊔ Subgroup.zpowers n).relIndex (Subgroup.centralizer ({t} : Set G)), ?_⟩
    rw [hprod, h.relIndex_eq]
  have hne : (L₁ ⊔ L₂).relIndex (L₁ ⊔ L₂ ⊔ Subgroup.zpowers n) ≠ 1 := by
    intro h1
    exact hnotle (Subgroup.relIndex_eq_one.mp h1)
  have ha : (L₁ ⊔ L₂).relIndex (L₁ ⊔ L₂ ⊔ Subgroup.zpowers n) = 2 := by
    rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h1 | h2
    · exact absurd h1 hne
    · exact h2
  have hrel1 :
      (L₁ ⊔ L₂ ⊔ Subgroup.zpowers n).relIndex (Subgroup.centralizer ({t} : Set G)) = 1 := by
    have := hprod
    rw [ha, h.relIndex_eq] at this
    omega
  have hCH : Subgroup.centralizer ({t} : Set G) ≤ L₁ ⊔ L₂ ⊔ Subgroup.zpowers n :=
    Subgroup.relIndex_eq_one.mp hrel1
  exact le_antisymm hHC hCH

theorem mul_mem_sup_of_not_mem (h : WongHyp t L₁ L₂) {g k : G}
    (hg : g ∈ Subgroup.centralizer ({t} : Set G)) (hk : k ∈ Subgroup.centralizer ({t} : Set G))
    (hgK : g ∉ L₁ ⊔ L₂) (hkK : k ∉ L₁ ⊔ L₂) : g * k ∈ L₁ ⊔ L₂ := by
  have hmem := Subgroup.mul_mem_iff_of_index_two
    (H := (L₁ ⊔ L₂).subgroupOf (Subgroup.centralizer ({t} : Set G)))
    (show ((L₁ ⊔ L₂).subgroupOf (Subgroup.centralizer ({t} : Set G))).index = 2 from
      h.relIndex_eq)
    (a := (⟨g, hg⟩ : Subgroup.centralizer ({t} : Set G)))
    (b := (⟨k, hk⟩ : Subgroup.centralizer ({t} : Set G)))
  have hgN : (⟨g, hg⟩ : Subgroup.centralizer ({t} : Set G)) ∉
      (L₁ ⊔ L₂).subgroupOf (Subgroup.centralizer ({t} : Set G)) := by
    simpa only [Subgroup.mem_subgroupOf] using hgK
  have hkN : (⟨k, hk⟩ : Subgroup.centralizer ({t} : Set G)) ∉
      (L₁ ⊔ L₂).subgroupOf (Subgroup.centralizer ({t} : Set G)) := by
    simpa only [Subgroup.mem_subgroupOf] using hkK
  have hprod : ((⟨g, hg⟩ : Subgroup.centralizer ({t} : Set G)) *
      (⟨k, hk⟩ : Subgroup.centralizer ({t} : Set G))) ∈
      (L₁ ⊔ L₂).subgroupOf (Subgroup.centralizer ({t} : Set G)) := by
    rw [hmem]
    exact ⟨fun hh => absurd hh hgN, fun hh => absurd hh hkN⟩
  simpa only [Subgroup.mem_subgroupOf, Subgroup.coe_mul] using hprod

theorem sq_mem_sup (h : WongHyp t L₁ L₂) {g : G} (hg : g ∈ Subgroup.centralizer ({t} : Set G)) :
    g ^ 2 ∈ L₁ ⊔ L₂ := by
  by_cases hgK : g ∈ L₁ ⊔ L₂
  · exact pow_mem hgK 2
  · rw [pow_two]
    exact mul_mem_sup_of_not_mem h hg hg hgK hgK

theorem card_eq_sixtyFour_of_isSylowOf (h : WongHyp t L₁ L₂) {v : G} (hv : IsConj t v)
    {U : Subgroup G}
    (hU : IsSylowOf 2 U (Subgroup.centralizer ({t} : Set G) ⊓ Subgroup.centralizer ({v} : Set G)))
    (hN : Subgroup.normalizer (U : Set G) ⊓ Subgroup.centralizer ({v} : Set G) ≤
      Subgroup.centralizer ({t} : Set G)) :
    Nat.card U = 64 := by
  have hU' : IsSylowOf 2 U (Subgroup.centralizer ({v} : Set G)) :=
    isSylowOf_of_normalizer_inf_le (H := Subgroup.centralizer ({t} : Set G))
      (M := Subgroup.centralizer ({v} : Set G)) hU hN
  rw [IsSylowOf.card_eq hU']
  have hcardv : Nat.card (Subgroup.centralizer ({v} : Set G)) =
      Nat.card (Subgroup.centralizer ({t} : Set G)) := by
    obtain ⟨c, hc⟩ := isConj_iff.mp hv
    rw [← hc, ← map_conj_centralizer_singleton_aux c t,
      Subgroup.card_map_of_injective (MulAut.conj c).injective]
  rw [hcardv, card_centralizer h, two_pow_factorization_14400]

theorem isSylowOf_top_of_normalizer_le (h : WongHyp t L₁ L₂) {U : Subgroup G}
    (hU : IsSylowOf 2 U (Subgroup.centralizer ({t} : Set G)))
    (hN : Subgroup.normalizer (U : Set G) ≤ Subgroup.centralizer ({t} : Set G)) :
    IsSylowOf 2 U ⊤ ∧ Nat.card U = 64 := by
  have hUt : IsSylowOf 2 U ⊤ :=
    isSylowOf_of_normalizer_inf_le (H := Subgroup.centralizer ({t} : Set G)) (M := ⊤)
      (by simpa using hU) (by simpa using hN)
  refine ⟨hUt, ?_⟩
  rw [IsSylowOf.card_eq hU, card_centralizer h, two_pow_factorization_14400]

end WongHyp

end CFSG.OddTranspositions.PartThree.Wong
