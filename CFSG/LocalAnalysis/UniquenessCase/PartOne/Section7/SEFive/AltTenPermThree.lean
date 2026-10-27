module

public import Mathlib.GroupTheory.SpecificGroups.Alternating
import CFSG.GH74.GLS.IVK.Proofs2.GHInvAltBasic
import CFSG.LocalAnalysis.AGLEmbedding.AltBetaGen
import CFSG.LocalAnalysis.ComponentClassification.GSThmBCatalog82A10Perm

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7.SEFive.AltTen

open Equiv Equiv.Perm

private theorem mem_altOn_of_isCycle_support_three {B : Finset (Fin 10)} {c : Perm (Fin 10)}
    (hc : c.IsCycle) (hcard : c.support.card = 3) (hsub : c.support ⊆ B) :
    c ∈ CFSG.GH74.GLS.IVK.GHInv.altOn B := by
  refine CFSG.GH74.GLS.IVK.GHInv.mem_altOn.2 ⟨?_, ?_⟩
  · intro x hx
    exact Equiv.Perm.notMem_support.mp fun h => hx (hsub h)
  · rw [hc.sign, hcard]
    decide

private theorem not_swaps_of_coprime_three {B : Finset (Fin 10)} (hB : B.card = 5)
    {Q : Subgroup (alternatingGroup (Fin 10))} (hQ : Nat.Coprime (Nat.card Q) 3)
    (hnorm : ∀ g : alternatingGroup (Fin 10), ((∀ i ∉ B, (g : Perm (Fin 10)) i = i) ∨
      ∀ i ∈ B, (g : Perm (Fin 10)) i = i) → ∀ σ ∈ Q, g * σ * g⁻¹ ∈ Q)
    {σ : alternatingGroup (Fin 10)} (hσ : σ ∈ Q)
    (hswap : ∀ i ∈ B, (σ : Perm (Fin 10)) i ∉ B) : False := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨S, hSB, hScard⟩ := Finset.exists_subset_card_eq (s := B) (n := 3) (by omega)
  obtain ⟨c, hccycle, hcsupp⟩ :=
    CFSG.AGLEmbedding.exists_isCycle_support_eq (s := S) (by omega)
  have hcsuppB : c.support ⊆ B := hcsupp ▸ hSB
  have hcA : c ∈ alternatingGroup (Fin 10) := by
    rw [Equiv.Perm.mem_alternatingGroup, hccycle.sign, hcsupp, hScard]
    decide
  let ca : alternatingGroup (Fin 10) := ⟨c, hcA⟩
  have hcfix : ∀ i ∉ B, (ca : Perm (Fin 10)) i = i := by
    intro i hi
    exact Equiv.Perm.notMem_support.mp fun h => hi (hcsuppB h)
  have hcQ : ca * σ * ca⁻¹ ∈ Q := hnorm ca (Or.inl hcfix) σ hσ
  let x : alternatingGroup (Fin 10) := ca * σ * ca⁻¹ * σ⁻¹
  have hxQ : x ∈ Q := Subgroup.mul_mem Q hcQ (Subgroup.inv_mem Q hσ)
  let d : Perm (Fin 10) := (σ : Perm (Fin 10)) * c⁻¹ * (σ : Perm (Fin 10))⁻¹
  have hxval : (x : Perm (Fin 10)) = c * d := by
    simp only [x, ca, d, Subgroup.coe_mul, Subgroup.coe_inv, mul_assoc]
  have hd_fixB : ∀ i ∈ B, d i = i := by
    intro i hi
    have hne : (σ : Perm (Fin 10))⁻¹ i ∉ B := by
      intro hmem
      exact (hswap _ hmem) (by simpa using hi)
    have hfix : c⁻¹ ((σ : Perm (Fin 10))⁻¹ i) = (σ : Perm (Fin 10))⁻¹ i :=
      Equiv.Perm.notMem_support.mp (by
        rw [Equiv.Perm.support_inv]
        exact fun h => hne (hcsuppB h))
    calc ((σ : Perm (Fin 10)) * c⁻¹ * (σ : Perm (Fin 10))⁻¹) i
        = (σ : Perm (Fin 10)) (c⁻¹ ((σ : Perm (Fin 10))⁻¹ i)) := rfl
      _ = (σ : Perm (Fin 10)) ((σ : Perm (Fin 10))⁻¹ i) := by rw [hfix]
      _ = i := Equiv.apply_symm_apply _ _
  have hcord : orderOf c = 3 := by rw [hccycle.orderOf, hcsupp, hScard]
  have hc3 : c ^ 3 = 1 := by rw [← hcord]; exact pow_orderOf_eq_one c
  have hd3 : d ^ 3 = 1 := by
    have hdc : d = MulAut.conj (σ : Perm (Fin 10)) c⁻¹ := by
      rw [MulAut.conj_apply]
    rw [hdc, ← map_pow, inv_pow, hc3, inv_one, map_one]
  have hdisj : c.Disjoint d := by
    intro i
    by_cases hi : i ∈ B
    · exact Or.inr (hd_fixB i hi)
    · exact Or.inl (Equiv.Perm.notMem_support.mp fun h => hi (hcsuppB h))
  obtain ⟨s, hsS⟩ := Finset.card_pos.1 (by rw [hScard]; norm_num)
  have hx3 : (x : Perm (Fin 10)) ^ 3 = 1 := by
    rw [hxval, hdisj.commute.mul_pow, hc3, hd3, mul_one]
  have hxne : (x : Perm (Fin 10)) ≠ 1 := by
    intro h1
    have h2 := congrArg (fun f : Perm (Fin 10) => f s) h1
    rw [hxval, Perm.mul_apply, hd_fixB s (hSB hsS), Perm.one_apply] at h2
    exact (Equiv.Perm.mem_support.mp (by rw [hcsupp]; exact hsS)) h2
  have hxord : orderOf (x : Perm (Fin 10)) = 3 := orderOf_eq_prime hx3 hxne
  have hxordQ : orderOf (⟨x, hxQ⟩ : ↥Q) = 3 := by
    rw [← Subgroup.orderOf_coe (⟨x, hxQ⟩ : ↥Q), ← Subgroup.orderOf_coe x]
    exact hxord
  have hdvd : 3 ∣ Nat.card Q := by
    have := orderOf_dvd_natCard (⟨x, hxQ⟩ : ↥Q)
    rwa [hxordQ] at this
  exact ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp hQ.symm) hdvd

private theorem normal_on_block {B : Finset (Fin 10)}
    {Q : Subgroup (alternatingGroup (Fin 10))}
    (hnorm : ∀ g : alternatingGroup (Fin 10), ((∀ i ∉ B, (g : Perm (Fin 10)) i = i) ∨
      ∀ i ∈ B, (g : Perm (Fin 10)) i = i) → ∀ σ ∈ Q, g * σ * g⁻¹ ∈ Q) :
    ∀ n ∈ Q.map (alternatingGroup (Fin 10)).subtype ⊓ CFSG.GH74.GLS.IVK.GHInv.altOn B,
      ∀ g ∈ CFSG.GH74.GLS.IVK.GHInv.altOn B,
        g * n * g⁻¹ ∈ Q.map (alternatingGroup (Fin 10)).subtype ⊓
          CFSG.GH74.GLS.IVK.GHInv.altOn B := by
  classical
  let U : Subgroup (Perm (Fin 10)) := Q.map (alternatingGroup (Fin 10)).subtype
  let AB : Subgroup (Perm (Fin 10)) := CFSG.GH74.GLS.IVK.GHInv.altOn B
  have hABle : AB ≤ alternatingGroup (Fin 10) :=
    CFSG.GH74.GLS.IVK.GHInv.altOn_le_alternatingGroup B
  have hUle : U ≤ alternatingGroup (Fin 10) := Subgroup.map_subtype_le Q
  intro n hn g hgAB
  have hnU : n ∈ U := hn.1
  have hnAB : n ∈ AB := hn.2
  have hgA : g ∈ alternatingGroup (Fin 10) := hABle hgAB
  have hgfix : ∀ i ∉ B, g i = i := (CFSG.GH74.GLS.IVK.GHInv.mem_altOn.1 hgAB).1
  have hnfix : ∀ i ∉ B, n i = i := (CFSG.GH74.GLS.IVK.GHInv.mem_altOn.1 hnAB).1
  obtain ⟨q, hqQ, hqval⟩ := Subgroup.mem_map.1 hnU
  let ga : alternatingGroup (Fin 10) := ⟨g, hgA⟩
  have hconjQ : ga * q * ga⁻¹ ∈ Q := hnorm ga (Or.inl hgfix) q hqQ
  have hconjUq : (g * q * g⁻¹) ∈ U := by
    refine Subgroup.mem_map.2 ⟨ga * q * ga⁻¹, hconjQ, ?_⟩
    show (ga : Perm (Fin 10)) * (q : Perm (Fin 10)) * (ga : Perm (Fin 10))⁻¹ =
      g * (q : Perm (Fin 10)) * g⁻¹
    rfl
  have hconjU : g * n * g⁻¹ ∈ U := by
    have hnq : n = (q : Perm (Fin 10)) := hqval.symm
    rw [hnq]
    exact hconjUq
  have hconjfix : ∀ i ∉ B, (g * n * g⁻¹) i = i := by
    intro i hi
    have hgi : g⁻¹ i = i := by
      have h := hgfix i hi
      calc g⁻¹ i = g⁻¹ (g i) := by rw [h]
        _ = i := Equiv.symm_apply_apply _ _
    show (g * n * g⁻¹) i = i
    rw [Perm.mul_apply, Perm.mul_apply, hgi, hnfix i hi, hgfix i hi]
  have hconjA : g * n * g⁻¹ ∈ alternatingGroup (Fin 10) :=
    mul_mem (mul_mem hgA (hUle hnU)) (inv_mem hgA)
  exact Subgroup.mem_inf.2 ⟨hconjU, CFSG.GH74.GLS.IVK.GHInv.mem_altOn.2
    ⟨hconjfix, Equiv.Perm.mem_alternatingGroup.1 hconjA⟩⟩

private theorem dvd_three_card_of_altOn_le {B : Finset (Fin 10)} (hB : B.card = 5)
    {Q : Subgroup (alternatingGroup (Fin 10))}
    (hle : CFSG.GH74.GLS.IVK.GHInv.altOn B ≤ Q.map (alternatingGroup (Fin 10)).subtype) :
    3 ∣ Nat.card Q := by
  obtain ⟨S, hSB, hScard⟩ := Finset.exists_subset_card_eq (s := B) (n := 3) (by omega)
  obtain ⟨c, hccycle, hcsupp⟩ :=
    CFSG.AGLEmbedding.exists_isCycle_support_eq (s := S) (by omega)
  have hcsuppB : c.support ⊆ B := hcsupp ▸ hSB
  have hcAB : c ∈ CFSG.GH74.GLS.IVK.GHInv.altOn B :=
    mem_altOn_of_isCycle_support_three hccycle (by rw [hcsupp, hScard]) hcsuppB
  have hcU : c ∈ Q.map (alternatingGroup (Fin 10)).subtype := hle hcAB
  obtain ⟨q, hqQ, hqval⟩ := Subgroup.mem_map.1 hcU
  have hqord : orderOf q = 3 := by
    have hqval' : (q : Perm (Fin 10)) = c := hqval
    rw [← Subgroup.orderOf_coe q, hqval', hccycle.orderOf, hcsupp, hScard]
  have hqordQ : orderOf (⟨q, hqQ⟩ : ↥Q) = 3 := by
    rw [← Subgroup.orderOf_coe (⟨q, hqQ⟩ : ↥Q)]
    exact hqord
  have := orderOf_dvd_natCard (⟨q, hqQ⟩ : ↥Q)
  rwa [hqordQ] at this

private theorem inf_altOn_eq_bot {B : Finset (Fin 10)} (hB : B.card = 5)
    {Q : Subgroup (alternatingGroup (Fin 10))} (hQ : Nat.Coprime (Nat.card Q) 3)
    (hnorm : ∀ g : alternatingGroup (Fin 10), ((∀ i ∉ B, (g : Perm (Fin 10)) i = i) ∨
      ∀ i ∈ B, (g : Perm (Fin 10)) i = i) → ∀ σ ∈ Q, g * σ * g⁻¹ ∈ Q) :
    Q.map (alternatingGroup (Fin 10)).subtype ⊓
      CFSG.GH74.GLS.IVK.GHInv.altOn B = ⊥ := by
  classical
  let U : Subgroup (Perm (Fin 10)) := Q.map (alternatingGroup (Fin 10)).subtype
  let AB : Subgroup (Perm (Fin 10)) := CFSG.GH74.GLS.IVK.GHInv.altOn B
  let H : Subgroup (Perm (Fin 10)) := U ⊓ AB
  have hHnormal : (H.subgroupOf AB).Normal := by
    refine ⟨fun n hn g => ?_⟩
    exact Subgroup.mem_subgroupOf.2 (normal_on_block hnorm n (Subgroup.mem_subgroupOf.1 hn) g g.2)
  haveI : IsSimpleGroup ↥AB :=
    CFSG.GH74.GLS.IVK.GHInv.isSimpleGroup_altOn (F := B) (by omega)
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (H.subgroupOf AB) with hbot | htop
  · rw [eq_bot_iff]
    intro z hz
    have hzH : (⟨z, hz.2⟩ : ↥AB) ∈ H.subgroupOf AB := Subgroup.mem_subgroupOf.2 hz
    rw [hbot] at hzH
    exact Subgroup.mem_bot.2 (congrArg Subtype.val (Subgroup.mem_bot.1 hzH))
  · exfalso
    have hle : AB ≤ U := by
      intro z hz
      have hzH : (⟨z, hz⟩ : ↥AB) ∈ H.subgroupOf AB := by
        rw [htop]
        exact Subgroup.mem_top _
      exact (Subgroup.mem_subgroupOf.1 hzH).1
    exact ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp hQ.symm)
      (dvd_three_card_of_altOn_le hB hle)

private theorem commute_altOn_of_preserves {B : Finset (Fin 10)} (hB : B.card = 5)
    {Q : Subgroup (alternatingGroup (Fin 10))}
    (hnorm : ∀ g : alternatingGroup (Fin 10), ((∀ i ∉ B, (g : Perm (Fin 10)) i = i) ∨
      ∀ i ∈ B, (g : Perm (Fin 10)) i = i) → ∀ σ ∈ Q, g * σ * g⁻¹ ∈ Q)
    {σ : alternatingGroup (Fin 10)} (hσ : σ ∈ Q)
    (hpres : ∀ i ∈ B, (σ : Perm (Fin 10)) i ∈ B)
    (hbot : Q.map (alternatingGroup (Fin 10)).subtype ⊓
      CFSG.GH74.GLS.IVK.GHInv.altOn B = ⊥) :
    ∀ c ∈ CFSG.GH74.GLS.IVK.GHInv.altOn B, Commute (σ : Perm (Fin 10)) c := by
  classical
  intro c hc
  have hcA : c ∈ alternatingGroup (Fin 10) :=
    CFSG.GH74.GLS.IVK.GHInv.altOn_le_alternatingGroup B hc
  have hcfix : ∀ i ∉ B, c i = i := (CFSG.GH74.GLS.IVK.GHInv.mem_altOn.1 hc).1
  let ca : alternatingGroup (Fin 10) := ⟨c, hcA⟩
  have hcaQ : ca * σ * ca⁻¹ ∈ Q := hnorm ca (Or.inl hcfix) σ hσ
  have hxQ : ca * σ * ca⁻¹ * σ⁻¹ ∈ Q := Subgroup.mul_mem Q hcaQ (Subgroup.inv_mem Q hσ)
  have hxfix : ∀ i ∉ B, (c * (σ : Perm (Fin 10)) * c⁻¹ * (σ : Perm (Fin 10))⁻¹) i = i := by
    intro i hi
    have hne : (σ : Perm (Fin 10))⁻¹ i ∉ B := by
      intro hmem
      exact hi (by simpa using hpres _ hmem)
    have hfix : c⁻¹ ((σ : Perm (Fin 10))⁻¹ i) = (σ : Perm (Fin 10))⁻¹ i := by
      have hc' : c ((σ : Perm (Fin 10))⁻¹ i) = (σ : Perm (Fin 10))⁻¹ i := hcfix _ hne
      calc c⁻¹ ((σ : Perm (Fin 10))⁻¹ i)
          = c⁻¹ (c ((σ : Perm (Fin 10))⁻¹ i)) := by rw [hc']
        _ = (σ : Perm (Fin 10))⁻¹ i := Equiv.symm_apply_apply _ _
    calc (c * (σ : Perm (Fin 10)) * c⁻¹ * (σ : Perm (Fin 10))⁻¹) i
        = c ((σ : Perm (Fin 10)) (c⁻¹ ((σ : Perm (Fin 10))⁻¹ i))) := rfl
      _ = c ((σ : Perm (Fin 10)) ((σ : Perm (Fin 10))⁻¹ i)) := by rw [hfix]
      _ = c i := by
          rw [show (σ : Perm (Fin 10)) ((σ : Perm (Fin 10))⁻¹ i) = i from
            Equiv.apply_symm_apply _ _]
      _ = i := hcfix i hi
  have hxAB : c * (σ : Perm (Fin 10)) * c⁻¹ * (σ : Perm (Fin 10))⁻¹ ∈
      CFSG.GH74.GLS.IVK.GHInv.altOn B := by
    refine CFSG.GH74.GLS.IVK.GHInv.mem_altOn.2 ⟨hxfix, ?_⟩
    exact Equiv.Perm.mem_alternatingGroup.1
      (mul_mem (mul_mem (mul_mem hcA σ.2) (inv_mem hcA)) (inv_mem σ.2))
  have hxU : c * (σ : Perm (Fin 10)) * c⁻¹ * (σ : Perm (Fin 10))⁻¹ ∈
      Q.map (alternatingGroup (Fin 10)).subtype := by
    refine Subgroup.mem_map.2 ⟨_, hxQ, ?_⟩
    rfl
  have hx1 : c * (σ : Perm (Fin 10)) * c⁻¹ * (σ : Perm (Fin 10))⁻¹ = 1 := by
    have hxH : c * (σ : Perm (Fin 10)) * c⁻¹ * (σ : Perm (Fin 10))⁻¹ ∈
        Q.map (alternatingGroup (Fin 10)).subtype ⊓
          CFSG.GH74.GLS.IVK.GHInv.altOn B := ⟨hxU, hxAB⟩
    rw [hbot] at hxH
    exact Subgroup.mem_bot.1 hxH
  have h1 : c * (σ : Perm (Fin 10)) * c⁻¹ = σ := by
    have := congrArg (fun t : Perm (Fin 10) => t * (σ : Perm (Fin 10))) hx1
    simpa [mul_assoc] using this
  show Commute (σ : Perm (Fin 10)) c
  exact (show c * (σ : Perm (Fin 10)) = (σ : Perm (Fin 10)) * c by
    calc c * (σ : Perm (Fin 10)) = (c * (σ : Perm (Fin 10)) * c⁻¹) * c := by
          simp only [mul_assoc, inv_mul_cancel, mul_one]
      _ = (σ : Perm (Fin 10)) * c := by rw [h1]).symm

private theorem exists_four_remaining {B : Finset (Fin 10)} (hB : B.card = 5) {i : Fin 10}
    (hi : i ∈ B) :
    ∃ y z u v : Fin 10, y ≠ i ∧ z ≠ i ∧ u ≠ i ∧ v ≠ i ∧ y ∈ B ∧ z ∈ B ∧
      u ∈ B ∧ v ∈ B ∧ y ≠ z ∧ y ≠ u ∧ y ≠ v ∧ z ≠ u ∧ z ≠ v ∧ u ≠ v := by
  have hcard : (B.erase i).card = 4 := by
    rw [Finset.card_erase_of_mem hi, hB]
  obtain ⟨y, z, u, v, hyz, hyu, hyv, hzu, hzv, huv, hT⟩ := Finset.card_eq_four.1 hcard
  have hy := Finset.mem_erase.1 (by rw [hT]; simp : y ∈ B.erase i)
  have hz := Finset.mem_erase.1 (by rw [hT]; simp : z ∈ B.erase i)
  have hu := Finset.mem_erase.1 (by rw [hT]; simp : u ∈ B.erase i)
  have hv := Finset.mem_erase.1 (by rw [hT]; simp : v ∈ B.erase i)
  exact ⟨y, z, u, v, hy.1, hz.1, hu.1, hv.1, hy.2, hz.2, hu.2, hv.2,
    hyz, hyu, hyv, hzu, hzv, huv⟩

private theorem exists_two_three_sets {B : Finset (Fin 10)} (hB : B.card = 5) :
    ∀ i ∈ B, ∃ S₁ S₂ : Finset (Fin 10), S₁.card = 3 ∧ S₂.card = 3 ∧ S₁ ⊆ B ∧
      S₂ ⊆ B ∧ S₁ ∩ S₂ = {i} ∧ i ∈ S₁ ∧ i ∈ S₂ := by
  intro i hi
  obtain ⟨y, z, u, v, hiy, hiz, hiu, hiv, hyB, hzB, huB, hvB, hyz, hyu, hyv, hzu, hzv, huv⟩ :=
    exists_four_remaining hB hi
  let S₁ : Finset (Fin 10) := {i, y, z}
  let S₂ : Finset (Fin 10) := {i, u, v}
  have hS₁card : S₁.card = 3 := by
    have hni : i ∉ ({y, z} : Finset (Fin 10)) := by
      intro h
      rcases Finset.mem_insert.1 h with h | h
      · exact hiy h.symm
      · rw [Finset.mem_singleton] at h
        exact hiz h.symm
    rw [show S₁ = insert i {y, z} from rfl, Finset.card_insert_of_notMem hni,
      Finset.card_pair hyz]
  have hS₂card : S₂.card = 3 := by
    have hni : i ∉ ({u, v} : Finset (Fin 10)) := by
      intro h
      rcases Finset.mem_insert.1 h with h | h
      · exact hiu h.symm
      · rw [Finset.mem_singleton] at h
        exact hiv h.symm
    rw [show S₂ = insert i {u, v} from rfl, Finset.card_insert_of_notMem hni,
      Finset.card_pair huv]
  have hS₁B : S₁ ⊆ B := by
    intro x hx
    have hx' : x = i ∨ x = y ∨ x = z := by simpa [S₁] using hx
    rcases hx' with rfl | rfl | rfl
    · exact hi
    · exact hyB
    · exact hzB
  have hS₂B : S₂ ⊆ B := by
    intro x hx
    have hx' : x = i ∨ x = u ∨ x = v := by simpa [S₂] using hx
    rcases hx' with rfl | rfl | rfl
    · exact hi
    · exact huB
    · exact hvB
  have hinter : S₁ ∩ S₂ = {i} := by
    ext w
    constructor
    · intro hw
      have h1 : w = i ∨ w = y ∨ w = z := by simpa [S₁] using (Finset.mem_inter.1 hw).1
      have h2 : w = i ∨ w = u ∨ w = v := by simpa [S₂] using (Finset.mem_inter.1 hw).2
      rcases h1 with rfl | rfl | rfl
      · exact Finset.mem_singleton.2 rfl
      · rcases h2 with h | h | h
        · exact absurd h hiy
        · exact absurd h hyu
        · exact absurd h hyv
      · rcases h2 with h | h | h
        · exact absurd h hiz
        · exact absurd h hzu
        · exact absurd h hzv
    · intro hw
      rw [Finset.mem_singleton] at hw
      subst hw
      exact Finset.mem_inter.2 ⟨by simp [S₁], by simp [S₂]⟩
  exact ⟨S₁, S₂, hS₁card, hS₂card, hS₁B, hS₂B, hinter,
    by simp [S₁], by simp [S₂]⟩

private theorem fixes_of_commute_altOn {B : Finset (Fin 10)} (hB : B.card = 5)
    {σ : Perm (Fin 10)}
    (hcomm : ∀ c ∈ CFSG.GH74.GLS.IVK.GHInv.altOn B, Commute σ c) :
    ∀ i ∈ B, σ i = i := by
  classical
  intro i hi
  obtain ⟨S₁, S₂, hS₁card, hS₂card, hS₁B, hS₂B, hinter, hiS₁, hiS₂⟩ :=
    exists_two_three_sets hB i hi
  obtain ⟨c₁, hc₁, hc₁supp⟩ :=
    CFSG.AGLEmbedding.exists_isCycle_support_eq (s := S₁) (by omega)
  obtain ⟨c₂, hc₂, hc₂supp⟩ :=
    CFSG.AGLEmbedding.exists_isCycle_support_eq (s := S₂) (by omega)
  have hc₁AB : c₁ ∈ CFSG.GH74.GLS.IVK.GHInv.altOn B :=
    mem_altOn_of_isCycle_support_three hc₁ (by rw [hc₁supp, hS₁card]) (hc₁supp ▸ hS₁B)
  have hc₂AB : c₂ ∈ CFSG.GH74.GLS.IVK.GHInv.altOn B :=
    mem_altOn_of_isCycle_support_three hc₂ (by rw [hc₂supp, hS₂card]) (hc₂supp ▸ hS₂B)
  have hmem₁ : σ i ∈ S₁ := by
    have h := (CFSG.ComponentClassification.GSThmB.Catalog82A10.mem_support_iff_of_commute
      (hcomm c₁ hc₁AB).eq i).2 (by rw [hc₁supp]; exact hiS₁)
    rwa [hc₁supp] at h
  have hmem₂ : σ i ∈ S₂ := by
    have h := (CFSG.ComponentClassification.GSThmB.Catalog82A10.mem_support_iff_of_commute
      (hcomm c₂ hc₂AB).eq i).2 (by rw [hc₂supp]; exact hiS₂)
    rwa [hc₂supp] at h
  have hmem : σ i ∈ S₁ ∩ S₂ := Finset.mem_inter.2 ⟨hmem₁, hmem₂⟩
  rw [hinter] at hmem
  exact Finset.mem_singleton.1 hmem

theorem eq_bot_of_normalized_by_alt_prod_three {B : Finset (Fin 10)} (hB : B.card = 5)
    {Q : Subgroup (alternatingGroup (Fin 10))} (hQ : Nat.Coprime (Nat.card Q) 3)
    (hQB : ∀ σ ∈ Q, (∀ i ∈ B, (σ : Perm (Fin 10)) i ∈ B) ∨
      ∀ i ∈ B, (σ : Perm (Fin 10)) i ∉ B)
    (hnorm : ∀ g : alternatingGroup (Fin 10), ((∀ i ∉ B, (g : Perm (Fin 10)) i = i) ∨
      ∀ i ∈ B, (g : Perm (Fin 10)) i = i) → ∀ σ ∈ Q, g * σ * g⁻¹ ∈ Q) :
    Q = ⊥ := by
  classical
  have hBc : Bᶜ.card = 5 := by
    rw [Finset.card_compl, Fintype.card_fin, hB]
  have hpres : ∀ σ ∈ Q, ∀ i ∈ B, (σ : Perm (Fin 10)) i ∈ B := by
    intro σ hσ i hi
    rcases hQB σ hσ with h | h
    · exact h i hi
    · exact absurd h (not_swaps_of_coprime_three hB hQ hnorm hσ)
  have hpresc : ∀ σ ∈ Q, ∀ i ∈ Bᶜ, (σ : Perm (Fin 10)) i ∈ Bᶜ := by
    intro σ hσ i hi
    have himg : B.image (σ : Perm (Fin 10)) = B :=
      Finset.eq_of_subset_of_card_le (Finset.image_subset_iff.2 (hpres σ hσ)) (by
        rw [Finset.card_image_of_injective B (σ : Perm (Fin 10)).injective])
    rw [Finset.mem_compl]
    intro hmemB
    obtain ⟨j, hjB, hji⟩ := Finset.mem_image.1 (himg ▸ hmemB)
    exact (Finset.mem_compl.1 hi) ((σ : Perm (Fin 10)).injective hji ▸ hjB)
  have hnormc : ∀ g : alternatingGroup (Fin 10), ((∀ i ∉ Bᶜ, (g : Perm (Fin 10)) i = i) ∨
      ∀ i ∈ Bᶜ, (g : Perm (Fin 10)) i = i) → ∀ σ ∈ Q, g * σ * g⁻¹ ∈ Q := by
    intro g hg
    apply hnorm g
    rcases hg with h | h
    · right
      intro i hi
      exact h i (by simpa using hi)
    · left
      intro i hi
      exact h i (by simpa using hi)
  have hbot := inf_altOn_eq_bot hB hQ hnorm
  have hbotc := inf_altOn_eq_bot (B := Bᶜ) hBc hQ hnormc
  rw [eq_bot_iff]
  intro σ hσ
  have hfix : ∀ i ∈ B, (σ : Perm (Fin 10)) i = i :=
    fixes_of_commute_altOn hB (commute_altOn_of_preserves hB hnorm hσ (hpres σ hσ) hbot)
  have hfixc : ∀ i ∈ Bᶜ, (σ : Perm (Fin 10)) i = i :=
    fixes_of_commute_altOn hBc
      (commute_altOn_of_preserves (B := Bᶜ) hBc hnormc hσ (hpresc σ hσ) hbotc)
  refine Subgroup.mem_bot.2 (Subtype.ext ?_)
  apply Equiv.Perm.ext
  intro i
  by_cases hi : i ∈ B
  · exact hfix i hi
  · exact hfixc i (by simpa using hi)

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7.SEFive.AltTen
