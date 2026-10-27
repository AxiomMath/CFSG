module

public import CFSG.HardMathSupport.Timmesfeld.CrossChar.PlanesToralWeyl
public import CFSG.LieType.AlgebraicGroups.ToralRootCover
public import CFSG.LieType.Chevalley.ToralCentralizerQuotient
import CFSG.HardMathSupport.Timmesfeld.CrossChar.E6ThreeBlock
import CFSG.HardMathSupport.Timmesfeld.Steinberg.ThreeChar
import CFSG.HardMathSupport.Timmesfeld.Steinberg.ThreeCharStabilizer
import CFSG.LieType.Chevalley.C2E6UnitaryFourImages
import CFSG.RankThree.Classical2.TwistedE6Phi3A2Case
import CFSG.RankThree.PartOne.KLCE.Sector

public section

namespace CFSG.StandardType.SCFourCover

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.HardMathSupport.Timmesfeld.Steinberg
  CFSG.LieType.AlgebraicGroups


theorem e6_nat_card_roots : Nat.card {v : Fin Tag.E6.rank → ℤ // IsRoot Tag.E6 v} = 72 := by
  rw [Nat.card_eq_fintype_card, card_isRoot]
  rfl

private theorem e6_rootReflection_single (j : Fin Tag.E6.rank) :
    rootReflection (Pi.single j 1 : Fin Tag.E6.rank → ℤ) = simple Tag.E6 j := by
  rw [rootReflection_eq_conj (w := 1) (j := j) (by simp)]
  simp

private theorem e6_base_fixed_count :
    ((rootFinset Tag.E6).filter
      (fun v => reflect Tag.E6 0 (reflect Tag.E6 2 v) = v)).card = 12 := by
  decide +kernel

private theorem e6_card_fixedBy_base :
    Nat.card (MulAction.fixedBy {v : Fin Tag.E6.rank → ℤ // IsRoot Tag.E6 v}
      (pairRefl ((Pi.single 0 1 : Fin Tag.E6.rank → ℤ),
        (Pi.single 2 1 : Fin Tag.E6.rank → ℤ)))) = 12 := by
  have e : Subtype.val '' MulAction.fixedBy {v : Fin Tag.E6.rank → ℤ // IsRoot Tag.E6 v}
      (pairRefl ((Pi.single 0 1 : Fin Tag.E6.rank → ℤ), (Pi.single 2 1 : Fin Tag.E6.rank → ℤ))) =
      ↑((rootFinset Tag.E6).filter (fun v => reflect Tag.E6 0 (reflect Tag.E6 2 v) = v)) := by
    ext v
    simp only [Set.mem_image, MulAction.mem_fixedBy, Finset.coe_filter, mem_rootFinset,
      Set.mem_setOf_eq, pairRefl, e6_rootReflection_single, Subtype.exists, exists_and_right,
      exists_eq_right]
    constructor
    · rintro ⟨hv, hfix⟩
      refine ⟨hv, ?_⟩
      have key := congrArg Subtype.val hfix
      rw [coe_smul_root, mul_smul, simple_smul, simple_smul] at key
      exact key
    · rintro ⟨hv, hfix⟩
      refine ⟨hv, Subtype.ext ?_⟩
      rw [coe_smul_root, mul_smul, simple_smul, simple_smul]
      exact hfix
  rw [Nat.card_coe_set_eq, ← Set.ncard_image_of_injective _ Subtype.val_injective, e,
    Set.ncard_coe_finset, e6_base_fixed_count]

open Pointwise in
theorem e6_card_fixedBy_pairRefl {α β : Fin Tag.E6.rank → ℤ} (h : IsA2Pair α β) :
    Nat.card (MulAction.fixedBy {v : Fin Tag.E6.rank → ℤ // IsRoot Tag.E6 v}
      (pairRefl (α, β))) = 12 := by
  obtain ⟨u, hu0, hu2⟩ := exists_weyl_a2Pair_E6 h
  have hconj : pairRefl (α, β) = u * pairRefl ((Pi.single 0 1 : Fin Tag.E6.rank → ℤ),
      (Pi.single 2 1 : Fin Tag.E6.rank → ℤ)) * u⁻¹ := by
    simp only [pairRefl]
    rw [← hu0, ← hu2, rootReflection_smul_root u (isRoot_single _ _),
      rootReflection_smul_root u (isRoot_single _ _)]
    group
  rw [hconj, ← MulAction.smul_fixedBy, Set.natCard_smul_set]
  exact e6_card_fixedBy_base

set_option synthInstance.maxSize 1024 in
private theorem e6_orth_a2_kerCount_ne :
    ∀ γ ∈ rootFinset Tag.E6, iform (Pi.single 0 1 : Fin Tag.E6.rank → ℤ) γ = 0 →
    iform (Pi.single 2 1 : Fin Tag.E6.rank → ℤ) γ = 0 →
    ∀ δ ∈ rootFinset Tag.E6, iform (Pi.single 0 1 : Fin Tag.E6.rank → ℤ) δ = 0 →
    iform (Pi.single 2 1 : Fin Tag.E6.rank → ℤ) δ = 0 → iform γ δ = -1 →
    ∀ n < 3 ^ Tag.E6.rank,
      triPairing (vec3OfIndex n) (Pi.single 0 1 : Fin Tag.E6.rank → ℤ) = 0 →
      triPairing (vec3OfIndex n) (Pi.single 2 1 : Fin Tag.E6.rank → ℤ) = 0 →
      triPairing (vec3OfIndex n) γ = 0 → triPairing (vec3OfIndex n) δ = 0 →
      ((rootFinset Tag.E6).filter fun α => triPairing (vec3OfIndex n) α = 0).card ≠ 22 ∧
      ((rootFinset Tag.E6).filter fun α => triPairing (vec3OfIndex n) α = 0).card ≠ 24 ∧
      ((rootFinset Tag.E6).filter fun α => triPairing (vec3OfIndex n) α = 0).card ≠ 40 := by
  decide +kernel

private theorem e6_ncard_kernelRoots_triChar (b : Fin Tag.E6.rank → ZMod 3) :
    (kernelRoots (triChar b)).ncard =
      ((rootFinset Tag.E6).filter fun α => triPairing b α = 0).card := by
  rw [← Set.ncard_coe_finset]
  congr 1
  ext α
  simp only [Finset.coe_filter, Set.mem_setOf_eq, mem_rootFinset]
  exact mem_kernelRoots_triChar

private theorem e6_not_two_orth_a2 {b : Fin Tag.E6.rank → ZMod 3}
    {α β γ δ : Fin Tag.E6.rank → ℤ} (hp : IsA2Pair α β) (hq : IsA2Pair γ δ)
    (hpS : a2Roots α β ⊆ kernelRoots (triChar b)) (hqS : a2Roots γ δ ⊆ kernelRoots (triChar b))
    (horth : PairsStrOrth (α, β) (γ, δ)) :
    (kernelRoots (triChar b)).ncard ≠ 22 ∧ (kernelRoots (triChar b)).ncard ≠ 24 ∧
      (kernelRoots (triChar b)).ncard ≠ 40 := by
  obtain ⟨u, hu0, hu2⟩ := exists_weyl_a2Pair_E6 hp
  obtain ⟨b', hb'⟩ : ∃ b', conjChar (triChar b) u⁻¹ = triChar b' := ⟨_, eq_triChar _⟩
  have hC : IsCharConj (triChar b) (conjChar (triChar b) u⁻¹) u⁻¹ := isCharConj_conjChar _ _
  rw [hb'] at hC
  have hker : ∀ ρ, ρ ∈ kernelRoots (triChar b') ↔ u • ρ ∈ kernelRoots (triChar b) := by
    intro ρ
    rw [kernelRoots_iff_of_isCharConj hC, inv_inv]
  have himg : kernelRoots (triChar b') = (fun ρ => u⁻¹ • ρ) '' kernelRoots (triChar b) := by
    ext ρ
    refine ⟨fun h => ⟨u • ρ, (hker ρ).1 h, inv_smul_smul u ρ⟩, ?_⟩
    rintro ⟨σ, hσ, rfl⟩
    rw [hker, smul_inv_smul]
    exact hσ
  have hnc : (kernelRoots (triChar b)).ncard = (kernelRoots (triChar b')).ncard := by
    rw [himg, Set.ncard_image_of_injective _ (MulAction.injective u⁻¹)]
  rw [hnc, e6_ncard_kernelRoots_triChar]
  have hαS : α ∈ kernelRoots (triChar b) := hpS (by simp [a2Roots])
  have hβS : β ∈ kernelRoots (triChar b) := hpS (by simp [a2Roots])
  have hγS : γ ∈ kernelRoots (triChar b) := hqS (by simp [a2Roots])
  have hδS : δ ∈ kernelRoots (triChar b) := hqS (by simp [a2Roots])
  have hαγ : iform α γ = 0 := (horth α (by simp [a2Roots]) γ (by simp [a2Roots])).1
  have hαδ : iform α δ = 0 := (horth α (by simp [a2Roots]) δ (by simp [a2Roots])).1
  have hβγ : iform β γ = 0 := (horth β (by simp [a2Roots]) γ (by simp [a2Roots])).1
  have hβδ : iform β δ = 0 := (horth β (by simp [a2Roots]) δ (by simp [a2Roots])).1
  have hγδ : iform γ δ = -1 := by
    have h2 := hq.two_iform
    rw [iform_self_E6 hq.isRoot_fst] at h2
    omega
  have he0 : (Pi.single 0 1 : Fin Tag.E6.rank → ℤ) ∈ kernelRoots (triChar b') := by
    rw [hker, hu0]; exact hαS
  have he2 : (Pi.single 2 1 : Fin Tag.E6.rank → ℤ) ∈ kernelRoots (triChar b') := by
    rw [hker, hu2]; exact hβS
  have hγ' : u⁻¹ • γ ∈ kernelRoots (triChar b') := by
    rw [hker, smul_inv_smul]; exact hγS
  have hδ' : u⁻¹ • δ ∈ kernelRoots (triChar b') := by
    rw [hker, smul_inv_smul]; exact hδS
  have hi : ∀ x y : Fin Tag.E6.rank → ℤ, iform (u⁻¹ • x) (u⁻¹ • y) = iform x y :=
    fun x y => iform_smul u⁻¹ x y
  have key : ∀ x y : Fin Tag.E6.rank → ℤ, iform (u • x) y = iform x (u⁻¹ • y) := fun x y => by
    rw [← hi (u • x) y, inv_smul_smul]
  obtain ⟨n, hn, rfl⟩ := exists_vec3OfIndex b'
  exact e6_orth_a2_kerCount_ne (u⁻¹ • γ) (mem_rootFinset.2 hγ'.1)
    (by rw [← key, hu0]; exact hαγ) (by rw [← key, hu2]; exact hβγ)
    (u⁻¹ • δ) (mem_rootFinset.2 hδ'.1)
    (by rw [← key, hu0]; exact hαδ) (by rw [← key, hu2]; exact hβδ)
    (by rw [hi]; exact hγδ) n hn (mem_kernelRoots_triChar.1 he0).2
    (mem_kernelRoots_triChar.1 he2).2 (mem_kernelRoots_triChar.1 hγ').2
    (mem_kernelRoots_triChar.1 hδ').2

theorem e6Levi_eq_pairRefl_of_pow_three {L : Type} [Field L] (a : Fin Tag.E6.rank → Lˣ)
    (ha : ∀ i, a i ^ 3 = 1) (hk : (kernelRoots (rootCharHom a)).ncard ∈ ({22, 24, 40} : Set ℕ))
    {w : WeylGroup Tag.E6} (hw : w ∈ kernelReflectionGroup a) (h3 : w ^ 3 = 1) (h1 : w ≠ 1) :
    ∃ α β : Fin Tag.E6.rank → ℤ, IsA2Pair α β ∧ w = pairRefl (α, β) := by
  classical
  obtain ⟨χ', hker⟩ := exists_triChar_ker_eq (rootCharHom3 a) (rootCharHom3_pow_three a ha)
  obtain ⟨b, rfl⟩ : ∃ b, χ' = triChar b := ⟨_, eq_triChar χ'⟩
  have hW : kernelReflectionGroup a = kernelWeylGroup (rootCharHom3 a) := rfl
  have hw' : w ∈ kernelWeylGroup (triChar b) := by
    rw [hW, kernelWeylGroup_congr_ker hker] at hw
    exact hw
  have hker' : kernelRoots (rootCharHom3 a) = kernelRoots (triChar b) :=
    kernelRoots_congr_ker hker
  have hk' : (kernelRoots (triChar b)).ncard = 22 ∨ (kernelRoots (triChar b)).ncard = 24 ∨
      (kernelRoots (triChar b)).ncard = 40 := by
    have hk2 : (kernelRoots (rootCharHom3 a)).ncard ∈ ({22, 24, 40} : Set ℕ) := hk
    rw [← hker']
    simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using hk2
  obtain ⟨B, hB, hPW, hprod⟩ := exists_a2Blocks hw' h3
  rcases B with _ | ⟨p, _ | ⟨q, rest⟩⟩
  · exact absurd (by simpa using hprod) h1
  · exact ⟨p.1, p.2, (hB p (by simp)).1, by simpa using hprod⟩
  · exfalso
    have hpq : PairsStrOrth p q := (List.pairwise_cons.1 hPW).1 q (by simp)
    obtain ⟨hp, hpS⟩ := hB p (by simp)
    obtain ⟨hq, hqS⟩ := hB q (by simp)
    obtain ⟨h22, h24, h40⟩ := e6_not_two_orth_a2 hp hq hpS hqS hpq
    rcases hk' with h | h | h
    exacts [h22 h, h24 h, h40 h]

end CFSG.StandardType.SCFourCover

end
