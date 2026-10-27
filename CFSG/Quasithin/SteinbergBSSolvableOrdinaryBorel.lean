module

public import CFSG.LieType.Chevalley.GraphFixedHighestRoot

public section

namespace CFSG.Quasithin.SteinbergBS

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open scoped Pointwise

namespace SolvableOrdinaryBorel

variable {τ : Tag} {K : Type} [Field K]

theorem exists_forall_yUnit_mem
    {M : Subgroup (ModGL τ K)} (hMC : M ≤ adjointGroup τ K)
    (hUM : posUnipotent τ K ≤ M) (hMB : ¬ M ≤ borelGroup τ K) :
    ∃ i : Fin τ.rank, ∀ c : K, yUnit τ K i c ∈ M := by
  obtain ⟨g, hg, hgB⟩ := Set.not_subset.1 hMB
  have hg' : g ∈ ⋃ w, bruhatCell τ K w := by
    rw [← adjointGroup_eq_iUnion_bruhatCell]
    exact hMC hg
  obtain ⟨w, hw⟩ := Set.mem_iUnion.1 hg'
  obtain ⟨b, hb, b', hb', rfl⟩ := mem_bruhatCell.1 hw
  have hT := triangular_borel_structure.{0, 0} τ K
  have hbUH : b ∈ (posUnipotent τ K : Set (ModGL τ K)) * (torusGroup τ K : Set (ModGL τ K)) := by
    rw [← hT.2.2.2.2.2.1]
    exact hb
  have hbHU : b' ∈ (torusGroup τ K : Set (ModGL τ K)) * (posUnipotent τ K : Set (ModGL τ K)) := by
    rw [← hT.2.2.2.2.1]
    exact hb'
  obtain ⟨u₁, hu₁, h₁, hh₁, rfl⟩ := Set.mem_mul.1 hbUH
  obtain ⟨h₂, hh₂, u₂, hu₂, rfl⟩ := Set.mem_mul.1 hbHU
  set n := canonicalRep (coxeterSystem τ) K w with hn
  set z := h₁ * n * h₂ with hz
  have hzM : z ∈ M := by
    have h := mul_mem (mul_mem (inv_mem (hUM hu₁)) hg) (inv_mem (hUM hu₂))
    have e : u₁⁻¹ * (u₁ * h₁ * n * (h₂ * u₂)) * u₂⁻¹ = z := by
      rw [hz]
      group
    rwa [e] at h
  have hw1 : w ≠ 1 := by
    rintro rfl
    have hn1 : n = 1 := by
      rw [hn, canonicalRep_one]
    rw [hn1, mul_one] at hgB
    exact hgB (mul_mem hb hb')
  obtain ⟨i, hi⟩ := (coxeterSystem τ).exists_rightDescent_of_ne_one (inv_ne_one.2 hw1)
  have hneg := (smul_single_mem_negRoots_iff w⁻¹ i).2 hi
  set β : Fin τ.rank → ℤ := -(w⁻¹ • (Pi.single i 1 : Fin τ.rank → ℤ)) with hβ
  have hβroot : IsRoot τ β := IsRoot.neg (IsRoot.smul (isRoot_single τ i) w⁻¹)
  have hβpos : 0 < height β := by
    rw [hβ, height_neg]
    exact neg_pos.2 hneg.2
  have hwβ : w • β = -Pi.single i 1 := by
    rw [hβ, smul_neg, smul_inv_smul]
  refine ⟨i, fun c => ?_⟩
  have hy : yUnit τ K i c ∈ rootSubgroup τ K (-Pi.single i 1) := by
    rw [← pinnedX_neg_single]
    exact Subgroup.subset_closure ⟨c, rfl⟩
  have hN₁ := torusGroup_le_normalizer_rootSubgroup (R := K) (isRoot_neg_single τ i)
    (inv_mem hh₁)
  have hy₁ := (Subgroup.mem_normalizer_iff.1 hN₁ _).1 hy
  rw [← hwβ, ← (canonical_weyl_root_transport τ K).2.1 w β hβroot] at hy₁
  obtain ⟨u, hu, hue⟩ := hy₁
  rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at hue
  have hN₂ := torusGroup_le_normalizer_rootSubgroup (R := K) hβroot (inv_mem hh₂)
  have hu' := (Subgroup.mem_normalizer_iff.1 hN₂ _).1 hu
  have huM : h₂⁻¹ * u * h₂⁻¹⁻¹ ∈ M :=
    hUM (Subgroup.mem_iSup_of_mem β (Subgroup.mem_iSup_of_mem ⟨hβroot, hβpos⟩ hu'))
  have e : yUnit τ K i c = z * (h₂⁻¹ * u * h₂⁻¹⁻¹) * z⁻¹ := by
    have e' : yUnit τ K i c = h₁ * (n * u * n⁻¹) * h₁⁻¹ := by
      rw [hue]
      group
    rw [e', hz]
    group
  rw [e]
  exact mul_mem (mul_mem hzM huM) (inv_mem hzM)

theorem not_isSolvable_rankOneSubgroup (hK : (4 : ℕ∞) ≤ ENat.card K) (i : Fin τ.rank) :
    ¬ Group.IsSolvable (rankOneSubgroup (τ := τ) (K := K) i) := by
  intro hsolv
  have hx1 : xElt (τ := τ) i (1 : K) ≠ 1 := by
    intro h
    have h' : pinnedX τ K (Pi.single i 1) 1 = pinnedX τ K (Pi.single i 1) 0 := by
      rw [pinnedX_single, pinnedX_single, xUnit_zero]
      exact congrArg Subtype.val h
    exact one_ne_zero (pinnedX_injective (τ := τ) (R := K) _ h')
  have : Nontrivial (rankOneSubgroup (τ := τ) (K := K) i) :=
    ⟨⟨⟨xElt i 1, Subgroup.mem_sup_left (xElt_mem_simplePosSubgroup i 1)⟩, 1,
      fun h => hx1 (congrArg Subtype.val h)⟩⟩
  have hlt := Group.IsSolvable.commutator_lt_top_of_nontrivial
    (rankOneSubgroup (τ := τ) (K := K) i)
  rw [(rank_one_scalar_perfect τ K i).2 hK] at hlt
  exact lt_irrefl _ hlt

end SolvableOrdinaryBorel

open SolvableOrdinaryBorel

theorem solvable_ordinary_posUnipotent_overgroups_le_borelGroup
    (τ : Tag) (K : Type) [Field K]
    [Finite K] (hK : 4 ≤ Nat.card K) {M : Subgroup (ModGL τ K)} (hMC : M ≤ adjointGroup τ K)
    (hUM : posUnipotent τ K ≤ M) (hM : Group.IsSolvable M) : M ≤ borelGroup τ K := by
  by_contra hMB
  obtain ⟨i, hi⟩ := exists_forall_yUnit_mem hMC hUM hMB
  have hle : ∀ g ∈ rankOneSubgroup (τ := τ) (K := K) i, (g : ModGL τ K) ∈ M := by
    intro g hg
    have hmap : (rankOneSubgroup (τ := τ) (K := K) i).map (adjointGroup τ K).subtype ≤ M := by
      rw [rankOneSubgroup, Subgroup.map_sup]
      refine sup_le ?_ ?_
      · rintro _ ⟨x, ⟨c, hc⟩, rfl⟩
        change (x : ModGL τ K) ∈ M
        rw [hc]
        exact hUM (xUnit_mem_posUnipotent i c)
      · rintro _ ⟨y, ⟨c, hc⟩, rfl⟩
        change (y : ModGL τ K) ∈ M
        rw [hc]
        exact hi c
    exact hmap ⟨g, hg, rfl⟩
  let f : rankOneSubgroup (τ := τ) (K := K) i →* M :=
    ((adjointGroup τ K).subtype.comp (rankOneSubgroup (τ := τ) (K := K) i).subtype).codRestrict
      M fun g => hle g g.2
  have hf : Function.Injective f := fun g g' h =>
    Subtype.ext (Subtype.ext (congrArg (fun x : M => (x : ModGL τ K)) h))
  have hK' : (4 : ℕ∞) ≤ ENat.card K := by
    rw [ENat.card_eq_coe_natCard K]
    exact_mod_cast hK
  exact not_isSolvable_rankOneSubgroup hK' i (Group.isSolvable_of_isSolvable_injective hf)

end CFSG.Quasithin.SteinbergBS
