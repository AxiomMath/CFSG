module

public import CFSG.GroupTheory.LocalCores.Layer
public import CFSG.LinearAlgebra.LinearGroups.ProjectiveSimple
public import CFSG.Timmesfeld.Bridge.Asc72Defs

public section

namespace CFSG.OddTranspositions

open CFSG.Timmesfeld.Bridge.Asc72
open Subgroup

attribute [local instance] CFSG.LocalCores.layer_characteristic

theorem l2Wreath_base_le_layer {f n : ℕ} (hf : 2 ≤ f) :
    (⊤ : Subgroup (Fin n → CFSG.Theory.Comparator.PSL2Model f)).map
        (SemidirectProduct.inl (φ := permAct (Fin n) (CFSG.Theory.Comparator.PSL2Model f))) ≤
      layer (L2Wreath f n) := by
  classical
  let L := CFSG.Theory.Comparator.PSL2Model f
  let φ : Equiv.Perm (Fin n) →* MulAut (Fin n → L) := permAct (Fin n) L
  let G := (Fin n → L) ⋊[φ] Equiv.Perm (Fin n)
  let inl : (Fin n → L) →* G := SemidirectProduct.inl
  let B : Subgroup G := (⊤ : Subgroup (Fin n → L)).map inl
  change B ≤ layer (L2Wreath f n)
  have hf0 : f ≠ 0 := by omega
  have hcard : Nat.card (GaloisField 2 f) = 2 ^ f := GaloisField.card 2 f hf0
  letI : Fintype (GaloisField 2 f) := Fintype.ofFinite _
  have h4 : ∃ s : Finset (GaloisField 2 f), s.card = 4 := by
    have h4' : 4 ≤ Fintype.card (GaloisField 2 f) := by
      rw [← Nat.card_eq_fintype_card, hcard]
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
    obtain ⟨s, -, hs⟩ := Finset.exists_subset_card_eq
      (s := (Finset.univ : Finset (GaloisField 2 f))) (n := 4) (by rwa [Finset.card_univ])
    exact ⟨s, hs⟩
  obtain ⟨hnt, hsimple, -⟩ := CFSG.LinearGroups.linear_projective_simple
    (K := GaloisField 2 f) (n := 2) le_rfl (Or.inr h4)
  have hperf : Group.IsPerfect L :=
    CFSG.LinearGroups.linear_projective_perfect
      (K := GaloisField 2 f) (n := 2) le_rfl (Or.inr h4)
  haveI : IsSimpleGroup L := hsimple
  haveI : Nontrivial L := hnt
  haveI : Group.IsPerfect L := hperf
  have hna : ∃ a b : L, a * b ≠ b * a := by
    by_contra h
    push Not at h
    exact Group.IsPerfect.not_isMulCommutative L (IsMulCommutative.mk (Std.Commutative.mk h))
  have hLq : CFSG.IsQuasisimple L :=
    (CFSG.LocalCores.isQuasisimple_of_isSimpleGroup (Q := L) hna).1
  let single : Fin n → L →* (Fin n → L) :=
    fun i => MonoidHom.mulSingle (fun _ : Fin n => L) i
  let c : Fin n → L →* G := fun i => inl.comp (single i)
  let Li : Fin n → Subgroup G := fun i => (c i).range
  have hBker : B = (SemidirectProduct.rightHom (φ := φ)).ker := by
    show (⊤ : Subgroup (Fin n → L)).map inl =
      (SemidirectProduct.rightHom (φ := φ)).ker
    rw [Subgroup.map_top]
    exact SemidirectProduct.range_inl_eq_ker_rightHom
  have hBnormal : B.Normal := hBker.symm ▸ MonoidHom.normal_ker _
  have hLiB : ∀ i, Li i ≤ B := by
    intro i x hx
    obtain ⟨s, rfl⟩ := hx
    change inl (single i s) ∈ B
    exact Subgroup.mem_map_of_mem inl (Subgroup.mem_top (single i s))
  have hLiNormalizer : ∀ i, B ≤ Subgroup.normalizer (Li i) := by
    intro i
    rw [Subgroup.le_normalizer_iff]
    intro x hx y hy
    obtain ⟨u, -, rfl⟩ := hx
    obtain ⟨s, rfl⟩ := hy
    have hconj : u * single i s * u⁻¹ = single i (u i * s * (u i)⁻¹) := by
      change u * Pi.mulSingle i s * u⁻¹ =
        Pi.mulSingle i (u i * s * (u i)⁻¹)
      funext j
      by_cases hj : j = i
      · subst hj
        simp only [Pi.mul_apply, Pi.inv_apply, Pi.mulSingle_eq_same]
      · simp only [Pi.mul_apply, Pi.inv_apply, Pi.mulSingle_eq_of_ne hj, mul_one,
          mul_inv_cancel]
    change inl u * inl ((single i) s) * (inl u)⁻¹ ∈ Li i
    rw [← map_inv, ← map_mul, ← map_mul]
    change inl (u * (single i) s * u⁻¹) ∈ Li i
    rw [hconj]
    exact ⟨u i * s * (u i)⁻¹, rfl⟩
  have hcoord : ∀ i, CFSG.IsComponent (Li i) := by
    intro i
    have hinj : Function.Injective (c i) := by
      intro a b hab
      have h1 : single i a = single i b := by
        apply SemidirectProduct.inl_injective (φ := φ)
        simpa only [c, MonoidHom.comp_apply] using hab
      exact Pi.mulSingle_injective (M := fun _ : Fin n => L) i (by
        simpa [single, MonoidHom.coe_mulSingle] using h1)
    have hLiq : CFSG.IsQuasisimple (Li i) :=
      CFSG.LocalCores.isQuasisimple_of_mulEquiv (MonoidHom.ofInjective hinj) hLq
    have hLinorm : ((Li i).subgroupOf B).Normal :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer (hLiB i)).mpr (hLiNormalizer i)
    have hLisub : (Li i).IsSubnormal :=
      Subgroup.IsSubnormal.step (Li i) B (hLiB i) hBnormal.isSubnormal hLinorm
    exact ⟨hLiq, hLisub⟩
  intro x hx
  obtain ⟨u, -, rfl⟩ := hx
  change u ∈ (layer (L2Wreath f n)).comap inl
  refine Subgroup.pi_mem_of_mulSingle_mem u fun i => ?_
  change inl (Pi.mulSingle i (u i)) ∈ layer (L2Wreath f n)
  exact CFSG.LocalCores.component_le_layer (hcoord i) ⟨u i, rfl⟩

end CFSG.OddTranspositions
