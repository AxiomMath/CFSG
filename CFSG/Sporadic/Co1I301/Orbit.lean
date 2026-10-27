module

public import CFSG.Sporadic.Co1I301.Elements
public import CFSG.Sporadic.Co1Patterson.GraphTree

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.Sporadic.Co1I301

open Subgroup CFSG.Sporadic.Co1Schreier CFSG.Sporadic.Co1Block CFSG.Sporadic.SmallF2
  CFSG.Sporadic.Co1Patterson CFSG.Sporadic.Co1Patterson.Native CFSG.Sporadic.Co1I301.Native
  CFSG.Sporadic.Co1.Module
open CFSG.Blueprint (NativeSporadic.Co1)

private theorem le_relIndex_centralizer {G : Type*} [Group G] (K : Subgroup G) [Finite K] (d : G)
    (n : ℕ) (f : ℕ → G) (hfK : ∀ i < n, f i ∈ K)
    (hf : ∀ i < n, ∀ j < n, f i * d * (f i)⁻¹ = f j * d * (f j)⁻¹ → i = j) :
    n ≤ (Subgroup.centralizer ({d} : Set G)).relIndex K := by
  rw [Subgroup.relIndex, Subgroup.index_eq_card]
  let F : Fin n → K ⧸ (Subgroup.centralizer ({d} : Set G)).subgroupOf K :=
    fun i => QuotientGroup.mk ⟨f i, hfK i i.2⟩
  have hFinj : Function.Injective F := by
    intro i j hij
    have h := QuotientGroup.eq.1 hij
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_centralizer_singleton_iff] at h
    refine Fin.ext (hf i i.2 j j.2 ?_)
    simp only [Subgroup.coe_mul, Subgroup.coe_inv] at h
    calc f i * d * (f i)⁻¹ = f i * (d * ((f i)⁻¹ * f j)) * (f j)⁻¹ := by group
      _ = f i * ((f i)⁻¹ * f j * d) * (f j)⁻¹ := by rw [h]
      _ = f j * d * (f j)⁻¹ := by group
  have := Nat.card_le_card_of_injective F hFinj
  simpa [Nat.card_fin] using this


theorem card_centralizer_dC_inf_le :
    Nat.card ↥(centralizer ({dC} : Set NativeSporadic.Co1) ⊓
      centralizer ({aNC} : Set NativeSporadic.Co1)) ≤ 9953280 := by
  have hcard := card_centralizer_aNC
  haveI : Finite ↥(centralizer ({aNC} : Set NativeSporadic.Co1)) :=
    Nat.finite_of_card_ne_zero (by rw [hcard]; norm_num)
  have h4 := co1RowCheck_parts.2.2.2.1
  simp only [chkOrbit, Bool.and_eq_true, beq_iff_eq] at h4
  obtain ⟨hok, hsize⟩ := h4
  have hsound := orbOK_sound matHom hok brayNC (fun l hl => nrep_brayArr l hl) dC nrep_dC
  choose! g hg _ _ hgp using hsound
  have hcl : Subgroup.closure (brayNC '' {l | l < brayArr.size}) =
      centralizer ({aNC} : Set NativeSporadic.Co1) := by
    rw [brayArr_size]
    exact closure_brayNC
  have hn : 8960 ≤ (centralizer ({dC} : Set NativeSporadic.Co1)).relIndex
      (centralizer ({aNC} : Set NativeSporadic.Co1)) := by
    refine le_relIndex_centralizer _ dC 8960 g ?_ ?_
    · intro i hi
      rw [← hcl]
      exact hg i (hsize ▸ hi)
    · intro i hi j hj hij
      refine orbOK_injective hok (hsize ▸ hi) (hsize ▸ hj) ?_
      rw [← hgp i (hsize ▸ hi), ← hgp j (hsize ▸ hj), hij]
  have h := Subgroup.relIndex_mul_card (centralizer ({dC} : Set NativeSporadic.Co1))
    (centralizer ({aNC} : Set NativeSporadic.Co1))
  rw [hcard] at h
  have h2 : 8960 * Nat.card ↥(centralizer ({dC} : Set NativeSporadic.Co1) ⊓
      centralizer ({aNC} : Set NativeSporadic.Co1)) ≤ 89181388800 := by
    rw [← h]
    exact Nat.mul_le_mul_right _ hn
  omega

end CFSG.Sporadic.Co1I301
