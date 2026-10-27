module

public import CFSG.Quasithin.Vol2.Ch10SecQ4A11
public import CFSG.Quasithin.Vol2.Ch10SecQ4A12
public import CFSG.Quasithin.Vol2.Ch10SecQ4A5
public import CFSG.Quasithin.Vol2.Ch1A3Cat

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecF.C10E4

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.QuasithinUnique.C1 Equiv

@[expose] def dbl5' : ↥(alternatingGroup (Fin 5)) :=
  ⟨swap 0 2 * swap 1 3, by rw [Perm.mem_alternatingGroup]; decide⟩

theorem dbl5'_facts : dbl5' ^ 2 = 1 ∧ dbl5' ≠ 1 ∧ dbl5 ≠ dbl5' ∧ dbl5 * dbl5' = dbl5' * dbl5 := by
  refine ⟨Subtype.ext ?_, fun h => ?_, fun h => ?_, Subtype.ext ?_⟩
  · show (swap (0 : Fin 5) 2 * swap 1 3) ^ 2 = 1
    decide
  · have := congrArg (fun σ : ↥(alternatingGroup (Fin 5)) => (σ : Perm (Fin 5)) 0) h
    revert this
    decide
  · have := congrArg (fun σ : ↥(alternatingGroup (Fin 5)) => (σ : Perm (Fin 5)) 0) h
    revert this
    decide
  · show swap (0 : Fin 5) 1 * swap 2 3 * (swap 0 2 * swap 1 3) =
      swap 0 2 * swap 1 3 * (swap 0 1 * swap 2 3)
    decide

variable {G : Type} [Group G] [Finite G] {K J X T : Subgroup G}

theorem false_of_nonquasi_of_blockQ_le (h36' : A36ForSQTK) (hXs : CFSG.SectionRank.IsSQTKCat ↥X)
    (hJ : J ∈ cComp X) (hKJ : K ≤ J) (h5 : IsAltType K 5) (hQQ : blockQ K ≤ pCoreOf 2 J)
    (hnq : ¬ CFSG.IsQuasisimple (↥J ⧸ CFSG.pCore 2 ↥J)) : False := by
  have hYc := sqtkHypCat_quot (le_of_mem_cComp hJ) hXs
  obtain ⟨α, hα, hαk, -⟩ := h5
  have hmem : ∀ x : ↥K, α x = 1 ↔ (x : G) ∈ blockQ K := fun x => by
    rw [← MonoidHom.mem_ker, hαk]
    exact ⟨mem_blockQ_of_mem_pCore, mem_pCore_of_mem_blockQ⟩
  have hf1 : ∀ x : ↥K, fK hKJ x = 1 ↔ α x = 1 := fun x =>
    ⟨fun h => (hmem x).mpr (fK_ker_le hKJ x h),
      fun h => (fK_eq_one_iff hKJ x).mpr (hQQ ((hmem x).mp h))⟩
  obtain ⟨h2, h1, h12, hc⟩ := dbl5'_facts
  obtain ⟨k₁, hk₁⟩ := hα dbl5
  obtain ⟨k₂, hk₂⟩ := hα dbl5'
  refine false_of_four (h36' _ (sqtkHyp_of_cat hYc)) (top_mem_cComp_quot hJ) hnq
    (a := fK hKJ k₁) (b := fK hKJ k₂) ?_ ?_ ?_ ?_ ?_ ?_
  · rw [← map_pow, hf1, map_pow, hk₁, dbl5_sq]
  · rw [← map_pow, hf1, map_pow, hk₂, h2]
  · rw [Ne, hf1, hk₁]
    exact dbl5_ne_one
  · rw [Ne, hf1, hk₂]
    exact h1
  · intro h
    have : fK hKJ (k₁⁻¹ * k₂) = 1 := by rw [map_mul, map_inv, h, inv_mul_cancel]
    rw [hf1, map_mul, map_inv, hk₁, hk₂, inv_mul_eq_one] at this
    exact h12 this
  · have : fK hKJ (k₁ * k₂ * k₁⁻¹ * k₂⁻¹) = 1 := by
      rw [hf1, map_mul, map_mul, map_mul, map_inv, map_inv, hk₁, hk₂, hc]
      group
    rw [map_mul, map_mul, map_mul, map_inv, map_inv] at this
    have h' := congrArg (· * (fK hKJ k₂ * fK hKJ k₁)) this
    simp only [one_mul] at h'
    rw [← h']
    group

end CFSG.Quasithin.Vol2.Ch10.SecF.C10E4
