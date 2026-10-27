module

public import CFSG.LocalAnalysis.SeitzReduction.EPilotRootSL2Basic

public section

namespace CFSG.StandardType.KGCentExc

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

theorem exists_rootDiagUnit_mem_rootSpan_pair
    {τ : Tag} {K : Type} [Field K]
    (hτ : τ = .E7 ∨ τ = .E8) {β : Fin τ.rank → ℤ} (hβ : IsRoot τ β) (ζ : Kˣ) :
    ∃ a : Fin τ.rank → Kˣ, rootDiagUnit τ a ∈ rootSpan τ K {β, -β} ∧
      rootChar a β = ζ ^ 2 ∧ ∀ i, ∃ m : ℤ, a i = ζ ^ m := by
  have hτ' : τ = .E6 ∨ τ = .E7 ∨ τ = .E8 := Or.inr hτ
  have hχ : ∀ γ, rootChar (fun j => ζ ^ iform β (Pi.single j 1)) γ = ζ ^ iform β γ := by
    intro γ
    rw [SeitzReduction.F4Pilot.iform_eq_sum_mul_iform_single β γ, rootChar,
      ← Finset.prod_zpow_eq_zpow_sum]
    exact Finset.prod_congr rfl fun j _ => by rw [← zpow_mul, mul_comm]
  obtain ⟨v, i, hv⟩ := isRoot_iff_exists_smul_single.1 hβ
  refine ⟨fun j => ζ ^ iform β (Pi.single j 1), ?_, ?_, fun j => ⟨_, rfl⟩⟩
  · have e : rootDiagUnit τ (fun j => ζ ^ iform β (Pi.single j 1)) =
        canonicalRep (coxeterSystem τ) K v * torusElt τ K i ζ *
          (canonicalRep (coxeterSystem τ) K v)⁻¹ := by
      rw [torusElt_eq_rootDiagUnit]
      refine (rootDiagUnit_eq_conj_canonicalRep_iff _ _ v).2 fun x => ?_
      rw [hχ, SeitzReduction.EPilot.rootChar_cartan_row, ← hv, iform_smul, iform_comm,
        SeitzReduction.EPilot.iform_single_eq_coPair hτ']
    have hmap : (rootSubgroup τ K (Pi.single i 1) ⊔ rootSubgroup τ K (-Pi.single i 1)).map
        (MulAut.conj (canonicalRep (coxeterSystem τ) K v)).toMonoidHom =
          rootSubgroup τ K β ⊔ rootSubgroup τ K (-β) := by
      rw [Subgroup.map_sup, (canonical_weyl_root_transport τ K).2.1 v _ (isRoot_single τ i),
        (canonical_weyl_root_transport τ K).2.1 v _ (IsRoot.neg (isRoot_single τ i)), smul_neg,
        hv]
    have hmem : rootDiagUnit τ (fun j => ζ ^ iform β (Pi.single j 1)) ∈
        rootSubgroup τ K β ⊔ rootSubgroup τ K (-β) := by
      rw [e, ← hmap]
      exact ⟨_, SeitzReduction.F4Pilot.torusElt_mem_rootPair i ζ, rfl⟩
    have h1 : rootSubgroup τ K β ≤ rootSpan τ K {β, -β} :=
      le_iSup₂_of_le β (Set.mem_insert _ _) le_rfl
    have h2 : rootSubgroup τ K (-β) ≤ rootSpan τ K {β, -β} :=
      le_iSup₂_of_le (-β) (Set.mem_insert_of_mem _ rfl) le_rfl
    exact sup_le h1 h2 hmem
  · rw [hχ, SeitzReduction.EPilot.iform_self_eq_two hτ' hβ]
    exact zpow_two ζ |>.trans (sq ζ).symm

end CFSG.StandardType.KGCentExc

end
