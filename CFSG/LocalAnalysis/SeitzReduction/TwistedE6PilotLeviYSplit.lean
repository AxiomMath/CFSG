module

public import CFSG.LocalAnalysis.SeitzReduction.TwistedE6PilotLeviYFaithful
public import CFSG.LocalAnalysis.SectionRank.EvenCover.Orthogonal
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalFamilyLemmasThree

public section

namespace CFSG.SeitzReduction.TwistedE6Pilot

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Chevalley.C2E6Std
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.OrthogonalSplit
  CFSG.LieType.Universal.Spin CFSG.ClassicalGroups.Orthogonal CFSG.Assembly.LowTwoRank

section Stated

variable (K : Type) [Field K] [CharP K 2]

@[expose] noncomputable def elementaryPlusStatedEquiv :
    orthElementaryGroup (quadPlus 4 K) ≃* StatedProj (StatedOmega (StatedQuadPlus 4 K)) :=
  ((elementaryGroup (quadPlus 4 K)).equivMapOfInjective
      (toLinEquiv (Fin 4 ⊕ Fin 4) K).symm.toMonoidHom (toLinEquiv (Fin 4 ⊕ Fin 4) K).symm.injective).trans
    ((MulEquiv.subgroupCongr (statedOmega_quadPlus_eq_map (n := 4) (K := K) (by norm_num)).symm).trans
      ((QuotientGroup.quotientMulEquivOfEq
        (CFSG.SectionRank.EvenCover.statedScalars_subgroupOf_statedOmega_eq_bot (coe_quadPlus 4 K)
          ⟨Pi.single (.inl 0) 1 + Pi.single (.inr 0) 1, by
            rw [quadPlus_apply]
            simp [Fin.sum_univ_four]⟩)).trans QuotientGroup.quotientBot).symm)

end Stated

section Equiv


variable (K : Type) [Field K] [Finite K] [CharP K 2]

@[expose] noncomputable def d4PsiEquiv : d4Levi K ≃* orthElementaryGroup (quadPlus 4 K) :=
  (MonoidHom.ofInjective d4Psi_injective).trans (MulEquiv.subgroupCongr range_d4Psi)

variable {K}

theorem coe_d4PsiEquiv (g : d4Levi K) :
    (d4PsiEquiv K g : (Fin 4 ⊕ Fin 4 → K) ≃ₗ[K] (Fin 4 ⊕ Fin 4 → K)) = d4Psi K g :=
  rfl

theorem d4PsiEquiv_xUnit (k : Fin 4) (c : K) :
    (d4PsiEquiv K ⟨xUnit Tag.E6 K (jD k) c, xUnit_mem_d4Levi k c⟩ :
      (Fin 4 ⊕ Fin 4 → K) ≃ₗ[K] (Fin 4 ⊕ Fin 4 → K)) =
        rootElt 4 K (OrthogonalSplit.simpleRoot 4 k) c :=
  d4Psi_xUnit k c

theorem d4PsiEquiv_yUnit (k : Fin 4) (c : K) :
    (d4PsiEquiv K ⟨yUnit Tag.E6 K (jD k) c, yUnit_mem_d4Levi k c⟩ :
      (Fin 4 ⊕ Fin 4 → K) ≃ₗ[K] (Fin 4 ⊕ Fin 4 → K)) =
        rootElt 4 K (-OrthogonalSplit.simpleRoot 4 k) c :=
  d4Psi_yUnit k c

theorem lieModel_d4Levi {f : ℕ} (hf : 1 ≤ f) (hK : Nat.card K = 2 ^ f) :
    LieModel (d4Levi K) .POmegaPlus 4 2 f :=
  Or.inl ⟨by decide, ⟨Nat.prime_two, hf, le_rfl⟩, K, inferInstance, inferInstance, hK,
    ⟨(d4PsiEquiv K).trans (elementaryPlusStatedEquiv K)⟩⟩

theorem isSimpleGroup_d4Levi : IsSimpleGroup (d4Levi K) :=
  have := isSimpleGroup_statedProj_statedOmega_quadPlus (n := 4) (K := K) (by norm_num)
  ((d4PsiEquiv K).trans (elementaryPlusStatedEquiv K)).isSimpleGroup

theorem isPerfect_d4Levi : Group.IsPerfect (d4Levi K) :=
  have := (orthogonal_elementary_perfect (regular_quadPlus (n := 4) (K := K) (by norm_num)).1
    (regular_quadPlus (n := 4) (K := K) (by norm_num)).2).1
  Group.IsPerfect.ofSurjective (f := (d4PsiEquiv K).symm.toMonoidHom) (d4PsiEquiv K).symm.surjective

end Equiv

end CFSG.SeitzReduction.TwistedE6Pilot
