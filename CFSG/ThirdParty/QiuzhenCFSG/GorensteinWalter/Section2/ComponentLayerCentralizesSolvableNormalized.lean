module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.Bender1970_18
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.FStarSubnormal

namespace CFSG
end CFSG
open CFSG

/-!
# A component layer centralizes normalized solvable subgroups

This is the finite-group fact used in Bender 1.7(iv): if a solvable subgroup
of `A` is normalized by `E(A)`, then `E(A)` centralizes it.  The proof first
shows that the solvable intersection with the layer is centralized by every
component.  The whole commutator lies in that intersection, and perfectness
of the layer plus the three-subgroups lemma finishes the argument.
-/

noncomputable section

namespace CFSG.GorensteinWalter

universe u

private theorem componentLayerOf_commutator_self
    {G : Type u} [Group G] [Finite G] (A : Subgroup G) :
    ⁅componentLayerOf A, componentLayerOf A⁆ = componentLayerOf A := by
  apply le_antisymm
  · exact (Subgroup.commutator_le_sup _ _).trans (sup_idem _).le
  · rw [componentLayerOf]
    apply sSup_le
    intro K hK
    have hKE : K ≤ componentLayerOf A := le_sSup hK
    have hKK : ⁅K, K⁆ = K := by
      have hperf : Group.IsPerfect K :=
        (Group.isPerfect_def).2 hK.2.2.2.1
      exact Subgroup.isPerfect_iff.mp hperf
    rw [← hKK]
    exact Subgroup.commutator_mono hKE hKE

/-- A solvable subgroup `N ≤ A` normalized by `E(A)` is centralized by the
component layer. -/
public theorem componentLayerOf_centralizes_solvable_of_le_normalizer
    {G : Type u} [Group G] [Finite G]
    (A N : Subgroup G)
    (hNA : N ≤ A)
    (hNsolv : Group.IsSolvable N)
    (hEN : componentLayerOf A ≤ Subgroup.normalizer (N : Set G)) :
    ⁅componentLayerOf A, N⁆ = ⊥ := by
  let E : Subgroup G := componentLayerOf A
  let S : Subgroup G := E ⊓ N
  have hEleA : E ≤ A := (fstar_componentLayerOf_isNormalIn A).1
  have hNleNormE : N ≤ Subgroup.normalizer (E : Set G) :=
    hNA.trans (le_normalizer_of_isNormalIn (fstar_componentLayerOf_isNormalIn A))
  have hSnormE : IsNormalIn S E := by
    refine ⟨inf_le_left, ?_⟩
    intro e he s hs
    refine ⟨E.mul_mem (E.mul_mem he hs.1) (E.inv_mem he), ?_⟩
    exact (Subgroup.mem_normalizer_iff.mp (hEN he) s).mp hs.2
  have hSsubE : (S.subgroupOf E).IsSubnormal := by
    exact (Subgroup.normal_subgroupOf_of_le_normalizer (H := E) (N := S)
      (le_normalizer_of_isNormalIn hSnormE)).isSubnormal
  have hSsubA : (S.subgroupOf A).IsSubnormal :=
    fstar_isSubnormal_subgroupOf_of_subnormal_subgroupOf_normal
      inf_le_left hSsubE hEleA (fstar_componentLayerOf_isNormalIn A)
  have hSsolv : Group.IsSolvable S := by
    let : Group.IsSolvable N := hNsolv
    have : Group.IsSolvable (S.subgroupOf N) := inferInstance
    exact isSolvable_of_mulEquiv (Subgroup.subgroupOfEquivOfLe inf_le_right)
  have hEleC : E ≤ Subgroup.centralizer (S : Set G) := by
    dsimp [E]
    rw [componentLayerOf]
    apply sSup_le
    intro K hK
    rcases fstar_component_le_or_commutator_eq_bot_of_subnormal_subgroupOf
        (S := S) (E := K) (hSnormE.1.trans hEleA) hSsubA hK with hKS | hcomm
    · exfalso
      let : Group.IsSolvable S := hSsolv
      have : Group.IsSolvable (K.subgroupOf S) := inferInstance
      have hKsolv : Group.IsSolvable K :=
        isSolvable_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hKS)
      let : Nontrivial K := hK.2.2.1
      let : Group.IsPerfect K :=
        ⟨by simpa [derivedSubgroup] using hK.2.2.2.1⟩
      exact Group.IsPerfect.not_isSolvable K hKsolv
    · exact (Subgroup.commutator_eq_bot_iff_le_centralizer
        (H₁ := K) (H₂ := S)).1 hcomm
  have hcommE : ⁅E, N⁆ ≤ E :=
    (Subgroup.le_normalizer_iff_commutator_le_left (H := N) (K := E)).1 hNleNormE
  have hcommN : ⁅E, N⁆ ≤ N :=
    (Subgroup.le_normalizer_iff_commutator_le_right (H := E) (K := N)).1 hEN
  have hcommS : ⁅E, N⁆ ≤ S := le_inf hcommE hcommN
  have hSE : ⁅S, E⁆ = ⊥ := by
    rw [Subgroup.commutator_comm]
    exact (Subgroup.commutator_eq_bot_iff_le_centralizer
      (H₁ := E) (H₂ := S)).2 hEleC
  have h1 : ⁅⁅E, N⁆, E⁆ = ⊥ := by
    apply le_antisymm
    · calc
        ⁅⁅E, N⁆, E⁆ ≤ ⁅S, E⁆ := Subgroup.commutator_mono hcommS le_rfl
        _ = ⊥ := hSE
    · exact bot_le
  have h2 : ⁅⁅N, E⁆, E⁆ = ⊥ := by
    rw [Subgroup.commutator_comm (H₁ := N) (H₂ := E)]
    exact h1
  have hrot : ⁅⁅E, E⁆, N⁆ = ⊥ :=
    Subgroup.commutator_commutator_eq_bot_of_rotate
      (H₁ := E) (H₂ := E) (H₃ := N) h1 h2
  simpa [E, componentLayerOf_commutator_self A] using hrot

end CFSG.GorensteinWalter
