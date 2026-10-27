module

public import Mathlib.GroupTheory.Transfer

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.ChiefFactors.Core

namespace CFSG
end CFSG
open CFSG

/-!
# Burnside normal p-complement consequence
-/

/-- If a Sylow `p`-subgroup is contained in the center of its normalizer, then there is a normal
subgroup of `p'`-order with `p`-group quotient. -/
public theorem CFSG.exists_normal_coprime_subgroup_and_pgroup_quotient_of_sylow_le_center_normalizer
    {G : Type*} [Group G] [Finite G] (p : ℕ) [Fact p.Prime] (S : Sylow p G)
    (hS : (S : Subgroup G) ≤ centerIn (G := G) (Subgroup.normalizer (S : Subgroup G))) :
    ∃ (N : Subgroup G) (_ : N.Normal), Nat.Coprime p (Nat.card N) ∧ IsPGroup p (G ⧸ N) := by
  let hNC : Subgroup.normalizer (S : Set G) ≤ Subgroup.centralizer (S : Set G) := by
    intro g hg s hs
    exact ((hS hs).2 g hg).symm
  let N : Subgroup G := (MonoidHom.transferSylow S hNC).ker
  have hcomp : N.IsComplement' (S : Subgroup G) := by
    simpa [N] using (MonoidHom.ker_transferSylow_isComplement' S hNC)
  refine ⟨N, inferInstance, ?_, ?_⟩
  · have hnot : ¬ p ∣ Nat.card N := by
      intro hp_dvd
      have : p ∣ (S : Subgroup G).index := by
        simpa [hcomp.index_eq_card] using hp_dvd
      exact S.not_dvd_index this
    exact (Nat.Prime.coprime_iff_not_dvd (Fact.out : Nat.Prime p)).2 hnot
  · have hcomp' : (S : Subgroup G).IsComplement' N := hcomp.symm
    let e : G ⧸ N ≃* (S : Subgroup G) := hcomp'.QuotientMulEquiv
    exact IsPGroup.of_injective (hG := by simpa using S.isPGroup')
      (ϕ := e.toMonoidHom) e.injective
