module

public import CFSG.LocalAnalysis.UniquenessCase.UC22K108BN
import CFSG.Milestones.ASVolI.I2
import CFSG.LocalAnalysis.QuasithinUnique.GammaFamiliesBasic

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open Subgroup CFSG.ASVolI.ChIJK

theorem uc22k108bn_exists_conj_split {X : Type} [Group X] [Finite X] {B N : Subgroup X}
    (hBN : IsSplitBNPair 2 B N) {U : Subgroup X} (hUp : IsPGroup 2 U)
    (hUi : ¬ 2 ∣ U.index) :
    ∃ B' N' : Subgroup X, IsSplitBNPair 2 B' N' ∧ U ≤ B' ∧
      normalizer (U : Set X) = B' ∧ B' ≤ U ⊔ (B' ⊓ N') := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨U₀, hU₀B, hU₀n, hU₀p, hU₀i, -, hU₀H, -⟩ := hBN.split
  have hsyl₀ : CFSG.QuasithinUnique.IsSylowTwoOf U₀ ⊤ := by
    simpa [IsPGroup.toSylow_coe] using
      CFSG.QuasithinUnique.isSylowTwoOf_top_of_sylow (hU₀p.toSylow hU₀i)
  have hsyl : CFSG.QuasithinUnique.IsSylowTwoOf U ⊤ := by
    simpa [IsPGroup.toSylow_coe] using
      CFSG.QuasithinUnique.isSylowTwoOf_top_of_sylow (hUp.toSylow hUi)
  obtain ⟨c, -, hc⟩ := hsyl₀.exists_conj hsyl
  have hfinj : Function.Injective (MulAut.conj c).toMonoidHom := (MulAut.conj c).injective
  have hBN' : IsSplitBNPair 2 (B.map (MulAut.conj c).toMonoidHom)
      (N.map (MulAut.conj c).toMonoidHom) :=
    burnsideI2BN_map hBN _ (MulAut.conj c).surjective
      (by rw [(MonoidHom.ker_eq_bot_iff _).2 hfinj]; exact bot_le)
  set B' := B.map (MulAut.conj c).toMonoidHom with hB'
  set N' := N.map (MulAut.conj c).toMonoidHom with hN'
  have hUB' : U ≤ B' := hc ▸ Subgroup.map_mono hU₀B
  have hBU₀ : B ≤ normalizer (U₀ : Set X) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hU₀B).1 hU₀n
  have hB'U : B' ≤ normalizer (U : Set X) := by
    rw [hc, hB', ← Subgroup.map_equiv_normalizer_eq U₀ (MulAut.conj c)]
    exact Subgroup.map_mono hBU₀
  have hUn' : (U.subgroupOf B').Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hUB').2 hB'U
  have hNU : normalizer (U : Set X) = B' :=
    uc22k108bn_normalizer_eq Nat.prime_two hBN' hUB' hUn' hUp hUi
  have hBUH : B' ≤ U ⊔ (B' ⊓ N') := by
    rw [hc, hB', hN', ← Subgroup.map_inf_eq _ _ _ hfinj, ← Subgroup.map_sup, hU₀H]
  exact ⟨B', N', hBN', hUB', hNU, hBUH⟩

end CFSG.LocalAnalysis.UniquenessCase.UC22

end
