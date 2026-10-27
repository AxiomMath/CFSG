module

public import CFSG.LocalAnalysis.UniquenessCase.UCFront14
import CFSG.GroupTheory.SubgroupTransport
import CFSG.GroupTheory.QuasiDihedralFusion.Basic

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.F14

open CFSG.ABGLocalTools (IsSylowOf)

theorem exists_conj_family_mem_funSet {X : Type} [Group X] [Finite X] {ι : Type*}
    {𝔉 : ∀ {Y : Type} [Group Y], Subgroup Y → Subgroup Y → Prop}
    (hconj : ∀ (g : X) {K : Subgroup X},
      𝔉 ⊤ K → 𝔉 ⊤ (K.map (MulAut.conj g).toMonoidHom))
    (K : ι → Subgroup X) (hK : ∀ i, 𝔉 ⊤ (K i))
    (hnorm : ∀ i j, K j ≤ Subgroup.normalizer (K i : Set X)) (P : Sylow 2 X) :
    ∃ g : X, ∀ i, (K i).map (MulAut.conj g).toMonoidHom ∈
      FunSet 𝔉 X (P : Subgroup X) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨Q, hQ⟩ := CFSG.ABGLocalTools.exists_isSylowOf 2 (⨆ i, K i)
  obtain ⟨g, _, hg⟩ := CFSG.QuasiDihedralFusion.exists_conj_le_sylow
    ⊤ P le_top Q le_top hQ.isPGroup
  refine ⟨g, fun i => ⟨hconj g (hK i), ?_⟩⟩
  have hQi : IsSylowOf 2 (Q ⊓ K i) (K i) :=
    hQ.inf_of_le_normalizer (le_iSup K i) (iSup_le fun j => hnorm i j)
  have hmap : IsSylowOf 2 ((Q ⊓ K i).map (MulAut.conj g).toMonoidHom)
      ((K i).map (MulAut.conj g).toMonoidHom) :=
    (CFSG.GroupTheory.isSylowOf_map_mulEquiv (MulAut.conj g)).mpr hQi
  have heq := hmap.eq_of_le
    (le_inf ((Subgroup.map_mono inf_le_left).trans hg) hmap.le)
    inf_le_right P.isPGroup'.to_inf_left
  rw [heq]
  exact hmap

theorem natCard_le_ncard_funSet_of_normalizing_family {X : Type} [Group X] [Finite X]
    {ι : Type*} [Finite ι]
    {𝔉 : ∀ {Y : Type} [Group Y], Subgroup Y → Subgroup Y → Prop}
    (hconj : ∀ (g : X) {K : Subgroup X},
      𝔉 ⊤ K → 𝔉 ⊤ (K.map (MulAut.conj g).toMonoidHom))
    (K : ι → Subgroup X) (hK : ∀ i, 𝔉 ⊤ (K i)) (hinj : Function.Injective K)
    (hnorm : ∀ i j, K j ≤ Subgroup.normalizer (K i : Set X)) (P : Sylow 2 X) :
    Nat.card ι ≤ (FunSet 𝔉 X (P : Subgroup X)).ncard := by
  obtain ⟨g, hg⟩ := exists_conj_family_mem_funSet hconj K hK hnorm P
  have hinj' : Function.Injective (fun i => (K i).map (MulAut.conj g).toMonoidHom) :=
    (Subgroup.map_injective (MulAut.conj g).injective).comp hinj
  have h := Set.ncard_le_ncard_of_injOn (fun i => (K i).map (MulAut.conj g).toMonoidHom)
    (s := Set.univ) (t := FunSet 𝔉 X (P : Subgroup X))
    (fun i _ => hg i) hinj'.injOn
  simpa only [Set.ncard_univ] using h

end CFSG.LocalAnalysis.UniquenessCase.UC22.F14
