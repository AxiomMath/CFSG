module

public import CFSG.LocalAnalysis.WeakClosure81.W183TwoCtx
public import CFSG.LocalAnalysis.WeakClosure81.W183TwoSec
public import CFSG.LocalAnalysis.WeakClosure81.W183TwoGrComp
public import CFSG.LocalAnalysis.WeakClosure81.W183TwoOdd

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.SignalizerFunctorTheorem.Quadratic CFSG.Quasithin.G11 CFSG.Quasithin CFSG.Open
  CFSG.QuasithinUnique Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
  CFSG.LocalAnalysis.UniquenessCase.PartTwo

variable {G : Type} [Group G] [Finite G] {D : Data G} {V₀ V H : Subgroup G} {i : ℕ}

theorem tail1812Two_false_graph (hB : ListBNonabelian) (hGraph : FinGraphOdd) {g : G}
    (cx : Tail1812TwoCtx G D V₀ V H i g) {L : Subgroup G}
    (hL : IsComponentModN (kerMV V H) H L) {X : Type} [Group X] [Finite X] [IsSimpleGroup X]
    (hnc : ∃ u v : X, u * v ≠ v * u) (φ : ↥L →* X) (hφs : Function.Surjective φ)
    (hφk : ∀ k : ↥L, φ k = 1 ↔ (k : G) ∈ kerMV V H) (hX : IsAlt X 6 ∨ IsSp4 X 2) {t : G}
    (htT : t ∈ D.T) (hDyn : ActsOnDynkinMod (kerMV V H) L t) : False := by
  classical
  obtain ⟨Y, _, _, π, a₁, Kk, P, hset⟩ := tail1812Two_exists_setting hB cx
  obtain ⟨φ', hφ's, hφ'k, -⟩ :=
    tail1812Two_exists_section hL hset.surj hset.ker_le hset.mem_kk φ hφs hφk
  have hLcP : (L.subgroupOf H).map π ≤ P :=
    le_of_simple_section hset.kk_le_p hset.p_normal hset.two_quot hnc φ' hφ's hφ'k
  have hPN : P ≤ Subgroup.normalClosure ({π a₁} : Set Y) :=
    hset.le_of_not_le _ Subgroup.normalClosure_normal fun hle =>
      hset.not_mem (hle (Subgroup.subset_normalClosure rfl))
  have hLH : L ≤ H := hL.2.2.1
  have hgen : L ≤ ((Subgroup.normalClosure ({π a₁} : Set Y)).comap π).map H.subtype := by
    intro l hl
    let lH : ↥H := ⟨l, hLH hl⟩
    have hπl : π lH ∈ (L.subgroupOf H).map π :=
      Subgroup.mem_map_of_mem π (Subgroup.mem_subgroupOf.mpr hl)
    exact Subgroup.mem_map.mpr
      ⟨lH, Subgroup.mem_comap.mpr (hPN (hLcP hπl)), rfl⟩
  have htH : t ∈ H := cx.cex.hyp.isSylowIn_T.le htT
  exact false_of_graph_component hGraph hL hnc φ hφs hφk hX htH hDyn π hset.surj hset.ker_le
    hset.ord (isOddTransp_class_of_comm_or_conj hset.ord hset.comm_or_conj) hgen

end CFSG.LocalAnalysis.WeakClosure81

end
