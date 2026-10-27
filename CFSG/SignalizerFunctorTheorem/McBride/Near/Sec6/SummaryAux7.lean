module

public import CFSG.SignalizerFunctorTheorem.McBride.Near.Sec3.Thm311bAux1
public import CFSG.SignalizerFunctorTheorem.McBride.Near.Sec6.FinalAuxBase

public section

namespace CFSG.SignalizerFunctorTheorem.McBride.Near.Sec6S34

namespace SingleOrbitAux

variable {G : Type*} [Group G]

theorem isPerfect_of_noncomm {D : Subgroup G} (hs : IsSimpleGroup ↥D)
    (hnc : ∃ x ∈ D, ∃ y ∈ D, x * y ≠ y * x) : Group.IsPerfect ↥D := by
  obtain ⟨x, hx, y, hy, hxy⟩ := hnc
  exact (CFSG.LocalCores.isQuasisimple_of_isSimpleGroup
    ⟨⟨x, hx⟩, ⟨y, hy⟩, fun h => hxy (congrArg Subtype.val h)⟩).1.1

theorem simple_of_isDiagonal_block [Finite G] {K D : Subgroup G} (hK : IsSemisimple K)
    {P : Set (Set (Subgroup G))} (hP0 : ∅ ∉ P) (hU : ⋃₀ P = lcal K) {T : Set (Subgroup G)}
    (hT : T ∈ P) (hD : IsDiagonal T D) :
    IsSimpleGroup ↥D ∧ ∃ x ∈ D, ∃ y ∈ D, x * y ≠ y * x := by
  have hKdp : IsDirectProduct (lcal K) K := hK.isDirectProduct_lcal
  have hTsub : T ⊆ lcal K := hU ▸ Set.subset_sUnion_of_mem hT
  obtain ⟨J, hJT⟩ : T.Nonempty := Set.nonempty_iff_ne_empty.mpr fun h => hP0 (h ▸ hT)
  have hJc : J ∈ CFSG.SignalizerFunctorTheorem.Nonsolvable.simpleComponents K := by
    rw [← hK.lcal_eq]
    exact hTsub hJT
  exact Thm311b.isSimple_of_isDiagonal (Thm210.isDirectProduct_of_subset hKdp hTsub) hJT
    hJc.2.2.1 hJc.2.2.2 hD

theorem inf_sSup_eq_perfRes [Finite G] {K Y : Subgroup G} (hK : IsSemisimple K)
    {P : Set (Set (Subgroup G))} (hP0 : ∅ ∉ P) (hU : ⋃₀ P = lcal K)
    (hdp : IsDirectProduct ((fun T => Y ⊓ sSup T) '' P) Y)
    (hdiag : ∀ T ∈ P, IsDiagonal T (Y ⊓ sSup T)) (hsimple : IsSimpleGroup ↥(perfRes Y))
    {T : Set (Subgroup G)} (hT : T ∈ P) : Y ⊓ sSup T = perfRes Y := by
  obtain ⟨hDs, hDnc⟩ := simple_of_isDiagonal_block hK hP0 hU hT (hdiag T hT)
  have hDperf : Group.IsPerfect ↥(Y ⊓ sSup T) := isPerfect_of_noncomm hDs hDnc
  have hDQ : Y ⊓ sSup T ≤ perfRes Y := Sec6S33.le_perfRes_of_isPerfect hDperf inf_le_left
  refine le_antisymm hDQ ?_
  have hnorm : perfRes Y ≤ Subgroup.normalizer ((Y ⊓ sSup T : Subgroup G) : Set G) :=
    (Sec6S33.perfRes_le Y).trans (hdp.le_normalizer ⟨T, hT, rfl⟩)
  have hN : ((Y ⊓ sSup T).subgroupOf (perfRes Y)).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hDQ).mpr hnorm
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal ((Y ⊓ sSup T).subgroupOf (perfRes Y)) with
    h | h
  · exfalso
    obtain ⟨x, hx, y, hy, hxy⟩ := hDnc
    have hxQ : (⟨x, hDQ hx⟩ : ↥(perfRes Y)) ∈ (Y ⊓ sSup T).subgroupOf (perfRes Y) := hx
    rw [h, Subgroup.mem_bot] at hxQ
    have hx1 : x = 1 := congrArg Subtype.val hxQ
    exact hxy (by rw [hx1, one_mul, mul_one])
  · exact Subgroup.subgroupOf_eq_top.mp h

theorem eq_of_inf_sSup_eq_perfRes [Finite G] {K Y : Subgroup G} (hK : IsSemisimple K)
    {P : Set (Set (Subgroup G))} (hU : ⋃₀ P = lcal K) (hdisj : P.PairwiseDisjoint id)
    (hblock : ∀ T ∈ P, Y ⊓ sSup T = perfRes Y) (hsimple : IsSimpleGroup ↥(perfRes Y))
    {T₁ T₂ : Set (Subgroup G)} (h₁ : T₁ ∈ P) (h₂ : T₂ ∈ P) : T₁ = T₂ := by
  by_contra hne
  have hKdp : IsDirectProduct (lcal K) K := hK.isDirectProduct_lcal
  have hsub₁ : T₁ ⊆ lcal K := hU ▸ Set.subset_sUnion_of_mem h₁
  have hsub₂ : T₂ ⊆ lcal K := hU ▸ Set.subset_sUnion_of_mem h₂
  have hdj : Disjoint (sSup T₁) (sSup T₂) :=
    Thm210.disjoint_sSup_sSup hKdp hsub₁ hsub₂ (hdisj h₁ h₂ hne)
  obtain ⟨x, hx1⟩ := exists_ne (1 : ↥(perfRes Y))
  have hx₁ : (x : G) ∈ sSup T₁ := by
    have : (x : G) ∈ Y ⊓ sSup T₁ := by
      rw [hblock T₁ h₁]
      exact x.2
    exact this.2
  have hx₂ : (x : G) ∈ sSup T₂ := by
    have : (x : G) ∈ Y ⊓ sSup T₂ := by
      rw [hblock T₂ h₂]
      exact x.2
    exact this.2
  have hxm : (x : G) ∈ sSup T₁ ⊓ sSup T₂ := ⟨hx₁, hx₂⟩
  rw [disjoint_iff.mp hdj, Subgroup.mem_bot] at hxm
  exact hx1 (Subtype.ext hxm)

end SingleOrbitAux

variable {G : Type*} [Group G]

theorem singleOrbit_of_isSimple_perfRes [Finite G] {p : ℕ} (hp : p.Prime) {K : Subgroup G}
    (hK : IsSemisimple K) {c : G} (hcK : c ∈ Subgroup.normalizer (K : Set G)) (hcp : c ^ p = 1)
    (hmove : ∀ J ∈ lcal K, c ∉ Subgroup.normalizer (J : Set G))
    (hsimple : IsSimpleGroup ↥(perfRes (K ⊓ Subgroup.centralizer {c}))) :
    (∀ J ∈ lcal K, ∀ J' ∈ lcal K,
      ∃ g ∈ Subgroup.zpowers c, J' = J.map (MulAut.conj g).toMonoidHom) ∧
    K ⊓ Subgroup.centralizer {c} ≤ perfRes (K ⊓ Subgroup.centralizer {c}) := by
  have hKdp : IsDirectProduct (lcal K) K := hK.isDirectProduct_lcal
  have hproj : ∀ J ∈ lcal K, projIn (lcal K) J (K ⊓ Subgroup.centralizer {c}) = J :=
    fun J hJ => Nonsolv.Diag.projIn_inf_centralizer_eq_self hp hKdp hcK hcp hJ (hmove J hJ)
  obtain ⟨P, hP0, hU, hdisj, hdp, hdiag⟩ :=
    exists_partition_isDiagonal hK (inf_le_left : K ⊓ Subgroup.centralizer {c} ≤ K) hproj
  have hblock : ∀ T ∈ P, K ⊓ Subgroup.centralizer {c} ⊓ sSup T =
      perfRes (K ⊓ Subgroup.centralizer {c}) := fun T hT =>
    SingleOrbitAux.inf_sSup_eq_perfRes hK hP0 hU hdp hdiag hsimple hT
  refine ⟨fun J hJ J' hJ' => ?_, ?_⟩
  · obtain ⟨T, hT, hJT⟩ : J ∈ ⋃₀ P := hU ▸ hJ
    obtain ⟨T', hT', hJ'T'⟩ : J' ∈ ⋃₀ P := hU ▸ hJ'
    obtain rfl := SingleOrbitAux.eq_of_inf_sSup_eq_perfRes hK hU hdisj hblock hsimple hT hT'
    have hsame : Nonsolv.Diag.SameBlock (lcal K) (K ⊓ Subgroup.centralizer {c}) J J' :=
      fun y hy => ⟨fun h => Nonsolv.Diag.mem_sSup_diff_of_mem_block hKdp hU hdisj hdp hT
        (hdiag T hT) hJT hJ'T' hy h, fun h => Nonsolv.Diag.mem_sSup_diff_of_mem_block hKdp hU
        hdisj hdp hT (hdiag T hT) hJ'T' hJT hy h⟩
    exact Nonsolv.Diag.mem_conjOrbit_of_sameBlock hp hKdp hcK hcp hJ (hmove J hJ) le_rfl hJ'
      hsame
  · refine le_trans (le_of_eq hdp.sSup_eq.symm) (sSup_le ?_)
    rintro _ ⟨T, hT, rfl⟩
    exact (hblock T hT).le

end CFSG.SignalizerFunctorTheorem.McBride.Near.Sec6S34
