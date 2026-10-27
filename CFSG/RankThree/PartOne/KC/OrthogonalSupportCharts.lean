module

public import CFSG.RankThree.PartOne.KC.OrthogonalAnchoredGeneration
public import CFSG.LocalAnalysis.GLTheoremA.CatA.S172CCentComp
public import CFSG.Permutation.ProperSupportMaps
import CFSG.RankThree.PartOne.KC.OrthogonalNonsingStab

public section

namespace CFSG.RankThree.PartOne.KCOrthogonal

open Module QuadraticMap CFSG.RankThree.Classical2 CFSG.ClassicalGroups.Orthogonal
  CFSG.LocalAnalysis.ComponentInitial

section FinsetSup

variable {K V : Type} [Field K] [AddCommGroup V] [Module K V]
  {Q : QuadraticForm K V} {I : Type} [DecidableEq I]

theorem polarNondegOn_finset_sup (U : I → Submodule K V)
    (hU : ∀ i, PolarNondegOn Q (U i))
    (horth : ∀ i j, i ≠ j → ∀ x ∈ U i, ∀ y ∈ U j, polar Q x y = 0)
    (S : Finset I) : PolarNondegOn Q (S.sup U) := by
  induction S using Finset.induction with
  | empty =>
      rw [Finset.sup_empty]
      intro x hx _
      rw [Submodule.mem_bot] at hx
      rw [hx]
  | insert i s hi ih =>
      rw [Finset.sup_insert]
      refine CFSG.LieType.SeitzGeneration.OrthBlk.polarNondegOn_sup (hU i) ih ?_
      intro x hx y hy
      have hle : s.sup U ≤ suppPerp Q (U i) := by
        refine Finset.sup_le fun j hj => ?_
        intro y hy
        rw [mem_suppPerp]
        intro u hu
        exact horth i j (fun h => hi (h.symm ▸ hj)) u hu y hy
      exact mem_suppPerp.mp (hle hy) x hx

theorem nondegenerate_finset_sup [FiniteDimensional K V] (U : I → Submodule K V)
    (hU : ∀ i, PolarNondegOn Q (U i))
    (horth : ∀ i j, i ≠ j → ∀ x ∈ U i, ∀ y ∈ U j, polar Q x y = 0)
    (S : Finset I) : (polarBilin (Q.comp (S.sup U).subtype)).Nondegenerate :=
  CFSG.RankThree.PartOne.K159.nondegenerate_of_regOn
    (polarNondegOn_finset_sup U hU horth S)

theorem polar_eq_zero_of_mem_finset_sup_disjoint (U : I → Submodule K V)
    (horth : ∀ i j, i ≠ j → ∀ x ∈ U i, ∀ y ∈ U j, polar Q x y = 0)
    {S T : Finset I} (hdisj : Disjoint S T) {x y : V}
    (hx : x ∈ S.sup U) (hy : y ∈ T.sup U) : polar Q x y = 0 := by
  have hSle : ∀ j ∈ T, S.sup U ≤ suppPerp Q (U j) := by
    intro j hj
    refine Finset.sup_le fun i hi => ?_
    intro u hu
    rw [mem_suppPerp]
    intro v hv
    rw [polar_comm]
    exact horth i j (fun h => (Finset.disjoint_left.mp hdisj) hi (h.symm ▸ hj)) u hu v hv
  have hTle : T.sup U ≤ suppPerp Q (Submodule.span K {x}) := by
    refine Finset.sup_le fun j hj => ?_
    intro u hu
    rw [mem_suppPerp]
    intro w hw
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hw
    rw [polar_smul_left_eq, polar_comm, mem_suppPerp.mp ((hSle j hj) hx) u hu, mul_zero]
  exact mem_suppPerp.mp (hTle hy) x (Submodule.subset_span (by simp))

theorem nondegenerate_finset_sup_of_sup [FiniteDimensional K V] (U : I → Submodule K V)
    (W : Submodule K V) (hWreg : (polarBilin (Q.comp W.subtype)).Nondegenerate)
    (hWU : ∀ i, ∀ w ∈ W, ∀ u ∈ U i, polar Q w u = 0)
    (hU : ∀ i, PolarNondegOn Q (U i))
    (horth : ∀ i j, i ≠ j → ∀ x ∈ U i, ∀ y ∈ U j, polar Q x y = 0)
    (S : Finset I) : (polarBilin (Q.comp (W ⊔ S.sup U).subtype)).Nondegenerate := by
  refine CFSG.RankThree.PartOne.K159.nondegenerate_of_regOn ?_
  refine CFSG.LieType.SeitzGeneration.OrthBlk.polarNondegOn_sup
    (polarNondegOn_of_nondegenerate hWreg) (polarNondegOn_finset_sup U hU horth S) ?_
  intro w hw s hs
  have hle : S.sup U ≤ suppPerp Q W := by
    refine Finset.sup_le fun i hi => ?_
    intro u hu
    rw [mem_suppPerp]
    intro w' hw'
    exact hWU i w' hw' u hu
  exact mem_suppPerp.mp (hle hs) w hw

end FinsetSup

section NativeCommutation

variable {K : Type} [Field K] [Finite K] {V : Type} [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] {Q : QuadraticForm K V}

theorem supportedDerived_commute_of_orthogonal_supports [CharP K 2]
    {A B : Submodule K V}
    (hA : (polarBilin (Q.comp A.subtype)).Nondegenerate)
    (hB : (polarBilin (Q.comp B.subtype)).Nondegenerate)
    (horth : ∀ a ∈ A, ∀ b ∈ B, polar Q a b = 0)
    {g e : V ≃ₗ[K] V} (hg : g ∈ supportedDerived Q A) (he : e ∈ supportedDerived Q B) :
    Commute g e := by
  have hApoly : PolarNondegOn Q A := polarNondegOn_of_nondegenerate hA
  have hBpoly : PolarNondegOn Q B := polarNondegOn_of_nondegenerate hB
  have hAperpB : A ≤ suppPerp Q B := by
    intro a ha
    rw [mem_suppPerp]
    intro b hb
    rw [polar_comm]
    exact horth a ha b hb
  have hfixA : ∀ x ∈ A, e x = x := fun x hx =>
    supportedDerived_apply_perp he (hAperpB hx)
  have hpresA : ∀ x ∈ A, g x ∈ A := fun x hx => supportedDerived_apply_mem hg hx
  have hfixAperp : ∀ x ∈ suppPerp Q A, g x = x := fun x hx => supportedDerived_apply_perp hg hx
  have hcomm : e * g = g * e :=
    CFSG.LocalAnalysis.GLTheoremA.S172C.Cent.commute_of_apply_eq hA
      (supportedDerived_le_orthogonalGroup hBpoly he) hfixA hpresA hfixAperp
  exact hcomm.symm

theorem supportedDerived_commute_of_anisotropic_anchor_involution [CharP K 2]
    {W A B : Submodule K V}
    (hW : (polarBilin (Q.comp W.subtype)).Nondegenerate)
    (hWdim : finrank K W = 2)
    (hWaniso : ∀ w ∈ W, Q w = 0 → w = 0)
    (hA : (polarBilin (Q.comp A.subtype)).Nondegenerate)
    (hB : (polarBilin (Q.comp B.subtype)).Nondegenerate)
    (hWA : ∀ w ∈ W, ∀ a ∈ A, polar Q w a = 0)
    (hWB : ∀ w ∈ W, ∀ b ∈ B, polar Q w b = 0)
    (hAB : ∀ a ∈ A, ∀ b ∈ B, polar Q a b = 0)
    {g h : V ≃ₗ[K] V}
    (hg : g ∈ supportedDerived Q (W ⊔ A))
    (hh : h ∈ supportedDerived Q (W ⊔ B))
    (hg2 : g ^ 2 = 1)
    (hcomm : ∀ r ∈ supportedDerived Q W, Commute g r) :
    Commute g h := by
  have hWon : PolarNondegOn Q W := polarNondegOn_of_nondegenerate hW
  have hAon : PolarNondegOn Q A := polarNondegOn_of_nondegenerate hA
  have hBon : PolarNondegOn Q B := polarNondegOn_of_nondegenerate hB
  have hWAon : PolarNondegOn Q (W ⊔ A) :=
    CFSG.LieType.SeitzGeneration.OrthBlk.polarNondegOn_sup hWon hAon hWA
  have hWBon : PolarNondegOn Q (W ⊔ B) :=
    CFSG.LieType.SeitzGeneration.OrthBlk.polarNondegOn_sup hWon hBon hWB
  have hWBreg : (polarBilin (Q.comp (W ⊔ B).subtype)).Nondegenerate :=
    CFSG.RankThree.PartOne.K159.nondegenerate_of_regOn hWBon
  have hgO : g ∈ TauCeti.QuadraticMap.orthogonalGroup Q :=
    supportedDerived_le_orthogonalGroup hWAon hg
  have hgW : ∀ w ∈ W, g w = w :=
    apply_eq_of_involution_commute_supportedDerived_anisotropic_plane
      hW hWdim hWaniso hgO hg2 hcomm
  have hBperp : B ≤ suppPerp Q (W ⊔ A) := by
    intro b hb
    rw [mem_suppPerp]
    intro x hx
    obtain ⟨w, hw, a, ha, rfl⟩ := Submodule.mem_sup.mp hx
    rw [polar_add_left, hWB w hw b hb, hAB a ha b hb, add_zero]
  have hgB : ∀ b ∈ B, g b = b := fun b hb => supportedDerived_apply_perp hg (hBperp hb)
  have hgWB : ∀ x ∈ W ⊔ B, g x = x := by
    intro x hx
    obtain ⟨w, hw, b, hb, rfl⟩ := Submodule.mem_sup.mp hx
    rw [map_add, hgW w hw, hgB b hb]
  have hhWB : ∀ x ∈ W ⊔ B, h x ∈ W ⊔ B := fun x hx => supportedDerived_apply_mem hh hx
  have hhperp : ∀ x ∈ CFSG.LocalAnalysis.GLTheoremA.S172C.Cent.polarPerp Q (W ⊔ B),
      h x = x := fun x hx => supportedDerived_apply_perp hh hx
  exact CFSG.LocalAnalysis.GLTheoremA.S172C.Cent.commute_of_apply_eq hWBreg hgO hgWB hhWB
    hhperp

end NativeCommutation

section SupportIntersection

variable {K : Type*} [Field K] {V : Type*} [AddCommGroup V] [Module K V]
  {Q : QuadraticForm K V}

theorem supportedDerived_apply_mem_of_mem_two_supports
    {W A B : Submodule K V}
    (hA : (polarBilin (Q.comp A.subtype)).Nondegenerate)
    (hWA : ∀ w ∈ W, ∀ a ∈ A, polar Q w a = 0)
    (hAB : ∀ a ∈ A, ∀ b ∈ B, polar Q a b = 0)
    {g : V ≃ₗ[K] V}
    (hgA : g ∈ supportedDerived Q (W ⊔ A))
    (hgB : g ∈ supportedDerived Q (W ⊔ B))
    {w : V} (hw : w ∈ W) :
    g w ∈ W := by
  obtain ⟨w₁, hw₁, a, ha, hwa⟩ :=
    Submodule.mem_sup.mp (supportedDerived_apply_mem hgA (Submodule.mem_sup_left hw))
  obtain ⟨w₂, hw₂, b, hb, hwb⟩ :=
    Submodule.mem_sup.mp (supportedDerived_apply_mem hgB (Submodule.mem_sup_left hw))
  have hzero : ∀ y ∈ A, polar Q a y = 0 := by
    intro y hy
    have hb_y : polar Q b y = 0 := by
      rw [polar_comm]
      exact hAB y hy b hb
    have h3 : polar Q w₁ y + polar Q a y = 0 := by
      rw [← polar_add_left, hwa, ← hwb, polar_add_left]
      simp [hWA w₂ hw₂ y hy, hb_y]
    rwa [hWA w₁ hw₁ y hy, zero_add] at h3
  have ha0 : a = 0 := polarNondegOn_of_nondegenerate hA a ha hzero
  rw [← hwa, ha0, add_zero]
  exact hw₁

theorem supportedDerived_apply_perp_of_mem_two_supports
    [FiniteDimensional K V]
    {W A B : Submodule K V}
    (hA : (polarBilin (Q.comp A.subtype)).Nondegenerate)
    (hWA : ∀ w ∈ W, ∀ a ∈ A, polar Q w a = 0)
    (hAB : ∀ a ∈ A, ∀ b ∈ B, polar Q a b = 0)
    {g : V ≃ₗ[K] V}
    (hgA : g ∈ supportedDerived Q (W ⊔ A))
    (hgB : g ∈ supportedDerived Q (W ⊔ B))
    {x : V} (hx : x ∈ suppPerp Q W) :
    g x = x := by
  have hAon : PolarNondegOn Q A := polarNondegOn_of_nondegenerate hA
  have hfixA : ∀ a ∈ A, g a = a := by
    intro a ha
    refine supportedDerived_apply_perp hgB (mem_suppPerp.mpr ?_)
    intro y hy
    obtain ⟨w, hw, b, hb, rfl⟩ := Submodule.mem_sup.mp hy
    rw [polar_add_left]
    have hba : polar Q b a = 0 := by
      rw [polar_comm]
      exact hAB a ha b hb
    simp [hWA w hw a ha, hba]
  obtain ⟨a, ha, t, ht, rfl⟩ :=
    suppExists_add_of_isCompl (isCompl_suppPerp hAon) x
  have hwt : ∀ w ∈ W, polar Q w t = 0 := by
    intro w hw
    have h := mem_suppPerp.mp hx w hw
    rw [polar_add_right, hWA w hw a ha, zero_add] at h
    exact h
  have htWA : t ∈ suppPerp Q (W ⊔ A) := by
    rw [mem_suppPerp]
    intro y hy
    obtain ⟨w, hw, a', ha', rfl⟩ := Submodule.mem_sup.mp hy
    rw [polar_add_left]
    simp [hwt w hw, mem_suppPerp.mp ht a' ha']
  have hgt : g t = t := supportedDerived_apply_perp hgA htWA
  simpa only [map_add, hfixA a ha, hgt]

end SupportIntersection

section AnchorSupports

variable {K : Type} [Field K] {V : Type} [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] {Q : QuadraticForm K V} {I : Type} [DecidableEq I]

theorem supportedDerived_anchor_mono (U : I → Submodule K V) (W : Submodule K V)
    (hWreg : (polarBilin (Q.comp W.subtype)).Nondegenerate)
    (hWU : ∀ i, ∀ w ∈ W, ∀ u ∈ U i, polar Q w u = 0)
    (hUreg : ∀ i, (polarBilin (Q.comp (U i).subtype)).Nondegenerate)
    (hUorth : ∀ i j, i ≠ j → ∀ x ∈ U i, ∀ y ∈ U j, polar Q x y = 0)
    {R S : Finset I} (hRS : R ⊆ S) :
    supportedDerived Q (W ⊔ R.sup U) ≤ supportedDerived Q (W ⊔ S.sup U) :=
  supportedDerived_le_supportedDerived_of_le
    (by
      rw [sup_le_iff]
      exact ⟨le_sup_left, (Finset.sup_mono hRS).trans le_sup_right⟩)
    (nondegenerate_finset_sup_of_sup U W hWreg hWU
      (fun i => polarNondegOn_of_nondegenerate (hUreg i)) hUorth R)
    (nondegenerate_finset_sup_of_sup U W hWreg hWU
      (fun i => polarNondegOn_of_nondegenerate (hUreg i)) hUorth S)

end AnchorSupports

section AnchoredPairGeneration

variable {K : Type} [Field K] [Finite K] [CharP K 2]
  {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  {Q : QuadraticForm K V} {I : Type} [Fintype I] [DecidableEq I]

theorem supportedDerived_anchor_finset_sup_eq_iSup_pair
    (U : I → Submodule K V) (W : Submodule K V)
    (hWreg : (polarBilin (Q.comp W.subtype)).Nondegenerate)
    (hWdim : finrank K W = 2)
    (hWU : ∀ i, ∀ w ∈ W, ∀ u ∈ U i, polar Q w u = 0)
    (hUreg : ∀ i, (polarBilin (Q.comp (U i).subtype)).Nondegenerate)
    (hUdim : ∀ i, finrank K (U i) = 2)
    (hUorth : ∀ i j, i ≠ j → ∀ u ∈ U i, ∀ v ∈ U j, polar Q u v = 0)
    (S : Finset I) (hS : 2 ≤ S.card) :
    supportedDerived Q (W ⊔ S.sup U) =
      ⨆ P : CFSG.Permutation.ProperSupportMaps.PairBelow S,
        supportedDerived Q (W ⊔ (P : Finset I).sup U) := by
  classical
  let A : Submodule K V := W ⊔ S.sup U
  let k : ℕ := Fintype.card {i : I // i ∈ S}
  let e : {i : I // i ∈ S} ≃ Fin k := Fintype.equivFin _
  let W' : Submodule K A := W.comap A.subtype
  let U' : Fin k → Submodule K A :=
    fun j => (U ((e.symm j : {i : I // i ∈ S}) : I)).comap A.subtype
  have hUpoly : ∀ i, PolarNondegOn Q (U i) := fun i =>
    polarNondegOn_of_nondegenerate (hUreg i)
  have hWA : W ≤ A := le_sup_left
  have hUA : ∀ i ∈ S, U i ≤ A := fun i hi => (Finset.le_sup hi).trans le_sup_right
  have hAreg : (polarBilin (Q.comp A.subtype)).Nondegenerate :=
    nondegenerate_finset_sup_of_sup U W hWreg hWU hUpoly hUorth S
  have hk : 2 ≤ k := by
    change 2 ≤ Fintype.card {i : I // i ∈ S}
    rw [Fintype.card_coe]
    exact hS
  have hW'reg : (polarBilin ((Q.comp A.subtype).comp W'.subtype)).Nondegenerate :=
    nondegenerate_comap_of_le hWA hWreg
  have hW'dim : finrank K W' = 2 := by
    let eW : W' ≃ₗ[K] W := Submodule.comapSubtypeEquivOfLe hWA
    rw [eW.finrank_eq, hWdim]
  have hU'reg : ∀ j : Fin k,
      (polarBilin ((Q.comp A.subtype).comp (U' j).subtype)).Nondegenerate := fun j =>
    nondegenerate_comap_of_le
      (hUA ((e.symm j : {i : I // i ∈ S}) : I) (e.symm j).2)
      (hUreg ((e.symm j : {i : I // i ∈ S}) : I))
  have hU'dim : ∀ j : Fin k, finrank K (U' j) = 2 := by
    intro j
    let ej : U' j ≃ₗ[K] U ((e.symm j : {i : I // i ∈ S}) : I) :=
      Submodule.comapSubtypeEquivOfLe
        (hUA ((e.symm j : {i : I // i ∈ S}) : I) (e.symm j).2)
    rw [ej.finrank_eq, hUdim _]
  have hWU' : ∀ j : Fin k,
      CFSG.LieType.SeitzGeneration.OrthBlk.OrthSep (Q.comp A.subtype) W' (U' j) := by
    intro j x hx y hy
    exact hWU ((e.symm j : {i : I // i ∈ S}) : I) x
      (Submodule.mem_comap.mp hx) y (Submodule.mem_comap.mp hy)
  have hU'orth : ∀ i j : Fin k, i ≠ j →
      CFSG.LieType.SeitzGeneration.OrthBlk.OrthSep (Q.comp A.subtype) (U' i) (U' j) := by
    intro i j hij x hx y hy
    exact hUorth ((e.symm i : {i : I // i ∈ S}) : I)
      ((e.symm j : {i : I // i ∈ S}) : I)
      (fun h => hij (e.symm.injective (Subtype.ext h)))
      x (Submodule.mem_comap.mp hx) y (Submodule.mem_comap.mp hy)
  have hreindex : (⨆ j : Fin k, U ((e.symm j : {i : I // i ∈ S}) : I)) = S.sup U := by
    apply le_antisymm
    · refine iSup_le fun j => ?_
      exact Finset.le_sup (e.symm j).2
    · refine Finset.sup_le fun i hi => ?_
      let j : Fin k := e ⟨i, hi⟩
      have hji : ((e.symm j : {i : I // i ∈ S}) : I) = i := by simp [j]
      rw [← hji]
      exact le_iSup (fun j : Fin k => U ((e.symm j : {i : I // i ∈ S}) : I)) j
  have hmapW : W'.map A.subtype = W := by
    rw [Submodule.map_comap_subtype, inf_eq_right.mpr hWA]
  have hmapU : ∀ j : Fin k,
      (U' j).map A.subtype = U ((e.symm j : {i : I // i ∈ S}) : I) := fun j => by
    rw [Submodule.map_comap_subtype,
      inf_eq_right.mpr (hUA ((e.symm j : {i : I // i ∈ S}) : I) (e.symm j).2)]
  have hspan : W' ⊔ ⨆ j : Fin k, U' j = ⊤ := by
    apply Submodule.map_injective_of_injective A.subtype_injective
    rw [Submodule.map_sup, Submodule.map_iSup, Submodule.map_top, Submodule.range_subtype,
      hmapW]
    have hIU : (⨆ j : Fin k, (U' j).map A.subtype) = S.sup U := by
      rw [show (⨆ j : Fin k, (U' j).map A.subtype) =
          ⨆ j : Fin k, U ((e.symm j : {i : I // i ∈ S}) : I) from iSup_congr hmapU]
      exact hreindex
    rw [hIU]
  let P : Fin k → Fin k → Finset I := fun i j =>
    {((e.symm i : {i : I // i ∈ S}) : I), ((e.symm j : {i : I // i ∈ S}) : I)}
  have hPsub : ∀ i j, P i j ⊆ S := by
    intro i j x hx
    simp only [P, Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl
    · exact (e.symm i).2
    · exact (e.symm j).2
  have hPcard : ∀ i j, i ≠ j → (P i j).card = 2 := by
    intro i j hij
    have hne : ((e.symm i : {i : I // i ∈ S}) : I) ≠
        ((e.symm j : {i : I // i ∈ S}) : I) := by
      intro h
      exact hij (e.symm.injective (Subtype.ext h))
    simpa only [P] using Finset.card_pair hne
  have hPsupW : ∀ i j : Fin k,
      W ⊔ (P i j).sup U = W ⊔ U ((e.symm i : {i : I // i ∈ S}) : I) ⊔
        U ((e.symm j : {i : I // i ∈ S}) : I) := by
    intro i j
    simp only [P, Finset.sup_insert, Finset.sup_singleton]
    ac_rfl
  have hPle : ∀ i j, W ⊔ (P i j).sup U ≤ A := fun i j =>
    sup_le hWA (Finset.sup_le fun x hx => hUA x (hPsub i j hx))
  have hmapP : ∀ i j,
      ((W ⊔ (P i j).sup U).comap A.subtype).map A.subtype =
        W ⊔ (P i j).sup U := by
    intro i j
    rw [Submodule.map_comap_subtype, inf_eq_right.mpr (hPle i j)]
  have hpiece : ∀ i j : Fin k,
      W' ⊔ U' i ⊔ U' j = (W ⊔ (P i j).sup U).comap A.subtype := by
    intro i j
    apply Submodule.map_injective_of_injective A.subtype_injective
    rw [Submodule.map_sup, Submodule.map_sup, hmapW, hmapU i, hmapU j, hmapP i j]
    exact (hPsupW i j).symm
  have hgenA := orthDerived_eq_iSup_anchored_pairs (Q := Q.comp A.subtype) (W := W')
    (U := U') hk hW'reg hW'dim hU'reg hU'dim hWU' hU'orth hspan
  let ext := orthExtend (isCompl_suppPerp (polarNondegOn_of_nondegenerate hAreg))
  have hmap := congrArg (Subgroup.map ext) hgenA
  rw [map_orthDerived_orthExtend_eq_supportedDerived_of_regular hAreg] at hmap
  rw [Subgroup.map_iSup] at hmap
  simp_rw [Subgroup.map_iSup] at hmap
  have hmapTerm : ∀ (i j : Fin k) (hij : i ≠ j),
      (supportedDerived (Q.comp A.subtype) (W' ⊔ U' i ⊔ U' j)).map ext =
        supportedDerived Q (W ⊔ (P i j).sup U) := by
    intro i j hij
    rw [hpiece i j]
    exact map_supportedDerived_comap_subtype_eq_supportedDerived
      (A := W ⊔ (P i j).sup U) (B := A) (hPle i j)
      (nondegenerate_finset_sup_of_sup U W hWreg hWU hUpoly hUorth (P i j)) hAreg
  have hmapFinal : supportedDerived Q A =
      ⨆ (i : Fin k) (j : Fin k) (_ : i ≠ j),
        supportedDerived Q (W ⊔ (P i j).sup U) := by
    refine hmap.trans ?_
    apply iSup_congr; intro i
    apply iSup_congr; intro j
    apply iSup_congr; intro hij
    exact hmapTerm i j hij
  refine le_antisymm ?_ ?_
  · change supportedDerived Q A ≤ _
    rw [hmapFinal]
    refine iSup_le fun i => iSup_le fun j => iSup_le fun hij => ?_
    exact le_iSup (fun P : CFSG.Permutation.ProperSupportMaps.PairBelow S =>
      supportedDerived Q (W ⊔ (P : Finset I).sup U))
      ⟨P i j, hPsub i j, hPcard i j hij⟩
  · change _ ≤ supportedDerived Q A
    refine iSup_le fun P => ?_
    exact supportedDerived_anchor_mono U W hWreg hWU hUreg hUorth P.2.1

end AnchoredPairGeneration

end CFSG.RankThree.PartOne.KCOrthogonal
