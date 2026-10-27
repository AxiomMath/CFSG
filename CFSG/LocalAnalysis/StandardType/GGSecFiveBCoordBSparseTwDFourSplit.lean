module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveBCoordBSparseTwDFourSplitDefs
public import CFSG.LocalAnalysis.StandardType.GGSecFiveBCoordBDenseDefs
public import CFSG.LocalAnalysis.StandardType.GGTPNNarrow
public import CFSG.LocalAnalysis.StandardType.GGForkA8NotRefl
public import CFSG.LocalAnalysis.StandardType.GGSecFiveBJoinDefs
public import CFSG.RankThree.PartOne.KC.OrthogonalSplitCompletion
public import CFSG.LocalAnalysis.StandardType.GGSecFiveBPermSpPlaneFrameDefs

import CFSG.RankThree.PartOne.KC.OrthogonalSplitFar
import CFSG.LocalAnalysis.StandardType.GGSecFiveBCoordBSparseOrthCharts
import CFSG.Adapters.SpecialLinearPerfect
import CFSG.LocalAnalysis.StandardType.GGTBJOrthLeft
import CFSG.LocalAnalysis.StandardType.GGTBJOrthNbr
import CFSG.LocalAnalysis.StandardType.GGSecFiveBCoordBSparseSp
import CFSG.LocalAnalysis.StandardType.GGSecFiveBCoordBSparseEndpoint
import CFSG.LocalAnalysis.StandardType.GGSecFiveBNbrAxis
import CFSG.LocalAnalysis.StandardType.GGSecFiveBCoordBDenseRows
import CFSG.LocalAnalysis.StandardType.GGSecFiveBCoordBSpSp
import CFSG.LocalAnalysis.StandardType.GGQuadMinusSpinCover
import CFSG.ClassicalGroups.Orthogonal.IsometryConj
import CFSG.RankThree.PartOne.S10.EmbeddingTransport
import CFSG.LocalAnalysis.StandardType.GGSecFiveBCoordBSparseTwDFourCrossing

public section

namespace CFSG.StandardType

section ChartAlgebra

open CFSG.RankThree.PartOne.KCOrthogonal
open CFSG.RankThree.Classical2 (orthDerived)
open CFSG.LieType.Universal.Spin

variable {G F : Type} [Group G] [Finite G] [Field F] [Finite F] [CharP F 2] {b c : F}

theorem exists_injective_split_completion_of_node_crossing (r : ℕ) (hr : 3 ≤ r)
    (hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0) (hcard : 2 < Nat.card F)
    (a : chartSubgroup (n := r + 2) (F := F) (b := b) (c := c) (deletionPlanes r) →* G)
    (k : chartSubgroup (n := r + 2) (F := F) (b := b) (c := c)
      (Finset.univ.erase (⟨3, by omega⟩ : Fin (r + 1))) →* G)
    (ha : Function.Injective a)
    (hcoh : ∀ x : chartSubgroup (n := r + 2) (F := F) (b := b) (c := c)
        (deletionPlanes r ∩ Finset.univ.erase (⟨3, by omega⟩ : Fin (r + 1))),
      a (Subgroup.inclusion (chartSubgroup_mono (n := r + 2) (F := F) (b := b) (c := c) hirr
          Finset.inter_subset_left) x) =
        k (Subgroup.inclusion (chartSubgroup_mono (n := r + 2) (F := F) (b := b) (c := c) hirr
          Finset.inter_subset_right) x))
    (hcross : ∀ (x : chartSubgroup (n := r + 2) (F := F) (b := b) (c := c)
        (Finset.univ.erase (⟨3, by omega⟩ : Fin (r + 1))))
      (y : chartSubgroup (n := r + 2) (F := F) (b := b) (c := c) (deletionPlanes r)),
      (x : orthDerived (quadMinus (r + 2) F b c)) ∈
          nodeOmega (F := F) (b := b) (c := c) r (by omega) hirr ⟨0, by omega⟩ →
        (y : orthDerived (quadMinus (r + 2) F b c)) ∈
          chartSubgroup (n := r + 2) (F := F) (b := b) (c := c)
            ({⟨2, by omega⟩, ⟨3, by omega⟩} : Finset (Fin (r + 1))) →
        Commute (k x) (a y)) :
    ∃ Φ : orthDerived (quadMinus (r + 2) F b c) →* G,
      Function.Injective Φ ∧ Φ.range = a.range ⊔ k.range := by
  classical
  let u : Fin (r + 1) := ⟨3, by omega⟩
  let v : Fin (r + 1) := ⟨2, by omega⟩
  let cc : Fin (r + 1) := ⟨1, by omega⟩
  have huv : u ≠ v := Fin.ne_of_val_ne (by simp [u, v])
  have hcu : cc ≠ u := Fin.ne_of_val_ne (by simp [u, cc])
  have hcv : cc ≠ v := Fin.ne_of_val_ne (by simp [v, cc])
  have h0u : (0 : Fin (r + 1)) ≠ u := Fin.ne_of_val_ne (by simp [u])
  have h0v : (0 : Fin (r + 1)) ≠ v := Fin.ne_of_val_ne (by simp [v])
  have hcc0 : cc ≠ 0 := Fin.ne_of_val_ne (by simp [cc])
  have hswap : splitMinusRhoOfTwoLe (r := r) (F := F) (b := b) (c := c) hirr (by omega)
      (Equiv.swap cc 0) ∈
        nodeOmega (F := F) (b := b) (c := c) r (by omega) hirr ⟨0, by omega⟩ := by
    rw [Equiv.swap_comm]
    exact splitMinusRhoOfTwoLe_swap_mem_nodeOmega (F := F) (b := b) (c := c) r (by omega) hirr
      (k := ⟨0, by omega⟩) (by simp only; omega)
  obtain ⟨t, hRestrL, hRestrK, hcrossT, hrangeT⟩ :=
    exists_permHom_of_coherent_sparse_split_charts_of_three_le (F := F) (b := b) (c := c)
      hr hirr hcard huv hcu hcv h0u h0v hcc0 a k hcoh (fun _ x => hcross _ _ hswap
        (chartSubgroup_mono (n := r + 2) (F := F) (b := b) (c := c) hirr
          (Finset.subset_of_eq (Finset.pair_comm u v)) x.2))
  obtain ⟨σ, hσ0, hσ1, hfar⟩ :=
    far_of_two_charts (F := F) (b := b) (c := c) r hr hirr hcard a k t hRestrL hRestrK hcoh
      (fun x y hx hy => hcross x y hx
        (nodeOmega_le_chartSubgroup (F := F) (b := b) (c := c) r (by omega) hirr hcard
          ⟨2, by omega⟩ (fun i hi => by
            rcases mem_totalCoords_singleton (n := r + 2) hi with h | h
            · rw [h]
              exact Finset.mem_insert_self _ _
            · rw [show i = ⟨3, by omega⟩ from Fin.ext h]
              exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)) hy))
  obtain ⟨Φ, ⟨haΦ, htΦ⟩, -⟩ :=
    existsUnique_extends_deletion_and_permutation_of_three_le (F := F) (b := b) (c := c)
      r hr hirr hcard a t huv hcu hcv h0u h0v hcc0 hRestrL hcrossT (Or.inr ⟨σ, hσ0, hσ1, hfar⟩)
  obtain ⟨hΦinj, hΦrange⟩ :=
    injective_range_of_injective_a_of_three_le (F := F) (b := b) (c := c)
      r hr hirr hcard a t huv hcu hcv h0u h0v hcc0 hRestrL hcrossT (Or.inr ⟨σ, hσ0, hσ1, hfar⟩)
      ha haΦ htΦ
  exact ⟨Φ, hΦinj, hΦrange.trans hrangeT⟩

theorem isPerfect_nodeOmega (r : ℕ) (hr : 2 ≤ r) (hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0)
    (hF : 4 ≤ Nat.card F) {k : Fin (r + 1)} (hk : k.val + 1 < r + 1) :
    Group.IsPerfect ↥(nodeOmega (F := F) (b := b) (c := c) r hr hirr k) := by
  have hk' : k.val + 1 < r + 2 - 1 := by omega
  have : Group.IsPerfect (Matrix.SpecialLinearGroup (Fin 2) F) :=
    CFSG.ClassicalModels.specialLinear_isPerfect_two_of_four_le_card F hF
  have := Group.IsPerfect.range (CFSG.ClassicalInvolution.WeakCT.rLong (r + 2) b c hk')
  unfold nodeOmega
  rw [CFSG.ClassicalInvolution.WeakCT.rankOne_minusDatum_long hirr hk']
  exact Group.IsPerfect.map _

omit [Finite G] in
theorem node_crossing_of_pairCrossing (r : ℕ) (hr : 3 ≤ r)
    (hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0) (hF : 4 ≤ Nat.card F) {p : ℕ}
    (Bs : Subgroup G) (eta : ↥Bs ≃* (Fin (r + 1) → Multiplicative (ZMod p)))
    (ell : Equiv.Perm (Fin (r + 1)))
    (a : chartSubgroup (n := r + 2) (F := F) (b := b) (c := c) (deletionPlanes r) →* G)
    (k : chartSubgroup (n := r + 2) (F := F) (b := b) (c := c)
      (Finset.univ.erase (⟨3, by omega⟩ : Fin (r + 1))) →* G)
    (hk : Function.Injective k)
    (hmarkL : ∀ S : Finset (Fin (r + 1)), S.Nonempty → S.card ≤ 2 → S ⊆ deletionPlanes r →
      ((chartSubgroup (n := r + 2) (F := F) (b := b) (c := c) S).subgroupOf
        (chartSubgroup (n := r + 2) (F := F) (b := b) (c := c) (deletionPlanes r))).map a =
        ggBlockComm Bs eta (ell '' (S : Set (Fin (r + 1)))))
    (hmarkK : ∀ S : Finset (Fin (r + 1)), S.Nonempty → S.card ≤ 2 →
      S ⊆ Finset.univ.erase (⟨3, by omega⟩ : Fin (r + 1)) →
      ((chartSubgroup (n := r + 2) (F := F) (b := b) (c := c) S).subgroupOf
        (chartSubgroup (n := r + 2) (F := F) (b := b) (c := c)
          (Finset.univ.erase (⟨3, by omega⟩ : Fin (r + 1))))).map k =
        ggBlockComm Bs eta (ell '' (S : Set (Fin (r + 1)))))
    (hO2 : ∀ i j i' j' : Fin (r + 1), i ≠ j → i' ≠ j' → i ≠ i' → i ≠ j' → j ≠ i' → j ≠ j' →
      ∀ P : Subgroup G, Group.IsPerfect P → P ≤ ggBlockComm Bs eta {i, j} →
        P ≤ Subgroup.centralizer
          ((ggBlockComm Bs eta {i} ⊓ ggBlockComm Bs eta {j} : Subgroup G) : Set G) →
        ∀ z ∈ P, ∀ w ∈ ggBlockComm Bs eta {i', j'}, Commute z w) :
    ∀ (x : chartSubgroup (n := r + 2) (F := F) (b := b) (c := c)
        (Finset.univ.erase (⟨3, by omega⟩ : Fin (r + 1))))
      (y : chartSubgroup (n := r + 2) (F := F) (b := b) (c := c) (deletionPlanes r)),
      (x : orthDerived (quadMinus (r + 2) F b c)) ∈
          nodeOmega (F := F) (b := b) (c := c) r (by omega) hirr ⟨0, by omega⟩ →
        (y : orthDerived (quadMinus (r + 2) F b c)) ∈
          chartSubgroup (n := r + 2) (F := F) (b := b) (c := c)
            ({⟨2, by omega⟩, ⟨3, by omega⟩} : Finset (Fin (r + 1))) →
        Commute (k x) (a y) := by
  classical
  intro x y hx hy
  let i0 : Fin (r + 1) := ⟨0, by omega⟩
  let i1 : Fin (r + 1) := ⟨1, by omega⟩
  let i2 : Fin (r + 1) := ⟨2, by omega⟩
  let i3 : Fin (r + 1) := ⟨3, by omega⟩
  let D3 : Finset (Fin (r + 1)) := Finset.univ.erase i3
  have hcard : 2 < Nat.card F := by omega
  have h01 : i0 ≠ i1 := Fin.ne_of_val_ne (by simp [i0, i1])
  have h23 : i2 ≠ i3 := Fin.ne_of_val_ne (by simp [i2, i3])
  have h02 : i0 ≠ i2 := Fin.ne_of_val_ne (by simp [i0, i2])
  have h03 : i0 ≠ i3 := Fin.ne_of_val_ne (by simp [i0, i3])
  have h12 : i1 ≠ i2 := Fin.ne_of_val_ne (by simp [i1, i2])
  have h13 : i1 ≠ i3 := Fin.ne_of_val_ne (by simp [i1, i3])
  let N : Subgroup (orthDerived (quadMinus (r + 2) F b c)) :=
    nodeOmega (F := F) (b := b) (c := c) r (by omega) hirr i0
  have hN01 : N ≤ chartSubgroup (n := r + 2) (F := F) (b := b) (c := c) {i0, i1} :=
    nodeOmega_le_chartSubgroup (F := F) (b := b) (c := c) r (by omega) hirr hcard i0
      (fun i hi => by
        rcases mem_totalCoords_singleton (n := r + 2) hi with h | h
        · rw [h]
          exact Finset.mem_insert_self _ _
        · rw [show i = i1 from Fin.ext h]
          exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _))
  have h01D3 : ({i0, i1} : Finset (Fin (r + 1))) ⊆ D3 := by
    intro i hi
    rcases Finset.mem_insert.mp hi with rfl | hi
    · exact Finset.mem_erase.mpr ⟨h03, Finset.mem_univ _⟩
    · rw [Finset.mem_singleton.mp hi]
      exact Finset.mem_erase.mpr ⟨h13, Finset.mem_univ _⟩
  let P : Subgroup G := (N.subgroupOf
    (chartSubgroup (n := r + 2) (F := F) (b := b) (c := c) D3)).map k
  have hNle : N ≤ chartSubgroup (n := r + 2) (F := F) (b := b) (c := c) D3 :=
    hN01.trans (chartSubgroup_mono (F := F) (b := b) (c := c) hirr h01D3)
  have hPperf : Group.IsPerfect P := by
    have : Group.IsPerfect ↥N :=
      isPerfect_nodeOmega (F := F) (b := b) (c := c) r (by omega) hirr hF (by simp [i0]; omega)
    have : Group.IsPerfect ↥(N.subgroupOf
        (chartSubgroup (n := r + 2) (F := F) (b := b) (c := c) D3)) :=
      Group.IsPerfect.ofSurjective (f := (Subgroup.subgroupOfEquivOfLe hNle).symm.toMonoidHom)
        (Subgroup.subgroupOfEquivOfLe hNle).symm.surjective
    exact Group.IsPerfect.map k
  have hPM : P ≤ ggBlockComm Bs eta {ell i0, ell i1} := by
    have hmark := hmarkK {i0, i1} (Finset.insert_nonempty _ _)
      (Finset.card_le_two) h01D3
    rw [Finset.coe_pair, Set.image_pair] at hmark
    rw [← hmark]
    refine Subgroup.map_mono ?_
    intro z hz
    exact Subgroup.mem_subgroupOf.mpr (hN01 (Subgroup.mem_subgroupOf.mp hz))
  have hPC : P ≤ Subgroup.centralizer
      ((ggBlockComm Bs eta {ell i0} ⊓ ggBlockComm Bs eta {ell i1} : Subgroup G) : Set G) := by
    have hD2 := map_chartPure_pair_le_inf_centralizer (F := F) (b := b) (c := c) r (by omega) hirr
      (D := D3) (i := i0) (j := i1) (Finset.mem_erase.mpr ⟨h03, Finset.mem_univ _⟩)
      (Finset.mem_erase.mpr ⟨h13, Finset.mem_univ _⟩) h01 k hk
      (Y := fun S => ggBlockComm Bs eta (ell '' (S : Set (Fin (r + 1))))) hmarkK
    have hNP : N ≤ chartPure (n := r + 2) (F := F) (b := b) (c := c) {i0, i1} :=
      nodeOmega_le_chartPure (F := F) (b := b) (c := c) r (by omega) hirr hcard (k := i0)
        (by simp only [i0]; omega)
    intro z hz
    have hz' : z ∈ ((chartPure (n := r + 2) (F := F) (b := b) (c := c) {i0, i1}).subgroupOf
        (chartSubgroup (n := r + 2) (F := F) (b := b) (c := c) D3)).map k := by
      obtain ⟨w, hw, rfl⟩ := Subgroup.mem_map.mp hz
      exact Subgroup.mem_map_of_mem k
        (Subgroup.mem_subgroupOf.mpr (hNP (Subgroup.mem_subgroupOf.mp hw)))
    simpa only [Finset.coe_singleton, Set.image_singleton] using (Subgroup.mem_inf.mp (hD2 hz')).2
  have hy23 : a y ∈ ggBlockComm Bs eta {ell i2, ell i3} := by
    have h23D0 : ({i2, i3} : Finset (Fin (r + 1))) ⊆ deletionPlanes r := by
      intro i hi
      rcases Finset.mem_insert.mp hi with rfl | hi
      · exact Finset.mem_erase.mpr ⟨h02.symm, Finset.mem_univ _⟩
      · rw [Finset.mem_singleton.mp hi]
        exact Finset.mem_erase.mpr ⟨h03.symm, Finset.mem_univ _⟩
    have hmark := hmarkL {i2, i3} (Finset.insert_nonempty _ _) (Finset.card_le_two) h23D0
    rw [Finset.coe_pair, Set.image_pair] at hmark
    rw [← hmark]
    exact Subgroup.mem_map_of_mem a (Subgroup.mem_subgroupOf.mpr hy)
  have hinj := ell.injective
  exact hO2 (ell i0) (ell i1) (ell i2) (ell i3) (hinj.ne h01) (hinj.ne h23) (hinj.ne h02)
    (hinj.ne h03) (hinj.ne h12) (hinj.ne h13) P hPperf hPM hPC (k x)
    (Subgroup.mem_map_of_mem k (Subgroup.mem_subgroupOf.mpr hx)) (a y) hy23

end ChartAlgebra

section Label

open CFSG.Assembly

private theorem exists_exact_twD_label_of_split_four
    {G : Type} [Group G] {n p : ℕ} {Bs L : Subgroup G}
    (hLab : GGInnerDiagOnLabel
      (fun p lab => GGSecFiveBCoordBLabel n p lab ∧
        (n = 4 ∧ lab.n ≠ 1 ∧ lab.tag = .twD ∧ p ∣ 2 ^ lab.n - 1)) p Bs L) :
    ∃ f : ℕ, n = 4 ∧ 2 ≤ f ∧ p ∣ 2 ^ f - 1 ∧
      GGInnerDiagOnLabel
        (fun p lab => lab = ⟨.twD, n, f⟩ ∧ GGTBRowR5O1 p lab) p Bs L := by
  obtain ⟨lab, hΛ, hPred, hHas, hKeep⟩ := GGInnerDiagOnLabel.exists_label_eq hLab
  have hBL : GGSecFiveBCoordBLabel n p lab := hPred.1
  have h4 : n = 4 := hPred.2.1
  have hf1 : lab.n ≠ 1 := hPred.2.2.1
  have htag : lab.tag = .twD := hPred.2.2.2.1
  have hpd : p ∣ 2 ^ lab.n - 1 := hPred.2.2.2.2
  rcases lab with ⟨tag, rank, f⟩
  simp only [GGSecFiveBCoordBLabel] at hBL
  rcases hBL with ⟨hBC, -, -⟩ | ⟨hTw, hrank, -⟩ | ⟨hD, -, -⟩ | ⟨hA, -, -⟩
  · rcases hBC with h | h
    · rw [h] at htag
      cases htag
    · rw [h] at htag
      cases htag
  · have hf1' : 1 ≤ f := by simpa using hΛ.1
    have hf : 2 ≤ f := Nat.succ_le_of_lt (Nat.lt_of_le_of_ne hf1' (Ne.symm hf1))
    have hlab_eq : (⟨tag, rank, f⟩ : LargeEvenLabel) = ⟨.twD, n, f⟩ := by rw [hTw, hrank]
    rw [hlab_eq] at hKeep
    refine ⟨f, h4, hf, hpd, ?_⟩
    refine largeEvenMarking_mono (fun lab' R _ I F θ hP => ?_) hKeep
    exact ⟨⟨hP.1.2, by
      rw [hP.1.2]
      exact ⟨rfl, by change 4 ≤ n; omega, Or.inl hpd⟩⟩, hP.2⟩
  · rw [hD] at htag
    cases htag
  · rw [hA] at htag
    cases htag

theorem pairCrossing_of_perfectResidual {G : Type} [Group G] [Finite G] {n p : ℕ}
    (Bs : Subgroup G) (eta : ↥Bs ≃* (Fin n → Multiplicative (ZMod p)))
    (hZ : ∀ i j i' j' : Fin n, i ≠ j → i' ≠ j' → i ≠ i' → i ≠ j' → j ≠ i' → j ≠ j' →
      ∀ z ∈ CFSG.inSubgroup CFSG.perfectResidual (ggBlockComm Bs eta {i, j} ⊓
          Subgroup.centralizer
            ((ggBlockComm Bs eta {i} ⊓ ggBlockComm Bs eta {j} : Subgroup G) : Set G)),
        ∀ w ∈ ggBlockComm Bs eta {i', j'}, Commute z w) :
    ∀ i j i' j' : Fin n, i ≠ j → i' ≠ j' → i ≠ i' → i ≠ j' → j ≠ i' → j ≠ j' →
      ∀ P : Subgroup G, Group.IsPerfect P → P ≤ ggBlockComm Bs eta {i, j} →
        P ≤ Subgroup.centralizer
          ((ggBlockComm Bs eta {i} ⊓ ggBlockComm Bs eta {j} : Subgroup G) : Set G) →
        ∀ z ∈ P, ∀ w ∈ ggBlockComm Bs eta {i', j'}, Commute z w := by
  intro i j i' j' h1 h2 h3 h4 h5 h6 P hP hPM hPC z hz w hw
  exact hZ i j i' j' h1 h2 h3 h4 h5 h6 z
    (CFSG.RankThree.PartOne.EmbeddingTransport.le_inSubgroup_perfectResidual_of_isPerfect
      (le_inf hPM hPC) hP hz) w hw

end Label

section Inputs

open CFSG.Assembly
open CFSG.RankThree.PartOne.KCOrthogonal
open CFSG.RankThree.Classical2 (orthDerived)
open CFSG.LieType.Universal.Spin
open CFSG.ClassicalGroups.Orthogonal

theorem ggSecFiveData_of_split_four_pairCrossing
    (hX : GGResXDichotomyInput) (hTCJ : GGTCJKnown) (hRig : GGLabelRigidInput)
    (hTPn : GGNbrTablePNbrInputNarrow) (hA8 : GGForkA8NotReflInput) (hraw : GGRawInnFieldInput)
    (hiso : GGRawInndiagIsoInput) (hFC : GGResNbrFixCentralizesInput) (hBJ : BMaxJoinInput)
    {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    {𝒦 : Finset (Subgroup G)} (hR : GGSecFiveRouteCfg p B Bs x L D J 𝒦) {n : ℕ}
    (e : (CoxeterMatrix.B n).Group ≃* ↥(ggAutomizerJoin L Bs 𝒦))
    (hP : GGCoxeterPres p (ggAutomizerJoin L Bs 𝒦) (CoxeterMatrix.B n) e)
    (eta : ↥Bs ≃* (Fin n → Multiplicative (ZMod p))) (i0 : Fin n)
    (h𝒦 : (ggAutomizerJoin L Bs 𝒦).map (MulAut.congr eta).toMonoidHom = bSignedFull n p)
    (hL : (ggAutomizer L Bs).map (MulAut.congr eta).toMonoidHom = bCoordinateBlock n p i0)
    (hLab : GGInnerDiagOnLabel (fun p lab => GGSecFiveBCoordBLabel n p lab ∧
      (n = 4 ∧ lab.n ≠ 1 ∧ lab.tag = .twD ∧ p ∣ 2 ^ lab.n - 1)) p Bs L)
    (hB : B = Bs)
    (hRM : ∀ (y : G) (K : Subgroup G), GGNbr p B x D J y K →
      ggAutomizer K Bs ≤ ggAutomizerJoin L Bs 𝒦)
    (hDense : ¬ ∃ K : Subgroup G, GGSecFiveBCoordBDenseNbr p Bs 𝒦 n eta K)
    (hO2 : ∀ i j i' j' : Fin n, i ≠ j → i' ≠ j' → i ≠ i' → i ≠ j' → j ≠ i' → j ≠ j' →
      ∀ P : Subgroup G, Group.IsPerfect P → P ≤ ggBlockComm Bs eta {i, j} →
        P ≤ Subgroup.centralizer
          ((ggBlockComm Bs eta {i} ⊓ ggBlockComm Bs eta {j} : Subgroup G) : Set G) →
        ∀ z ∈ P, ∀ w ∈ ggBlockComm Bs eta {i', j'}, Commute z w) :
    GGSecFiveData p B x L D J := by
  classical
  obtain ⟨f, h4, hf, hpd, hLexact⟩ := exists_exact_twD_label_of_split_four hLab
  obtain ⟨r, rfl⟩ : ∃ r, n = r + 1 := ⟨n - 1, by omega⟩
  have hr : 3 ≤ r := by omega
  obtain ⟨hp, hp2⟩ := ggRouteCfg_prime hR
  have : Fact p.Prime := ⟨hp⟩
  have hcfg : GGConfig p B Bs x L D J := hR.1.1
  obtain ⟨K, hKmem, hKL⟩ :=
    exists_mem_not_le_ggAutomizer_of_bSignedFull hp hp2 eta h𝒦 hL
  obtain ⟨y, hnb⟩ := hR.2.2.2.1.2 K hKmem
  have hy : y ∈ Bs := hB ▸ hnb.1.2.1
  rcases hR.nbr_axis_or_dense hX hTCJ hRig hTPn hA8 hraw hiso hFC hB (by omega) eta h𝒦 hL
    hnb (hRM y K hnb) hKL hy with ⟨j, hj, hblk, haxis⟩ | ⟨⟨δ, hδ, hKδ⟩, -⟩
  swap
  · exact (hDense ⟨K, hKmem, δ, hδ, hKδ⟩).elim
  obtain ⟨w, hw, hact0, hKeq, hAK⟩ :=
    hR.exists_eq_map_conj_swap_of_sparse hB (by omega) eta i0 h𝒦 hL hy hnb hj haxis hblk
  have hLK : ggG0 p B x L D J = L ⊔ K :=
    ggG0_eq_sup_of_bCoordinateBlocks hBJ hR e hP (by omega) h𝒦 hL hRM hKmem hj hAK
  have hyj : eta ⟨y, hcfg.2.1.1 hnb.1.2.1⟩ j ≠ 1 := by
    intro h1
    have hfun : eta ⟨y, hcfg.2.1.1 hnb.1.2.1⟩ = 1 := by
      funext k
      by_cases hk : k = j
      · subst hk
        exact h1
      · exact haxis k hk
    have hy1 : (⟨y, hcfg.2.1.1 hnb.1.2.1⟩ : ↥Bs) = 1 := by
      apply eta.injective
      rw [hfun, map_one]
    exact hnb.1.2.2.1 (by simpa using congrArg Subtype.val hy1)
  obtain ⟨F, fieldF, finiteF, charF, b, c, hFcard, hirr, θ, hBsN, E, Δ, hE, σ, ΘA, Θ,
    hψσ, hΘA, hΘ, hcoord, hAut, hW, hrest⟩ :=
    ggTBJOrthLeft_nativeModel_of_twD (n := r + 1) (f := f) hcfg hB.symm
      (by omega) hf hL hLexact
  obtain ⟨⟨hminus, hdim, hrow⟩, hZL, hfin⟩ := hrest
  obtain ⟨χ, κ, hχraw, hχτ, hκτ, hκinj, hκrange, hHmap, hJmap⟩ := hfin
  let _ : Field F := fieldF
  let _ : Finite F := finiteF
  have : CharP F 2 := charF
  have hQ : (QuadraticMap.polarBilin (TableBOrth.qMinusForm F r b c)).Nondegenerate :=
    TableBOrth.nondegenerate_qMinusForm r hirr
  have hsplit : p ∣ Nat.card F - 1 := by
    rw [hFcard]
    exact hpd
  obtain ⟨eL, a, ell, hainj, harange, hfac, hell0, hdict, hmarkL, hJchart⟩ :=
    OrthTorus.ggTBJOrthLeft_exists_markedDeletionChart_of_sparse
      (r := r) (R := OrthRest.RMinus F r b c) (eR := OrthTorus.rMinusEquiv F r b c)
      (hcfg := hcfg) (hnb := hnb) (hBsB := hB.symm) (hr := hr)
      (Δ := Δ) (hQ := hQ) (hE := hE) (hdim := hdim) (hminus := hminus)
      (hsplit := hsplit) (hirr := hirr) (θ := θ) (hBsN := hBsN)
      (σ := σ) (ΘA := ΘA) (hψσ := hψσ) (hΘA := hΘA) (Θ := Θ) (hΘ := hΘ)
      (hW := hW) (κ := κ) (hκτ := hκτ) (hκinj := hκinj) (hκrange := hκrange)
      (hJmap := hJmap) (eta := eta) (i0 := i0) (j := j) (hcoord := hcoord)
      (hj := hj) (hyj := hyj) (hyoff := fun k _ hkj => haxis k hkj)
  let i3 : Fin (r + 1) := ⟨3, by omega⟩
  let u : Fin (r + 1) := ell.symm j
  have hellu : ell u = j := by simp [u]
  have h0u : (0 : Fin (r + 1)) ≠ u := by
    intro h
    have h1 : ell (0 : Fin (r + 1)) = ell u := congrArg ell h
    rw [hell0, hellu] at h1
    exact hj h1.symm
  have h03 : (0 : Fin (r + 1)) ≠ i3 := Fin.ne_of_val_ne (by simp [i3])
  let τ : Equiv.Perm (Fin (r + 1)) := Equiv.swap i3 u
  have hτ0 : τ 0 = 0 := Equiv.swap_apply_of_ne_of_ne h03 h0u
  obtain ⟨a', ha'inj, ha'range, hmarkL'⟩ :=
    ggTBJOrthNbr_exists_markedDeletionChart_relabel (r := r) (F := F) (p := p) (b := b) (c := c)
      (by omega) hirr Bs eta ell a hainj hmarkL τ hτ0
  have hell'0 : (ell * τ) 0 = i0 := by
    rw [Equiv.Perm.mul_apply, hτ0, hell0]
  have hell'3 : (ell * τ) i3 = j := by
    rw [Equiv.Perm.mul_apply, show τ i3 = u from Equiv.swap_apply_left i3 u, hellu]
  have hact : MulAut.congr eta (ggConjAut Bs hw) =
      SpCoord.permAut ((ell * τ) * Equiv.swap 0 i3 * (ell * τ)⁻¹) := by
    rw [hact0, ← Equiv.swap_apply_apply, hell'0, hell'3]
  obtain ⟨Pc, k, hksquare, hPval, hkinj, hkrange, hmarkK⟩ :=
    ggTBJOrthNbr_exists_markedDeletionChart_of_conj_of_three_le (r := r) (F := F) (p := p)
      (b := b) (c := c) (hr := hr) (hirr := hirr)
      (Bs := Bs) (L := L) (K := K) (eta := eta) (ell := ell * τ) (u := i3)
      (w := w) (hw := hw) (hact := hact) (hK := hKeq.symm)
      (a := a') (ha := ha'inj) (haL := ha'range.trans harange) (hmarkL := hmarkL')
  let D0 : Finset (Fin (r + 1)) := Finset.univ.erase (0 : Fin (r + 1))
  let Du : Finset (Fin (r + 1)) := Finset.univ.erase i3
  let O : Finset (Fin (r + 1)) := D0 ∩ Du
  have hF4 : 4 ≤ Nat.card F := by
    rw [hFcard]
    calc (4 : ℕ) = 2 ^ 2 := rfl
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
  have hcard : 2 < Nat.card F := by omega
  have hmark : ∀ S : Finset (Fin (r + 1)), S.Nonempty → S.card ≤ 2 → S ⊆ O →
      ((chartSubgroup (n := r + 2) (F := F) (b := b) (c := c) S).subgroupOf
        (chartSubgroup (n := r + 2) (F := F) (b := b) (c := c) D0)).map a' =
      ((chartSubgroup (n := r + 2) (F := F) (b := b) (c := c) S).subgroupOf
        (chartSubgroup (n := r + 2) (F := F) (b := b) (c := c) Du)).map k := by
    intro S hSne hScard hSub
    dsimp only [D0, Du, O] at hSub ⊢
    rw [hmarkL' S hSne hScard (fun x hx => (Finset.mem_inter.mp (hSub hx)).1),
      hmarkK S hSne hScard (fun x hx => (Finset.mem_inter.mp (hSub hx)).2)]
  obtain ⟨beta, hcoh', hk'inj, hk'range, hbetaSupp⟩ :=
    exists_calibrated_deletion_chart_of_marked_supports_of_three_le
      (F := F) (b := b) (c := c) (r := r) (G := G) (u := i3)
      hr hirr hcard h03 a' k ha'inj hkinj hmark
  let k' : chartSubgroup (n := r + 2) (F := F) (b := b) (c := c) Du →* G :=
    k.comp beta.toMonoidHom
  have hk'range' : k'.range = K := hk'range.trans hkrange
  have hcoh : ∀ x : chartSubgroup (n := r + 2) (F := F) (b := b) (c := c) O,
      a' (Subgroup.inclusion (chartSubgroup_mono hirr (Finset.inter_subset_left)) x) =
      k' (Subgroup.inclusion (chartSubgroup_mono hirr (Finset.inter_subset_right)) x) := by
    intro x
    exact (DFunLike.congr_fun hcoh' x).symm
  have hmarkK' : ∀ S : Finset (Fin (r + 1)), S.Nonempty → S.card ≤ 2 → S ⊆ Du →
      ((chartSubgroup (n := r + 2) (F := F) (b := b) (c := c) S).subgroupOf
        (chartSubgroup (n := r + 2) (F := F) (b := b) (c := c) Du)).map k' =
        ggBlockComm Bs eta ((ell * τ) '' (S : Set (Fin (r + 1)))) := by
    intro S hSne hScard hSub
    rw [show k' = k.comp beta.toMonoidHom from rfl, ← Subgroup.map_map,
      hbetaSupp S hSub, hmarkK S hSne hScard hSub]
  obtain ⟨Phi, hPhiInj, hPhiRange⟩ :=
    exists_injective_split_completion_of_node_crossing (F := F) (b := b) (c := c)
      r hr hirr hcard a' k' ha'inj hcoh
      (node_crossing_of_pairCrossing (F := F) (b := b) (c := c) r hr hirr hF4 Bs eta (ell * τ)
        a' k' hk'inj hmarkL' hmarkK' hO2)
  have hPhiRange' : Phi.range = L ⊔ K := by
    rw [hPhiRange, ha'range, harange, hk'range']
  exact ggSecFiveData_of_injective_quadMinus (F := F) (b := b) (c := c)
    (m := r + 2) (f := f) hirr (by omega) (by omega) hFcard hPhiInj
    (hPhiRange'.trans hLK.symm)

theorem ggSecFiveBCoordBSparseTwDFourSplitInput_holds :
    GGSecFiveBCoordBSparseTwDFourSplitInput := by
  intro hX hTCJ hRig hTPn hA8 hraw hiso hFC hBJ G _ _ p B Bs x L D J 𝒦 hR _ n e hP _ eta i0
    h𝒦 hL hLab hB hRM _ _ _ _ hDense
  exact ggSecFiveData_of_split_four_pairCrossing hX hTCJ hRig hTPn hA8 hraw hiso hFC hBJ hR e hP
    eta i0 h𝒦 hL hLab hB hRM hDense
    (pairCrossing_of_perfectResidual Bs eta
      (hR.ggBlockComm_pairResidual_commute_of_sparse_twD_four_split hX hTCJ hRig hTPn hA8 hraw
        hiso hFC eta i0 h𝒦 hL hLab hB hRM hDense))

end Inputs

end CFSG.StandardType

end
