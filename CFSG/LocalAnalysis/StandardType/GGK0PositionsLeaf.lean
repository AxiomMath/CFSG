module

public import CFSG.LocalAnalysis.StandardType.GGK0StageDefs
import CFSG.LocalAnalysis.StandardType.GGK0NormalFrob
import CFSG.LocalAnalysis.StandardType.GGK0NormalTypes
import CFSG.LocalAnalysis.StandardType.GGK0RowOrbits
import CFSG.LocalAnalysis.StandardType.GGKacCompsSpec
import CFSG.LocalAnalysis.StandardType.GGKacCompOrbitsSpec
public import CFSG.Sporadic.ThSchreier.GlobalData
public import CFSG.Sporadic.ThSchreier.LocalOrbitBase1

public section

namespace CFSG.StandardType.GGK0MarkedKacIface1587

open CFSG CFSG.Assembly CFSG.StandardType
open CFSG.HardMathSupport.Timmesfeld.LangTorus
open CFSG.Blueprint.Chevalley
open CFSG.LieType.Chevalley
open CFSG.LieType.AlgebraicGroups
open CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

variable {Omega : Type} [Field Omega] [IsAlgClosed Omega] [CharP Omega 2]
  {lab : LargeEvenLabel} {p : ℕ} {R : Type} [Group R] {I : Set (MulAut R)} {phi : MulAut R}

open CFSG.HardMathSupport.Timmesfeld.CrossChar

private def zeroList (A : K0LangMark Omega lab p R I phi) : List ℕ :=
  (List.range A.row.diagram.marks.length).filter (fun i => decide (A.row.s.getD i 0 = 0))

omit [CharP Omega 2] in
private theorem zeroList_nodup (A : K0LangMark Omega lab p R I phi) : (zeroList A).Nodup := by
  unfold zeroList
  exact List.Nodup.filter _ List.nodup_range

omit [CharP Omega 2] in
private theorem mem_zeroList {A : K0LangMark Omega lab p R I phi} {i : ℕ} :
    i ∈ zeroList A ↔ i < A.row.diagram.marks.length ∧ A.row.s.getD i 0 = 0 := by
  unfold zeroList
  rw [List.mem_filter, List.mem_range, decide_eq_true_eq]

omit [CharP Omega 2] in
private theorem zrel_iff {A : K0LangMark Omega lab p R I phi} (N : K0Normal A)
    {a b : ℕ} (ha : a < A.row.diagram.marks.length) (hb : b < A.row.diagram.marks.length) :
    N.K.ZRel p A.kacMu (idxNode a)
      (idxNode b) ↔
      a ∈ zeroList A ∧ b ∈ zeroList A ∧ 0 < A.row.diagram.adj a b := by
  have ha' : a < A.tau.rank + 1 := by rw [← N.length_eq]; exact ha
  have hb' : b < A.tau.rank + 1 := by rw [← N.length_eq]; exact hb
  unfold CFSG.HardMathSupport.Timmesfeld.CrossChar.KacData.ZRel
  rw [N.isZ_iff ha', N.isZ_iff hb', N.adj_iff a b ha' hb']
  rw [mem_zeroList, mem_zeroList]
  constructor
  · rintro ⟨hsa, hsb, hadj⟩
    exact ⟨⟨ha, hsa⟩, ⟨hb, hsb⟩, hadj⟩
  · rintro ⟨⟨_, hsa⟩, ⟨_, hsb⟩, hadj⟩
    exact ⟨hsa, hsb, hadj⟩

omit [CharP Omega 2] in
private theorem eqvGen_idxNode_iff {A : K0LangMark Omega lab p R I phi} (N : K0Normal A)
    {i k : ℕ} (hi : i < A.row.diagram.marks.length) (hk : k < A.row.diagram.marks.length)
    (_hsi : A.row.s.getD i 0 = 0) (_hsk : A.row.s.getD k 0 = 0) :
    Relation.EqvGen (N.K.ZRel p A.kacMu)
      (idxNode i)
      (idxNode k) ↔
      Relation.EqvGen (fun a b => a ∈ zeroList A ∧ b ∈ zeroList A ∧ 0 < A.row.diagram.adj a b) i k := by
  let R₀ : ℕ → ℕ → Prop := fun a b => a ∈ zeroList A ∧ b ∈ zeroList A ∧ 0 < A.row.diagram.adj a b
  change Relation.EqvGen (N.K.ZRel p A.kacMu)
      (idxNode i)
      (idxNode k) ↔ Relation.EqvGen R₀ i k
  constructor
  · intro h
    have hgen : ∀ x y : Option (Fin A.tau.rank), Relation.EqvGen (N.K.ZRel p A.kacMu) x y →
        Relation.EqvGen R₀ (nodeIdx x)
          (nodeIdx y) := by
      intro x y hxy
      induction hxy with
      | rel a b hab =>
        have ha : nodeIdx a < A.row.diagram.marks.length := by
          rw [N.length_eq]
          exact nodeIdx_lt a
        have hb : nodeIdx b < A.row.diagram.marks.length := by
          rw [N.length_eq]
          exact nodeIdx_lt b
        have hZ : N.K.ZRel p A.kacMu
            (idxNode (nodeIdx a))
            (idxNode (nodeIdx b)) := by
          simpa [idxNode_nodeIdx] using hab
        exact Relation.EqvGen.rel _ _ ((zrel_iff N ha hb).1 hZ)
      | refl a => exact Relation.EqvGen.refl _
      | symm a b hab ih => exact Relation.EqvGen.symm _ _ ih
      | trans a b c hab hbc ih1 ih2 => exact Relation.EqvGen.trans _ _ _ ih1 ih2
    have hik := hgen (idxNode i)
      (idxNode k) h
    have hi' : i < A.tau.rank + 1 := by rw [← N.length_eq]; exact hi
    have hk' : k < A.tau.rank + 1 := by rw [← N.length_eq]; exact hk
    rw [nodeIdx_idxNode (r := A.tau.rank) hi',
        nodeIdx_idxNode (r := A.tau.rank) hk'] at hik
    exact hik
  · intro h
    change Relation.EqvGen R₀ i k at h
    clear hi hk _hsi _hsk
    induction h with
    | rel a b hab =>
      have ha : a < A.row.diagram.marks.length := ((mem_zeroList).1 hab.1).1
      have hb : b < A.row.diagram.marks.length := ((mem_zeroList).1 hab.2.1).1
      exact Relation.EqvGen.rel _ _ ((zrel_iff N ha hb).2 hab)
    | refl a => exact Relation.EqvGen.refl _
    | symm a b hab ih => exact Relation.EqvGen.symm _ _ ih
    | trans a b c hab hbc ih1 ih2 => exact Relation.EqvGen.trans _ _ _ ih1 ih2

private def compsList (A : K0LangMark Omega lab p R I phi) : List (List ℕ) :=
  k0Comps A.row.diagram (zeroList A)

omit [CharP Omega 2] in
private theorem comp_eq_class {A : K0LangMark Omega lab p R I phi} (N : K0Normal A)
    {c : List ℕ} (hc : c ∈ compsList A) {i : ℕ} (hi : i ∈ c) :
    N.K.comp p A.kacMu (idxNode i) =
      idxNode '' {k | k ∈ c} := by
  have hspec := k0Comps_spec A.row.diagram (zeroList_nodup A)
  have hc_zero : i ∈ zeroList A := (hspec.1 c hc).2.2 i hi
  have hi_lt : i < A.row.diagram.marks.length := ((mem_zeroList).1 hc_zero).1
  have hclass : ∀ j, j ∈ c ↔ Relation.EqvGen (fun a b => a ∈ zeroList A ∧ b ∈ zeroList A ∧ 0 < A.row.diagram.adj a b) i j :=
    hspec.2.1 c hc i hi
  ext y
  constructor
  · intro hy
    have hZ : N.K.IsZ p A.kacMu y := hy.1
    have heq : Relation.EqvGen (N.K.ZRel p A.kacMu) (idxNode i) y := hy.2
    let k := nodeIdx y
    have hy_eq : y = idxNode k := by
      exact (idxNode_nodeIdx y).symm
    have hk_lt : k < A.row.diagram.marks.length := by
      rw [N.length_eq]
      exact nodeIdx_lt y
    have hk_zero : k ∈ zeroList A := by
      rw [mem_zeroList]
      refine ⟨hk_lt, ?_⟩
      have hZk : N.K.IsZ p A.kacMu (idxNode k) := by
        rwa [hy_eq] at hZ
      have hk' : k < A.tau.rank + 1 := by rw [← N.length_eq]; exact hk_lt
      exact (N.isZ_iff hk').1 hZk
    have heq' : Relation.EqvGen (N.K.ZRel p A.kacMu) (idxNode i) (idxNode k) := by
      rwa [hy_eq] at heq
    have hR : Relation.EqvGen (fun a b => a ∈ zeroList A ∧ b ∈ zeroList A ∧ 0 < A.row.diagram.adj a b) i k :=
      (eqvGen_idxNode_iff N hi_lt hk_lt ((mem_zeroList).1 hc_zero).2 ((mem_zeroList).1 hk_zero).2).1 heq'
    have hk_mem : k ∈ c := (hclass k).2 hR
    exact ⟨k, hk_mem, hy_eq.symm⟩
  · rintro ⟨k, hk, rfl⟩
    have hk_zero : k ∈ zeroList A := (hspec.1 c hc).2.2 k hk
    have hk_lt : k < A.row.diagram.marks.length := ((mem_zeroList).1 hk_zero).1
    have hk' : k < A.tau.rank + 1 := by rw [← N.length_eq]; exact hk_lt
    have hZk : N.K.IsZ p A.kacMu (idxNode k) :=
      (N.isZ_iff hk').2 ((mem_zeroList).1 hk_zero).2
    have hR : Relation.EqvGen (fun a b => a ∈ zeroList A ∧ b ∈ zeroList A ∧ 0 < A.row.diagram.adj a b) i k :=
      (hclass k).1 hk
    have heq : Relation.EqvGen (N.K.ZRel p A.kacMu) (idxNode i) (idxNode k) :=
      (eqvGen_idxNode_iff N hi_lt hk_lt ((mem_zeroList).1 hc_zero).2 ((mem_zeroList).1 hk_zero).2).2 hR
    exact ⟨hZk, heq⟩

private def imgList (A : K0LangMark Omega lab p R I phi) (c : List ℕ) : List ℕ :=
  k0SortNat (c.map (fun i => A.row.rho.getD i 0))

omit [CharP Omega 2] in
private theorem rho_inj {A : K0LangMark Omega lab p R I phi} {i j : ℕ}
    (hi : i < A.row.diagram.marks.length) (hj : j < A.row.diagram.marks.length)
    (h : A.row.rho.getD i 0 = A.row.rho.getD j 0) : i = j := by
  rw [A.row.rho_apply ⟨i, hi⟩, A.row.rho_apply ⟨j, hj⟩] at h
  have h' : A.row.nodePerm ⟨i, hi⟩ = A.row.nodePerm ⟨j, hj⟩ := Fin.ext h
  have h'' : (⟨i, hi⟩ : Fin A.row.diagram.marks.length) = ⟨j, hj⟩ := A.row.nodePerm.injective h'
  exact congrArg Fin.val h''

omit [CharP Omega 2] in
private theorem imgList_sorted {A : K0LangMark Omega lab p R I phi} (c : List ℕ) :
    (imgList A c).SortedLE := by
  unfold imgList
  rw [k0SortNat_eq_insertionSort]
  exact List.sortedLE_insertionSort

omit [CharP Omega 2] in
private theorem imgList_nodup {A : K0LangMark Omega lab p R I phi} {c : List ℕ}
    (hc : c.Nodup) (hlt : ∀ i ∈ c, i < A.row.diagram.marks.length) : (imgList A c).Nodup := by
  unfold imgList
  rw [k0SortNat_eq_insertionSort]
  exact (List.perm_insertionSort _ _).nodup_iff.mpr
    (List.Nodup.map_on (fun a ha b hb h => rho_inj (hlt a ha) (hlt b hb) h) hc)

private def piNat (A : K0LangMark Omega lab p R I phi) : ℕ → ℕ := fun i => A.row.rho.getD i 0

omit [CharP Omega 2] in
private theorem imgList_eq_sort (A : K0LangMark Omega lab p R I phi) (c : List ℕ) :
    imgList A c = k0SortNat (c.map (piNat A)) := rfl

omit [CharP Omega 2] in
private theorem piNat_apply {A : K0LangMark Omega lab p R I phi} {i : ℕ}
    (hi : i < A.row.diagram.marks.length) :
    piNat A i = (A.row.nodePerm ⟨i, hi⟩).val :=
  A.row.rho_apply ⟨i, hi⟩

omit [CharP Omega 2] in
private theorem piNat_lt {A : K0LangMark Omega lab p R I phi} {i : ℕ}
    (hi : i < A.row.diagram.marks.length) :
    piNat A i < A.row.diagram.marks.length := by
  rw [piNat_apply hi]
  exact (A.row.nodePerm ⟨i, hi⟩).isLt

private theorem piNat_mem_zeroList {A : K0LangMark Omega lab p R I phi} (N : K0Normal A)
    {i : ℕ} (hi : i < A.row.diagram.marks.length) :
    piNat A i ∈ zeroList A ↔ i ∈ zeroList A := by
  have h1 : piNat A i < A.row.diagram.marks.length := piNat_lt hi
  rw [mem_zeroList, mem_zeroList]
  constructor
  · rintro ⟨-, hs⟩
    refine ⟨hi, ?_⟩
    rw [piNat_apply hi] at hs
    exact (N.s_nodePerm_eq_zero_iff ⟨i, hi⟩).1 hs
  · rintro ⟨-, hs⟩
    refine ⟨h1, ?_⟩
    rw [piNat_apply hi]
    exact (N.s_nodePerm_eq_zero_iff ⟨i, hi⟩).2 hs

omit [CharP Omega 2] in
private theorem piNat_adj {A : K0LangMark Omega lab p R I phi} (N : K0Normal A)
    {i j : ℕ} (hi : i < A.row.diagram.marks.length) (hj : j < A.row.diagram.marks.length) :
    0 < A.row.diagram.adj (piNat A i) (piNat A j) ↔ 0 < A.row.diagram.adj i j := by
  rw [piNat_apply hi, piNat_apply hj]
  exact N.adj_nodePerm ⟨i, hi⟩ ⟨j, hj⟩

omit [CharP Omega 2] in
private theorem piNat_surj {A : K0LangMark Omega lab p R I phi} {j : ℕ}
    (hj : j < A.row.diagram.marks.length) :
    ∃ i, i < A.row.diagram.marks.length ∧ piNat A i = j := by
  have hinj : Function.Injective
      (fun i : Fin A.row.diagram.marks.length =>
        (⟨piNat A i.val, piNat_lt i.isLt⟩ : Fin A.row.diagram.marks.length)) := by
    intro i j' hij
    have h : piNat A i.val = piNat A j'.val := congrArg Fin.val hij
    exact Fin.ext (rho_inj i.isLt j'.isLt h)
  obtain ⟨i, hi⟩ := (Finite.injective_iff_surjective).1 hinj ⟨j, hj⟩
  exact ⟨i.val, i.isLt, congrArg Fin.val hi⟩

omit [CharP Omega 2] in
private theorem idxNode_injOn {A : K0LangMark Omega lab p R I phi} {a b : ℕ}
    (ha : a < A.tau.rank + 1) (hb : b < A.tau.rank + 1)
    (h : idxNode (r := A.tau.rank) a =
      idxNode (r := A.tau.rank) b) : a = b := by
  rw [← nodeIdx_idxNode (r := A.tau.rank) ha,
    ← nodeIdx_idxNode (r := A.tau.rank) hb, h]

private noncomputable def permNode (A : K0LangMark Omega lab p R I phi) (N : K0Normal A) :
    Equiv.Perm (Option (Fin A.tau.rank)) :=
  Equiv.ofBijective (fun x => idxNode (piNat A
      (nodeIdx x)))
    ⟨fun x y h => by
      have hx : nodeIdx x <
          A.row.diagram.marks.length := by
        rw [N.length_eq]
        exact nodeIdx_lt x
      have hy : nodeIdx y <
          A.row.diagram.marks.length := by
        rw [N.length_eq]
        exact nodeIdx_lt y
      have hpx : piNat A (nodeIdx x) <
          A.tau.rank + 1 := by
        rw [← N.length_eq]; exact piNat_lt hx
      have hpy : piNat A (nodeIdx y) <
          A.tau.rank + 1 := by
        rw [← N.length_eq]; exact piNat_lt hy
      have h' : nodeIdx
            (idxNode
              (piNat A (nodeIdx x))) =
          nodeIdx
            (idxNode
              (piNat A (nodeIdx y))) :=
        congrArg nodeIdx h
      rw [nodeIdx_idxNode (r := A.tau.rank) hpx,
        nodeIdx_idxNode (r := A.tau.rank) hpy] at h'
      have h'' : nodeIdx x =
          nodeIdx y := rho_inj hx hy h'
      rw [← idxNode_nodeIdx x,
        ← idxNode_nodeIdx y, h''],
    fun y => by
      have hy : nodeIdx y <
          A.row.diagram.marks.length := by
        rw [N.length_eq]
        exact nodeIdx_lt y
      obtain ⟨i, hi, hpi⟩ := piNat_surj hy
      refine ⟨idxNode i, ?_⟩
      show idxNode
          (piNat A (nodeIdx
            (idxNode i))) = y
      rw [nodeIdx_idxNode (r := A.tau.rank)
          (by rw [← N.length_eq]; exact hi), hpi,
        idxNode_nodeIdx]⟩

omit [CharP Omega 2] in
private theorem permNode_apply_idxNode {A : K0LangMark Omega lab p R I phi} (N : K0Normal A)
    {i : ℕ} (hi : i < A.row.diagram.marks.length) :
    permNode A N (idxNode i) =
      idxNode (piNat A i) := by
  show idxNode
      (piNat A (nodeIdx
        (idxNode i))) =
    idxNode (piNat A i)
  rw [nodeIdx_idxNode (r := A.tau.rank)
    (by rw [← N.length_eq]; exact hi)]

private theorem permNode_isZ {A : K0LangMark Omega lab p R I phi} (N : K0Normal A)
    (x : Option (Fin A.tau.rank)) :
    N.K.IsZ p A.kacMu (permNode A N x) ↔ N.K.IsZ p A.kacMu x := by
  have hx : nodeIdx x <
      A.row.diagram.marks.length := by
    rw [N.length_eq]
    exact nodeIdx_lt x
  have hx' : nodeIdx x < A.tau.rank + 1 := by
    rw [← N.length_eq]; exact hx
  have hp : piNat A (nodeIdx x) < A.tau.rank + 1 := by
    rw [← N.length_eq]; exact piNat_lt hx
  show N.K.IsZ p A.kacMu
      (idxNode
        (piNat A (nodeIdx x))) ↔ _
  have e2 : N.K.IsZ p A.kacMu x ↔ N.K.IsZ p A.kacMu (idxNode (nodeIdx x)) := by
    rw [idxNode_nodeIdx x]
  rw [e2, N.isZ_iff hp, N.isZ_iff hx']
  have e1 : A.row.s.getD (piNat A (nodeIdx x)) 0 = 0 ↔
      piNat A (nodeIdx x) ∈ zeroList A := by
    rw [mem_zeroList]
    exact ⟨fun h => ⟨piNat_lt hx, h⟩, fun h => h.2⟩
  have e2 : A.row.s.getD (nodeIdx x) 0 = 0 ↔
      nodeIdx x ∈ zeroList A := by
    rw [mem_zeroList]
    exact ⟨fun h => ⟨hx, h⟩, fun h => h.2⟩
  rw [e1, e2]
  exact piNat_mem_zeroList N hx

omit [CharP Omega 2] in
private theorem permNode_adj {A : K0LangMark Omega lab p R I phi} (N : K0Normal A)
    (x y : Option (Fin A.tau.rank)) :
    N.K.Adj (permNode A N x) (permNode A N y) ↔ N.K.Adj x y := by
  have hx : nodeIdx x <
      A.row.diagram.marks.length := by
    rw [N.length_eq]
    exact nodeIdx_lt x
  have hy : nodeIdx y <
      A.row.diagram.marks.length := by
    rw [N.length_eq]
    exact nodeIdx_lt y
  have hx' : nodeIdx x < A.tau.rank + 1 := by
    rw [← N.length_eq]; exact hx
  have hy' : nodeIdx y < A.tau.rank + 1 := by
    rw [← N.length_eq]; exact hy
  have hp : piNat A (nodeIdx x) < A.tau.rank + 1 := by
    rw [← N.length_eq]; exact piNat_lt hx
  have hq : piNat A (nodeIdx y) < A.tau.rank + 1 := by
    rw [← N.length_eq]; exact piNat_lt hy
  have h1 : permNode A N x = idxNode
      (piNat A (nodeIdx x)) := rfl
  have h2 : permNode A N y = idxNode
      (piNat A (nodeIdx y)) := rfl
  conv_rhs => rw [← idxNode_nodeIdx x, ← idxNode_nodeIdx y]
  rw [h1, h2,
    N.adj_iff _ _ hp hq, N.adj_iff _ _ hx' hy']
  exact piNat_adj N hx hy

private theorem comp_permNode {A : K0LangMark Omega lab p R I phi} (N : K0Normal A)
    (x : Option (Fin A.tau.rank)) :
    (permNode A N : Option (Fin A.tau.rank) → Option (Fin A.tau.rank)) ''
        N.K.comp p A.kacMu x = N.K.comp p A.kacMu (permNode A N x) :=
  N.K.image_comp (permNode A N) (permNode_isZ N) (permNode_adj N) x

omit [CharP Omega 2] in
private theorem mem_imgList_iff {A : K0LangMark Omega lab p R I phi} {c : List ℕ} {x : ℕ} :
    x ∈ imgList A c ↔ ∃ i ∈ c, piNat A i = x := by
  rw [imgList_eq_sort, k0SortNat_eq_insertionSort, List.mem_insertionSort]
  exact List.mem_map

private theorem comp_imgList_head {A : K0LangMark Omega lab p R I phi} (N : K0Normal A)
    {c : List ℕ} (hc : c ∈ compsList A) :
    N.K.comp p A.kacMu (idxNode (piNat A (c.headD 0))) =
      idxNode '' {x | x ∈ imgList A c} := by
  have hspec := k0Comps_spec A.row.diagram (zeroList_nodup A)
  have hne : c ≠ [] := (hspec.1 c hc).1
  have hmem : c.headD 0 ∈ c := by
    cases c with
    | nil => exact absurd rfl hne
    | cons a as => simp
  have hz : c.headD 0 ∈ zeroList A := (hspec.1 c hc).2.2 _ hmem
  have hlt : c.headD 0 < A.row.diagram.marks.length := ((mem_zeroList).1 hz).1
  have hcls : N.K.comp p A.kacMu
      (idxNode (c.headD 0)) =
      idxNode '' {k | k ∈ c} :=
    comp_eq_class N hc hmem
  have himg := comp_permNode N (idxNode (c.headD 0))
  rw [permNode_apply_idxNode N hlt] at himg
  rw [← himg, hcls]
  have hset : piNat A '' {k | k ∈ c} = {x | x ∈ imgList A c} := by
    ext x
    rw [Set.mem_image]
    simp only [Set.mem_ofPred_eq]
    rw [mem_imgList_iff]
  calc (permNode A N : Option (Fin A.tau.rank) → Option (Fin A.tau.rank)) ''
        (idxNode '' {k | k ∈ c})
      = (fun k => permNode A N (idxNode k)) ''
          {k | k ∈ c} := Set.image_image ..
    _ = (fun k => idxNode (piNat A k)) '' {k | k ∈ c} := by
        refine Set.image_congr (fun k hk => ?_)
        exact permNode_apply_idxNode N ((mem_zeroList).1 ((hspec.1 c hc).2.2 k hk)).1
    _ = idxNode ''
          (piNat A '' {k | k ∈ c}) := (Set.image_image ..).symm
    _ = idxNode '' {x | x ∈ imgList A c} := by rw [hset]

omit [CharP Omega 2] in
private theorem mem_imgList_iff_of_image_eq {A : K0LangMark Omega lab p R I phi} (N : K0Normal A)
    {c c' : List ℕ} (hc : c ∈ compsList A) (hc' : c' ∈ compsList A)
    (h : idxNode (r := A.tau.rank) '' {x | x ∈ imgList A c} =
      idxNode (r := A.tau.rank) '' {k | k ∈ c'}) :
    ∀ x, x ∈ imgList A c ↔ x ∈ c' := by
  have hspec := k0Comps_spec A.row.diagram (zeroList_nodup A)
  have hsub1 : ∀ y ∈ imgList A c, y < A.row.diagram.marks.length := by
    intro y hy
    obtain ⟨i, hi, rfl⟩ := (mem_imgList_iff (A := A)).1 hy
    exact piNat_lt ((mem_zeroList).1 (((k0Comps_spec A.row.diagram (zeroList_nodup A)).1 c hc).2.2 i hi)).1
  have hsub2 : ∀ y ∈ c', y < A.row.diagram.marks.length := by
    intro y hy
    exact ((mem_zeroList).1 (((k0Comps_spec A.row.diagram (zeroList_nodup A)).1 c' hc').2.2 y hy)).1
  have hsub1' : ∀ y ∈ imgList A c, y < A.tau.rank + 1 := fun y hy => by
    rw [← N.length_eq]; exact hsub1 y hy
  have hsub2' : ∀ y ∈ c', y < A.tau.rank + 1 := fun y hy => by
    rw [← N.length_eq]; exact hsub2 y hy
  have key : ∀ x, x < A.row.diagram.marks.length → (x ∈ imgList A c ↔ x ∈ c') := by
    intro x hx
    have hx' : x < A.tau.rank + 1 := by rw [← N.length_eq]; exact hx
    constructor
    · intro hxin
      have hmem : idxNode (r := A.tau.rank) x ∈ idxNode (r := A.tau.rank) '' {y | y ∈ c'} := by
        rw [← h]
        exact ⟨x, hxin, rfl⟩
      obtain ⟨y, hy, hyeq⟩ := hmem
      exact (idxNode_injOn (A := A) (hsub2' y hy) hx' hyeq) ▸ hy
    · intro hxin
      have hmem : idxNode (r := A.tau.rank) x ∈ idxNode (r := A.tau.rank) '' {y | y ∈ imgList A c} := by
        rw [h]
        exact ⟨x, hxin, rfl⟩
      obtain ⟨y, hy, hyeq⟩ := hmem
      exact (idxNode_injOn (A := A) (hsub1' y hy) hx' hyeq) ▸ hy
  intro x
  by_cases hx : x < A.row.diagram.marks.length
  · exact key x hx
  · constructor
    · intro hxin; exact absurd (hsub1 x hxin) hx
    · intro hxin; exact absurd (hsub2 x hxin) hx

omit [CharP Omega 2] in
private theorem eq_of_mem_iff_of_mem_comps {A : K0LangMark Omega lab p R I phi} (_N : K0Normal A)
    {c c' : List ℕ} (hc : c ∈ compsList A) (hc' : c' ∈ compsList A)
    (h : ∀ x, x ∈ imgList A c ↔ x ∈ c') : imgList A c = c' := by
  have hspec := k0Comps_spec A.row.diagram (zeroList_nodup A)
  have hnd1 : (imgList A c).Nodup := imgList_nodup (hspec.1 c hc).2.1.nodup
    (fun i hi => ((mem_zeroList).1 (((k0Comps_spec A.row.diagram (zeroList_nodup A)).1 c hc).2.2 i hi)).1)
  have hnd2 : c'.Nodup := (hspec.1 c' hc').2.1.nodup
  have hperm : (imgList A c).Perm c' := (List.perm_ext_iff_of_nodup hnd1 hnd2).2 h
  have hs1 : (imgList A c).SortedLE := imgList_sorted c
  have hs2 : c'.SortedLE := (List.sortedLE_iff_pairwise).2
    ((hspec.1 c' hc').2.1.imp (fun h => le_of_lt h))
  exact List.Perm.eq_of_sortedLE hs1 hs2 hperm

private theorem imgList_mem_compsList {A : K0LangMark Omega lab p R I phi} (N : K0Normal A)
    {c : List ℕ} (hc : c ∈ compsList A) : imgList A c ∈ compsList A := by
  have hspec := k0Comps_spec A.row.diagram (zeroList_nodup A)
  have hne : c ≠ [] := (hspec.1 c hc).1
  have hmem : c.headD 0 ∈ c := by
    cases c with
    | nil => exact absurd rfl hne
    | cons a as => simp
  have hz : c.headD 0 ∈ zeroList A := hspec.1 c hc |>.2.2 _ hmem
  have hlt : c.headD 0 < A.row.diagram.marks.length := ((mem_zeroList).1 hz).1
  have hjz : piNat A (c.headD 0) ∈ zeroList A := (piNat_mem_zeroList N hlt).2 hz
  obtain ⟨c', hc', hjc'⟩ := hspec.2.2.1 _ hjz
  have h1 : N.K.comp p A.kacMu (idxNode (piNat A (c.headD 0))) =
      idxNode '' {x | x ∈ imgList A c} := comp_imgList_head N hc
  have h2 : N.K.comp p A.kacMu (idxNode (piNat A (c.headD 0))) =
      idxNode '' {k | k ∈ c'} := comp_eq_class N hc' hjc'
  rw [h1] at h2
  rw [eq_of_mem_iff_of_mem_comps N hc hc' (mem_imgList_iff_of_image_eq N hc hc' h2)]
  exact hc'

omit [CharP Omega 2] in
private theorem imgList_inj {A : K0LangMark Omega lab p R I phi} (_N : K0Normal A)
    {c₁ c₂ : List ℕ} (h₁ : c₁ ∈ compsList A) (h₂ : c₂ ∈ compsList A)
    (h : imgList A c₁ = imgList A c₂) : c₁ = c₂ := by
  have hspec := k0Comps_spec A.row.diagram (zeroList_nodup A)
  have himg : piNat A '' {k | k ∈ c₁} = piNat A '' {k | k ∈ c₂} := by
    ext x
    rw [Set.mem_image, Set.mem_image]
    simp only [Set.mem_ofPred_eq]
    have e1 : (∃ k, k ∈ c₁ ∧ piNat A k = x) ↔ x ∈ imgList A c₁ :=
      (mem_imgList_iff (A := A)).symm
    have e2 : (∃ k, k ∈ c₂ ∧ piNat A k = x) ↔ x ∈ imgList A c₂ :=
      (mem_imgList_iff (A := A)).symm
    rw [e1, e2, h]
  have hmem_iff : ∀ k, k ∈ c₁ ↔ k ∈ c₂ := by
    intro k
    constructor
    · intro hk
      have hkz : k ∈ zeroList A := (hspec.1 c₁ h₁).2.2 k hk
      have hx : piNat A k ∈ piNat A '' {j | j ∈ c₁} := ⟨k, hk, rfl⟩
      rw [himg] at hx
      obtain ⟨j, hj, hjk⟩ := hx
      have hjz : j ∈ zeroList A := (hspec.1 c₂ h₂).2.2 j hj
      have hjk' : j = k := rho_inj ((mem_zeroList).1 hjz).1 ((mem_zeroList).1 hkz).1 hjk
      exact hjk' ▸ hj
    · intro hk
      have hkz : k ∈ zeroList A := (hspec.1 c₂ h₂).2.2 k hk
      have hx : piNat A k ∈ piNat A '' {j | j ∈ c₂} := ⟨k, hk, rfl⟩
      rw [← himg] at hx
      obtain ⟨j, hj, hjk⟩ := hx
      have hjz : j ∈ zeroList A := (hspec.1 c₁ h₁).2.2 j hj
      have hjk' : j = k := rho_inj ((mem_zeroList).1 hjz).1 ((mem_zeroList).1 hkz).1 hjk
      exact hjk' ▸ hj
  have hnd1 : c₁.Nodup := (hspec.1 c₁ h₁).2.1.nodup
  have hnd2 : c₂.Nodup := (hspec.1 c₂ h₂).2.1.nodup
  have hperm : c₁.Perm c₂ := (List.perm_ext_iff_of_nodup hnd1 hnd2).2 hmem_iff
  have hs1 : c₁.SortedLE := (List.sortedLE_iff_pairwise).2
    ((hspec.1 c₁ h₁).2.1.imp (fun h => le_of_lt h))
  have hs2 : c₂.SortedLE := (List.sortedLE_iff_pairwise).2
    ((hspec.1 c₂ h₂).2.1.imp (fun h => le_of_lt h))
  exact List.Perm.eq_of_sortedLE hs1 hs2 hperm

private def orbitNodesOf (A : K0LangMark Omega lab p R I phi)
    (M : List (List (List ℕ))) : Fin A.row.D.orbits.length → List (List ℕ) :=
  fun j => M.getD j.val []

omit [CharP Omega 2] in
private theorem ofFn_orbitNodesOf {A : K0LangMark Omega lab p R I phi}
    {M : List (List (List ℕ))} (hlen : M.length = A.row.D.orbits.length) :
    List.ofFn (orbitNodesOf A M) = M := by
  apply List.ext_getElem
  · rw [List.length_ofFn]; exact hlen.symm
  · intro i h1 h2
    rw [List.getElem_ofFn]
    exact List.getD_eq_getElem M [] h2

omit [CharP Omega 2] in
private theorem orbitNodesOf_getElem {A : K0LangMark Omega lab p R I phi}
    {M : List (List (List ℕ))} (hlen : M.length = A.row.D.orbits.length)
    (j : Fin A.row.D.orbits.length) :
    orbitNodesOf A M j = M[j.val]'(by rw [hlen]; exact j.isLt) :=
  List.getD_eq_getElem M [] (by rw [hlen]; exact j.isLt)

omit [CharP Omega 2] in
private theorem orbitNodesOf_mem {A : K0LangMark Omega lab p R I phi}
    {M : List (List (List ℕ))} (hlen : M.length = A.row.D.orbits.length)
    (hM : M.Perm A.row.rawComponentOrbits) (j : Fin A.row.D.orbits.length) :
    orbitNodesOf A M j ∈ A.row.rawComponentOrbits := by
  rw [orbitNodesOf_getElem hlen j]
  exact hM.mem_iff.1 (List.getElem_mem _)

omit [CharP Omega 2] in
private theorem rawComponentOrbits_eq (A : K0LangMark Omega lab p R I phi) :
    A.row.rawComponentOrbits =
      k0CompOrbits (imgList A) (A.row.diagram.marks.length + 1) (compsList A) [] := rfl

omit [CharP Omega 2] in
private theorem compsList_nodup (A : K0LangMark Omega lab p R I phi) :
    (compsList A).Nodup :=
  (k0Comps_spec A.row.diagram (zeroList_nodup A)).2.2.2.1

omit [CharP Omega 2] in
private theorem compsList_length_lt (A : K0LangMark Omega lab p R I phi) :
    (compsList A).length < A.row.diagram.marks.length + 1 := by
  have h1 : (compsList A).length ≤ (zeroList A).length :=
    (k0Comps_spec A.row.diagram (zeroList_nodup A)).2.2.2.2
  have h2 : (zeroList A).length ≤ A.row.diagram.marks.length := by
    unfold zeroList
    simpa using List.length_filter_le (fun i => decide (A.row.s.getD i 0 = 0))
      (List.range A.row.diagram.marks.length)
  omega

private theorem rawOrbits_facts (A : K0LangMark Omega lab p R I phi) (N : K0Normal A) :
    (∀ o ∈ A.row.rawComponentOrbits, o ≠ [] ∧ o.Nodup ∧
      (∀ (k : ℕ) (hk : k < o.length), o[k] = (imgList A)^[k] (o.headD [])) ∧
      (imgList A)^[o.length] (o.headD []) = o.headD [] ∧ o ⊆ compsList A) ∧
    A.row.rawComponentOrbits.flatten.Perm (compsList A) := by
  have hmain := k0CompOrbits_spec (img := imgList A) (cs := compsList A)
    (compsList_nodup A) (fun c hc => imgList_mem_compsList N hc)
    (fun c hc c' hc' h => imgList_inj N hc hc' h) (compsList_length_lt A)
  rw [rawComponentOrbits_eq]
  exact ⟨fun o ho => by
      obtain ⟨h1, h2, h3, h4⟩ := hmain.1 o ho
      exact ⟨h1, h2, h3, h4,
        fun x hx => hmain.2.mem_iff.1 (List.mem_flatten.2 ⟨o, ho, hx⟩)⟩,
    hmain.2⟩

private theorem rawOrbit_subset_comps {A : K0LangMark Omega lab p R I phi} (N : K0Normal A)
    {o : List (List ℕ)} (ho : o ∈ A.row.rawComponentOrbits) : o ⊆ compsList A :=
  ((rawOrbits_facts A N).1 o ho).2.2.2.2

private theorem orbitNodesOf_subset_compsList {A : K0LangMark Omega lab p R I phi}
    (N : K0Normal A) {M : List (List (List ℕ))}
    (hlen : M.length = A.row.D.orbits.length)
    (hM : M.Perm A.row.rawComponentOrbits) (j : Fin A.row.D.orbits.length) :
    orbitNodesOf A M j ⊆ compsList A :=
  rawOrbit_subset_comps N (orbitNodesOf_mem hlen hM j)

private theorem orbitNodesOf_headD_mem {A : K0LangMark Omega lab p R I phi}
    (N : K0Normal A) {M : List (List (List ℕ))}
    (hlen : M.length = A.row.D.orbits.length)
    (hM : M.Perm A.row.rawComponentOrbits) (j : Fin A.row.D.orbits.length) :
    (orbitNodesOf A M j).headD [] ∈ compsList A := by
  have hne : orbitNodesOf A M j ≠ [] :=
    ((rawOrbits_facts A N).1 _ (orbitNodesOf_mem hlen hM j)).1
  have hmem : (orbitNodesOf A M j).headD [] ∈ orbitNodesOf A M j := by
    cases hl : orbitNodesOf A M j with
    | nil => exact absurd hl hne
    | cons a as => simp
  exact orbitNodesOf_subset_compsList N hlen hM j hmem

private theorem rawOrbit_iterate_mem {A : K0LangMark Omega lab p R I phi} (N : K0Normal A)
    {o : List (List ℕ)} (ho : o ∈ A.row.rawComponentOrbits) (t : ℕ) :
    (imgList A)^[t] (o.headD []) ∈ o := by
  obtain ⟨hne, hnd, hget, hper, -⟩ := (rawOrbits_facts A N).1 o ho
  have hL : 0 < o.length := List.length_pos_iff.2 hne
  have hmult : ∀ m, (imgList A)^[o.length * m] (o.headD []) = o.headD [] := by
    intro m
    induction m with
    | zero => simp
    | succ q ih => rw [Nat.mul_succ, Function.iterate_add_apply, hper, ih]
  have hdiv : t % o.length + o.length * (t / o.length) = t := by
    rw [Nat.add_comm, Nat.div_add_mod]
  have heq : (imgList A)^[t] (o.headD []) = (imgList A)^[t % o.length] (o.headD []) := by
    conv_lhs => rw [← hdiv]
    rw [Function.iterate_add_apply, hmult]
  rw [heq, ← hget (t % o.length) (Nat.mod_lt _ hL)]
  exact List.getElem_mem _

private theorem imgList_iterate_eq_head_iff {A : K0LangMark Omega lab p R I phi} (N : K0Normal A)
    {o : List (List ℕ)} (ho : o ∈ A.row.rawComponentOrbits) {s : ℕ} (hs : 0 < s) :
    (imgList A)^[s] (o.headD []) = o.headD [] ↔ o.length ∣ s := by
  obtain ⟨hne, hnd, hget, hper, -⟩ := (rawOrbits_facts A N).1 o ho
  have hL : 0 < o.length := List.length_pos_iff.2 hne
  have hmult : ∀ m, (imgList A)^[o.length * m] (o.headD []) = o.headD [] := by
    intro m
    induction m with
    | zero => simp
    | succ q ih => rw [Nat.mul_succ, Function.iterate_add_apply, hper, ih]
  constructor
  · intro hc
    have hmod : (imgList A)^[s % o.length] (o.headD []) = o.headD [] := by
      have hdiv : s % o.length + o.length * (s / o.length) = s := by
        rw [Nat.add_comm, Nat.div_add_mod]
      have h1 : (imgList A)^[s] (o.headD []) =
          (imgList A)^[s % o.length] ((imgList A)^[o.length * (s / o.length)] (o.headD [])) := by
        conv_lhs => rw [← hdiv]
        rw [Function.iterate_add_apply]
      rw [h1, hmult] at hc
      exact hc
    by_contra hdvd
    have hpos : 0 < s % o.length := by
      rcases Nat.eq_zero_or_pos (s % o.length) with h | h
      · exact absurd (Nat.dvd_iff_mod_eq_zero.2 h) hdvd
      · exact h
    have h0 : o[0]'(by omega) = o.headD [] := by simpa using hget 0 hL
    have hr : o[s % o.length]'(Nat.mod_lt _ hL) = o[0]'(by omega) := by
      rw [hget (s % o.length) (Nat.mod_lt _ hL), hmod, h0]
    have hidx := (hnd.getElem_inj_iff).1 hr
    omega
  · intro hdvd
    obtain ⟨m, rfl⟩ := hdvd
    exact hmult m

omit [CharP Omega 2] in
private theorem compsList_ne_nil {A : K0LangMark Omega lab p R I phi} {c : List ℕ}
    (hc : c ∈ compsList A) : c ≠ [] :=
  ((k0Comps_spec A.row.diagram (zeroList_nodup A)).1 c hc).1

omit [CharP Omega 2] in
private theorem headD_mem_compsList {A : K0LangMark Omega lab p R I phi} {c : List ℕ}
    (hc : c ∈ compsList A) : c.headD 0 ∈ c := by
  cases c with
  | nil => exact absurd rfl (compsList_ne_nil hc)
  | cons a as => simp

omit [CharP Omega 2] in
private theorem mem_zeroList_of_mem_comps {A : K0LangMark Omega lab p R I phi} {c : List ℕ}
    (hc : c ∈ compsList A) {i : ℕ} (hi : i ∈ c) : i ∈ zeroList A :=
  ((k0Comps_spec A.row.diagram (zeroList_nodup A)).1 c hc).2.2 i hi

omit [CharP Omega 2] in
private theorem headD_mem_zeroList {A : K0LangMark Omega lab p R I phi} {c : List ℕ}
    (hc : c ∈ compsList A) : c.headD 0 ∈ zeroList A :=
  mem_zeroList_of_mem_comps hc (headD_mem_compsList hc)

omit [CharP Omega 2] in
private theorem headD_lt {A : K0LangMark Omega lab p R I phi} {c : List ℕ}
    (hc : c ∈ compsList A) : c.headD 0 < A.row.diagram.marks.length :=
  ((mem_zeroList).1 (headD_mem_zeroList hc)).1

omit [CharP Omega 2] in
private theorem isZ_headD {A : K0LangMark Omega lab p R I phi} (N : K0Normal A) {c : List ℕ}
    (hc : c ∈ compsList A) :
    N.K.IsZ p A.kacMu (idxNode (c.headD 0)) :=
  (N.isZ_iff (by rw [← N.length_eq]; exact headD_lt hc)).2
    ((mem_zeroList).1 (headD_mem_zeroList hc)).2

private noncomputable def cls (A : K0LangMark Omega lab p R I phi) (N : K0Normal A)
    (c : List ℕ) (hc : c ∈ compsList A) : KernelComponent (rootCharHom A.a) :=
  ⟦⟨N.K.extRoot (idxNode (c.headD 0)),
    N.K.extRoot_mem_kernelRoots A.rootChar_eq_one_iff (isZ_headD N hc)⟩⟧

omit [CharP Omega 2] in
private theorem componentRoots_cls {A : K0LangMark Omega lab p R I phi} (N : K0Normal A)
    {c : List ℕ} (hc : c ∈ compsList A) :
    componentRoots (rootCharHom A.a) (cls A N c hc) =
      N.K.rootsOf (N.K.comp p A.kacMu (idxNode (c.headD 0))) := by
  have h := N.K.componentRoots_mk_extRoot N.facts N.zero_lt N.isNormal
    (χ := rootCharHom A.a) A.rootChar_eq_one_iff (isZ_headD N hc)
  simpa only [cls] using h

private theorem imgList_iterate_mem_compsList {A : K0LangMark Omega lab p R I phi} (N : K0Normal A)
    {c : List ℕ} (hc : c ∈ compsList A) (t : ℕ) : (imgList A)^[t] c ∈ compsList A := by
  induction t with
  | zero => simpa using hc
  | succ q ih =>
    rw [Function.iterate_succ_apply']
    exact imgList_mem_compsList N ih

private theorem rho_image_componentRoots_cls {A : K0LangMark Omega lab p R I phi} (N : K0Normal A)
    {c : List ℕ} (hc : c ∈ compsList A) :
    (A.setup.ρ : (Fin A.tau.rank → ℤ) → (Fin A.tau.rank → ℤ)) ''
        componentRoots (rootCharHom A.a) (cls A N c hc) =
      componentRoots (rootCharHom A.a) (cls A N (imgList A c)
        (imgList_mem_compsList N hc)) := by
  rw [componentRoots_cls N hc, componentRoots_cls N (imgList_mem_compsList N hc)]
  rw [N.rho_image_rootsOf_comp ⟨c.headD 0, headD_lt hc⟩]
  congr 1
  rw [← piNat_apply (headD_lt hc), comp_imgList_head N hc,
    comp_eq_class N (imgList_mem_compsList N hc)
      (headD_mem_compsList (imgList_mem_compsList N hc))]

private theorem rho_iterate_image_componentRoots_cls {A : K0LangMark Omega lab p R I phi}
    (N : K0Normal A) {c : List ℕ} (hc : c ∈ compsList A) :
    ∀ (t : ℕ) (hc' : (imgList A)^[t] c ∈ compsList A),
      (A.setup.ρ : (Fin A.tau.rank → ℤ) → (Fin A.tau.rank → ℤ))^[t] ''
          componentRoots (rootCharHom A.a) (cls A N c hc) =
        componentRoots (rootCharHom A.a) (cls A N ((imgList A)^[t] c) hc') := by
  intro t
  induction t with
  | zero =>
    intro hc'
    rw [show hc = hc' from Subsingleton.elim hc hc']
    simp
  | succ q ih =>
    intro hc'
    have hstep : (A.setup.ρ : (Fin A.tau.rank → ℤ) → (Fin A.tau.rank → ℤ))^[q + 1] ''
        componentRoots (rootCharHom A.a) (cls A N c hc) =
        (A.setup.ρ : (Fin A.tau.rank → ℤ) → (Fin A.tau.rank → ℤ)) ''
          ((A.setup.ρ : (Fin A.tau.rank → ℤ) → (Fin A.tau.rank → ℤ))^[q] ''
            componentRoots (rootCharHom A.a) (cls A N c hc)) := by
      rw [show (A.setup.ρ : (Fin A.tau.rank → ℤ) → (Fin A.tau.rank → ℤ))^[q + 1] =
          (A.setup.ρ : (Fin A.tau.rank → ℤ) → (Fin A.tau.rank → ℤ)) ∘
            (A.setup.ρ : (Fin A.tau.rank → ℤ) → (Fin A.tau.rank → ℤ))^[q] from by
        funext x
        rw [Function.comp_apply, Function.iterate_succ_apply']]
      rw [Set.image_comp]
    rw [hstep, ih (imgList_iterate_mem_compsList N hc q),
      rho_image_componentRoots_cls N (imgList_iterate_mem_compsList N hc q)]
    have key : ∀ (d : List ℕ) (hd : d ∈ compsList A), d = (imgList A)^[q + 1] c →
        componentRoots (rootCharHom A.a) (cls A N d hd) =
          componentRoots (rootCharHom A.a) (cls A N ((imgList A)^[q + 1] c) hc') := by
      rintro d hd rfl
      rfl
    exact key _ _ (Function.iterate_succ_apply' (imgList A) q c).symm

private theorem componentRoots_inj {τ : Tag} {M : Type*} [CommGroup M]
    (χ : Multiplicative (Fin τ.rank → ℤ) →* M) {i j : KernelComponent χ}
    (h : componentRoots χ i = componentRoots χ j) : i = j := by
  obtain ⟨a, ha⟩ := Quotient.exists_rep i
  have hmem : (a : Fin τ.rank → ℤ) ∈ componentRoots χ i := ⟨a.2, ha⟩
  rw [h] at hmem
  obtain ⟨h', hq⟩ := hmem
  rw [← ha, ← hq]

omit [CharP Omega 2] in
private theorem cls_inj {A : K0LangMark Omega lab p R I phi} (N : K0Normal A)
    {c₁ c₂ : List ℕ} (h₁ : c₁ ∈ compsList A) (h₂ : c₂ ∈ compsList A)
    (h : cls A N c₁ h₁ = cls A N c₂ h₂) : c₁ = c₂ := by
  have hZ : Relation.EqvGen (N.K.ZRel p A.kacMu) (idxNode (c₁.headD 0)) (idxNode (c₂.headD 0)) :=
    (N.K.mk_extRoot_eq_iff N.facts N.zero_lt N.isNormal A.rootChar_eq_one_iff
      (isZ_headD N h₁) (isZ_headD N h₂)).1 h
  have hR : Relation.EqvGen (fun a b => a ∈ zeroList A ∧ b ∈ zeroList A ∧
      0 < A.row.diagram.adj a b) (c₁.headD 0) (c₂.headD 0) :=
    (eqvGen_idxNode_iff N (headD_lt h₁) (headD_lt h₂)
      ((mem_zeroList).1 (headD_mem_zeroList h₁)).2
      ((mem_zeroList).1 (headD_mem_zeroList h₂)).2).1 hZ
  have hspec := k0Comps_spec A.row.diagram (zeroList_nodup A)
  have hmem : ∀ x, x ∈ c₁ ↔ x ∈ c₂ := by
    intro x
    constructor
    · intro hx
      have hx1 : Relation.EqvGen (fun a b => a ∈ zeroList A ∧ b ∈ zeroList A ∧
          0 < A.row.diagram.adj a b) (c₁.headD 0) x :=
        (hspec.2.1 c₁ h₁ (c₁.headD 0) (headD_mem_compsList h₁) x).1 hx
      exact (hspec.2.1 c₂ h₂ (c₂.headD 0) (headD_mem_compsList h₂) x).2
        (Relation.EqvGen.trans _ _ _ hR.symm hx1)
    · intro hx
      have hx2 : Relation.EqvGen (fun a b => a ∈ zeroList A ∧ b ∈ zeroList A ∧
          0 < A.row.diagram.adj a b) (c₂.headD 0) x :=
        (hspec.2.1 c₂ h₂ (c₂.headD 0) (headD_mem_compsList h₂) x).1 hx
      exact (hspec.2.1 c₁ h₁ (c₁.headD 0) (headD_mem_compsList h₁) x).2
        (Relation.EqvGen.trans _ _ _ hR hx2)
  have hperm : c₁.Perm c₂ :=
    (List.perm_ext_iff_of_nodup ((hspec.1 c₁ h₁).2.1.nodup)
      ((hspec.1 c₂ h₂).2.1.nodup)).2 hmem
  exact List.Perm.eq_of_sortedLE
    ((List.sortedLE_iff_pairwise).2 ((hspec.1 c₁ h₁).2.1.imp (fun h => le_of_lt h)))
    ((List.sortedLE_iff_pairwise).2 ((hspec.1 c₂ h₂).2.1.imp (fun h => le_of_lt h))) hperm

omit [CharP Omega 2] in
private theorem exists_cls {A : K0LangMark Omega lab p R I phi} (N : K0Normal A)
    (i : KernelComponent (rootCharHom A.a)) :
    ∃ (c : List ℕ) (hc : c ∈ compsList A), cls A N c hc = i := by
  obtain ⟨x, hx, hix⟩ := N.K.exists_mk_extRoot N.facts N.zero_lt N.isNormal
    (χ := rootCharHom A.a) A.rootChar_eq_one_iff i
  have hk_lt : nodeIdx x < A.row.diagram.marks.length := by
    rw [N.length_eq]; exact nodeIdx_lt x
  have hk' : nodeIdx x < A.tau.rank + 1 := by rw [← N.length_eq]; exact hk_lt
  have hx' : N.K.IsZ p A.kacMu (idxNode (nodeIdx x)) := by rwa [idxNode_nodeIdx]
  have hko : A.row.s.getD (nodeIdx x) 0 = 0 := (N.isZ_iff hk').1 hx'
  have hkz : nodeIdx x ∈ zeroList A := (mem_zeroList).2 ⟨hk_lt, hko⟩
  obtain ⟨c, hc, hxc⟩ := (k0Comps_spec A.row.diagram (zeroList_nodup A)).2.2.1 _ hkz
  refine ⟨c, hc, ?_⟩
  have hclass := (k0Comps_spec A.row.diagram (zeroList_nodup A)).2.1 c hc (c.headD 0)
    (headD_mem_compsList hc) (nodeIdx x)
  have hR : Relation.EqvGen (fun a b => a ∈ zeroList A ∧ b ∈ zeroList A ∧
      0 < A.row.diagram.adj a b) (c.headD 0) (nodeIdx x) := hclass.1 hxc
  have hZ : Relation.EqvGen (N.K.ZRel p A.kacMu) (idxNode (c.headD 0)) (idxNode (nodeIdx x)) :=
    (eqvGen_idxNode_iff N (headD_lt hc) hk_lt
      ((mem_zeroList).1 (headD_mem_zeroList hc)).2 hko).2 hR
  rw [idxNode_nodeIdx] at hZ
  rw [hix]
  exact (N.K.mk_extRoot_eq_iff N.facts N.zero_lt N.isNormal A.rootChar_eq_one_iff
    (isZ_headD N hc) hx).2 hZ

private theorem iterate_image_eq {V : Type*} {ρ : Equiv.Perm V} {Ψ : Set V} {L : ℕ}
    (hper : (ρ : V → V)^[L] '' Ψ = Ψ) (m : ℕ) : (ρ : V → V)^[m * L] '' Ψ = Ψ := by
  induction m with
  | zero => simp
  | succ q ih =>
    rw [Nat.succ_mul]
    rw [show (ρ : V → V)^[q * L + L] = (ρ : V → V)^[q * L] ∘ (ρ : V → V)^[L] from by
      funext x
      rw [Function.comp_apply, Function.iterate_add_apply]]
    rw [Set.image_comp, hper, ih]

omit [CharP Omega 2] in
private theorem rationalRoots_congr_image {A : K0LangMark Omega lab p R I phi} (_N : K0Normal A)
    {i i' : KernelComponent (rootCharHom A.a)} {t L : ℕ} (hL : 0 < L)
    (hcomp : componentRoots (rootCharHom A.a) i =
      (A.setup.ρ : (Fin A.tau.rank → ℤ) → (Fin A.tau.rank → ℤ))^[t] ''
        componentRoots (rootCharHom A.a) i')
    (hper : (A.setup.ρ : (Fin A.tau.rank → ℤ) → (Fin A.tau.rank → ℤ))^[L] ''
        componentRoots (rootCharHom A.a) i' = componentRoots (rootCharHom A.a) i') :
    rationalRoots A.setup.ρ (rootCharHom A.a) i = rationalRoots A.setup.ρ (rootCharHom A.a) i' := by
  ext γ
  constructor
  · rintro ⟨k, δ, hδ, rfl⟩
    rw [hcomp] at hδ
    obtain ⟨δ', hδ', rfl⟩ := hδ
    exact ⟨k + t, δ', hδ', by rw [Function.iterate_add_apply]⟩
  · rintro ⟨k, δ, hδ, rfl⟩
    have htL : t ≤ t * L := by
      calc t = t * 1 := (Nat.mul_one t).symm
        _ ≤ t * L := Nat.mul_le_mul_left t hL
    have hsplit : k + t * L - t + t = k + t * L := Nat.sub_add_cancel (by omega)
    have himg := iterate_image_eq (ρ := A.setup.ρ) hper t
    have hδmem : δ ∈ (A.setup.ρ : (Fin A.tau.rank → ℤ) → (Fin A.tau.rank → ℤ))^[t * L] ''
        componentRoots (rootCharHom A.a) i' := by rw [himg]; exact hδ
    obtain ⟨δ₀, hδ₀, hδ₀δ⟩ := hδmem
    have hγ : (A.setup.ρ : (Fin A.tau.rank → ℤ) → (Fin A.tau.rank → ℤ))^[k] δ =
        (A.setup.ρ : (Fin A.tau.rank → ℤ) → (Fin A.tau.rank → ℤ))^[k + t * L - t]
          ((A.setup.ρ : (Fin A.tau.rank → ℤ) → (Fin A.tau.rank → ℤ))^[t] δ₀) := by
      calc (A.setup.ρ : (Fin A.tau.rank → ℤ) → (Fin A.tau.rank → ℤ))^[k] δ
          = (A.setup.ρ : (Fin A.tau.rank → ℤ) → (Fin A.tau.rank → ℤ))^[k]
              ((A.setup.ρ : (Fin A.tau.rank → ℤ) → (Fin A.tau.rank → ℤ))^[t * L] δ₀) := by
            rw [hδ₀δ]
        _ = (A.setup.ρ : (Fin A.tau.rank → ℤ) → (Fin A.tau.rank → ℤ))^[k + t * L] δ₀ :=
            (Function.iterate_add_apply ..).symm
        _ = (A.setup.ρ : (Fin A.tau.rank → ℤ) → (Fin A.tau.rank → ℤ))^[k + t * L - t + t] δ₀ := by
            rw [hsplit]
        _ = (A.setup.ρ : (Fin A.tau.rank → ℤ) → (Fin A.tau.rank → ℤ))^[k + t * L - t]
              ((A.setup.ρ : (Fin A.tau.rank → ℤ) → (Fin A.tau.rank → ℤ))^[t] δ₀) :=
            Function.iterate_add_apply ..
    refine ⟨k + t * L - t, (A.setup.ρ)^[t] δ₀, ?_, hγ⟩
    rw [hcomp]
    exact ⟨δ₀, hδ₀, rfl⟩

private theorem componentOrbitLength_eq_of_least {τ : Tag} {ρ : Equiv.Perm (Fin τ.rank → ℤ)}
    {Ψ : Set (Fin τ.rank → ℤ)} {L : ℕ} (hLpos : 0 < L) (hLper : (ρ : _ → _)^[L] '' Ψ = Ψ)
    (hleast : ∀ s, 0 < s → (ρ : _ → _)^[s] '' Ψ = Ψ → L ≤ s) :
    componentOrbitLength ρ Ψ = L := by
  unfold componentOrbitLength
  have hnon : {s : ℕ | 0 < s ∧ (ρ : _ → _)^[s] '' Ψ = Ψ}.Nonempty := ⟨L, hLpos, hLper⟩
  have h1 : sInf {s : ℕ | 0 < s ∧ (ρ : _ → _)^[s] '' Ψ = Ψ} ≤ L :=
    Nat.sInf_le ⟨hLpos, hLper⟩
  have h2 : L ≤ sInf {s : ℕ | 0 < s ∧ (ρ : _ → _)^[s] '' Ψ = Ψ} :=
    hleast _ (Nat.sInf_mem hnon).1 (Nat.sInf_mem hnon).2
  omega

private theorem rawOrbit_period_mul {A : K0LangMark Omega lab p R I phi} (N : K0Normal A)
    {o : List (List ℕ)} (ho : o ∈ A.row.rawComponentOrbits) (m : ℕ) :
    (imgList A)^[o.length * m] (o.headD []) = o.headD [] := by
  obtain ⟨hne, hnd, hget, hper, -⟩ := (rawOrbits_facts A N).1 o ho
  induction m with
  | zero => simp
  | succ q ih => rw [Nat.mul_succ, Function.iterate_add_apply, hper, ih]

omit [CharP Omega 2] in
private theorem cls_congr {A : K0LangMark Omega lab p R I phi} (N : K0Normal A)
    {c c' : List ℕ} (h : c = c') (hc : c ∈ compsList A) (hc' : c' ∈ compsList A) :
    cls A N c hc = cls A N c' hc' := by
  cases h
  rfl

omit [CharP Omega 2] in
private theorem componentRoots_cls_congr {A : K0LangMark Omega lab p R I phi} (N : K0Normal A)
    {c c' : List ℕ} (h : c = c') (hc : c ∈ compsList A) (hc' : c' ∈ compsList A) :
    componentRoots (rootCharHom A.a) (cls A N c hc) =
      componentRoots (rootCharHom A.a) (cls A N c' hc') := by
  cases h
  rfl

private theorem rationalRoots_cls_eq_iUnion {A : K0LangMark Omega lab p R I phi} (N : K0Normal A)
    {o : List (List ℕ)} (ho : o ∈ A.row.rawComponentOrbits)
    (hc : o.headD [] ∈ compsList A) :
    rationalRoots A.setup.ρ (rootCharHom A.a) (cls A N (o.headD []) hc) =
      {γ | ∃ t, t < o.length ∧ γ ∈ componentRoots (rootCharHom A.a)
        (cls A N ((imgList A)^[t] (o.headD [])) (imgList_iterate_mem_compsList N hc t))} := by
  have hne : o ≠ [] := ((rawOrbits_facts A N).1 o ho).1
  have hL : 0 < o.length := List.length_pos_iff.2 hne
  have hiter : ∀ (t : ℕ) (hd : (imgList A)^[t] (o.headD []) ∈ compsList A),
      (A.setup.ρ : (Fin A.tau.rank → ℤ) → (Fin A.tau.rank → ℤ))^[t] ''
          componentRoots (rootCharHom A.a) (cls A N (o.headD []) hc) =
        componentRoots (rootCharHom A.a) (cls A N ((imgList A)^[t] (o.headD [])) hd) :=
    fun t hd => rho_iterate_image_componentRoots_cls N hc t hd
  ext γ
  constructor
  · rintro ⟨k, δ, hδ, rfl⟩
    have hdiv : k % o.length + o.length * (k / o.length) = k := by
      rw [Nat.add_comm, Nat.div_add_mod]
    set d : List ℕ := (imgList A)^[o.length * (k / o.length)] (o.headD []) with hd_def
    have hdmem : d ∈ compsList A := imgList_iterate_mem_compsList N hc _
    have hperd : d = o.headD [] := rawOrbit_period_mul N ho (k / o.length)
    have hcls : cls A N d hdmem = cls A N (o.headD []) hc := cls_congr N hperd hdmem hc
    have hiter' : (A.setup.ρ : (Fin A.tau.rank → ℤ) → (Fin A.tau.rank → ℤ))^[o.length * (k / o.length)]
        '' componentRoots (rootCharHom A.a) (cls A N (o.headD []) hc) =
        componentRoots (rootCharHom A.a) (cls A N d hdmem) :=
      rho_iterate_image_componentRoots_cls N hc _ hdmem
    have hδ' : (A.setup.ρ : (Fin A.tau.rank → ℤ) → (Fin A.tau.rank → ℤ))^[o.length * (k / o.length)]
        δ ∈ componentRoots (rootCharHom A.a) (cls A N (o.headD []) hc) := by
      rw [← hcls, ← hiter']
      exact ⟨δ, hδ, rfl⟩
    refine ⟨k % o.length, Nat.mod_lt _ hL, ?_⟩
    rw [← hiter (k % o.length) (imgList_iterate_mem_compsList N hc _)]
    exact ⟨_, hδ', by rw [← Function.iterate_add_apply, hdiv]⟩
  · rintro ⟨t, ht, hγ⟩
    rw [← hiter t (imgList_iterate_mem_compsList N hc t)] at hγ
    obtain ⟨δ, hδ, rfl⟩ := hγ
    exact ⟨t, δ, hδ, rfl⟩

private theorem componentOrbitLength_orbit {A : K0LangMark Omega lab p R I phi} (N : K0Normal A)
    {o : List (List ℕ)} (ho : o ∈ A.row.rawComponentOrbits)
    (hc : o.headD [] ∈ compsList A) :
    componentOrbitLength A.setup.ρ (componentRoots (rootCharHom A.a) (cls A N (o.headD []) hc)) =
      o.length := by
  have hne : o ≠ [] := ((rawOrbits_facts A N).1 o ho).1
  have hL : 0 < o.length := List.length_pos_iff.2 hne
  refine componentOrbitLength_eq_of_least hL ?_ ?_
  · have h := rho_iterate_image_componentRoots_cls N hc o.length (imgList_iterate_mem_compsList N hc _)
    have hcls := componentRoots_cls_congr N (((rawOrbits_facts A N).1 o ho).2.2.2.1)
      (imgList_iterate_mem_compsList N hc o.length) hc
    exact h.trans hcls
  · intro s hs hse
    have himg : (imgList A)^[s] (o.headD []) = o.headD [] := by
      have h1 := rho_iterate_image_componentRoots_cls N hc s (imgList_iterate_mem_compsList N hc s)
      rw [h1] at hse
      have hcls : cls A N ((imgList A)^[s] (o.headD [])) (imgList_iterate_mem_compsList N hc s) =
          cls A N (o.headD []) hc := componentRoots_inj _ hse
      exact cls_inj N _ _ hcls
    obtain ⟨m, rfl⟩ := (imgList_iterate_eq_head_iff N ho hs).1 himg
    have hm : 1 ≤ m := by
      rcases Nat.eq_zero_or_pos m with h | h
      · rw [h, Nat.mul_zero] at hs; exact absurd hs (Nat.lt_irrefl 0)
      · exact h
    calc o.length = o.length * 1 := (Nat.mul_one _).symm
      _ ≤ o.length * m := Nat.mul_le_mul_left _ hm

private theorem orbitNodesOf_disjoint {A : K0LangMark Omega lab p R I phi} (N : K0Normal A)
    {M : List (List (List ℕ))} (hlen : M.length = A.row.D.orbits.length)
    (hM : M.Perm A.row.rawComponentOrbits) {j k : Fin A.row.D.orbits.length} (hjk : j ≠ k)
    {x : List ℕ} (hxj : x ∈ orbitNodesOf A M j) (hxk : x ∈ orbitNodesOf A M k) : False := by
  have hrawnd : A.row.rawComponentOrbits.flatten.Nodup :=
    ((rawOrbits_facts A N).2.nodup_iff).2 (compsList_nodup A)
  have hMnd : M.flatten.Nodup := (hM.flatten.nodup_iff).2 hrawnd
  have hpair : M.Pairwise List.Disjoint := (List.nodup_flatten.1 hMnd).2
  have hjk' : j.val ≠ k.val := fun h => hjk (Fin.ext h)
  have hj' : j.val < M.length := by rw [hlen]; exact j.isLt
  have hk' : k.val < M.length := by rw [hlen]; exact k.isLt
  have hD : List.Disjoint M[j.val] M[k.val] := by
    rcases Nat.lt_or_gt_of_ne hjk' with hlt | hgt
    · exact (List.pairwise_iff_get.1 hpair) ⟨j.val, hj'⟩ ⟨k.val, hk'⟩ hlt
    · exact List.Disjoint.symm
        ((List.pairwise_iff_get.1 hpair) ⟨k.val, hk'⟩ ⟨j.val, hj'⟩ hgt)
  have hxj' : x ∈ M[j.val] := by rwa [orbitNodesOf_getElem hlen j] at hxj
  have hxk' : x ∈ M[k.val] := by rwa [orbitNodesOf_getElem hlen k] at hxk
  exact List.disjoint_left.1 hD hxj' hxk'

private theorem exists_orbit_rationalRoots_eq {A : K0LangMark Omega lab p R I phi} (N : K0Normal A)
    (i : KernelComponent (rootCharHom A.a)) :
    ∃ (o : List (List ℕ)) (_ : o ∈ A.row.rawComponentOrbits)
      (hc : o.headD [] ∈ compsList A),
      rationalRoots A.setup.ρ (rootCharHom A.a) i =
        rationalRoots A.setup.ρ (rootCharHom A.a) (cls A N (o.headD []) hc) := by
  obtain ⟨c, hc, hcls⟩ := exists_cls N i
  have hcflat : c ∈ A.row.rawComponentOrbits.flatten :=
    ((rawOrbits_facts A N).2.mem_iff).2 hc
  obtain ⟨o, ho, hco⟩ := List.mem_flatten.1 hcflat
  have hne : o ≠ [] := ((rawOrbits_facts A N).1 o ho).1
  have hL : 0 < o.length := List.length_pos_iff.2 hne
  have hmem : o.headD [] ∈ o := by
    cases hl : o with
    | nil => exact absurd hl hne
    | cons a as => simp
  have hc' : o.headD [] ∈ compsList A := rawOrbit_subset_comps N ho hmem
  obtain ⟨t, ht, hct⟩ := List.mem_iff_getElem.1 hco
  refine ⟨o, ho, hc', ?_⟩
  have hget := ((rawOrbits_facts A N).1 o ho).2.2.1 t ht
  have htc : (imgList A)^[t] (o.headD []) = c := hget.symm.trans hct
  have hcls' : cls A N ((imgList A)^[t] (o.headD [])) (imgList_iterate_mem_compsList N hc' t) =
      cls A N c hc := cls_congr N htc _ hc
  have hper' : (A.setup.ρ : (Fin A.tau.rank → ℤ) → (Fin A.tau.rank → ℤ))^[o.length] ''
      componentRoots (rootCharHom A.a) (cls A N (o.headD []) hc') =
      componentRoots (rootCharHom A.a) (cls A N (o.headD []) hc') := by
    have h := rho_iterate_image_componentRoots_cls N hc' o.length (imgList_iterate_mem_compsList N hc' _)
    have hcls'' := componentRoots_cls_congr N (((rawOrbits_facts A N).1 o ho).2.2.2.1)
      (imgList_iterate_mem_compsList N hc' o.length) hc'
    exact h.trans hcls''
  have hcomp : componentRoots (rootCharHom A.a) i =
      (A.setup.ρ : (Fin A.tau.rank → ℤ) → (Fin A.tau.rank → ℤ))^[t] ''
        componentRoots (rootCharHom A.a) (cls A N (o.headD []) hc') := by
    rw [← hcls, ← hcls']
    exact (rho_iterate_image_componentRoots_cls N hc' t
      (imgList_iterate_mem_compsList N hc' t)).symm
  exact rationalRoots_congr_image N hL hcomp hper'

omit [CharP Omega 2] in
private theorem componentRoots_cls_eq_span {A : K0LangMark Omega lab p R I phi} (N : K0Normal A)
    {c : List ℕ} (hc : c ∈ compsList A) :
    componentRoots (rootCharHom A.a) (cls A N c hc) =
      {v | IsRoot A.tau v ∧ v ∈ Submodule.span ℤ {w |
        ∃ i : Fin A.row.diagram.marks.length, i.val ∈ c ∧ w = A.nodeMap (Pi.single i 1)}} := by
  rw [componentRoots_cls N hc,
    N.K.rootsOf_comp_eq_span N.facts N.zero_lt N.isNormal,
    comp_eq_class N hc (headD_mem_compsList hc)]
  have hspan : Submodule.span ℤ (N.K.extRoot '' (idxNode '' {k | k ∈ c})) =
      Submodule.span ℤ {w | ∃ i : Fin A.row.diagram.marks.length, i.val ∈ c ∧
        w = A.nodeMap (Pi.single i 1)} := by
    congr 1
    ext w
    simp only [Set.mem_image, Set.mem_ofPred_eq]
    constructor
    · rintro ⟨y, ⟨k, hk, rfl⟩, rfl⟩
      exact ⟨⟨k, ((mem_zeroList).1 (mem_zeroList_of_mem_comps hc hk)).1⟩, hk,
        (N.nodeMap_eq ⟨k, ((mem_zeroList).1 (mem_zeroList_of_mem_comps hc hk)).1⟩).symm⟩
    · rintro ⟨i, hi, rfl⟩
      exact ⟨idxNode i.val, ⟨i.val, hi, rfl⟩, (N.nodeMap_eq i).symm⟩
  rw [hspan]

omit [CharP Omega 2] in
private theorem orbitNodesOf_perm {A : K0LangMark Omega lab p R I phi}
    {M : List (List (List ℕ))} (hlen : M.length = A.row.D.orbits.length)
    (hM : M.Perm A.row.rawComponentOrbits) :
    List.Perm (List.ofFn (orbitNodesOf A M)) A.row.rawComponentOrbits := by
  rw [ofFn_orbitNodesOf hlen]
  exact hM

omit [CharP Omega 2] in
private theorem orbit_descriptor_field {A : K0LangMark Omega lab p R I phi}
    {M : List (List (List ℕ))} (hlen : M.length = A.row.D.orbits.length)
    (hMorb : A.row.D.orbits = M.map A.row.orbitDescriptor)
    (j : Fin A.row.D.orbits.length) :
    A.row.D.orbits[j] = A.row.orbitDescriptor (orbitNodesOf A M j) := by
  have h1 : A.row.D.orbits[j.val] =
      (M.map A.row.orbitDescriptor)[j.val]'(by rw [← hMorb]; exact j.isLt) :=
    List.getElem_of_eq hMorb j.isLt
  have h2 : (M.map A.row.orbitDescriptor)[j.val]'(by rw [← hMorb]; exact j.isLt) =
      A.row.orbitDescriptor (M[j.val]'(by rw [hlen]; exact j.isLt)) :=
    List.getElem_map A.row.orbitDescriptor
  rw [orbitNodesOf_getElem hlen j]
  exact h1.trans h2

omit [CharP Omega 2] in
private theorem field_exp_field {A : K0LangMark Omega lab p R I phi}
    {M : List (List (List ℕ))} (hlen : M.length = A.row.D.orbits.length)
    (hMorb : A.row.D.orbits = M.map A.row.orbitDescriptor)
    (j : Fin A.row.D.orbits.length) :
    A.row.D.orbits[j].lab.n = (orbitNodesOf A M j).length * lab.n := by
  rw [orbit_descriptor_field hlen hMorb j]
  exact orbitDescriptorOf_lab_n _ _ _ _ _

private theorem orbit_cover_field {A : K0LangMark Omega lab p R I phi} (N : K0Normal A)
    {M : List (List (List ℕ))} (hlen : M.length = A.row.D.orbits.length)
    (hM : M.Perm A.row.rawComponentOrbits) (i : KernelComponent (rootCharHom A.a)) :
    ∃ j : Fin A.row.D.orbits.length,
      rationalRoots A.setup.ρ (rootCharHom A.a) i =
        rationalRoots A.setup.ρ (rootCharHom A.a)
          (cls A N ((orbitNodesOf A M j).headD [])
            (orbitNodesOf_headD_mem N hlen hM j)) := by
  obtain ⟨o, ho, hc, heq⟩ := exists_orbit_rationalRoots_eq N i
  have homem : o ∈ M := hM.mem_iff.2 ho
  obtain ⟨i₀, hi₀, hio⟩ := List.mem_iff_getElem.1 homem
  refine ⟨⟨i₀, by rw [← hlen]; exact hi₀⟩, ?_⟩
  have hoj : orbitNodesOf A M ⟨i₀, by rw [← hlen]; exact hi₀⟩ = o := by
    rw [orbitNodesOf_getElem hlen]
    exact hio
  have hd : ((orbitNodesOf A M ⟨i₀, by rw [← hlen]; exact hi₀⟩).headD []) = o.headD [] := by
    rw [hoj]
  have hcls : cls A N ((orbitNodesOf A M ⟨i₀, by rw [← hlen]; exact hi₀⟩).headD [])
        (orbitNodesOf_headD_mem N hlen hM ⟨i₀, by rw [← hlen]; exact hi₀⟩) =
      cls A N (o.headD []) hc := cls_congr N hd _ hc
  rw [hcls]
  exact heq

private theorem orbit_length_field {A : K0LangMark Omega lab p R I phi} (N : K0Normal A)
    {M : List (List (List ℕ))} (hlen : M.length = A.row.D.orbits.length)
    (hM : M.Perm A.row.rawComponentOrbits) (j : Fin A.row.D.orbits.length) :
    componentOrbitLength A.setup.ρ
        (componentRoots (rootCharHom A.a)
          (cls A N ((orbitNodesOf A M j).headD []) (orbitNodesOf_headD_mem N hlen hM j))) =
      (orbitNodesOf A M j).length :=
  componentOrbitLength_orbit N (orbitNodesOf_mem hlen hM j) _

private theorem orbit_distinct_field {A : K0LangMark Omega lab p R I phi} (N : K0Normal A)
    {M : List (List (List ℕ))} (hlen : M.length = A.row.D.orbits.length)
    (hM : M.Perm A.row.rawComponentOrbits) {j k : Fin A.row.D.orbits.length} (hjk : j ≠ k) :
    Disjoint
      (rationalRoots A.setup.ρ (rootCharHom A.a)
        (cls A N ((orbitNodesOf A M j).headD []) (orbitNodesOf_headD_mem N hlen hM j)))
      (rationalRoots A.setup.ρ (rootCharHom A.a)
        (cls A N ((orbitNodesOf A M k).headD []) (orbitNodesOf_headD_mem N hlen hM k))) := by
  rw [Set.disjoint_left]
  intro γ hγj hγk
  rw [rationalRoots_cls_eq_iUnion N (orbitNodesOf_mem hlen hM j)
    (orbitNodesOf_headD_mem N hlen hM j)] at hγj
  rw [rationalRoots_cls_eq_iUnion N (orbitNodesOf_mem hlen hM k)
    (orbitNodesOf_headD_mem N hlen hM k)] at hγk
  obtain ⟨t, ht, htj⟩ := hγj
  obtain ⟨u, hu, huk⟩ := hγk
  have hcls : cls A N ((imgList A)^[t] ((orbitNodesOf A M j).headD []))
        (imgList_iterate_mem_compsList N (orbitNodesOf_headD_mem N hlen hM j) t) =
      cls A N ((imgList A)^[u] ((orbitNodesOf A M k).headD []))
        (imgList_iterate_mem_compsList N (orbitNodesOf_headD_mem N hlen hM k) u) := by
    obtain ⟨h1, hq1⟩ := htj
    obtain ⟨h2, hq2⟩ := huk
    rw [← hq1, ← hq2]
  have himg := cls_inj N (imgList_iterate_mem_compsList N (orbitNodesOf_headD_mem N hlen hM j) t)
    (imgList_iterate_mem_compsList N (orbitNodesOf_headD_mem N hlen hM k) u) hcls
  exact orbitNodesOf_disjoint N hlen hM hjk
    (rawOrbit_iterate_mem N (orbitNodesOf_mem hlen hM j) t)
    (himg ▸ rawOrbit_iterate_mem N (orbitNodesOf_mem hlen hM k) u)

theorem k0Positions_nonempty (A : K0LangMark Omega lab p R I phi) : Nonempty (K0Positions A) := by
  obtain ⟨N⟩ := k0Normal_nonempty A
  obtain ⟨M, hMperm, hMdescr⟩ := A.row.exists_perm_orbits
  have hlen : M.length = A.row.D.orbits.length := by rw [hMdescr]; simp
  exact ⟨{ repr := fun j => cls A N ((orbitNodesOf A M j).headD [])
              (orbitNodesOf_headD_mem N hlen hMperm j),
            orbitNodes := orbitNodesOf A M,
            orbitNodes_perm := orbitNodesOf_perm hlen hMperm,
            orbit_descriptor := fun j => orbit_descriptor_field hlen hMdescr j,
            repr_roots := fun j =>
              componentRoots_cls_eq_span N (orbitNodesOf_headD_mem N hlen hMperm j),
            orbit_cover := fun i => orbit_cover_field N hlen hMperm i,
            orbit_distinct := fun j k hjk => orbit_distinct_field N hlen hMperm hjk,
            orbit_length := fun j => orbit_length_field N hlen hMperm j,
            field_exp := fun j => field_exp_field hlen hMdescr j }⟩

end CFSG.StandardType.GGK0MarkedKacIface1587

end
