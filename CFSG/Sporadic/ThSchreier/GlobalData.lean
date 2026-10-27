
module

public import CFSG.Sporadic.ThSchreier.GlobalDataBase

public import CFSG.Sporadic.ThSchreier.BFS
public import CFSG.Sporadic.ThSchreier.Row

public section

namespace CFSG.Sporadic.ThSchreier

open CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Sporadic.Th.Max3 CFSG.Sporadic.LySchreier
  Pointwise

noncomputable abbrev planeX :
    Set (Set RowV) := MulAction.orbit J planeWSet

@[expose] noncomputable def planeGens : List (Set RowV → Set RowV) :=
  [fun U => a • U, fun U => b • U]

open Classical in
@[expose] noncomputable def iotaList : List (Set RowV) :=
  bfsList planeGens planeWSet planeX.ncard

@[expose] noncomputable def nPlanes : ℕ := iotaList.length

theorem planeX_finite : planeX.Finite := Set.toFinite _

theorem closure_ab_J :
    Subgroup.closure ({a, b} : Set J) = ⊤ := closure_ab

open Classical in
theorem iotaList_facts :
    iotaList.Nodup ∧ (∀ U, U ∈ iotaList ↔ U ∈ planeX) ∧ iotaList.length ≤ planeX.ncard :=
  bfsList_orbit closure_ab_J planeWSet planeX_finite le_rfl

theorem iotaList_nodup : iotaList.Nodup := iotaList_facts.1

theorem mem_iotaList
    {U : Set RowV} : U ∈ iotaList ↔ U ∈ planeX := iotaList_facts.2.1 U

open Classical in
theorem iotaList_stable {N : ℕ} (hN : planeX.ncard ≤ N) :
    bfsList planeGens planeWSet N = iotaList :=
  bfsList_stable planeGens planeWSet iotaList_facts.2.2 hN

theorem nPlanes_eq_ncard : nPlanes = planeX.ncard := by
  classical
  rw [nPlanes, ← List.toFinset_card_of_nodup iotaList_nodup, ← Set.ncard_coe_finset]
  congr 1
  ext U
  simp [mem_iotaList]

@[expose] noncomputable def iota
    (i : Fin nPlanes) : Set RowV := iotaList[i.val]'i.isLt

theorem iota_mem (i : Fin nPlanes) : iota i ∈ planeX :=
  mem_iotaList.1 (List.getElem_mem _)

theorem iota_injective : Function.Injective iota := by
  intro i j h
  exact Fin.ext ((List.Nodup.getElem_inj_iff iotaList_nodup).1 h)

theorem iota_surjective
    {U : Set RowV} (hU : U ∈ planeX) : ∃ i, iota i = U := by
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem (mem_iotaList.2 hU)
  exact ⟨⟨i, hi⟩, rfl⟩

@[expose] noncomputable def iotaEquiv : Fin nPlanes ≃ planeX :=
  Equiv.ofBijective (fun i => ⟨iota i, iota_mem i⟩)
    ⟨fun i j h => iota_injective (congrArg Subtype.val h),
      fun U => by
        obtain ⟨i, hi⟩ := iota_surjective U.2
        exact ⟨i, Subtype.ext hi⟩⟩

theorem iotaEquiv_apply
    (i : Fin nPlanes) : (iotaEquiv i : Set RowV) = iota i := rfl

theorem iota_zero_eq
    (h : 0 < nPlanes) : iota ⟨0, h⟩ = planeWSet := by
  classical
  have := bfsList_getElem?_zero planeGens planeWSet planeX.ncard
  rw [iota]
  exact Option.some_injective _ ((List.getElem?_eq_getElem h).symm.trans this)

theorem nPlanes_pos : 0 < nPlanes := by
  classical
  exact bfsList_length_pos planeGens planeWSet planeX.ncard

open Classical in
@[expose] noncomputable def parentIdx (i : ℕ) : ℕ :=
  if i = 0 then 0 else discParent planeGens iotaList i

open Classical in
@[expose] noncomputable def labelIdx (i : ℕ) : ℕ :=
  if i = 0 then 0 else discGen planeGens iotaList i + 1

@[expose] noncomputable def labelGen
    (l : ℕ) : J := if l = 1 then a else b

@[expose] noncomputable def transversal (i : ℕ) : J :=
  if _h : 0 < i ∧ parentIdx i < i then labelGen (labelIdx i) * transversal (parentIdx i) else 1
termination_by i
decreasing_by exact _h.2

theorem transversal_zero : transversal 0 = 1 := by
  rw [transversal]
  simp

theorem parentIdx_lt
    {i : ℕ} (hi : i < nPlanes) (h0 : 0 < i) : parentIdx i < i := by
  classical
  rw [parentIdx, ite_eq_right (by omega)]
  exact bfsList_discParent_lt planeGens planeWSet planeX.ncard
    (List.getElem?_eq_getElem hi) h0

theorem transversal_of_pos {i : ℕ} (hi : i < nPlanes) (h0 : 0 < i) :
    transversal i = labelGen (labelIdx i) * transversal (parentIdx i) := by
  rw [transversal, dite_eq_left ⟨h0, parentIdx_lt hi h0⟩]

theorem disc_record {i : ℕ} (hi : i < nPlanes) (h0 : 0 < i) :
    (labelIdx i = 1 ∨ labelIdx i = 2) ∧ ∃ hp : parentIdx i < nPlanes,
      iota ⟨i, hi⟩ = labelGen (labelIdx i) • iota ⟨parentIdx i, hp⟩ := by
  classical
  have hdisc := bfsList_exists_isDisc planeGens planeWSet planeX.ncard
    (List.getElem?_eq_getElem hi) h0
  obtain ⟨g, z, hg, hz, hj⟩ := discParent_spec planeGens iotaList hdisc
  have hlt : discGen planeGens iotaList i < 2 := discGen_lt planeGens iotaList hdisc
  have hpl : discParent planeGens iotaList i < nPlanes := by
    have := (List.getElem?_eq_some_iff.1 hz).1
    exact this
  have hpar : parentIdx i = discParent planeGens iotaList i := by
    rw [parentIdx, ite_eq_right (by omega)]
  have hlab : labelIdx i = discGen planeGens iotaList i + 1 := by
    rw [labelIdx, ite_eq_right (by omega)]
  refine ⟨by omega, hpar ▸ hpl, ?_⟩
  have hz' : z = iota ⟨parentIdx i, hpar ▸ hpl⟩ := by
    have h1 : iotaList[parentIdx i]? = some z := by rw [hpar]; exact hz
    have h2 : iotaList[parentIdx i]? = some (iota ⟨parentIdx i, hpar ▸ hpl⟩) :=
      List.getElem?_eq_getElem (hpar ▸ hpl)
    exact Option.some_injective _ (h1.symm.trans h2)
  have hj' : iota ⟨i, hi⟩ = g z := by
    have h2 : iotaList[i]? = some (iota ⟨i, hi⟩) := List.getElem?_eq_getElem hi
    exact Option.some_injective _ (h2.symm.trans hj)
  rw [hj', hz']
  rcases (by omega : discGen planeGens iotaList i = 0 ∨ discGen planeGens iotaList i = 1) with
    h | h
  · rw [h] at hg hlab
    simp only [planeGens, List.getElem?_cons_zero, Option.some.injEq] at hg
    rw [hlab, ← hg]
    rfl
  · rw [h] at hg hlab
    simp only [planeGens, List.getElem?_cons_succ, List.getElem?_cons_zero,
      Option.some.injEq] at hg
    rw [hlab, ← hg]
    rfl

theorem transversal_smul
    (i : Fin nPlanes) : transversal i • planeWSet = iota i := by
  obtain ⟨i, hi⟩ := i
  induction i using Nat.strong_induction_on with
  | _ i ih =>
    rcases Nat.eq_zero_or_pos i with rfl | h0
    · rw [transversal_zero, one_smul, iota_zero_eq]
    · obtain ⟨-, hp, he⟩ := disc_record hi h0
      rw [transversal_of_pos hi h0, mul_smul, ih _ (parentIdx_lt hi h0) hp, he]

noncomputable instance instMulActionIndex :
    MulAction J (Fin nPlanes) := iotaEquiv.mulAction J

@[expose] noncomputable def phi :
    J →* Equiv.Perm (Fin nPlanes) := MulAction.toPermHom J _

@[expose] noncomputable def alphaPerm :
    Equiv.Perm (Fin nPlanes) := phi a

@[expose] noncomputable def betaPerm :
    Equiv.Perm (Fin nPlanes) := phi b

theorem iota_smul
    (g : J) (i : Fin nPlanes) : iota (g • i) = g • iota i := by
  have h : iotaEquiv (g • i) = g • iotaEquiv i := by
    show iotaEquiv (iotaEquiv.symm (g • iotaEquiv i)) = g • iotaEquiv i
    rw [Equiv.apply_symm_apply]
  have := congrArg Subtype.val h
  exact this

theorem iota_phi
    (g : J) (i : Fin nPlanes) : iota (phi g i) = g • iota i := iota_smul g i

theorem isRows_matRows (g : J) : IsRows (matRows (toMat g)) g := by
  refine ⟨by simp [matRows], fun r hr => ?_, ?_⟩
  · obtain ⟨i, rfl⟩ := Array.mem_ofFn.1 hr
    exact V4.ofFn_wf _
  · ext i j
    rw [rowsMatrix_apply]
    simp only [matRows, Array.getElem?_ofFn, Fin.is_lt, ↓reduceDIte, Option.getD_some]
    rw [V4.toVec_ofFn]
    simp only [Fin.is_lt, ↓reduceDIte, Fin.eta]
    have hz : ∀ c : ZMod 2, c = 0 ∨ c = 1 := by decide
    rcases hz (toMat g i j) with h | h <;> simp [h]

theorem smul_rowPlane (g : J) (k : Key) :
    g • rowPlane k = rowPlane (imageKey (frTable (matRows (toMat g⁻¹))) k) :=
  (rowPlane_imageKey (isRows_matRows g⁻¹) k).symm

theorem imageKey_canonical
    (g : J) {k : Key} (hk : k.isCanonical = true) :
    (imageKey (frTable (matRows (toMat g⁻¹))) k).isCanonical = true := by
  obtain ⟨hu0', hv0', huv'⟩ := Key.toVec_of_isCanonical hk
  have hinj : Function.Injective fun w : RowV => g • w := MulAction.injective g
  have hvec (w : V4) : toRow (frApply (frTable (matRows (toMat g⁻¹))) w).toVec =
      g • toRow w.toVec := by
    rw [rowSmul_def, frApply_frTable_vecMul, (isRows_matRows g⁻¹).eq]
    rfl
  have hne (w : V4) (hw : w.toVec ≠ 0) :
      (frApply (frTable (matRows (toMat g⁻¹))) w).toVec ≠ 0 := by
    intro e
    have h1 := hvec w
    rw [e, toRow_zero, ← rowSmul_zero g] at h1
    exact hw (congrArg ofRow (hinj h1.symm))
  unfold imageKey
  refine canon_isCanonical (frApply_matRows_wf _ _) (frApply_matRows_wf _ _) (hne _ hu0')
    (hne _ hv0') ?_
  intro e
  have h1 := hvec k.u
  have h2 := hvec k.v
  rw [e, h2] at h1
  exact huv' (congrArg ofRow (hinj h1)).symm

theorem exists_unique_canonical_key
    {U : Set RowV} (hU : U ∈ planeX) :
    ∃! k : Key, k.isCanonical = true ∧ rowPlane k = U := by
  obtain ⟨g, rfl⟩ := hU
  refine ⟨imageKey (frTable (matRows (toMat g⁻¹))) wKeyRow,
    ⟨imageKey_canonical g wKeyRow_canonical, ?_⟩, fun k ⟨hk, hkU⟩ => ?_⟩
  · rw [← smul_rowPlane, rowPlane_wKeyRow]
  · refine eq_of_rowPlane_eq hk (imageKey_canonical g wKeyRow_canonical) ?_
    rw [hkU, ← smul_rowPlane, rowPlane_wKeyRow]

theorem cert_Th_global_plane_enumeration_data :
    Module.finrank (ZMod 2) planeW = 2 ∧
    (∀ U ∈ planeX, ∃! k : Key, k.isCanonical = true ∧ rowPlane k = U) ∧
    planeX.Finite ∧
    (∀ N, planeX.ncard ≤ N → bfsList planeGens planeWSet N = iotaList) ∧
    iotaList.Nodup ∧ (∀ U, U ∈ iotaList ↔ U ∈ planeX) ∧ nPlanes = planeX.ncard ∧
    Function.Bijective (fun i => (⟨iota i, iota_mem i⟩ : planeX)) ∧
    iota ⟨0, nPlanes_pos⟩ = planeWSet ∧
    (∀ (i : ℕ) (hi : i < nPlanes) (h0 : 0 < i), parentIdx i < i ∧
      (labelIdx i = 1 ∨ labelIdx i = 2) ∧
      iota ⟨i, hi⟩ = labelGen (labelIdx i) • iota ⟨parentIdx i, by
        have := parentIdx_lt hi h0; omega⟩) ∧
    (∀ i : Fin nPlanes, transversal i • planeWSet = iota i) ∧
    (∀ (g : J) (i : Fin nPlanes), iota (phi g i) = g • iota i) := by
  classical
  refine ⟨finrank_planeW, fun U hU => exists_unique_canonical_key hU, planeX_finite,
    fun N hN => iotaList_stable hN, iotaList_nodup, fun U => mem_iotaList, nPlanes_eq_ncard,
    iotaEquiv.bijective, iota_zero_eq _, fun i hi h0 => ?_, transversal_smul, iota_phi⟩
  obtain ⟨hl, hp, he⟩ := disc_record hi h0
  exact ⟨parentIdx_lt hi h0, hl, he⟩

end CFSG.Sporadic.ThSchreier
