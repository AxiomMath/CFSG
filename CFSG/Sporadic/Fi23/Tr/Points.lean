module

public import CFSG.Sporadic.Fi23.Tr.Parts
public import CFSG.Fischer.Uniq.LocalHyperoval
public import CFSG.Sporadic.Fi23.Tr.Defs

public section

namespace CFSG.Sporadic.Fi23

open CFSG.Blueprint.Fischer CFSG.Fischer CFSG.F3.Native Native CFSG.Sporadic.Th
  CFSG.Sporadic.Th.Native CFSG.Perm CFSG.Perm.Native

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

@[expose] def pset (B : PBits) : Set (Fin 31671) := {x | pBit B x.val = true}

@[expose] noncomputable def dsetP
    (B : PBits) : Set D23 := ptD23 '' pset B

theorem mem_pset {B : PBits} {x : Fin 31671} : x ∈ pset B ↔ pBit B x.val = true := Iff.rfl

theorem ptD23_mem_dsetP
    {B : PBits} {i : Fin 31671} : ptD23 i ∈ dsetP B ↔ pBit B i.val = true := by
  unfold dsetP
  rw [ptD23.injective.mem_set_image]
  rfl

theorem mem_dsetP
    {B : PBits} {x : D23} : x ∈ dsetP B ↔ pBit B (ptD23.symm x).val = true := by
  rw [← ptD23.apply_symm_apply x, ptD23_mem_dsetP, Equiv.apply_symm_apply]

theorem dsetP_eq_of_pBit
    {A B : PBits} (h : ∀ x < 31671, pBit A x = pBit B x) :
    dsetP A = dsetP B := by
  ext y
  rw [mem_dsetP, mem_dsetP, h _ (ptD23.symm y).2]

theorem pBit_eq_of_dsetP_eq
    {A B : PBits} (h : dsetP A = dsetP B) {x : ℕ} (hx : x < 31671) :
    pBit A x = pBit B x := by
  have h' := congrArg (fun S => ptD23 ⟨x, hx⟩ ∈ S) h
  simp only [ptD23_mem_dsetP, eq_iff_iff] at h'
  cases hA : pBit A x <;> cases hB : pBit B x <;> simp_all

theorem ptD23_val'
    (i : Fin 31671) : (ptD23 i : J) = conjPt i.val := rfl

theorem conjPerm_ptD23 (g : J) (i : Fin 31671) :
    Pair.conjPerm pair_J g (ptD23 i) = ptD23 (g • i) := by
  apply Subtype.ext
  rw [Pair.conjPerm_apply, ptD23_val', ptD23_val', conjPt_smul]

theorem conjPerm_image_ptD23 (g : J) (S : Set (Fin 31671)) :
    ⇑(Pair.conjPerm pair_J g) '' (ptD23 '' S) = ptD23 '' ((fun x => g • x) '' S) := by
  rw [Set.image_image, Set.image_image]
  simp only [conjPerm_ptD23]

theorem smul_val_of_rep
    {g : J} {T : Table} (hT : Rep 31671 T g) (i : Fin 31671) :
    (g • i).val = ap T i.val := by
  rw [hT i.val i.2, idx_of_lt g i.2]

theorem ap_lt_of_rep
    {g : J} {T : Table} (hT : Rep 31671 T g) {i : ℕ} (hi : i < 31671) :
    ap T i < 31671 := by
  rw [hT i hi]
  exact idx_lt g hi

theorem image_pset
    {T : Table} {g : J} (hT : Rep 31671 T g) {A B : PBits}
    (h : pMaps T A B = true) : (fun x => g • x) '' pset A = pset B := by
  have key : ∀ x : Fin 31671, g • x ∈ pset B ↔ x ∈ pset A := by
    intro x
    rw [mem_pset, mem_pset, smul_val_of_rep hT, pMaps_spec h x.2]
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact (key x).2 hx
  · intro hy
    refine ⟨g⁻¹ • y, (key _).1 ?_, smul_inv_smul g y⟩
    rwa [smul_inv_smul]

theorem conjPerm_image_dsetP
    {T : Table} {g : J} (hT : Rep 31671 T g) {A B : PBits}
    (h : pMaps T A B = true) : ⇑(Pair.conjPerm pair_J g) '' dsetP A = dsetP B := by
  unfold dsetP
  rw [conjPerm_image_ptD23, image_pset hT h]

theorem pBit_cB
    {x : ℕ} (hx : x < 31671) : pBit cB x = true ↔ x ∈ cData := by
  rw [trMemOK_spec tr_parts.2.2.1 hx, Array.contains_iff_mem]

theorem pBit_tB
    {x : ℕ} (hx : x < 31671) : pBit tB x = true ↔ x ∈ trData := by
  rw [trMemOK_spec tr_parts.2.2.2.1 hx, Array.contains_iff_mem]

theorem cRoot_eq :
    cRoot = dsetP cB := by
  unfold cRoot dsetP pset
  congr 1
  ext x
  exact (pBit_cB x.2).symm

theorem trRoot_eq :
    trRoot = dsetP tB := by
  unfold trRoot dsetP pset
  congr 1
  ext x
  exact (pBit_tB x.2).symm

theorem ptD23_mem_cRoot
    {x : Fin 31671} : ptD23 x ∈ cRoot ↔ pBit cB x.val = true := by
  rw [cRoot_eq, ptD23_mem_dsetP]

theorem ptD23_mem_trRoot
    {x : Fin 31671} : ptD23 x ∈ trRoot ↔ pBit tB x.val = true := by
  rw [trRoot_eq, ptD23_mem_dsetP]

theorem ptD23_mem_cRoot'
    {x : ℕ} (hx : x < 31671) : ptD23 ⟨x, hx⟩ ∈ cRoot ↔ pBit cB x = true :=
  ptD23_mem_cRoot

theorem ptD23_mem_trRoot'
    {x : ℕ} (hx : x < 31671) :
    ptD23 ⟨x, hx⟩ ∈ trRoot ↔ pBit tB x = true :=
  ptD23_mem_trRoot

theorem conjPt_mem_cRoot
    {x : ℕ} (hx : x < 31671) (hB : pBit cB x = true) :
    conjPt x ∈ Subtype.val '' cRoot :=
  ⟨ptD23 ⟨x, hx⟩, (ptD23_mem_cRoot' hx).2 hB, rfl⟩

theorem conjPt_mem_trRoot
    {x : ℕ} (hx : x < 31671) (hB : pBit tB x = true) :
    conjPt x ∈ Subtype.val '' trRoot :=
  ⟨ptD23 ⟨x, hx⟩, (ptD23_mem_trRoot' hx).2 hB, rfl⟩

theorem cRoot_subset_trRoot :
    cRoot ⊆ trRoot := by
  intro x hx
  rw [← ptD23.apply_symm_apply x] at hx ⊢
  rw [ptD23_mem_cRoot] at hx
  rw [ptD23_mem_trRoot]
  exact ((trGensOK_spec tr_parts.2.2.2.2.2.1).2.2.2.2 _ (ptD23.symm x).2).2.2 hx

theorem tauAct_eq_act23
    (k m : ℕ) : tauAct orb dT biT k m = act23 k m := rfl

theorem act23_lt {k m : ℕ} (hm : m < 31671) : act23 k m < 31671 := by
  rw [act23_spec k m hm]
  exact idx_lt _ hm

theorem conjPt_conj_act23 {k m : ℕ} (hm : m < 31671) :
    conjPt k * conjPt m * (conjPt k)⁻¹ = conjPt (act23 k m) :=
  (idx_eq_iff hm (act23_lt hm)).1 (act23_spec k m hm).symm

theorem conjPt_mem_D23 {k : ℕ} (hk : k < 31671) : conjPt k ∈ D23 :=
  (isConj_d_iff _).2 ⟨⟨k, hk⟩, rfl⟩

theorem conjPt_inv'
    {k : ℕ} (hk : k < 31671) : (conjPt k)⁻¹ = conjPt k :=
  Pair.inv_eq pair_J (conjPt_mem_D23 hk)

theorem conjPt_mul_conjPt
    {k m : ℕ} (hk : k < 31671) (hm : m < 31671) :
    conjPt k * conjPt m * conjPt k = conjPt (act23 k m) := by
  rw [← conjPt_conj_act23 hm, conjPt_inv' hk]

theorem conjPt_injOn
    {i j : ℕ} (hi : i < 31671) (hj : j < 31671) (h : conjPt i = conjPt j) :
    i = j :=
  conjPt_inj (by rw [orb_size]; exact hi) (by rw [orb_size]; exact hj) h

theorem conjPt_commute_iff
    {k m : ℕ} (hk : k < 31671) (hm : m < 31671) :
    conjPt k * conjPt m = conjPt m * conjPt k ↔ act23 k m = m := by
  rw [← Pair.mul_mul_eq_self_iff pair_J (conjPt_mem_D23 hk), conjPt_mul_conjPt hk hm]
  exact ⟨fun h => conjPt_injOn (act23_lt hm) hm h, fun h => by rw [h]⟩

theorem ptD23_commute_iff (i j : Fin 31671) :
    (ptD23 i : J) * ptD23 j = ptD23 j * ptD23 i ↔ act23 i.val j.val = j.val :=
  conjPt_commute_iff i.2 j.2

theorem act23_comm
    {k m : ℕ} (hk : k < 31671) (hm : m < 31671) (h : act23 k m = m) :
    act23 m k = k :=
  (conjPt_commute_iff hm hk).1 ((conjPt_commute_iff hk hm).2 h).symm

theorem tv_ptD23 (i j : Fin 31671) :
    (pairModel pair_J).tv (ptD23 i) (ptD23 j) = ptD23 ⟨act23 i.val j.val, act23_lt j.2⟩ := by
  apply Subtype.ext
  rw [pairModel_tv, ptD23_val', ptD23_val', ptD23_val', conjPt_mul_conjPt i.2 j.2]

theorem tv_eq_conjPerm (p : D23) :
    ⇑((pairModel pair_J).tv p) = ⇑(Pair.conjPerm pair_J (p : J)) := by
  funext y
  apply Subtype.ext
  rw [pairModel_tv, Pair.conjPerm_apply, Pair.inv_eq pair_J p.2]

theorem lK_get
    {l : ℕ} (hl : l < 9) : lK[l]! = treeActTab orb dT biT cGens[l]! := by
  have hs : l < (cGens.map fun g => treeActTab orb (dTable orb) (genTables orb (-2)) g).size := by
    rw [Array.size_map, cGens_size]
    exact hl
  rw [lK_eq, trLetters, getElem!_pos _ l hs, Array.getElem_map,
    getElem!_pos cGens l (by rw [cGens_size]; exact hl), dT_eq, biT_eq]

theorem rep_lK
    {l : ℕ} (hl : l < 9) : Rep 31671 lK[l]! (conjPt cGens[l]!) := by
  rw [lK_get hl]
  exact rep_actTab _

end CFSG.Sporadic.Fi23
