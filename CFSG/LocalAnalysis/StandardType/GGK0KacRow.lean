module

public import CFSG.LocalAnalysis.StandardType.GGK0KacPart
public import CFSG.LocalAnalysis.StandardType.GGK0KacList
public import CFSG.LocalAnalysis.StandardType.GGFinModelRat
import CFSG.LieType.Chevalley.AlgebraicClosurePrimeField

public section

namespace CFSG.StandardType.GGK0MarkedKacIface1587

open CFSG.Assembly CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.AlgebraicGroups
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.StandardType.GGFinModel






theorem k0_getD_lt_of_perm {l : List ℕ} {n i : ℕ} (hl : l.Perm (List.range n))
    (hi : i < n) : l.getD i 0 < n := by
  have hi' : i < l.length := by rw [hl.length_eq, List.length_range]; exact hi
  have hmem : l.getD i 0 ∈ l := by
    rw [List.getD_eq_getElem l 0 hi']
    exact List.getElem_mem hi'
  have hmem' := hl.subset hmem
  simpa using hmem'

private theorem k0_nodup_of_perm {l : List ℕ} {n : ℕ} (hl : l.Perm (List.range n)) :
    l.Nodup :=
  hl.symm.nodup List.nodup_range

private theorem k0_exists_getD_of_perm {n : ℕ} {a : List ℕ} (ha : a.Perm (List.range n))
    {j : ℕ} (hj : j < n) : ∃ i, i < n ∧ a.getD i 0 = j := by
  have hmem : j ∈ a := ha.symm.subset (List.mem_range.mpr hj)
  obtain ⟨i, hi, hget⟩ := List.getElem_of_mem hmem
  have hin : i < n := by rw [ha.length_eq, List.length_range] at hi; exact hi
  exact ⟨i, hin, by rw [List.getD_eq_getElem a 0 hi, hget]⟩

theorem k0_list_ext_getD {l₁ l₂ : List ℕ} (hlen : l₁.length = l₂.length)
    (h : ∀ i, i < l₁.length → l₁.getD i 0 = l₂.getD i 0) : l₁ = l₂ := by
  apply List.ext_getElem hlen
  intro i h1 h2
  rw [← List.getD_eq_getElem l₁ 0 h1, ← List.getD_eq_getElem l₂ 0 h2]
  exact h i h1

private noncomputable def k0NodeEquiv (T : GGKacType) :
    Fin (k0DiagOf T).marks.length ≃ Option (Fin (absTag T).rank) :=
  Equiv.ofBijective (fun i => idxNode (r := (absTag T).rank) i.val) (by
    have hlen := k0Kac_marks_length T
    constructor
    · intro i j hij
      have hi : i.val < (absTag T).rank + 1 := by rw [← hlen]; exact i.isLt
      have hj : j.val < (absTag T).rank + 1 := by rw [← hlen]; exact j.isLt
      have h : i.val = j.val := by
        have hc := congrArg (nodeIdx (r := (absTag T).rank)) hij
        rwa [nodeIdx_idxNode hi, nodeIdx_idxNode hj] at hc
      exact Fin.ext h
    · intro x
      exact ⟨⟨nodeIdx x, by rw [hlen]; exact nodeIdx_lt x⟩, idxNode_nodeIdx x⟩)

private theorem k0NodeEquiv_apply (T : GGKacType)
    (i : Fin (k0DiagOf T).marks.length) :
    k0NodeEquiv T i = idxNode (r := (absTag T).rank) i.val := rfl

private theorem k0NodeEquiv_symm_apply (T : GGKacType)
    (x : Option (Fin (absTag T).rank)) :
    (k0NodeEquiv T).symm x =
      ⟨nodeIdx x, by rw [k0Kac_marks_length T]; exact nodeIdx_lt x⟩ := by
  apply (k0NodeEquiv T).injective
  rw [Equiv.apply_symm_apply, k0NodeEquiv_apply, idxNode_nodeIdx]

private theorem k0NodeEquiv_symm_apply_idxNode (T : GGKacType)
    (i : Fin (k0DiagOf T).marks.length) :
    (k0NodeEquiv T).symm (idxNode (r := (absTag T).rank) i.val) = i := by
  rw [← k0NodeEquiv_apply T i, Equiv.symm_apply_apply]

private noncomputable def k0FinPermOfList {n : ℕ} (l : List ℕ)
    (hl : l.Perm (List.range n)) : Equiv.Perm (Fin n) :=
  Equiv.ofBijective (fun i : Fin n => ⟨l.getD i.val 0, k0_getD_lt_of_perm hl i.isLt⟩) (by
    constructor
    · intro i j hij
      apply Fin.ext
      have h : l.getD i.val 0 = l.getD j.val 0 := congrArg Fin.val hij
      have hi : i.val < l.length := by rw [hl.length_eq, List.length_range]; exact i.isLt
      have hj : j.val < l.length := by rw [hl.length_eq, List.length_range]; exact j.isLt
      rw [List.getD_eq_getElem l 0 hi, List.getD_eq_getElem l 0 hj] at h
      exact (k0_nodup_of_perm hl).eq_of_getElem_eq hi hj h
    · intro y
      have hmem : y.val ∈ l := hl.symm.subset (List.mem_range.mpr y.isLt)
      obtain ⟨i, hi, hget⟩ := List.getElem_of_mem hmem
      have hin : i < n := by rw [hl.length_eq, List.length_range] at hi; exact hi
      exact ⟨⟨i, hin⟩, by
        apply Fin.ext
        show l.getD i 0 = y.val
        rw [List.getD_eq_getElem l 0 hi, hget]⟩)

private theorem k0FinPermOfList_apply {n : ℕ} (l : List ℕ) (hl : l.Perm (List.range n))
    (i : Fin n) : (k0FinPermOfList l hl i).val = l.getD i.val 0 := rfl

private noncomputable def k0PermOfList (T : GGKacType) (l : List ℕ)
    (hl : l.Perm (List.range (k0DiagOf T).marks.length)) :
    Equiv.Perm (Option (Fin (absTag T).rank)) :=
  (k0NodeEquiv T).symm.trans ((k0FinPermOfList l hl).trans (k0NodeEquiv T))

private theorem k0PermOfList_apply (T : GGKacType) {l : List ℕ}
    (hl : l.Perm (List.range (k0DiagOf T).marks.length))
    (i : Fin (k0DiagOf T).marks.length) :
    k0PermOfList T l hl (k0NodeEquiv T i) = k0NodeEquiv T (k0FinPermOfList l hl i) := by
  rw [k0PermOfList, Equiv.trans_apply, Equiv.trans_apply, Equiv.symm_apply_apply]

private theorem k0PermOfList_idxNode (T : GGKacType) {l : List ℕ}
    (hl : l.Perm (List.range (k0DiagOf T).marks.length))
    (i : Fin (k0DiagOf T).marks.length) :
    k0PermOfList T l hl (idxNode (r := (absTag T).rank) i.val) =
      idxNode (r := (absTag T).rank) (l.getD i.val 0) := by
  rw [← k0NodeEquiv_apply T i, k0PermOfList_apply, k0NodeEquiv_apply, k0FinPermOfList_apply]

private theorem k0PermOfList_idxNode_of_lt (T : GGKacType) {l : List ℕ}
    (hl : l.Perm (List.range (k0DiagOf T).marks.length)) {i : ℕ}
    (hi : i < (k0DiagOf T).marks.length) :
    k0PermOfList T l hl (idxNode (r := (absTag T).rank) i) =
      idxNode (r := (absTag T).rank) (l.getD i 0) := by
  have := k0PermOfList_idxNode T hl ⟨i, hi⟩
  simpa using this

private noncomputable def k0ListOfPerm (T : GGKacType)
    (σ : Equiv.Perm (Option (Fin (absTag T).rank))) : List ℕ :=
  List.ofFn fun i : Fin (k0DiagOf T).marks.length =>
    nodeIdx (r := (absTag T).rank) (σ (idxNode (r := (absTag T).rank) i.val))

private theorem k0ListOfPerm_length (T : GGKacType)
    (σ : Equiv.Perm (Option (Fin (absTag T).rank))) :
    (k0ListOfPerm T σ).length = (k0DiagOf T).marks.length := by
  rw [k0ListOfPerm, List.length_ofFn]

private theorem k0ListOfPerm_getD (T : GGKacType)
    (σ : Equiv.Perm (Option (Fin (absTag T).rank))) {i : ℕ}
    (hi : i < (k0DiagOf T).marks.length) :
    (k0ListOfPerm T σ).getD i 0 =
      nodeIdx (r := (absTag T).rank) (σ (idxNode (r := (absTag T).rank) i)) := by
  rw [k0ListOfPerm, List.getD_eq_getElem _ _ (by rw [List.length_ofFn]; exact hi),
    List.getElem_ofFn]

private theorem k0ListOfPerm_nodup (T : GGKacType)
    (σ : Equiv.Perm (Option (Fin (absTag T).rank))) :
    (k0ListOfPerm T σ).Nodup := by
  apply List.nodup_ofFn_ofInjective
  intro i j hij
  have h1 : σ (idxNode (r := (absTag T).rank) i.val) =
      σ (idxNode (r := (absTag T).rank) j.val) := nodeIdx_injective hij
  have h2 : idxNode (r := (absTag T).rank) i.val =
      idxNode (r := (absTag T).rank) j.val := σ.injective h1
  have h3 : k0NodeEquiv T i = k0NodeEquiv T j := by
    rw [k0NodeEquiv_apply, k0NodeEquiv_apply]; exact h2
  exact (k0NodeEquiv T).injective h3

private theorem k0ListOfPerm_subset (T : GGKacType)
    (σ : Equiv.Perm (Option (Fin (absTag T).rank))) :
    k0ListOfPerm T σ ⊆ List.range (k0DiagOf T).marks.length := by
  intro x hx
  rw [k0ListOfPerm, List.mem_ofFn] at hx
  obtain ⟨i, rfl⟩ := hx
  have h := nodeIdx_lt (σ (idxNode (r := (absTag T).rank) i.val))
  rw [← k0Kac_marks_length T] at h
  exact List.mem_range.mpr h

private theorem k0ListOfPerm_perm (T : GGKacType)
    (σ : Equiv.Perm (Option (Fin (absTag T).rank))) :
    (k0ListOfPerm T σ).Perm (List.range (k0DiagOf T).marks.length) := by
  have hsub := (k0ListOfPerm_nodup T σ).subperm (k0ListOfPerm_subset T σ)
  refine hsub.perm_of_length_le ?_
  rw [List.length_range, k0ListOfPerm_length]

private theorem k0ListOfPerm_permOfList (T : GGKacType) {l : List ℕ}
    (hl : l.Perm (List.range (k0DiagOf T).marks.length)) :
    k0ListOfPerm T (k0PermOfList T l hl) = l := by
  apply k0_list_ext_getD
  · rw [k0ListOfPerm_length]
    simpa using hl.length_eq.symm
  · intro i hi
    have hi' : i < (k0DiagOf T).marks.length := by
      rw [← k0ListOfPerm_length]; exact hi
    rw [k0ListOfPerm_getD T _ hi', k0PermOfList_idxNode_of_lt T hl hi']
    have hlt : l.getD i 0 < (k0DiagOf T).marks.length := k0_getD_lt_of_perm hl hi'
    rw [nodeIdx_idxNode (r := (absTag T).rank) (by
      rw [k0Kac_marks_length T] at hlt
      exact hlt)]

private theorem k0PermOfList_listOfPerm (T : GGKacType)
    (σ : Equiv.Perm (Option (Fin (absTag T).rank))) :
    k0PermOfList T (k0ListOfPerm T σ) (k0ListOfPerm_perm T σ) = σ := by
  apply Equiv.ext
  intro x
  conv_lhs => rw [← idxNode_nodeIdx (r := (absTag T).rank) x]
  have hx : nodeIdx (r := (absTag T).rank) x < (k0DiagOf T).marks.length := by
    rw [k0Kac_marks_length T]; exact nodeIdx_lt x
  rw [k0PermOfList_idxNode_of_lt T (k0ListOfPerm_perm T σ) hx]
  rw [k0ListOfPerm_getD T σ hx, idxNode_nodeIdx]
  exact congrArg σ (idxNode_nodeIdx x)

private theorem k0ListOfPerm_trans (T : GGKacType)
    (σ τ : Equiv.Perm (Option (Fin (absTag T).rank))) :
    k0ListOfPerm T (σ.trans τ) =
      k0pMul (k0ListOfPerm T τ) (k0ListOfPerm T σ) := by
  apply k0_list_ext_getD
  · simp only [k0pMul, List.length_map]; rw [k0ListOfPerm_length, k0ListOfPerm_length]
  · intro i hi
    rw [k0ListOfPerm_length] at hi
    rw [k0ListOfPerm_getD T _ hi,
      k0pMul_getD (k0ListOfPerm T τ) (k0ListOfPerm T σ)
        (by rw [k0ListOfPerm_length]; exact hi)]
    rw [k0ListOfPerm_getD T σ hi]
    rw [k0ListOfPerm_getD T τ (by
      rw [k0Kac_marks_length T]
      exact nodeIdx_lt (σ (idxNode i))), idxNode_nodeIdx]
    rfl

private theorem k0ListOfPerm_symm (T : GGKacType)
    (σ : Equiv.Perm (Option (Fin (absTag T).rank))) :
    k0ListOfPerm T σ.symm = k0pInv (k0ListOfPerm T σ) := by
  apply k0_list_ext_getD
  · rw [k0ListOfPerm_length, (k0pInv_perm (k0ListOfPerm_perm T σ)).length_eq, List.length_range]
  · intro i hi
    rw [k0ListOfPerm_length] at hi
    have ha := k0ListOfPerm_perm T σ
    have hj : nodeIdx (r := (absTag T).rank) (σ.symm (idxNode (r := (absTag T).rank) i)) <
        (k0DiagOf T).marks.length := by
      rw [k0Kac_marks_length T]
      exact nodeIdx_lt _
    have haj : (k0ListOfPerm T σ).getD
        (nodeIdx (r := (absTag T).rank) (σ.symm (idxNode (r := (absTag T).rank) i))) 0 = i := by
      rw [k0ListOfPerm_getD T σ hj, idxNode_nodeIdx, Equiv.apply_symm_apply,
        nodeIdx_idxNode (r := (absTag T).rank) (by
          rw [k0Kac_marks_length T] at hi
          exact hi)]
    have h := k0pInv_getD_of_perm (ha := ha) (hi := hj)
    rw [haj] at h
    rw [k0ListOfPerm_getD T σ.symm hi, h]

theorem k0pMul_assoc {a b c : List ℕ}
    (hc : ∀ i, i < c.length → c.getD i 0 < b.length) :
    k0pMul (k0pMul a b) c = k0pMul a (k0pMul b c) := by
  apply k0_list_ext_getD
  · simp only [k0pMul, List.length_map]
  · intro i hi
    have hi' : i < c.length := by simpa only [k0pMul, List.length_map] using hi
    have hi'' : i < (k0pMul b c).length := by simpa only [k0pMul, List.length_map] using hi'
    rw [k0pMul_getD (k0pMul a b) c hi', k0pMul_getD a b (hc i hi'),
      k0pMul_getD a (k0pMul b c) hi'', k0pMul_getD b c hi']

theorem k0pMul_id_right {n : ℕ} {a : List ℕ} (ha : a.length = n) :
    k0pMul a (k0pId n) = a := by
  apply k0_list_ext_getD
  · simp only [k0pMul, k0pId, List.length_map, List.length_range]
    exact ha.symm
  · intro i hi
    have hai : i < a.length := by
      have h := hi
      rw [k0pMul, List.length_map, k0pId, List.length_range] at h
      rwa [← ha] at h
    have hi' : i < (k0pId n).length := by
      simp only [k0pId, List.length_range]; rw [← ha]; exact hai
    rw [k0pMul_getD a (k0pId n) hi']
    have hgi : (k0pId n).getD i 0 = i := by
      rw [k0pId, List.getD_eq_getElem _ _ (by
          simp only [List.length_range]; rw [← ha]; exact hai), List.getElem_range]
    rw [hgi]

theorem k0pMul_id_left {n : ℕ} {a : List ℕ}
    (hlt : ∀ i, i < a.length → a.getD i 0 < n) :
    k0pMul (k0pId n) a = a := by
  apply k0_list_ext_getD
  · simp only [k0pMul, k0pId, List.length_map]
  · intro i hi
    have hai : i < a.length := by
      have h := hi
      rw [k0pMul, List.length_map] at h
      exact h
    rw [k0pMul_getD (k0pId n) a hai]
    have hgi : (k0pId n).getD (a.getD i 0) 0 = a.getD i 0 := by
      rw [k0pId, List.getD_eq_getElem _ _
        (by simp only [List.length_range]; exact hlt i hai), List.getElem_range]
    rw [hgi]


theorem k0pMul_assoc_perm (T : GGKacType) {a b c : List ℕ}
    (_ha : a.Perm (List.range (k0DiagOf T).marks.length))
    (hb : b.Perm (List.range (k0DiagOf T).marks.length))
    (hc : c.Perm (List.range (k0DiagOf T).marks.length)) :
    k0pMul (k0pMul a b) c = k0pMul a (k0pMul b c) := by
  apply k0pMul_assoc
  intro i hi
  have hi' : i < (k0DiagOf T).marks.length := by
    rw [hc.length_eq, List.length_range] at hi
    exact hi
  have h : c.getD i 0 < (k0DiagOf T).marks.length := k0_getD_lt_of_perm hc hi'
  rw [hb.length_eq, List.length_range]
  exact h

private theorem k0pMul_inv_right {n : ℕ} {a : List ℕ} (ha : a.Perm (List.range n)) :
    k0pMul a (k0pInv a) = k0pId n := by
  apply k0_list_ext_getD
  · rw [k0pMul, k0pId, List.length_map, (k0pInv_perm ha).length_eq, List.length_range]
  · intro i hi
    have hin : i < n := by
      rw [k0pMul, List.length_map, (k0pInv_perm ha).length_eq, List.length_range] at hi
      exact hi
    have hi' : i < (k0pInv a).length := by
      rw [(k0pInv_perm ha).length_eq, List.length_range]; exact hin
    rw [k0pMul_getD a (k0pInv a) hi']
    obtain ⟨j, hj, hja⟩ := k0_exists_getD_of_perm ha hin
    have hinv : (k0pInv a).getD i 0 = j := by
      have h := k0pInv_getD_of_perm (ha := ha) (hi := hj)
      rwa [hja] at h
    rw [hinv, hja, k0pId,
      List.getD_eq_getElem _ _ (by rw [List.length_range]; exact hin), List.getElem_range]

private theorem k0pMul_inv_left {n : ℕ} {a : List ℕ} (ha : a.Perm (List.range n)) :
    k0pMul (k0pInv a) a = k0pId n := by
  apply k0_list_ext_getD
  · rw [k0pMul, List.length_map, k0pId, List.length_range, ha.length_eq, List.length_range]
  · intro i hi
    have hin : i < n := by
      rw [k0pMul, List.length_map, ha.length_eq, List.length_range] at hi
      exact hi
    have hi' : i < a.length := by rw [ha.length_eq, List.length_range]; exact hin
    rw [k0pMul_getD (k0pInv a) a hi', k0pInv_getD_of_perm (ha := ha) (hi := hin),
      k0pId, List.getD_eq_getElem _ _ (by rw [List.length_range]; exact hin), List.getElem_range]

private theorem k0pAct_eq_self_of_getD (T : GGKacType) {a s : List ℕ}
    (ha : a.Perm (List.range (k0DiagOf T).marks.length))
    (hs : s.length = (k0DiagOf T).marks.length)
    (h : ∀ i, i < (k0DiagOf T).marks.length →
      s.getD (a.getD i 0) 0 = s.getD i 0) :
    k0pAct a s = s := by
  apply k0_list_ext_getD
  · rw [k0pAct_length, hs]
  · intro j hj
    have hjlen : j < (k0DiagOf T).marks.length := by
      rw [k0pAct_length, hs] at hj; exact hj
    obtain ⟨i, hi, hia⟩ := k0_exists_getD_of_perm ha hjlen
    have h1 : (k0pAct a s).getD j 0 = s.getD i 0 := by
      rw [← hia]
      exact k0pAct_getD_of_perm ha hs hi
    rw [h1, ← hia, h i hi]




private theorem k0_marks_zero (T : GGKacType) :
    (k0DiagOf T).marks.getD 0 0 = 1 := by
  cases T <;> decide

private theorem k0_idxNode_zero (r : ℕ) : idxNode (r := r) 0 = none := by
  simp [idxNode]

private theorem k0_idxNode_succ {r : ℕ} (j : ℕ) (hj : j < r) :
    idxNode (r := r) (j + 1) = some ⟨j, hj⟩ := by
  unfold idxNode
  rw [dite_eq_left ⟨by omega, by omega⟩]
  congr 1

private theorem k0_toNat_marks_succ
    (T : GGKacType) (j : Fin (absTag T).rank) :
    (((k0DiagOf T).marks.getD (j.val + 1) 0 : ℕ) : ℤ) = (k0Kac T).θ j := by
  rw [← k0Kac_θ T j]

private theorem k0_alcove_sum
    (T : GGKacType) (p : ℕ) {μ : Fin (absTag T).rank → ℤ}
    (hμ : (k0Kac T).IsNormal p μ) :
    (∑ i : Fin (k0DiagOf T).marks.length,
      (k0DiagOf T).marks.getD i.val 0 *
        (alcoveValue p μ ((k0Kac T).extRoot (idxNode i.val))).toNat) = p := by
  classical
  let K := k0Kac T
  let D := k0DiagOf T
  have hK : K.Facts := k0Kac_facts T
  have hlen : D.marks.length = (absTag T).rank + 1 := k0Kac_marks_length T
  let F : Fin ((absTag T).rank + 1) → ℕ := fun i =>
    D.marks.getD i.val 0 * (alcoveValue p μ (K.extRoot (idxNode i.val))).toNat
  have hsum_int : ((∑ i : Fin D.marks.length,
      D.marks.getD i.val 0 *
        (alcoveValue p μ (K.extRoot (idxNode i.val))).toNat : ℕ) : ℤ) = (p : ℤ) := by
    have hsum_eq : (∑ i : Fin D.marks.length,
        D.marks.getD i.val 0 *
          (alcoveValue p μ (K.extRoot (idxNode i.val))).toNat) = ∑ i : Fin _, F i := by
      simpa only [F, Fin.val_cast] using (Fin.sum_congr' (f := F) hlen)
    rw [hsum_eq, Nat.cast_sum, Fin.sum_univ_succ]
    have hterm : ∀ k : Fin (absTag T).rank, ((F k.succ : ℕ) : ℤ) = K.θ k * μ k := by
      intro k
      dsimp only [F, D]
      rw [Nat.cast_mul]
      simp only [Fin.val_succ]
      rw [k0_idxNode_succ k.val k.isLt]
      rw [KacData.alcoveValue_extRoot_some]
      rw [k0_toNat_marks_succ T k]
      rw [Int.toNat_of_nonneg (hμ.1 k)]
    rw [Finset.sum_congr rfl (fun k _ => hterm k)]
    have h0 : ((F 0 : ℕ) : ℤ) = (p : ℤ) - dotProduct K.θ μ := by
      dsimp only [F, D]
      rw [Nat.cast_mul]
      simp only [Fin.val_zero]
      rw [k0_marks_zero T, Nat.cast_one, one_mul, k0_idxNode_zero,
        KacData.alcoveValue_extRoot_none K hK p μ]
      have hpθ : 0 ≤ (p : ℤ) - dotProduct K.θ μ := by
        have := hμ.2
        linarith
      rw [Int.toNat_of_nonneg hpθ]
    rw [h0, add_comm]
    unfold dotProduct
    ring
  exact_mod_cast hsum_int



private theorem k0_theta_idxNode
    (T : GGKacType) {i : ℕ}
    (hi : i < (k0DiagOf T).marks.length) :
    Option.elim (idxNode (r := (absTag T).rank) i) (1 : ℤ) (k0Kac T).θ =
      ((k0DiagOf T).marks.getD i 0 : ℤ) := by
  cases i with
  | zero =>
      rw [k0_idxNode_zero]
      simp only [Option.elim_none]
      rw [k0_marks_zero T]
      norm_num
  | succ j =>
      have hj : j < (absTag T).rank := by
        rw [k0Kac_marks_length T] at hi
        omega
      rw [k0_idxNode_succ j hj]
      simp only [Option.elim_some]
      rw [k0Kac_θ T ⟨j, hj⟩]

private theorem k0_hma_omega
    (T : GGKacType) {a : List ℕ}
    (ha : a ∈ (k0DiagOf T).omega) :
    ∀ x : Option (Fin (absTag T).rank),
      Option.elim ((k0PermOfList T a (omega_perm T ha)) x) (1 : ℤ) (k0Kac T).θ =
      Option.elim x (1 : ℤ) (k0Kac T).θ := by
  intro x
  conv_lhs => rw [← idxNode_nodeIdx (r := (absTag T).rank) x]
  conv_rhs => rw [← idxNode_nodeIdx (r := (absTag T).rank) x]
  have hx : nodeIdx (r := (absTag T).rank) x < (k0DiagOf T).marks.length := by
    rw [k0Kac_marks_length T]; exact nodeIdx_lt x
  rw [k0PermOfList_idxNode_of_lt T (omega_perm T ha) hx]
  have hlt : a.getD (nodeIdx (r := (absTag T).rank) x) 0 <
      (k0DiagOf T).marks.length :=
    k0_getD_lt_of_perm (omega_perm T ha) hx
  rw [k0_theta_idxNode T hlt, k0_theta_idxNode T hx]
  rw [omega_marks T ha hx]

private theorem k0_hv_omega
    (T : GGKacType) {a : List ℕ}
    (ha : a ∈ (k0DiagOf T).omega) {v : WeylGroup (absTag T)}
    (hv : ∀ i, i < (k0DiagOf T).marks.length →
      v • (k0Kac T).extRoot (idxNode (r := (absTag T).rank) i) =
        (k0Kac T).extRoot (idxNode (r := (absTag T).rank) (a.getD i 0))) :
    ∀ x : Option (Fin (absTag T).rank),
      v • (k0Kac T).extRoot x =
        (k0Kac T).extRoot ((k0PermOfList T a (omega_perm T ha)) x) := by
  intro x
  have hx : nodeIdx (r := (absTag T).rank) x < (k0DiagOf T).marks.length := by
    rw [k0Kac_marks_length T]; exact nodeIdx_lt x
  have hperm : (k0PermOfList T a (omega_perm T ha)) x =
      idxNode (r := (absTag T).rank) (a.getD (nodeIdx (r := (absTag T).rank) x) 0) := by
    conv_lhs => rw [← idxNode_nodeIdx (r := (absTag T).rank) x]
    rw [k0PermOfList_idxNode_of_lt T (omega_perm T ha) hx]
  rw [hperm]
  conv_lhs => rw [← idxNode_nodeIdx (r := (absTag T).rank) x]
  exact hv (nodeIdx (r := (absTag T).rank) x) hx

private theorem k0_ofFn_alcove_eq_pAct
    (T : GGKacType) (p : ℕ) {μ μ' : Fin (absTag T).rank → ℤ}
    {b : List ℕ} (hb : b.Perm (List.range (k0DiagOf T).marks.length))
    (hval : ∀ x : Option (Fin (absTag T).rank),
      alcoveValue p μ' ((k0Kac T).extRoot ((k0PermOfList T b hb) x)) =
        alcoveValue p μ ((k0Kac T).extRoot x)) :
    List.ofFn (fun i : Fin (k0DiagOf T).marks.length =>
        (alcoveValue p μ' ((k0Kac T).extRoot (idxNode (r := (absTag T).rank) i.val))).toNat) =
      k0pAct b (List.ofFn (fun i : Fin (k0DiagOf T).marks.length =>
        (alcoveValue p μ ((k0Kac T).extRoot (idxNode (r := (absTag T).rank) i.val))).toNat)) := by
  let s0 : List ℕ := List.ofFn (fun i : Fin (k0DiagOf T).marks.length =>
    (alcoveValue p μ ((k0Kac T).extRoot (idxNode (r := (absTag T).rank) i.val))).toNat)
  let s1 : List ℕ := List.ofFn (fun i : Fin (k0DiagOf T).marks.length =>
    (alcoveValue p μ' ((k0Kac T).extRoot (idxNode (r := (absTag T).rank) i.val))).toNat)
  have hs0 : s0.length = (k0DiagOf T).marks.length := List.length_ofFn
  change s1 = k0pAct b s0
  apply k0_list_ext_getD
  · dsimp only [s1]
    rw [List.length_ofFn, k0pAct_length, hs0]
  · intro j hj
    have hjlen : j < (k0DiagOf T).marks.length := by
      dsimp only [s1] at hj
      rw [List.length_ofFn] at hj
      exact hj
    obtain ⟨i, hi, hib⟩ := k0_exists_getD_of_perm hb hjlen
    have hs1 : s1.getD (b.getD i 0) 0 =
        (alcoveValue p μ' ((k0Kac T).extRoot (idxNode (r := (absTag T).rank) (b.getD i 0)))).toNat := by
      dsimp only [s1]
      rw [List.getD_eq_getElem _ _
        (by rw [List.length_ofFn]; exact k0_getD_lt_of_perm hb hi), List.getElem_ofFn]
    have hs0i : s0.getD i 0 =
        (alcoveValue p μ ((k0Kac T).extRoot (idxNode (r := (absTag T).rank) i))).toNat := by
      dsimp only [s0]
      rw [List.getD_eq_getElem _ _ (by rw [List.length_ofFn]; exact hi), List.getElem_ofFn]
    have h := hval (idxNode (r := (absTag T).rank) i)
    rw [k0PermOfList_idxNode_of_lt T hb hi] at h
    have h1 : s1.getD j 0 = s0.getD i 0 := by
      rw [← hib, hs1, hs0i, h]
    have h2 : (k0pAct b s0).getD j 0 = s0.getD i 0 := by
      rw [← hib]
      exact k0pAct_getD_of_perm hb hs0 hi
    rw [h1, h2]


theorem k0_eps_dvd {lab : LargeEvenLabel} {p : ℕ} (hpair : GGKacExcPair lab p) :
    (p : ℤ) ∣ (2 : ℤ) ^ lab.n - (if p ∣ 2 ^ lab.n - 1 then (1 : ℤ) else -1) := by
  by_cases h : p ∣ 2 ^ lab.n - 1
  · rw [ite_eq_left h]
    have hz : ((2 ^ lab.n - 1 : ℕ) : ℤ) = (2 : ℤ) ^ lab.n - 1 := by
      rw [Nat.cast_sub (Nat.one_le_two_pow), Nat.cast_pow, Nat.cast_one]
      norm_num
    have hd : (p : ℤ) ∣ ((2 ^ lab.n - 1 : ℕ) : ℤ) := by exact_mod_cast h
    rwa [hz] at hd
  · rw [ite_eq_right h]
    have h' : p ∣ 2 ^ lab.n + 1 := hpair.2.2.1.resolve_left h
    have hz : ((2 ^ lab.n + 1 : ℕ) : ℤ) = (2 : ℤ) ^ lab.n + 1 := by
      rw [Nat.cast_add, Nat.cast_pow, Nat.cast_one]
      norm_num
    have hd : (p : ℤ) ∣ ((2 ^ lab.n + 1 : ℕ) : ℤ) := by exact_mod_cast h'
    rw [hz] at hd
    convert hd using 1
    ring

private theorem k0_eps_cases {lab : LargeEvenLabel} {p : ℕ} :
    (if p ∣ 2 ^ lab.n - 1 then (1 : ℤ) else -1) = 1 ∨
      (if p ∣ 2 ^ lab.n - 1 then (1 : ℤ) else -1) = -1 := by
  split_ifs <;> norm_num

private theorem k0_d_eq {lab : LargeEvenLabel} {p : ℕ} :
    (if p ∣ 2 ^ lab.n - 1 then 1 else 2) = if p ∣ 2 ^ lab.n - 1 then 1 else 2 := rfl

private theorem k0_hτ_absTag (T : GGKacType) :
    absTag T = .F4 ∨ absTag T = .E6 ∨ absTag T = .E7 ∨ absTag T = .E8 := by
  cases T <;> simp [absTag]


private theorem k0pInv_inv {n : ℕ} {a : List ℕ} (ha : a.Perm (List.range n)) :
    k0pInv (k0pInv a) = a := by
  apply k0_list_ext_getD
  · rw [(k0pInv_perm (k0pInv_perm ha)).length_eq, List.length_range]
    exact ((ha.length_eq.trans (by rw [List.length_range])).symm)
  · intro i hi
    have hin : i < n := by
      rw [(k0pInv_perm (k0pInv_perm ha)).length_eq, List.length_range] at hi
      exact hi
    have hji : a.getD i 0 < n := k0_getD_lt_of_perm ha hin
    have h1 := k0pInv_getD_of_perm (ha := k0pInv_perm ha) (hi := hji)
    have h2 := k0pInv_getD_of_perm (ha := ha) (hi := hin)
    rwa [h2] at h1

private theorem k0PermOfList_symm (T : GGKacType) {l : List ℕ}
    (hl : l.Perm (List.range (k0DiagOf T).marks.length)) :
    (k0PermOfList T l hl)⁻¹ =
      k0PermOfList T (k0pInv l) (k0pInv_perm hl) := by
  apply Equiv.ext
  intro x
  conv_lhs => rw [← idxNode_nodeIdx (r := (absTag T).rank) x]
  conv_rhs => rw [← idxNode_nodeIdx (r := (absTag T).rank) x]
  have hx : nodeIdx (r := (absTag T).rank) x < (k0DiagOf T).marks.length := by
    rw [k0Kac_marks_length T]; exact nodeIdx_lt x
  rw [k0PermOfList_idxNode_of_lt T (k0pInv_perm hl) hx]
  obtain ⟨t, ht, hlt⟩ := k0_exists_getD_of_perm hl hx
  have hinv : (k0pInv l).getD (nodeIdx (r := (absTag T).rank) x) 0 = t := by
    rw [← hlt]
    exact k0pInv_getD_of_perm (ha := hl) (hi := ht)
  rw [hinv, ← hlt, ← k0PermOfList_idxNode_of_lt T hl ht]
  exact Equiv.symm_apply_apply (k0PermOfList T l hl) (idxNode (r := (absTag T).rank) t)

private theorem k0RepsAux_mem (stab : List (List ℕ)) (base : List ℕ) :
    ∀ (fuel : ℕ) (as seenF acc : List (List ℕ)), (∀ a ∈ as, a ∈ stab) →
      ∀ rho ∈ k0RepsAux stab base fuel as seenF acc,
        (∃ a ∈ stab, rho = k0pMul a base) ∨ rho ∈ acc := by
  intro fuel
  induction fuel with
  | zero =>
      intro as seenF acc _ rho hrho
      exact Or.inr hrho
  | succ fuel ih =>
      intro as seenF acc hsub rho hrho
      cases as with
      | nil => exact Or.inr hrho
      | cons a rest =>
          simp only [k0RepsAux] at hrho
          split at hrho
          · exact ih rest seenF acc (fun x hx => hsub x (by simp [hx])) rho hrho
          · rcases ih rest _ (acc ++ [k0pMul a base]) (fun x hx => hsub x (by simp [hx]))
              rho hrho with h | h
            · exact Or.inl h
            · rcases List.mem_append.mp h with h' | h'
              · exact Or.inr h'
              · refine Or.inl ⟨a, hsub a (by simp), ?_⟩
                simp only [List.mem_singleton] at h'
                exact h'

private theorem k0Reps_mem {stab : List (List ℕ)} {base rho : List ℕ}
    (h : rho ∈ k0Reps stab base) : ∃ a ∈ stab, rho = k0pMul a base := by
  rcases k0RepsAux_mem stab base (stab.length + 1) stab [] [] (fun x hx => hx) rho h with
    h' | h'
  · exact h'
  · simp at h'

private theorem k0Reps_perm (T : GGKacType) {stab : List (List ℕ)} {base r : List ℕ}
    (hstab : ∀ b ∈ stab, b ∈ (k0DiagOf T).omega)
    (hbase : base.Perm (List.range (k0DiagOf T).marks.length))
    (hr : r ∈ k0Reps stab base) :
    r.Perm (List.range (k0DiagOf T).marks.length) := by
  obtain ⟨a, ha, rfl⟩ := k0Reps_mem hr
  exact k0pMul_perm (omega_perm T (hstab a ha)) hbase

private theorem k0pAct_id (T : GGKacType) {s : List ℕ}
    (hs : s.length = (k0DiagOf T).marks.length) :
    k0pAct (k0pId (k0DiagOf T).marks.length) s = s := by
  apply k0pAct_eq_self_of_getD T (a := k0pId (k0DiagOf T).marks.length)
  · exact List.perm_rfl
  · exact hs
  · intro i hi
    rw [k0pId]
    have h : (List.range (k0DiagOf T).marks.length).getD i 0 = i := by
      rw [List.getD_eq_getElem _ _ (by rw [List.length_range]; exact hi), List.getElem_range]
    rw [h]

private theorem k0pAct_mul (T : GGKacType) {a b s : List ℕ}
    (ha : a.Perm (List.range (k0DiagOf T).marks.length))
    (hb : b.Perm (List.range (k0DiagOf T).marks.length))
    (hs : s.length = (k0DiagOf T).marks.length) :
    k0pAct (k0pMul a b) s = k0pAct a (k0pAct b s) := by
  have hab := k0pMul_perm ha hb
  have hbs : (k0pAct b s).length = (k0DiagOf T).marks.length := by
    rw [k0pAct_length, hs]
  apply k0_list_ext_getD
  · rw [k0pAct_length, k0pAct_length, k0pAct_length]
  · intro i hi
    have hi' : i < (k0DiagOf T).marks.length := by
      rw [k0pAct_length] at hi
      rw [hs] at hi
      exact hi
    obtain ⟨j, hj, hja⟩ := k0_exists_getD_of_perm hab hi'
    have hbj : b.getD j 0 < (k0DiagOf T).marks.length := k0_getD_lt_of_perm hb hj
    rw [← hja]
    rw [k0pAct_getD_of_perm hab hs hj]
    rw [k0pMul_getD a b (by rw [hb.length_eq, List.length_range]; exact hj)]
    rw [k0pAct_getD_of_perm ha hbs hbj]
    rw [k0pAct_getD_of_perm hb hs hj]

private theorem k0ListOfPerm_conj (T : GGKacType) {b rho r : List ℕ}
    (hb : b.Perm (List.range (k0DiagOf T).marks.length))
    (hρ : rho.Perm (List.range (k0DiagOf T).marks.length))
    (hr : r.Perm (List.range (k0DiagOf T).marks.length))
    (hconj : rho = k0pMul b (k0pMul r (k0pInv b))) :
    k0ListOfPerm T ((k0PermOfList T (k0pInv b) (k0pInv_perm hb)) *
        (k0PermOfList T rho hρ) *
        (k0PermOfList T (k0pInv b) (k0pInv_perm hb))⁻¹) = r := by
  let a := k0PermOfList T (k0pInv b) (k0pInv_perm hb)
  let σ := k0PermOfList T rho hρ
  have haL : k0ListOfPerm T a = k0pInv b := k0ListOfPerm_permOfList T (k0pInv_perm hb)
  have haLinv : k0ListOfPerm T a⁻¹ = b := by
    change k0ListOfPerm T a.symm = b
    rw [k0ListOfPerm_symm T a, haL, k0pInv_inv hb]
  have hσL : k0ListOfPerm T σ = rho := k0ListOfPerm_permOfList T hρ
  apply k0_list_ext_getD
  · rw [k0ListOfPerm_length]
    exact ((hr.length_eq.trans (by rw [List.length_range])).symm)
  · intro i hi
    have hi' : i < (k0DiagOf T).marks.length := by
      rw [k0ListOfPerm_length] at hi
      exact hi
    rw [k0ListOfPerm_getD T _ hi']
    show nodeIdx (r := (absTag T).rank) ((a * σ * a⁻¹) (idxNode (r := (absTag T).rank) i)) =
      r.getD i 0
    rw [Equiv.Perm.mul_apply, Equiv.Perm.mul_apply]
    have hbi : b.getD i 0 < (k0DiagOf T).marks.length := k0_getD_lt_of_perm hb hi'
    have h1 : a⁻¹ (idxNode (r := (absTag T).rank) i) =
        idxNode (r := (absTag T).rank) (b.getD i 0) := by
      dsimp only [a]
      rw [k0PermOfList_symm T (k0pInv_perm hb),
        k0PermOfList_idxNode_of_lt T (k0pInv_perm (k0pInv_perm hb)) hi', k0pInv_inv hb]
    have h2 : σ (idxNode (r := (absTag T).rank) (b.getD i 0)) =
        idxNode (r := (absTag T).rank) (rho.getD (b.getD i 0) 0) := by
      dsimp only [σ]
      rw [k0PermOfList_idxNode_of_lt T hρ hbi]
    have hρi : rho.getD (b.getD i 0) 0 < (k0DiagOf T).marks.length :=
      k0_getD_lt_of_perm hρ hbi
    have h3 : a (idxNode (r := (absTag T).rank) (rho.getD (b.getD i 0) 0)) =
        idxNode (r := (absTag T).rank) ((k0pInv b).getD (rho.getD (b.getD i 0) 0) 0) := by
      dsimp only [a]
      rw [k0PermOfList_idxNode_of_lt T (k0pInv_perm hb) hρi]
    have h4 : rho.getD (b.getD i 0) 0 = b.getD (r.getD i 0) 0 := by
      rw [hconj]
      have hlen : b.getD i 0 < (k0pMul r (k0pInv b)).length := by
        rw [k0pMul, List.length_map, (k0pInv_perm hb).length_eq, List.length_range]
        exact hbi
      rw [k0pMul_getD b (k0pMul r (k0pInv b)) hlen]
      have hlen2 : b.getD i 0 < (k0pInv b).length := by
        rw [(k0pInv_perm hb).length_eq, List.length_range]; exact hbi
      rw [k0pMul_getD r (k0pInv b) hlen2, k0pInv_getD_of_perm (ha := hb) (hi := hi')]
    have hri : r.getD i 0 < (k0DiagOf T).marks.length := k0_getD_lt_of_perm hr hi'
    have h5 : (k0pInv b).getD (rho.getD (b.getD i 0) 0) 0 = r.getD i 0 := by
      rw [h4]
      exact k0pInv_getD_of_perm (ha := hb) (hi := hri)
    rw [h1, h2, h3, h5]
    rw [nodeIdx_idxNode (r := (absTag T).rank) (by simpa [k0Kac_marks_length T] using hri)]

private theorem k0_inv_smul_tau0
    (T : GGKacType) {v : WeylGroup (absTag T)}
    (hv : ∀ i, i < (k0DiagOf T).marks.length →
      v • (k0Kac T).extRoot (idxNode (r := (absTag T).rank) i) =
        - (k0Kac T).extRoot (idxNode (r := (absTag T).rank)
          ((k0DiagOf T).tau0.getD i 0))) :
    ∀ j, j < (k0DiagOf T).marks.length →
      v⁻¹ • (k0Kac T).extRoot (idxNode (r := (absTag T).rank) j) =
        - (k0Kac T).extRoot (idxNode (r := (absTag T).rank)
          ((k0DiagOf T).tau0.getD j 0)) := by
  intro j hj
  let D := k0DiagOf T
  have ht : D.tau0.getD j 0 < D.marks.length :=
    k0_getD_lt_of_perm (tau0_perm T) hj
  have htt : D.tau0.getD (D.tau0.getD j 0) 0 = j := by
    have h := k0pMul_getD D.tau0 D.tau0 (i := j)
      (by rw [(tau0_perm T).length_eq, List.length_range]; exact hj)
    rw [tau0_mul_tau0 T] at h
    rw [k0pId, List.getD_eq_getElem _ _ (by rw [List.length_range]; exact hj),
      List.getElem_range] at h
    exact h.symm
  have h := hv (D.tau0.getD j 0) ht
  rw [htt] at h
  calc v⁻¹ • (k0Kac T).extRoot (idxNode (r := (absTag T).rank) j)
      = v⁻¹ • (-(v • (k0Kac T).extRoot (idxNode (r := (absTag T).rank)
          (D.tau0.getD j 0)))) := by rw [h, neg_neg]
    _ = -(v⁻¹ • v • (k0Kac T).extRoot (idxNode (r := (absTag T).rank)
          (D.tau0.getD j 0))) := by rw [smul_neg]
    _ = - (k0Kac T).extRoot (idxNode (r := (absTag T).rank)
          (D.tau0.getD j 0)) := by rw [inv_smul_smul]

theorem k0pMul_id_left_perm (T : GGKacType) {a : List ℕ}
    (ha : a.Perm (List.range (k0DiagOf T).marks.length)) :
    k0pMul (k0pId (k0DiagOf T).marks.length) a = a := by
  apply k0pMul_id_left
  intro i hi
  exact k0_getD_lt_of_perm ha (by rw [ha.length_eq, List.length_range] at hi; exact hi)

theorem k0pMul_id_right_perm (T : GGKacType) {a : List ℕ}
    (ha : a.Perm (List.range (k0DiagOf T).marks.length)) :
    k0pMul a (k0pId (k0DiagOf T).marks.length) = a :=
  k0pMul_id_right (by rw [ha.length_eq, List.length_range])

theorem k0Rho0_one (T : GGKacType) :
    k0Rho0 (k0DiagOf T) false 1 = k0pId (k0DiagOf T).marks.length := by
  simp [k0Rho0]

theorem k0Rho0_two (T : GGKacType) :
    k0Rho0 (k0DiagOf T) false 2 = (k0DiagOf T).tau0 := by
  rw [k0Rho0]
  simp only [ite_eq_right (by norm_num : (2 : ℕ) ≠ 1), Bool.false_eq_true, ↓reduceIte]
  rw [k0pMul_id_right_perm T (tau0_perm T)]

theorem k0Rho0_perm (T : GGKacType) (d : ℕ) (hd : d = 1 ∨ d = 2) :
    (k0Rho0 (k0DiagOf T) false d).Perm (List.range (k0DiagOf T).marks.length) := by
  rcases hd with rfl | rfl
  · rw [k0Rho0_one T]; exact List.perm_rfl
  · rw [k0Rho0_two T]; exact tau0_perm T

private theorem k0Rho0_perm_tw (T : GGKacType) (tw : Bool) (d : ℕ) (hd : d = 1 ∨ d = 2) :
    (k0Rho0 (k0DiagOf T) tw d).Perm (List.range (k0DiagOf T).marks.length) := by
  rcases hd with rfl | rfl <;> cases T <;> cases tw <;> decide

private theorem k0_marks_pos (T : GGKacType) :
    ∀ m ∈ (k0DiagOf T).marks, 0 < m := by
  cases T <;> decide

private theorem k0_stepA_of
    (T : GGKacType) {lab : LargeEvenLabel} {p : ℕ} (hpair : GGKacExcPair lab p)
    (F : ModGL (absTag T) GGL →* ModGL (absTag T) GGL)
    (θ : WeylGroup (absTag T) ≃* WeylGroup (absTag T))
    (π₀ : (Fin (absTag T).rank → ℤ) ≃ₗ[ℤ] (Fin (absTag T).rank → ℤ))
    (hF : ∀ v, F (canonicalRep (coxeterSystem (absTag T)) GGL v) =
      canonicalRep (coxeterSystem (absTag T)) GGL (θ v))
    (hθ : ∀ v γ, θ v • π₀ γ = π₀ (v • γ))
    {u : ModGL (absTag T) GGL} {ζ : GGLˣ} (hζ : orderOf ζ = p)
    (h0 : ∃ g ∈ adjointGroup (absTag T) GGL, ∃ (μ : Fin (absTag T).rank → ℤ)
      (w : WeylGroup (absTag T)) (σ : Equiv.Perm (Option (Fin (absTag T).rank))),
      (k0Kac T).IsNormal p μ ∧ g⁻¹ * u * g = rootDiagUnit (absTag T) (fun i => ζ ^ μ i) ∧
      g⁻¹ * F g = canonicalRep (coxeterSystem (absTag T)) GGL w ∧
      (∀ x, (if p ∣ 2 ^ lab.n - 1 then (1 : ℤ) else -1) •
        (w • π₀ ((k0Kac T).extRoot x)) = (k0Kac T).extRoot (σ x)) ∧
      ∀ x, alcoveValue p μ ((k0Kac T).extRoot (σ x)) = alcoveValue p μ ((k0Kac T).extRoot x))
    {tw : Bool}
    (hrat : ∀ (w₁ : WeylGroup (absTag T)) (rho : List ℕ),
      rho.Perm (List.range (k0DiagOf T).marks.length) →
      (∀ i, i < (k0DiagOf T).marks.length →
        (if p ∣ 2 ^ lab.n - 1 then (1 : ℤ) else -1) •
          (w₁ • π₀ ((k0Kac T).extRoot (idxNode (r := (absTag T).rank) i))) =
          (k0Kac T).extRoot (idxNode (r := (absTag T).rank) (rho.getD i 0))) →
      ∃ a ∈ (k0DiagOf T).omega,
        rho = k0pMul a (k0Rho0 (k0DiagOf T) tw (if p ∣ 2 ^ lab.n - 1 then 1 else 2))) :
    ∃ (g : ModGL (absTag T) GGL) (μ : Fin (absTag T).rank → ℤ) (w : WeylGroup (absTag T))
      (s rho : List ℕ),
      g ∈ adjointGroup (absTag T) GGL ∧
      g⁻¹ * u * g = rootDiagUnit (absTag T) (fun i => ζ ^ μ i) ∧
      g⁻¹ * F g = canonicalRep (coxeterSystem (absTag T)) GGL w ∧
      (k0Kac T).IsNormal p μ ∧
      s.length = (k0DiagOf T).marks.length ∧
      s ∈ k0VecsAux (k0DiagOf T).marks p ∧
      k0OrbMin (k0DiagOf T) s = s ∧
      (∀ i : Fin (k0DiagOf T).marks.length,
        alcoveValue p μ ((k0Kac T).extRoot (idxNode i.val)) = (s.getD i.val 0 : ℤ)) ∧
      rho.Perm (List.range (k0DiagOf T).marks.length) ∧
      k0pAct rho s = s ∧
      (∀ i, i < (k0DiagOf T).marks.length →
        (if p ∣ 2 ^ lab.n - 1 then (1 : ℤ) else -1) •
          (w • π₀ ((k0Kac T).extRoot (idxNode (r := (absTag T).rank) i))) =
          (k0Kac T).extRoot (idxNode (r := (absTag T).rank) (rho.getD i 0))) ∧
      (∃ a ∈ (k0DiagOf T).omega,
        rho = k0pMul a (k0Rho0 (k0DiagOf T) tw (if p ∣ 2 ^ lab.n - 1 then 1 else 2))) := by
  classical
  have hp : p.Prime := hpair.1
  let K := k0Kac T
  let D := k0DiagOf T
  let ε : ℤ := if p ∣ 2 ^ lab.n - 1 then 1 else -1
  have hε : ε = 1 ∨ ε = -1 := by dsimp only [ε]; split_ifs <;> norm_num
  obtain ⟨g0, hg0, μ0, w0, σ0, hμ0, hgu0, hgw0, hσ0, hσv0⟩ := h0
  let s0 : List ℕ := List.ofFn fun i : Fin D.marks.length =>
    (alcoveValue p μ0 (K.extRoot (idxNode (r := (absTag T).rank) i.val))).toNat
  have hs0len : s0.length = D.marks.length := List.length_ofFn
  obtain ⟨b, hb_mem, hb_min, hb_min2⟩ := exists_omega_k0OrbMin T hs0len
  have hb_perm : b.Perm (List.range D.marks.length) := omega_perm T hb_mem
  obtain ⟨v_b, hv_b⟩ := exists_weyl_omega T hb_mem
  have hma_b : ∀ x : Option (Fin (absTag T).rank),
      Option.elim ((k0PermOfList T b hb_perm) x) (1 : ℤ) K.θ = Option.elim x (1 : ℤ) K.θ :=
    k0_hma_omega T hb_mem
  have hv_b' : ∀ x : Option (Fin (absTag T).rank),
      v_b • K.extRoot x = K.extRoot ((k0PermOfList T b hb_perm) x) :=
    k0_hv_omega T hb_mem hv_b
  obtain ⟨g1, hg1, μ1, hμ1, hval1, hgu1, hgw1, hσ1, hσv1⟩ :=
    k0_lang_normal_transport_of (K := K) (k0Kac_facts T) (L := GGL) hp hε hζ
      F θ π₀ hF hθ hg0 hμ0 hgu0 hgw0 (by simpa only [ε] using hσ0) hσv0 hv_b' hma_b
  let w1 : WeylGroup (absTag T) := v_b * w0 * (θ v_b)⁻¹
  let σ1 : Equiv.Perm (Option (Fin (absTag T).rank)) :=
    (k0PermOfList T b hb_perm) * σ0 * (k0PermOfList T b hb_perm)⁻¹
  have hσ1' : ∀ x : Option (Fin (absTag T).rank),
      ε • (w1 • π₀ (K.extRoot x)) = K.extRoot (σ1 x) := hσ1
  have hσv1' : ∀ x : Option (Fin (absTag T).rank),
      alcoveValue p μ1 (K.extRoot (σ1 x)) = alcoveValue p μ1 (K.extRoot x) := hσv1
  let s : List ℕ := k0OrbMin D s0
  have hs_eq : s = k0pAct b s0 := hb_min
  have hs_min : k0OrbMin D s = s := hb_min2
  have hs_val : s = List.ofFn (fun i : Fin D.marks.length =>
      (alcoveValue p μ1 (K.extRoot (idxNode (r := (absTag T).rank) i.val))).toNat) := by
    rw [hs_eq]
    exact (k0_ofFn_alcove_eq_pAct T p hb_perm hval1).symm
  have hs_len : s.length = D.marks.length := by
    rw [hs_val, List.length_ofFn]
  have hs_mem : s ∈ k0VecsAux D.marks p := by
    apply mem_k0VecsAux_of_sum (p := p) (marks := D.marks) (s := s)
    · exact k0_marks_pos T
    · exact hs_len
    · rw [hs_val]
      have hget : ∀ i : Fin D.marks.length,
          (List.ofFn (fun i : Fin D.marks.length =>
            (alcoveValue p μ1 (K.extRoot (idxNode (r := (absTag T).rank) i.val))).toNat)).getD
              i.val 0 =
            (alcoveValue p μ1 (K.extRoot (idxNode (r := (absTag T).rank) i.val))).toNat := by
        intro i
        rw [List.getD_eq_getElem _ _ (by rw [List.length_ofFn]; exact i.isLt), List.getElem_ofFn]
      simp only [hget]
      exact k0_alcove_sum T p hμ1
  have hσl_perm : (k0ListOfPerm T σ1).Perm (List.range D.marks.length) :=
    k0ListOfPerm_perm T σ1
  have hfix_vals : ∀ i, i < D.marks.length →
      s.getD ((k0ListOfPerm T σ1).getD i 0) 0 = s.getD i 0 := by
    intro i hi
    rw [hs_val]
    let L : List ℕ := List.ofFn (fun j : Fin D.marks.length =>
      (alcoveValue p μ1 (K.extRoot (idxNode (r := (absTag T).rank) j.val))).toNat)
    have h1 : L.getD (nodeIdx (r := (absTag T).rank)
        (σ1 (idxNode (r := (absTag T).rank) i))) 0 =
        (alcoveValue p μ1 (K.extRoot (σ1 (idxNode (r := (absTag T).rank) i)))).toNat := by
      dsimp only [L]
      rw [List.getD_eq_getElem _ _ (by
        rw [List.length_ofFn]
        rw [k0Kac_marks_length T]
        exact nodeIdx_lt (σ1 (idxNode (r := (absTag T).rank) i))), List.getElem_ofFn,
        idxNode_nodeIdx]
    have h2 : L.getD i 0 =
        (alcoveValue p μ1 (K.extRoot (idxNode (r := (absTag T).rank) i))).toNat := by
      dsimp only [L]
      rw [List.getD_eq_getElem _ _ (by rw [List.length_ofFn]; exact hi), List.getElem_ofFn]
    have h3 := hσv1' (idxNode (r := (absTag T).rank) i)
    have h4 : alcoveValue p μ1 (K.extRoot (idxNode (r := (absTag T).rank)
        (nodeIdx (r := (absTag T).rank) (σ1 (idxNode (r := (absTag T).rank) i))))) =
        alcoveValue p μ1 (K.extRoot (σ1 (idxNode (r := (absTag T).rank) i))) := by
      rw [idxNode_nodeIdx]
    change L.getD ((k0ListOfPerm T σ1).getD i 0) 0 = L.getD i 0
    rw [k0ListOfPerm_getD T σ1 hi, h1, h2, h3]
  have hσl_fix : k0pAct (k0ListOfPerm T σ1) s = s :=
    k0pAct_eq_self_of_getD T hσl_perm hs_len hfix_vals
  have hσl_action : ∀ i, i < D.marks.length →
      ε • (w1 • π₀ (K.extRoot (idxNode (r := (absTag T).rank) i))) =
        K.extRoot (idxNode (r := (absTag T).rank) ((k0ListOfPerm T σ1).getD i 0)) := by
    intro i hi
    have h := hσ1' (idxNode (r := (absTag T).rank) i)
    rw [k0ListOfPerm_getD T σ1 hi, idxNode_nodeIdx]
    exact h
  have hval_s : ∀ i : Fin D.marks.length,
      alcoveValue p μ1 (K.extRoot (idxNode (r := (absTag T).rank) i.val)) =
        (s.getD i.val 0 : ℤ) := by
    intro i
    rw [hs_val]
    rw [List.getD_eq_getElem _ _ (by rw [List.length_ofFn]; exact i.isLt), List.getElem_ofFn,
      Int.toNat_of_nonneg (KacData.alcoveValue_nonneg K (k0Kac_facts T) hμ1 (K.isRoot_extRoot _))]
  let rho : List ℕ := k0ListOfPerm T σ1
  have hmem_a : ∃ a ∈ D.omega,
      rho = k0pMul a (k0Rho0 D tw (if p ∣ 2 ^ lab.n - 1 then 1 else 2)) :=
    hrat w1 rho hσl_perm hσl_action
  exact ⟨g1, μ1, w1, s, rho, hg1, hgu1, hgw1, hμ1, hs_len, hs_mem, hs_min, hval_s,
    hσl_perm, hσl_fix, hσl_action, hmem_a⟩


private theorem k0_ofFn_alcove_eq_self
    (T : GGKacType) (p : ℕ)
    {μ : Fin (absTag T).rank → ℤ} {s : List ℕ}
    (hs : s.length = (k0DiagOf T).marks.length)
    (hval : ∀ i : Fin (k0DiagOf T).marks.length,
      alcoveValue p μ ((k0Kac T).extRoot (idxNode (r := (absTag T).rank) i.val)) =
        (s.getD i.val 0 : ℤ)) :
    List.ofFn (fun i : Fin (k0DiagOf T).marks.length =>
      (alcoveValue p μ ((k0Kac T).extRoot (idxNode (r := (absTag T).rank) i.val))).toNat) = s := by
  apply k0_list_ext_getD
  · rw [List.length_ofFn, hs]
  · intro i hi
    have hi' : i < (k0DiagOf T).marks.length := by
      rw [List.length_ofFn] at hi
      exact hi
    rw [List.getD_eq_getElem _ _ (by rw [List.length_ofFn]; exact hi'), List.getElem_ofFn,
      hval ⟨i, hi'⟩, Int.toNat_natCast]

private theorem k0BaseAux_mem {rho0 s : List ℕ} :
    ∀ {l : List (List ℕ)} {r : List ℕ}, k0BaseAux rho0 s l = some r →
      (∃ a0 ∈ l, r = k0pMul a0 rho0) ∧ k0pAct r s = s := by
  intro l
  induction l with
  | nil => intro r h; simp [k0BaseAux] at h
  | cons a0 rest ih =>
      intro r h
      simp only [k0BaseAux] at h
      split at h
      · rename_i hact
        simp only [Option.some.injEq] at h
        exact ⟨⟨a0, by simp, h.symm⟩, h ▸ hact⟩
      · obtain ⟨⟨a0', ha0', heq⟩, hact⟩ := ih h
        exact ⟨⟨a0', by simp [ha0'], heq⟩, hact⟩

private theorem k0_zpow_dot_eq_zpow_alcove
    (T : GGKacType) {p : ℕ}
    {μ : Fin (absTag T).rank → ℤ} {ζ : GGLˣ} (hζ : orderOf ζ = p)
    (hμ : (k0Kac T).IsNormal p μ) {γ : Fin (absTag T).rank → ℤ}
    (hγ : IsRoot (absTag T) γ) :
    ζ ^ (dotProduct γ μ) = ζ ^ ((alcoveValue p μ γ).toNat : ℤ) := by
  have hζp : ζ ^ (p : ℤ) = 1 := by
    rw [zpow_natCast, ← hζ]
    exact pow_orderOf_eq_one ζ
  have hnn := KacData.alcoveValue_nonneg (k0Kac T) (k0Kac_facts T) hμ hγ
  rw [Int.toNat_of_nonneg hnn]
  unfold alcoveValue
  by_cases hpos : ∀ j, 0 ≤ γ j
  · rw [ite_eq_left hpos, add_zero]
  · rw [ite_eq_right hpos, zpow_add, hζp, mul_one]

private theorem k0_finalData_of
    (T : GGKacType) {lab : LargeEvenLabel} {p : ℕ} (hpair : GGKacExcPair lab p)
    (F : ModGL (absTag T) GGL →* ModGL (absTag T) GGL)
    (θ : WeylGroup (absTag T) ≃* WeylGroup (absTag T))
    (π₀ : (Fin (absTag T).rank → ℤ) ≃ₗ[ℤ] (Fin (absTag T).rank → ℤ))
    (hF : ∀ v, F (canonicalRep (coxeterSystem (absTag T)) GGL v) =
      canonicalRep (coxeterSystem (absTag T)) GGL (θ v))
    (hθ : ∀ v γ, θ v • π₀ γ = π₀ (v • γ))
    {u : ModGL (absTag T) GGL} {ζ : GGLˣ} (hζ : orderOf ζ = p)
    (h0 : ∃ g ∈ adjointGroup (absTag T) GGL, ∃ (μ : Fin (absTag T).rank → ℤ)
      (w : WeylGroup (absTag T)) (σ : Equiv.Perm (Option (Fin (absTag T).rank))),
      (k0Kac T).IsNormal p μ ∧ g⁻¹ * u * g = rootDiagUnit (absTag T) (fun i => ζ ^ μ i) ∧
      g⁻¹ * F g = canonicalRep (coxeterSystem (absTag T)) GGL w ∧
      (∀ x, (if p ∣ 2 ^ lab.n - 1 then (1 : ℤ) else -1) •
        (w • π₀ ((k0Kac T).extRoot x)) = (k0Kac T).extRoot (σ x)) ∧
      ∀ x, alcoveValue p μ ((k0Kac T).extRoot (σ x)) = alcoveValue p μ ((k0Kac T).extRoot x))
    {tw : Bool}
    (hrat : ∀ (w₁ : WeylGroup (absTag T)) (rho : List ℕ),
      rho.Perm (List.range (k0DiagOf T).marks.length) →
      (∀ i, i < (k0DiagOf T).marks.length →
        (if p ∣ 2 ^ lab.n - 1 then (1 : ℤ) else -1) •
          (w₁ • π₀ ((k0Kac T).extRoot (idxNode (r := (absTag T).rank) i))) =
          (k0Kac T).extRoot (idxNode (r := (absTag T).rank) (rho.getD i 0))) →
      ∃ a ∈ (k0DiagOf T).omega,
        rho = k0pMul a (k0Rho0 (k0DiagOf T) tw (if p ∣ 2 ^ lab.n - 1 then 1 else 2))) :
    ∃ (g : ModGL (absTag T) GGL) (μ : Fin (absTag T).rank → ℤ) (w : WeylGroup (absTag T))
      (s base rho : List ℕ),
      g ∈ adjointGroup (absTag T) GGL ∧
      g⁻¹ * u * g = rootDiagUnit (absTag T) (fun i => ζ ^ μ i) ∧
      g⁻¹ * F g = canonicalRep (coxeterSystem (absTag T)) GGL w ∧
      (k0Kac T).IsNormal p μ ∧
      s.length = (k0DiagOf T).marks.length ∧
      s ∈ k0VecsAux (k0DiagOf T).marks p ∧
      k0OrbMin (k0DiagOf T) s = s ∧
      k0KacBase (k0DiagOf T)
        (k0Rho0 (k0DiagOf T) tw (if p ∣ 2 ^ lab.n - 1 then 1 else 2)) s = some base ∧
      rho ∈ k0Reps (((k0DiagOf T).omega).filter (fun a => decide (k0pAct a s = s))) base ∧
      rho.length = (k0DiagOf T).marks.length ∧
      (∀ i : Fin (k0DiagOf T).marks.length,
        alcoveValue p μ ((k0Kac T).extRoot (idxNode i.val)) = (s.getD i.val 0 : ℤ)) ∧
      (∀ i, i < (k0DiagOf T).marks.length →
        (if p ∣ 2 ^ lab.n - 1 then (1 : ℤ) else -1) •
          (w • π₀ ((k0Kac T).extRoot (idxNode (r := (absTag T).rank) i))) =
          (k0Kac T).extRoot (idxNode (r := (absTag T).rank) (rho.getD i 0))) := by
  classical
  let D := k0DiagOf T
  let ε : ℤ := if p ∣ 2 ^ lab.n - 1 then 1 else -1
  obtain ⟨g1, μ1, w1, s, rho, hg1, hgu1, hgw1, hμ1, hs_len, hs_mem, hs_min, hval1,
    hρperm, hfix, hσact, hmem_a⟩ :=
    k0_stepA_of (tw := tw) T hpair F θ π₀ hF hθ hζ h0 hrat
  have hs_val : s = List.ofFn (fun i : Fin D.marks.length =>
      (alcoveValue p μ1 ((k0Kac T).extRoot (idxNode (r := (absTag T).rank) i.val))).toNat) :=
    (k0_ofFn_alcove_eq_self T p hs_len hval1).symm
  obtain ⟨a, ha, hrho_eq⟩ := hmem_a
  let rho0 : List ℕ := k0Rho0 D tw (if p ∣ 2 ^ lab.n - 1 then 1 else 2)
  have has : k0pAct (k0pMul a rho0) s = s := by rw [← hrho_eq]; exact hfix
  obtain ⟨base, hbase_eq, ⟨a0, ha0, hbase_eq'⟩, hbase_fix⟩ := exists_k0KacBase ha has
  have hrho0_perm : rho0.Perm (List.range D.marks.length) := by
    dsimp only [rho0, D]
    exact k0Rho0_perm_tw T tw _ (by split_ifs <;> simp)
  have hbase_perm : base.Perm (List.range D.marks.length) := by
    rw [hbase_eq']
    exact k0pMul_perm (omega_perm T ha0) hrho0_perm
  let x : List ℕ := k0pMul a (k0pInv a0)
  have hx_omega : x ∈ D.omega := mul_mem_omega T ha (inv_mem_omega T ha0)
  have hx_perm : x.Perm (List.range D.marks.length) := omega_perm T hx_omega
  have hxbase : k0pMul x base = rho := by
    dsimp only [x]
    rw [hbase_eq', hrho_eq]
    rw [k0pMul_assoc_perm T (omega_perm T ha) (omega_perm T (inv_mem_omega T ha0))
      (k0pMul_perm (omega_perm T ha0) hrho0_perm)]
    rw [← k0pMul_assoc_perm T (omega_perm T (inv_mem_omega T ha0)) (omega_perm T ha0)
        hrho0_perm,
      k0pMul_inv_left (omega_perm T ha0), k0pMul_id_left_perm T hrho0_perm]
  have hx_fix : k0pAct x s = s := by
    conv_lhs => rw [← hbase_fix]
    rw [← k0pAct_mul T hx_perm hbase_perm hs_len, hxbase, hfix]
  have hx_stab : x ∈ D.omega.filter (fun b => decide (k0pAct b s = s)) := by
    rw [List.mem_filter]
    exact ⟨hx_omega, by simpa using hx_fix⟩
  rcases mem_or_conj_k0Reps hx_stab with hcase1 | hcase2
  · refine ⟨g1, μ1, w1, s, base, rho, hg1, hgu1, hgw1, hμ1, hs_len, hs_mem, hs_min,
      hbase_eq, ?_, hρperm.length_eq.trans (by rw [List.length_range]), hval1, hσact⟩
    rwa [hxbase] at hcase1
  · obtain ⟨r, hr_mem, b, hb_stab, hconj⟩ := hcase2
    have hb_omega : b ∈ D.omega := (List.mem_filter.mp hb_stab).1
    have hb_fix : k0pAct b s = s := by
      have h := (List.mem_filter.mp hb_stab).2
      simpa using h
    have hb_perm : b.Perm (List.range D.marks.length) := omega_perm T hb_omega
    have hr_perm : r.Perm (List.range D.marks.length) :=
      k0Reps_perm T (fun b hb => (List.mem_filter.mp hb).1) hbase_perm hr_mem
    have hrho_conj : rho = k0pMul b (k0pMul r (k0pInv b)) := by
      rw [← hxbase]
      exact hconj
    have hfixvals : ∀ i, i < D.marks.length → s.getD (rho.getD i 0) 0 = s.getD i 0 := by
      intro i hi
      have h := k0pAct_getD_of_perm hρperm hs_len hi
      rwa [hfix] at h
    let σρ : Equiv.Perm (Option (Fin (absTag T).rank)) := k0PermOfList T rho hρperm
    have hnodes_all : ∀ x : Option (Fin (absTag T).rank),
        (if p ∣ 2 ^ lab.n - 1 then (1 : ℤ) else -1) • (w1 • π₀ ((k0Kac T).extRoot x)) =
          (k0Kac T).extRoot (σρ x) := by
      intro x
      conv_lhs => rw [← idxNode_nodeIdx (r := (absTag T).rank) x]
      conv_rhs => rw [← idxNode_nodeIdx (r := (absTag T).rank) x]
      have hx : nodeIdx (r := (absTag T).rank) x < D.marks.length := by
        rw [k0Kac_marks_length T]; exact nodeIdx_lt x
      rw [show σρ = k0PermOfList T rho hρperm from rfl,
        k0PermOfList_idxNode_of_lt T hρperm hx]
      exact hσact (nodeIdx (r := (absTag T).rank) x) hx
    have hval_all : ∀ x : Option (Fin (absTag T).rank),
        alcoveValue p μ1 ((k0Kac T).extRoot (σρ x)) =
          alcoveValue p μ1 ((k0Kac T).extRoot x) := by
      intro x
      conv_lhs => rw [← idxNode_nodeIdx (r := (absTag T).rank) x]
      conv_rhs => rw [← idxNode_nodeIdx (r := (absTag T).rank) x]
      have hx : nodeIdx (r := (absTag T).rank) x < D.marks.length := by
        rw [k0Kac_marks_length T]; exact nodeIdx_lt x
      rw [show σρ = k0PermOfList T rho hρperm from rfl,
        k0PermOfList_idxNode_of_lt T hρperm hx]
      have hlt : rho.getD (nodeIdx (r := (absTag T).rank) x) 0 < D.marks.length :=
        k0_getD_lt_of_perm hρperm hx
      rw [hval1 ⟨rho.getD (nodeIdx (r := (absTag T).rank) x) 0, hlt⟩,
        hval1 ⟨nodeIdx (r := (absTag T).rank) x, hx⟩]
      rw [hfixvals (nodeIdx (r := (absTag T).rank) x) hx]
    have hb_inv_omega : k0pInv b ∈ D.omega := inv_mem_omega T hb_omega
    have hb_inv_perm : (k0pInv b).Perm (List.range D.marks.length) := omega_perm T hb_inv_omega
    obtain ⟨v2, hv2⟩ := exists_weyl_omega T hb_inv_omega
    have hma2 := k0_hma_omega T hb_inv_omega
    have hv2' := k0_hv_omega T hb_inv_omega hv2
    have hp : p.Prime := hpair.1
    obtain ⟨g2, hg2, μ2, hμ2, hval2, hgu2, hgw2, hσ2, hσv2⟩ :=
      k0_lang_normal_transport_of (K := k0Kac T) (k0Kac_facts T) (L := GGL) (p := p) hp
        (ε := if p ∣ 2 ^ lab.n - 1 then 1 else -1) (by split_ifs <;> norm_num) hζ
        F θ π₀ hF hθ hg1 hμ1 hgu1 hgw1 hnodes_all hval_all hv2' hma2
    let w2 : WeylGroup (absTag T) := v2 * w1 * (θ v2)⁻¹
    let a2 : Equiv.Perm (Option (Fin (absTag T).rank)) :=
      k0PermOfList T (k0pInv b) hb_inv_perm
    let σ2 : Equiv.Perm (Option (Fin (absTag T).rank)) := a2 * σρ * a2⁻¹
    have hσ2' : ∀ x : Option (Fin (absTag T).rank),
        (if p ∣ 2 ^ lab.n - 1 then (1 : ℤ) else -1) • (w2 • π₀ ((k0Kac T).extRoot x)) =
          (k0Kac T).extRoot (σ2 x) := by
      simpa only [w2, a2, σ2] using hσ2
    have hrho2 : k0ListOfPerm T σ2 = r := by
      simpa only [a2, σ2] using
        (k0ListOfPerm_conj T hb_perm hρperm hr_perm hrho_conj)
    have hsigma2_eq : σ2 = k0PermOfList T r hr_perm := by
      have h := (k0PermOfList_listOfPerm T σ2).symm
      simpa only [hrho2] using h
    have hval2_all : ∀ x : Option (Fin (absTag T).rank),
        alcoveValue p μ2 ((k0Kac T).extRoot (a2 x)) =
          alcoveValue p μ1 ((k0Kac T).extRoot x) := hval2
    let s2 : List ℕ := List.ofFn (fun i : Fin D.marks.length =>
      (alcoveValue p μ2 ((k0Kac T).extRoot (idxNode (r := (absTag T).rank) i.val))).toNat)
    have hs2_eq : s2 = k0pAct (k0pInv b) s := by
      dsimp only [s2]
      rw [k0_ofFn_alcove_eq_pAct T p (μ := μ1) (μ' := μ2) hb_inv_perm hval2_all, hs_val]
    have hb_inv_fix : k0pAct (k0pInv b) s = s := by
      have h := k0pAct_mul T hb_inv_perm hb_perm hs_len
      rw [k0pMul_inv_left hb_perm, hb_fix, k0pAct_id T hs_len] at h
      exact h.symm
    have hs2 : s2 = s := by rw [hs2_eq, hb_inv_fix]
    have hval2_s : ∀ i : Fin D.marks.length,
        alcoveValue p μ2 ((k0Kac T).extRoot (idxNode (r := (absTag T).rank) i.val)) =
          (s.getD i.val 0 : ℤ) := by
      intro i
      have h2 : (alcoveValue p μ2 ((k0Kac T).extRoot (idxNode (r := (absTag T).rank) i.val))).toNat =
          s.getD i.val 0 := by
        have h := congrArg (fun l => l.getD i.val 0) hs2
        dsimp only [s2] at h
        rwa [List.getD_eq_getElem _ _ (by rw [List.length_ofFn]; exact i.isLt),
          List.getElem_ofFn] at h
      have hnn := KacData.alcoveValue_nonneg (k0Kac T) (k0Kac_facts T) hμ2
        ((k0Kac T).isRoot_extRoot (idxNode (r := (absTag T).rank) i.val))
      calc alcoveValue p μ2 ((k0Kac T).extRoot (idxNode (r := (absTag T).rank) i.val))
          = ((alcoveValue p μ2 ((k0Kac T).extRoot (idxNode (r := (absTag T).rank) i.val))).toNat : ℤ) :=
            (Int.toNat_of_nonneg hnn).symm
        _ = (s.getD i.val 0 : ℤ) := by rw [h2]
    have hσact2 : ∀ i, i < D.marks.length →
        (if p ∣ 2 ^ lab.n - 1 then (1 : ℤ) else -1) •
          (w2 • π₀ ((k0Kac T).extRoot (idxNode (r := (absTag T).rank) i))) =
          (k0Kac T).extRoot (idxNode (r := (absTag T).rank) (r.getD i 0)) := by
      intro i hi
      have h := hσ2' (idxNode (r := (absTag T).rank) i)
      rw [hsigma2_eq] at h
      rw [k0PermOfList_idxNode_of_lt T hr_perm hi] at h
      exact h
    exact ⟨g2, μ2, w2, s, base, r, hg2, hgu2, hgw2, hμ2, hs_len, hs_mem, hs_min,
      hbase_eq, hr_mem, hr_perm.length_eq.trans (by rw [List.length_range]), hval2_s, hσact2⟩


private theorem k0_rat_untw_one
    (T : GGKacType) (w₁ : WeylGroup (absTag T)) {rho : List ℕ}
    (hrho : rho.Perm (List.range (k0DiagOf T).marks.length))
    (hact : ∀ i, i < (k0DiagOf T).marks.length →
      w₁ • (k0Kac T).extRoot (idxNode (r := (absTag T).rank) i) =
        (k0Kac T).extRoot (idxNode (r := (absTag T).rank) (rho.getD i 0))) :
    ∃ a ∈ (k0DiagOf T).omega, rho = k0pMul a (k0Rho0 (k0DiagOf T) false 1) := by
  classical
  let D := k0DiagOf T
  let σfun : ℕ → ℕ := fun i => rho.getD i 0
  have hbound : ∀ i, i < D.marks.length → σfun i < D.marks.length := by
    intro i hi
    exact k0_getD_lt_of_perm hrho hi
  have hweyl : ∀ i, i < D.marks.length →
      w₁ • (k0Kac T).extRoot (idxNode (r := (absTag T).rank) i) =
        (k0Kac T).extRoot (idxNode (r := (absTag T).rank) (σfun i)) := hact
  obtain ⟨a, ha, haeq⟩ := exists_omega_of_weyl T hbound hweyl
  refine ⟨a, ha, ?_⟩
  rw [k0Rho0_one T, k0pMul_id_right_perm T (omega_perm T ha)]
  apply k0_list_ext_getD
  · rw [hrho.length_eq, (omega_perm T ha).length_eq, List.length_range]
  · intro i hi
    have hi' : i < (k0DiagOf T).marks.length := by
      rw [hrho.length_eq, List.length_range] at hi
      exact hi
    simpa [σfun] using haeq i hi'

private theorem k0_rat_untw_two_weyl
    (T : GGKacType) (w₁ : WeylGroup (absTag T)) {rho : List ℕ}
    (hrho : rho.Perm (List.range (k0DiagOf T).marks.length))
    (hact : ∀ i, i < (k0DiagOf T).marks.length →
      -(w₁ • (k0Kac T).extRoot (idxNode (r := (absTag T).rank) i)) =
        (k0Kac T).extRoot (idxNode (r := (absTag T).rank) (rho.getD i 0))) :
    ∃ (v : WeylGroup (absTag T)) (cfun : ℕ → ℕ),
      (∀ i, i < (k0DiagOf T).marks.length →
        cfun i = (k0DiagOf T).tau0.getD (rho.getD i 0) 0) ∧
      (∀ i, i < (k0DiagOf T).marks.length → cfun i < (k0DiagOf T).marks.length) ∧
      (∀ i, i < (k0DiagOf T).marks.length →
        (v⁻¹ * w₁) • (k0Kac T).extRoot (idxNode (r := (absTag T).rank) i) =
          (k0Kac T).extRoot (idxNode (r := (absTag T).rank) (cfun i))) := by
  classical
  obtain ⟨v0, hv0⟩ := exists_weyl_tau0 T
  have hinv := k0_inv_smul_tau0 T hv0
  let cfun : ℕ → ℕ := fun i => (k0DiagOf T).tau0.getD (rho.getD i 0) 0
  have hbound : ∀ i, i < (k0DiagOf T).marks.length →
      cfun i < (k0DiagOf T).marks.length := by
    intro i hi
    exact k0_getD_lt_of_perm (tau0_perm T) (k0_getD_lt_of_perm hrho hi)
  have hweyl : ∀ i, i < (k0DiagOf T).marks.length →
      (v0⁻¹ * w₁) • (k0Kac T).extRoot (idxNode (r := (absTag T).rank) i) =
        (k0Kac T).extRoot (idxNode (r := (absTag T).rank) (cfun i)) := by
    intro i hi
    have hiρ : rho.getD i 0 < (k0DiagOf T).marks.length := k0_getD_lt_of_perm hrho hi
    have h := hact i hi
    have hw : w₁ • (k0Kac T).extRoot (idxNode (r := (absTag T).rank) i) =
        - (k0Kac T).extRoot (idxNode (r := (absTag T).rank) (rho.getD i 0)) := by
      calc w₁ • (k0Kac T).extRoot (idxNode (r := (absTag T).rank) i)
          = - (-(w₁ • (k0Kac T).extRoot (idxNode (r := (absTag T).rank) i))) := by rw [neg_neg]
        _ = - (k0Kac T).extRoot (idxNode (r := (absTag T).rank) (rho.getD i 0)) := by rw [h]
    calc (v0⁻¹ * w₁) • (k0Kac T).extRoot (idxNode (r := (absTag T).rank) i)
        = v0⁻¹ • (w₁ • (k0Kac T).extRoot (idxNode (r := (absTag T).rank) i)) := by rw [mul_smul]
      _ = v0⁻¹ • (- (k0Kac T).extRoot (idxNode (r := (absTag T).rank) (rho.getD i 0))) := by rw [hw]
      _ = - (v0⁻¹ • (k0Kac T).extRoot (idxNode (r := (absTag T).rank) (rho.getD i 0))) := by rw [smul_neg]
      _ = - (- (k0Kac T).extRoot (idxNode (r := (absTag T).rank)
            ((k0DiagOf T).tau0.getD (rho.getD i 0) 0))) := by rw [hinv _ hiρ]
      _ = (k0Kac T).extRoot (idxNode (r := (absTag T).rank) (cfun i)) := by rw [neg_neg]
  exact ⟨v0, cfun, fun i _ => rfl, hbound, hweyl⟩

private theorem k0_rat_untw_two
    (T : GGKacType) (w₁ : WeylGroup (absTag T)) {rho : List ℕ}
    (hrho : rho.Perm (List.range (k0DiagOf T).marks.length))
    (hact : ∀ i, i < (k0DiagOf T).marks.length →
      -(w₁ • (k0Kac T).extRoot (idxNode (r := (absTag T).rank) i)) =
        (k0Kac T).extRoot (idxNode (r := (absTag T).rank) (rho.getD i 0))) :
    ∃ a ∈ (k0DiagOf T).omega, rho = k0pMul a (k0Rho0 (k0DiagOf T) false 2) := by
  classical
  obtain ⟨v0, cfun, hcfun, hbound, hweyl⟩ := k0_rat_untw_two_weyl T w₁ hrho hact
  obtain ⟨c, hc, hceq⟩ := exists_omega_of_weyl T hbound hweyl
  have hcr : c = k0pMul (k0DiagOf T).tau0 rho := by
    apply k0_list_ext_getD
    · rw [(omega_perm T hc).length_eq, List.length_range, k0pMul, List.length_map,
        hrho.length_eq, List.length_range]
    · intro i hi
      have hi' : i < (k0DiagOf T).marks.length := by
        rw [(omega_perm T hc).length_eq, List.length_range] at hi
        exact hi
      rw [k0pMul_getD (k0DiagOf T).tau0 rho
        (by rw [hrho.length_eq, List.length_range]; exact hi')]
      simpa [hcfun i hi'] using (hceq i hi').symm
  have htau_c : k0pMul (k0DiagOf T).tau0 c = rho := by
    rw [hcr, ← k0pMul_assoc_perm T (tau0_perm T) (tau0_perm T) hrho,
      tau0_mul_tau0 T, k0pMul_id_left_perm T hrho]
  let a_om : List ℕ := k0pMul (k0DiagOf T).tau0 (k0pMul c (k0DiagOf T).tau0)
  have ha_om : a_om ∈ (k0DiagOf T).omega := tau0_conj_mem_omega T hc
  refine ⟨a_om, ha_om, ?_⟩
  rw [k0Rho0_two T]
  calc rho = k0pMul (k0DiagOf T).tau0 c := htau_c.symm
    _ = k0pMul (k0DiagOf T).tau0 (k0pMul c (k0pId (k0DiagOf T).marks.length)) := by
      rw [k0pMul_id_right_perm T (omega_perm T hc)]
    _ = k0pMul (k0DiagOf T).tau0
          (k0pMul c (k0pMul (k0DiagOf T).tau0 (k0DiagOf T).tau0)) := by
      rw [tau0_mul_tau0 T]
    _ = k0pMul (k0DiagOf T).tau0
          (k0pMul (k0pMul c (k0DiagOf T).tau0) (k0DiagOf T).tau0) := by
      rw [k0pMul_assoc_perm T (omega_perm T hc) (tau0_perm T) (tau0_perm T)]
    _ = k0pMul (k0pMul (k0DiagOf T).tau0 (k0pMul c (k0DiagOf T).tau0))
          (k0DiagOf T).tau0 := by
      rw [k0pMul_assoc_perm T (tau0_perm T)
        (k0pMul_perm (omega_perm T hc) (tau0_perm T)) (tau0_perm T)]
    _ = k0pMul a_om (k0DiagOf T).tau0 := rfl

theorem k0_rat_untw (T : GGKacType)
    {ε : ℤ} {d : ℕ} (hεd : ε = 1 ∧ d = 1 ∨ ε = -1 ∧ d = 2) (w₁ : WeylGroup (absTag T))
    {rho : List ℕ} (hrho : rho.Perm (List.range (k0DiagOf T).marks.length))
    (hact : ∀ i, i < (k0DiagOf T).marks.length →
      ε • (w₁ • (k0Kac T).extRoot (idxNode (r := (absTag T).rank) i)) =
        (k0Kac T).extRoot (idxNode (r := (absTag T).rank) (rho.getD i 0))) :
    ∃ a ∈ (k0DiagOf T).omega, rho = k0pMul a (k0Rho0 (k0DiagOf T) false d) := by
  rcases hεd with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact k0_rat_untw_one T w₁ hrho (fun i hi => by simpa using hact i hi)
  · exact k0_rat_untw_two T w₁ hrho (fun i hi => by simpa using hact i hi)

theorem exists_k0KacPart_of
    {lab : LargeEvenLabel} {p : ℕ} (hpair : GGKacExcPair lab p)
    {T : GGKacType} {tw : Bool} (hT : ggKacTypeOfLabel lab = some (T, tw))
    (F : ModGL (absTag T) GGL →* ModGL (absTag T) GGL)
    (θ : WeylGroup (absTag T) ≃* WeylGroup (absTag T))
    (π₀ : (Fin (absTag T).rank → ℤ) ≃ₗ[ℤ] (Fin (absTag T).rank → ℤ))
    (hF : ∀ v, F (canonicalRep (coxeterSystem (absTag T)) GGL v) =
      canonicalRep (coxeterSystem (absTag T)) GGL (θ v))
    (hθ : ∀ v γ, θ v • π₀ γ = π₀ (v • γ))
    {u : ModGL (absTag T) GGL} {ζ : GGLˣ} (hζ : orderOf ζ = p)
    (h0 : ∃ g ∈ adjointGroup (absTag T) GGL, ∃ (μ : Fin (absTag T).rank → ℤ)
      (w : WeylGroup (absTag T)) (σ : Equiv.Perm (Option (Fin (absTag T).rank))),
      (k0Kac T).IsNormal p μ ∧ g⁻¹ * u * g = rootDiagUnit (absTag T) (fun i => ζ ^ μ i) ∧
      g⁻¹ * F g = canonicalRep (coxeterSystem (absTag T)) GGL w ∧
      (∀ x, (if p ∣ 2 ^ lab.n - 1 then (1 : ℤ) else -1) • (w • π₀ ((k0Kac T).extRoot x)) =
        (k0Kac T).extRoot (σ x)) ∧
      ∀ x, alcoveValue p μ ((k0Kac T).extRoot (σ x)) = alcoveValue p μ ((k0Kac T).extRoot x))
    (hrat : ∀ (w₁ : WeylGroup (absTag T)) (rho : List ℕ),
      rho.Perm (List.range (k0DiagOf T).marks.length) →
      (∀ i, i < (k0DiagOf T).marks.length →
        (if p ∣ 2 ^ lab.n - 1 then (1 : ℤ) else -1) •
          (w₁ • π₀ ((k0Kac T).extRoot (idxNode (r := (absTag T).rank) i))) =
          (k0Kac T).extRoot (idxNode (r := (absTag T).rank) (rho.getD i 0))) →
      ∃ a ∈ (k0DiagOf T).omega,
        rho = k0pMul a (k0Rho0 (k0DiagOf T) tw (if p ∣ 2 ^ lab.n - 1 then 1 else 2))) :
    ∃ (row : KacRow lab p) (_ : row.T = T) (g : ModGL (absTag T) GGL)
      (μ : Fin (absTag T).rank → ℤ) (w : WeylGroup (absTag T))
      (nodeMap : (Fin row.diagram.marks.length → ℤ) →ₗ[ℤ] (Fin (absTag T).rank → ℤ))
      (frobLinear : (Fin (absTag T).rank → ℤ) ≃ₗ[ℤ] (Fin (absTag T).rank → ℤ)),
      g ∈ adjointGroup (absTag T) GGL ∧
      g⁻¹ * u * g = rootDiagUnit (absTag T) (fun i => ζ ^ μ i) ∧
      g⁻¹ * F g = canonicalRep (coxeterSystem (absTag T)) GGL w ∧
      Function.Surjective nodeMap ∧
      nodeMap.ker = Submodule.span ℤ
        ({fun i : Fin row.diagram.marks.length => (row.diagram.marks.getD i.val 0 : ℤ)} :
          Set (Fin row.diagram.marks.length → ℤ)) ∧
      (∀ i, IsRoot (absTag T) (nodeMap (Pi.single i 1))) ∧
      (∀ i : Fin row.diagram.marks.length,
        rootChar (fun j => ζ ^ μ j) (nodeMap (Pi.single i 1)) = ζ ^ (row.s.getD i.val 0)) ∧
      Submodule.span ℤ (kernelRoots (rootCharHom (fun j => ζ ^ μ j))) =
        Submodule.span ℤ {γ | ∃ i : Fin row.diagram.marks.length,
          row.s.getD i.val 0 = 0 ∧ γ = nodeMap (Pi.single i 1)} ∧
      (∀ γ, IsRoot (absTag T) γ → frobLinear γ = w • π₀ γ) ∧
      (∀ i : Fin row.diagram.marks.length, frobLinear (nodeMap (Pi.single i 1)) =
        (if row.d = 1 then 1 else -1 : ℤ) • nodeMap (Pi.single (row.nodePerm i) 1)) ∧
      ∀ (i : Fin row.diagram.marks.length) (j : Fin (absTag T).rank), i.val = j.val + 1 →
        nodeMap (Pi.single i 1) = Pi.single j 1 := by
  classical
  let D := k0DiagOf T
  obtain ⟨g, μ, w, s, base, rho, hg, hgu, hgw, hμ, hs_len, hs_mem, hs_min, hbase_eq,
    hrho_mem, hrho_len, hval, hσact⟩ :=
    k0_finalData_of (tw := tw) T hpair F θ π₀ hF hθ hζ h0 hrat
  obtain ⟨a0, ha0, hbase_eq'⟩ :=
    (k0BaseAux_mem (rho0 := k0Rho0 D tw (if p ∣ 2 ^ lab.n - 1 then 1 else 2))
      hbase_eq).1
  have hbase_perm : base.Perm (List.range D.marks.length) := by
    rw [hbase_eq']
    exact k0pMul_perm (omega_perm T ha0) (k0Rho0_perm_tw T tw _ (by split_ifs <;> simp))
  have hrho_perm : rho.Perm (List.range D.marks.length) :=
    k0Reps_perm T (fun b hb => (List.mem_filter.mp hb).1) hbase_perm hrho_mem
  let nodePerm : Equiv.Perm (Fin D.marks.length) := k0FinPermOfList rho hrho_perm
  let row : KacRow lab p := {
    T := T
    tw := tw
    type_eq := hT
    d := if p ∣ 2 ^ lab.n - 1 then 1 else 2
    d_eq := rfl
    s := s
    s_length := hs_len
    s_mem := hs_mem
    s_min := hs_min
    base := base
    base_eq := hbase_eq
    rho := rho
    rho_length := hrho_len
    rho_mem := hrho_mem
    nodePerm := nodePerm
    rho_apply := fun i => k0FinPermOfList_apply rho hrho_perm i
    D := k0Datum D s rho (if p ∣ 2 ^ lab.n - 1 then 1 else 2) lab.n
      (((D.omega).filter (fun a => decide (k0pAct a s = s))).length)
    D_eq := rfl
    valid := ggKacValid_k0Datum hT hpair.2.2.1 hs_mem hs_min hbase_eq hrho_mem }
  obtain ⟨nodeMap, hnode, hsurj, hker⟩ := exists_k0NodeMap T
  have hiff : ∀ i : Fin D.marks.length,
      s.getD i.val 0 = 0 ↔
        alcoveValue p μ ((k0Kac T).extRoot (idxNode (r := (absTag T).rank) i.val)) = 0 := by
    intro i
    rw [hval i]
    constructor <;> intro h <;> exact_mod_cast h
  refine ⟨row, rfl, g, μ, w, nodeMap, π₀.trans (DistribMulAction.toLinearEquiv ℤ _ w),
    hg, hgu, hgw, hsurj, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa [row, KacRow.diagram, D] using hker
  · intro i
    rw [hnode i]
    exact (k0Kac T).isRoot_extRoot _
  · intro i
    rw [hnode i, KacData.rootChar_eq_zpow,
      k0_zpow_dot_eq_zpow_alcove T hζ hμ ((k0Kac T).isRoot_extRoot _), hval i,
      Int.toNat_natCast, zpow_natCast]
  · rw [span_kernelRoots_eq_zero_nodes T hpair.1 hζ hμ]
    congr 1
    ext γ
    simp only [hnode]
    constructor
    · rintro ⟨i, hi, rfl⟩
      exact ⟨i, (hiff i).mpr hi, rfl⟩
    · rintro ⟨i, hi, rfl⟩
      exact ⟨i, (hiff i).mp hi, rfl⟩
  · intro γ _
    rw [LinearEquiv.trans_apply, DistribMulAction.toLinearEquiv_apply]
  · intro i
    have hε2 : (if p ∣ 2 ^ lab.n - 1 then (1 : ℤ) else -1) *
        (if p ∣ 2 ^ lab.n - 1 then (1 : ℤ) else -1) = 1 := by
      split_ifs <;> norm_num
    have h := hσact i i.isLt
    have hw : w • π₀ ((k0Kac T).extRoot (idxNode (r := (absTag T).rank) i.val)) =
        (if p ∣ 2 ^ lab.n - 1 then (1 : ℤ) else -1) •
          (k0Kac T).extRoot (idxNode (r := (absTag T).rank) (rho.getD i.val 0)) := by
      have h' := congrArg
        (fun z => (if p ∣ 2 ^ lab.n - 1 then (1 : ℤ) else -1) • z) h
      rwa [smul_smul, hε2, one_smul] at h'
    rw [LinearEquiv.trans_apply, DistribMulAction.toLinearEquiv_apply, hnode i, hnode (nodePerm i),
      show (nodePerm i).val = rho.getD i.val 0 from k0FinPermOfList_apply rho hrho_perm i, hw]
    have hdrow : row.d = (if p ∣ 2 ^ lab.n - 1 then 1 else 2) := rfl
    rw [hdrow]
    by_cases hcond : p ∣ 2 ^ lab.n - 1 <;> simp [hcond]
  · intro i j hij
    rw [hnode i]
    rw [show idxNode (r := (absTag T).rank) i.val = some j from by
      rw [hij]
      simpa using k0_idxNode_succ j.val j.isLt]
    rfl

theorem exists_k0KacPart
    {lab : LargeEvenLabel} {p : ℕ} (hpair : GGKacExcPair lab p) (hn : 1 ≤ lab.n)
    {T : GGKacType} (hT : ggKacTypeOfLabel lab = some (T, false))
    {u : ModGL (absTag T) GGL} (hu : u ∈ adjointGroup (absTag T) GGL)
    (huF : entrywiseFrobGL (absTag T) GGL 2 lab.n u = u) (hup : u ^ p = 1)
    {ζ : GGLˣ} (hζ : orderOf ζ = p) :
    ∃ (row : KacRow lab p) (_ : row.T = T) (g : ModGL (absTag T) GGL)
      (μ : Fin (absTag T).rank → ℤ) (w : WeylGroup (absTag T))
      (nodeMap : (Fin row.diagram.marks.length → ℤ) →ₗ[ℤ] (Fin (absTag T).rank → ℤ))
      (frobLinear : (Fin (absTag T).rank → ℤ) ≃ₗ[ℤ] (Fin (absTag T).rank → ℤ)),
      g ∈ adjointGroup (absTag T) GGL ∧
      g⁻¹ * u * g = rootDiagUnit (absTag T) (fun i => ζ ^ μ i) ∧
      g⁻¹ * entrywiseFrobGL (absTag T) GGL 2 lab.n g =
        canonicalRep (coxeterSystem (absTag T)) GGL w ∧
      Function.Surjective nodeMap ∧
      nodeMap.ker = Submodule.span ℤ
        ({fun i : Fin row.diagram.marks.length => (row.diagram.marks.getD i.val 0 : ℤ)} :
          Set (Fin row.diagram.marks.length → ℤ)) ∧
      (∀ i, IsRoot (absTag T) (nodeMap (Pi.single i 1))) ∧
      (∀ i : Fin row.diagram.marks.length,
        rootChar (fun j => ζ ^ μ j) (nodeMap (Pi.single i 1)) = ζ ^ (row.s.getD i.val 0)) ∧
      Submodule.span ℤ (kernelRoots (rootCharHom (fun j => ζ ^ μ j))) =
        Submodule.span ℤ {γ | ∃ i : Fin row.diagram.marks.length,
          row.s.getD i.val 0 = 0 ∧ γ = nodeMap (Pi.single i 1)} ∧
      (∀ γ, IsRoot (absTag T) γ → frobLinear γ = w • γ) ∧
      (∀ i : Fin row.diagram.marks.length, frobLinear (nodeMap (Pi.single i 1)) =
        (if row.d = 1 then 1 else -1 : ℤ) • nodeMap (Pi.single (row.nodePerm i) 1)) ∧
      ∀ (i : Fin row.diagram.marks.length) (j : Fin (absTag T).rank), i.val = j.val + 1 →
        nodeMap (Pi.single i 1) = Pi.single j 1 := by
  classical
  let F : ModGL (absTag T) GGL →* ModGL (absTag T) GGL :=
    entrywiseFrobGL (absTag T) GGL 2 lab.n
  let θ : WeylGroup (absTag T) ≃* WeylGroup (absTag T) := MulEquiv.refl _
  let π₀ : (Fin (absTag T).rank → ℤ) ≃ₗ[ℤ] (Fin (absTag T).rank → ℤ) := LinearEquiv.refl ℤ _
  have hF : ∀ v, F (canonicalRep (coxeterSystem (absTag T)) GGL v) =
      canonicalRep (coxeterSystem (absTag T)) GGL (θ v) := by
    intro v
    simpa [F, θ] using
      CFSG.RankThree.PartOne.KE.frobenius_canonicalRep (iterateFrobenius GGL 2 lab.n) v
  have hθ : ∀ v γ, θ v • π₀ γ = π₀ (v • γ) := by
    intro v γ
    rfl
  have hεd : (if p ∣ 2 ^ lab.n - 1 then (1 : ℤ) else -1) = 1 ∧
      (if p ∣ 2 ^ lab.n - 1 then 1 else 2) = 1 ∨
      (if p ∣ 2 ^ lab.n - 1 then (1 : ℤ) else -1) = -1 ∧
      (if p ∣ 2 ^ lab.n - 1 then 1 else 2) = 2 := by
    by_cases h : p ∣ 2 ^ lab.n - 1
    · left
      rw [ite_eq_left h, ite_eq_left h]
      exact ⟨rfl, rfl⟩
    · right
      rw [ite_eq_right h, ite_eq_right h]
      exact ⟨rfl, rfl⟩
  have h0 : ∃ g ∈ adjointGroup (absTag T) GGL, ∃ (μ : Fin (absTag T).rank → ℤ)
      (w : WeylGroup (absTag T)) (σ : Equiv.Perm (Option (Fin (absTag T).rank))),
      (k0Kac T).IsNormal p μ ∧ g⁻¹ * u * g = rootDiagUnit (absTag T) (fun i => ζ ^ μ i) ∧
      g⁻¹ * F g = canonicalRep (coxeterSystem (absTag T)) GGL w ∧
      (∀ x, (if p ∣ 2 ^ lab.n - 1 then (1 : ℤ) else -1) •
        (w • π₀ ((k0Kac T).extRoot x)) = (k0Kac T).extRoot (σ x)) ∧
      ∀ x, alcoveValue p μ ((k0Kac T).extRoot (σ x)) = alcoveValue p μ ((k0Kac T).extRoot x) := by
    obtain ⟨g0, hg0, μ0, w0, σ0, hμ0, hgu0, hgw0, hσ0, hσv0⟩ :=
      exists_lang_alcove_normal (K := k0Kac T) (k0Kac_facts T) (k0Kac_hup T) (k0Kac_hdown T)
        (k0_hτ_absTag T) (CFSG.LieType.Chevalley.algebraicClosure_isAlgebraic_zmod 2 (ZMod 2)) lab.n hn
        hpair.1 hpair.2.1 (k0_eps_cases (lab := lab) (p := p)) (k0_eps_dvd hpair) hζ hu huF hup
    exact ⟨g0, hg0, μ0, w0, σ0, hμ0, hgu0, by simpa [F] using hgw0, by simpa [π₀] using hσ0, hσv0⟩
  have hrat : ∀ (w₁ : WeylGroup (absTag T)) (rho : List ℕ),
      rho.Perm (List.range (k0DiagOf T).marks.length) →
      (∀ i, i < (k0DiagOf T).marks.length →
        (if p ∣ 2 ^ lab.n - 1 then (1 : ℤ) else -1) •
          (w₁ • π₀ ((k0Kac T).extRoot (idxNode (r := (absTag T).rank) i))) =
          (k0Kac T).extRoot (idxNode (r := (absTag T).rank) (rho.getD i 0))) →
      ∃ a ∈ (k0DiagOf T).omega,
        rho = k0pMul a (k0Rho0 (k0DiagOf T) false (if p ∣ 2 ^ lab.n - 1 then 1 else 2)) := by
    intro w₁ rho hrho hact
    rcases hεd with ⟨hε1, hd1⟩ | ⟨hεm1, hd2⟩
    · have h := k0_rat_untw (T := T) (ε := 1) (d := 1) (Or.inl ⟨rfl, rfl⟩) w₁ hrho (by
        intro i hi
        have h' := hact i hi
        rw [hε1] at h'
        simpa [π₀] using h')
      simpa [hd1] using h
    · have h := k0_rat_untw (T := T) (ε := -1) (d := 2) (Or.inr ⟨rfl, rfl⟩) w₁ hrho (by
        intro i hi
        have h' := hact i hi
        rw [hεm1] at h'
        simpa [π₀] using h')
      simpa [hd2] using h
  obtain ⟨row, hrowT, g, μ, w, nodeMap, frobLinear, hg, hgu, hgw, hsurj, hker, hroot, hchar,
    hker2, hfrob, hnode, hdown⟩ :=
    exists_k0KacPart_of (tw := false) hpair hT F θ π₀ hF hθ hζ h0 hrat
  refine ⟨row, hrowT, g, μ, w, nodeMap, frobLinear, hg, hgu, hgw, hsurj, hker, hroot, hchar,
    hker2, ?_, hnode, hdown⟩
  intro γ hγ
  rw [hfrob γ hγ]
  rfl


end CFSG.StandardType.GGK0MarkedKacIface1587

end
