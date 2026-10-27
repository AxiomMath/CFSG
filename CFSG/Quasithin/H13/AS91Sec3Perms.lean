module

public import CFSG.Quasithin.H13.AS91Sec3Base
public import Certificates.Data.CFSGNative.AS91.M24Geom

public section

namespace CFSG.Quasithin.H13.AS91.M24G

open CFSG.Monster.Code (bridgePA bridgePB bridgePA_mem bridgePB_mem mem_AutPerm_of_basis)

theorem repT_pA : RepT Native.pATab CFSG.Monster.Code.bridgePA := by
  unfold RepT
  decide +kernel

theorem repT_pB : RepT Native.pBTab CFSG.Monster.Code.bridgePB := by
  unfold RepT
  decide +kernel

theorem repT_pBi : RepT Native.pBiTab CFSG.Monster.Code.bridgePB⁻¹ := by
  unfold RepT
  decide +kernel

@[expose] def genPerm : Fin 3 → Equiv.Perm (Fin 24) := ![bridgePA, bridgePB, bridgePB⁻¹]

theorem genTabs_rep (j : Fin 3) : RepT (Native.genTabs.getD j #[]) (genPerm j) := by
  fin_cases j
  · exact repT_pA
  · exact repT_pB
  · exact repT_pBi

theorem genTabs_rep_nat {j : ℕ} (hj : j < 3) :
    RepT (Native.genTabs.getD j #[]) (genPerm ⟨j, hj⟩) :=
  genTabs_rep ⟨j, hj⟩

theorem genPerm_mem (j : Fin 3) : genPerm j ∈ CFSG.ASVolI.ChH.M24g := by
  fin_cases j
  · exact bridgePA_mem
  · exact bridgePB_mem
  · exact CFSG.ASVolI.ChH.M24g.inv_mem bridgePB_mem

theorem exists_repT_of_mem {tabs : List (Array ℕ)} {n : ℕ} (hn : tabs.length = n)
    {P : Fin n → Equiv.Perm (Fin 24)} (h : ∀ j : Fin n, RepT (tabs.getD j #[]) (P j))
    {t : Array ℕ} (ht : t ∈ tabs) : ∃ j : Fin n, RepT t (P j) := by
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem ht
  have hi' : i < n := hn ▸ hi
  refine ⟨⟨i, hi'⟩, ?_⟩
  have h1 : tabs.getD i #[] = tabs[i] := List.getD_eq_getElem _ _ hi
  have h2 : RepT (tabs.getD i #[]) (P ⟨i, hi'⟩) := h ⟨i, hi'⟩
  rwa [h1] at h2

theorem exists_repT_of_mem_genTabs {t : Array ℕ} (ht : t ∈ Native.genTabs) :
    ∃ j : Fin 3, RepT t (genPerm j) :=
  exists_repT_of_mem (tabs := Native.genTabs) (n := 3) rfl genTabs_rep ht

@[expose] def lPerm0 : Equiv.Perm (Fin 24) where
  toFun := ![12, 11, 8, 15, 10, 13, 14, 9, 19, 20, 23, 16, 21, 18, 17, 22, 1, 6, 5, 2, 7, 0, 3, 4]
  invFun :=
    ![21, 16, 19, 22, 23, 18, 17, 20, 2, 7, 4, 1, 0, 5, 6, 3, 11, 14, 13, 8, 9, 12, 15, 10]
  left_inv := by decide
  right_inv := by decide

@[expose] def lPerm1 : Equiv.Perm (Fin 24) where
  toFun := ![3, 4, 2, 5, 6, 1, 7, 0, 14, 9, 15, 8, 11, 12, 10, 13, 22, 17, 23, 16, 19, 20, 18, 21]
  invFun :=
    ![7, 5, 2, 0, 1, 3, 4, 6, 11, 9, 14, 12, 13, 15, 8, 10, 19, 17, 22, 20, 21, 23, 16, 18]
  left_inv := by decide
  right_inv := by decide

@[expose] def lPerm2 : Equiv.Perm (Fin 24) where
  toFun := ![15, 9, 8, 14, 13, 11, 10, 12, 3, 5, 4, 2, 1, 7, 6, 0, 22, 16, 17, 23, 20, 18, 19, 21]
  invFun :=
    ![15, 12, 11, 8, 10, 9, 14, 13, 2, 1, 6, 5, 7, 4, 3, 0, 17, 18, 21, 22, 20, 23, 16, 19]
  left_inv := by decide
  right_inv := by decide

@[expose] def lPerm3 : Equiv.Perm (Fin 24) where
  toFun := ![10, 9, 15, 12, 13, 14, 8, 11, 17, 18, 20, 23, 22, 21, 19, 16, 1, 2, 4, 7, 6, 5, 3, 0]
  invFun :=
    ![23, 16, 17, 22, 18, 21, 20, 19, 6, 1, 0, 7, 3, 4, 5, 2, 15, 8, 9, 14, 10, 13, 12, 11]
  left_inv := by decide
  right_inv := by decide

@[expose] def lPerm : Fin 4 → Equiv.Perm (Fin 24) := ![lPerm0, lPerm1, lPerm2, lPerm3]

theorem repT_lPerm (j : Fin 4) : RepT (Native.lTabs.getD j #[]) (lPerm j) := by
  revert j
  unfold RepT
  decide +kernel

theorem exists_repT_of_mem_lTabs {t : Array ℕ} (ht : t ∈ Native.lTabs) :
    ∃ j : Fin 4, RepT t (lPerm j) :=
  exists_repT_of_mem (tabs := Native.lTabs) (n := 4) rfl repT_lPerm ht

private theorem lPerm_basis :
    ∀ (j : Fin 4) (i : Fin 12), CFSG.Monster.Code.B i ∘ ⇑(lPerm j) ∈ CFSG.Monster.Code.C := by
  decide +kernel

private theorem lPerm_basis' :
    ∀ (j : Fin 4) (i : Fin 12), CFSG.Monster.Code.B i ∘ ⇑(lPerm j)⁻¹ ∈ CFSG.Monster.Code.C := by
  decide +kernel

theorem lPerm_mem (j : Fin 4) : lPerm j ∈ CFSG.ASVolI.ChH.M24g :=
  mem_AutPerm_of_basis (lPerm_basis j) (lPerm_basis' j)

@[expose] def uPerm0 : Equiv.Perm (Fin 24) where
  toFun := ![18, 16, 19, 17, 15, 14, 12, 13, 4, 5, 7, 6, 21, 22, 23, 20, 8, 11, 10, 9, 3, 1, 2, 0]
  invFun :=
    ![23, 21, 22, 20, 8, 9, 11, 10, 16, 19, 18, 17, 6, 7, 5, 4, 1, 3, 0, 2, 15, 12, 13, 14]
  left_inv := by decide
  right_inv := by decide

@[expose] def uPerm1 : Equiv.Perm (Fin 24) where
  toFun := ![22, 21, 20, 23, 1, 2, 3, 0, 19, 16, 17, 18, 4, 7, 6, 5, 13, 12, 14, 15, 8, 10, 9, 11]
  invFun :=
    ![7, 4, 5, 6, 12, 15, 14, 13, 20, 22, 21, 23, 17, 16, 18, 19, 9, 10, 11, 8, 2, 1, 0, 3]
  left_inv := by decide
  right_inv := by decide

@[expose] def uPerm2 : Equiv.Perm (Fin 24) where
  toFun := ![5, 4, 7, 6, 20, 21, 22, 23, 3, 2, 1, 0, 18, 19, 16, 17, 12, 15, 13, 14, 10, 8, 9, 11]
  invFun :=
    ![11, 10, 9, 8, 1, 0, 3, 2, 21, 22, 20, 23, 16, 18, 19, 17, 14, 15, 12, 13, 4, 5, 6, 7]
  left_inv := by decide
  right_inv := by decide

@[expose] def uPerm3 : Equiv.Perm (Fin 24) where
  toFun := ![0, 2, 1, 3, 18, 16, 19, 17, 5, 7, 4, 6, 23, 21, 22, 20, 8, 11, 10, 9, 13, 12, 14, 15]
  invFun :=
    ![0, 2, 1, 3, 10, 8, 11, 9, 16, 19, 18, 17, 21, 20, 22, 23, 5, 7, 4, 6, 15, 13, 14, 12]
  left_inv := by decide
  right_inv := by decide

@[expose] def uPerm : Fin 4 → Equiv.Perm (Fin 24) := ![uPerm0, uPerm1, uPerm2, uPerm3]

theorem repT_uPerm (j : Fin 4) : RepT (Native.uTabs.getD j #[]) (uPerm j) := by
  revert j
  unfold RepT
  decide +kernel

theorem exists_repT_of_mem_uTabs {t : Array ℕ} (ht : t ∈ Native.uTabs) :
    ∃ j : Fin 4, RepT t (uPerm j) :=
  exists_repT_of_mem (tabs := Native.uTabs) (n := 4) rfl repT_uPerm ht

private theorem uPerm_basis :
    ∀ (j : Fin 4) (i : Fin 12), CFSG.Monster.Code.B i ∘ ⇑(uPerm j) ∈ CFSG.Monster.Code.C := by
  decide +kernel

private theorem uPerm_basis' :
    ∀ (j : Fin 4) (i : Fin 12), CFSG.Monster.Code.B i ∘ ⇑(uPerm j)⁻¹ ∈ CFSG.Monster.Code.C := by
  decide +kernel

theorem uPerm_mem (j : Fin 4) : uPerm j ∈ CFSG.ASVolI.ChH.M24g :=
  mem_AutPerm_of_basis (uPerm_basis j) (uPerm_basis' j)

end CFSG.Quasithin.H13.AS91.M24G
