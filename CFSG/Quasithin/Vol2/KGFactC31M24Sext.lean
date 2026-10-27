module

public import CFSG.Quasithin.Vol2.KGFactC31M24Nor
public import CFSG.Quasithin.Vol2.KGFactC31FrameSound

public section

namespace CFSG.Quasithin.KGC31.M24

open CFSG.Blueprint CFSG.Certificates CFSG.Sporadic.Th CFSG.Sporadic.Th.Native
  CFSG.Sporadic.Schreier CFSG.Sporadic.Schreier.Native CFSG.Quasithin.KGC31.Native
  CFSG.Quasithin.KGC31 _root_.Certificates

@[expose] def tetB : Fin 6 → Finset (Fin 24) := fun i =>
  Finset.univ.filter fun p => p.val ∈ tets.getD i []

theorem mem_tetB (i : Fin 6) (p : Fin 24) : p ∈ tetB i ↔ p.val ∈ tets.getD i [] := by
  simp [tetB]

theorem tetB_inj : Function.Injective tetB := by decide

theorem card_tetB : ∀ i, (tetB i).card = 4 := by decide

theorem tets_lt : ∀ T ∈ tets, ∀ p ∈ T, p < 24 := by decide

theorem tets_length : tets.length = 6 := rfl

@[expose] def Lb : Subgroup G₀ := (blockStab tetB tetB_inj).comap NativeSporadic.M24.subtype

theorem y5_mem_Lb : y5 ∈ Lb :=
  mem_blockStab_of_blocksOK tetB_inj tets_length mem_tetB card_tetB (rep_elt y5W) c_blocks_y5

theorem nj_mem_Lb : ∀ w ∈ njW, elt w ∈ Lb := fun w hw =>
  mem_blockStab_of_blocksOK tetB_inj tets_length mem_tetB card_tetB (rep_elt w)
    (List.all_eq_true.mp c_blocks_nj _ (List.mem_map.mpr ⟨w, hw, rfl⟩))

theorem Ls_le_Lb : Ls ≤ Lb :=
  conjGenOf_le fun w hw => Lb.mul_mem (Lb.mul_mem (nj_mem_Lb w hw) y5_mem_Lb)
    (Lb.inv_mem (nj_mem_Lb w hw))

@[expose] noncomputable def lsAct : ↥Ls →* Equiv.Perm (Fin 6) :=
  (blockAct tetB_inj).comp ((NativeSporadic.M24.subtype.comp Ls.subtype).codRestrict _
    fun x => Ls_le_Lb x.2)

theorem lsAct_eq_one_iff (x : ↥Ls) :
    lsAct x = 1 ↔ ∀ i, (tetB i).image ((x : G₀) : Equiv.Perm (Fin 24)) = tetB i := by
  rw [lsAct, MonoidHom.comp_apply, blockAct_eq_one_iff]
  rfl

theorem card_ker_lsAct : Nat.card lsAct.ker = 192 := by
  classical
  have h := card_subtype_eq_countProducts hn24 lsChain c_ls_check
    (P := fun g => ∀ i, (tetB i).image g = tetB i)
    fun T g hT => fixesBlocks_iff tets_length mem_tetB tets_lt hT
  rw [c_ker_ls] at h
  have hQ : lsChain.originalSubgroup = Ls.map NativeSporadic.M24.subtype := by
    rw [lsChain, certificate_originalSubgroup, Ls, map_conjGenOf]
    rfl
  rw [hQ] at h
  rw [← h]
  refine (Nat.card_congr ?_).trans (Nat.card_congr (Equiv.subtypeEquiv
    (Ls.equivMapOfInjective _ Subtype.val_injective).toEquiv fun x => Iff.rfl))
  exact
    { toFun := fun x => ⟨x.1, (lsAct_eq_one_iff x.1).mp x.2⟩
      invFun := fun x => ⟨x.1, (lsAct_eq_one_iff x.1).mpr x.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }

@[expose] def tetFix : Subgroup (Equiv.Perm (Fin 24)) where
  carrier := {g | ∀ i, (tetB i).image g = tetB i}
  one_mem' := fun i => by simp
  mul_mem' := fun {a b} ha hb i => by
    rw [Equiv.Perm.coe_mul, ← Finset.image_image, hb i, ha i]
  inv_mem' := fun {a} ha i => by
    conv_lhs => rw [← ha i]
    rw [Finset.image_image]
    simp

theorem s_le_ker_lsAct : (eSub basis_s).subgroupOf Ls ≤ lsAct.ker := by
  intro x hx
  rw [Subgroup.mem_subgroupOf] at hx
  rw [MonoidHom.mem_ker, lsAct_eq_one_iff]
  have hle : (eSub basis_s).map NativeSporadic.M24.subtype ≤ tetFix := by
    rw [eSub_eq_closure, MonoidHom.map_closure, Subgroup.closure_le]
    rintro _ ⟨_, ⟨i, rfl⟩, rfl⟩
    obtain ⟨b, hb, hbi⟩ : ∃ b ∈ sT, Rep 24 b ((vS i : G₀) : Equiv.Perm (Fin 24)) :=
      exists_tab_of_mem forall₂_s (List.mem_ofFn.mpr ⟨i, rfl⟩)
    exact (fixesBlocks_iff tets_length mem_tetB tets_lt hbi).mp
      (List.all_eq_true.mp c_fix_s b hb)
  exact hle ⟨x, hx, rfl⟩

theorem card_alt6 : Nat.card (alternatingGroup (Fin 6)) = 360 := by
  rw [Nat.card_eq_fintype_card, card_alternatingGroup]
  simp [Nat.factorial]

theorem ls_alt_data (hperf : ⁅Ls, Ls⁆ = Ls) :
    ∃ ψ : ↥Ls →* ↥(alternatingGroup (Fin 6)), Function.Surjective ψ ∧ Nat.card ψ.ker = 192 ∧
      (eSub basis_s).subgroupOf Ls ≤ ψ.ker := by
  have hcommK : commutator ↥Ls = ⊤ := by
    apply Subgroup.map_injective Ls.subtype_injective
    rw [commutator_def, Subgroup.map_commutator, ← MonoidHom.range_eq_map,
      Subgroup.range_subtype, hperf]
  have hsign : ∀ x, Equiv.Perm.sign (lsAct x) = 1 := by
    intro x
    have h1 : x ∈ (Equiv.Perm.sign.comp lsAct).ker := by
      have := Abelianization.commutator_subset_ker (Equiv.Perm.sign.comp lsAct)
      rw [hcommK] at this
      exact this (Subgroup.mem_top x)
    exact h1
  let ψ : ↥Ls →* ↥(alternatingGroup (Fin 6)) :=
    lsAct.codRestrict _ fun x => Equiv.Perm.mem_alternatingGroup.mpr (hsign x)
  have hker : ψ.ker = lsAct.ker := MonoidHom.ker_codRestrict _ _ _
  refine ⟨ψ, ?_, by rw [hker, card_ker_lsAct], hker ▸ s_le_ker_lsAct⟩
  rw [← MonoidHom.range_eq_top]
  apply Subgroup.eq_top_of_card_eq
  have h1 := Subgroup.card_mul_index ψ.ker
  rw [Subgroup.index_ker, hker, card_ker_lsAct, card_Ls] at h1
  rw [card_alt6]
  omega

end CFSG.Quasithin.KGC31.M24

end
