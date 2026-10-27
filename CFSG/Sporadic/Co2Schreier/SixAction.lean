module

public import CFSG.Sporadic.Co2Schreier.Six

public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Sporadic.Co2Schreier

open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Certificates.Native CFSG.Sporadic.Co2Cert
  CFSG.Sporadic.SmallF2 CFSG.Sporadic.SmallF2.Native
open scoped Matrix

@[expose] def linC :
    locC →* (Co2V ≃ₗ[ZMod 2] Co2V) := linP.comp (Subgroup.inclusion locC_le_P)

theorem linC_vec
    (c : locC) (i : Fin 2300) :
    linC c (co2Vec i) = co2Vec ((c : Equiv.Perm (Fin 2300)) i) :=
  linP_vec _ i

@[expose] def sixN (i : ℕ) : Matrix (Fin 6) (Fin 6) (ZMod 2) :=
  Matrix.of fun j k => if ((witRec.wLocal.sixRows.getD i []).getD j 0).testBit k then 1 else 0

theorem colBits_testBit (rows : List ℕ) (k j : ℕ) :
    (colBits rows k).testBit j = (decide (j < 6) && (rows.getD j 0).testBit k) := by
  rw [colBits]
  exact foldl_or_testBit (fun j => (rows.getD j 0).testBit k) 6 j

theorem toVecD_sixImage
    {t : Array ℕ} {g : Equiv.Perm (Fin 2300)} (ht : Rep 2300 t g)
    (k : Fin 6) :
    toVecD 22 (sixImage t k) = co2Vec (g ⟨sixIdx k, sixFacts.idx_lt k k.2⟩) +
      co2Vec (g ⟨sixAnchorIdx, sixFacts.anchor_lt⟩) := by
  rw [sixImage, toVecD_xor, ht.apply (sixFacts.idx_lt k k.2), ht.apply sixFacts.anchor_lt,
    ← co2Vec_eq_toVecD (Fin.isLt _), ← co2Vec_eq_toVecD (Fin.isLt _)]

theorem linC_sixVec
    (c : locC) (k : Fin 6) :
    linC c (sixVec k) = co2Vec ((c : Equiv.Perm (Fin 2300)) ⟨sixIdx k, sixFacts.idx_lt k k.2⟩) +
      co2Vec ((c : Equiv.Perm (Fin 2300)) ⟨sixAnchorIdx, sixFacts.anchor_lt⟩) := by
  have e1 : sixVec k = co2Vec (⟨sixIdx k, sixFacts.idx_lt k k.2⟩ : Fin 2300) +
      co2Vec (⟨sixAnchorIdx, sixFacts.anchor_lt⟩ : Fin 2300) := rfl
  rw [e1, map_add, linC_vec, linC_vec]

theorem getD_one_mem_of {H : Subgroup (Equiv.Perm (Fin 2300))} {l : List (Equiv.Perm (Fin 2300))}
    (hl : ∀ g ∈ l, g ∈ H) (i : ℕ) : l.getD i 1 ∈ H := by
  rw [List.getD_eq_getElem?_getD]
  cases h : l[i]? with
  | none => exact H.one_mem
  | some g => exact hl g (List.mem_of_getElem? h)

@[expose] def cGen (i : ℕ) : locC := ⟨cTuple.getD i 1, getD_one_mem_of (fun _ hg =>
  Subgroup.subset_closure hg) i⟩

@[expose] def qGen (m : ℕ) : locC := ⟨qTuple.getD m 1, getD_one_mem_of qTuple_mem_C m⟩

theorem coe_cGen (i : ℕ) : ((cGen i : locC) : Equiv.Perm (Fin 2300)) = cTuple.getD i 1 := rfl

theorem coe_qGen (m : ℕ) : ((qGen m : locC) : Equiv.Perm (Fin 2300)) = qTuple.getD m 1 := rfl

theorem linC_cGen_sixVec
    {i : ℕ} (hi : i < 2) (k : Fin 6) :
    linC (cGen i) (sixVec k) = ∑ j : Fin 6, sixN i j k • sixVec j := by
  rw [linC_sixVec, coe_cGen, ← toVecD_sixImage (repTuple_c.rep (by rw [cTuple_length]; exact hi)) k,
    sixFacts.imgC i hi k k.2, ← sum_sixVec]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [colBits_testBit, sixN, Matrix.of_apply]
  simp only [j.2, decide_true, Bool.true_and]
  split_ifs <;> simp

theorem linC_qGen_sixVec
    {m : ℕ} (hm : m < 8) (k : Fin 6) :
    linC (qGen m) (sixVec k) = sixVec k := by
  rw [linC_sixVec, coe_qGen, ← toVecD_sixImage (repTuple_q.rep (by rw [qTuple_length]; exact hm)) k,
    sixFacts.imgQ m hm k k.2, sixVec_eq]

theorem coe_linP_mul
    (a b : co2P) : (linP (a * b) : Co2V →ₗ[ZMod 2] Co2V) =
    (linP a : Co2V →ₗ[ZMod 2] Co2V) ∘ₗ (linP b : Co2V →ₗ[ZMod 2] Co2V) := by
  rw [map_mul]
  rfl

theorem coe_linP_one :
    (linP 1 : Co2V →ₗ[ZMod 2] Co2V) = LinearMap.id := by
  rw [map_one]
  rfl

@[expose] def stabV6 :
    Subgroup co2P where
  carrier := {g | V6.map (linP g : Co2V →ₗ[ZMod 2] Co2V) = V6}
  mul_mem' := fun {a b} ha hb => by
    simp only [Set.mem_ofPred_eq] at ha hb ⊢
    rw [coe_linP_mul, Submodule.map_comp, hb, ha]
  one_mem' := by
    simp only [Set.mem_ofPred_eq]
    rw [coe_linP_one, Submodule.map_id]
  inv_mem' := fun {a} ha => by
    simp only [Set.mem_ofPred_eq] at ha ⊢
    conv_lhs => rw [← ha]
    rw [← Submodule.map_comp, ← coe_linP_mul, inv_mul_cancel, coe_linP_one, Submodule.map_id]

theorem map_V6_of_images {f : Co2V ≃ₗ[ZMod 2] Co2V} (hf : ∀ k, f (sixVec k) ∈ V6) :
    V6.map (f : Co2V →ₗ[ZMod 2] Co2V) = V6 := by
  have hle : V6.map (f : Co2V →ₗ[ZMod 2] Co2V) ≤ V6 := by
    rw [V6, Submodule.map_span, Submodule.span_le]
    rintro _ ⟨_, ⟨k, rfl⟩, rfl⟩
    exact hf k
  refine Submodule.eq_of_le_of_finrank_eq hle ?_
  exact LinearEquiv.finrank_map_eq f V6

theorem sum_mem_V6 (c : Fin 6 → ZMod 2) : ∑ j, c j • sixVec j ∈ V6 :=
  Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)

theorem cGen_mem_stab
    {i : ℕ} (hi : i < 2) :
    (⟨cTuple.getD i 1, locC_le_P (cGen i).2⟩ : co2P) ∈ stabV6 := by
  refine map_V6_of_images fun k => ?_
  have h := linC_cGen_sixVec hi k
  change linP _ (sixVec k) = _ at h
  rw [show (⟨cTuple.getD i 1, locC_le_P (cGen i).2⟩ : co2P) = Subgroup.inclusion locC_le_P (cGen i)
    from rfl]
  rw [h]
  exact sum_mem_V6 _

theorem locC_le_stab :
    locC ≤ stabV6.map co2P.subtype := by
  rw [locC, Subgroup.closure_le]
  intro g hg
  obtain ⟨i, hi, rfl⟩ := (mem_iff_exists_getD (d := 1)).1 hg
  rw [cTuple_length] at hi
  exact ⟨_, cGen_mem_stab hi, rfl⟩

theorem V6_map
    (c : locC) : V6.map (linC c : Co2V →ₗ[ZMod 2] Co2V) = V6 := by
  obtain ⟨g, hg, hgc⟩ := locC_le_stab c.2
  have : g = Subgroup.inclusion locC_le_P c := Subtype.ext hgc
  rw [this] at hg
  exact hg

@[expose] def sixAction :
    locC →* (V6 ≃ₗ[ZMod 2] V6) where
  toFun c := ((linC c).submoduleMap V6).trans (LinearEquiv.ofEq _ _ (V6_map c))
  map_one' := by
    refine LinearEquiv.ext fun x => Subtype.ext ?_
    simp
  map_mul' a b := by
    refine LinearEquiv.ext fun x => Subtype.ext ?_
    simp [map_mul]

theorem sixAction_apply
    (c : locC) (x : V6) : ((sixAction c x : V6) : Co2V) = linC c x := rfl

theorem sixAction_cGen_basis
    {i : ℕ} (hi : i < 2) (k : Fin 6) :
    sixAction (cGen i) (sixBasis k) = ∑ j : Fin 6, sixN i j k • sixBasis j := by
  apply Subtype.ext
  rw [sixAction_apply, sixBasis_apply, linC_cGen_sixVec hi, Submodule.coe_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Submodule.coe_smul, sixBasis_apply]

theorem toMatrix_sixAction_cGen
    {i : ℕ} (hi : i < 2) :
    LinearMap.toMatrix sixBasis sixBasis (sixAction (cGen i) : V6 →ₗ[ZMod 2] V6) = sixN i := by
  ext j k
  rw [LinearMap.toMatrix_apply, LinearEquiv.coe_coe, sixAction_cGen_basis hi,
    Module.Basis.repr_sum_self]

theorem sixAction_qGen
    {m : ℕ} (hm : m < 8) : sixAction (qGen m) = 1 := by
  refine LinearEquiv.toLinearMap_injective (sixBasis.ext fun k => Subtype.ext ?_)
  rw [LinearEquiv.coe_coe, sixAction_apply, sixBasis_apply, linC_qGen_sixVec hm,
    ← sixBasis_apply]
  rfl

end CFSG.Sporadic.Co2Schreier
