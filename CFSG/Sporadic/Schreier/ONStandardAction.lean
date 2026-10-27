module

public import CFSG.Sporadic.Schreier.ONSmallGens
public import CFSG.Sporadic.Schreier.ONRestrict
public import CFSG.Sporadic.Schreier.ONCheckSmallAux
public import CFSG.LocalAnalysis.ComponentClassification.PSL3FourExactModel
public import CFSG.GroupActions.PermutationCentralizerOrbitBound
import all CFSG.LocalAnalysis.ComponentClassification.PSL3FourActionData

public noncomputable section

namespace CFSG.ONSchreier

open Matrix CFSG.ONSchreier.Native CFSG.Certificates
open CFSG.ComponentClassification.PSL3Four (F4 vIdx vIdx_lt vecOf vecOf_ne_zero vIdx_vecOf
  vIdx_mulVec_mulVec vIdx_smul vecOf_of_lt TabRep)
open scoped Pointwise

abbrev scalars3 : Subgroup (SpecialLinearGroup (Fin 3) F4) :=
  CFSG.LocalAnalysis.ComponentInitial.LinearFlag.scalars 3 F4

@[expose] def pt21Fun (A : GL (Fin 3) F4) (i : Fin 21) : Fin 21 :=
  ⟨vIdx ((A : Matrix (Fin 3) (Fin 3) F4) *ᵥ vecOf ⟨i.val, by omega⟩), vIdx_lt _⟩

theorem rhoFun_lt (A : GL (Fin 3) F4) {i : ℕ} (hi : i < 21) :
    (CFSG.ComponentClassification.PSL3Four.rhoFun A ⟨i, by omega⟩ : ℕ) =
      vIdx ((A : Matrix (Fin 3) (Fin 3) F4) *ᵥ vecOf ⟨i, by omega⟩) := by
  simp only [CFSG.ComponentClassification.PSL3Four.rhoFun, hi, ↓reduceIte]

theorem pt21Fun_mul (A B : GL (Fin 3) F4) (i : Fin 21) :
    pt21Fun A (pt21Fun B i) = pt21Fun (A * B) i := by
  have h := congrArg Fin.val
    (CFSG.ComponentClassification.PSL3Four.rhoFun_rhoFun A B ⟨i.val, by omega⟩)
  have hB : CFSG.ComponentClassification.PSL3Four.rhoFun B ⟨i.val, by omega⟩ =
      ⟨(pt21Fun B i).val, by have := (pt21Fun B i).isLt; omega⟩ := Fin.ext (rhoFun_lt B i.isLt)
  rw [hB, rhoFun_lt A (pt21Fun B i).isLt, rhoFun_lt (A * B) i.isLt] at h
  exact Fin.ext h

theorem pt21Fun_one (i : Fin 21) : pt21Fun 1 i = i := by
  apply Fin.ext
  show vIdx (((1 : GL (Fin 3) F4) : Matrix (Fin 3) (Fin 3) F4) *ᵥ vecOf ⟨i.val, by omega⟩) = i.val
  rw [Units.val_one, one_mulVec, vIdx_vecOf]
  exact Nat.mod_eq_of_lt i.isLt

@[expose] def pt21Hom : GL (Fin 3) F4 →* Equiv.Perm (Fin 21) where
  toFun A :=
    { toFun := pt21Fun A
      invFun := pt21Fun A⁻¹
      left_inv := fun i => by rw [pt21Fun_mul, inv_mul_cancel, pt21Fun_one]
      right_inv := fun i => by rw [pt21Fun_mul, mul_inv_cancel, pt21Fun_one] }
  map_one' := Equiv.ext pt21Fun_one
  map_mul' A B := Equiv.ext fun i => (pt21Fun_mul A B i).symm

@[expose] def sl21 : SpecialLinearGroup (Fin 3) F4 →* Equiv.Perm (Fin 21) :=
  pt21Hom.comp SpecialLinearGroup.toGL

theorem sl21_scalar {A : SpecialLinearGroup (Fin 3) F4} (hA : A ∈ scalars3) :
    sl21 A = 1 := by
  obtain ⟨c, -, hAc⟩ := CFSG.LocalAnalysis.ComponentInitial.LinearFlag.mem_scalars.1 hA
  refine Equiv.ext fun i => Fin.ext ?_
  show vIdx (((SpecialLinearGroup.toGL A : GL (Fin 3) F4) : Matrix (Fin 3) (Fin 3) F4) *ᵥ
    vecOf ⟨i.val, by omega⟩) = i.val
  rw [show ((SpecialLinearGroup.toGL A : GL (Fin 3) F4) : Matrix (Fin 3) (Fin 3) F4) =
    (A : Matrix (Fin 3) (Fin 3) F4) from rfl, hAc,
    CFSG.ComponentClassification.PSL3Four.scalar_mulVec, vIdx_smul c.ne_zero, vIdx_vecOf]
  exact Nat.mod_eq_of_lt i.isLt

theorem scalars_le_ker_sl21 : scalars3 ≤ sl21.ker :=
  fun _ hA => sl21_scalar hA

theorem onElems_length : onElems.length = 12 := rfl

@[expose] def elemAt (j : ℕ) : SpecialLinearGroup (Fin 3) F4 := onElems.getD j 1

theorem psl21_gens : ∀ j : Fin 12, ∀ i : Fin 21,
    (Data.PSL21Chain.generators[j.val]!)[i.val]! = (sl21 (elemAt j) i : ℕ) := by
  decide +kernel

theorem psl21_size :
    Data.PSL21Chain.generators.size = 12 := fano_cert.2.2.2.2.1

theorem psl120_size :
    Data.PSL120Chain.generators.size = 12 := fano_cert.2.2.2.1

theorem prep_psl21 {j : ℕ} (hj : j < 12) :
    PRep 21 Data.PSL21Chain.generators[j]! (sl21 (elemAt j)) :=
  fun i => psl21_gens ⟨j, hj⟩ i

theorem sl21_elem
    {j : ℕ} (hj : j < 12) :
    sl21 (elemAt j) = permOfArr 21 Data.PSL21Chain.generators[j]! :=
  (prep_psl21 hj).unique (prep_smallGen small_chain_certs.2.2.2.1 j (by rw [psl21_size]; exact hj))

theorem onElems_set : {g | g ∈ onElems} = elemAt '' {j | j < 12} := by
  ext g
  simp only [Set.mem_ofPred_eq, Set.mem_image]
  constructor
  · intro hg
    obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hg
    exact ⟨j, by rw [onElems_length] at hj; exact hj, by rw [elemAt, List.getD_eq_getElem]⟩
  · rintro ⟨j, hj, rfl⟩
    rw [elemAt, List.getD_eq_getElem _ _ (by rw [onElems_length]; exact hj)]
    exact List.getElem_mem _

theorem onU_eq : onU = Subgroup.closure (elemAt '' {j | j < 12}) := by
  rw [onU, onElems_set]

theorem psl21_eq_map :
    onPSL21Chain.originalSubgroup = onU.map sl21 := by
  rw [onPSL21Chain, smallChain_sub, onU_eq, MonoidHom.map_closure, ← Set.image_comp, psl21_size]
  congr 1
  ext g
  simp only [Set.mem_image, Set.mem_ofPred_eq, Function.comp_apply]
  constructor
  · rintro ⟨j, hj, rfl⟩
    exact ⟨j, hj, sl21_elem hj⟩
  · rintro ⟨j, hj, rfl⟩
    exact ⟨j, hj, (sl21_elem hj).symm⟩

theorem card_range_mul_ker {G H : Type*} [Group G] [Group H] (f : G →* H) :
    Nat.card G = Nat.card f.range * Nat.card f.ker := by
  rw [Subgroup.card_eq_card_quotient_mul_card_subgroup f.ker,
    Nat.card_congr (QuotientGroup.quotientKerEquivRange f).toEquiv]

theorem card_le_of_scalars_le_ker {H : Type*} [Group H]
    (f : SpecialLinearGroup (Fin 3) F4 →* H) (hf : scalars3 ≤ f.ker) :
    Nat.card f.range ≤ 20160 := by
  have h := card_range_mul_ker f
  rw [CFSG.ComponentClassification.PSL3Four.card_SL] at h
  have h3 : Nat.card scalars3 ≤ Nat.card f.ker := Subgroup.card_le_of_le hf
  rw [CFSG.ComponentClassification.PSL3Four.card_scalars] at h3
  nlinarith

theorem sl21_range :
    sl21.range = onPSL21Chain.originalSubgroup := by
  have hle : onPSL21Chain.originalSubgroup ≤ sl21.range := by
    rw [psl21_eq_map, MonoidHom.range_eq_map]
    exact Subgroup.map_mono le_top
  exact (Subgroup.eq_of_le_of_card_ge hle (by
    rw [card_onPSL21]; exact card_le_of_scalars_le_ker sl21 scalars_le_ker_sl21)).symm

theorem mem_insertSorted (x y : ℕ) (l : List ℕ) : y ∈ insertSorted x l ↔ y = x ∨ y ∈ l := by
  induction l with
  | nil => simp [insertSorted]
  | cons a l ih =>
    unfold insertSorted
    split_ifs
    · simp
    · simp only [List.mem_cons, ih]
      tauto

theorem mem_foldl_insertSorted (g : Array ℕ) (y : ℕ) :
    ∀ (l acc : List ℕ), y ∈ l.foldl (fun acc p => insertSorted g[p]! acc) acc ↔
      y ∈ acc ∨ ∃ p ∈ l, g[p]! = y
  | [], acc => by simp
  | p :: l, acc => by
    rw [List.foldl_cons, mem_foldl_insertSorted g y l, mem_insertSorted]
    simp only [List.mem_cons, exists_eq_or_imp]
    constructor
    · rintro ((h | h) | ⟨q, hq, h⟩)
      · exact Or.inr (Or.inl h.symm)
      · exact Or.inl h
      · exact Or.inr (Or.inr ⟨q, hq, h⟩)
    · rintro (h | h | ⟨q, hq, h⟩)
      · exact Or.inl (Or.inr h)
      · exact Or.inl (Or.inl h.symm)
      · exact Or.inr ⟨q, hq, h⟩

theorem mem_sortedImage (g b : Array ℕ) (y : ℕ) :
    y ∈ sortedImage g b ↔ ∃ p ∈ b.toList, g[p]! = y := by
  rw [sortedImage, mem_foldl_insertSorted]
  simp

@[expose] def finOf (b : Array ℕ) : Finset (Fin 21) := (b.toList.map pt21).toFinset

theorem pt21_val {x : ℕ} (hx : x < 21) : ((pt21 x : Fin 21) : ℕ) = x := Nat.mod_eq_of_lt hx

theorem image_finOf {g b : Array ℕ} {σ : Equiv.Perm (Fin 21)} (hg : PRep 21 g σ)
    (hb : ∀ x ∈ b.toList, x < 21) :
    (finOf b).image σ = ((sortedImage g b).map pt21).toFinset := by
  ext y
  simp only [finOf, Finset.mem_image, List.mem_toFinset, List.mem_map, mem_sortedImage]
  constructor
  · rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩
    refine ⟨g[x]!, ⟨x, hx, rfl⟩, Fin.ext ?_⟩
    have := hg (pt21 x)
    rw [pt21_val (hb x hx)] at this
    rw [this]
    exact pt21_val (σ (pt21 x)).isLt
  · rintro ⟨z, ⟨x, hx, rfl⟩, rfl⟩
    refine ⟨pt21 x, ⟨x, hx, rfl⟩, Fin.ext ?_⟩
    have := hg (pt21 x)
    rw [pt21_val (hb x hx)] at this
    rw [← this, pt21_val]
    rw [this]
    exact (σ (pt21 x)).isLt

theorem fano_size : Data.targetFanoBlocks.size = 120 := fano_cert.1

theorem onFanoBlocks_length : onFanoBlocks.length = 120 := by
  simp [onFanoBlocks, fano_size]

theorem onFanoBlocks_get {i : ℕ} (hi : i < onFanoBlocks.length) :
    onFanoBlocks[i] = finOf Data.targetFanoBlocks[i]! := by
  have hi' : i < Data.targetFanoBlocks.size := by simpa [onFanoBlocks] using hi
  have e := List.getElem_of_eq (show onFanoBlocks = Data.targetFanoBlocks.toList.map
    fun b => (b.toList.map pt21).toFinset from rfl) hi
  rw [e, List.getElem_map, Array.getElem_toList, finOf, getElem!_pos _ i hi']

theorem block_facts {i : ℕ} (hi : i < 120) :
    Data.targetFanoBlocks[i]!.size = 7 ∧ sortedOK Data.targetFanoBlocks[i]! = true ∧
      ∀ x ∈ Data.targetFanoBlocks[i]!.toList, x < 21 := by
  have := allBelowN_spec fano_cert.2.1 hi
  simp only [Bool.and_eq_true, beq_iff_eq] at this
  obtain ⟨⟨h1, h2⟩, h3⟩ := this
  refine ⟨h1, h2, fun x hx => ?_⟩
  rw [Array.all_eq_true] at h3
  obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hx
  have := h3 k (by simpa using hk)
  simpa using this

theorem sortedLT_of_sortedOK {b : Array ℕ} (h : sortedOK b = true) : b.toList.SortedLT := by
  rw [List.sortedLT_iff_isChain, List.isChain_iff_getElem]
  intro k hk
  have hk' : k < b.size := by simp at hk; omega
  have := allBelowN_spec h hk'
  simp only [Bool.or_eq_true, beq_iff_eq, decide_eq_true_eq] at this
  rcases this with h1 | h1
  · simp at hk; omega
  · simp only [Array.getElem_toList]
    rwa [getElem!_pos b k hk', getElem!_pos b (k + 1) (by simp at hk; omega)] at h1

theorem finOf_inj {i k : ℕ} (hi : i < 120) (hk : k < 120)
    (h : finOf Data.targetFanoBlocks[i]! = finOf Data.targetFanoBlocks[k]!) : i = k := by
  have hmem : ∀ x, x ∈ Data.targetFanoBlocks[i]!.toList ↔ x ∈ Data.targetFanoBlocks[k]!.toList := by
    intro x
    constructor
    · intro hx
      have hx21 := (block_facts hi).2.2 x hx
      have : pt21 x ∈ finOf Data.targetFanoBlocks[k]! := by
        rw [← h, finOf, List.mem_toFinset]; exact List.mem_map_of_mem hx
      rw [finOf, List.mem_toFinset, List.mem_map] at this
      obtain ⟨y, hy, hxy⟩ := this
      have := congrArg Fin.val hxy
      rw [pt21_val ((block_facts hk).2.2 y hy), pt21_val hx21] at this
      rwa [← this]
    · intro hx
      have hx21 := (block_facts hk).2.2 x hx
      have : pt21 x ∈ finOf Data.targetFanoBlocks[i]! := by
        rw [h, finOf, List.mem_toFinset]; exact List.mem_map_of_mem hx
      rw [finOf, List.mem_toFinset, List.mem_map] at this
      obtain ⟨y, hy, hxy⟩ := this
      have := congrArg Fin.val hxy
      rw [pt21_val ((block_facts hi).2.2 y hy), pt21_val hx21] at this
      rwa [← this]
  have heq := List.SortedLT.eq_of_mem_iff (sortedLT_of_sortedOK (block_facts hi).2.1)
    (sortedLT_of_sortedOK (block_facts hk).2.1) hmem
  by_contra hne
  have := allBelowN_spec (allBelowN_spec fano_cert.2.2.1 hi) hk
  simp only [Bool.or_eq_true, beq_iff_eq, bne_iff_ne, ne_eq] at this
  rcases this with h1 | h1
  · exact hne h1
  · exact h1 heq

theorem onFanoBlocks_nodup : onFanoBlocks.Nodup := by
  rw [List.nodup_iff_injective_get]
  intro a b hab
  simp only [List.get_eq_getElem] at hab
  rw [onFanoBlocks_get, onFanoBlocks_get] at hab
  have ha : a.val < 120 := lt_of_lt_of_eq a.isLt onFanoBlocks_length
  have hb : b.val < 120 := lt_of_lt_of_eq b.isLt onFanoBlocks_length
  exact Fin.ext (finOf_inj ha hb hab)

theorem psl21_block
    {j i : ℕ} (hj : j < 12) (hi : i < 120) :
    (Data.PSL120Chain.generators[j]!)[i]! < 120 ∧
      (finOf Data.targetFanoBlocks[i]!).image (permOfArr 21 Data.PSL21Chain.generators[j]!) =
        finOf Data.targetFanoBlocks[(Data.PSL120Chain.generators[j]!)[i]!]! := by
  have := allBelowN_spec (allBelowN_spec fano_cert.2.2.2.2.2 hj) hi
  simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at this
  obtain ⟨hlt, heq⟩ := this
  refine ⟨hlt, ?_⟩
  rw [image_finOf (prep_smallGen small_chain_certs.2.2.2.1 j (by rw [psl21_size]; exact hj))
    (block_facts hi).2.2, heq, finOf]

theorem smul_finset_eq_image (σ : Equiv.Perm (Fin 21)) (F : Finset (Fin 21)) :
    σ • F = F.image σ := by
  rw [Finset.smul_finset_def]
  rfl

theorem psl21_preserve :
    ∀ σ ∈ onPSL21Chain.originalSubgroup, ∀ F ∈ onFanoBlocks,
    σ • F ∈ onFanoBlocks := by
  rw [onPSL21Chain, smallChain_sub, psl21_size]
  apply listInvariant
  rintro _ ⟨j, hj, rfl⟩ F hF
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hF
  have hi' : i < 120 := by rwa [onFanoBlocks_length] at hi
  obtain ⟨hlt, heq⟩ := psl21_block hj hi'
  rw [smul_finset_eq_image, onFanoBlocks_get, heq, ← onFanoBlocks_get (by
    rw [onFanoBlocks_length]; exact hlt)]
  exact List.getElem_mem _

@[expose] def psi21 :
    onPSL21Chain.originalSubgroup →* Equiv.Perm (Fin 120) :=
  (finCongr onFanoBlocks_length).permCongrHom.toMonoidHom.comp
    (listRestrict onFanoBlocks onPSL21Chain.originalSubgroup psl21_preserve onFanoBlocks_nodup)

theorem psi21_spec
    (σ : onPSL21Chain.originalSubgroup) (k : Fin 120) :
    onFanoBlocks[(psi21 σ k : ℕ)]'(by rw [onFanoBlocks_length]; exact (psi21 σ k).isLt) =
      (onFanoBlocks[(k : ℕ)]'(by rw [onFanoBlocks_length]; exact k.isLt)).image σ := by
  have := get_listRestrict onFanoBlocks onPSL21Chain.originalSubgroup psl21_preserve
    onFanoBlocks_nodup σ (Fin.cast onFanoBlocks_length.symm k)
  rw [smul_finset_eq_image] at this
  exact this

theorem sl21_mem
    (A : SpecialLinearGroup (Fin 3) F4) : sl21 A ∈ onPSL21Chain.originalSubgroup := by
  rw [← sl21_range]
  exact ⟨A, rfl⟩

@[expose] def psi :
    SpecialLinearGroup (Fin 3) F4 →* Equiv.Perm (Fin 120) :=
  psi21.comp (sl21.codRestrict _ sl21_mem)

theorem psi_spec
    (A : SpecialLinearGroup (Fin 3) F4) (k : Fin 120) :
    onFanoBlocks[(psi A k : ℕ)]'(by rw [onFanoBlocks_length]; exact (psi A k).isLt) =
      (onFanoBlocks[(k : ℕ)]'(by rw [onFanoBlocks_length]; exact k.isLt)).image (sl21 A) :=
  psi21_spec _ k

theorem psi_scalar :
    scalars3 ≤ psi.ker := by
  intro A hA
  rw [MonoidHom.mem_ker, psi, MonoidHom.comp_apply]
  have : sl21.codRestrict _ sl21_mem A = 1 := Subtype.ext (sl21_scalar hA)
  rw [this, map_one]

theorem psi_elem
    {j : ℕ} (hj : j < 12) :
    psi (elemAt j) = permOfArr 120 Data.PSL120Chain.generators[j]! := by
  have hrep : PRep 120 Data.PSL120Chain.generators[j]! (psi (elemAt j)) := by
    intro k
    obtain ⟨hlt, heq⟩ := psl21_block hj k.isLt
    have hs := psi_spec (elemAt j) k
    rw [onFanoBlocks_get, onFanoBlocks_get, sl21_elem hj] at hs
    have hk : (psi (elemAt j) k : ℕ) < 120 := (psi (elemAt j) k).isLt
    exact (finOf_inj hk hlt (hs.trans heq)).symm
  exact hrep.unique (prep_smallGen small_chain_certs.2.2.2.2.1 j (by rw [psl120_size]; exact hj))

theorem onX_eq_map :
    onX = onU.map psi := by
  rw [onX, onPSL120Chain, smallChain_sub, onU_eq, MonoidHom.map_closure, ← Set.image_comp,
    psl120_size]
  congr 1
  ext g
  simp only [Set.mem_image, Set.mem_ofPred_eq, Function.comp_apply]
  constructor
  · rintro ⟨j, hj, rfl⟩
    exact ⟨j, hj, psi_elem hj⟩
  · rintro ⟨j, hj, rfl⟩
    exact ⟨j, hj, (psi_elem hj).symm⟩

theorem psi_range :
    psi.range = onX := by
  have hle : onX ≤ psi.range := by
    rw [onX_eq_map, MonoidHom.range_eq_map]
    exact Subgroup.map_mono le_top
  exact (Subgroup.eq_of_le_of_card_ge hle (by
    rw [card_onX]; exact card_le_of_scalars_le_ker psi psi_scalar)).symm

theorem psi_ker :
    psi.ker = scalars3 := by
  have h := card_range_mul_ker psi
  rw [CFSG.ComponentClassification.PSL3Four.card_SL, psi_range, card_onX] at h
  exact (Subgroup.eq_of_le_of_card_ge psi_scalar (by
    rw [CFSG.ComponentClassification.PSL3Four.card_scalars]; omega)).symm

@[expose] def thetaX :
    CFSG.LocalAnalysis.ComponentInitial.LinearFlag.projectiveSL 3 F4 ≃* onX :=
  (QuotientGroup.quotientMulEquivOfEq psi_ker.symm).trans
    ((QuotientGroup.quotientKerEquivRange psi).trans (MulEquiv.subgroupCongr psi_range))

theorem thetaX_proj
    (A : SpecialLinearGroup (Fin 3) F4) :
    (thetaX (CFSG.LocalAnalysis.ComponentInitial.LinearFlag.proj 3 F4 A) :
      Equiv.Perm (Fin 120)) = psi A := rfl

theorem onX_classicalModel :
    CFSG.Assembly.LowTwoRank.StatedClassicalModel onX .PSL 3 2 2 :=
  ⟨CFSG.ComponentClassification.PSL3Four.admissible, F4, inferInstance, inferInstance,
    CFSG.ComponentClassification.PSL3Four.natCard_F4',
    ⟨thetaX.symm.trans CFSG.ComponentClassification.PSL3Four.projectiveSLEquivStated⟩⟩

theorem psl120_arrays :
    CArrays onPSL120Chain Data.PSL120Chain.generators.size
      Data.PSL120Chain.strongGenerators Data.PSL120Chain.base
      (Array.replicate Data.PSL120Chain.generators.size [] ++ Data.PSL120Chain.derivations) ∧
    fullChainOK 120 Data.PSL120Chain.generators.size Data.PSL120Chain.strongGenerators
      Data.PSL120Chain.base
      (Array.replicate Data.PSL120Chain.generators.size [] ++ Data.PSL120Chain.derivations) 2 =
        true :=
  smallChain_arrays (by norm_num) Data.PSL120Chain _ _ small_chain_certs.2.2.2.2.1

theorem psl120_valid : ValidSchreier onPSL120Chain ∧
    (List.finRange onPSL120Chain.baseCount).map (fun i => Nat.card (onPSL120Chain.orbitPoints i)) =
      [120, 21, 8] := by
  obtain ⟨hA, hfull⟩ := psl120_arrays
  obtain ⟨hV, horb⟩ := validSchreier_of_fullChainOK hA (by norm_num) hfull
  exact ⟨hV, (orbit_sizes_eq hA.base_size horb).trans small_chain_certs.2.2.2.2.2.2.2.2.2⟩

theorem psl120_baseCount : onPSL120Chain.baseCount = 3 := by
  simp [onPSL120Chain, smallChain, RawSchreierDatum.ofArrays, smallBase]
  decide

theorem psl120_base0 :
    onPSL120Chain.base.get ⟨0, by rw [psl120_baseCount]; norm_num⟩ = 0 := by
  have e : onPSL120Chain.base.get ⟨0, by rw [psl120_baseCount]; norm_num⟩ =
      (smallBase 120 (by norm_num) Data.PSL120Chain)[0]'(by decide) :=
    ofArrays_base_get (hb := by decide) _
  rw [e]
  decide

theorem psl120_orbit0 :
    Nat.card (onPSL120Chain.orbitPoints ⟨0, by rw [psl120_baseCount]; norm_num⟩) = 120 := by
  have h := List.getElem_of_eq psl120_valid.2 (i := 0) (by simp [psl120_baseCount])
  simpa using h

theorem psl120_level0 : onPSL120Chain.levelSubgroup 0 = onX := by
  rw [onPSL120Chain.levelSubgroup_eq_pointwise_stabilizer psl120_valid.1 0 (Nat.zero_le _),
    List.take_zero]
  simp [onX]

theorem onX_orbit :
    MulAction.orbit onX (0 : Fin 120) = Set.univ := by
  have h := onPSL120Chain.orbitPoints_eq_orbit ⟨0, by rw [psl120_baseCount]; norm_num⟩
  rw [psl120_base0] at h
  simp only at h
  rw [psl120_level0] at h
  have hc := psl120_orbit0
  rw [h] at hc
  apply Set.eq_of_subset_of_ncard_le (Set.subset_univ _) _ (Set.toFinite _)
  rw [Set.ncard_univ, Nat.card_fin, ← Nat.card_coe_set_eq, hc]

theorem onX_transitive (i j : Fin 120) : ∃ x ∈ onX, x i = j := by
  have hi : i ∈ MulAction.orbit onX (0 : Fin 120) := by rw [onX_orbit]; trivial
  have hj : j ∈ MulAction.orbit onX (0 : Fin 120) := by rw [onX_orbit]; trivial
  obtain ⟨⟨x, hx⟩, rfl⟩ := hi
  obtain ⟨⟨y, hy⟩, rfl⟩ := hj
  refine ⟨y * x⁻¹, mul_mem hy (inv_mem hx), ?_⟩
  simp [Equiv.Perm.smul_def]

theorem psl120_level1_fixed
    {b : Fin 120}
    (hb : ∀ e ∈ onPSL120Chain.levelSubgroup 1, e b = b) : b = 0 := by
  obtain ⟨hA, hfull⟩ := psl120_arrays
  have hF := chainFacts hfull
  have hgen : ∀ j ∈ levIdx Data.PSL120Chain.strongGenerators Data.PSL120Chain.base 1,
      (Data.PSL120Chain.strongGenerators[j]!)[(b : ℕ)]! = b := by
    intro j hj
    have hjs := CArrays.levIdx_lt hj
    have hmem : strongAt onPSL120Chain j ∈ onPSL120Chain.levelGenerators 1 := by
      rw [hA.levelGenerators_eq hF (by rw [psl120_baseCount]; norm_num)]
      exact List.mem_map_of_mem hj
    have := hb _ (Subgroup.subset_closure hmem)
    rw [(hA.prep_strong hF j hjs) b, this]
  have hfix := psl120_fixed_cert
  have hb' : (b : ℕ) ∈ fixedSet 120 ((levIdx Data.PSL120Chain.strongGenerators
      Data.PSL120Chain.base 1).map fun j => Data.PSL120Chain.strongGenerators[j]!).toArray := by
    rw [fixedSet, List.mem_filter, List.mem_range]
    refine ⟨b.isLt, ?_⟩
    rw [Array.all_eq_true]
    intro k hk
    simp only [List.size_toArray, List.length_map] at hk
    simp only [List.getElem_toArray, List.getElem_map, beq_iff_eq]
    exact hgen _ (List.getElem_mem _)
  rw [hfix, List.mem_singleton] at hb'
  exact Fin.ext hb'

theorem onX_centralizer :
    Subgroup.centralizer (onX : Set (Equiv.Perm (Fin 120))) = ⊥ := by
  have h1 : onPSL120Chain.levelSubgroup 1 ≤ onX :=
    onPSL120Chain.levelSubgroup_le_originalSubgroup_of_point psl120_valid.1.validPointSchreier 1
  have hfix0 : ∀ e ∈ onPSL120Chain.levelSubgroup 1, e 0 = 0 := by
    intro e he
    have := onPSL120Chain.levelSubgroup_fixes_base_index 1 e he
      ⟨0, by rw [psl120_baseCount]; norm_num⟩ (by norm_num)
    rwa [psl120_base0] at this
  have hb := (CFSG.GroupActions.permutation_centralizer_orbit_fixed_bound onX
    (r := 1) (fun _ => (0 : Fin 120)) (fun x => ⟨0, by rw [onX_orbit]; trivial⟩)
    (fun i j _ => Subsingleton.elim i j) (fun _ => onPSL120Chain.levelSubgroup 1) (fun _ => h1)
    (fun _ => hfix0)).2.2
  have hsub :
      (CFSG.GroupActions.orbitFixedSet onX (onPSL120Chain.levelSubgroup 1) 0).Subsingleton :=
    fun x hx y hy => (psl120_level1_fixed hx.2).trans (psl120_level1_fixed hy.2).symm
  have hle :
      Nat.card (CFSG.GroupActions.orbitFixedSet onX (onPSL120Chain.levelSubgroup 1) 0) ≤ 1 := by
    rw [Nat.card_coe_set_eq]
    exact Set.ncard_le_one_iff_subsingleton.2 hsub
  simp only [Finset.univ_unique, Finset.prod_singleton] at hb
  exact Subgroup.eq_bot_of_card_le _ (hb.trans hle)

@[expose] def vecCode (v : CFSG.ComponentClassification.PSL3Four.Vec) : ℕ :=
  16 * (v 0).code.val + 4 * (v 1).code.val + (v 2).code.val

theorem targetVecs_eq : onTargetVecs = CFSG.ComponentClassification.PSL3Four.V := by
  decide +kernel

theorem targetVecs_sorted : onTargetVecs.Pairwise fun v w => vecCode v < vecCode w := by
  rw [targetVecs_eq]
  decide +kernel

theorem fano0_binary :
    onFanoBlocks[0]'(by rw [onFanoBlocks_length]; norm_num) =
    Finset.univ.filter fun i : Fin 21 =>
      ∀ k : Fin 3, ((CFSG.ComponentClassification.PSL3Four.V.getD i.val 0) k).code.val < 2 := by
  rw [onFanoBlocks_get]
  decide +kernel

theorem fano_orbit :
    {F | F ∈ onFanoBlocks} = {F | ∃ A ∈ onU,
    F = (onFanoBlocks[0]'(by rw [onFanoBlocks_length]; norm_num)).image (sl21 A)} := by
  ext F
  simp only [Set.mem_ofPred_eq]
  constructor
  · intro hF
    obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hF
    have hk' : k < 120 := by rwa [onFanoBlocks_length] at hk
    obtain ⟨x, hx, hx0⟩ := onX_transitive 0 ⟨k, hk'⟩
    rw [onX_eq_map] at hx
    obtain ⟨A, hA, rfl⟩ := hx
    refine ⟨A, hA, ?_⟩
    have := psi_spec A 0
    simp only [hx0, Fin.val_zero] at this
    exact this
  · rintro ⟨A, -, rfl⟩
    have := psi_spec A 0
    simp only [Fin.val_zero] at this
    rw [← this]
    exact List.getElem_mem _


theorem at_on_standard_psl34_action :
    onTargetVecs = CFSG.ComponentClassification.PSL3Four.V ∧ onTargetVecs.length = 21 ∧
      onTargetVecs.Nodup ∧
      (∀ v, v ∈ onTargetVecs ↔ v ≠ 0 ∧ CFSG.ComponentClassification.PSL3Four.normalize v = v) ∧
      (∀ u, u ≠ 0 → CFSG.ComponentClassification.PSL3Four.normalize u ∈ onTargetVecs ∧
        CFSG.ComponentClassification.PSL3Four.normalize u =
          (CFSG.ComponentClassification.PSL3Four.lead u)⁻¹ • u) ∧
      onTargetVecs.Pairwise (fun v w => vecCode v < vecCode w) ∧
      onFanoBlocks.length = 120 ∧ onFanoBlocks.Nodup ∧
      onFanoBlocks[0]'(by rw [onFanoBlocks_length]; norm_num) = Finset.univ.filter
        (fun i : Fin 21 =>
          ∀ k : Fin 3, ((CFSG.ComponentClassification.PSL3Four.V.getD i.val 0) k).code.val < 2) ∧
      {F | F ∈ onFanoBlocks} = {F | ∃ A ∈ onU,
        F = (onFanoBlocks[0]'(by rw [onFanoBlocks_length]; norm_num)).image (sl21 A)} ∧
      (∀ (A : SpecialLinearGroup (Fin 3) F4) (k : Fin 120),
        onFanoBlocks[(psi A k : ℕ)]'(by rw [onFanoBlocks_length]; exact (psi A k).isLt) =
          (onFanoBlocks[(k : ℕ)]'(by rw [onFanoBlocks_length]; exact k.isLt)).image (sl21 A)) ∧
      psi.ker = scalars3 ∧ psi.range = onX ∧
      (∃ θ : CFSG.LocalAnalysis.ComponentInitial.LinearFlag.projectiveSL 3 F4 ≃* onX,
        ∀ A, (θ (CFSG.LocalAnalysis.ComponentInitial.LinearFlag.proj 3 F4 A) :
          Equiv.Perm (Fin 120)) = psi A) ∧
      Nat.card onX = 20160 ∧ CFSG.Assembly.LowTwoRank.StatedClassicalModel onX .PSL 3 2 2 ∧
      (∀ i j : Fin 120, ∃ x ∈ onX, x i = j) ∧
      Subgroup.centralizer (onX : Set (Equiv.Perm (Fin 120))) = ⊥ := by
  have hV := CFSG.ComponentClassification.PSL3Four.action_data
  have hs := targetVecs_sorted
  rw [targetVecs_eq] at hs ⊢
  exact ⟨rfl, hV.2.2.1, hV.2.2.2.1, hV.2.2.2.2.1,
    fun u hu => ⟨(hV.2.2.2.2.2.1 u hu).2, (hV.2.2.2.2.2.1 u hu).1⟩, hs, onFanoBlocks_length,
    onFanoBlocks_nodup, fano0_binary, fano_orbit, psi_spec, psi_ker, psi_range,
    ⟨thetaX, thetaX_proj⟩, card_onX, onX_classicalModel, onX_transitive, onX_centralizer⟩

end CFSG.ONSchreier
