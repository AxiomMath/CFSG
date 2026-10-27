module

public import CFSG.RankThree.PartTwo.Sec21.HeringRootsU58Model

public section

namespace CFSG.RankThree.PartTwo.Sec21.RootsU58

open Matrix CFSG.RankThree.PartTwo.KFacts.KS21 CFSG.RankThree.PartTwo.KFacts.KS21.U58
open CFSG.RankThree.PartTwo.Sec21.TablesU58 CFSG.RankThree.PartTwo.Sec21.Tables
open CFSG.Assembly (IsElemAbelian)
open CFSG.Assembly.LowTwoRank

theorem mem_idOutsideSU {c : Set (Fin 5)} {x : SUI} :
    x ∈ idOutsideSU c ↔ IsIdOutside c (mU x) := Iff.rfl

theorem idOutsideSU_mono {c c' : Set (Fin 5)} (h : c ⊆ c') : idOutsideSU c ≤ idOutsideSU c' := by
  intro x hx
  rw [mem_idOutsideSU] at hx ⊢
  intro i j hij
  apply hx i j
  rcases hij with hi | hj
  · exact Or.inl (fun hc => hi (h hc))
  · exact Or.inr (fun hc => hj (h hc))

theorem isQuasisimple_idOutsideSU (F : Finset (Fin 5)) (hF : 2 ≤ F.card) :
    CFSG.IsQuasisimple (idOutsideSU (F : Set (Fin 5))) := by
  have hinj := (F.orderEmbOfFin rfl).injective
  have hrange : idOutsideSU (F : Set (Fin 5)) =
      (embedSU hinj card_K (by omega : 1 ≤ F.card) (by norm_num : 1 ≤ 5)).range := by
    ext x
    rw [mem_range_embedSU_iff, Finset.range_orderEmbOfFin]
    exact Iff.rfl
  rw [hrange]
  exact CFSG.LocalCores.isQuasisimple_of_mulEquiv
    (MonoidHom.ofInjective (embedSU_injective hinj card_K _ _)) (isQuasisimple_SU hF)

theorem isQuasisimple_idOutsideSU_fibre {v : Fin 4 → ZMod 3} {κ : ZMod 3}
    (hbig : ∃ i j : Fin 5, i ≠ j ∧ ext3 v i = κ ∧ ext3 v j = κ) :
    CFSG.IsQuasisimple (idOutsideSU {i : Fin 5 | ext3 v i = κ}) := by
  classical
  obtain ⟨i, j, hij, hi, hj⟩ := hbig
  have hS : {i : Fin 5 | ext3 v i = κ} =
      ((Finset.univ.filter fun k => ext3 v k = κ : Finset (Fin 5)) : Set (Fin 5)) := by
    ext k
    simp
  have hcard : 2 ≤ (Finset.univ.filter fun k => ext3 v k = κ : Finset (Fin 5)).card := by
    have hsub : ({i, j} : Finset (Fin 5)) ⊆ Finset.univ.filter fun k => ext3 v k = κ := by
      intro k hk
      simp only [Finset.mem_insert, Finset.mem_singleton] at hk
      rcases hk with rfl | rfl
      · simp [hi]
      · simp [hj]
    calc 2 = ({i, j} : Finset (Fin 5)).card := (Finset.card_pair hij).symm
      _ ≤ _ := Finset.card_le_card hsub
  rw [hS]
  exact isQuasisimple_idOutsideSU _ hcard

theorem isBlockDiag_of_mem_centralizer_δ {v : Fin 4 → ZMod 3} {g : SUI}
    (hg : g ∈ Subgroup.centralizer ({δ (Multiplicative.ofAdd v)} : Set SUI)) :
    IsBlockDiag (ext3 v) (mU g) := by
  have h := isBlockDiag_of_mem_centralizer (u := ι3v v) hg
  simp only [ext9_ι3v] at h
  exact IsBlockDiag.of_comp (f := ι3) ι3_injective h

theorem mem_centralizer_of_isBlockDiag_δ {v : Fin 4 → ZMod 3} {g : SUI}
    (hg : IsBlockDiag (ext3 v) (mU g)) :
    g ∈ Subgroup.centralizer ({δ (Multiplicative.ofAdd v)} : Set SUI) :=
  mem_centralizer_of_isBlockDiag (u := ι3v v) (by
    simp only [ext9_ι3v]
    exact hg.comp ι3)

theorem idOutsideSU_le_cv (v : Fin 4 → ZMod 3) (κ : ZMod 3) :
    idOutsideSU {i : Fin 5 | ext3 v i = κ} ≤
      Subgroup.centralizer ({δ (Multiplicative.ofAdd v)} : Set SUI) := fun _ hx =>
  mem_centralizer_of_isBlockDiag_δ (IsIdOutside.isBlockDiag hx)

theorem cv_le_normalizer (v : Fin 4 → ZMod 3) (κ : ZMod 3) :
    Subgroup.centralizer ({δ (Multiplicative.ofAdd v)} : Set SUI) ≤
      Subgroup.normalizer (idOutsideSU {i : Fin 5 | ext3 v i = κ} : Set SUI) :=
  centralizer_le_normalizer_idOutsideSU (u := ι3v v) fun i j e => by
    simp only [ext9_ι3v] at e
    have h := ι3_injective e
    simp only [Set.mem_setOf_eq, h]

section BlockParts

@[expose] noncomputable def blkM (T : Set (Fin 5)) (A : Matrix (Fin 5) (Fin 5) K) :
    Matrix (Fin 5) (Fin 5) K :=
  Matrix.of fun i j => by
    classical
    exact if i ∈ T then A i j else (1 : Matrix (Fin 5) (Fin 5) K) i j

theorem blkM_apply_mem {T : Set (Fin 5)} {A : Matrix (Fin 5) (Fin 5) K} {i : Fin 5} (h : i ∈ T)
    (j : Fin 5) : blkM T A i j = A i j := by
  simp [blkM, h]

theorem blkM_apply_not_mem {T : Set (Fin 5)} {A : Matrix (Fin 5) (Fin 5) K} {i : Fin 5}
    (h : i ∉ T) (j : Fin 5) : blkM T A i j = (1 : Matrix (Fin 5) (Fin 5) K) i j := by
  simp [blkM, h]

theorem blkM_univ (A : Matrix (Fin 5) (Fin 5) K) : blkM Set.univ A = A := by
  ext i j
  exact blkM_apply_mem (Set.mem_univ i) j

theorem blkM_one (T : Set (Fin 5)) : blkM T (1 : Matrix (Fin 5) (Fin 5) K) = 1 := by
  ext i j
  by_cases hi : i ∈ T
  · rw [blkM_apply_mem hi]
  · rw [blkM_apply_not_mem hi]

theorem blkM_eq_one_of_subsingleton {T : Set (Fin 5)} {A : Matrix (Fin 5) (Fin 5) K}
    (hA : ∀ i k, i ∈ T → k ∉ T → A i k = 0) (hT : ∀ i ∈ T, ∀ j ∈ T, i = j)
    (hdiag : ∀ k ∈ T, A k k = 1) :
    blkM T A = 1 := by
  ext i j
  by_cases hi : i ∈ T
  · rw [blkM_apply_mem hi j]
    by_cases hj : j ∈ T
    · have hij : j = i := hT j hj i hi
      rw [hij, hdiag i hi, Matrix.one_apply_eq]
    · rw [hA i j hi hj, Matrix.one_apply_ne (fun (h : i = j) => hj (h ▸ hi))]
  · rw [blkM_apply_not_mem hi j]

@[expose] def SatBlock (U : Set (Fin 5)) (A : Matrix (Fin 5) (Fin 5) K) : Prop :=
  ∀ i k, i ∈ U → k ∉ U → A i k = 0

theorem satBlock_union {U W : Set (Fin 5)} {A : Matrix (Fin 5) (Fin 5) K}
    (hU : SatBlock U A) (hW : SatBlock W A) : SatBlock (U ∪ W) A := by
  intro i k hi hk
  rcases (Set.mem_union _ _ _).mp hi with hi' | hi'
  · exact hU i k hi' (fun h => hk (Set.mem_union_left W h))
  · exact hW i k hi' (fun h => hk (Set.mem_union_right U h))

theorem satBlock_fibre {v : Fin 4 → ZMod 3} {A : Matrix (Fin 5) (Fin 5) K}
    (hb : IsBlockDiag (ext3 v) A) (κ : ZMod 3) : SatBlock {i : Fin 5 | ext3 v i = κ} A := by
  intro i k hi hk
  apply hb i k
  intro h
  apply hk
  show ext3 v k = κ
  rw [← h]
  exact hi

theorem satBlock_fibre_compl {v : Fin 4 → ZMod 3} {A : Matrix (Fin 5) (Fin 5) K}
    (hb : IsBlockDiag (ext3 v) A) (κ : ZMod 3) : SatBlock {i : Fin 5 | ext3 v i = κ}ᶜ A := by
  intro i k hi hk
  apply hb i k
  intro h
  have hk' : ext3 v k = κ := not_not.mp hk
  have hi' : ¬ext3 v i = κ := hi
  exact hi' (h.trans hk')

theorem blkM_mul_of_sat {U : Set (Fin 5)} {A B : Matrix (Fin 5) (Fin 5) K}
    (hA : SatBlock U A) : blkM U (A * B) = blkM U A * blkM U B := by
  ext i j
  by_cases hi : i ∈ U
  · rw [blkM_apply_mem hi, Matrix.mul_apply, Matrix.mul_apply]
    apply Finset.sum_congr rfl
    intro k _
    rw [blkM_apply_mem hi]
    by_cases hk : k ∈ U
    · rw [blkM_apply_mem hk]
    · rw [hA i k hi hk]
      simp
  · rw [blkM_apply_not_mem hi]
    simp [Matrix.mul_apply, Matrix.one_apply, blkM_apply_not_mem hi]

theorem isIdOutside_blkM {U : Set (Fin 5)} {A : Matrix (Fin 5) (Fin 5) K} (hA : SatBlock U A) :
    IsIdOutside U (blkM U A) := by
  intro a b hab
  by_cases ha : a ∈ U
  · have hb : b ∉ U := by
      rcases hab with h | h
      · exact absurd ha h
      · exact h
    have hne : a ≠ b := fun h => hb (h ▸ ha)
    rw [blkM_apply_mem ha b, hA a b ha hb, Matrix.one_apply_ne hne]
  · rw [blkM_apply_not_mem ha b]

theorem blkM_mul_disjoint {U W : Set (Fin 5)} {A : Matrix (Fin 5) (Fin 5) K}
    (hA : SatBlock U A) (hd : ∀ i, i ∈ U → i ∉ W) :
    blkM U A * blkM W A = blkM (U ∪ W) A := by
  ext i j
  rw [Matrix.mul_apply]
  by_cases hiU : i ∈ U
  · rw [blkM_apply_mem (Set.mem_union_left W hiU) j]
    calc ∑ k, blkM U A i k * blkM W A k j
        = ∑ k, A i k * (1 : Matrix (Fin 5) (Fin 5) K) k j := by
          apply Finset.sum_congr rfl
          intro k _
          rw [blkM_apply_mem hiU]
          by_cases hkW : k ∈ W
          · rw [hA i k hiU (fun hkU => hd k hkU hkW)]
            simp
          · rw [blkM_apply_not_mem hkW]
      _ = A i j := by rw [← Matrix.mul_apply, Matrix.mul_one]
  · have hrow : ∑ k, blkM U A i k * blkM W A k j = ∑ k, (1 : Matrix (Fin 5) (Fin 5) K) i k *
        blkM W A k j := by
      apply Finset.sum_congr rfl
      intro k _
      rw [blkM_apply_not_mem hiU]
    by_cases hiW : i ∈ W
    · rw [blkM_apply_mem (Set.mem_union_right U hiW) j, hrow, ← Matrix.mul_apply, Matrix.one_mul,
        blkM_apply_mem hiW j]
    · have hiUW : i ∉ U ∪ W := fun h => ((Set.mem_union _ _ _).mp h).elim hiU hiW
      rw [blkM_apply_not_mem hiUW j, hrow, ← Matrix.mul_apply, Matrix.one_mul,
        blkM_apply_not_mem hiW j]

theorem blkM_fibre_prod {v : Fin 4 → ZMod 3} {A : Matrix (Fin 5) (Fin 5) K}
    (hb : IsBlockDiag (ext3 v) A) :
    blkM {i : Fin 5 | ext3 v i = 0} A * blkM {i : Fin 5 | ext3 v i = 1} A *
      blkM {i : Fin 5 | ext3 v i = 2} A = A := by
  have hd01 : ∀ i, i ∈ {i : Fin 5 | ext3 v i = 0} → i ∉ {i : Fin 5 | ext3 v i = 1} := by
    intro i h0 h1
    exact absurd ((show ext3 v i = 0 from h0).symm.trans (show ext3 v i = 1 from h1)) (by decide)
  have hd2 : ∀ i, i ∈ {i : Fin 5 | ext3 v i = 0} ∪ {i : Fin 5 | ext3 v i = 1} →
      i ∉ {i : Fin 5 | ext3 v i = 2} := by
    intro i h01 h2
    rcases (Set.mem_union _ _ _).mp h01 with h0 | h1
    · exact absurd ((show ext3 v i = 0 from h0).symm.trans (show ext3 v i = 2 from h2)) (by decide)
    · exact absurd ((show ext3 v i = 1 from h1).symm.trans (show ext3 v i = 2 from h2)) (by decide)
  have e1 := blkM_mul_disjoint (satBlock_fibre hb 0) hd01
  have e2 := blkM_mul_disjoint (satBlock_union (satBlock_fibre hb 0) (satBlock_fibre hb 1)) hd2
  have hU : ({i : Fin 5 | ext3 v i = 0} ∪ {i : Fin 5 | ext3 v i = 1}) ∪
      {i : Fin 5 | ext3 v i = 2} = Set.univ := by
    apply Set.eq_univ_of_forall
    intro i
    rcases (by decide : ∀ x : ZMod 3, x = 0 ∨ x = 1 ∨ x = 2) (ext3 v i) with h | h | h <;>
      simp [h]
  rw [e1, e2, hU, blkM_univ]

theorem blkM_map_transpose {T : Set (Fin 5)} {A : Matrix (Fin 5) (Fin 5) K}
    (hT : SatBlock T A) (hT' : SatBlock Tᶜ A) :
    ((blkM T A).map (iterateFrobenius K 2 3))ᵀ =
      blkM T ((A.map (iterateFrobenius K 2 3))ᵀ) := by
  ext i j
  simp only [Matrix.transpose_apply, Matrix.map_apply]
  by_cases hi : i ∈ T <;> by_cases hj : j ∈ T
  · rw [blkM_apply_mem hj, blkM_apply_mem hi, Matrix.transpose_apply, Matrix.map_apply]
  · have hne : j ≠ i := fun h => hj (h ▸ hi)
    rw [blkM_apply_not_mem hj, blkM_apply_mem hi, Matrix.transpose_apply, Matrix.map_apply,
      hT' j i hj (not_not.mpr hi), Matrix.one_apply_ne hne, map_zero]
  · have hne : i ≠ j := fun h => hi (h ▸ hj)
    rw [blkM_apply_mem hj, blkM_apply_not_mem hi, hT j i hj hi, Matrix.one_apply_ne hne,
      map_zero]
  · rw [blkM_apply_not_mem hj, blkM_apply_not_mem hi]
    by_cases hij : i = j
    · subst hij
      simp
    · rw [Matrix.one_apply_ne hij, Matrix.one_apply_ne (Ne.symm hij), map_zero]

theorem unitary_blkM {v : Fin 4 → ZMod 3} {A : Matrix (Fin 5) (Fin 5) K}
    (hb : IsBlockDiag (ext3 v) A) (hu : (A.map (iterateFrobenius K 2 3))ᵀ * A = 1) (κ : ZMod 3) :
    ((blkM {i : Fin 5 | ext3 v i = κ} A).map (iterateFrobenius K 2 3))ᵀ *
      blkM {i : Fin 5 | ext3 v i = κ} A = 1 := by
  have hT : SatBlock {i : Fin 5 | ext3 v i = κ} A := satBlock_fibre hb κ
  have hT' : SatBlock {i : Fin 5 | ext3 v i = κ}ᶜ A := satBlock_fibre_compl hb κ
  have hbar : SatBlock {i : Fin 5 | ext3 v i = κ} ((A.map (iterateFrobenius K 2 3))ᵀ) := by
    intro i k hi hk
    rw [Matrix.transpose_apply, Matrix.map_apply, hT' k i hk (not_not.mpr hi), map_zero]
  rw [blkM_map_transpose hT hT', ← blkM_mul_of_sat hbar, hu, blkM_one]

end BlockParts

section Join

abbrev BigFibre (v : Fin 4 → ZMod 3) : Type :=
  {κ : ZMod 3 // ∃ i j : Fin 5, i ≠ j ∧ ext3 v i = κ ∧ ext3 v j = κ}

theorem exists_blk {v : Fin 4 → ZMod 3} {Q : Type*} [Group Q]
    (hQ : Group.IsPerfect Q) (f : Q →* SUI)
    (hf : ∀ q, f q ∈ Subgroup.centralizer ({δ (Multiplicative.ofAdd v)} : Set SUI))
    (κ : ZMod 3) (q : Q) :
    ∃ b : SUI, mU b = blkM {i : Fin 5 | ext3 v i = κ} (mU (f q)) := by
  have hdet : Matrix.det (blkM {i : Fin 5 | ext3 v i = κ} (mU (f q))) = 1 := by
    let Fdet : Q →* K :=
      { toFun := fun x => Matrix.det (blkM {i : Fin 5 | ext3 v i = κ} (mU (f x)))
        map_one' := by
          simp only [map_one, mU_one, blkM_one, Matrix.det_one]
        map_mul' := fun x y => by
          simp only [map_mul, mU_mul]
          rw [blkM_mul_of_sat (satBlock_fibre (isBlockDiag_of_mem_centralizer_δ (hf x)) κ),
            Matrix.det_mul] }
    exact perfect_hom_trivial hQ Fdet q
  have hunit := unitary_blkM (isBlockDiag_of_mem_centralizer_δ (hf q))
    ((mem_SUI_iff _).mp (f q).2).2 κ
  have hinv := mul_eq_one_comm.mp hunit
  exact ⟨⟨⟨blkM {i : Fin 5 | ext3 v i = κ} (mU (f q)),
      ((blkM {i : Fin 5 | ext3 v i = κ} (mU (f q))).map (iterateFrobenius K 2 3))ᵀ, hinv, hunit⟩,
    (mem_SUI_iff _).mpr ⟨hdet, hunit⟩⟩, rfl⟩

theorem mem_iSup_fibre_of_perfect {v : Fin 4 → ZMod 3} {Q : Type*} [Group Q]
    (hQ : Group.IsPerfect Q) (f : Q →* SUI)
    (hf : ∀ q, f q ∈ Subgroup.centralizer ({δ (Multiplicative.ofAdd v)} : Set SUI)) (q : Q)
    (κ : ZMod 3) (b : SUI)
    (hb : mU b = blkM {i : Fin 5 | ext3 v i = κ} (mU (f q))) :
    b ∈ ⨆ κ' : BigFibre v, idOutsideSU {i : Fin 5 | ext3 v i = κ'.1} := by
  haveI : Group.IsPerfect Q := hQ
  have hPr : Group.IsPerfect f.range := Group.IsPerfect.range f
  have hSat := satBlock_fibre (isBlockDiag_of_mem_centralizer_δ (hf q)) κ
  by_cases hbig : ∃ i j : Fin 5, i ≠ j ∧ ext3 v i = κ ∧ ext3 v j = κ
  · refine Subgroup.mem_iSup_of_mem (⟨κ, hbig⟩ : BigFibre v) (mem_idOutsideSU.mpr ?_)
    rw [hb]
    exact isIdOutside_blkM hSat
  · have hT : ∀ i ∈ {i : Fin 5 | ext3 v i = κ}, ∀ j ∈ {i : Fin 5 | ext3 v i = κ}, i = j := by
      intro i hi j hj
      by_contra hne
      exact hbig ⟨i, j, hne, hi, hj⟩
    have hrow : ∀ k : Fin 5, ext3 v k = κ → ∀ g ∈ f.range, ∀ l : Fin 5, l ≠ k →
        mU g k l = 0 := by
      intro k hk g hg l hl
      obtain ⟨q', rfl⟩ := MonoidHom.mem_range.mp hg
      apply isBlockDiag_of_mem_centralizer_δ (hf q') k l
      intro hkl
      exact hl (hT k hk l (hkl.symm.trans hk)).symm
    have hd : ∀ k ∈ {i : Fin 5 | ext3 v i = κ}, mU (f q) k k = 1 :=
      fun k hk => diag_eq_one_of_perfect hPr k (hrow k hk) (f q) (MonoidHom.mem_range.mpr ⟨q, rfl⟩)
    have hone : b = 1 := by
      apply mU_injective
      rw [mU_one, hb]
      exact blkM_eq_one_of_subsingleton hSat hT hd
    rw [hone]
    exact one_mem _

theorem mem_iSup_big_of_perfect {v : Fin 4 → ZMod 3} {Q : Type*} [Group Q]
    (hQ : Group.IsPerfect Q) (f : Q →* SUI)
    (hf : ∀ q, f q ∈ Subgroup.centralizer ({δ (Multiplicative.ofAdd v)} : Set SUI)) (q : Q) :
    f q ∈ ⨆ κ : BigFibre v, idOutsideSU {i : Fin 5 | ext3 v i = κ.1} := by
  obtain ⟨b0, hb0⟩ := exists_blk hQ f hf 0 q
  obtain ⟨b1, hb1⟩ := exists_blk hQ f hf 1 q
  obtain ⟨b2, hb2⟩ := exists_blk hQ f hf 2 q
  have hprod : f q = b0 * b1 * b2 := by
    apply mU_injective
    rw [mU_mul, mU_mul, hb0, hb1, hb2]
    exact (blkM_fibre_prod (isBlockDiag_of_mem_centralizer_δ (hf q))).symm
  rw [hprod]
  exact mul_mem (mul_mem (mem_iSup_fibre_of_perfect hQ f hf q 0 b0 hb0)
    (mem_iSup_fibre_of_perfect hQ f hf q 1 b1 hb1)) (mem_iSup_fibre_of_perfect hQ f hf q 2 b2 hb2)

theorem blk_iSup_map (v : Fin 4 → ZMod 3) :
    (⨆ κ : BigFibre v, (idOutsideSU {i : Fin 5 | ext3 v i = κ.1}).subgroupOf
        (Subgroup.centralizer ({δ (Multiplicative.ofAdd v)} : Set SUI))).map
      (Subgroup.centralizer ({δ (Multiplicative.ofAdd v)} : Set SUI)).subtype =
    ⨆ κ : BigFibre v, idOutsideSU {i : Fin 5 | ext3 v i = κ.1} := by
  rw [Subgroup.map_iSup]
  refine iSup_congr fun κ => ?_
  rw [Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr (idOutsideSU_le_cv v κ.1)]

theorem perfect_le_iSup_sub {v : Fin 4 → ZMod 3}
    (P : Subgroup (Subgroup.centralizer ({δ (Multiplicative.ofAdd v)} : Set SUI)))
    (hP : Group.IsPerfect P) :
    P ≤ ⨆ κ : BigFibre v, (idOutsideSU {i : Fin 5 | ext3 v i = κ.1}).subgroupOf
        (Subgroup.centralizer ({δ (Multiplicative.ofAdd v)} : Set SUI)) := by
  intro g hg
  have hS := mem_iSup_big_of_perfect (Q := P) hP
    ((Subgroup.centralizer ({δ (Multiplicative.ofAdd v)} : Set SUI)).subtype.comp P.subtype)
    (fun x => x.1.2) ⟨g, hg⟩
  have hS' : (g : SUI) ∈ ⨆ κ : BigFibre v, idOutsideSU {i : Fin 5 | ext3 v i = κ.1} := hS
  rw [← blk_iSup_map v] at hS'
  obtain ⟨t, ht, htg⟩ := Subgroup.mem_map.mp hS'
  have htg' : t = g := by
    apply Subtype.ext
    exact htg
  rw [← htg']
  exact ht

theorem components_big (v : Fin 4 → ZMod 3) :
    {Y : Subgroup (Subgroup.centralizer ({δ (Multiplicative.ofAdd v)} : Set SUI)) |
        CFSG.IsComponent Y} =
      Set.range (fun κ : BigFibre v =>
        (idOutsideSU {i : Fin 5 | ext3 v i = κ.1}).subgroupOf
          (Subgroup.centralizer ({δ (Multiplicative.ofAdd v)} : Set SUI))) :=
  components_eq_range_of_finite _
    (fun κ => CFSG.LocalCores.isQuasisimple_of_mulEquiv
      (Subgroup.subgroupOfEquivOfLe (idOutsideSU_le_cv v κ.1)).symm
      (isQuasisimple_idOutsideSU_fibre κ.2))
    (fun κ => (Subgroup.normal_subgroupOf_iff_le_normalizer (idOutsideSU_le_cv v κ.1)).mpr
      (cv_le_normalizer v κ.1))
    (fun P hP => perfect_le_iSup_sub P hP)

end Join

end CFSG.RankThree.PartTwo.Sec21.RootsU58
