module

public import CFSG.LocalAnalysis.ComponentInitial.SymplecticHigherParabolicData
public import CFSG.LocalAnalysis.ComponentInitial.SymplecticHigherBruhat
public import CFSG.RankThree.PartTwo.Sec19.KF1923ParSp6Layer

public section

namespace CFSG.RankThree.PartTwo.Late.KFParSp6

open Matrix CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag
  CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher CFSG.LocalAnalysis.ComponentInitial

@[expose] def tauF (k : Fin 6) : Fin 3 ⊕ Fin 3 :=
  if h : k.val < 3 then Sum.inl ⟨k.val, h⟩ else Sum.inr ⟨5 - k.val, by omega⟩

@[expose] def tauInv (x : Fin 3 ⊕ Fin 3) : Fin 6 :=
  match x with
  | Sum.inl j => ⟨j.val, by have := j.isLt; omega⟩
  | Sum.inr j => ⟨5 - j.val, by have := j.isLt; omega⟩

@[expose] def tauEquiv : Fin 6 ≃ Fin 3 ⊕ Fin 3 where
  toFun := tauF
  invFun := tauInv
  left_inv := by decide
  right_inv := by decide

theorem tauEquiv_lt (k : Fin 6) (h : k.val < 3) : tauEquiv k = Sum.inl ⟨k.val, h⟩ := by
  simp [tauEquiv, tauF, h]

theorem tauEquiv_ge (k : Fin 6) (h : 3 ≤ k.val) :
    tauEquiv k = Sum.inr ⟨5 - k.val, by omega⟩ := by
  simp [tauEquiv, tauF, not_lt.2 h]

theorem tauEquiv_symm_inl (j : Fin 3) :
    tauEquiv ⟨j.val, by have := j.isLt; omega⟩ = Sum.inl j :=
  tauEquiv_lt _ _

theorem tauEquiv_symm_inr (j : Fin 3) :
    tauEquiv ⟨5 - j.val, by have := j.isLt; omega⟩ = Sum.inr j := by
  rw [tauEquiv_ge _ (by have := j.isLt; simp; omega)]
  congr 1
  apply Fin.ext
  have := j.isLt
  simp only
  omega

@[expose] def toM6 (g : Matrix.GeneralLinearGroup (Fin 3 ⊕ Fin 3) (ZMod 2)) :
    Matrix (Fin 6) (Fin 6) (ZMod 2) :=
  (g : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) (ZMod 2)).submatrix tauEquiv tauEquiv

@[expose] def toGL6 : Matrix.GeneralLinearGroup (Fin 3 ⊕ Fin 3) (ZMod 2) →*
    Matrix.GeneralLinearGroup (Fin 6) (ZMod 2) :=
  MonoidHom.mk' (fun g => Units.mk (toM6 g) (toM6 g⁻¹)
    (by
      unfold toM6
      rw [Matrix.submatrix_mul_equiv, ← Units.val_mul, mul_inv_cancel, Units.val_one,
        Matrix.submatrix_one_equiv])
    (by
      unfold toM6
      rw [Matrix.submatrix_mul_equiv, ← Units.val_mul, inv_mul_cancel, Units.val_one,
        Matrix.submatrix_one_equiv]))
    (fun g h => Units.ext (by
      show toM6 (g * h) = toM6 g * toM6 h
      unfold toM6
      rw [Units.val_mul, Matrix.submatrix_mul_equiv]))

theorem toGL6_injective : Function.Injective toGL6 := by
  intro g h hgh
  have h1 : toM6 g = toM6 h := congrArg Units.val hgh
  apply Units.ext
  ext i j
  have := congrFun (congrFun h1 (tauEquiv.symm i)) (tauEquiv.symm j)
  simpa [toM6] using this

theorem mem_flag_iff_tau (s : ℕ) (hs : s ≤ 6) (v : Fin 3 ⊕ Fin 3 → ZMod 2) :
    v ∈ flag 3 (ZMod 2) s ↔ ∀ k : Fin 6, s ≤ k.val → v (tauEquiv k) = 0 := by
  by_cases hs3 : s ≤ 3
  · rw [flag, if_pos hs3, mem_isoFlag]
    constructor
    · rintro ⟨h1, h2⟩ k hk
      by_cases hk3 : k.val < 3
      · rw [tauEquiv_lt k hk3]
        exact h2 ⟨k.val, hk3⟩ hk
      · rw [tauEquiv_ge k (not_lt.1 hk3)]
        exact h1 _
    · intro h
      refine ⟨fun j => ?_, fun j hj => ?_⟩
      · have h' := h ⟨5 - j.val, by have := j.isLt; omega⟩ (by have := j.isLt; simp; omega)
        rwa [tauEquiv_symm_inr] at h'
      · have h' := h ⟨j.val, by have := j.isLt; omega⟩ (by simpa using hj)
        rwa [tauEquiv_symm_inl] at h'
  · push_neg at hs3
    rw [mem_flag_of_lt hs3]
    constructor
    · intro h k hk
      have hk3 : 3 ≤ k.val := by omega
      rw [tauEquiv_ge k hk3]
      have hk5 := k.isLt
      exact h ⟨5 - k.val, by omega⟩ (show 5 - k.val < 2 * 3 - s by omega)
    · intro h j hj
      have hj3 := j.isLt
      have hjs : s ≤ 5 - j.val := by omega
      have h' := h ⟨5 - j.val, by omega⟩ (show s ≤ 5 - j.val from hjs)
      rwa [tauEquiv_symm_inr] at h'

theorem mulVec_mem_of_stab {W : Submodule (ZMod 2) (Fin 3 ⊕ Fin 3 → ZMod 2)}
    {g : StatedSp 3 (ZMod 2)} (hg : g ∈ stabilizer 3 (ZMod 2) W) {v : Fin 3 ⊕ Fin 3 → ZMod 2}
    (hv : v ∈ W) : ((g : Matrix.GeneralLinearGroup (Fin 3 ⊕ Fin 3) (ZMod 2)) :
      Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) (ZMod 2)) *ᵥ v ∈ W := by
  rw [mem_stabilizer] at hg
  have h := Submodule.mem_map_of_mem (f := mulVecLin ((g : Matrix.GeneralLinearGroup
    (Fin 3 ⊕ Fin 3) (ZMod 2)) : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) (ZMod 2))) hv
  rw [hg] at h
  exact h

theorem toM6_eq_zero_of_stab {g : StatedSp 3 (ZMod 2)} {s : ℕ} (hs : s ≤ 6)
    (hg : g ∈ stabilizer 3 (ZMod 2) (flag 3 (ZMod 2) s)) (i j : Fin 6) (hj : j.val < s)
    (hi : s ≤ i.val) : toM6 (g : Matrix.GeneralLinearGroup (Fin 3 ⊕ Fin 3) (ZMod 2)) i j = 0 := by
  have hv : Pi.single (tauEquiv j) (1 : ZMod 2) ∈ flag 3 (ZMod 2) s := by
    rw [mem_flag_iff_tau s hs]
    intro k hk
    rw [Pi.single_apply, if_neg]
    intro e
    have := tauEquiv.injective e
    subst this
    omega
  have hgv := mulVec_mem_of_stab hg hv
  rw [mem_flag_iff_tau s hs] at hgv
  have h := hgv i hi
  rw [Matrix.mulVec_single_one] at h
  simpa [toM6] using h

@[expose] def blkOf (S : Finset ℕ) (j : Fin 6) : ℕ := (S.filter (fun c => 0 < c ∧ c ≤ j.val)).card

theorem exists_cut_of_blkOf_lt (S : Finset ℕ) {i j : Fin 6} (h : blkOf S j < blkOf S i) :
    ∃ s ∈ S, j.val < s ∧ s ≤ i.val := by
  by_contra H
  push_neg at H
  have hsub : S.filter (fun c => 0 < c ∧ c ≤ i.val) ⊆ S.filter (fun c => 0 < c ∧ c ≤ j.val) := by
    intro c hc
    rw [Finset.mem_filter] at hc ⊢
    refine ⟨hc.1, hc.2.1, ?_⟩
    by_contra hcj
    have := H c hc.1 (by omega)
    omega
  have := Finset.card_le_card hsub
  unfold blkOf at h
  omega

theorem blockTri_of_stab (S : Finset ℕ) (hS : ∀ s ∈ S, s ≤ 6) {g : StatedSp 3 (ZMod 2)}
    (hg : ∀ s ∈ S, g ∈ stabilizer 3 (ZMod 2) (flag 3 (ZMod 2) s)) :
    BlockTri (blkOf S) (toM6 (g : Matrix.GeneralLinearGroup (Fin 3 ⊕ Fin 3) (ZMod 2))) := by
  unfold BlockTri
  intro i j hij
  obtain ⟨s, hs, hj, hi⟩ := exists_cut_of_blkOf_lt S hij
  exact toM6_eq_zero_of_stab (hS s hs) (hg s hs) i j hj hi

@[expose] abbrev stMat (g : StatedSp 3 (ZMod 2)) :
    Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) (ZMod 2) :=
  ((g : Matrix.GeneralLinearGroup (Fin 3 ⊕ Fin 3) (ZMod 2)) :
    Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) (ZMod 2))

theorem mem_stab_orth {W : Submodule (ZMod 2) (Fin 3 ⊕ Fin 3 → ZMod 2)} {g : StatedSp 3 (ZMod 2)}
    (hg : g ∈ stabilizer 3 (ZMod 2) W) :
    g ∈ stabilizer 3 (ZMod 2) ((pairedSympForm (ZMod 2) 3).orthogonal W) := by
  have key : ∀ h : StatedSp 3 (ZMod 2), h ∈ stabilizer 3 (ZMod 2) W →
      ∀ v ∈ (pairedSympForm (ZMod 2) 3).orthogonal W,
        stMat h *ᵥ v ∈ (pairedSympForm (ZMod 2) 3).orthogonal W := by
    intro h hh v hv
    rw [LinearMap.BilinForm.mem_orthogonal_iff] at hv ⊢
    intro w hw
    have hw' : stMat h⁻¹ *ᵥ w ∈ W := mulVec_mem_of_stab (Subgroup.inv_mem _ hh) hw
    have hmul : stMat h * stMat h⁻¹ = 1 := by
      unfold stMat
      rw [← Units.val_mul, ← Subgroup.coe_mul, mul_inv_cancel, Subgroup.coe_one, Units.val_one]
    have e : w = stMat h *ᵥ (stMat h⁻¹ *ᵥ w) := by
      rw [Matrix.mulVec_mulVec, hmul, Matrix.one_mulVec]
    rw [e]
    unfold stMat at hw' ⊢
    rw [pairedSympForm_mulVec]
    exact hv _ hw'
  exact mem_stabilizer_of_mulVec_mem (key g hg) (key g⁻¹ (Subgroup.inv_mem _ hg))

theorem flag_six_sub_eq_orth (i : ℕ) (hi : i ≤ 2) :
    flag 3 (ZMod 2) (6 - i) = (pairedSympForm (ZMod 2) 3).orthogonal (isoFlag 3 (ZMod 2) i) := by
  rw [flag, if_neg (by omega), show 2 * 3 - (6 - i) = i by omega]

theorem flag_le_eq_iso (i : ℕ) (hi : i ≤ 3) : flag 3 (ZMod 2) i = isoFlag 3 (ZMod 2) i := by
  rw [flag, if_pos hi]

@[expose] def cutSet (I : Finset ℕ) : Finset ℕ := I ∪ I.image (fun i => 6 - i)

theorem stab_cutSet {I : Finset ℕ} (hI : I ⊆ {1, 2, 3}) {g : StatedSp 3 (ZMod 2)}
    (hg : g ∈ flagStabilizer 3 (ZMod 2) (↑I : Set ℕ)) :
    ∀ s ∈ cutSet I, g ∈ stabilizer 3 (ZMod 2) (flag 3 (ZMod 2) s) := by
  rw [mem_flagStabilizer] at hg
  intro s hs
  unfold cutSet at hs
  rw [Finset.mem_union, Finset.mem_image] at hs
  rcases hs with hs | ⟨i, hi, rfl⟩
  · exact hg s (Finset.mem_coe.2 hs)
  · have hi3 : i ∈ ({1, 2, 3} : Finset ℕ) := hI hi
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi3
    rcases hi3 with rfl | rfl | rfl
    · rw [flag_six_sub_eq_orth 1 (by norm_num)]
      have h1 := hg 1 (Finset.mem_coe.2 hi)
      rw [flag_le_eq_iso 1 (by norm_num)] at h1
      exact mem_stab_orth h1
    · rw [flag_six_sub_eq_orth 2 (by norm_num)]
      have h2 := hg 2 (Finset.mem_coe.2 hi)
      rw [flag_le_eq_iso 2 (by norm_num)] at h2
      exact mem_stab_orth h2
    · have h3 := hg 3 (Finset.mem_coe.2 hi)
      norm_num
      exact h3

theorem blockSize_le_three_all : ∀ I ∈ ({1, 2, 3} : Finset ℕ).powerset, I ≠ ∅ → I ≠ {1} →
    ∀ β : Fin 6, (Finset.univ.filter (fun j : Fin 6 => blkOf (cutSet I) j = β.val)).card ≤ 3 := by
  decide

theorem blkOf_lt_six_all : ∀ I ∈ ({1, 2, 3} : Finset ℕ).powerset,
    ∀ j : Fin 6, blkOf (cutSet I) j < 6 := by
  decide

theorem flag_no_E9 (I : Finset ℕ) (hI : I ⊆ {1, 2, 3}) (hI0 : I ≠ ∅) (hI1 : I ≠ {1})
    (D : Subgroup (StatedSp 3 (ZMod 2))) (t : StatedSp 3 (ZMod 2))
    (hDP : D ≤ flagStabilizer 3 (ZMod 2) (↑I : Set ℕ)) (hD9 : Nat.card D = 9)
    (hexp : ∀ d ∈ D, d ^ 3 = 1) (htP : t ∈ flagStabilizer 3 (ZMod 2) (↑I : Set ℕ))
    (htD : ∀ d ∈ D, t * d * t⁻¹ ∈ D) (ht2 : ∀ d ∈ D, t ^ 2 * d * (t ^ 2)⁻¹ = d⁻¹) : False := by
  have hIm : I ∈ ({1, 2, 3} : Finset ℕ).powerset := Finset.mem_powerset.2 hI
  let ψ : StatedSp 3 (ZMod 2) →* Matrix.GeneralLinearGroup (Fin 6) (ZMod 2) :=
    toGL6.comp (Subgroup.subtype _)
  have hψinj : Function.Injective ψ := fun a b h => Subtype.ext (toGL6_injective h)
  have hS6 : ∀ s ∈ cutSet I, s ≤ 6 := by
    intro s hs
    unfold cutSet at hs
    rw [Finset.mem_union, Finset.mem_image] at hs
    rcases hs with hs | ⟨i, _, rfl⟩
    · have := hI hs
      simp only [Finset.mem_insert, Finset.mem_singleton] at this
      omega
    · exact Nat.sub_le 6 i
  have hsz : ∀ β : ℕ, Fintype.card (Blk (blkOf (cutSet I)) β) ≤ 3 := by
    intro β
    by_cases hβ : β < 6
    · have h := blockSize_le_three_all I hIm hI0 hI1 ⟨β, hβ⟩
      rw [Fintype.card_subtype]
      exact h
    · have hempty : IsEmpty (Blk (blkOf (cutSet I)) β) :=
        ⟨fun j => by
          have h1 := blkOf_lt_six_all I hIm j
          have h2 := j.2
          omega⟩
      rw [Fintype.card_of_isEmpty]
      omega
  have hblk : ∀ i, blkOf (cutSet I) i < 6 := fun i => blkOf_lt_six_all I hIm i
  have hP : ∀ g ∈ (flagStabilizer 3 (ZMod 2) (↑I : Set ℕ)).map ψ,
      BlockTri (blkOf (cutSet I)) (g : Matrix (Fin 6) (Fin 6) (ZMod 2)) := by
    intro g hg
    obtain ⟨h, hh, rfl⟩ := Subgroup.mem_map.1 hg
    exact blockTri_of_stab (cutSet I) hS6 (stab_cutSet hI hh)
  refine layer_contradiction (blkOf (cutSet I)) hblk hsz
    ((flagStabilizer 3 (ZMod 2) (↑I : Set ℕ)).map ψ) (D.map ψ) (ψ t) hP
    (Subgroup.map_mono hDP) ?_ ?_ (Subgroup.mem_map_of_mem ψ htP) ?_ ?_
  · rw [Subgroup.card_map_of_injective hψinj, hD9]
  · intro d6 hd6
    obtain ⟨d, hd, rfl⟩ := Subgroup.mem_map.1 hd6
    rw [← map_pow, hexp d hd, map_one]
  · intro d6 hd6
    obtain ⟨d, hd, rfl⟩ := Subgroup.mem_map.1 hd6
    rw [← map_inv, ← map_mul, ← map_mul]
    exact Subgroup.mem_map_of_mem ψ (htD d hd)
  · intro d6 hd6
    obtain ⟨d, hd, rfl⟩ := Subgroup.mem_map.1 hd6
    have := congrArg ψ (ht2 d hd)
    simpa [map_mul, map_pow, map_inv] using this

end CFSG.RankThree.PartTwo.Late.KFParSp6

end
