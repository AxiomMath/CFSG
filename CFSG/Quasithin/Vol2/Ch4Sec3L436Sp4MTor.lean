module

public import CFSG.Quasithin.Vol2.Ch4Sec3L436Sp4MPt

public section

namespace CFSG.Quasithin.H13.Ch4.Sp4M

open Matrix CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag
  CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher
  CFSG.LocalAnalysis.ComponentInitial.SymplecticTorusWeyl CFSG.QuasithinUnique.Setup.X7a
  CFSG.QuasithinUnique.Vol2Native.A312L CFSG.Quasithin.H13.NQCat.Sp4
  CFSG.Quasithin.Lie2Parabolic
open CFSG.Quasithin (perfectCore perfectCore_le)
open CFSG.Open (pCoreOf)
open scoped commutatorElement

variable {F : Type} [Field F]

@[expose] noncomputable def y1Hom : Fˣ →* StatedSp 2 F :=
  torusHom.comp (MonoidHom.mulSingle (fun _ : Fin 2 => Fˣ) 0)

@[expose] noncomputable def y2Hom : Fˣ →* StatedSp 2 F :=
  torusHom.comp (MonoidHom.mulSingle (fun _ : Fin 2 => Fˣ) 1)

theorem spMat_y1 (s : Fˣ) :
    spMat (y1Hom s) = diagonal (Sum.elim ![(s : F), 1] ![((s⁻¹ : Fˣ) : F), 1]) := by
  change ((torusHom (Pi.mulSingle 0 s) : StatedSp 2 F) : GL (Fin 2 ⊕ Fin 2) F).val = _
  rw [coe_torusHom]
  congr 1
  funext x
  rcases x with x | x <;> fin_cases x <;> simp [Pi.mulSingle_apply]

theorem spMat_y2 (s : Fˣ) :
    spMat (y2Hom s) = diagonal (Sum.elim ![1, (s : F)] ![1, ((s⁻¹ : Fˣ) : F)]) := by
  change ((torusHom (Pi.mulSingle 1 s) : StatedSp 2 F) : GL (Fin 2 ⊕ Fin 2) F).val = _
  rw [coe_torusHom]
  congr 1
  funext x
  rcases x with x | x <;> fin_cases x <;> simp [Pi.mulSingle_apply]

theorem y2Hom_eq (s : Fˣ) : y2Hom s = spLevi 0 (NQCat.dg2 s) := by
  apply statedSp_ext
  change spMat (y2Hom s) = spMat (spLevi 0 (NQCat.dg2 s))
  rw [spMat_y2, spMat_spLevi_dg2]
  congr 1

theorem y1Hom_injective : Function.Injective (y1Hom (F := F)) := by
  intro s t h
  apply Units.ext
  have := congrArg (fun g : StatedSp 2 F => spMat g (Sum.inl 0) (Sum.inl 0)) h
  simpa [spMat_y1] using this

theorem y2Hom_injective : Function.Injective (y2Hom (F := F)) := by
  intro s t h
  apply Units.ext
  have := congrArg (fun g : StatedSp 2 F => spMat g (Sum.inl 1) (Sum.inl 1)) h
  simpa [spMat_y2] using this

theorem y1Hom_comm_y2Hom (a b : Fˣ) : y1Hom a * y2Hom b = y2Hom b * y1Hom a := by
  rw [y1Hom, y2Hom, MonoidHom.comp_apply, MonoidHom.comp_apply, ← map_mul, ← map_mul, mul_comm]

theorem y1Hom_mem_Q0 (s : Fˣ) : y1Hom s ∈ Q2 F 0 := by
  show y1Hom s ∈ stabilizer 2 F (flag 2 F 1)
  rw [CFSG.Quasithin.F134.Sp4.mem_stabilizer_one_iff]
  change spMat (y1Hom s) (Sum.inr 0) (Sum.inl 0) = 0 ∧ spMat (y1Hom s) (Sum.inr 1) (Sum.inl 0) = 0 ∧
    spMat (y1Hom s) (Sum.inl 1) (Sum.inl 0) = 0
  rw [spMat_y1]
  simp

theorem y1Hom_mem_Q1 (s : Fˣ) : y1Hom s ∈ Q2 F 1 := by
  show y1Hom s ∈ stabilizer 2 F (flag 2 F 2)
  rw [CFSG.Quasithin.F134.Sp4.mem_stabilizer_two_iff]
  intro i j
  change spMat (y1Hom s) (Sum.inr i) (Sum.inl j) = 0
  rw [spMat_y1]
  simp

theorem spMat_y1_apply (s : Fˣ) : spMat (y1Hom s) (Sum.inl 0) (Sum.inl 0) = s := by
  rw [spMat_y1]
  simp

theorem conj_y1_xAB (s : Fˣ) (t : F) : y1Hom s * xAB t * (y1Hom s)⁻¹ = xAB ((s : F) * t) := by
  rw [mul_inv_eq_iff_eq_mul]
  apply statedSp_ext
  change spMat (y1Hom s) * spMat (xAB t) = spMat (xAB _) * spMat (y1Hom s)
  rw [spMat_y1, spMat_xAB, spMat_xAB]
  ext x y
  rcases x with x | x <;> rcases y with y | y <;> fin_cases x <;> fin_cases y <;>
    simp
  all_goals field_simp

theorem det_blk0_of_mem_Q0 {g : StatedSp 2 F} (hg : g ∈ Q2 F 0) :
    (blkIdx (sigma2 0) (spMat g)).det = 1 := by
  obtain ⟨-, -, -, h4, h5, -⟩ := entries_of_mem_Q0 hg
  have hs := congrFun₂ (mem_statedSp_iff.mp g.2) (Sum.inl 1) (Sum.inr 1)
  simp only [Matrix.mul_apply, Fintype.sum_sum_type, Fin.sum_univ_two, Matrix.transpose_apply,
    fromBlocks_apply₁₁, fromBlocks_apply₁₂, fromBlocks_apply₂₁, fromBlocks_apply₂₂,
    Matrix.zero_apply, Matrix.one_apply, Matrix.neg_apply] at hs
  have hb : blkIdx (sigma2 0) (spMat g) = !![spMat g (Sum.inl 1) (Sum.inl 1),
      spMat g (Sum.inl 1) (Sum.inr 1); spMat g (Sum.inr 1) (Sum.inl 1),
      spMat g (Sum.inr 1) (Sum.inr 1)] := by
    ext i k
    fin_cases i <;> fin_cases k <;> rfl
  rw [hb, det_fin_two_of]
  simp [h4, h5] at hs
  linear_combination hs

theorem mem_unipotent_of_mem_Q0 {g : StatedSp 2 F} (hg : g ∈ Q2 F 0)
    (hlam : spMat g (Sum.inl 0) (Sum.inl 0) = 1) (hblk : blkIdx (sigma2 0) (spMat g) = 1) :
    g ∈ unipotent 2 F := by
  obtain ⟨h1, h2, h3, h4, -, -⟩ := entries_of_mem_Q0 hg
  have e00 : spMat g (Sum.inl 1) (Sum.inl 1) = 1 := by
    have := congrFun₂ hblk 0 0
    simpa [blkIdx, sigma2] using this
  have e10 : spMat g (Sum.inr 1) (Sum.inl 1) = 0 := by
    have := congrFun₂ hblk 1 0
    simpa [blkIdx, sigma2] using this
  have h21 : (spMat g).toBlocks₂₁ = 0 := by
    ext i k
    show spMat g (Sum.inr i) (Sum.inl k) = 0
    fin_cases i <;> fin_cases k
    · exact h2
    · exact h4
    · exact h3
    · exact e10
  obtain ⟨-, C, hC, hM⟩ := exists_blockMat_of_toBlocks₂₁_eq_zero h21
  refine ⟨(spMat g).toBlocks₁₁, C, ⟨?_, ?_⟩, hC, hM⟩
  · intro i k hik
    fin_cases i <;> fin_cases k <;> simp at hik ⊢
    exact h1
  · intro i
    fin_cases i
    · exact hlam
    · exact e00

variable [Finite F] [CharP F 2] {n : ℕ}

theorem Q0_eq_sup (hn : 2 ≤ n) (hF : Nat.card F = 2 ^ n) :
    Q2 F 0 = y1Hom.range ⊔ perfectCore (Q2 F 0) := by
  have hK4 := NQCat.exists_finset_card_four_of_card hn hF
  apply le_antisymm
  · intro g hg
    have hlam0 := spMat_inl_zero_ne_zero hg
    set u : Fˣ := Units.mk0 _ hlam0 with hu
    have hyQ : (y1Hom u)⁻¹ ∈ Q2 F 0 := inv_mem (y1Hom_mem_Q0 u)
    set h := (y1Hom u)⁻¹ * g with hh
    have hhQ : h ∈ Q2 F 0 := mul_mem hyQ hg
    have hh00 : spMat h (Sum.inl 0) (Sum.inl 0) = 1 := by
      rw [hh, ← map_inv]
      change (spMat (y1Hom u⁻¹) * spMat g) (Sum.inl 0) (Sum.inl 0) = 1
      rw [spMat_y1]
      simp [diagonal_mul, hu]
      exact inv_mul_cancel₀ hlam0
    set A : Matrix.SpecialLinearGroup (Fin 2) F := ⟨blkIdx (sigma2 0) (spMat h),
      det_blk0_of_mem_Q0 hhQ⟩ with hA
    have hSQ : (spLevi 0 A)⁻¹ ∈ Q2 F 0 := inv_mem (spLevi_mem 0 A)
    set h' := h * (spLevi 0 A)⁻¹ with hh'
    have hh'Q : h' ∈ Q2 F 0 := mul_mem hhQ hSQ
    have hblk : blkIdx (sigma2 0) (spMat h') = 1 := by
      have e' : blkIdx (sigma2 0) (spMat (h * (spLevi 0 A)⁻¹)) =
          blkIdx (sigma2 0) (spMat h) * blkIdx (sigma2 0) (spMat (spLevi 0 A)⁻¹) :=
        (blkQ (K := F) 0).map_mul ⟨h, hhQ⟩ ⟨(spLevi 0 A)⁻¹, hSQ⟩
      rw [hh', e', ← map_inv, blkIdx_spLevi]
      show (A : Matrix (Fin 2) (Fin 2) F) * ((A⁻¹ : Matrix.SpecialLinearGroup (Fin 2) F) :
        Matrix (Fin 2) (Fin 2) F) = 1
      rw [← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel, Matrix.SpecialLinearGroup.coe_one]
    have hh'00 : spMat h' (Sum.inl 0) (Sum.inl 0) = 1 := by
      rw [hh', ← map_inv]
      change (spMat h * spMat (spLevi 0 A⁻¹)) (Sum.inl 0) (Sum.inl 0) = 1
      rw [spMat_lam]
      rw [Matrix.mul_apply, Finset.sum_eq_single (Sum.inl 0)]
      · rw [pairMat_apply_of_ne' (by simp) (by simp), Matrix.one_apply_eq, mul_one, hh00]
      · intro y _ hy
        rw [pairMat_apply_of_ne' (by simp) (by simp), Matrix.one_apply_ne hy, mul_zero]
      · intro h
        exact absurd (Finset.mem_univ _) h
    have hU := mem_unipotent_of_mem_Q0 hh'Q hh'00 hblk
    have hgdec : g = y1Hom u * h' * spLevi 0 A := by
      rw [hh', hh]
      group
    rw [hgdec]
    exact mul_mem (mul_mem (Subgroup.mem_sup_left ⟨u, rfl⟩)
      (Subgroup.mem_sup_right (mem_perfectCore_of_mem_unipotent hn hF 0 hU)))
      (Subgroup.mem_sup_right (spLevi_mem_perfectCore hK4 0 A))
  · exact sup_le (by rintro _ ⟨s, rfl⟩; exact y1Hom_mem_Q0 s) (perfectCore_le _)

omit [Finite F] [CharP F 2] in
theorem mem_normalizer_XAB {y : StatedSp 2 F} {w w' : F}
    (h1 : ∀ t, y * xAB t * y⁻¹ = xAB (w * t)) (h2 : ∀ t, y⁻¹ * xAB t * y⁻¹⁻¹ = xAB (w' * t)) :
    y ∈ Subgroup.normalizer (XAB F : Set (StatedSp 2 F)) := by
  rw [Subgroup.mem_normalizer_iff]
  intro h
  constructor
  · rintro ⟨t, rfl⟩
    exact ⟨_, (h1 t).symm⟩
  · rintro ⟨t, ht⟩
    refine ⟨w' * t, ?_⟩
    rw [← h2 t, ht]
    group

omit [Finite F] [CharP F 2] in
theorem y1Hom_mem_normalizer_XAB (s : Fˣ) :
    y1Hom s ∈ Subgroup.normalizer (XAB F : Set (StatedSp 2 F)) := by
  refine mem_normalizer_XAB (conj_y1_xAB s) (w' := ((s⁻¹ : Fˣ) : F)) fun t => ?_
  rw [← map_inv, conj_y1_xAB]

omit [Finite F] [CharP F 2] in
theorem y2Hom_mem_normalizer_XAB (s : Fˣ) :
    y2Hom s ∈ Subgroup.normalizer (XAB F : Set (StatedSp 2 F)) := by
  refine mem_normalizer_XAB (w := (s : F)) (w' := ((s⁻¹ : Fˣ) : F)) (fun t => ?_) fun t => ?_
  · rw [y2Hom_eq, conj_zero_xAB]
  · rw [← map_inv, y2Hom_eq, conj_zero_xAB]

omit [Finite F] [CharP F 2] in
theorem card_range_y1 (hF : Nat.card F = 2 ^ n) : Nat.card ↥(y1Hom (F := F)).range = 2 ^ n - 1 := by
  rw [← hF, ← Nat.card_units F]
  exact Nat.card_range_of_injective y1Hom_injective

omit [Finite F] [CharP F 2] in
theorem card_range_y2 (hF : Nat.card F = 2 ^ n) : Nat.card ↥(y2Hom (F := F)).range = 2 ^ n - 1 := by
  rw [← hF, ← Nat.card_units F]
  exact Nat.card_range_of_injective y2Hom_injective

omit [CharP F 2] in
theorem isCyclic_range (f : Fˣ →* StatedSp 2 F) : IsCyclic ↥f.range :=
  isCyclic_of_surjective f.rangeRestrict f.rangeRestrict_surjective

omit [Finite F] [CharP F 2] in
theorem blkIdx_y1 (s : Fˣ) : blkIdx (sigma2 0) (spMat (y1Hom s)) = 1 := by
  rw [spMat_y1]
  ext i k
  fin_cases i <;> fin_cases k <;> simp [blkIdx, sigma2]

theorem sp4Torus_model (hn : 2 ≤ n) (hF : Nat.card F = 2 ^ n) :
    L436.Sp4Torus n ⊤ (Q2 F 1) (XAB F) (XC F) (perfectCore (Q2 F 0))
      (pCoreOf 2 (perfectCore (Q2 F 0))) := by
  have hK4 := NQCat.exists_finset_card_four_of_card hn hF
  have hNZ : (⊤ : Subgroup (StatedSp 2 F)) ⊓ Subgroup.normalizer (XC F : Set (StatedSp 2 F)) =
      Q2 F 0 := by rw [top_inf_eq, normalizer_XC]
  refine ⟨y1Hom.range, y2Hom.range, ?_, ?_, isCyclic_range _, card_range_y1 hF, ?_, ?_, ?_, ?_,
    isCyclic_range _, card_range_y2 hF, ?_, ?_, ?_⟩
  · rw [hNZ]
    rintro _ ⟨s, rfl⟩
    exact y1Hom_mem_Q0 s
  · rintro _ ⟨s, rfl⟩
    exact y1Hom_mem_Q1 s
  · rintro _ ⟨s, rfl⟩ _ ⟨a, rfl⟩ h
    rw [conj_xC_of_mem_Q0 (y1Hom_mem_Q0 s), spMat_y1_apply] at h
    by_cases ha : a = 0
    · right
      rw [ha, xC_zero]
    · left
      have h2 := xC_injective h
      have hs2 : (s : F) ^ 2 = 1 := by
        have := mul_right_cancel₀ ha (h2.trans (one_mul a).symm)
        exact this
      have hs1 : (s : F) = 1 := CharTwo.sq_injective (hs2.trans (one_pow 2).symm)
      have : s = 1 := Units.ext hs1
      rw [this, map_one]
  · rintro _ ⟨s, rfl⟩ k hk
    have hkQ : k ∈ Q2 F 0 := perfectCore_le _ hk
    have hyN : y1Hom s ∈ Subgroup.normalizer (perfectCore (Q2 F 0) : Set (StatedSp 2 F)) :=
      CFSG.Quasithin.normalizer_le_normalizer_perfectCore _
        (Subgroup.le_normalizer (y1Hom_mem_Q0 s))
    have hmem : y1Hom s * k * (y1Hom s)⁻¹ * k⁻¹ ∈ perfectCore (Q2 F 0) :=
      mul_mem ((Subgroup.mem_normalizer_iff.mp hyN k).mp hk) (inv_mem hk)
    rw [mem_pCoreOf_perfectCore_Q2 hn hF 0 hmem]
    have e : blkIdx (sigma2 0) (spMat (y1Hom s * k * (y1Hom s)⁻¹ * k⁻¹)) =
        blkIdx (sigma2 0) (spMat (y1Hom s)) * blkIdx (sigma2 0) (spMat k) *
          blkIdx (sigma2 0) (spMat (y1Hom s)⁻¹) * blkIdx (sigma2 0) (spMat k⁻¹) := by
      show blkQ (K := F) 0 (⟨y1Hom s, y1Hom_mem_Q0 s⟩ * ⟨k, hkQ⟩ *
          (⟨y1Hom s, y1Hom_mem_Q0 s⟩)⁻¹ * (⟨k, hkQ⟩)⁻¹) =
        blkQ (K := F) 0 ⟨y1Hom s, y1Hom_mem_Q0 s⟩ * blkQ (K := F) 0 ⟨k, hkQ⟩ *
          blkQ (K := F) 0 (⟨y1Hom s, y1Hom_mem_Q0 s⟩)⁻¹ * blkQ (K := F) 0 (⟨k, hkQ⟩)⁻¹
      rw [map_mul, map_mul, map_mul]
    have ek : blkIdx (sigma2 0) (spMat k) * blkIdx (sigma2 0) (spMat k⁻¹) = 1 := by
      have := (blkQ (K := F) 0).map_mul (⟨k, hkQ⟩) (⟨k, hkQ⟩)⁻¹
      rw [mul_inv_cancel, map_one] at this
      exact this.symm
    rw [e, ← map_inv, blkIdx_y1, blkIdx_y1, one_mul, mul_one, ek]
  · rw [hNZ]
    exact Q0_eq_sup hn hF
  · rintro _ ⟨s, rfl⟩
    rw [y2Hom_eq]
    exact spLevi_mem_perfectCore hK4 0 _
  · rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩
    exact y1Hom_comm_y2Hom a b
  · refine sup_le ?_ ?_
    · rintro _ ⟨s, rfl⟩
      exact y1Hom_mem_normalizer_XAB s
    · rintro _ ⟨s, rfl⟩
      exact y2Hom_mem_normalizer_XAB s
  · rintro _ ⟨u, rfl⟩ _ ⟨u', rfl⟩ hu hu'
    have hu0 : u ≠ 0 := fun h => hu (by rw [h, xAB_zero])
    have hu0' : u' ≠ 0 := fun h => hu' (by rw [h, xAB_zero])
    refine ⟨y1Hom (Units.mk0 (u' / u) (div_ne_zero hu0' hu0)),
      Subgroup.mem_sup_left ⟨_, rfl⟩, ?_⟩
    rw [conj_y1_xAB]
    congr 1
    simp only [Units.val_mk0]
    field_simp

end CFSG.Quasithin.H13.Ch4.Sp4M
