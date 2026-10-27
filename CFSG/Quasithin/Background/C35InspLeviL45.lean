module

public import CFSG.Quasithin.Background.C35InspLeviRes
public import CFSG.Quasithin.Background.C35InspL45D
public import CFSG.Quasithin.Background.KGSchurMult2
public import CFSG.RankThree.PartOne.AUTSL.Interface

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.Quasithin.C35Levi

open CFSG.Open hiding StatedSL StatedSp StatedSU StatedProj StatedScalars
open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank Matrix C35Pf
  CFSG.LocalAnalysis.ComponentInitial.LinearFlag CFSG.QuasithinUnique.Vol2Native.A312L
  CFSG.Quasithin.C48Pf.FMod

variable {A : Type} [Group A] [Finite A]

theorem exists_flag_cover {K Y : Subgroup A} (hZ : IsPGroup 2 ↥(centerOf K)) {n : ℕ}
    (hn4 : 4 ≤ n) (hn5 : n ≤ 5) (ψ : ↥K →* SpecialLinearGroup (Fin n) (ZMod 2))
    (hψker : ψ.ker ≤ Subgroup.center ↥K) (hψ : Function.Surjective ψ)
    (hpar : IsParabolic2 K Y) (hYK : Y ≠ K) (hne : perfectCore Y ≠ ⊥) :
    ∃ (g : SpecialLinearGroup (Fin n) (ZMod 2)) (I : Set ℕ) (a m : ℕ) (_ : a + m ≤ n),
      3 ≤ m ∧ (a = 0 ∨ a ∈ I) ∧ (a + m = n ∨ a + m ∈ I) ∧ (∀ c ∈ I, ¬ (a < c ∧ c < a + m)) ∧
      (∀ c ∈ I, 1 ≤ c ∧ c < n) ∧ (0 < a ∨ a + m < n) ∧
      img ((MulAut.conj g⁻¹).toMonoidHom.comp ψ) Y = flagStabilizer n (ZMod 2) I ∧
      img ((MulAut.conj g⁻¹).toMonoidHom.comp ψ) (perfectCore Y) =
        perfectCore (flagStabilizer n (ZMod 2) I) := by
  classical
  have hK2 : Nat.card (ZMod 2) = 2 := Nat.card_zmod 2
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨Pu, hPu⟩ := exists_sylow_unitriangular (K := ZMod 2) 2 (n := n) (by omega)
  have hUsyl : IsSylowTwoOf (unitriangular n (ZMod 2)) ⊤ :=
    hPu ▸ CFSG.QuasithinUnique.isSylowTwoOf_top_of_sylow Pu
  obtain ⟨g, hNY, hQtop, -⟩ := exists_conj_normalizer hZ hpar hYK hne ψ hψker hψ hUsyl
  set θ := (MulAut.conj g⁻¹).toMonoidHom.comp ψ with hθ
  have hθker : θ.ker ≤ Subgroup.center ↥K := by rw [hθ, ker_conj_comp]; exact hψker
  have hUQ : upperTriangular n (ZMod 2) ≤ img θ Y :=
    (upperTriangular_le_unitriangular hK2).trans (Subgroup.le_normalizer.trans hNY)
  obtain ⟨hQI, -⟩ := borel_overgroups (img θ Y) hUQ
  set I := borelOvergroupCuts (img θ Y) with hI
  have hIcuts : ∀ c ∈ I, 1 ≤ c ∧ c < n := fun c hc => by
    obtain ⟨h1, h2, -⟩ := hc
    exact ⟨h1, h2⟩
  have hMQ : img θ (perfectCore Y) = perfectCore (img θ Y) := img_perfectCore θ hpar.1
  have hMne : perfectCore (img θ Y) ≠ ⊥ := hMQ ▸ img_perfectCore_ne_bot hZ hpar.1 θ hθker hne
  rcases exists_big_or_small (n := n) (I := I) with hsmall | ⟨a, m, h, hm3, ha, hb, hno⟩
  · exfalso
    apply hMne
    rw [hQI]
    exact perfectCore_eq_bot_of_small hK2 (by omega) hsmall
  have hmn : m < n := by
    by_contra hmn
    apply hQtop
    have hIe : I = ∅ := by
      ext c
      simp only [Set.mem_empty_iff_false, iff_false]
      intro hc
      obtain ⟨h1, h2⟩ := hIcuts c hc
      exact hno c hc ⟨by omega, by omega⟩
    rw [hQI, hIe, flagStabilizer_empty]
  exact ⟨g, I, a, m, h, hm3, ha, hb, hno, hIcuts, by omega, hQI, hMQ.trans (congrArg _ hQI)⟩

section Block

variable {n : ℕ} {I : Set ℕ} {a m : ℕ}

omit [Finite A] in
theorem isPGroup_ker_bigBlockHom (hn1 : 1 ≤ n) (hn5 : n ≤ 5) (h : a + m ≤ n) (hm3 : 3 ≤ m)
    (ha : a = 0 ∨ a ∈ I) (hb : a + m = n ∨ a + m ∈ I) (hno : ∀ c ∈ I, ¬ (a < c ∧ c < a + m)) :
    IsPGroup 2 (bigBlockHom (K := ZMod 2) I a m h ha hb).ker := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rintro ⟨x, hx⟩
  have hU := unitriangular_of_bigBlockHom (Nat.card_zmod 2) hn5 h hm3 ha hb hno x hx
  obtain ⟨j, hj⟩ := isPGroup_unitriangular_charTwo (K := ZMod 2) (n := n) hn1 ⟨_, hU⟩
  refine ⟨j, Subtype.ext (Subtype.ext ?_)⟩
  have := congrArg Subtype.val hj
  simpa using this

omit [Finite A] in
theorem transvection_ne_one {k l : Fin n} (hkl : k ≠ l) :
    SpecialLinearGroup.transvection hkl (1 : ZMod 2) ≠ 1 := by
  intro h
  have := congrFun (congrFun (congrArg Subtype.val h) k) l
  rw [CFSG.LinearGroups.coe_transvection] at this
  simp [Matrix.one_apply_ne hkl] at this

omit [Finite A] in
theorem exists_noncomm_flag (h : a + m ≤ n) (hm3 : 3 ≤ m) (ha : a = 0 ∨ a ∈ I)
    (hb : a + m = n ∨ a + m ∈ I) (hno : ∀ c ∈ I, ¬ (a < c ∧ c < a + m))
    (hprop : 0 < a ∨ a + m < n) :
    ∃ r x : ↥(perfectCore (flagStabilizer n (ZMod 2) I)),
      bigBlockHom (K := ZMod 2) I a m h ha hb r = 1 ∧ x * r ≠ r * x := by
  have h0 : (0 : ℕ) < m := by omega
  have h1 : (1 : ℕ) < m := by omega
  rcases hprop with hpos | hlt
  ·
    set k : Fin n := ⟨a - 1, by omega⟩
    set l : Fin n := blkIdxN a m h ⟨0, h0⟩
    have hc : IsCross a m k l := Or.inl ⟨by simp [k]; omega, by simp [l, blkIdxN],
      by simp [l, blkIdxN]; omega⟩
    have hij : (⟨0, h0⟩ : Fin m) ≠ ⟨1, h1⟩ := by simp
    refine ⟨⟨_, transvection_mem_perfectCore h hm3 hno hc⟩,
      ⟨_, liftT_mem_perfectCore h hm3 hno hij⟩, ?_, ?_⟩
    · apply Subtype.ext
      rw [bigBlockHom_coe]
      exact blkAt_transvection_cross h hc
    · intro hxr
      have hk2 : k ≠ blkIdxN a m h ⟨1, h1⟩ := by
        intro e
        have := congrArg Fin.val e
        simp [k, blkIdxN] at this
      have hcomm := SpecialLinearGroup.commutatorElement_transvection hc.ne (blkIdxN_ne hij) hk2
        (1 : ZMod 2) 1
      rw [mul_one] at hcomm
      apply transvection_ne_one hk2
      rw [← hcomm, commutatorElement_eq_one_iff_mul_comm]
      have := congrArg Subtype.val hxr
      exact this.symm
  ·
    set k : Fin n := blkIdxN a m h ⟨0, h0⟩
    set l : Fin n := ⟨a + m, hlt⟩
    have hc : IsCross a m k l := Or.inr ⟨by simp [k, blkIdxN], by simp [k, blkIdxN]; omega,
      by simp [l]⟩
    have hij : (⟨1, h1⟩ : Fin m) ≠ ⟨0, h0⟩ := by simp
    refine ⟨⟨_, transvection_mem_perfectCore h hm3 hno hc⟩,
      ⟨_, liftT_mem_perfectCore h hm3 hno hij⟩, ?_, ?_⟩
    · apply Subtype.ext
      rw [bigBlockHom_coe]
      exact blkAt_transvection_cross h hc
    · intro hxr
      have hk2 : blkIdxN a m h ⟨1, h1⟩ ≠ l := by
        intro e
        have := congrArg Fin.val e
        simp [l, blkIdxN] at this
        omega
      have hcomm := SpecialLinearGroup.commutatorElement_transvection (blkIdxN_ne hij) hc.ne hk2
        (1 : ZMod 2) 1
      rw [mul_one] at hcomm
      apply transvection_ne_one hk2
      rw [← hcomm, commutatorElement_eq_one_iff_mul_comm]
      exact congrArg Subtype.val hxr

end Block

section Inner

theorem eq_zero_of_add_single {n : ℕ} {k l : Fin n} (hkl : k ≠ l) {w : Fin n → ZMod 2}
    {c : ZMod 2} (h : w + Pi.single k (w l) = c • w) : w l = 0 := by
  have h1 := congrFun h k
  have h2 := congrFun h l
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.single_eq_same,
    Pi.single_eq_of_ne' hkl] at h1 h2
  clear h
  revert h1 h2
  generalize w k = x
  generalize w l = y
  revert x y c
  decide

theorem transvection_mulVec {n : ℕ} {k l : Fin n} (hkl : k ≠ l) (w : Fin n → ZMod 2) :
    ((SpecialLinearGroup.transvection hkl (1 : ZMod 2) : SpecialLinearGroup (Fin n) (ZMod 2)) :
      Matrix (Fin n) (Fin n) (ZMod 2)) *ᵥ w = w + Pi.single k (w l) := by
  rw [CFSG.LinearGroups.coe_transvection, Matrix.add_mulVec, Matrix.one_mulVec,
    Matrix.single_mulVec, one_mul]
  rfl

theorem transvection_transpose_mulVec {n : ℕ} {k l : Fin n} (hkl : k ≠ l) (w : Fin n → ZMod 2) :
    ((SpecialLinearGroup.transvection hkl (1 : ZMod 2) : SpecialLinearGroup (Fin n) (ZMod 2)) :
      Matrix (Fin n) (Fin n) (ZMod 2))ᵀ *ᵥ w = w + Pi.single l (w k) := by
  rw [CFSG.LinearGroups.coe_transvection, Matrix.transpose_add, Matrix.transpose_one,
    Matrix.transpose_single, Matrix.add_mulVec, Matrix.one_mulVec, Matrix.single_mulVec, one_mul]
  rfl

theorem mulVec_single_one_apply {n : ℕ} (M : Matrix (Fin n) (Fin n) (ZMod 2)) (j i : Fin n) :
    (M *ᵥ Pi.single j 1) i = M i j := by
  simp [Matrix.mulVec, dotProduct, Pi.single_apply]

theorem exists_inner_of_flag {c : ℕ} (hc : c = 1 ∨ c = 4)
    (β : MulAut (SpecialLinearGroup (Fin 5) (ZMod 2)))
    (hβ : (flagStabilizer 5 (ZMod 2) {c}).map β.toMonoidHom = flagStabilizer 5 (ZMod 2) {c}) :
    ∃ B : SpecialLinearGroup (Fin 5) (ZMod 2), ∀ s, β s = B * s * B⁻¹ := by
  classical
  obtain ⟨A, σ, hform⟩ := CFSG.RankThree.PartOne.AUTSL.exists_matrix_form_of_mulAut_sl
    (by norm_num : 3 ≤ 5) β
  have hσ : ∀ x : ZMod 2, σ x = x := by
    have h01 : ∀ x : ZMod 2, x = 0 ∨ x = 1 := by decide
    intro x
    rcases h01 x with rfl | rfl
    · exact map_zero σ
    · exact map_one σ
  have hmap : ∀ M : Matrix (Fin 5) (Fin 5) (ZMod 2), M.map σ = M := fun M => by
    ext i j
    simp [Matrix.map_apply, hσ]
  have hu : ∀ u : (ZMod 2)ˣ, u = 1 := by decide
  have hdet : (A : Matrix (Fin 5) (Fin 5) (ZMod 2)).det = 1 := by
    rw [← Matrix.GeneralLinearGroup.val_det_apply, hu (Matrix.GeneralLinearGroup.det A),
      Units.val_one]
  have hAinv : ((A⁻¹ : GL (Fin 5) (ZMod 2)) : Matrix (Fin 5) (Fin 5) (ZMod 2)) *
      (A : Matrix (Fin 5) (Fin 5) (ZMod 2)) = 1 := by
    rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  have hAinv' : (A : Matrix (Fin 5) (Fin 5) (ZMod 2)) *
      ((A⁻¹ : GL (Fin 5) (ZMod 2)) : Matrix (Fin 5) (Fin 5) (ZMod 2)) = 1 := by
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  rcases hform with hconj | htr
  · let B : SpecialLinearGroup (Fin 5) (ZMod 2) := ⟨(A : Matrix (Fin 5) (Fin 5) (ZMod 2)), hdet⟩
    refine ⟨B, fun s => Subtype.ext ?_⟩
    rw [hconj s, hmap]
    have hBinv : ((B⁻¹ : SpecialLinearGroup (Fin 5) (ZMod 2)) : Matrix (Fin 5) (Fin 5) (ZMod 2)) =
        ((A⁻¹ : GL (Fin 5) (ZMod 2)) : Matrix (Fin 5) (Fin 5) (ZMod 2)) := by
      have h1 : ((B⁻¹ : SpecialLinearGroup (Fin 5) (ZMod 2)) : Matrix (Fin 5) (Fin 5) (ZMod 2)) *
          (A : Matrix (Fin 5) (Fin 5) (ZMod 2)) = 1 := by
        have := congrArg (fun x : SpecialLinearGroup (Fin 5) (ZMod 2) =>
          (x : Matrix (Fin 5) (Fin 5) (ZMod 2))) (inv_mul_cancel B)
        simp only [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_one] at this
        exact this
      calc ((B⁻¹ : SpecialLinearGroup (Fin 5) (ZMod 2)) : Matrix (Fin 5) (Fin 5) (ZMod 2)) =
            ((B⁻¹ : SpecialLinearGroup (Fin 5) (ZMod 2)) : Matrix (Fin 5) (Fin 5) (ZMod 2)) *
              ((A : Matrix (Fin 5) (Fin 5) (ZMod 2)) *
                ((A⁻¹ : GL (Fin 5) (ZMod 2)) : Matrix (Fin 5) (Fin 5) (ZMod 2))) := by
            rw [hAinv', Matrix.mul_one]
        _ = _ := by rw [← Matrix.mul_assoc, h1, Matrix.one_mul]
    show _ = ((B : Matrix (Fin 5) (Fin 5) (ZMod 2)) * (s : Matrix (Fin 5) (Fin 5) (ZMod 2))) *
      ((B⁻¹ : SpecialLinearGroup (Fin 5) (ZMod 2)) : Matrix (Fin 5) (Fin 5) (ZMod 2))
    rw [hBinv]
  · exfalso
    have hβmem : ∀ s ∈ flagStabilizer 5 (ZMod 2) {c}, β s ∈ flagStabilizer 5 (ZMod 2) {c} :=
      fun s hs => hβ ▸ ⟨s, hs, rfl⟩
    have hβm : ∀ s : SpecialLinearGroup (Fin 5) (ZMod 2),
        ((β s : SpecialLinearGroup (Fin 5) (ZMod 2)) : Matrix (Fin 5) (Fin 5) (ZMod 2)) =
          (A : Matrix (Fin 5) (Fin 5) (ZMod 2)) *
            ((s⁻¹ : SpecialLinearGroup (Fin 5) (ZMod 2)) : Matrix (Fin 5) (Fin 5) (ZMod 2))ᵀ *
              ((A⁻¹ : GL (Fin 5) (ZMod 2)) : Matrix (Fin 5) (Fin 5) (ZMod 2)) := fun s => by
      rw [htr s, hmap]
    rcases hc with rfl | rfl
    ·
      set e0 : Fin 5 → ZMod 2 := Pi.single 0 1 with he0
      set w : Fin 5 → ZMod 2 :=
        ((A⁻¹ : GL (Fin 5) (ZMod 2)) : Matrix (Fin 5) (Fin 5) (ZMod 2)) *ᵥ e0 with hw
      have hfix : ∀ u ∈ flagStabilizer 5 (ZMod 2) {1},
          ∃ c : ZMod 2, (u : Matrix (Fin 5) (Fin 5) (ZMod 2)) *ᵥ e0 = c • e0 := by
        intro u hu
        have hst := mem_flagStabilizer.1 hu 1 rfl
        refine ⟨(u : Matrix (Fin 5) (Fin 5) (ZMod 2)) 0 0, ?_⟩
        ext i
        rw [he0, mulVec_single_one_apply]
        rcases Fin.eq_zero_or_eq_succ i with rfl | ⟨i', rfl⟩
        · simp
        · rw [stabilizer_entries hst (by simp) (by simp)]
          simp
      have hw2 : ∀ s ∈ flagStabilizer 5 (ZMod 2) {1}, ∃ c : ZMod 2,
          ((s⁻¹ : SpecialLinearGroup (Fin 5) (ZMod 2)) : Matrix (Fin 5) (Fin 5) (ZMod 2))ᵀ *ᵥ w =
            c • w := by
        intro s hs
        obtain ⟨c, hc⟩ := hfix _ (hβmem s hs)
        refine ⟨c, ?_⟩
        rw [hβm s] at hc
        have := congrArg (fun v => ((A⁻¹ : GL (Fin 5) (ZMod 2)) :
          Matrix (Fin 5) (Fin 5) (ZMod 2)) *ᵥ v) hc
        simp only [Matrix.mulVec_mulVec, Matrix.mulVec_smul] at this
        rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hAinv, Matrix.one_mul] at this
        rw [hw, Matrix.mulVec_mulVec]
        exact this
      have hw0 : w ≠ 0 := by
        intro h0
        have := congrArg (fun v => (A : Matrix (Fin 5) (Fin 5) (ZMod 2)) *ᵥ v) h0
        simp only [hw, Matrix.mulVec_mulVec, hAinv', Matrix.one_mulVec, Matrix.mulVec_zero] at this
        have h1 := congrFun this 0
        simp [he0] at h1
      apply hw0
      funext k
      set l : Fin 5 := if k = 1 then 2 else 1 with hl
      have hkl : k ≠ l := by
        rw [hl]
        split_ifs with h
        · rw [h]; decide
        · exact h
      have hl0 : (1 : ℕ) ≤ (l : ℕ) := by
        rw [hl]
        split_ifs <;> decide
      have hmem : SpecialLinearGroup.transvection hkl (1 : ZMod 2) ∈
          flagStabilizer 5 (ZMod 2) {1} := by
        refine transvection_mem_flag hkl fun d hd => ?_
        rw [Set.mem_singleton_iff] at hd
        subst hd
        omega
      obtain ⟨c, hc⟩ := hw2 _ (inv_mem hmem)
      rw [inv_inv, transvection_transpose_mulVec] at hc
      exact eq_zero_of_add_single (Ne.symm hkl) hc
    ·
      set e4 : Fin 5 → ZMod 2 := Pi.single 4 1 with he4
      set w : Fin 5 → ZMod 2 := (A : Matrix (Fin 5) (Fin 5) (ZMod 2)) *ᵥ e4 with hw
      have hrow : ∀ s ∈ flagStabilizer 5 (ZMod 2) {4}, ∃ c : ZMod 2,
          (s : Matrix (Fin 5) (Fin 5) (ZMod 2))ᵀ *ᵥ e4 = c • e4 := by
        intro s hs
        have hst := mem_flagStabilizer.1 hs 4 rfl
        refine ⟨(s : Matrix (Fin 5) (Fin 5) (ZMod 2)) 4 4, ?_⟩
        ext i
        rw [he4, mulVec_single_one_apply, Matrix.transpose_apply]
        by_cases hi : i = 4
        · subst hi
          simp
        · have hi' : (i : ℕ) < 4 := by
            have := i.isLt
            have : (i : ℕ) ≠ 4 := fun h => hi (Fin.ext h)
            omega
          rw [stabilizer_entries hst hi' (by simp)]
          simp [Pi.single_eq_of_ne hi]
      have hw2 : ∀ u ∈ flagStabilizer 5 (ZMod 2) {4}, ∃ c : ZMod 2,
          (u : Matrix (Fin 5) (Fin 5) (ZMod 2)) *ᵥ w = c • w := by
        intro u hu
        rw [← hβ] at hu
        obtain ⟨s, hs, rfl⟩ := hu
        obtain ⟨c, hc⟩ := hrow _ (inv_mem hs)
        refine ⟨c, ?_⟩
        show ((β s : SpecialLinearGroup (Fin 5) (ZMod 2)) : Matrix (Fin 5) (Fin 5) (ZMod 2)) *ᵥ w =
          c • w
        rw [hβm s, hw, Matrix.mulVec_mulVec, Matrix.mul_assoc, Matrix.mul_assoc, hAinv,
          Matrix.mul_one, ← Matrix.mulVec_mulVec, hc, Matrix.mulVec_smul]
      have hw0 : w ≠ 0 := by
        intro h0
        have := congrArg (fun v => ((A⁻¹ : GL (Fin 5) (ZMod 2)) :
          Matrix (Fin 5) (Fin 5) (ZMod 2)) *ᵥ v) h0
        simp only [hw, Matrix.mulVec_mulVec, hAinv, Matrix.one_mulVec, Matrix.mulVec_zero] at this
        have h1 := congrFun this 4
        simp [he4] at h1
      apply hw0
      funext l
      set k : Fin 5 := if l = 0 then 1 else 0 with hk
      have hkl : k ≠ l := by
        rw [hk]
        split_ifs with h
        · rw [h]; decide
        · exact Ne.symm h
      have hk3 : (k : ℕ) ≤ 3 := by
        rw [hk]
        split_ifs <;> decide
      have hmem : SpecialLinearGroup.transvection hkl (1 : ZMod 2) ∈
          flagStabilizer 5 (ZMod 2) {4} := by
        refine transvection_mem_flag hkl fun d hd => ?_
        rw [Set.mem_singleton_iff] at hd
        subst hd
        omega
      obtain ⟨c, hc⟩ := hw2 _ hmem
      rw [transvection_mulVec] at hc
      exact eq_zero_of_add_single hkl hc

end Inner


omit [Finite A] in
theorem exists_sl_quotient {K : Subgroup A}
    (hfam : IsAlt 8 (↥K ⧸ Subgroup.center ↥K) ∨
      ∃ n : ℕ, (n = 4 ∨ n = 5) ∧ IsPSL n 2 1 (↥K ⧸ Subgroup.center ↥K)) :
    ∃ n : ℕ, (n = 4 ∨ n = 5) ∧ (n = 5 → IsPSL 5 2 1 (↥K ⧸ Subgroup.center ↥K)) ∧
      Nonempty ((↥K ⧸ Subgroup.center ↥K) ≃* SpecialLinearGroup (Fin n) (ZMod 2)) := by
  rcases hfam with h8 | ⟨n, hn, h⟩
  · obtain ⟨e⟩ := h8
    obtain ⟨φ, -⟩ := exists_iso_alt8_carm
    exact ⟨4, Or.inl rfl, fun h => absurd h (by norm_num), ⟨(e.trans φ).trans (glEquivSL 4)⟩⟩
  · obtain ⟨e⟩ := CFSG.RankThree.PartOne.Sec109.exists_mulEquiv_sl_two h
    exact ⟨n, hn, fun h5 => by subst h5; exact h, ⟨e⟩⟩

theorem levi_l45 {K Y : Subgroup A} (hq : CFSG.Open.IsQuasisimple ↥K)
    (hZ : IsPGroup 2 ↥(centerOf K)) (hL52 : SchurMult2L52)
    (hfam : IsAlt 8 (↥K ⧸ Subgroup.center ↥K) ∨
      ∃ n : ℕ, (n = 4 ∨ n = 5) ∧ IsPSL n 2 1 (↥K ⧸ Subgroup.center ↥K))
    (hpar : IsParabolic2 K Y) (hne : Y ≠ K) (hX0 : perfectCore Y ≠ ⊥) : LeviConcl K Y := by
  classical
  have hK2 : Nat.card (ZMod 2) = 2 := Nat.card_zmod 2
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨n, hn, h5, ⟨e⟩⟩ := exists_sl_quotient hfam
  set ψ : ↥K →* SpecialLinearGroup (Fin n) (ZMod 2) :=
    e.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center ↥K)) with hψ
  have hψker : ψ.ker = Subgroup.center ↥K := by
    ext x
    rw [MonoidHom.mem_ker]
    simp only [hψ, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulEquiv.map_eq_one_iff,
      QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
  have hψs : Function.Surjective ψ := e.surjective.comp (QuotientGroup.mk'_surjective _)
  obtain ⟨g₀, I, a, m, h, hm3, ha, hb, hno, hIc, hprop, hQ, hM⟩ :=
    exists_flag_cover hZ (by omega) (by omega) ψ hψker.le hψs hpar hne hX0
  set θ := (MulAut.conj g₀⁻¹).toMonoidHom.comp ψ with hθ
  have hθker : θ.ker = Subgroup.center ↥K := by rw [hθ, ker_conj_comp, hψker]
  have := sl_isSimple_of_card_two hK2 hm3
  have hM' : img θ (perfectCore Y) =
      (perfectCore (flagStabilizer n (ZMod 2) I)).map
        (MonoidHom.id (SpecialLinearGroup (Fin n) (ZMod 2))) := by
    rw [Subgroup.map_id]
    exact hM
  obtain ⟨hc, ⟨eT⟩⟩ := levi_of_model hZ hpar.1 θ hθker.le
    (MonoidHom.id (SpecialLinearGroup (Fin n) (ZMod 2))) (fun _ _ _ _ h => h) hM'
    (sl_nonabelian_of_card_two hK2 hm3) (bigBlockHom (K := ZMod 2) I a m h ha hb)
    (bigBlockHom_surjective hK2 h hm3 ha hb hno)
    (isPGroup_ker_bigBlockHom (by omega) (by omega) h hm3 ha hb hno)
    (exists_noncomm_flag h hm3 ha hb hno hprop)
  have hpsl : IsPSL m 2 1 (ModO2 (perfectCore Y)) := isPSL_of_mulEquiv_sl hm3 eT
  rcases (by omega : m = 3 ∨ (m = 4 ∧ n = 5)) with rfl | ⟨rfl, rfl⟩
  · exact leviConcl_of_small hc (Or.inr (Or.inr hpsl))
  have hc0 : Subgroup.center ↥K = ⊥ := hL52 ↥K hq (isPGroup_center hZ) (h5 rfl)
  have hθbij : Function.Bijective θ := by
    refine ⟨?_, (MulAut.conj g₀⁻¹).surjective.comp hψs⟩
    rw [← MonoidHom.ker_eq_bot_iff, hθker, hc0]
  obtain ⟨c, hc14, hI⟩ : ∃ c : ℕ, (c = 1 ∨ c = 4) ∧ I = {c} := by
    rcases Nat.eq_zero_or_pos a with rfl | hapos
    · refine ⟨4, Or.inr rfl, ?_⟩
      ext d
      refine ⟨fun hd => ?_, fun hd => ?_⟩
      · have := hIc d hd
        have := hno d hd
        show d = 4
        omega
      · rw [hd]
        rcases hb with hb | hb
        · omega
        · simpa using hb
    · refine ⟨1, Or.inl rfl, ?_⟩
      ext d
      refine ⟨fun hd => ?_, fun hd => ?_⟩
      · have := hIc d hd
        have := hno d hd
        show d = 1
        omega
      · rw [hd]
        rcases ha with ha | ha
        · omega
        · have ha1 : a = 1 := by omega
          rw [ha1] at ha
          exact ha
  subst hI
  have hmax : IsMaxParabolic2 K Y := isMaxParabolic2_of_flag hc0 θ hθbij hpar hne
    (by rcases hc14 with rfl | rfl <;> omega) hQ
  refine ⟨hc, Or.inr (Or.inr (Or.inr hpsl)), fun _ => ⟨h5 rfl, hmax, ?_⟩⟩
  rintro t ⟨htK, htY⟩
  let ct : ↥K →* ↥K :=
    { toFun := fun x => ⟨t * x * t⁻¹, (Subgroup.mem_normalizer_iff.1 htK x).1 x.2⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun x y => Subtype.ext (by simp only [Subgroup.coe_mul]; group) }
  have hct : ∀ x : ↥K, ((ct x : ↥K) : A) = t * x * t⁻¹ := fun x => rfl
  set θe : ↥K ≃* SpecialLinearGroup (Fin 5) (ZMod 2) := MulEquiv.ofBijective θ hθbij with hθe
  have hsym : ∀ y : ↥K, θe.symm (θ y) = y := fun y => θe.symm_apply_apply y
  let β₀ : SpecialLinearGroup (Fin 5) (ZMod 2) →* SpecialLinearGroup (Fin 5) (ZMod 2) :=
    θ.comp (ct.comp θe.symm.toMonoidHom)
  have hβ₀ : ∀ y : ↥K, β₀ (θ y) = θ (ct y) := fun y => by
    show θ (ct (θe.symm (θ y))) = θ (ct y)
    rw [hsym]
  have hβinj : Function.Injective β₀ := by
    intro u v huv
    have h1 : ct (θe.symm u) = ct (θe.symm v) := hθbij.1 huv
    have h2 := congrArg Subtype.val h1
    rw [hct, hct] at h2
    have h3 : θe.symm u = θe.symm v := Subtype.ext (by simpa using h2)
    exact θe.symm.injective h3
  obtain ⟨β, hβdef⟩ : ∃ β : MulAut (SpecialLinearGroup (Fin 5) (ZMod 2)), ∀ s, β s = β₀ s :=
    ⟨MulEquiv.ofBijective β₀ ⟨hβinj, Finite.injective_iff_surjective.1 hβinj⟩, fun _ => rfl⟩
  have hβY : (flagStabilizer 5 (ZMod 2) {c}).map β.toMonoidHom =
      flagStabilizer 5 (ZMod 2) {c} := by
    rw [← hQ]
    refine Subgroup.eq_of_le_of_card_ge ?_ (Subgroup.card_map_of_injective β.injective).ge
    rintro _ ⟨_, ⟨y, hy, rfl⟩, rfl⟩
    refine ⟨ct y, (show ((ct y : ↥K) : A) ∈ Y from ?_), ?_⟩
    swap
    · show θ (ct y) = β (θ y)
      rw [hβdef, hβ₀]
    rw [hct]
    exact (Subgroup.mem_normalizer_iff.1 htY y).1 (Subgroup.mem_subgroupOf.1 hy)
  obtain ⟨B, hB⟩ := exists_inner_of_flag hc14 β hβY
  refine ⟨((θe.symm B : ↥K) : A), (θe.symm B).2, fun x hx => ?_⟩
  have hkey : θ (ct ⟨x, hx⟩) = θ (θe.symm B * ⟨x, hx⟩ * (θe.symm B)⁻¹) := by
    have h1 : β (θ ⟨x, hx⟩) = B * θ ⟨x, hx⟩ * B⁻¹ := hB _
    have h2 : β (θ ⟨x, hx⟩) = θ (ct ⟨x, hx⟩) := by rw [hβdef, hβ₀]
    rw [← h2, h1, map_mul, map_mul, map_inv]
    have h3 : θ (θe.symm B) = B := θe.apply_symm_apply B
    rw [h3]
  have h4 := congrArg Subtype.val (hθbij.1 hkey)
  rw [hct] at h4
  simp only [Subgroup.coe_mul, Subgroup.coe_inv] at h4
  rw [h4, inv_mul_cancel]
  exact (centerOf K).one_mem

end CFSG.Quasithin.C35Levi
