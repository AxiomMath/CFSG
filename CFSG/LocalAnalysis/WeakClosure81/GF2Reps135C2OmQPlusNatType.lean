module

public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2OmPlusNat
import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2OmQPlusNatTypePart1

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.LieType.Universal.Spin CFSG.Quasithin.SmithCurtis CFSG.LieType.Steinberg
open scoped Matrix

variable {F : Type} [Field F] [Finite F] [CharP F 2] {k : Type} [Field k] [CharP k 2]

private theorem c2slomqnt_torus {n : ℕ} (hn : 3 ≤ n) (τ : F →+* k) :
    ∀ h ∈ (omPlusCurtisDatum n F hn).H,
      (omPlusNatRep n τ) h (Pi.single (Sum.inl (⟨0, by omega⟩ : Fin n)) (1 : k)) =
        τ ((spinMatrix (quadPlus n F) h : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F)
          (Sum.inl (⟨0, by omega⟩ : Fin n)) (Sum.inl (⟨0, by omega⟩ : Fin n))) •
        Pi.single (Sum.inl (⟨0, by omega⟩ : Fin n)) (1 : k) := by
  classical
  intro h hh
  let C : spinGroup (quadPlus n F) → Prop := fun g =>
    (∀ a : Fin n ⊕ Fin n, a ≠ Sum.inl (⟨0, by omega⟩ : Fin n) →
      (spinMatrix (quadPlus n F) g : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F)
        a (Sum.inl (⟨0, by omega⟩ : Fin n)) = 0) ∧
    ((omPlusNatRep n τ) g (Pi.single (Sum.inl (⟨0, by omega⟩ : Fin n)) (1 : k)) =
      τ ((spinMatrix (quadPlus n F) g : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F)
        (Sum.inl (⟨0, by omega⟩ : Fin n)) (Sum.inl (⟨0, by omega⟩ : Fin n))) •
      Pi.single (Sum.inl (⟨0, by omega⟩ : Fin n)) (1 : k))
  have hC : ∀ g ∈ (omPlusCurtisDatum n F hn).H, C g := by
    intro g hg
    rw [omPlusCurtisDatum_H] at hg
    refine Subgroup.iSup_induction (fun j => (torusD F hn j).range) (C := C) hg ?_ ?_ ?_
    · intro j x hx
      obtain ⟨t, rfl⟩ := hx
      have hMv : (spinMatrix (quadPlus n F) (torusD F hn j t) :
            Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) *ᵥ
          (Pi.single (Sum.inl (⟨0, by omega⟩ : Fin n)) (1 : F)) =
          (((t ^ longCoroot (rootIdxD n j) (rootIdxD' n j) true (rootSignD n j)
            (⟨0, by omega⟩ : Fin n) true : Fˣ) : F)) •
          (Pi.single (Sum.inl (⟨0, by omega⟩ : Fin n)) (1 : F)) := by
        have h := spinMatrix_mulVec (quadPlus n F) (torusD F hn j t)
          (plusVec n F (⟨0, by omega⟩ : Fin n) true)
        rw [spinAction_torusD] at h
        simpa only [plusVec_true] using h
      have hcol : ∀ a : Fin n ⊕ Fin n, a ≠ Sum.inl (⟨0, by omega⟩ : Fin n) →
          (spinMatrix (quadPlus n F) (torusD F hn j t) :
            Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F)
            a (Sum.inl (⟨0, by omega⟩ : Fin n)) = 0 := by
        intro a ha
        have h := congrFun hMv a
        rw [Matrix.mulVec_single_one, Matrix.col_apply, Pi.smul_apply, Pi.single_apply,
          if_neg ha, smul_zero] at h
        exact h
      refine ⟨hcol, ?_⟩
      rw [c2slomqnt_rep_apply, Matrix.mulVec_single_one]
      ext a
      rw [Matrix.col_apply, Matrix.map_apply, Pi.smul_apply, Pi.single_apply]
      by_cases ha : a = Sum.inl (⟨0, by omega⟩ : Fin n)
      · subst ha; simp
      · rw [hcol a ha, map_zero, if_neg ha, smul_zero]
    · refine ⟨?_, ?_⟩
      · intro a ha
        simp [map_one, Matrix.one_apply, ha]
      · simp [map_one, Matrix.one_apply]
    · intro x y hx hy
      obtain ⟨hxcol, hxval⟩ := hx
      obtain ⟨hycol, hyval⟩ := hy
      have hmul : (spinMatrix (quadPlus n F) (x * y) :
            Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) =
          (spinMatrix (quadPlus n F) x : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) *
          (spinMatrix (quadPlus n F) y : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) := by
        rw [map_mul, Units.val_mul]
      have hdiag : (spinMatrix (quadPlus n F) (x * y) :
            Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F)
            (Sum.inl (⟨0, by omega⟩ : Fin n)) (Sum.inl (⟨0, by omega⟩ : Fin n)) =
          (spinMatrix (quadPlus n F) x : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F)
            (Sum.inl (⟨0, by omega⟩ : Fin n)) (Sum.inl (⟨0, by omega⟩ : Fin n)) *
          (spinMatrix (quadPlus n F) y : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F)
            (Sum.inl (⟨0, by omega⟩ : Fin n)) (Sum.inl (⟨0, by omega⟩ : Fin n)) := by
        rw [hmul, Matrix.mul_apply,
          Finset.sum_eq_single (Sum.inl (⟨0, by omega⟩ : Fin n))
            (fun b _ hb => by rw [hycol b hb, mul_zero])
            (fun h => absurd (Finset.mem_univ _) h)]
      refine ⟨?_, ?_⟩
      · intro a ha
        rw [hmul, Matrix.mul_apply,
          Finset.sum_eq_single (Sum.inl (⟨0, by omega⟩ : Fin n))
            (fun b _ hb => by rw [hycol b hb, mul_zero])
            (fun h => absurd (Finset.mem_univ _) h)]
        simp only [hxcol a ha, zero_mul]
      · rw [map_mul, Module.End.mul_apply, hyval, map_smul, hxval, smul_smul, hdiag, map_mul,
          mul_comm]
  exact (hC h hh).2

private theorem c2slomqnt_hecke {n : ℕ} (hn : 3 ≤ n) (hF : 2 < Nat.card F) (τ : F →+* k)
    (s : Fin n) :
    (omPlusCurtisDatum n F hn).heckeT (omPlusNatRep n τ) s
      (Pi.single (Sum.inl (⟨0, by omega⟩ : Fin n)) (1 : k)) = 0 := by
  classical
  haveI : Fintype F := Fintype.ofFinite F
  have : Fintype ((omPlusCurtisDatum n F hn).X s) := Fintype.ofFinite _
  have hcardF : (Fintype.card F : k) = 0 := by
    obtain ⟨f, -, hf⟩ := FiniteField.card F 2
    refine (CharP.cast_eq_zero_iff k 2 (Fintype.card F)).mpr ?_
    rw [hf]
    exact dvd_pow_self 2 (PNat.ne_zero f)
  have hsumF : (∑ c : F, c) = 0 := by
    have h := FiniteField.sum_pow_lt_card_sub_one F 1 (by
      rw [← Nat.card_eq_fintype_card]; omega)
    simpa using h
  have hsumτ : (∑ c : F, τ c) = 0 := by rw [← map_sum, hsumF, map_zero]
  erw [CurtisDatum.heckeT_apply (omPlusCurtisDatum n F hn)]
  rw [← (c2slomqnt_XEquiv_bijective (F := F) hn s).sum_comp]
  simp only [omPlusCurtisDatum_n]
  by_cases hs0 : s.val = 0
  · have hs : s = (⟨0, by omega⟩ : Fin n) := Fin.ext hs0
    have hterm : ∀ c : F, (omPlusNatRep n τ)
        (rootD F hn s (.ofAdd c) * weylD F hn s)
        (Pi.single (Sum.inl (⟨0, by omega⟩ : Fin n)) (1 : k)) =
        Pi.single (Sum.inl (⟨1, by omega⟩ : Fin n)) (1 : k) +
          τ c • Pi.single (Sum.inl (⟨0, by omega⟩ : Fin n)) (1 : k) := by
      intro c
      rw [hs, map_mul, Module.End.mul_apply, c2slomqnt_weylD_zero_e0 hn τ,
        c2slomqnt_rootD_zero_e1 hn τ c]
    simp_rw [hterm]
    rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
      ← Nat.cast_smul_eq_nsmul k, hcardF, ← Finset.sum_smul, hsumτ]
    simp
  · have hterm : ∀ c : F, (omPlusNatRep n τ)
        (rootD F hn s (.ofAdd c) * weylD F hn s)
        (Pi.single (Sum.inl (⟨0, by omega⟩ : Fin n)) (1 : k)) =
        Pi.single (Sum.inl (⟨0, by omega⟩ : Fin n)) (1 : k) := by
      intro c
      rw [map_mul, Module.End.mul_apply, c2slomqnt_weylD_ne_zero_e0 hn hs0 τ,
        c2slomqnt_rootD_ne_zero_e0 hn hs0 τ c]
    simp_rw [hterm]
    rw [Finset.sum_const, Finset.card_univ, ← Nat.cast_smul_eq_nsmul k, hcardF]
    simp

theorem omq_isCurtisType_omPlus_natural {n : ℕ} (hn : 3 ≤ n) {F : Type} [Field F] [Finite F]
    [CharP F 2] (hF : 2 < Nat.card F) {k : Type} [Field k] [CharP k 2] (τ : F →+* k) :
    (omPlusCurtisDatum n F hn).IsCurtisType (omPlusNatRep n τ)
      (Pi.single (Sum.inl (⟨0, by omega⟩ : Fin n)) (1 : k))
      (fun g => τ ((spinMatrix (quadPlus n F) g : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F)
        (Sum.inl ⟨0, by omega⟩) (Sum.inl ⟨0, by omega⟩))) 0 := by
  refine ⟨c2slomqnt_fixU hn τ, Pi.single_ne_zero_iff.mpr one_ne_zero, ?_, ?_⟩
  · intro h hh
    exact c2slomqnt_torus hn τ h hh
  · intro s
    simpa using c2slomqnt_hecke hn hF τ s

end CFSG.LocalAnalysis.WeakClosure81
