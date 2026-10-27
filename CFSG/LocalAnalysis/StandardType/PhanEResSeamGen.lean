module

public import CFSG.LocalAnalysis.StandardType.PhanEResSL
public import CFSG.LocalAnalysis.StandardType.PhanEStdSetting

public section

namespace CFSG.ClassicalInvolution.Phan.PhanE.Res

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LieType.Universal CFSG.LieType.CurtisTits
  CFSG.LieType.RootSystem
  CFSG.LieType.Steinberg CFSG.LieType.Chevalley.CosetBuilding CFSG.Monster.B.Geometry
  CFSG.ClassicalInvolution.Phan.PhanE CFSG.ClassicalInvolution.Phan.PhanE.Flag
  CFSG.LieType.Steinberg.CentralExt.SLClosed CFSG.AGLEmbeddingD2.ParabLevi

open scoped commutatorElement

private theorem hmbSM_hchain_mem {F : Type} [Field F] {m : ℕ}
    {T : Subgroup (SpecialLinearGroup (Fin (m + 1)) F)}
    {a b : SpecialLinearGroup (Fin (m + 1)) F} (ha : a ∈ T) (hb : b ∈ T) :
    ⁅a, b⁆ ∈ T := by
  rw [commutatorElement_def]
  exact T.mul_mem (T.mul_mem (T.mul_mem ha hb) (T.inv_mem ha)) (T.inv_mem hb)

private theorem hmbSM_tv_mem_closure_upper {F : Type} [Field F] {m : ℕ}
    (T : Subgroup (SpecialLinearGroup (Fin (m + 1)) F))
    (hgen : ∀ k : Fin m, ∀ c : F,
      tv F k.castSucc k.succ c ∈ T ∧ tv F k.succ k.castSucc c ∈ T) :
    ∀ (i j : Fin (m + 1)), i < j → ∀ c : F, tv F i j c ∈ T := by
  have H : ∀ d : ℕ, ∀ (i j : Fin (m + 1)), i < j → j.val - i.val = d →
      ∀ c : F, tv F i j c ∈ T := by
    intro d
    induction d using Nat.strong_induction_on with
    | _ d ih =>
      intro i j hij hd c
      by_cases hstep : j.val = i.val + 1
      · have hm : i.val < m := by omega
        have hk : (⟨i.val, hm⟩ : Fin m).castSucc = i := by ext; simp
        have hk' : (⟨i.val, hm⟩ : Fin m).succ = j := by
          ext; simp [Fin.val_succ]; omega
        rw [← hk, ← hk']
        exact (hgen ⟨i.val, hm⟩ c).1
      · have hlt : (i.val + 1) < m + 1 := by omega
        let p : Fin (m + 1) := ⟨i.val + 1, hlt⟩
        have hip : i < p := by simp [p, Fin.lt_def]
        have hpj : p < j := by simp [p, Fin.lt_def]; omega
        have hpm : i.val < m := by omega
        have hkp : (⟨i.val, hpm⟩ : Fin m).castSucc = i := by ext; simp
        have hkp' : (⟨i.val, hpm⟩ : Fin m).succ = p := by
          ext; simp [Fin.val_succ, p]
        have h1 : tv F i p c ∈ T := by
          rw [← hkp, ← hkp']; exact (hgen ⟨i.val, hpm⟩ c).1
        have h2 : tv F p j 1 ∈ T :=
          ih (j.val - p.val) (by simp [p] at hd ⊢; omega) p j hpj rfl 1
        have hchain := tv_chain (F := F) (i := i) (j := p) (l := j)
          (ne_of_lt hip) (ne_of_lt hpj) (ne_of_lt (lt_trans hip hpj)) c 1
        rw [mul_one] at hchain
        rw [← hchain]
        exact hmbSM_hchain_mem h1 h2
  intro i j hij c
  exact H (j.val - i.val) i j hij rfl c

private theorem hmbSM_tv_mem_closure_lower {F : Type} [Field F] {m : ℕ}
    (T : Subgroup (SpecialLinearGroup (Fin (m + 1)) F))
    (hgen : ∀ k : Fin m, ∀ c : F,
      tv F k.castSucc k.succ c ∈ T ∧ tv F k.succ k.castSucc c ∈ T) :
    ∀ (i j : Fin (m + 1)), j < i → ∀ c : F, tv F i j c ∈ T := by
  have H : ∀ d : ℕ, ∀ (i j : Fin (m + 1)), j < i → i.val - j.val = d →
      ∀ c : F, tv F i j c ∈ T := by
    intro d
    induction d using Nat.strong_induction_on with
    | _ d ih =>
      intro i j hji hd c
      by_cases hstep : i.val = j.val + 1
      · have hm : j.val < m := by omega
        have hk : (⟨j.val, hm⟩ : Fin m).castSucc = j := by ext; simp
        have hk' : (⟨j.val, hm⟩ : Fin m).succ = i := by
          ext; simp [Fin.val_succ]; omega
        rw [← hk, ← hk']
        exact (hgen ⟨j.val, hm⟩ c).2
      · have hlt : (j.val + 1) < m + 1 := by omega
        let p : Fin (m + 1) := ⟨j.val + 1, hlt⟩
        have hjp : j < p := by simp [p, Fin.lt_def]
        have hpi : p < i := by simp [p, Fin.lt_def]; omega
        have hpm : j.val < m := by omega
        have hkp : (⟨j.val, hpm⟩ : Fin m).castSucc = j := by ext; simp
        have hkp' : (⟨j.val, hpm⟩ : Fin m).succ = p := by
          ext; simp [Fin.val_succ, p]
        have h1 : tv F p j 1 ∈ T := by
          rw [← hkp, ← hkp']; exact (hgen ⟨j.val, hpm⟩ 1).2
        have h2 : tv F i p c ∈ T :=
          ih (i.val - p.val) (by simp [p] at hd ⊢; omega) i p hpi rfl c
        have hchain := tv_chain (F := F) (i := i) (j := p) (l := j)
          (ne_of_gt hpi) (ne_of_gt hjp) (ne_of_lt (lt_trans hjp hpi)).symm c 1
        rw [mul_one] at hchain
        rw [← hchain]
        exact hmbSM_hchain_mem h2 h1
  intro i j hji c
  exact H (i.val - j.val) i j hji rfl c

private theorem hmbSM_tv_mem_closure {F : Type} [Field F] {m : ℕ}
    (T : Subgroup (SpecialLinearGroup (Fin (m + 1)) F))
    (hgen : ∀ k : Fin m, ∀ c : F,
      tv F k.castSucc k.succ c ∈ T ∧ tv F k.succ k.castSucc c ∈ T) :
    ∀ (i j : Fin (m + 1)), i ≠ j → ∀ c : F, tv F i j c ∈ T := by
  intro i j hij c
  rcases lt_or_gt_of_ne hij with h | h
  · exact hmbSM_tv_mem_closure_upper T hgen i j h c
  · exact hmbSM_tv_mem_closure_lower T hgen i j h c

private theorem hmbSM_closure_simple_eq_top {F : Type} [Field F] {m : ℕ} :
    Subgroup.closure {A : SpecialLinearGroup (Fin (m + 1)) F | ∃ k : Fin m, ∃ c : F,
      A = tv F k.castSucc k.succ c ∨ A = tv F k.succ k.castSucc c} = ⊤ := by
  let T : Subgroup (SpecialLinearGroup (Fin (m + 1)) F) :=
    Subgroup.closure {A | ∃ k : Fin m, ∃ c : F,
      A = tv F k.castSucc k.succ c ∨ A = tv F k.succ k.castSucc c}
  have hgen : ∀ k : Fin m, ∀ c : F,
      tv F k.castSucc k.succ c ∈ T ∧ tv F k.succ k.castSucc c ∈ T := by
    intro k c
    exact ⟨Subgroup.subset_closure ⟨k, c, Or.inl rfl⟩,
      Subgroup.subset_closure ⟨k, c, Or.inr rfl⟩⟩
  have htv : ∀ (i j : Fin (m + 1)), i ≠ j → ∀ c : F, tv F i j c ∈ T :=
    hmbSM_tv_mem_closure T hgen
  rw [eq_top_iff]
  intro A _
  by_cases hm : m = 0
  · subst hm
    haveI : Subsingleton (SpecialLinearGroup (Fin (0 + 1)) F) := by
      refine ⟨fun a b => Subtype.ext ?_⟩
      have ha : (a : Matrix (Fin (0 + 1)) (Fin (0 + 1)) F) = 1 := by
        ext i j
        fin_cases i; fin_cases j
        have h := a.2
        rw [Matrix.det_fin_one] at h
        simpa using h
      have hb : (b : Matrix (Fin (0 + 1)) (Fin (0 + 1)) F) = 1 := by
        ext i j
        fin_cases i; fin_cases j
        have h := b.2
        rw [Matrix.det_fin_one] at h
        simpa using h
      rw [ha, hb]
    rw [Subsingleton.elim A 1]
    exact T.one_mem
  · haveI : Nontrivial (Fin (m + 1)) := by
      rw [Fin.nontrivial_iff_two_le]; omega
    refine SpecialLinearGroup.diagonal_transvection_induction' (fun x => x ∈ T) A ?_ ?_ ?_
    · intro i j hij c hc
      rw [SpecialLinearGroup.diag2n_decompose hij c hc]
      refine T.mul_mem (T.mul_mem (T.mul_mem (T.mul_mem (T.mul_mem ?_ ?_) ?_) ?_) ?_) ?_
      · simpa [tv_of_ne hij] using htv i j hij c
      · simpa [tv_of_ne hij.symm] using htv j i hij.symm (-c⁻¹)
      · simpa [tv_of_ne hij] using htv i j hij c
      · simpa [tv_of_ne hij] using htv i j hij (-1)
      · simpa [tv_of_ne hij.symm] using htv j i hij.symm 1
      · simpa [tv_of_ne hij] using htv i j hij (-1)
    · intro i j hij c
      simpa [tv_of_ne hij] using htv i j hij c
    · intro a b ha hb
      exact T.mul_mem ha hb

theorem sl_hom_ext_simple {F G : Type} [Field F] [Group G] {m : ℕ}
    {f f' : SpecialLinearGroup (Fin (m + 1)) F →* G}
    (hu : ∀ (k : Fin m) (c : F), f (tv F k.castSucc k.succ c) = f' (tv F k.castSucc k.succ c))
    (hl : ∀ (k : Fin m) (c : F), f (tv F k.succ k.castSucc c) = f' (tv F k.succ k.castSucc c)) :
    f = f' := by
  let T : Subgroup (SpecialLinearGroup (Fin (m + 1)) F) :=
    Subgroup.closure {A | ∃ k : Fin m, ∃ c : F,
      A = tv F k.castSucc k.succ c ∨ A = tv F k.succ k.castSucc c}
  have hT : T = ⊤ := hmbSM_closure_simple_eq_top
  have key : ∀ A ∈ T, f A = f' A := by
    intro A hA
    induction hA using Subgroup.closure_induction with
    | mem x hx =>
      rcases hx with ⟨k, c, h | h⟩
      · rw [h]; exact hu k c
      · rw [h]; exact hl k c
    | one => simp
    | mul x y hx hy ihx ihy => rw [map_mul, map_mul, ihx, ihy]
    | inv x hx ih => rw [map_inv, map_inv, ih]
  ext A
  exact key A (by rw [hT]; exact Subgroup.mem_top A)

@[expose] def blockSL (Fld : Type) [Field Fld] (m : ℕ) (d : List ℕ) :
    Subgroup (SpecialLinearGroup (Fin (m + 1)) Fld) :=
  Subgroup.closure {A | ∃ k : Fin m, k ∈ cutTypes m d ∧ ∃ c : Fld,
    A = tv Fld k.castSucc k.succ c ∨ A = tv Fld k.succ k.castSucc c}

@[expose] def kapMat {Fld : Type} [Field Fld] {m : ℕ} (θ : Fld →+* Fld) (pol : Bool)
    (P : SpecialLinearGroup (Fin (m + 1)) Fld) :
    SpecialLinearGroup (Fin (m + 1)) Fld →* SpecialLinearGroup (Fin (m + 1)) Fld :=
  (MulAut.conj P).toMonoidHom.comp
    (if pol then slSigma θ (m + 1) else SpecialLinearGroup.map θ)

section Matrices

variable {Fld : Type} [Field Fld] {m : ℕ}

theorem hmbSM_castSucc_ne_succ {m : ℕ} (k : Fin m) : k.castSucc ≠ k.succ := by
  intro hh
  have h := congrArg Fin.val hh
  simp only [Fin.val_castSucc, Fin.val_succ] at h
  omega

theorem pathRoot_castSucc_succ {r : ℕ} (e : Fin m → Fin r) (k : Fin m) :
    pathRoot e k.castSucc k.succ = Pi.single (e k) 1 := by
  unfold pathRoot
  rw [if_pos (by simp [Fin.lt_def])]
  rw [Fintype.sum_eq_single k]
  · simp
  · intro j hj
    have hne : ¬ (k.val ≤ j.val ∧ j.val < k.val + 1) := by
      rintro ⟨h1, h2⟩
      exact hj (Fin.ext (by omega))
    simp only [Fin.val_castSucc, Fin.val_succ]
    rw [if_neg hne]

theorem pathRoot_succ_castSucc {r : ℕ} (e : Fin m → Fin r) (k : Fin m) :
    pathRoot e k.succ k.castSucc = -Pi.single (e k) 1 := by
  unfold pathRoot
  rw [if_neg (by simp [Fin.lt_def])]
  rw [Fintype.sum_eq_single k]
  · simp
  · intro j hj
    have hne : ¬ (k.val ≤ j.val ∧ j.val < k.val + 1) := by
      rintro ⟨h1, h2⟩
      exact hj (Fin.ext (by omega))
    simp only [Fin.val_castSucc, Fin.val_succ]
    rw [if_neg hne]

end Matrices

end CFSG.ClassicalInvolution.Phan.PhanE.Res

end
