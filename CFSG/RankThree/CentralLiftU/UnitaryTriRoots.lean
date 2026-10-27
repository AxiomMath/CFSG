module

public import CFSG.RankThree.CentralLiftU.UnitaryTriBasic
public import CFSG.RankThree.CentralLiftU.UnitaryHeis
public import CFSG.RankThree.CentralLiftU.UnitaryWeyl

public section

namespace CFSG.RankThree.CentralLiftU

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.ClassicalGroups.UnitaryFlag
open CFSG.LocalAnalysis.ComponentInitial.SymplecticTorusWeyl (IsLinePerm)
open CFSG.LieType.Chevalley (uSL vSL coe_uSL coe_vSL)

variable {ℓ f : ℕ} {K : Type} [Field K] {h : UnitaryFieldData ℓ f K} {r ε : ℕ}

section Order

theorem val_swap (i j x : Fin r) :
    (Equiv.swap i j x).val =
      if x.val = i.val then j.val else if x.val = j.val then i.val else x.val := by
  rw [Equiv.swap_apply_def]
  split_ifs with h1 h2 h3 h4 h5 <;> simp_all [Fin.ext_iff]

theorem swapIdx_order {i j : Fin r} (hj : j.val = i.val + 1) {a b : HypIndex r ε}
    (hab : fullPos a < fullPos b) (hba : fullPos (swapIdx i j b) < fullPos (swapIdx i j a)) :
    (a = .inl i ∧ b = .inl j) ∨ (a = .inr (.inr j) ∧ b = .inr (.inr i)) := by
  have hi := i.isLt
  rcases a with a | k | a <;> rcases b with b | l | b <;>
    simp only [swapIdx_inl, swapIdx_z, swapIdx_inr, fullPos_inl, fullPos_inr_inl,
      fullPos_inr_inr, val_swap, Sum.inl.injEq, Sum.inr.injEq, reduceCtorEq, false_and,
      or_false, false_or, Fin.ext_iff] at hab hba ⊢ <;>
    (try have := a.isLt) <;> (try have := b.isLt) <;> (try have := k.isLt) <;>
    (try have := l.isLt) <;> (try split_ifs at hba) <;> omega

theorem swap_last_order {i : Fin r} (hi : ¬i.val + 1 < r) {a b : HypIndex r ε}
    (hab : fullPos a < fullPos b)
    (hba : fullPos (Equiv.swap (.inl i) (.inr (.inr i)) b) <
      fullPos (Equiv.swap (.inl i) (.inr (.inr i)) a)) :
    (a = .inl i ∧ (b = .inr (.inr i) ∨ ∃ k, b = .inr (.inl k))) ∨
      ((∃ k, a = .inr (.inl k)) ∧ b = .inr (.inr i)) := by
  have hir : i.val + 1 = r := by have := i.isLt; omega
  have hp1 : fullPos (.inl i : HypIndex r ε) = r - 1 := by simp only [fullPos_inl]; omega
  have hp2 : fullPos (.inr (.inr i) : HypIndex r ε) = r + ε := by
    simp only [fullPos_inr_inr]; omega
  by_cases ha1 : a = .inl i
  · subst ha1
    rw [Equiv.swap_apply_left, hp2] at hba
    by_cases hb2 : b = .inr (.inr i)
    · exact Or.inl ⟨rfl, Or.inl hb2⟩
    · have hb1 : b ≠ .inl i := fun e => by rw [e] at hab; omega
      rw [Equiv.swap_apply_of_ne_of_ne hb1 hb2] at hba
      exact Or.inl ⟨rfl, Or.inr (exists_eq_z_of_between hi hab hba)⟩
  by_cases ha2 : a = .inr (.inr i)
  · subst ha2
    rw [Equiv.swap_apply_right, hp1] at hba
    have hb2 : b ≠ .inr (.inr i) := fun e => by rw [e] at hab; omega
    have hb1 : b ≠ .inl i := fun e => by rw [e, hp1, hp2] at hab; omega
    rw [Equiv.swap_apply_of_ne_of_ne hb1 hb2] at hba
    rw [hp2] at hab
    omega
  rw [Equiv.swap_apply_of_ne_of_ne ha1 ha2] at hba
  by_cases hb1 : b = .inl i
  · subst hb1
    rw [Equiv.swap_apply_left, hp2] at hba
    rw [hp1] at hab
    omega
  by_cases hb2 : b = .inr (.inr i)
  · subst hb2
    rw [Equiv.swap_apply_right] at hba
    exact Or.inr ⟨exists_eq_z_of_between hi hba (by rw [hp2] at hab; exact hab), rfl⟩
  rw [Equiv.swap_apply_of_ne_of_ne hb1 hb2] at hba
  omega

end Order

section Supports

variable (h)

theorem rho4Mat_uSL_offdiag (t : K) (a b : Fin 2 ⊕ Fin 2) (hab : a ≠ b)
    (h0 : rho4Mat h (uSL t) a b ≠ 0) :
    (a = .inl 0 ∧ b = .inl 1) ∨ (a = .inr 1 ∧ b = .inr 0) := by
  rcases a with a | a <;> rcases b with b | b <;> fin_cases a <;> fin_cases b <;>
    simp_all [rho4Mat, coe_uSL, adjugate_fin_two]

theorem rho4Mat_vSL_offdiag (t : K) (a b : Fin 2 ⊕ Fin 2) (hab : a ≠ b)
    (h0 : rho4Mat h (vSL t) a b ≠ 0) :
    (a = .inl 1 ∧ b = .inl 0) ∨ (a = .inr 0 ∧ b = .inr 1) := by
  rcases a with a | a <;> rcases b with b | b <;> fin_cases a <;> fin_cases b <;>
    simp_all [rho4Mat, coe_vSL, adjugate_fin_two]

theorem rho4Mat_uSL_diag (t : K) (a : Fin 2 ⊕ Fin 2) : rho4Mat h (uSL t) a a = 1 := by
  rcases a with a | a <;> fin_cases a <;> simp [rho4Mat, coe_uSL, adjugate_fin_two]

theorem rho4Mat_vSL_diag (t : K) (a : Fin 2 ⊕ Fin 2) : rho4Mat h (vSL t) a a = 1 := by
  rcases a with a | a <;> fin_cases a <;> simp [rho4Mat, coe_vSL, adjugate_fin_two]

end Supports

section Rho

theorem fullPos_weylPerm_partner (hε : ε ≤ 1) {w : Equiv.Perm (Fin r ⊕ Fin r)}
    (hw : w ∈ hypWeyl r) (a : HypIndex r ε) :
    fullPos (weylPerm w (hypPartner a)) = 2 * r + ε - 1 - fullPos (weylPerm w a) := by
  rw [weylPerm_hypPartner hw, fullPos_hypPartner hε]

theorem rhoU_uSL_mem {i j : Fin r} (hij : i ≠ j) (hlt : i.val < j.val) (t : K) :
    rhoU (ε := ε) h hij (uSL t) ∈ hypUnitriangular h r ε := by
  refine mem_hypUnitriangular_of_support (fun x => ?_) fun x y hxy h0 => ?_
  · rw [coe_rhoU]
    exact blockMat_apply_self (quadIdx_injective hij) (rho4Mat_uSL_diag h t) x
  · rw [coe_rhoU] at h0
    obtain ⟨a, b, hab, rfl, rfl, hM⟩ := blockMat_offdiag (quadIdx_injective hij) hxy h0
    have hj := j.isLt
    rcases rho4Mat_uSL_offdiag h t a b hab hM with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · simpa [quadIdx] using hlt
    · simp only [quadIdx, Sum.elim_inr, Matrix.cons_val_one, Matrix.cons_val_zero,
        fullPos_inr_inr]
      omega

theorem coe_rhoU_uSL_apply {i j : Fin r} (hij : i ≠ j) (t : K) :
    ((rhoU (ε := ε) h hij (uSL t) : GL (HypIndex r ε) K) :
      Matrix (HypIndex r ε) (HypIndex r ε) K) (.inl i) (.inl j) = t := by
  rw [coe_rhoU, show (.inl i : HypIndex r ε) = quadIdx i j (.inl 0) from rfl,
    show (.inl j : HypIndex r ε) = quadIdx i j (.inl 1) from rfl,
    blockMat_apply_e (quadIdx_injective hij)]
  simp [rho4Mat, coe_uSL]

theorem exists_rhoU_mul_mem_simpleKerU {i : Fin r} (hi : i.val + 1 < r) {u : hypSU h r ε}
    (hu : u ∈ hypUnitriangular h r ε) :
    ∃ t : K, (rhoU h (ne_succ_of_lt hi) (uSL t))⁻¹ * u ∈ simpleKerU h r ε i := by
  set t := ((u : GL (HypIndex r ε) K) : Matrix (HypIndex r ε) (HypIndex r ε) K) (.inl i)
    (.inl ⟨i.val + 1, hi⟩)
  have hx := rhoU_uSL_mem (ε := ε) (h := h) (ne_succ_of_lt hi) (by simp) t
  refine ⟨t, mul_mem (inv_mem hx) hu, ?_⟩
  rw [simpleCond_of_lt hi, mul_apply_of_adjacent (inv_mem hx) hu (by simp),
    inv_apply_of_adjacent hx (by simp), coe_rhoU_uSL_apply, neg_add_cancel]

theorem conj_rhoU_or (hε : ε ≤ 1) {g : hypSU h r ε} {w : Equiv.Perm (Fin r ⊕ Fin r)}
    (hw : w ∈ hypWeyl r)
    (hg : IsLinePerm (weylPerm (ε := ε) w)
      ((g : GL (HypIndex r ε) K) : Matrix (HypIndex r ε) (HypIndex r ε) K))
    {i j : Fin r} (hij : i ≠ j) :
    (∀ t : K, g * rhoU h hij (uSL t) * g⁻¹ ∈ hypUnitriangular h r ε) ∨
      ∀ t : K, g * rhoU h hij (vSL t) * g⁻¹ ∈ hypUnitriangular h r ε := by
  have hpi := fullPos_weylPerm_partner hε hw (.inl i : HypIndex r ε)
  have hpj := fullPos_weylPerm_partner hε hw (.inl j : HypIndex r ε)
  simp only [hypPartner_inl] at hpi hpj
  have hlt1 := fullPos_lt (weylPerm (ε := ε) w (.inl i))
  have hlt2 := fullPos_lt (weylPerm (ε := ε) w (.inl j))
  have hne : fullPos (weylPerm (ε := ε) w (.inl i)) ≠ fullPos (weylPerm (ε := ε) w (.inl j)) :=
    fun e => hij (Sum.inl_injective ((weylPerm w).injective (fullPos_injective e)))
  rcases Nat.lt_or_gt_of_ne hne with hlt | hlt
  · left
    intro t
    refine conj_mem_hypUnitriangular hg (fun x => ?_) fun x y hxy h0 => ?_
    · rw [coe_rhoU]
      exact blockMat_apply_self (quadIdx_injective hij) (rho4Mat_uSL_diag h t) x
    · rw [coe_rhoU] at h0
      obtain ⟨a, b, hab, rfl, rfl, hM⟩ := blockMat_offdiag (quadIdx_injective hij) hxy h0
      rcases rho4Mat_uSL_offdiag h t a b hab hM with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact hlt
      · change fullPos (weylPerm w (.inr (.inr j))) < fullPos (weylPerm w (.inr (.inr i)))
        omega
  · right
    intro t
    refine conj_mem_hypUnitriangular hg (fun x => ?_) fun x y hxy h0 => ?_
    · rw [coe_rhoU]
      exact blockMat_apply_self (quadIdx_injective hij) (rho4Mat_vSL_diag h t) x
    · rw [coe_rhoU] at h0
      obtain ⟨a, b, hab, rfl, rfl, hM⟩ := blockMat_offdiag (quadIdx_injective hij) hxy h0
      rcases rho4Mat_vSL_offdiag h t a b hab hM with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact hlt
      · change fullPos (weylPerm w (.inr (.inr i))) < fullPos (weylPerm w (.inr (.inr j)))
        omega

end Rho

section Normalize

open CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher (simpleRefl)

theorem fullPos_lt_of_apply_ne_zero {X : hypSU h r ε} (hX : X ∈ hypUnitriangular h r ε)
    {a b : HypIndex r ε} (hab : a ≠ b)
    (h0 : ((X : GL (HypIndex r ε) K) : Matrix (HypIndex r ε) (HypIndex r ε) K) a b ≠ 0) :
    fullPos a < fullPos b := by
  by_contra hle
  rcases Nat.lt_or_ge (fullPos b) (fullPos a) with hlt | hge
  · exact h0 (apply_eq_zero_of_mem hX hlt)
  · exact hab (fullPos_injective (by omega))

theorem apply_partner_eq_bar (X : hypSU h r ε) (a b : HypIndex r ε) :
    ((X : GL (HypIndex r ε) K) : Matrix (HypIndex r ε) (HypIndex r ε) K)
      (hypPartner b) (hypPartner a) =
      h.bar ((((X⁻¹ : hypSU h r ε) : GL (HypIndex r ε) K) :
        Matrix (HypIndex r ε) (HypIndex r ε) K) a b) := by
  rw [inv_apply_eq_bar, h.bar_bar]

theorem conj_mem_simpleKerU_of_isLinePerm {i : Fin r} {g X : hypSU h r ε}
    (hg : IsLinePerm (weylPerm (ε := ε) (simpleRefl r i))
      ((g : GL (HypIndex r ε) K) : Matrix (HypIndex r ε) (HypIndex r ε) K))
    (hX : X ∈ simpleKerU h r ε i) : g * X * g⁻¹ ∈ simpleKerU h r ε i := by
  obtain ⟨hXU, hXc⟩ := hX
  have hdiag := apply_self_of_mem hXU
  by_cases hi : i.val + 1 < r
  · set j : Fin r := ⟨i.val + 1, hi⟩ with hj
    have hσ : weylPerm (ε := ε) (simpleRefl r i) = swapIdx i j := by
      rw [simpleRefl, dite_eq_left hi, weylPerm_sumCongr_swap]
    rw [hσ] at hg
    rw [simpleCond_of_lt hi] at hXc
    have hXc' : ((X : GL (HypIndex r ε) K) : Matrix (HypIndex r ε) (HypIndex r ε) K)
        (.inr (.inr j)) (.inr (.inr i)) = 0 := by
      have e := apply_partner_eq_bar X (.inl i) (.inl j)
      simp only [hypPartner_inl] at e
      rw [e, inv_apply_of_adjacent hXU (by simp [hj]), hXc, neg_zero, map_zero]
    refine ⟨conj_mem_hypUnitriangular hg hdiag fun x y hxy h0 => ?_, ?_⟩
    · have hlt := fullPos_lt_of_apply_ne_zero hXU hxy h0
      by_contra hle
      have hlt' : fullPos (swapIdx i j y) < fullPos (swapIdx i j x) := by
        rcases Nat.lt_or_ge (fullPos (swapIdx i j y)) (fullPos (swapIdx i j x)) with h1 | h1
        · exact h1
        · exact absurd (fullPos_injective (by omega) : swapIdx (ε := ε) i j x = swapIdx i j y)
            fun e => hxy ((swapIdx i j).injective e)
      rcases swapIdx_order (ε := ε) (j := j) rfl hlt hlt' with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact h0 hXc
      · exact h0 hXc'
    · rw [simpleCond_of_lt hi]
      have e := conj_apply_hypSU (X := X) hg (.inl j) (.inl i)
      rw [swapIdx_inl, swapIdx_inl, Equiv.swap_apply_right, Equiv.swap_apply_left] at e
      rw [e, apply_eq_zero_of_mem hXU (by simp [hj]), mul_zero, zero_mul]
  · have hσ : weylPerm (ε := ε) (simpleRefl r i) = Equiv.swap (.inl i) (.inr (.inr i)) := by
      rw [simpleRefl, dite_eq_right hi, weylPerm_swap_inl_inr]
    rw [hσ] at hg
    rw [simpleCond_of_not_lt hi] at hXc
    have hir : i.val + 1 = r := by have := i.isLt; omega
    have hXinv := simpleCond_inv hXU (show SimpleCond i _ from (simpleCond_of_not_lt hi).2 hXc)
    rw [simpleCond_of_not_lt hi] at hXinv
    have hXz : ∀ k, ((X : GL (HypIndex r ε) K) : Matrix (HypIndex r ε) (HypIndex r ε) K)
        (.inr (.inl k)) (.inr (.inr i)) = 0 := by
      intro k
      have e := apply_partner_eq_bar X (.inl i) (.inr (.inl k))
      simp only [hypPartner_inl, hypPartner_inr_inl] at e
      rw [e, hXinv.2 k, map_zero]
    refine ⟨conj_mem_hypUnitriangular hg hdiag fun x y hxy h0 => ?_, ?_⟩
    · have hlt := fullPos_lt_of_apply_ne_zero hXU hxy h0
      by_contra hle
      have hlt' : fullPos (Equiv.swap (.inl i : HypIndex r ε) (.inr (.inr i)) y) <
          fullPos (Equiv.swap (.inl i : HypIndex r ε) (.inr (.inr i)) x) := by
        rcases Nat.lt_or_ge (fullPos (Equiv.swap (.inl i : HypIndex r ε) (.inr (.inr i)) y))
          (fullPos (Equiv.swap (.inl i : HypIndex r ε) (.inr (.inr i)) x)) with h1 | h1
        · exact h1
        · exact absurd (fullPos_injective (by omega)) fun e =>
            hxy ((Equiv.swap (.inl i : HypIndex r ε) (.inr (.inr i))).injective e)
      rcases swap_last_order hi hlt hlt' with ⟨rfl, rfl | ⟨k, rfl⟩⟩ | ⟨⟨k, rfl⟩, rfl⟩
      · exact h0 hXc.1
      · exact h0 (hXc.2 k)
      · exact h0 (hXz k)
    · rw [simpleCond_of_not_lt hi]
      refine ⟨?_, fun k => ?_⟩
      · have e := conj_apply_hypSU (X := X) hg (.inr (.inr i)) (.inl i)
        rw [Equiv.swap_apply_right, Equiv.swap_apply_left] at e
        rw [e, apply_eq_zero_of_mem hXU (by simp; omega), mul_zero, zero_mul]
      · have e := conj_apply_hypSU (X := X) hg (.inr (.inr i)) (.inr (.inl k))
        rw [Equiv.swap_apply_right, Equiv.swap_apply_of_ne_of_ne (by simp) (by simp)] at e
        rw [e, apply_eq_zero_of_mem hXU (by simp; omega), mul_zero, zero_mul]

end Normalize

section Iota

variable {c : K} (hc : c ∈ h.traceZero) (hc0 : c ≠ 0)

theorem iotaBlock_uSL (t : h.fixedField) :
    !![((((uSL t : SpecialLinearGroup (Fin 2) h.fixedField)) :
        Matrix (Fin 2) (Fin 2) h.fixedField) 0 0 : K),
      c⁻¹ * ((((uSL t : SpecialLinearGroup (Fin 2) h.fixedField)) :
        Matrix (Fin 2) (Fin 2) h.fixedField) 0 1 : K);
      c * ((((uSL t : SpecialLinearGroup (Fin 2) h.fixedField)) :
        Matrix (Fin 2) (Fin 2) h.fixedField) 1 0 : K),
      ((((uSL t : SpecialLinearGroup (Fin 2) h.fixedField)) :
        Matrix (Fin 2) (Fin 2) h.fixedField) 1 1 : K)] = !![1, c⁻¹ * (t : K); 0, 1] := by
  ext a b
  fin_cases a <;> fin_cases b <;> simp [coe_uSL]

theorem iotaBlock_vSL (t : h.fixedField) :
    !![((((vSL t : SpecialLinearGroup (Fin 2) h.fixedField)) :
        Matrix (Fin 2) (Fin 2) h.fixedField) 0 0 : K),
      c⁻¹ * ((((vSL t : SpecialLinearGroup (Fin 2) h.fixedField)) :
        Matrix (Fin 2) (Fin 2) h.fixedField) 0 1 : K);
      c * ((((vSL t : SpecialLinearGroup (Fin 2) h.fixedField)) :
        Matrix (Fin 2) (Fin 2) h.fixedField) 1 0 : K),
      ((((vSL t : SpecialLinearGroup (Fin 2) h.fixedField)) :
        Matrix (Fin 2) (Fin 2) h.fixedField) 1 1 : K)] = !![1, 0; c * (t : K), 1] := by
  ext a b
  fin_cases a <;> fin_cases b <;> simp [coe_vSL]

theorem coe_iotaU_uSL (k : Fin r) (t : h.fixedField) :
    ((iotaU (ε := ε) h hc hc0 k (uSL t) : GL (HypIndex r ε) K) :
      Matrix (HypIndex r ε) (HypIndex r ε) K) =
      blockMat (pairIdx k) !![1, c⁻¹ * (t : K); 0, 1] := by
  rw [coe_iotaU, iotaBlock_uSL]

theorem coe_iotaU_vSL (k : Fin r) (t : h.fixedField) :
    ((iotaU (ε := ε) h hc hc0 k (vSL t) : GL (HypIndex r ε) K) :
      Matrix (HypIndex r ε) (HypIndex r ε) K) =
      blockMat (pairIdx k) !![1, 0; c * (t : K), 1] := by
  rw [coe_iotaU, iotaBlock_vSL]

theorem iotaU_uSL_mem (k : Fin r) (t : h.fixedField) :
    iotaU (ε := ε) h hc hc0 k (uSL t) ∈ hypUnitriangular h r ε := by
  refine mem_hypUnitriangular_of_support (fun x => ?_) fun x y hxy h0 => ?_
  · rw [coe_iotaU_uSL]
    exact blockMat_apply_self (pairIdx_injective k) (fun a => by fin_cases a <;> simp) x
  · rw [coe_iotaU_uSL] at h0
    obtain ⟨a, b, hab, rfl, rfl, hM⟩ := blockMat_offdiag (pairIdx_injective k) hxy h0
    have hk := k.isLt
    fin_cases a <;> fin_cases b <;> simp_all [pairIdx]
    all_goals omega

theorem coe_iotaU_uSL_apply (k : Fin r) (t : h.fixedField) :
    ((iotaU (ε := ε) h hc hc0 k (uSL t) : GL (HypIndex r ε) K) :
      Matrix (HypIndex r ε) (HypIndex r ε) K) (.inl k) (.inr (.inr k)) = c⁻¹ * (t : K) := by
  rw [coe_iotaU_uSL, show (.inl k : HypIndex r ε) = pairIdx k 0 from rfl,
    show (.inr (.inr k) : HypIndex r ε) = pairIdx k 1 from rfl,
    blockMat_apply_e (pairIdx_injective k)]
  simp

theorem exists_iotaU_mul_mem_simpleKerU {i : Fin r} (hi : ¬i.val + 1 < r) {u : hypSU h r 0}
    (hu : u ∈ hypUnitriangular h r 0) :
    ∃ t : h.fixedField, (iotaU h hc hc0 i (uSL t))⁻¹ * u ∈ simpleKerU h r 0 i := by
  have hir : i.val + 1 = r := by have := i.isLt; omega
  have hadj : fullPos (.inr (.inr i) : HypIndex r 0) = fullPos (.inl i : HypIndex r 0) + 1 := by
    simp only [fullPos_inl, fullPos_inr_inr]
    omega
  set y := ((u : GL (HypIndex r 0) K) : Matrix (HypIndex r 0) (HypIndex r 0) K) (.inl i)
    (.inr (.inr i)) with hy
  have hby : h.bar y = -y := by
    have e := apply_partner_eq_bar u (.inl i) (.inr (.inr i))
    simp only [hypPartner_inl, hypPartner_inr_inr] at e
    rw [inv_apply_of_adjacent hu hadj, ← hy, map_neg] at e
    linear_combination e
  have hbc := bar_c h hc
  have hmem : c * y ∈ h.fixedField := by
    rw [h.mem_fixedField, map_mul, hbc, hby, neg_mul_neg]
  have hx := iotaU_uSL_mem (ε := 0) hc hc0 i ⟨c * y, hmem⟩
  refine ⟨⟨c * y, hmem⟩, mul_mem (inv_mem hx) hu, ?_⟩
  rw [simpleCond_of_not_lt hi]
  refine ⟨?_, fun k => isEmptyElim k⟩
  rw [mul_apply_of_adjacent (inv_mem hx) hu hadj, inv_apply_of_adjacent hx hadj,
    coe_iotaU_uSL_apply]
  simp only [← hy]
  field_simp
  ring

theorem conj_iotaU_or (hε : ε ≤ 1) {g : hypSU h r ε} {w : Equiv.Perm (Fin r ⊕ Fin r)}
    (hw : w ∈ hypWeyl r)
    (hg : IsLinePerm (weylPerm (ε := ε) w)
      ((g : GL (HypIndex r ε) K) : Matrix (HypIndex r ε) (HypIndex r ε) K)) (k : Fin r) :
    (∀ t : h.fixedField, g * iotaU h hc hc0 k (uSL t) * g⁻¹ ∈ hypUnitriangular h r ε) ∨
      ∀ t : h.fixedField, g * iotaU h hc hc0 k (vSL t) * g⁻¹ ∈ hypUnitriangular h r ε := by
  have hpk := fullPos_weylPerm_partner hε hw (.inl k : HypIndex r ε)
  simp only [hypPartner_inl] at hpk
  have hwk : weylPerm (ε := ε) w (.inl k) = lineCoord (w (.inl k)) := weylPerm_inl w k
  rcases hwx : w (.inl k) with j | j
  · left
    intro t
    have hA : fullPos (weylPerm (ε := ε) w (.inl k)) = j := by rw [hwk, hwx]; rfl
    have hj := j.isLt
    refine conj_mem_hypUnitriangular hg (fun x => ?_) fun x y hxy h0 => ?_
    · rw [coe_iotaU_uSL]
      exact blockMat_apply_self (pairIdx_injective k) (fun a => by fin_cases a <;> simp) x
    · rw [coe_iotaU_uSL] at h0
      obtain ⟨a, b, hab, rfl, rfl, hM⟩ := blockMat_offdiag (pairIdx_injective k) hxy h0
      fin_cases a <;> fin_cases b <;> simp_all [pairIdx]
      all_goals omega
  · right
    intro t
    have hA : fullPos (weylPerm (ε := ε) w (.inl k)) = 2 * r + ε - 1 - j := by
      rw [hwk, hwx]; rfl
    have hj := j.isLt
    refine conj_mem_hypUnitriangular hg (fun x => ?_) fun x y hxy h0 => ?_
    · rw [coe_iotaU_vSL]
      exact blockMat_apply_self (pairIdx_injective k) (fun a => by fin_cases a <;> simp) x
    · rw [coe_iotaU_vSL] at h0
      obtain ⟨a, b, hab, rfl, rfl, hM⟩ := blockMat_offdiag (pairIdx_injective k) hxy h0
      fin_cases a <;> fin_cases b <;> simp_all [pairIdx]
      all_goals omega

end Iota

section Kappa

variable (h) in
theorem heisUMat_offdiag (u v : K) (a b : Fin 3) (hab : a ≠ b) (h0 : heisUMat h u v a b ≠ 0) :
    (a = 0 ∧ b = 1) ∨ (a = 1 ∧ b = 2) ∨ (a = 0 ∧ b = 2) := by
  fin_cases a <;> fin_cases b <;> simp_all [heisUMat]

variable (h) in
theorem heisLMat_offdiag (z t : K) (a b : Fin 3) (hab : a ≠ b) (h0 : heisLMat h z t a b ≠ 0) :
    (a = 1 ∧ b = 0) ∨ (a = 2 ∧ b = 1) ∨ (a = 2 ∧ b = 0) := by
  fin_cases a <;> fin_cases b <;> simp_all [heisLMat]

theorem coe_kappaU_of_mem_heisUpper (k : Fin r) {X : gramSU h (gramJ3 K)}
    {u v : K} (hX : ((X : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = heisUMat h u v) :
    ((kappaU h k X : GL (HypIndex r 1) K) : Matrix (HypIndex r 1) (HypIndex r 1) K) =
      blockMat (tripIdx k) (heisUMat h u v) := by
  rw [coe_kappaU, hX]

theorem coe_kappaU_of_mem_heisLower (k : Fin r) {X : gramSU h (gramJ3 K)}
    {z t : K} (hX : ((X : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = heisLMat h z t) :
    ((kappaU h k X : GL (HypIndex r 1) K) : Matrix (HypIndex r 1) (HypIndex r 1) K) =
      blockMat (tripIdx k) (heisLMat h z t) := by
  rw [coe_kappaU, hX]

theorem heisUMat_diag (u v : K) (a : Fin 3) : heisUMat h u v a a = 1 := by
  fin_cases a <;> simp [heisUMat]

theorem heisLMat_diag (z t : K) (a : Fin 3) : heisLMat h z t a a = 1 := by
  fin_cases a <;> simp [heisLMat]

theorem kappaU_mem_of_heisUpper (k : Fin r) {X : gramSU h (gramJ3 K)} (hX : X ∈ heisUpper h) :
    kappaU h k X ∈ hypUnitriangular h r 1 := by
  obtain ⟨u, v, -, hXm⟩ := hX
  refine mem_hypUnitriangular_of_support (fun x => ?_) fun x y hxy h0 => ?_
  · rw [coe_kappaU_of_mem_heisUpper k hXm]
    exact blockMat_apply_self (tripIdx_injective k) (heisUMat_diag u v) x
  · rw [coe_kappaU_of_mem_heisUpper k hXm] at h0
    obtain ⟨a, b, hab, rfl, rfl, hM⟩ := blockMat_offdiag (tripIdx_injective k) hxy h0
    have hk := k.isLt
    rcases heisUMat_offdiag h u v a b hab hM with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      simp [tripIdx] <;> omega

theorem coe_kappaU_heisU_apply_z (k : Fin r) {u v : K} (huv : v + h.bar v = -(u * h.bar u)) :
    ((kappaU h k (heisU h huv) : GL (HypIndex r 1) K) :
      Matrix (HypIndex r 1) (HypIndex r 1) K) (.inl k) (.inr (.inl 0)) = u := by
  rw [coe_kappaU_of_mem_heisUpper k (coe_heisU h huv),
    show (.inl k : HypIndex r 1) = tripIdx k 0 from rfl,
    show (.inr (.inl 0) : HypIndex r 1) = tripIdx k 1 from rfl,
    blockMat_apply_e (tripIdx_injective k)]
  simp [heisUMat]

theorem coe_kappaU_heisU_apply_f (k : Fin r) {u v : K} (huv : v + h.bar v = -(u * h.bar u)) :
    ((kappaU h k (heisU h huv) : GL (HypIndex r 1) K) :
      Matrix (HypIndex r 1) (HypIndex r 1) K) (.inl k) (.inr (.inr k)) = v := by
  rw [coe_kappaU_of_mem_heisUpper k (coe_heisU h huv),
    show (.inl k : HypIndex r 1) = tripIdx k 0 from rfl,
    show (.inr (.inr k) : HypIndex r 1) = tripIdx k 2 from rfl,
    blockMat_apply_e (tripIdx_injective k)]
  simp [heisUMat]

theorem mul_apply_last_odd {i : Fin r} (hi : ¬i.val + 1 < r) {g g' : hypSU h r 1}
    (hg : g ∈ hypUnitriangular h r 1) (hg' : g' ∈ hypUnitriangular h r 1) :
    (((g * g' : hypSU h r 1) : GL (HypIndex r 1) K) : Matrix (HypIndex r 1) (HypIndex r 1) K)
      (.inl i) (.inr (.inr i)) =
      ((g : GL (HypIndex r 1) K) : Matrix (HypIndex r 1) (HypIndex r 1) K) (.inl i)
          (.inr (.inr i)) +
        ((g' : GL (HypIndex r 1) K) : Matrix (HypIndex r 1) (HypIndex r 1) K) (.inl i)
          (.inr (.inr i)) +
        ((g : GL (HypIndex r 1) K) : Matrix (HypIndex r 1) (HypIndex r 1) K) (.inl i)
            (.inr (.inl 0)) *
          ((g' : GL (HypIndex r 1) K) : Matrix (HypIndex r 1) (HypIndex r 1) K) (.inr (.inl 0))
            (.inr (.inr i)) := by
  have hir : i.val + 1 = r := by have := i.isLt; omega
  rw [mul_apply_of_mem hg hg' (by simp only [fullPos]; omega)]
  congr 1
  rw [Finset.sum_eq_single (.inr (.inl 0))]
  · intro c hc hc0
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hc
    have hc2 := hc.2
    rw [fullPos_inr_inr] at hc2
    obtain ⟨k, rfl⟩ := exists_eq_z_of_between hi hc.1 (by omega)
    exact absurd (by rw [Subsingleton.elim k 0]) hc0
  · intro h0
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_and_or, not_lt] at h0
    simp only [fullPos] at h0
    omega

theorem exists_kappaU_mul_mem_simpleKerU {i : Fin r} (hi : ¬i.val + 1 < r) {u : hypSU h r 1}
    (hu : u ∈ hypUnitriangular h r 1) :
    ∃ X ∈ heisUpper h, (kappaU h i X)⁻¹ * u ∈ simpleKerU h r 1 i := by
  have hir : i.val + 1 = r := by have := i.isLt; omega
  have hadj : fullPos (.inr (.inl 0) : HypIndex r 1) = fullPos (.inl i : HypIndex r 1) + 1 := by
    simp only [fullPos_inl, fullPos_inr_inl]
    simp
    omega
  set a := ((u : GL (HypIndex r 1) K) : Matrix (HypIndex r 1) (HypIndex r 1) K) (.inl i)
    (.inr (.inl 0)) with ha
  set v := ((u : GL (HypIndex r 1) K) : Matrix (HypIndex r 1) (HypIndex r 1) K) (.inl i)
    (.inr (.inr i)) with hv
  have hinv_f : ((((u⁻¹ : hypSU h r 1)) : GL (HypIndex r 1) K) :
      Matrix (HypIndex r 1) (HypIndex r 1) K) (.inl i) (.inr (.inr i)) = h.bar v := by
    rw [inv_apply_eq_bar]
    rfl
  have hinv_z : ((((u⁻¹ : hypSU h r 1)) : GL (HypIndex r 1) K) :
      Matrix (HypIndex r 1) (HypIndex r 1) K) (.inr (.inl 0)) (.inr (.inr i)) = h.bar a := by
    rw [inv_apply_eq_bar]
    rfl
  have hzf : ((u : GL (HypIndex r 1) K) : Matrix (HypIndex r 1) (HypIndex r 1) K)
      (.inr (.inl 0)) (.inr (.inr i)) = -h.bar a := by
    have e := apply_partner_eq_bar u (.inl i) (.inr (.inl 0))
    simp only [hypPartner_inl, hypPartner_inr_inl] at e
    rw [e, inv_apply_of_adjacent hu hadj, ← ha, map_neg]
  have huv : v + h.bar v = -(a * h.bar a) := by
    have e := mul_apply_last_odd hi hu (inv_mem hu)
    rw [mul_inv_cancel, OneMemClass.coe_one, Units.val_one, one_apply_ne (by simp), hinv_f,
      hinv_z, ← ha, ← hv] at e
    linear_combination -e
  have hx := kappaU_mem_of_heisUpper (r := r) i (heisU_mem h huv)
  refine ⟨heisU h huv, heisU_mem h huv, mul_mem (inv_mem hx) hu, ?_⟩
  rw [simpleCond_of_not_lt hi]
  refine ⟨?_, fun k => ?_⟩
  · rw [mul_apply_last_odd hi (inv_mem hx) hu, inv_apply_eq_bar, inv_apply_of_adjacent hx hadj,
      hzf]
    simp only [hypPartner_inl, hypPartner_inr_inr]
    rw [coe_kappaU_heisU_apply_f, coe_kappaU_heisU_apply_z, ← hv]
    linear_combination huv
  · have hk : k = 0 := Subsingleton.elim _ _
    subst hk
    rw [mul_apply_of_adjacent (inv_mem hx) hu hadj, inv_apply_of_adjacent hx hadj,
      coe_kappaU_heisU_apply_z, ← ha, neg_add_cancel]

theorem conj_kappaU_or {g : hypSU h r 1} {w : Equiv.Perm (Fin r ⊕ Fin r)}
    (hw : w ∈ hypWeyl r)
    (hg : IsLinePerm (weylPerm (ε := 1) w)
      ((g : GL (HypIndex r 1) K) : Matrix (HypIndex r 1) (HypIndex r 1) K)) (k : Fin r) :
    (∀ X ∈ heisUpper h, g * kappaU h k X * g⁻¹ ∈ hypUnitriangular h r 1) ∨
      ∀ X ∈ heisLower h, g * kappaU h k X * g⁻¹ ∈ hypUnitriangular h r 1 := by
  have hpk := fullPos_weylPerm_partner le_rfl hw (.inl k : HypIndex r 1)
  simp only [hypPartner_inl] at hpk
  have hz : weylPerm (ε := 1) w (.inr (.inl 0)) = .inr (.inl 0) := weylPerm_inr_inl w 0
  have hwk : weylPerm (ε := 1) w (.inl k) = lineCoord (w (.inl k)) := weylPerm_inl w k
  rcases hwx : w (.inl k) with j | j
  · left
    intro X hX
    obtain ⟨u, v, -, hXm⟩ := hX
    have hA : fullPos (weylPerm (ε := 1) w (.inl k)) = j := by rw [hwk, hwx]; rfl
    have hj := j.isLt
    refine conj_mem_hypUnitriangular hg (fun x => ?_) fun x y hxy h0 => ?_
    · rw [coe_kappaU_of_mem_heisUpper k hXm]
      exact blockMat_apply_self (tripIdx_injective k) (heisUMat_diag u v) x
    · rw [coe_kappaU_of_mem_heisUpper k hXm] at h0
      obtain ⟨a, b, hab, rfl, rfl, hM⟩ := blockMat_offdiag (tripIdx_injective k) hxy h0
      rcases heisUMat_offdiag h u v a b hab hM with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · change fullPos (weylPerm w (.inl k)) < fullPos (weylPerm w (.inr (.inl 0)))
        rw [hz, hA, fullPos_inr_inl]
        simp
      · change fullPos (weylPerm w (.inr (.inl 0))) < fullPos (weylPerm w (.inr (.inr k)))
        rw [hz, hpk, hA, fullPos_inr_inl]
        simp
        omega
      · change fullPos (weylPerm w (.inl k)) < fullPos (weylPerm w (.inr (.inr k)))
        rw [hpk, hA]
        omega
  · right
    intro X hX
    obtain ⟨z, t, -, hXm⟩ := hX
    have hA : fullPos (weylPerm (ε := 1) w (.inl k)) = 2 * r + 1 - 1 - j := by
      rw [hwk, hwx]; rfl
    have hj := j.isLt
    refine conj_mem_hypUnitriangular hg (fun x => ?_) fun x y hxy h0 => ?_
    · rw [coe_kappaU_of_mem_heisLower k hXm]
      exact blockMat_apply_self (tripIdx_injective k) (heisLMat_diag z t) x
    · rw [coe_kappaU_of_mem_heisLower k hXm] at h0
      obtain ⟨a, b, hab, rfl, rfl, hM⟩ := blockMat_offdiag (tripIdx_injective k) hxy h0
      rcases heisLMat_offdiag h z t a b hab hM with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · change fullPos (weylPerm w (.inr (.inl 0))) < fullPos (weylPerm w (.inl k))
        rw [hz, hA, fullPos_inr_inl]
        simp
        omega
      · change fullPos (weylPerm w (.inr (.inr k))) < fullPos (weylPerm w (.inr (.inl 0)))
        rw [hz, hpk, hA, fullPos_inr_inl]
        simp
        omega
      · change fullPos (weylPerm w (.inr (.inr k))) < fullPos (weylPerm w (.inl k))
        rw [hpk, hA]
        omega

end Kappa

end CFSG.RankThree.CentralLiftU
