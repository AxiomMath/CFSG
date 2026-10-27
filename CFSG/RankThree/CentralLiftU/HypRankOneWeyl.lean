module

public import CFSG.RankThree.CentralLiftU.HypRankOneConj

public section

namespace CFSG.RankThree.CentralLiftU

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.ClassicalGroups.UnitaryFlag
open CFSG.LocalAnalysis.ComponentInitial.SymplecticTorusWeyl (sl2Diag sl2W sl2ConjDiag
  coe_sl2Diag coe_sl2W coe_sl2ConjDiag coe_sl2W_inv)
open CFSG.RankThree.CentralLift.LinearRoots (swapSL coe_swapSL)
open CFSG.LieType.Universal.SpecialLinear (signedPerm signedPerm_apply)
open scoped Matrix

variable {p f : ℕ} {K : Type} [Field K] {r ε : ℕ}

section Signs

@[expose] def lineSign (j x : Fin r) : K := if x = j then -1 else 1

theorem lineSign_ne_zero (j x : Fin r) : lineSign (K := K) j x ≠ 0 := by
  unfold lineSign; split_ifs <;> simp

theorem lineSign_mul_self (j x : Fin r) : lineSign (K := K) j x * lineSign j x = 1 := by
  unfold lineSign; split_ifs <;> simp

@[expose] def wSignU (j : Fin r) : HypIndex r ε → K
  | .inl x => lineSign j x
  | .inr (.inl _) => 1
  | .inr (.inr x) => lineSign j x

@[expose] def swapIdx (i j : Fin r) : Equiv.Perm (HypIndex r ε) :=
  Equiv.sumCongr (Equiv.swap i j) (Equiv.sumCongr 1 (Equiv.swap i j))

theorem swapIdx_inl (i j x : Fin r) :
    swapIdx (ε := ε) i j (.inl x) = .inl (Equiv.swap i j x) := rfl

theorem swapIdx_z (i j : Fin r) (k : Fin ε) :
    swapIdx (ε := ε) i j (.inr (.inl k)) = .inr (.inl k) := rfl

theorem swapIdx_inr (i j x : Fin r) :
    swapIdx (ε := ε) i j (.inr (.inr x)) = .inr (.inr (Equiv.swap i j x)) := rfl

theorem swapIdx_symm (i j : Fin r) : (swapIdx (ε := ε) i j).symm = swapIdx i j := by
  ext x
  rcases x with x | k | x <;> simp [swapIdx, Equiv.symm_swap]

theorem swapIdx_comp_quadIdx (i j k l : Fin r) :
    swapIdx (ε := ε) i j ∘ quadIdx k l = quadIdx (Equiv.swap i j k) (Equiv.swap i j l) := by
  funext a
  rcases a with a | a <;> fin_cases a <;> rfl

theorem swapIdx_comp_pairIdx (i j k : Fin r) :
    swapIdx (ε := ε) i j ∘ pairIdx k = pairIdx (Equiv.swap i j k) := by
  funext a
  fin_cases a <;> rfl

end Signs

section RhoW

variable (h : UnitaryFieldData p f K)

theorem rho4Mat_sl2W :
    rho4Mat h sl2W = signedPerm (Equiv.sumCongr (Equiv.swap 0 1) (Equiv.swap 0 1))
      (Sum.elim ![1, -1] ![1, -1]) := by
  ext (a | a) (b | b) <;> fin_cases a <;> fin_cases b <;>
    simp [rho4Mat, adjugate_fin_two, signedPerm_apply]

theorem coe_rhoU_sl2W {i j : Fin r} (hij : i ≠ j) :
    ((rhoU (ε := ε) h hij sl2W : GL (HypIndex r ε) K) :
      Matrix (HypIndex r ε) (HypIndex r ε) K) = signedPerm (swapIdx i j) (wSignU j) := by
  rw [coe_rhoU, rho4Mat_sl2W]
  refine blockMat_signedPerm (quadIdx_injective hij) ?_ ?_ ?_ ?_
  · rintro (a | a) <;> fin_cases a <;>
      simp [quadIdx, swapIdx_inl, swapIdx_inr, Equiv.swap_apply_left, Equiv.swap_apply_right]
  · rintro (x | k | x) hx
    · have h1 : x ≠ i := fun h1 => hx (.inl 0) (by simp [quadIdx, h1])
      have h2 : x ≠ j := fun h2 => hx (.inl 1) (by simp [quadIdx, h2])
      rw [swapIdx_inl, Equiv.swap_apply_of_ne_of_ne h1 h2]
    · rfl
    · have h1 : x ≠ i := fun h1 => hx (.inr 0) (by simp [quadIdx, h1])
      have h2 : x ≠ j := fun h2 => hx (.inr 1) (by simp [quadIdx, h2])
      rw [swapIdx_inr, Equiv.swap_apply_of_ne_of_ne h1 h2]
  · rintro (a | a) <;> fin_cases a <;> simp [quadIdx, wSignU, lineSign, hij]
  · rintro (x | k | x) hx
    · have h2 : x ≠ j := fun h2 => hx (.inl 1) (by simp [quadIdx, h2])
      simp [wSignU, lineSign, h2]
    · rfl
    · have h2 : x ≠ j := fun h2 => hx (.inr 1) (by simp [quadIdx, h2])
      simp [wSignU, lineSign, h2]

theorem wSignU_ne_zero (j : Fin r) (x : HypIndex r ε) : wSignU (K := K) j x ≠ 0 := by
  rcases x with x | k | x <;> simp [wSignU, lineSign_ne_zero]

theorem coe_rhoU_sl2W_inv {i j : Fin r} (hij : i ≠ j) :
    (((rhoU (ε := ε) h hij sl2W)⁻¹ : hypSU h r ε) : GL (HypIndex r ε) K).val =
      signedPerm (swapIdx i j).symm (fun y => (wSignU (K := K) j ((swapIdx i j).symm y))⁻¹) :=
  coe_inv_of_signedPerm h (wSignU_ne_zero j) (coe_rhoU_sl2W h hij)

theorem wSignU_mul_inv (j : Fin r) (x : HypIndex r ε) :
    wSignU (K := K) j x * (wSignU j x)⁻¹ = 1 :=
  mul_inv_cancel₀ (wSignU_ne_zero j x)

theorem conj_rhoU_sl2W_rhoU {i j : Fin r} (hij : i ≠ j) {k l : Fin r} (hkl : k ≠ l)
    (g : SpecialLinearGroup (Fin 2) K) :
    rhoU h hij sl2W * rhoU (ε := ε) h hkl g * (rhoU h hij sl2W)⁻¹ =
      rhoU h ((Equiv.swap i j).injective.ne hkl)
        (sl2ConjDiag (Units.mk0 (lineSign j l / lineSign j k)
          (div_ne_zero (lineSign_ne_zero j l) (lineSign_ne_zero j k))) g) := by
  apply Subtype.ext
  apply Units.ext
  rw [Subgroup.coe_mul, Subgroup.coe_mul, Units.val_mul, Units.val_mul, coe_rhoU_sl2W h hij,
    coe_rhoU_sl2W_inv h hij, coe_rhoU, coe_rhoU, conj_signedPerm_blockMat _ ?_,
    swapIdx_comp_quadIdx]
  · congr 1
    have e1 : (wSignU (K := K) (ε := ε) j ∘ quadIdx k l) =
        Sum.elim ![lineSign j k, lineSign j l] ![(h.bar (lineSign j k))⁻¹,
          (h.bar (lineSign j l))⁻¹] := by
      funext a
      rcases a with a | a <;> fin_cases a <;> simp [quadIdx, wSignU, lineSign] <;>
        split_ifs <;> simp
    have e2 : (fun a => (wSignU (K := K) (ε := ε) j ((swapIdx i j).symm
        (swapIdx i j (quadIdx k l a))))⁻¹) =
        Sum.elim ![(lineSign j k)⁻¹, (lineSign j l)⁻¹] ![h.bar (lineSign j k),
          h.bar (lineSign j l)] := by
      funext a
      simp only [Equiv.symm_apply_apply]
      rcases a with a | a <;> fin_cases a <;> simp [quadIdx, wSignU, lineSign] <;>
        split_ifs <;> simp
    rw [e1, e2]
    exact diag_mul_rho4Mat_mul_diag h (lineSign_ne_zero j k) (lineSign_ne_zero j l) g
  · intro x
    rw [Equiv.symm_apply_apply]
    exact wSignU_mul_inv j x

theorem conj_rhoU_sl2W_iotaU {i j : Fin r} (hij : i ≠ j) {c : K} (hc : c ∈ h.traceZero)
    (hc0 : c ≠ 0) (k : Fin r) (g : SpecialLinearGroup (Fin 2) h.fixedField) :
    rhoU h hij sl2W * iotaU (ε := ε) h hc hc0 k g * (rhoU h hij sl2W)⁻¹ =
      iotaU h hc hc0 (Equiv.swap i j k) g := by
  apply Subtype.ext
  apply Units.ext
  rw [Subgroup.coe_mul, Subgroup.coe_mul, Units.val_mul, Units.val_mul, coe_rhoU_sl2W h hij,
    coe_rhoU_sl2W_inv h hij, coe_iotaU, coe_iotaU, conj_signedPerm_blockMat _ ?_,
    swapIdx_comp_pairIdx]
  · congr 1
    have e1 : (wSignU (K := K) (ε := ε) j ∘ pairIdx k) = ![lineSign j k, lineSign j k] := by
      funext a; fin_cases a <;> rfl
    have e2 : (fun a => (wSignU (K := K) (ε := ε) j ((swapIdx i j).symm
        (swapIdx i j (pairIdx k a))))⁻¹) = ![(lineSign j k)⁻¹, (lineSign j k)⁻¹] := by
      funext a
      simp only [Equiv.symm_apply_apply]
      fin_cases a <;> rfl
    rw [e1, e2]
    have hs := lineSign_ne_zero (K := K) j k
    ext a b
    fin_cases a <;> fin_cases b <;> simp [diagonal_mul, mul_diagonal] <;> field_simp
  · intro x
    rw [Equiv.symm_apply_apply]
    exact wSignU_mul_inv j x

end RhoW

section Commute

variable (h : UnitaryFieldData p f K)

theorem hypSU_commute_of_val {x y : hypSU h r ε}
    (hxy : Commute ((x : GL (HypIndex r ε) K) : Matrix (HypIndex r ε) (HypIndex r ε) K)
      ((y : GL (HypIndex r ε) K) : Matrix (HypIndex r ε) (HypIndex r ε) K)) : Commute x y :=
  Subtype.ext (Units.ext hxy)

theorem commute_rhoU_rhoU {i j k l : Fin r} (hij : i ≠ j) (hkl : k ≠ l) (hik : i ≠ k)
    (hil : i ≠ l) (hjk : j ≠ k) (hjl : j ≠ l) (g g' : SpecialLinearGroup (Fin 2) K) :
    Commute (rhoU (ε := ε) h hij g) (rhoU h hkl g') := by
  refine hypSU_commute_of_val h ?_
  rw [coe_rhoU, coe_rhoU]
  refine commute_blockMat ?_ _ _
  rintro (a | a) (b | b) <;> fin_cases a <;> fin_cases b <;> simp_all [quadIdx]

theorem commute_rhoU_iotaU {i j : Fin r} (hij : i ≠ j) {c : K} (hc : c ∈ h.traceZero)
    (hc0 : c ≠ 0) {k : Fin r} (hik : i ≠ k) (hjk : j ≠ k) (g : SpecialLinearGroup (Fin 2) K)
    (g' : SpecialLinearGroup (Fin 2) h.fixedField) :
    Commute (rhoU (ε := ε) h hij g) (iotaU h hc hc0 k g') := by
  refine hypSU_commute_of_val h ?_
  rw [coe_rhoU, coe_iotaU]
  refine commute_blockMat ?_ _ _
  rintro (a | a) b <;> fin_cases a <;> fin_cases b <;> simp_all [quadIdx, pairIdx]

theorem commute_iotaU_iotaU {c : K} (hc : c ∈ h.traceZero) (hc0 : c ≠ 0) {k l : Fin r}
    (hkl : k ≠ l) (g g' : SpecialLinearGroup (Fin 2) h.fixedField) :
    Commute (iotaU (ε := ε) h hc hc0 k g) (iotaU h hc hc0 l g') := by
  refine hypSU_commute_of_val h ?_
  rw [coe_iotaU, coe_iotaU]
  refine commute_blockMat ?_ _ _
  intro a b
  fin_cases a <;> fin_cases b <;> simp_all [pairIdx]

end Commute

section Swap

variable (h : UnitaryFieldData p f K)

@[expose] def swap4 : Fin 2 ⊕ Fin 2 → Fin 2 ⊕ Fin 2 :=
  Sum.map (Equiv.swap 0 1) (Equiv.swap 0 1)

theorem swap4_involutive : Function.Involutive swap4 := by
  rintro (a | a) <;> fin_cases a <;> rfl

theorem quadIdx_comp_swap4 (i j : Fin r) :
    quadIdx (ε := ε) i j ∘ swap4 = quadIdx j i := by
  funext a
  rcases a with a | a <;> fin_cases a <;> rfl

theorem blockMat_swap4_rho4Mat (g : SpecialLinearGroup (Fin 2) K) :
    blockMat swap4 (rho4Mat h g) = rho4Mat h (swapSL g) := by
  ext x y
  obtain ⟨a, rfl⟩ : ∃ a, swap4 a = x := ⟨swap4 x, swap4_involutive x⟩
  obtain ⟨b, rfl⟩ : ∃ b, swap4 b = y := ⟨swap4 y, swap4_involutive y⟩
  rw [blockMat_apply_e swap4_involutive.injective]
  rcases a with a | a <;> rcases b with b | b <;> fin_cases a <;> fin_cases b <;>
    simp [rho4Mat, swap4, coe_swapSL, adjugate_fin_two]

theorem rhoU_swap {i j : Fin r} (hij : i ≠ j) :
    rhoU (ε := ε) h hij.symm = (rhoU h hij).comp swapSL := by
  ext g : 1
  apply Subtype.ext
  apply Units.ext
  rw [MonoidHom.comp_apply, coe_rhoU, coe_rhoU, ← blockMat_swap4_rho4Mat, blockMat_blockMat,
    quadIdx_comp_swap4]

end Swap

section Tori

variable (h : UnitaryFieldData p f K)

@[expose] noncomputable def rhoDiag (i j : Fin r) (t : Kˣ) : HypIndex r ε → K
  | .inl x => if x = i then (t : K) else if x = j then ((t⁻¹ : Kˣ) : K) else 1
  | .inr (.inl _) => 1
  | .inr (.inr x) => if x = i then (h.bar t)⁻¹ else if x = j then h.bar t else 1

theorem coe_rhoU_sl2Diag {i j : Fin r} (hij : i ≠ j) (t : Kˣ) :
    ((rhoU (ε := ε) h hij (sl2Diag t) : GL (HypIndex r ε) K) :
      Matrix (HypIndex r ε) (HypIndex r ε) K) = diagonal (rhoDiag h i j t) := by
  rw [coe_rhoU]
  have hd : rho4Mat h (sl2Diag t) =
      diagonal (Sum.elim ![(t : K), ((t⁻¹ : Kˣ) : K)] ![(h.bar t)⁻¹, h.bar t]) := by
    ext (a | a) (b | b) <;> fin_cases a <;> fin_cases b <;>
      simp [rho4Mat, adjugate_fin_two, map_inv₀]
  rw [hd]
  refine blockMat_diagonal (quadIdx_injective hij) ?_ ?_
  · rintro (a | a) <;> fin_cases a <;> simp [quadIdx, rhoDiag, Ne.symm hij]
  · rintro (x | k | x) hx
    · have h1 : x ≠ i := fun h1 => hx (.inl 0) (by simp [quadIdx, h1])
      have h2 : x ≠ j := fun h2 => hx (.inl 1) (by simp [quadIdx, h2])
      simp [rhoDiag, h1, h2]
    · rfl
    · have h1 : x ≠ i := fun h1 => hx (.inr 0) (by simp [quadIdx, h1])
      have h2 : x ≠ j := fun h2 => hx (.inr 1) (by simp [quadIdx, h2])
      simp [rhoDiag, h1, h2]

variable {c : K} (hc : c ∈ h.traceZero) (hc0 : c ≠ 0)

@[expose] noncomputable def iotaDiag (k : Fin r) (b : h.fixedFieldˣ) : HypIndex r ε → K
  | .inl x => if x = k then ((b : h.fixedField) : K) else 1
  | .inr (.inl _) => 1
  | .inr (.inr x) => if x = k then (((b⁻¹ : h.fixedFieldˣ) : h.fixedField) : K) else 1

theorem coe_iotaU_sl2Diag (k : Fin r) (b : h.fixedFieldˣ) :
    ((iotaU (ε := ε) h hc hc0 k (sl2Diag b) : GL (HypIndex r ε) K) :
      Matrix (HypIndex r ε) (HypIndex r ε) K) = diagonal (iotaDiag h k b) := by
  rw [coe_iotaU]
  have hd : !![((((sl2Diag b : SpecialLinearGroup (Fin 2) h.fixedField) :
        Matrix (Fin 2) (Fin 2) h.fixedField) 0 0 : h.fixedField) : K),
      c⁻¹ * ((((sl2Diag b : SpecialLinearGroup (Fin 2) h.fixedField) :
        Matrix (Fin 2) (Fin 2) h.fixedField) 0 1 : h.fixedField) : K);
      c * ((((sl2Diag b : SpecialLinearGroup (Fin 2) h.fixedField) :
        Matrix (Fin 2) (Fin 2) h.fixedField) 1 0 : h.fixedField) : K),
      ((((sl2Diag b : SpecialLinearGroup (Fin 2) h.fixedField) :
        Matrix (Fin 2) (Fin 2) h.fixedField) 1 1 : h.fixedField) : K)] =
      diagonal ![((b : h.fixedField) : K), (((b⁻¹ : h.fixedFieldˣ) : h.fixedField) : K)] := by
    ext a a'
    fin_cases a <;> fin_cases a' <;> simp
  rw [hd]
  refine blockMat_diagonal (pairIdx_injective k) ?_ ?_
  · intro a
    fin_cases a <;> simp [pairIdx, iotaDiag]
  · rintro (x | l | x) hx
    · have h1 : x ≠ k := fun h1 => hx 0 (by simp [pairIdx, h1])
      simp [iotaDiag, h1]
    · rfl
    · have h1 : x ≠ k := fun h1 => hx 1 (by simp [pairIdx, h1])
      simp [iotaDiag, h1]

@[expose] noncomputable def iotaWSign (c : K) (k : Fin r) : HypIndex r ε → K
  | .inl x => if x = k then c else 1
  | .inr (.inl _) => 1
  | .inr (.inr x) => if x = k then -c⁻¹ else 1

theorem coe_iotaU_sl2W (k : Fin r) :
    ((iotaU (ε := ε) h hc hc0 k sl2W : GL (HypIndex r ε) K) :
      Matrix (HypIndex r ε) (HypIndex r ε) K) =
      signedPerm (Equiv.swap (.inl k) (.inr (.inr k))) (iotaWSign c k) := by
  rw [coe_iotaU]
  have hd : !![((((sl2W : SpecialLinearGroup (Fin 2) h.fixedField) :
        Matrix (Fin 2) (Fin 2) h.fixedField) 0 0 : h.fixedField) : K),
      c⁻¹ * ((((sl2W : SpecialLinearGroup (Fin 2) h.fixedField) :
        Matrix (Fin 2) (Fin 2) h.fixedField) 0 1 : h.fixedField) : K);
      c * ((((sl2W : SpecialLinearGroup (Fin 2) h.fixedField) :
        Matrix (Fin 2) (Fin 2) h.fixedField) 1 0 : h.fixedField) : K),
      ((((sl2W : SpecialLinearGroup (Fin 2) h.fixedField) :
        Matrix (Fin 2) (Fin 2) h.fixedField) 1 1 : h.fixedField) : K)] =
      signedPerm (Equiv.swap 0 1) ![c, -c⁻¹] := by
    ext a a'
    fin_cases a <;> fin_cases a' <;> simp [signedPerm_apply]
  rw [hd]
  refine blockMat_signedPerm (pairIdx_injective k) ?_ ?_ ?_ ?_
  · intro a
    fin_cases a <;> simp [pairIdx, Equiv.swap_apply_left, Equiv.swap_apply_right]
  · rintro (x | l | x) hx
    · have h1 : x ≠ k := fun h1 => hx 0 (by simp [pairIdx, h1])
      exact Equiv.swap_apply_of_ne_of_ne (by simpa using h1) (by simp)
    · exact Equiv.swap_apply_of_ne_of_ne (by simp) (by simp)
    · have h1 : x ≠ k := fun h1 => hx 1 (by simp [pairIdx, h1])
      exact Equiv.swap_apply_of_ne_of_ne (by simp) (by simpa using h1)
  · intro a
    fin_cases a <;> simp [pairIdx, iotaWSign]
  · rintro (x | l | x) hx
    · have h1 : x ≠ k := fun h1 => hx 0 (by simp [pairIdx, h1])
      simp [iotaWSign, h1]
    · rfl
    · have h1 : x ≠ k := fun h1 => hx 1 (by simp [pairIdx, h1])
      simp [iotaWSign, h1]

end Tori

end CFSG.RankThree.CentralLiftU
