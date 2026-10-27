module

public import CFSG.RankThree.PartTwo.Sec21.ReeF4Conj2ProofWeyl
public import CFSG.RankThree.PartOne.KF4.LongA2Frame
public import CFSG.RankThree.PartOne.KF4.ShortA2Frame
public import CFSG.RankThree.PartOne.KE.StabGeneral

public section

set_option linter.unusedSectionVars false

namespace CFSG.RankThree.PartTwo.Sec8.ReeF4Conj2Proof

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Ree
open CFSG.Monster.B.Geometry CFSG.RankThree.PartOne.KF4 CFSG.RankThree.PartOne.KE
open CFSG.RankThree.Chevalley CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open CFSG.RankThree.PartTwo.Sec21.ReeF4ThreeLocalProof CFSG.LieType.Steinberg.Adjoint
open CFSG.RankThree.E6 (chainRoot)
open scoped MatrixGroups Pointwise


@[expose] def wL : Fin 3 → Fin Tag.F4.rank → ℤ :=
  ![![2, 3, 4, 2], ![1, 3, 4, 2], 0]

@[expose] def sigmaL (i j : Fin 3) : Fin Tag.F4.rank → ℤ := wL i - wL j

@[expose] noncomputable def trElemF : WeylGroup Tag.F4 := trElem

theorem trElem_smul_eq (v : Fin Tag.F4.rank → ℤ) :
    trElemF • v = lin4 v (codeRoots (f4Code trCode)) := by
  refine (smul_eq_lin4 trElem v).trans ?_
  congr 1
  funext k
  exact smul_single_eq_codeRoots f4Realizes_trElem k

set_option maxRecDepth 10000 in
theorem trElem_smul_chainRoot (i j : Fin 3) :
    trElemF • chainRoot (τ := Tag.F4) f4chainLong i j = sigmaL i j := by
  rw [trElem_smul_eq]
  funext l
  fin_cases i <;> fin_cases j <;> fin_cases l <;> decide +kernel

@[expose] def kernelCheck : Bool :=
  (List.range 48).all fun k =>
    !(Tag.F4.rootCertificate.root k 1 % 3 == 0) ||
      (List.finRange 3).any fun i => (List.finRange 3).any fun j =>
        i != j && (List.ofFn (Tag.F4.rootCertificate.root k) == List.ofFn (sigmaL i j) ||
          List.ofFn (Tag.F4.rootCertificate.root k) == List.ofFn (f4ShortSigma i j))

set_option maxRecDepth 100000 in
theorem kernelCheck_eq : kernelCheck = true := by decide +kernel

theorem kernel_cases {α : Fin Tag.F4.rank → ℤ} (hα : IsRoot Tag.F4 α)
    (h3 : (3 : ℤ) ∣ α 1) :
    (∃ i j : Fin 3, i ≠ j ∧ α = sigmaL i j) ∨ (∃ i j : Fin 3, i ≠ j ∧ α = f4ShortSigma i j) := by
  obtain ⟨k, hk, rfl⟩ := RootCertificate.exists_root_eq (Tag.rootCertificate_check Tag.F4) hα
  have hcheck := kernelCheck_eq
  simp only [kernelCheck, List.all_eq_true, List.mem_range] at hcheck
  have hlen : Tag.F4.rootCertificate.roots.length = 48 :=
    CFSG.Monster.B.Geometry.f4_roots_length
  have h1 := hcheck k (hlen ▸ hk)
  have h3' : Tag.F4.rootCertificate.root k 1 % 3 = 0 := Int.emod_eq_zero_of_dvd h3
  simp only [h3', beq_self_eq_true, Bool.not_true, Bool.false_or, List.any_eq_true,
    List.mem_finRange, true_and, Bool.and_eq_true, bne_iff_ne, ne_eq, Bool.or_eq_true,
    beq_iff_eq] at h1
  obtain ⟨i, j, hij, h | h⟩ := h1
  · exact Or.inl ⟨i, j, hij, List.ofFn_injective h⟩
  · exact Or.inr ⟨i, j, hij, List.ofFn_injective h⟩

set_option maxRecDepth 10000 in
theorem three_dvd_sigma (i j : Fin 3) :
    (3 : ℤ) ∣ sigmaL i j 1 ∧ (3 : ℤ) ∣ f4ShortSigma i j 1 := by
  fin_cases i <;> fin_cases j <;> decide +kernel

set_option maxRecDepth 10000 in
theorem iform_sigma (i j k l : Fin 3) : iform (τ := Tag.F4) (sigmaL i j)
    (f4ShortSigma k l) = 0 := by
  fin_cases i <;> fin_cases j <;> fin_cases k <;> fin_cases l <;> decide +kernel

@[expose] def sumCheck : Bool :=
  (List.finRange 3).all fun i => (List.finRange 3).all fun j =>
    (List.finRange 3).all fun k => (List.finRange 3).all fun l =>
      i == j || k == l || (List.range 48).all fun m =>
        List.ofFn (Tag.F4.rootCertificate.root m) != List.ofFn (sigmaL i j + f4ShortSigma k l)

set_option maxRecDepth 100000 in
theorem sumCheck_eq : sumCheck = true := by decide +kernel

theorem not_isRoot_add_sigma {i j k l : Fin 3} (hij : i ≠ j) (hkl : k ≠ l) :
    ¬ IsRoot Tag.F4 (sigmaL i j + f4ShortSigma k l) := by
  intro h
  obtain ⟨m, hm, hmv⟩ := RootCertificate.exists_root_eq (Tag.rootCertificate_check Tag.F4) h
  have hcheck := sumCheck_eq
  simp only [sumCheck, List.all_eq_true, List.mem_finRange, true_implies, Bool.or_eq_true,
    beq_iff_eq, List.mem_range, bne_iff_ne, ne_eq] at hcheck
  have hlen : Tag.F4.rootCertificate.roots.length = 48 :=
    CFSG.Monster.B.Geometry.f4_roots_length
  rcases hcheck i j k l with (h1 | h1) | h1
  · exact hij h1
  · exact hkl h1
  · have h2 := h1 m (hlen ▸ hm)
    rw [hmv] at h2
    simp at h2

section Frames

variable (L : Type) [Field L]

@[expose] noncomputable def rhoL : SL(3, L) →* ModGL Tag.F4 L :=
  (MulAut.conj (canonicalRep (coxeterSystem Tag.F4) L trElemF)).toMonoidHom.comp (f4rhoLong L)

@[expose] def setL : Set (Fin Tag.F4.rank → ℤ) := {r | ∃ i j : Fin 3, i ≠ j ∧ r = sigmaL i j}

@[expose] def setS : Set (Fin Tag.F4.rank → ℤ) := {r | ∃ i j : Fin 3, i ≠ j ∧ r = f4ShortSigma i j}

variable {L}

theorem rhoL_frame : IsA2Frame (rhoL L) sigmaL := by
  have h := (f4Long_frame (L := L)).transport trElemF
  have he : (fun i j => trElemF • chainRoot (τ := Tag.F4) f4chainLong i j) = sigmaL :=
    funext fun i => funext fun j => trElem_smul_chainRoot i j
  rw [he] at h
  exact h

theorem range_rhoL : (rhoL L).range = rootSpan Tag.F4 L setL :=
  rhoL_frame.range

theorem range_rhoS : (f4rhoShort L).range = rootSpan Tag.F4 L setS :=
  f4Short_frame.range

theorem isRoot_of_mem_setL {r : Fin Tag.F4.rank → ℤ} (hr : r ∈ setL) : IsRoot Tag.F4 r := by
  obtain ⟨i, j, hij, rfl⟩ := hr
  exact (rhoL_frame (L := ℚ)).isRoot i j hij

theorem isRoot_of_mem_setS {r : Fin Tag.F4.rank → ℤ} (hr : r ∈ setS) : IsRoot Tag.F4 r := by
  obtain ⟨i, j, hij, rfl⟩ := hr
  exact (f4Short_frame (L := ℚ)).isRoot i j hij

theorem pinnedX_commute_sigma {α β : Fin Tag.F4.rank → ℤ} (hα : α ∈ setL) (hβ : β ∈ setS)
    (s t : L) : pinnedX Tag.F4 L α s * pinnedX Tag.F4 L β t =
      pinnedX Tag.F4 L β t * pinnedX Tag.F4 L α s := by
  have hαr := isRoot_of_mem_setL hα
  have hβr := isRoot_of_mem_setS hβ
  obtain ⟨i, j, hij, rfl⟩ := hα
  obtain ⟨k, l, hkl, rfl⟩ := hβ
  exact pinnedX_commute_of_iform_eq_zero L hαr hβr (iform_sigma i j k l)
    (not_isRoot_add_sigma hij hkl) s t

theorem commute_xS_yS {x y : ModGL Tag.F4 L} (hx : x ∈ (rhoL L).range)
    (hy : y ∈ (f4rhoShort L).range) : x * y = y * x := by
  rw [range_rhoL] at hx
  rw [range_rhoS] at hy
  have hA : ∀ α ∈ setL, ∀ s : L,
      rootSpan Tag.F4 L setS ≤ Subgroup.centralizer {pinnedX Tag.F4 L α s} := by
    intro α hα s
    refine iSup₂_le fun β hβ => (Subgroup.closure_le _).2 ?_
    rintro _ ⟨t, rfl⟩
    exact Subgroup.mem_centralizer_singleton_iff.2 (pinnedX_commute_sigma hα hβ s t).symm
  have hB : rootSpan Tag.F4 L setL ≤ Subgroup.centralizer {y} := by
    refine iSup₂_le fun α hα => (Subgroup.closure_le _).2 ?_
    rintro _ ⟨s, rfl⟩
    exact Subgroup.mem_centralizer_singleton_iff.2
      (Subgroup.mem_centralizer_singleton_iff.1 (hA α hα s hy)).symm
  exact Subgroup.mem_centralizer_singleton_iff.1 (hB hx)

end Frames

section Characters

variable {L : Type} [Field L]

theorem diag_mul_mul_inv (D : SL(3, L))
    (hD : ∀ i j : Fin 3, i ≠ j → (D : Matrix (Fin 3) (Fin 3) L) i j = 0)
    (hD0 : ∀ k, (D : Matrix (Fin 3) (Fin 3) L) k k ≠ 0) (A : SL(3, L)) :
    D * A * D⁻¹ = conjDiag3 (fun k => Units.mk0 _ (hD0 k)) A := by
  set d : Fin 3 → Lˣ := fun k => Units.mk0 _ (hD0 k) with hd
  have hDd : (D : Matrix (Fin 3) (Fin 3) L) = (diagGL3 d : Matrix (Fin 3) (Fin 3) L) := by
    ext i j
    by_cases hij : i = j
    · subst hij
      simp [diagGL3, hd]
    · simp [diagGL3, hD i j hij, Matrix.diagonal_apply_ne _ hij]
  have hinv : ((D⁻¹ : SL(3, L)) : Matrix (Fin 3) (Fin 3) L) =
      (((diagGL3 d)⁻¹ : GL (Fin 3) L) : Matrix (Fin 3) (Fin 3) L) := by
    have h1 : (D : Matrix (Fin 3) (Fin 3) L) *
        ((D⁻¹ : SL(3, L)) : Matrix (Fin 3) (Fin 3) L) = 1 := by
      have := congrArg (fun X : SL(3, L) => (X : Matrix (Fin 3) (Fin 3) L)) (mul_inv_cancel D)
      rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_one] at this
      exact this
    have h2 : (((diagGL3 d)⁻¹ : GL (Fin 3) L) : Matrix (Fin 3) (Fin 3) L) *
        (diagGL3 d : Matrix (Fin 3) (Fin 3) L) = 1 :=
      congrArg Units.val (inv_mul_cancel (diagGL3 d))
    calc ((D⁻¹ : SL(3, L)) : Matrix (Fin 3) (Fin 3) L) =
        ((((diagGL3 d)⁻¹ : GL (Fin 3) L) : Matrix (Fin 3) (Fin 3) L) *
          (diagGL3 d : Matrix (Fin 3) (Fin 3) L)) *
            ((D⁻¹ : SL(3, L)) : Matrix (Fin 3) (Fin 3) L) := by rw [h2, Matrix.one_mul]
      _ = _ := by rw [Matrix.mul_assoc, ← hDd, h1, Matrix.mul_one]
  apply Subtype.ext
  rw [coe_conjDiag3, Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, hinv,
    hDd]

theorem diag_ne_zero (D : SL(3, L))
    (hD : ∀ i j : Fin 3, i ≠ j → (D : Matrix (Fin 3) (Fin 3) L) i j = 0) (k : Fin 3) :
    (D : Matrix (Fin 3) (Fin 3) L) k k ≠ 0 := by
  have hdiag : (D : Matrix (Fin 3) (Fin 3) L) =
      Matrix.diagonal fun i => (D : Matrix (Fin 3) (Fin 3) L) i i := by
    ext i j
    by_cases hij : i = j
    · subst hij
      simp
    · simp [hD i j hij, Matrix.diagonal_apply_ne _ hij]
  have hdet : (Matrix.diagonal fun i => (D : Matrix (Fin 3) (Fin 3) L) i i).det = 1 := by
    rw [← hdiag]
    exact D.2
  rw [Matrix.det_diagonal] at hdet
  intro h0
  exact zero_ne_one ((Finset.prod_eq_zero (f := fun i => (D : Matrix (Fin 3) (Fin 3) L) i i)
    (Finset.mem_univ k) h0).symm.trans hdet)

theorem rootChar_of_frame_diag {ρ : SL(3, L) →* ModGL Tag.F4 L}
    {σ : Fin 3 → Fin 3 → Fin Tag.F4.rank → ℤ} (h : IsA2Frame ρ σ) (D : SL(3, L))
    (hD : ∀ i j : Fin 3, i ≠ j → (D : Matrix (Fin 3) (Fin 3) L) i j = 0)
    {c : Fin Tag.F4.rank → Lˣ} (hc : ρ D = rootDiagUnit Tag.F4 c) {i j : Fin 3} (hij : i ≠ j) :
    (rootChar c (σ i j) : L) =
      (D : Matrix (Fin 3) (Fin 3) L) i i * ((D : Matrix (Fin 3) (Fin 3) L) j j)⁻¹ := by
  obtain ⟨ε, hε⟩ := h.transv i j hij
  have hD0 := diag_ne_zero D hD
  have h1 := rootDiagUnit_conj_pinnedX c (h.isRoot i j hij) ((ε : L) * 1)
  rw [← hc, ← hε, ← map_inv, ← map_mul, ← map_mul, diag_mul_mul_inv D hD hD0,
    conjDiag3_transvection, hε] at h1
  have h2 := pinnedX_injective Tag.F4 L (σ i j) h1
  simp only [Units.val_mk0, mul_one, Units.val_inv_eq_inv_val] at h2
  have hε0 : (ε : L) ≠ 0 := ε.ne_zero
  have h3 : (ε : L) * ((D : Matrix (Fin 3) (Fin 3) L) i i *
      ((D : Matrix (Fin 3) (Fin 3) L) j j)⁻¹) = (ε : L) * (rootChar c (σ i j) : L) := by
    rw [h2]
    ring
  exact (mul_left_cancel₀ hε0 h3).symm

theorem rootChar_eq_one_of_commute {c : Fin Tag.F4.rank → Lˣ} {β : Fin Tag.F4.rank → ℤ}
    (hβ : IsRoot Tag.F4 β)
    (h : rootDiagUnit Tag.F4 c * pinnedX Tag.F4 L β 1 =
      pinnedX Tag.F4 L β 1 * rootDiagUnit Tag.F4 c) :
    rootChar c β = 1 := by
  have h1 := rootDiagUnit_conj_pinnedX c hβ (1 : L)
  rw [h, mul_inv_cancel_right] at h1
  have h2 := pinnedX_injective Tag.F4 L β h1
  rw [mul_one] at h2
  exact Units.ext h2.symm

end Characters

section Std

variable {L : Type} [Field L]

@[expose] def bStd (ζ : Lˣ) : Fin Tag.F4.rank → Lˣ := Pi.mulSingle 1 ζ

theorem rootChar_bStd (ζ : Lˣ) (v : Fin Tag.F4.rank → ℤ) : rootChar (bStd ζ) v = ζ ^ v 1 := by
  unfold rootChar bStd
  rw [Finset.prod_eq_single (1 : Fin Tag.F4.rank)]
  · simp
  · intro i _ hi
    simp [hi]
  · intro h
    exact absurd (Finset.mem_univ _) h

theorem rootDiagUnit_pow' (a : Fin Tag.F4.rank → Lˣ) (n : ℕ) :
    rootDiagUnit Tag.F4 a ^ n = rootDiagUnit Tag.F4 (a ^ n) := by
  induction n with
  | zero => rw [pow_zero, pow_zero, rootDiagUnit_one]
  | succ n ih => rw [pow_succ, ih, ← rootDiagUnit_mul, ← pow_succ]

variable {ζ : Lˣ}

theorem zpow_eq_one_iff_three_dvd (hζ : orderOf ζ = 3) (n : ℤ) : ζ ^ n = 1 ↔ (3 : ℤ) ∣ n := by
  rw [← orderOf_dvd_iff_zpow_eq_one, hζ]
  norm_cast

theorem mem_rootCharKernel_bStd (hζ : orderOf ζ = 3) {α : Fin Tag.F4.rank → ℤ} :
    α ∈ rootCharKernel (bStd ζ) ↔ IsRoot Tag.F4 α ∧ (3 : ℤ) ∣ α 1 := by
  show IsRoot _ α ∧ rootChar _ α = 1 ↔ _
  rw [rootChar_bStd, zpow_eq_one_iff_three_dvd hζ]

theorem rootCharKernel_bStd (hζ : orderOf ζ = 3) : rootCharKernel (bStd ζ) = setL ∪ setS := by
  ext α
  rw [mem_rootCharKernel_bStd hζ]
  constructor
  · rintro ⟨hα, h3⟩
    rcases kernel_cases hα h3 with h | h
    · exact Or.inl h
    · exact Or.inr h
  · rintro (⟨i, j, hij, rfl⟩ | ⟨i, j, hij, rfl⟩)
    · exact ⟨isRoot_of_mem_setL ⟨i, j, hij, rfl⟩, (three_dvd_sigma i j).1⟩
    · exact ⟨isRoot_of_mem_setS ⟨i, j, hij, rfl⟩, (three_dvd_sigma i j).2⟩

set_option maxRecDepth 10000 in
theorem sigma_values : sigmaL 0 1 = ![1, 0, 0, 0] ∧ sigmaL 1 2 = ![1, 3, 4, 2] ∧
    f4ShortSigma 1 0 = ![0, 0, 1, 0] ∧ f4ShortSigma 2 1 = ![0, 0, 0, 1] := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> funext l <;> fin_cases l <;> decide +kernel

theorem rootChar_vec (c : Fin Tag.F4.rank → Lˣ) (a b d e : ℤ) :
    rootChar c ![a, b, d, e] = c 0 ^ a * c 1 ^ b * c 2 ^ d * c 3 ^ e := by
  show (∏ i : Fin 4, c i ^ (![a, b, d, e] : Fin 4 → ℤ) i) = _
  rw [Fin.prod_univ_four]
  rfl

theorem eq_bStd_pow_of_trivial (hζ : orderOf ζ = 3) {c : Fin Tag.F4.rank → Lˣ}
    (h01 : rootChar c (sigmaL 0 1) = 1) (h12 : rootChar c (sigmaL 1 2) = 1)
    (h10 : rootChar c (f4ShortSigma 1 0) = 1) (h21 : rootChar c (f4ShortSigma 2 1) = 1) :
    ∃ k : ℕ, k < 3 ∧ c = bStd ζ ^ k := by
  obtain ⟨e01, e12, e10, e21⟩ := sigma_values
  rw [e01, rootChar_vec] at h01
  rw [e12, rootChar_vec] at h12
  rw [e10, rootChar_vec] at h10
  rw [e21, rootChar_vec] at h21
  simp only [zpow_one, zpow_zero, mul_one, one_mul] at h01 h10 h21
  rw [h01, h10, h21] at h12
  simp only [one_zpow, one_mul, mul_one] at h12
  have hc1 : ((c 1 : Lˣ) : L) ^ 3 = 1 := by
    rw [← Units.val_pow_eq_pow_val, ← zpow_natCast, Nat.cast_ofNat, h12, Units.val_one]
  have hprim : IsPrimitiveRoot (ζ : L) 3 :=
    IsPrimitiveRoot.coe_units_iff.2 (IsPrimitiveRoot.iff_orderOf.2 hζ)
  obtain ⟨k, hk, hk'⟩ := hprim.eq_pow_of_pow_eq_one hc1
  refine ⟨k, hk, funext fun i => ?_⟩
  rw [Pi.pow_apply]
  by_cases hi : i = 1
  · subst hi
    rw [bStd, Pi.mulSingle_eq_same]
    exact Units.ext (by rw [Units.val_pow_eq_pow_val, hk'])
  · rw [bStd, Pi.mulSingle_eq_of_ne hi, one_pow]
    fin_cases i
    · exact h01
    · exact absurd rfl hi
    · exact h10
    · exact h21

theorem pinnedX_mem_rangeS {β : Fin Tag.F4.rank → ℤ} (hβ : β ∈ setS) (t : L) :
    pinnedX Tag.F4 L β t ∈ (f4rhoShort L).range := by
  rw [range_rhoS]
  exact le_iSup₂_of_le (f := fun γ (_ : γ ∈ setS) => rootSubgroup Tag.F4 L γ) β hβ le_rfl
    (Subgroup.subset_closure ⟨t, rfl⟩)

theorem pinnedX_mem_rangeL {α : Fin Tag.F4.rank → ℤ} (hα : α ∈ setL) (t : L) :
    pinnedX Tag.F4 L α t ∈ (rhoL L).range := by
  rw [range_rhoL]
  exact le_iSup₂_of_le (f := fun γ (_ : γ ∈ setL) => rootSubgroup Tag.F4 L γ) α hα le_rfl
    (Subgroup.subset_closure ⟨t, rfl⟩)

theorem rootChar_short_of_mem_rangeL {c : Fin Tag.F4.rank → Lˣ}
    (hc : rootDiagUnit Tag.F4 c ∈ (rhoL L).range) {β : Fin Tag.F4.rank → ℤ} (hβ : β ∈ setS) :
    rootChar c β = 1 :=
  rootChar_eq_one_of_commute (isRoot_of_mem_setS hβ)
    (commute_xS_yS hc (pinnedX_mem_rangeS hβ 1))

theorem rootChar_long_of_mem_rangeS {c : Fin Tag.F4.rank → Lˣ}
    (hc : rootDiagUnit Tag.F4 c ∈ (f4rhoShort L).range) {α : Fin Tag.F4.rank → ℤ}
    (hα : α ∈ setL) : rootChar c α = 1 :=
  rootChar_eq_one_of_commute (isRoot_of_mem_setL hα)
    (commute_xS_yS (pinnedX_mem_rangeL hα 1) hc).symm

theorem mem_set_basic : sigmaL 0 1 ∈ setL ∧ sigmaL 1 2 ∈ setL ∧ f4ShortSigma 1 0 ∈ setS ∧
    f4ShortSigma 2 1 ∈ setS :=
  ⟨⟨0, 1, by decide, rfl⟩, ⟨1, 2, by decide, rfl⟩, ⟨1, 0, by decide, rfl⟩, ⟨2, 1, by decide, rfl⟩⟩

theorem rootChar_mul' (a b : Fin Tag.F4.rank → Lˣ) (v : Fin Tag.F4.rank → ℤ) :
    rootChar (a * b) v = rootChar a v * rootChar b v := by
  simp only [rootChar, Pi.mul_apply, mul_zpow, Finset.prod_mul_distrib]

theorem rootChar_inv' (a : Fin Tag.F4.rank → Lˣ) (v : Fin Tag.F4.rank → ℤ) :
    rootChar a⁻¹ v = (rootChar a v)⁻¹ := by
  simp only [rootChar, Pi.inv_apply, inv_zpow, Finset.prod_inv_distrib]

theorem bStd_pow_three (hζ : orderOf ζ = 3) : bStd ζ ^ 3 = 1 := by
  rw [bStd, ← Pi.mulSingle_pow, ← hζ, pow_orderOf_eq_one, Pi.mulSingle_one]

@[expose] noncomputable def scalarSL (hζ : orderOf ζ = 3) : SL(3, L) :=
  ⟨Matrix.diagonal fun _ => (ζ : L), by
    have h3 : (ζ : L) ^ 3 = 1 := by
      rw [← Units.val_pow_eq_pow_val, ← hζ, pow_orderOf_eq_one, Units.val_one]
    rw [Matrix.det_diagonal, Fin.prod_univ_three]
    calc (ζ : L) * ζ * ζ = (ζ : L) ^ 3 := by ring
      _ = 1 := h3⟩

variable [IsAlgClosed L]

theorem rootDiagUnit_bStd_mem_rangeL (hζ : orderOf ζ = 3) :
    rootDiagUnit Tag.F4 (bStd ζ) ∈ (rhoL L).range := by
  set Z := scalarSL hζ with hZ
  have hZd : ∀ i j : Fin 3, i ≠ j → (Z : Matrix (Fin 3) (Fin 3) L) i j = 0 :=
    fun i j hij => Matrix.diagonal_apply_ne _ hij
  obtain ⟨c, hc⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup (rhoL_frame.diag Z hZd)
  have hcX : rootDiagUnit Tag.F4 c ∈ (rhoL L).range := hc ▸ ⟨Z, rfl⟩
  have hval : ∀ i j : Fin 3, i ≠ j → rootChar c (sigmaL i j) = 1 := by
    intro i j hij
    refine Units.ext ?_
    rw [rootChar_of_frame_diag rhoL_frame Z hZd hc hij, Units.val_one]
    simp [hZ, scalarSL]
  obtain ⟨-, -, h10, h21⟩ := mem_set_basic
  obtain ⟨k, hk, rfl⟩ := eq_bStd_pow_of_trivial hζ (hval 0 1 (by decide)) (hval 1 2 (by decide))
    (rootChar_short_of_mem_rangeL hcX h10) (rootChar_short_of_mem_rangeL hcX h21)
  have h3 := bStd_pow_three hζ
  interval_cases k
  · exfalso
    rw [pow_zero, rootDiagUnit_one, ← map_one (rhoL L)] at hc
    have h1 := congrArg (fun X : SL(3, L) => (X : Matrix (Fin 3) (Fin 3) L) 0 0)
      ((rhoL_frame (L := L)).injective hc)
    simp only [hZ, scalarSL, Matrix.diagonal_apply_eq, Matrix.SpecialLinearGroup.coe_one,
      Matrix.one_apply_eq] at h1
    have : ζ = 1 := Units.ext h1
    rw [this, orderOf_one] at hζ
    exact absurd hζ (by norm_num)
  · rw [pow_one] at hcX
    exact hcX
  · have e : rootDiagUnit Tag.F4 (bStd ζ) = rootDiagUnit Tag.F4 (bStd ζ ^ 2) ^ 2 := by
      rw [rootDiagUnit_pow', ← pow_mul, show 2 * 2 = 3 + 1 by norm_num, pow_succ, h3, one_mul]
    rw [e]
    exact pow_mem hcX 2

theorem exists_cube_root (a : Lˣ) : ∃ r : Lˣ, r ^ 3 = a := by
  obtain ⟨z, hz⟩ := IsAlgClosed.exists_pow_nat_eq (a : L) (n := 3) (by norm_num)
  have hz0 : z ≠ 0 := by
    rintro rfl
    rw [zero_pow (by norm_num)] at hz
    exact a.ne_zero hz.symm
  exact ⟨Units.mk0 z hz0, Units.ext (by rw [Units.val_pow_eq_pow_val, Units.val_mk0, hz])⟩

theorem rootDiagUnit_mem_sup (hζ : orderOf ζ = 3) (c : Fin Tag.F4.rank → Lˣ) :
    rootDiagUnit Tag.F4 c ∈ (rhoL L).range ⊔ (f4rhoShort L).range := by
  obtain ⟨e01, e12, e10, e21⟩ := sigma_values
  obtain ⟨m01, m12, m10, m21⟩ := mem_set_basic
  set x : Lˣ := c 0 with hx
  set y : Lˣ := rootChar c (sigmaL 1 2) with hy
  obtain ⟨r, hr⟩ := exists_cube_root (y * x⁻¹)
  set D₁ : SL(3, L) := ⟨Matrix.diagonal ![(x : L) * r, r, r * ((y⁻¹ : Lˣ) : L)], by
    rw [Matrix.det_diagonal, Fin.prod_univ_three]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.head_cons, Matrix.tail_cons]
    have h1 : ((r : L)) ^ 3 = (y : L) * ((x⁻¹ : Lˣ) : L) := by
      rw [← Units.val_pow_eq_pow_val, hr, Units.val_mul]
    have hx0 : (x : L) ≠ 0 := x.ne_zero
    have hy0 : (y : L) ≠ 0 := y.ne_zero
    simp only [Units.val_inv_eq_inv_val] at h1 ⊢
    calc (x : L) * r * r * (r * (y : L)⁻¹) = (x : L) * (r : L) ^ 3 * (y : L)⁻¹ := by ring
      _ = 1 := by rw [h1]; field_simp⟩ with hD₁
  have hD₁d : ∀ i j : Fin 3, i ≠ j → (D₁ : Matrix (Fin 3) (Fin 3) L) i j = 0 :=
    fun i j hij => Matrix.diagonal_apply_ne _ hij
  obtain ⟨c₁, hc₁⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup (rhoL_frame.diag D₁ hD₁d)
  have hc₁X : rootDiagUnit Tag.F4 c₁ ∈ (rhoL L).range := hc₁ ▸ ⟨D₁, rfl⟩
  have hc₁01 : rootChar c₁ (sigmaL 0 1) = x := by
    refine Units.ext ?_
    rw [rootChar_of_frame_diag rhoL_frame D₁ hD₁d hc₁ (by decide : (0 : Fin 3) ≠ 1)]
    simp only [hD₁, Matrix.diagonal_apply_eq, Matrix.cons_val_zero, Matrix.cons_val_one]
    field_simp
  have hc₁12 : rootChar c₁ (sigmaL 1 2) = y := by
    refine Units.ext ?_
    rw [rootChar_of_frame_diag rhoL_frame D₁ hD₁d hc₁ (by decide : (1 : Fin 3) ≠ 2)]
    simp only [hD₁, Matrix.diagonal_apply_eq, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Units.val_inv_eq_inv_val]
    have hr0 : (r : L) ≠ 0 := r.ne_zero
    have hy0 : (y : L) ≠ 0 := y.ne_zero
    field_simp
  obtain ⟨s, hs⟩ := exists_cube_root (c 2 ^ 2 * c 3)⁻¹
  set D₂ : SL(3, L) := ⟨Matrix.diagonal ![(s : L), (c 2 : L) * s, (c 3 : L) * (c 2 : L) * s], by
    rw [Matrix.det_diagonal, Fin.prod_univ_three]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.head_cons, Matrix.tail_cons]
    have h1 : ((s : L)) ^ 3 = (((c 2 ^ 2 * c 3)⁻¹ : Lˣ) : L) := by
      rw [← Units.val_pow_eq_pow_val, hs]
    simp only [Units.val_inv_eq_inv_val, Units.val_mul, Units.val_pow_eq_pow_val] at h1
    have h20 : (c 2 : L) ≠ 0 := (c 2).ne_zero
    have h30 : (c 3 : L) ≠ 0 := (c 3).ne_zero
    calc (s : L) * ((c 2 : L) * s) * ((c 3 : L) * (c 2 : L) * s) =
        (c 2 : L) ^ 2 * (c 3 : L) * (s : L) ^ 3 := by ring
      _ = 1 := by rw [h1]; field_simp⟩ with hD₂
  have hD₂d : ∀ i j : Fin 3, i ≠ j → (D₂ : Matrix (Fin 3) (Fin 3) L) i j = 0 :=
    fun i j hij => Matrix.diagonal_apply_ne _ hij
  obtain ⟨c₂, hc₂⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup
    ((f4Short_frame (L := L)).diag D₂ hD₂d)
  have hc₂Y : rootDiagUnit Tag.F4 c₂ ∈ (f4rhoShort L).range := hc₂ ▸ ⟨D₂, rfl⟩
  have hc₂10 : rootChar c₂ (f4ShortSigma 1 0) = c 2 := by
    refine Units.ext ?_
    rw [rootChar_of_frame_diag f4Short_frame D₂ hD₂d hc₂ (by decide : (1 : Fin 3) ≠ 0)]
    simp only [hD₂, Matrix.diagonal_apply_eq, Matrix.cons_val_zero, Matrix.cons_val_one]
    have hs0 : (s : L) ≠ 0 := s.ne_zero
    field_simp
  have hc₂21 : rootChar c₂ (f4ShortSigma 2 1) = c 3 := by
    refine Units.ext ?_
    rw [rootChar_of_frame_diag f4Short_frame D₂ hD₂d hc₂ (by decide : (2 : Fin 3) ≠ 1)]
    simp only [hD₂, Matrix.diagonal_apply_eq, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
    have hs0 : (s : L) ≠ 0 := s.ne_zero
    have h20 : (c 2 : L) ≠ 0 := (c 2).ne_zero
    field_simp
  set e := c * (c₁ * c₂)⁻¹ with he
  have hchar : ∀ v, rootChar e v = rootChar c v * (rootChar c₁ v * rootChar c₂ v)⁻¹ := by
    intro v
    rw [he, rootChar_mul', rootChar_inv', rootChar_mul']
  have hc0 : rootChar c (sigmaL 0 1) = x := by
    rw [e01, rootChar_vec]
    simp [hx]
  have hc10 : rootChar c (f4ShortSigma 1 0) = c 2 := by
    rw [e10, rootChar_vec]
    simp
  have hc21 : rootChar c (f4ShortSigma 2 1) = c 3 := by
    rw [e21, rootChar_vec]
    simp
  obtain ⟨k, -, hk⟩ := eq_bStd_pow_of_trivial hζ
    (by rw [hchar, hc0, hc₁01, rootChar_long_of_mem_rangeS hc₂Y m01, mul_one, mul_inv_cancel])
    (by rw [hchar, ← hy, hc₁12, rootChar_long_of_mem_rangeS hc₂Y m12, mul_one, mul_inv_cancel])
    (by rw [hchar, hc10, rootChar_short_of_mem_rangeL hc₁X m10, hc₂10, one_mul, mul_inv_cancel])
    (by rw [hchar, hc21, rootChar_short_of_mem_rangeL hc₁X m21, hc₂21, one_mul, mul_inv_cancel])
  have hce : c = c₁ * c₂ * bStd ζ ^ k := by
    rw [← hk, he, mul_comm c (c₁ * c₂)⁻¹, ← mul_assoc, mul_inv_cancel, one_mul]
  rw [hce, rootDiagUnit_mul, rootDiagUnit_mul, ← rootDiagUnit_pow']
  exact mul_mem (mul_mem (Subgroup.mem_sup_left hc₁X) (Subgroup.mem_sup_right hc₂Y))
    (Subgroup.mem_sup_left (pow_mem (rootDiagUnit_bStd_mem_rangeL hζ) k))

theorem exists_mul_of_mem_sup {g : ModGL Tag.F4 L}
    (hg : g ∈ (rhoL L).range ⊔ (f4rhoShort L).range) :
    ∃ x ∈ (rhoL L).range, ∃ y ∈ (f4rhoShort L).range, g = x * y := by
  have hle : (rhoL L).range ≤
      Subgroup.normalizer ((f4rhoShort L).range : Set (ModGL Tag.F4 L)) := by
    intro x hx
    refine Subgroup.mem_normalizer_iff.2 fun y => ?_
    constructor
    · intro hy
      have h1 : x * y * x⁻¹ = y := by rw [commute_xS_yS hx hy, mul_inv_cancel_right]
      rw [h1]
      exact hy
    · intro hy
      have h2 : x⁻¹ * (x * y * x⁻¹) * x⁻¹⁻¹ = x * y * x⁻¹ := by
        rw [commute_xS_yS (inv_mem hx) hy, inv_inv, inv_mul_cancel_right]
      have h3 : y = x⁻¹ * (x * y * x⁻¹) * x⁻¹⁻¹ := by group
      rw [h3, h2]
      exact hy
  have hset := Subgroup.coe_mul_of_left_le_normalizer_right _ _ hle
  have hg' : g ∈ ((rhoL L).range : Set (ModGL Tag.F4 L)) *
      ((f4rhoShort L).range : Set (ModGL Tag.F4 L)) := by
    rw [← hset]
    exact hg
  obtain ⟨x, hx, y, hy, rfl⟩ := hg'
  exact ⟨x, hx, y, hy, rfl⟩

theorem mem_sup_of_commute_bStd (hζ : orderOf ζ = 3) {g : ModGL Tag.F4 L}
    (hg : g ∈ adjointGroup Tag.F4 L)
    (hcomm : g * rootDiagUnit Tag.F4 (bStd ζ) = rootDiagUnit Tag.F4 (bStd ζ) * g) :
    g ∈ (rhoL L).range ⊔ (f4rhoShort L).range := by
  have hS : ∀ α ∈ rootCharKernel (bStd ζ), IsRoot Tag.F4 α := fun α hα => hα.1
  have hSn : ∀ α ∈ rootCharKernel (bStd ζ), -α ∈ rootCharKernel (bStd ζ) := by
    intro α hα
    rw [mem_rootCharKernel_bStd hζ] at hα ⊢
    exact ⟨CFSG.LieType.Chevalley.IsRoot.neg hα.1, by simpa using hα.2⟩
  have hgen : ∀ g : Fin 4, stdGenRoot g ∈ rootCharKernel (bStd ζ) := by
    intro g
    refine (mem_rootCharKernel_bStd hζ).2 ?_
    have h02 : stdGenRoot 1 = sigmaL 0 2 := by
      funext l
      fin_cases l <;> decide +kernel
    fin_cases g
    · exact ⟨isRoot_single _ _, by decide⟩
    · refine ⟨?_, by decide +kernel⟩
      change IsRoot Tag.F4 (stdGenRoot 1)
      rw [h02]
      exact isRoot_of_mem_setL ⟨0, 2, by decide, rfl⟩
    · exact ⟨isRoot_single _ _, by decide⟩
    · exact ⟨isRoot_single _ _, by decide⟩
  have hstab : rootCharStabilizer (bStd ζ) ⊆ (Subgroup.closure
      {s | ∃ α ∈ rootCharKernel (bStd ζ), s = rootReflection α} : Set (WeylGroup Tag.F4)) := by
    intro w hw
    refine mem_closure_of_stdStab (S := rootCharKernel (bStd ζ)) hgen fun j => ?_
    have h := hw (Pi.single j 1)
    rw [rootChar_bStd, rootChar_bStd] at h
    have h2 : ζ ^ ((w • (Pi.single j 1 : Fin Tag.F4.rank → ℤ)) 1 -
        (Pi.single j 1 : Fin Tag.F4.rank → ℤ) 1) = 1 := by
      rw [zpow_sub, h, mul_inv_cancel]
    have h3 := (zpow_eq_one_iff_three_dvd hζ _).1 h2
    have h4 : (Pi.single j 1 : Fin Tag.F4.rank → ℤ) 1 = if j = 1 then 1 else 0 := by
      by_cases hj : j = 1
      · subst hj
        rw [Pi.single_eq_same]
        simp
      · rw [Pi.single_eq_of_ne (Ne.symm hj)]
        simp [hj]
    rw [h4] at h3
    exact h3
  obtain ⟨h, hh, q, hq, rfl⟩ := mem_torus_mul_rootSpan_of_commute_of_stab hstab hS hSn
    subset_rfl hg hcomm
  refine mul_mem ?_ ?_
  · obtain ⟨c, rfl⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup hh
    exact rootDiagUnit_mem_sup hζ c
  · rw [rootCharKernel_bStd hζ] at hq
    refine (iSup₂_le fun α hα => ?_ : rootSpan Tag.F4 L (setL ∪ setS) ≤ _) hq
    rcases hα with hα | hα
    · refine le_trans ?_ le_sup_left
      rw [range_rhoL]
      exact le_iSup₂_of_le (f := fun γ (_ : γ ∈ setL) => rootSubgroup Tag.F4 L γ) α hα le_rfl
    · refine le_trans ?_ le_sup_right
      rw [range_rhoS]
      exact le_iSup₂_of_le (f := fun γ (_ : γ ∈ setS) => rootSubgroup Tag.F4 L γ) α hα le_rfl

theorem mem_inf_xS_yS (hζ : orderOf ζ = 3) {g : ModGL Tag.F4 L} (hX : g ∈ (rhoL L).range)
    (hY : g ∈ (f4rhoShort L).range) :
    ∃ k : ℕ, k < 3 ∧ g = rootDiagUnit Tag.F4 (bStd ζ) ^ k := by
  obtain ⟨M, rfl⟩ := hX
  have hMc : M ∈ Subgroup.center (SL(3, L)) := by
    refine Subgroup.mem_center_iff.2 fun A => (rhoL_frame (L := L)).injective ?_
    rw [map_mul, map_mul]
    exact commute_xS_yS ⟨A, rfl⟩ hY
  obtain ⟨r, hr3, hrM⟩ := Matrix.SpecialLinearGroup.mem_center_iff.1 hMc
  have hr0 : r ≠ 0 := by
    rintro rfl
    rw [zero_pow (by simp)] at hr3
    exact zero_ne_one hr3
  have hMd : ∀ i j : Fin 3, i ≠ j → (M : Matrix (Fin 3) (Fin 3) L) i j = 0 := by
    intro i j hij
    rw [← hrM]
    exact Matrix.diagonal_apply_ne _ hij
  obtain ⟨c, hc⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup (rhoL_frame.diag M hMd)
  have hcX : rootDiagUnit Tag.F4 c ∈ (rhoL L).range := hc ▸ ⟨M, rfl⟩
  have hval : ∀ i j : Fin 3, i ≠ j → rootChar c (sigmaL i j) = 1 := by
    intro i j hij
    refine Units.ext ?_
    rw [rootChar_of_frame_diag rhoL_frame M hMd hc hij, Units.val_one, ← hrM]
    simp [Matrix.scalar_apply, hr0]
  obtain ⟨-, -, h10, h21⟩ := mem_set_basic
  obtain ⟨k, hk, rfl⟩ := eq_bStd_pow_of_trivial hζ (hval 0 1 (by decide)) (hval 1 2 (by decide))
    (rootChar_short_of_mem_rangeL hcX h10) (rootChar_short_of_mem_rangeL hcX h21)
  exact ⟨k, hk, by rw [hc, rootDiagUnit_pow']⟩

theorem commute_bStd_pinnedX {α : Fin Tag.F4.rank → ℤ}
    (hα : α ∈ rootCharKernel (bStd ζ)) (t : L) :
    pinnedX Tag.F4 L α t * rootDiagUnit Tag.F4 (bStd ζ) =
      rootDiagUnit Tag.F4 (bStd ζ) * pinnedX Tag.F4 L α t := by
  have h1 := rootDiagUnit_conj_pinnedX (bStd ζ) hα.1 t
  rw [hα.2, Units.val_one, one_mul] at h1
  exact (mul_inv_eq_iff_eq_mul.1 h1).symm

theorem commute_bStd_of_mem_sup (hζ : orderOf ζ = 3) {g : ModGL Tag.F4 L}
    (hg : g ∈ (rhoL L).range ⊔ (f4rhoShort L).range) :
    g * rootDiagUnit Tag.F4 (bStd ζ) = rootDiagUnit Tag.F4 (bStd ζ) * g := by
  have hle : (rhoL L).range ⊔ (f4rhoShort L).range ≤
      Subgroup.centralizer {rootDiagUnit Tag.F4 (bStd ζ)} := by
    rw [range_rhoL, range_rhoS]
    refine sup_le (iSup₂_le fun α hα => (Subgroup.closure_le _).2 ?_)
      (iSup₂_le fun α hα => (Subgroup.closure_le _).2 ?_)
    · rintro _ ⟨t, rfl⟩
      exact Subgroup.mem_centralizer_singleton_iff.2 (commute_bStd_pinnedX
        (by rw [rootCharKernel_bStd hζ]; exact Or.inl hα) t)
    · rintro _ ⟨t, rfl⟩
      exact Subgroup.mem_centralizer_singleton_iff.2 (commute_bStd_pinnedX
        (by rw [rootCharKernel_bStd hζ]; exact Or.inr hα) t)
  exact Subgroup.mem_centralizer_singleton_iff.1 (hle hg)

end Std

end CFSG.RankThree.PartTwo.Sec8.ReeF4Conj2Proof
