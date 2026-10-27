module

public import CFSG.RankThree.PartTwo.Sec11.KS11Lie6ProofShort

public section

set_option linter.unusedSectionVars false

namespace CFSG.RankThree.PartTwo.Sec11.KS11Lie6Proof

open Matrix
open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.Chevalley
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.RankThree.PartTwo.Sec11.KS11Lie5Proof
open scoped MatrixGroups

section DiagConj

variable {L : Type} [Field L]

@[expose] def diagConjMat (a : Lˣ) (A : Matrix (Fin 2) (Fin 2) L) : Matrix (Fin 2) (Fin 2) L :=
  !![A 0 0, (a : L) * A 0 1; ((a⁻¹ : Lˣ) : L) * A 1 0, A 1 1]

theorem det_diagConjMat (a : Lˣ) (A : Matrix (Fin 2) (Fin 2) L) :
    (diagConjMat a A).det = A.det := by
  rw [diagConjMat, Matrix.det_fin_two_of, Matrix.det_fin_two]
  have ha : (a : L) * ((a⁻¹ : Lˣ) : L) = 1 := Units.mul_inv a
  linear_combination -(A 0 1 * A 1 0) * ha

theorem diagConjMat_mul (a : Lˣ) (A B : Matrix (Fin 2) (Fin 2) L) :
    diagConjMat a (A * B) = diagConjMat a A * diagConjMat a B := by
  have ha : (a : L) * (a : L)⁻¹ = 1 := mul_inv_cancel₀ (Units.ne_zero a)
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [diagConjMat, Matrix.mul_apply, Fin.sum_univ_two] <;>
    first
    | ring1
    | linear_combination -(A 0 1 * B 1 0) * ha
    | linear_combination -(A 1 0 * B 0 1) * ha

@[expose] def diagConj (a : Lˣ) : SL2 L →* SL2 L where
  toFun A := ⟨diagConjMat a A, by rw [det_diagConjMat]; exact A.2⟩
  map_one' := by
    refine Subtype.ext (Matrix.ext fun i j => ?_)
    fin_cases i <;> fin_cases j <;> simp [diagConjMat]
  map_mul' A B := Subtype.ext (diagConjMat_mul a A B)

theorem coe_diagConj (a : Lˣ) (A : SL2 L) :
    ((diagConj a A : SL2 L) : Matrix (Fin 2) (Fin 2) L) = diagConjMat a A := rfl

theorem diagConj_uSL (a : Lˣ) (s : L) : diagConj a (uSL s) = uSL ((a : L) * s) :=
  SL2_ext (by simp [coe_diagConj, diagConjMat, coe_uSL]) (by simp [coe_diagConj, diagConjMat,
    coe_uSL]) (by simp [coe_diagConj, diagConjMat, coe_uSL]) (by simp [coe_diagConj, diagConjMat,
    coe_uSL])

theorem diagConj_vSL (a : Lˣ) (s : L) : diagConj a (vSL s) = vSL (((a⁻¹ : Lˣ) : L) * s) :=
  SL2_ext (by simp [coe_diagConj, diagConjMat, coe_vSL]) (by simp [coe_diagConj, diagConjMat,
    coe_vSL]) (by simp [coe_diagConj, diagConjMat, coe_vSL]) (by simp [coe_diagConj, diagConjMat,
    coe_vSL])

theorem diagConj_HSL (a : Lˣ) (u : Lˣ) : diagConj a (HSL u) = HSL u :=
  SL2_ext (by simp [coe_diagConj, diagConjMat, coe_HSL]) (by simp [coe_diagConj, diagConjMat,
    coe_HSL]) (by simp [coe_diagConj, diagConjMat, coe_HSL]) (by simp [coe_diagConj, diagConjMat,
    coe_HSL])

theorem HSL_mul_units (a b : Lˣ) : (HSL a : SL2 L) * HSL b = HSL (a * b) := by
  refine SL2_ext ?_ ?_ ?_ ?_ <;>
    simp [coe_HSL, Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two, mul_comm]

theorem HSL_units_one : (HSL (1 : Lˣ) : SL2 L) = 1 :=
  SL2_ext (by simp [coe_HSL]) (by simp [coe_HSL]) (by simp [coe_HSL]) (by simp [coe_HSL])

theorem WSL_eq : (WSL : SL2 L) = uSL 1 * vSL (-1) * uSL 1 :=
  SL2_ext (by simp [coe_uSL, coe_vSL, coe_WSL, Matrix.mul_apply, Fin.sum_univ_two])
    (by simp [coe_uSL, coe_vSL, coe_WSL, Matrix.mul_apply, Fin.sum_univ_two])
    (by simp [coe_uSL, coe_vSL, coe_WSL, Matrix.mul_apply, Fin.sum_univ_two])
    (by simp [coe_uSL, coe_vSL, coe_WSL, Matrix.mul_apply, Fin.sum_univ_two])

end DiagConj

section RankOne

variable
  {L : Type} [Field L]

theorem twistHom_rankOneHom_D4 (Fr : L →+* L) (i : Fin TwistTag.D4.tag.rank) (A : SL2 L) :
    twistHom TwistTag.D4 L Fr (rankOneHom TwistTag.D4 L i A) =
      rankOneHom TwistTag.D4 L (TwistTag.D4.perm i) (Matrix.SpecialLinearGroup.map Fr A) := by
  have h := SL2_hom_ext (φ := (twistHom TwistTag.D4 L Fr).comp (rankOneHom TwistTag.D4 L i))
    (ψ := (rankOneHom TwistTag.D4 L (TwistTag.D4.perm i)).comp
      (Matrix.SpecialLinearGroup.map Fr))
    (fun s => by simp only [MonoidHom.comp_apply, rankOneHom_uSL, twistHom_xUnit, map_uSL])
    (fun u => by simp only [MonoidHom.comp_apply, rankOneHom_HSL, twistHom_torusElt, map_HSL])
    (by simp only [MonoidHom.comp_apply, rankOneHom_WSL, twistHom_weylElt_one, map_WSL])
  exact DFunLike.congr_fun h A

theorem rootChar_single (b : Fin TwistTag.D4.tag.rank → Lˣ) (i : Fin TwistTag.D4.tag.rank) :
    rootChar b (Pi.single i 1) = b i := by
  have := rootChar_nsmul_single b i 1
  rwa [one_nsmul, pow_one] at this

theorem rootChar_neg_single (b : Fin TwistTag.D4.tag.rank → Lˣ) (i : Fin TwistTag.D4.tag.rank) :
    rootChar b (-Pi.single i 1) = (b i)⁻¹ := by
  rw [← rootChar_single b i]
  simp only [rootChar, Pi.neg_apply, _root_.zpow_neg, Finset.prod_inv_distrib]

theorem rootDiagUnit_conj_rankOneHom (b : Fin TwistTag.D4.tag.rank → Lˣ)
    (i : Fin TwistTag.D4.tag.rank) (A : SL2 L) :
    rootDiagUnit TwistTag.D4.tag b * rankOneHom TwistTag.D4 L i A *
        (rootDiagUnit TwistTag.D4.tag b)⁻¹ =
      rankOneHom TwistTag.D4 L i (diagConj (b i) A) := by
  set φ : SL2 L →* ModGL TwistTag.D4.tag L :=
    (MulAut.conj (rootDiagUnit TwistTag.D4.tag b)).toMonoidHom.comp
      (rankOneHom TwistTag.D4 L i) with hφ
  set ψ : SL2 L →* ModGL TwistTag.D4.tag L :=
    (rankOneHom TwistTag.D4 L i).comp (diagConj (b i)) with hψ
  have hu : ∀ s, φ (uSL s) = ψ (uSL s) := fun s => by
    simp only [hφ, hψ, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply,
      rankOneHom_uSL, diagConj_uSL]
    rw [← pinnedX_single, ← pinnedX_single, rootDiagUnit_conj_pinnedX b (isRoot_single _ i),
      rootChar_single]
  have hv : ∀ s, φ (vSL s) = ψ (vSL s) := fun s => by
    simp only [hφ, hψ, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply,
      rankOneHom_vSL, diagConj_vSL]
    rw [← pinnedX_neg_single, ← pinnedX_neg_single,
      rootDiagUnit_conj_pinnedX b (IsRoot.neg (isRoot_single _ i)), rootChar_neg_single]
  have h := SL2_hom_ext (φ := φ) (ψ := ψ) hu
    (fun u => by
      simp only [hφ, hψ, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply,
        rankOneHom_HSL, diagConj_HSL]
      rw [rootDiagUnit_mul_comm_of_mem_torusGroup b (torusElt_mem_torusGroup i u),
        mul_inv_cancel_right])
    (by rw [WSL_eq, map_mul, map_mul, map_mul, map_mul, hu, hv])
  exact DFunLike.congr_fun h A

end RankOne

section Outer

variable
  {L : Type} [Field L]

theorem commute_rankOneHom_outer {i j : Fin TwistTag.D4.tag.rank}
    (hi : i = n0 ∨ i = n1 ∨ i = n3) (hj : j = n0 ∨ j = n1 ∨ j = n3) (hij : i ≠ j)
    (A B : SL2 L) : Commute (rankOneHom TwistTag.D4 L i A) (rankOneHom TwistTag.D4 L j B) := by
  have hmem : ∀ k : Fin TwistTag.D4.tag.rank, (k = n0 ∨ k = n1 ∨ k = n3) →
      k ∈ TwistTag.D4.orbit KS11Lie4Proof.d4Outer := by
    intro k hk
    rcases hk with rfl | rfl | rfl <;> decide
  exact commute_rankOneHom (K := L) (hmem i hi) (hmem j hj) hij A B

theorem twistHom_outerTriple (Fr : L →+* L) (A B C : SL2 L) :
    twistHom TwistTag.D4 L Fr (outerTriple L (A, B, C)) =
      outerTriple L (Matrix.SpecialLinearGroup.map Fr C, Matrix.SpecialLinearGroup.map Fr A,
        Matrix.SpecialLinearGroup.map Fr B) := by
  rw [outerTriple_apply, outerTriple_apply, map_mul, map_mul, twistHom_rankOneHom_D4,
    twistHom_rankOneHom_D4, twistHom_rankOneHom_D4]
  have p0 : TwistTag.D4.perm n0 = n1 := by decide
  have p1 : TwistTag.D4.perm n1 = n3 := by decide
  have p3 : TwistTag.D4.perm n3 = n0 := by decide
  simp only [p0, p1, p3]
  have c1 := commute_rankOneHom_outer (L := L) (Or.inr (Or.inl rfl)) (Or.inl rfl) (by decide)
    (Matrix.SpecialLinearGroup.map Fr A) (Matrix.SpecialLinearGroup.map Fr C)
  have c3 := commute_rankOneHom_outer (L := L) (Or.inr (Or.inr rfl)) (Or.inl rfl) (by decide)
    (Matrix.SpecialLinearGroup.map Fr B) (Matrix.SpecialLinearGroup.map Fr C)
  rw [mul_assoc, c3.eq, ← mul_assoc, c1.eq]

theorem outerTriple_HSL_units (a b c : Lˣ) :
    outerTriple L (HSL a, HSL b, HSL c) = rootDiagUnit TwistTag.D4.tag (fun j =>
      a ^ TwistTag.D4.tag.cartan n0 j * b ^ TwistTag.D4.tag.cartan n1 j *
        c ^ TwistTag.D4.tag.cartan n3 j) := by
  rw [outerTriple_apply, rankOneHom_HSL, rankOneHom_HSL, rankOneHom_HSL,
    LieType.Chevalley.torusElt_eq_rootDiagUnit, LieType.Chevalley.torusElt_eq_rootDiagUnit,
    LieType.Chevalley.torusElt_eq_rootDiagUnit, ← rootDiagUnit_mul, ← rootDiagUnit_mul]
  rfl

theorem eq_one_or_neg_one_of_commute (i : Fin TwistTag.D4.tag.rank) {A : SL2 L}
    (h : ∀ D : SL2 L, rankOneHom TwistTag.D4 L i A * rankOneHom TwistTag.D4 L i D =
      rankOneHom TwistTag.D4 L i D * rankOneHom TwistTag.D4 L i A) :
    A = 1 ∨ A = -1 := by
  have hker := (exceptional_ordinary_rank_one_central_image (τ := TwistTag.D4.tag) (K := L)
    i).choose_spec.2.2.2.2.2.1
  have key : ∀ D : SL2 L, Matrix.trace (D : Matrix (Fin 2) (Fin 2) L) = 2 → A * D = D * A := by
    intro D hD
    have hc : A * D * A⁻¹ * D⁻¹ ∈ (rankOneHom TwistTag.D4 L i).ker := by
      rw [MonoidHom.mem_ker, map_mul, map_mul, map_mul, map_inv, map_inv, h D]
      group
    obtain ⟨l, hl2, hl⟩ := hker _ hc
    have hl' : ((A * D * A⁻¹ : SL2 L) : Matrix (Fin 2) (Fin 2) L) =
        (l : L) • (D : Matrix (Fin 2) (Fin 2) L) := by
      have e : A * D * A⁻¹ = A * D * A⁻¹ * D⁻¹ * D := by group
      rw [e, Matrix.SpecialLinearGroup.coe_mul, hl, Matrix.smul_mul, Matrix.one_mul]
    have htr : Matrix.trace ((A * D * A⁻¹ : SL2 L) : Matrix (Fin 2) (Fin 2) L) =
        Matrix.trace (D : Matrix (Fin 2) (Fin 2) L) := by
      rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul,
        Matrix.trace_mul_cycle, ← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel,
        Matrix.SpecialLinearGroup.coe_one, Matrix.one_mul]
    rw [hl', Matrix.trace_smul, hD, smul_eq_mul] at htr
    have hl1 : (l : L) = 1 := by
      by_cases h2 : (2 : L) = 0
      · have : ((l : L) - 1) ^ 2 = 0 := by linear_combination hl2 + (1 - (l : L)) * h2
        exact sub_eq_zero.1 (pow_eq_zero_iff (by norm_num) |>.1 this)
      · have : ((l : L) - 1) * 2 = 0 := by linear_combination htr
        exact sub_eq_zero.1 ((mul_eq_zero.1 this).resolve_right h2)
    have hone : A * D * A⁻¹ * D⁻¹ = 1 := by
      apply Subtype.ext
      rw [hl, hl1, one_smul, Matrix.SpecialLinearGroup.coe_one]
    calc A * D = A * D * A⁻¹ * D⁻¹ * (D * A) := by group
      _ = D * A := by rw [hone, one_mul]
  have hu := key (uSL 1) (by simp [coe_uSL, Matrix.trace_fin_two]; norm_num)
  have hv := key (vSL 1) (by simp [coe_vSL, Matrix.trace_fin_two]; norm_num)
  have hu' : (A : Matrix (Fin 2) (Fin 2) L) * !![1, 1; 0, 1] =
      !![1, 1; 0, 1] * (A : Matrix (Fin 2) (Fin 2) L) := by
    have := congrArg (fun X : SL2 L => (X : Matrix (Fin 2) (Fin 2) L)) hu
    simpa [coe_uSL] using this
  have hv' : (A : Matrix (Fin 2) (Fin 2) L) * !![1, 0; 1, 1] =
      !![1, 0; 1, 1] * (A : Matrix (Fin 2) (Fin 2) L) := by
    have := congrArg (fun X : SL2 L => (X : Matrix (Fin 2) (Fin 2) L)) hv
    simpa [coe_vSL] using this
  have hsc := CFSG.RankThree.QuadraticSL2.eq_scalar_of_commute _ hu' hv'
  set c := (A : Matrix (Fin 2) (Fin 2) L) 0 0 with hc
  have hdet : c ^ 2 = 1 := by
    have h := A.2
    rw [Matrix.det_fin_two, hsc] at h
    simpa [Matrix.scalar_apply, Matrix.diagonal, sq] using h
  have hc' : c = 1 ∨ c = -1 := by
    have : (c - 1) * (c + 1) = 0 := by linear_combination hdet
    rcases mul_eq_zero.1 this with h | h
    · exact Or.inl (sub_eq_zero.1 h)
    · exact Or.inr (eq_neg_of_add_eq_zero_left h)
  rcases hc' with h1 | h1
  · left
    apply Subtype.ext
    rw [hsc, h1, Matrix.SpecialLinearGroup.coe_one, map_one]
  · right
    apply Subtype.ext
    rw [hsc, h1, Matrix.SpecialLinearGroup.coe_neg, Matrix.SpecialLinearGroup.coe_one, map_neg,
      map_one]

theorem neg_one_eq_HSL : (-1 : SL2 L) = HSL (-1) :=
  SL2_ext (by simp [coe_HSL]) (by simp [coe_HSL]) (by simp [coe_HSL]) (by simp [coe_HSL])

theorem outerTriple_ker {A B C : SL2 L} (h : outerTriple L (A, B, C) = 1) :
    (A = 1 ∨ A = -1) ∧ (B = 1 ∨ B = -1) ∧ (C = 1 ∨ C = -1) ∧ A * B * C = 1 := by
  rw [outerTriple_apply] at h
  simp only at h
  have h0 : n0 = n0 ∨ n0 = n1 ∨ n0 = n3 := Or.inl rfl
  have h1 : n1 = n0 ∨ n1 = n1 ∨ n1 = n3 := Or.inr (Or.inl rfl)
  have h3 : n3 = n0 ∨ n3 = n1 ∨ n3 = n3 := Or.inr (Or.inr rfl)
  have hA : A = 1 ∨ A = -1 := by
    refine eq_one_or_neg_one_of_commute n0 fun D => ?_
    have e : rankOneHom TwistTag.D4 L n0 A = (rankOneHom TwistTag.D4 L n1 B *
        rankOneHom TwistTag.D4 L n3 C)⁻¹ := by
      calc rankOneHom TwistTag.D4 L n0 A = rankOneHom TwistTag.D4 L n0 A *
            rankOneHom TwistTag.D4 L n1 B * rankOneHom TwistTag.D4 L n3 C *
              (rankOneHom TwistTag.D4 L n1 B * rankOneHom TwistTag.D4 L n3 C)⁻¹ := by group
        _ = _ := by rw [h, one_mul]
    rw [e]
    have c1 := (commute_rankOneHom_outer (L := L) h0 h1 (by decide) D B).symm
    have c3 := (commute_rankOneHom_outer (L := L) h0 h3 (by decide) D C).symm
    exact ((c1.mul_left c3).inv_left).eq
  have hB : B = 1 ∨ B = -1 := by
    refine eq_one_or_neg_one_of_commute n1 fun D => ?_
    have e : rankOneHom TwistTag.D4 L n1 B = (rankOneHom TwistTag.D4 L n0 A)⁻¹ *
        (rankOneHom TwistTag.D4 L n3 C)⁻¹ := by
      calc rankOneHom TwistTag.D4 L n1 B = (rankOneHom TwistTag.D4 L n0 A)⁻¹ *
            (rankOneHom TwistTag.D4 L n0 A * rankOneHom TwistTag.D4 L n1 B *
              rankOneHom TwistTag.D4 L n3 C) * (rankOneHom TwistTag.D4 L n3 C)⁻¹ := by group
        _ = _ := by rw [h, mul_one]
    rw [e]
    have c0 := (commute_rankOneHom_outer (L := L) h1 h0 (by decide) D A).symm
    have c3 := (commute_rankOneHom_outer (L := L) h1 h3 (by decide) D C).symm
    exact (c0.inv_left.mul_left c3.inv_left).eq
  have hC : C = 1 ∨ C = -1 := by
    refine eq_one_or_neg_one_of_commute n3 fun D => ?_
    have e : rankOneHom TwistTag.D4 L n3 C = (rankOneHom TwistTag.D4 L n0 A *
        rankOneHom TwistTag.D4 L n1 B)⁻¹ := by
      calc rankOneHom TwistTag.D4 L n3 C = (rankOneHom TwistTag.D4 L n0 A *
            rankOneHom TwistTag.D4 L n1 B)⁻¹ * (rankOneHom TwistTag.D4 L n0 A *
              rankOneHom TwistTag.D4 L n1 B * rankOneHom TwistTag.D4 L n3 C) := by group
        _ = _ := by rw [h, mul_one]
    rw [e]
    have c0 := (commute_rankOneHom_outer (L := L) h3 h0 (by decide) D A).symm
    have c1 := (commute_rankOneHom_outer (L := L) h3 h1 (by decide) D B).symm
    exact ((c0.mul_left c1).inv_left).eq
  refine ⟨hA, hB, hC, ?_⟩
  obtain ⟨a, ha2, rfl⟩ : ∃ a : Lˣ, a ^ 2 = 1 ∧ A = HSL a := by
    rcases hA with rfl | rfl
    · exact ⟨1, one_pow 2, HSL_units_one.symm⟩
    · exact ⟨-1, by norm_num, neg_one_eq_HSL⟩
  obtain ⟨b, hb2, rfl⟩ : ∃ b : Lˣ, b ^ 2 = 1 ∧ B = HSL b := by
    rcases hB with rfl | rfl
    · exact ⟨1, one_pow 2, HSL_units_one.symm⟩
    · exact ⟨-1, by norm_num, neg_one_eq_HSL⟩
  obtain ⟨c, hc2, rfl⟩ : ∃ c : Lˣ, c ^ 2 = 1 ∧ C = HSL c := by
    rcases hC with rfl | rfl
    · exact ⟨1, one_pow 2, HSL_units_one.symm⟩
    · exact ⟨-1, by norm_num, neg_one_eq_HSL⟩
  have hd := outerTriple_HSL_units (L := L) a b c
  rw [outerTriple_apply] at hd
  simp only at hd
  rw [h, ← rootDiagUnit_one] at hd
  have h2 := congrFun (CFSG.LieType.Chevalley.rootDiagUnit_injective hd) n2
  have e0 : TwistTag.D4.tag.cartan n0 n2 = -1 := by decide
  have e1 : TwistTag.D4.tag.cartan n1 n2 = -1 := by decide
  have e3 : TwistTag.D4.tag.cartan n3 n2 = -1 := by decide
  simp only [Pi.one_apply, e0, e1, e3, _root_.zpow_neg_one] at h2
  have habc : a * b * c = 1 := by
    have : (a⁻¹ * b⁻¹ * c⁻¹)⁻¹ = (1 : Lˣ)⁻¹ := by rw [← h2]
    simpa only [mul_inv, inv_inv, inv_one] using this
  rw [HSL_mul_units, HSL_mul_units, habc, HSL_units_one]

end Outer

end CFSG.RankThree.PartTwo.Sec11.KS11Lie6Proof
