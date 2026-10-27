module

public import CFSG.RankThree.PartTwo.Sec19.Item19Res6ProofUnitaryNF
public import CFSG.RankThree.PartTwo.Sec19.Item19Res5ProofFaithTools
public import CFSG.LieType.SeitzGeneration.SubfieldPairSUOddProof
public import CFSG.RankThree.PartTwo.KFacts.AutPSUFaithful

public section

namespace CFSG.RankThree.PartTwo.Sec19.Item19Res6Proof

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.ClassicalGroups.UnitaryFlag
open CFSG.RankThree.PartTwo.KFacts
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher (glAut coe_glAut)

variable {p f e : ℕ} {K : Type} [Field K] {k : Subfield K}

section Fix

variable {h : UnitaryFieldData p f K}

theorem psuConj_fix_of_commute (W : unitaryIsom3 h) (t : unitarySU p f K 3)
    (hc : (W : GL (Fin 3) K) * t = t * W) :
    psuConj h W (unitaryProj h 3 t) = unitaryProj h 3 t := by
  change psuConj h W (t : unitaryPSU h 3) = (t : unitaryPSU h 3)
  rw [psuConj_mk]
  congr 1
  apply Subtype.ext
  rw [coe_suConj, hc]
  simp

theorem psuField_mul_psuConj_fix (σ : K ≃+* K) (W : unitaryIsom3 h) (t : unitarySU p f K 3)
    (hc : glAut σ ((W : GL (Fin 3) K) * (t : GL (Fin 3) K) * (W : GL (Fin 3) K)⁻¹) = t) :
    (psuField h σ * psuConj h W) (unitaryProj h 3 t) = unitaryProj h 3 t := by
  change psuField h σ (psuConj h W (t : unitaryPSU h 3)) = (t : unitaryPSU h 3)
  rw [psuConj_mk, psuField_mk]
  congr 1
  apply Subtype.ext
  rw [coe_suField, coe_suConj, Subgroup.coe_inv, hc]

end Fix

section Sub

variable (h : UnitaryFieldData p f K) (h₀ : UnitaryFieldData p e k)
  (hbar : ∀ x : k, h.bar (x : K) = ((h₀.bar x : k) : K))

theorem map_apply_mem (z : GL (Fin 3) k) (i j : Fin 3) :
    ((GeneralLinearGroup.map k.subtype z : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) i j ∈ k := by
  rw [GeneralLinearGroup.map_apply]
  exact ((z : Matrix (Fin 3) (Fin 3) k) i j).2

include hbar in
theorem map_mem_unitarySU {z : GL (Fin 3) k} (hz : z ∈ unitarySU p e k 3) :
    GeneralLinearGroup.map k.subtype z ∈ unitarySU p f K 3 := by
  obtain ⟨hdet, hu⟩ := (mem_unitarySU_iff h₀).mp hz
  refine (mem_unitarySU_iff h).mpr ⟨?_, (mem_unitaryIsom3_map_iff h h₀ hbar z).2 hu⟩
  have hcoe : ((GeneralLinearGroup.map k.subtype z : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
      (z : Matrix (Fin 3) (Fin 3) k).map k.subtype := by
    ext i j
    rw [GeneralLinearGroup.map_apply, Matrix.map_apply]
  rw [hcoe, ← RingHom.mapMatrix_apply, ← RingHom.map_det, hdet, map_one]

include hbar in
theorem exists_unitarySU_of_mem {g : GL (Fin 3) K} (hg : g ∈ unitarySU p f K 3)
    (hk : ∀ i j, (g : Matrix (Fin 3) (Fin 3) K) i j ∈ k) :
    ∃ z : GL (Fin 3) k, z ∈ unitarySU p e k 3 ∧ GeneralLinearGroup.map k.subtype z = g := by
  obtain ⟨z, hz⟩ := Item19Res5Proof.exists_map_eq_of_mem k hk
  refine ⟨z, ?_, hz⟩
  obtain ⟨hdet, hu⟩ := (mem_unitarySU_iff h).mp hg
  refine (mem_unitarySU_iff h₀).mpr ⟨?_, (mem_unitaryIsom3_map_iff h h₀ hbar z).1 (hz ▸ hu)⟩
  have hcoe : ((GeneralLinearGroup.map k.subtype z : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
      (z : Matrix (Fin 3) (Fin 3) k).map k.subtype := by
    ext i j
    rw [GeneralLinearGroup.map_apply, Matrix.map_apply]
  apply k.subtype_injective
  rw [RingHom.map_det, RingHom.mapMatrix_apply, ← hcoe, hz, hdet, map_one]

end Sub

section Pair

variable (h : UnitaryFieldData p f K) (h₀ : UnitaryFieldData p e k)
  (hbar : ∀ x : k, h.bar (x : K) = ((h₀.bar x : k) : K))

include hbar in
theorem eq_top_of_conj_not_mem (hfe : f = 3 * e) (hq : p ^ e ≠ 2)
    {Y : Subgroup (unitaryPSU h 3)}
    (hY : ∀ g : unitarySU p f K 3,
      (∀ i j, ((g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) i j ∈ k) → unitaryProj h 3 g ∈ Y)
    (t : unitarySU p f K 3) (ht : unitaryProj h 3 t ∈ Y)
    (hne : ∃ g : unitarySU p f K 3,
      (∀ i j, ((g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) i j ∈ k) ∧
        ∃ i j, (((t * g * t⁻¹ : unitarySU p f K 3) : GL (Fin 3) K) :
          Matrix (Fin 3) (Fin 3) K) i j ∉ k) :
    Y = ⊤ := by
  classical
  have hbar' : ∀ c : k, ((h₀.bar c : k) : K) = h.bar (c : K) := fun c => (hbar c).symm
  set S := gramSU h ((1 : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) with hS
  set ε : unitarySU p f K 3 ≃* S := suGramEquiv h with hε
  have hεv : ∀ x : unitarySU p f K 3, ((ε x : S) : GL (Fin 3) K) = x := fun x => rfl
  set A : CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.primeFormUnitary h
      ((1 : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) :=
    ⟨t, mem_primeFormUnitary_one (unitarySU_le_unitaryIsom3 t.2)⟩ with hA
  set R := CFSG.RankThree.PartOne.CTP.suSub h h₀ hbar' 3 with hR
  set c := (CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.primeFormConjSU h
    ((1 : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) A).toMonoidHom with hc
  have hcv : ∀ x : S, ((c x : S) : GL (Fin 3) K) = (t : GL (Fin 3) K) * x * (t : GL (Fin 3) K)⁻¹ :=
    fun x => rfl
  have hRk : ∀ x ∈ R, ∀ i j, ((x : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) i j ∈ k := by
    rintro _ ⟨z, rfl⟩ i j
    change ((CFSG.RankThree.Classical.subfieldGL k 3 (z : GL (Fin 3) k) : GL (Fin 3) K) :
      Matrix (Fin 3) (Fin 3) K) i j ∈ k
    rw [CFSG.RankThree.Classical.coe_subfieldGL, Matrix.map_apply]
    exact ((z : GL (Fin 3) k) i j).2
  have hkR : ∀ g : unitarySU p f K 3,
      (∀ i j, ((g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) i j ∈ k) → ε g ∈ R := by
    intro g hgk
    obtain ⟨z, hz, hzg⟩ := exists_unitarySU_of_mem h h₀ hbar g.2 hgk
    have hzS : z ∈ gramSU h₀ ((1 : GL (Fin 3) k) : Matrix (Fin 3) (Fin 3) k) := by
      rw [← unitarySU_three_eq_gramSU h₀]
      exact hz
    refine ⟨⟨z, hzS⟩, Subtype.ext ?_⟩
    change GeneralLinearGroup.map k.subtype z = (g : GL (Fin 3) K)
    exact hzg
  have hneR : R.map c ≠ R := by
    intro heq
    obtain ⟨g, hgk, i, j, hij⟩ := hne
    have hmem : c (ε g) ∈ R := by
      rw [← heq]
      exact Subgroup.mem_map_of_mem c (hkR g hgk)
    apply hij
    have := hRk _ hmem i j
    rw [hcv, hεv] at this
    exact this
  have hgen := CFSG.LieType.SeitzGeneration.subfieldPairSUOdd_of_ne_two p f e K h k h₀ hbar' 3
    Nat.prime_three (by norm_num) hfe hq 3 le_rfl A hneR
  set Y' : Subgroup S := (Y.comap (unitaryProj h 3)).comap ε.symm.toMonoidHom with hY'
  have hRY : R ≤ Y' := by
    intro x hx
    show unitaryProj h 3 (ε.symm x) ∈ Y
    refine hY _ fun i j => ?_
    exact hRk x hx i j
  have htY : ∀ x ∈ Y', c x ∈ Y' := by
    intro x hx
    show unitaryProj h 3 (ε.symm (c x)) ∈ Y
    have he : ε.symm (c x) = t * ε.symm x * t⁻¹ := by
      apply Subtype.ext
      rfl
    rw [he, map_mul, map_mul, map_inv]
    exact Y.mul_mem (Y.mul_mem ht hx) (Y.inv_mem ht)
  have hcRY : R.map c ≤ Y' := by
    rintro _ ⟨x, hx, rfl⟩
    exact htY x (hRY hx)
  have hYtop : Y' = ⊤ := by
    rw [eq_top_iff, ← hgen, Subgroup.closure_le]
    rintro x (hx | hx)
    · exact hRY hx
    · exact hcRY hx
  rw [eq_top_iff]
  intro y _
  obtain ⟨g, rfl⟩ := unitaryProj_surjective h 3 y
  have hg : ε g ∈ Y' := by rw [hYtop]; trivial
  have : ε.symm (ε g) = g := ε.symm_apply_apply g
  change unitaryProj h 3 (ε.symm (ε g)) ∈ Y at hg
  rwa [this] at hg

end Pair

section Witness

variable (h : UnitaryFieldData p f K) (h₀ : UnitaryFieldData p e k)
  (hbar : ∀ x : k, h.bar (x : K) = ((h₀.bar x : k) : K))

@[expose] def swapMat (F : Type) [Field F] : Matrix (Fin 3) (Fin 3) F :=
  !![0, 1, 0; 1, 0, 0; 0, 0, -1]

theorem swapMat_mul_self (F : Type) [Field F] : swapMat F * swapMat F = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [swapMat, Matrix.mul_apply, Fin.sum_univ_three]

@[expose] def swapGL (F : Type) [Field F] : GL (Fin 3) F :=
  ⟨swapMat F, swapMat F, swapMat_mul_self F, swapMat_mul_self F⟩

theorem swapGL_mem (h₀ : UnitaryFieldData p e k) : swapGL k ∈ unitarySU p e k 3 := by
  refine (mem_unitarySU_iff h₀).mpr ⟨?_, ?_⟩
  · change (swapMat k).det = 1
    simp [swapMat, Matrix.det_fin_three]
  · change ((swapMat k).map h₀.bar)ᵀ * swapMat k = 1
    have hmap : (swapMat k).map h₀.bar = swapMat k := by
      ext i j
      fin_cases i <;> fin_cases j <;> simp [swapMat]
    rw [hmap]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [swapMat, Matrix.mul_apply, Fin.sum_univ_three]

include hbar in
theorem exists_conj_not_mem (P : GL (Fin 3) k) (hP : P ∈ unitaryIsom3 h₀) (D : unitarySU p f K 3)
    {d : Fin 3 → K} (hD : ((D : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = diagonal d)
    (hd : d 0 * (d 1)⁻¹ ∉ k) :
    ∃ g : unitarySU p f K 3,
      (∀ i j, ((g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) i j ∈ k) ∧
        ∃ i j, ((((⟨GeneralLinearGroup.map k.subtype P * D *
          (GeneralLinearGroup.map k.subtype P)⁻¹, conj_mem_unitarySU
            ((mem_unitaryIsom3_map_iff h h₀ hbar P).2 hP) D.2⟩ : unitarySU p f K 3) * g *
          (⟨GeneralLinearGroup.map k.subtype P * D * (GeneralLinearGroup.map k.subtype P)⁻¹,
            conj_mem_unitarySU ((mem_unitaryIsom3_map_iff h h₀ hbar P).2 hP) D.2⟩ :
              unitarySU p f K 3)⁻¹ : unitarySU p f K 3) : GL (Fin 3) K) :
            Matrix (Fin 3) (Fin 3) K) i j ∉ k := by
  classical
  set z : GL (Fin 3) k := P * swapGL k * P⁻¹ with hz
  have hzSU : z ∈ unitarySU p e k 3 := conj_mem_unitarySU hP (swapGL_mem h₀)
  set g : unitarySU p f K 3 := ⟨GeneralLinearGroup.map k.subtype z,
    map_mem_unitarySU h h₀ hbar hzSU⟩ with hg
  refine ⟨g, fun i j => map_apply_mem z i j, ?_⟩
  by_contra hall
  push Not at hall
  set M : GL (Fin 3) K := GeneralLinearGroup.map k.subtype P * D *
    (GeneralLinearGroup.map k.subtype P)⁻¹ * (GeneralLinearGroup.map k.subtype z) *
    (GeneralLinearGroup.map k.subtype P * D * (GeneralLinearGroup.map k.subtype P)⁻¹)⁻¹ with hM
  have hMk : ∀ i j, (M : Matrix (Fin 3) (Fin 3) K) i j ∈ k := hall
  obtain ⟨M', hM'⟩ := Item19Res5Proof.exists_map_eq_of_mem k hMk
  have hDE : (D : GL (Fin 3) K) * GeneralLinearGroup.map k.subtype (swapGL k) *
      (D : GL (Fin 3) K)⁻¹ = GeneralLinearGroup.map k.subtype (P⁻¹ * M' * P) := by
    rw [map_mul, map_mul, hM', map_inv, hM, hz, map_mul, map_mul, map_inv]
    group
  have h01 := congrArg (fun x : GL (Fin 3) K => (x : Matrix (Fin 3) (Fin 3) K) 0 1) hDE
  have hmem : ((GeneralLinearGroup.map k.subtype (P⁻¹ * M' * P) : GL (Fin 3) K) :
      Matrix (Fin 3) (Fin 3) K) 0 1 ∈ k := map_apply_mem _ 0 1
  rw [← h01] at hmem
  apply hd
  have hDinv : (((D : GL (Fin 3) K)⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
      diagonal (fun i => (d i)⁻¹) := by
    have hd0 : ∀ i, d i ≠ 0 := by
      intro i h0
      have hdet := (D : GL (Fin 3) K).isUnit.map Matrix.detMonoidHom
      have : ((D : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).det = 0 := by
        rw [hD, det_diagonal]
        exact Finset.prod_eq_zero (Finset.mem_univ i) h0
      exact hdet.ne_zero this
    have h1 : diagonal d * diagonal (fun i => (d i)⁻¹) = 1 := by
      rw [diagonal_mul_diagonal, ← diagonal_one]
      congr 1
      funext i
      exact mul_inv_cancel₀ (hd0 i)
    rw [← hD] at h1
    exact (Units.inv_eq_of_mul_eq_one_right h1)
  have hsw : ((GeneralLinearGroup.map k.subtype (swapGL k) : GL (Fin 3) K) :
      Matrix (Fin 3) (Fin 3) K) = swapMat K := by
    ext i j
    rw [GeneralLinearGroup.map_apply]
    fin_cases i <;> fin_cases j <;> simp [swapGL, swapMat]
  have hentry : (((D : GL (Fin 3) K) * GeneralLinearGroup.map k.subtype (swapGL k) *
      (D : GL (Fin 3) K)⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) 0 1 = d 0 * (d 1)⁻¹ := by
    rw [Units.val_mul, Units.val_mul, hD, hsw, hDinv, Matrix.mul_diagonal, Matrix.diagonal_mul]
    simp [swapMat]
  rw [hentry] at hmem
  exact hmem

end Witness

section Diag

variable (h : UnitaryFieldData p f K)

theorem exists_diag_mem (d : Fin 3 → K) (hN : ∀ i, h.norm (d i) = 1)
    (hdet : d 0 * d 1 * d 2 = 1) :
    ∃ D : unitarySU p f K 3, ((D : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = diagonal d := by
  have hdet' : (diagonal d).det = 1 := by
    rw [det_diagonal, Fin.prod_univ_three, hdet]
  have hdet0 : (diagonal d).det ≠ 0 := by rw [hdet']; exact one_ne_zero
  refine ⟨⟨GeneralLinearGroup.mkOfDetNeZero _ hdet0, ?_⟩, rfl⟩
  refine (mem_unitarySU_iff h).mpr ⟨hdet', ?_⟩
  change ((diagonal d).map h.bar)ᵀ * diagonal d = 1
  rw [diagonal_map (map_zero h.bar), diagonal_transpose, diagonal_mul_diagonal, ← diagonal_one]
  congr 1
  funext i
  have := hN i
  rw [UnitaryFieldData.norm] at this
  rw [mul_comm]
  exact this

end Diag

end CFSG.RankThree.PartTwo.Sec19.Item19Res6Proof
