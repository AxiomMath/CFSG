module

public import CFSG.RankThree.PartOne.KSP6.UV
public import CFSG.RankThree.PartOne.AUTSL.PushShared

public section

namespace CFSG.RankThree.PartOne.KSP6

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag
  CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher CFSG.RankThree.Classical
  CFSG.Assembly.LowTwoRank

section Matrices

variable {K : Type} [Field K]

@[expose] def gm (A : gsp 3 K) : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) K :=
  ((A : GL (Fin 3 ⊕ Fin 3) K) : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) K)

@[expose] def gmi (A : gsp 3 K) : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) K :=
  (((A : GL (Fin 3 ⊕ Fin 3) K)⁻¹ : GL (Fin 3 ⊕ Fin 3) K) :
    Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) K)

theorem gm_mul_gmi (A : gsp 3 K) : gm A * gmi A = 1 := by
  rw [gm, gmi, ← Units.val_mul, mul_inv_cancel, Units.val_one]

theorem mat_conjSp_fieldSp (A : gsp 3 K) (σ : K ≃+* K) (g : StatedSp 3 K) :
    mat (conjSp 3 K A (fieldSp 3 K σ g)) = gm A * (mat g).map σ * gmi A := by
  rw [mat, coe_conjSp, Units.val_mul, Units.val_mul, coe_fieldSp]
  rfl

end Matrices

section Aut

variable {K : Type} [Field K] [Finite K] [CharP K 2]

theorem exists_conjSp_fieldSp (β : MulAut (StatedSp 3 K)) :
    ∃ (A : gsp 3 K) (σ : K ≃+* K), ∀ g : StatedSp 3 K, β g = conjSp 3 K A (fieldSp 3 K σ g) := by
  have hbij : Function.Bijective (proj 3 K) :=
    UnitaryHigher.proj_bijective_of_charTwo
  let ψ : StatedSp 3 K ≃* StatedProj (StatedSp 3 K) := MulEquiv.ofBijective (proj 3 K) hbij
  obtain ⟨A, σ, hα⟩ := (automorphism_generation (r := 3) (K := K) (by norm_num)).2
    (MulAut.congr ψ β)
  refine ⟨A, σ, fun g => ?_⟩
  have h1 : proj 3 K (β g) = proj 3 K (conjSp 3 K A (fieldSp 3 K σ g)) := by
    have h2 := congrArg (fun φ : MulAut (StatedProj (StatedSp 3 K)) => φ (proj 3 K g)) hα
    simp only [MulAut.mul_apply, conjAut_proj, fieldAut_proj] at h2
    rw [← h2]
    have hs : ψ.symm (proj 3 K g) = g := ψ.symm_apply_apply g
    simp only [MulAut.congr_apply, MulEquiv.trans_apply]
    rw [hs]
    rfl
  exact hbij.1 h1

theorem exists_conj_of_conjSp (A : gsp 3 K) :
    ∃ s : StatedSp 3 K, ∀ g, conjSp 3 K A g = MulAut.conj s g := by
  have hbij : Function.Bijective (proj 3 K) :=
    UnitaryHigher.proj_bijective_of_charTwo
  obtain ⟨s, hs⟩ := UnitaryHigher.exists_conjAut_eq_statedSp A
  refine ⟨s, fun g => ?_⟩
  apply hbij.1
  have h := congrArg (fun φ : MulAut (StatedProj (StatedSp 3 K)) => φ (proj 3 K g)) hs
  simp only [conjAut_proj] at h
  rw [h]
  apply congrArg (proj 3 K)
  apply Subtype.ext
  rw [coe_conjSp]
  rfl

end Aut

section Semilinear

variable {K : Type} [Field K]

@[expose] def symSub (K : Type) [Field K] : Submodule K (Matrix (Fin 3) (Fin 3) K) where
  carrier := {C | Cᵀ = C}
  add_mem' := fun {a b} ha hb => by
    have ha' : aᵀ = a := ha
    have hb' : bᵀ = b := hb
    show (a + b)ᵀ = a + b
    rw [transpose_add, ha', hb']
  zero_mem' := by
    show (0 : Matrix (Fin 3) (Fin 3) K)ᵀ = 0
    simp
  smul_mem' := fun c a ha => by
    have ha' : aᵀ = a := ha
    show (c • a)ᵀ = c • a
    rw [transpose_smul, ha']

theorem mem_symSub {C : Matrix (Fin 3) (Fin 3) K} : C ∈ symSub K ↔ Cᵀ = C := Iff.rfl

@[expose] def nmat (C : Matrix (Fin 3) (Fin 3) K) : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) K :=
  fromBlocks 0 C 0 0

theorem fromBlocks_one_eq_one_add (C : Matrix (Fin 3) (Fin 3) K) :
    (fromBlocks 1 C 0 1 : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) K) = 1 + nmat C := by
  rw [nmat, ← fromBlocks_one, fromBlocks_add]
  simp

theorem nmat_add (C D : Matrix (Fin 3) (Fin 3) K) : nmat (C + D) = nmat C + nmat D := by
  simp [nmat, fromBlocks_add]

theorem nmat_smul (c : K) (C : Matrix (Fin 3) (Fin 3) K) : nmat (c • C) = c • nmat C := by
  simp [nmat, fromBlocks_smul]

theorem map_one_add_nmat (σ : K ≃+* K) (C : Matrix (Fin 3) (Fin 3) K) :
    ((1 : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) K) + nmat C).map σ = 1 + nmat (C.map σ) := by
  ext i j
  rcases i with i | i <;> rcases j with j | j <;>
    simp [nmat, Matrix.one_apply]

@[expose] def psiMap (A Ai : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) K) (σ : K ≃+* K)
    (C : Matrix (Fin 3) (Fin 3) K) : Matrix (Fin 3) (Fin 3) K :=
  (A * nmat (C.map σ) * Ai).toBlocks₁₂

theorem psiMap_add (A Ai : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) K) (σ : K ≃+* K)
    (C D : Matrix (Fin 3) (Fin 3) K) :
    psiMap A Ai σ (C + D) = psiMap A Ai σ C + psiMap A Ai σ D := by
  have h : (C + D).map σ = C.map σ + D.map σ := by
    ext i j
    simp
  rw [psiMap, psiMap, psiMap, h, nmat_add, Matrix.mul_add, Matrix.add_mul]
  ext i j
  simp [Matrix.toBlocks₁₂]

theorem psiMap_smul (A Ai : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) K) (σ : K ≃+* K) (c : K)
    (C : Matrix (Fin 3) (Fin 3) K) :
    psiMap A Ai σ (c • C) = σ c • psiMap A Ai σ C := by
  have : (c • C).map σ = σ c • C.map σ := by
    ext i j
    simp
  rw [psiMap, this, nmat_smul, Matrix.mul_smul, Matrix.smul_mul]
  ext i j
  simp [psiMap, Matrix.toBlocks₁₂]

theorem conj_one_add {A Ai N : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) K} (h : A * Ai = 1) :
    A * (1 + N) * Ai = 1 + A * N * Ai := by
  rw [Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, h]

end Semilinear

section Fixed

variable {K : Type} [Field K] [Finite K] [CharP K 2]

omit [CharP K 2] in
theorem card_symSub : Nat.card (symSub K) = Nat.card K ^ 6 := by
  have h : Nat.card (symSub K) = Nat.card (symMatrices 3 K) :=
    Nat.card_congr (Equiv.subtypeEquivRight fun C => by rw [mem_symSub, mem_symMatrices])
  rw [h, card_symMatrices]

omit [CharP K 2] in
theorem finrank_symSub : Module.finrank K (symSub K) = 6 := by
  have h1 := Module.natCard_eq_pow_finrank (K := K) (V := symSub K)
  rw [card_symSub] at h1
  exact (Nat.pow_right_injective (Finite.one_lt_card (α := K))).eq_iff.1 h1.symm

omit [Finite K] [CharP K 2] in
theorem psi_spec {β : MulAut (StatedSp 3 K)} {A : gsp 3 K} {σ : K ≃+* K}
    (hβ : ∀ g, β g = conjSp 3 K A (fieldSp 3 K σ g))
    (hV : ∀ v ∈ siegelRadicalSp 3 K, β v ∈ siegelRadicalSp 3 K)
    {C : Matrix (Fin 3) (Fin 3) K} (hC : Cᵀ = C) {v : StatedSp 3 K}
    (hv : mat v = fromBlocks 1 C 0 1) :
    (psiMap (gm A) (gmi A) σ C)ᵀ = psiMap (gm A) (gmi A) σ C ∧
      mat (β v) = fromBlocks 1 (psiMap (gm A) (gmi A) σ C) 0 1 := by
  have hvV : v ∈ siegelRadicalSp 3 K := mem_siegelRadicalSp.2 ⟨C, hC, hv⟩
  obtain ⟨C', hC', hvC'⟩ := mem_siegelRadicalSp.1 (hV v hvV)
  have hvC'' : mat (β v) = fromBlocks 1 C' 0 1 := hvC'
  have h1 : mat (β v) = gm A * (mat v).map σ * gmi A := by
    rw [hβ v]
    exact mat_conjSp_fieldSp A σ v
  have h2 : fromBlocks 1 C' 0 1 = 1 + gm A * nmat (C.map σ) * gmi A := by
    rw [← hvC'', h1, hv, fromBlocks_one_eq_one_add, map_one_add_nmat, conj_one_add (gm_mul_gmi A)]
  rw [fromBlocks_one_eq_one_add] at h2
  have h3 : nmat C' = gm A * nmat (C.map σ) * gmi A := add_left_cancel h2
  have h4 : C' = psiMap (gm A) (gmi A) σ C := by
    rw [psiMap, ← h3]
    simp [nmat]
  rw [← h4]
  exact ⟨hC', hvC''⟩

theorem fixed_card_le {β : MulAut (StatedSp 3 K)}
    (hV : ∀ v ∈ siegelRadicalSp 3 K, β v ∈ siegelRadicalSp 3 K)
    (hβ : β ∉ (MulAut.conj : StatedSp 3 K →* MulAut (StatedSp 3 K)).range) :
    Nat.card {v : ↥(siegelRadicalSp 3 K) // β (v : StatedSp 3 K) = v} * Nat.card K ≤
      Nat.card K ^ 6 := by
  classical
  obtain ⟨A, σ, hAσ⟩ := exists_conjSp_fieldSp β
  have hσ : σ ≠ 1 := by
    rintro rfl
    obtain ⟨s, hs⟩ := exists_conj_of_conjSp A
    refine hβ ⟨s, ?_⟩
    ext g
    rw [hAσ g, ← hs g]
    simp
  have hsymm : ∀ C : Matrix (Fin 3) (Fin 3) K, Cᵀ = C →
      (psiMap (gm A) (gmi A) σ C)ᵀ = psiMap (gm A) (gmi A) σ C := fun C hC => by
    obtain ⟨v, -, hv⟩ := exists_siegel_elt hC
    exact (psi_spec hAσ hV hC hv).1
  let ψ : symSub K →+ symSub K :=
    AddMonoidHom.mk' (fun C => ⟨psiMap (gm A) (gmi A) σ C.1, hsymm C.1 C.2⟩) (fun C D => by
      apply Subtype.ext
      exact psiMap_add _ _ _ _ _)
  have hψ : ∀ (c : K) (C : symSub K), ψ (c • C) = σ c • ψ C := fun c C => by
    apply Subtype.ext
    exact psiMap_smul _ _ _ _ _
  let C₀ : symSub K := ⟨Matrix.single 0 0 1, by simp [mem_symSub]⟩
  have hne : ∃ C, ψ C ≠ C := by
    by_contra h
    push Not at h
    apply hσ
    ext c
    have e1 : σ c • C₀ = c • C₀ :=
      calc σ c • C₀ = σ c • ψ C₀ := by rw [h C₀]
        _ = ψ (c • C₀) := (hψ c C₀).symm
        _ = c • C₀ := h _
    have e2 := congrArg (fun C : symSub K => C.1 0 0) e1
    simpa [C₀] using e2
  have hfix : ∀ v : ↥(siegelRadicalSp 3 K), ∃ C : symSub K, mat v.1 = fromBlocks 1 C.1 0 1 ∧
      mat (β v.1) = fromBlocks 1 (ψ C).1 0 1 := fun v => by
    obtain ⟨C, hC, hvC⟩ := mem_siegelRadicalSp.1 v.2
    exact ⟨⟨C, hC⟩, hvC, (psi_spec hAσ hV hC hvC).2⟩
  choose Cof hCof1 hCof2 using hfix
  have hfixC : ∀ v : {v : ↥(siegelRadicalSp 3 K) // β (v : StatedSp 3 K) = v},
      ψ (Cof v.1) = Cof v.1 := fun v => by
    have h := hCof2 v.1
    rw [v.2, hCof1 v.1] at h
    exact Subtype.ext (fromBlocks_inj.1 h).2.1.symm
  have hle : Nat.card {v : ↥(siegelRadicalSp 3 K) // β (v : StatedSp 3 K) = v} ≤
      Nat.card {C : symSub K // ψ C = C} := by
    refine Nat.card_le_card_of_injective (fun v => ⟨Cof v.1, hfixC v⟩) ?_
    intro v w h
    have h' : Cof v.1 = Cof w.1 := congrArg Subtype.val h
    apply Subtype.ext
    apply Subtype.ext
    apply mat_inj
    rw [hCof1 v.1, hCof1 w.1, h']
  have hmain := AUTSL.card_fix_mul_le (V := symSub K) (n := 6) (by norm_num) finrank_symSub σ ψ
    hψ hne
  rw [card_symSub] at hmain
  exact (Nat.mul_le_mul_right _ hle).trans hmain

end Fixed

end CFSG.RankThree.PartOne.KSP6
