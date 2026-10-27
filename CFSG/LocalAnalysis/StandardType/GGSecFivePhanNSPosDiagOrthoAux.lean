module

public import CFSG.LocalAnalysis.StandardType.GGSecFivePhanNSPosDefs
public import CFSG.RankThree.PartOne.KF.UnitaryDiag

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Assembly.LowTwoRank CFSG.Blueprint CFSG.LieType.Universal CFSG.ClassicalInvolution.Phan
  CFSG.LieType.Universal.Unitary CFSG.LieType.BorelTits Matrix
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  CFSG.RankThree.PartOne.KCUnitaryModel

open scoped MatrixGroups

private noncomputable def ggNSPosPE3_ufd {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G}
    {K : Type} [Field K] [Finite K] [CharP K 2] {f n : ℕ} {ψ : Su K 2 f n →* G}
    (h : GGNSLocalHyp p B Bs K f n ψ) : UnitaryFieldData 2 f K where
  prime := Nat.prime_two
  one_le := by
    by_contra hf
    have hf0 : f = 0 := by omega
    subst hf0
    have hdiv : p ∣ 2 := by simpa using h.dvd
    have hle : p ≤ 2 := Nat.le_of_dvd (by norm_num) hdiv
    have hge : 2 ≤ p := h.prime.two_le
    exact h.odd (by omega)
  card := by
    rw [h.card, ← pow_mul]
    congr 1
    ring

private lemma ggNSPosPE3_bar_eq {K : Type} [Field K] [Finite K] [CharP K 2] {f : ℕ}
    (h : UnitaryFieldData 2 f K) :
    (⇑h.bar : K → K) = ⇑(unitaryInvolution K 2 f) := by
  funext c
  rw [UnitaryFieldData.bar_apply, unitaryInvolution_apply]

private lemma ggNSPosPE3_mem_primeFormUnitary {K : Type} [Field K] [Finite K] [CharP K 2] {f n : ℕ}
    (h : UnitaryFieldData 2 f K) {B : GL (Fin n) K}
    (hB : ggIsUnitaryMat (p := 2) (f := f) B) :
    B ∈ primeFormUnitary h (idGram K n) := by
  rw [mem_primeFormUnitary, idGram, Units.val_one, Matrix.mul_one]
  have hσ : (⇑(unitaryInvolution K 2 f) : K → K) = ⇑h.bar := (ggNSPosPE3_bar_eq h).symm
  have h1 := hB
  unfold ggIsUnitaryMat conjTr at h1
  rwa [hσ] at h1

private lemma ggNSPosPE3_closure_commute {H : Type} [Group H] {S : Set H}
    (hS : ∀ x ∈ S, ∀ y ∈ S, x * y = y * x) :
    ∀ x ∈ Subgroup.closure S, ∀ y ∈ Subgroup.closure S, x * y = y * x := by
  have h1 : Subgroup.closure S ≤ Subgroup.centralizer S :=
    (Subgroup.closure_le _).mpr (fun x hx =>
      (Subgroup.mem_centralizer_iff).mpr (fun y hy => (hS x hx y hy).symm))
  intro x hx y hy
  have hy' := (Subgroup.mem_centralizer_iff).mp (h1 hy)
  have h3 : Subgroup.closure S ≤ Subgroup.centralizer ({y} : Set H) :=
    (Subgroup.closure_le _).mpr (fun w hw =>
      (Subgroup.mem_centralizer_iff).mpr (fun v hv => by
        rw [Set.mem_singleton_iff] at hv
        subst hv
        exact (hy' w hw).symm))
  exact ((Subgroup.mem_centralizer_iff).mp (h3 hx) y (Set.mem_singleton y)).symm

private lemma ggNSPosPE3_closure_pow {H : Type} [Group H] {S : Set H} {m : ℕ}
    (hcomm : ∀ x ∈ Subgroup.closure S, ∀ y ∈ Subgroup.closure S, x * y = y * x)
    (hpowS : ∀ x ∈ S, x ^ m = 1) :
    ∀ x ∈ Subgroup.closure S, x ^ m = 1 := by
  apply Subgroup.closure_induction_left (s := S) (p := fun x _ => x ^ m = 1)
  · simp
  · intro x hx y hy hyP
    have hc : Commute x y := hcomm x (Subgroup.subset_closure hx) y hy
    rw [hc.mul_pow, hpowS x hx, hyP, one_mul]
  · intro x hx y hy hyP
    have hc : Commute x y := hcomm x (Subgroup.subset_closure hx) y hy
    have hci : Commute x⁻¹ y := hc.inv_left
    rw [hci.mul_pow, hyP, mul_one, inv_pow, hpowS x hx, inv_one]

private lemma ggNSPosPE3_diag_conj_diag {K : Type} [Field K] {n : ℕ}
    {A : Matrix (Fin n) (Fin n) K} (hA : A.IsDiag) {d : Fin n → K} (hd : ∀ i, d i ≠ 0) :
    Matrix.diagonal (fun i => (d i)⁻¹) * A * Matrix.diagonal d = A := by
  have hA' : A = Matrix.diagonal (fun i => A i i) := by
    ext i j
    rw [Matrix.diagonal_apply]
    by_cases h : i = j
    · subst h; simp
    · rw [if_neg h]; exact hA h
  rw [hA']
  ext i j
  rw [Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.diagonal_apply]
  by_cases hij : i = j
  · subst hij
    rw [if_pos rfl, mul_assoc, mul_comm (A i i) (d i), ← mul_assoc, inv_mul_cancel₀ (hd i), one_mul]
  · simp [hij]

private lemma ggNSPosPE3_diagonal_mul_diagonal {K : Type} [Field K] {n : ℕ} (a b : Fin n → K) :
    Matrix.diagonal a * Matrix.diagonal b = Matrix.diagonal (fun i => a i * b i) := by
  ext i j
  rw [Matrix.mul_diagonal, Matrix.diagonal_apply, Matrix.diagonal_apply]
  by_cases h : i = j <;> simp [h]

theorem ggNSPosPE3_orthonormal_diag {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G}
    {K : Type} [Field K] [Finite K] [CharP K 2] {f n : ℕ} {ψ : Su K 2 f n →* G}
    (h : GGNSLocalHyp p B Bs K f n ψ) (g : Bs → GL (Fin n) K)
    (hu : ∀ b : Bs, ggIsUnitaryMat (p := 2) (f := f) (g b)) (hpow : ∀ b : Bs, g b ^ p = 1)
    (hcomm : ∀ b₁ b₂ : Bs, g b₁ * g b₂ = g b₂ * g b₁) :
    ∃ c : Su K 2 f n, ∀ b : Bs,
      ggIsDiagMat ((c : GL (Fin n) K)⁻¹ * g b * (c : GL (Fin n) K)) := by
  classical
  have h' : UnitaryFieldData 2 f K := ggNSPosPE3_ufd h
  let Q := primeFormUnitary h' (idGram K n)
  let gen : Bs → Q := fun b => ⟨g b, ggNSPosPE3_mem_primeFormUnitary h' (hu b)⟩
  let S : Set Q := Set.range gen
  have hcommS : ∀ x ∈ S, ∀ y ∈ S, x * y = y * x := by
    rintro x ⟨b, rfl⟩ y ⟨b', rfl⟩
    refine Subtype.ext ?_
    simpa using hcomm b b'
  have hpowS : ∀ x ∈ S, x ^ p = 1 := by
    rintro x ⟨b, rfl⟩
    refine Subtype.ext ?_
    simpa using hpow b
  let Gsub : Subgroup Q := Subgroup.closure S
  have hcommG : ∀ x ∈ Gsub, ∀ y ∈ Gsub, x * y = y * x :=
    ggNSPosPE3_closure_commute hcommS
  have hpowG : ∀ x ∈ Gsub, x ^ p = 1 :=
    ggNSPosPE3_closure_pow hcommG hpowS
  obtain ⟨P, hPdiag⟩ :=
    CFSG.RankThree.PartOne.KFU.exists_unitary_conj_diag h' h.prime h.dvd Gsub hcommG hpowG
  let Pgl : GL (Fin n) K := (P : Q)
  let Pinv : GL (Fin n) K := Pgl⁻¹
  let δ : K := (Pgl : Matrix (Fin n) (Fin n) K).det
  have hPu : ((Pgl : Matrix (Fin n) (Fin n) K).map h'.bar)ᵀ *
      (Pgl : Matrix (Fin n) (Fin n) K) = 1 := by
    have h1 := (mem_primeFormUnitary (C := idGram K n)).mp P.2
    simpa [idGram] using h1
  have hPuσ : conjTr (unitaryInvolution K 2 f) (Pgl : Matrix (Fin n) (Fin n) K) *
      (Pgl : Matrix (Fin n) (Fin n) K) = 1 := by
    have hmap : (Pgl : Matrix (Fin n) (Fin n) K).map (⇑h'.bar) =
        (Pgl : Matrix (Fin n) (Fin n) K).map (⇑(unitaryInvolution K 2 f)) := by
      ext i j
      exact congrFun (ggNSPosPE3_bar_eq h') _
    unfold conjTr
    rw [← hmap]
    exact hPu
  have hδ : h'.bar δ * δ = 1 := by
    have h1 := congrArg Matrix.det hPu
    rw [Matrix.det_mul, Matrix.det_transpose, Matrix.det_one] at h1
    rw [show ((Pgl : Matrix (Fin n) (Fin n) K).map h'.bar).det = h'.bar δ from
      (RingHom.map_det h'.bar (Pgl : Matrix (Fin n) (Fin n) K)).symm] at h1
    exact h1
  have hδσ : unitaryInvolution K 2 f δ * δ = 1 := by
    rw [← congrFun (ggNSPosPE3_bar_eq h') δ]
    exact hδ
  have hδσinv : unitaryInvolution K 2 f δ⁻¹ * δ⁻¹ = 1 := by
    rw [map_inv₀, ← _root_.mul_inv_rev, mul_comm δ (unitaryInvolution K 2 f δ), hδσ, inv_one]
  have hδne : δ ≠ 0 := by
    have hmul : ((Pinv : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
        (Pgl : Matrix (Fin n) (Fin n) K) = 1 := by
      show (((Pgl⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
        (Pgl : Matrix (Fin n) (Fin n) K)) = 1
      rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
    exact Matrix.det_ne_zero_of_left_inverse hmul
  have hn4 : 4 ≤ n := h.four_le
  let i0 : Fin n := ⟨0, by omega⟩
  let d0 : Fin n → K := fun i => if i = i0 then δ⁻¹ else 1
  have hd0 : ∀ i, d0 i ≠ 0 := by
    intro i
    by_cases hi : i = i0
    · simp [d0, hi, inv_ne_zero hδne]
    · simp [d0, hi]
  let Dmat : Matrix (Fin n) (Fin n) K := Matrix.diagonal d0
  let Dinvmat : Matrix (Fin n) (Fin n) K := Matrix.diagonal (fun i => (d0 i)⁻¹)
  have hmul1 : Dmat * Dinvmat = 1 := by
    simp only [Dmat, Dinvmat]
    rw [ggNSPosPE3_diagonal_mul_diagonal,
      show (fun i => d0 i * (d0 i)⁻¹) = (fun _ => 1) from funext (fun i => mul_inv_cancel₀ (hd0 i))]
    exact Matrix.diagonal_one
  have hmul2 : Dinvmat * Dmat = 1 := by
    simp only [Dmat, Dinvmat]
    rw [ggNSPosPE3_diagonal_mul_diagonal,
      show (fun i => (d0 i)⁻¹ * d0 i) = (fun _ => 1) from funext (fun i => inv_mul_cancel₀ (hd0 i))]
    exact Matrix.diagonal_one
  let D : GL (Fin n) K := ⟨Dmat, Dinvmat, hmul1, hmul2⟩
  have hDdet : (Dmat : Matrix (Fin n) (Fin n) K).det = δ⁻¹ := by
    simp only [Dmat, Matrix.det_diagonal]
    simp only [d0]
    rw [Finset.prod_ite_eq' Finset.univ i0 (fun _ => δ⁻¹)]
    simp
  have hd0u : ∀ i, unitaryInvolution K 2 f (d0 i) * d0 i = 1 := by
    intro i
    by_cases hi : i = i0
    · subst hi
      simp only [d0, if_pos rfl]
      exact hδσinv
    · simp only [d0, if_neg hi, map_one, one_mul]
  have hDunitary : conjTr (unitaryInvolution K 2 f) Dmat * Dmat = 1 := by
    have h1 : conjTr (unitaryInvolution K 2 f) Dmat =
        Matrix.diagonal (fun i => unitaryInvolution K 2 f (d0 i)) := by
      simp only [conjTr, Dmat]
      rw [Matrix.diagonal_map (map_zero (unitaryInvolution K 2 f)), Matrix.diagonal_transpose]
    rw [h1]
    simp only [Dmat]
    rw [ggNSPosPE3_diagonal_mul_diagonal,
      show (fun i => unitaryInvolution K 2 f (d0 i) * d0 i) = (fun _ => 1) from funext hd0u]
    exact Matrix.diagonal_one
  let c : Su K 2 f n :=
    ⟨Pgl * D, by
      rw [mem_SUid]
      refine ⟨?_, ?_⟩
      · rw [Units.val_mul, Matrix.det_mul]
        change δ * (Dmat : Matrix (Fin n) (Fin n) K).det = 1
        rw [hDdet, mul_inv_cancel₀ hδne]
      · rw [Units.val_mul, conjTr_mul]
        rw [Matrix.mul_assoc (conjTr (unitaryInvolution K 2 f) (D : Matrix (Fin n) (Fin n) K))
            (conjTr (unitaryInvolution K 2 f) (Pgl : Matrix (Fin n) (Fin n) K))
            ((Pgl : Matrix (Fin n) (Fin n) K) * (D : Matrix (Fin n) (Fin n) K)),
          ← Matrix.mul_assoc (conjTr (unitaryInvolution K 2 f) (Pgl : Matrix (Fin n) (Fin n) K))
            (Pgl : Matrix (Fin n) (Fin n) K) (D : Matrix (Fin n) (Fin n) K),
          hPuσ, Matrix.one_mul, hDunitary]⟩
  refine ⟨c, fun b => ?_⟩
  have hbdiag := hPdiag (gen b) (Subgroup.subset_closure ⟨b, rfl⟩)
  let A : Matrix (Fin n) (Fin n) K :=
    (Pinv : Matrix (Fin n) (Fin n) K) * (g b : Matrix (Fin n) (Fin n) K) *
      (Pgl : Matrix (Fin n) (Fin n) K)
  have hA : A.IsDiag := by
    have h1 : (((↑(P⁻¹ * gen b * P) : Q) : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = A := by
      simp only [A, Pinv, Pgl, gen, Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv,
        Units.val_mul]
    rwa [h1] at hbdiag
  refine ⟨fun i => A i i, ?_⟩
  have hconjE : ((((c : GL (Fin n) K))⁻¹ * (g b) * (c : GL (Fin n) K) : GL (Fin n) K) :
      Matrix (Fin n) (Fin n) K) = Dinvmat * A * Dmat := by
    have hc : (c : GL (Fin n) K) = Pgl * D := rfl
    rw [hc, _root_.mul_inv_rev]
    simp only [Dinvmat, Dmat, A, Pinv, Units.val_mul, mul_assoc]
    rfl
  rw [hconjE]
  rw [show Dinvmat = Matrix.diagonal (fun i => (d0 i)⁻¹) from rfl,
    show Dmat = Matrix.diagonal d0 from rfl,
    ggNSPosPE3_diag_conj_diag hA hd0]
  exact (show A = Matrix.diagonal (fun i => A i i) from by
    ext i j
    rw [Matrix.diagonal_apply]
    by_cases hij : i = j
    · subst hij; simp
    · rw [if_neg hij]; exact hA hij)

end CFSG.StandardType

end
