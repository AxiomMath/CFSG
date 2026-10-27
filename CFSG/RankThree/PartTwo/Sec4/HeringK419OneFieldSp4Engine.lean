module

public import CFSG.RankThree.PartTwo.Sec4.HeringK419OneFieldSL2
public import CFSG.RankThree.PartTwo.Sec4.HeringK419OneFieldBlock
public import CFSG.RankThree.PartTwo.Sec4.HeringK419OneFieldDiag

public section

namespace CFSG.RankThree.PartTwo.Sec4.HeringOF

open Matrix CFSG.Open CFSG.Assembly.LowTwoRank
open scoped _root_.Classical

section Symplectic

variable {n : ℕ} {F : Type} [Field F] [CharP F 2]

theorem jMat_mul_self : (fromBlocks 0 1 (-1) 0 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) *
    fromBlocks 0 1 (-1) 0 = 1 := by
  have hneg : (-1 : Matrix (Fin n) (Fin n) F) = 1 := by
    ext i j
    simp [Matrix.neg_apply, Matrix.one_apply, apply_ite Neg.neg, CharTwo.neg_eq]
  rw [hneg, fromBlocks_multiply]
  simp [fromBlocks_one]

theorem statedSp_det_eq_one {g : GL (Fin n ⊕ Fin n) F} (hg : g ∈ StatedSp n F) :
    (g : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F).det = 1 := by
  have h := StatedAPI.mem_statedSp_iff.mp hg
  have hJ : (fromBlocks 0 1 (-1) 0 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F).det *
      (fromBlocks 0 1 (-1) 0 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F).det = 1 := by
    rw [← det_mul, jMat_mul_self, det_one]
  have h1 := congrArg Matrix.det h
  rw [det_mul, det_mul, det_transpose] at h1
  set d := (g : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F).det with hd
  set j := (fromBlocks 0 1 (-1) 0 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F).det with hj
  have hj0 : j ≠ 0 := by
    intro h0
    rw [h0, zero_mul] at hJ
    exact zero_ne_one hJ
  have h2 : (d * d) = 1 := by
    have : j * (d * d) = j * 1 := by linear_combination h1
    exact mul_left_cancel₀ hj0 this
  have h3 : (d + 1) ^ 2 = 0 := by
    have h2' : (2 : F) = 0 := CharP.cast_eq_zero F 2
    linear_combination h2 + d * h2' + CharTwo.add_self_eq_zero (1 : F)
  have h4 := pow_eq_zero_iff (n := 2) (by norm_num) |>.mp h3
  linear_combination h4 - CharTwo.add_self_eq_zero (1 : F)

theorem statedSp_trace_inv {g : GL (Fin n ⊕ Fin n) F} (hg : g ∈ StatedSp n F) :
    ((g⁻¹ : GL (Fin n ⊕ Fin n) F) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F).trace =
      (g : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F).trace := by
  have h := StatedAPI.mem_statedSp_iff.mp hg
  set J : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F := fromBlocks 0 1 (-1) 0 with hJdef
  set G : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F :=
    (g : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) with hG
  set Gi : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F :=
    ((g⁻¹ : GL (Fin n ⊕ Fin n) F) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) with hGi
  have hGGi : G * Gi = 1 := by rw [hG, hGi, ← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hJJ : J * J = 1 := jMat_mul_self
  have hGi' : Gi = J * Gᵀ * J := by
    have h1 : Gi = (J * J) * Gi := by rw [hJJ, Matrix.one_mul]
    have h2 : Gᵀ * J * G = J := h
    calc Gi = (J * J) * Gi := h1
      _ = J * (J * Gi) := by rw [Matrix.mul_assoc]
      _ = J * (Gᵀ * J * G * Gi) := by rw [h2]
      _ = J * (Gᵀ * J * (G * Gi)) := by simp only [Matrix.mul_assoc]
      _ = J * Gᵀ * J := by rw [hGGi, Matrix.mul_one, Matrix.mul_assoc]
  have hJu : IsUnit J := ⟨⟨J, J, hJJ, hJJ⟩, rfl⟩
  rw [hGi', show J * Gᵀ * J = J * (Gᵀ * J) by simp only [Matrix.mul_assoc], trace_mul_comm,
    show Gᵀ * J * J = Gᵀ * (J * J) by simp only [Matrix.mul_assoc], hJJ, Matrix.mul_one,
    trace_transpose]

end Symplectic

theorem core_eigenvalues {E' : Type} [Field E'] [CharP E' 2] {l ν : E'} (hl : l ^ 3 = 1)
    (hprod : l ^ 3 * ν = 1) (hsum : l + l + l + ν = l⁻¹ + l⁻¹ + l⁻¹ + ν⁻¹) (hne : l ≠ ν) :
    False := by
  have hν : ν = 1 := by rw [hl, one_mul] at hprod; exact hprod
  subst hν
  have hl0 : l ≠ 0 := by
    intro h0
    rw [h0] at hl
    norm_num at hl
  have h2 : (2 : E') = 0 := CharP.cast_eq_zero E' 2
  have h3 : l = l⁻¹ := by
    have : l + l + l + 1 = l + 1 := by linear_combination l * h2
    have h4 : l⁻¹ + l⁻¹ + l⁻¹ + 1⁻¹ = l⁻¹ + 1 := by
      rw [inv_one]; linear_combination l⁻¹ * h2
    rw [this, h4] at hsum
    linear_combination hsum
  have h5 : l * l = 1 := by
    have := congrArg (· * l) h3
    simpa [hl0] using this
  have h6 : (l + 1) ^ 2 = 0 := by
    linear_combination h5 + l * h2 + CharTwo.add_self_eq_zero (1 : E')
  have h7 := pow_eq_zero_iff (n := 2) (by norm_num) |>.mp h6
  exact hne (by linear_combination h7 - CharTwo.add_self_eq_zero (1 : E'))

theorem class_card_le_two {ι : Type} [Fintype ι] [DecidableEq ι] (hι : Fintype.card ι = 4)
    {E' : Type} [Field E'] [CharP E' 2] (μ : ι → E') (h3 : ∀ i, μ i ^ 3 = 1)
    (hprod : ∏ i, μ i = 1) (hsum : ∑ i, μ i = ∑ i, (μ i)⁻¹)
    (hnc : ¬ ∀ i j, μ i = μ j) (i : ι) : Fintype.card {j // μ j = μ i} ≤ 2 := by
  by_contra hcon
  push Not at hcon
  have hcard : Fintype.card {j // μ j = μ i} + Fintype.card {j // ¬ μ j = μ i} = 4 := by
    rw [Fintype.card_subtype_compl, ← hι]
    have := Fintype.card_subtype_le (fun j => μ j = μ i)
    omega
  have hT : Fintype.card {j // ¬ μ j = μ i} ≤ 1 := by omega
  rcases (show Fintype.card {j // ¬ μ j = μ i} = 0 ∨ Fintype.card {j // ¬ μ j = μ i} = 1 by
    omega) with h0 | h1
  · apply hnc
    intro a b
    have hall : ∀ j, μ j = μ i := by
      intro j
      by_contra hj
      have : Nonempty {j // ¬ μ j = μ i} := ⟨⟨j, hj⟩⟩
      have := Fintype.card_pos (α := {j // ¬ μ j = μ i})
      omega
    rw [hall a, hall b]
  · obtain ⟨k, hk⟩ := Fintype.card_eq_one_iff.mp h1
    have hS : Fintype.card {j // μ j = μ i} = 3 := by omega
    have hS3 : ∀ f : ι → E', (∀ j, μ j = μ i → f j = f i) →
        (∑ j : {j // μ j = μ i}, f j) = 3 • f i := by
      intro f hf
      rw [show (∑ j : {j // μ j = μ i}, f j) = ∑ _j : {j // μ j = μ i}, f i from
        Finset.sum_congr rfl fun j _ => hf j j.2, Finset.sum_const, Finset.card_univ, hS]
    have hP3 : ∀ f : ι → E', (∀ j, μ j = μ i → f j = f i) →
        (∏ j : {j // μ j = μ i}, f j) = f i ^ 3 := by
      intro f hf
      rw [show (∏ j : {j // μ j = μ i}, f j) = ∏ _j : {j // μ j = μ i}, f i from
        Finset.prod_congr rfl fun j _ => hf j j.2, Finset.prod_const, Finset.card_univ, hS]
    have hT1 : ∀ f : ι → E', (∑ j : {j // ¬ μ j = μ i}, f j) = f k := by
      intro f
      exact Finset.sum_eq_single k (fun b _ hb => absurd (hk b) hb)
        (fun h => absurd (Finset.mem_univ k) h)
    have hP1 : ∀ f : ι → E', (∏ j : {j // ¬ μ j = μ i}, f j) = f k := by
      intro f
      exact Finset.prod_eq_single k (fun b _ hb => absurd (hk b) hb)
        (fun h => absurd (Finset.mem_univ k) h)
    have hprod' : (μ i) ^ 3 * μ k = 1 := by
      rw [← hP3 μ (fun j hj => hj), ← hP1 μ, Fintype.prod_subtype_mul_prod_subtype]
      exact hprod
    have hsum1 : 3 • μ i + μ k = ∑ j, μ j := by
      rw [← Fintype.sum_subtype_add_sum_subtype (fun j => μ j = μ i) μ,
        hS3 μ (fun j hj => hj), hT1 μ]
    have hsum2 : 3 • (μ i)⁻¹ + (μ k)⁻¹ = ∑ j, (μ j)⁻¹ := by
      rw [← Fintype.sum_subtype_add_sum_subtype (fun j => μ j = μ i) (fun j => (μ j)⁻¹),
        hS3 (fun j => (μ j)⁻¹) (fun j hj => by rw [hj]), hT1 (fun j => (μ j)⁻¹)]
    have hne : μ i ≠ μ k := fun h => k.2 h.symm
    refine core_eigenvalues (h3 i) hprod' ?_ hne
    have h3' : (3 : ℕ) • μ i = μ i + μ i + μ i := by
      rw [three_nsmul, add_assoc]
    have h3'' : (3 : ℕ) • (μ i)⁻¹ = (μ i)⁻¹ + (μ i)⁻¹ + (μ i)⁻¹ := by
      rw [three_nsmul, add_assoc]
    rw [← h3', ← h3'', hsum1, hsum2, hsum]

section Engine


theorem not_isType419_of_commute_sp4 {F : Type} [Field F] [Finite F] [CharP F 2]
    {K : Type} [Group K] (hK : IsType419 K) (hs : IsSimpleGroup K)
    (hZ : Subgroup.center K = ⊥) (ι : K →* StatedSp 2 F) (hι : Function.Injective ι)
    (g : StatedSp 2 F) (hg3 : g ^ 3 = 1) (hg1 : g ≠ 1) (hcomm : ∀ k, ι k * g = g * ι k) :
    False := by
  have hnc := Item419Res3.exists_noncommuting_isType419 hK hZ
  set ρ : K →* GL (Fin 2 ⊕ Fin 2) F := (StatedSp 2 F).subtype.comp ι with hρ
  set B : GL (Fin 2 ⊕ Fin 2) F := (g : GL (Fin 2 ⊕ Fin 2) F) with hBdef
  have h2 : (2 : F) = 0 := CharP.cast_eq_zero F 2
  have h3 : (3 : F) ≠ 0 := by
    intro h
    have : (1 : F) = 0 := by linear_combination h - h2
    exact one_ne_zero this
  have hB : ((B : GL (Fin 2 ⊕ Fin 2) F) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) ^ 3 =
      (((1 : Fˣ) : F)) • (1 : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) := by
    have h0 : ((g ^ 3 : StatedSp 2 F) : GL (Fin 2 ⊕ Fin 2) F) = 1 := by rw [hg3]; rfl
    have h1 : (B ^ 3 : GL (Fin 2 ⊕ Fin 2) F) = 1 := by
      rw [hBdef]
      exact h0
    have := congrArg
      (fun x : GL (Fin 2 ⊕ Fin 2) F => (x : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F)) h1
    simpa [Units.val_pow_eq_pow_val] using this
  have hcomm' : ∀ k, ρ k * B = B * ρ k := fun k => congrArg Subtype.val (hcomm k)
  obtain ⟨E', hF', hfin', φ, μ, M, hchar, hMinj, hblock, hμ3, hprod, hsum, hsum_inv, hconst, -⟩ :=
    exists_blockDiagonalization h3 ρ B 1 hB hcomm'
  letI : Field E' := hF'
  haveI : Finite E' := hfin'
  haveI : CharP E' 2 := hchar 2 inferInstance
  have hμ3' : ∀ i, μ i ^ 3 = 1 := fun i => by simpa using hμ3 i
  have hdet : (B : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F).det = 1 := statedSp_det_eq_one g.2
  have hprod' : ∏ i, μ i = 1 := by rw [hprod, hdet, map_one]
  have hsum' : ∑ i, μ i = ∑ i, (μ i)⁻¹ := by
    rw [hsum, hsum_inv, ← statedSp_trace_inv (g := (g : GL (Fin 2 ⊕ Fin 2) F)) g.2]
  have hnc' : ¬ ∀ i j, μ i = μ j := by
    intro hc
    obtain ⟨b, hb⟩ := hconst hc
    have hsp := StatedAPI.mem_statedSp_iff.mp g.2
    have hb' : ((g : GL (Fin 2 ⊕ Fin 2) F) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) =
        b • (1 : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) := hb
    rw [hb'] at hsp
    simp only [Matrix.transpose_smul, Matrix.transpose_one, Matrix.smul_mul, Matrix.one_mul,
      Matrix.mul_smul, Matrix.mul_one, smul_smul] at hsp
    have hbb : b * b = 1 := by
      have := congrFun (congrFun hsp (Sum.inl 0)) (Sum.inr 0)
      simpa [Matrix.fromBlocks_apply₁₂] using this
    have hb1 : b = 1 := by
      have h4 : (b + 1) ^ 2 = 0 := by
        linear_combination hbb + b * h2 + CharTwo.add_self_eq_zero (1 : F)
      have h5 := pow_eq_zero_iff (n := 2) (by norm_num) |>.mp h4
      linear_combination h5 - CharTwo.add_self_eq_zero (1 : F)
    apply hg1
    apply Subtype.ext
    apply Units.ext
    rw [hb', hb1, one_smul]
    rfl
  have hbound := class_card_le_two (by simp) μ hμ3' hprod' hsum' hnc'
  have hMi : Function.Injective M := fun k₁ k₂ h =>
    hι (Subtype.ext (hMinj k₁ k₂ h))
  obtain ⟨f, hf⟩ := exists_injective_slTwo_of_blockDiagonal μ hs hnc M hMi hblock hbound
  exact Item419Res3.not_isType419_of_injective_slTwo hK hs hZ f hf

end Engine

end CFSG.RankThree.PartTwo.Sec4.HeringOF
