module

public import CFSG.ClassicalGroups.Orthogonal.MinusSplitTorus
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KOm.PlaneIsometry

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.KGen

open Matrix CFSG.Open
open CFSG.ClassicalGroups.Orthogonal (minusFlip minusFlip_inv minusFlip_apply_inl
  minusFlip_apply_inr minusFlip_apply_inr_inr minusDiagGL coe_minusDiagGL
  orderOf_minusDiagGL_mulSingle toLinEquiv toLinEquiv_apply)
open CFSG.RankThree.PartTwo.Sec19.Census194.RonanC194.OmegaEven (permGL diagGL coe_diagGL
  mulVec_diagGL mulVec_permGL permGL_mul_diagGL torusEntMinus)
open CFSG.LieType.Universal.Spin (binaryForm binaryForm_apply)
open CFSG.LocalAnalysis.UniquenessCase.UC22.KOm (planeO mem_planeO card_planeO conj_eq_inv)
open scoped commutatorElement

variable {K : Type} [Field K]

private def planeMatHom :
    Matrix (Fin 2) (Fin 2) K →*
      Matrix (Fin 1 ⊕ (Fin 1 ⊕ Fin 2)) (Fin 1 ⊕ (Fin 1 ⊕ Fin 2)) K where
  toFun A := Matrix.fromBlocks 1 0 0 (Matrix.fromBlocks 1 0 0 A)
  map_one' := by simp
  map_mul' A B := by
    rw [Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply]
    simp

private noncomputable def planeGL :
    GL (Fin 2) K →* GL (Fin 1 ⊕ (Fin 1 ⊕ Fin 2)) K :=
  Units.map planeMatHom

@[simp]
private theorem coe_planeGL (X : GL (Fin 2) K) :
    ((planeGL X : GL (Fin 1 ⊕ (Fin 1 ⊕ Fin 2)) K) :
        Matrix (Fin 1 ⊕ (Fin 1 ⊕ Fin 2)) (Fin 1 ⊕ (Fin 1 ⊕ Fin 2)) K) =
      Matrix.fromBlocks 1 0 0 (Matrix.fromBlocks 1 0 0 (X : Matrix (Fin 2) (Fin 2) K)) :=
  rfl

private theorem planeMatHom_injective : Function.Injective (planeMatHom (K := K)) := by
  intro A B hAB
  ext i j
  have h := congrArg (fun M : Matrix (Fin 1 ⊕ (Fin 1 ⊕ Fin 2)) (Fin 1 ⊕ (Fin 1 ⊕ Fin 2)) K =>
    M (Sum.inr (Sum.inr i)) (Sum.inr (Sum.inr j))) hAB
  simpa [planeMatHom] using h

private theorem planeGL_injective : Function.Injective (planeGL (K := K)) :=
  Units.map_injective planeMatHom_injective

private theorem orderOf_planeGL (X : GL (Fin 2) K) :
    orderOf (planeGL X) = orderOf X :=
  orderOf_injective planeGL planeGL_injective X

private theorem mulVec_planeGL_inl (X : GL (Fin 2) K)
    (v : Fin 1 ⊕ (Fin 1 ⊕ Fin 2) → K) (i : Fin 1) :
    (((planeGL X : GL (Fin 1 ⊕ (Fin 1 ⊕ Fin 2)) K) :
        Matrix (Fin 1 ⊕ (Fin 1 ⊕ Fin 2)) (Fin 1 ⊕ (Fin 1 ⊕ Fin 2)) K) *ᵥ v) (Sum.inl i) =
      v (Sum.inl i) := by
  rw [coe_planeGL, Matrix.fromBlocks_mulVec]
  simp

private theorem mulVec_planeGL_inrl (X : GL (Fin 2) K)
    (v : Fin 1 ⊕ (Fin 1 ⊕ Fin 2) → K) (i : Fin 1) :
    (((planeGL X : GL (Fin 1 ⊕ (Fin 1 ⊕ Fin 2)) K) :
        Matrix (Fin 1 ⊕ (Fin 1 ⊕ Fin 2)) (Fin 1 ⊕ (Fin 1 ⊕ Fin 2)) K) *ᵥ v)
        (Sum.inr (Sum.inl i)) = v (Sum.inr (Sum.inl i)) := by
  rw [coe_planeGL, Matrix.fromBlocks_mulVec]
  simp [Matrix.fromBlocks_mulVec]

private theorem mulVec_planeGL_inrr (X : GL (Fin 2) K)
    (v : Fin 1 ⊕ (Fin 1 ⊕ Fin 2) → K) (k : Fin 2) :
    (((planeGL X : GL (Fin 1 ⊕ (Fin 1 ⊕ Fin 2)) K) :
        Matrix (Fin 1 ⊕ (Fin 1 ⊕ Fin 2)) (Fin 1 ⊕ (Fin 1 ⊕ Fin 2)) K) *ᵥ v)
        (Sum.inr (Sum.inr k)) =
      ((X : Matrix (Fin 2) (Fin 2) K) *ᵥ fun k => v (Sum.inr (Sum.inr k))) k := by
  rw [coe_planeGL, Matrix.fromBlocks_mulVec]
  simp [Matrix.fromBlocks_mulVec]

private theorem planeGL_isometry {b c : K} {X : GL (Fin 2) K} (hX : X ∈ planeO b c)
    (v : Fin 1 ⊕ (Fin 1 ⊕ Fin 2) → K) :
    StatedQuadMinus 2 K b c
        (((planeGL X : GL (Fin 1 ⊕ (Fin 1 ⊕ Fin 2)) K) :
          Matrix (Fin 1 ⊕ (Fin 1 ⊕ Fin 2)) (Fin 1 ⊕ (Fin 1 ⊕ Fin 2)) K) *ᵥ v) =
      StatedQuadMinus 2 K b c v := by
  change CFSG.MatrixModel.minusQuadCore 1 K b c
      (((planeGL X : GL (Fin 1 ⊕ (Fin 1 ⊕ Fin 2)) K) :
        Matrix (Fin 1 ⊕ (Fin 1 ⊕ Fin 2)) (Fin 1 ⊕ (Fin 1 ⊕ Fin 2)) K) *ᵥ v) =
    CFSG.MatrixModel.minusQuadCore 1 K b c v
  have hw := mem_planeO.mp hX (fun k : Fin 2 => v (Sum.inr (Sum.inr k)))
  simp only [binaryForm_apply] at hw
  simp only [CFSG.MatrixModel.minusQuadCore, mulVec_planeGL_inl, mulVec_planeGL_inrl,
    mulVec_planeGL_inrr, Fin.sum_univ_one]
  linear_combination hw

private theorem commute_flipGL_planeGL (X : GL (Fin 2) K) :
    permGL (K := K) (minusFlip 1 (0 : Fin 1)) * planeGL X =
      planeGL X * permGL (K := K) (minusFlip 1 (0 : Fin 1)) := by
  apply (toLinEquiv (Fin 1 ⊕ (Fin 1 ⊕ Fin 2)) K).injective
  ext v c
  simp only [toLinEquiv_apply, map_mul, LinearEquiv.mul_apply]
  rw [mulVec_permGL, mulVec_permGL, minusFlip_inv]
  rcases c with c | c | c
  · have hc : c = 0 := Subsingleton.elim c 0
    subst hc
    rw [Function.comp_apply, minusFlip_apply_inl,
      mulVec_planeGL_inrl X v (0 : Fin 1),
      mulVec_planeGL_inl X (v ∘ ⇑(minusFlip 1 (0 : Fin 1))) (0 : Fin 1),
      Function.comp_apply, minusFlip_apply_inl]
  · have hc : c = 0 := Subsingleton.elim c 0
    subst hc
    rw [Function.comp_apply, minusFlip_apply_inr,
      mulVec_planeGL_inl X v (0 : Fin 1),
      mulVec_planeGL_inrl X (v ∘ ⇑(minusFlip 1 (0 : Fin 1))) (0 : Fin 1),
      Function.comp_apply, minusFlip_apply_inr]
  · rw [Function.comp_apply, minusFlip_apply_inr_inr,
      mulVec_planeGL_inrr X v c,
      mulVec_planeGL_inrr X (v ∘ ⇑(minusFlip 1 (0 : Fin 1))) c]
    simp only [Function.comp_apply, minusFlip_apply_inr_inr]

private theorem three_dvd_sub_one_or_add_one [Finite K] [CharP K 2] :
    3 ∣ Nat.card K - 1 ∨ 3 ∣ Nat.card K + 1 := by
  haveI : Fintype K := Fintype.ofFinite K
  obtain ⟨m, -, hcard⟩ := FiniteField.card K 2
  have hq : Nat.card K = 2 ^ (m : ℕ) := by rw [Nat.card_eq_fintype_card, hcard]
  have h3q : ¬ 3 ∣ Nat.card K := by
    rw [hq]
    intro h
    have h32 : 3 ∣ 2 := Nat.Prime.dvd_of_dvd_pow Nat.prime_three h
    norm_num at h32
  have hq2 : 2 ≤ Nat.card K := by
    rw [hq]
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ (m : ℕ) := Nat.pow_le_pow_right (by norm_num) m.pos
  have hmod : Nat.card K % 3 ≠ 0 := fun h => h3q (Nat.dvd_iff_mod_eq_zero.mpr h)
  omega

private theorem permGL_minusFlip_mul_diagGL_mul_inv {m : ℕ} (i : Fin m)
    (e : Fin m ⊕ Fin m ⊕ Fin 2 → Kˣ)
    (he : ∀ j, e (minusFlip m i j) = (e j)⁻¹) :
    permGL (K := K) (minusFlip m i) * diagGL e * (permGL (K := K) (minusFlip m i))⁻¹ =
      (diagGL e)⁻¹ := by
  have h1 : permGL (K := K) (minusFlip m i) * diagGL e =
      diagGL (fun j => e (minusFlip m i j)) * permGL (K := K) (minusFlip m i) := by
    rw [permGL_mul_diagGL, minusFlip_inv]
  rw [h1, mul_assoc, mul_inv_cancel, mul_one, ← map_inv]
  congr 1
  funext j
  exact he j

private theorem torusEntMinus_one_comp_minusFlip (i : Fin 1) (t : Kˣ) :
    ∀ j, torusEntMinus 1 K (Pi.mulSingle i t) (minusFlip 1 i j) =
      (torusEntMinus 1 K (Pi.mulSingle i t) j)⁻¹ := by
  intro j
  rcases j with j | j | j
  · have hj : j = i := Subsingleton.elim j i
    subst hj
    simp [torusEntMinus]
  · have hj : j = i := Subsingleton.elim j i
    subst hj
    simp [torusEntMinus]
  · rw [minusFlip_apply_inr_inr]
    have h : torusEntMinus 1 K (Pi.mulSingle i t) (Sum.inr (Sum.inr j)) = 1 := rfl
    rw [h]
    simp

private theorem exists_orderThree_flip_of_dvd_sub_one [Finite K] [CharP K 2] {b c : K}
    (h3 : 3 ∣ Nat.card K - 1) :
    ∃ g : GL (Fin (2 - 1) ⊕ (Fin (2 - 1)) ⊕ Fin 2) K,
      g ∈ StatedOmega (StatedQuadMinus 2 K b c) ∧ orderOf g = 3 ∧
        permGL (minusFlip (2 - 1) (⟨0, by norm_num⟩ : Fin (2 - 1))) * g *
            (permGL (minusFlip (2 - 1) (⟨0, by norm_num⟩ : Fin (2 - 1))))⁻¹ ∈
          Subgroup.zpowers g := by
  have hdvd : 3 ∣ Nat.card Kˣ := by
    rw [Nat.card_units]
    exact h3
  obtain ⟨t, ht⟩ := exists_prime_orderOf_dvd_card' (p := 3) (hp := ⟨Nat.prime_three⟩) hdvd
  have ht3 : t ^ 3 = 1 := by rw [← ht]; exact pow_orderOf_eq_one t
  have hd : ∀ j : Fin 1, (Pi.mulSingle (0 : Fin 1) t : Fin 1 → Kˣ) j ^ 3 = 1 := by
    intro j
    rw [Subsingleton.elim j 0, Pi.mulSingle_eq_same]
    exact ht3
  let g' : StatedOmega (StatedQuadMinus 2 K b c) :=
    minusDiagGL (b := b) (c := c) (n := 2) (r := 3) (by decide : Odd 3)
      (Pi.mulSingle (0 : Fin 1) t) hd
  have hgord' : orderOf g' = 3 := by
    dsimp only [g']
    exact (orderOf_minusDiagGL_mulSingle (b := b) (c := c) (n := 2) (r := 3)
      (by decide : Odd 3) t (0 : Fin 1) hd).trans ht
  have hconj : permGL (K := K) (minusFlip (2 - 1) (⟨0, by norm_num⟩ : Fin (2 - 1))) *
      (g' : GL (Fin (2 - 1) ⊕ (Fin (2 - 1)) ⊕ Fin 2) K) *
      (permGL (K := K) (minusFlip (2 - 1) (⟨0, by norm_num⟩ : Fin (2 - 1))))⁻¹ =
      (g' : GL (Fin (2 - 1) ⊕ (Fin (2 - 1)) ⊕ Fin 2) K)⁻¹ := by
    dsimp only [g']
    rw [coe_minusDiagGL]
    exact permGL_minusFlip_mul_diagGL_mul_inv (m := 1) (0 : Fin 1) _
      (torusEntMinus_one_comp_minusFlip 0 t)
  refine ⟨(g' : GL (Fin (2 - 1) ⊕ (Fin (2 - 1)) ⊕ Fin 2) K), g'.2, ?_, ?_⟩
  · rw [Subgroup.orderOf_coe, hgord']
  · rw [hconj]
    exact Subgroup.inv_mem _ (Subgroup.mem_zpowers _)

private theorem exists_orderThree_flip_of_dvd_add_one [Finite K] [CharP K 2] {b c : K}
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) (h3 : 3 ∣ Nat.card K + 1) :
    ∃ g : GL (Fin (2 - 1) ⊕ (Fin (2 - 1)) ⊕ Fin 2) K,
      g ∈ StatedOmega (StatedQuadMinus 2 K b c) ∧ orderOf g = 3 ∧
        permGL (minusFlip (2 - 1) (⟨0, by norm_num⟩ : Fin (2 - 1))) * g *
            (permGL (minusFlip (2 - 1) (⟨0, by norm_num⟩ : Fin (2 - 1))))⁻¹ ∈
          Subgroup.zpowers g := by
  classical
  have hdvd3 : 3 ∣ Nat.card ↥(planeO b c) := by
    rw [card_planeO hirr]
    exact Dvd.dvd.mul_left h3 2
  have hdvd2 : 2 ∣ Nat.card ↥(planeO b c) := by
    rw [card_planeO hirr]
    exact dvd_mul_right 2 _
  obtain ⟨ρ, hρord⟩ := exists_prime_orderOf_dvd_card' (G := ↥(planeO b c)) (p := 3)
    (hp := ⟨Nat.prime_three⟩) hdvd3
  obtain ⟨τ, hτord⟩ := exists_prime_orderOf_dvd_card' (G := ↥(planeO b c)) (p := 2)
    (hp := ⟨Nat.prime_two⟩) hdvd2
  have hτ2' : τ ^ 2 = 1 := by
    have h := pow_orderOf_eq_one τ
    rwa [hτord] at h
  have hτ2 : (τ : GL (Fin 2) K) ^ 2 = 1 := by
    have h := congrArg (Subgroup.subtype (planeO b c)) hτ2'
    simpa using h
  have hτ1 : (τ : GL (Fin 2) K) ≠ 1 := by
    intro h
    have h1 : orderOf (τ : GL (Fin 2) K) = 2 := by
      rw [Subgroup.orderOf_coe, hτord]
    rw [h, orderOf_one] at h1
    norm_num at h1
  have hρGLord : orderOf (ρ : GL (Fin 2) K) = 3 := by
    rw [Subgroup.orderOf_coe, hρord]
  have hρodd : Odd (orderOf (ρ : GL (Fin 2) K)) := by
    rw [hρGLord]
    exact ⟨1, by norm_num⟩
  have hconj : (τ : GL (Fin 2) K) * (ρ : GL (Fin 2) K) * (τ : GL (Fin 2) K)⁻¹ =
      (ρ : GL (Fin 2) K)⁻¹ :=
    conj_eq_inv hirr τ.2 hτ2 hτ1 ρ.2 hρodd
  have hρ3' : ρ ^ 3 = 1 := by
    have h := pow_orderOf_eq_one ρ
    rwa [hρord] at h
  have hρ3 : (ρ : GL (Fin 2) K) ^ 3 = 1 := by
    have h := congrArg (Subgroup.subtype (planeO b c)) hρ3'
    simpa using h
  have hρinv : (ρ : GL (Fin 2) K)⁻¹ * (ρ : GL (Fin 2) K)⁻¹ = (ρ : GL (Fin 2) K) := by
    calc (ρ : GL (Fin 2) K)⁻¹ * (ρ : GL (Fin 2) K)⁻¹
        = (ρ : GL (Fin 2) K)⁻¹ * (ρ : GL (Fin 2) K)⁻¹ * (ρ : GL (Fin 2) K) ^ 3 := by
          rw [hρ3, mul_one]
      _ = (ρ : GL (Fin 2) K) := by group
  have hcomm : ⁅(τ : GL (Fin 2) K), (ρ : GL (Fin 2) K)⁆ = (ρ : GL (Fin 2) K) := by
    rw [commutatorElement_def, hconj]
    exact hρinv
  have himg : ⁅planeGL (τ : GL (Fin 2) K), planeGL (ρ : GL (Fin 2) K)⁆ =
      planeGL (ρ : GL (Fin 2) K) := by
    have h := map_commutatorElement (f := planeGL) (g₁ := (τ : GL (Fin 2) K))
      (g₂ := (ρ : GL (Fin 2) K))
    rw [hcomm] at h
    exact h.symm
  have hmem : planeGL (ρ : GL (Fin 2) K) ∈ StatedOmega (StatedQuadMinus 2 K b c) := by
    rw [StatedOmega, ← himg]
    exact Subgroup.commutator_mem_commutator
      (Subgroup.subset_closure (planeGL_isometry (b := b) (c := c) τ.2))
      (Subgroup.subset_closure (planeGL_isometry (b := b) (c := c) ρ.2))
  have hgord : orderOf (planeGL (ρ : GL (Fin 2) K)) = 3 := by
    rw [orderOf_planeGL, hρGLord]
  have hflip :
      permGL (K := K) (minusFlip (2 - 1) (⟨0, by norm_num⟩ : Fin (2 - 1))) *
        planeGL (ρ : GL (Fin 2) K) *
        (permGL (K := K) (minusFlip (2 - 1) (⟨0, by norm_num⟩ : Fin (2 - 1))))⁻¹ =
      planeGL (ρ : GL (Fin 2) K) := by
    change permGL (K := K) (minusFlip 1 (0 : Fin 1)) * planeGL (ρ : GL (Fin 2) K) *
      (permGL (K := K) (minusFlip 1 (0 : Fin 1)))⁻¹ = planeGL (ρ : GL (Fin 2) K)
    rw [commute_flipGL_planeGL (ρ : GL (Fin 2) K), mul_assoc, mul_inv_cancel, mul_one]
  refine ⟨planeGL (ρ : GL (Fin 2) K), hmem, hgord, ?_⟩
  rw [hflip]
  exact Subgroup.mem_zpowers _

theorem exists_orderThree_flip [Finite K] [CharP K 2] {b c : K}
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) :
    ∃ g ∈ StatedOmega (StatedQuadMinus 2 K b c), orderOf g = 3 ∧
      permGL (minusFlip (2 - 1) ⟨0, by norm_num⟩) * g *
          (permGL (minusFlip (2 - 1) ⟨0, by norm_num⟩))⁻¹ ∈ Subgroup.zpowers g := by
  rcases three_dvd_sub_one_or_add_one (K := K) with h3 | h3
  · exact exists_orderThree_flip_of_dvd_sub_one (b := b) (c := c) h3
  · exact exists_orderThree_flip_of_dvd_add_one (b := b) (c := c) hirr h3

end CFSG.LocalAnalysis.UniquenessCase.UC22.KGen
