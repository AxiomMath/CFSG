module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KSL3PointTorusProof
public import CFSG.GroupTheory.SteinbergBKLinearPlaneSL2

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.Vol2 CFSG.Quasithin.Vol2.KGNat
open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.Quasithin.Vol2.KGNat.PointStab
open CFSG.QuasithinUnique.Vol2Native.A312L
open CFSG.ClassicalInvolution.ModelFacts.OddCover
open CFSG.LocalAnalysis.ComponentInitial LinearFlag
open scoped Matrix Pointwise

variable {K : Type} [Field K] [CharP K 2] [Finite K]

private theorem uSL_sub_mulVec_mem_stdLine (a b : K) (y : Fin 3 → K) :
    -y + ((uSL a b 0 : Matrix.SpecialLinearGroup (Fin 3) K) :
      Matrix (Fin 3) (Fin 3) K) *ᵥ y ∈ stdLine K := by
  rw [coe_uSL, uMat_mulVec]
  constructor <;> simp

private def liftSL (L : Matrix.SpecialLinearGroup (Fin 2) K) :
    Matrix.SpecialLinearGroup (Fin 3) K :=
  ⟨!![1, 0, 0; 0, (L : Matrix (Fin 2) (Fin 2) K) 0 0, (L : Matrix (Fin 2) (Fin 2) K) 0 1;
      0, (L : Matrix (Fin 2) (Fin 2) K) 1 0, (L : Matrix (Fin 2) (Fin 2) K) 1 1], by
    have hdet : (L : Matrix (Fin 2) (Fin 2) K) 0 0 * (L : Matrix (Fin 2) (Fin 2) K) 1 1 -
        (L : Matrix (Fin 2) (Fin 2) K) 0 1 * (L : Matrix (Fin 2) (Fin 2) K) 1 0 = 1 := by
      have h := L.2
      rwa [Matrix.det_fin_two] at h
    rw [Matrix.det_fin_three]
    simpa using hdet⟩

private theorem liftSL_mem_stabE0 (L : Matrix.SpecialLinearGroup (Fin 2) K) :
    liftSL L ∈ stabE0 K := by
  rw [mem_stabE0]
  ext i
  fin_cases i <;> simp [liftSL, Matrix.mulVec, dotProduct, Fin.sum_univ_three]

private theorem liftSL_mul_uSL (L : Matrix.SpecialLinearGroup (Fin 2) K) (a b : K) :
    liftSL L * uSL a b 0 =
      uSL (a * (L : Matrix (Fin 2) (Fin 2) K) 1 1 -
            b * (L : Matrix (Fin 2) (Fin 2) K) 1 0)
          (b * (L : Matrix (Fin 2) (Fin 2) K) 0 0 -
            a * (L : Matrix (Fin 2) (Fin 2) K) 0 1) 0 * liftSL L := by
  have hdet : (L : Matrix (Fin 2) (Fin 2) K) 0 0 * (L : Matrix (Fin 2) (Fin 2) K) 1 1 -
      (L : Matrix (Fin 2) (Fin 2) K) 0 1 * (L : Matrix (Fin 2) (Fin 2) K) 1 0 = 1 := by
    have h := L.2
    rwa [Matrix.det_fin_two] at h
  set M : Matrix (Fin 3) (Fin 3) K :=
    !![1, 0, 0; 0, (L : Matrix (Fin 2) (Fin 2) K) 0 0, (L : Matrix (Fin 2) (Fin 2) K) 0 1;
      0, (L : Matrix (Fin 2) (Fin 2) K) 1 0, (L : Matrix (Fin 2) (Fin 2) K) 1 1] with hM
  have hlift : ((liftSL L : Matrix.SpecialLinearGroup (Fin 3) K) :
      Matrix (Fin 3) (Fin 3) K) = M := rfl
  refine Matrix.SpecialLinearGroup.ext _ _ fun i j => ?_
  rw [Matrix.SpecialLinearGroup.coe_mul, hlift, coe_uSL, Matrix.SpecialLinearGroup.coe_mul,
    hlift, coe_uSL]
  change (M * uMat a b 0) i j =
    (uMat (a * (L : Matrix (Fin 2) (Fin 2) K) 1 1 -
        b * (L : Matrix (Fin 2) (Fin 2) K) 1 0)
      (b * (L : Matrix (Fin 2) (Fin 2) K) 0 0 -
        a * (L : Matrix (Fin 2) (Fin 2) K) 0 1) 0 * M) i j
  have hdet' : (L : Matrix (Fin 2) (Fin 2) K) 1 1 * (L : Matrix (Fin 2) (Fin 2) K) 0 0 -
      (L : Matrix (Fin 2) (Fin 2) K) 1 0 * (L : Matrix (Fin 2) (Fin 2) K) 0 1 = 1 := by
    linear_combination hdet
  fin_cases i <;> fin_cases j <;>
    simp [hM, uMat, Matrix.mul_apply, Fin.sum_univ_three, hdet]
  · linear_combination -a * hdet'
  · linear_combination -b * hdet'

private theorem eq_one_of_fixed_e0_of_odd {L : Matrix.SpecialLinearGroup (Fin 2) K}
    (hfix : (L : Matrix (Fin 2) (Fin 2) K) *ᵥ ![1, 0] = ![1, 0])
    {r : ℕ} (hodd : Odd r) (hr : L ^ r = 1) : L = 1 := by
  have h00 : (L : Matrix (Fin 2) (Fin 2) K) 0 0 = 1 := by
    simpa [Matrix.mulVec, dotProduct, Fin.sum_univ_two] using congrFun hfix 0
  have h10 : (L : Matrix (Fin 2) (Fin 2) K) 1 0 = 0 := by
    simpa [Matrix.mulVec, dotProduct, Fin.sum_univ_two] using congrFun hfix 1
  have h11 : (L : Matrix (Fin 2) (Fin 2) K) 1 1 = 1 := by
    have hdet : (L : Matrix (Fin 2) (Fin 2) K).det = 1 := L.2
    rw [Matrix.det_fin_two] at hdet
    simpa [h00, h10] using hdet
  have hLeq : L = ⟨!![1, (L : Matrix (Fin 2) (Fin 2) K) 0 1; 0, 1], by
      rw [Matrix.det_fin_two]; simp⟩ := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [h00, h10, h11]
  have hsq : L ^ 2 = 1 := by
    rw [hLeq]
    apply Subtype.ext
    change (!![1, (L : Matrix (Fin 2) (Fin 2) K) 0 1; 0, 1] :
      Matrix (Fin 2) (Fin 2) K) ^ 2 = 1
    rw [pow_two]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.one_apply,
        CharTwo.add_self_eq_zero]
  exact orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes hodd.coprime_two_left
    (orderOf_dvd_of_pow_eq_one hsq) (orderOf_dvd_of_pow_eq_one hr))

private theorem conj_mulVec_e0_eq_e0 {L A : Matrix.SpecialLinearGroup (Fin 2) K}
    {v : Fin 2 → K}
    (hA : (A : Matrix (Fin 2) (Fin 2) K) *ᵥ ![1, 0] = v)
    (hfix : (L : Matrix (Fin 2) (Fin 2) K) *ᵥ v = v) :
    (((A⁻¹ * L * A : Matrix.SpecialLinearGroup (Fin 2) K)) :
      Matrix (Fin 2) (Fin 2) K) *ᵥ ![1, 0] = ![1, 0] := by
  have hAinv : ((A⁻¹ : Matrix.SpecialLinearGroup (Fin 2) K) :
      Matrix (Fin 2) (Fin 2) K) *ᵥ v = ![1, 0] := by
    calc ((A⁻¹ : Matrix.SpecialLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) *ᵥ v
        = ((A⁻¹ : Matrix.SpecialLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) *ᵥ
            (((A : Matrix.SpecialLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) *ᵥ
              ![1, 0]) := by rw [hA]
      _ = ((((A⁻¹ : Matrix.SpecialLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) *
            ((A : Matrix.SpecialLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K)) *ᵥ
              ![1, 0]) := by rw [Matrix.mulVec_mulVec]
      _ = ![1, 0] := by
        rw [← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel,
          Matrix.SpecialLinearGroup.coe_one, Matrix.one_mulVec]
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul]
  calc ((((A⁻¹ : Matrix.SpecialLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) *
        ((L : Matrix.SpecialLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K)) *
          ((A : Matrix.SpecialLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K)) *ᵥ
            ![1, 0]
      = ((A⁻¹ : Matrix.SpecialLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) *ᵥ
          (((L : Matrix.SpecialLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) *ᵥ
            (((A : Matrix.SpecialLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) *ᵥ
              ![1, 0])) := by rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
    _ = ((A⁻¹ : Matrix.SpecialLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) *ᵥ
          (((L : Matrix.SpecialLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) *ᵥ v) := by
          rw [hA]
    _ = ((A⁻¹ : Matrix.SpecialLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) *ᵥ v := by
          rw [hfix]
    _ = ![1, 0] := hAinv

private theorem eq_one_of_pow_eq_one_of_fixed {L : Matrix.SpecialLinearGroup (Fin 2) K}
    {v : Fin 2 → K} (hv : v ≠ 0)
    (hfix : (L : Matrix (Fin 2) (Fin 2) K) *ᵥ v = v)
    {r : ℕ} (hodd : Odd r) (hr : L ^ r = 1) : L = 1 := by
  obtain ⟨A, hA⟩ := CFSG.GroupTheory.SteinbergBK.exists_sl2_mulVec_single v hv
  have hA' : ((A : Matrix.SpecialLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) *ᵥ
      ![1, 0] = v := by
    have hvec : (![1, 0] : Fin 2 → K) = Pi.single 0 1 := by
      ext i
      fin_cases i <;> rfl
    simpa [hvec, Matrix.mulVec_single_one] using hA
  let L' : Matrix.SpecialLinearGroup (Fin 2) K := A⁻¹ * L * A
  have hL'fix : (L' : Matrix (Fin 2) (Fin 2) K) *ᵥ ![1, 0] = ![1, 0] := by
    simpa [L'] using conj_mulVec_e0_eq_e0 hA' hfix
  have hL'pow : L' ^ r = 1 := by
    change (A⁻¹ * L * A) ^ r = 1
    rw [show A⁻¹ * L * A = A⁻¹ * L * (A⁻¹)⁻¹ by rw [inv_inv], conj_pow, hr]
    group
  have hL'one : L' = 1 := eq_one_of_fixed_e0_of_odd hL'fix hodd hL'pow
  calc L = A * L' * A⁻¹ := by
        change L = A * (A⁻¹ * L * A) * A⁻¹
        group
    _ = 1 := by rw [hL'one]; group

private theorem lev_fixed_of_stdLine {B : Matrix.SpecialLinearGroup (Fin 3) K}
    (hB : B ∈ stabE0 K) {z : Fin 3 → K}
    (hz : -z + (B : Matrix (Fin 3) (Fin 3) K) *ᵥ z ∈ stdLine K) :
    ((leviHom K ⟨B, hB⟩ : Matrix.SpecialLinearGroup (Fin 2) K) :
      Matrix (Fin 2) (Fin 2) K) *ᵥ ![z 1, z 2] = ![z 1, z 2] := by
  obtain ⟨h10, h20⟩ := (stabE0_entries hB).2
  have hx1 : (B : Matrix (Fin 3) (Fin 3) K) 1 1 * z 1 +
      (B : Matrix (Fin 3) (Fin 3) K) 1 2 * z 2 = z 1 := by
    have h := hz.1
    simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three, h10] at h
    linear_combination h
  have hx2 : (B : Matrix (Fin 3) (Fin 3) K) 2 1 * z 1 +
      (B : Matrix (Fin 3) (Fin 3) K) 2 2 * z 2 = z 2 := by
    have h := hz.2
    simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three, h20] at h
    linear_combination h
  ext i
  fin_cases i
  · simpa [Matrix.mulVec, dotProduct, Fin.sum_univ_two, lev_apply, leviHom_coe] using hx1
  · simpa [Matrix.mulVec, dotProduct, Fin.sum_univ_two, lev_apply, leviHom_coe] using hx2

private theorem f_inv_mul_apply {W : Type} [CommGroup W] [Finite W]
    {H : Subgroup (MulAut W)} {ρ : ↥(StatedSL 3 K) →* ↥H} {f : W → Fin 3 → K}
    (hf : IsCoord (linModelNat (StatedSL 3 K)) H ⊥ ρ f)
    {h : Matrix.SpecialLinearGroup (Fin 3) K}
    {Kstar' : Subgroup ↥H} (e : ↥(stabE0 K) ≃* ↥Kstar')
    (he : ∀ B : ↥(stabE0 K), ((e B : ↥Kstar') : MulAut W) =
      ((rho3 ρ (h * (B : Matrix.SpecialLinearGroup (Fin 3) K) * h⁻¹) : ↥H) : MulAut W))
    (B : ↥(stabE0 K)) (w : W) (y : Fin 3 → K)
    (hy : (h : Matrix (Fin 3) (Fin 3) K) *ᵥ y = f w) :
    f (w⁻¹ * (((e B : ↥Kstar') : MulAut W) w)) =
      (h : Matrix (Fin 3) (Fin 3) K) *ᵥ
        (-y + (B : Matrix (Fin 3) (Fin 3) K) *ᵥ y) := by
  have h1 : f (w⁻¹ * (((e B : ↥Kstar') : MulAut W) w)) =
      -f w + (((h * (B : Matrix.SpecialLinearGroup (Fin 3) K) * h⁻¹) :
        Matrix.SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ f w := by
    rw [hf.map_mul, hf.map_inv, he B, hf.act3]
  have hyinv : ((h⁻¹ : Matrix.SpecialLinearGroup (Fin 3) K) :
      Matrix (Fin 3) (Fin 3) K) *ᵥ f w = y := by
    rw [← hy, ginv_g_mulVec]
  rw [h1, gconj_mulVec, hyinv, ← hy, ← Matrix.mulVec_neg, ← Matrix.mulVec_add]

private theorem uSL_mem_of_ne {R : Subgroup ↥(stabE0 K)}
    (hR : ∀ C : ↥(stabE0 K), ∀ r ∈ R, C * r * C⁻¹ ∈ R)
    {a b : K} (hB : (⟨uSL a b 0, uSL_mem_stabE0 a b 0⟩ : ↥(stabE0 K)) ∈ R)
    (hab : a ≠ 0 ∨ b ≠ 0) (c d : K) (hcd : c ≠ 0 ∨ d ≠ 0) :
    (⟨uSL c d 0, uSL_mem_stabE0 c d 0⟩ : ↥(stabE0 K)) ∈ R := by
  have hcdv : (![c, d] : Fin 2 → K) ≠ 0 := by
    intro h
    rcases hcd with hc | hd
    · exact hc (by simpa using congrFun h 0)
    · exact hd (by simpa using congrFun h 1)
  have habv : (![a, b] : Fin 2 → K) ≠ 0 := by
    intro h
    rcases hab with ha | hb
    · exact ha (by simpa using congrFun h 0)
    · exact hb (by simpa using congrFun h 1)
  obtain ⟨M, hM⟩ := CFSG.GroupTheory.SteinbergBK.exists_sl2_mulVec_eq
    ![c, d] ![a, b] hcdv habv
  let L : Matrix.SpecialLinearGroup (Fin 2) K := Matrix.SpecialLinearGroup.transpose M
  have hMdet : (M : Matrix (Fin 2) (Fin 2) K).det = 1 := M.2
  rw [Matrix.det_fin_two] at hMdet
  have h0 : (M : Matrix (Fin 2) (Fin 2) K) 0 0 * c +
      (M : Matrix (Fin 2) (Fin 2) K) 0 1 * d = a := by
    have h := congrFun hM 0
    simpa [Matrix.mulVec, dotProduct, Fin.sum_univ_two] using h
  have h1 : (M : Matrix (Fin 2) (Fin 2) K) 1 0 * c +
      (M : Matrix (Fin 2) (Fin 2) K) 1 1 * d = b := by
    have h := congrFun hM 1
    simpa [Matrix.mulVec, dotProduct, Fin.sum_univ_two] using h
  have hc : a * (L : Matrix (Fin 2) (Fin 2) K) 1 1 -
      b * (L : Matrix (Fin 2) (Fin 2) K) 1 0 = c := by
    change a * (M : Matrix (Fin 2) (Fin 2) K) 1 1 -
      b * (M : Matrix (Fin 2) (Fin 2) K) 0 1 = c
    linear_combination - (M : Matrix (Fin 2) (Fin 2) K) 1 1 * h0 +
      (M : Matrix (Fin 2) (Fin 2) K) 0 1 * h1 + c * hMdet
  have hd : b * (L : Matrix (Fin 2) (Fin 2) K) 0 0 -
      a * (L : Matrix (Fin 2) (Fin 2) K) 0 1 = d := by
    change b * (M : Matrix (Fin 2) (Fin 2) K) 0 0 -
      a * (M : Matrix (Fin 2) (Fin 2) K) 1 0 = d
    linear_combination - (M : Matrix (Fin 2) (Fin 2) K) 0 0 * h1 +
      (M : Matrix (Fin 2) (Fin 2) K) 1 0 * h0 + d * hMdet
  let C : ↥(stabE0 K) := ⟨liftSL L, liftSL_mem_stabE0 L⟩
  have hconj : C * (⟨uSL a b 0, uSL_mem_stabE0 a b 0⟩ : ↥(stabE0 K)) * C⁻¹ =
      (⟨uSL c d 0, uSL_mem_stabE0 c d 0⟩ : ↥(stabE0 K)) := by
    apply Subtype.ext
    change liftSL L * uSL a b 0 * (liftSL L)⁻¹ = uSL c d 0
    rw [liftSL_mul_uSL L a b, hc, hd, mul_assoc, mul_inv_cancel, mul_one]
  have hmem := hR C _ hB
  rwa [hconj] at hmem

private theorem exists_pointCore_equiv {W : Type} [CommGroup W] [Finite W]
    {H : Subgroup (MulAut W)} {ρ : ↥(StatedSL 3 K) →* ↥H} {f : W → Fin 3 → K}
    (hSL : commutator (Matrix.SpecialLinearGroup (Fin 2) K) = ⊤)
    (hf : IsCoord (linModelNat (StatedSL 3 K)) H ⊥ ρ f)
    (h : Matrix.SpecialLinearGroup (Fin 3) K) :
    ∃ e : ↥(stabE0 K) ≃* ↥(Hinf (MulAction.stabilizer ↥H
        ((preLine hf h : Subgroup W) : Set W))),
      ∀ B : ↥(stabE0 K), ((e B : ↥(Hinf (MulAction.stabilizer ↥H
          ((preLine hf h : Subgroup W) : Set W)))) : MulAut W) =
        ((rho3 ρ (h * (B : Matrix.SpecialLinearGroup (Fin 3) K) * h⁻¹) : ↥H) :
          MulAut W) := by
  obtain ⟨e0, he0⟩ := exists_equiv_stabE0 hSL hf h
  let Kstar' : Subgroup ↥H :=
    Hinf (MulAction.stabilizer ↥H ((preLine hf h : Subgroup W) : Set W))
  let A : Subgroup (MulAut W) :=
    H ⊓ Ch11.SecA.stabW (hf.pre (gmap h (flagSpace 3 K 1)).toAddSubgroup)
  let ePK : ↥(CFSG.Quasithin.perfectCore A) ≃* ↥Kstar' :=
    { toFun := fun p =>
        let pH : ↥H := ⟨(p : MulAut W),
          (inf_le_left : A ≤ H) ((CFSG.Quasithin.perfectCore_le A) p.2)⟩
        ⟨pH, (mem_hinf_stabilizer_iff hf h (z := pH)).mpr p.2⟩
      invFun := fun z => ⟨(z : MulAut W),
        (mem_hinf_stabilizer_iff hf h (z := (z : ↥H))).mp z.2⟩
      left_inv := fun p => Subtype.ext rfl
      right_inv := fun z => Subtype.ext rfl
      map_mul' := fun p q => Subtype.ext rfl }
  let e : ↥(stabE0 K) ≃* ↥Kstar' := e0.trans ePK
  refine ⟨e, ?_⟩
  intro B
  simpa [e, ePK] using he0 B

private theorem pointCore_U_eq_ker {W : Type} [CommGroup W] [Finite W]
    {H : Subgroup (MulAut W)} {ρ : ↥(StatedSL 3 K) →* ↥H} {f : W → Fin 3 → K}
    (hSL : commutator (Matrix.SpecialLinearGroup (Fin 2) K) = ⊤)
    (hf : IsCoord (linModelNat (StatedSL 3 K)) H ⊥ ρ f)
    {h : Matrix.SpecialLinearGroup (Fin 3) K}
    {Kstar' : Subgroup ↥H} (e : ↥(stabE0 K) ≃* ↥Kstar')
    (he : ∀ B : ↥(stabE0 K), ((e B : ↥Kstar') : MulAut W) =
      ((rho3 ρ (h * (B : Matrix.SpecialLinearGroup (Fin 3) K) * h⁻¹) : ↥H) : MulAut W))
    (hKstar' : Kstar' = Hinf (MulAction.stabilizer ↥H
      ((preLine hf h : Subgroup W) : Set W))) :
    CFSG.Open.pCoreOf 2 Kstar' =
      ((leviHom K).ker.map e.toMonoidHom).map Kstar'.subtype := by
  subst hKstar'
  apply le_antisymm
  · intro u hu
    obtain ⟨a, b, rfl⟩ := (mem_pCore_hinf_iff_exists_uSL hSL hf h u).mp hu
    let B : ↥(stabE0 K) := ⟨uSL a b 0, uSL_mem_stabE0 a b 0⟩
    have hB : B ∈ (leviHom K).ker := by
      rw [MonoidHom.mem_ker, leviHom_uSL]
    refine Subgroup.mem_map.mpr ⟨e B, Subgroup.mem_map_of_mem e.toMonoidHom hB, ?_⟩
    apply Subtype.ext
    exact he B
  · intro u hu
    obtain ⟨z, hz, hzu⟩ := Subgroup.mem_map.mp hu
    obtain ⟨B, hB, hBe⟩ := Subgroup.mem_map.mp hz
    rw [← hzu, ← hBe]
    apply (mem_pCore_hinf_iff_exists_uSL hSL hf h _).mpr
    refine ⟨(B : Matrix.SpecialLinearGroup (Fin 3) K) 0 1,
      (B : Matrix.SpecialLinearGroup (Fin 3) K) 0 2, ?_⟩
    apply Subtype.ext
    change ((e B : ↥(Hinf (MulAction.stabilizer ↥H
      ((preLine hf h : Subgroup W) : Set W)))) : MulAut W) =
      ((rho3 ρ (h * uSL ((B : Matrix.SpecialLinearGroup (Fin 3) K) 0 1)
        ((B : Matrix.SpecialLinearGroup (Fin 3) K) 0 2) 0 * h⁻¹) : ↥H) : MulAut W)
    rw [he B]
    congr 1
    exact congrArg (fun M : Matrix.SpecialLinearGroup (Fin 3) K =>
      rho3 ρ (h * M * h⁻¹)) (eq_uSL_of_mem_ker hB)

private theorem pointCore_trivial_quotient {W : Type} [CommGroup W] [Finite W]
    {H : Subgroup (MulAut W)} {ρ : ↥(StatedSL 3 K) →* ↥H} {f : W → Fin 3 → K}
    (hSL : commutator (Matrix.SpecialLinearGroup (Fin 2) K) = ⊤)
    (hf : IsCoord (linModelNat (StatedSL 3 K)) H ⊥ ρ f)
    {h : Matrix.SpecialLinearGroup (Fin 3) K}
    {Kstar' : Subgroup ↥H} (e : ↥(stabE0 K) ≃* ↥Kstar')
    (he : ∀ B : ↥(stabE0 K), ((e B : ↥Kstar') : MulAut W) =
      ((rho3 ρ (h * (B : Matrix.SpecialLinearGroup (Fin 3) K) * h⁻¹) : ↥H) : MulAut W))
    {U : Subgroup ↥H}
    (hUker : U = ((leviHom K).ker.map e.toMonoidHom).map Kstar'.subtype)
    {u : ↥H} (hu : u ∈ U) (w : W) :
    w⁻¹ * ((u : MulAut W) w) ∈ preLine hf h := by
  rw [hUker] at hu
  obtain ⟨z, hz, hzu⟩ := Subgroup.mem_map.mp hu
  obtain ⟨B, hB, hBe⟩ := Subgroup.mem_map.mp hz
  have huB : u = ((e B : ↥Kstar') : ↥H) :=
    hzu.symm.trans (congrArg Kstar'.subtype hBe.symm)
  let y : Fin 3 → K := ((h⁻¹ : Matrix.SpecialLinearGroup (Fin 3) K) :
    Matrix (Fin 3) (Fin 3) K) *ᵥ f w
  have hy : (h : Matrix (Fin 3) (Fin 3) K) *ᵥ y = f w := g_ginv_mulVec h (f w)
  have hfeq := f_inv_mul_apply hf e he B w y hy
  have hmem : f (w⁻¹ * ((u : MulAut W) w)) ∈ gmap h (stdLine K) := by
    rw [huB, hfeq, eq_uSL_of_mem_ker hB]
    refine mem_gmap.mpr ?_
    rw [ginv_g_mulVec]
    exact uSL_sub_mulVec_mem_stdLine _ _ y
  rw [preLine, hf.mem_pre]
  simpa [stdLine_eq_flagSpace] using hmem

private theorem lev_fpf_of_stdLine {B : ↥(stabE0 K)} {r : ℕ} (hodd : Odd r)
    (hBnot : B ∉ (leviHom K).ker) (hBpow : B ^ r ∈ (leviHom K).ker)
    {z : Fin 3 → K} (hz : -z + (B : Matrix (Fin 3) (Fin 3) K) *ᵥ z ∈ stdLine K) :
    z ∈ stdLine K := by
  have hfix := lev_fixed_of_stdLine B.2 hz
  have hLpow : (leviHom K B) ^ r = 1 := by
    rw [← map_pow]
    exact MonoidHom.mem_ker.mp hBpow
  have hLnot : leviHom K B ≠ 1 := fun h => hBnot (MonoidHom.mem_ker.mpr h)
  by_cases hz0 : (![z 1, z 2] : Fin 2 → K) = 0
  · refine ⟨?_, ?_⟩
    · simpa using congrFun hz0 0
    · simpa using congrFun hz0 1
  · exact absurd (eq_one_of_pow_eq_one_of_fixed hz0 hfix hodd hLpow) hLnot

private theorem pointCore_fpf {W : Type} [CommGroup W] [Finite W]
    {H : Subgroup (MulAut W)} {ρ : ↥(StatedSL 3 K) →* ↥H} {f : W → Fin 3 → K}
    (hSL : commutator (Matrix.SpecialLinearGroup (Fin 2) K) = ⊤)
    (hf : IsCoord (linModelNat (StatedSL 3 K)) H ⊥ ρ f)
    {h : Matrix.SpecialLinearGroup (Fin 3) K}
    {Kstar' : Subgroup ↥H} (e : ↥(stabE0 K) ≃* ↥Kstar')
    (he : ∀ B : ↥(stabE0 K), ((e B : ↥Kstar') : MulAut W) =
      ((rho3 ρ (h * (B : Matrix.SpecialLinearGroup (Fin 3) K) * h⁻¹) : ↥H) : MulAut W))
    {U : Subgroup ↥H}
    (hUker : U = ((leviHom K).ker.map e.toMonoidHom).map Kstar'.subtype)
    {r : ℕ} (hodd : Odd r) {k : ↥H} (hk : k ∈ Kstar') (hknotU : k ∉ U)
    (hkpow : k ^ r ∈ U) {w : W}
    (hw : w⁻¹ * ((k : MulAut W) w) ∈ preLine hf h) :
    w ∈ preLine hf h := by
  have hUle : U ≤ Kstar' := hUker ▸ Subgroup.map_subtype_le _
  have hkpow' : (⟨k ^ r, hUle hkpow⟩ : ↥Kstar') ∈ (leviHom K).ker.map e.toMonoidHom := by
    have hkpowU : k ^ r ∈ ((leviHom K).ker.map e.toMonoidHom).map Kstar'.subtype := by
      rwa [← hUker]
    obtain ⟨z, hz, hzu⟩ := Subgroup.mem_map.mp hkpowU
    rwa [show z = (⟨k ^ r, hUle hkpow⟩ : ↥Kstar') from Subtype.ext hzu] at hz
  obtain ⟨B, hBk⟩ := e.surjective (⟨k, hk⟩ : ↥Kstar')
  have hBnot : B ∉ (leviHom K).ker := by
    intro hB
    exact hknotU (by
      rw [hUker]
      exact Subgroup.mem_map.mpr ⟨e B, Subgroup.mem_map_of_mem e.toMonoidHom hB,
        by simpa using congrArg (fun x : ↥Kstar' => (x : ↥H)) hBk⟩)
  have hBpow : B ^ r ∈ (leviHom K).ker := by
    refine (Subgroup.mem_map_iff_mem (f := e.toMonoidHom) e.injective).mp ?_
    rw [map_pow]; change (e B) ^ r ∈ (leviHom K).ker.map e.toMonoidHom
    rw [hBk]; simpa using hkpow'
  let y : Fin 3 → K := ((h⁻¹ : Matrix.SpecialLinearGroup (Fin 3) K) :
    Matrix (Fin 3) (Fin 3) K) *ᵥ f w
  have hy : (h : Matrix (Fin 3) (Fin 3) K) *ᵥ y = f w := g_ginv_mulVec h (f w)
  have hfeq := f_inv_mul_apply hf e he B w y hy
  have hk_eq : k = ((e B : ↥Kstar') : ↥H) := by
    simpa using (congrArg (fun x : ↥Kstar' => (x : ↥H)) hBk).symm
  have hstd : -y + (B : Matrix (Fin 3) (Fin 3) K) *ᵥ y ∈ stdLine K := by
    rw [hk_eq] at hw
    have hmem : f (w⁻¹ * (((e B : ↥Kstar') : MulAut W) w)) ∈ gmap h (stdLine K) := by
      have := hf.mem_pre.mp hw
      simpa [stdLine_eq_flagSpace] using this
    rw [hfeq] at hmem
    rwa [mem_gmap, ginv_g_mulVec] at hmem
  have hzstd := lev_fpf_of_stdLine hodd hBnot hBpow hstd
  rw [preLine, hf.mem_pre,
    show f w = (h : Matrix (Fin 3) (Fin 3) K) *ᵥ y from (g_ginv_mulVec h (f w)).symm]
  exact mem_gmap.mpr (by rw [ginv_g_mulVec]; simpa [stdLine_eq_flagSpace] using hzstd)

private theorem exists_uSL_mem_of_ne {R : Subgroup ↥(stabE0 K)}
    (hRle : R ≤ (leviHom K).ker) (hRne : R ≠ ⊥) :
    ∃ (B : ↥(stabE0 K)) (a b : K), B ∈ R ∧ (a ≠ 0 ∨ b ≠ 0) ∧
      B = (⟨uSL a b 0, uSL_mem_stabE0 a b 0⟩ : ↥(stabE0 K)) := by
  obtain ⟨⟨B, hBR⟩, hBne'⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hRne
  have hBne : B ≠ 1 := fun h => hBne' (Subtype.ext h)
  have hBsl : (B : Matrix.SpecialLinearGroup (Fin 3) K) =
      uSL ((B : Matrix.SpecialLinearGroup (Fin 3) K) 0 1)
        ((B : Matrix.SpecialLinearGroup (Fin 3) K) 0 2) 0 :=
    eq_uSL_of_mem_ker (hRle hBR)
  have hab : (B : Matrix.SpecialLinearGroup (Fin 3) K) 0 1 ≠ 0 ∨
      (B : Matrix.SpecialLinearGroup (Fin 3) K) 0 2 ≠ 0 := by
    by_contra h
    push Not at h
    apply hBne
    apply Subtype.ext
    change (B : Matrix.SpecialLinearGroup (Fin 3) K) = 1
    rw [hBsl, h.1, h.2, uSL_zero]
  exact ⟨B, _, _, hBR, hab, Subtype.ext hBsl⟩

private theorem pointCore_R_eq_ker {R : Subgroup ↥(stabE0 K)}
    (hRle : R ≤ (leviHom K).ker)
    (hRnorm : ∀ C : ↥(stabE0 K), ∀ r ∈ R, C * r * C⁻¹ ∈ R)
    (hRne : R ≠ ⊥) : R = (leviHom K).ker := by
  apply le_antisymm hRle
  obtain ⟨B, a, b, hBR, hab, hBsub⟩ := exists_uSL_mem_of_ne hRle hRne
  have hB' : (⟨uSL a b 0, uSL_mem_stabE0 a b 0⟩ : ↥(stabE0 K)) ∈ R := by
    rwa [hBsub] at hBR
  intro C hCker
  have hCsl : (C : Matrix.SpecialLinearGroup (Fin 3) K) =
      uSL ((C : Matrix.SpecialLinearGroup (Fin 3) K) 0 1)
        ((C : Matrix.SpecialLinearGroup (Fin 3) K) 0 2) 0 := eq_uSL_of_mem_ker hCker
  let C' : ↥(stabE0 K) := ⟨uSL ((C : Matrix.SpecialLinearGroup (Fin 3) K) 0 1)
    ((C : Matrix.SpecialLinearGroup (Fin 3) K) 0 2) 0, uSL_mem_stabE0 _ _ _⟩
  have hC' : C' ∈ R := by
    by_cases hcd : (C : Matrix.SpecialLinearGroup (Fin 3) K) 0 1 = 0 ∧
        (C : Matrix.SpecialLinearGroup (Fin 3) K) 0 2 = 0
    · have hCone : C' = 1 := by
        apply Subtype.ext
        change uSL ((C : Matrix.SpecialLinearGroup (Fin 3) K) 0 1)
          ((C : Matrix.SpecialLinearGroup (Fin 3) K) 0 2) 0 = 1
        rw [hcd.1, hcd.2, uSL_zero]
      rw [hCone]
      exact R.one_mem
    · have hcd' : (C : Matrix.SpecialLinearGroup (Fin 3) K) 0 1 ≠ 0 ∨
          (C : Matrix.SpecialLinearGroup (Fin 3) K) 0 2 ≠ 0 := by
        by_contra h
        push Not at h
        exact hcd h
      exact uSL_mem_of_ne hRnorm hB' hab _ _ hcd'
  have hC'eq : C' = C := Subtype.ext hCsl.symm
  rwa [hC'eq] at hC'

private theorem pointCore_subgroupOf_eq_ker {W : Type} [CommGroup W]
    {H : Subgroup (MulAut W)} {Kstar' : Subgroup ↥H}
    (e : ↥(stabE0 K) ≃* ↥Kstar')
    (hUker : CFSG.Open.pCoreOf 2 Kstar' =
      ((leviHom K).ker.map e.toMonoidHom).map Kstar'.subtype) :
    (CFSG.Open.pCoreOf 2 Kstar').subgroupOf Kstar' =
      (leviHom K).ker.map e.toMonoidHom := by
  ext x
  constructor
  · intro hx
    have hx' : (x : ↥H) ∈ ((leviHom K).ker.map e.toMonoidHom).map Kstar'.subtype := by
      rwa [← hUker]
    obtain ⟨z, hz, hzx⟩ := Subgroup.mem_map.mp hx'
    rwa [show z = x from Subtype.ext hzx] at hz
  · intro hx
    have hx' : (x : ↥H) ∈ ((leviHom K).ker.map e.toMonoidHom).map Kstar'.subtype :=
      Subgroup.mem_map_of_mem Kstar'.subtype hx
    rwa [← hUker] at hx'

private theorem pointCore_irreducible_K {W : Type} [CommGroup W]
    {H : Subgroup (MulAut W)} {Kstar' : Subgroup ↥H} (e : ↥(stabE0 K) ≃* ↥Kstar')
    (hUker : CFSG.Open.pCoreOf 2 Kstar' =
      ((leviHom K).ker.map e.toMonoidHom).map Kstar'.subtype)
    {N : Subgroup ↥Kstar'}
    (hNle : N ≤ (CFSG.Open.pCoreOf 2 Kstar').subgroupOf Kstar')
    (hNne : N ≠ ⊥)
    (hNnorm : ∀ k : ↥Kstar', ∀ x ∈ N, k * x * k⁻¹ ∈ N) :
    N = (CFSG.Open.pCoreOf 2 Kstar').subgroupOf Kstar' := by
  have hker := pointCore_subgroupOf_eq_ker e hUker
  let R : Subgroup ↥(stabE0 K) := N.map e.symm.toMonoidHom
  have hRle : R ≤ (leviHom K).ker := by
    intro r hr
    obtain ⟨n, hn, rfl⟩ := Subgroup.mem_map.mp hr
    have hn' : n ∈ (CFSG.Open.pCoreOf 2 Kstar').subgroupOf Kstar' := hNle hn
    rw [hker] at hn'
    exact (Subgroup.mem_map_iff_mem (f := e.toMonoidHom) e.injective).mp (by simpa using hn')
  have hRnorm : ∀ C : ↥(stabE0 K), ∀ r ∈ R, C * r * C⁻¹ ∈ R := by
    intro C r hr
    obtain ⟨n, hn, rfl⟩ := Subgroup.mem_map.mp hr
    have hN : e C * n * (e C)⁻¹ ∈ N := by simpa using hNnorm (e C) n hn
    have hmap : e.symm.toMonoidHom (e C) * e.symm.toMonoidHom n *
        (e.symm.toMonoidHom (e C))⁻¹ ∈ R := by
      simpa only [map_mul, map_inv] using
        Subgroup.mem_map_of_mem e.symm.toMonoidHom hN
    simpa using hmap
  have hRne : R ≠ ⊥ := by
    intro hR
    apply hNne
    rw [eq_bot_iff]
    intro n hn
    have hmem : e.symm n ∈ R := Subgroup.mem_map_of_mem e.symm.toMonoidHom hn
    rw [hR] at hmem
    have h1 : e.symm n = 1 := Subgroup.mem_bot.mp hmem
    simpa using congrArg e h1
  have hRker : R = (leviHom K).ker := pointCore_R_eq_ker hRle hRnorm hRne
  have hRmap : R.map e.toMonoidHom = N := by
    change (N.map e.symm.toMonoidHom).map e.toMonoidHom = N
    rw [Subgroup.map_map]
    simp
  rw [hker, ← hRmap]
  exact congrArg (Subgroup.map e.toMonoidHom) hRker

private theorem pointCore_irreducible_H {W : Type} [CommGroup W] [Finite W]
    {H : Subgroup (MulAut W)}
    {Kstar' : Subgroup ↥H} (e : ↥(stabE0 K) ≃* ↥Kstar')
    {Kstar U : Subgroup ↥H} (hKstar : Kstar = Kstar')
    (hU : U = CFSG.Open.pCoreOf 2 Kstar')
    (hUker : U = ((leviHom K).ker.map e.toMonoidHom).map Kstar'.subtype)
    {N : Subgroup ↥H} (hNle : N ≤ U) (hNne : N ≠ ⊥)
    (hNnorm : ∀ k ∈ Kstar, ∀ x ∈ N, k * x * k⁻¹ ∈ N) : N = U := by
  have hUle : U ≤ Kstar' := by
    rw [hU]
    exact CFSG.LieType.BorelTits.pCoreOf_le 2 Kstar'
  have hUkerK : CFSG.Open.pCoreOf 2 Kstar' =
      ((leviHom K).ker.map e.toMonoidHom).map Kstar'.subtype := by
    rw [← hU, hUker]
  have hNK : N ≤ Kstar' := hNle.trans hUle
  let N' : Subgroup ↥Kstar' := N.subgroupOf Kstar'
  have hN'le : N' ≤ (CFSG.Open.pCoreOf 2 Kstar').subgroupOf Kstar' := by
    intro x hx
    have hxN : (x : ↥H) ∈ N := by rwa [Subgroup.mem_subgroupOf] at hx
    have hxU : (x : ↥H) ∈ U := hNle hxN
    rw [hUker] at hxU
    obtain ⟨z, hz, hzx⟩ := Subgroup.mem_map.mp hxU
    have hzx' : z = x := Subtype.ext hzx
    rw [hzx'] at hz
    have hxker : (x : ↥H) ∈ ((leviHom K).ker.map e.toMonoidHom).map Kstar'.subtype :=
      Subgroup.mem_map_of_mem Kstar'.subtype hz
    rwa [← hUkerK] at hxker
  have hN'ne : N' ≠ ⊥ := by
    intro hbot
    apply hNne
    have hmap : N'.map Kstar'.subtype = (⊥ : Subgroup ↥H) := by rw [hbot, Subgroup.map_bot]
    rwa [Subgroup.map_subgroupOf_eq_of_le hNK] at hmap
  have hN'norm : ∀ k : ↥Kstar', ∀ x ∈ N', k * x * k⁻¹ ∈ N' := by
    intro k x hx
    have hk : (k : ↥H) ∈ Kstar := by rw [hKstar]; exact k.2
    have hxN : (x : ↥H) ∈ N := by rwa [Subgroup.mem_subgroupOf] at hx
    rw [Subgroup.mem_subgroupOf]
    simpa using hNnorm (k : ↥H) hk (x : ↥H) hxN
  have hN'eq := pointCore_irreducible_K e hUkerK hN'le hN'ne hN'norm
  have hmap : N'.map Kstar'.subtype = N := Subgroup.map_subgroupOf_eq_of_le hNK
  rw [← hmap, hN'eq,
    Subgroup.map_subgroupOf_eq_of_le (CFSG.LieType.BorelTits.pCoreOf_le 2 Kstar')]
  exact hU.symm

theorem kSL3PointCore_holds :
    ∀ (W : Type) [CommGroup W] [Finite W] (H : Subgroup (MulAut W)) (n : ℕ),
      IsSLn ↥H 3 n → CFSG.Quasithin.BinaryNaturalSL H ⊤ ⊥ 3 n → 2 ≤ n →
        letI : MulDistribMulAction ↥H W := MulDistribMulAction.compHom W H.subtype
        letI : MulAction ↥H W := MulAction.compHom W H.subtype
        letI : MulAction ↥H (Set W) := Set.mulActionSet
        ∀ S : Sylow 2 ↥H,
          letI : MulDistribMulAction ↥S W :=
            MulDistribMulAction.compHom W (H.subtype.comp (S : Subgroup ↥H).subtype)
          let ℓ : Subgroup W := fixedPointSubgroup ↥S W
          let Kstar : Subgroup ↥H := Hinf (MulAction.stabilizer ↥H (ℓ : Set W))
          let U : Subgroup ↥H := CFSG.Open.pCoreOf 2 Kstar
          (∀ u ∈ U, ∀ w : W, w⁻¹ * (u • w) ∈ ℓ) ∧
          (∀ k ∈ Kstar, k ∉ U → ∀ r : ℕ, Odd r → k ^ r ∈ U →
            ∀ w : W, w⁻¹ * (k • w) ∈ ℓ → w ∈ ℓ) ∧
          (∀ N : Subgroup ↥H, N ≤ U → N ≠ ⊥ →
            (∀ k ∈ Kstar, ∀ x ∈ N, k * x * k⁻¹ ∈ N) → N = U) := by
  intro W _ _ H n hSLn hnat hn S ℓ Kstar U
  obtain ⟨K, hfield, hfinite, hK, ρ, hρ⟩ := hnat
  letI : Field K := hfield; letI : Finite K := hfinite
  letI : CharP K 2 := charP_two_of_card (by omega) hK
  haveI : Finite (MulAut W) := Finite.of_injective _ MulEquiv.toEquiv_injective
  have hSL := commutator_SL2_eq_top (four_le_card (by omega) hK)
  obtain ⟨f, hf⟩ := exists_isCoord (linModelNat (StatedSL 3 K)) hρ
  obtain ⟨h, hh⟩ := exists_sylow_eq_conj_Usl hK (by omega) hf
    (CFSG.Quasithin.A4.isSylowTwoOf_map H S)
  have hℓ : ℓ = preLine hf h := fixedPointSubgroup_eq_preLine hf hh
  let Kstar' : Subgroup ↥H := Hinf (MulAction.stabilizer ↥H
    ((preLine hf h : Subgroup W) : Set W))
  have hKstar : Kstar = Kstar' := by
    show Hinf (MulAction.stabilizer ↥H (ℓ : Set W)) = Kstar'
    rw [hℓ]
  obtain ⟨e, he⟩ := exists_pointCore_equiv hSL hf h
  have hUker : U = ((leviHom K).ker.map e.toMonoidHom).map Kstar'.subtype := by
    rw [show U = CFSG.Open.pCoreOf 2 Kstar from rfl, hKstar]
    exact pointCore_U_eq_ker hSL hf e he rfl
  have hU : U = CFSG.Open.pCoreOf 2 Kstar' := by
    rw [show U = CFSG.Open.pCoreOf 2 Kstar from rfl, hKstar]
  refine ⟨?_, ?_, ?_⟩
  · intro u hu w
    change w⁻¹ * ((u : MulAut W) w) ∈ ℓ
    rw [hℓ]
    exact pointCore_trivial_quotient hSL hf e he hUker hu w
  · intro k hk hknot r hodd hkpow w hw
    have hk' : k ∈ Kstar' := by rwa [← hKstar]
    change w ∈ ℓ
    rw [hℓ] at hw ⊢
    exact pointCore_fpf hSL hf e he hUker hodd hk' hknot hkpow hw
  · intro N hNle hNne hNnorm
    exact pointCore_irreducible_H e hKstar hU hUker hNle hNne hNnorm

end CFSG.LocalAnalysis.UniquenessCase.UC22

end
