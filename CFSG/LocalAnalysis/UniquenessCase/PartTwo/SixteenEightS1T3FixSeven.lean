module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightS1T3Set
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightS1T3ShapeId
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightS1T3FixSevenA
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightS1T3FixSevenB
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightS1T3FixSevenC
import CFSG.LocalAnalysis.RankThreeUC.AGL81U4FFTorusTrA
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightRowCtx

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open scoped Matrix

variable {W : Type} [CommGroup W] [Finite W] {A L T : Subgroup (MulAut W)}


theorem s16t3_exists_fix_seven_of_sum_nat (helem : ∀ w : W, w * w = 1) {n : ℕ}
    (hL : IsSLn ↥L n 1) (hn : n = 6 ∨ n = 7)
    (hsum : SumOfNat (fun H U Z => BinaryNaturalSL H U Z n 1) L ⊤ (fixV L) 3) :
    ∀ x : W, x ≠ 1 → ∃ y ∈ L, orderOf y = 7 ∧ y x = x := by
  classical
  intro x hx1
  obtain ⟨I, hZI, -, hsup, hnat⟩ := hsum
  have hnf := fun i => s16t3_natural_normal_form (hnat i)
  choose π β hπinj hπsurj hβsurj hβker hβact using
    fun i => (hnf i).2.2.2
  have hn3 : 3 ≤ n := by rcases hn with rfl | rfl <;> norm_num
  obtain ⟨A1, hA1⟩ := s16t3_twist_of_isomorphisms (n := n) hn3
    (π₁ := π 0) (π₂ := π 1) (hπinj 0) (hπsurj 0) (hπinj 1) (hπsurj 1)
  obtain ⟨A2, hA2⟩ := s16t3_twist_of_isomorphisms (n := n) hn3
    (π₁ := π 0) (π₂ := π 2) (hπinj 0) (hπsurj 0) (hπinj 2) (hπsurj 2)
  let InnerRel : Matrix.GeneralLinearGroup (Fin n) (ZMod 2) → Fin 3 → Prop :=
    fun A i => ∀ s : Matrix.SpecialLinearGroup (Fin n) (ZMod 2),
      ∃ t : Matrix.SpecialLinearGroup (Fin n) (ZMod 2), π i t = π 0 s ∧
        (t : Matrix (Fin n) (Fin n) (ZMod 2)) =
          (A : Matrix (Fin n) (Fin n) (ZMod 2)) *
            (s : Matrix (Fin n) (Fin n) (ZMod 2)) *
              ((A⁻¹ : Matrix.GeneralLinearGroup (Fin n) (ZMod 2)) :
                Matrix (Fin n) (Fin n) (ZMod 2))
  let TwistRel : Matrix.GeneralLinearGroup (Fin n) (ZMod 2) → Fin 3 → Prop :=
    fun A i => ∀ s : Matrix.SpecialLinearGroup (Fin n) (ZMod 2),
      ∃ t : Matrix.SpecialLinearGroup (Fin n) (ZMod 2), π i t = π 0 s ∧
        (t : Matrix (Fin n) (Fin n) (ZMod 2)) =
          (A : Matrix (Fin n) (Fin n) (ZMod 2)) *
            ((s⁻¹ : Matrix.SpecialLinearGroup (Fin n) (ZMod 2)) :
              Matrix (Fin n) (Fin n) (ZMod 2)).transpose *
              ((A⁻¹ : Matrix.GeneralLinearGroup (Fin n) (ZMod 2)) :
                Matrix (Fin n) (Fin n) (ZMod 2))
  let Ag : Fin 3 → Matrix.GeneralLinearGroup (Fin n) (ZMod 2) :=
    fun i => if i = 0 then 1 else if i = 1 then A1 else A2
  let inner : Fin 3 → Prop :=
    fun i => if i = 0 then True else if i = 1 then InnerRel A1 1 else InnerRel A2 2
  have hArel : ∀ i, inner i → InnerRel (Ag i) i := by
    intro i hi
    fin_cases i
    · intro s
      exact ⟨s, rfl, by simp [Ag]⟩
    · simpa [Ag, inner] using hi
    · simpa [Ag, inner] using hi
  have hTwistRel : ∀ i, ¬ inner i → TwistRel (Ag i) i := by
    intro i hni
    fin_cases i
    · exact absurd trivial hni
    · have hni1 : ¬ InnerRel A1 1 := by simpa [inner] using hni
      have h := hA1.resolve_left hni1
      simpa [TwistRel, Ag] using h
    · have hni2 : ¬ InnerRel A2 2 := by simpa [inner] using hni
      have h := hA2.resolve_left hni2
      simpa [TwistRel, Ag] using h
  have hxmem : x ∈ fixV L ⊔ ⨆ i, I i := by
    rw [hsup]
    exact Subgroup.mem_top x
  rw [Subgroup.mem_sup] at hxmem
  obtain ⟨z, hz, p, hp_mem, hxdec0⟩ := hxmem
  obtain ⟨xcomp, hxcomp, hxprod⟩ :=
    CFSG.LocalAnalysis.RankThreeUC.exists_prod_of_mem_iSup I hp_mem
  rw [Fin.prod_univ_three] at hxprod
  let x0 : W := xcomp 0
  let x1 : W := xcomp 1
  let x2 : W := xcomp 2
  have hx0 : x0 ∈ I 0 := hxcomp 0
  have hx1 : x1 ∈ I 1 := hxcomp 1
  have hx2 : x2 ∈ I 2 := hxcomp 2
  have hxdec : x = z * (x0 * x1 * x2) := by
    rw [← hxprod] at hxdec0
    simpa [x0, x1, x2] using hxdec0.symm
  let xf : Fin 3 → W := xcomp
  have hxf : ∀ i, xf i ∈ I i := hxcomp
  let bvec : Fin 3 → (Fin n → ZMod 2) :=
    fun i => Multiplicative.toAdd (β i ⟨xf i, hxf i⟩)
  let v : {i : Fin 3 // inner i} → Fin n → ZMod 2 := fun j =>
    (((Ag j.1)⁻¹ : Matrix.GeneralLinearGroup (Fin n) (ZMod 2)) :
      Matrix (Fin n) (Fin n) (ZMod 2)) *ᵥ bvec j.1
  let f : {i : Fin 3 // ¬ inner i} → Fin n → ZMod 2 := fun j =>
    (((Ag j.1)⁻¹ : Matrix.GeneralLinearGroup (Fin n) (ZMod 2)) :
      Matrix (Fin n) (Fin n) (ZMod 2)) *ᵥ bvec j.1
  have hcard : Fintype.card {i : Fin 3 // inner i} +
      Fintype.card {i : Fin 3 // ¬ inner i} ≤ 3 := by
    have h1 : Fintype.card {i : Fin 3 // inner i} ≤ 3 := by
      simpa using Fintype.card_subtype_le (fun i : Fin 3 => inner i)
    have h2 := Fintype.card_subtype_compl (p := fun i : Fin 3 => inner i)
    have h3 : Fintype.card (Fin 3) = 3 := by simp
    omega
  obtain ⟨glin, hglin7, hglv, hglf⟩ := s16t3_model_exists_fix_seven hn v f hcard
  obtain ⟨gs, hgsorder, hgsmul⟩ := s16t3_sl_of_linearEquiv glin
  have hgs7 : orderOf gs = 7 := hgsorder.trans hglin7
  let y : MulAut W := ((π 0 gs : ↥L) : MulAut W)
  have hyL : y ∈ L := (π 0 gs).2
  have horder_y : orderOf y = 7 := by
    change orderOf (((π 0 gs : ↥L) : MulAut W)) = 7
    rw [Subgroup.orderOf_coe]
    exact (orderOf_injective (π 0) (hπinj 0) gs).trans hgs7
  have hy7 : y ^ 7 = 1 := by
    rw [← horder_y]
    exact pow_orderOf_eq_one y
  have hBfix : ∀ i, β i ⟨y (xf i), (s16t3_natural_normal_form (hnat i)).2.1
      (π 0 gs) (xf i) (hxf i)⟩ = β i ⟨xf i, hxf i⟩ := by
    intro i
    fin_cases i
    · have himg : y (xf 0) ∈ I 0 := (hnf 0).2.1 (π 0 gs) (xf 0) (hxf 0)
      have hact := hβact 0 gs ⟨xf 0, hxf 0⟩ himg
      have hv0 : glin (Multiplicative.toAdd (β 0 ⟨xf 0, hxf 0⟩)) =
          Multiplicative.toAdd (β 0 ⟨xf 0, hxf 0⟩) := by
        have := hglv ⟨0, by simp [inner]⟩
        simpa [v, bvec, Ag] using this
      rw [hgsmul, hv0] at hact
      exact hact
    · by_cases hi : inner 1
      · obtain ⟨t, hπt, htmat⟩ := hArel 1 hi gs
        have hπtcoe : ((π 1 t : ↥L) : MulAut W) = y := by
          simpa [y] using congrArg (fun u : ↥L => (u : MulAut W)) hπt
        have himg : y (xf 1) ∈ I 1 := (hnf 1).2.1 (π 0 gs) (xf 1) (hxf 1)
        have himg' : ((π 1 t : ↥L) : MulAut W) (xf 1) ∈ I 1 := by
          rw [hπtcoe]
          exact himg
        have hact := hβact 1 t ⟨xf 1, hxf 1⟩ himg'
        have hv1 : glin ((((Ag 1)⁻¹ : Matrix.GeneralLinearGroup (Fin n) (ZMod 2)) :
            Matrix (Fin n) (Fin n) (ZMod 2)) *ᵥ bvec 1) =
            (((Ag 1)⁻¹ : Matrix.GeneralLinearGroup (Fin n) (ZMod 2)) :
              Matrix (Fin n) (Fin n) (ZMod 2)) *ᵥ bvec 1 := by
          simpa [v, bvec] using hglv ⟨1, hi⟩
        have htfix : ((t : Matrix (Fin n) (Fin n) (ZMod 2))) *ᵥ bvec 1 = bvec 1 := by
          have hAA : (Ag 1 : Matrix (Fin n) (Fin n) (ZMod 2)) *
              (((Ag 1)⁻¹ : Matrix.GeneralLinearGroup (Fin n) (ZMod 2)) :
                Matrix (Fin n) (Fin n) (ZMod 2)) = 1 := by
            have h : ((Ag 1 * (Ag 1)⁻¹ : Matrix.GeneralLinearGroup (Fin n) (ZMod 2)) :
                Matrix (Fin n) (Fin n) (ZMod 2)) = 1 := by simp
            simpa using h
          calc ((t : Matrix (Fin n) (Fin n) (ZMod 2))) *ᵥ bvec 1
              = (Ag 1 : Matrix (Fin n) (Fin n) (ZMod 2)) *ᵥ
                  ((gs : Matrix (Fin n) (Fin n) (ZMod 2)) *ᵥ
                    ((((Ag 1)⁻¹ : Matrix.GeneralLinearGroup (Fin n) (ZMod 2)) :
                      Matrix (Fin n) (Fin n) (ZMod 2)) *ᵥ bvec 1)) := by
                rw [htmat, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
            _ = (Ag 1 : Matrix (Fin n) (Fin n) (ZMod 2)) *ᵥ
                  (glin ((((Ag 1)⁻¹ : Matrix.GeneralLinearGroup (Fin n) (ZMod 2)) :
                    Matrix (Fin n) (Fin n) (ZMod 2)) *ᵥ bvec 1)) := by
                rw [hgsmul]
            _ = (Ag 1 : Matrix (Fin n) (Fin n) (ZMod 2)) *ᵥ
                  ((((Ag 1)⁻¹ : Matrix.GeneralLinearGroup (Fin n) (ZMod 2)) :
                    Matrix (Fin n) (Fin n) (ZMod 2)) *ᵥ bvec 1) := by
                rw [hv1]
            _ = bvec 1 := by
                rw [Matrix.mulVec_mulVec, hAA, Matrix.one_mulVec]
        have hproof : (⟨y (xf 1), himg⟩ : ↥(I 1)) =
            ⟨((π 1 t : ↥L) : MulAut W) (xf 1), himg'⟩ := by
          apply Subtype.ext
          exact (congrArg (fun u : MulAut W => u (xf 1)) hπtcoe).symm
        calc β 1 ⟨y (xf 1), himg⟩
            = β 1 ⟨((π 1 t : ↥L) : MulAut W) (xf 1), himg'⟩ := by rw [hproof]
          _ = Multiplicative.ofAdd ((t : Matrix (Fin n) (Fin n) (ZMod 2)) *ᵥ
                Multiplicative.toAdd (β 1 ⟨xf 1, hxf 1⟩)) := hact
          _ = Multiplicative.ofAdd (bvec 1) := by rw [htfix]
          _ = β 1 ⟨xf 1, hxf 1⟩ := rfl
      · obtain ⟨t, hπt, htmat⟩ := hTwistRel 1 hi gs
        have hπtcoe : ((π 1 t : ↥L) : MulAut W) = y := by
          simpa [y] using congrArg (fun u : ↥L => (u : MulAut W)) hπt
        have himg : y (xf 1) ∈ I 1 := (hnf 1).2.1 (π 0 gs) (xf 1) (hxf 1)
        have himg' : ((π 1 t : ↥L) : MulAut W) (xf 1) ∈ I 1 := by
          rw [hπtcoe]
          exact himg
        have hact := hβact 1 t ⟨xf 1, hxf 1⟩ himg'
        have hrow : ((((Ag 1)⁻¹ : Matrix.GeneralLinearGroup (Fin n) (ZMod 2)) :
            Matrix (Fin n) (Fin n) (ZMod 2)) *ᵥ bvec 1) ᵥ*
              (gs : Matrix (Fin n) (Fin n) (ZMod 2)) =
            (((Ag 1)⁻¹ : Matrix.GeneralLinearGroup (Fin n) (ZMod 2)) :
              Matrix (Fin n) (Fin n) (ZMod 2)) *ᵥ bvec 1 := by
          funext a
          rw [Matrix.vecMul_apply, ← Matrix.mulVec_single_one
            (gs : Matrix (Fin n) (Fin n) (ZMod 2)) a, hgsmul]
          simpa [f, bvec] using hglf ⟨1, hi⟩ (Pi.single a 1)
        have hgTw : ((gs : Matrix (Fin n) (Fin n) (ZMod 2))).transpose *ᵥ
            ((((Ag 1)⁻¹ : Matrix.GeneralLinearGroup (Fin n) (ZMod 2)) :
              Matrix (Fin n) (Fin n) (ZMod 2)) *ᵥ bvec 1) =
            (((Ag 1)⁻¹ : Matrix.GeneralLinearGroup (Fin n) (ZMod 2)) :
              Matrix (Fin n) (Fin n) (ZMod 2)) *ᵥ bvec 1 := by
          rw [Matrix.mulVec_transpose]
          exact hrow
        have hginvT : ((((gs⁻¹ : Matrix.SpecialLinearGroup (Fin n) (ZMod 2)) :
            Matrix (Fin n) (Fin n) (ZMod 2))).transpose) *ᵥ
            ((((Ag 1)⁻¹ : Matrix.GeneralLinearGroup (Fin n) (ZMod 2)) :
              Matrix (Fin n) (Fin n) (ZMod 2)) *ᵥ bvec 1) =
            ((((Ag 1)⁻¹ : Matrix.GeneralLinearGroup (Fin n) (ZMod 2)) :
              Matrix (Fin n) (Fin n) (ZMod 2)) *ᵥ bvec 1) := by
          have hmul : ((((gs⁻¹ : Matrix.SpecialLinearGroup (Fin n) (ZMod 2)) :
              Matrix (Fin n) (Fin n) (ZMod 2))).transpose *
              ((gs : Matrix (Fin n) (Fin n) (ZMod 2))).transpose) = 1 := by
            rw [← Matrix.transpose_mul]
            have h2 : (((gs * gs⁻¹ : Matrix.SpecialLinearGroup (Fin n) (ZMod 2)) :
                Matrix (Fin n) (Fin n) (ZMod 2))) = 1 := by
              rw [mul_inv_cancel gs, Matrix.SpecialLinearGroup.coe_one]
            have h : (gs : Matrix (Fin n) (Fin n) (ZMod 2)) *
                (((gs⁻¹ : Matrix.SpecialLinearGroup (Fin n) (ZMod 2)) :
                  Matrix (Fin n) (Fin n) (ZMod 2))) = 1 := by
              rw [← Matrix.SpecialLinearGroup.coe_mul]
              exact h2
            rw [h, Matrix.transpose_one]
          calc ((((gs⁻¹ : Matrix.SpecialLinearGroup (Fin n) (ZMod 2)) :
                Matrix (Fin n) (Fin n) (ZMod 2))).transpose) *ᵥ
                ((((Ag 1)⁻¹ : Matrix.GeneralLinearGroup (Fin n) (ZMod 2)) :
                  Matrix (Fin n) (Fin n) (ZMod 2)) *ᵥ bvec 1)
              = ((((gs⁻¹ : Matrix.SpecialLinearGroup (Fin n) (ZMod 2)) :
                  Matrix (Fin n) (Fin n) (ZMod 2))).transpose) *ᵥ
                  (((gs : Matrix (Fin n) (Fin n) (ZMod 2))).transpose *ᵥ
                    ((((Ag 1)⁻¹ : Matrix.GeneralLinearGroup (Fin n) (ZMod 2)) :
                      Matrix (Fin n) (Fin n) (ZMod 2)) *ᵥ bvec 1)) := by
                  rw [hgTw]
            _ = (((((gs⁻¹ : Matrix.SpecialLinearGroup (Fin n) (ZMod 2)) :
                  Matrix (Fin n) (Fin n) (ZMod 2))).transpose) *
                  ((gs : Matrix (Fin n) (Fin n) (ZMod 2))).transpose) *ᵥ
                  ((((Ag 1)⁻¹ : Matrix.GeneralLinearGroup (Fin n) (ZMod 2)) :
                    Matrix (Fin n) (Fin n) (ZMod 2)) *ᵥ bvec 1) := by
                  rw [Matrix.mulVec_mulVec]
            _ = ((((Ag 1)⁻¹ : Matrix.GeneralLinearGroup (Fin n) (ZMod 2)) :
                  Matrix (Fin n) (Fin n) (ZMod 2)) *ᵥ bvec 1) := by
                  rw [hmul, Matrix.one_mulVec]
        have htfix : ((t : Matrix (Fin n) (Fin n) (ZMod 2))) *ᵥ bvec 1 = bvec 1 := by
          have hAA : (Ag 1 : Matrix (Fin n) (Fin n) (ZMod 2)) *
              (((Ag 1)⁻¹ : Matrix.GeneralLinearGroup (Fin n) (ZMod 2)) :
                Matrix (Fin n) (Fin n) (ZMod 2)) = 1 := by
            have h : ((Ag 1 * (Ag 1)⁻¹ : Matrix.GeneralLinearGroup (Fin n) (ZMod 2)) :
                Matrix (Fin n) (Fin n) (ZMod 2)) = 1 := by simp
            simpa using h
          calc ((t : Matrix (Fin n) (Fin n) (ZMod 2))) *ᵥ bvec 1
              = (Ag 1 : Matrix (Fin n) (Fin n) (ZMod 2)) *ᵥ
                  ((((gs⁻¹ : Matrix.SpecialLinearGroup (Fin n) (ZMod 2)) :
                    Matrix (Fin n) (Fin n) (ZMod 2))).transpose *ᵥ
                    ((((Ag 1)⁻¹ : Matrix.GeneralLinearGroup (Fin n) (ZMod 2)) :
                      Matrix (Fin n) (Fin n) (ZMod 2)) *ᵥ bvec 1)) := by
                rw [htmat, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
            _ = (Ag 1 : Matrix (Fin n) (Fin n) (ZMod 2)) *ᵥ
                  ((((Ag 1)⁻¹ : Matrix.GeneralLinearGroup (Fin n) (ZMod 2)) :
                    Matrix (Fin n) (Fin n) (ZMod 2)) *ᵥ bvec 1) := by
                rw [hginvT]
            _ = bvec 1 := by
                rw [Matrix.mulVec_mulVec, hAA, Matrix.one_mulVec]
        have hproof : (⟨y (xf 1), himg⟩ : ↥(I 1)) =
            ⟨((π 1 t : ↥L) : MulAut W) (xf 1), himg'⟩ := by
          apply Subtype.ext
          exact (congrArg (fun u : MulAut W => u (xf 1)) hπtcoe).symm
        calc β 1 ⟨y (xf 1), himg⟩
            = β 1 ⟨((π 1 t : ↥L) : MulAut W) (xf 1), himg'⟩ := by rw [hproof]
          _ = Multiplicative.ofAdd ((t : Matrix (Fin n) (Fin n) (ZMod 2)) *ᵥ
                Multiplicative.toAdd (β 1 ⟨xf 1, hxf 1⟩)) := hact
          _ = Multiplicative.ofAdd (bvec 1) := by rw [htfix]
          _ = β 1 ⟨xf 1, hxf 1⟩ := rfl
    · by_cases hi : inner 2
      · obtain ⟨t, hπt, htmat⟩ := hArel 2 hi gs
        have hπtcoe : ((π 2 t : ↥L) : MulAut W) = y := by
          simpa [y] using congrArg (fun u : ↥L => (u : MulAut W)) hπt
        have himg : y (xf 2) ∈ I 2 := (hnf 2).2.1 (π 0 gs) (xf 2) (hxf 2)
        have himg' : ((π 2 t : ↥L) : MulAut W) (xf 2) ∈ I 2 := by
          rw [hπtcoe]
          exact himg
        have hact := hβact 2 t ⟨xf 2, hxf 2⟩ himg'
        have hv2 : glin ((((Ag 2)⁻¹ : Matrix.GeneralLinearGroup (Fin n) (ZMod 2)) :
            Matrix (Fin n) (Fin n) (ZMod 2)) *ᵥ bvec 2) =
            (((Ag 2)⁻¹ : Matrix.GeneralLinearGroup (Fin n) (ZMod 2)) :
              Matrix (Fin n) (Fin n) (ZMod 2)) *ᵥ bvec 2 := by
          simpa [v, bvec] using hglv ⟨2, hi⟩
        have htfix : ((t : Matrix (Fin n) (Fin n) (ZMod 2))) *ᵥ bvec 2 = bvec 2 := by
          have hAA : (Ag 2 : Matrix (Fin n) (Fin n) (ZMod 2)) *
              (((Ag 2)⁻¹ : Matrix.GeneralLinearGroup (Fin n) (ZMod 2)) :
                Matrix (Fin n) (Fin n) (ZMod 2)) = 1 := by
            have h : ((Ag 2 * (Ag 2)⁻¹ : Matrix.GeneralLinearGroup (Fin n) (ZMod 2)) :
                Matrix (Fin n) (Fin n) (ZMod 2)) = 1 := by simp
            simpa using h
          calc ((t : Matrix (Fin n) (Fin n) (ZMod 2))) *ᵥ bvec 2
              = (Ag 2 : Matrix (Fin n) (Fin n) (ZMod 2)) *ᵥ
                  ((gs : Matrix (Fin n) (Fin n) (ZMod 2)) *ᵥ
                    ((((Ag 2)⁻¹ : Matrix.GeneralLinearGroup (Fin n) (ZMod 2)) :
                      Matrix (Fin n) (Fin n) (ZMod 2)) *ᵥ bvec 2)) := by
                rw [htmat, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
            _ = (Ag 2 : Matrix (Fin n) (Fin n) (ZMod 2)) *ᵥ
                  (glin ((((Ag 2)⁻¹ : Matrix.GeneralLinearGroup (Fin n) (ZMod 2)) :
                    Matrix (Fin n) (Fin n) (ZMod 2)) *ᵥ bvec 2)) := by
                rw [hgsmul]
            _ = (Ag 2 : Matrix (Fin n) (Fin n) (ZMod 2)) *ᵥ
                  ((((Ag 2)⁻¹ : Matrix.GeneralLinearGroup (Fin n) (ZMod 2)) :
                    Matrix (Fin n) (Fin n) (ZMod 2)) *ᵥ bvec 2) := by
                rw [hv2]
            _ = bvec 2 := by
                rw [Matrix.mulVec_mulVec, hAA, Matrix.one_mulVec]
        have hproof : (⟨y (xf 2), himg⟩ : ↥(I 2)) =
            ⟨((π 2 t : ↥L) : MulAut W) (xf 2), himg'⟩ := by
          apply Subtype.ext
          exact (congrArg (fun u : MulAut W => u (xf 2)) hπtcoe).symm
        calc β 2 ⟨y (xf 2), himg⟩
            = β 2 ⟨((π 2 t : ↥L) : MulAut W) (xf 2), himg'⟩ := by rw [hproof]
          _ = Multiplicative.ofAdd ((t : Matrix (Fin n) (Fin n) (ZMod 2)) *ᵥ
                Multiplicative.toAdd (β 2 ⟨xf 2, hxf 2⟩)) := hact
          _ = Multiplicative.ofAdd (bvec 2) := by rw [htfix]
          _ = β 2 ⟨xf 2, hxf 2⟩ := rfl
      · obtain ⟨t, hπt, htmat⟩ := hTwistRel 2 hi gs
        have hπtcoe : ((π 2 t : ↥L) : MulAut W) = y := by
          simpa [y] using congrArg (fun u : ↥L => (u : MulAut W)) hπt
        have himg : y (xf 2) ∈ I 2 := (hnf 2).2.1 (π 0 gs) (xf 2) (hxf 2)
        have himg' : ((π 2 t : ↥L) : MulAut W) (xf 2) ∈ I 2 := by
          rw [hπtcoe]
          exact himg
        have hact := hβact 2 t ⟨xf 2, hxf 2⟩ himg'
        have hrow : ((((Ag 2)⁻¹ : Matrix.GeneralLinearGroup (Fin n) (ZMod 2)) :
            Matrix (Fin n) (Fin n) (ZMod 2)) *ᵥ bvec 2) ᵥ*
              (gs : Matrix (Fin n) (Fin n) (ZMod 2)) =
            (((Ag 2)⁻¹ : Matrix.GeneralLinearGroup (Fin n) (ZMod 2)) :
              Matrix (Fin n) (Fin n) (ZMod 2)) *ᵥ bvec 2 := by
          funext a
          rw [Matrix.vecMul_apply, ← Matrix.mulVec_single_one
            (gs : Matrix (Fin n) (Fin n) (ZMod 2)) a, hgsmul]
          simpa [f, bvec] using hglf ⟨2, hi⟩ (Pi.single a 1)
        have hgTw : ((gs : Matrix (Fin n) (Fin n) (ZMod 2))).transpose *ᵥ
            ((((Ag 2)⁻¹ : Matrix.GeneralLinearGroup (Fin n) (ZMod 2)) :
              Matrix (Fin n) (Fin n) (ZMod 2)) *ᵥ bvec 2) =
            (((Ag 2)⁻¹ : Matrix.GeneralLinearGroup (Fin n) (ZMod 2)) :
              Matrix (Fin n) (Fin n) (ZMod 2)) *ᵥ bvec 2 := by
          rw [Matrix.mulVec_transpose]
          exact hrow
        have hginvT : ((((gs⁻¹ : Matrix.SpecialLinearGroup (Fin n) (ZMod 2)) :
            Matrix (Fin n) (Fin n) (ZMod 2))).transpose) *ᵥ
            ((((Ag 2)⁻¹ : Matrix.GeneralLinearGroup (Fin n) (ZMod 2)) :
              Matrix (Fin n) (Fin n) (ZMod 2)) *ᵥ bvec 2) =
            ((((Ag 2)⁻¹ : Matrix.GeneralLinearGroup (Fin n) (ZMod 2)) :
              Matrix (Fin n) (Fin n) (ZMod 2)) *ᵥ bvec 2) := by
          have hmul : ((((gs⁻¹ : Matrix.SpecialLinearGroup (Fin n) (ZMod 2)) :
              Matrix (Fin n) (Fin n) (ZMod 2))).transpose *
              ((gs : Matrix (Fin n) (Fin n) (ZMod 2))).transpose) = 1 := by
            rw [← Matrix.transpose_mul]
            have h2 : (((gs * gs⁻¹ : Matrix.SpecialLinearGroup (Fin n) (ZMod 2)) :
                Matrix (Fin n) (Fin n) (ZMod 2))) = 1 := by
              rw [mul_inv_cancel gs, Matrix.SpecialLinearGroup.coe_one]
            have h : (gs : Matrix (Fin n) (Fin n) (ZMod 2)) *
                (((gs⁻¹ : Matrix.SpecialLinearGroup (Fin n) (ZMod 2)) :
                  Matrix (Fin n) (Fin n) (ZMod 2))) = 1 := by
              rw [← Matrix.SpecialLinearGroup.coe_mul]
              exact h2
            rw [h, Matrix.transpose_one]
          calc ((((gs⁻¹ : Matrix.SpecialLinearGroup (Fin n) (ZMod 2)) :
                Matrix (Fin n) (Fin n) (ZMod 2))).transpose) *ᵥ
                ((((Ag 2)⁻¹ : Matrix.GeneralLinearGroup (Fin n) (ZMod 2)) :
                  Matrix (Fin n) (Fin n) (ZMod 2)) *ᵥ bvec 2)
              = ((((gs⁻¹ : Matrix.SpecialLinearGroup (Fin n) (ZMod 2)) :
                  Matrix (Fin n) (Fin n) (ZMod 2))).transpose) *ᵥ
                  (((gs : Matrix (Fin n) (Fin n) (ZMod 2))).transpose *ᵥ
                    ((((Ag 2)⁻¹ : Matrix.GeneralLinearGroup (Fin n) (ZMod 2)) :
                      Matrix (Fin n) (Fin n) (ZMod 2)) *ᵥ bvec 2)) := by
                  rw [hgTw]
            _ = (((((gs⁻¹ : Matrix.SpecialLinearGroup (Fin n) (ZMod 2)) :
                  Matrix (Fin n) (Fin n) (ZMod 2))).transpose) *
                  ((gs : Matrix (Fin n) (Fin n) (ZMod 2))).transpose) *ᵥ
                  ((((Ag 2)⁻¹ : Matrix.GeneralLinearGroup (Fin n) (ZMod 2)) :
                    Matrix (Fin n) (Fin n) (ZMod 2)) *ᵥ bvec 2) := by
                  rw [Matrix.mulVec_mulVec]
            _ = ((((Ag 2)⁻¹ : Matrix.GeneralLinearGroup (Fin n) (ZMod 2)) :
                  Matrix (Fin n) (Fin n) (ZMod 2)) *ᵥ bvec 2) := by
                  rw [hmul, Matrix.one_mulVec]
        have htfix : ((t : Matrix (Fin n) (Fin n) (ZMod 2))) *ᵥ bvec 2 = bvec 2 := by
          have hAA : (Ag 2 : Matrix (Fin n) (Fin n) (ZMod 2)) *
              (((Ag 2)⁻¹ : Matrix.GeneralLinearGroup (Fin n) (ZMod 2)) :
                Matrix (Fin n) (Fin n) (ZMod 2)) = 1 := by
            have h : ((Ag 2 * (Ag 2)⁻¹ : Matrix.GeneralLinearGroup (Fin n) (ZMod 2)) :
                Matrix (Fin n) (Fin n) (ZMod 2)) = 1 := by simp
            simpa using h
          calc ((t : Matrix (Fin n) (Fin n) (ZMod 2))) *ᵥ bvec 2
              = (Ag 2 : Matrix (Fin n) (Fin n) (ZMod 2)) *ᵥ
                  ((((gs⁻¹ : Matrix.SpecialLinearGroup (Fin n) (ZMod 2)) :
                    Matrix (Fin n) (Fin n) (ZMod 2))).transpose *ᵥ
                    ((((Ag 2)⁻¹ : Matrix.GeneralLinearGroup (Fin n) (ZMod 2)) :
                      Matrix (Fin n) (Fin n) (ZMod 2)) *ᵥ bvec 2)) := by
                rw [htmat, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
            _ = (Ag 2 : Matrix (Fin n) (Fin n) (ZMod 2)) *ᵥ
                  ((((Ag 2)⁻¹ : Matrix.GeneralLinearGroup (Fin n) (ZMod 2)) :
                    Matrix (Fin n) (Fin n) (ZMod 2)) *ᵥ bvec 2) := by
                rw [hginvT]
            _ = bvec 2 := by
                rw [Matrix.mulVec_mulVec, hAA, Matrix.one_mulVec]
        have hproof : (⟨y (xf 2), himg⟩ : ↥(I 2)) =
            ⟨((π 2 t : ↥L) : MulAut W) (xf 2), himg'⟩ := by
          apply Subtype.ext
          exact (congrArg (fun u : MulAut W => u (xf 2)) hπtcoe).symm
        calc β 2 ⟨y (xf 2), himg⟩
            = β 2 ⟨((π 2 t : ↥L) : MulAut W) (xf 2), himg'⟩ := by rw [hproof]
          _ = Multiplicative.ofAdd ((t : Matrix (Fin n) (Fin n) (ZMod 2)) *ᵥ
                Multiplicative.toAdd (β 2 ⟨xf 2, hxf 2⟩)) := hact
          _ = Multiplicative.ofAdd (bvec 2) := by rw [htfix]
          _ = β 2 ⟨xf 2, hxf 2⟩ := rfl
  have hfix_i : ∀ i, y (xf i) * (xf i)⁻¹ ∈ fixV L := by
    intro i
    have himg : y (xf i) ∈ I i := (hnf i).2.1 (π 0 gs) (xf i) (hxf i)
    have hmem : y (xf i) * (xf i)⁻¹ ∈ I i :=
      (I i).mul_mem himg ((I i).inv_mem (hxf i))
    have hprod : (⟨y (xf i) * (xf i)⁻¹, hmem⟩ : ↥(I i)) =
        ⟨y (xf i), himg⟩ * (⟨xf i, hxf i⟩ : ↥(I i))⁻¹ := by
      ext
      simp
    have hβu : β i ⟨y (xf i) * (xf i)⁻¹, hmem⟩ = 1 := by
      rw [hprod, map_mul, map_inv, hBfix i, mul_inv_cancel]
    exact (hβker i ⟨y (xf i) * (xf i)⁻¹, hmem⟩).1 hβu
  have hyz : y z = z := (mem_fixV.1 hz) (y : MulAut W) hyL
  have hzpart : y z * z⁻¹ ∈ fixV L := by
    rw [hyz, mul_inv_cancel]
    exact (fixV L).one_mem
  have hp : y (x0 * x1 * x2) * (x0 * x1 * x2)⁻¹ ∈ fixV L := by
    have h := (fixV L).mul_mem ((fixV L).mul_mem (hfix_i 0) (hfix_i 1)) (hfix_i 2)
    convert h using 1
    simp [xf, x0, x1, x2, map_mul, map_inv]
    ac_rfl
  have hfull : y x * x⁻¹ ∈ fixV L := by
    have hprod : y x * x⁻¹ = (y z * z⁻¹) * (y (x0 * x1 * x2) * (x0 * x1 * x2)⁻¹) := by
      rw [hxdec, map_mul, mul_inv_rev]
      ac_rfl
    rw [hprod]
    exact (fixV L).mul_mem hzpart hp
  have hW2 : ∀ w : W, w ^ 2 = 1 := fun w => by rw [pow_two]; exact helem w
  have hfix : y x = x := s16g_apply_eq_of_odd hW2 (by norm_num : Odd 7) hy7
    (fun w hw => (mem_fixV.1 hw) (y : MulAut W) hyL) hfull
  exact ⟨y, hyL, horder_y, hfix⟩

theorem ThreeNat.exists_fix_seven_sl (h : ThreeNat A L T)
    (hL : IsSLn ↥L 6 1 ∨ IsSLn ↥L 7 1) :
    ∀ x : W, x ≠ 1 → ∃ y ∈ L, orderOf y = 7 ∧ y x = x := by
  rcases hL with hL | hL
  · exact s16t3_exists_fix_seven_of_sum_nat h.elem hL (Or.inl rfl)
      (s16t3_shape_branch_sl h.sum (Or.inl rfl) hL)
  · exact s16t3_exists_fix_seven_of_sum_nat h.elem hL (Or.inr rfl)
      (s16t3_shape_branch_sl h.sum (Or.inr rfl) hL)

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
