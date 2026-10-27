module

public import CFSG.LocalAnalysis.StandardType.GGLangRatLift
import CFSG.HardMathSupport.Timmesfeld.LangTorus.BigAnyTorus
import Mathlib.LinearAlgebra.FreeModule.PID
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
import Mathlib.LinearAlgebra.Matrix.Adjugate
import Mathlib.FieldTheory.IsAlgClosed.Basic
import CFSG.HardMathSupport.Timmesfeld.LangTorus.BigAnyDefs
import CFSG.HardMathSupport.Timmesfeld.LangTorus.CentralizerTrivialPoly
import CFSG.HardMathSupport.Timmesfeld.LangTorus.RigidField
import CFSG.HardMathSupport.Timmesfeld.LangTorus.RigidNorm

public section

namespace CFSG.StandardType.LangRat

open CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.LieType.Steinberg.Adjoint
open scoped TensorProduct

private theorem langRatLS_solve {A : Type*} [AddCommGroup A]
    (hdiv : ∀ (a : A) (d : ℤ), d ≠ 0 → ∃ s, d • s = a)
    {n : ℕ} (G : Matrix (Fin n) (Fin n) ℤ) (hG : G.det ≠ 0) (t : Fin n → A) :
    ∃ u : Fin n → A, ∀ j, ∑ i, G i j • u i = t j := by
  classical
  choose s hs using fun k => hdiv (t k) G.det hG
  refine ⟨fun i => ∑ k, Matrix.adjugate G.transpose i k • s k, fun j => ?_⟩
  calc ∑ i, G i j • (∑ k, Matrix.adjugate G.transpose i k • s k)
      = ∑ i, ∑ k, (G i j * Matrix.adjugate G.transpose i k) • s k := by
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [Finset.smul_sum]
        exact Finset.sum_congr rfl fun k _ => by rw [smul_smul]
    _ = ∑ k, ∑ i, (G i j * Matrix.adjugate G.transpose i k) • s k := Finset.sum_comm
    _ = ∑ k, (∑ i, G i j * Matrix.adjugate G.transpose i k) • s k := by
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [Finset.sum_smul]
    _ = ∑ k, (G.transpose * Matrix.adjugate G.transpose) j k • s k := by
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [Matrix.mul_apply]
        simp only [Matrix.transpose_apply]
    _ = ∑ k, (G.transpose.det • (1 : Matrix (Fin n) (Fin n) ℤ)) j k • s k := by
        rw [Matrix.mul_adjugate]
    _ = ∑ k, (if j = k then G.det else 0) • s k := by
        refine Finset.sum_congr rfl fun k _ => ?_
        by_cases h : j = k
        · subst h
          simp [Matrix.smul_apply, Matrix.one_apply, Matrix.det_transpose, smul_eq_mul]
        · simp [Matrix.smul_apply, Matrix.one_apply, Matrix.det_transpose, smul_eq_mul, h]
    _ = G.det • s j := by
        rw [Finset.sum_eq_single j
          (fun b _ hbj => by simp only [if_neg (Ne.symm hbj), zero_smul])
          (fun hj => absurd (Finset.mem_univ j) hj)]
        simp
    _ = t j := hs j

private theorem langRatLS_iform_sum_left {τ : Tag}
    {n : ℕ} (v : Fin n → ℤ) (x : Fin n → Fin τ.rank → ℤ)
    (w : Fin τ.rank → ℤ) :
    iform (∑ j, v j • x j) w = ∑ j, v j * iform (x j) w := by
  classical
  have key : ∀ s : Finset (Fin n),
      iform (∑ j ∈ s, v j • x j) w = ∑ j ∈ s, v j * iform (x j) w := by
    intro s
    induction s using Finset.induction_on with
    | empty => simp [iform]
    | insert a s ha ih =>
        rw [Finset.sum_insert ha, Finset.sum_insert ha, iform_add_left, iform_smul_left, ih]
  simpa using key Finset.univ

private theorem langRatLS_coe_sum {τ : Tag} (Ψ : Set (Fin τ.rank → ℤ)) {n : ℕ}
    (v : Fin n → ℤ) (B : Fin n → ↥(Submodule.span ℤ Ψ)) :
    ((∑ j, v j • B j : ↥(Submodule.span ℤ Ψ)) : Fin τ.rank → ℤ)
      = ∑ j, v j • ((B j : ↥(Submodule.span ℤ Ψ)) : Fin τ.rank → ℤ) := by
  change Submodule.subtype (Submodule.span ℤ Ψ) (∑ j, v j • B j)
    = ∑ j, v j • ((B j : ↥(Submodule.span ℤ Ψ)) : Fin τ.rank → ℤ)
  rw [map_sum]
  exact Finset.sum_congr rfl fun j _ => Submodule.coe_smul (v j) (B j)

private theorem langRatLS_gram_det_ne_zero {τ : Tag}
    {n : ℕ} (Ψ : Set (Fin τ.rank → ℤ))
    (B : Module.Basis (Fin n) ℤ ↥(Submodule.span ℤ Ψ)) :
    (Matrix.of fun i j => iform ((B i : ↥(Submodule.span ℤ Ψ)) : Fin τ.rank → ℤ)
      ((B j : ↥(Submodule.span ℤ Ψ)) : Fin τ.rank → ℤ)).det ≠ 0 := by
  classical
  intro hdet
  obtain ⟨v, hv0, hv⟩ := (Matrix.exists_mulVec_eq_zero_iff (M := Matrix.of fun i j =>
    iform ((B i : ↥(Submodule.span ℤ Ψ)) : Fin τ.rank → ℤ)
      ((B j : ↥(Submodule.span ℤ Ψ)) : Fin τ.rank → ℤ))).2 hdet
  let G : Matrix (Fin n) (Fin n) ℤ := Matrix.of fun i j =>
    iform ((B i : ↥(Submodule.span ℤ Ψ)) : Fin τ.rank → ℤ)
      ((B j : ↥(Submodule.span ℤ Ψ)) : Fin τ.rank → ℤ)
  let y : Fin τ.rank → ℤ := ∑ j, v j • ((B j : ↥(Submodule.span ℤ Ψ)) : Fin τ.rank → ℤ)
  have hvG : G.mulVec v = 0 := hv
  have hy_ne : y ≠ 0 := by
    intro hy
    have hsum : (∑ j, v j • B j : ↥(Submodule.span ℤ Ψ)) = 0 := by
      apply Subtype.ext
      change ((∑ j, v j • B j : ↥(Submodule.span ℤ Ψ)) : Fin τ.rank → ℤ) = 0
      rw [langRatLS_coe_sum, ← hy]
    have hcoeff := (Fintype.linearIndependent_iff).1 B.linearIndependent v hsum
    exact hv0 (funext fun j => hcoeff j)
  have hFi : ∀ i, iform y ((B i : ↥(Submodule.span ℤ Ψ)) : Fin τ.rank → ℤ) = 0 := by
    intro i
    have hsym : ∀ j, v j * iform ((B j : ↥(Submodule.span ℤ Ψ)) : Fin τ.rank → ℤ)
        ((B i : ↥(Submodule.span ℤ Ψ)) : Fin τ.rank → ℤ) = G i j * v j := by
      intro j
      rw [iform_comm, mul_comm]
      rfl
    rw [show y = ∑ j, v j • ((B j : ↥(Submodule.span ℤ Ψ)) : Fin τ.rank → ℤ) from rfl,
      langRatLS_iform_sum_left]
    have hsum_eq : (∑ j, v j * iform ((B j : ↥(Submodule.span ℤ Ψ)) : Fin τ.rank → ℤ)
        ((B i : ↥(Submodule.span ℤ Ψ)) : Fin τ.rank → ℤ)) = ∑ j, G i j * v j :=
      Finset.sum_congr rfl fun j _ => hsym j
    have hrow : (G.mulVec v) i = ∑ j, G i j * v j := Matrix.mulVec_apply_eq_sum G v i
    rw [hsum_eq, ← hrow, hvG]
    rfl
  have hyy : iform y y = 0 := by
    rw [show y = ∑ j, v j • ((B j : ↥(Submodule.span ℤ Ψ)) : Fin τ.rank → ℤ) from rfl,
      langRatLS_iform_sum_left]
    refine Finset.sum_eq_zero fun j _ => ?_
    rw [iform_comm ((B j : ↥(Submodule.span ℤ Ψ)) : Fin τ.rank → ℤ) y, hFi j, mul_zero]
  have hpos := iform_self_pos hy_ne
  rw [hyy] at hpos
  exact lt_irrefl 0 hpos

private theorem langRatLS_divisible (L : Type) [Field L] [IsAlgClosed L] :
    ∀ (a : Additive Lˣ) (d : ℤ), d ≠ 0 → ∃ s : Additive Lˣ, d • s = a := by
  intro a d hd
  have hm : 0 < d.natAbs := Int.natAbs_pos.mpr hd
  rcases lt_or_gt_of_ne hd with hlt | hgt
  · obtain ⟨z, hz⟩ := IsAlgClosed.exists_pow_nat_eq (((Additive.toMul a : Lˣ) : L)⁻¹) hm
    have hz0 : z ≠ 0 := by
      intro h0
      have hz' : (((Additive.toMul a : Lˣ) : L))⁻¹ = 0 := by rw [← hz, h0]; exact zero_pow hm.ne'
      exact inv_ne_zero (Units.ne_zero (Additive.toMul a)) hz'
    refine ⟨Additive.ofMul (Units.mk0 z hz0), ?_⟩
    rw [← ofMul_zpow]
    show Additive.ofMul (Units.mk0 z hz0 ^ d) = Additive.ofMul (Additive.toMul a)
    exact congrArg Additive.ofMul (by
      have hd_eq : d = -((d.natAbs : ℕ) : ℤ) := by omega
      have hwm : Units.mk0 z hz0 ^ d.natAbs = (Additive.toMul a)⁻¹ := by
        apply Units.ext
        rw [Units.val_pow_eq_pow_val, Units.val_mk0]
        simpa using hz
      rw [hd_eq, zpow_neg, zpow_natCast, hwm, inv_inv])
  · obtain ⟨z, hz⟩ := IsAlgClosed.exists_pow_nat_eq ((Additive.toMul a : Lˣ) : L) hm
    have hz0 : z ≠ 0 := by
      intro h0
      have hz' : ((Additive.toMul a : Lˣ) : L) = 0 := by rw [← hz, h0]; exact zero_pow hm.ne'
      exact Units.ne_zero (Additive.toMul a) hz'
    refine ⟨Additive.ofMul (Units.mk0 z hz0), ?_⟩
    rw [← ofMul_zpow]
    show Additive.ofMul (Units.mk0 z hz0 ^ d) = Additive.ofMul (Additive.toMul a)
    exact congrArg Additive.ofMul (by
      have hd_eq : d = ((d.natAbs : ℕ) : ℤ) := by omega
      have hwm : Units.mk0 z hz0 ^ d.natAbs = Additive.toMul a := by
        apply Units.ext
        rw [Units.val_pow_eq_pow_val, Units.val_mk0]
        simpa using hz
      rw [hd_eq, zpow_natCast, hwm])

private theorem langRatLS_toMul_sum {ι : Type*} [Fintype ι] {G : Type*} [CommGroup G]
    (f : ι → Additive G) : (∑ i, f i).toMul = ∏ i, (f i).toMul := by
  classical
  induction (Finset.univ : Finset ι) using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.prod_insert ha, toMul_add, ih]

private theorem langRatLS_rootChar_zsmul {τ : Tag} {K : Type} [Field K]
    (b : Fin τ.rank → Kˣ) (c : ℤ) (v : Fin τ.rank → ℤ) :
    rootChar b (c • v) = (rootChar b v) ^ c := by
  simp only [rootChar, Pi.smul_apply, smul_eq_mul]
  rw [← Finset.prod_zpow]
  exact Finset.prod_congr rfl fun i _ => zpow_mul' (b i) c (v i)

private theorem langRatLS_rootChar_prod {τ : Tag} {K : Type} [Field K]
    {ι : Type*} [Fintype ι] (f : ι → Fin τ.rank → Kˣ) (v : Fin τ.rank → ℤ) :
    rootChar (∏ i, f i) v = ∏ i, rootChar (f i) v := by
  simp only [rootChar, Finset.prod_apply]
  trans ∏ l, ∏ i, f i l ^ v l
  · exact Finset.prod_congr rfl fun l _ =>
      (Finset.prod_zpow (fun i => f i l) Finset.univ (v l)).symm
  · exact Finset.prod_comm

private noncomputable def langRatLS_charLin {τ : Tag} {L : Type} [Field L]
    (Ψ : Set (Fin τ.rank → ℤ)) (b : Fin τ.rank → Lˣ) :
    ↥(Submodule.span ℤ Ψ) →ₗ[ℤ] Additive Lˣ where
  toFun γ := Additive.ofMul (rootChar b ((γ : ↥(Submodule.span ℤ Ψ)) : Fin τ.rank → ℤ))
  map_add' x y := by
    show Additive.ofMul (rootChar b (((x + y : ↥(Submodule.span ℤ Ψ)) : Fin τ.rank → ℤ)))
      = Additive.ofMul (rootChar b ((x : ↥(Submodule.span ℤ Ψ)) : Fin τ.rank → ℤ))
        + Additive.ofMul (rootChar b ((y : ↥(Submodule.span ℤ Ψ)) : Fin τ.rank → ℤ))
    rw [show ((x + y : ↥(Submodule.span ℤ Ψ)) : Fin τ.rank → ℤ)
        = (x : Fin τ.rank → ℤ) + (y : Fin τ.rank → ℤ) from rfl,
      rootChar_add, ofMul_mul]
  map_smul' c x := by
    show Additive.ofMul (rootChar b (((c • x : ↥(Submodule.span ℤ Ψ)) : Fin τ.rank → ℤ)))
      = c • Additive.ofMul (rootChar b ((x : ↥(Submodule.span ℤ Ψ)) : Fin τ.rank → ℤ))
    rw [show ((c • x : ↥(Submodule.span ℤ Ψ)) : Fin τ.rank → ℤ)
        = c • (x : Fin τ.rank → ℤ) from rfl,
      langRatLS_rootChar_zsmul, ofMul_zpow]

theorem langRatLift_exists_preimage
    {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] (Ψ : Set (Fin τ.rank → ℤ))
    (a : Fin τ.rank → Lˣ) :
    ∃ x : TSc Ψ L, ∀ γ ∈ Ψ,
      rootChar (Additive.toMul (langRatPiT Ψ L x)) γ = rootChar a γ := by
  classical
  obtain ⟨n, B⟩ := Submodule.basisOfPid (Pi.basisFun ℤ (Fin τ.rank)) (Submodule.span ℤ Ψ)
  let G : Matrix (Fin n) (Fin n) ℤ := Matrix.of fun i j =>
    iform ((B i : ↥(Submodule.span ℤ Ψ)) : Fin τ.rank → ℤ)
      ((B j : ↥(Submodule.span ℤ Ψ)) : Fin τ.rank → ℤ)
  have hG : G.det ≠ 0 := langRatLS_gram_det_ne_zero Ψ B
  let t : Fin n → Additive Lˣ := fun j =>
    Additive.ofMul (rootChar a ((B j : ↥(Submodule.span ℤ Ψ)) : Fin τ.rank → ℤ))
  obtain ⟨u, hu⟩ := langRatLS_solve (A := Additive Lˣ) (langRatLS_divisible L) G hG t
  let x : TSc Ψ L := ∑ i, (B i) ⊗ₜ[ℤ] u i
  refine ⟨x, fun γ hγ => ?_⟩
  have hprod : Additive.toMul (langRatPiT Ψ L x)
      = ∏ i, Hchar (τ := τ) (((B i : ↥(Submodule.span ℤ Ψ)) : Fin τ.rank → ℤ))
          (Additive.toMul (u i)) := by
    have hpiT : langRatPiT Ψ L x
        = ∑ i, Additive.ofMul (Hchar (τ := τ)
            (((B i : ↥(Submodule.span ℤ Ψ)) : Fin τ.rank → ℤ)) (Additive.toMul (u i))) := by
      rw [show x = ∑ i, (B i) ⊗ₜ[ℤ] u i from rfl, map_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      apply Additive.toMul.injective
      rw [toMul_langRatPiT_tmul, toMul_ofMul]
      rfl
    rw [hpiT, langRatLS_toMul_sum]
    exact Finset.prod_congr rfl fun i _ => by simp
  have hbase : ∀ j, rootChar (Additive.toMul (langRatPiT Ψ L x))
        ((B j : ↥(Submodule.span ℤ Ψ)) : Fin τ.rank → ℤ)
      = rootChar a ((B j : ↥(Submodule.span ℤ Ψ)) : Fin τ.rank → ℤ) := by
    intro j
    calc rootChar (Additive.toMul (langRatPiT Ψ L x))
          ((B j : ↥(Submodule.span ℤ Ψ)) : Fin τ.rank → ℤ)
        = rootChar (∏ i, Hchar (((B i : ↥(Submodule.span ℤ Ψ)) : Fin τ.rank → ℤ))
              (Additive.toMul (u i))) ((B j : ↥(Submodule.span ℤ Ψ)) : Fin τ.rank → ℤ) := by
            rw [hprod]
      _ = ∏ i, rootChar (Hchar (((B i : ↥(Submodule.span ℤ Ψ)) : Fin τ.rank → ℤ))
              (Additive.toMul (u i))) ((B j : ↥(Submodule.span ℤ Ψ)) : Fin τ.rank → ℤ) :=
            langRatLS_rootChar_prod _ _
      _ = ∏ i, (Additive.toMul (u i)) ^ G i j := by
            refine Finset.prod_congr rfl fun i _ => ?_
            rw [rootChar_Hchar]
            rfl
      _ = ∏ i, Additive.toMul (G i j • u i) := by
            exact Finset.prod_congr rfl fun i _ => by rw [toMul_zsmul]
      _ = Additive.toMul (∑ i, G i j • u i) := (langRatLS_toMul_sum _).symm
      _ = Additive.toMul (t j) := by rw [hu j]
      _ = rootChar a ((B j : ↥(Submodule.span ℤ Ψ)) : Fin τ.rank → ℤ) := by simp [t]
  have hlin : langRatLS_charLin Ψ (Additive.toMul (langRatPiT Ψ L x)) = langRatLS_charLin Ψ a :=
    B.ext fun j => congrArg Additive.ofMul (hbase j)
  have hγ' : Additive.ofMul (rootChar (Additive.toMul (langRatPiT Ψ L x)) γ)
      = Additive.ofMul (rootChar a γ) := by
    have h := congrArg (fun f : ↥(Submodule.span ℤ Ψ) →ₗ[ℤ] Additive Lˣ =>
      f ⟨γ, Submodule.subset_span hγ⟩) hlin
    simpa [langRatLS_charLin] using h
  exact Additive.ofMul.injective hγ'

end CFSG.StandardType.LangRat
