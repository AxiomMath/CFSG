module

public import CFSG.LocalAnalysis.StandardType.GGTBTorRelA5LinModel
import CFSG.LocalAnalysis.StandardType.GGTableBNbrInnerTypeADvdModel

@[expose] public section

namespace CFSG.StandardType.RelA5

open CFSG CFSG.StandardType.CoordSL Matrix Polynomial Multiplicative

section Cent

variable {K : Type} [Field K] [Finite K] [CharP K 2] {g : K[X]} [Fact (Irreducible g)] {n : ℕ}
  {ε : Fin n ≃ (Fin (rootPB g).dim × Fin 3) ⊕ Fin 0}

omit [CharP K 2] in
theorem mem_linFullTorus_of_commute {p : ℕ} [Fact p.Prime]
    (hprim : IsPrimitiveRoot (AdjoinRoot.root g) p) (hpK : p ∣ Nat.card K + 1)
    {F : (Fin 3 → muPlus g) →* SpecialLinearGroup (Fin n) K}
    (hF : ∀ z, (F z : Matrix (Fin n) (Fin n) K) =
      thetaMat g ε (diagonal fun i => (((z i : muPlus g) : (AdjoinRoot g)ˣ) : AdjoinRoot g)))
    {TH : Subgroup (SpecialLinearGroup (Fin n) K)}
    (hTH : ∀ x, x ∈ TH ↔ ∃ c : Fin 3 → (AdjoinRoot g)ˣ, (x : Matrix (Fin n) (Fin n) K) =
      thetaMat g ε (diagonal fun i => ((c i : (AdjoinRoot g)ˣ) : AdjoinRoot g)))
    (x : SpecialLinearGroup (Fin n) K)
    (hx : ∀ z : Fin 3 → muPlus g, (∀ i, z i ^ p = 1) → Commute x (F z)) : x ∈ TH := by
  classical
  have hζ : AdjoinRoot.root g ^ p = 1 := hprim.pow_eq_one
  have hq1 : (AdjoinRoot.root g) ^ (Nat.card K + 1) = 1 := by
    obtain ⟨m, hm⟩ := hpK
    rw [hm, pow_mul, hprim.pow_eq_one, one_pow]
  set ζ : muPlus g := rootsOfUnity.mkOfPowEq (AdjoinRoot.root g) hq1 with hζdef
  have hζroot : (((ζ : muPlus g) : (AdjoinRoot g)ˣ) : AdjoinRoot g) = AdjoinRoot.root g := by
    rw [hζdef, rootsOfUnity.val_mkOfPowEq_coe]
  have hζp : ζ ^ p = 1 := by
    apply Subtype.ext
    apply Units.ext
    change ((((ζ : muPlus g) : (AdjoinRoot g)ˣ) : AdjoinRoot g)) ^ p = 1
    rw [hζroot, hprim.pow_eq_one]
  let c : Fin 3 → AdjoinRoot g := fun j =>
    (frameForm g ε (x : Matrix (Fin n) (Fin n) K) (Pi.single j 1, (0 : Fin 0 → K))).1 j
  have hcomm : ∀ j : Fin 3,
      (x : Matrix (Fin n) (Fin n) K) *
          SLNS.nsMat ε (rootMat g)
            (fun i => ((Pi.single j (1 : ZMod p) : Fin 3 → ZMod p) i).val) =
        SLNS.nsMat ε (rootMat g)
            (fun i => ((Pi.single j (1 : ZMod p) : Fin 3 → ZMod p) i).val) *
          (x : Matrix (Fin n) (Fin n) K) := by
    intro j
    have hzp : ∀ i, (Pi.mulSingle j ζ : Fin 3 → muPlus g) i ^ p = 1 := by
      intro i
      by_cases hi : i = j
      · subst hi
        rw [Pi.mulSingle_eq_same, hζp]
      · rw [Pi.mulSingle_eq_of_ne hi, one_pow]
    have hfun : (fun i => ((((Pi.mulSingle j ζ : Fin 3 → muPlus g) i : muPlus g) :
        (AdjoinRoot g)ˣ) : AdjoinRoot g)) =
        fun i => AdjoinRoot.root g ^
          (((Pi.single j (1 : ZMod p) : Fin 3 → ZMod p) i)).val := by
      funext i
      by_cases hi : i = j
      · subst hi
        rw [Pi.mulSingle_eq_same, hζroot, Pi.single_eq_same,
          ZMod.val_one'' (Fact.out : p.Prime).ne_one, pow_one]
      · rw [Pi.mulSingle_eq_of_ne hi, Pi.single_eq_of_ne hi 1, ZMod.val_zero, pow_zero]
        rfl
    have hxmat : (x : Matrix (Fin n) (Fin n) K) *
        (F (Pi.mulSingle j ζ) : Matrix (Fin n) (Fin n) K) =
        (F (Pi.mulSingle j ζ) : Matrix (Fin n) (Fin n) K) *
          (x : Matrix (Fin n) (Fin n) K) := by
      have h := congrArg (fun v : SpecialLinearGroup (Fin n) K =>
        (v : Matrix (Fin n) (Fin n) K)) (hx (Pi.mulSingle j ζ) hzp)
      simpa only [Matrix.SpecialLinearGroup.coe_mul] using h
    rw [hF (Pi.mulSingle j ζ), hfun, thetaMat_diagonal] at hxmat
    exact hxmat
  have hal : ∀ j : Fin 3, Aligned hζ (Pi.single j (1 : ZMod p)) := by
    intro j
    exact SlNsRootGen.aligned_of_eq_zero_or_one (fun m => by
      by_cases hm : m = j
      · right; rw [hm, Pi.single_eq_same]
      · left; rw [Pi.single_eq_of_ne hm])
  have hj : ∀ j : Fin 3, (Pi.single j (1 : ZMod p) : Fin 3 → ZMod p) j ≠ 0 := by
    intro j
    rw [Pi.single_eq_same]
    exact one_ne_zero
  have hsingle : ∀ (j : Fin 3) (y : AdjoinRoot g),
      frameForm g ε (x : Matrix (Fin n) (Fin n) K) (Pi.single j y, (0 : Fin 0 → K)) =
        (Pi.single j (y * c j), 0) := by
    intro j y
    have hcommj : ∀ y' : (Fin 3 → AdjoinRoot g) × (Fin 0 → K),
        frameForm g ε (x : Matrix (Fin n) (Fin n) K)
            (torusAct g (fun i =>
              ((Pi.single j (1 : ZMod p) : Fin 3 → ZMod p) i).val) y') =
          torusAct g (fun i =>
            ((Pi.single j (1 : ZMod p) : Fin 3 → ZMod p) i).val)
            (frameForm g ε (x : Matrix (Fin n) (Fin n) K) y') :=
      frameForm_torusAct_comm g ε (hcomm j)
    have h := apply_single_of_comm hprim (hal j) hcommj (j := j) (hj j) y
    rw [h]
    congr 1
    funext i
    by_cases hi : i = j
    · subst hi
      rw [Pi.single_eq_same, if_pos rfl, Pi.single_eq_same]
    · have hne : (Pi.single j (1 : ZMod p) : Fin 3 → ZMod p) i ≠
          (Pi.single j (1 : ZMod p) : Fin 3 → ZMod p) j := by
        rw [Pi.single_eq_of_ne hi 1, Pi.single_eq_same]
        exact zero_ne_one
      rw [if_neg hne, Pi.single_eq_of_ne hi]
  have hframe : frameForm g ε (x : Matrix (Fin n) (Fin n) K) = blockAct g (Matrix.diagonal c) := by
    refine LinearMap.ext fun p => ?_
    obtain ⟨d, w⟩ := p
    have hw : w = (0 : Fin 0 → K) := Subsingleton.elim w 0
    rw [hw]
    have hx0 : (d, (0 : Fin 0 → K)) =
        ∑ j, ((Pi.single j (d j), (0 : Fin 0 → K)) :
          (Fin 3 → AdjoinRoot g) × (Fin 0 → K)) := by
      refine Prod.ext ?_ ?_
      · rw [Prod.fst_sum]
        exact (Finset.univ_sum_single d).symm
      · rw [Prod.snd_sum]
        simp
    conv_lhs => rw [hx0]
    rw [map_sum]
    have hsum_eq : (∑ j, frameForm g ε (x : Matrix (Fin n) (Fin n) K)
          ((Pi.single j (d j), (0 : Fin 0 → K)) :
            (Fin 3 → AdjoinRoot g) × (Fin 0 → K))) =
        ∑ j, ((Pi.single j (d j * c j), (0 : Fin 0 → K)) :
          (Fin 3 → AdjoinRoot g) × (Fin 0 → K)) :=
      Finset.sum_congr rfl fun j _ => hsingle j (d j)
    rw [hsum_eq]
    have hR : ((fun i => c i * d i), (0 : Fin 0 → K)) =
        ∑ j, ((Pi.single j (d j * c j), (0 : Fin 0 → K)) :
          (Fin 3 → AdjoinRoot g) × (Fin 0 → K)) := by
      refine Prod.ext ?_ ?_
      · rw [Prod.fst_sum]
        funext i
        dsimp only
        rw [Finset.sum_apply, Finset.sum_eq_single i]
        · rw [Pi.single_eq_same, mul_comm]
        · intro j _ hji
          rw [Pi.single_eq_of_ne (Ne.symm hji)]
        · intro hi
          exact absurd (Finset.mem_univ i) hi
      · rw [Prod.snd_sum]
        simp
    rw [← hR]
    have hblock : blockAct g (Matrix.diagonal c) (d, (0 : Fin 0 → K)) =
        ((fun i => c i * d i), (0 : Fin 0 → K)) := by
      refine Prod.ext ?_ ?_
      · funext i
        simp only [blockAct_apply, Matrix.mulVec_diagonal]
      · rfl
    rw [hblock]
  have hx_eq : (x : Matrix (Fin n) (Fin n) K) = thetaMat g ε (Matrix.diagonal c) := by
    refine frameForm_injective g ε ?_
    rw [frameForm_thetaMat]
    exact hframe
  have : Module.Finite K (AdjoinRoot g) := (rootPB g).finite
  have hdet : Algebra.norm K (Matrix.diagonal c).det = 1 := by
    rw [← det_thetaMat, ← hx_eq]
    exact x.2
  rw [Matrix.det_diagonal] at hdet
  have hprod : (∏ i, c i) ≠ 0 := by
    intro h0
    have h1 : Algebra.norm K (∏ i, c i) = 0 := by
      rw [h0]
      exact Algebra.norm_zero
    rw [h1] at hdet
    exact zero_ne_one hdet
  have hc : ∀ i, c i ≠ 0 := by
    intro i hi
    exact hprod (Finset.prod_eq_zero (s := Finset.univ) (f := c) (Finset.mem_univ i) hi)
  refine (hTH x).mpr ⟨fun i => Units.mk0 (c i) (hc i), ?_⟩
  have hcoe : (fun i => (((Units.mk0 (c i) (hc i) : (AdjoinRoot g)ˣ) : (AdjoinRoot g)))) = c := by
    funext i
    exact Units.val_mk0 (hc i)
  rw [hx_eq, hcoe]

end Cent

section Weyl

variable {K : Type} [Field K] [Fintype K] [CharP K 2] {g : K[X]} [Fact (Irreducible g)] {n : ℕ}
  {ε : Fin n ≃ (Fin (rootPB g).dim × Fin 3) ⊕ Fin 0}

omit [Fintype K] [CharP K 2] in
private theorem thetaMat_swapSL_conj [CharP (AdjoinRoot g) 2] (i j : Fin 3)
    (z : Fin 3 → muPlus g) :
    ((SlNsRootGen.swapSL g ε i j : SpecialLinearGroup (Fin n) K) :
        Matrix (Fin n) (Fin n) K) *
      thetaMat g ε (Matrix.diagonal fun m =>
        (((z m : muPlus g) : (AdjoinRoot g)ˣ) : AdjoinRoot g)) *
      (((SlNsRootGen.swapSL g ε i j)⁻¹ : SpecialLinearGroup (Fin n) K) :
        Matrix (Fin n) (Fin n) K) =
    thetaMat g ε (Matrix.diagonal fun m =>
      (((z (Equiv.swap i j m) : muPlus g) : (AdjoinRoot g)ˣ) : AdjoinRoot g)) := by
  classical
  set P : SpecialLinearGroup (Fin 3) (AdjoinRoot g) := TypeA.permSL (Equiv.swap i j) with hP
  set D : Matrix (Fin 3) (Fin 3) (AdjoinRoot g) :=
    Matrix.diagonal fun m => (((z m : muPlus g) : (AdjoinRoot g)ˣ) : AdjoinRoot g) with hD
  have hPmat : (P : Matrix (Fin 3) (Fin 3) (AdjoinRoot g)) =
      (Equiv.swap i j).permMatrix (AdjoinRoot g) := TypeA.coe_permSL _
  have hPinv : ((P⁻¹ : SpecialLinearGroup (Fin 3) (AdjoinRoot g)) :
      Matrix (Fin 3) (Fin 3) (AdjoinRoot g)) =
      ((Equiv.swap i j)⁻¹).permMatrix (AdjoinRoot g) := by
    rw [TypeA.permSL_inv]
    exact TypeA.coe_permSL _
  have hraw : (P : Matrix (Fin 3) (Fin 3) (AdjoinRoot g)) * D *
      ((P⁻¹ : SpecialLinearGroup (Fin 3) (AdjoinRoot g)) :
        Matrix (Fin 3) (Fin 3) (AdjoinRoot g)) =
      Matrix.diagonal (fun m => (((z (Equiv.swap i j m) : muPlus g) :
        (AdjoinRoot g)ˣ) : AdjoinRoot g)) := by
    rw [hPmat, hPinv, hD]
    exact TypeANbrDvd.permMatrix_mul_diagonal_mul_inv (Equiv.swap i j)
      (fun m => (((z m : muPlus g) : (AdjoinRoot g)ˣ) : AdjoinRoot g))
  have hcoe : ((SlNsRootGen.swapSL g ε i j : SpecialLinearGroup (Fin n) K) :
      Matrix (Fin n) (Fin n) K) =
      thetaMat g ε (P : Matrix (Fin 3) (Fin 3) (AdjoinRoot g)) := by
    rw [SlNsRootGen.swapSL, coe_theta]
  have hcoeinv : (((SlNsRootGen.swapSL g ε i j)⁻¹ : SpecialLinearGroup (Fin n) K) :
      Matrix (Fin n) (Fin n) K) =
      thetaMat g ε ((P⁻¹ : SpecialLinearGroup (Fin 3) (AdjoinRoot g)) :
        Matrix (Fin 3) (Fin 3) (AdjoinRoot g)) := by
    rw [SlNsRootGen.swapSL, ← map_inv, coe_theta]
  rw [hcoe, hcoeinv, ← thetaMat_mul, ← thetaMat_mul, hraw]

omit [CharP K 2] in
private theorem frameForm_negMat_conj {p : ℕ} [NeZero p] [Fact p.Prime]
    (hζ : AdjoinRoot.root g ^ p = 1) (hpK : p ∣ Nat.card K + 1) (z : Fin 3 → muPlus g) :
    frameForm g ε (SlNsRootGen.negMat g ε 2 *
        thetaMat g ε (Matrix.diagonal fun m =>
          (((z m : muPlus g) : (AdjoinRoot g)ˣ) : AdjoinRoot g)) *
        SlNsRootGen.negMat g ε 2) =
      frameForm g ε (thetaMat g ε (Matrix.diagonal fun m =>
        SlNsRootGen.negTau g 2 m (((z m : muPlus g) : (AdjoinRoot g)ˣ) : AdjoinRoot g))) := by
  simp only [frameForm_mul, SlNsRootGen.frameForm_negMat, frameForm_thetaMat]
  refine LinearMap.ext fun x => ?_
  obtain ⟨d, w⟩ := x
  change SlNsRootGen.negMove g 2
      (blockAct g (Matrix.diagonal fun m =>
        (((z m : muPlus g) : (AdjoinRoot g)ˣ) : AdjoinRoot g))
        (SlNsRootGen.negMove g 2 (d, w))) =
      blockAct g (Matrix.diagonal fun m => SlNsRootGen.negTau g 2 m
        (((z m : muPlus g) : (AdjoinRoot g)ˣ) : AdjoinRoot g)) (d, w)
  have htau : ∀ (m : Fin 3) (x : AdjoinRoot g),
      SlNsRootGen.negTau g 2 m (SlNsRootGen.negTau g 2 m x) = x :=
    fun m x => SlNsRootGen.negTau_apply_apply (g := g) hζ hpK 2 m x
  rw [SlNsRootGen.negMove_apply, blockAct_apply, SlNsRootGen.negMove_apply, blockAct_apply]
  refine Prod.ext ?_ rfl
  funext m
  change SlNsRootGen.negTau g 2 m
      (((diagonal fun m => (((z m : muPlus g) : (AdjoinRoot g)ˣ) : AdjoinRoot g)) *ᵥ
        fun m => SlNsRootGen.negTau g 2 m (d m)) m) =
    ((diagonal fun m => SlNsRootGen.negTau g 2 m
      (((z m : muPlus g) : (AdjoinRoot g)ˣ) : AdjoinRoot g)) *ᵥ d) m
  rw [Matrix.mulVec_diagonal, Matrix.mulVec_diagonal, map_mul, htau]

theorem exists_linWeyl {p : ℕ} [Fact p.Prime] (hζ : AdjoinRoot.root g ^ p = 1)
    (hpK : p ∣ Nat.card K + 1) {F : (Fin 3 → muPlus g) →* SpecialLinearGroup (Fin n) K}
    (hF : ∀ z, (F z : Matrix (Fin n) (Fin n) K) =
      thetaMat g ε (diagonal fun i => (((z i : muPlus g) : (AdjoinRoot g)ˣ) : AdjoinRoot g))) :
    ∃ w : Fin 3 → SpecialLinearGroup (Fin n) K, ∀ k z, w k * F z * (w k)⁻¹ = F (refl k z) := by
  classical
  have : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  have : CharP (AdjoinRoot g) 2 :=
    charP_of_injective_algebraMap (algebraMap K (AdjoinRoot g)).injective 2
  have hswap01 : ∀ z : Fin 3 → muPlus g,
      SlNsRootGen.swapSL g ε 0 1 * F z * (SlNsRootGen.swapSL g ε 0 1)⁻¹ = F (refl 0 z) := by
    intro z
    apply Subtype.ext
    rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul,
      hF z, hF (refl 0 z)]
    rw [thetaMat_swapSL_conj (g := g) (ε := ε) (i := 0) (j := 1) (z := z)]
    have hfun : (fun m => (((z (Equiv.swap 0 1 m) : muPlus g) :
        (AdjoinRoot g)ˣ) : AdjoinRoot g)) =
        fun m => ((((refl 0 z) m : muPlus g) : (AdjoinRoot g)ˣ) : AdjoinRoot g) := by
      funext m; fin_cases m <;> simp [refl, Equiv.swap_apply_def]
    rw [hfun]
  have hswap12 : ∀ z : Fin 3 → muPlus g,
      SlNsRootGen.swapSL g ε 1 2 * F z * (SlNsRootGen.swapSL g ε 1 2)⁻¹ = F (refl 1 z) := by
    intro z
    apply Subtype.ext
    rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul,
      hF z, hF (refl 1 z)]
    rw [thetaMat_swapSL_conj (g := g) (ε := ε) (i := 1) (j := 2) (z := z)]
    have hfun : (fun m => (((z (Equiv.swap 1 2 m) : muPlus g) :
        (AdjoinRoot g)ˣ) : AdjoinRoot g)) =
        fun m => ((((refl 1 z) m : muPlus g) : (AdjoinRoot g)ˣ) : AdjoinRoot g) := by
      funext m; fin_cases m <;> simp [refl, Equiv.swap_apply_def]
    rw [hfun]
  have hneg2 : ∀ z : Fin 3 → muPlus g,
      SlNsRootGen.negSL g hζ hpK ε 2 * F z * (SlNsRootGen.negSL g hζ hpK ε 2)⁻¹ =
        F (refl 2 z) := by
    intro z
    have hneg_coe : ((SlNsRootGen.negSL g hζ hpK ε 2 : SpecialLinearGroup (Fin n) K) :
        Matrix (Fin n) (Fin n) K) = SlNsRootGen.negMat g ε 2 := rfl
    have hneg_inv : (((SlNsRootGen.negSL g hζ hpK ε 2)⁻¹ :
        SpecialLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K) =
        SlNsRootGen.negMat g ε 2 := by
      have h2 := SlNsRootGen.negSL_mul_self g hζ hpK ε 2
      have hinv : (SlNsRootGen.negSL g hζ hpK ε 2)⁻¹ =
          SlNsRootGen.negSL g hζ hpK ε 2 := inv_eq_of_mul_eq_one_right h2
      rw [hinv]
      rfl
    have hq2 : (((z 2 : muPlus g) : (AdjoinRoot g)ˣ) : AdjoinRoot g) ^ Nat.card K =
        (((z 2 : muPlus g) : (AdjoinRoot g)ˣ) : AdjoinRoot g)⁻¹ := by
      have hpow : (((z 2 : muPlus g) : (AdjoinRoot g)ˣ) : AdjoinRoot g) ^
          (Nat.card K + 1) = 1 :=
        (mem_rootsOfUnity' (Nat.card K + 1) ((z 2 : muPlus g) : (AdjoinRoot g)ˣ)).mp
          (z 2).2
      have h1 : (((z 2 : muPlus g) : (AdjoinRoot g)ˣ) : AdjoinRoot g) ^ Nat.card K *
          (((z 2 : muPlus g) : (AdjoinRoot g)ˣ) : AdjoinRoot g) = 1 := by
        rw [← pow_succ]
        exact hpow
      exact eq_inv_of_mul_eq_one_right (by rw [mul_comm]; exact h1)
    have hrefl : (fun m => SlNsRootGen.negTau g 2 m
        (((z m : muPlus g) : (AdjoinRoot g)ˣ) : AdjoinRoot g)) =
        fun m => ((((refl 2 z) m : muPlus g) : (AdjoinRoot g)ˣ) : AdjoinRoot g) := by
      funext m
      by_cases hm : m = 2
      · subst hm
        rw [SlNsRootGen.negTau_apply_self, SlNsRootGen.frobAlgEquiv_apply, hq2]
        simp [refl, Units.val_inv_eq_inv_val]
      · have hreflm : (((refl 2 z) m : muPlus g) : (AdjoinRoot g)ˣ) =
            ((z m : muPlus g) : (AdjoinRoot g)ˣ) := by
          fin_cases m <;> simp_all [refl]
        rw [SlNsRootGen.negTau_apply_of_ne (g := g) (i := 2) hm, hreflm]
        rfl
    have hmat : SlNsRootGen.negMat g ε 2 *
        thetaMat g ε (Matrix.diagonal fun m =>
          (((z m : muPlus g) : (AdjoinRoot g)ˣ) : AdjoinRoot g)) *
        SlNsRootGen.negMat g ε 2 =
        thetaMat g ε (Matrix.diagonal fun m => SlNsRootGen.negTau g 2 m
          (((z m : muPlus g) : (AdjoinRoot g)ˣ) : AdjoinRoot g)) := by
      refine frameForm_injective g ε ?_
      rw [frameForm_thetaMat]
      have h := frameForm_negMat_conj (g := g) (ε := ε) hζ hpK z
      rw [frameForm_thetaMat] at h
      exact h
    apply Subtype.ext
    rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul,
      hF z, hF (refl 2 z), hneg_coe, hneg_inv, hmat, hrefl]
  refine ⟨fun k : Fin 3 => match k with
    | 0 => SlNsRootGen.swapSL g ε 0 1
    | 1 => SlNsRootGen.swapSL g ε 1 2
    | 2 => SlNsRootGen.negSL g hζ hpK ε 2, ?_⟩
  intro k z
  fin_cases k
  · exact hswap01 z
  · exact hswap12 z
  · exact hneg2 z

end Weyl

end CFSG.StandardType.RelA5
