module

public import CFSG.LocalAnalysis.StandardType.GGR4JMeetKGDefs
public import CFSG.LocalAnalysis.StandardType.GGPDDefs
public import CFSG.LocalAnalysis.StandardType.GGPDWeightSupport
public import CFSG.Sporadic.ThSchreier.GlobalData
public import CFSG.Sporadic.ThSchreier.LocalOrbitBase1

public section

namespace CFSG.StandardType

open CFSG.Assembly

private theorem pda_map_eq_prod_single {k : ℕ} {G : Type*} [CommGroup G]
    (f : Multiplicative (Fin k → ZMod 3) →* G) (c : Multiplicative (Fin k → ZMod 3)) :
    f c = ∏ j : Fin k,
      f (Multiplicative.ofAdd (Pi.single j 1)) ^ (Multiplicative.toAdd c j).val := by
  have hc : c = ∏ j : Fin k, (Multiplicative.ofAdd (Pi.single j 1 : Fin k → ZMod 3)) ^
      (Multiplicative.toAdd c j).val := by
    apply Multiplicative.toAdd.injective
    rw [toAdd_prod]
    funext m
    simp only [toAdd_pow, toAdd_ofAdd, Finset.sum_apply, Pi.smul_apply, Pi.single_apply, smul_ite,
      smul_zero, Finset.sum_ite_eq, Finset.mem_univ, ite_true, Nat.smul_one_eq_cast,
      ZMod.natCast_zmod_val]
  conv_lhs => rw [hc]
  rw [map_prod]
  exact Finset.prod_congr rfl fun j _ => by rw [map_pow]

private theorem pda_scalar_injective {K : Type} [Field K] {d : ℕ} (hd : 0 < d) :
    Function.Injective (fun c : Kˣ => Matrix.GeneralLinearGroup.scalar (Fin d) c) := by
  intro a b h
  apply Units.ext
  have hmat : ((Matrix.GeneralLinearGroup.scalar (Fin d) a :
        Matrix.GeneralLinearGroup (Fin d) K) : Matrix (Fin d) (Fin d) K)
      = (Matrix.GeneralLinearGroup.scalar (Fin d) b :
        Matrix.GeneralLinearGroup (Fin d) K) := by
    exact congrArg (fun x : Matrix.GeneralLinearGroup (Fin d) K =>
      (x : Matrix (Fin d) (Fin d) K)) h
  let r : Fin d := ⟨0, hd⟩
  have hr := congrFun (congrFun hmat r) r
  simpa [Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, Matrix.diagonal_apply]
    using hr

private theorem pda_ggPDChar_add {K : Type} [Field K] {ζ : K} (hζ : IsPrimitiveRoot ζ 3)
    (x y : ZMod 3) : ggPDChar ζ (x + y) = ggPDChar ζ x * ggPDChar ζ y := by
  have hmod : x.val + y.val ≡ (x + y).val [MOD 3] := by
    apply (ZMod.natCast_eq_natCast_iff _ _ 3).mp
    push_cast
    rw [ZMod.natCast_zmod_val x, ZMod.natCast_zmod_val y, ZMod.natCast_zmod_val (x + y)]
  have hp : ζ ^ (x.val + y.val) = ζ ^ ((x + y).val) :=
    pow_eq_pow_of_modEq hmod hζ.pow_eq_one
  unfold ggPDChar
  rw [← pow_add]
  exact hp.symm

private theorem pda_mulVec_mul {K : Type} [Field K] {d : ℕ}
    (A B : Matrix.GeneralLinearGroup (Fin d) K) (v : Fin d → K) :
    ((A * B : Matrix.GeneralLinearGroup (Fin d) K) : Matrix (Fin d) (Fin d) K).mulVec v
      = (A : Matrix (Fin d) (Fin d) K).mulVec
        ((B : Matrix (Fin d) (Fin d) K).mulVec v) := by
  rw [Matrix.GeneralLinearGroup.coe_mul, ← Matrix.mulVec_mulVec]

private theorem pda_scalar_mulVec {K : Type} [Field K] {d : ℕ} (a : K) (v : Fin d → K) :
    (Matrix.scalar (Fin d) a).mulVec v = a • v := by
  rw [Matrix.scalar_apply, Matrix.diagonal_const_mulVec]

private theorem pda_GL_scalar_mulVec {K : Type} [Field K] {d : ℕ}
    (a : Kˣ) (v : Fin d → K) :
    ((Matrix.GeneralLinearGroup.scalar (Fin d) a :
        Matrix.GeneralLinearGroup (Fin d) K) : Matrix (Fin d) (Fin d) K).mulVec v
      = (a : K) • v := by
  rw [Matrix.GeneralLinearGroup.coe_scalar, pda_scalar_mulVec]

private theorem pda_scalar_mul_mul {K : Type} [Field K] {d : ℕ} (a b : Kˣ)
    (X Y : Matrix.GeneralLinearGroup (Fin d) K) :
    (Matrix.GeneralLinearGroup.scalar (Fin d) a * X) *
        (Matrix.GeneralLinearGroup.scalar (Fin d) b * Y)
      = Matrix.GeneralLinearGroup.scalar (Fin d) (a * b) * (X * Y) := by
  calc
    (Matrix.GeneralLinearGroup.scalar (Fin d) a * X) *
        (Matrix.GeneralLinearGroup.scalar (Fin d) b * Y)
        = Matrix.GeneralLinearGroup.scalar (Fin d) a *
            (X * Matrix.GeneralLinearGroup.scalar (Fin d) b) * Y := by group
    _ = Matrix.GeneralLinearGroup.scalar (Fin d) a *
            (Matrix.GeneralLinearGroup.scalar (Fin d) b * X) * Y := by
          rw [(Matrix.GeneralLinearGroup.scalar_commute b X).symm]
    _ = Matrix.GeneralLinearGroup.scalar (Fin d) a *
            Matrix.GeneralLinearGroup.scalar (Fin d) b * (X * Y) := by group
    _ = Matrix.GeneralLinearGroup.scalar (Fin d) (a * b) * (X * Y) := by
          rw [← map_mul]

theorem ggPD_weight_affine {K : Type} [Field K] {d : ℕ} {ζ : K} (hζ : IsPrimitiveRoot ζ 3)
    (M : Matrix (Fin 4) (Fin 4) (ZMod 3)) (i : Fin 4)
    (ρ : Multiplicative (Fin 4 → ZMod 3) →* Matrix.GeneralLinearGroup (Fin d) K)
    (b : Module.Basis (Fin d) K (Fin d → K)) (u : Fin d → (Fin 4 → ZMod 3))
    (hb : ∀ (v : Multiplicative (Fin 4 → ZMod 3)) (j : Fin d),
      (ρ v : Matrix (Fin d) (Fin d) K).mulVec (b j) =
        ggPDChar ζ (u j ⬝ᵥ Multiplicative.toAdd v) • b j)
    (hinv : ∀ v, (ggPDRefl M i).mulVec ((ggPDRefl M i).mulVec v) = v)
    (g : Matrix.GeneralLinearGroup (Fin d) K)
    (hg : ∀ v, ∃ c : Kˣ, g * ρ v * g⁻¹ = Matrix.GeneralLinearGroup.scalar (Fin d) c *
      ρ (Multiplicative.ofAdd ((ggPDRefl M i).mulVec (Multiplicative.toAdd v)))) :
    ∃ t : Fin 4 → ZMod 3, ∀ j, ∃ j', u j' = (ggPDRefl M i).transpose.mulVec (u j) + t := by
  classical
  rcases Nat.eq_zero_or_pos d with hd0 | hd
  · subst d
    exact ⟨0, fun j => j.elim0⟩
  set S : Matrix (Fin 4) (Fin 4) (ZMod 3) := ggPDRefl M i with hS
  choose c hc using hg
  have hc_add : ∀ x : Fin 4 → ZMod 3,
      g * ρ (Multiplicative.ofAdd x) * g⁻¹ =
        Matrix.GeneralLinearGroup.scalar (Fin d) (c (Multiplicative.ofAdd x)) *
          ρ (Multiplicative.ofAdd (S.mulVec x)) := by
    intro x
    simpa only [toAdd_ofAdd] using hc (Multiplicative.ofAdd x)
  have hmul : ∀ x y : Fin 4 → ZMod 3,
      c (Multiplicative.ofAdd (x + y)) =
        c (Multiplicative.ofAdd x) * c (Multiplicative.ofAdd y) := by
    intro x y
    apply pda_scalar_injective hd
    apply mul_right_cancel (b := ρ (Multiplicative.ofAdd (S.mulVec (x + y))))
    calc
      Matrix.GeneralLinearGroup.scalar (Fin d) (c (Multiplicative.ofAdd (x + y))) *
          ρ (Multiplicative.ofAdd (S.mulVec (x + y)))
          = g * ρ (Multiplicative.ofAdd (x + y)) * g⁻¹ :=
            (hc_add (x + y)).symm
      _ = (Matrix.GeneralLinearGroup.scalar (Fin d) (c (Multiplicative.ofAdd x)) *
            ρ (Multiplicative.ofAdd (S.mulVec x))) *
          (Matrix.GeneralLinearGroup.scalar (Fin d) (c (Multiplicative.ofAdd y)) *
            ρ (Multiplicative.ofAdd (S.mulVec y))) := by
            rw [show Multiplicative.ofAdd (x + y)
                  = Multiplicative.ofAdd x * Multiplicative.ofAdd y from rfl]
            rw [map_mul]
            have hconj : g * (ρ (Multiplicative.ofAdd x) * ρ (Multiplicative.ofAdd y)) * g⁻¹
                = (g * ρ (Multiplicative.ofAdd x) * g⁻¹) *
                  (g * ρ (Multiplicative.ofAdd y) * g⁻¹) := by group
            rw [hconj, hc_add, hc_add]
      _ = Matrix.GeneralLinearGroup.scalar (Fin d)
            (c (Multiplicative.ofAdd x) * c (Multiplicative.ofAdd y)) *
          ρ (Multiplicative.ofAdd (S.mulVec (x + y))) := by
            rw [pda_scalar_mul_mul]
            congr 1
            rw [← map_mul, ← ofAdd_add, Matrix.mulVec_add]
  have hc0 : c (Multiplicative.ofAdd (0 : Fin 4 → ZMod 3)) = 1 := by
    have h := hmul 0 0
    rw [add_zero] at h
    have h2 : (1 : Kˣ) = c (Multiplicative.ofAdd 0) := by
      calc (1 : Kˣ) = (c (Multiplicative.ofAdd 0))⁻¹ * c (Multiplicative.ofAdd 0) :=
            (inv_mul_cancel _).symm
        _ = (c (Multiplicative.ofAdd 0))⁻¹ *
              (c (Multiplicative.ofAdd 0) * c (Multiplicative.ofAdd 0)) := by rw [← h]
        _ = c (Multiplicative.ofAdd 0) := by rw [← mul_assoc, inv_mul_cancel, one_mul]
    exact h2.symm
  have hc_cube : ∀ x : Fin 4 → ZMod 3, (c (Multiplicative.ofAdd x)) ^ 3 = 1 := by
    intro x
    have h3x : (3 : ℕ) • x = 0 := by
      funext k
      simp only [Pi.smul_apply, nsmul_eq_mul, ZMod.natCast_self, zero_mul, Pi.zero_apply]
    have hcube : c (Multiplicative.ofAdd ((3 : ℕ) • x)) =
        (c (Multiplicative.ofAdd x)) ^ 3 := by
      calc c (Multiplicative.ofAdd ((3 : ℕ) • x))
          = c (Multiplicative.ofAdd ((x + x) + x)) := by rw [three_nsmul, ← add_assoc]
        _ = c (Multiplicative.ofAdd (x + x)) * c (Multiplicative.ofAdd x) := hmul (x + x) x
        _ = (c (Multiplicative.ofAdd x) * c (Multiplicative.ofAdd x)) *
              c (Multiplicative.ofAdd x) := by rw [hmul x x]
        _ = (c (Multiplicative.ofAdd x)) ^ 3 := by rw [pow_three, ← mul_assoc]
    rw [h3x, hc0] at hcube
    exact hcube.symm
  let Cfun : (Fin 4 → ZMod 3) → Kˣ :=
    fun x => (c (Multiplicative.ofAdd (S.mulVec x)))⁻¹
  have hCfun_mul : ∀ x y, Cfun (x + y) = Cfun x * Cfun y := by
    intro x y
    change (c (Multiplicative.ofAdd (S.mulVec (x + y))))⁻¹
        = (c (Multiplicative.ofAdd (S.mulVec x)))⁻¹ *
          (c (Multiplicative.ofAdd (S.mulVec y)))⁻¹
    rw [Matrix.mulVec_add, hmul, mul_inv_rev, mul_comm]
  let C : Multiplicative (Fin 4 → ZMod 3) →* Kˣ :=
    MonoidHom.mk' (fun v => Cfun (Multiplicative.toAdd v)) (by
      intro v w'
      change Cfun (Multiplicative.toAdd (v * w')) =
        Cfun (Multiplicative.toAdd v) * Cfun (Multiplicative.toAdd w')
      exact hCfun_mul _ _)
  have hC3 : ∀ v, C v ^ 3 = 1 := by
    intro v
    change (Cfun (Multiplicative.toAdd v)) ^ 3 = 1
    rw [show Cfun (Multiplicative.toAdd v) =
          (c (Multiplicative.ofAdd (S.mulVec (Multiplicative.toAdd v))))⁻¹ from rfl]
    rw [inv_pow, hc_cube (S.mulVec (Multiplicative.toAdd v)), inv_one]
  have hE : ∀ k : Fin 4, ∃ r : ℕ, r < 3 ∧
      ζ ^ r = ((C (Multiplicative.ofAdd (Pi.single k 1)) : K)) := by
    intro k
    have h3 : ((C (Multiplicative.ofAdd (Pi.single k 1)) : K)) ^ 3 = 1 := by
      have h := congrArg (fun u : Kˣ => (u : K))
        (hC3 (Multiplicative.ofAdd (Pi.single k 1)))
      simpa [Units.val_pow_eq_pow_val] using h
    exact IsPrimitiveRoot.eq_pow_of_pow_eq_one hζ h3
  let iota : Fin 4 → ℕ := fun k => Classical.choose (hE k)
  have hi_lt : ∀ k, iota k < 3 := fun k => (Classical.choose_spec (hE k)).1
  have hi_pow : ∀ k, ζ ^ iota k = ((C (Multiplicative.ofAdd (Pi.single k 1)) : K)) :=
    fun k => (Classical.choose_spec (hE k)).2
  let t : Fin 4 → ZMod 3 := fun k => (iota k : ZMod 3)
  have hCt : ∀ v : Multiplicative (Fin 4 → ZMod 3),
      (C v : K) = ζ ^ ((t ⬝ᵥ Multiplicative.toAdd v).val) := by
    intro v
    have hprod := pda_map_eq_prod_single C v
    have hco : ((C v : K)) = ∏ k : Fin 4,
        ((C (Multiplicative.ofAdd (Pi.single k 1)) : K)) ^
          (Multiplicative.toAdd v k).val := by
      have h := congrArg (fun u : Kˣ => (u : K)) hprod
      simpa [Units.coe_prod, Units.val_pow_eq_pow_val] using h
    have hbase : ∀ k ∈ Finset.univ,
        ((C (Multiplicative.ofAdd (Pi.single k 1)) : K)) ^
            (Multiplicative.toAdd v k).val
          = ζ ^ (iota k * (Multiplicative.toAdd v k).val) := by
      intro k _
      rw [← hi_pow k, ← pow_mul]
    have hcast : ((∑ k : Fin 4, iota k * (Multiplicative.toAdd v k).val : ℕ) : ZMod 3)
        = t ⬝ᵥ Multiplicative.toAdd v := by
      unfold dotProduct
      push_cast
      apply Finset.sum_congr rfl
      intro k _
      simp only [t]
      rw [ZMod.natCast_zmod_val]
    have hmod : (∑ k : Fin 4, iota k * (Multiplicative.toAdd v k).val) ≡
        (t ⬝ᵥ Multiplicative.toAdd v).val [MOD 3] := by
      apply (ZMod.natCast_eq_natCast_iff _ _ 3).mp
      rw [hcast, ZMod.natCast_zmod_val]
    rw [hco, Finset.prod_congr rfl hbase, Finset.prod_pow_eq_pow_sum]
    exact pow_eq_pow_of_modEq hmod hζ.pow_eq_one
  have hρv_GL : ∀ v' : Fin 4 → ZMod 3,
      ρ (Multiplicative.ofAdd v') =
        Matrix.GeneralLinearGroup.scalar (Fin d)
            (c (Multiplicative.ofAdd (S.mulVec v')))⁻¹ *
          (g * ρ (Multiplicative.ofAdd (S.mulVec v')) * g⁻¹) := by
    intro v'
    have h := hc_add (S.mulVec v')
    rw [hinv v'] at h
    rw [h, ← mul_assoc, ← map_mul, inv_mul_cancel, map_one, one_mul]
  have hfv : ∀ (j : Fin d) (v' : Fin 4 → ZMod 3),
      ((c (Multiplicative.ofAdd (S.mulVec v')))⁻¹ : K) *
          ggPDChar ζ (u j ⬝ᵥ S.mulVec v')
        = ggPDChar ζ ((S.transpose.mulVec (u j) + t) ⬝ᵥ v') := by
    intro j v'
    have hST : S.transpose.mulVec (u j) = Matrix.vecMul (u j) S := by
      rw [← Matrix.vecMul_transpose (A := S.transpose) (x := u j), Matrix.transpose_transpose]
    have hdot : (S.transpose.mulVec (u j)) ⬝ᵥ v' = u j ⬝ᵥ S.mulVec v' := by
      rw [hST, ← Matrix.dotProduct_mulVec]
    have hCv : ((c (Multiplicative.ofAdd (S.mulVec v')))⁻¹ : K) =
        ggPDChar ζ (t ⬝ᵥ v') := by
      have h := hCt (Multiplicative.ofAdd v')
      simpa [C, Cfun, ggPDChar] using h
    rw [add_dotProduct, pda_ggPDChar_add hζ]
    rw [hCv, hdot]
    ring
  have key : ∀ j : Fin d, ∃ j', u j' = S.transpose.mulVec (u j) + t := by
    intro j
    set w : Fin d → K := (g : Matrix (Fin d) (Fin d) K).mulVec (b j) with hw
    have hg_inv_w : ((g⁻¹ : Matrix.GeneralLinearGroup (Fin d) K) :
        Matrix (Fin d) (Fin d) K).mulVec w = b j := by
      rw [hw, Matrix.mulVec_mulVec, ← Matrix.GeneralLinearGroup.coe_mul,
        inv_mul_cancel, Matrix.GeneralLinearGroup.coe_one, Matrix.one_mulVec]
    have hw_ne : w ≠ 0 := by
      intro h0
      have hb0 : b j = 0 := by
        rw [← hg_inv_w, h0, Matrix.mulVec_zero]
      exact b.ne_zero j hb0
    have heig' : ∀ v' : Fin 4 → ZMod 3,
        (ρ (Multiplicative.ofAdd v') : Matrix (Fin d) (Fin d) K).mulVec w
          = ggPDChar ζ ((S.transpose.mulVec (u j) + t) ⬝ᵥ v') • w := by
      intro v'
      calc
        (ρ (Multiplicative.ofAdd v') : Matrix (Fin d) (Fin d) K).mulVec w
            = ((Matrix.GeneralLinearGroup.scalar (Fin d)
                  (c (Multiplicative.ofAdd (S.mulVec v')))⁻¹ *
                (g * ρ (Multiplicative.ofAdd (S.mulVec v')) * g⁻¹) :
                  Matrix.GeneralLinearGroup (Fin d) K) :
                  Matrix (Fin d) (Fin d) K).mulVec w := by rw [hρv_GL v']
        _ = ((Matrix.GeneralLinearGroup.scalar (Fin d)
                  (c (Multiplicative.ofAdd (S.mulVec v')))⁻¹ :
                  Matrix.GeneralLinearGroup (Fin d) K) :
                  Matrix (Fin d) (Fin d) K).mulVec
              ((((g * ρ (Multiplicative.ofAdd (S.mulVec v')) * g⁻¹) :
                  Matrix.GeneralLinearGroup (Fin d) K) :
                  Matrix (Fin d) (Fin d) K).mulVec w) := by
              rw [pda_mulVec_mul]
        _ = ((c (Multiplicative.ofAdd (S.mulVec v')))⁻¹ : K) •
              ((((g * ρ (Multiplicative.ofAdd (S.mulVec v')) * g⁻¹) :
                  Matrix.GeneralLinearGroup (Fin d) K) :
                  Matrix (Fin d) (Fin d) K).mulVec w) := by
              rw [pda_GL_scalar_mulVec]
              simp only [Units.val_inv_eq_inv_val]
        _ = ((c (Multiplicative.ofAdd (S.mulVec v')))⁻¹ : K) •
              ((g : Matrix (Fin d) (Fin d) K).mulVec
                ((ρ (Multiplicative.ofAdd (S.mulVec v')) :
                    Matrix (Fin d) (Fin d) K).mulVec
                  (((g⁻¹ : Matrix.GeneralLinearGroup (Fin d) K) :
                    Matrix (Fin d) (Fin d) K).mulVec w))) := by
              congr 1
              rw [pda_mulVec_mul, pda_mulVec_mul]
        _ = ((c (Multiplicative.ofAdd (S.mulVec v')))⁻¹ : K) •
              ((g : Matrix (Fin d) (Fin d) K).mulVec
                (ggPDChar ζ (u j ⬝ᵥ S.mulVec v') • b j)) := by
              congr 1
              rw [hg_inv_w, hb (Multiplicative.ofAdd (S.mulVec v')) j]
              simp only [toAdd_ofAdd]
        _ = ((c (Multiplicative.ofAdd (S.mulVec v')))⁻¹ : K) •
              (ggPDChar ζ (u j ⬝ᵥ S.mulVec v') • w) := by
              congr 1
              rw [Matrix.mulVec_smul, ← hw]
        _ = (((c (Multiplicative.ofAdd (S.mulVec v')))⁻¹ : K) *
              ggPDChar ζ (u j ⬝ᵥ S.mulVec v')) • w := by
              rw [smul_smul]
        _ = ggPDChar ζ ((S.transpose.mulVec (u j) + t) ⬝ᵥ v') • w := by
              rw [hfv]
    have heig : ∀ v : Multiplicative (Fin 4 → ZMod 3),
        (ρ v : Matrix (Fin d) (Fin d) K).mulVec w
          = ggPDChar ζ ((S.transpose.mulVec (u j) + t) ⬝ᵥ Multiplicative.toAdd v) • w := by
      intro v
      have h := heig' (Multiplicative.toAdd v)
      simpa [ofAdd_toAdd] using h
    have hmem := (ggPD_weight_support hζ ρ b u hb).1 w hw_ne
      (S.transpose.mulVec (u j) + t) heig
    rcases hmem with ⟨j', hj'⟩
    exact ⟨j', hj'⟩
  exact ⟨t, key⟩

end CFSG.StandardType

end
