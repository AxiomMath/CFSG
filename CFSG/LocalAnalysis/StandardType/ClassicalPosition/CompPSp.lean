module

public import CFSG.LocalAnalysis.StandardType.ClassicalPosition.Defs
public import CFSG.LocalAnalysis.StandardType.ClassicalPosition.BlockDecomp
public import CFSG.LocalAnalysis.StandardType.ClassicalPosition.CompCore
public import CFSG.LocalAnalysis.StandardType.ClassicalPosition.GeoAdj
public import CFSG.Open.StatedDefs
public import CFSG.Open.StatedAPI

public section

namespace CFSG.StandardType.ClassicalPosition

open CFSG.Assembly

open scoped commutatorElement

private abbrev cpSp_J (n : ℕ) (F : Type) [Field F] :
    Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F :=
  Matrix.fromBlocks 0 1 (-1) 0

private lemma cpSp_J_mul_self {n : ℕ} {F : Type} [Field F] :
    cpSp_J n F * cpSp_J n F = -1 := by
  unfold cpSp_J
  rw [Matrix.fromBlocks_multiply]
  simp only [Matrix.mul_zero, Matrix.mul_one, zero_add, add_zero, Matrix.mul_neg, neg_zero]
  rw [show (-1 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) =
      Matrix.fromBlocks (-1) 0 0 (-1) by
    rw [← Matrix.fromBlocks_one, Matrix.fromBlocks_neg]
    simp]

private lemma cpSp_J_isUnit_det {n : ℕ} {F : Type} [Field F] :
    IsUnit (cpSp_J n F).det := by
  have h1 : cpSp_J n F * (-(cpSp_J n F)) = 1 := by
    rw [Matrix.mul_neg, cpSp_J_mul_self, neg_neg]
  have h2 : (-(cpSp_J n F)) * cpSp_J n F = 1 := by
    rw [Matrix.neg_mul, cpSp_J_mul_self, neg_neg]
  exact (Matrix.isUnit_iff_isUnit_det (cpSp_J n F)).mp
    (isUnit_iff_exists.mpr ⟨-(cpSp_J n F), h1, h2⟩)

private lemma cpSp_eps_mul_one_sub {ι F : Type} [Fintype ι] [DecidableEq ι] [Ring F]
    {ε : Matrix ι ι F} (h : IsIdempotentElem ε) : ε * (1 - ε) = 0 := by
  rw [Matrix.mul_sub, Matrix.mul_one, h.eq, sub_self]

private lemma cpSp_one_sub_mul_eps {ι F : Type} [Fintype ι] [DecidableEq ι] [Ring F]
    {ε : Matrix ι ι F} (h : IsIdempotentElem ε) : (1 - ε) * ε = 0 := by
  rw [Matrix.sub_mul, Matrix.one_mul, h.eq, sub_self]

private lemma cpSp_one_sub_mul_one_sub {ι F : Type} [Fintype ι] [DecidableEq ι] [Ring F]
    {ε : Matrix ι ι F} (h : IsIdempotentElem ε) : (1 - ε) * (1 - ε) = 1 - ε := by
  rw [Matrix.mul_sub, Matrix.mul_one, cpSp_one_sub_mul_eps h, sub_zero]

private lemma cpSp_blk_mul {ι F : Type} [Fintype ι] [DecidableEq ι] [Ring F]
    {ε : Matrix ι ι F} (hid : IsIdempotentElem ε)
    {p q : Matrix ι ι F} (hq : q * ε = ε * q) :
    (p * ε + (1 - ε)) * (q * ε + (1 - ε)) = (p * q) * ε + (1 - ε) := by
  have hεε : ε * ε = ε := hid.eq
  have hp1 : p * ε * (1 - ε) = 0 := by
    rw [Matrix.mul_assoc, cpSp_eps_mul_one_sub hid, Matrix.mul_zero]
  have hq1 : (1 - ε) * q = q * (1 - ε) := by
    rw [Matrix.sub_mul, Matrix.one_mul, Matrix.mul_sub, Matrix.mul_one, hq]
  have h1q : (1 - ε) * (q * ε) = 0 := by
    rw [← Matrix.mul_assoc, hq1, Matrix.mul_assoc, cpSp_one_sub_mul_eps hid, Matrix.mul_zero]
  have hpq : (p * ε) * (q * ε) = (p * q) * ε := by
    rw [Matrix.mul_assoc p ε, ← Matrix.mul_assoc ε q ε, ← hq, Matrix.mul_assoc q ε ε, hεε,
        ← Matrix.mul_assoc p q ε]
  calc (p * ε + (1 - ε)) * (q * ε + (1 - ε))
      = (p * ε) * (q * ε) + (p * ε) * (1 - ε) +
          ((1 - ε) * (q * ε) + (1 - ε) * (1 - ε)) := by
        rw [Matrix.add_mul, Matrix.mul_add, Matrix.mul_add]
    _ = (p * q) * ε + 0 + (0 + (1 - ε)) := by
        rw [hpq, hp1, h1q, cpSp_one_sub_mul_one_sub hid]
    _ = (p * q) * ε + (1 - ε) := by abel

@[expose] def cpSp_blkVal {ι F : Type} [Fintype ι] [DecidableEq ι] [Field F]
    (m : GL ι F) (ε : Matrix ι ι F) : Matrix ι ι F :=
  (m : Matrix ι ι F) * ε + (1 - ε)

def cpSp_blkInvVal {ι F : Type} [Fintype ι] [DecidableEq ι] [Field F]
    (m : GL ι F) (ε : Matrix ι ι F) : Matrix ι ι F :=
  (((m⁻¹ : GL ι F)) : Matrix ι ι F) * ε + (1 - ε)

private lemma cpSp_inv_comm {ι F : Type} [Fintype ι] [DecidableEq ι] [Field F]
    (m : GL ι F) {ε : Matrix ι ι F}
    (hm : (m : Matrix ι ι F) * ε = ε * (m : Matrix ι ι F)) :
    (((m⁻¹ : GL ι F)) : Matrix ι ι F) * ε =
      ε * (((m⁻¹ : GL ι F)) : Matrix ι ι F) := by
  have hmm : (m : Matrix ι ι F) * (((m⁻¹ : GL ι F)) : Matrix ι ι F) = 1 := by
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hm'm : (((m⁻¹ : GL ι F)) : Matrix ι ι F) * (m : Matrix ι ι F) = 1 := by
    rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  calc (((m⁻¹ : GL ι F)) : Matrix ι ι F) * ε
      = (((m⁻¹ : GL ι F)) : Matrix ι ι F) * ε *
          ((m : Matrix ι ι F) * (((m⁻¹ : GL ι F)) : Matrix ι ι F)) := by
        rw [hmm, Matrix.mul_one]
    _ = (((m⁻¹ : GL ι F)) : Matrix ι ι F) * (ε * (m : Matrix ι ι F)) *
          (((m⁻¹ : GL ι F)) : Matrix ι ι F) := by simp only [Matrix.mul_assoc]
    _ = (((m⁻¹ : GL ι F)) : Matrix ι ι F) * ((m : Matrix ι ι F) * ε) *
          (((m⁻¹ : GL ι F)) : Matrix ι ι F) := by rw [← hm]
    _ = ε * (((m⁻¹ : GL ι F)) : Matrix ι ι F) := by
        rw [← Matrix.mul_assoc (((m⁻¹ : GL ι F)) : Matrix ι ι F)
              (m : Matrix ι ι F) ε, hm'm, Matrix.one_mul]

lemma cpSp_blk_val_mul_inv {ι F : Type} [Fintype ι] [DecidableEq ι] [Field F]
    (m : GL ι F) (ε : Matrix ι ι F) (hid : IsIdempotentElem ε)
    (hm : (m : Matrix ι ι F) * ε = ε * (m : Matrix ι ι F)) :
    cpSp_blkVal m ε * cpSp_blkInvVal m ε = 1 := by
  have hmm : (m : Matrix ι ι F) * (((m⁻¹ : GL ι F)) : Matrix ι ι F) = 1 := by
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  rw [cpSp_blkVal, cpSp_blkInvVal,
      cpSp_blk_mul hid (cpSp_inv_comm m hm), hmm, Matrix.one_mul,
      ← add_sub_assoc, add_sub_cancel_left]

lemma cpSp_blk_inv_mul_val {ι F : Type} [Fintype ι] [DecidableEq ι] [Field F]
    (m : GL ι F) (ε : Matrix ι ι F) (hid : IsIdempotentElem ε)
    (hm : (m : Matrix ι ι F) * ε = ε * (m : Matrix ι ι F)) :
    cpSp_blkInvVal m ε * cpSp_blkVal m ε = 1 := by
  have hm'm : (((m⁻¹ : GL ι F)) : Matrix ι ι F) * (m : Matrix ι ι F) = 1 := by
    rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  rw [cpSp_blkVal, cpSp_blkInvVal,
      cpSp_blk_mul hid hm, hm'm, Matrix.one_mul,
      ← add_sub_assoc, add_sub_cancel_left]

@[expose] noncomputable def cpSp_blk {ι F : Type} [Fintype ι] [DecidableEq ι] [Field F]
    (m : GL ι F) (ε : Matrix ι ι F) (hid : IsIdempotentElem ε)
    (hm : (m : Matrix ι ι F) * ε = ε * (m : Matrix ι ι F)) : GL ι F :=
  Units.mk (cpSp_blkVal m ε) (cpSp_blkInvVal m ε)
    (cpSp_blk_val_mul_inv m ε hid hm) (cpSp_blk_inv_mul_val m ε hid hm)

private lemma cpSp_mem_adjoin_comm {ι F : Type} [Fintype ι] [DecidableEq ι] [Field F]
    {S : Set (GL ι F)} {g : Matrix ι ι F}
    (hg : ∀ s ∈ S, (s : Matrix ι ι F) * g = g * (s : Matrix ι ι F))
    {ε : Matrix ι ι F} (hε : ε ∈ Algebra.adjoin F (Units.val '' S)) :
    g * ε = ε * g := by
  have hAle : Algebra.adjoin F (Units.val '' S) ≤
      Subalgebra.centralizer F ({g} : Set (Matrix ι ι F)) := by
    refine Algebra.adjoin_le ?_
    rintro y ⟨s, hs, rfl⟩
    change (s : Matrix ι ι F) ∈ Subalgebra.centralizer F ({g} : Set (Matrix ι ι F))
    rw [Subalgebra.mem_centralizer_iff F]
    intro z hz
    rw [Set.mem_singleton_iff] at hz
    subst hz
    exact (hg s hs).symm
  exact (Subalgebra.mem_centralizer_iff F).mp (hAle hε) g (Set.mem_singleton g)

private lemma cpSp_blk_mem_statedSp {n : ℕ} {F : Type} [Field F]
    (m : GL (Fin n ⊕ Fin n) F) (hm : m ∈ CFSG.Open.StatedSp n F)
    (ε : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) (hid : IsIdempotentElem ε)
    (hcomm : (m : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) * ε =
      ε * (m : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F))
    (hst : formAdj (RingHom.id F) (cpSp_J n F) ε = ε) :
    cpSp_blk m ε hid hcomm ∈ CFSG.Open.StatedSp n F := by
  have hJdet : IsUnit (cpSp_J n F).det := cpSp_J_isUnit_det
  have hcomm' := cpSp_inv_comm m hcomm
  have hm_inv : formAdj (RingHom.id F) (cpSp_J n F) (m : Matrix _ _ F) =
      (((m⁻¹ : GL (Fin n ⊕ Fin n) F)) : Matrix _ _ F) := by
    refine Geo.formAdj_eq_inv_of_isometry (RingHom.id F) hJdet m ?_
    simpa [cpSp_J] using (CFSG.Open.StatedAPI.mem_statedSp_iff.mp hm)
  have h1e : formAdj (RingHom.id F) (cpSp_J n F) (1 - ε) = 1 - ε := by
    have h := Geo.formAdj_add (RingHom.id F) (cpSp_J n F) (1 - ε) ε
    rw [sub_add_cancel, Geo.formAdj_one (RingHom.id F) hJdet, hst] at h
    exact eq_sub_iff_add_eq.mpr h.symm
  have hformX : formAdj (RingHom.id F) (cpSp_J n F) (cpSp_blkVal m ε) =
      cpSp_blkInvVal m ε := by
    rw [cpSp_blkVal, cpSp_blkInvVal, Geo.formAdj_add,
        Geo.formAdj_mul (RingHom.id F) hJdet, hm_inv, hst, h1e, ← hcomm']
  have hinv_val : cpSp_blkInvVal m ε * cpSp_blkVal m ε = 1 :=
    cpSp_blk_inv_mul_val m ε hid hcomm
  have hJJ : cpSp_J n F * (cpSp_J n F)⁻¹ = 1 := Matrix.mul_nonsing_inv _ hJdet
  have hJform : (cpSp_J n F)⁻¹ * Matrix.transpose (cpSp_blkVal m ε) * cpSp_J n F =
      cpSp_blkInvVal m ε := by
    exact hformX
  have hcoee : (cpSp_blk m ε hid hcomm : Matrix _ _ F) = cpSp_blkVal m ε := rfl
  rw [CFSG.Open.StatedAPI.mem_statedSp_iff, hcoee]
  have h1 : Matrix.transpose (cpSp_blkVal m ε) * cpSp_J n F =
      cpSp_J n F * cpSp_blkInvVal m ε := by
    calc Matrix.transpose (cpSp_blkVal m ε) * cpSp_J n F
        = 1 * (Matrix.transpose (cpSp_blkVal m ε) * cpSp_J n F) := (Matrix.one_mul _).symm
      _ = (cpSp_J n F * (cpSp_J n F)⁻¹) *
            (Matrix.transpose (cpSp_blkVal m ε) * cpSp_J n F) := by rw [hJJ]
      _ = cpSp_J n F * ((cpSp_J n F)⁻¹ * Matrix.transpose (cpSp_blkVal m ε) *
            cpSp_J n F) := by simp only [Matrix.mul_assoc]
      _ = cpSp_J n F * cpSp_blkInvVal m ε := by rw [hJform]
  calc Matrix.transpose (cpSp_blkVal m ε) * cpSp_J n F * cpSp_blkVal m ε
      = (cpSp_J n F * cpSp_blkInvVal m ε) * cpSp_blkVal m ε := by rw [h1]
    _ = cpSp_J n F * (cpSp_blkInvVal m ε * cpSp_blkVal m ε) := by rw [Matrix.mul_assoc]
    _ = cpSp_J n F * 1 := by rw [hinv_val]
    _ = cpSp_J n F := Matrix.mul_one _

theorem exists_isComponentOf_glBlockCentralizer_PSp (n : ℕ) (F : Type) [Field F] [Finite F]
    (S : Set (GL (Fin n ⊕ Fin n) F))
    (hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s')
    {J' : Subgroup ↥(CFSG.Open.StatedSp n F)}
    (hJ : IsComponentOf J' ((Subgroup.centralizer S).comap (CFSG.Open.StatedSp n F).subtype)) :
    ∃ ε, IsPrimAdjIdemIn (RingHom.id F)
      (Matrix.fromBlocks 0 1 (-1) 0 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F)
      (Algebra.adjoin F (Units.val '' S)) ε ∧
      IsComponentOf J'
        ⁅glBlockCentralizer (CFSG.Open.StatedSp n F).subtype S ε, glBlockCentralizer
        (CFSG.Open.StatedSp n F).subtype S ε⁆ := by
  have hJdet : IsUnit (cpSp_J n F).det := cpSp_J_isUnit_det
  have hblock : ∀ ε ∈ Algebra.adjoin F (Units.val '' S), IsIdempotentElem ε →
      formAdj (RingHom.id F) (cpSp_J n F) ε = ε →
      ∀ x ∈ (Subgroup.centralizer S).comap (CFSG.Open.StatedSp n F).subtype,
      ∀ y ∈ (Subgroup.centralizer S).comap (CFSG.Open.StatedSp n F).subtype,
        ∃ w : ↥(CFSG.Open.StatedSp n F),
          ((CFSG.Open.StatedSp n F).subtype w : Matrix _ _ F) *
          ((((x : GL (Fin n ⊕ Fin n) F) : Matrix _ _ F) * ε + (1 - ε)) *
            (((y : GL (Fin n ⊕ Fin n) F) : Matrix _ _ F) * ε + (1 - ε))) =
          ((((y : GL (Fin n ⊕ Fin n) F) : Matrix _ _ F) * ε + (1 - ε)) *
            (((x : GL (Fin n ⊕ Fin n) F) : Matrix _ _ F) * ε + (1 - ε))) := by
    intro ε hεA hεid hεst x hx y hy
    have hmx_comm : ((x : GL (Fin n ⊕ Fin n) F) : Matrix _ _ F) * ε =
        ε * ((x : GL (Fin n ⊕ Fin n) F) : Matrix _ _ F) :=
      cpSp_mem_adjoin_comm (fun s hs => by
        have h := Subgroup.mem_centralizer_iff.mp (Subgroup.mem_comap.mp hx) s hs
        have h' : s * (x : GL (Fin n ⊕ Fin n) F) = (x : GL (Fin n ⊕ Fin n) F) * s := h
        simpa only [Units.val_mul] using
          congrArg (fun u : GL (Fin n ⊕ Fin n) F =>
            (u : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F)) h') hεA
    have hmy_comm : ((y : GL (Fin n ⊕ Fin n) F) : Matrix _ _ F) * ε =
        ε * ((y : GL (Fin n ⊕ Fin n) F) : Matrix _ _ F) :=
      cpSp_mem_adjoin_comm (fun s hs => by
        have h := Subgroup.mem_centralizer_iff.mp (Subgroup.mem_comap.mp hy) s hs
        have h' : s * (y : GL (Fin n ⊕ Fin n) F) = (y : GL (Fin n ⊕ Fin n) F) * s := h
        simpa only [Units.val_mul] using
          congrArg (fun u : GL (Fin n ⊕ Fin n) F =>
            (u : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F)) h') hεA
    let X : GL (Fin n ⊕ Fin n) F := cpSp_blk (x : GL (Fin n ⊕ Fin n) F) ε hεid hmx_comm
    let Y : GL (Fin n ⊕ Fin n) F := cpSp_blk (y : GL (Fin n ⊕ Fin n) F) ε hεid hmy_comm
    have hXsp : X ∈ CFSG.Open.StatedSp n F :=
      cpSp_blk_mem_statedSp (x : GL (Fin n ⊕ Fin n) F) x.2 ε hεid hmx_comm hεst
    have hYsp : Y ∈ CFSG.Open.StatedSp n F :=
      cpSp_blk_mem_statedSp (y : GL (Fin n ⊕ Fin n) F) y.2 ε hεid hmy_comm hεst
    have hcomm : ⁅Y, X⁆ ∈ CFSG.Open.StatedSp n F := by
      rw [commutatorElement_def]
      exact mul_mem (mul_mem (mul_mem hYsp hXsp) (inv_mem hYsp)) (inv_mem hXsp)
    refine ⟨⟨⁅Y, X⁆, hcomm⟩, ?_⟩
    have hgl : (⟨⁅Y, X⁆, hcomm⟩ : ↥(CFSG.Open.StatedSp n F)) * (X * Y) = Y * X := by
      change (⁅Y, X⁆ : GL (Fin n ⊕ Fin n) F) * (X * Y) = Y * X
      rw [commutatorElement_def]
      group
    have hXcoe : (X : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) =
        ((x : GL (Fin n ⊕ Fin n) F) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) *
          ε + (1 - ε) := rfl
    have hYcoe : (Y : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) =
        ((y : GL (Fin n ⊕ Fin n) F) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) *
          ε + (1 - ε) := rfl
    have hcoe := congrArg (fun u : GL (Fin n ⊕ Fin n) F =>
      (u : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F)) hgl
    simp only [Units.val_mul] at hcoe
    rw [hXcoe, hYcoe] at hcoe
    exact hcoe
  obtain ⟨ε, hε, hcomp⟩ :=
    Block.exists_isPrimStarIdemIn_isComponentOf_glBlockCentralizer
      (j := (CFSG.Open.StatedSp n F).subtype) (Subgroup.subtype_injective _)
      S hS (formAdj (RingHom.id F) (cpSp_J n F))
      (Geo.formAdj_one (RingHom.id F) hJdet)
      (fun a _ b _ => Geo.formAdj_add (RingHom.id F) (cpSp_J n F) a b)
      hblock hJ
  exact ⟨ε, (Block.isPrimStarIdemIn_formAdj_iff (RingHom.id F) (cpSp_J n F)
      (Algebra.adjoin F (Units.val '' S)) ε).mp hε, hcomp⟩

end CFSG.StandardType.ClassicalPosition
