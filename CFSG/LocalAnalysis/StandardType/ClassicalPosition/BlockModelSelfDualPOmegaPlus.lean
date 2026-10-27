module

public import CFSG.RankThree.GF2n.Smith81.Orth28Omega
public import CFSG.LocalAnalysis.StandardType.ClassicalPosition.NbrPSU
public import CFSG.LocalAnalysis.StandardType.ClassicalPosition.GeoPOmegaPlusRoot
public import CFSG.LocalAnalysis.StandardType.ClassicalPosition.GeoPOmegaMinusRoot
public import CFSG.ClassicalGroups.Orthogonal.StatedOmegaElementary
public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Inputs141d2
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanParabHub
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T123CBlockOrthA
public import CFSG.RankThree.GF2n.Smith81.Orth28FourPlusModel
public import CFSG.LocalAnalysis.UniquenessCase.UC22P20g
public import CFSG.CGT.Timmesfeld75.Forms
public import CFSG.ClassicalGroups.Orthogonal.RootGroupFixedCard
public import CFSG.GroupTheory.HuppertProduct.Quotient
public import CFSG.HardMathSupport.Solomon.Coordinator.L5Conj
public import CFSG.RankThree.GF2n.Smith81.OrthStmt
public import CFSG.RankThree.GF2n.Smith81.Sec2FStar
public import CFSG.RankThree.GF2n.Smith81.Sec2Stmt
public import CFSG.RankThree.GF2n.Smith81.TiLane
public import CFSG.RankThree.GF2n.Stroth80.Consumers
public import CFSG.RankThree.GF2n.Stroth80.GlobalModel
public import CFSG.RankThree.GF2n.Stroth80.Sec5Comm
public import CFSG.RankThree.GF2n.SupIndepDecomp
public import CFSG.RankThree.GF2n.Tim79CentC
public import CFSG.RankThree.GF2n.Tim79CentL
public import CFSG.RankThree.GF2n.Tim79Mod

public section

namespace CFSG.StandardType.ClassicalPosition

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.RootSystem
  CFSG.Assembly.LowTwoRank CFSG.StandardType CFSG.StandardType.S2MathFi1035Pos

private def bmsdop_geom₁ (k f : ℕ)
    (S : Set (GL (Fin (k + 3) ⊕ Fin (k + 3)) (GaloisField 2 f)))
    (e : Matrix (Fin (k + 3) ⊕ Fin (k + 3)) (Fin (k + 3) ⊕ Fin (k + 3)) (GaloisField 2 f)) :
    Prop :=
  IsIdempotentElem e ∧ e ≠ 0 ∧
    blockDegree (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e = 1 ∧
    IsUnit (LinearMap.toMatrix₂' (GaloisField 2 f)
      (QuadraticMap.polarBilin (Spin.quadPlus (k + 3) (GaloisField 2 f)))).det ∧
    e.rank % 2 = 0

private def bmsdop_geom₂ (k f : ℕ)
    (S : Set (GL (Fin (k + 3) ⊕ Fin (k + 3)) (GaloisField 2 f)))
    (e : Matrix (Fin (k + 3) ⊕ Fin (k + 3)) (Fin (k + 3) ⊕ Fin (k + 3)) (GaloisField 2 f)) :
    Prop :=
  (∀ s ∈ S, ∀ x : (Fin (k + 3) ⊕ Fin (k + 3)) → (GaloisField 2 f),
      Matrix.mulVec e x = x →
      Matrix.mulVec (s : Matrix (Fin (k + 3) ⊕ Fin (k + 3)) (Fin (k + 3) ⊕ Fin (k + 3))
        (GaloisField 2 f)) x = x) ∧
    (∀ x y : (Fin (k + 3) ⊕ Fin (k + 3)) → (GaloisField 2 f),
      Matrix.mulVec e x = x → Matrix.mulVec (1 - e) y = y →
      QuadraticMap.polar (Spin.quadPlus (k + 3) (GaloisField 2 f)) x y = 0) ∧
    (∀ x : (Fin (k + 3) ⊕ Fin (k + 3)) → (GaloisField 2 f), Matrix.mulVec e x = x →
      (∀ y : (Fin (k + 3) ⊕ Fin (k + 3)) → (GaloisField 2 f),
        Matrix.mulVec e y = y →
        QuadraticMap.polar (Spin.quadPlus (k + 3) (GaloisField 2 f)) x y = 0) → x = 0)

private lemma bmsdop_isUnit_det {ι F : Type} [Fintype ι] [DecidableEq ι] [Field F]
    (Q : QuadraticForm F (ι → F))
    (hnd : (QuadraticMap.polarBilin Q).Nondegenerate) :
    IsUnit (LinearMap.toMatrix₂' F (QuadraticMap.polarBilin Q)).det := by
  have h1 : (LinearMap.toMatrix₂' F (QuadraticMap.polarBilin Q)) =
      LinearMap.BilinForm.toMatrix' (QuadraticMap.polarBilin Q) := rfl
  rw [h1]
  exact isUnit_iff_ne_zero.mpr (Matrix.nondegenerate_iff_det_ne_zero.mp
    ((LinearMap.BilinForm.nondegenerate_toMatrix'_iff).mpr hnd))

private lemma bmsdop_polar_eq_dot {ι F : Type} [Fintype ι] [DecidableEq ι] [Field F]
    (Q : QuadraticForm F (ι → F)) (x y : ι → F) :
    QuadraticMap.polar Q x y =
      dotProduct x ((LinearMap.toMatrix₂' F (QuadraticMap.polarBilin Q)).mulVec y) := by
  have h1 : (LinearMap.toMatrix₂' F (QuadraticMap.polarBilin Q)) =
      LinearMap.BilinForm.toMatrix' (QuadraticMap.polarBilin Q) := rfl
  rw [h1]
  rw [← Matrix.toBilin'_apply' (LinearMap.BilinForm.toMatrix' (QuadraticMap.polarBilin Q)) x y,
    Matrix.toBilin'_toMatrix', QuadraticMap.polarBilin_apply_apply]

private lemma bmsdop_formAdj_id {ι F : Type} [Fintype ι] [DecidableEq ι] [Field F]
    (G a : Matrix ι ι F) : formAdj (RingHom.id F) G a = G⁻¹ * a.transpose * G := by
  unfold formAdj
  rw [show a.map (⇑(RingHom.id F)) = a from by ext i j; rfl]

private lemma bmsdop_formAdj_mulVec {ι F : Type} [Fintype ι] [DecidableEq ι] [Field F]
    {G a : Matrix ι ι F} (hG : IsUnit G.det) (y : ι → F) :
    G.mulVec ((formAdj (RingHom.id F) G a).mulVec y) = a.transpose.mulVec (G.mulVec y) := by
  have hmat : G * (G⁻¹ * a.transpose * G) = a.transpose * G := by
    rw [← Matrix.mul_assoc G (G⁻¹ * a.transpose) G,
      ← Matrix.mul_assoc G G⁻¹ a.transpose, Matrix.mul_nonsing_inv G hG, Matrix.one_mul]
  rw [bmsdop_formAdj_id, Matrix.mulVec_mulVec, hmat, Matrix.mulVec_mulVec]

private lemma bmsdop_dotProduct_mulVec_transpose {ι F : Type} [Fintype ι] [CommSemiring F]
    (M : Matrix ι ι F) (x y : ι → F) :
    dotProduct (M.mulVec x) y = dotProduct x (M.transpose.mulVec y) := by
  exact ((Matrix.dotProduct_mulVec x M.transpose y).trans
    (by rw [Matrix.vecMul_transpose])).symm

private lemma bmsdop_formAdj_apply {ι F : Type} [Fintype ι] [DecidableEq ι] [Field F]
    (Q : QuadraticForm F (ι → F))
    (hG : IsUnit (LinearMap.toMatrix₂' F (QuadraticMap.polarBilin Q)).det)
    (a : Matrix ι ι F) (x y : ι → F) :
    QuadraticMap.polar Q (a.mulVec x) y =
      QuadraticMap.polar Q x ((formAdj (RingHom.id F)
        (LinearMap.toMatrix₂' F (QuadraticMap.polarBilin Q)) a).mulVec y) := by
  rw [bmsdop_polar_eq_dot Q, bmsdop_polar_eq_dot Q,
    bmsdop_dotProduct_mulVec_transpose a x
      ((LinearMap.toMatrix₂' F (QuadraticMap.polarBilin Q)).mulVec y),
    bmsdop_formAdj_mulVec hG y]

private lemma bmsdop_polar_selfAdjoint {ι F : Type} [Fintype ι] [DecidableEq ι] [Field F]
    (Q : QuadraticForm F (ι → F))
    (hG : IsUnit (LinearMap.toMatrix₂' F (QuadraticMap.polarBilin Q)).det)
    {E : Matrix ι ι F}
    (hE : formAdj (RingHom.id F)
      (LinearMap.toMatrix₂' F (QuadraticMap.polarBilin Q)) E = E) (x y : ι → F) :
    QuadraticMap.polar Q (E.mulVec x) y = QuadraticMap.polar Q x (E.mulVec y) := by
  rw [bmsdop_formAdj_apply Q hG E x y, hE]

private lemma bmsdop_even_rank_of_selfAdjoint_idem {ι F : Type} [Fintype ι] [DecidableEq ι]
    [Field F] [CharP F 2] (Q : QuadraticForm F (ι → F))
    (hnd : (QuadraticMap.polarBilin Q).Nondegenerate)
    {e : Matrix ι ι F} (hidem : IsIdempotentElem e)
    (hE : formAdj (RingHom.id F)
      (LinearMap.toMatrix₂' F (QuadraticMap.polarBilin Q)) e = e) :
    e.rank % 2 = 0 := by
  let W : Submodule F (ι → F) := LinearMap.range (Matrix.toLin' e)
  have hdet : IsUnit (LinearMap.toMatrix₂' F (QuadraticMap.polarBilin Q)).det :=
    bmsdop_isUnit_det Q hnd
  have hself : ∀ x y : ι → F,
      QuadraticMap.polar Q (e.mulVec x) y = QuadraticMap.polar Q x (e.mulVec y) :=
    fun x y => bmsdop_polar_selfAdjoint Q hdet hE x y
  have haltB : (QuadraticMap.polarBilin Q).IsAlt := by
    intro x
    rw [QuadraticMap.polarBilin_apply_apply, QuadraticMap.polar_self, two_nsmul,
      CharTwo.add_self_eq_zero]
  have hdisj : Disjoint W (LinearMap.BilinForm.orthogonal (QuadraticMap.polarBilin Q) W) := by
    rw [disjoint_iff_inf_le]
    intro x hx
    rw [Submodule.mem_inf] at hx
    obtain ⟨hxW, hxorth⟩ := hx
    rw [Submodule.mem_bot]
    rw [show W = LinearMap.range (Matrix.toLin' e) from rfl] at hxW
    obtain ⟨a, ha⟩ := LinearMap.mem_range.mp hxW
    have ha' : e.mulVec a = x := by rw [← ha, Matrix.toLin'_apply]
    have hxorth' : ∀ n ∈ W, (QuadraticMap.polarBilin Q) n x = 0 :=
      LinearMap.BilinForm.mem_orthogonal_iff.mp hxorth
    have hBx : ∀ y : ι → F, (QuadraticMap.polarBilin Q) x y = 0 := by
      intro y
      have hdecomp : y = e.mulVec y + (1 - e).mulVec y := by
        have h1 : (e + (1 - e) : Matrix ι ι F) = 1 := by abel
        calc y = (1 : Matrix ι ι F).mulVec y := (Matrix.one_mulVec y).symm
          _ = (e + (1 - e)).mulVec y := by rw [h1]
          _ = e.mulVec y + (1 - e).mulVec y := Matrix.add_mulVec e (1 - e) y
      have he1e : e * (1 - e) = 0 := by
        rw [Matrix.mul_sub, Matrix.mul_one, hidem.eq, sub_self]
      have hker : e.mulVec ((1 - e).mulVec y) = 0 := by
        rw [Matrix.mulVec_mulVec, he1e, Matrix.zero_mulVec]
      have hmem_e : e.mulVec y ∈ W := by
        rw [show W = LinearMap.range (Matrix.toLin' e) from rfl]
        exact LinearMap.mem_range.mpr ⟨y, by rw [Matrix.toLin'_apply]⟩
      have h1e : (QuadraticMap.polarBilin Q) x (e.mulVec y) = 0 := by
        have h := hxorth' (e.mulVec y) hmem_e
        rw [QuadraticMap.polarBilin_apply_apply] at h ⊢
        rw [QuadraticMap.polar_comm, h]
      have h2e : (QuadraticMap.polarBilin Q) x ((1 - e).mulVec y) = 0 := by
        have hss := hself a ((1 - e).mulVec y)
        calc (QuadraticMap.polarBilin Q) x ((1 - e).mulVec y)
            = QuadraticMap.polar Q (e.mulVec a) ((1 - e).mulVec y) := by
              rw [← ha', QuadraticMap.polarBilin_apply_apply]
          _ = QuadraticMap.polar Q a (e.mulVec ((1 - e).mulVec y)) := hss
          _ = 0 := by rw [hker, QuadraticMap.polar_zero_right]
      rw [hdecomp, map_add, h1e, h2e, add_zero]
    exact hnd.1 x hBx
  have hndW : (LinearMap.BilinForm.restrict (QuadraticMap.polarBilin Q) W).Nondegenerate :=
    LinearMap.BilinForm.nondegenerate_restrict_of_disjoint_orthogonal
      (QuadraticMap.polarBilin Q) haltB.isRefl hdisj
  have haltW : (LinearMap.BilinForm.restrict (QuadraticMap.polarBilin Q) W).IsAlt := by
    intro x
    rw [LinearMap.BilinForm.restrict_apply, LinearMap.domRestrict_apply]
    exact haltB x
  have heven : Even (Module.finrank F W) :=
    LinearMap.BilinForm.IsAlt.even_finrank haltW hndW
  have hrank : e.rank = Module.finrank F W := by
    rw [show W = LinearMap.range (Matrix.toLin' e) from rfl, Matrix.range_toLin' e]
    rw [← Matrix.rank_transpose e, Matrix.rank_eq_finrank_span_row (Matrix.transpose e)]
    rw [show (Matrix.transpose e).row = Matrix.col e from by ext i j; rfl]
  rw [hrank]
  exact Nat.even_iff.mp heven

private theorem bmsdop_block_idem_and_degree
    (k f : ℕ) (S : Set (GL (Fin (k + 3) ⊕ Fin (k + 3)) (GaloisField 2 f)))
    (hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s') (hodd : ∀ s ∈ S, Odd (orderOf s))
    {e : Matrix (Fin (k + 3) ⊕ Fin (k + 3)) (Fin (k + 3) ⊕ Fin (k + 3)) (GaloisField 2 f)}
    (he : IsPrimIdemIn (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e)
    (hadj : formAdj (RingHom.id (GaloisField 2 f))
      (LinearMap.toMatrix₂' (GaloisField 2 f)
      (QuadraticMap.polarBilin (Spin.quadPlus (k + 3) (GaloisField 2 f)))) e = e)
      (hdeg : blockDegree (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e < 2)
    (hnm : ¬
      (e.rank = 4 ∧ ∀ x y : (Fin (k + 3) ⊕ Fin (k + 3)) → (GaloisField 2 f), Matrix.mulVec e x = x →
      Matrix.mulVec e y = y →
      (Spin.quadPlus (k + 3) (GaloisField 2 f)) x = 0 → (Spin.quadPlus (k + 3) (GaloisField 2 f)) y
      = 0 → QuadraticMap.polar (Spin.quadPlus (k + 3) (GaloisField 2 f)) x y = 0 → ¬
      LinearIndependent (GaloisField 2 f) ![x, y])) :
    bmsdop_geom₁ k f S e := by
  obtain ⟨heA, heid, hene, _heprim⟩ := he
  refine ⟨heid, hene, ?_, ?_, ?_⟩
  · have hmem : e ∈ (Subalgebra.toSubmodule
        (Algebra.adjoin (GaloisField 2 f) (Units.val '' S))).map
        (LinearMap.mulRight (GaloisField 2 f) e) := by
      refine Submodule.mem_map.mpr ⟨e, heA, ?_⟩
      show e * e = e
      exact heid.eq
    have hMne : (Subalgebra.toSubmodule
        (Algebra.adjoin (GaloisField 2 f) (Units.val '' S))).map
        (LinearMap.mulRight (GaloisField 2 f) e) ≠ ⊥ := by
      intro h
      have hbot : e ∈ (⊥ : Submodule (GaloisField 2 f)
          (Matrix (Fin (k + 3) ⊕ Fin (k + 3)) (Fin (k + 3) ⊕ Fin (k + 3))
            (GaloisField 2 f))) := h ▸ hmem
      rw [Submodule.mem_bot] at hbot
      exact hene hbot
    have hpos : 1 ≤ blockDegree
        (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e := by
      unfold blockDegree
      exact Submodule.one_le_finrank_iff.mpr hMne
    omega
  · exact bmsdop_isUnit_det (Spin.quadPlus (k + 3) (GaloisField 2 f))
      (Spin.nondegenerate_polarBilin_quadPlus (k + 3) (GaloisField 2 f))
  · exact bmsdop_even_rank_of_selfAdjoint_idem (Spin.quadPlus (k + 3) (GaloisField 2 f))
      (Spin.nondegenerate_polarBilin_quadPlus (k + 3) (GaloisField 2 f)) heid hadj

private theorem bmsdop_block_trivial_and_split
    (k f : ℕ) (S : Set (GL (Fin (k + 3) ⊕ Fin (k + 3)) (GaloisField 2 f)))
    (hSU : ∀ s ∈ S, s ∈ (Spin.spinMatrix (Spin.quadPlus (k + 3) (GaloisField 2 f))).range)
    (hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s') (hodd : ∀ s ∈ S, Odd (orderOf s))
    {e : Matrix (Fin (k + 3) ⊕ Fin (k + 3)) (Fin (k + 3) ⊕ Fin (k + 3)) (GaloisField 2 f)}
    (he : IsPrimIdemIn (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e)
    (hadj : formAdj (RingHom.id (GaloisField 2 f))
      (LinearMap.toMatrix₂' (GaloisField 2 f)
      (QuadraticMap.polarBilin (Spin.quadPlus (k + 3) (GaloisField 2 f)))) e = e)
      (hdeg : blockDegree (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e < 2)
    (hnm : ¬
      (e.rank = 4 ∧ ∀ x y : (Fin (k + 3) ⊕ Fin (k + 3)) → (GaloisField 2 f), Matrix.mulVec e x = x →
      Matrix.mulVec e y = y →
      (Spin.quadPlus (k + 3) (GaloisField 2 f)) x = 0 → (Spin.quadPlus (k + 3) (GaloisField 2 f)) y
      = 0 → QuadraticMap.polar (Spin.quadPlus (k + 3) (GaloisField 2 f)) x y = 0 → ¬
      LinearIndependent (GaloisField 2 f) ![x, y])) :
    bmsdop_geom₂ k f S e := by
  have heA : e ∈ Algebra.adjoin (GaloisField 2 f) (Units.val '' S) := he.1
  have heid : IsIdempotentElem e := he.2.1
  have hene : e ≠ 0 := he.2.2.1
  have hdet : IsUnit (LinearMap.toMatrix₂' (GaloisField 2 f)
      (QuadraticMap.polarBilin (Spin.quadPlus (k + 3) (GaloisField 2 f)))).det :=
    bmsdop_isUnit_det (Spin.quadPlus (k + 3) (GaloisField 2 f))
      (Spin.nondegenerate_polarBilin_quadPlus (k + 3) (GaloisField 2 f))
  have hndV : (QuadraticMap.polarBilin (Spin.quadPlus (k + 3) (GaloisField 2 f))).Nondegenerate :=
    Spin.nondegenerate_polarBilin_quadPlus (k + 3) (GaloisField 2 f)
  have hself : ∀ x y : (Fin (k + 3) ⊕ Fin (k + 3)) → (GaloisField 2 f),
      QuadraticMap.polar (Spin.quadPlus (k + 3) (GaloisField 2 f)) (e.mulVec x) y =
        QuadraticMap.polar (Spin.quadPlus (k + 3) (GaloisField 2 f)) x (e.mulVec y) :=
    fun x y => bmsdop_polar_selfAdjoint (Spin.quadPlus (k + 3) (GaloisField 2 f)) hdet hadj x y
  have he1e : e * (1 - e) = 0 := by
    rw [Matrix.mul_sub, Matrix.mul_one, heid.eq, sub_self]
  have hnondeg : ∀ x : (Fin (k + 3) ⊕ Fin (k + 3)) → (GaloisField 2 f),
      e.mulVec x = x →
      (∀ y : (Fin (k + 3) ⊕ Fin (k + 3)) → (GaloisField 2 f), e.mulVec y = y →
        QuadraticMap.polar (Spin.quadPlus (k + 3) (GaloisField 2 f)) x y = 0) → x = 0 := by
    intro x hx hxorth
    have hBx : ∀ y, QuadraticMap.polar (Spin.quadPlus (k + 3) (GaloisField 2 f)) x y = 0 := by
      intro y
      have hdecomp : y = e.mulVec y + (1 - e).mulVec y := by
        have h1 : (e + (1 - e) : Matrix _ _ (GaloisField 2 f)) = 1 := by abel
        calc y = (1 : Matrix _ _ (GaloisField 2 f)).mulVec y := (Matrix.one_mulVec y).symm
          _ = (e + (1 - e)).mulVec y := by rw [h1]
          _ = e.mulVec y + (1 - e).mulVec y := Matrix.add_mulVec e (1 - e) y
      have h1 : QuadraticMap.polar (Spin.quadPlus (k + 3) (GaloisField 2 f)) x (e.mulVec y) = 0 :=
        hxorth (e.mulVec y) (by rw [Matrix.mulVec_mulVec, heid.eq])
      have h2 : QuadraticMap.polar (Spin.quadPlus (k + 3) (GaloisField 2 f)) x
          ((1 - e).mulVec y) = 0 := by
        calc QuadraticMap.polar (Spin.quadPlus (k + 3) (GaloisField 2 f)) x ((1 - e).mulVec y)
            = QuadraticMap.polar (Spin.quadPlus (k + 3) (GaloisField 2 f)) (e.mulVec x)
                ((1 - e).mulVec y) := by rw [hx]
          _ = QuadraticMap.polar (Spin.quadPlus (k + 3) (GaloisField 2 f)) x
                (e.mulVec ((1 - e).mulVec y)) := hself x _
          _ = QuadraticMap.polar (Spin.quadPlus (k + 3) (GaloisField 2 f)) x 0 := by
                rw [Matrix.mulVec_mulVec, he1e, Matrix.zero_mulVec]
          _ = 0 := by rw [QuadraticMap.polar_zero_right]
      rw [hdecomp, QuadraticMap.polar_add_right, h1, h2, add_zero]
    exact hndV.1 x hBx
  have horth : ∀ x y : (Fin (k + 3) ⊕ Fin (k + 3)) → (GaloisField 2 f), e.mulVec x = x →
      (1 - e).mulVec y = y →
      QuadraticMap.polar (Spin.quadPlus (k + 3) (GaloisField 2 f)) x y = 0 := by
    intro x y hx hy
    have hey : e.mulVec y = 0 := by
      rw [← hy, Matrix.mulVec_mulVec, he1e, Matrix.zero_mulVec]
    calc QuadraticMap.polar (Spin.quadPlus (k + 3) (GaloisField 2 f)) x y
        = QuadraticMap.polar (Spin.quadPlus (k + 3) (GaloisField 2 f)) (e.mulVec x) y := by
            rw [hx]
      _ = QuadraticMap.polar (Spin.quadPlus (k + 3) (GaloisField 2 f)) x (e.mulVec y) :=
            hself x y
      _ = QuadraticMap.polar (Spin.quadPlus (k + 3) (GaloisField 2 f)) x 0 := by rw [hey]
      _ = 0 := by rw [QuadraticMap.polar_zero_right]
  have htriv : ∀ s ∈ S, ∀ x : (Fin (k + 3) ⊕ Fin (k + 3)) → (GaloisField 2 f),
      e.mulVec x = x → (s : Matrix _ _ (GaloisField 2 f)).mulVec x = x := by
    intro s hs x hx
    have hsQ : ∀ v : (Fin (k + 3) ⊕ Fin (k + 3)) → (GaloisField 2 f),
        (Spin.quadPlus (k + 3) (GaloisField 2 f)) ((s : Matrix _ _ (GaloisField 2 f)).mulVec v) =
          (Spin.quadPlus (k + 3) (GaloisField 2 f)) v := by
      intro v
      obtain ⟨g, rfl⟩ := hSU s hs
      rw [Spin.spinMatrix_mulVec, Spin.map_spinAction]
    have hsB : ∀ u v : (Fin (k + 3) ⊕ Fin (k + 3)) → (GaloisField 2 f),
        QuadraticMap.polar (Spin.quadPlus (k + 3) (GaloisField 2 f))
          ((s : Matrix _ _ (GaloisField 2 f)).mulVec u)
          ((s : Matrix _ _ (GaloisField 2 f)).mulVec v) =
        QuadraticMap.polar (Spin.quadPlus (k + 3) (GaloisField 2 f)) u v := by
      intro u v
      rw [QuadraticMap.polar, QuadraticMap.polar, ← Matrix.mulVec_add, hsQ (u + v), hsQ u, hsQ v]
    have hgeom := bmsdop_block_idem_and_degree k f S hS hodd he hadj hdeg hnm
    have hdeg1 : blockDegree (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e = 1 :=
      hgeom.2.2.1
    have hmem : e ∈ (Subalgebra.toSubmodule
        (Algebra.adjoin (GaloisField 2 f) (Units.val '' S))).map
        (LinearMap.mulRight (GaloisField 2 f) e) := by
      refine Submodule.mem_map.mpr ⟨e, heA, ?_⟩
      show e * e = e
      exact heid.eq
    have hspan : (Subalgebra.toSubmodule
        (Algebra.adjoin (GaloisField 2 f) (Units.val '' S))).map
        (LinearMap.mulRight (GaloisField 2 f) e) = Submodule.span (GaloisField 2 f) {e} :=
      eq_span_singleton_of_mem_of_finrank_eq_one hdeg1 hmem hene
    have hsA : (s : Matrix _ _ (GaloisField 2 f)) ∈
        Algebra.adjoin (GaloisField 2 f) (Units.val '' S) :=
      Algebra.subset_adjoin ⟨s, hs, rfl⟩
    have hseM : (s : Matrix _ _ (GaloisField 2 f)) * e ∈ (Subalgebra.toSubmodule
        (Algebra.adjoin (GaloisField 2 f) (Units.val '' S))).map
        (LinearMap.mulRight (GaloisField 2 f) e) :=
      Submodule.mem_map.mpr ⟨(s : Matrix _ _ (GaloisField 2 f)), hsA, rfl⟩
    rw [hspan] at hseM
    obtain ⟨lam, hlam⟩ := Submodule.mem_span_singleton.mp hseM
    have hscalar : ∀ z : (Fin (k + 3) ⊕ Fin (k + 3)) → (GaloisField 2 f),
        e.mulVec z = z → (s : Matrix _ _ (GaloisField 2 f)).mulVec z = lam • z := by
      intro z hz
      calc (s : Matrix _ _ (GaloisField 2 f)).mulVec z
          = (s : Matrix _ _ (GaloisField 2 f)).mulVec (e.mulVec z) := by rw [hz]
        _ = ((s : Matrix _ _ (GaloisField 2 f)) * e).mulVec z := by rw [Matrix.mulVec_mulVec]
        _ = (lam • e).mulVec z := by rw [← hlam]
        _ = lam • (e.mulVec z) := by rw [Matrix.smul_mulVec]
        _ = lam • z := by rw [hz]
    have hlin : Matrix.toLin' e ≠ 0 := by
      intro h
      exact hene (Matrix.toLin'.injective (by rw [h, map_zero]))
    have hex : ∃ v, (Matrix.toLin' e) v ≠ 0 := by
      by_contra h
      apply hlin
      refine LinearMap.ext fun v => ?_
      show (Matrix.toLin' e) v = 0
      by_contra hv
      exact h ⟨v, hv⟩
    obtain ⟨v, hv⟩ := hex
    have hx0 : e.mulVec v ≠ 0 := by
      rwa [Matrix.toLin'_apply] at hv
    have hx0fix : e.mulVec (e.mulVec v) = e.mulVec v := by
      rw [Matrix.mulVec_mulVec, heid.eq]
    have hy : ∃ y, e.mulVec y = y ∧
        QuadraticMap.polar (Spin.quadPlus (k + 3) (GaloisField 2 f)) (e.mulVec v) y ≠ 0 := by
      by_contra h
      apply hx0
      apply hnondeg (e.mulVec v) hx0fix
      intro y hy'
      by_contra hB
      exact h ⟨y, hy', hB⟩
    obtain ⟨y, hyfix, hBy⟩ := hy
    have hlam2 : lam * lam = 1 := by
      have h1 : QuadraticMap.polar (Spin.quadPlus (k + 3) (GaloisField 2 f)) (e.mulVec v) y =
          (lam * lam) • QuadraticMap.polar (Spin.quadPlus (k + 3) (GaloisField 2 f))
            (e.mulVec v) y := by
        calc QuadraticMap.polar (Spin.quadPlus (k + 3) (GaloisField 2 f)) (e.mulVec v) y
            = QuadraticMap.polar (Spin.quadPlus (k + 3) (GaloisField 2 f))
                ((s : Matrix _ _ (GaloisField 2 f)).mulVec (e.mulVec v))
                ((s : Matrix _ _ (GaloisField 2 f)).mulVec y) := (hsB (e.mulVec v) y).symm
          _ = QuadraticMap.polar (Spin.quadPlus (k + 3) (GaloisField 2 f))
                (lam • (e.mulVec v)) (lam • y) := by
                rw [hscalar (e.mulVec v) hx0fix, hscalar y hyfix]
          _ = (lam * lam) • QuadraticMap.polar (Spin.quadPlus (k + 3) (GaloisField 2 f))
                (e.mulVec v) y := by
                rw [QuadraticMap.polar_smul_left, QuadraticMap.polar_smul_right, smul_smul]
      have h3 : (lam * lam) * QuadraticMap.polar (Spin.quadPlus (k + 3) (GaloisField 2 f))
          (e.mulVec v) y = QuadraticMap.polar (Spin.quadPlus (k + 3) (GaloisField 2 f))
          (e.mulVec v) y := by
        rw [← smul_eq_mul]
        exact h1.symm
      exact mul_right_cancel₀ hBy (by simpa using h3)
    have hlam1 : lam = 1 := by
      rcases (sq_eq_one_iff.mp (by simpa [sq] using hlam2)) with h | h
      · exact h
      · simpa [CharTwo.neg_eq] using h
    rw [hscalar x hx, hlam1, one_smul]
  exact ⟨htriv, horth, hnondeg⟩

private noncomputable def bmsdop_blockForm (k f : ℕ)
    (e : Matrix (Fin (k + 3) ⊕ Fin (k + 3)) (Fin (k + 3) ⊕ Fin (k + 3)) (GaloisField 2 f)) :
    QuadraticForm (GaloisField 2 f) ↥(LinearMap.range (Matrix.toLin' e)) :=
  (Spin.quadPlus (k + 3) (GaloisField 2 f)).comp (LinearMap.range (Matrix.toLin' e)).subtype

private lemma bmsdop_spinMatrix_commute_adjoin {ι F : Type} [Fintype ι] [DecidableEq ι] [Field F]
    {Q : QuadraticForm F (ι → F)} {S : Set (GL ι F)}
    {u : spinGroup Q} (hu : Spin.spinMatrix Q u ∈ Subgroup.centralizer S)
    (a : Matrix ι ι F) (ha : a ∈ Algebra.adjoin F (Units.val '' S)) :
    (Spin.spinMatrix Q u : Matrix ι ι F) * a = a * (Spin.spinMatrix Q u) := by
  have hgen : Units.val '' S ⊆ Subalgebra.centralizer F {(Spin.spinMatrix Q u : Matrix ι ι F)} := by
    intro y hy
    change y ∈ Subalgebra.centralizer F {(Spin.spinMatrix Q u : Matrix ι ι F)}
    rw [Subalgebra.mem_centralizer_iff]
    intro g hg
    rw [Set.mem_singleton_iff] at hg
    subst hg
    rcases hy with ⟨t, ht, rfl⟩
    have hmem := (Subgroup.mem_centralizer_iff.mp hu) t ht
    have hm : (t : Matrix ι ι F) * (Spin.spinMatrix Q u : Matrix ι ι F) =
        (Spin.spinMatrix Q u : Matrix ι ι F) * (t : Matrix ι ι F) := by
      simpa only [Units.val_mul] using congrArg (fun u : GL ι F => (u : Matrix ι ι F)) hmem
    exact hm.symm
  have hA : Algebra.adjoin F (Units.val '' S) ≤
      Subalgebra.centralizer F {(Spin.spinMatrix Q u : Matrix ι ι F)} :=
    Algebra.adjoin_le hgen
  exact (Subalgebra.mem_centralizer_iff F).mp (hA ha) (Spin.spinMatrix Q u) (Set.mem_singleton _)

private lemma bmsdop_spinMatrix_preserves_block {ι F : Type} [Fintype ι] [DecidableEq ι] [Field F]
    {Q : QuadraticForm F (ι → F)} {S : Set (GL ι F)}
    {e : Matrix ι ι F} (heA : e ∈ Algebra.adjoin F (Units.val '' S))
    (u : ↥(glBlockCentralizer (Spin.spinMatrix Q) S e)) :
    ∀ x, e.mulVec x = x →
      e.mulVec (((Spin.spinMatrix Q (u : spinGroup Q)) : Matrix ι ι F).mulVec x) =
        ((Spin.spinMatrix Q (u : spinGroup Q)) : Matrix ι ι F).mulVec x := by
  intro x hx
  have hu_cent : Spin.spinMatrix Q (u : spinGroup Q) ∈ Subgroup.centralizer S :=
    (Subgroup.mem_inf.mp (Subgroup.mem_comap.mp u.2)).1
  have hcomm := bmsdop_spinMatrix_commute_adjoin hu_cent e heA
  rw [Matrix.mulVec_mulVec, hcomm.symm, ← Matrix.mulVec_mulVec, hx]

private lemma bmsdop_blockForm_polar (k f : ℕ)
    (e : Matrix (Fin (k + 3) ⊕ Fin (k + 3)) (Fin (k + 3) ⊕ Fin (k + 3)) (GaloisField 2 f))
    (x y : ↥(LinearMap.range (Matrix.toLin' e))) :
    (QuadraticMap.polarBilin (bmsdop_blockForm k f e)) x y =
      QuadraticMap.polar (Spin.quadPlus (k + 3) (GaloisField 2 f))
        (x : (Fin (k + 3) ⊕ Fin (k + 3)) → (GaloisField 2 f))
        (y : (Fin (k + 3) ⊕ Fin (k + 3)) → (GaloisField 2 f)) := by
  simp only [bmsdop_blockForm, QuadraticMap.polarBilin_comp, LinearMap.compl₁₂_apply,
    QuadraticMap.polarBilin_apply_apply]
  rfl

private theorem bmsdop_hnd_W (k f : ℕ)
    (S : Set (GL (Fin (k + 3) ⊕ Fin (k + 3)) (GaloisField 2 f)))
    (e : Matrix (Fin (k + 3) ⊕ Fin (k + 3)) (Fin (k + 3) ⊕ Fin (k + 3)) (GaloisField 2 f))
    (hid : IsIdempotentElem e) (h2 : bmsdop_geom₂ k f S e) :
    (QuadraticMap.polarBilin (bmsdop_blockForm k f e)).Nondegenerate := by
  constructor
  · intro x hx
    apply Subtype.ext
    apply h2.2.2 (x : (Fin (k + 3) ⊕ Fin (k + 3)) → (GaloisField 2 f))
    · obtain ⟨z, hz⟩ := LinearMap.mem_range.mp x.2
      rw [Matrix.toLin'_apply] at hz
      rw [← hz, Matrix.mulVec_mulVec, hid.eq]
    · intro y hy
      let yW : ↥(LinearMap.range (Matrix.toLin' e)) :=
        ⟨y, ⟨y, by rw [Matrix.toLin'_apply, hy]⟩⟩
      have h := hx yW
      rw [bmsdop_blockForm_polar k f e x yW] at h
      simpa using h
  · intro y hy
    apply Subtype.ext
    apply h2.2.2 (y : (Fin (k + 3) ⊕ Fin (k + 3)) → (GaloisField 2 f))
    · obtain ⟨z, hz⟩ := LinearMap.mem_range.mp y.2
      rw [Matrix.toLin'_apply] at hz
      rw [← hz, Matrix.mulVec_mulVec, hid.eq]
    · intro x hx
      let xW : ↥(LinearMap.range (Matrix.toLin' e)) :=
        ⟨x, ⟨x, by rw [Matrix.toLin'_apply, hx]⟩⟩
      have h := hy xW
      rw [bmsdop_blockForm_polar k f e xW y] at h
      rw [QuadraticMap.polar_comm]
      simpa using h

private noncomputable abbrev bmsdop_Q (k f : ℕ) :
    QuadraticForm (GaloisField 2 f) ((Fin (k + 3) ⊕ Fin (k + 3)) → GaloisField 2 f) :=
  Spin.quadPlus (k + 3) (GaloisField 2 f)

private noncomputable abbrev bmsdop_W (k f : ℕ)
    (e : Matrix (Fin (k + 3) ⊕ Fin (k + 3)) (Fin (k + 3) ⊕ Fin (k + 3)) (GaloisField 2 f)) :
    Submodule (GaloisField 2 f) ((Fin (k + 3) ⊕ Fin (k + 3)) → GaloisField 2 f) :=
  LinearMap.range (Matrix.toLin' e)

private noncomputable abbrev bmsdop_W' (k f : ℕ)
    (e : Matrix (Fin (k + 3) ⊕ Fin (k + 3)) (Fin (k + 3) ⊕ Fin (k + 3)) (GaloisField 2 f)) :
    Submodule (GaloisField 2 f) ((Fin (k + 3) ⊕ Fin (k + 3)) → GaloisField 2 f) :=
  LinearMap.range (Matrix.toLin' (1 - e))

private noncomputable abbrev bmsdop_Ge (k f : ℕ)
    (S : Set (GL (Fin (k + 3) ⊕ Fin (k + 3)) (GaloisField 2 f)))
    (e : Matrix (Fin (k + 3) ⊕ Fin (k + 3)) (Fin (k + 3) ⊕ Fin (k + 3)) (GaloisField 2 f)) :
    Subgroup ↥(spinGroup (bmsdop_Q k f)) :=
  glBlockCentralizer (Spin.spinMatrix (bmsdop_Q k f)) S e

private def bmsdop_ExtProps (k f : ℕ) (S : Set (GL (Fin (k + 3) ⊕ Fin (k + 3))
      (GaloisField 2 f)))
    (e : Matrix (Fin (k + 3) ⊕ Fin (k + 3)) (Fin (k + 3) ⊕ Fin (k + 3)) (GaloisField 2 f))
    {Vstd : Type} [AddCommGroup Vstd] [Module (GaloisField 2 f) Vstd]
    [FiniteDimensional (GaloisField 2 f) Vstd]
    (Qstd : QuadraticForm (GaloisField 2 f) Vstd)
    (hnd_std : (QuadraticMap.polarBilin Qstd).Nondegenerate)
    (θ : Vstd ≃ₗ[GaloisField 2 f] ↥(bmsdop_W k f e))
    (E : (Vstd ≃ₗ[GaloisField 2 f] Vstd) →*
        (((Fin (k + 3) ⊕ Fin (k + 3)) → GaloisField 2 f) ≃ₗ[GaloisField 2 f]
          ((Fin (k + 3) ⊕ Fin (k + 3)) → GaloisField 2 f))) : Prop :=
  (∀ g, g ∈ TauCeti.QuadraticMap.orthogonalGroup Qstd →
      E g ∈ TauCeti.QuadraticMap.orthogonalGroup (bmsdop_Q k f)) ∧
  Function.Injective E ∧
  (∀ g v, v ∈ bmsdop_W' k f e → E g v = v) ∧
  (∀ g x, E g (θ x) = θ (g x)) ∧
  (∀ g, E g ∈ CFSG.RankThree.OrthogonalInvolutions.omegaGroup (bmsdop_Q k f)
          (Spin.nondegenerate_polarBilin_quadPlus (k + 3) (GaloisField 2 f)) ↔
        g ∈ CFSG.RankThree.OrthogonalInvolutions.omegaGroup Qstd hnd_std)

private theorem bmsdop_theta
    (k f : ℕ) (S : Set (GL (Fin (k + 3) ⊕ Fin (k + 3)) (GaloisField 2 f)))
    {e : Matrix (Fin (k + 3) ⊕ Fin (k + 3)) (Fin (k + 3) ⊕ Fin (k + 3)) (GaloisField 2 f)}
    (h1 : bmsdop_geom₁ k f S e) (h2 : bmsdop_geom₂ k f S e)
    (ρ : ℕ) (hρ : e.rank = 2 * ρ) (hρ1 : 1 ≤ ρ) :
    (∃ θ : (Fin ρ ⊕ Fin ρ → GaloisField 2 f) ≃ₗ[GaloisField 2 f] ↥(bmsdop_W k f e),
        ∀ x, (bmsdop_blockForm k f e) (θ x) = (Spin.quadPlus ρ (GaloisField 2 f)) x) ∨
    (∃ (β γ : GaloisField 2 f) (_hirr : ∀ s : GaloisField 2 f, s ^ 2 + β * s + γ ≠ 0)
        (θ : (Fin (ρ - 1) ⊕ Fin (ρ - 1) ⊕ Fin 2 → GaloisField 2 f) ≃ₗ[GaloisField 2 f]
              ↥(bmsdop_W k f e)),
        ∀ x, (bmsdop_blockForm k f e) (θ x) = (Spin.quadMinus ρ (GaloisField 2 f) β γ) x) := by
  have hnd : (QuadraticMap.polarBilin (bmsdop_blockForm k f e)).Nondegenerate :=
    bmsdop_hnd_W k f S e h1.1 h2
  have hrank : e.rank = Module.finrank (GaloisField 2 f) ↥(bmsdop_W k f e) := by
    rw [show bmsdop_W k f e = LinearMap.range (Matrix.toLin' e) from rfl]
    rw [Matrix.rank_eq_finrank_range_toLin e (Pi.basisFun (GaloisField 2 f) _)
      (Pi.basisFun (GaloisField 2 f) _), Matrix.toLin_eq_toLin']
  have hfin : Module.finrank (GaloisField 2 f) ↥(bmsdop_W k f e) = 2 * ρ := by
    rw [← hrank, hρ]
  obtain ⟨-, -, hnf, -⟩ :=
    CFSG.ComponentClassification.UnbalancedCatalog.finite_even_regular_quadratic_normal_forms
      (bmsdop_blockForm k f e) hnd
  rcases hnf ρ hρ1 hfin with ⟨b, hb⟩ | ⟨β, γ, _hβ, hirr, b, hb⟩
  · left
    refine ⟨b.equivFun.symm, fun x => ?_⟩
    rw [Module.Basis.equivFun_symm_apply, Fintype.sum_sum_type]
    rw [hb (fun i => x (.inl i)) (fun i => x (.inr i)), Spin.quadPlus_apply]
  · right
    refine ⟨β, γ, hirr, b.equivFun.symm, fun x => ?_⟩
    rw [Module.Basis.equivFun_symm_apply]
    simp only [Fintype.sum_sum_type, Fin.sum_univ_two]
    rw [Spin.quadMinus_apply]
    simpa only [add_assoc] using hb (fun i => x (.inl i)) (fun i => x (.inr (.inl i)))
      (x (.inr (.inr 0))) (x (.inr (.inr 1)))

private lemma bmsdop_mulVecLin_idem {k f : ℕ}
    {e : Matrix (Fin (k + 3) ⊕ Fin (k + 3)) (Fin (k + 3) ⊕ Fin (k + 3)) (GaloisField 2 f)}
    (hid : IsIdempotentElem e) : IsIdempotentElem (Matrix.mulVecLin e) := by
  show Matrix.mulVecLin e ∘ₗ Matrix.mulVecLin e = Matrix.mulVecLin e
  rw [← Matrix.mulVecLin_mul, hid.eq]

private lemma bmsdop_mulVecLin_add (k f : ℕ)
    (e : Matrix (Fin (k + 3) ⊕ Fin (k + 3)) (Fin (k + 3) ⊕ Fin (k + 3)) (GaloisField 2 f)) :
    Matrix.mulVecLin e + Matrix.mulVecLin (1 - e) =
      (LinearMap.id : ((Fin (k + 3) ⊕ Fin (k + 3)) → (GaloisField 2 f)) →ₗ[GaloisField 2 f]
        ((Fin (k + 3) ⊕ Fin (k + 3)) → (GaloisField 2 f))) := by
  rw [← Matrix.mulVecLin_add, add_sub_cancel, Matrix.mulVecLin_one]

private lemma bmsdop_ker_e_eq_range_one_sub {k f : ℕ}
    {e : Matrix (Fin (k + 3) ⊕ Fin (k + 3)) (Fin (k + 3) ⊕ Fin (k + 3)) (GaloisField 2 f)}
    (hid : IsIdempotentElem e) :
    LinearMap.ker (Matrix.mulVecLin e) = LinearMap.range (Matrix.mulVecLin (1 - e)) := by
  have hE : IsIdempotentElem (Matrix.mulVecLin e) := bmsdop_mulVecLin_idem hid
  have h := LinearMap.IsIdempotentElem.ker_eq_range_one_sub hE
  have hsub : Matrix.mulVecLin (1 - e) = 1 - Matrix.mulVecLin e := by
    rw [eq_sub_iff_add_eq]
    exact (add_comm _ _).trans (bmsdop_mulVecLin_add k f e)
  rw [h, hsub]

private lemma bmsdop_isCompl_W {k f : ℕ}
    {e : Matrix (Fin (k + 3) ⊕ Fin (k + 3)) (Fin (k + 3) ⊕ Fin (k + 3)) (GaloisField 2 f)}
    (hid : IsIdempotentElem e) : IsCompl (bmsdop_W k f e) (bmsdop_W' k f e) := by
  have hE : IsIdempotentElem (Matrix.mulVecLin e) := bmsdop_mulVecLin_idem hid
  have h := LinearMap.IsIdempotentElem.isCompl hE
  rw [bmsdop_ker_e_eq_range_one_sub hid] at h
  exact h

private lemma bmsdop_mem_W_iff {k f : ℕ}
    {e : Matrix (Fin (k + 3) ⊕ Fin (k + 3)) (Fin (k + 3) ⊕ Fin (k + 3)) (GaloisField 2 f)}
    (hid : IsIdempotentElem e) (v : (Fin (k + 3) ⊕ Fin (k + 3)) → (GaloisField 2 f)) :
    v ∈ bmsdop_W k f e ↔ e.mulVec v = v := by
  rw [bmsdop_W, LinearMap.mem_range]
  constructor
  · rintro ⟨z, rfl⟩
    rw [Matrix.toLin'_apply, Matrix.mulVec_mulVec, hid.eq]
  · intro hv
    exact ⟨v, by rw [Matrix.toLin'_apply, hv]⟩

private lemma bmsdop_mem_W'_iff {k f : ℕ}
    {e : Matrix (Fin (k + 3) ⊕ Fin (k + 3)) (Fin (k + 3) ⊕ Fin (k + 3)) (GaloisField 2 f)}
    (hid : IsIdempotentElem e) (v : (Fin (k + 3) ⊕ Fin (k + 3)) → (GaloisField 2 f)) :
    v ∈ bmsdop_W' k f e ↔ (1 - e).mulVec v = v := by
  have hid' : IsIdempotentElem (1 - e) := by
    show (1 - e) * (1 - e) = 1 - e
    rw [Matrix.sub_mul, Matrix.one_mul, Matrix.mul_sub, Matrix.mul_one, hid.eq]
    abel
  rw [bmsdop_W', LinearMap.mem_range]
  constructor
  · rintro ⟨z, rfl⟩
    rw [Matrix.toLin'_apply, Matrix.mulVec_mulVec, hid'.eq]
  · intro hv
    exact ⟨v, by rw [Matrix.toLin'_apply, hv]⟩

private abbrev bmsdop_V (k f : ℕ) := (Fin (k + 3) ⊕ Fin (k + 3)) → GaloisField 2 f

private noncomputable def bmsdop_glueG (k f : ℕ)
    (S : Set (GL (Fin (k + 3) ⊕ Fin (k + 3)) (GaloisField 2 f)))
    {e : Matrix (Fin (k + 3) ⊕ Fin (k + 3)) (Fin (k + 3) ⊕ Fin (k + 3)) (GaloisField 2 f)}
    (h1 : bmsdop_geom₁ k f S e)
    {Vstd : Type} [AddCommGroup Vstd] [Module (GaloisField 2 f) Vstd]
    (θ : Vstd ≃ₗ[GaloisField 2 f] ↥(bmsdop_W k f e))
    (g : Vstd ≃ₗ[GaloisField 2 f] Vstd) :
    ((↥(bmsdop_W k f e) × ↥(bmsdop_W' k f e)) ≃ₗ[GaloisField 2 f]
      (↥(bmsdop_W k f e) × ↥(bmsdop_W' k f e))) :=
  (θ.symm.trans (g.trans θ)).prodCongr
    (LinearEquiv.refl (GaloisField 2 f) ↥(bmsdop_W' k f e))

private lemma bmsdop_glueG_one (k f : ℕ)
    (S : Set (GL (Fin (k + 3) ⊕ Fin (k + 3)) (GaloisField 2 f)))
    {e : Matrix (Fin (k + 3) ⊕ Fin (k + 3)) (Fin (k + 3) ⊕ Fin (k + 3)) (GaloisField 2 f)}
    (h1 : bmsdop_geom₁ k f S e)
    {Vstd : Type} [AddCommGroup Vstd] [Module (GaloisField 2 f) Vstd]
    (θ : Vstd ≃ₗ[GaloisField 2 f] ↥(bmsdop_W k f e)) :
    bmsdop_glueG k f S h1 θ (1 : Vstd ≃ₗ[GaloisField 2 f] Vstd) = 1 := by
  ext x <;> simp only [bmsdop_glueG, LinearEquiv.prodCongr_apply, LinearEquiv.trans_apply,
    LinearEquiv.refl_trans, LinearEquiv.apply_symm_apply, LinearEquiv.one_eq_refl,
    LinearEquiv.refl_apply, Prod.mk.eta]

private lemma bmsdop_glueG_mul (k f : ℕ)
    (S : Set (GL (Fin (k + 3) ⊕ Fin (k + 3)) (GaloisField 2 f)))
    {e : Matrix (Fin (k + 3) ⊕ Fin (k + 3)) (Fin (k + 3) ⊕ Fin (k + 3)) (GaloisField 2 f)}
    (h1 : bmsdop_geom₁ k f S e)
    {Vstd : Type} [AddCommGroup Vstd] [Module (GaloisField 2 f) Vstd]
    (θ : Vstd ≃ₗ[GaloisField 2 f] ↥(bmsdop_W k f e))
    (g h : Vstd ≃ₗ[GaloisField 2 f] Vstd) :
    bmsdop_glueG k f S h1 θ (g * h) =
      bmsdop_glueG k f S h1 θ g * bmsdop_glueG k f S h1 θ h := by
  ext x <;> simp only [bmsdop_glueG, LinearEquiv.prodCongr_apply, LinearEquiv.trans_apply,
    LinearEquiv.mul_apply, LinearEquiv.symm_apply_apply, LinearEquiv.refl_apply, Prod.mk.eta]

private noncomputable def bmsdop_glueFun (k f : ℕ)
    (S : Set (GL (Fin (k + 3) ⊕ Fin (k + 3)) (GaloisField 2 f)))
    {e : Matrix (Fin (k + 3) ⊕ Fin (k + 3)) (Fin (k + 3) ⊕ Fin (k + 3)) (GaloisField 2 f)}
    (h1 : bmsdop_geom₁ k f S e)
    {Vstd : Type} [AddCommGroup Vstd] [Module (GaloisField 2 f) Vstd]
    [FiniteDimensional (GaloisField 2 f) Vstd]
    (θ : Vstd ≃ₗ[GaloisField 2 f] ↥(bmsdop_W k f e))
    (g : Vstd ≃ₗ[GaloisField 2 f] Vstd) :
    bmsdop_V k f ≃ₗ[GaloisField 2 f] bmsdop_V k f :=
  let D := Submodule.prodEquivOfIsCompl (bmsdop_W k f e) (bmsdop_W' k f e)
    (bmsdop_isCompl_W h1.1)
  let G := (θ.symm.trans (g.trans θ)).prodCongr
    (LinearEquiv.refl (GaloisField 2 f) ↥(bmsdop_W' k f e))
  D.symm.trans (G.trans D)

private lemma bmsdop_glueFun_one (k f : ℕ)
    (S : Set (GL (Fin (k + 3) ⊕ Fin (k + 3)) (GaloisField 2 f)))
    {e : Matrix (Fin (k + 3) ⊕ Fin (k + 3)) (Fin (k + 3) ⊕ Fin (k + 3)) (GaloisField 2 f)}
    (h1 : bmsdop_geom₁ k f S e)
    {Vstd : Type} [AddCommGroup Vstd] [Module (GaloisField 2 f) Vstd]
    [FiniteDimensional (GaloisField 2 f) Vstd]
    (θ : Vstd ≃ₗ[GaloisField 2 f] ↥(bmsdop_W k f e)) :
    bmsdop_glueFun k f S h1 θ (1 : Vstd ≃ₗ[GaloisField 2 f] Vstd) = 1 := by
  rw [show bmsdop_glueFun k f S h1 θ (1 : Vstd ≃ₗ[GaloisField 2 f] Vstd) =
      (Submodule.prodEquivOfIsCompl (bmsdop_W k f e) (bmsdop_W' k f e)
        (bmsdop_isCompl_W h1.1)).symm.trans
        ((bmsdop_glueG k f S h1 θ (1 : Vstd ≃ₗ[GaloisField 2 f] Vstd)).trans
          (Submodule.prodEquivOfIsCompl (bmsdop_W k f e) (bmsdop_W' k f e)
            (bmsdop_isCompl_W h1.1))) from rfl]
  rw [bmsdop_glueG_one, LinearEquiv.one_eq_refl, LinearEquiv.refl_trans,
    LinearEquiv.symm_trans_self]
  exact LinearEquiv.one_eq_refl.symm

private lemma bmsdop_glueFun_mul (k f : ℕ)
    (S : Set (GL (Fin (k + 3) ⊕ Fin (k + 3)) (GaloisField 2 f)))
    {e : Matrix (Fin (k + 3) ⊕ Fin (k + 3)) (Fin (k + 3) ⊕ Fin (k + 3)) (GaloisField 2 f)}
    (h1 : bmsdop_geom₁ k f S e)
    {Vstd : Type} [AddCommGroup Vstd] [Module (GaloisField 2 f) Vstd]
    [FiniteDimensional (GaloisField 2 f) Vstd]
    (θ : Vstd ≃ₗ[GaloisField 2 f] ↥(bmsdop_W k f e))
    (g h : Vstd ≃ₗ[GaloisField 2 f] Vstd) :
    bmsdop_glueFun k f S h1 θ (g * h) =
      bmsdop_glueFun k f S h1 θ g * bmsdop_glueFun k f S h1 θ h := by
  rw [show bmsdop_glueFun k f S h1 θ (g * h) =
      (Submodule.prodEquivOfIsCompl (bmsdop_W k f e) (bmsdop_W' k f e)
        (bmsdop_isCompl_W h1.1)).symm.trans
        ((bmsdop_glueG k f S h1 θ (g * h)).trans
          (Submodule.prodEquivOfIsCompl (bmsdop_W k f e) (bmsdop_W' k f e)
        (bmsdop_isCompl_W h1.1))) from rfl,
    show bmsdop_glueFun k f S h1 θ g =
      (Submodule.prodEquivOfIsCompl (bmsdop_W k f e) (bmsdop_W' k f e)
        (bmsdop_isCompl_W h1.1)).symm.trans
        ((bmsdop_glueG k f S h1 θ g).trans
          (Submodule.prodEquivOfIsCompl (bmsdop_W k f e) (bmsdop_W' k f e)
        (bmsdop_isCompl_W h1.1))) from rfl,
    show bmsdop_glueFun k f S h1 θ h =
      (Submodule.prodEquivOfIsCompl (bmsdop_W k f e) (bmsdop_W' k f e)
        (bmsdop_isCompl_W h1.1)).symm.trans
        ((bmsdop_glueG k f S h1 θ h).trans
          (Submodule.prodEquivOfIsCompl (bmsdop_W k f e) (bmsdop_W' k f e)
        (bmsdop_isCompl_W h1.1))) from rfl]
  rw [bmsdop_glueG_mul]
  ext v
  simp only [LinearEquiv.trans_apply, LinearEquiv.mul_apply, LinearEquiv.symm_apply_apply]

private noncomputable def bmsdop_glue (k f : ℕ)
    (S : Set (GL (Fin (k + 3) ⊕ Fin (k + 3)) (GaloisField 2 f)))
    {e : Matrix (Fin (k + 3) ⊕ Fin (k + 3)) (Fin (k + 3) ⊕ Fin (k + 3)) (GaloisField 2 f)}
    (h1 : bmsdop_geom₁ k f S e)
    {Vstd : Type} [AddCommGroup Vstd] [Module (GaloisField 2 f) Vstd]
    [FiniteDimensional (GaloisField 2 f) Vstd]
    (θ : Vstd ≃ₗ[GaloisField 2 f] ↥(bmsdop_W k f e)) :
    (Vstd ≃ₗ[GaloisField 2 f] Vstd) →* (bmsdop_V k f ≃ₗ[GaloisField 2 f] bmsdop_V k f) :=
  { toFun := bmsdop_glueFun k f S h1 θ
    map_one' := bmsdop_glueFun_one k f S h1 θ
    map_mul' := bmsdop_glueFun_mul k f S h1 θ }

private lemma bmsdop_glue_apply (k f : ℕ)
    (S : Set (GL (Fin (k + 3) ⊕ Fin (k + 3)) (GaloisField 2 f)))
    {e : Matrix (Fin (k + 3) ⊕ Fin (k + 3)) (Fin (k + 3) ⊕ Fin (k + 3)) (GaloisField 2 f)}
    (h1 : bmsdop_geom₁ k f S e)
    {Vstd : Type} [AddCommGroup Vstd] [Module (GaloisField 2 f) Vstd]
    [FiniteDimensional (GaloisField 2 f) Vstd]
    (θ : Vstd ≃ₗ[GaloisField 2 f] ↥(bmsdop_W k f e))
    (g : Vstd ≃ₗ[GaloisField 2 f] Vstd) (v : bmsdop_V k f) :
    bmsdop_glue k f S h1 θ g v =
      (θ (g (θ.symm ⟨e.mulVec v, ⟨v, by rw [Matrix.toLin'_apply]⟩⟩)) : bmsdop_V k f) +
        (1 - e).mulVec v := by
  have hD : (Submodule.prodEquivOfIsCompl (bmsdop_W k f e) (bmsdop_W' k f e)
      (bmsdop_isCompl_W h1.1)).symm v =
      ((⟨e.mulVec v, ⟨v, by rw [Matrix.toLin'_apply]⟩⟩ : ↥(bmsdop_W k f e)),
        (⟨(1 - e).mulVec v, ⟨v, by rw [Matrix.toLin'_apply]⟩⟩ :
          ↥(bmsdop_W' k f e))) := by
    rw [LinearEquiv.symm_apply_eq]
    change v = (e.mulVec v : bmsdop_V k f) + (1 - e).mulVec v
    have hmat : e + (1 - e) = 1 := by abel
    simp only [← Matrix.add_mulVec, hmat, Matrix.one_mulVec]
  rw [show bmsdop_glue k f S h1 θ g =
      (Submodule.prodEquivOfIsCompl (bmsdop_W k f e) (bmsdop_W' k f e)
        (bmsdop_isCompl_W h1.1)).symm.trans
        (((θ.symm.trans (g.trans θ)).prodCongr
          (LinearEquiv.refl (GaloisField 2 f) ↥(bmsdop_W' k f e))).trans
          (Submodule.prodEquivOfIsCompl (bmsdop_W k f e) (bmsdop_W' k f e)
            (bmsdop_isCompl_W h1.1))) from rfl]
  simp only [LinearEquiv.trans_apply, hD, LinearEquiv.prodCongr_apply,
    LinearEquiv.refl_apply]
  rfl

private lemma bmsdop_glue_theta (k f : ℕ)
    (S : Set (GL (Fin (k + 3) ⊕ Fin (k + 3)) (GaloisField 2 f)))
    {e : Matrix (Fin (k + 3) ⊕ Fin (k + 3)) (Fin (k + 3) ⊕ Fin (k + 3)) (GaloisField 2 f)}
    (h1 : bmsdop_geom₁ k f S e)
    {Vstd : Type} [AddCommGroup Vstd] [Module (GaloisField 2 f) Vstd]
    [FiniteDimensional (GaloisField 2 f) Vstd]
    (θ : Vstd ≃ₗ[GaloisField 2 f] ↥(bmsdop_W k f e))
    (g : Vstd ≃ₗ[GaloisField 2 f] Vstd) (x : Vstd) :
    bmsdop_glue k f S h1 θ g (θ x) = θ (g x) := by
  rw [bmsdop_glue_apply]
  have hm : e.mulVec (θ x : bmsdop_V k f) = (θ x : bmsdop_V k f) :=
    (bmsdop_mem_W_iff h1.1 (θ x : bmsdop_V k f)).mp (θ x).2
  have hsub : (⟨e.mulVec (θ x : bmsdop_V k f),
      ⟨(θ x : bmsdop_V k f), by rw [Matrix.toLin'_apply]⟩⟩ :
        ↥(bmsdop_W k f e)) = θ x := Subtype.ext hm
  have hz : (1 - e).mulVec (θ x : bmsdop_V k f) = 0 := by
    rw [Matrix.sub_mulVec, Matrix.one_mulVec, hm, sub_self]
  simp only [hsub, hz, add_zero, LinearEquiv.symm_apply_apply]

private lemma bmsdop_glue_fixes (k f : ℕ)
    (S : Set (GL (Fin (k + 3) ⊕ Fin (k + 3)) (GaloisField 2 f)))
    {e : Matrix (Fin (k + 3) ⊕ Fin (k + 3)) (Fin (k + 3) ⊕ Fin (k + 3)) (GaloisField 2 f)}
    (h1 : bmsdop_geom₁ k f S e)
    {Vstd : Type} [AddCommGroup Vstd] [Module (GaloisField 2 f) Vstd]
    [FiniteDimensional (GaloisField 2 f) Vstd]
    (θ : Vstd ≃ₗ[GaloisField 2 f] ↥(bmsdop_W k f e))
    (g : Vstd ≃ₗ[GaloisField 2 f] Vstd) {v : bmsdop_V k f} (hv : v ∈ bmsdop_W' k f e) :
    bmsdop_glue k f S h1 θ g v = v := by
  rw [bmsdop_glue_apply]
  have hv' : (1 - e).mulVec v = v := (bmsdop_mem_W'_iff h1.1 v).mp hv
  have hzero : e * (1 - e) = 0 := by
    rw [Matrix.mul_sub, Matrix.mul_one, h1.1.eq, sub_self]
  have hev : e.mulVec v = 0 := by
    calc e.mulVec v = e.mulVec ((1 - e).mulVec v) := by rw [hv']
      _ = (e * (1 - e)).mulVec v := by rw [← Matrix.mulVec_mulVec]
      _ = 0 := by rw [hzero, Matrix.zero_mulVec]
  have hsub : (⟨e.mulVec v, ⟨v, by rw [Matrix.toLin'_apply]⟩⟩ : ↥(bmsdop_W k f e)) = 0 := by
    apply Subtype.ext
    change e.mulVec v = (0 : bmsdop_V k f)
    exact hev
  rw [hsub]
  simp only [map_zero]
  change (0 : bmsdop_V k f) + (1 - e).mulVec v = v
  rw [zero_add]
  exact hv'

private lemma bmsdop_glue_injective (k f : ℕ)
    (S : Set (GL (Fin (k + 3) ⊕ Fin (k + 3)) (GaloisField 2 f)))
    {e : Matrix (Fin (k + 3) ⊕ Fin (k + 3)) (Fin (k + 3) ⊕ Fin (k + 3)) (GaloisField 2 f)}
    (h1 : bmsdop_geom₁ k f S e)
    {Vstd : Type} [AddCommGroup Vstd] [Module (GaloisField 2 f) Vstd]
    [FiniteDimensional (GaloisField 2 f) Vstd]
    (θ : Vstd ≃ₗ[GaloisField 2 f] ↥(bmsdop_W k f e)) :
    Function.Injective (bmsdop_glue k f S h1 θ) := by
  intro g h hgh
  ext x
  have hx : bmsdop_glue k f S h1 θ g (θ x) = bmsdop_glue k f S h1 θ h (θ x) :=
    congrArg (fun f : bmsdop_V k f ≃ₗ[GaloisField 2 f] bmsdop_V k f => f (θ x)) hgh
  rw [bmsdop_glue_theta k f S h1 θ g x, bmsdop_glue_theta k f S h1 θ h x] at hx
  exact θ.injective (Subtype.ext hx)

private lemma bmsdop_glue_isometry (k f : ℕ)
    (S : Set (GL (Fin (k + 3) ⊕ Fin (k + 3)) (GaloisField 2 f)))
    {e : Matrix (Fin (k + 3) ⊕ Fin (k + 3)) (Fin (k + 3) ⊕ Fin (k + 3)) (GaloisField 2 f)}
    (h1 : bmsdop_geom₁ k f S e) (h2 : bmsdop_geom₂ k f S e)
    {Vstd : Type} [AddCommGroup Vstd] [Module (GaloisField 2 f) Vstd]
    [FiniteDimensional (GaloisField 2 f) Vstd]
    (Qstd : QuadraticForm (GaloisField 2 f) Vstd)
    (θ : Vstd ≃ₗ[GaloisField 2 f] ↥(bmsdop_W k f e))
    (hθ : ∀ x, (bmsdop_blockForm k f e) (θ x) = Qstd x)
    (g : Vstd ≃ₗ[GaloisField 2 f] Vstd)
    (hg : g ∈ TauCeti.QuadraticMap.orthogonalGroup Qstd) :
    bmsdop_glue k f S h1 θ g ∈ TauCeti.QuadraticMap.orthogonalGroup (bmsdop_Q k f) := by
  rw [TauCeti.QuadraticMap.mem_orthogonalGroup_iff]
  intro v
  rw [bmsdop_glue_apply]
  set w : ↥(bmsdop_W k f e) := ⟨e.mulVec v, ⟨v, by rw [Matrix.toLin'_apply]⟩⟩ with hw
  set u : bmsdop_V k f := (θ (g (θ.symm w)) : bmsdop_V k f) with hu
  have hid' : IsIdempotentElem (1 - e) := by
    show (1 - e) * (1 - e) = 1 - e
    rw [Matrix.sub_mul, Matrix.one_mul, Matrix.mul_sub, Matrix.mul_one, h1.1.eq]
    abel
  have huW : u ∈ bmsdop_W k f e := by
    rw [hu]
    exact (θ (g (θ.symm w))).2
  have hz1 : e.mulVec u = u := (bmsdop_mem_W_iff h1.1 u).mp huW
  have hz2 : (1 - e).mulVec ((1 - e).mulVec v) = (1 - e).mulVec v := by
    rw [Matrix.mulVec_mulVec, hid'.eq]
  have hz0 : e.mulVec (e.mulVec v) = e.mulVec v := by
    rw [Matrix.mulVec_mulVec, h1.1.eq]
  have horth : QuadraticMap.polar (bmsdop_Q k f) u ((1 - e).mulVec v) = 0 :=
    h2.2.1 _ _ hz1 hz2
  have horth0 : QuadraticMap.polar (bmsdop_Q k f) (e.mulVec v) ((1 - e).mulVec v) = 0 :=
    h2.2.1 _ _ hz0 hz2
  have hv : e.mulVec v + (1 - e).mulVec v = v := by
    rw [← Matrix.add_mulVec]
    have hmat : e + (1 - e) = 1 := by abel
    rw [hmat, Matrix.one_mulVec]
  have hgl1 : (bmsdop_Q k f) (u + (1 - e).mulVec v) = (bmsdop_Q k f) u +
      (bmsdop_Q k f) ((1 - e).mulVec v) := by
    rw [QuadraticMap.map_add (⇑(bmsdop_Q k f)), horth, add_zero]
  have hv1 : (bmsdop_Q k f) v = (bmsdop_Q k f) (e.mulVec v) +
      (bmsdop_Q k f) ((1 - e).mulVec v) := by
    calc (bmsdop_Q k f) v
        = (bmsdop_Q k f) (e.mulVec v + (1 - e).mulVec v) :=
          congrArg (bmsdop_Q k f) hv.symm
      _ = (bmsdop_Q k f) (e.mulVec v) + (bmsdop_Q k f) ((1 - e).mulVec v) := by
            rw [QuadraticMap.map_add (⇑(bmsdop_Q k f)), horth0, add_zero]
  have hmid : (bmsdop_Q k f) u = (bmsdop_Q k f) (e.mulVec v) := by
    rw [hu]
    rw [show (bmsdop_Q k f) (θ (g (θ.symm w)) : bmsdop_V k f) =
        (bmsdop_blockForm k f e) (θ (g (θ.symm w))) from rfl]
    rw [hθ]
    have hg' : ∀ m : Vstd, Qstd (g m) = Qstd m :=
      TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mp hg
    rw [hg' (θ.symm w)]
    rw [← hθ (θ.symm w), LinearEquiv.apply_symm_apply]
    rfl
  simp only [hgl1, hv1, hmid]

private lemma bmsdop_glue_basic (k f : ℕ)
    (S : Set (GL (Fin (k + 3) ⊕ Fin (k + 3)) (GaloisField 2 f)))
    {e : Matrix (Fin (k + 3) ⊕ Fin (k + 3)) (Fin (k + 3) ⊕ Fin (k + 3)) (GaloisField 2 f)}
    (h1 : bmsdop_geom₁ k f S e) (h2 : bmsdop_geom₂ k f S e)
    {Vstd : Type} [AddCommGroup Vstd] [Module (GaloisField 2 f) Vstd]
    [FiniteDimensional (GaloisField 2 f) Vstd]
    (Qstd : QuadraticForm (GaloisField 2 f) Vstd)
    (θ : Vstd ≃ₗ[GaloisField 2 f] ↥(bmsdop_W k f e))
    (hθ : ∀ x, (bmsdop_blockForm k f e) (θ x) = Qstd x) :
    (∀ g, g ∈ TauCeti.QuadraticMap.orthogonalGroup Qstd →
        bmsdop_glue k f S h1 θ g ∈ TauCeti.QuadraticMap.orthogonalGroup (bmsdop_Q k f)) ∧
      Function.Injective (bmsdop_glue k f S h1 θ) ∧
      (∀ g v, v ∈ bmsdop_W' k f e → bmsdop_glue k f S h1 θ g v = v) ∧
      (∀ g x, bmsdop_glue k f S h1 θ g (θ x) = θ (g x)) := by
  exact ⟨fun g hg => bmsdop_glue_isometry k f S h1 h2 Qstd θ hθ g hg,
    bmsdop_glue_injective k f S h1 θ,
    fun g v hv => bmsdop_glue_fixes k f S h1 θ g hv,
    fun g x => bmsdop_glue_theta k f S h1 θ g x⟩

private lemma bmsdop_glue_sub_one_apply (k f : ℕ)
    (S : Set (GL (Fin (k + 3) ⊕ Fin (k + 3)) (GaloisField 2 f)))
    {e : Matrix (Fin (k + 3) ⊕ Fin (k + 3)) (Fin (k + 3) ⊕ Fin (k + 3)) (GaloisField 2 f)}
    (h1 : bmsdop_geom₁ k f S e)
    {Vstd : Type} [AddCommGroup Vstd] [Module (GaloisField 2 f) Vstd]
    [FiniteDimensional (GaloisField 2 f) Vstd]
    (θ : Vstd ≃ₗ[GaloisField 2 f] ↥(bmsdop_W k f e))
    (g : Vstd ≃ₗ[GaloisField 2 f] Vstd) (v : bmsdop_V k f) :
    ((bmsdop_glue k f S h1 θ g : bmsdop_V k f →ₗ[GaloisField 2 f] bmsdop_V k f) - 1) v =
      (((bmsdop_W k f e).subtype.comp θ.toLinearMap).comp
        ((g : Vstd →ₗ[GaloisField 2 f] Vstd) - 1))
        (θ.symm ⟨e.mulVec v, ⟨v, by rw [Matrix.toLin'_apply]⟩⟩) := by
  rw [LinearMap.sub_apply, LinearMap.comp_apply, LinearMap.comp_apply, LinearMap.sub_apply,
    show ((bmsdop_glue k f S h1 θ g : bmsdop_V k f →ₗ[GaloisField 2 f] bmsdop_V k f)) v =
      bmsdop_glue k f S h1 θ g v from rfl,
    bmsdop_glue_apply]
  set w : ↥(bmsdop_W k f e) := ⟨e.mulVec v, ⟨v, by rw [Matrix.toLin'_apply]⟩⟩ with hw
  rw [show (1 : bmsdop_V k f →ₗ[GaloisField 2 f] bmsdop_V k f) v = v from rfl]
  rw [show (1 : Vstd →ₗ[GaloisField 2 f] Vstd) (θ.symm w) = θ.symm w from rfl]
  rw [Matrix.sub_mulVec, Matrix.one_mulVec]
  rw [map_sub]
  rw [show θ.toLinearMap (θ.symm w) = w from LinearEquiv.apply_symm_apply θ w]
  rw [map_sub]
  simp only [Submodule.coe_subtype]
  rw [show (w : bmsdop_V k f) = e.mulVec v from by rw [hw]]
  change (θ (g (θ.symm w)) : bmsdop_V k f) + (v - e.mulVec v) - v =
    (θ (g (θ.symm w)) : bmsdop_V k f) - e.mulVec v
  abel

private lemma bmsdop_glue_commSpace (k f : ℕ)
    (S : Set (GL (Fin (k + 3) ⊕ Fin (k + 3)) (GaloisField 2 f)))
    {e : Matrix (Fin (k + 3) ⊕ Fin (k + 3)) (Fin (k + 3) ⊕ Fin (k + 3)) (GaloisField 2 f)}
    (h1 : bmsdop_geom₁ k f S e)
    {Vstd : Type} [AddCommGroup Vstd] [Module (GaloisField 2 f) Vstd]
    [FiniteDimensional (GaloisField 2 f) Vstd]
    (θ : Vstd ≃ₗ[GaloisField 2 f] ↥(bmsdop_W k f e))
    (g : Vstd ≃ₗ[GaloisField 2 f] Vstd) :
    CFSG.RankThree.OrthogonalInvolutions.commSpace (bmsdop_glue k f S h1 θ g) =
      (CFSG.RankThree.OrthogonalInvolutions.commSpace g).map
        ((bmsdop_W k f e).subtype.comp θ.toLinearMap) := by
  rw [show CFSG.RankThree.OrthogonalInvolutions.commSpace (bmsdop_glue k f S h1 θ g) =
      LinearMap.range ((bmsdop_glue k f S h1 θ g :
        bmsdop_V k f →ₗ[GaloisField 2 f] bmsdop_V k f) - 1) from rfl]
  rw [show CFSG.RankThree.OrthogonalInvolutions.commSpace g =
      LinearMap.range ((g : Vstd →ₗ[GaloisField 2 f] Vstd) - 1) from rfl]
  rw [← LinearMap.range_comp]
  apply le_antisymm
  · rintro x ⟨v, rfl⟩
    exact ⟨θ.symm ⟨e.mulVec v, ⟨v, by rw [Matrix.toLin'_apply]⟩⟩,
      (bmsdop_glue_sub_one_apply k f S h1 θ g v).symm⟩
  · rintro x ⟨u, rfl⟩
    refine ⟨(θ u : bmsdop_V k f), ?_⟩
    rw [bmsdop_glue_sub_one_apply]
    have hmem : e.mulVec (θ u : bmsdop_V k f) = (θ u : bmsdop_V k f) :=
      (bmsdop_mem_W_iff h1.1 (θ u : bmsdop_V k f)).mp (θ u).2
    have hwu : (⟨e.mulVec (θ u : bmsdop_V k f),
        ⟨(θ u : bmsdop_V k f), by rw [Matrix.toLin'_apply]⟩⟩ :
          ↥(bmsdop_W k f e)) = θ u := Subtype.ext hmem
    rw [hwu, LinearEquiv.symm_apply_apply]

private lemma bmsdop_glue_mem_orthogonalGroup (k f : ℕ)
    (S : Set (GL (Fin (k + 3) ⊕ Fin (k + 3)) (GaloisField 2 f)))
    {e : Matrix (Fin (k + 3) ⊕ Fin (k + 3)) (Fin (k + 3) ⊕ Fin (k + 3)) (GaloisField 2 f)}
    (h1 : bmsdop_geom₁ k f S e) (h2 : bmsdop_geom₂ k f S e)
    {Vstd : Type} [AddCommGroup Vstd] [Module (GaloisField 2 f) Vstd]
    [FiniteDimensional (GaloisField 2 f) Vstd]
    (Qstd : QuadraticForm (GaloisField 2 f) Vstd)
    (θ : Vstd ≃ₗ[GaloisField 2 f] ↥(bmsdop_W k f e))
    (hθ : ∀ x, (bmsdop_blockForm k f e) (θ x) = Qstd x)
    (g : Vstd ≃ₗ[GaloisField 2 f] Vstd) :
    bmsdop_glue k f S h1 θ g ∈ TauCeti.QuadraticMap.orthogonalGroup (bmsdop_Q k f) ↔
      g ∈ TauCeti.QuadraticMap.orthogonalGroup Qstd := by
  constructor
  · intro hg
    rw [TauCeti.QuadraticMap.mem_orthogonalGroup_iff] at hg ⊢
    intro x
    have h := hg (θ x)
    rw [bmsdop_glue_theta k f S h1 θ g x] at h
    change (bmsdop_blockForm k f e) (θ (g x)) = (bmsdop_blockForm k f e) (θ x) at h
    simpa only [hθ] using h
  · intro hg
    exact bmsdop_glue_isometry k f S h1 h2 Qstd θ hθ g hg

private lemma bmsdop_glue_omegaGroup (k f : ℕ)
    (S : Set (GL (Fin (k + 3) ⊕ Fin (k + 3)) (GaloisField 2 f)))
    {e : Matrix (Fin (k + 3) ⊕ Fin (k + 3)) (Fin (k + 3) ⊕ Fin (k + 3)) (GaloisField 2 f)}
    (h1 : bmsdop_geom₁ k f S e) (h2 : bmsdop_geom₂ k f S e)
    {Vstd : Type} [AddCommGroup Vstd] [Module (GaloisField 2 f) Vstd]
    [FiniteDimensional (GaloisField 2 f) Vstd]
    (Qstd : QuadraticForm (GaloisField 2 f) Vstd)
    (θ : Vstd ≃ₗ[GaloisField 2 f] ↥(bmsdop_W k f e))
    (hθ : ∀ x, (bmsdop_blockForm k f e) (θ x) = Qstd x)
    (hnd_std : (QuadraticMap.polarBilin Qstd).Nondegenerate)
    (g : Vstd ≃ₗ[GaloisField 2 f] Vstd) :
    bmsdop_glue k f S h1 θ g ∈ CFSG.RankThree.OrthogonalInvolutions.omegaGroup (bmsdop_Q k f)
        (Spin.nondegenerate_polarBilin_quadPlus (k + 3) (GaloisField 2 f)) ↔
      g ∈ CFSG.RankThree.OrthogonalInvolutions.omegaGroup Qstd hnd_std := by
  rw [show bmsdop_glue k f S h1 θ g ∈
        CFSG.RankThree.OrthogonalInvolutions.omegaGroup (bmsdop_Q k f)
          (Spin.nondegenerate_polarBilin_quadPlus (k + 3) (GaloisField 2 f)) ↔
      bmsdop_glue k f S h1 θ g ∈ TauCeti.QuadraticMap.orthogonalGroup (bmsdop_Q k f) ∧
        Even (Module.finrank (GaloisField 2 f)
          (CFSG.RankThree.OrthogonalInvolutions.commSpace (bmsdop_glue k f S h1 θ g)))
      from Iff.rfl]
  rw [show g ∈ CFSG.RankThree.OrthogonalInvolutions.omegaGroup Qstd hnd_std ↔
      g ∈ TauCeti.QuadraticMap.orthogonalGroup Qstd ∧
        Even (Module.finrank (GaloisField 2 f)
          (CFSG.RankThree.OrthogonalInvolutions.commSpace g)) from Iff.rfl]
  rw [bmsdop_glue_mem_orthogonalGroup k f S h1 h2 Qstd θ hθ g]
  have hinj : Function.Injective ((bmsdop_W k f e).subtype.comp θ.toLinearMap) := by
    intro x y h
    exact θ.injective (Subtype.coe_injective h)
  have hfin : Module.finrank (GaloisField 2 f)
        (CFSG.RankThree.OrthogonalInvolutions.commSpace (bmsdop_glue k f S h1 θ g)) =
      Module.finrank (GaloisField 2 f)
        (CFSG.RankThree.OrthogonalInvolutions.commSpace g) := by
    rw [bmsdop_glue_commSpace k f S h1 θ g]
    exact (Submodule.equivMapOfInjective ((bmsdop_W k f e).subtype.comp θ.toLinearMap)
      hinj (CFSG.RankThree.OrthogonalInvolutions.commSpace g)).finrank_eq.symm
  constructor
  · rintro ⟨hgO, hge⟩
    exact ⟨hgO, by rwa [hfin] at hge⟩
  · rintro ⟨hgO, hge⟩
    exact ⟨hgO, by rwa [← hfin] at hge⟩

private lemma bmsdop_ext_apply (k f : ℕ)
    (S : Set (GL (Fin (k + 3) ⊕ Fin (k + 3)) (GaloisField 2 f)))
    {e : Matrix (Fin (k + 3) ⊕ Fin (k + 3)) (Fin (k + 3) ⊕ Fin (k + 3)) (GaloisField 2 f)}
    (h1 : bmsdop_geom₁ k f S e)
    {Vstd : Type} [AddCommGroup Vstd] [Module (GaloisField 2 f) Vstd]
    [FiniteDimensional (GaloisField 2 f) Vstd]
    (Qstd : QuadraticForm (GaloisField 2 f) Vstd)
    (hnd_std : (QuadraticMap.polarBilin Qstd).Nondegenerate)
    (E : (Vstd ≃ₗ[GaloisField 2 f] Vstd) →*
        (((Fin (k + 3) ⊕ Fin (k + 3)) → GaloisField 2 f) ≃ₗ[GaloisField 2 f]
          ((Fin (k + 3) ⊕ Fin (k + 3)) → GaloisField 2 f)))
    (θ : Vstd ≃ₗ[GaloisField 2 f] ↥(bmsdop_W k f e))
    (hE : bmsdop_ExtProps k f S e Qstd hnd_std θ E)
    (g : Vstd ≃ₗ[GaloisField 2 f] Vstd) (v : (Fin (k + 3) ⊕ Fin (k + 3)) → GaloisField 2 f) :
    E g v = (θ (g (θ.symm ⟨e.mulVec v, ⟨v, by rw [Matrix.toLin'_apply]⟩⟩)) :
        (Fin (k + 3) ⊕ Fin (k + 3)) → GaloisField 2 f) + (1 - e).mulVec v := by
  have hv : e.mulVec v + (1 - e).mulVec v = v := by
    rw [← Matrix.add_mulVec]
    have hmat : e + (1 - e) = 1 := by abel
    rw [hmat, Matrix.one_mulVec]
  have h4 : E g (e.mulVec v) =
      (θ (g (θ.symm ⟨e.mulVec v, ⟨v, by rw [Matrix.toLin'_apply]⟩⟩)) :
        (Fin (k + 3) ⊕ Fin (k + 3)) → GaloisField 2 f) := by
    have h := hE.2.2.2.1 g (θ.symm ⟨e.mulVec v, ⟨v, by rw [Matrix.toLin'_apply]⟩⟩)
    rw [LinearEquiv.apply_symm_apply] at h
    exact h
  have h3 : E g ((1 - e).mulVec v) = (1 - e).mulVec v :=
    hE.2.2.1 g ((1 - e).mulVec v) ⟨v, by rw [Matrix.toLin'_apply]⟩
  calc E g v = E g (e.mulVec v + (1 - e).mulVec v) := by rw [hv]
    _ = E g (e.mulVec v) + E g ((1 - e).mulVec v) := map_add (E g) _ _
    _ = (θ (g (θ.symm ⟨e.mulVec v, ⟨v, by rw [Matrix.toLin'_apply]⟩⟩)) :
          (Fin (k + 3) ⊕ Fin (k + 3)) → GaloisField 2 f) + (1 - e).mulVec v := by
          simp only [h4, h3]

private lemma bmsdop_ext_eq_glue (k f : ℕ)
    (S : Set (GL (Fin (k + 3) ⊕ Fin (k + 3)) (GaloisField 2 f)))
    {e : Matrix (Fin (k + 3) ⊕ Fin (k + 3)) (Fin (k + 3) ⊕ Fin (k + 3)) (GaloisField 2 f)}
    (h1 : bmsdop_geom₁ k f S e)
    {Vstd : Type} [AddCommGroup Vstd] [Module (GaloisField 2 f) Vstd]
    [FiniteDimensional (GaloisField 2 f) Vstd]
    (Qstd : QuadraticForm (GaloisField 2 f) Vstd)
    (hnd_std : (QuadraticMap.polarBilin Qstd).Nondegenerate)
    (E : (Vstd ≃ₗ[GaloisField 2 f] Vstd) →*
        (((Fin (k + 3) ⊕ Fin (k + 3)) → GaloisField 2 f) ≃ₗ[GaloisField 2 f]
          ((Fin (k + 3) ⊕ Fin (k + 3)) → GaloisField 2 f)))
    (θ : Vstd ≃ₗ[GaloisField 2 f] ↥(bmsdop_W k f e))
    (hE : bmsdop_ExtProps k f S e Qstd hnd_std θ E) :
    E = bmsdop_glue k f S h1 θ := by
  apply MonoidHom.ext
  intro g
  apply LinearEquiv.ext
  intro v
  exact (bmsdop_ext_apply k f S h1 Qstd hnd_std E θ hE g v).trans
    (bmsdop_glue_apply k f S h1 θ g v).symm

private lemma bmsdop_spinAction_mem_omegaGroup (k f : ℕ)
    (u : spinGroup (bmsdop_Q k f)) :
    Spin.spinAction (bmsdop_Q k f) u ∈
      CFSG.RankThree.OrthogonalInvolutions.omegaGroup (bmsdop_Q k f)
        (Spin.nondegenerate_polarBilin_quadPlus (k + 3) (GaloisField 2 f)) := by
  have hle : CFSG.ClassicalGroups.Orthogonal.elementaryGroup (bmsdop_Q k f) ≤
      CFSG.RankThree.OrthogonalInvolutions.omegaGroup (bmsdop_Q k f)
        (Spin.nondegenerate_polarBilin_quadPlus (k + 3) (GaloisField 2 f)) :=
    CFSG.ClassicalGroups.Orthogonal.elementaryGroup_le_omegaGroup
      (Q := bmsdop_Q k f)
      (Spin.nondegenerate_polarBilin_quadPlus (k + 3) (GaloisField 2 f))
  have hmem : Spin.spinAction (bmsdop_Q k f) u ∈
      CFSG.ClassicalGroups.Orthogonal.elementaryGroup (bmsdop_Q k f) := by
    rw [← Spin.range_spinAction_quadPlus (n := k + 3) (K := GaloisField 2 f) (by omega)]
    exact ⟨u, rfl⟩
  exact hle hmem

private lemma bmsdop_mem_Ge_of_action (k f : ℕ)
    (S : Set (GL (Fin (k + 3) ⊕ Fin (k + 3)) (GaloisField 2 f)))
    {e : Matrix (Fin (k + 3) ⊕ Fin (k + 3)) (Fin (k + 3) ⊕ Fin (k + 3)) (GaloisField 2 f)}
    (u : spinGroup (bmsdop_Q k f))
    (hfix : ∀ v : (Fin (k + 3) ⊕ Fin (k + 3)) → GaloisField 2 f,
      v ∈ bmsdop_W' k f e → Spin.spinAction (bmsdop_Q k f) u v = v)
    (hcomm : ∀ s ∈ S, ∀ x : (Fin (k + 3) ⊕ Fin (k + 3)) → GaloisField 2 f,
      (s : Matrix (Fin (k + 3) ⊕ Fin (k + 3)) (Fin (k + 3) ⊕ Fin (k + 3))
          (GaloisField 2 f)).mulVec (Spin.spinAction (bmsdop_Q k f) u x) =
        Spin.spinAction (bmsdop_Q k f) u
          ((s : Matrix (Fin (k + 3) ⊕ Fin (k + 3)) (Fin (k + 3) ⊕ Fin (k + 3))
            (GaloisField 2 f)).mulVec x)) :
    u ∈ bmsdop_Ge k f S e := by
  rw [bmsdop_Ge, glBlockCentralizer, Subgroup.mem_comap, Subgroup.mem_inf]
  have htoLin : Matrix.toLin' (↑(Spin.spinMatrix (bmsdop_Q k f) u)) =
      (Spin.spinAction (bmsdop_Q k f) u).toLinearMap := by
    rw [Spin.coe_spinMatrix, Matrix.toLin'_toMatrix']
  constructor
  · rw [Subgroup.mem_centralizer_iff]
    intro s hs
    apply Units.ext
    rw [Units.val_mul, Units.val_mul]
    apply Matrix.toLin'.injective
    rw [Matrix.toLin'_mul, Matrix.toLin'_mul, htoLin]
    apply LinearMap.ext
    intro x
    exact hcomm s hs x
  · show ((Spin.spinMatrix (bmsdop_Q k f) u : GL (Fin (k + 3) ⊕ Fin (k + 3))
        (GaloisField 2 f)) : Matrix (Fin (k + 3) ⊕ Fin (k + 3))
          (Fin (k + 3) ⊕ Fin (k + 3)) (GaloisField 2 f)) * (1 - e) = 1 - e
    apply Matrix.toLin'.injective
    rw [Matrix.toLin'_mul, htoLin]
    apply LinearMap.ext
    intro x
    exact hfix ((1 - e).mulVec x) ⟨x, by rw [Matrix.toLin'_apply]⟩

private lemma bmsdop_mem_adjoin_commute {ι F : Type} [Fintype ι] [DecidableEq ι] [Field F]
    {S : Set (GL ι F)} (hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s')
    (s : GL ι F) (hs : s ∈ S) (a : Matrix ι ι F)
    (ha : a ∈ Algebra.adjoin F (Units.val '' S)) :
    (s : Matrix ι ι F) * a = a * (s : Matrix ι ι F) := by
  have hgen : Units.val '' S ⊆ Subalgebra.centralizer F {(s : Matrix ι ι F)} := by
    intro y hy
    change y ∈ Subalgebra.centralizer F {(s : Matrix ι ι F)}
    rw [Subalgebra.mem_centralizer_iff]
    intro g hg
    rw [Set.mem_singleton_iff] at hg
    subst hg
    rcases hy with ⟨t, ht, rfl⟩
    have hm : (s : Matrix ι ι F) * (t : Matrix ι ι F) =
        (t : Matrix ι ι F) * (s : Matrix ι ι F) := by
      simpa only [Units.val_mul] using congrArg (fun u : GL ι F => (u : Matrix ι ι F))
        (hS s hs t ht).eq
    exact hm
  have hA : Algebra.adjoin F (Units.val '' S) ≤
      Subalgebra.centralizer F {(s : Matrix ι ι F)} :=
    Algebra.adjoin_le hgen
  exact (Subalgebra.mem_centralizer_iff F).mp (hA ha) (s : Matrix ι ι F) (Set.mem_singleton _)

private lemma bmsdop_glue_commute_S (k f : ℕ)
    (S : Set (GL (Fin (k + 3) ⊕ Fin (k + 3)) (GaloisField 2 f)))
    {e : Matrix (Fin (k + 3) ⊕ Fin (k + 3)) (Fin (k + 3) ⊕ Fin (k + 3)) (GaloisField 2 f)}
    (h1 : bmsdop_geom₁ k f S e) (h2 : bmsdop_geom₂ k f S e)
    (hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s')
    (heA : e ∈ Algebra.adjoin (GaloisField 2 f) (Units.val '' S))
    {Vstd : Type} [AddCommGroup Vstd] [Module (GaloisField 2 f) Vstd]
    [FiniteDimensional (GaloisField 2 f) Vstd]
    (θ : Vstd ≃ₗ[GaloisField 2 f] ↥(bmsdop_W k f e))
    (h : Vstd ≃ₗ[GaloisField 2 f] Vstd)
    (s : GL (Fin (k + 3) ⊕ Fin (k + 3)) (GaloisField 2 f)) (hs : s ∈ S)
    (x : (Fin (k + 3) ⊕ Fin (k + 3)) → GaloisField 2 f) :
    (s : Matrix (Fin (k + 3) ⊕ Fin (k + 3)) (Fin (k + 3) ⊕ Fin (k + 3))
        (GaloisField 2 f)).mulVec (bmsdop_glue k f S h1 θ h x) =
      bmsdop_glue k f S h1 θ h
        ((s : Matrix (Fin (k + 3) ⊕ Fin (k + 3)) (Fin (k + 3) ⊕ Fin (k + 3))
          (GaloisField 2 f)).mulVec x) := by
  have hse : (s : Matrix (Fin (k + 3) ⊕ Fin (k + 3)) (Fin (k + 3) ⊕ Fin (k + 3)) (GaloisField 2 f))
      * e = e * (s : Matrix (Fin (k + 3) ⊕ Fin (k + 3)) (Fin (k + 3) ⊕ Fin (k + 3)) (GaloisField 2
          f)) := bmsdop_mem_adjoin_commute hS s hs e heA
  have hesx : e.mulVec ((s : Matrix (Fin (k + 3) ⊕ Fin (k + 3)) (Fin (k + 3) ⊕ Fin (k + 3))
      (GaloisField 2 f)).mulVec x) = e.mulVec x := by
    calc e.mulVec ((s : Matrix (Fin (k + 3) ⊕ Fin (k + 3)) (Fin (k + 3) ⊕ Fin (k + 3)) (GaloisField
        2 f)).mulVec x) = (e * (s : Matrix (Fin (k + 3) ⊕ Fin (k + 3)) (Fin (k + 3) ⊕ Fin (k + 3))
            (GaloisField 2 f))).mulVec x := by rw [Matrix.mulVec_mulVec]
      _ = ((s : Matrix (Fin (k + 3) ⊕ Fin (k + 3)) (Fin (k + 3) ⊕ Fin (k + 3)) (GaloisField 2 f)) *
          e).mulVec x := by rw [← hse]
      _ = (s : Matrix (Fin (k + 3) ⊕ Fin (k + 3)) (Fin (k + 3) ⊕ Fin (k + 3)) (GaloisField 2
          f)).mulVec (e.mulVec x) := by rw [Matrix.mulVec_mulVec]
      _ = e.mulVec x := h2.1 s hs (e.mulVec x) (by rw [Matrix.mulVec_mulVec, h1.1.eq])
  have hsub : (⟨e.mulVec ((s : Matrix (Fin (k + 3) ⊕ Fin (k + 3)) (Fin (k + 3) ⊕ Fin (k + 3))
      (GaloisField 2 f)).mulVec x),
        ⟨(s : Matrix (Fin (k + 3) ⊕ Fin (k + 3)) (Fin (k + 3) ⊕ Fin (k + 3)) (GaloisField 2
            f)).mulVec x, by rw [Matrix.toLin'_apply]⟩⟩ : ↥(bmsdop_W k f e)) =
      ⟨e.mulVec x, ⟨x, by rw [Matrix.toLin'_apply]⟩⟩ := Subtype.ext hesx
  have hmat : (s : Matrix (Fin (k + 3) ⊕ Fin (k + 3)) (Fin (k + 3) ⊕ Fin (k + 3)) (GaloisField 2 f))
      * (1 - e) = (1 - e) * (s : Matrix (Fin (k + 3) ⊕ Fin (k + 3)) (Fin (k + 3) ⊕ Fin (k + 3))
          (GaloisField 2 f)) := by
    rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, Matrix.one_mul, hse]
  have hmul : (s : Matrix (Fin (k + 3) ⊕ Fin (k + 3)) (Fin (k + 3) ⊕ Fin (k + 3)) (GaloisField 2
      f)).mulVec ((1 - e).mulVec x) = (1 - e).mulVec ((s : Matrix (Fin (k + 3) ⊕ Fin (k + 3)) (Fin
          (k + 3) ⊕ Fin (k + 3)) (GaloisField 2 f)).mulVec x) := by
    calc (s : Matrix (Fin (k + 3) ⊕ Fin (k + 3)) (Fin (k + 3) ⊕ Fin (k + 3)) (GaloisField 2
        f)).mulVec ((1 - e).mulVec x)
        = ((s : Matrix (Fin (k + 3) ⊕ Fin (k + 3)) (Fin (k + 3) ⊕ Fin (k + 3)) (GaloisField 2 f)) *
            (1 - e)).mulVec x := by rw [Matrix.mulVec_mulVec]
      _ = ((1 - e) * (s : Matrix (Fin (k + 3) ⊕ Fin (k + 3)) (Fin (k + 3) ⊕ Fin (k + 3))
          (GaloisField 2 f))).mulVec x := by rw [hmat]
      _ = (1 - e).mulVec ((s : Matrix (Fin (k + 3) ⊕ Fin (k + 3)) (Fin (k + 3) ⊕ Fin (k + 3))
          (GaloisField 2 f)).mulVec x) := by rw [Matrix.mulVec_mulVec]
  have hfixs : (s : Matrix (Fin (k + 3) ⊕ Fin (k + 3)) (Fin (k + 3) ⊕ Fin (k + 3)) (GaloisField 2
      f)).mulVec
      (θ (h (θ.symm ⟨e.mulVec x, ⟨x, by rw [Matrix.toLin'_apply]⟩⟩)) : bmsdop_V k f) =
      (θ (h (θ.symm ⟨e.mulVec x, ⟨x, by rw [Matrix.toLin'_apply]⟩⟩)) : bmsdop_V k f) :=
    h2.1 s hs _ ((bmsdop_mem_W_iff h1.1 _).mp
      (θ (h (θ.symm ⟨e.mulVec x, ⟨x, by rw [Matrix.toLin'_apply]⟩⟩))).2)
  rw [bmsdop_glue_apply, bmsdop_glue_apply, Matrix.mulVec_add, hfixs, hmul, hsub]

private lemma bmsdop_Ge_spinAction_of_mem_range (k f : ℕ)
    (S : Set (GL (Fin (k + 3) ⊕ Fin (k + 3)) (GaloisField 2 f)))
    {e : Matrix (Fin (k + 3) ⊕ Fin (k + 3)) (Fin (k + 3) ⊕ Fin (k + 3)) (GaloisField 2 f)}
    (he : IsIdempotentElem e)
    (g' : bmsdop_V k f ≃ₗ[GaloisField 2 f] bmsdop_V k f)
    (hSg' : ∀ s ∈ S, ∀ x : bmsdop_V k f,
      g' ((s : Matrix (Fin (k + 3) ⊕ Fin (k + 3)) (Fin (k + 3) ⊕ Fin (k + 3))
          (GaloisField 2 f)).mulVec x) =
        (s : Matrix (Fin (k + 3) ⊕ Fin (k + 3)) (Fin (k + 3) ⊕ Fin (k + 3))
          (GaloisField 2 f)).mulVec (g' x))
    (hker : ∀ x : bmsdop_V k f, (1 - e).mulVec x = x → g' x = x)
    (hg'range : g' ∈ (Spin.spinAction (bmsdop_Q k f)).range) :
    ∃ u : bmsdop_Ge k f S e, ∀ x : bmsdop_V k f,
      Spin.spinAction (bmsdop_Q k f) (u : spinGroup (bmsdop_Q k f)) x = g' x := by
  have h1eid : (1 - e) * (1 - e) = (1 - e) := by
    calc (1 - e) * (1 - e) = 1 * (1 - e) - e * (1 - e) := by rw [Matrix.sub_mul]
      _ = (1 - e) - (e * 1 - e * e) := by rw [Matrix.one_mul, Matrix.mul_sub]
      _ = (1 - e) - (e - e) := by rw [Matrix.mul_one, he.eq]
      _ = 1 - e := by abel
  obtain ⟨x, hx⟩ := hg'range
  refine ⟨⟨x, ?_⟩, fun y => congrArg (fun e => e y) hx⟩
  rw [bmsdop_Ge, glBlockCentralizer, Subgroup.mem_comap]
  refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
  · rw [Subgroup.mem_centralizer_iff]
    intro s hs
    apply Units.ext
    simp only [Units.val_mul]
    exact Matrix.mulVec_injective (funext fun y => by
      rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Spin.spinMatrix_mulVec,
        Spin.spinMatrix_mulVec, hx, hSg' s hs y])
  · exact Matrix.mulVec_injective (funext fun y => by
      rw [← Matrix.mulVec_mulVec, Spin.spinMatrix_mulVec, hx]
      exact hker ((1 - e).mulVec y) (by rw [Matrix.mulVec_mulVec, h1eid]))

private lemma bmsdop_glue_map_ge (k f : ℕ)
    (S : Set (GL (Fin (k + 3) ⊕ Fin (k + 3)) (GaloisField 2 f)))
    {e : Matrix (Fin (k + 3) ⊕ Fin (k + 3)) (Fin (k + 3) ⊕ Fin (k + 3)) (GaloisField 2 f)}
    (h1 : bmsdop_geom₁ k f S e) (h2 : bmsdop_geom₂ k f S e)
    (hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s')
    (heA : e ∈ Algebra.adjoin (GaloisField 2 f) (Units.val '' S))
    {Vstd : Type} [AddCommGroup Vstd] [Module (GaloisField 2 f) Vstd]
    [FiniteDimensional (GaloisField 2 f) Vstd]
    (Qstd : QuadraticForm (GaloisField 2 f) Vstd)
    (hnd_std : (QuadraticMap.polarBilin Qstd).Nondegenerate)
    (E : (Vstd ≃ₗ[GaloisField 2 f] Vstd) →*
        (((Fin (k + 3) ⊕ Fin (k + 3)) → GaloisField 2 f) ≃ₗ[GaloisField 2 f]
          ((Fin (k + 3) ⊕ Fin (k + 3)) → GaloisField 2 f)))
    (θ : Vstd ≃ₗ[GaloisField 2 f] ↥(bmsdop_W k f e))
    (hE : bmsdop_ExtProps k f S e Qstd hnd_std θ E) :
    (CFSG.RankThree.OrthogonalInvolutions.omegaGroup Qstd hnd_std).map E ≤
      (bmsdop_Ge k f S e).map (Spin.spinAction (bmsdop_Q k f)) := by
  have hEglue : E = bmsdop_glue k f S h1 θ :=
    bmsdop_ext_eq_glue k f S h1 Qstd hnd_std E θ hE
  intro x hx
  obtain ⟨g, hg, rfl⟩ := Subgroup.mem_map.mp hx
  have hgQ : bmsdop_glue k f S h1 θ g ∈
      CFSG.RankThree.OrthogonalInvolutions.omegaGroup (bmsdop_Q k f)
        (Spin.nondegenerate_polarBilin_quadPlus (k + 3) (GaloisField 2 f)) := by
    have h := (hE.2.2.2.2 g).mpr hg
    rwa [DFunLike.congr_fun hEglue g] at h
  have h4 : 4 ≤ Module.finrank (GaloisField 2 f) (bmsdop_V k f) := by
    rw [Module.finrank_fintype_fun_eq_card, Fintype.card_sum, Fintype.card_fin]
    omega
  have hge : bmsdop_glue k f S h1 θ g ∈
      CFSG.ClassicalGroups.Orthogonal.elementaryGroup (bmsdop_Q k f) :=
    CFSG.RankThree.GF2n.Smith81.omegaGroup_le_elementaryGroup_of_four_le
      (Q := bmsdop_Q k f)
      (Spin.nondegenerate_polarBilin_quadPlus (k + 3) (GaloisField 2 f)) h4 hgQ
  have hgrange : bmsdop_glue k f S h1 θ g ∈ (Spin.spinAction (bmsdop_Q k f)).range := by
    rw [Spin.range_spinAction_quadPlus (n := k + 3) (K := GaloisField 2 f) (by omega)]
    exact hge
  obtain ⟨u, hueq⟩ := bmsdop_Ge_spinAction_of_mem_range k f S h1.1
    (bmsdop_glue k f S h1 θ g)
    (fun s hs y => (bmsdop_glue_commute_S k f S h1 h2 hS heA θ g s hs y).symm)
    (fun y hy => bmsdop_glue_fixes k f S h1 θ g ((bmsdop_mem_W'_iff h1.1 y).mpr hy))
    hgrange
  exact Subgroup.mem_map.mpr ⟨(u : spinGroup (bmsdop_Q k f)), u.2,
    (LinearEquiv.ext hueq).trans (DFunLike.congr_fun hEglue g).symm⟩

private lemma bmsdop_glue_map_le (k f : ℕ)
    (S : Set (GL (Fin (k + 3) ⊕ Fin (k + 3)) (GaloisField 2 f)))
    {e : Matrix (Fin (k + 3) ⊕ Fin (k + 3)) (Fin (k + 3) ⊕ Fin (k + 3)) (GaloisField 2 f)}
    (h1 : bmsdop_geom₁ k f S e) (h2 : bmsdop_geom₂ k f S e)
    (hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s')
    (heA : e ∈ Algebra.adjoin (GaloisField 2 f) (Units.val '' S))
    {Vstd : Type} [AddCommGroup Vstd] [Module (GaloisField 2 f) Vstd]
    [FiniteDimensional (GaloisField 2 f) Vstd]
    (Qstd : QuadraticForm (GaloisField 2 f) Vstd)
    (hnd_std : (QuadraticMap.polarBilin Qstd).Nondegenerate)
    (E : (Vstd ≃ₗ[GaloisField 2 f] Vstd) →*
        (((Fin (k + 3) ⊕ Fin (k + 3)) → GaloisField 2 f) ≃ₗ[GaloisField 2 f]
          ((Fin (k + 3) ⊕ Fin (k + 3)) → GaloisField 2 f)))
    (θ : Vstd ≃ₗ[GaloisField 2 f] ↥(bmsdop_W k f e))
    (hE : bmsdop_ExtProps k f S e Qstd hnd_std θ E) :
    (bmsdop_Ge k f S e).map (Spin.spinAction (bmsdop_Q k f)) ≤
      (CFSG.RankThree.OrthogonalInvolutions.omegaGroup Qstd hnd_std).map E := by
  have hEglue : E = bmsdop_glue k f S h1 θ :=
    bmsdop_ext_eq_glue k f S h1 Qstd hnd_std E θ hE
  intro x hx
  obtain ⟨u, hu, rfl⟩ := Subgroup.mem_map.mp hx
  have hu_fix : (Spin.spinMatrix (bmsdop_Q k f) u : Matrix (Fin (k + 3) ⊕ Fin (k + 3))
      (Fin (k + 3) ⊕ Fin (k + 3)) (GaloisField 2 f)) * (1 - e) = 1 - e :=
    (Subgroup.mem_inf.mp (Subgroup.mem_comap.mp hu)).2
  have hpres : ∀ x : bmsdop_V k f, e.mulVec x = x →
      e.mulVec (Spin.spinAction (bmsdop_Q k f) u x) = Spin.spinAction (bmsdop_Q k f) u x := by
    intro x hx
    simpa only [Spin.spinMatrix_mulVec] using
      bmsdop_spinMatrix_preserves_block heA ⟨u, hu⟩ x hx
  have hle : Submodule.map ((Spin.spinAction (bmsdop_Q k f) u) :
      bmsdop_V k f →ₗ[GaloisField 2 f] bmsdop_V k f) (bmsdop_W k f e) ≤
      bmsdop_W k f e := by
    rw [Submodule.map_le_iff_le_comap]
    intro w hw
    rw [Submodule.mem_comap, bmsdop_mem_W_iff h1.1]
    exact hpres w ((bmsdop_mem_W_iff h1.1 w).mp hw)
  have hfr : Module.finrank (GaloisField 2 f) ↥(Submodule.map ((Spin.spinAction (bmsdop_Q k f) u) :
      bmsdop_V k f →ₗ[GaloisField 2 f] bmsdop_V k f) (bmsdop_W k f e)) =
      Module.finrank (GaloisField 2 f) ↥(bmsdop_W k f e) :=
    ((LinearEquiv.submoduleMap (Spin.spinAction (bmsdop_Q k f) u) (bmsdop_W k f e)).finrank_eq).symm
  have hmapW : Submodule.map ((Spin.spinAction (bmsdop_Q k f) u) :
      bmsdop_V k f →ₗ[GaloisField 2 f] bmsdop_V k f) (bmsdop_W k f e) = bmsdop_W k f e :=
    Submodule.eq_of_le_of_finrank_eq hle hfr
  let g : Vstd ≃ₗ[GaloisField 2 f] Vstd :=
    θ.trans (((LinearEquiv.submoduleMap (Spin.spinAction (bmsdop_Q k f) u)
      (bmsdop_W k f e)).trans (LinearEquiv.ofEq _ _ hmapW)).trans θ.symm)
  have hgθ : ∀ y : Vstd, θ (g y) = Spin.spinAction (bmsdop_Q k f) u (θ y) := by
    intro y
    change θ (θ.symm ((((LinearEquiv.submoduleMap (Spin.spinAction (bmsdop_Q k f) u)
      (bmsdop_W k f e)).trans (LinearEquiv.ofEq _ _ hmapW)) (θ y)))) =
      Spin.spinAction (bmsdop_Q k f) u (θ y)
    rw [LinearEquiv.apply_symm_apply]
    change (((Spin.spinAction (bmsdop_Q k f) u).submoduleMap (bmsdop_W k f e)) (θ y) :
        bmsdop_V k f) = (Spin.spinAction (bmsdop_Q k f) u) ((θ y : ↥(bmsdop_W k f e)) :
          bmsdop_V k f)
    rw [LinearEquiv.submoduleMap_apply]
  have hfixW' : ∀ v, v ∈ bmsdop_W' k f e → Spin.spinAction (bmsdop_Q k f) u v = v := by
    intro v hv
    have hv' : (1 - e).mulVec v = v := (bmsdop_mem_W'_iff h1.1 v).mp hv
    have hmv : ((Spin.spinMatrix (bmsdop_Q k f) u : GL (Fin (k + 3) ⊕ Fin (k + 3))
        (GaloisField 2 f)) : Matrix (Fin (k + 3) ⊕ Fin (k + 3))
        (Fin (k + 3) ⊕ Fin (k + 3)) (GaloisField 2 f)).mulVec v =
        Spin.spinAction (bmsdop_Q k f) u v :=
      Spin.spinMatrix_mulVec (bmsdop_Q k f) u v
    rw [← hmv, ← hv', Matrix.mulVec_mulVec, hu_fix]
  have hglue : bmsdop_glue k f S h1 θ g = Spin.spinAction (bmsdop_Q k f) u := by
    apply LinearEquiv.ext
    intro v
    have hv : e.mulVec v + (1 - e).mulVec v = v := by
      rw [← Matrix.add_mulVec]
      have hmat : e + (1 - e) = 1 := by abel
      rw [hmat, Matrix.one_mulVec]
    have hmem : (1 - e).mulVec v ∈ bmsdop_W' k f e := ⟨v, by rw [Matrix.toLin'_apply]⟩
    have h1 : θ (g (θ.symm ⟨e.mulVec v, ⟨v, by rw [Matrix.toLin'_apply]⟩⟩)) =
        Spin.spinAction (bmsdop_Q k f) u (e.mulVec v) :=
      (hgθ (θ.symm ⟨e.mulVec v, ⟨v, by rw [Matrix.toLin'_apply]⟩⟩)).trans
        (congrArg (Spin.spinAction (bmsdop_Q k f) u)
          (congrArg Subtype.val (LinearEquiv.apply_symm_apply θ _)))
    have hsplit : Spin.spinAction (bmsdop_Q k f) u v =
        Spin.spinAction (bmsdop_Q k f) u (e.mulVec v) + (1 - e).mulVec v := by
      calc Spin.spinAction (bmsdop_Q k f) u v
          = Spin.spinAction (bmsdop_Q k f) u (e.mulVec v + (1 - e).mulVec v) := by rw [hv]
        _ = Spin.spinAction (bmsdop_Q k f) u (e.mulVec v) +
              Spin.spinAction (bmsdop_Q k f) u ((1 - e).mulVec v) := map_add _ _ _
        _ = Spin.spinAction (bmsdop_Q k f) u (e.mulVec v) + (1 - e).mulVec v := by
              rw [hfixW' ((1 - e).mulVec v) hmem]
    rw [bmsdop_glue_apply, h1, hsplit]
  refine Subgroup.mem_map.mpr ⟨g, ?_, ?_⟩
  · refine (hE.2.2.2.2 g).mp ?_
    rw [DFunLike.congr_fun hEglue g, hglue]
    exact bmsdop_spinAction_mem_omegaGroup k f u
  · rw [DFunLike.congr_fun hEglue g, hglue]

private theorem bmsdop_block_group_eq_ext
    (k f : ℕ) (S : Set (GL (Fin (k + 3) ⊕ Fin (k + 3)) (GaloisField 2 f)))
    {e : Matrix (Fin (k + 3) ⊕ Fin (k + 3)) (Fin (k + 3) ⊕ Fin (k + 3)) (GaloisField 2 f)}
    (h1 : bmsdop_geom₁ k f S e) (h2 : bmsdop_geom₂ k f S e)
    (hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s')
    (heA : e ∈ Algebra.adjoin (GaloisField 2 f) (Units.val '' S))
    {Vstd : Type} [AddCommGroup Vstd] [Module (GaloisField 2 f) Vstd]
    [FiniteDimensional (GaloisField 2 f) Vstd]
    (Qstd : QuadraticForm (GaloisField 2 f) Vstd)
    (hnd_std : (QuadraticMap.polarBilin Qstd).Nondegenerate)
    (E : (Vstd ≃ₗ[GaloisField 2 f] Vstd) →*
        (((Fin (k + 3) ⊕ Fin (k + 3)) → GaloisField 2 f) ≃ₗ[GaloisField 2 f]
          ((Fin (k + 3) ⊕ Fin (k + 3)) → GaloisField 2 f)))
    (θ : Vstd ≃ₗ[GaloisField 2 f] ↥(bmsdop_W k f e))
    (hE : bmsdop_ExtProps k f S e Qstd hnd_std θ E) :
    (bmsdop_Ge k f S e).map (Spin.spinAction (bmsdop_Q k f)) =
      (CFSG.RankThree.OrthogonalInvolutions.omegaGroup Qstd hnd_std).map E := by
  exact le_antisymm (bmsdop_glue_map_le k f S h1 h2 hS heA Qstd hnd_std E θ hE)
    (bmsdop_glue_map_ge k f S h1 h2 hS heA Qstd hnd_std E θ hE)

private noncomputable def bmsdop_thetaIsometry (k f : ℕ)
    {e : Matrix (Fin (k + 3) ⊕ Fin (k + 3)) (Fin (k + 3) ⊕ Fin (k + 3)) (GaloisField 2 f)}
    {Vstd : Type} [AddCommGroup Vstd] [Module (GaloisField 2 f) Vstd]
    [FiniteDimensional (GaloisField 2 f) Vstd]
    (Qstd : QuadraticForm (GaloisField 2 f) Vstd)
    (θ : Vstd ≃ₗ[GaloisField 2 f] ↥(bmsdop_W k f e))
    (hθ : ∀ x : Vstd, (bmsdop_blockForm k f e) (θ x) = Qstd x) :
    Qstd →qᵢ bmsdop_Q k f :=
  { toLinearMap := (bmsdop_W k f e).subtype.comp θ.toLinearMap
    map_app' := fun x => by
      change (Spin.quadPlus (k + 3) (GaloisField 2 f))
        (((θ x : ↥(bmsdop_W k f e)) : bmsdop_V k f)) = Qstd x
      exact hθ x }

private lemma bmsdop_thetaIsometry_apply (k f : ℕ)
    {e : Matrix (Fin (k + 3) ⊕ Fin (k + 3)) (Fin (k + 3) ⊕ Fin (k + 3)) (GaloisField 2 f)}
    {Vstd : Type} [AddCommGroup Vstd] [Module (GaloisField 2 f) Vstd]
    [FiniteDimensional (GaloisField 2 f) Vstd]
    (Qstd : QuadraticForm (GaloisField 2 f) Vstd)
    (θ : Vstd ≃ₗ[GaloisField 2 f] ↥(bmsdop_W k f e))
    (hθ : ∀ x : Vstd, (bmsdop_blockForm k f e) (θ x) = Qstd x) (x : Vstd) :
    (bmsdop_thetaIsometry k f Qstd θ hθ : Vstd → bmsdop_V k f) x =
      ((θ x : ↥(bmsdop_W k f e)) : bmsdop_V k f) := rfl

private lemma bmsdop_spinGroupMap_spinAction {K M₁ M₂ : Type} [Field K]
    [AddCommGroup M₁] [Module K M₁] [AddCommGroup M₂] [Module K M₂]
    {Q₁ : QuadraticForm K M₁} {Q₂ : QuadraticForm K M₂}
    (f : Q₁ →qᵢ Q₂) (x : spinGroup Q₁) (v : M₁) :
    Spin.spinAction Q₂ (f.spinGroupMap x) (f v) = f (Spin.spinAction Q₁ x v) := by
  apply Spin.ι_injective' Q₂
  rw [Spin.ι_spinAction Q₂ (f.spinGroupMap x) (f v)]
  rw [← CliffordAlgebra.map_apply_ι f (Spin.spinAction Q₁ x v)]
  rw [Spin.ι_spinAction Q₁ x v]
  rw [← map_inv (f.spinGroupMap) x]
  rw [QuadraticMap.Isometry.coe_spinGroupMap_apply f x]
  rw [QuadraticMap.Isometry.coe_spinGroupMap_apply f x⁻¹]
  rw [← CliffordAlgebra.map_apply_ι f v]
  rw [map_mul, map_mul]

private lemma bmsdop_map_commute_iota_of_polar_eq_zero
    {R M₁ M₂ : Type} [CommRing R] [CharP R 2]
    [AddCommGroup M₁] [Module R M₁] [AddCommGroup M₂] [Module R M₂]
    {Q₁ : QuadraticForm R M₁} {Q₂ : QuadraticForm R M₂}
    (f : Q₁ →qᵢ Q₂) (m' : M₂)
    (hpol : ∀ v : M₁, QuadraticMap.polar (⇑Q₂) (f v) m' = 0) (a : CliffordAlgebra Q₁) :
    Commute ((CliffordAlgebra.map f) a) (CliffordAlgebra.ι Q₂ m') := by
  have hneg : ∀ b : CliffordAlgebra Q₂, -b = b := by
    intro b
    have h1 : (-1 : R) = 1 := CharTwo.neg_eq (1 : R)
    calc -b = (-1 : R) • b := (neg_one_smul R b).symm
      _ = (1 : R) • b := by rw [h1]
      _ = b := one_smul _ _
  have hx : a ∈ Algebra.adjoin R (Set.range (CliffordAlgebra.ι Q₁)) := by
    rw [CliffordAlgebra.adjoin_range_ι]; trivial
  induction hx using Algebra.adjoin_induction with
  | mem x hx =>
      obtain ⟨v, rfl⟩ := hx
      rw [CliffordAlgebra.map_apply_ι f v]
      have h := CliffordAlgebra.ι_mul_ι_add_swap (Q := Q₂) (f v) m'
      rw [hpol v, map_zero] at h
      have h' : (CliffordAlgebra.ι Q₂) (f v) * (CliffordAlgebra.ι Q₂) m' =
          (CliffordAlgebra.ι Q₂) m' * (CliffordAlgebra.ι Q₂) (f v) := by
        have h2 := add_eq_zero_iff_eq_neg.mp h
        rwa [hneg] at h2
      exact h'
  | algebraMap r =>
      rw [AlgHom.commutes]
      exact Algebra.commutes r _
  | add x y hx hy ihx ihy =>
      rw [map_add]
      exact ihx.add_left ihy
  | mul x y hx hy ihx ihy =>
      rw [map_mul]
      exact ihx.mul_left ihy

private lemma bmsdop_spinAction_spinGroupMap_eq_self
    {K M₁ M₂ : Type} [Field K]
    [AddCommGroup M₁] [Module K M₁] [AddCommGroup M₂] [Module K M₂]
    {Q₁ : QuadraticForm K M₁} {Q₂ : QuadraticForm K M₂}
    (f : Q₁ →qᵢ Q₂) (x : spinGroup Q₁) (m' : M₂)
    (hcomm : Commute ((CliffordAlgebra.map f) ↑x) (CliffordAlgebra.ι Q₂ m')) :
    Spin.spinAction Q₂ (f.spinGroupMap x) m' = m' := by
  apply Spin.ι_injective' Q₂
  rw [Spin.ι_spinAction Q₂ (f.spinGroupMap x) m']
  rw [QuadraticMap.Isometry.coe_spinGroupMap_apply f x]
  rw [hcomm.eq]
  rw [← QuadraticMap.Isometry.coe_spinGroupMap_apply f x]
  rw [mul_assoc]
  have hy : (↑(f.spinGroupMap x) : CliffordAlgebra Q₂) * ↑((f.spinGroupMap x)⁻¹) = 1 := by
    rw [← Submonoid.coe_mul, mul_inv_cancel, Submonoid.coe_one]
  rw [hy, mul_one]

private lemma bmsdop_spinGroupMap_fixes_W' (k f : ℕ)
    (S : Set (GL (Fin (k + 3) ⊕ Fin (k + 3)) (GaloisField 2 f)))
    {e : Matrix (Fin (k + 3) ⊕ Fin (k + 3)) (Fin (k + 3) ⊕ Fin (k + 3)) (GaloisField 2 f)}
    (h1 : bmsdop_geom₁ k f S e) (h2 : bmsdop_geom₂ k f S e)
    {Vstd : Type} [AddCommGroup Vstd] [Module (GaloisField 2 f) Vstd]
    [FiniteDimensional (GaloisField 2 f) Vstd]
    (Qstd : QuadraticForm (GaloisField 2 f) Vstd)
    (θ : Vstd ≃ₗ[GaloisField 2 f] ↥(bmsdop_W k f e))
    (hθ : ∀ x : Vstd, (bmsdop_blockForm k f e) (θ x) = Qstd x)
    (x : spinGroup Qstd) {w' : bmsdop_V k f} (hw' : w' ∈ bmsdop_W' k f e) :
    Spin.spinAction (bmsdop_Q k f)
      ((bmsdop_thetaIsometry k f Qstd θ hθ).spinGroupMap x) w' = w' := by
  have hpol : ∀ v : Vstd, QuadraticMap.polar (⇑(bmsdop_Q k f))
      ((bmsdop_thetaIsometry k f Qstd θ hθ) v) w' = 0 := by
    intro v
    rw [bmsdop_thetaIsometry_apply k f Qstd θ hθ v]
    exact h2.2.1 _ _ ((bmsdop_mem_W_iff h1.1 _).mp (θ v).2)
      ((bmsdop_mem_W'_iff h1.1 _).mp hw')
  exact bmsdop_spinAction_spinGroupMap_eq_self (bmsdop_thetaIsometry k f Qstd θ hθ) x w'
    (bmsdop_map_commute_iota_of_polar_eq_zero (bmsdop_thetaIsometry k f Qstd θ hθ) w' hpol x)

private lemma bmsdop_spinGroupMap_eq_glue (k f : ℕ)
    (S : Set (GL (Fin (k + 3) ⊕ Fin (k + 3)) (GaloisField 2 f)))
    {e : Matrix (Fin (k + 3) ⊕ Fin (k + 3)) (Fin (k + 3) ⊕ Fin (k + 3)) (GaloisField 2 f)}
    (h1 : bmsdop_geom₁ k f S e) (h2 : bmsdop_geom₂ k f S e)
    {Vstd : Type} [AddCommGroup Vstd] [Module (GaloisField 2 f) Vstd]
    [FiniteDimensional (GaloisField 2 f) Vstd]
    (Qstd : QuadraticForm (GaloisField 2 f) Vstd)
    (θ : Vstd ≃ₗ[GaloisField 2 f] ↥(bmsdop_W k f e))
    (hθ : ∀ x : Vstd, (bmsdop_blockForm k f e) (θ x) = Qstd x) (x : spinGroup Qstd) :
    Spin.spinAction (bmsdop_Q k f)
        ((bmsdop_thetaIsometry k f Qstd θ hθ).spinGroupMap x) =
      bmsdop_glue k f S h1 θ (Spin.spinAction Qstd x) := by
  apply LinearEquiv.ext
  intro v
  have hdecomp : e.mulVec v + (1 - e).mulVec v = v := by
    rw [← Matrix.add_mulVec]
    have hmat : e + (1 - e) = 1 := by abel
    rw [hmat, Matrix.one_mulVec]
  have hmemW : e.mulVec v ∈ bmsdop_W k f e := ⟨v, by rw [Matrix.toLin'_apply]⟩
  have hmemW' : (1 - e).mulVec v ∈ bmsdop_W' k f e := ⟨v, by rw [Matrix.toLin'_apply]⟩
  have hWpart : (Spin.spinAction (bmsdop_Q k f)
      ((bmsdop_thetaIsometry k f Qstd θ hθ).spinGroupMap x)) (e.mulVec v) =
      bmsdop_glue k f S h1 θ (Spin.spinAction Qstd x) (e.mulVec v) := by
    obtain ⟨z, hz⟩ : ∃ z : Vstd,
        ((θ z : ↥(bmsdop_W k f e)) : bmsdop_V k f) = e.mulVec v :=
      ⟨θ.symm ⟨e.mulVec v, hmemW⟩, by rw [LinearEquiv.apply_symm_apply]⟩
    calc (Spin.spinAction (bmsdop_Q k f)
            ((bmsdop_thetaIsometry k f Qstd θ hθ).spinGroupMap x)) (e.mulVec v)
        = (Spin.spinAction (bmsdop_Q k f)
            ((bmsdop_thetaIsometry k f Qstd θ hθ).spinGroupMap x))
            ((θ z : ↥(bmsdop_W k f e)) : bmsdop_V k f) := by rw [hz]
      _ = (Spin.spinAction (bmsdop_Q k f)
            ((bmsdop_thetaIsometry k f Qstd θ hθ).spinGroupMap x))
            ((bmsdop_thetaIsometry k f Qstd θ hθ) z) := by
            rw [bmsdop_thetaIsometry_apply k f Qstd θ hθ z]
      _ = (bmsdop_thetaIsometry k f Qstd θ hθ) (Spin.spinAction Qstd x z) :=
            bmsdop_spinGroupMap_spinAction (bmsdop_thetaIsometry k f Qstd θ hθ) x z
      _ = ((θ (Spin.spinAction Qstd x z) : ↥(bmsdop_W k f e)) : bmsdop_V k f) := by
            rw [bmsdop_thetaIsometry_apply k f Qstd θ hθ (Spin.spinAction Qstd x z)]
      _ = bmsdop_glue k f S h1 θ (Spin.spinAction Qstd x)
            ((θ z : ↥(bmsdop_W k f e)) : bmsdop_V k f) :=
            (bmsdop_glue_theta k f S h1 θ (Spin.spinAction Qstd x) z).symm
      _ = bmsdop_glue k f S h1 θ (Spin.spinAction Qstd x) (e.mulVec v) := by rw [hz]
  have hW'part : (Spin.spinAction (bmsdop_Q k f)
      ((bmsdop_thetaIsometry k f Qstd θ hθ).spinGroupMap x)) ((1 - e).mulVec v) =
      bmsdop_glue k f S h1 θ (Spin.spinAction Qstd x) ((1 - e).mulVec v) := by
    calc (Spin.spinAction (bmsdop_Q k f)
            ((bmsdop_thetaIsometry k f Qstd θ hθ).spinGroupMap x)) ((1 - e).mulVec v)
        = (1 - e).mulVec v :=
            bmsdop_spinGroupMap_fixes_W' k f S h1 h2 Qstd θ hθ x hmemW'
      _ = bmsdop_glue k f S h1 θ (Spin.spinAction Qstd x) ((1 - e).mulVec v) :=
            (bmsdop_glue_fixes k f S h1 θ (Spin.spinAction Qstd x) hmemW').symm
  rw [← hdecomp, map_add, map_add, hWpart, hW'part]

private lemma bmsdop_spinAction_injective (k f : ℕ) :
    Function.Injective (Spin.spinAction (bmsdop_Q k f)) := by
  rw [← MonoidHom.ker_eq_bot_iff]
  exact le_bot_iff.mp ((Spin.ker_spinAction_le_center (bmsdop_Q k f)).trans
    (le_of_eq (CFSG.StandardType.RootCentOmega.center_spinGroup_quadPlus_eq_bot_charTwo
      (n := k + 3) (K := GaloisField 2 f) (by omega))))

private lemma bmsdop_spinGroupMap_range (k f : ℕ)
    (S : Set (GL (Fin (k + 3) ⊕ Fin (k + 3)) (GaloisField 2 f)))
    {e : Matrix (Fin (k + 3) ⊕ Fin (k + 3)) (Fin (k + 3) ⊕ Fin (k + 3)) (GaloisField 2 f)}
    (h1 : bmsdop_geom₁ k f S e) (h2 : bmsdop_geom₂ k f S e)
    (hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s')
    (heA : e ∈ Algebra.adjoin (GaloisField 2 f) (Units.val '' S))
    {Vstd : Type} [AddCommGroup Vstd] [Module (GaloisField 2 f) Vstd]
    [FiniteDimensional (GaloisField 2 f) Vstd]
    (Qstd : QuadraticForm (GaloisField 2 f) Vstd)
    (hnd_std : (QuadraticMap.polarBilin Qstd).Nondegenerate)
    (E : (Vstd ≃ₗ[GaloisField 2 f] Vstd) →* (bmsdop_V k f ≃ₗ[GaloisField 2 f] bmsdop_V k f))
    (θ : Vstd ≃ₗ[GaloisField 2 f] ↥(bmsdop_W k f e))
    (hE : bmsdop_ExtProps k f S e Qstd hnd_std θ E)
    (hθ : ∀ x : Vstd, (bmsdop_blockForm k f e) (θ x) = Qstd x)
    (hΩ : (Spin.spinAction Qstd).range =
      CFSG.RankThree.OrthogonalInvolutions.omegaGroup Qstd hnd_std) :
    (bmsdop_thetaIsometry k f Qstd θ hθ).spinGroupMap.range = bmsdop_Ge k f S e := by
  apply le_antisymm
  · rintro u ⟨x, rfl⟩
    refine bmsdop_mem_Ge_of_action k f S
      ((bmsdop_thetaIsometry k f Qstd θ hθ).spinGroupMap x) ?_ ?_
    · intro v hv
      rw [bmsdop_spinGroupMap_eq_glue k f S h1 h2 Qstd θ hθ x]
      exact bmsdop_glue_fixes k f S h1 θ (Spin.spinAction Qstd x) hv
    · intro s hs v
      rw [bmsdop_spinGroupMap_eq_glue k f S h1 h2 Qstd θ hθ x]
      exact bmsdop_glue_commute_S k f S h1 h2 hS heA θ (Spin.spinAction Qstd x) s hs v
  · intro u hu
    have hmem : Spin.spinAction (bmsdop_Q k f) u ∈
        (CFSG.RankThree.OrthogonalInvolutions.omegaGroup Qstd hnd_std).map E := by
      rw [← bmsdop_block_group_eq_ext k f S h1 h2 hS heA Qstd hnd_std E θ hE]
      exact Subgroup.mem_map.mpr ⟨u, hu, rfl⟩
    obtain ⟨g, hgΩ, hgu⟩ := Subgroup.mem_map.mp hmem
    obtain ⟨x, hx⟩ := MonoidHom.mem_range.mp (hΩ.symm ▸ hgΩ)
    refine ⟨x, bmsdop_spinAction_injective k f ?_⟩
    rw [bmsdop_spinGroupMap_eq_glue k f S h1 h2 Qstd θ hθ x,
      ← DFunLike.congr_fun (bmsdop_ext_eq_glue k f S h1 Qstd hnd_std E θ hE)
        (Spin.spinAction Qstd x),
      hx, hgu]

private lemma bmsdop_thetaIsometry_injective (k f : ℕ)
    {e : Matrix (Fin (k + 3) ⊕ Fin (k + 3)) (Fin (k + 3) ⊕ Fin (k + 3)) (GaloisField 2 f)}
    {Vstd : Type} [AddCommGroup Vstd] [Module (GaloisField 2 f) Vstd]
    [FiniteDimensional (GaloisField 2 f) Vstd]
    (Qstd : QuadraticForm (GaloisField 2 f) Vstd)
    (θ : Vstd ≃ₗ[GaloisField 2 f] ↥(bmsdop_W k f e))
    (hθ : ∀ x : Vstd, (bmsdop_blockForm k f e) (θ x) = Qstd x) :
    Function.Injective (bmsdop_thetaIsometry k f Qstd θ hθ) :=
  fun _ _ h => θ.injective (Subtype.ext h)

private lemma bmsdop_spinAction_injective_of (f : ℕ) {Vstd : Type} [AddCommGroup Vstd]
    [Module (GaloisField 2 f) Vstd] [FiniteDimensional (GaloisField 2 f) Vstd]
    (Qstd : QuadraticForm (GaloisField 2 f) Vstd)
    (hnd_std : (QuadraticMap.polarBilin Qstd).Nondegenerate)
    [Algebra.IsCentral (GaloisField 2 f) (CliffordAlgebra Qstd)] :
    Function.Injective (Spin.spinAction Qstd) := by
  rw [← MonoidHom.ker_eq_bot_iff]
  exact Spin.ker_spinAction_eq_bot_of_isCentral Qstd (CharP.cast_eq_zero (GaloisField 2 f) 2)

private lemma bmsdop_spinGroupMap_injective (k f : ℕ)
    {e : Matrix (Fin (k + 3) ⊕ Fin (k + 3)) (Fin (k + 3) ⊕ Fin (k + 3)) (GaloisField 2 f)}
    {Vstd : Type} [AddCommGroup Vstd] [Module (GaloisField 2 f) Vstd]
    [FiniteDimensional (GaloisField 2 f) Vstd]
    (Qstd : QuadraticForm (GaloisField 2 f) Vstd)
    (hnd_std : (QuadraticMap.polarBilin Qstd).Nondegenerate)
    [Algebra.IsCentral (GaloisField 2 f) (CliffordAlgebra Qstd)]
    (θ : Vstd ≃ₗ[GaloisField 2 f] ↥(bmsdop_W k f e))
    (hθ : ∀ x : Vstd, (bmsdop_blockForm k f e) (θ x) = Qstd x) :
    Function.Injective (bmsdop_thetaIsometry k f Qstd θ hθ).spinGroupMap := by
  intro x y hxy
  have hact : Spin.spinAction Qstd x = Spin.spinAction Qstd y := by
    ext v
    have hx := bmsdop_spinGroupMap_spinAction (bmsdop_thetaIsometry k f Qstd θ hθ) x v
    have hy := bmsdop_spinGroupMap_spinAction (bmsdop_thetaIsometry k f Qstd θ hθ) y v
    rw [hxy] at hx
    exact bmsdop_thetaIsometry_injective k f Qstd θ hθ (hx.symm.trans hy)
  have hker : Spin.spinAction Qstd (x * y⁻¹) = 1 := by
    rw [map_mul, map_inv, hact, mul_inv_cancel]
  exact mul_inv_eq_one.mp (bmsdop_spinAction_injective_of f Qstd hnd_std
    (hker.trans (map_one (Spin.spinAction Qstd)).symm))

private lemma bmsdop_spinGroupMap_center (k f : ℕ)
    {e : Matrix (Fin (k + 3) ⊕ Fin (k + 3)) (Fin (k + 3) ⊕ Fin (k + 3)) (GaloisField 2 f)}
    {Vstd : Type} [AddCommGroup Vstd] [Module (GaloisField 2 f) Vstd]
    [FiniteDimensional (GaloisField 2 f) Vstd]
    (Qstd : QuadraticForm (GaloisField 2 f) Vstd)
    (hnd_std : (QuadraticMap.polarBilin Qstd).Nondegenerate)
    [Algebra.IsCentral (GaloisField 2 f) (CliffordAlgebra Qstd)]
    (θ : Vstd ≃ₗ[GaloisField 2 f] ↥(bmsdop_W k f e))
    (hθ : ∀ x : Vstd, (bmsdop_blockForm k f e) (θ x) = Qstd x) :
    ∀ y, (bmsdop_thetaIsometry k f Qstd θ hθ).spinGroupMap y ∈
        Subgroup.center ↥(spinGroup (bmsdop_Q k f)) →
      y ∈ Subgroup.center (spinGroup Qstd) := by
  intro y hy
  rw [Subgroup.mem_center_iff] at hy ⊢
  intro x
  apply bmsdop_spinGroupMap_injective k f Qstd hnd_std θ hθ
  rw [map_mul, map_mul]
  exact hy ((bmsdop_thetaIsometry k f Qstd θ hθ).spinGroupMap x)

private theorem bmsdop_iota₁
    (k f : ℕ) (S : Set (GL (Fin (k + 3) ⊕ Fin (k + 3)) (GaloisField 2 f)))
    {e : Matrix (Fin (k + 3) ⊕ Fin (k + 3)) (Fin (k + 3) ⊕ Fin (k + 3)) (GaloisField 2 f)}
    (h1 : bmsdop_geom₁ k f S e) (h2 : bmsdop_geom₂ k f S e)
    (hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s')
    (heA : e ∈ Algebra.adjoin (GaloisField 2 f) (Units.val '' S))
    {Vstd : Type} [AddCommGroup Vstd] [Module (GaloisField 2 f) Vstd]
    [FiniteDimensional (GaloisField 2 f) Vstd]
    (Qstd : QuadraticForm (GaloisField 2 f) Vstd)
    (hnd_std : (QuadraticMap.polarBilin Qstd).Nondegenerate)
    [Algebra.IsCentral (GaloisField 2 f) (CliffordAlgebra Qstd)]
    (E : (Vstd ≃ₗ[GaloisField 2 f] Vstd) →*
        (((Fin (k + 3) ⊕ Fin (k + 3)) → GaloisField 2 f) ≃ₗ[GaloisField 2 f]
          ((Fin (k + 3) ⊕ Fin (k + 3)) → GaloisField 2 f)))
    (θ : Vstd ≃ₗ[GaloisField 2 f] ↥(bmsdop_W k f e))
    (hE : bmsdop_ExtProps k f S e Qstd hnd_std θ E)
    (hθ : ∀ x : Vstd, (bmsdop_blockForm k f e) (θ x) = Qstd x)
    (hΩ : (Spin.spinAction Qstd).range =
      CFSG.RankThree.OrthogonalInvolutions.omegaGroup Qstd hnd_std) :
    ∃ (ι₁ : spinGroup Qstd →* spinGroup (bmsdop_Q k f)),
      Function.Injective ι₁ ∧ ι₁.range = bmsdop_Ge k f S e ∧
      (∀ x, Spin.spinAction (bmsdop_Q k f) (ι₁ x) = E (Spin.spinAction Qstd x)) ∧
      (∀ y, ι₁ y ∈ Subgroup.center ↥(spinGroup (bmsdop_Q k f)) →
        y ∈ Subgroup.center (spinGroup Qstd)) := by
  have hEglue : E = bmsdop_glue k f S h1 θ :=
    bmsdop_ext_eq_glue k f S h1 Qstd hnd_std E θ hE
  refine ⟨(bmsdop_thetaIsometry k f Qstd θ hθ).spinGroupMap,
    bmsdop_spinGroupMap_injective k f Qstd hnd_std θ hθ,
    bmsdop_spinGroupMap_range k f S h1 h2 hS heA Qstd hnd_std E θ hE hθ hΩ, ?_, ?_⟩
  · intro x
    exact (bmsdop_spinGroupMap_eq_glue k f S h1 h2 Qstd θ hθ x).trans
      (DFunLike.congr_fun hEglue (Spin.spinAction Qstd x)).symm
  · intro y
    exact bmsdop_spinGroupMap_center k f Qstd hnd_std θ hθ y

private theorem bmsdop_std_quasisimple_plus (f ρ : ℕ) (hρ : 3 ≤ ρ) :
    IsQuasisimple (spinGroup (Spin.quadPlus ρ (GaloisField 2 f))) :=
  Spin.isQuasisimple_spinGroup_quadPlus hρ

private theorem bmsdop_std_quasisimple_minus (f ρ : ℕ) (hρ : 4 ≤ ρ) (β γ : GaloisField 2 f)
    (hirr : ∀ s : GaloisField 2 f, s ^ 2 + β * s + γ ≠ 0) :
    IsQuasisimple (spinGroup (Spin.quadMinus ρ (GaloisField 2 f) β γ)) :=
  Spin.isQuasisimple_spinGroup_quadMinus hρ hirr

private theorem bmsdop_component_eq
    (k f : ℕ) (S : Set (GL (Fin (k + 3) ⊕ Fin (k + 3)) (GaloisField 2 f)))
    {e : Matrix (Fin (k + 3) ⊕ Fin (k + 3)) (Fin (k + 3) ⊕ Fin (k + 3)) (GaloisField 2 f)}
    {J' : Subgroup ↥(spinGroup (bmsdop_Q k f))}
    (h1 : bmsdop_geom₁ k f S e) (h2 : bmsdop_geom₂ k f S e)
    {Vstd : Type} [AddCommGroup Vstd] [Module (GaloisField 2 f) Vstd]
    [FiniteDimensional (GaloisField 2 f) Vstd]
    (Qstd : QuadraticForm (GaloisField 2 f) Vstd)
    (hq : IsQuasisimple (spinGroup Qstd))
    (ι₁ : spinGroup Qstd →* spinGroup (bmsdop_Q k f))
    (hι₁ : Function.Injective ι₁ ∧ ι₁.range = bmsdop_Ge k f S e)
    (hJe : IsComponentOf J' ⁅bmsdop_Ge k f S e, bmsdop_Ge k f S e⁆) :
    J' = bmsdop_Ge k f S e := by
  classical
  let ι₁' : spinGroup Qstd →* ↥(bmsdop_Ge k f S e) :=
    { toFun := fun x => ⟨ι₁ x, hι₁.2.le (MonoidHom.mem_range.mpr ⟨x, rfl⟩)⟩
      map_one' := Subtype.ext (map_one ι₁)
      map_mul' := fun a b => Subtype.ext (map_mul ι₁ a b) }
  have hι₁' : Function.Bijective ι₁' := by
    constructor
    · intro a b hab
      exact hι₁.1 (Subtype.ext_iff.mp hab)
    · intro y
      obtain ⟨x, hx⟩ := MonoidHom.mem_range.mp (hι₁.2.symm.le y.2)
      exact ⟨x, Subtype.ext hx⟩
  let φe : spinGroup Qstd ≃* ↥(bmsdop_Ge k f S e) := MulEquiv.ofBijective ι₁' hι₁'
  have hqOpen : CFSG.Open.IsQuasisimple (spinGroup Qstd) :=
    ⟨(Group.isPerfect_def).mp hq.1, hq.2.1⟩
  have hGq : CFSG.Open.IsQuasisimple ↥(bmsdop_Ge k f S e) :=
    CFSG.ComponentClassification.Components.quasisimple_of_equiv φe.symm hqOpen
  have hcomm : ⁅bmsdop_Ge k f S e, bmsdop_Ge k f S e⁆ = bmsdop_Ge k f S e := by
    have hmap : Subgroup.map (Subgroup.subtype (bmsdop_Ge k f S e))
        (commutator ↥(bmsdop_Ge k f S e)) = ⁅bmsdop_Ge k f S e, bmsdop_Ge k f S e⁆ := by
      rw [commutator_def, Subgroup.map_commutator, Subgroup.map_top, Subgroup.range_subtype]
    rw [hGq.1, Subgroup.map_top, Subgroup.range_subtype] at hmap
    exact hmap.symm
  have hJeOpen : CFSG.Open.IsComponentOf J' (bmsdop_Ge k f S e) := by
    have h := (CFSG.Assembly.isComponentOf_iff_open).mp hJe
    rwa [hcomm] at h
  exact CFSG.Fischer.Classification.Recognition.IsComponentOf.eq_of_isQuasisimple hJeOpen hGq

private lemma bmsdop_eichler_coe (k f : ℕ)
    {e : Matrix (Fin (k + 3) ⊕ Fin (k + 3)) (Fin (k + 3) ⊕ Fin (k + 3)) (GaloisField 2 f)}
    (u w x : ↥(bmsdop_W k f e))
    (hu : (bmsdop_Q k f) (u : bmsdop_V k f) = 0)
    (huw : QuadraticMap.polar (⇑(bmsdop_Q k f)) (u : bmsdop_V k f) (w : bmsdop_V k f) = 0) :
    ((CFSG.ClassicalGroups.Orthogonal.eichler (bmsdop_blockForm k f e) u w x : ↥(bmsdop_W k f e)) :
        bmsdop_V k f) =
      CFSG.ClassicalGroups.Orthogonal.eichler (bmsdop_Q k f) (u : bmsdop_V k f) (w : bmsdop_V k f)
        (x : bmsdop_V k f) := by
  rw [CFSG.ClassicalGroups.Orthogonal.eichler_apply,
    CFSG.ClassicalGroups.Orthogonal.eichler_apply hu huw]
  · simp only [Submodule.coe_add, Submodule.coe_sub, Submodule.coe_smul,
      QuadraticMap.polarBilin_comp,
      LinearMap.compl₁₂_apply, QuadraticMap.polarBilin_apply_apply]
    rfl
  · exact hu
  · exact huw

private lemma bmsdop_polar_theta (k f : ℕ)
    {e : Matrix (Fin (k + 3) ⊕ Fin (k + 3)) (Fin (k + 3) ⊕ Fin (k + 3)) (GaloisField 2 f)}
    {Vstd : Type} [AddCommGroup Vstd] [Module (GaloisField 2 f) Vstd]
    (Qstd : QuadraticForm (GaloisField 2 f) Vstd)
    (θ : Vstd ≃ₗ[GaloisField 2 f] ↥(bmsdop_W k f e))
    (hθ : ∀ x, (bmsdop_blockForm k f e) (θ x) = Qstd x) (u w : Vstd) :
    QuadraticMap.polar (⇑(bmsdop_Q k f)) (θ u) (θ w) = QuadraticMap.polar (⇑Qstd) u w := by
  have hQ : Qstd = (bmsdop_blockForm k f e).comp θ.toLinearMap :=
    QuadraticMap.ext (fun x => (hθ x).symm)
  rw [hQ, ← QuadraticMap.polarBilin_apply_apply, ← QuadraticMap.polarBilin_apply_apply,
    QuadraticMap.polarBilin_comp, LinearMap.compl₁₂_apply]
  simp only [QuadraticMap.polarBilin_apply_apply]
  rfl

private lemma bmsdop_ext_eichler (k f : ℕ)
    (S : Set (GL (Fin (k + 3) ⊕ Fin (k + 3)) (GaloisField 2 f)))
    {e : Matrix (Fin (k + 3) ⊕ Fin (k + 3)) (Fin (k + 3) ⊕ Fin (k + 3)) (GaloisField 2 f)}
    (h1 : bmsdop_geom₁ k f S e) (h2 : bmsdop_geom₂ k f S e)
    {Vstd : Type} [AddCommGroup Vstd] [Module (GaloisField 2 f) Vstd]
    [FiniteDimensional (GaloisField 2 f) Vstd]
    (Qstd : QuadraticForm (GaloisField 2 f) Vstd)
    (hnd_std : (QuadraticMap.polarBilin Qstd).Nondegenerate)
    (θ : Vstd ≃ₗ[GaloisField 2 f] ↥(bmsdop_W k f e))
    (hθ : ∀ x, (bmsdop_blockForm k f e) (θ x) = Qstd x)
    (E : (Vstd ≃ₗ[GaloisField 2 f] Vstd) →*
        (bmsdop_V k f ≃ₗ[GaloisField 2 f] bmsdop_V k f))
    (hE : bmsdop_ExtProps k f S e Qstd hnd_std θ E) (u w : Vstd)
    (hu : Qstd u = 0) (huw : QuadraticMap.polar (⇑Qstd) u w = 0) :
    E (CFSG.ClassicalGroups.Orthogonal.eichler Qstd u w) =
      CFSG.ClassicalGroups.Orthogonal.eichler (bmsdop_Q k f) (θ u) (θ w) := by
  rw [show E = bmsdop_glue k f S h1 θ from bmsdop_ext_eq_glue k f S h1 Qstd hnd_std E θ hE]
  have hθu : (bmsdop_Q k f) (θ u) = 0 := by
    rw [show (bmsdop_Q k f) (θ u) = (bmsdop_blockForm k f e) (θ u) from rfl, hθ u, hu]
  have hθuw : QuadraticMap.polar (⇑(bmsdop_Q k f)) (θ u) (θ w) = 0 := by
    rw [bmsdop_polar_theta k f Qstd θ hθ u w, huw]
  have honW : ∀ x : Vstd, CFSG.ClassicalGroups.Orthogonal.eichler (bmsdop_Q k f) (θ u) (θ w) (θ x) =
      θ (CFSG.ClassicalGroups.Orthogonal.eichler Qstd u w x) := by
    intro x
    rw [← bmsdop_eichler_coe k f (θ u) (θ w) (θ x) hθu hθuw]
    have h := congrArg (fun (g : Vstd ≃ₗ[GaloisField 2 f] Vstd) => g x)
      (CFSG.RankThree.PartTwo.Census.Carrier.SpinD.eichler_isometry θ hθ u w)
    simpa using congrArg θ h
  have hfixW' : ∀ v ∈ bmsdop_W' k f e,
      CFSG.ClassicalGroups.Orthogonal.eichler (bmsdop_Q k f) (θ u) (θ w) v = v := by
    intro v hv
    rw [CFSG.ClassicalGroups.Orthogonal.eichler_apply_of_polar_eq_zero]
    · rw [QuadraticMap.polar_comm]
      exact h2.2.1 _ _ ((bmsdop_mem_W_iff h1.1 _).mp (θ u).2) ((bmsdop_mem_W'_iff h1.1 _).mp hv)
    · rw [QuadraticMap.polar_comm]
      exact h2.2.1 _ _ ((bmsdop_mem_W_iff h1.1 _).mp (θ w).2) ((bmsdop_mem_W'_iff h1.1 _).mp hv)
  apply LinearEquiv.ext
  intro v
  have hdecomp : e.mulVec v + (1 - e).mulVec v = v := by
    rw [← Matrix.add_mulVec]
    have hmat : e + (1 - e) = 1 := by abel
    rw [hmat, Matrix.one_mulVec]
  have hmemW : e.mulVec v ∈ bmsdop_W k f e := ⟨v, by rw [Matrix.toLin'_apply]⟩
  have hmemW' : (1 - e).mulVec v ∈ bmsdop_W' k f e := ⟨v, by rw [Matrix.toLin'_apply]⟩
  rw [← hdecomp, map_add, map_add]
  congr 1
  · obtain ⟨x, hx⟩ : ∃ x : Vstd, (θ x : bmsdop_V k f) = e.mulVec v :=
      ⟨θ.symm ⟨e.mulVec v, hmemW⟩, by rw [LinearEquiv.apply_symm_apply]⟩
    calc bmsdop_glue k f S h1 θ (CFSG.ClassicalGroups.Orthogonal.eichler Qstd u w) (e.mulVec v)
        = bmsdop_glue k f S h1 θ (CFSG.ClassicalGroups.Orthogonal.eichler Qstd u w) (θ x) := by
            rw [hx]
      _ = θ (CFSG.ClassicalGroups.Orthogonal.eichler Qstd u w x) :=
            bmsdop_glue_theta k f S h1 θ (CFSG.ClassicalGroups.Orthogonal.eichler Qstd u w) x
      _ = CFSG.ClassicalGroups.Orthogonal.eichler (bmsdop_Q k f) (θ u) (θ w) (θ x) :=
            (honW x).symm
      _ = CFSG.ClassicalGroups.Orthogonal.eichler (bmsdop_Q k f) (θ u) (θ w) (e.mulVec v) := by
            rw [hx]
  · calc bmsdop_glue k f S h1 θ (CFSG.ClassicalGroups.Orthogonal.eichler Qstd u w)
          ((1 - e).mulVec v)
        = (1 - e).mulVec v :=
            bmsdop_glue_fixes k f S h1 θ (CFSG.ClassicalGroups.Orthogonal.eichler Qstd u w) hmemW'
      _ = CFSG.ClassicalGroups.Orthogonal.eichler (bmsdop_Q k f) (θ u) (θ w)
            ((1 - e).mulVec v) := (hfixW' _ hmemW').symm

private theorem bmsdop_ext_siegel
    (k f : ℕ) (S : Set (GL (Fin (k + 3) ⊕ Fin (k + 3)) (GaloisField 2 f)))
    {e : Matrix (Fin (k + 3) ⊕ Fin (k + 3)) (Fin (k + 3) ⊕ Fin (k + 3)) (GaloisField 2 f)}
    (h1 : bmsdop_geom₁ k f S e) (h2 : bmsdop_geom₂ k f S e)
    {Vstd : Type} [AddCommGroup Vstd] [Module (GaloisField 2 f) Vstd]
    [FiniteDimensional (GaloisField 2 f) Vstd]
    (Qstd : QuadraticForm (GaloisField 2 f) Vstd)
    (hnd_std : (QuadraticMap.polarBilin Qstd).Nondegenerate)
    (θ : Vstd ≃ₗ[GaloisField 2 f] ↥(bmsdop_W k f e))
    (hθ : ∀ x, (bmsdop_blockForm k f e) (θ x) = Qstd x)
    (E : (Vstd ≃ₗ[GaloisField 2 f] Vstd) →*
        (bmsdop_V k f ≃ₗ[GaloisField 2 f] bmsdop_V k f))
    (hE : bmsdop_ExtProps k f S e Qstd hnd_std θ E)
    (a b : Vstd) (ha : Qstd a = 0) (hab : QuadraticMap.polar (⇑Qstd) a b = 0) :
    (siegelGroup Qstd a b).map E = siegelGroup (bmsdop_Q k f) (θ a) (θ b) := by
  have hpol : ∀ c : GaloisField 2 f, QuadraticMap.polar (⇑Qstd) a (c • b) = 0 := fun c => by
    rw [QuadraticMap.polar_smul_right, hab, smul_zero]
  rw [siegelGroup, siegelGroup, MonoidHom.map_closure]
  apply le_antisymm
  · rw [Subgroup.closure_le]
    rintro g ⟨h, ⟨c, rfl⟩, rfl⟩
    exact Subgroup.subset_closure ⟨c, by
      rw [bmsdop_ext_eichler k f S h1 h2 Qstd hnd_std θ hθ E hE a (c • b) ha (hpol c),
        map_smul, Submodule.coe_smul]⟩
  · rw [Subgroup.closure_le]
    rintro g ⟨c, rfl⟩
    exact Subgroup.subset_closure ⟨CFSG.ClassicalGroups.Orthogonal.eichler Qstd a (c • b),
      ⟨c, rfl⟩, by
      rw [bmsdop_ext_eichler k f S h1 h2 Qstd hnd_std θ hθ E hE a (c • b) ha (hpol c),
        map_smul, Submodule.coe_smul]⟩

private theorem bmsdop_root_siegel
    (k f : ℕ) (S : Set (GL (Fin (k + 3) ⊕ Fin (k + 3)) (GaloisField 2 f)))
    {e : Matrix (Fin (k + 3) ⊕ Fin (k + 3)) (Fin (k + 3) ⊕ Fin (k + 3)) (GaloisField 2 f)}
    (h1 : bmsdop_geom₁ k f S e) (h2 : bmsdop_geom₂ k f S e)
    {Vstd : Type} [AddCommGroup Vstd] [Module (GaloisField 2 f) Vstd]
    [FiniteDimensional (GaloisField 2 f) Vstd]
    (Qstd : QuadraticForm (GaloisField 2 f) Vstd)
    (hnd_std : (QuadraticMap.polarBilin Qstd).Nondegenerate)
    (θ : Vstd ≃ₗ[GaloisField 2 f] ↥(bmsdop_W k f e))
    (hθ : ∀ x, (bmsdop_blockForm k f e) (θ x) = Qstd x)
    (D : UniversalRootDatum (spinGroup Qstd))
    (ι₁ : spinGroup Qstd →* spinGroup (bmsdop_Q k f))
    (hι₁ : Function.Injective ι₁ ∧ ι₁.range = bmsdop_Ge k f S e)
    (E : (Vstd ≃ₗ[GaloisField 2 f] Vstd) →*
        (bmsdop_V k f ≃ₗ[GaloisField 2 f] bmsdop_V k f))
    (hE : bmsdop_ExtProps k f S e Qstd hnd_std θ E)
    (hιE : ∀ x, Spin.spinAction (bmsdop_Q k f) (ι₁ x) = E (Spin.spinAction Qstd x))
    (hD : ∀ a₁ a₂ b₁ b₂ : Vstd,
      (Qstd a₁ = 0 ∧ Qstd a₂ = 0 ∧ Qstd b₁ = 0 ∧ Qstd b₂ = 0) →
      QuadraticMap.polar Qstd a₁ b₁ = 1 → QuadraticMap.polar Qstd a₂ b₂ = 1 →
      (QuadraticMap.polar Qstd a₁ a₂ = 0 ∧ QuadraticMap.polar Qstd b₁ b₂ = 0 ∧
        QuadraticMap.polar Qstd a₁ b₂ = 0 ∧ QuadraticMap.polar Qstd a₂ b₁ = 0) →
      ∃ β : Fin D.rank → ℤ, β ∈ D.roots ∧ GGLongRoot D β ∧
        ∃ u : spinGroup Qstd,
          (((D.rootGroup β).map (MulAut.conj u).toMonoidHom).map
            (Spin.spinAction Qstd) = siegelGroup Qstd a₁ a₂) ∧
          (((D.rootGroup (-β)).map (MulAut.conj u).toMonoidHom).map
            (Spin.spinAction Qstd) = siegelGroup Qstd b₁ b₂))
    (hfr : ∃ a₁ a₂ b₁ b₂ : Vstd,
      (Qstd a₁ = 0 ∧ Qstd a₂ = 0 ∧ Qstd b₁ = 0 ∧ Qstd b₂ = 0) ∧
      QuadraticMap.polar Qstd a₁ b₁ = 1 ∧ QuadraticMap.polar Qstd a₂ b₂ = 1 ∧
      (QuadraticMap.polar Qstd a₁ a₂ = 0 ∧ QuadraticMap.polar Qstd b₁ b₂ = 0 ∧
        QuadraticMap.polar Qstd a₁ b₂ = 0 ∧ QuadraticMap.polar Qstd a₂ b₁ = 0)) :
    ∃ (β₀ : Fin D.rank → ℤ) (u₀ : spinGroup Qstd) (a₁ a₂ b₁ b₂ : Vstd),
      GGLongRoot D β₀ ∧
      (Qstd a₁ = 0 ∧ Qstd a₂ = 0 ∧ Qstd b₁ = 0 ∧ Qstd b₂ = 0) ∧
      QuadraticMap.polar Qstd a₁ b₁ = 1 ∧ QuadraticMap.polar Qstd a₂ b₂ = 1 ∧
      (QuadraticMap.polar Qstd a₁ a₂ = 0 ∧ QuadraticMap.polar Qstd b₁ b₂ = 0 ∧
        QuadraticMap.polar Qstd a₁ b₂ = 0 ∧ QuadraticMap.polar Qstd a₂ b₁ = 0) ∧
      ((((D.rootGroup β₀).map (MulAut.conj u₀).toMonoidHom).map ι₁).map
        (Spin.spinAction (bmsdop_Q k f)) = siegelGroup (bmsdop_Q k f) (θ a₁) (θ a₂)) ∧
      ((((D.rootGroup (-β₀)).map (MulAut.conj u₀).toMonoidHom).map ι₁).map
        (Spin.spinAction (bmsdop_Q k f)) = siegelGroup (bmsdop_Q k f) (θ b₁) (θ b₂)) := by
  obtain ⟨a₁, a₂, b₁, b₂, hframe, hpol₁, hpol₂, horth⟩ := hfr
  obtain ⟨β, _hβroot, hβlong, u, hu₁, hu₂⟩ := hD a₁ a₂ b₁ b₂ hframe hpol₁ hpol₂ horth
  have hιE' : (Spin.spinAction (bmsdop_Q k f)).comp ι₁ = E.comp (Spin.spinAction Qstd) :=
    MonoidHom.ext hιE
  refine ⟨β, u, a₁, a₂, b₁, b₂, hβlong, hframe, hpol₁, hpol₂, horth, ?_, ?_⟩
  · rw [Subgroup.map_map, hιE', ← Subgroup.map_map, hu₁,
      bmsdop_ext_siegel k f S h1 h2 Qstd hnd_std θ hθ E hE a₁ a₂ hframe.1 horth.1]
  · rw [Subgroup.map_map, hιE', ← Subgroup.map_map, hu₂,
      bmsdop_ext_siegel k f S h1 h2 Qstd hnd_std θ hθ E hE b₁ b₂ hframe.2.2.1 horth.2.1]

private lemma bmsdop_Ge_spinAction_fixes_W' (k f : ℕ)
    (S : Set (GL (Fin (k + 3) ⊕ Fin (k + 3)) (GaloisField 2 f)))
    {e : Matrix (Fin (k + 3) ⊕ Fin (k + 3)) (Fin (k + 3) ⊕ Fin (k + 3)) (GaloisField 2 f)}
    (x : spinGroup (bmsdop_Q k f)) (hx : x ∈ bmsdop_Ge k f S e) :
    ∀ v : bmsdop_V k f, v ∈ bmsdop_W' k f e → Spin.spinAction (bmsdop_Q k f) x v = v := by
  intro v hv
  have hx' : Spin.spinMatrix (bmsdop_Q k f) x ∈
      Subgroup.centralizer S ⊓ glFixing (1 - e) := by
    have h := hx
    rwa [bmsdop_Ge, glBlockCentralizer, Subgroup.mem_comap] at h
  have hxfix : ((Spin.spinMatrix (bmsdop_Q k f) x : GL (Fin (k + 3) ⊕ Fin (k + 3))
        (GaloisField 2 f)) : Matrix (Fin (k + 3) ⊕ Fin (k + 3))
          (Fin (k + 3) ⊕ Fin (k + 3)) (GaloisField 2 f)) * (1 - e) = 1 - e :=
    (Subgroup.mem_inf.mp hx').2
  obtain ⟨a, ha⟩ := hv
  have ha' : (1 - e).mulVec a = v := by rw [← ha, Matrix.toLin'_apply]
  rw [← Spin.spinMatrix_mulVec, ← ha', Matrix.mulVec_mulVec, hxfix]

private lemma bmsdop_mem_W_of_polar_W'_eq_zero (k f : ℕ)
    (S : Set (GL (Fin (k + 3) ⊕ Fin (k + 3)) (GaloisField 2 f)))
    {e : Matrix (Fin (k + 3) ⊕ Fin (k + 3)) (Fin (k + 3) ⊕ Fin (k + 3)) (GaloisField 2 f)}
    (h1 : bmsdop_geom₁ k f S e) (h2 : bmsdop_geom₂ k f S e)
    {v : bmsdop_V k f}
    (hv : ∀ w' : bmsdop_V k f, w' ∈ bmsdop_W' k f e →
      QuadraticMap.polar (⇑(bmsdop_Q k f)) v w' = 0) :
    v ∈ bmsdop_W k f e := by
  have hVnd : (QuadraticMap.polarBilin (bmsdop_Q k f)).Nondegenerate :=
    Spin.nondegenerate_polarBilin_quadPlus (k + 3) (GaloisField 2 f)
  have hW'nd : ∀ w' : bmsdop_V k f, w' ∈ bmsdop_W' k f e →
      (∀ u : bmsdop_V k f, u ∈ bmsdop_W' k f e →
        QuadraticMap.polar (⇑(bmsdop_Q k f)) w' u = 0) → w' = 0 := by
    intro w' hw' horth
    apply hVnd.1 w'
    intro y
    rw [QuadraticMap.polarBilin_apply_apply]
    have hdecomp : y = e.mulVec y + (1 - e).mulVec y := by
      rw [← Matrix.add_mulVec]
      have hmat : e + (1 - e) = 1 := by abel
      rw [hmat, Matrix.one_mulVec]
    rw [hdecomp, QuadraticMap.polar_add_right]
    have h1' : QuadraticMap.polar (⇑(bmsdop_Q k f)) w' (e.mulVec y) = 0 := by
      rw [QuadraticMap.polar_comm]
      exact h2.2.1 (e.mulVec y) w'
        (by rw [Matrix.mulVec_mulVec, h1.1.eq])
        ((bmsdop_mem_W'_iff h1.1 w').mp hw')
    have h2' : QuadraticMap.polar (⇑(bmsdop_Q k f)) w' ((1 - e).mulVec y) = 0 :=
      horth ((1 - e).mulVec y) ⟨y, by rw [Matrix.toLin'_apply]⟩
    rw [h1', h2', add_zero]
  have hmem : (1 - e).mulVec v ∈ bmsdop_W' k f e := ⟨v, by rw [Matrix.toLin'_apply]⟩
  have hzero : (1 - e).mulVec v = 0 := by
    apply hW'nd _ hmem
    intro u hu
    have hdecomp2 : v = e.mulVec v + (1 - e).mulVec v := by
      rw [← Matrix.add_mulVec]
      have hmat : e + (1 - e) = 1 := by abel
      rw [hmat, Matrix.one_mulVec]
    have hvu : QuadraticMap.polar (⇑(bmsdop_Q k f)) ((1 - e).mulVec v) u = 0 := by
      have h := hv u hu
      rw [hdecomp2, QuadraticMap.polar_add_left] at h
      have h1'' : QuadraticMap.polar (⇑(bmsdop_Q k f)) (e.mulVec v) u = 0 :=
        h2.2.1 (e.mulVec v) u
          (by rw [Matrix.mulVec_mulVec, h1.1.eq])
          ((bmsdop_mem_W'_iff h1.1 u).mp hu)
      rw [h1'', zero_add] at h
      exact h
    exact hvu
  have hdecomp3 : v = e.mulVec v + (1 - e).mulVec v := by
    rw [← Matrix.add_mulVec]
    have hmat : e + (1 - e) = 1 := by abel
    rw [hmat, Matrix.one_mulVec]
  rw [hdecomp3, hzero, add_zero]
  exact ⟨v, by rw [Matrix.toLin'_apply]⟩

private theorem bmsdop_closure
    (k f : ℕ) (S : Set (GL (Fin (k + 3) ⊕ Fin (k + 3)) (GaloisField 2 f)))
    {e : Matrix (Fin (k + 3) ⊕ Fin (k + 3)) (Fin (k + 3) ⊕ Fin (k + 3)) (GaloisField 2 f)}
    {J' : Subgroup ↥(spinGroup (bmsdop_Q k f))}
    (h1 : bmsdop_geom₁ k f S e) (h2 : bmsdop_geom₂ k f S e)
    (hJe : IsComponentOf J' ⁅bmsdop_Ge k f S e, bmsdop_Ge k f S e⁆)
    {Vstd : Type} [AddCommGroup Vstd] [Module (GaloisField 2 f) Vstd]
    [FiniteDimensional (GaloisField 2 f) Vstd]
    (Qstd : QuadraticForm (GaloisField 2 f) Vstd)
    (hnd_std : (QuadraticMap.polarBilin Qstd).Nondegenerate)
    (θ : Vstd ≃ₗ[GaloisField 2 f] ↥(bmsdop_W k f e))
    (hθ : ∀ x, (bmsdop_blockForm k f e) (θ x) = Qstd x)
    (D : UniversalRootDatum (spinGroup Qstd))
    (ι₁ : spinGroup Qstd →* spinGroup (bmsdop_Q k f))
    (hι₁ : Function.Injective ι₁ ∧ ι₁.range = bmsdop_Ge k f S e)
    (E : (Vstd ≃ₗ[GaloisField 2 f] Vstd) →*
        (bmsdop_V k f ≃ₗ[GaloisField 2 f] bmsdop_V k f))
    (hE : bmsdop_ExtProps k f S e Qstd hnd_std θ E)
    (hιE : ∀ x, Spin.spinAction (bmsdop_Q k f) (ι₁ x) = E (Spin.spinAction Qstd x))
    (hD : ∀ a₁ a₂ b₁ b₂ : Vstd,
      (Qstd a₁ = 0 ∧ Qstd a₂ = 0 ∧ Qstd b₁ = 0 ∧ Qstd b₂ = 0) →
      QuadraticMap.polar Qstd a₁ b₁ = 1 → QuadraticMap.polar Qstd a₂ b₂ = 1 →
      (QuadraticMap.polar Qstd a₁ a₂ = 0 ∧ QuadraticMap.polar Qstd b₁ b₂ = 0 ∧
        QuadraticMap.polar Qstd a₁ b₂ = 0 ∧ QuadraticMap.polar Qstd a₂ b₁ = 0) →
      ∃ β : Fin D.rank → ℤ, β ∈ D.roots ∧ GGLongRoot D β ∧
        ∃ u : spinGroup Qstd,
          (((D.rootGroup β).map (MulAut.conj u).toMonoidHom).map
            (Spin.spinAction Qstd) = siegelGroup Qstd a₁ a₂) ∧
          (((D.rootGroup (-β)).map (MulAut.conj u).toMonoidHom).map
            (Spin.spinAction Qstd) = siegelGroup Qstd b₁ b₂))
    (hext : ∀ a₁ a₂ : Vstd, a₁ ≠ 0 → a₂ ≠ 0 →
      LinearIndependent (GaloisField 2 f) ![a₁, a₂] → Qstd a₁ = 0 → Qstd a₂ = 0 →
      QuadraticMap.polar Qstd a₁ a₂ = 0 →
      ∃ b₁ b₂ : Vstd,
        (Qstd a₁ = 0 ∧ Qstd a₂ = 0 ∧ Qstd b₁ = 0 ∧ Qstd b₂ = 0) ∧
        QuadraticMap.polar Qstd a₁ b₁ = 1 ∧ QuadraticMap.polar Qstd a₂ b₂ = 1 ∧
        (QuadraticMap.polar Qstd a₁ a₂ = 0 ∧ QuadraticMap.polar Qstd b₁ b₂ = 0 ∧
          QuadraticMap.polar Qstd a₁ b₂ = 0 ∧ QuadraticMap.polar Qstd a₂ b₁ = 0)) :
    (∀ a₁ a₂ : ((Fin (k + 3) ⊕ Fin (k + 3)) → GaloisField 2 f), a₁ ≠ 0 → a₂ ≠ 0 →
        LinearIndependent (GaloisField 2 f) ![a₁, a₂] → (bmsdop_Q k f) a₁ = 0 →
        (bmsdop_Q k f) a₂ = 0 → QuadraticMap.polar (bmsdop_Q k f) a₁ a₂ = 0 →
        siegelGroup (bmsdop_Q k f) a₁ a₂ ≤ J'.map (Spin.spinAction (bmsdop_Q k f)) →
      ∃ (β : Fin D.rank → ℤ) (u : spinGroup Qstd), β ∈ D.roots ∧ GGLongRoot D β ∧
        ((((D.rootGroup β).map (MulAut.conj u).toMonoidHom).map ι₁).map
          (Spin.spinAction (bmsdop_Q k f)) = siegelGroup (bmsdop_Q k f) a₁ a₂)) := by
  intro a₁ a₂ ha₁ ha₂ hlin hQ₁ hQ₂ hpol hle
  have hJ'le : J' ≤ bmsdop_Ge k f S e :=
    ((CFSG.Assembly.isComponentOf_iff_open).mp hJe).1.trans
      (Subgroup.commutator_le_self (bmsdop_Ge k f S e))
  have hfix : ∀ c : GaloisField 2 f, ∀ v ∈ bmsdop_W' k f e,
      CFSG.ClassicalGroups.Orthogonal.eichler (bmsdop_Q k f) a₁ (c • a₂) v = v := by
    intro c v hv
    have hg : CFSG.ClassicalGroups.Orthogonal.eichler (bmsdop_Q k f) a₁ (c • a₂) ∈
        siegelGroup (bmsdop_Q k f) a₁ a₂ := Subgroup.subset_closure ⟨c, rfl⟩
    obtain ⟨x, hxJ, hxeq⟩ := Subgroup.mem_map.mp (hle hg)
    rw [← hxeq]
    exact bmsdop_Ge_spinAction_fixes_W' k f S x (hJ'le hxJ) v hv
  have hpolar : ∀ w' ∈ bmsdop_W' k f e,
      QuadraticMap.polar (⇑(bmsdop_Q k f)) w' a₁ = 0 ∧
      QuadraticMap.polar (⇑(bmsdop_Q k f)) w' a₂ = 0 := by
    intro w' hw'
    have h := hfix 1 w' hw'
    rw [one_smul, CFSG.ClassicalGroups.Orthogonal.eichler_apply hQ₁ hpol, hQ₂, zero_mul,
      add_zero] at h
    have h' : QuadraticMap.polar (⇑(bmsdop_Q k f)) w' a₁ • a₂ =
        QuadraticMap.polar (⇑(bmsdop_Q k f)) w' a₂ • a₁ := by
      have hc : w' + (QuadraticMap.polar (⇑(bmsdop_Q k f)) w' a₁ • a₂ -
          QuadraticMap.polar (⇑(bmsdop_Q k f)) w' a₂ • a₁) = w' + 0 := by
        rw [add_zero, ← add_sub_assoc]
        exact h
      exact sub_eq_zero.mp (add_left_cancel hc)
    have hli := (LinearIndependent.pair_iff.mp hlin)
      (QuadraticMap.polar (⇑(bmsdop_Q k f)) w' a₂)
      (-(QuadraticMap.polar (⇑(bmsdop_Q k f)) w' a₁)) (by
        rw [neg_smul, h'.symm]
        simp)
    exact ⟨neg_eq_zero.mp hli.2, hli.1⟩
  have hmem₁ : a₁ ∈ bmsdop_W k f e :=
    bmsdop_mem_W_of_polar_W'_eq_zero k f S h1 h2 (fun w' hw' => by
      rw [QuadraticMap.polar_comm]; exact (hpolar w' hw').1)
  have hmem₂ : a₂ ∈ bmsdop_W k f e :=
    bmsdop_mem_W_of_polar_W'_eq_zero k f S h1 h2 (fun w' hw' => by
      rw [QuadraticMap.polar_comm]; exact (hpolar w' hw').2)
  let u₁ : Vstd := θ.symm ⟨a₁, hmem₁⟩
  let u₂ : Vstd := θ.symm ⟨a₂, hmem₂⟩
  have hθu₁ : (θ u₁ : bmsdop_V k f) = a₁ := by
    change (θ (θ.symm ⟨a₁, hmem₁⟩) : bmsdop_V k f) = a₁
    rw [LinearEquiv.apply_symm_apply]
  have hθu₂ : (θ u₂ : bmsdop_V k f) = a₂ := by
    change (θ (θ.symm ⟨a₂, hmem₂⟩) : bmsdop_V k f) = a₂
    rw [LinearEquiv.apply_symm_apply]
  have hu₁ne : u₁ ≠ 0 := by
    intro h0
    apply ha₁
    rw [← hθu₁, h0]
    simp
  have hu₂ne : u₂ ≠ 0 := by
    intro h0
    apply ha₂
    rw [← hθu₂, h0]
    simp
  have hlin_u : LinearIndependent (GaloisField 2 f) ![u₁, u₂] := by
    rw [LinearIndependent.pair_iff] at hlin ⊢
    intro s t hst
    apply hlin s t
    have hc := congrArg (fun x => (θ x : bmsdop_V k f)) hst
    simpa only [map_add, map_smul, Submodule.coe_add, Submodule.coe_smul, hθu₁,
      hθu₂, map_zero, Submodule.coe_zero] using hc
  have hQstd₁ : Qstd u₁ = 0 := by
    rw [← hθ u₁]
    change (bmsdop_Q k f) (↑(θ u₁) : bmsdop_V k f) = 0
    rw [hθu₁, hQ₁]
  have hQstd₂ : Qstd u₂ = 0 := by
    rw [← hθ u₂]
    change (bmsdop_Q k f) (↑(θ u₂) : bmsdop_V k f) = 0
    rw [hθu₂, hQ₂]
  have hpolstd : QuadraticMap.polar (⇑Qstd) u₁ u₂ = 0 := by
    rw [← bmsdop_polar_theta k f Qstd θ hθ u₁ u₂]
    rw [hθu₁, hθu₂]
    exact hpol
  obtain ⟨b₁, b₂, hframe, hp₁, hp₂, horth⟩ :=
    hext u₁ u₂ hu₁ne hu₂ne hlin_u hQstd₁ hQstd₂ hpolstd
  obtain ⟨β, hβroot, hβlong, u, hu₁', _hu₂'⟩ := hD u₁ u₂ b₁ b₂ hframe hp₁ hp₂ horth
  refine ⟨β, u, hβroot, hβlong, ?_⟩
  have hιE' : (Spin.spinAction (bmsdop_Q k f)).comp ι₁ = E.comp (Spin.spinAction Qstd) :=
    MonoidHom.ext hιE
  calc Subgroup.map (Spin.spinAction (bmsdop_Q k f))
        (Subgroup.map ι₁ (Subgroup.map (MulAut.conj u).toMonoidHom (D.rootGroup β)))
      = Subgroup.map ((Spin.spinAction (bmsdop_Q k f)).comp ι₁)
          (Subgroup.map (MulAut.conj u).toMonoidHom (D.rootGroup β)) :=
        Subgroup.map_map _ _ _
    _ = Subgroup.map (E.comp (Spin.spinAction Qstd))
          (Subgroup.map (MulAut.conj u).toMonoidHom (D.rootGroup β)) := by rw [hιE']
    _ = Subgroup.map E (Subgroup.map (Spin.spinAction Qstd)
          (Subgroup.map (MulAut.conj u).toMonoidHom (D.rootGroup β))) :=
        (Subgroup.map_map _ _ _).symm
    _ = Subgroup.map E (siegelGroup Qstd u₁ u₂) := by rw [hu₁']
    _ = siegelGroup (bmsdop_Q k f) (θ u₁) (θ u₂) :=
        bmsdop_ext_siegel k f S h1 h2 Qstd hnd_std θ hθ E hE u₁ u₂ hQstd₁ hpolstd
    _ = siegelGroup (bmsdop_Q k f) a₁ a₂ := by rw [hθu₁, hθu₂]

private def bmsdop_AmbientMinus (ρ f : ℕ) (β γ : GaloisField 2 f)
    (hirr : ∀ s : GaloisField 2 f, s ^ 2 + β * s + γ ≠ 0) : Prop :=
  ∀ a₁ a₂ b₁ b₂ : Fin (ρ - 1) ⊕ Fin (ρ - 1) ⊕ Fin 2 → GaloisField 2 f,
    ((Spin.quadMinus ρ (GaloisField 2 f) β γ) a₁ = 0 ∧ (Spin.quadMinus ρ (GaloisField 2 f) β γ) a₂ =
        0 ∧
      (Spin.quadMinus ρ (GaloisField 2 f) β γ) b₁ = 0 ∧ (Spin.quadMinus ρ (GaloisField 2 f) β γ) b₂
          = 0) →
    QuadraticMap.polar (Spin.quadMinus ρ (GaloisField 2 f) β γ) a₁ b₁ = 1 →
    QuadraticMap.polar (Spin.quadMinus ρ (GaloisField 2 f) β γ) a₂ b₂ = 1 →
    (QuadraticMap.polar (Spin.quadMinus ρ (GaloisField 2 f) β γ) a₁ a₂ = 0 ∧
      QuadraticMap.polar (Spin.quadMinus ρ (GaloisField 2 f) β γ) b₁ b₂ = 0 ∧
      QuadraticMap.polar (Spin.quadMinus ρ (GaloisField 2 f) β γ) a₁ b₂ = 0 ∧
      QuadraticMap.polar (Spin.quadMinus ρ (GaloisField 2 f) β γ) a₂ b₁ = 0) →
    ∃ β' ∈ (Spin.Twisted.minusDatum ρ hirr).roots, GGLongRoot (Spin.Twisted.minusDatum ρ hirr) β' ∧
      ∃ u : ↥(spinGroup (Spin.quadMinus ρ (GaloisField 2 f) β γ)),
        (((Spin.Twisted.minusDatum ρ hirr).rootGroup β').map (MulAut.conj u).toMonoidHom).map
          (Spin.spinAction (Spin.quadMinus ρ (GaloisField 2 f) β γ)) =
            siegelGroup (Spin.quadMinus ρ (GaloisField 2 f) β γ) a₁ a₂ ∧
        (((Spin.Twisted.minusDatum ρ hirr).rootGroup (-β')).map (MulAut.conj u).toMonoidHom).map
          (Spin.spinAction (Spin.quadMinus ρ (GaloisField 2 f) β γ)) =
            siegelGroup (Spin.quadMinus ρ (GaloisField 2 f) β γ) b₁ b₂

private theorem bmsdop_ambient_minus_of_four (ρ f : ℕ) (hρ : 4 ≤ ρ) (β γ : GaloisField 2 f)
    (hirr : ∀ s : GaloisField 2 f, s ^ 2 + β * s + γ ≠ 0) : bmsdop_AmbientMinus ρ f β γ hirr := by
  intro a₁ a₂ b₁ b₂ hQ h₁ h₂ h₀
  exact exists_conj_rootGroup_eq_siegelGroup_POmegaMinus ρ hirr hρ a₁ a₂ b₁ b₂ hQ h₁ h₂ h₀

private theorem bmsdop_r3m_lift {K : Type} [Field K] [Finite K] [CharP K 2] {b c : K}
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0)
    {g : (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2 → K) ≃ₗ[K] (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2 → K)}
    (hg : g ∈ CFSG.RankThree.OrthogonalInvolutions.omegaGroup (Spin.quadMinus 3 K b c)
      (Spin.nondegenerate_polarBilin_quadMinus_of_finite 3 K hirr)) :
    ∃ h : spinGroup (Spin.quadMinus 3 K b c), Spin.spinAction (Spin.quadMinus 3 K b c) h = g := by
  have hQ := Spin.nondegenerate_polarBilin_quadMinus_of_finite 3 K hirr
  have hfin : 3 ≤ Module.finrank K (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2 → K) := by
    rw [Module.finrank_fintype_fun_eq_card, Fintype.card_sum, Fintype.card_sum, Fintype.card_fin]
    omega
  have h6 : Module.finrank K (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2 → K) = 6 := by
    rw [Module.finrank_fintype_fun_eq_card, Fintype.card_sum, Fintype.card_sum, Fintype.card_fin]
  have hne : ¬ CFSG.RankThree.PartOne.KCOrthogonal.SmallFixedException
      (Spin.quadMinus 3 K b c) := by
    rintro (⟨h3, _⟩ | ⟨h4, _⟩) <;> omega
  have h1 :=
    CFSG.LocalAnalysis.GLTheoremB.MovingAround.Inputs141d.omegaGroup_le_orthDerived_of_listed
    (Spin.quadMinus 3 K b c) hQ hfin hne hg
  rw [CFSG.RankThree.Classical2.orthDerived,
    CFSG.ClassicalGroups.Orthogonal.commutator_orthogonalGroup_quadMinus_of_two_le
      (by norm_num : 2 ≤ 3) hirr,
    ← CFSG.ClassicalInvolution.WeakCT.range_spinAction_quadMinus_three hirr] at h1
  exact h1

private theorem bmsdop_r3m_exists_long {n : ℕ} {K : Type} [Field K] {b c : K}
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) (hn : 3 ≤ n)
    {γ : Fin (Spin.Twisted.minusDatum n hirr).rank → ℤ}
    (hγ : GGLongRoot (Spin.Twisted.minusDatum n hirr) γ) :
    ∃ (i j : Fin (n - 1)) (_ : i ≠ j) (s t : Bool),
      Spin.toStdB (n - 1) γ = Pi.single i (Spin.boolSign s) + Pi.single j (Spin.boolSign t) := by
  obtain ⟨w, γ₀, hγ₀, hmax, rfl⟩ := hγ
  refine CFSG.StandardType.RootCentOmega.exists_long_weylAction w ?_
  rcases Spin.Twisted.exists_toStdB_eq_of_mem_roots n hγ₀ with h | ⟨k, s, hk⟩
  · exact h
  · exfalso
    set e : Fin (n - 1) → ℤ := Pi.single ⟨0, by omega⟩ 1 + Pi.single ⟨1, by omega⟩ 1 with he
    have h01 : (⟨0, by omega⟩ : Fin (n - 1)) ≠ ⟨1, by omega⟩ := by simp [Fin.ext_iff]
    have hδ := Spin.ofStdB_mem_rootsB (n - 1) (e := e)
      (Or.inl ⟨⟨0, by omega⟩, ⟨1, by omega⟩, 1, 1, h01, Or.inl rfl, Or.inl rfl, rfl⟩)
    have h1 : @CFSG.LieType.Steinberg.ht (Fin (n - 1)) _ (Spin.ofStdB (n - 1) e) ≤
        @CFSG.LieType.Steinberg.ht (Fin (n - 1)) _ γ₀ := hmax _ hδ
    rw [Spin.ht_of_toStdB_eq_add (n - 1) (Spin.toStdB_ofStdB (n - 1) e),
      Spin.ht_of_toStdB_eq_single (n - 1) hk] at h1
    have hk' := k.isLt
    cases s <;> simp [Spin.boolSign] at h1 <;> omega

private theorem bmsdop_r3m_spinAction_apply_eq {K : Type} [Field K] [Finite K] [CharP K 2]
    {b c : K} (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) {ι : Type} [Fintype ι]
    (w w' : ι → Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2 → K) (hw : LinearIndependent K w)
    (hw' : LinearIndependent K w')
    (hQ : ∀ i, (Spin.quadMinus 3 K b c) (w' i) = (Spin.quadMinus 3 K b c) (w i))
    (hpol : ∀ i k, QuadraticMap.polar (Spin.quadMinus 3 K b c) (w' i) (w' k) =
      QuadraticMap.polar (Spin.quadMinus 3 K b c) (w i) (w k))
    (a : Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2 → K) (ha : (Spin.quadMinus 3 K b c) a ≠ 0)
    (haw : ∀ i, QuadraticMap.polar (Spin.quadMinus 3 K b c) a (w' i) = 0) :
    ∃ g : ↥(spinGroup (Spin.quadMinus 3 K b c)),
      ∀ i, Spin.spinAction (Spin.quadMinus 3 K b c) g (w i) = w' i := by
  obtain ⟨g, hgΩ, hg⟩ := exists_mem_omegaGroup_family_apply_eq
    (Spin.nondegenerate_polarBilin_quadMinus_of_finite 3 K hirr) w w' hw hw' hQ hpol a ha haw
  obtain ⟨h, hh⟩ := bmsdop_r3m_lift hirr hgΩ
  exact ⟨h, fun i => by rw [hh]; exact hg i⟩

private theorem bmsdop_r3m_quasisimple
    (f : ℕ) (β γ : GaloisField 2 f)
    (hirr : ∀ s : GaloisField 2 f, s ^ 2 + β * s + γ ≠ 0) :
    IsQuasisimple (spinGroup (Spin.quadMinus 3 (GaloisField 2 f) β γ)) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨f', hf'1, hfcard⟩ :=
    CFSG.AGLEmbedding.ParabHub.exists_card_eq_two_pow (GaloisField 2 f)
  have hdim : Module.finrank (GaloisField 2 f)
      (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2 → GaloisField 2 f) = 6 := by
    rw [Module.finrank_fintype_fun_eq_card, Fintype.card_sum, Fintype.card_sum, Fintype.card_fin]
  have hts : ∀ U : Submodule (GaloisField 2 f)
      (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2 → GaloisField 2 f),
      Module.finrank (GaloisField 2 f) U = 3 →
        ∃ u ∈ U, (Spin.quadMinus 3 (GaloisField 2 f) β γ) u ≠ 0 :=
    (CFSG.ClassicalGroups.Orthogonal.isMinus_quadMinus (K := GaloisField 2 f) (m := 3)
      (by norm_num) hirr).noTS
  obtain ⟨E, hEfield, hEfin, hEcard, hψ⟩ :=
    CFSG.SeitzReduction.OmegaPilot.nonempty_orthDerived_mulEquiv_statedSU_of_six
      (K := GaloisField 2 f) (R := Spin.quadMinus 3 (GaloisField 2 f) β γ) hfcard
      (Spin.nondegenerate_polarBilin_quadMinus_of_finite 3 (GaloisField 2 f) hirr) hdim hts
  obtain ⟨ψ⟩ := hψ
  have hSU : IsQuasisimple (CFSG.Open.StatedSU 4 (2 ^ f') E) :=
    (Unitary.isQuasisimple_statedSU_of_card (F := E) (p := 2) (f := f') (n := 4) hEcard
      (by norm_num) (by intro h; exact (by norm_num : (4 : ℕ) ≠ 3) (congrArg Prod.fst h))).1
  have hrange : (Spin.spinAction (Spin.quadMinus 3 (GaloisField 2 f) β γ)).range =
      CFSG.RankThree.Classical2.orthDerived (Spin.quadMinus 3 (GaloisField 2 f) β γ) := by
    rw [CFSG.ClassicalInvolution.WeakCT.range_spinAction_quadMinus_three hirr,
      ← CFSG.ClassicalGroups.Orthogonal.commutator_orthogonalGroup_quadMinus_of_two_le
        (by norm_num : 2 ≤ 3) hirr]
  have e1 : spinGroup (Spin.quadMinus 3 (GaloisField 2 f) β γ) ≃*
      CFSG.RankThree.Classical2.orthDerived (Spin.quadMinus 3 (GaloisField 2 f) β γ) :=
    (MonoidHom.ofInjective
      (CFSG.StandardType.RootCentOmega.spinAction_quadMinus_injective hirr)).trans
      (MulEquiv.subgroupCongr hrange)
  exact Unitary.isQuasisimple_of_mulEquiv (e1.trans ψ).symm hSU

private theorem bmsdop_r3m_range
    (f : ℕ) (β γ : GaloisField 2 f)
    (hirr : ∀ s : GaloisField 2 f, s ^ 2 + β * s + γ ≠ 0) :
    (Spin.spinAction (Spin.quadMinus 3 (GaloisField 2 f) β γ)).range =
      CFSG.RankThree.OrthogonalInvolutions.omegaGroup (Spin.quadMinus 3 (GaloisField 2 f) β γ)
        (Spin.nondegenerate_polarBilin_quadMinus_of_finite 3 (GaloisField 2 f) hirr) := by
  refine le_antisymm ?_ ?_
  · rw [CFSG.ClassicalInvolution.WeakCT.range_spinAction_quadMinus_three hirr]
    exact CFSG.ClassicalGroups.Orthogonal.elementaryGroup_le_omegaGroup
      (Spin.nondegenerate_polarBilin_quadMinus_of_finite 3 (GaloisField 2 f) hirr)
  · intro g hg
    obtain ⟨h, hh⟩ := bmsdop_r3m_lift hirr hg
    exact ⟨h, hh⟩

private theorem bmsdop_r3m_ambient
    (f : ℕ) (β γ : GaloisField 2 f)
    (hirr : ∀ s : GaloisField 2 f, s ^ 2 + β * s + γ ≠ 0) : bmsdop_AmbientMinus 3 f β γ hirr := by
  intro a₁ a₂ b₁ b₂ hQ h₁ h₂ h₀
  let Q : QuadraticForm (GaloisField 2 f)
      (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2 → GaloisField 2 f) :=
    Spin.quadMinus 3 (GaloisField 2 f) β γ
  have hQp : Q a₁ = 0 ∧ Q a₂ = 0 ∧ Q b₁ = 0 ∧ Q b₂ = 0 := hQ
  have h₁p : QuadraticMap.polar Q a₁ b₁ = 1 := h₁
  have h₂p : QuadraticMap.polar Q a₂ b₂ = 1 := h₂
  have h₀p : QuadraticMap.polar Q a₁ a₂ = 0 ∧ QuadraticMap.polar Q b₁ b₂ = 0 ∧
      QuadraticMap.polar Q a₁ b₂ = 0 ∧ QuadraticMap.polar Q a₂ b₁ = 0 := h₀
  obtain ⟨γ₀, hγ₀, hmax⟩ :=
    exists_maxHeight (D := Spin.Twisted.minusDatum 3 hirr) (show 0 < 3 - 1 by omega)
  have hlong : GGLongRoot (Spin.Twisted.minusDatum 3 hirr) γ₀ :=
    ⟨1, γ₀, hγ₀, hmax, by rw [map_one, Module.End.one_apply]⟩
  obtain ⟨i, j, hij, s, t, hst⟩ :=
    bmsdop_r3m_exists_long hirr (by norm_num : 3 ≤ 3) hlong
  let Fr : Spin.HypFrame Q (3 - 1) := (Spin.Twisted.minusFrame 3 β γ).toHypFrame
  have hX : Spin.Twisted.minusRootGroup 3 hirr γ₀ = (Fr.longRoot hij s t).range :=
    Spin.Twisted.minusRootGroup_eq_long 3 hirr hij s t hst
  have hst_neg : Spin.toStdB (3 - 1) (-γ₀) =
      Pi.single i (Spin.boolSign (!s)) + Pi.single j (Spin.boolSign (!t)) := by
    calc Spin.toStdB (3 - 1) (-γ₀) = -Spin.toStdB (3 - 1) γ₀ := Spin.toStdB_neg (3 - 1) γ₀
      _ = -(Pi.single i (Spin.boolSign s) + Pi.single j (Spin.boolSign t)) := by rw [hst]
      _ = Pi.single i (-Spin.boolSign s) + Pi.single j (-Spin.boolSign t) := by
            rw [neg_add, Pi.single_neg, Pi.single_neg]
      _ = Pi.single i (Spin.boolSign (!s)) + Pi.single j (Spin.boolSign (!t)) := by
            rw [Spin.boolSign_not, Spin.boolSign_not]
  have hXneg : Spin.Twisted.minusRootGroup 3 hirr (-γ₀) = (Fr.longRoot hij (!s) (!t)).range :=
    Spin.Twisted.minusRootGroup_eq_long 3 hirr hij (!s) (!t) hst_neg
  let w : Fin 4 → (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2 → GaloisField 2 f) :=
    ![Fr.vec j t, Fr.vec i s, Fr.vec j (!t), Fr.vec i (!s)]
  let w' : Fin 4 → (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2 → GaloisField 2 f) := ![a₁, a₂, b₁, b₂]
  have hQw : Q (Fr.vec j t) = 0 ∧ Q (Fr.vec i s) = 0 ∧ Q (Fr.vec j (!t)) = 0 ∧
      Q (Fr.vec i (!s)) = 0 :=
    ⟨Fr.map_vec j t, Fr.map_vec i s, Fr.map_vec j (!t), Fr.map_vec i (!s)⟩
  have h0w : QuadraticMap.polar Q (Fr.vec j t) (Fr.vec i s) = 0 ∧
      QuadraticMap.polar Q (Fr.vec j (!t)) (Fr.vec i (!s)) = 0 ∧
      QuadraticMap.polar Q (Fr.vec j t) (Fr.vec i (!s)) = 0 ∧
      QuadraticMap.polar Q (Fr.vec i s) (Fr.vec j (!t)) = 0 := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [QuadraticMap.polar_comm, Fr.polar_vec_of_ne hij]
    · rw [QuadraticMap.polar_comm, Fr.polar_vec_of_ne hij]
    · rw [QuadraticMap.polar_comm, Fr.polar_vec_of_ne hij]
    · exact Fr.polar_vec_of_ne hij s (!t)
  have hw : LinearIndependent (GaloisField 2 f) w :=
    Geo.linearIndependent_quad_of_polar Q hQw (Fr.polar_vec_not j t) (Fr.polar_vec_not i s) h0w
  have hw' : LinearIndependent (GaloisField 2 f) w' :=
    Geo.linearIndependent_quad_of_polar Q hQp h₁p h₂p h₀p
  have hQf : ∀ k, Q (w' k) = Q (w k) := by
    intro k
    fin_cases k <;>
      simp [w, w', Fr.map_vec, hQp.1, hQp.2.1, hQp.2.2.1, hQp.2.2.2]
  have ha1a1 : QuadraticMap.polar Q a₁ a₁ = 0 := by
    rw [QuadraticMap.polar_self, hQp.1, smul_zero]
  have ha2a2 : QuadraticMap.polar Q a₂ a₂ = 0 := by
    rw [QuadraticMap.polar_self, hQp.2.1, smul_zero]
  have hb1b1 : QuadraticMap.polar Q b₁ b₁ = 0 := by
    rw [QuadraticMap.polar_self, hQp.2.2.1, smul_zero]
  have hb2b2 : QuadraticMap.polar Q b₂ b₂ = 0 := by
    rw [QuadraticMap.polar_self, hQp.2.2.2, smul_zero]
  have hb1a1 : QuadraticMap.polar Q b₁ a₁ = 1 := by
    rw [QuadraticMap.polar_comm, h₁p]
  have hb2a2 : QuadraticMap.polar Q b₂ a₂ = 1 := by
    rw [QuadraticMap.polar_comm, h₂p]
  have ha2a1 : QuadraticMap.polar Q a₂ a₁ = 0 := by
    rw [QuadraticMap.polar_comm, h₀p.1]
  have hb2b1 : QuadraticMap.polar Q b₂ b₁ = 0 := by
    rw [QuadraticMap.polar_comm, h₀p.2.1]
  have hb1a2 : QuadraticMap.polar Q b₁ a₂ = 0 := by
    rw [QuadraticMap.polar_comm, h₀p.2.2.2]
  have hb2a1 : QuadraticMap.polar Q b₂ a₁ = 0 := by
    rw [QuadraticMap.polar_comm, h₀p.2.2.1]
  have hpol : ∀ k l, QuadraticMap.polar Q (w' k) (w' l) =
      QuadraticMap.polar Q (w k) (w l) := by
    intro k l
    fin_cases k <;> fin_cases l <;>
      simp [w, w', Fr.polar_vec_vec, hij, Ne.symm hij, h₁p, h₂p, hb1a1, hb2a2, h₀p.1,
        h₀p.2.1, h₀p.2.2.1, h₀p.2.2.2, ha2a1, hb2b1, hb1a2, hb2a1, ha1a1, ha2a2, hb1b1,
        hb2b2]
  obtain ⟨g, hgO, hg⟩ := CFSG.StandardType.TableBOrth.exists_orth_apply_eq
    (Spin.nondegenerate_polarBilin_quadMinus_of_finite 3 (GaloisField 2 f) hirr) w w' hw hw'
    hQf hpol
  obtain ⟨a₀, ha₀unit, ha₀⟩ := Fr.exists_aux i j
  let a : Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2 → GaloisField 2 f := g a₀
  have ha : Q a ≠ 0 := by
    rw [show a = g a₀ from rfl, CFSG.ClassicalGroups.Orthogonal.map_of_mem hgO]
    exact ha₀unit.ne_zero
  have haw : ∀ k, QuadraticMap.polar Q a (w' k) = 0 := by
    intro k
    rw [show a = g a₀ from rfl, ← hg k,
      CFSG.ClassicalGroups.Orthogonal.polar_map_of_mem hgO, QuadraticMap.polar_comm]
    fin_cases k <;>
      simp only [w, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
    · exact (ha₀ t).2
    · exact (ha₀ s).1
    · exact (ha₀ (!t)).2
    · exact (ha₀ (!s)).1
  obtain ⟨u, hu⟩ := bmsdop_r3m_spinAction_apply_eq hirr w w' hw hw' hQf hpol a ha haw
  refine ⟨γ₀, hγ₀, hlong, u, ?_, ?_⟩
  · rw [show (Spin.Twisted.minusDatum 3 hirr).rootGroup γ₀ =
        Spin.Twisted.minusRootGroup 3 hirr γ₀ from rfl, hX,
      Geo.map_conj_range_longRoot_eq_siegelGroup Fr hij s t u]
    have h0 : Spin.spinAction Q u (Fr.vec j t) = a₁ := by
      change Spin.spinAction Q u (w 0) = a₁
      exact hu 0
    have h1 : Spin.spinAction Q u (Fr.vec i s) = a₂ := by
      change Spin.spinAction Q u (w 1) = a₂
      exact hu 1
    rw [h0, h1]
  · rw [show (Spin.Twisted.minusDatum 3 hirr).rootGroup (-γ₀) =
        Spin.Twisted.minusRootGroup 3 hirr (-γ₀) from rfl, hXneg,
      Geo.map_conj_range_longRoot_eq_siegelGroup Fr hij (!s) (!t) u]
    have h2 : Spin.spinAction Q u (Fr.vec j (!t)) = b₁ := by
      change Spin.spinAction Q u (w 2) = b₁
      exact hu 2
    have h3 : Spin.spinAction Q u (Fr.vec i (!s)) = b₂ := by
      change Spin.spinAction Q u (w 3) = b₂
      exact hu 3
    rw [h2, h3]

private lemma bmsdop_plus_omegaGroup (f ρ : ℕ) (hρ : 3 ≤ ρ) :
    (Spin.spinAction (Spin.quadPlus ρ (GaloisField 2 f))).range =
      CFSG.RankThree.OrthogonalInvolutions.omegaGroup (Spin.quadPlus ρ (GaloisField 2 f))
        (Spin.nondegenerate_polarBilin_quadPlus ρ (GaloisField 2 f)) := by
  apply le_antisymm
  · rw [Spin.range_spinAction_quadPlus (K := GaloisField 2 f) hρ]
    exact CFSG.ClassicalGroups.Orthogonal.elementaryGroup_le_omegaGroup
      (Q := Spin.quadPlus ρ (GaloisField 2 f))
      (Spin.nondegenerate_polarBilin_quadPlus ρ (GaloisField 2 f))
  · intro g hg
    exact MonoidHom.mem_range.mpr
      (CFSG.StandardType.GGOppRadOmega.exists_spinAction_eq_of_mem_omegaGroup_plus
        (K := GaloisField 2 f) hρ hg)

private lemma bmsdop_plus_extProps (k f : ℕ)
    (S : Set (GL (Fin (k + 3) ⊕ Fin (k + 3)) (GaloisField 2 f)))
    {e : Matrix (Fin (k + 3) ⊕ Fin (k + 3)) (Fin (k + 3) ⊕ Fin (k + 3)) (GaloisField 2 f)}
    (h1 : bmsdop_geom₁ k f S e) (h2 : bmsdop_geom₂ k f S e) (ρ : ℕ) (hρ : 3 ≤ ρ)
    (θ : (Fin ρ ⊕ Fin ρ → GaloisField 2 f) ≃ₗ[GaloisField 2 f] ↥(bmsdop_W k f e))
    (hθ : ∀ x, (bmsdop_blockForm k f e) (θ x) = (Spin.quadPlus ρ (GaloisField 2 f)) x) :
    bmsdop_ExtProps k f S e (Spin.quadPlus ρ (GaloisField 2 f))
      (Spin.nondegenerate_polarBilin_quadPlus ρ (GaloisField 2 f)) θ
      (bmsdop_glue k f S h1 θ) := by
  have hnd_std : (QuadraticMap.polarBilin (Spin.quadPlus ρ (GaloisField 2 f))).Nondegenerate :=
    Spin.nondegenerate_polarBilin_quadPlus ρ (GaloisField 2 f)
  have hb := bmsdop_glue_basic k f S h1 h2 (Spin.quadPlus ρ (GaloisField 2 f)) θ hθ
  exact ⟨hb.1, hb.2.1, hb.2.2.1, hb.2.2.2,
    fun g => bmsdop_glue_omegaGroup k f S h1 h2 (Spin.quadPlus ρ (GaloisField 2 f)) θ hθ
      hnd_std g⟩

private theorem bmsdop_plus_embedding (k f : ℕ)
    (S : Set (GL (Fin (k + 3) ⊕ Fin (k + 3)) (GaloisField 2 f)))
    {e : Matrix (Fin (k + 3) ⊕ Fin (k + 3)) (Fin (k + 3) ⊕ Fin (k + 3)) (GaloisField 2 f)}
    {J' : Subgroup ↥(spinGroup (bmsdop_Q k f))}
    (h1 : bmsdop_geom₁ k f S e) (h2 : bmsdop_geom₂ k f S e)
    (hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s')
    (heA : e ∈ Algebra.adjoin (GaloisField 2 f) (Units.val '' S))
    (hJe : IsComponentOf J' ⁅bmsdop_Ge k f S e, bmsdop_Ge k f S e⁆)
    (ρ : ℕ) (hρ : 3 ≤ ρ) (hrank : e.rank = 2 * ρ)
    (θ : (Fin ρ ⊕ Fin ρ → GaloisField 2 f) ≃ₗ[GaloisField 2 f] ↥(bmsdop_W k f e))
    (hθ : ∀ x, (bmsdop_blockForm k f e) (θ x) = (Spin.quadPlus ρ (GaloisField 2 f)) x) :
    ∃ (ι₁ : spinGroup (Spin.quadPlus ρ (GaloisField 2 f)) →* ↥(spinGroup (bmsdop_Q k f))),
      Function.Injective ι₁ ∧ ι₁.range = bmsdop_Ge k f S e ∧
      (∀ x, Spin.spinAction (bmsdop_Q k f) (ι₁ x) =
        bmsdop_glue k f S h1 θ (Spin.spinAction (Spin.quadPlus ρ (GaloisField 2 f)) x)) ∧
      (∀ y, ι₁ y ∈ Subgroup.center ↥(spinGroup (bmsdop_Q k f)) →
        y ∈ Subgroup.center (spinGroup (Spin.quadPlus ρ (GaloisField 2 f)))) ∧
      J' = bmsdop_Ge k f S e := by
  haveI : Algebra.IsCentral (GaloisField 2 f)
      (CliffordAlgebra (Spin.quadPlus ρ (GaloisField 2 f))) :=
    Spin.isCentral_cliffordAlgebra_quadPlus (GaloisField 2 f) ρ
  have hE : bmsdop_ExtProps k f S e (Spin.quadPlus ρ (GaloisField 2 f))
      (Spin.nondegenerate_polarBilin_quadPlus ρ (GaloisField 2 f)) θ
      (bmsdop_glue k f S h1 θ) :=
    bmsdop_plus_extProps k f S h1 h2 ρ hρ θ hθ
  obtain ⟨ι₁, hι₁inj, hι₁range, hι₁E, hι₁center⟩ :=
    bmsdop_iota₁ k f S h1 h2 hS heA (Spin.quadPlus ρ (GaloisField 2 f))
      (Spin.nondegenerate_polarBilin_quadPlus ρ (GaloisField 2 f)) (bmsdop_glue k f S h1 θ) θ
      hE hθ (bmsdop_plus_omegaGroup f ρ hρ)
  have hq : IsQuasisimple (spinGroup (Spin.quadPlus ρ (GaloisField 2 f))) :=
    bmsdop_std_quasisimple_plus f ρ hρ
  have hJ' : J' = bmsdop_Ge k f S e :=
    bmsdop_component_eq k f S h1 h2 (Spin.quadPlus ρ (GaloisField 2 f)) hq ι₁
      ⟨hι₁inj, hι₁range⟩ hJe
  exact ⟨ι₁, hι₁inj, hι₁range, hι₁E, hι₁center, hJ'⟩

private lemma bmsdop_plus_frame (f ρ : ℕ) (hρ : 3 ≤ ρ) :
    ∃ a₁ a₂ b₁ b₂ : (Fin ρ ⊕ Fin ρ → GaloisField 2 f),
      ((Spin.quadPlus ρ (GaloisField 2 f)) a₁ = 0 ∧
        (Spin.quadPlus ρ (GaloisField 2 f)) a₂ = 0 ∧
        (Spin.quadPlus ρ (GaloisField 2 f)) b₁ = 0 ∧
        (Spin.quadPlus ρ (GaloisField 2 f)) b₂ = 0) ∧
      QuadraticMap.polar (Spin.quadPlus ρ (GaloisField 2 f)) a₁ b₁ = 1 ∧
      QuadraticMap.polar (Spin.quadPlus ρ (GaloisField 2 f)) a₂ b₂ = 1 ∧
      (QuadraticMap.polar (Spin.quadPlus ρ (GaloisField 2 f)) a₁ a₂ = 0 ∧
        QuadraticMap.polar (Spin.quadPlus ρ (GaloisField 2 f)) b₁ b₂ = 0 ∧
        QuadraticMap.polar (Spin.quadPlus ρ (GaloisField 2 f)) a₁ b₂ = 0 ∧
        QuadraticMap.polar (Spin.quadPlus ρ (GaloisField 2 f)) a₂ b₁ = 0) := by
  let Fr : Spin.HypFrame (Spin.quadPlus ρ (GaloisField 2 f)) ρ :=
    Spin.plusFrame ρ (GaloisField 2 f) hρ
  let i0 : Fin ρ := ⟨0, by omega⟩
  let i1 : Fin ρ := ⟨1, by omega⟩
  have hij : i0 ≠ i1 := by
    intro h
    have : (0 : ℕ) = 1 := by simpa [i0, i1] using congrArg Fin.val h
    omega
  refine ⟨Fr.vec i1 false, Fr.vec i0 false, Fr.vec i1 true, Fr.vec i0 true,
    ⟨Fr.map_vec i1 false, Fr.map_vec i0 false, Fr.map_vec i1 true, Fr.map_vec i0 true⟩,
    ?_, ?_, ⟨?_, ?_, ?_, ?_⟩⟩
  · rw [Fr.polar_vec_vec]; simp
  · rw [Fr.polar_vec_vec]; simp
  · exact Fr.polar_vec_of_ne hij.symm false false
  · exact Fr.polar_vec_of_ne hij.symm true true
  · exact Fr.polar_vec_of_ne hij.symm false true
  · exact Fr.polar_vec_of_ne hij false true

private lemma bmsdop_plus_ambient (f ρ : ℕ) (hρ : 3 ≤ ρ) :
    ∀ a₁ a₂ b₁ b₂ : (Fin ρ ⊕ Fin ρ → GaloisField 2 f),
      ((Spin.quadPlus ρ (GaloisField 2 f)) a₁ = 0 ∧
        (Spin.quadPlus ρ (GaloisField 2 f)) a₂ = 0 ∧
        (Spin.quadPlus ρ (GaloisField 2 f)) b₁ = 0 ∧
        (Spin.quadPlus ρ (GaloisField 2 f)) b₂ = 0) →
      QuadraticMap.polar (Spin.quadPlus ρ (GaloisField 2 f)) a₁ b₁ = 1 →
      QuadraticMap.polar (Spin.quadPlus ρ (GaloisField 2 f)) a₂ b₂ = 1 →
      (QuadraticMap.polar (Spin.quadPlus ρ (GaloisField 2 f)) a₁ a₂ = 0 ∧
        QuadraticMap.polar (Spin.quadPlus ρ (GaloisField 2 f)) b₁ b₂ = 0 ∧
        QuadraticMap.polar (Spin.quadPlus ρ (GaloisField 2 f)) a₁ b₂ = 0 ∧
        QuadraticMap.polar (Spin.quadPlus ρ (GaloisField 2 f)) a₂ b₁ = 0) →
      ∃ β : Fin (Spin.plusDatum ρ (GaloisField 2 f) hρ).rank → ℤ,
        β ∈ (Spin.plusDatum ρ (GaloisField 2 f) hρ).roots ∧
        GGLongRoot (Spin.plusDatum ρ (GaloisField 2 f) hρ) β ∧
        ∃ u : spinGroup (Spin.quadPlus ρ (GaloisField 2 f)),
          (((Spin.plusDatum ρ (GaloisField 2 f) hρ).rootGroup β).map
            (MulAut.conj u).toMonoidHom).map
            (Spin.spinAction (Spin.quadPlus ρ (GaloisField 2 f))) =
              siegelGroup (Spin.quadPlus ρ (GaloisField 2 f)) a₁ a₂ ∧
          (((Spin.plusDatum ρ (GaloisField 2 f) hρ).rootGroup (-β)).map
            (MulAut.conj u).toMonoidHom).map
            (Spin.spinAction (Spin.quadPlus ρ (GaloisField 2 f))) =
              siegelGroup (Spin.quadPlus ρ (GaloisField 2 f)) b₁ b₂ :=
  fun a₁ a₂ b₁ b₂ hQ h₁ h₂ h₀ =>
    exists_conj_rootGroup_eq_siegelGroup_POmegaPlus ρ (GaloisField 2 f) hρ
      a₁ a₂ b₁ b₂ hQ h₁ h₂ h₀

private theorem bmsdop_plus_model_data (k f : ℕ)
    (S : Set (GL (Fin (k + 3) ⊕ Fin (k + 3)) (GaloisField 2 f)))
    {e : Matrix (Fin (k + 3) ⊕ Fin (k + 3)) (Fin (k + 3) ⊕ Fin (k + 3)) (GaloisField 2 f)}
    {J' : Subgroup ↥(spinGroup (bmsdop_Q k f))}
    (h1 : bmsdop_geom₁ k f S e) (h2 : bmsdop_geom₂ k f S e)
    (hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s')
    (heA : e ∈ Algebra.adjoin (GaloisField 2 f) (Units.val '' S))
    (hJe : IsComponentOf J' ⁅bmsdop_Ge k f S e, bmsdop_Ge k f S e⁆)
    (ρ : ℕ) (hρ : 3 ≤ ρ) (hrank : e.rank = 2 * ρ) (hf : 1 ≤ f)
    (θ : (Fin ρ ⊕ Fin ρ → GaloisField 2 f) ≃ₗ[GaloisField 2 f] ↥(bmsdop_W k f e))
    (hθ : ∀ x, (bmsdop_blockForm k f e) (θ x) = (Spin.quadPlus ρ (GaloisField 2 f)) x) :
    ∃ (β₀ : Fin (Spin.plusDatum ρ (GaloisField 2 f) hρ).rank → ℤ)
      (ι : spinGroup (Spin.quadPlus ρ (GaloisField 2 f)) →* ↥(spinGroup (bmsdop_Q k f))),
      GGPosTag .POmegaPlus ∧ 1 ≤ f ∧
      GGLongRoot (Spin.plusDatum ρ (GaloisField 2 f) hρ) β₀ ∧
      (∀ y, ι y ∈ Subgroup.center ↥(spinGroup (bmsdop_Q k f)) →
        y ∈ Subgroup.center (spinGroup (Spin.quadPlus ρ (GaloisField 2 f)))) ∧
      ι.range = J' ∧
      ∃ a₁ a₂ b₁ b₂ : ((Fin (k + 3) ⊕ Fin (k + 3)) → GaloisField 2 f),
        ((bmsdop_Q k f) a₁ = 0 ∧ (bmsdop_Q k f) a₂ = 0 ∧
          (bmsdop_Q k f) b₁ = 0 ∧ (bmsdop_Q k f) b₂ = 0) ∧
        QuadraticMap.polar (bmsdop_Q k f) a₁ b₁ = 1 ∧
        QuadraticMap.polar (bmsdop_Q k f) a₂ b₂ = 1 ∧
        (QuadraticMap.polar (bmsdop_Q k f) a₁ a₂ = 0 ∧
          QuadraticMap.polar (bmsdop_Q k f) b₁ b₂ = 0 ∧
          QuadraticMap.polar (bmsdop_Q k f) a₁ b₂ = 0 ∧
          QuadraticMap.polar (bmsdop_Q k f) a₂ b₁ = 0) ∧
        ((((Spin.plusDatum ρ (GaloisField 2 f) hρ).rootGroup β₀).map ι).map
          (Spin.spinAction (bmsdop_Q k f)) = siegelGroup (bmsdop_Q k f) a₁ a₂) ∧
        ((((Spin.plusDatum ρ (GaloisField 2 f) hρ).rootGroup (-β₀)).map ι).map
          (Spin.spinAction (bmsdop_Q k f)) = siegelGroup (bmsdop_Q k f) b₁ b₂) := by
  have hnd_std : (QuadraticMap.polarBilin (Spin.quadPlus ρ (GaloisField 2 f))).Nondegenerate :=
    Spin.nondegenerate_polarBilin_quadPlus ρ (GaloisField 2 f)
  have hE : bmsdop_ExtProps k f S e (Spin.quadPlus ρ (GaloisField 2 f)) hnd_std θ
      (bmsdop_glue k f S h1 θ) := bmsdop_plus_extProps k f S h1 h2 ρ hρ θ hθ
  obtain ⟨ι₁, hι₁inj, hι₁range, hι₁E, hι₁center, hJ'⟩ :=
    bmsdop_plus_embedding k f S h1 h2 hS heA hJe ρ hρ hrank θ hθ
  obtain ⟨β₀, u₀, a₁, a₂, b₁, b₂, hβlong, hframe, hpol₁, hpol₂, horth, hroot₁, hroot₂⟩ :=
    bmsdop_root_siegel k f S h1 h2 (Spin.quadPlus ρ (GaloisField 2 f)) hnd_std θ hθ
      (Spin.plusDatum ρ (GaloisField 2 f) hρ) ι₁ ⟨hι₁inj, hι₁range⟩
      (bmsdop_glue k f S h1 θ) hE hι₁E (bmsdop_plus_ambient f ρ hρ) (bmsdop_plus_frame f ρ hρ)
  have hιrange : (ι₁.comp (MulAut.conj u₀).toMonoidHom).range = J' := by
    rw [MonoidHom.range_comp, MonoidHom.range_eq_top.mpr (MulAut.conj u₀).surjective,
      Subgroup.map_top, hι₁range, hJ']
  have hιcenter : ∀ y, (ι₁.comp (MulAut.conj u₀).toMonoidHom) y ∈
      Subgroup.center ↥(spinGroup (bmsdop_Q k f)) →
      y ∈ Subgroup.center (spinGroup (Spin.quadPlus ρ (GaloisField 2 f))) := by
    intro y hy
    have h1 := hι₁center (MulAut.conj u₀ y) hy
    rw [Subgroup.mem_center_iff] at h1 ⊢
    intro g
    have h2 := h1 (MulAut.conj u₀ g)
    have h3 := congrArg (MulAut.conj u₀⁻¹) h2
    simpa [MulAut.conj_apply, mul_assoc] using h3
  refine ⟨β₀, ι₁.comp (MulAut.conj u₀).toMonoidHom, ?_, hf, hβlong, hιcenter, hιrange,
    θ a₁, θ a₂, θ b₁, θ b₂, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold GGPosTag
    exact Or.inr (Or.inr (Or.inr (Or.inl rfl)))
  · refine ⟨?_, ?_, ?_, ?_⟩
    · rw [show (bmsdop_Q k f) (θ a₁) = (bmsdop_blockForm k f e) (θ a₁) from rfl, hθ a₁, hframe.1]
    · rw [show (bmsdop_Q k f) (θ a₂) = (bmsdop_blockForm k f e) (θ a₂) from rfl, hθ a₂, hframe.2.1]
    · rw [show (bmsdop_Q k f) (θ b₁) = (bmsdop_blockForm k f e) (θ b₁) from rfl, hθ b₁,
        hframe.2.2.1]
    · rw [show (bmsdop_Q k f) (θ b₂) = (bmsdop_blockForm k f e) (θ b₂) from rfl, hθ b₂,
        hframe.2.2.2]
  · rw [bmsdop_polar_theta k f (Spin.quadPlus ρ (GaloisField 2 f)) θ hθ a₁ b₁]; exact hpol₁
  · rw [bmsdop_polar_theta k f (Spin.quadPlus ρ (GaloisField 2 f)) θ hθ a₂ b₂]; exact hpol₂
  · refine ⟨?_, ?_, ?_, ?_⟩
    · rw [bmsdop_polar_theta k f (Spin.quadPlus ρ (GaloisField 2 f)) θ hθ a₁ a₂]; exact horth.1
    · rw [bmsdop_polar_theta k f (Spin.quadPlus ρ (GaloisField 2 f)) θ hθ b₁ b₂]; exact horth.2.1
    · rw [bmsdop_polar_theta k f (Spin.quadPlus ρ (GaloisField 2 f)) θ hθ a₁ b₂]; exact horth.2.2.1
    · rw [bmsdop_polar_theta k f (Spin.quadPlus ρ (GaloisField 2 f)) θ hθ a₂ b₁]; exact horth.2.2.2
  · rw [← Subgroup.map_map]
    exact hroot₁
  · rw [← Subgroup.map_map]
    exact hroot₂

private lemma bmsdop_minus_range_of_four (ρ f : ℕ) (hρ : 4 ≤ ρ) (β γ : GaloisField 2 f)
    (hirr : ∀ s : GaloisField 2 f, s ^ 2 + β * s + γ ≠ 0) :
    (Spin.spinAction (Spin.quadMinus ρ (GaloisField 2 f) β γ)).range =
      CFSG.RankThree.OrthogonalInvolutions.omegaGroup (Spin.quadMinus ρ (GaloisField 2 f) β γ)
        (Spin.nondegenerate_polarBilin_quadMinus_of_finite ρ (GaloisField 2 f) hirr) := by
  apply le_antisymm
  · rw [Spin.range_spinAction_quadMinus (K := GaloisField 2 f) hρ hirr]
    exact CFSG.ClassicalGroups.Orthogonal.elementaryGroup_le_omegaGroup
      (Q := Spin.quadMinus ρ (GaloisField 2 f) β γ)
      (Spin.nondegenerate_polarBilin_quadMinus_of_finite ρ (GaloisField 2 f) hirr)
  · intro g hg
    exact MonoidHom.mem_range.mpr
      (CFSG.StandardType.GGOppRadOmega.exists_spinAction_eq_of_mem_omegaGroup_minus
        (K := GaloisField 2 f) hirr hρ hg)

private lemma bmsdop_minus_frame (f ρ : ℕ) (hρ : 3 ≤ ρ) (β γ : GaloisField 2 f)
    (hirr : ∀ s : GaloisField 2 f, s ^ 2 + β * s + γ ≠ 0) :
    ∃ a₁ a₂ b₁ b₂ : (Fin (ρ - 1) ⊕ Fin (ρ - 1) ⊕ Fin 2 → GaloisField 2 f),
      ((Spin.quadMinus ρ (GaloisField 2 f) β γ) a₁ = 0 ∧
        (Spin.quadMinus ρ (GaloisField 2 f) β γ) a₂ = 0 ∧
        (Spin.quadMinus ρ (GaloisField 2 f) β γ) b₁ = 0 ∧
        (Spin.quadMinus ρ (GaloisField 2 f) β γ) b₂ = 0) ∧
      QuadraticMap.polar (Spin.quadMinus ρ (GaloisField 2 f) β γ) a₁ b₁ = 1 ∧
      QuadraticMap.polar (Spin.quadMinus ρ (GaloisField 2 f) β γ) a₂ b₂ = 1 ∧
      (QuadraticMap.polar (Spin.quadMinus ρ (GaloisField 2 f) β γ) a₁ a₂ = 0 ∧
        QuadraticMap.polar (Spin.quadMinus ρ (GaloisField 2 f) β γ) b₁ b₂ = 0 ∧
        QuadraticMap.polar (Spin.quadMinus ρ (GaloisField 2 f) β γ) a₁ b₂ = 0 ∧
        QuadraticMap.polar (Spin.quadMinus ρ (GaloisField 2 f) β γ) a₂ b₁ = 0) := by
  let Fr : Spin.HypFrame (Spin.quadMinus ρ (GaloisField 2 f) β γ) (ρ - 1) :=
    (Spin.Twisted.minusFrame ρ β γ).toHypFrame
  let i0 : Fin (ρ - 1) := ⟨0, by omega⟩
  let i1 : Fin (ρ - 1) := ⟨1, by omega⟩
  have hij : i0 ≠ i1 := by
    intro h
    have : (0 : ℕ) = 1 := by simpa [i0, i1] using congrArg Fin.val h
    omega
  refine ⟨Fr.vec i1 false, Fr.vec i0 false, Fr.vec i1 true, Fr.vec i0 true,
    ⟨Fr.map_vec i1 false, Fr.map_vec i0 false, Fr.map_vec i1 true, Fr.map_vec i0 true⟩,
    ?_, ?_, ⟨?_, ?_, ?_, ?_⟩⟩
  · rw [Fr.polar_vec_vec]; simp
  · rw [Fr.polar_vec_vec]; simp
  · exact Fr.polar_vec_of_ne hij.symm false false
  · exact Fr.polar_vec_of_ne hij.symm true true
  · exact Fr.polar_vec_of_ne hij.symm false true
  · exact Fr.polar_vec_of_ne hij false true

private theorem bmsdop_minus_model_data (k f : ℕ)
    (S : Set (GL (Fin (k + 3) ⊕ Fin (k + 3)) (GaloisField 2 f)))
    {e : Matrix (Fin (k + 3) ⊕ Fin (k + 3)) (Fin (k + 3) ⊕ Fin (k + 3)) (GaloisField 2 f)}
    {J' : Subgroup ↥(spinGroup (bmsdop_Q k f))}
    (h1 : bmsdop_geom₁ k f S e) (h2 : bmsdop_geom₂ k f S e)
    (hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s')
    (heA : e ∈ Algebra.adjoin (GaloisField 2 f) (Units.val '' S))
    (hJe : IsComponentOf J' ⁅bmsdop_Ge k f S e, bmsdop_Ge k f S e⁆)
    (ρ : ℕ) (hρ : 3 ≤ ρ) (hrank : e.rank = 2 * ρ) (hf : 1 ≤ f)
    (β γ : GaloisField 2 f) (hirr : ∀ s : GaloisField 2 f, s ^ 2 + β * s + γ ≠ 0)
    (hq : IsQuasisimple (spinGroup (Spin.quadMinus ρ (GaloisField 2 f) β γ)))
    (hΩ : (Spin.spinAction (Spin.quadMinus ρ (GaloisField 2 f) β γ)).range =
      CFSG.RankThree.OrthogonalInvolutions.omegaGroup (Spin.quadMinus ρ (GaloisField 2 f) β γ)
        (Spin.nondegenerate_polarBilin_quadMinus_of_finite ρ (GaloisField 2 f) hirr))
    (hD : bmsdop_AmbientMinus ρ f β γ hirr)
    (θ : (Fin (ρ - 1) ⊕ Fin (ρ - 1) ⊕ Fin 2 → GaloisField 2 f) ≃ₗ[GaloisField 2 f]
      ↥(bmsdop_W k f e))
    (hθ : ∀ x, (bmsdop_blockForm k f e) (θ x) = (Spin.quadMinus ρ (GaloisField 2 f) β γ) x) :
    ∃ (β₀ : Fin (Spin.Twisted.minusDatum ρ hirr).rank → ℤ)
      (ι : spinGroup (Spin.quadMinus ρ (GaloisField 2 f) β γ) →* ↥(spinGroup (bmsdop_Q k f))),
      GGLongRoot (Spin.Twisted.minusDatum ρ hirr) β₀ ∧
      (∀ y, ι y ∈ Subgroup.center ↥(spinGroup (bmsdop_Q k f)) →
        y ∈ Subgroup.center (spinGroup (Spin.quadMinus ρ (GaloisField 2 f) β γ))) ∧
      ι.range = J' ∧
      ∃ a₁ a₂ b₁ b₂ : ((Fin (k + 3) ⊕ Fin (k + 3)) → GaloisField 2 f),
        ((bmsdop_Q k f) a₁ = 0 ∧ (bmsdop_Q k f) a₂ = 0 ∧
          (bmsdop_Q k f) b₁ = 0 ∧ (bmsdop_Q k f) b₂ = 0) ∧
        QuadraticMap.polar (bmsdop_Q k f) a₁ b₁ = 1 ∧
        QuadraticMap.polar (bmsdop_Q k f) a₂ b₂ = 1 ∧
        (QuadraticMap.polar (bmsdop_Q k f) a₁ a₂ = 0 ∧
          QuadraticMap.polar (bmsdop_Q k f) b₁ b₂ = 0 ∧
          QuadraticMap.polar (bmsdop_Q k f) a₁ b₂ = 0 ∧
          QuadraticMap.polar (bmsdop_Q k f) a₂ b₁ = 0) ∧
        ((((Spin.Twisted.minusDatum ρ hirr).rootGroup β₀).map ι).map
          (Spin.spinAction (bmsdop_Q k f)) = siegelGroup (bmsdop_Q k f) a₁ a₂) ∧
        ((((Spin.Twisted.minusDatum ρ hirr).rootGroup (-β₀)).map ι).map
          (Spin.spinAction (bmsdop_Q k f)) = siegelGroup (bmsdop_Q k f) b₁ b₂) := by
  have hnd_std : (QuadraticMap.polarBilin (Spin.quadMinus ρ (GaloisField 2 f) β γ)).Nondegenerate :=
    Spin.nondegenerate_polarBilin_quadMinus_of_finite ρ (GaloisField 2 f) hirr
  haveI : Algebra.IsCentral (GaloisField 2 f)
      (CliffordAlgebra (Spin.quadMinus ρ (GaloisField 2 f) β γ)) :=
    Spin.isCentral_cliffordAlgebra_quadMinus ρ β γ hirr
  have hE : bmsdop_ExtProps k f S e (Spin.quadMinus ρ (GaloisField 2 f) β γ) hnd_std θ
      (bmsdop_glue k f S h1 θ) := by
    have hb := bmsdop_glue_basic k f S h1 h2 (Spin.quadMinus ρ (GaloisField 2 f) β γ) θ hθ
    exact ⟨hb.1, hb.2.1, hb.2.2.1, hb.2.2.2,
      fun g => bmsdop_glue_omegaGroup k f S h1 h2 (Spin.quadMinus ρ (GaloisField 2 f) β γ) θ hθ
        hnd_std g⟩
  obtain ⟨ι₁, hι₁inj, hι₁range, hι₁E, hι₁center⟩ :=
    bmsdop_iota₁ k f S h1 h2 hS heA (Spin.quadMinus ρ (GaloisField 2 f) β γ) hnd_std
      (bmsdop_glue k f S h1 θ) θ hE hθ hΩ
  have hJ' : J' = bmsdop_Ge k f S e :=
    bmsdop_component_eq k f S h1 h2 (Spin.quadMinus ρ (GaloisField 2 f) β γ) hq ι₁
      ⟨hι₁inj, hι₁range⟩ hJe
  obtain ⟨β₀, u₀, a₁, a₂, b₁, b₂, hβlong, hframe, hpol₁, hpol₂, horth, hroot₁, hroot₂⟩ :=
    bmsdop_root_siegel k f S h1 h2 (Spin.quadMinus ρ (GaloisField 2 f) β γ) hnd_std θ hθ
      (Spin.Twisted.minusDatum ρ hirr) ι₁ ⟨hι₁inj, hι₁range⟩
      (bmsdop_glue k f S h1 θ) hE hι₁E hD (bmsdop_minus_frame f ρ hρ β γ hirr)
  have hιrange : (ι₁.comp (MulAut.conj u₀).toMonoidHom).range = J' := by
    rw [MonoidHom.range_comp, MonoidHom.range_eq_top.mpr (MulAut.conj u₀).surjective,
      Subgroup.map_top, hι₁range, hJ']
  have hιcenter : ∀ y, (ι₁.comp (MulAut.conj u₀).toMonoidHom) y ∈
      Subgroup.center ↥(spinGroup (bmsdop_Q k f)) →
      y ∈ Subgroup.center (spinGroup (Spin.quadMinus ρ (GaloisField 2 f) β γ)) := by
    intro y hy
    have h1 := hι₁center (MulAut.conj u₀ y) hy
    rw [Subgroup.mem_center_iff] at h1 ⊢
    intro g
    have h2 := h1 (MulAut.conj u₀ g)
    have h3 := congrArg (MulAut.conj u₀⁻¹) h2
    simpa [MulAut.conj_apply, mul_assoc] using h3
  refine ⟨β₀, ι₁.comp (MulAut.conj u₀).toMonoidHom, hβlong, hιcenter, hιrange,
    θ a₁, θ a₂, θ b₁, θ b₂, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · refine ⟨?_, ?_, ?_, ?_⟩
    · rw [show (bmsdop_Q k f) (θ a₁) = (bmsdop_blockForm k f e) (θ a₁) from rfl, hθ a₁, hframe.1]
    · rw [show (bmsdop_Q k f) (θ a₂) = (bmsdop_blockForm k f e) (θ a₂) from rfl, hθ a₂, hframe.2.1]
    · rw [show (bmsdop_Q k f) (θ b₁) = (bmsdop_blockForm k f e) (θ b₁) from rfl, hθ b₁,
        hframe.2.2.1]
    · rw [show (bmsdop_Q k f) (θ b₂) = (bmsdop_blockForm k f e) (θ b₂) from rfl, hθ b₂,
        hframe.2.2.2]
  · rw [bmsdop_polar_theta k f (Spin.quadMinus ρ (GaloisField 2 f) β γ) θ hθ a₁ b₁]; exact hpol₁
  · rw [bmsdop_polar_theta k f (Spin.quadMinus ρ (GaloisField 2 f) β γ) θ hθ a₂ b₂]; exact hpol₂
  · refine ⟨?_, ?_, ?_, ?_⟩
    · rw [bmsdop_polar_theta k f (Spin.quadMinus ρ (GaloisField 2 f) β γ) θ hθ a₁ a₂]; exact horth.1
    · rw [bmsdop_polar_theta k f (Spin.quadMinus ρ (GaloisField 2 f) β γ) θ hθ b₁ b₂]; exact
        horth.2.1
    · rw [bmsdop_polar_theta k f (Spin.quadMinus ρ (GaloisField 2 f) β γ) θ hθ a₁ b₂]; exact
        horth.2.2.1
    · rw [bmsdop_polar_theta k f (Spin.quadMinus ρ (GaloisField 2 f) β γ) θ hθ a₂ b₁]; exact
        horth.2.2.2
  · rw [← Subgroup.map_map]
    exact hroot₁
  · rw [← Subgroup.map_map]
    exact hroot₂

private lemma bmsdop_minus_arf_isometry (f ρ : ℕ) (β γ : GaloisField 2 f)
    (hirr : ∀ s : GaloisField 2 f, s ^ 2 + β * s + γ ≠ 0) :
    Nonempty ((Spin.quadMinus ρ (GaloisField 2 f) β γ).IsometryEquiv
      (Spin.quadMinus ρ (GaloisField 2 f) (minusCoeffs 2 f).1 (minusCoeffs 2 f).2)) := by
  obtain ⟨e⟩ := GroupTheory.WeirSylow.binForm_isometry (K := GaloisField 2 f) hirr
    (minusCoeffs_irr 2 f)
  exact ⟨(GroupTheory.WeirSylow.quadMinusIsometry (K := GaloisField 2 f) ρ β γ).trans
    ((QuadraticMap.IsometryEquiv.prod
      (QuadraticMap.IsometryEquiv.refl (Spin.quadPlus (ρ - 1) (GaloisField 2 f)))
      e.symm).trans
    (GroupTheory.WeirSylow.quadMinusIsometry (K := GaloisField 2 f) ρ
      (minusCoeffs 2 f).1 (minusCoeffs 2 f).2).symm)⟩

private lemma bmsdop_plus_hext (f ρ : ℕ) (hρ : 3 ≤ ρ) :
    ∀ a₁ a₂ : (Fin ρ ⊕ Fin ρ → GaloisField 2 f),
      a₁ ≠ 0 → a₂ ≠ 0 → LinearIndependent (GaloisField 2 f) ![a₁, a₂] →
      (Spin.quadPlus ρ (GaloisField 2 f)) a₁ = 0 →
      (Spin.quadPlus ρ (GaloisField 2 f)) a₂ = 0 →
      QuadraticMap.polar (Spin.quadPlus ρ (GaloisField 2 f)) a₁ a₂ = 0 →
      ∃ b₁ b₂ : (Fin ρ ⊕ Fin ρ → GaloisField 2 f),
        ((Spin.quadPlus ρ (GaloisField 2 f)) a₁ = 0 ∧
          (Spin.quadPlus ρ (GaloisField 2 f)) a₂ = 0 ∧
          (Spin.quadPlus ρ (GaloisField 2 f)) b₁ = 0 ∧
          (Spin.quadPlus ρ (GaloisField 2 f)) b₂ = 0) ∧
        QuadraticMap.polar (Spin.quadPlus ρ (GaloisField 2 f)) a₁ b₁ = 1 ∧
        QuadraticMap.polar (Spin.quadPlus ρ (GaloisField 2 f)) a₂ b₂ = 1 ∧
        (QuadraticMap.polar (Spin.quadPlus ρ (GaloisField 2 f)) a₁ a₂ = 0 ∧
          QuadraticMap.polar (Spin.quadPlus ρ (GaloisField 2 f)) b₁ b₂ = 0 ∧
          QuadraticMap.polar (Spin.quadPlus ρ (GaloisField 2 f)) a₁ b₂ = 0 ∧
          QuadraticMap.polar (Spin.quadPlus ρ (GaloisField 2 f)) a₂ b₁ = 0) := by
  intro a₁ a₂ ha₁ ha₂ hlin hQ₁ hQ₂ hpol
  let Q := Spin.quadPlus ρ (GaloisField 2 f)
  let Fr : Spin.HypFrame Q ρ := Spin.plusFrame ρ (GaloisField 2 f) hρ
  let i0 : Fin ρ := ⟨0, by omega⟩
  let i1 : Fin ρ := ⟨1, by omega⟩
  have hij : i0 ≠ i1 := by
    intro h
    have h01 : (0 : ℕ) = 1 := by simpa [i0, i1] using congrArg Fin.val h
    omega
  have hLI : LinearIndependent (GaloisField 2 f) ![Fr.vec i0 false, Fr.vec i1 false] := by
    rw [LinearIndependent.pair_iff]
    intro c d hcd
    have hc : c = 0 := by
      have h := congrArg (QuadraticMap.polarBilin Q (Fr.vec i0 true)) hcd
      simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul,
        map_zero] at h
      rw [QuadraticMap.polarBilin_apply_apply, QuadraticMap.polarBilin_apply_apply] at h
      rw [Fr.polar_vec_of_ne hij true false, QuadraticMap.polar_comm] at h
      rw [show QuadraticMap.polar (⇑Q) (Fr.vec i0 false) (Fr.vec i0 true) = 1 from
        Fr.polar_vec_not i0 false] at h
      simpa using h
    have hd : d = 0 := by
      have h := congrArg (QuadraticMap.polarBilin Q (Fr.vec i1 true)) hcd
      simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul,
        map_zero] at h
      rw [QuadraticMap.polarBilin_apply_apply, QuadraticMap.polarBilin_apply_apply] at h
      rw [Fr.polar_vec_of_ne hij.symm true false, QuadraticMap.polar_comm] at h
      rw [show QuadraticMap.polar (⇑Q) (Fr.vec i1 false) (Fr.vec i1 true) = 1 from
        Fr.polar_vec_not i1 false] at h
      simpa using h
    exact ⟨hc, hd⟩
  obtain ⟨g, hgO, hg⟩ := CFSG.StandardType.TableBOrth.exists_orth_apply_eq
    (K := GaloisField 2 f) (Spin.nondegenerate_polarBilin_quadPlus ρ (GaloisField 2 f))
    ![a₁, a₂] ![Fr.vec i0 false, Fr.vec i1 false] hlin hLI
    (by
      intro i
      fin_cases i <;>
        simp [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Fr.map_vec,
          hQ₁, hQ₂])
    (by
      intro i j
      fin_cases i <;> fin_cases j
      · change QuadraticMap.polar (⇑Q) (Fr.vec i0 false) (Fr.vec i0 false) =
          QuadraticMap.polar (⇑Q) a₁ a₁
        rw [Fr.polar_vec_vec, QuadraticMap.polar_self, hQ₁, smul_zero]; simp
      · change QuadraticMap.polar (⇑Q) (Fr.vec i0 false) (Fr.vec i1 false) =
          QuadraticMap.polar (⇑Q) a₁ a₂
        rw [Fr.polar_vec_of_ne hij false false, hpol]
      · change QuadraticMap.polar (⇑Q) (Fr.vec i1 false) (Fr.vec i0 false) =
          QuadraticMap.polar (⇑Q) a₂ a₁
        rw [Fr.polar_vec_of_ne hij.symm false false, QuadraticMap.polar_comm, hpol]
      · change QuadraticMap.polar (⇑Q) (Fr.vec i1 false) (Fr.vec i1 false) =
          QuadraticMap.polar (⇑Q) a₂ a₂
        rw [Fr.polar_vec_vec, QuadraticMap.polar_self, hQ₂, smul_zero]; simp)
  have hg0 : g a₁ = Fr.vec i0 false := by simpa using hg 0
  have hg1 : g a₂ = Fr.vec i1 false := by simpa using hg 1
  refine ⟨g.symm (Fr.vec i0 true), g.symm (Fr.vec i1 true), ⟨hQ₁, hQ₂, ?_, ?_⟩, ?_, ?_,
    ⟨hpol, ?_, ?_, ?_⟩⟩
  · rw [← CFSG.ClassicalGroups.Orthogonal.map_of_mem hgO (g.symm (Fr.vec i0 true)),
      LinearEquiv.apply_symm_apply]
    exact Fr.map_vec i0 true
  · rw [← CFSG.ClassicalGroups.Orthogonal.map_of_mem hgO (g.symm (Fr.vec i1 true)),
      LinearEquiv.apply_symm_apply]
    exact Fr.map_vec i1 true
  · rw [← CFSG.ClassicalGroups.Orthogonal.polar_map_of_mem hgO a₁ (g.symm (Fr.vec i0 true)),
      hg0, LinearEquiv.apply_symm_apply]
    exact Fr.polar_vec_not i0 false
  · rw [← CFSG.ClassicalGroups.Orthogonal.polar_map_of_mem hgO a₂ (g.symm (Fr.vec i1 true)),
      hg1, LinearEquiv.apply_symm_apply]
    exact Fr.polar_vec_not i1 false
  · rw [← CFSG.ClassicalGroups.Orthogonal.polar_map_of_mem hgO (g.symm (Fr.vec i0 true))
        (g.symm (Fr.vec i1 true)), LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]
    exact Fr.polar_vec_of_ne hij true true
  · rw [← CFSG.ClassicalGroups.Orthogonal.polar_map_of_mem hgO a₁ (g.symm (Fr.vec i1 true)),
      hg0, LinearEquiv.apply_symm_apply]
    exact Fr.polar_vec_of_ne hij false true
  · rw [← CFSG.ClassicalGroups.Orthogonal.polar_map_of_mem hgO a₂ (g.symm (Fr.vec i0 true)),
      hg1, LinearEquiv.apply_symm_apply]
    exact Fr.polar_vec_of_ne hij.symm false true

private lemma bmsdop_minus_hext (f ρ : ℕ) (hρ : 3 ≤ ρ) (β γ : GaloisField 2 f)
    (hirr : ∀ s : GaloisField 2 f, s ^ 2 + β * s + γ ≠ 0) :
    ∀ a₁ a₂ : (Fin (ρ - 1) ⊕ Fin (ρ - 1) ⊕ Fin 2 → GaloisField 2 f),
      a₁ ≠ 0 → a₂ ≠ 0 → LinearIndependent (GaloisField 2 f) ![a₁, a₂] →
      (Spin.quadMinus ρ (GaloisField 2 f) β γ) a₁ = 0 →
      (Spin.quadMinus ρ (GaloisField 2 f) β γ) a₂ = 0 →
      QuadraticMap.polar (Spin.quadMinus ρ (GaloisField 2 f) β γ) a₁ a₂ = 0 →
      ∃ b₁ b₂ : (Fin (ρ - 1) ⊕ Fin (ρ - 1) ⊕ Fin 2 → GaloisField 2 f),
        ((Spin.quadMinus ρ (GaloisField 2 f) β γ) a₁ = 0 ∧
          (Spin.quadMinus ρ (GaloisField 2 f) β γ) a₂ = 0 ∧
          (Spin.quadMinus ρ (GaloisField 2 f) β γ) b₁ = 0 ∧
          (Spin.quadMinus ρ (GaloisField 2 f) β γ) b₂ = 0) ∧
        QuadraticMap.polar (Spin.quadMinus ρ (GaloisField 2 f) β γ) a₁ b₁ = 1 ∧
        QuadraticMap.polar (Spin.quadMinus ρ (GaloisField 2 f) β γ) a₂ b₂ = 1 ∧
        (QuadraticMap.polar (Spin.quadMinus ρ (GaloisField 2 f) β γ) a₁ a₂ = 0 ∧
          QuadraticMap.polar (Spin.quadMinus ρ (GaloisField 2 f) β γ) b₁ b₂ = 0 ∧
          QuadraticMap.polar (Spin.quadMinus ρ (GaloisField 2 f) β γ) a₁ b₂ = 0 ∧
          QuadraticMap.polar (Spin.quadMinus ρ (GaloisField 2 f) β γ) a₂ b₁ = 0) := by
  intro a₁ a₂ ha₁ ha₂ hlin hQ₁ hQ₂ hpol
  let Q := Spin.quadMinus ρ (GaloisField 2 f) β γ
  let Fr : Spin.HypFrame Q (ρ - 1) := (Spin.Twisted.minusFrame ρ β γ).toHypFrame
  let i0 : Fin (ρ - 1) := ⟨0, by omega⟩
  let i1 : Fin (ρ - 1) := ⟨1, by omega⟩
  have hij : i0 ≠ i1 := by
    intro h
    have h01 : (0 : ℕ) = 1 := by simpa [i0, i1] using congrArg Fin.val h
    omega
  have hLI : LinearIndependent (GaloisField 2 f) ![Fr.vec i0 false, Fr.vec i1 false] := by
    rw [LinearIndependent.pair_iff]
    intro c d hcd
    have hc : c = 0 := by
      have h := congrArg (QuadraticMap.polarBilin Q (Fr.vec i0 true)) hcd
      simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul,
        map_zero] at h
      rw [QuadraticMap.polarBilin_apply_apply, QuadraticMap.polarBilin_apply_apply] at h
      rw [Fr.polar_vec_of_ne hij true false, QuadraticMap.polar_comm] at h
      rw [show QuadraticMap.polar (⇑Q) (Fr.vec i0 false) (Fr.vec i0 true) = 1 from
        Fr.polar_vec_not i0 false] at h
      simpa using h
    have hd : d = 0 := by
      have h := congrArg (QuadraticMap.polarBilin Q (Fr.vec i1 true)) hcd
      simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul,
        map_zero] at h
      rw [QuadraticMap.polarBilin_apply_apply, QuadraticMap.polarBilin_apply_apply] at h
      rw [Fr.polar_vec_of_ne hij.symm true false, QuadraticMap.polar_comm] at h
      rw [show QuadraticMap.polar (⇑Q) (Fr.vec i1 false) (Fr.vec i1 true) = 1 from
        Fr.polar_vec_not i1 false] at h
      simpa using h
    exact ⟨hc, hd⟩
  obtain ⟨g, hgO, hg⟩ := CFSG.StandardType.TableBOrth.exists_orth_apply_eq
    (K := GaloisField 2 f)
    (Spin.nondegenerate_polarBilin_quadMinus_of_finite ρ (GaloisField 2 f) hirr)
    ![a₁, a₂] ![Fr.vec i0 false, Fr.vec i1 false] hlin hLI
    (by
      intro i
      fin_cases i <;>
        simp [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Fr.map_vec,
          hQ₁, hQ₂])
    (by
      intro i j
      fin_cases i <;> fin_cases j
      · change QuadraticMap.polar (⇑Q) (Fr.vec i0 false) (Fr.vec i0 false) =
          QuadraticMap.polar (⇑Q) a₁ a₁
        rw [Fr.polar_vec_vec, QuadraticMap.polar_self, hQ₁, smul_zero]; simp
      · change QuadraticMap.polar (⇑Q) (Fr.vec i0 false) (Fr.vec i1 false) =
          QuadraticMap.polar (⇑Q) a₁ a₂
        rw [Fr.polar_vec_of_ne hij false false, hpol]
      · change QuadraticMap.polar (⇑Q) (Fr.vec i1 false) (Fr.vec i0 false) =
          QuadraticMap.polar (⇑Q) a₂ a₁
        rw [Fr.polar_vec_of_ne hij.symm false false, QuadraticMap.polar_comm, hpol]
      · change QuadraticMap.polar (⇑Q) (Fr.vec i1 false) (Fr.vec i1 false) =
          QuadraticMap.polar (⇑Q) a₂ a₂
        rw [Fr.polar_vec_vec, QuadraticMap.polar_self, hQ₂, smul_zero]; simp)
  have hg0 : g a₁ = Fr.vec i0 false := by simpa using hg 0
  have hg1 : g a₂ = Fr.vec i1 false := by simpa using hg 1
  refine ⟨g.symm (Fr.vec i0 true), g.symm (Fr.vec i1 true), ⟨hQ₁, hQ₂, ?_, ?_⟩, ?_, ?_,
    ⟨hpol, ?_, ?_, ?_⟩⟩
  · rw [← CFSG.ClassicalGroups.Orthogonal.map_of_mem hgO (g.symm (Fr.vec i0 true)),
      LinearEquiv.apply_symm_apply]
    exact Fr.map_vec i0 true
  · rw [← CFSG.ClassicalGroups.Orthogonal.map_of_mem hgO (g.symm (Fr.vec i1 true)),
      LinearEquiv.apply_symm_apply]
    exact Fr.map_vec i1 true
  · rw [← CFSG.ClassicalGroups.Orthogonal.polar_map_of_mem hgO a₁ (g.symm (Fr.vec i0 true)),
      hg0, LinearEquiv.apply_symm_apply]
    exact Fr.polar_vec_not i0 false
  · rw [← CFSG.ClassicalGroups.Orthogonal.polar_map_of_mem hgO a₂ (g.symm (Fr.vec i1 true)),
      hg1, LinearEquiv.apply_symm_apply]
    exact Fr.polar_vec_not i1 false
  · rw [← CFSG.ClassicalGroups.Orthogonal.polar_map_of_mem hgO (g.symm (Fr.vec i0 true))
        (g.symm (Fr.vec i1 true)), LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]
    exact Fr.polar_vec_of_ne hij true true
  · rw [← CFSG.ClassicalGroups.Orthogonal.polar_map_of_mem hgO a₁ (g.symm (Fr.vec i1 true)),
      hg0, LinearEquiv.apply_symm_apply]
    exact Fr.polar_vec_of_ne hij false true
  · rw [← CFSG.ClassicalGroups.Orthogonal.polar_map_of_mem hgO a₂ (g.symm (Fr.vec i0 true)),
      hg1, LinearEquiv.apply_symm_apply]
    exact Fr.polar_vec_of_ne hij.symm false true

private theorem bmsdop_ext
    (k f : ℕ) (S : Set (GL (Fin (k + 3) ⊕ Fin (k + 3)) (GaloisField 2 f)))
    {e : Matrix (Fin (k + 3) ⊕ Fin (k + 3)) (Fin (k + 3) ⊕ Fin (k + 3)) (GaloisField 2 f)}
    (h1 : bmsdop_geom₁ k f S e) (h2 : bmsdop_geom₂ k f S e)
    {Vstd : Type} [AddCommGroup Vstd] [Module (GaloisField 2 f) Vstd]
    [FiniteDimensional (GaloisField 2 f) Vstd]
    (Qstd : QuadraticForm (GaloisField 2 f) Vstd)
    (θ : Vstd ≃ₗ[GaloisField 2 f] ↥(bmsdop_W k f e))
    (hθ : ∀ x, (bmsdop_blockForm k f e) (θ x) = Qstd x)
    (hnd_std : (QuadraticMap.polarBilin Qstd).Nondegenerate) :
    ∃ (E : (Vstd ≃ₗ[GaloisField 2 f] Vstd) →*
        (((Fin (k + 3) ⊕ Fin (k + 3)) → GaloisField 2 f) ≃ₗ[GaloisField 2 f]
          ((Fin (k + 3) ⊕ Fin (k + 3)) → GaloisField 2 f))),
      bmsdop_ExtProps k f S e Qstd hnd_std θ E := by
  obtain ⟨hiso, hinj, hfix, heq⟩ := bmsdop_glue_basic k f S h1 h2 Qstd θ hθ
  exact ⟨bmsdop_glue k f S h1 θ, hiso, hinj, hfix, heq,
    bmsdop_glue_omegaGroup k f S h1 h2 Qstd θ hθ hnd_std⟩

private lemma bmsdop_r2_degenerate (k f : ℕ)
    (S : Set (GL (Fin (k + 3) ⊕ Fin (k + 3)) (GaloisField 2 f)))
    {e : Matrix (Fin (k + 3) ⊕ Fin (k + 3)) (Fin (k + 3) ⊕ Fin (k + 3)) (GaloisField 2 f)}
    {J' : Subgroup ↥(spinGroup (bmsdop_Q k f))}
    (h1 : bmsdop_geom₁ k f S e) (h2 : bmsdop_geom₂ k f S e)
    (hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s')
    (heA : e ∈ Algebra.adjoin (GaloisField 2 f) (Units.val '' S))
    (hJe : IsComponentOf J' ⁅bmsdop_Ge k f S e, bmsdop_Ge k f S e⁆)
    (θ : (Fin 2 ⊕ Fin 2 → GaloisField 2 f) ≃ₗ[GaloisField 2 f] ↥(bmsdop_W k f e))
    (hθ : ∀ x, (bmsdop_blockForm k f e) (θ x) = (Spin.quadPlus 2 (GaloisField 2 f)) x)
    (hcard : Nat.card (GaloisField 2 f) = 2) : False := by
  classical
  let Qstd : QuadraticForm (GaloisField 2 f) (Fin 2 ⊕ Fin 2 → GaloisField 2 f) :=
    Spin.quadPlus 2 (GaloisField 2 f)
  have hnd_std : (QuadraticMap.polarBilin Qstd).Nondegenerate :=
    Spin.nondegenerate_polarBilin_quadPlus 2 (GaloisField 2 f)
  obtain ⟨E, hE⟩ := bmsdop_ext k f S h1 h2 Qstd θ hθ hnd_std
  have hmap := bmsdop_block_group_eq_ext k f S h1 h2 hS heA Qstd hnd_std E θ hE
  have hfin_std : Module.finrank (GaloisField 2 f) (Fin 2 ⊕ Fin 2 → GaloisField 2 f) = 4 := by
    rw [Module.finrank_fintype_fun_eq_card, Fintype.card_sum, Fintype.card_fin]
  have hplus_std : CFSG.GroupTheory.WeirSylow.IsPlusType Qstd :=
    CFSG.GroupTheory.WeirSylow.isPlusType_quadPlus (GaloisField 2 f) 2
  haveI : Group.IsSolvable ↥(TauCeti.QuadraticMap.orthogonalGroup Qstd) :=
    CFSG.LocalAnalysis.GLTheoremA.T123CB.isSolvable_orthogonalGroup_of_card_two_of_plus
      Qstd hnd_std hcard hfin_std hplus_std
  haveI : Group.IsSolvable
      ↥(CFSG.RankThree.OrthogonalInvolutions.omegaGroup Qstd hnd_std) :=
    solvable_of_solvable_injective
      (Subgroup.inclusion_injective
        (CFSG.RankThree.OrthogonalInvolutions.omegaGroup_le Qstd hnd_std))
  have hsolvΩE : Group.IsSolvable
      ↥((CFSG.RankThree.OrthogonalInvolutions.omegaGroup Qstd hnd_std).map E) :=
    CFSG.ClassicalInvolution.LBalanceProof.isSolvable_map_of_isSolvable E
      (CFSG.RankThree.OrthogonalInvolutions.omegaGroup Qstd hnd_std)
  let φ : ↥(bmsdop_Ge k f S e) →*
      (bmsdop_V k f ≃ₗ[GaloisField 2 f] bmsdop_V k f) :=
    (Spin.spinAction (bmsdop_Q k f)).comp (Subgroup.subtype (bmsdop_Ge k f S e))
  have hφinj : Function.Injective φ := by
    intro a b hab
    exact Subtype.ext (bmsdop_spinAction_injective k f hab)
  have hrange : φ.range =
      (CFSG.RankThree.OrthogonalInvolutions.omegaGroup Qstd hnd_std).map E := by
    have hφrange : φ.range =
        (bmsdop_Ge k f S e).map (Spin.spinAction (bmsdop_Q k f)) := by
      simp only [φ, MonoidHom.range_comp, Subgroup.range_subtype]
    exact hφrange.trans hmap
  haveI : Group.IsSolvable ↥φ.range := by
    rw [hrange]
    exact hsolvΩE
  haveI : Group.IsSolvable ↥(bmsdop_Ge k f S e) :=
    solvable_of_solvable_injective (MonoidHom.ofInjective hφinj).injective
  haveI : Group.IsSolvable ↥⁅bmsdop_Ge k f S e, bmsdop_Ge k f S e⁆ :=
    solvable_of_solvable_injective
      (Subgroup.inclusion_injective (Subgroup.commutator_le_self (bmsdop_Ge k f S e)))
  have hsolvJ : Group.IsSolvable ↥J' :=
    solvable_of_solvable_injective (Subgroup.inclusion_injective hJe.1)
  have hperf : Group.IsPerfect ↥J' := (Group.isPerfect_def).mpr hJe.2.2.1
  have hsub : Subsingleton ↥J' :=
    CFSG.RankThree.PartTwo.Sec21.subsingleton_of_isPerfect_of_isSolvable hperf hsolvJ
  haveI hsubI : Subsingleton ↥J' := hsub
  haveI : Nontrivial (↥J' ⧸ Subgroup.center ↥J') := (isSimpleGroup_iff _).mp hJe.2.2.2 |>.1
  exact not_subsingleton (↥J' ⧸ Subgroup.center ↥J') inferInstance

private lemma bmsdop_r2_restrict (k f : ℕ)
    (S : Set (GL (Fin (k + 3) ⊕ Fin (k + 3)) (GaloisField 2 f)))
    {e : Matrix (Fin (k + 3) ⊕ Fin (k + 3)) (Fin (k + 3) ⊕ Fin (k + 3)) (GaloisField 2 f)}
    (h1 : bmsdop_geom₁ k f S e) (h2 : bmsdop_geom₂ k f S e)
    (hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s')
    (heA : e ∈ Algebra.adjoin (GaloisField 2 f) (Units.val '' S))
    (θ : (Fin 2 ⊕ Fin 2 → GaloisField 2 f) ≃ₗ[GaloisField 2 f] ↥(bmsdop_W k f e))
    (hθ : ∀ x, (bmsdop_blockForm k f e) (θ x) = (Spin.quadPlus 2 (GaloisField 2 f)) x)
    (E : ((Fin 2 ⊕ Fin 2 → GaloisField 2 f) ≃ₗ[GaloisField 2 f]
        (Fin 2 ⊕ Fin 2 → GaloisField 2 f)) →*
        (bmsdop_V k f ≃ₗ[GaloisField 2 f] bmsdop_V k f))
    (hE : bmsdop_ExtProps k f S e (Spin.quadPlus 2 (GaloisField 2 f))
        (Spin.nondegenerate_polarBilin_quadPlus 2 (GaloisField 2 f)) θ E) :
    ∃ r : ↥(CFSG.RankThree.OrthogonalInvolutions.omegaGroup (Spin.quadPlus 2 (GaloisField 2 f))
          (Spin.nondegenerate_polarBilin_quadPlus 2 (GaloisField 2 f))) →*
        ↥(spinGroup (bmsdop_Q k f)),
      Function.Injective r ∧ r.range = bmsdop_Ge k f S e ∧
        ∀ g, Spin.spinAction (bmsdop_Q k f) (r g) = E g := by
  classical
  let Qstd : QuadraticForm (GaloisField 2 f) (Fin 2 ⊕ Fin 2 → GaloisField 2 f) :=
    Spin.quadPlus 2 (GaloisField 2 f)
  have hnd_std : (QuadraticMap.polarBilin Qstd).Nondegenerate :=
    Spin.nondegenerate_polarBilin_quadPlus 2 (GaloisField 2 f)
  let Ωstd : Subgroup ((Fin 2 ⊕ Fin 2 → GaloisField 2 f) ≃ₗ[GaloisField 2 f]
      (Fin 2 ⊕ Fin 2 → GaloisField 2 f)) :=
    CFSG.RankThree.OrthogonalInvolutions.omegaGroup Qstd hnd_std
  have hmap := bmsdop_block_group_eq_ext k f S h1 h2 hS heA Qstd hnd_std E θ hE
  let φ : ↥(bmsdop_Ge k f S e) →*
      (bmsdop_V k f ≃ₗ[GaloisField 2 f] bmsdop_V k f) :=
    (Spin.spinAction (bmsdop_Q k f)).comp (Subgroup.subtype (bmsdop_Ge k f S e))
  have hφinj : Function.Injective φ := by
    intro a b hab
    exact Subtype.ext ((bmsdop_spinAction_injective k f) hab)
  have hφrange : φ.range = Ωstd.map E := by
    have h : φ.range = (bmsdop_Ge k f S e).map (Spin.spinAction (bmsdop_Q k f)) := by
      simp only [φ, MonoidHom.range_comp, Subgroup.range_subtype]
    exact h.trans hmap
  let ψ : ↥Ωstd →* ↥φ.range :=
    MonoidHom.codRestrict (E.comp (Subgroup.subtype Ωstd)) φ.range
      (fun g => hφrange.ge (Subgroup.mem_map.mpr ⟨g, g.2, rfl⟩))
  have hψinj : Function.Injective ψ := by
    intro a b hab
    exact Subtype.ext (hE.2.1 (congrArg Subtype.val hab))
  have hψsurj : Function.Surjective ψ := by
    intro y
    obtain ⟨g, hg, hgy⟩ := Subgroup.mem_map.mp (hφrange.le y.2)
    exact ⟨⟨g, hg⟩, Subtype.ext hgy⟩
  let r : ↥Ωstd →* ↥(spinGroup (bmsdop_Q k f)) :=
    ((Subgroup.subtype (bmsdop_Ge k f S e)).comp
      ((MonoidHom.ofInjective hφinj).symm.toMonoidHom)).comp ψ
  refine ⟨r, ?_, ?_, ?_⟩
  · intro a b hab
    have h1 : ((MonoidHom.ofInjective hφinj).symm (ψ a)) =
        ((MonoidHom.ofInjective hφinj).symm (ψ b)) :=
      Subgroup.subtype_injective (bmsdop_Ge k f S e) hab
    exact hψinj ((MonoidHom.ofInjective hφinj).symm.injective h1)
  · apply le_antisymm
    · rintro x ⟨g, rfl⟩
      exact ((MonoidHom.ofInjective hφinj).symm (ψ g)).2
    · intro x hx
      obtain ⟨g, hg⟩ := hψsurj ((MonoidHom.ofInjective hφinj) ⟨x, hx⟩)
      refine ⟨g, ?_⟩
      change ((MonoidHom.ofInjective hφinj).symm (ψ g)).val = x
      rw [hg, MulEquiv.symm_apply_apply]
  · intro g
    change Spin.spinAction (bmsdop_Q k f)
      (((MonoidHom.ofInjective hφinj).symm (ψ g)) : spinGroup (bmsdop_Q k f)) = E g
    have h : ((MonoidHom.ofInjective hφinj)
          ((MonoidHom.ofInjective hφinj).symm (ψ g))).val = (ψ g).val :=
      congrArg Subtype.val ((MonoidHom.ofInjective hφinj).apply_symm_apply (ψ g))
    exact h

private noncomputable def bmsdop_r2_kappa (f : ℕ) :
    (Fin 2 ⊕ Fin 2 → GaloisField 2 f) ≃ₗ[GaloisField 2 f]
      Matrix (Fin 2) (Fin 2) (GaloisField 2 f) where
  toFun x := !![x (Sum.inl 0), x (Sum.inl 1); x (Sum.inr 1), x (Sum.inr 0)]
  invFun M := fun z => Sum.elim (fun i => M 0 i) (fun i => M 1 (1 - i)) z
  left_inv := by
    intro x
    ext z
    rcases z with i | i <;> fin_cases i <;> simp
  right_inv := by
    intro M
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  map_add' := by
    intro x y
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  map_smul' := by
    intro c x
    ext i j
    fin_cases i <;> fin_cases j <;> simp

private lemma bmsdop_r2_kappa_det (f : ℕ) (x : Fin 2 ⊕ Fin 2 → GaloisField 2 f) :
    (bmsdop_r2_kappa f x).det = (Spin.quadPlus 2 (GaloisField 2 f)) x := by
  rw [Spin.quadPlus_apply, Fin.sum_univ_two]
  simp [bmsdop_r2_kappa, Matrix.det_fin_two, CharTwo.sub_eq_add]

private lemma bmsdop_r2_kappa_polar (f : ℕ) (x y : Fin 2 ⊕ Fin 2 → GaloisField 2 f) :
    QuadraticMap.polar (Spin.quadPlus 2 (GaloisField 2 f)) x y =
      (bmsdop_r2_kappa f x + bmsdop_r2_kappa f y).det -
        (bmsdop_r2_kappa f x).det - (bmsdop_r2_kappa f y).det := by
  rw [← map_add]
  rw [bmsdop_r2_kappa_det, bmsdop_r2_kappa_det, bmsdop_r2_kappa_det]
  rfl

private noncomputable def bmsdop_r2_e11 (f : ℕ) : Fin 2 ⊕ Fin 2 → GaloisField 2 f :=
  (bmsdop_r2_kappa f).symm (!![1, 0; 0, 0] : Matrix (Fin 2) (Fin 2) (GaloisField 2 f))

private noncomputable def bmsdop_r2_e12 (f : ℕ) : Fin 2 ⊕ Fin 2 → GaloisField 2 f :=
  (bmsdop_r2_kappa f).symm (!![0, 1; 0, 0] : Matrix (Fin 2) (Fin 2) (GaloisField 2 f))

private noncomputable def bmsdop_r2_e21 (f : ℕ) : Fin 2 ⊕ Fin 2 → GaloisField 2 f :=
  (bmsdop_r2_kappa f).symm (!![0, 0; 1, 0] : Matrix (Fin 2) (Fin 2) (GaloisField 2 f))

private noncomputable def bmsdop_r2_e22 (f : ℕ) : Fin 2 ⊕ Fin 2 → GaloisField 2 f :=
  (bmsdop_r2_kappa f).symm (!![0, 0; 0, 1] : Matrix (Fin 2) (Fin 2) (GaloisField 2 f))

private noncomputable def bmsdop_r2_mulLeftEquiv (f : ℕ)
    (g : Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 f)) :
    Matrix (Fin 2) (Fin 2) (GaloisField 2 f) ≃ₗ[GaloisField 2 f]
      Matrix (Fin 2) (Fin 2) (GaloisField 2 f) :=
  LinearEquiv.ofBijective
    (LinearMap.mulLeft (GaloisField 2 f) (g : Matrix (Fin 2) (Fin 2) (GaloisField 2 f)))
    (by
      have hleft : Function.LeftInverse
          (fun Y : Matrix (Fin 2) (Fin 2) (GaloisField 2 f) =>
            (g⁻¹ : Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 f)) * Y)
          (fun X : Matrix (Fin 2) (Fin 2) (GaloisField 2 f) =>
            (g : Matrix (Fin 2) (Fin 2) (GaloisField 2 f)) * X) := by
        intro X
        show ((g⁻¹ : Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 f)) :
              Matrix (Fin 2) (Fin 2) (GaloisField 2 f)) *
            ((g : Matrix (Fin 2) (Fin 2) (GaloisField 2 f)) * X) = X
        rw [← Matrix.mul_assoc, ← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel,
          Matrix.SpecialLinearGroup.coe_one, Matrix.one_mul]
      have hright : Function.RightInverse
          (fun Y : Matrix (Fin 2) (Fin 2) (GaloisField 2 f) =>
            (g⁻¹ : Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 f)) * Y)
          (fun X : Matrix (Fin 2) (Fin 2) (GaloisField 2 f) =>
            (g : Matrix (Fin 2) (Fin 2) (GaloisField 2 f)) * X) := by
        intro Y
        show ((g : Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 f)) :
              Matrix (Fin 2) (Fin 2) (GaloisField 2 f)) *
            ((g⁻¹ : Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 f)) * Y) = Y
        rw [← Matrix.mul_assoc, ← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel,
          Matrix.SpecialLinearGroup.coe_one, Matrix.one_mul]
      exact ⟨hleft.injective, hright.surjective⟩)

private noncomputable def bmsdop_r2_mulRightEquiv (f : ℕ)
    (g : Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 f)) :
    Matrix (Fin 2) (Fin 2) (GaloisField 2 f) ≃ₗ[GaloisField 2 f]
      Matrix (Fin 2) (Fin 2) (GaloisField 2 f) :=
  LinearEquiv.ofBijective
    (LinearMap.mulRight (GaloisField 2 f)
      ((g⁻¹ : Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 f)) :
        Matrix (Fin 2) (Fin 2) (GaloisField 2 f)))
    (by
      have hleft : Function.LeftInverse
          (fun Y : Matrix (Fin 2) (Fin 2) (GaloisField 2 f) =>
            Y * (g : Matrix (Fin 2) (Fin 2) (GaloisField 2 f)))
          (fun X : Matrix (Fin 2) (Fin 2) (GaloisField 2 f) =>
            X * ((g⁻¹ : Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 f)) :
              Matrix (Fin 2) (Fin 2) (GaloisField 2 f))) := by
        intro X
        show (X * ((g⁻¹ : Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 f)) :
              Matrix (Fin 2) (Fin 2) (GaloisField 2 f))) *
            (g : Matrix (Fin 2) (Fin 2) (GaloisField 2 f)) = X
        rw [Matrix.mul_assoc, ← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel,
          Matrix.SpecialLinearGroup.coe_one, Matrix.mul_one]
      have hright : Function.RightInverse
          (fun Y : Matrix (Fin 2) (Fin 2) (GaloisField 2 f) =>
            Y * (g : Matrix (Fin 2) (Fin 2) (GaloisField 2 f)))
          (fun X : Matrix (Fin 2) (Fin 2) (GaloisField 2 f) =>
            X * ((g⁻¹ : Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 f)) :
              Matrix (Fin 2) (Fin 2) (GaloisField 2 f))) := by
        intro Y
        show (Y * (g : Matrix (Fin 2) (Fin 2) (GaloisField 2 f))) *
            ((g⁻¹ : Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 f)) :
              Matrix (Fin 2) (Fin 2) (GaloisField 2 f)) = Y
        rw [Matrix.mul_assoc, ← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel,
          Matrix.SpecialLinearGroup.coe_one, Matrix.mul_one]
      exact ⟨hleft.injective, hright.surjective⟩)

private lemma bmsdop_r2_mulLeftEquiv_apply (f : ℕ)
    (g : Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 f))
    (X : Matrix (Fin 2) (Fin 2) (GaloisField 2 f)) :
    bmsdop_r2_mulLeftEquiv f g X =
      (g : Matrix (Fin 2) (Fin 2) (GaloisField 2 f)) * X := rfl

private noncomputable def bmsdop_r2_rhoLFun (f : ℕ)
    (g : Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 f)) :
    (Fin 2 ⊕ Fin 2 → GaloisField 2 f) ≃ₗ[GaloisField 2 f]
      (Fin 2 ⊕ Fin 2 → GaloisField 2 f) :=
  (bmsdop_r2_kappa f).trans ((bmsdop_r2_mulLeftEquiv f g).trans (bmsdop_r2_kappa f).symm)

private lemma bmsdop_r2_rhoLFun_apply (f : ℕ)
    (g : Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 f))
    (x : Fin 2 ⊕ Fin 2 → GaloisField 2 f) :
    bmsdop_r2_rhoLFun f g x = (bmsdop_r2_kappa f).symm
      ((g : Matrix (Fin 2) (Fin 2) (GaloisField 2 f)) * (bmsdop_r2_kappa f) x) := by
  simp only [bmsdop_r2_rhoLFun, LinearEquiv.trans_apply, bmsdop_r2_mulLeftEquiv_apply]

private lemma bmsdop_r2_col_mul (f : ℕ) (A X : Matrix (Fin 2) (Fin 2) (GaloisField 2 f))
    (j : Fin 2) :
    Matrix.col (A * X) j = A.mulVec (Matrix.col X j) := by
  ext i
  simp only [Matrix.col_apply, Matrix.mul_apply, Matrix.mulVec_apply, dotProduct, Matrix.row]

private noncomputable def bmsdop_r2_rangeMulLeftEquiv (f : ℕ)
    (A : Matrix (Fin 2) (Fin 2) (GaloisField 2 f)) :
    ↥(LinearMap.range (LinearMap.mulLeft (GaloisField 2 f) A)) ≃ₗ[GaloisField 2 f]
      (Fin 2 → ↥(LinearMap.range (Matrix.mulVecLin A))) where
  toFun M := fun j => ⟨Matrix.col (M : Matrix (Fin 2) (Fin 2) (GaloisField 2 f)) j, by
    obtain ⟨X, hX⟩ := LinearMap.mem_range.mp M.2
    refine ⟨Matrix.col X j, ?_⟩
    rw [Matrix.mulVecLin_apply, ← bmsdop_r2_col_mul f A X j]
    exact congrArg (fun Y => Matrix.col Y j) hX⟩
  invFun g := ⟨Matrix.of (fun i j => (g j : Fin 2 → GaloisField 2 f) i), by
    choose X hX using fun j => LinearMap.mem_range.mp (g j).2
    refine ⟨Matrix.of (fun a b => X b a), ?_⟩
    ext i j
    simp only [LinearMap.mulLeft_apply, Matrix.mul_apply, Matrix.of_apply]
    rw [← hX j]
    simp only [Matrix.mulVecLin_apply, Matrix.mulVec_apply, dotProduct, Matrix.row]⟩
  left_inv := by intro M; ext j i; rfl
  right_inv := by intro g; ext j i; rfl
  map_add' := by intro M N; ext j i; rfl
  map_smul' := by intro c M; ext j i; rfl

private lemma bmsdop_r2_finrank_range_mulLeft (f : ℕ)
    (A : Matrix (Fin 2) (Fin 2) (GaloisField 2 f)) :
    Even (Module.finrank (GaloisField 2 f)
      ↥(LinearMap.range (LinearMap.mulLeft (GaloisField 2 f) A))) := by
  rw [LinearEquiv.finrank_eq (bmsdop_r2_rangeMulLeftEquiv f A),
    LinearEquiv.finrank_eq (LinearEquiv.finTwoArrow (GaloisField 2 f)
      ↥(LinearMap.range (Matrix.mulVecLin A))), Module.finrank_prod]
  exact ⟨_, by ring⟩

private lemma bmsdop_r2_rhoLFun_mem (f : ℕ)
    (g : Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 f)) :
    bmsdop_r2_rhoLFun f g ∈ CFSG.RankThree.OrthogonalInvolutions.omegaGroup
      (Spin.quadPlus 2 (GaloisField 2 f))
      (Spin.nondegenerate_polarBilin_quadPlus 2 (GaloisField 2 f)) := by
  rw [CFSG.RankThree.OrthogonalInvolutions.mem_omegaGroup]
  constructor
  · rw [TauCeti.QuadraticMap.mem_orthogonalGroup_iff]
    intro x
    rw [bmsdop_r2_rhoLFun_apply, ← bmsdop_r2_kappa_det, ← bmsdop_r2_kappa_det,
      LinearEquiv.apply_symm_apply, Matrix.det_mul, Matrix.SpecialLinearGroup.det_coe, one_mul]
  · have hsub : ((bmsdop_r2_rhoLFun f g : (Fin 2 ⊕ Fin 2 → GaloisField 2 f) ≃ₗ[GaloisField 2 f]
        (Fin 2 ⊕ Fin 2 → GaloisField 2 f)) : (Fin 2 ⊕ Fin 2 → GaloisField 2 f) →ₗ[GaloisField 2 f]
          (Fin 2 ⊕ Fin 2 → GaloisField 2 f)) - 1 =
        (bmsdop_r2_kappa f).symm.toLinearMap.comp
          ((LinearMap.mulLeft (GaloisField 2 f)
              ((g : Matrix (Fin 2) (Fin 2) (GaloisField 2 f)) - 1)).comp
            (bmsdop_r2_kappa f).toLinearMap) := by
      apply LinearMap.ext
      intro x
      change bmsdop_r2_rhoLFun f g x - x = (bmsdop_r2_kappa f).symm
        (((g : Matrix (Fin 2) (Fin 2) (GaloisField 2 f)) - 1) * (bmsdop_r2_kappa f) x)
      rw [bmsdop_r2_rhoLFun_apply, Matrix.sub_mul, Matrix.one_mul, map_sub,
        LinearEquiv.symm_apply_apply]
    rw [CFSG.RankThree.OrthogonalInvolutions.commSpace, hsub, LinearMap.range_comp,
      LinearEquiv.finrank_map_eq]
    rw [LinearMap.range_comp, LinearEquiv.range, Submodule.map_top]
    exact bmsdop_r2_finrank_range_mulLeft f
      ((g : Matrix (Fin 2) (Fin 2) (GaloisField 2 f)) - 1)

private noncomputable def bmsdop_r2_rhoL (f : ℕ) :
    Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 f) →*
      ↥(CFSG.RankThree.OrthogonalInvolutions.omegaGroup (Spin.quadPlus 2 (GaloisField 2 f))
        (Spin.nondegenerate_polarBilin_quadPlus 2 (GaloisField 2 f))) :=
  { toFun := fun g => ⟨bmsdop_r2_rhoLFun f g, bmsdop_r2_rhoLFun_mem f g⟩
    map_one' := by
      apply Subtype.ext
      apply LinearEquiv.ext
      intro x
      change bmsdop_r2_rhoLFun f 1 x = x
      simp only [bmsdop_r2_rhoLFun_apply, Matrix.SpecialLinearGroup.coe_one, Matrix.one_mul,
        LinearEquiv.symm_apply_apply]
    map_mul' := by
      intro g h
      apply Subtype.ext
      apply LinearEquiv.ext
      intro x
      change bmsdop_r2_rhoLFun f (g * h) x = bmsdop_r2_rhoLFun f g (bmsdop_r2_rhoLFun f h x)
      simp only [bmsdop_r2_rhoLFun_apply, Matrix.SpecialLinearGroup.coe_mul,
        LinearEquiv.apply_symm_apply, Matrix.mul_assoc] }

private lemma bmsdop_r2_mulRightEquiv_apply (f : ℕ)
    (g : Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 f))
    (X : Matrix (Fin 2) (Fin 2) (GaloisField 2 f)) :
    bmsdop_r2_mulRightEquiv f g X =
      X * ((g⁻¹ : Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 f)) :
        Matrix (Fin 2) (Fin 2) (GaloisField 2 f)) := rfl

private noncomputable def bmsdop_r2_rhoRFun (f : ℕ)
    (g : Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 f)) :
    (Fin 2 ⊕ Fin 2 → GaloisField 2 f) ≃ₗ[GaloisField 2 f]
      (Fin 2 ⊕ Fin 2 → GaloisField 2 f) :=
  (bmsdop_r2_kappa f).trans ((bmsdop_r2_mulRightEquiv f g).trans (bmsdop_r2_kappa f).symm)

private lemma bmsdop_r2_rhoRFun_apply (f : ℕ)
    (g : Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 f))
    (x : Fin 2 ⊕ Fin 2 → GaloisField 2 f) :
    bmsdop_r2_rhoRFun f g x = (bmsdop_r2_kappa f).symm
      ((bmsdop_r2_kappa f) x * ((g⁻¹ : Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 f)) :
        Matrix (Fin 2) (Fin 2) (GaloisField 2 f))) := by
  simp only [bmsdop_r2_rhoRFun, LinearEquiv.trans_apply, bmsdop_r2_mulRightEquiv_apply]

private lemma bmsdop_r2_row_mul (f : ℕ) (X B : Matrix (Fin 2) (Fin 2) (GaloisField 2 f))
    (i : Fin 2) :
    Matrix.row (X * B) i = B.transpose.mulVec (Matrix.row X i) := by
  ext j
  simp only [Matrix.row_apply, Matrix.mul_apply, Matrix.mulVec_apply, Matrix.transpose_apply,
    dotProduct, mul_comm]

private noncomputable def bmsdop_r2_rangeMulRightEquiv (f : ℕ)
    (B : Matrix (Fin 2) (Fin 2) (GaloisField 2 f)) :
    ↥(LinearMap.range (LinearMap.mulRight (GaloisField 2 f) B)) ≃ₗ[GaloisField 2 f]
      (Fin 2 → ↥(LinearMap.range (Matrix.mulVecLin B.transpose))) where
  toFun M := fun i => ⟨Matrix.row (M : Matrix (Fin 2) (Fin 2) (GaloisField 2 f)) i, by
    obtain ⟨Y, hY⟩ := LinearMap.mem_range.mp M.2
    refine ⟨Matrix.row Y i, ?_⟩
    rw [Matrix.mulVecLin_apply, ← bmsdop_r2_row_mul f Y B i]
    exact congrArg (fun Z => Matrix.row Z i) hY⟩
  invFun g := ⟨Matrix.of (fun i j => (g i : Fin 2 → GaloisField 2 f) j), by
    choose Y hY using fun i => LinearMap.mem_range.mp (g i).2
    refine ⟨Matrix.of (fun a b => Y a b), ?_⟩
    ext i j
    simp only [LinearMap.mulRight_apply, Matrix.mul_apply, Matrix.of_apply]
    rw [← hY i]
    simp only [Matrix.mulVecLin_apply, Matrix.mulVec_apply, dotProduct, Matrix.row,
      Matrix.transpose_apply, mul_comm]⟩
  left_inv := by intro M; ext i j; rfl
  right_inv := by intro g; ext i j; rfl
  map_add' := by intro M N; ext i j; rfl
  map_smul' := by intro c M; ext i j; rfl

private lemma bmsdop_r2_finrank_range_mulRight (f : ℕ)
    (B : Matrix (Fin 2) (Fin 2) (GaloisField 2 f)) :
    Even (Module.finrank (GaloisField 2 f)
      ↥(LinearMap.range (LinearMap.mulRight (GaloisField 2 f) B))) := by
  rw [LinearEquiv.finrank_eq (bmsdop_r2_rangeMulRightEquiv f B),
    LinearEquiv.finrank_eq (LinearEquiv.finTwoArrow (GaloisField 2 f)
      ↥(LinearMap.range (Matrix.mulVecLin B.transpose))), Module.finrank_prod]
  exact ⟨_, by ring⟩

private lemma bmsdop_r2_rhoRFun_mem (f : ℕ)
    (g : Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 f)) :
    bmsdop_r2_rhoRFun f g ∈ CFSG.RankThree.OrthogonalInvolutions.omegaGroup
      (Spin.quadPlus 2 (GaloisField 2 f))
      (Spin.nondegenerate_polarBilin_quadPlus 2 (GaloisField 2 f)) := by
  rw [CFSG.RankThree.OrthogonalInvolutions.mem_omegaGroup]
  constructor
  · rw [TauCeti.QuadraticMap.mem_orthogonalGroup_iff]
    intro x
    rw [bmsdop_r2_rhoRFun_apply, ← bmsdop_r2_kappa_det, ← bmsdop_r2_kappa_det,
      LinearEquiv.apply_symm_apply, Matrix.det_mul, Matrix.SpecialLinearGroup.det_coe, mul_one]
  · have hsub : ((bmsdop_r2_rhoRFun f g : (Fin 2 ⊕ Fin 2 → GaloisField 2 f) ≃ₗ[GaloisField 2 f]
        (Fin 2 ⊕ Fin 2 → GaloisField 2 f)) : (Fin 2 ⊕ Fin 2 → GaloisField 2 f) →ₗ[GaloisField 2 f]
          (Fin 2 ⊕ Fin 2 → GaloisField 2 f)) - 1 =
        (bmsdop_r2_kappa f).symm.toLinearMap.comp
          ((LinearMap.mulRight (GaloisField 2 f)
              (((g⁻¹ : Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 f)) :
                Matrix (Fin 2) (Fin 2) (GaloisField 2 f)) - 1)).comp
            (bmsdop_r2_kappa f).toLinearMap) := by
      apply LinearMap.ext
      intro x
      change bmsdop_r2_rhoRFun f g x - x = (bmsdop_r2_kappa f).symm
        ((bmsdop_r2_kappa f) x *
          (((g⁻¹ : Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 f)) :
            Matrix (Fin 2) (Fin 2) (GaloisField 2 f)) - 1))
      rw [bmsdop_r2_rhoRFun_apply, Matrix.mul_sub, Matrix.mul_one, map_sub,
        LinearEquiv.symm_apply_apply]
    rw [CFSG.RankThree.OrthogonalInvolutions.commSpace, hsub, LinearMap.range_comp,
      LinearEquiv.finrank_map_eq]
    rw [LinearMap.range_comp, LinearEquiv.range, Submodule.map_top]
    exact bmsdop_r2_finrank_range_mulRight f
      (((g⁻¹ : Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 f)) :
        Matrix (Fin 2) (Fin 2) (GaloisField 2 f)) - 1)

private noncomputable def bmsdop_r2_rhoR (f : ℕ) :
    Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 f) →*
      ↥(CFSG.RankThree.OrthogonalInvolutions.omegaGroup (Spin.quadPlus 2 (GaloisField 2 f))
        (Spin.nondegenerate_polarBilin_quadPlus 2 (GaloisField 2 f))) :=
  { toFun := fun g => ⟨bmsdop_r2_rhoRFun f g, bmsdop_r2_rhoRFun_mem f g⟩
    map_one' := by
      apply Subtype.ext
      apply LinearEquiv.ext
      intro x
      change bmsdop_r2_rhoRFun f 1 x = x
      simp only [bmsdop_r2_rhoRFun_apply, Matrix.SpecialLinearGroup.coe_one, inv_one,
        Matrix.mul_one, LinearEquiv.symm_apply_apply]
    map_mul' := by
      intro g h
      apply Subtype.ext
      apply LinearEquiv.ext
      intro x
      change bmsdop_r2_rhoRFun f (g * h) x = bmsdop_r2_rhoRFun f g (bmsdop_r2_rhoRFun f h x)
      simp only [bmsdop_r2_rhoRFun_apply, Matrix.SpecialLinearGroup.coe_mul,
        Matrix.SpecialLinearGroup.coe_inv, mul_inv_rev, Matrix.mul_assoc,
        LinearEquiv.apply_symm_apply] }

private lemma bmsdop_r2_rhoL_injective (f : ℕ) :
    Function.Injective (bmsdop_r2_rhoL f) := by
  intro a b hab
  have h1 : bmsdop_r2_rhoLFun f a = bmsdop_r2_rhoLFun f b :=
    congrArg (fun x : ↥(CFSG.RankThree.OrthogonalInvolutions.omegaGroup
      (Spin.quadPlus 2 (GaloisField 2 f))
      (Spin.nondegenerate_polarBilin_quadPlus 2 (GaloisField 2 f))) =>
        (x : (Fin 2 ⊕ Fin 2 → GaloisField 2 f) ≃ₗ[GaloisField 2 f]
          (Fin 2 ⊕ Fin 2 → GaloisField 2 f))) hab
  have h2 := congrArg (fun e : (Fin 2 ⊕ Fin 2 → GaloisField 2 f) ≃ₗ[GaloisField 2 f]
      (Fin 2 ⊕ Fin 2 → GaloisField 2 f) =>
        e ((bmsdop_r2_kappa f).symm (1 : Matrix (Fin 2) (Fin 2) (GaloisField 2 f)))) h1
  simp only [bmsdop_r2_rhoLFun_apply, LinearEquiv.apply_symm_apply, Matrix.mul_one] at h2
  exact Subtype.ext ((bmsdop_r2_kappa f).symm.injective h2)

private lemma bmsdop_r2_rhoR_injective (f : ℕ) :
    Function.Injective (bmsdop_r2_rhoR f) := by
  intro a b hab
  have h1 : bmsdop_r2_rhoRFun f a = bmsdop_r2_rhoRFun f b :=
    congrArg (fun x : ↥(CFSG.RankThree.OrthogonalInvolutions.omegaGroup
      (Spin.quadPlus 2 (GaloisField 2 f))
      (Spin.nondegenerate_polarBilin_quadPlus 2 (GaloisField 2 f))) =>
        (x : (Fin 2 ⊕ Fin 2 → GaloisField 2 f) ≃ₗ[GaloisField 2 f]
          (Fin 2 ⊕ Fin 2 → GaloisField 2 f))) hab
  have h2 := congrArg (fun e : (Fin 2 ⊕ Fin 2 → GaloisField 2 f) ≃ₗ[GaloisField 2 f]
      (Fin 2 ⊕ Fin 2 → GaloisField 2 f) =>
        e ((bmsdop_r2_kappa f).symm (1 : Matrix (Fin 2) (Fin 2) (GaloisField 2 f)))) h1
  simp only [bmsdop_r2_rhoRFun_apply, LinearEquiv.apply_symm_apply] at h2
  have h2' : (bmsdop_r2_kappa f).symm (↑(a⁻¹)) =
      (bmsdop_r2_kappa f).symm (↑(b⁻¹)) := by
    simpa only [Matrix.one_mul] using h2
  have h3 : (a⁻¹ : Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 f)) = b⁻¹ :=
    Subtype.ext ((bmsdop_r2_kappa f).symm.injective h2')
  exact inv_injective h3

private lemma bmsdop_r2_rhoL_commute_rhoR (f : ℕ) :
    ∀ x ∈ (bmsdop_r2_rhoL f).range, ∀ y ∈ (bmsdop_r2_rhoR f).range, x * y = y * x := by
  rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩
  apply Subtype.ext
  apply LinearEquiv.ext
  intro x
  change bmsdop_r2_rhoLFun f a (bmsdop_r2_rhoRFun f b x) =
    bmsdop_r2_rhoRFun f b (bmsdop_r2_rhoLFun f a x)
  rw [bmsdop_r2_rhoLFun_apply, bmsdop_r2_rhoRFun_apply, bmsdop_r2_rhoRFun_apply,
    bmsdop_r2_rhoLFun_apply, LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]
  rw [Matrix.mul_assoc]

private lemma bmsdop_r2_swEquiv_eq (f : ℕ)
    (h k : Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 f)) :
    CFSG.RankThree.GF2n.Smith81.FourPlus.swEquiv (bmsdop_r2_kappa f) h k =
      bmsdop_r2_rhoLFun f h *
        bmsdop_r2_rhoRFun f ((Matrix.SpecialLinearGroup.transpose k)⁻¹) := by
  ext x
  simp only [CFSG.RankThree.GF2n.Smith81.FourPlus.swEquiv,
    CFSG.RankThree.GF2n.Smith81.D2.pairEquiv_apply, LinearEquiv.trans_apply,
    LinearEquiv.mul_apply, bmsdop_r2_rhoLFun_apply, bmsdop_r2_rhoRFun_apply,
    LinearEquiv.apply_symm_apply, Matrix.SpecialLinearGroup.coe_inv,
    Matrix.SpecialLinearGroup.coe_transpose, inv_inv, Matrix.mul_assoc]

private lemma bmsdop_r2_sl_eq_one_of_central (f : ℕ)
    (a : Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 f))
    (h : ∀ M : Matrix (Fin 2) (Fin 2) (GaloisField 2 f),
      (a : Matrix (Fin 2) (Fin 2) (GaloisField 2 f)) * M =
        M * (a : Matrix (Fin 2) (Fin 2) (GaloisField 2 f))) :
    a = 1 := by
  have h10 : (a : Matrix (Fin 2) (Fin 2) (GaloisField 2 f)) 1 0 = 0 := by
    have hh := congrFun (congrFun (h !![0, 1; 0, 0]) 1) 1
    simpa [Matrix.mul_apply, Fin.sum_univ_two] using hh
  have h01 : (a : Matrix (Fin 2) (Fin 2) (GaloisField 2 f)) 0 1 = 0 := by
    have hh := congrFun (congrFun (h !![0, 0; 1, 0]) 0) 0
    simpa [Matrix.mul_apply, Fin.sum_univ_two] using hh
  have hdiag : (a : Matrix (Fin 2) (Fin 2) (GaloisField 2 f)) 0 0 =
      (a : Matrix (Fin 2) (Fin 2) (GaloisField 2 f)) 1 1 := by
    have hh := congrFun (congrFun (h !![0, 1; 0, 0]) 0) 1
    simpa [Matrix.mul_apply, Fin.sum_univ_two] using hh
  have hdet : (a : Matrix (Fin 2) (Fin 2) (GaloisField 2 f)).det = 1 :=
    Matrix.SpecialLinearGroup.det_coe a
  rw [Matrix.det_fin_two, h10, h01, mul_zero, sub_zero, ← hdiag] at hdet
  have ha00 : (a : Matrix (Fin 2) (Fin 2) (GaloisField 2 f)) 0 0 = 1 := by
    rcases mul_self_eq_one_iff.mp hdet with hh | hh
    · exact hh
    · rw [hh, CharTwo.neg_eq]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [h10, h01, hdiag.symm, ha00]

private lemma bmsdop_r2_split (f : ℕ)
    (hcard : Nat.card (GaloisField 2 f) ≠ 2) :
    (bmsdop_r2_rhoL f).range ⊔ (bmsdop_r2_rhoR f).range = ⊤ ∧
    CFSG.IsQuasisimple ↥((bmsdop_r2_rhoL f).range) ∧
    CFSG.IsQuasisimple ↥((bmsdop_r2_rhoR f).range) ∧
    (∀ x ∈ (bmsdop_r2_rhoL f).range, ∀ y ∈ (bmsdop_r2_rhoR f).range, x * y = y * x) ∧
    (bmsdop_r2_rhoL f).range ⊓ (bmsdop_r2_rhoR f).range = ⊥ ∧
    Function.Injective (bmsdop_r2_rhoL f) ∧ Function.Injective (bmsdop_r2_rhoR f) := by
  have h4 : 4 ≤ Nat.card (GaloisField 2 f) := by
    have hf0 : f ≠ 0 := by
      intro hf
      rw [hf] at hcard
      exact hcard CFSG.RankThree.PartTwo.Sec21.natCard_galoisField_two_zero
    have hf1 : f ≠ 1 := by
      intro hf
      rw [hf, GaloisField.card 2 1 (by norm_num)] at hcard
      exact hcard (by norm_num)
    rw [GaloisField.card 2 f hf0]
    have h2 : 2 ≤ f := by omega
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) h2
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [Subgroup.eq_top_iff']
    intro o
    rw [GL83.CompFam.mem_sup_of_commute (bmsdop_r2_rhoL_commute_rhoR f)]
    have ho : (o : (Fin 2 ⊕ Fin 2 → GaloisField 2 f) ≃ₗ[GaloisField 2 f]
        (Fin 2 ⊕ Fin 2 → GaloisField 2 f)) ∈
        CFSG.RankThree.OrthogonalInvolutions.omegaGroup
          (Spin.quadPlus 2 (GaloisField 2 f))
          (Spin.nondegenerate_polarBilin_quadPlus 2 (GaloisField 2 f)) := o.2
    rw [CFSG.RankThree.GF2n.Smith81.FourPlus.mem_omegaGroup_iff_exists_swEquiv
      (Spin.nondegenerate_polarBilin_quadPlus 2 (GaloisField 2 f))
      (bmsdop_r2_kappa_det f) h4
      (CFSG.GroupTheory.WeirSylow.isPlusType_quadPlus (GaloisField 2 f) 2)
      (by norm_num)] at ho
    obtain ⟨h, k, hk⟩ := ho
    refine ⟨⟨bmsdop_r2_rhoLFun f h, bmsdop_r2_rhoLFun_mem f h⟩, ⟨h, rfl⟩,
      ⟨bmsdop_r2_rhoRFun f ((Matrix.SpecialLinearGroup.transpose k)⁻¹),
        bmsdop_r2_rhoRFun_mem f ((Matrix.SpecialLinearGroup.transpose k)⁻¹)⟩,
      ⟨_, rfl⟩, ?_⟩
    apply Subtype.ext
    rw [hk, bmsdop_r2_swEquiv_eq f h k, Subgroup.coe_mul]
  · exact CFSG.LocalCores.isQuasisimple_of_mulEquiv
      (MonoidHom.ofInjective (bmsdop_r2_rhoL_injective f))
      (CFSG.SeitzReduction.LinearPilot.isQuasisimple_specialLinearGroup_of_le (m := 2)
        (by norm_num) (Or.inr h4))
  · exact CFSG.LocalCores.isQuasisimple_of_mulEquiv
      (MonoidHom.ofInjective (bmsdop_r2_rhoR_injective f))
      (CFSG.SeitzReduction.LinearPilot.isQuasisimple_specialLinearGroup_of_le (m := 2)
        (by norm_num) (Or.inr h4))
  · exact bmsdop_r2_rhoL_commute_rhoR f
  · rw [Subgroup.eq_bot_iff_forall]
    intro x hx
    obtain ⟨hxL, hxR⟩ := Subgroup.mem_inf.mp hx
    obtain ⟨a, rfl⟩ := hxL
    obtain ⟨b, hb⟩ := hxR
    have h1 : bmsdop_r2_rhoLFun f a = bmsdop_r2_rhoRFun f b := by
      have hh := congrArg (fun y : ↥(CFSG.RankThree.OrthogonalInvolutions.omegaGroup
        (Spin.quadPlus 2 (GaloisField 2 f))
        (Spin.nondegenerate_polarBilin_quadPlus 2 (GaloisField 2 f))) =>
          (y : (Fin 2 ⊕ Fin 2 → GaloisField 2 f) ≃ₗ[GaloisField 2 f]
            (Fin 2 ⊕ Fin 2 → GaloisField 2 f))) hb
      exact hh.symm
    have hab : (a : Matrix (Fin 2) (Fin 2) (GaloisField 2 f)) = ↑(b⁻¹) := by
      have h2 := congrArg (fun e : (Fin 2 ⊕ Fin 2 → GaloisField 2 f) ≃ₗ[GaloisField 2 f]
          (Fin 2 ⊕ Fin 2 → GaloisField 2 f) =>
            e ((bmsdop_r2_kappa f).symm (1 : Matrix (Fin 2) (Fin 2) (GaloisField 2 f)))) h1
      simp only [bmsdop_r2_rhoLFun_apply, bmsdop_r2_rhoRFun_apply,
        LinearEquiv.apply_symm_apply] at h2
      have h2' : (bmsdop_r2_kappa f).symm (a : Matrix (Fin 2) (Fin 2) (GaloisField 2 f)) =
          (bmsdop_r2_kappa f).symm (↑(b⁻¹)) := by
        simpa only [Matrix.mul_one, Matrix.one_mul] using h2
      exact (bmsdop_r2_kappa f).symm.injective h2'
    have hcentral : ∀ M : Matrix (Fin 2) (Fin 2) (GaloisField 2 f),
        (a : Matrix (Fin 2) (Fin 2) (GaloisField 2 f)) * M =
          M * (a : Matrix (Fin 2) (Fin 2) (GaloisField 2 f)) := by
      intro M
      obtain ⟨y, hy⟩ := (bmsdop_r2_kappa f).surjective M
      have h2 := congrArg (fun e : (Fin 2 ⊕ Fin 2 → GaloisField 2 f) ≃ₗ[GaloisField 2 f]
          (Fin 2 ⊕ Fin 2 → GaloisField 2 f) => e y) h1
      simp only [bmsdop_r2_rhoLFun_apply, bmsdop_r2_rhoRFun_apply,
        LinearEquiv.apply_symm_apply] at h2
      have h2' := (bmsdop_r2_kappa f).symm.injective h2
      rw [← hab, hy] at h2'
      exact h2'
    rw [bmsdop_r2_sl_eq_one_of_central f a hcentral]
    exact map_one (bmsdop_r2_rhoL f)
  · exact bmsdop_r2_rhoL_injective f
  · exact bmsdop_r2_rhoR_injective f

private lemma bmsdop_r2_component (k f : ℕ)
    (S : Set (GL (Fin (k + 3) ⊕ Fin (k + 3)) (GaloisField 2 f)))
    {e : Matrix (Fin (k + 3) ⊕ Fin (k + 3)) (Fin (k + 3) ⊕ Fin (k + 3)) (GaloisField 2 f)}
    {J' : Subgroup ↥(spinGroup (bmsdop_Q k f))}
    (hJe : IsComponentOf J' ⁅bmsdop_Ge k f S e, bmsdop_Ge k f S e⁆)
    (r : ↥(CFSG.RankThree.OrthogonalInvolutions.omegaGroup (Spin.quadPlus 2 (GaloisField 2 f))
          (Spin.nondegenerate_polarBilin_quadPlus 2 (GaloisField 2 f))) →*
        ↥(spinGroup (bmsdop_Q k f)))
    (hr : Function.Injective r ∧ r.range = bmsdop_Ge k f S e)
    (T₁ T₂ : Subgroup ↥(CFSG.RankThree.OrthogonalInvolutions.omegaGroup
        (Spin.quadPlus 2 (GaloisField 2 f))
        (Spin.nondegenerate_polarBilin_quadPlus 2 (GaloisField 2 f))))
    (hOmega : T₁ ⊔ T₂ = ⊤)
    (hq₁ : CFSG.IsQuasisimple ↥T₁) (hq₂ : CFSG.IsQuasisimple ↥T₂)
    (hcomm : ∀ x ∈ T₁, ∀ y ∈ T₂, x * y = y * x) :
    J' = Subgroup.map r T₁ ∨ J' = Subgroup.map r T₂ := by
  classical
  have hJ'le : J' ≤ r.range := by
    refine le_trans hJe.1 ?_
    rw [← hr.2]
    calc ⁅r.range, r.range⁆ = Subgroup.map r
          ⁅(⊤ : Subgroup ↥(CFSG.RankThree.OrthogonalInvolutions.omegaGroup
            (Spin.quadPlus 2 (GaloisField 2 f))
            (Spin.nondegenerate_polarBilin_quadPlus 2 (GaloisField 2 f)))), ⊤⁆ := by
          rw [Subgroup.map_commutator, Subgroup.map_top]
      _ ≤ Subgroup.map r ⊤ := Subgroup.map_mono le_top
      _ = r.range := Subgroup.map_top r
  have hPmap : (J'.comap r).map r = J' := by
    rw [Subgroup.map_comap_eq, inf_eq_right.mpr hJ'le]
  have hcomap : (⁅bmsdop_Ge k f S e, bmsdop_Ge k f S e⁆).comap r =
      ⁅(⊤ : Subgroup ↥(CFSG.RankThree.OrthogonalInvolutions.omegaGroup
        (Spin.quadPlus 2 (GaloisField 2 f))
        (Spin.nondegenerate_polarBilin_quadPlus 2 (GaloisField 2 f)))), ⊤⁆ := by
    have hmap : Subgroup.map r ⁅(⊤ : Subgroup ↥(CFSG.RankThree.OrthogonalInvolutions.omegaGroup
          (Spin.quadPlus 2 (GaloisField 2 f))
          (Spin.nondegenerate_polarBilin_quadPlus 2 (GaloisField 2 f)))), ⊤⁆ =
        ⁅bmsdop_Ge k f S e, bmsdop_Ge k f S e⁆ := by
      rw [Subgroup.map_commutator, Subgroup.map_top, hr.2]
    rw [← hmap, Subgroup.comap_map_eq_self_of_injective hr.1]
  have hperfect : ⁅(⊤ : Subgroup ↥(CFSG.RankThree.OrthogonalInvolutions.omegaGroup
      (Spin.quadPlus 2 (GaloisField 2 f))
      (Spin.nondegenerate_polarBilin_quadPlus 2 (GaloisField 2 f)))),
      (⊤ : Subgroup ↥(CFSG.RankThree.OrthogonalInvolutions.omegaGroup
        (Spin.quadPlus 2 (GaloisField 2 f))
        (Spin.nondegenerate_polarBilin_quadPlus 2 (GaloisField 2 f))))⁆ =
      (⊤ : Subgroup ↥(CFSG.RankThree.OrthogonalInvolutions.omegaGroup
        (Spin.quadPlus 2 (GaloisField 2 f))
        (Spin.nondegenerate_polarBilin_quadPlus 2 (GaloisField 2 f)))) := by
    apply le_antisymm le_top
    refine le_trans (le_of_eq hOmega.symm) ?_
    apply sup_le
    · have hperf₁ : T₁ = ⁅T₁, T₁⁆ := by
        have hh : Subgroup.map T₁.subtype (commutator ↥T₁) = T₁ := by
          rw [hq₁.1.commutator_eq_top, ← MonoidHom.range_eq_map, Subgroup.range_subtype]
        rw [show commutator ↥T₁ = ⁅(⊤ : Subgroup ↥T₁), (⊤ : Subgroup ↥T₁)⁆ from rfl,
          Subgroup.map_commutator, Subgroup.map_top, Subgroup.range_subtype] at hh
        exact hh.symm
      rw [hperf₁]
      exact Subgroup.commutator_mono le_top le_top
    · have hperf₂ : T₂ = ⁅T₂, T₂⁆ := by
        have hh : Subgroup.map T₂.subtype (commutator ↥T₂) = T₂ := by
          rw [hq₂.1.commutator_eq_top, ← MonoidHom.range_eq_map, Subgroup.range_subtype]
        rw [show commutator ↥T₂ = ⁅(⊤ : Subgroup ↥T₂), (⊤ : Subgroup ↥T₂)⁆ from rfl,
          Subgroup.map_commutator, Subgroup.map_top, Subgroup.range_subtype] at hh
        exact hh.symm
      rw [hperf₂]
      exact Subgroup.commutator_mono le_top le_top
  let φ : ↥(J'.comap r) →* ↥J' :=
    { toFun := fun x => ⟨r x.1, Subgroup.mem_comap.mp x.2⟩
      map_one' := Subtype.ext (map_one r)
      map_mul' := fun x y => Subtype.ext (map_mul r x.1 y.1) }
  have he : ↥(J'.comap r) ≃* ↥J' :=
    MulEquiv.ofBijective φ
      ⟨fun x y hxy => Subtype.ext (hr.1 (congrArg Subtype.val hxy)), fun y => by
        obtain ⟨x, -, hx⟩ := Subgroup.mem_map.mp (show (y : ↥(spinGroup (bmsdop_Q k f))) ∈
            Subgroup.map r ⊤ by rw [Subgroup.map_top]; exact hJ'le y.2)
        exact ⟨⟨x, by show r x ∈ J'; rw [hx]; exact y.2⟩, Subtype.ext hx⟩⟩
  have hP : CFSG.Open.IsQuasisimple ↥(J'.comap r) :=
    CFSG.ComponentClassification.Components.quasisimple_of_equiv he hJe.2.2
  have hsn : CFSG.Open.IsSubnormal (J'.comap r) ⊤ := by
    have h1 : IsSubnormal (J'.comap r) ((⁅bmsdop_Ge k f S e, bmsdop_Ge k f S e⁆).comap r) :=
      IsSubnormal.comap r hJe.2.1
    rw [hcomap, hperfect] at h1
    exact isSubnormal_iff_open.mp h1
  have h₁ : CFSG.Open.IsQuasisimple ↥T₁ := ⟨hq₁.1.commutator_eq_top, hq₁.2.1⟩
  have h₂ : CFSG.Open.IsQuasisimple ↥T₂ := ⟨hq₂.1.commutator_eq_top, hq₂.2.1⟩
  rcases CFSG.LocalAnalysis.UniquenessCase.UC22.uc22p20g_eq_of_components hOmega hcomm h₁ h₂ hP hsn
    with h | h
  · left
    rw [← hPmap, h]
  · right
    rw [← hPmap, h]

private lemma bmsdop_r2_frame_orth (f : ℕ) :
    ((Spin.quadPlus 2 (GaloisField 2 f)) (bmsdop_r2_e11 f) = 0 ∧
      (Spin.quadPlus 2 (GaloisField 2 f)) (bmsdop_r2_e12 f) = 0 ∧
      (Spin.quadPlus 2 (GaloisField 2 f)) (bmsdop_r2_e22 f) = 0 ∧
      (Spin.quadPlus 2 (GaloisField 2 f)) (bmsdop_r2_e21 f) = 0) ∧
    QuadraticMap.polar (Spin.quadPlus 2 (GaloisField 2 f))
        (bmsdop_r2_e11 f) (bmsdop_r2_e22 f) = 1 ∧
    QuadraticMap.polar (Spin.quadPlus 2 (GaloisField 2 f))
        (bmsdop_r2_e12 f) (bmsdop_r2_e21 f) = 1 ∧
    (QuadraticMap.polar (Spin.quadPlus 2 (GaloisField 2 f))
        (bmsdop_r2_e11 f) (bmsdop_r2_e12 f) = 0 ∧
      QuadraticMap.polar (Spin.quadPlus 2 (GaloisField 2 f))
        (bmsdop_r2_e22 f) (bmsdop_r2_e21 f) = 0 ∧
      QuadraticMap.polar (Spin.quadPlus 2 (GaloisField 2 f))
        (bmsdop_r2_e11 f) (bmsdop_r2_e21 f) = 0 ∧
      QuadraticMap.polar (Spin.quadPlus 2 (GaloisField 2 f))
        (bmsdop_r2_e12 f) (bmsdop_r2_e22 f) = 0) := by
  refine ⟨⟨?_, ?_, ?_, ?_⟩, ?_, ?_, ⟨?_, ?_, ?_, ?_⟩⟩
  · rw [← bmsdop_r2_kappa_det, bmsdop_r2_e11, LinearEquiv.apply_symm_apply,
      ]; simp [Matrix.det_fin_two, CharTwo.neg_eq]
  · rw [← bmsdop_r2_kappa_det, bmsdop_r2_e12, LinearEquiv.apply_symm_apply,
      ]; simp [Matrix.det_fin_two, CharTwo.neg_eq]
  · rw [← bmsdop_r2_kappa_det, bmsdop_r2_e22, LinearEquiv.apply_symm_apply,
      ]; simp [Matrix.det_fin_two, CharTwo.neg_eq]
  · rw [← bmsdop_r2_kappa_det, bmsdop_r2_e21, LinearEquiv.apply_symm_apply,
      ]; simp [Matrix.det_fin_two, CharTwo.neg_eq]
  · rw [bmsdop_r2_kappa_polar, bmsdop_r2_e11, bmsdop_r2_e22, LinearEquiv.apply_symm_apply]
    simp [Matrix.det_fin_two, CharTwo.neg_eq]
  · rw [bmsdop_r2_kappa_polar, bmsdop_r2_e12, bmsdop_r2_e21, LinearEquiv.apply_symm_apply]
    simp [Matrix.det_fin_two, CharTwo.neg_eq]
  · rw [bmsdop_r2_kappa_polar, bmsdop_r2_e11, bmsdop_r2_e12, LinearEquiv.apply_symm_apply]
    simp [Matrix.det_fin_two, CharTwo.neg_eq]
  · rw [bmsdop_r2_kappa_polar, bmsdop_r2_e22, bmsdop_r2_e21, LinearEquiv.apply_symm_apply]
    simp [Matrix.det_fin_two, CharTwo.neg_eq]
  · rw [bmsdop_r2_kappa_polar, bmsdop_r2_e11, bmsdop_r2_e21, LinearEquiv.apply_symm_apply]
    simp [Matrix.det_fin_two, CharTwo.neg_eq]
  · rw [bmsdop_r2_kappa_polar, bmsdop_r2_e12, bmsdop_r2_e22, LinearEquiv.apply_symm_apply]
    simp [Matrix.det_fin_two, CharTwo.neg_eq]

private lemma bmsdop_r2_polar_e11 (f : ℕ) (x : Fin 2 ⊕ Fin 2 → GaloisField 2 f) :
    QuadraticMap.polar (Spin.quadPlus 2 (GaloisField 2 f)) x (bmsdop_r2_e11 f) =
      ((bmsdop_r2_kappa f) x) 1 1 := by
  rw [bmsdop_r2_kappa_polar, bmsdop_r2_e11, LinearEquiv.apply_symm_apply]
  simp only [Matrix.det_fin_two, Matrix.of_apply, Matrix.add_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val', Matrix.head_cons, Matrix.empty_val',
    Matrix.cons_val_fin_one, Matrix.zero_apply]
  ring

private lemma bmsdop_r2_polar_e12 (f : ℕ) (x : Fin 2 ⊕ Fin 2 → GaloisField 2 f) :
    QuadraticMap.polar (Spin.quadPlus 2 (GaloisField 2 f)) x (bmsdop_r2_e12 f) =
      -((bmsdop_r2_kappa f) x) 1 0 := by
  rw [bmsdop_r2_kappa_polar, bmsdop_r2_e12, LinearEquiv.apply_symm_apply]
  simp only [Matrix.det_fin_two, Matrix.of_apply, Matrix.add_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val', Matrix.head_cons, Matrix.empty_val',
    Matrix.cons_val_fin_one, Matrix.zero_apply]
  ring

private lemma bmsdop_r2_polar_e22 (f : ℕ) (x : Fin 2 ⊕ Fin 2 → GaloisField 2 f) :
    QuadraticMap.polar (Spin.quadPlus 2 (GaloisField 2 f)) x (bmsdop_r2_e22 f) =
      ((bmsdop_r2_kappa f) x) 0 0 := by
  rw [bmsdop_r2_kappa_polar, bmsdop_r2_e22, LinearEquiv.apply_symm_apply]
  simp only [Matrix.det_fin_two, Matrix.of_apply, Matrix.add_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val', Matrix.head_cons, Matrix.empty_val',
    Matrix.cons_val_fin_one, Matrix.zero_apply]
  ring

private lemma bmsdop_r2_polar_e21 (f : ℕ) (x : Fin 2 ⊕ Fin 2 → GaloisField 2 f) :
    QuadraticMap.polar (Spin.quadPlus 2 (GaloisField 2 f)) x (bmsdop_r2_e21 f) =
      -((bmsdop_r2_kappa f) x) 0 1 := by
  rw [bmsdop_r2_kappa_polar, bmsdop_r2_e21, LinearEquiv.apply_symm_apply]
  simp only [Matrix.det_fin_two, Matrix.of_apply, Matrix.add_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val', Matrix.head_cons, Matrix.empty_val',
    Matrix.cons_val_fin_one, Matrix.zero_apply]
  ring

private lemma bmsdop_r2_eichler_left (f : ℕ) (c : GaloisField 2 f) :
    CFSG.ClassicalGroups.Orthogonal.eichler (Spin.quadPlus 2 (GaloisField 2 f))
        (bmsdop_r2_e11 f) (c • bmsdop_r2_e12 f) =
      bmsdop_r2_rhoLFun f
        (Matrix.SpecialLinearGroup.transvection (i := (0 : Fin 2)) (j := 1) (by decide) c) := by
  apply LinearEquiv.ext
  intro x
  have hQ : (Spin.quadPlus 2 (GaloisField 2 f)) (c • bmsdop_r2_e12 f) = 0 := by
    rw [QuadraticMap.map_smul, (bmsdop_r2_frame_orth f).1.2.1, smul_zero]
  rw [CFSG.ClassicalGroups.Orthogonal.eichler_apply (bmsdop_r2_frame_orth f).1.1 (by
    rw [QuadraticMap.polar_smul_right, (bmsdop_r2_frame_orth f).2.2.2.1, smul_zero])]
  rw [bmsdop_r2_rhoLFun_apply]
  apply (bmsdop_r2_kappa f).injective
  rw [LinearEquiv.apply_symm_apply]
  simp only [map_add, map_sub, map_smul, QuadraticMap.polar_smul_right,
    bmsdop_r2_polar_e11, bmsdop_r2_polar_e12, hQ]
  rw [Matrix.SpecialLinearGroup.transvection_coe]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Matrix.add_apply, Matrix.single_apply, Matrix.one_apply,
      Fin.sum_univ_two, bmsdop_r2_e11, bmsdop_r2_e12, LinearEquiv.apply_symm_apply] <;> ring_nf

private noncomputable def bmsdop_r2_i0 (f : ℕ) :
    Fin (SpecialLinear.rootDatum 1 (GaloisField 2 f)).rank :=
  Fin.cast (show 1 = (SpecialLinear.rootDatum 1 (GaloisField 2 f)).rank from rfl) 0

private lemma bmsdop_r2_root_mem (f : ℕ) :
    Pi.single (bmsdop_r2_i0 f) 1 ∈ (SpecialLinear.rootDatum 1 (GaloisField 2 f)).roots := by
  refine Or.inl ⟨1, bmsdop_r2_i0 f, ?_⟩
  simp

private lemma bmsdop_r2_root_long (f : ℕ)
    (hcard : Nat.card (GaloisField 2 f) ≠ 2) :
    GGLongRoot (SpecialLinear.rootDatum 1 (GaloisField 2 f))
      (Pi.single (bmsdop_r2_i0 f) 1) := by
  refine ⟨1, Pi.single (bmsdop_r2_i0 f) 1, bmsdop_r2_root_mem f, ?_, ?_⟩
  · intro δ hδ
    rcases hδ with ⟨w, i, rfl⟩ | ⟨w, i, hi, rfl⟩
    · rcases CFSG.ClassicalInvolution.ModelFacts.weylAction_single_eq_or_neg
        (SpecialLinear.rootDatum 1 (GaloisField 2 f)).isFiniteType
        (fun i j : Fin (SpecialLinear.rootDatum 1 (GaloisField 2 f)).rank => Fin.ext (by
          have hi : i.val < 1 := i.isLt
          have hj : j.val < 1 := j.isLt
          omega)) i w with h | h
      · rw [h]; simp
      · rw [h]; simp
    · exact absurd hi (Set.notMem_empty i)
  · simp

private lemma bmsdop_r2_eichler_right (f : ℕ) (c : GaloisField 2 f) :
    CFSG.ClassicalGroups.Orthogonal.eichler (Spin.quadPlus 2 (GaloisField 2 f))
        (bmsdop_r2_e22 f) (c • bmsdop_r2_e21 f) =
      bmsdop_r2_rhoLFun f
        (Matrix.SpecialLinearGroup.transvection (i := (1 : Fin 2)) (j := 0) (by decide) c) := by
  apply LinearEquiv.ext
  intro x
  have hQ : (Spin.quadPlus 2 (GaloisField 2 f)) (c • bmsdop_r2_e21 f) = 0 := by
    rw [QuadraticMap.map_smul, (bmsdop_r2_frame_orth f).1.2.2.2, smul_zero]
  rw [CFSG.ClassicalGroups.Orthogonal.eichler_apply (bmsdop_r2_frame_orth f).1.2.2.1 (by
    rw [QuadraticMap.polar_smul_right, (bmsdop_r2_frame_orth f).2.2.2.2.1, smul_zero])]
  rw [bmsdop_r2_rhoLFun_apply]
  apply (bmsdop_r2_kappa f).injective
  rw [LinearEquiv.apply_symm_apply]
  simp only [map_add, map_sub, map_smul, QuadraticMap.polar_smul_right,
    bmsdop_r2_polar_e22, bmsdop_r2_polar_e21, hQ]
  rw [Matrix.SpecialLinearGroup.transvection_coe]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Matrix.add_apply, Matrix.single_apply, Matrix.one_apply,
      Fin.sum_univ_two, bmsdop_r2_e22, bmsdop_r2_e21, LinearEquiv.apply_symm_apply,
      sub_eq_add_neg, CharTwo.neg_eq] <;> ring_nf

private lemma bmsdop_r2_rootGroup_upper (f : ℕ)
    (hcard : Nat.card (GaloisField 2 f) ≠ 2) :
    ((SpecialLinear.rootDatum 1 (GaloisField 2 f)).rootGroup (Pi.single (bmsdop_r2_i0 f) 1)).map
        ((Subgroup.subtype (CFSG.RankThree.OrthogonalInvolutions.omegaGroup (Spin.quadPlus 2
            (GaloisField 2 f))
            (Spin.nondegenerate_polarBilin_quadPlus 2 (GaloisField 2 f)))).comp (bmsdop_r2_rhoL f))
                =
      siegelGroup (Spin.quadPlus 2 (GaloisField 2 f)) (bmsdop_r2_e11 f) (bmsdop_r2_e12 f) := by
  dsimp only [SpecialLinear.rootDatum]
  rw [SpecialLinear.rootGroup_eq 1 (GaloisField 2 f) (i := (0 : Fin 2)) (j := 1)
    (by decide) (by
      funext a
      fin_cases a <;>
        simp [SpecialLinear.toStd, bmsdop_r2_i0, Pi.single_eq_same, Pi.single_eq_of_ne]
        <;> rfl)]
  rw [SpecialLinear.rootSubgroup, ← MonoidHom.range_comp, MonoidHom.range_eq_map,
    ← Subgroup.closure_univ, MonoidHom.map_closure]
  congr 1
  ext x
  constructor
  · rintro ⟨c, -, rfl⟩
    refine ⟨Multiplicative.toAdd c, ?_⟩
    simp only [MonoidHom.comp_apply, Matrix.SpecialLinearGroup.transvectionHom_apply,
      bmsdop_r2_rhoLFun_apply, LinearEquiv.apply_symm_apply]
    exact (bmsdop_r2_eichler_left f (Multiplicative.toAdd c)).symm
  · rintro ⟨c, rfl⟩
    refine ⟨Multiplicative.ofAdd c, trivial, ?_⟩
    simp only [MonoidHom.comp_apply, Matrix.SpecialLinearGroup.transvectionHom_apply,
      bmsdop_r2_rhoLFun_apply, LinearEquiv.apply_symm_apply]
    rw [show Multiplicative.toAdd (Multiplicative.ofAdd c) = c from rfl]
    exact (bmsdop_r2_eichler_left f c).symm

private lemma bmsdop_r2_rootGroup_lower (f : ℕ)
    (hcard : Nat.card (GaloisField 2 f) ≠ 2) :
    ((SpecialLinear.rootDatum 1 (GaloisField 2 f)).rootGroup (-Pi.single (bmsdop_r2_i0 f) 1)).map
        ((Subgroup.subtype (CFSG.RankThree.OrthogonalInvolutions.omegaGroup (Spin.quadPlus 2
            (GaloisField 2 f))
            (Spin.nondegenerate_polarBilin_quadPlus 2 (GaloisField 2 f)))).comp (bmsdop_r2_rhoL f))
                =
      siegelGroup (Spin.quadPlus 2 (GaloisField 2 f)) (bmsdop_r2_e22 f) (bmsdop_r2_e21 f) := by
  dsimp only [SpecialLinear.rootDatum]
  rw [SpecialLinear.rootGroup_eq 1 (GaloisField 2 f) (i := (1 : Fin 2)) (j := 0)
    (by decide) (by
      funext a
      fin_cases a <;>
        simp [SpecialLinear.toStd, bmsdop_r2_i0, Pi.single_eq_same, Pi.single_eq_of_ne]
        <;> rfl)]
  rw [SpecialLinear.rootSubgroup, ← MonoidHom.range_comp, MonoidHom.range_eq_map,
    ← Subgroup.closure_univ, MonoidHom.map_closure]
  congr 1
  ext x
  constructor
  · rintro ⟨c, -, rfl⟩
    refine ⟨Multiplicative.toAdd c, ?_⟩
    simp only [MonoidHom.comp_apply, Matrix.SpecialLinearGroup.transvectionHom_apply,
      bmsdop_r2_rhoLFun_apply, LinearEquiv.apply_symm_apply]
    exact (bmsdop_r2_eichler_right f (Multiplicative.toAdd c)).symm
  · rintro ⟨c, rfl⟩
    refine ⟨Multiplicative.ofAdd c, trivial, ?_⟩
    simp only [MonoidHom.comp_apply, Matrix.SpecialLinearGroup.transvectionHom_apply,
      bmsdop_r2_rhoLFun_apply, LinearEquiv.apply_symm_apply]
    rw [show Multiplicative.toAdd (Multiplicative.ofAdd c) = c from rfl]
    exact (bmsdop_r2_eichler_right f c).symm

private lemma bmsdop_r2_frame_root (f : ℕ)
    (hcard : Nat.card (GaloisField 2 f) ≠ 2) :
    ∃ (β : Fin (SpecialLinear.rootDatum 1 (GaloisField 2 f)).rank → ℤ),
      β ∈ (SpecialLinear.rootDatum 1 (GaloisField 2 f)).roots ∧
      GGLongRoot (SpecialLinear.rootDatum 1 (GaloisField 2 f)) β ∧
      ((SpecialLinear.rootDatum 1 (GaloisField 2 f)).rootGroup β).map
          ((Subgroup.subtype (CFSG.RankThree.OrthogonalInvolutions.omegaGroup
            (Spin.quadPlus 2 (GaloisField 2 f))
            (Spin.nondegenerate_polarBilin_quadPlus 2 (GaloisField 2 f)))).comp
            (bmsdop_r2_rhoL f)) =
        siegelGroup (Spin.quadPlus 2 (GaloisField 2 f)) (bmsdop_r2_e11 f) (bmsdop_r2_e12 f) ∧
      ((SpecialLinear.rootDatum 1 (GaloisField 2 f)).rootGroup (-β)).map
          ((Subgroup.subtype (CFSG.RankThree.OrthogonalInvolutions.omegaGroup
            (Spin.quadPlus 2 (GaloisField 2 f))
            (Spin.nondegenerate_polarBilin_quadPlus 2 (GaloisField 2 f)))).comp
            (bmsdop_r2_rhoL f)) =
        siegelGroup (Spin.quadPlus 2 (GaloisField 2 f)) (bmsdop_r2_e22 f) (bmsdop_r2_e21 f)  :=
  ⟨Pi.single (bmsdop_r2_i0 f) 1, bmsdop_r2_root_mem f, bmsdop_r2_root_long f hcard,
    bmsdop_r2_rootGroup_upper f hcard, bmsdop_r2_rootGroup_lower f hcard⟩

private lemma bmsdop_r2_frame (f : ℕ)
    (hcard : Nat.card (GaloisField 2 f) ≠ 2) :
    ∃ (β : Fin (SpecialLinear.rootDatum 1 (GaloisField 2 f)).rank → ℤ),
      β ∈ (SpecialLinear.rootDatum 1 (GaloisField 2 f)).roots ∧
      GGLongRoot (SpecialLinear.rootDatum 1 (GaloisField 2 f)) β ∧
      ((Spin.quadPlus 2 (GaloisField 2 f)) (bmsdop_r2_e11 f) = 0 ∧
        (Spin.quadPlus 2 (GaloisField 2 f)) (bmsdop_r2_e12 f) = 0 ∧
        (Spin.quadPlus 2 (GaloisField 2 f)) (bmsdop_r2_e22 f) = 0 ∧
        (Spin.quadPlus 2 (GaloisField 2 f)) (bmsdop_r2_e21 f) = 0) ∧
      QuadraticMap.polar (Spin.quadPlus 2 (GaloisField 2 f))
          (bmsdop_r2_e11 f) (bmsdop_r2_e22 f) = 1 ∧
      QuadraticMap.polar (Spin.quadPlus 2 (GaloisField 2 f))
          (bmsdop_r2_e12 f) (bmsdop_r2_e21 f) = 1 ∧
      (QuadraticMap.polar (Spin.quadPlus 2 (GaloisField 2 f))
          (bmsdop_r2_e11 f) (bmsdop_r2_e12 f) = 0 ∧
        QuadraticMap.polar (Spin.quadPlus 2 (GaloisField 2 f))
          (bmsdop_r2_e22 f) (bmsdop_r2_e21 f) = 0 ∧
        QuadraticMap.polar (Spin.quadPlus 2 (GaloisField 2 f))
          (bmsdop_r2_e11 f) (bmsdop_r2_e21 f) = 0 ∧
        QuadraticMap.polar (Spin.quadPlus 2 (GaloisField 2 f))
          (bmsdop_r2_e12 f) (bmsdop_r2_e22 f) = 0) ∧
      ((SpecialLinear.rootDatum 1 (GaloisField 2 f)).rootGroup β).map
          ((Subgroup.subtype (CFSG.RankThree.OrthogonalInvolutions.omegaGroup
            (Spin.quadPlus 2 (GaloisField 2 f))
            (Spin.nondegenerate_polarBilin_quadPlus 2 (GaloisField 2 f)))).comp
            (bmsdop_r2_rhoL f)) =
        siegelGroup (Spin.quadPlus 2 (GaloisField 2 f)) (bmsdop_r2_e11 f) (bmsdop_r2_e12 f) ∧
      ((SpecialLinear.rootDatum 1 (GaloisField 2 f)).rootGroup (-β)).map
          ((Subgroup.subtype (CFSG.RankThree.OrthogonalInvolutions.omegaGroup
            (Spin.quadPlus 2 (GaloisField 2 f))
            (Spin.nondegenerate_polarBilin_quadPlus 2 (GaloisField 2 f)))).comp
            (bmsdop_r2_rhoL f)) =
        siegelGroup (Spin.quadPlus 2 (GaloisField 2 f)) (bmsdop_r2_e22 f) (bmsdop_r2_e21 f) := by
  obtain ⟨β, hβroot, hβlong, hroot₁, hroot₂⟩ := bmsdop_r2_frame_root f hcard
  exact ⟨β, hβroot, hβlong, (bmsdop_r2_frame_orth f).1, (bmsdop_r2_frame_orth f).2.1,
    (bmsdop_r2_frame_orth f).2.2.1, (bmsdop_r2_frame_orth f).2.2.2, hroot₁, hroot₂⟩

private lemma bmsdop_r2_frame_R_orth (f : ℕ) :
    ((Spin.quadPlus 2 (GaloisField 2 f)) (bmsdop_r2_e11 f) = 0 ∧
      (Spin.quadPlus 2 (GaloisField 2 f)) (bmsdop_r2_e21 f) = 0 ∧
      (Spin.quadPlus 2 (GaloisField 2 f)) (bmsdop_r2_e22 f) = 0 ∧
      (Spin.quadPlus 2 (GaloisField 2 f)) (bmsdop_r2_e12 f) = 0) ∧
    QuadraticMap.polar (Spin.quadPlus 2 (GaloisField 2 f))
        (bmsdop_r2_e11 f) (bmsdop_r2_e22 f) = 1 ∧
    QuadraticMap.polar (Spin.quadPlus 2 (GaloisField 2 f))
        (bmsdop_r2_e21 f) (bmsdop_r2_e12 f) = 1 ∧
    (QuadraticMap.polar (Spin.quadPlus 2 (GaloisField 2 f))
        (bmsdop_r2_e11 f) (bmsdop_r2_e21 f) = 0 ∧
      QuadraticMap.polar (Spin.quadPlus 2 (GaloisField 2 f))
        (bmsdop_r2_e22 f) (bmsdop_r2_e12 f) = 0 ∧
      QuadraticMap.polar (Spin.quadPlus 2 (GaloisField 2 f))
        (bmsdop_r2_e11 f) (bmsdop_r2_e12 f) = 0 ∧
      QuadraticMap.polar (Spin.quadPlus 2 (GaloisField 2 f))
        (bmsdop_r2_e21 f) (bmsdop_r2_e22 f) = 0) := by
  obtain ⟨⟨h11, h12, h22, h21⟩, hp1122, hp1221, hp1112, hp2221, hp1121, hp1222⟩ :=
    bmsdop_r2_frame_orth f
  exact ⟨⟨h11, h21, h22, h12⟩, hp1122, by rw [QuadraticMap.polar_comm]; exact hp1221,
    hp1121, by rw [QuadraticMap.polar_comm]; exact hp1222, hp1112,
    by rw [QuadraticMap.polar_comm]; exact hp2221⟩

private lemma bmsdop_r2_eichler_R_a (f : ℕ) (c : GaloisField 2 f) :
    CFSG.ClassicalGroups.Orthogonal.eichler (Spin.quadPlus 2 (GaloisField 2 f))
        (bmsdop_r2_e22 f) (c • bmsdop_r2_e12 f) =
      bmsdop_r2_rhoRFun f
        (Matrix.SpecialLinearGroup.transvection (i := (0 : Fin 2)) (j := 1) (by decide) c) := by
  apply LinearEquiv.ext
  intro x
  have hQ : (Spin.quadPlus 2 (GaloisField 2 f)) (c • bmsdop_r2_e12 f) = 0 := by
    rw [QuadraticMap.map_smul, (bmsdop_r2_frame_orth f).1.2.1, smul_zero]
  rw [CFSG.ClassicalGroups.Orthogonal.eichler_apply (bmsdop_r2_frame_orth f).1.2.2.1 (by
    rw [QuadraticMap.polar_smul_right, QuadraticMap.polar_comm,
      (bmsdop_r2_frame_orth f).2.2.2.2.2.2, smul_zero])]
  rw [bmsdop_r2_rhoRFun_apply]
  apply (bmsdop_r2_kappa f).injective
  rw [LinearEquiv.apply_symm_apply]
  simp only [map_add, map_sub, map_smul, QuadraticMap.polar_smul_right,
    bmsdop_r2_polar_e22, bmsdop_r2_polar_e12, hQ]
  rw [Matrix.SpecialLinearGroup.transvection_inv, CharTwo.neg_eq,
    Matrix.SpecialLinearGroup.transvection_coe]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Matrix.add_apply, Matrix.single_apply, Matrix.one_apply,
      Fin.sum_univ_two, bmsdop_r2_e22, bmsdop_r2_e12, LinearEquiv.apply_symm_apply,
      sub_eq_add_neg, CharTwo.neg_eq] <;> ring_nf

private lemma bmsdop_r2_eichler_R_b (f : ℕ) (c : GaloisField 2 f) :
    CFSG.ClassicalGroups.Orthogonal.eichler (Spin.quadPlus 2 (GaloisField 2 f))
        (bmsdop_r2_e11 f) (c • bmsdop_r2_e21 f) =
      bmsdop_r2_rhoRFun f
        (Matrix.SpecialLinearGroup.transvection (i := (1 : Fin 2)) (j := 0) (by decide) c) := by
  apply LinearEquiv.ext
  intro x
  have hQ : (Spin.quadPlus 2 (GaloisField 2 f)) (c • bmsdop_r2_e21 f) = 0 := by
    rw [QuadraticMap.map_smul, (bmsdop_r2_frame_orth f).1.2.2.2, smul_zero]
  rw [CFSG.ClassicalGroups.Orthogonal.eichler_apply (bmsdop_r2_frame_orth f).1.1 (by
    rw [QuadraticMap.polar_smul_right, (bmsdop_r2_frame_orth f).2.2.2.2.2.1, smul_zero])]
  rw [bmsdop_r2_rhoRFun_apply]
  apply (bmsdop_r2_kappa f).injective
  rw [LinearEquiv.apply_symm_apply]
  simp only [map_add, map_sub, map_smul, QuadraticMap.polar_smul_right,
    bmsdop_r2_polar_e11, bmsdop_r2_polar_e21, hQ]
  rw [Matrix.SpecialLinearGroup.transvection_inv, CharTwo.neg_eq,
    Matrix.SpecialLinearGroup.transvection_coe]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Matrix.add_apply, Matrix.single_apply, Matrix.one_apply,
      Fin.sum_univ_two, bmsdop_r2_e11, bmsdop_r2_e21, LinearEquiv.apply_symm_apply,
      sub_eq_add_neg, CharTwo.neg_eq] <;> ring_nf

private lemma bmsdop_r2_rootGroup_R_upper (f : ℕ)
    (hcard : Nat.card (GaloisField 2 f) ≠ 2) :
    ((SpecialLinear.rootDatum 1 (GaloisField 2 f)).rootGroup (Pi.single (bmsdop_r2_i0 f) 1)).map
        ((Subgroup.subtype (CFSG.RankThree.OrthogonalInvolutions.omegaGroup (Spin.quadPlus 2
            (GaloisField 2 f))
            (Spin.nondegenerate_polarBilin_quadPlus 2 (GaloisField 2 f)))).comp (bmsdop_r2_rhoR f))
                =
      siegelGroup (Spin.quadPlus 2 (GaloisField 2 f)) (bmsdop_r2_e22 f) (bmsdop_r2_e12 f) := by
  dsimp only [SpecialLinear.rootDatum]
  rw [SpecialLinear.rootGroup_eq 1 (GaloisField 2 f) (i := (0 : Fin 2)) (j := 1)
    (by decide) (by
      funext a
      fin_cases a <;>
        simp [SpecialLinear.toStd, bmsdop_r2_i0, Pi.single_eq_same, Pi.single_eq_of_ne]
        <;> rfl)]
  rw [SpecialLinear.rootSubgroup, ← MonoidHom.range_comp, MonoidHom.range_eq_map,
    ← Subgroup.closure_univ, MonoidHom.map_closure]
  congr 1
  ext x
  constructor
  · rintro ⟨c, -, rfl⟩
    refine ⟨Multiplicative.toAdd c, ?_⟩
    simp only [MonoidHom.comp_apply, Matrix.SpecialLinearGroup.transvectionHom_apply,
      bmsdop_r2_rhoRFun_apply, LinearEquiv.apply_symm_apply]
    exact (bmsdop_r2_eichler_R_a f (Multiplicative.toAdd c)).symm
  · rintro ⟨c, rfl⟩
    refine ⟨Multiplicative.ofAdd c, trivial, ?_⟩
    simp only [MonoidHom.comp_apply, Matrix.SpecialLinearGroup.transvectionHom_apply,
      bmsdop_r2_rhoRFun_apply, LinearEquiv.apply_symm_apply]
    rw [show Multiplicative.toAdd (Multiplicative.ofAdd c) = c from rfl]
    exact (bmsdop_r2_eichler_R_a f c).symm

private lemma bmsdop_r2_rootGroup_R_lower (f : ℕ)
    (hcard : Nat.card (GaloisField 2 f) ≠ 2) :
    ((SpecialLinear.rootDatum 1 (GaloisField 2 f)).rootGroup (-Pi.single (bmsdop_r2_i0 f) 1)).map
        ((Subgroup.subtype (CFSG.RankThree.OrthogonalInvolutions.omegaGroup (Spin.quadPlus 2
            (GaloisField 2 f))
            (Spin.nondegenerate_polarBilin_quadPlus 2 (GaloisField 2 f)))).comp (bmsdop_r2_rhoR f))
                =
      siegelGroup (Spin.quadPlus 2 (GaloisField 2 f)) (bmsdop_r2_e11 f) (bmsdop_r2_e21 f) := by
  dsimp only [SpecialLinear.rootDatum]
  rw [SpecialLinear.rootGroup_eq 1 (GaloisField 2 f) (i := (1 : Fin 2)) (j := 0)
    (by decide) (by
      funext a
      fin_cases a <;>
        simp [SpecialLinear.toStd, bmsdop_r2_i0, Pi.single_eq_same, Pi.single_eq_of_ne]
        <;> rfl)]
  rw [SpecialLinear.rootSubgroup, ← MonoidHom.range_comp, MonoidHom.range_eq_map,
    ← Subgroup.closure_univ, MonoidHom.map_closure]
  congr 1
  ext x
  constructor
  · rintro ⟨c, -, rfl⟩
    refine ⟨Multiplicative.toAdd c, ?_⟩
    simp only [MonoidHom.comp_apply, Matrix.SpecialLinearGroup.transvectionHom_apply,
      bmsdop_r2_rhoRFun_apply, LinearEquiv.apply_symm_apply]
    exact (bmsdop_r2_eichler_R_b f (Multiplicative.toAdd c)).symm
  · rintro ⟨c, rfl⟩
    refine ⟨Multiplicative.ofAdd c, trivial, ?_⟩
    simp only [MonoidHom.comp_apply, Matrix.SpecialLinearGroup.transvectionHom_apply,
      bmsdop_r2_rhoRFun_apply, LinearEquiv.apply_symm_apply]
    rw [show Multiplicative.toAdd (Multiplicative.ofAdd c) = c from rfl]
    exact (bmsdop_r2_eichler_R_b f c).symm

private lemma bmsdop_r2_frame_R_root (f : ℕ)
    (hcard : Nat.card (GaloisField 2 f) ≠ 2) :
    ∃ (β : Fin (SpecialLinear.rootDatum 1 (GaloisField 2 f)).rank → ℤ),
      β ∈ (SpecialLinear.rootDatum 1 (GaloisField 2 f)).roots ∧
      GGLongRoot (SpecialLinear.rootDatum 1 (GaloisField 2 f)) β ∧
      ((SpecialLinear.rootDatum 1 (GaloisField 2 f)).rootGroup β).map
          ((Subgroup.subtype (CFSG.RankThree.OrthogonalInvolutions.omegaGroup
            (Spin.quadPlus 2 (GaloisField 2 f))
            (Spin.nondegenerate_polarBilin_quadPlus 2 (GaloisField 2 f)))).comp
            (bmsdop_r2_rhoR f)) =
        siegelGroup (Spin.quadPlus 2 (GaloisField 2 f)) (bmsdop_r2_e22 f) (bmsdop_r2_e12 f) ∧
      ((SpecialLinear.rootDatum 1 (GaloisField 2 f)).rootGroup (-β)).map
          ((Subgroup.subtype (CFSG.RankThree.OrthogonalInvolutions.omegaGroup
            (Spin.quadPlus 2 (GaloisField 2 f))
            (Spin.nondegenerate_polarBilin_quadPlus 2 (GaloisField 2 f)))).comp
            (bmsdop_r2_rhoR f)) =
        siegelGroup (Spin.quadPlus 2 (GaloisField 2 f)) (bmsdop_r2_e11 f) (bmsdop_r2_e21 f) :=
  ⟨Pi.single (bmsdop_r2_i0 f) 1, bmsdop_r2_root_mem f, bmsdop_r2_root_long f hcard,
    bmsdop_r2_rootGroup_R_upper f hcard, bmsdop_r2_rootGroup_R_lower f hcard⟩

private lemma bmsdop_r2_frame_R (f : ℕ)
    (hcard : Nat.card (GaloisField 2 f) ≠ 2) :
    ∃ (β : Fin (SpecialLinear.rootDatum 1 (GaloisField 2 f)).rank → ℤ),
      β ∈ (SpecialLinear.rootDatum 1 (GaloisField 2 f)).roots ∧
      GGLongRoot (SpecialLinear.rootDatum 1 (GaloisField 2 f)) β ∧
      ((Spin.quadPlus 2 (GaloisField 2 f)) (bmsdop_r2_e11 f) = 0 ∧
        (Spin.quadPlus 2 (GaloisField 2 f)) (bmsdop_r2_e21 f) = 0 ∧
        (Spin.quadPlus 2 (GaloisField 2 f)) (bmsdop_r2_e22 f) = 0 ∧
        (Spin.quadPlus 2 (GaloisField 2 f)) (bmsdop_r2_e12 f) = 0) ∧
      QuadraticMap.polar (Spin.quadPlus 2 (GaloisField 2 f))
          (bmsdop_r2_e11 f) (bmsdop_r2_e22 f) = 1 ∧
      QuadraticMap.polar (Spin.quadPlus 2 (GaloisField 2 f))
          (bmsdop_r2_e21 f) (bmsdop_r2_e12 f) = 1 ∧
      (QuadraticMap.polar (Spin.quadPlus 2 (GaloisField 2 f))
          (bmsdop_r2_e11 f) (bmsdop_r2_e21 f) = 0 ∧
        QuadraticMap.polar (Spin.quadPlus 2 (GaloisField 2 f))
          (bmsdop_r2_e22 f) (bmsdop_r2_e12 f) = 0 ∧
        QuadraticMap.polar (Spin.quadPlus 2 (GaloisField 2 f))
          (bmsdop_r2_e11 f) (bmsdop_r2_e12 f) = 0 ∧
        QuadraticMap.polar (Spin.quadPlus 2 (GaloisField 2 f))
          (bmsdop_r2_e21 f) (bmsdop_r2_e22 f) = 0) ∧
      ((SpecialLinear.rootDatum 1 (GaloisField 2 f)).rootGroup β).map
          ((Subgroup.subtype (CFSG.RankThree.OrthogonalInvolutions.omegaGroup
            (Spin.quadPlus 2 (GaloisField 2 f))
            (Spin.nondegenerate_polarBilin_quadPlus 2 (GaloisField 2 f)))).comp
            (bmsdop_r2_rhoR f)) =
        siegelGroup (Spin.quadPlus 2 (GaloisField 2 f)) (bmsdop_r2_e22 f) (bmsdop_r2_e12 f) ∧
      ((SpecialLinear.rootDatum 1 (GaloisField 2 f)).rootGroup (-β)).map
          ((Subgroup.subtype (CFSG.RankThree.OrthogonalInvolutions.omegaGroup
            (Spin.quadPlus 2 (GaloisField 2 f))
            (Spin.nondegenerate_polarBilin_quadPlus 2 (GaloisField 2 f)))).comp
            (bmsdop_r2_rhoR f)) =
        siegelGroup (Spin.quadPlus 2 (GaloisField 2 f)) (bmsdop_r2_e11 f) (bmsdop_r2_e21 f) := by
  obtain ⟨β, hβroot, hβlong, hroot₁, hroot₂⟩ := bmsdop_r2_frame_R_root f hcard
  exact ⟨β, hβroot, hβlong, (bmsdop_r2_frame_R_orth f).1, (bmsdop_r2_frame_R_orth f).2.1,
    (bmsdop_r2_frame_R_orth f).2.2.1, (bmsdop_r2_frame_R_orth f).2.2.2, hroot₁, hroot₂⟩

private def bmsdop_r2_PSLData
    (k f : ℕ)
    (S : Set (GL (Fin (k + 3) ⊕ Fin (k + 3)) (GaloisField 2 f)))
    (e : Matrix (Fin (k + 3) ⊕ Fin (k + 3)) (Fin (k + 3) ⊕ Fin (k + 3)) (GaloisField 2 f))
    (J' : Subgroup ↥(spinGroup (bmsdop_Q k f))) : Prop :=
  ∃ (ι : (ggU .PSL 2 f).K →* ↥(spinGroup (bmsdop_Q k f)))
    (β₀ : Fin (ggU .PSL 2 f).D.rank → ℤ),
    GGLongRoot (ggU .PSL 2 f).D β₀ ∧
    (∀ y, ι y ∈ Subgroup.center ↥(spinGroup (bmsdop_Q k f)) →
      y ∈ Subgroup.center (ggU .PSL 2 f).K) ∧ ι.range = J' ∧
    ∃ a₁ a₂ b₁ b₂ : (Fin (k + 3) ⊕ Fin (k + 3)) → (GaloisField 2 f),
      ((bmsdop_Q k f) a₁ = 0 ∧ (bmsdop_Q k f) a₂ = 0 ∧ (bmsdop_Q k f) b₁ = 0 ∧
        (bmsdop_Q k f) b₂ = 0) ∧
      QuadraticMap.polar (bmsdop_Q k f) a₁ b₁ = 1 ∧
      QuadraticMap.polar (bmsdop_Q k f) a₂ b₂ = 1 ∧
      (QuadraticMap.polar (bmsdop_Q k f) a₁ a₂ = 0 ∧
        QuadraticMap.polar (bmsdop_Q k f) b₁ b₂ = 0 ∧
        QuadraticMap.polar (bmsdop_Q k f) a₁ b₂ = 0 ∧
        QuadraticMap.polar (bmsdop_Q k f) a₂ b₁ = 0) ∧
      (((ggU .PSL 2 f).D.rootGroup β₀).map ι).map (Spin.spinAction (bmsdop_Q k f)) =
        siegelGroup (bmsdop_Q k f) a₁ a₂ ∧
      (((ggU .PSL 2 f).D.rootGroup (-β₀)).map ι).map (Spin.spinAction (bmsdop_Q k f)) =
        siegelGroup (bmsdop_Q k f) b₁ b₂

private def bmsdop_r2_PSLClosureData
    (k f : ℕ)
    (S : Set (GL (Fin (k + 3) ⊕ Fin (k + 3)) (GaloisField 2 f)))
    (e : Matrix (Fin (k + 3) ⊕ Fin (k + 3)) (Fin (k + 3) ⊕ Fin (k + 3)) (GaloisField 2 f))
    (J' : Subgroup ↥(spinGroup (bmsdop_Q k f))) : Prop :=
  ∃ (ι : (ggU .PSL 2 f).K →* ↥(spinGroup (bmsdop_Q k f))),
    (∀ y, ι y ∈ Subgroup.center ↥(spinGroup (bmsdop_Q k f)) →
      y ∈ Subgroup.center (ggU .PSL 2 f).K) ∧ ι.range = J' ∧
    (∀ a₁ a₂ : ((Fin (k + 3) ⊕ Fin (k + 3)) → GaloisField 2 f), a₁ ≠ 0 → a₂ ≠ 0 →
        LinearIndependent (GaloisField 2 f) ![a₁, a₂] → (bmsdop_Q k f) a₁ = 0 →
        (bmsdop_Q k f) a₂ = 0 → QuadraticMap.polar (bmsdop_Q k f) a₁ a₂ = 0 →
        siegelGroup (bmsdop_Q k f) a₁ a₂ ≤ J'.map (Spin.spinAction (bmsdop_Q k f)) →
      ∃ (β : Fin (ggU .PSL 2 f).D.rank → ℤ) (u : (ggU .PSL 2 f).K),
        β ∈ (ggU .PSL 2 f).D.roots ∧ GGLongRoot (ggU .PSL 2 f).D β ∧
        ((((ggU .PSL 2 f).D.rootGroup β).map (MulAut.conj u).toMonoidHom).map ι).map
          (Spin.spinAction (bmsdop_Q k f)) = siegelGroup (bmsdop_Q k f) a₁ a₂)

private lemma bmsdop_r2_model_data_center
    (k f : ℕ)
    (S : Set (GL (Fin (k + 3) ⊕ Fin (k + 3)) (GaloisField 2 f)))
    {e : Matrix (Fin (k + 3) ⊕ Fin (k + 3)) (Fin (k + 3) ⊕ Fin (k + 3)) (GaloisField 2 f)}
    (E : ((Fin 2 ⊕ Fin 2 → GaloisField 2 f) ≃ₗ[GaloisField 2 f]
        (Fin 2 ⊕ Fin 2 → GaloisField 2 f)) →*
        (bmsdop_V k f ≃ₗ[GaloisField 2 f] bmsdop_V k f))
    (r : ↥(CFSG.RankThree.OrthogonalInvolutions.omegaGroup (Spin.quadPlus 2 (GaloisField 2 f))
        (Spin.nondegenerate_polarBilin_quadPlus 2 (GaloisField 2 f))) →* ↥(spinGroup (bmsdop_Q k
            f)))
    (hr : Function.Injective r ∧ r.range = bmsdop_Ge k f S e)
    (ρ : (ggU .PSL 2 f).K →* ↥(CFSG.RankThree.OrthogonalInvolutions.omegaGroup (Spin.quadPlus 2
        (GaloisField 2 f))
        (Spin.nondegenerate_polarBilin_quadPlus 2 (GaloisField 2 f))))
    (hρ : ρ = bmsdop_r2_rhoL f ∨ ρ = bmsdop_r2_rhoR f) :
    ∀ y, (r.comp ρ) y ∈ Subgroup.center ↥(spinGroup (bmsdop_Q k f)) →
      y ∈ Subgroup.center (ggU .PSL 2 f).K := by
  intro y hy
  rw [Subgroup.mem_center_iff] at hy ⊢
  intro k
  have hρinj : Function.Injective ρ := by
    rcases hρ with rfl | rfl
    · exact bmsdop_r2_rhoL_injective f
    · exact bmsdop_r2_rhoR_injective f
  apply hρinj
  have h := hy (r (ρ k))
  simp only [MonoidHom.comp_apply, ← map_mul] at h
  exact hr.1 h

private lemma bmsdop_r2_model_data_L
    (k f : ℕ)
    (S : Set (GL (Fin (k + 3) ⊕ Fin (k + 3)) (GaloisField 2 f)))
    {e : Matrix (Fin (k + 3) ⊕ Fin (k + 3)) (Fin (k + 3) ⊕ Fin (k + 3)) (GaloisField 2 f)}
    {J' : Subgroup ↥(spinGroup (bmsdop_Q k f))}
    (h1 : bmsdop_geom₁ k f S e) (h2 : bmsdop_geom₂ k f S e)
    (hcard : Nat.card (GaloisField 2 f) ≠ 2)
    (θ : (Fin 2 ⊕ Fin 2 → GaloisField 2 f) ≃ₗ[GaloisField 2 f] ↥(bmsdop_W k f e))
    (hθ : ∀ x, (bmsdop_blockForm k f e) (θ x) = (Spin.quadPlus 2 (GaloisField 2 f)) x)
    (E : ((Fin 2 ⊕ Fin 2 → GaloisField 2 f) ≃ₗ[GaloisField 2 f]
        (Fin 2 ⊕ Fin 2 → GaloisField 2 f)) →*
        (bmsdop_V k f ≃ₗ[GaloisField 2 f] bmsdop_V k f))
    (hE : bmsdop_ExtProps k f S e (Spin.quadPlus 2 (GaloisField 2 f))
        (Spin.nondegenerate_polarBilin_quadPlus 2 (GaloisField 2 f)) θ E)
    (r : ↥(CFSG.RankThree.OrthogonalInvolutions.omegaGroup (Spin.quadPlus 2 (GaloisField 2 f))
        (Spin.nondegenerate_polarBilin_quadPlus 2 (GaloisField 2 f))) →* ↥(spinGroup (bmsdop_Q k
            f)))
    (hr : Function.Injective r ∧ r.range = bmsdop_Ge k f S e ∧
      ∀ g, Spin.spinAction (bmsdop_Q k f) (r g) = E g)
    (hJ : J' = Subgroup.map r (bmsdop_r2_rhoL f).range) :
    bmsdop_r2_PSLData k f S e J' := by
  obtain ⟨β, hβroot, hβlong, hQstd, hp₁, hp₂, horth, hroot₁, hroot₂⟩ :=
    bmsdop_r2_frame f hcard
  let ρ : (ggU .PSL 2 f).K →* ↥(CFSG.RankThree.OrthogonalInvolutions.omegaGroup (Spin.quadPlus 2
      (GaloisField 2 f))
        (Spin.nondegenerate_polarBilin_quadPlus 2 (GaloisField 2 f))) := bmsdop_r2_rhoL f
  have hρ : ρ = bmsdop_r2_rhoL f := rfl
  have hQθ : ∀ x, (bmsdop_Q k f) (θ x) = (Spin.quadPlus 2 (GaloisField 2 f)) x := by
    intro x
    rw [show (bmsdop_Q k f) (θ x) = (bmsdop_blockForm k f e) (θ x) from rfl, hθ x]
  have hpolθ : ∀ x y, QuadraticMap.polar (bmsdop_Q k f) (θ x) (θ y) =
      QuadraticMap.polar (Spin.quadPlus 2 (GaloisField 2 f)) x y := by
    intro x y
    rw [QuadraticMap.polar, QuadraticMap.polar, ← Submodule.coe_add, ← map_add, hQθ, hQθ, hQθ]
  have hEr : (Spin.spinAction (bmsdop_Q k f)).comp r = E.comp (Subgroup.subtype
      (CFSG.RankThree.OrthogonalInvolutions.omegaGroup (Spin.quadPlus 2 (GaloisField 2 f))
        (Spin.nondegenerate_polarBilin_quadPlus 2 (GaloisField 2 f)))) :=
    MonoidHom.ext hr.2.2
  refine ⟨r.comp ρ, β, hβlong, ?_, ?_, θ (bmsdop_r2_e11 f), θ (bmsdop_r2_e12 f),
    θ (bmsdop_r2_e22 f), θ (bmsdop_r2_e21 f), ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact bmsdop_r2_model_data_center k f S E r ⟨hr.1, hr.2.1⟩ ρ (Or.inl hρ)
  · rw [MonoidHom.range_comp, hρ]
    exact hJ.symm
  · exact ⟨by rw [hQθ]; exact hQstd.1, by rw [hQθ]; exact hQstd.2.1,
      by rw [hQθ]; exact hQstd.2.2.1, by rw [hQθ]; exact hQstd.2.2.2⟩
  · rw [hpolθ]; exact hp₁
  · rw [hpolθ]; exact hp₂
  · exact ⟨by rw [hpolθ]; exact horth.1, by rw [hpolθ]; exact horth.2.1,
      by rw [hpolθ]; exact horth.2.2.1, by rw [hpolθ]; exact horth.2.2.2⟩
  · show Subgroup.map (Spin.spinAction (bmsdop_Q k f))
        (Subgroup.map (r.comp (bmsdop_r2_rhoL f)) ((SpecialLinear.rootDatum 1 (GaloisField 2
            f)).rootGroup β)) =
        siegelGroup (bmsdop_Q k f) (↑(θ (bmsdop_r2_e11 f)))
          (↑(θ (bmsdop_r2_e12 f)))
    rw [Subgroup.map_map, ← MonoidHom.comp_assoc, hEr, MonoidHom.comp_assoc,
      ← Subgroup.map_map, hroot₁]
    exact bmsdop_ext_siegel k f S h1 h2 (Spin.quadPlus 2 (GaloisField 2 f))
        (Spin.nondegenerate_polarBilin_quadPlus 2 (GaloisField 2 f)) θ hθ E hE
      (bmsdop_r2_e11 f) (bmsdop_r2_e12 f) hQstd.1 horth.1
  · show Subgroup.map (Spin.spinAction (bmsdop_Q k f))
        (Subgroup.map (r.comp (bmsdop_r2_rhoL f)) ((SpecialLinear.rootDatum 1 (GaloisField 2
            f)).rootGroup (-β))) =
        siegelGroup (bmsdop_Q k f) (↑(θ (bmsdop_r2_e22 f)))
          (↑(θ (bmsdop_r2_e21 f)))
    rw [Subgroup.map_map, ← MonoidHom.comp_assoc, hEr, MonoidHom.comp_assoc,
      ← Subgroup.map_map, hroot₂]
    exact bmsdop_ext_siegel k f S h1 h2 (Spin.quadPlus 2 (GaloisField 2 f))
        (Spin.nondegenerate_polarBilin_quadPlus 2 (GaloisField 2 f)) θ hθ E hE
      (bmsdop_r2_e22 f) (bmsdop_r2_e21 f) hQstd.2.2.1 horth.2.1

private lemma bmsdop_r2_model_data_R
    (k f : ℕ)
    (S : Set (GL (Fin (k + 3) ⊕ Fin (k + 3)) (GaloisField 2 f)))
    {e : Matrix (Fin (k + 3) ⊕ Fin (k + 3)) (Fin (k + 3) ⊕ Fin (k + 3)) (GaloisField 2 f)}
    {J' : Subgroup ↥(spinGroup (bmsdop_Q k f))}
    (h1 : bmsdop_geom₁ k f S e) (h2 : bmsdop_geom₂ k f S e)
    (hcard : Nat.card (GaloisField 2 f) ≠ 2)
    (θ : (Fin 2 ⊕ Fin 2 → GaloisField 2 f) ≃ₗ[GaloisField 2 f] ↥(bmsdop_W k f e))
    (hθ : ∀ x, (bmsdop_blockForm k f e) (θ x) = (Spin.quadPlus 2 (GaloisField 2 f)) x)
    (E : ((Fin 2 ⊕ Fin 2 → GaloisField 2 f) ≃ₗ[GaloisField 2 f]
        (Fin 2 ⊕ Fin 2 → GaloisField 2 f)) →*
        (bmsdop_V k f ≃ₗ[GaloisField 2 f] bmsdop_V k f))
    (hE : bmsdop_ExtProps k f S e (Spin.quadPlus 2 (GaloisField 2 f))
        (Spin.nondegenerate_polarBilin_quadPlus 2 (GaloisField 2 f)) θ E)
    (r : ↥(CFSG.RankThree.OrthogonalInvolutions.omegaGroup (Spin.quadPlus 2 (GaloisField 2 f))
        (Spin.nondegenerate_polarBilin_quadPlus 2 (GaloisField 2 f))) →* ↥(spinGroup (bmsdop_Q k
            f)))
    (hr : Function.Injective r ∧ r.range = bmsdop_Ge k f S e ∧
      ∀ g, Spin.spinAction (bmsdop_Q k f) (r g) = E g)
    (hJ : J' = Subgroup.map r (bmsdop_r2_rhoR f).range) :
    bmsdop_r2_PSLData k f S e J' := by
  obtain ⟨β, hβroot, hβlong, hQstd, hp₁, hp₂, horth, hroot₁, hroot₂⟩ :=
    bmsdop_r2_frame_R f hcard
  let ρ : (ggU .PSL 2 f).K →* ↥(CFSG.RankThree.OrthogonalInvolutions.omegaGroup (Spin.quadPlus 2
      (GaloisField 2 f))
        (Spin.nondegenerate_polarBilin_quadPlus 2 (GaloisField 2 f))) := bmsdop_r2_rhoR f
  have hρ : ρ = bmsdop_r2_rhoR f := rfl
  have hQθ : ∀ x, (bmsdop_Q k f) (θ x) = (Spin.quadPlus 2 (GaloisField 2 f)) x := by
    intro x
    rw [show (bmsdop_Q k f) (θ x) = (bmsdop_blockForm k f e) (θ x) from rfl, hθ x]
  have hpolθ : ∀ x y, QuadraticMap.polar (bmsdop_Q k f) (θ x) (θ y) =
      QuadraticMap.polar (Spin.quadPlus 2 (GaloisField 2 f)) x y := by
    intro x y
    rw [QuadraticMap.polar, QuadraticMap.polar, ← Submodule.coe_add, ← map_add, hQθ, hQθ, hQθ]
  have hEr : (Spin.spinAction (bmsdop_Q k f)).comp r = E.comp (Subgroup.subtype
      (CFSG.RankThree.OrthogonalInvolutions.omegaGroup (Spin.quadPlus 2 (GaloisField 2 f))
        (Spin.nondegenerate_polarBilin_quadPlus 2 (GaloisField 2 f)))) :=
    MonoidHom.ext hr.2.2
  refine ⟨r.comp ρ, β, hβlong, ?_, ?_, θ (bmsdop_r2_e22 f), θ (bmsdop_r2_e12 f),
    θ (bmsdop_r2_e11 f), θ (bmsdop_r2_e21 f), ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact bmsdop_r2_model_data_center k f S E r ⟨hr.1, hr.2.1⟩ ρ (Or.inr hρ)
  · rw [MonoidHom.range_comp, hρ]
    exact hJ.symm
  · exact ⟨by rw [hQθ]; exact hQstd.2.2.1, by rw [hQθ]; exact hQstd.2.2.2,
      by rw [hQθ]; exact hQstd.1, by rw [hQθ]; exact hQstd.2.1⟩
  · rw [hpolθ, QuadraticMap.polar_comm]; exact hp₁
  · rw [hpolθ, QuadraticMap.polar_comm]; exact hp₂
  · exact ⟨by rw [hpolθ]; exact horth.2.1, by rw [hpolθ]; exact horth.1,
      by rw [hpolθ, QuadraticMap.polar_comm]; exact horth.2.2.2,
      by rw [hpolθ, QuadraticMap.polar_comm]; exact horth.2.2.1⟩
  · show Subgroup.map (Spin.spinAction (bmsdop_Q k f))
        (Subgroup.map (r.comp (bmsdop_r2_rhoR f)) ((SpecialLinear.rootDatum 1 (GaloisField 2
            f)).rootGroup β)) =
        siegelGroup (bmsdop_Q k f) (↑(θ (bmsdop_r2_e22 f)))
          (↑(θ (bmsdop_r2_e12 f)))
    rw [Subgroup.map_map, ← MonoidHom.comp_assoc, hEr, MonoidHom.comp_assoc,
      ← Subgroup.map_map, hroot₁]
    exact bmsdop_ext_siegel k f S h1 h2 (Spin.quadPlus 2 (GaloisField 2 f))
        (Spin.nondegenerate_polarBilin_quadPlus 2 (GaloisField 2 f)) θ hθ E hE
      (bmsdop_r2_e22 f) (bmsdop_r2_e12 f) hQstd.2.2.1 horth.2.1
  · show Subgroup.map (Spin.spinAction (bmsdop_Q k f))
        (Subgroup.map (r.comp (bmsdop_r2_rhoR f)) ((SpecialLinear.rootDatum 1 (GaloisField 2
            f)).rootGroup (-β))) =
        siegelGroup (bmsdop_Q k f) (↑(θ (bmsdop_r2_e11 f)))
          (↑(θ (bmsdop_r2_e21 f)))
    rw [Subgroup.map_map, ← MonoidHom.comp_assoc, hEr, MonoidHom.comp_assoc,
      ← Subgroup.map_map, hroot₂]
    exact bmsdop_ext_siegel k f S h1 h2 (Spin.quadPlus 2 (GaloisField 2 f))
        (Spin.nondegenerate_polarBilin_quadPlus 2 (GaloisField 2 f)) θ hθ E hE
      (bmsdop_r2_e11 f) (bmsdop_r2_e21 f) hQstd.1 horth.1

private lemma bmsdop_r2_model_data
    (k f : ℕ) (hf : 1 ≤ f)
    (S : Set (GL (Fin (k + 3) ⊕ Fin (k + 3)) (GaloisField 2 f)))
    {e : Matrix (Fin (k + 3) ⊕ Fin (k + 3)) (Fin (k + 3) ⊕ Fin (k + 3)) (GaloisField 2 f)}
    {J' : Subgroup ↥(spinGroup (bmsdop_Q k f))}
    (h1 : bmsdop_geom₁ k f S e) (h2 : bmsdop_geom₂ k f S e)
    (hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s')
    (heA : e ∈ Algebra.adjoin (GaloisField 2 f) (Units.val '' S))
    (hJe : IsComponentOf J' ⁅bmsdop_Ge k f S e, bmsdop_Ge k f S e⁆)
    (θ : (Fin 2 ⊕ Fin 2 → GaloisField 2 f) ≃ₗ[GaloisField 2 f] ↥(bmsdop_W k f e))
    (hθ : ∀ x, (bmsdop_blockForm k f e) (θ x) = (Spin.quadPlus 2 (GaloisField 2 f)) x)
    (hrank : e.rank = 4)
    (hcard : Nat.card (GaloisField 2 f) ≠ 2) :
    bmsdop_r2_PSLData k f S e J' := by
  obtain ⟨E, hE⟩ := bmsdop_ext k f S h1 h2 (Spin.quadPlus 2 (GaloisField 2 f)) θ hθ
    (Spin.nondegenerate_polarBilin_quadPlus 2 (GaloisField 2 f))
  obtain ⟨r, hrinj, hrrange, hrspin⟩ := bmsdop_r2_restrict k f S h1 h2 hS heA θ hθ E hE
  obtain ⟨hOmega, hq₁, hq₂, hcomm, -, -, -⟩ := bmsdop_r2_split f hcard
  have hcomp := bmsdop_r2_component k f S hJe r ⟨hrinj, hrrange⟩
    ((bmsdop_r2_rhoL f).range) ((bmsdop_r2_rhoR f).range) hOmega hq₁ hq₂ hcomm
  rcases hcomp with hJ | hJ
  · exact bmsdop_r2_model_data_L k f S h1 h2 hcard θ hθ E hE r ⟨hrinj, hrrange, hrspin⟩ hJ
  · exact bmsdop_r2_model_data_R k f S h1 h2 hcard θ hθ E hE r ⟨hrinj, hrrange, hrspin⟩ hJ

private lemma bmsdop_r2_rank1_decomp (f : ℕ) (A : Matrix (Fin 2) (Fin 2) (GaloisField 2 f))
    (hA : A.det = 0) :
    ∃ u v : Fin 2 → GaloisField 2 f, A = Matrix.vecMulVec u v := by
  rw [Matrix.det_fin_two] at hA
  have h00 : A 0 0 * A 1 1 = A 0 1 * A 1 0 := by linear_combination hA
  by_cases h : A 0 0 = 0
  · by_cases h01 : A 0 1 = 0
    · by_cases h10 : A 1 0 = 0
      · refine ⟨![0, 1], ![0, A 1 1], ?_⟩
        ext i j <;> fin_cases i <;> fin_cases j <;>
          simp [Matrix.vecMulVec, h, h01, h10]
      · refine ⟨![0, A 1 0], ![1, (A 1 0)⁻¹ * A 1 1], ?_⟩
        ext i j <;> fin_cases i <;> fin_cases j <;>
          simp [Matrix.vecMulVec, h, h01, h10, inv_mul_cancel₀]
    · have h10 : A 1 0 = 0 := by
        rcases mul_eq_zero.mp (by rw [h, zero_mul] at h00; exact h00.symm) with h' | h'
        · exact absurd h' h01
        · exact h'
      refine ⟨![A 0 1, A 1 1], ![0, 1], ?_⟩
      ext i j <;> fin_cases i <;> fin_cases j <;>
        simp [Matrix.vecMulVec, h, h10]
  · refine ⟨![A 0 0, A 1 0], ![1, (A 0 0)⁻¹ * A 0 1], ?_⟩
    ext i j <;> fin_cases i <;> fin_cases j <;>
      simp [Matrix.vecMulVec, h] <;> field_simp <;> linear_combination h00

private lemma bmsdop_r2_rank1_dichotomy (f : ℕ)
    (u₁ u₂ v₁ v₂ : Fin 2 → (GaloisField 2 f))
    (h : (Matrix.vecMulVec u₁ v₁ + Matrix.vecMulVec u₂ v₂).det = 0) :
    (Matrix.of ![u₁, u₂]).det = 0 ∨ (Matrix.of ![v₁, v₂]).det = 0 := by
  have hmul : Matrix.vecMulVec u₁ v₁ + Matrix.vecMulVec u₂ v₂ =
      (Matrix.of ![u₁, u₂]).transpose * Matrix.of ![v₁, v₂] := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.vecMulVec, Matrix.mul_apply, Fin.sum_univ_two]
  rw [hmul, Matrix.det_mul, Matrix.det_transpose] at h
  exact mul_eq_zero.mp h

private lemma bmsdop_r2_fin2_dependent (f : ℕ) (u₁ u₂ : Fin 2 → GaloisField 2 f)
    (h₁ : u₁ ≠ 0) (h₂ : u₂ ≠ 0)
    (h : (Matrix.of ![u₁, u₂]).det = 0) :
    ∃ c : GaloisField 2 f, u₂ = c • u₁ := by
  have h00 : u₁ 0 * u₂ 1 = u₁ 1 * u₂ 0 := by
    have h' := h
    simp only [Matrix.det_fin_two, Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons] at h'
    linear_combination h'
  by_cases h0 : u₁ 0 = 0
  · have h1 : u₁ 1 ≠ 0 := by
      intro h1
      exact h₁ (funext fun i => by fin_cases i <;> simp [h0, h1])
    have h20 : u₂ 0 = 0 := by
      rw [h0, zero_mul] at h00
      exact (mul_eq_zero.mp h00.symm).resolve_left h1
    refine ⟨u₂ 1 / u₁ 1, funext fun i => ?_⟩
    fin_cases i <;> simp [h0, h20, Pi.smul_apply, div_eq_mul_inv]
    field_simp [h1]
  · refine ⟨u₂ 0 / u₁ 0, funext fun i => ?_⟩
    fin_cases i <;> simp [Pi.smul_apply, div_eq_mul_inv]
    · field_simp
    · field_simp
      linear_combination h00

private lemma bmsdop_r2_lagrangian_image_or_kernel (f : ℕ)
    (hcard : Nat.card (GaloisField 2 f) ≠ 2)
    (a₁ a₂ : Fin 2 ⊕ Fin 2 → (GaloisField 2 f))
    (ha₁ : a₁ ≠ 0) (ha₂ : a₂ ≠ 0)
    (hlin : LinearIndependent (GaloisField 2 f) ![a₁, a₂])
    (hQ₁ : (Spin.quadPlus 2 (GaloisField 2 f)) a₁ = 0)
    (hQ₂ : (Spin.quadPlus 2 (GaloisField 2 f)) a₂ = 0)
    (hpol : QuadraticMap.polar (Spin.quadPlus 2 (GaloisField 2 f)) a₁ a₂ = 0) :
    (∃ u v₁ v₂ : Fin 2 → (GaloisField 2 f),
        bmsdop_r2_kappa f a₁ = Matrix.vecMulVec u v₁ ∧
        bmsdop_r2_kappa f a₂ = Matrix.vecMulVec u v₂) ∨ (∃ v w₁ w₂ : Fin 2 → (GaloisField 2 f),
        bmsdop_r2_kappa f a₁ = Matrix.vecMulVec w₁ v ∧
        bmsdop_r2_kappa f a₂ = Matrix.vecMulVec w₂ v) := by
  obtain ⟨u₁, v₁, hu₁⟩ := bmsdop_r2_rank1_decomp f (bmsdop_r2_kappa f a₁) (by
    rw [bmsdop_r2_kappa_det, hQ₁])
  obtain ⟨u₂, v₂, hu₂⟩ := bmsdop_r2_rank1_decomp f (bmsdop_r2_kappa f a₂) (by
    rw [bmsdop_r2_kappa_det, hQ₂])
  have hdet : (Matrix.vecMulVec u₁ v₁ + Matrix.vecMulVec u₂ v₂).det = 0 := by
    rw [← hu₁, ← hu₂]
    have hp := bmsdop_r2_kappa_polar f a₁ a₂
    rw [bmsdop_r2_kappa_det, bmsdop_r2_kappa_det, hQ₁, hQ₂, sub_zero, sub_zero] at hp
    rw [← hp, hpol]
  rcases bmsdop_r2_rank1_dichotomy f u₁ u₂ v₁ v₂ hdet with hU | hV
  · left
    have hu₁' : u₁ ≠ 0 := fun h => ha₁ ((bmsdop_r2_kappa f).injective (by
      rw [hu₁, h, map_zero]
      ext i j
      simp [Matrix.vecMulVec]))
    have hu₂' : u₂ ≠ 0 := fun h => ha₂ ((bmsdop_r2_kappa f).injective (by
      rw [hu₂, h, map_zero]
      ext i j
      simp [Matrix.vecMulVec]))
    obtain ⟨c, hc⟩ := bmsdop_r2_fin2_dependent f u₁ u₂ hu₁' hu₂' hU
    have hw : bmsdop_r2_kappa f a₂ = Matrix.vecMulVec u₁ (c • v₂) := by
      rw [hu₂, hc]
      ext i j
      simp only [Matrix.vecMulVec, Matrix.of_apply, Pi.smul_apply, smul_eq_mul]
      ring
    exact ⟨u₁, v₁, c • v₂, hu₁, hw⟩
  · right
    have hv₁' : v₁ ≠ 0 := fun h => ha₁ ((bmsdop_r2_kappa f).injective (by
      rw [hu₁, h, map_zero]
      ext i j
      simp [Matrix.vecMulVec]))
    have hv₂' : v₂ ≠ 0 := fun h => ha₂ ((bmsdop_r2_kappa f).injective (by
      rw [hu₂, h, map_zero]
      ext i j
      simp [Matrix.vecMulVec]))
    obtain ⟨c, hc⟩ := bmsdop_r2_fin2_dependent f v₁ v₂ hv₁' hv₂' hV
    have hw : bmsdop_r2_kappa f a₂ = Matrix.vecMulVec (c • u₂) v₁ := by
      rw [hu₂, hc]
      ext i j
      simp only [Matrix.vecMulVec, Matrix.of_apply, Pi.smul_apply, smul_eq_mul]
      ring
    exact ⟨v₁, u₁, c • u₂, hu₁, hw⟩

private lemma bmsdop_r2_siegelGroup_conj (f : ℕ)
    (g : (Fin 2 ⊕ Fin 2 → (GaloisField 2 f)) ≃ₗ[(GaloisField 2 f)] (Fin 2 ⊕ Fin 2 → (GaloisField 2
        f)))
    (hg : g ∈ TauCeti.QuadraticMap.orthogonalGroup (Spin.quadPlus 2 (GaloisField 2 f)))
    (u w : Fin 2 ⊕ Fin 2 → (GaloisField 2 f)) :
    (siegelGroup (Spin.quadPlus 2 (GaloisField 2 f)) u w).map (MulAut.conj g).toMonoidHom =
      siegelGroup (Spin.quadPlus 2 (GaloisField 2 f)) (g u) (g w) := by
  rw [siegelGroup, siegelGroup, MonoidHom.map_closure]
  congr 1
  ext x
  constructor
  · rintro ⟨y, ⟨c, rfl⟩, rfl⟩
    refine ⟨c, ?_⟩
    change g * CFSG.ClassicalGroups.Orthogonal.eichler _ u (c • w) * g⁻¹ =
      CFSG.ClassicalGroups.Orthogonal.eichler _ (g u) (c • g w)
    rw [CFSG.ClassicalGroups.Orthogonal.eichler_conj hg u (c • w), map_smul]
  · rintro ⟨c, rfl⟩
    refine ⟨CFSG.ClassicalGroups.Orthogonal.eichler _ u (c • w), ⟨c, rfl⟩, ?_⟩
    change g * CFSG.ClassicalGroups.Orthogonal.eichler _ u (c • w) * g⁻¹ =
      CFSG.ClassicalGroups.Orthogonal.eichler _ (g u) (c • g w)
    rw [CFSG.ClassicalGroups.Orthogonal.eichler_conj hg u (c • w), map_smul]

private lemma bmsdop_r2_det_add_vecMulVec (f : ℕ) (Y : Matrix (Fin 2) (Fin 2) (GaloisField 2 f))
    (u v : Fin 2 → (GaloisField 2 f)) :
    (Y + Matrix.vecMulVec u v).det =
      Y.det + ((Y 1 1 * u 0 - Y 0 1 * u 1) * v 0 + (Y 0 0 * u 1 - Y 1 0 * u 0) * v 1) := by
  simp only [Matrix.det_fin_two, Matrix.add_apply, Matrix.vecMulVec, Matrix.of_apply]
  ring

private lemma bmsdop_r2_polar_rank1 (f : ℕ) (X : Fin 2 ⊕ Fin 2 → (GaloisField 2 f))
    (u v : Fin 2 → (GaloisField 2 f)) :
    QuadraticMap.polar (Spin.quadPlus 2 (GaloisField 2 f)) X
        ((bmsdop_r2_kappa f).symm (Matrix.vecMulVec u v)) =
      ((bmsdop_r2_kappa f X) 1 1 * u 0 - (bmsdop_r2_kappa f X) 0 1 * u 1) * v 0 +
        ((bmsdop_r2_kappa f X) 0 0 * u 1 - (bmsdop_r2_kappa f X) 1 0 * u 0) * v 1 := by
  rw [bmsdop_r2_kappa_polar, LinearEquiv.apply_symm_apply, Matrix.det_vecMulVec, sub_zero,
    bmsdop_r2_det_add_vecMulVec]
  ring

private lemma bmsdop_r2_polar_rank1_pair (f : ℕ)
    (a₁ a₂ : Fin 2 ⊕ Fin 2 → (GaloisField 2 f)) (u v₁ v₂ : Fin 2 → (GaloisField 2 f))
    (h₁ : (bmsdop_r2_kappa f) a₁ = Matrix.vecMulVec u v₁)
    (h₂ : (bmsdop_r2_kappa f) a₂ = Matrix.vecMulVec u v₂) :
    QuadraticMap.polar (Spin.quadPlus 2 (GaloisField 2 f)) a₁ a₂ = 0 := by
  have ha₁ : a₁ = (bmsdop_r2_kappa f).symm (Matrix.vecMulVec u v₁) := ((bmsdop_r2_kappa
      f).symm_apply_eq.mpr h₁.symm).symm
  have ha₂ : a₂ = (bmsdop_r2_kappa f).symm (Matrix.vecMulVec u v₂) := ((bmsdop_r2_kappa
      f).symm_apply_eq.mpr h₂.symm).symm
  rw [ha₁, ha₂, QuadraticMap.polar_comm, bmsdop_r2_polar_rank1]
  simp only [LinearEquiv.apply_symm_apply, Matrix.vecMulVec, Matrix.of_apply]
  ring

private lemma bmsdop_r2_eichler_action_rank1 (f : ℕ)
    (u v₁ v₂ : Fin 2 → (GaloisField 2 f)) (c : (GaloisField 2 f)) (X : Fin 2 ⊕ Fin 2 → (GaloisField
        2 f)) :
    (bmsdop_r2_kappa f) (CFSG.ClassicalGroups.Orthogonal.eichler (Spin.quadPlus 2 (GaloisField 2 f))
        ((bmsdop_r2_kappa f).symm (Matrix.vecMulVec u v₁))
        (c • (bmsdop_r2_kappa f).symm (Matrix.vecMulVec u v₂)) X) =
      (bmsdop_r2_kappa f) X + Matrix.vecMulVec u (fun j => c * ((((bmsdop_r2_kappa f) X) 1 1 * u 0 -
          ((bmsdop_r2_kappa f) X) 0 1 * u 1) * v₁ 0 + (((bmsdop_r2_kappa f) X) 0 0 * u 1 -
              ((bmsdop_r2_kappa f) X) 1 0 * u 0) * v₁ 1) * v₂ j - c * ((((bmsdop_r2_kappa f) X) 1 1
                  * u 0 - ((bmsdop_r2_kappa f) X) 0 1 * u 1) * v₂ 0 + (((bmsdop_r2_kappa f) X) 0 0 *
                      u 1 - ((bmsdop_r2_kappa f) X) 1 0 * u 0) * v₂ 1) * v₁ j) := by
  have hQ1 : (Spin.quadPlus 2 (GaloisField 2 f)) ((bmsdop_r2_kappa f).symm (Matrix.vecMulVec u v₁))
      = 0 := by
    rw [← bmsdop_r2_kappa_det, LinearEquiv.apply_symm_apply, Matrix.det_vecMulVec]
  have hQ2 : (Spin.quadPlus 2 (GaloisField 2 f)) ((bmsdop_r2_kappa f).symm (Matrix.vecMulVec u v₂))
      = 0 := by
    rw [← bmsdop_r2_kappa_det, LinearEquiv.apply_symm_apply, Matrix.det_vecMulVec]
  have hpol : QuadraticMap.polar (Spin.quadPlus 2 (GaloisField 2 f)) ((bmsdop_r2_kappa f).symm
      (Matrix.vecMulVec u v₁))
      (c • (bmsdop_r2_kappa f).symm (Matrix.vecMulVec u v₂)) = 0 := by
    rw [QuadraticMap.polar_smul_right, bmsdop_r2_polar_rank1_pair f _ _ u v₁ v₂
      (by rw [LinearEquiv.apply_symm_apply]) (by rw [LinearEquiv.apply_symm_apply]), smul_zero]
  rw [CFSG.ClassicalGroups.Orthogonal.eichler_apply hQ1 hpol X]
  simp only [map_add, map_sub, map_smul, LinearEquiv.apply_symm_apply, hQ2,
    QuadraticMap.map_smul, QuadraticMap.polar_smul_right, smul_eq_mul, bmsdop_r2_polar_rank1]
  simp only [Matrix.vecMulVec, Matrix.of_apply]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp only [Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, Matrix.of_apply,
      Fin.reduceFinMk] <;> ring_nf

private lemma bmsdop_r2_eichler_action_normalized (f : ℕ)
    (u : Fin 2 → (GaloisField 2 f)) (c : (GaloisField 2 f)) (X : Fin 2 ⊕ Fin 2 → (GaloisField 2 f))
        :
    (bmsdop_r2_kappa f) (CFSG.ClassicalGroups.Orthogonal.eichler (Spin.quadPlus 2 (GaloisField 2 f))
        ((bmsdop_r2_kappa f).symm (Matrix.vecMulVec u ![1, 0]))
        (c • (bmsdop_r2_kappa f).symm (Matrix.vecMulVec u ![0, 1])) X) =
      (bmsdop_r2_kappa f) X + Matrix.vecMulVec u (fun j => c * (((bmsdop_r2_kappa f) X) 1 1 * u 0 -
          ((bmsdop_r2_kappa f) X) 0 1 * u 1) * ![0, 1] j - c * (((bmsdop_r2_kappa f) X) 0 0 * u 1 -
              ((bmsdop_r2_kappa f) X) 1 0 * u 0) * ![1, 0] j) := by
  simpa only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.head_fin_const,
    mul_one, mul_zero, add_zero, zero_add, zero_mul, sub_zero] using
    bmsdop_r2_eichler_action_rank1 f u ![1, 0] ![0, 1] c X

private lemma bmsdop_r2_vecMulVec_z_eq (f : ℕ)
    (u v₁ v₂ : Fin 2 → (GaloisField 2 f)) (c : (GaloisField 2 f)) (X : Fin 2 ⊕ Fin 2 → (GaloisField
        2 f)) :
    Matrix.vecMulVec u (fun j => c * ((((bmsdop_r2_kappa f) X) 1 1 * u 0 - ((bmsdop_r2_kappa f) X) 0
        1 * u 1) * v₁ 0 + (((bmsdop_r2_kappa f) X) 0 0 * u 1 - ((bmsdop_r2_kappa f) X) 1 0 * u 0) *
            v₁ 1) * v₂ j - c * ((((bmsdop_r2_kappa f) X) 1 1 * u 0 - ((bmsdop_r2_kappa f) X) 0 1 * u
                1) * v₂ 0 + (((bmsdop_r2_kappa f) X) 0 0 * u 1 - ((bmsdop_r2_kappa f) X) 1 0 * u 0)
                    * v₂ 1) * v₁ j) =
      Matrix.vecMulVec u (fun j => (c * (v₁ 0 * v₂ 1 - v₁ 1 * v₂ 0)) * (((bmsdop_r2_kappa f) X) 1 1
          * u 0 - ((bmsdop_r2_kappa f) X) 0 1 * u 1) * ![0, 1] j - (c * (v₁ 0 * v₂ 1 - v₁ 1 * v₂ 0))
              * (((bmsdop_r2_kappa f) X) 0 0 * u 1 - ((bmsdop_r2_kappa f) X) 1 0 * u 0) * ![1, 0] j)
                  := by
  ext i j
  fin_cases j <;>
    simp only [Matrix.vecMulVec, Matrix.of_apply, Fin.reduceFinMk, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.head_cons, Matrix.head_fin_const] <;> ring_nf

private lemma bmsdop_r2_eichler_eq_normalized (f : ℕ)
    (a₁ a₂ : Fin 2 ⊕ Fin 2 → (GaloisField 2 f)) (u v₁ v₂ : Fin 2 → (GaloisField 2 f))
    (h₁ : bmsdop_r2_kappa f a₁ = Matrix.vecMulVec u v₁)
    (h₂ : bmsdop_r2_kappa f a₂ = Matrix.vecMulVec u v₂) (c : (GaloisField 2 f)) :
    CFSG.ClassicalGroups.Orthogonal.eichler (Spin.quadPlus 2 (GaloisField 2 f)) a₁ (c • a₂) =
      CFSG.ClassicalGroups.Orthogonal.eichler (Spin.quadPlus 2 (GaloisField 2 f))
        ((bmsdop_r2_kappa f).symm (Matrix.vecMulVec u ![1, 0]))
        ((c * (v₁ 0 * v₂ 1 - v₁ 1 * v₂ 0)) •
          (bmsdop_r2_kappa f).symm (Matrix.vecMulVec u ![0, 1])) := by
  apply LinearEquiv.ext
  intro X
  apply (bmsdop_r2_kappa f).injective
  have ha₁ : a₁ = (bmsdop_r2_kappa f).symm (Matrix.vecMulVec u v₁) := ((bmsdop_r2_kappa
      f).symm_apply_eq.mpr h₁.symm).symm
  have ha₂ : a₂ = (bmsdop_r2_kappa f).symm (Matrix.vecMulVec u v₂) := ((bmsdop_r2_kappa
      f).symm_apply_eq.mpr h₂.symm).symm
  rw [ha₁, ha₂, bmsdop_r2_eichler_action_rank1,
    bmsdop_r2_eichler_action_normalized (c := c * (v₁ 0 * v₂ 1 - v₁ 1 * v₂ 0)),
    bmsdop_r2_vecMulVec_z_eq]

private lemma bmsdop_r2_eichler_mem_normalized (f : ℕ)
    (a₁ a₂ : Fin 2 ⊕ Fin 2 → (GaloisField 2 f)) (u v₁ v₂ : Fin 2 → (GaloisField 2 f))
    (h₁ : bmsdop_r2_kappa f a₁ = Matrix.vecMulVec u v₁)
    (h₂ : bmsdop_r2_kappa f a₂ = Matrix.vecMulVec u v₂) (c : (GaloisField 2 f)) :
    CFSG.ClassicalGroups.Orthogonal.eichler (Spin.quadPlus 2 (GaloisField 2 f)) a₁ (c • a₂) ∈
      siegelGroup (Spin.quadPlus 2 (GaloisField 2 f)) ((bmsdop_r2_kappa f).symm (Matrix.vecMulVec u
          ![1, 0]))
        ((bmsdop_r2_kappa f).symm (Matrix.vecMulVec u ![0, 1])) := by
  rw [bmsdop_r2_eichler_eq_normalized f a₁ a₂ u v₁ v₂ h₁ h₂ c]
  exact Subgroup.subset_closure ⟨_, rfl⟩

private lemma bmsdop_r2_siegelGroup_le_normalized (f : ℕ)
    (a₁ a₂ : Fin 2 ⊕ Fin 2 → (GaloisField 2 f)) (u v₁ v₂ : Fin 2 → (GaloisField 2 f))
    (h₁ : bmsdop_r2_kappa f a₁ = Matrix.vecMulVec u v₁)
    (h₂ : bmsdop_r2_kappa f a₂ = Matrix.vecMulVec u v₂) :
    siegelGroup (Spin.quadPlus 2 (GaloisField 2 f)) a₁ a₂ ≤ siegelGroup (Spin.quadPlus 2
        (GaloisField 2 f)) ((bmsdop_r2_kappa f).symm (Matrix.vecMulVec u ![1, 0]))
        ((bmsdop_r2_kappa f).symm (Matrix.vecMulVec u ![0, 1])) := by
  rw [siegelGroup, Subgroup.closure_le]
  rintro x ⟨c, rfl⟩
  exact bmsdop_r2_eichler_mem_normalized f a₁ a₂ u v₁ v₂ h₁ h₂ c

private lemma bmsdop_r2_siegelGroup_normalized_le (f : ℕ)
    (a₁ a₂ : Fin 2 ⊕ Fin 2 → (GaloisField 2 f)) (u v₁ v₂ : Fin 2 → (GaloisField 2 f))
    (h₁ : bmsdop_r2_kappa f a₁ = Matrix.vecMulVec u v₁)
    (h₂ : bmsdop_r2_kappa f a₂ = Matrix.vecMulVec u v₂)
    (hdet : v₁ 0 * v₂ 1 - v₁ 1 * v₂ 0 ≠ 0) :
    siegelGroup (Spin.quadPlus 2 (GaloisField 2 f)) ((bmsdop_r2_kappa f).symm (Matrix.vecMulVec u
        ![1, 0]))
        ((bmsdop_r2_kappa f).symm (Matrix.vecMulVec u ![0, 1])) ≤ siegelGroup (Spin.quadPlus 2
            (GaloisField 2 f)) a₁ a₂ := by
  rw [siegelGroup, Subgroup.closure_le]
  rintro x ⟨c, rfl⟩
  have hEq : CFSG.ClassicalGroups.Orthogonal.eichler (Spin.quadPlus 2 (GaloisField 2 f))
      ((bmsdop_r2_kappa f).symm (Matrix.vecMulVec u ![1, 0]))
      (c • (bmsdop_r2_kappa f).symm (Matrix.vecMulVec u ![0, 1])) =
      CFSG.ClassicalGroups.Orthogonal.eichler (Spin.quadPlus 2 (GaloisField 2 f)) a₁ ((c * (v₁ 0 *
          v₂ 1 - v₁ 1 * v₂ 0)⁻¹) • a₂) := by
    apply LinearEquiv.ext
    intro X
    apply (bmsdop_r2_kappa f).injective
    have ha₁ : a₁ = (bmsdop_r2_kappa f).symm (Matrix.vecMulVec u v₁) :=
      ((bmsdop_r2_kappa f).symm_apply_eq.mpr h₁.symm).symm
    have ha₂ : a₂ = (bmsdop_r2_kappa f).symm (Matrix.vecMulVec u v₂) :=
      ((bmsdop_r2_kappa f).symm_apply_eq.mpr h₂.symm).symm
    rw [ha₁, ha₂, bmsdop_r2_eichler_action_normalized,
      bmsdop_r2_eichler_action_rank1 (c := c * (v₁ 0 * v₂ 1 - v₁ 1 * v₂ 0)⁻¹),
          bmsdop_r2_vecMulVec_z_eq]
    congr 1
    ext i j
    simp only [Matrix.vecMulVec, Matrix.of_apply]
    field_simp [hdet]
  rw [hEq]
  exact Subgroup.subset_closure ⟨_, rfl⟩

private lemma bmsdop_r2_siegelGroup_eq_normalized (f : ℕ)
    (a₁ a₂ : Fin 2 ⊕ Fin 2 → (GaloisField 2 f)) (u v₁ v₂ : Fin 2 → (GaloisField 2 f))
    (h₁ : bmsdop_r2_kappa f a₁ = Matrix.vecMulVec u v₁)
    (h₂ : bmsdop_r2_kappa f a₂ = Matrix.vecMulVec u v₂)
    (hdet : v₁ 0 * v₂ 1 - v₁ 1 * v₂ 0 ≠ 0) :
    siegelGroup (Spin.quadPlus 2 (GaloisField 2 f)) a₁ a₂ = siegelGroup (Spin.quadPlus 2
        (GaloisField 2 f)) ((bmsdop_r2_kappa f).symm (Matrix.vecMulVec u ![1, 0]))
        ((bmsdop_r2_kappa f).symm (Matrix.vecMulVec u ![0, 1])) :=
  le_antisymm (bmsdop_r2_siegelGroup_le_normalized f a₁ a₂ u v₁ v₂ h₁ h₂)
    (bmsdop_r2_siegelGroup_normalized_le f a₁ a₂ u v₁ v₂ h₁ h₂ hdet)

private lemma bmsdop_r2_eichler_mem_siegelGroup (f : ℕ)
    (a₁ a₂ b₁ b₂ : Fin 2 ⊕ Fin 2 → (GaloisField 2 f)) (u v₁ v₂ w₁ w₂ : Fin 2 → (GaloisField 2 f))
    (ha₁ : bmsdop_r2_kappa f a₁ = Matrix.vecMulVec u v₁)
    (ha₂ : bmsdop_r2_kappa f a₂ = Matrix.vecMulVec u v₂)
    (hb₁ : bmsdop_r2_kappa f b₁ = Matrix.vecMulVec u w₁)
    (hb₂ : bmsdop_r2_kappa f b₂ = Matrix.vecMulVec u w₂)
    (hdetv : v₁ 0 * v₂ 1 - v₁ 1 * v₂ 0 ≠ 0) (hdetw : w₁ 0 * w₂ 1 - w₁ 1 * w₂ 0 ≠ 0)
    (c : (GaloisField 2 f)) :
    CFSG.ClassicalGroups.Orthogonal.eichler (Spin.quadPlus 2 (GaloisField 2 f)) a₁ (c • a₂) ∈
      siegelGroup (Spin.quadPlus 2 (GaloisField 2 f)) b₁ b₂ := by
  have hmem : CFSG.ClassicalGroups.Orthogonal.eichler (Spin.quadPlus 2 (GaloisField 2 f)) a₁
      (c • a₂) ∈ siegelGroup (Spin.quadPlus 2 (GaloisField 2 f)) a₁ a₂ :=
    Subgroup.subset_closure ⟨c, rfl⟩
  rw [bmsdop_r2_siegelGroup_eq_normalized f a₁ a₂ u v₁ v₂ ha₁ ha₂ hdetv] at hmem
  rw [bmsdop_r2_siegelGroup_eq_normalized f b₁ b₂ u w₁ w₂ hb₁ hb₂ hdetw]
  exact hmem

private lemma bmsdop_r2_siegelGroup_le_of_same_image (f : ℕ)
    (a₁ a₂ b₁ b₂ : Fin 2 ⊕ Fin 2 → (GaloisField 2 f)) (u v₁ v₂ w₁ w₂ : Fin 2 → (GaloisField 2 f))
    (ha₁ : bmsdop_r2_kappa f a₁ = Matrix.vecMulVec u v₁)
    (ha₂ : bmsdop_r2_kappa f a₂ = Matrix.vecMulVec u v₂)
    (hb₁ : bmsdop_r2_kappa f b₁ = Matrix.vecMulVec u w₁)
    (hb₂ : bmsdop_r2_kappa f b₂ = Matrix.vecMulVec u w₂)
    (hdetv : v₁ 0 * v₂ 1 - v₁ 1 * v₂ 0 ≠ 0) (hdetw : w₁ 0 * w₂ 1 - w₁ 1 * w₂ 0 ≠ 0) :
    siegelGroup (Spin.quadPlus 2 (GaloisField 2 f)) a₁ a₂ ≤ siegelGroup (Spin.quadPlus 2
        (GaloisField 2 f)) b₁ b₂ := by
  rw [siegelGroup, Subgroup.closure_le]
  rintro x ⟨c, rfl⟩
  exact bmsdop_r2_eichler_mem_siegelGroup f a₁ a₂ b₁ b₂ u v₁ v₂ w₁ w₂ ha₁ ha₂ hb₁ hb₂ hdetv hdetw c

private lemma bmsdop_r2_siegelGroup_basis_invariant (f : ℕ)
    (a₁ a₂ b₁ b₂ : Fin 2 ⊕ Fin 2 → (GaloisField 2 f)) (u v₁ v₂ w₁ w₂ : Fin 2 → (GaloisField 2 f))
    (ha₁ : bmsdop_r2_kappa f a₁ = Matrix.vecMulVec u v₁)
    (ha₂ : bmsdop_r2_kappa f a₂ = Matrix.vecMulVec u v₂)
    (hb₁ : bmsdop_r2_kappa f b₁ = Matrix.vecMulVec u w₁)
    (hb₂ : bmsdop_r2_kappa f b₂ = Matrix.vecMulVec u w₂)
    (hdetv : v₁ 0 * v₂ 1 - v₁ 1 * v₂ 0 ≠ 0) (hdetw : w₁ 0 * w₂ 1 - w₁ 1 * w₂ 0 ≠ 0) :
    siegelGroup (Spin.quadPlus 2 (GaloisField 2 f)) a₁ a₂ = siegelGroup (Spin.quadPlus 2
        (GaloisField 2 f)) b₁ b₂ := by
  exact le_antisymm
    (bmsdop_r2_siegelGroup_le_of_same_image f a₁ a₂ b₁ b₂ u v₁ v₂ w₁ w₂ ha₁ ha₂ hb₁ hb₂ hdetv hdetw)
    (bmsdop_r2_siegelGroup_le_of_same_image f b₁ b₂ a₁ a₂ u w₁ w₂ v₁ v₂ hb₁ hb₂ ha₁ ha₂ hdetw hdetv)

private lemma bmsdop_r2_siegelGroup_family1_param (f : ℕ)
    (a₁ a₂ : Fin 2 ⊕ Fin 2 → (GaloisField 2 f)) (u : Fin 2 → (GaloisField 2 f))
    (hu : u ≠ 0)
    (ha₁ : (bmsdop_r2_kappa f) a₁ = Matrix.vecMulVec u ![1, 0])
    (ha₂ : (bmsdop_r2_kappa f) a₂ = Matrix.vecMulVec u ![0, 1]) :
    ∃ g : Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 f),
      siegelGroup (Spin.quadPlus 2 (GaloisField 2 f)) a₁ a₂ =
        siegelGroup (Spin.quadPlus 2 (GaloisField 2 f))
          ((bmsdop_r2_kappa f).symm ((g : Matrix (Fin 2) (Fin 2) (GaloisField 2 f)) * (!![1, 0; 0,
              0] : Matrix (Fin 2) (Fin 2) (GaloisField 2 f))))
          ((bmsdop_r2_kappa f).symm ((g : Matrix (Fin 2) (Fin 2) (GaloisField 2 f)) * (!![0, 1; 0,
              0] : Matrix (Fin 2) (Fin 2) (GaloisField 2 f)))) := by
  have ha₁' : a₁ = (bmsdop_r2_kappa f).symm (Matrix.vecMulVec u ![1, 0]) :=
    ((bmsdop_r2_kappa f).symm_apply_eq.mpr ha₁.symm).symm
  have ha₂' : a₂ = (bmsdop_r2_kappa f).symm (Matrix.vecMulVec u ![0, 1]) :=
    ((bmsdop_r2_kappa f).symm_apply_eq.mpr ha₂.symm).symm
  have key : ∀ (g : Matrix (Fin 2) (Fin 2) (GaloisField 2 f)), g * (!![1, 0; 0, 0] : Matrix (Fin 2)
      (Fin 2) (GaloisField 2 f)) =
      Matrix.vecMulVec (fun i => g i 0) ![1, 0] := by
    intro g
    ext i j
    fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.vecMulVec, Matrix.of_apply]
  have key2 : ∀ (g : Matrix (Fin 2) (Fin 2) (GaloisField 2 f)), g * (!![0, 1; 0, 0] : Matrix (Fin 2)
      (Fin 2) (GaloisField 2 f)) =
      Matrix.vecMulVec (fun i => g i 0) ![0, 1] := by
    intro g
    ext i j
    fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.vecMulVec, Matrix.of_apply]
  by_cases hu0 : u 0 = 0
  · have hu1 : u 1 ≠ 0 := by
      intro h1
      exact hu (funext fun i => by fin_cases i <;> simp [hu0, h1])
    refine ⟨⟨!![0, -(u 1)⁻¹; u 1, 0], ?_⟩, ?_⟩
    · rw [Matrix.det_fin_two]
      simp only [Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
      field_simp
      ring
    · rw [ha₁', ha₂']
      congr 1
      · apply (bmsdop_r2_kappa f).injective
        rw [LinearEquiv.apply_symm_apply, key]
        ext i
        fin_cases i <;> simp [hu0]
      · apply (bmsdop_r2_kappa f).injective
        rw [LinearEquiv.apply_symm_apply, key2]
        ext i
        fin_cases i <;> simp [hu0]
  · refine ⟨⟨!![u 0, 0; u 1, (u 0)⁻¹], ?_⟩, ?_⟩
    · rw [Matrix.det_fin_two]
      simp only [Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
      field_simp [hu0]
      ring
    · rw [ha₁', ha₂']
      congr 1
      · apply (bmsdop_r2_kappa f).injective
        rw [LinearEquiv.apply_symm_apply, key]
        ext i
        fin_cases i <;> simp
      · apply (bmsdop_r2_kappa f).injective
        rw [LinearEquiv.apply_symm_apply, key2]
        ext i
        fin_cases i <;> simp

private lemma bmsdop_r2_v_det_ne_zero (f : ℕ)
    (a₁ a₂ : Fin 2 ⊕ Fin 2 → (GaloisField 2 f)) (u v₁ v₂ : Fin 2 → (GaloisField 2 f))
    (hlin : LinearIndependent (GaloisField 2 f) ![a₁, a₂])
    (h₁ : (bmsdop_r2_kappa f) a₁ = Matrix.vecMulVec u v₁)
    (h₂ : (bmsdop_r2_kappa f) a₂ = Matrix.vecMulVec u v₂) :
    v₁ 0 * v₂ 1 - v₁ 1 * v₂ 0 ≠ 0 := by
  intro hdet
  have ha₁ne : a₁ ≠ 0 := by simpa [Matrix.cons_val_zero] using hlin.ne_zero 0
  have ha₂ne : a₂ ≠ 0 := by simpa [Matrix.cons_val_one, Matrix.head_cons] using hlin.ne_zero 1
  have hv₁ : v₁ ≠ 0 := fun h0 => ha₁ne ((bmsdop_r2_kappa f).injective (by
    rw [h₁, h0]; ext i j; simp [Matrix.vecMulVec]))
  have hv₂ : v₂ ≠ 0 := fun h0 => ha₂ne ((bmsdop_r2_kappa f).injective (by
    rw [h₂, h0]; ext i j; simp [Matrix.vecMulVec]))
  have hdet0 : (Matrix.of ![v₁, v₂]).det = 0 := by
    rw [Matrix.det_fin_two]; exact hdet
  obtain ⟨c, hc⟩ := bmsdop_r2_fin2_dependent f v₁ v₂ hv₁ hv₂ hdet0
  have ha2 : a₂ = c • a₁ := (bmsdop_r2_kappa f).injective (by
    rw [map_smul, h₂, hc, h₁]
    ext i j
    simp only [Matrix.vecMulVec, Matrix.of_apply, Matrix.smul_apply, Pi.smul_apply, smul_eq_mul]
    ring)
  have hc1 : c • a₁ + (1 : (GaloisField 2 f)) • a₂ = 0 := by
    rw [ha2, one_smul]
    rw [← CharTwo.neg_eq (c • a₁), ← sub_eq_add_neg, CharTwo.neg_eq (c • a₁), sub_self]
  exact one_ne_zero ((LinearIndependent.pair_iff.mp hlin) c 1 hc1).2

private lemma bmsdop_r2_siegelGroup_family1 (f : ℕ)
    (a₁ a₂ : Fin 2 ⊕ Fin 2 → (GaloisField 2 f))
    (hlin : LinearIndependent (GaloisField 2 f) ![a₁, a₂])
    (h : ∃ u v₁ v₂ : Fin 2 → (GaloisField 2 f),
        bmsdop_r2_kappa f a₁ = Matrix.vecMulVec u v₁ ∧
        bmsdop_r2_kappa f a₂ = Matrix.vecMulVec u v₂) :
    ∃ g : Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 f),
      siegelGroup (Spin.quadPlus 2 (GaloisField 2 f)) a₁ a₂ =
        siegelGroup (Spin.quadPlus 2 (GaloisField 2 f))
          ((bmsdop_r2_kappa f).symm (((g : Matrix (Fin 2) (Fin 2) (GaloisField 2 f)) * (!![1, 0; 0,
              0] : Matrix (Fin 2) (Fin 2) (GaloisField 2 f)))))
          ((bmsdop_r2_kappa f).symm (((g : Matrix (Fin 2) (Fin 2) (GaloisField 2 f)) * (!![0, 1; 0,
              0] : Matrix (Fin 2) (Fin 2) (GaloisField 2 f))))) := by
  obtain ⟨u, v₁, v₂, ha₁, ha₂⟩ := h
  have hu : u ≠ 0 := by
    intro h0
    have ha0 : a₁ = 0 := (bmsdop_r2_kappa f).injective (by
      rw [ha₁, h0]; ext i j; simp [Matrix.vecMulVec])
    exact hlin.ne_zero 0 (by simpa [Matrix.cons_val_zero] using ha0)
  have hdetv := bmsdop_r2_v_det_ne_zero f a₁ a₂ u v₁ v₂ hlin ha₁ ha₂
  have hdetw : ((![1, 0] : Fin 2 → (GaloisField 2 f))) 0 * (![0, 1] : Fin 2 → (GaloisField 2 f)) 1 -
      (![1, 0] : Fin 2 → (GaloisField 2 f)) 1 * (![0, 1] : Fin 2 → (GaloisField 2 f)) 0 ≠ 0 := by
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.head_fin_const,
      mul_one, mul_zero, sub_zero]
    exact one_ne_zero
  obtain ⟨g, hg⟩ := bmsdop_r2_siegelGroup_family1_param f
    ((bmsdop_r2_kappa f).symm (Matrix.vecMulVec u ![1, 0]))
    ((bmsdop_r2_kappa f).symm (Matrix.vecMulVec u ![0, 1])) u hu
    (by rw [LinearEquiv.apply_symm_apply]) (by rw [LinearEquiv.apply_symm_apply])
  exact ⟨g, by
    rw [bmsdop_r2_siegelGroup_basis_invariant f a₁ a₂ _ _ u v₁ v₂ ![1, 0] ![0, 1]
      ha₁ ha₂ (by rw [LinearEquiv.apply_symm_apply]) (by rw [LinearEquiv.apply_symm_apply])
      hdetv hdetw, hg]⟩

private noncomputable def bmsdop_r2_transpose (f : ℕ) :
    (Fin 2 ⊕ Fin 2 → (GaloisField 2 f)) ≃ₗ[(GaloisField 2 f)] (Fin 2 ⊕ Fin 2 → (GaloisField 2 f))
        where
  toFun x := (bmsdop_r2_kappa f).symm (((bmsdop_r2_kappa f) x).transpose)
  invFun x := (bmsdop_r2_kappa f).symm (((bmsdop_r2_kappa f) x).transpose)
  left_inv x := by simp [Matrix.transpose_transpose]
  right_inv x := by simp [Matrix.transpose_transpose]
  map_add' x y := by
    simp only [map_add, Matrix.transpose_add, LinearEquiv.apply_symm_apply]
  map_smul' a x := by
    simp only [map_smul, Matrix.transpose_smul, LinearEquiv.apply_symm_apply, RingHom.id_apply]

private lemma bmsdop_r2_transpose_mem (f : ℕ) :
    bmsdop_r2_transpose f ∈ TauCeti.QuadraticMap.orthogonalGroup (Spin.quadPlus 2 (GaloisField 2 f))
        := by
  rw [TauCeti.QuadraticMap.mem_orthogonalGroup_iff]
  intro x
  change (Spin.quadPlus 2 (GaloisField 2 f))
      ((bmsdop_r2_kappa f).symm (((bmsdop_r2_kappa f) x).transpose)) =
    (Spin.quadPlus 2 (GaloisField 2 f)) x
  rw [← bmsdop_r2_kappa_det, LinearEquiv.apply_symm_apply, Matrix.det_transpose,
    bmsdop_r2_kappa_det]

private lemma bmsdop_r2_transpose_apply (f : ℕ) (x : Fin 2 ⊕ Fin 2 → (GaloisField 2 f)) :
    (bmsdop_r2_kappa f) (bmsdop_r2_transpose f x) = (((bmsdop_r2_kappa f) x).transpose) := by
  change (bmsdop_r2_kappa f)
      ((bmsdop_r2_kappa f).symm (((bmsdop_r2_kappa f) x).transpose)) = ((bmsdop_r2_kappa f)
          x).transpose
  rw [LinearEquiv.apply_symm_apply]

private lemma bmsdop_r2_transpose_symm_apply (f : ℕ) (M : Matrix (Fin 2) (Fin 2) (GaloisField 2 f))
    :
    bmsdop_r2_transpose f (((bmsdop_r2_kappa f).symm M)) = (bmsdop_r2_kappa f).symm (M.transpose) :=
        by
  apply (bmsdop_r2_kappa f).injective
  rw [bmsdop_r2_transpose_apply, LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]

private lemma bmsdop_r2_transpose_transpose (f : ℕ) (x : Fin 2 ⊕ Fin 2 → (GaloisField 2 f)) :
    bmsdop_r2_transpose f (bmsdop_r2_transpose f x) = x := by
  apply (bmsdop_r2_kappa f).injective
  rw [bmsdop_r2_transpose_apply, bmsdop_r2_transpose_apply, Matrix.transpose_transpose]

private lemma bmsdop_r2_transpose_vecMulVec (f : ℕ) (w v : Fin 2 → (GaloisField 2 f)) :
    (Matrix.vecMulVec w v).transpose = Matrix.vecMulVec v w := by
  ext i j
  simp only [Matrix.transpose_apply, Matrix.vecMulVec, Matrix.of_apply]
  exact mul_comm _ _

private lemma bmsdop_r2_transpose_injective (f : ℕ) :
    Function.Injective (bmsdop_r2_transpose f) :=
  (bmsdop_r2_transpose f).injective

private lemma bmsdop_r2_transpose_hlin (f : ℕ) (a₁ a₂ : Fin 2 ⊕ Fin 2 → (GaloisField 2 f))
    (hlin : LinearIndependent (GaloisField 2 f) ![a₁, a₂]) :
    LinearIndependent (GaloisField 2 f) ![(bmsdop_r2_transpose f) a₁, (bmsdop_r2_transpose f) a₂] :=
        by
  have h := hlin.map' (bmsdop_r2_transpose f).toLinearMap (by
    rw [LinearMap.ker_eq_bot]; exact bmsdop_r2_transpose_injective f)
  convert h using 1
  funext i
  fin_cases i <;> rfl

private lemma bmsdop_r2_transpose_mul_E (f : ℕ) (g : Matrix (Fin 2) (Fin 2) (GaloisField 2 f)) :
    (g * (!![1, 0; 0, 0] : Matrix (Fin 2) (Fin 2) (GaloisField 2 f))).transpose =
        (!![1, 0; 0, 0] : Matrix (Fin 2) (Fin 2) (GaloisField 2 f)) * g.transpose ∧
      (g * (!![0, 1; 0, 0] : Matrix (Fin 2) (Fin 2) (GaloisField 2 f))).transpose =
        (!![0, 0; 1, 0] : Matrix (Fin 2) (Fin 2) (GaloisField 2 f)) * g.transpose := by
  constructor <;>
    ext i j <;>
    fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Matrix.transpose_apply, Fin.sum_univ_two]

private lemma bmsdop_r2_transpose_siegelGroup (f : ℕ) (a₁ a₂ : Fin 2 ⊕ Fin 2 → (GaloisField 2 f)) :
    (siegelGroup (Spin.quadPlus 2 (GaloisField 2 f)) (bmsdop_r2_transpose f a₁) (bmsdop_r2_transpose
        f a₂)).map
        (MulAut.conj (bmsdop_r2_transpose f)).toMonoidHom = siegelGroup (Spin.quadPlus 2
            (GaloisField 2 f)) a₁ a₂ := by
  rw [bmsdop_r2_siegelGroup_conj f (bmsdop_r2_transpose f) (bmsdop_r2_transpose_mem f)
    (bmsdop_r2_transpose f a₁) (bmsdop_r2_transpose f a₂)]
  congr 1
  · exact bmsdop_r2_transpose_transpose f a₁
  · exact bmsdop_r2_transpose_transpose f a₂

private lemma bmsdop_r2_siegelGroup_family2 (f : ℕ)
    (a₁ a₂ : Fin 2 ⊕ Fin 2 → (GaloisField 2 f))
    (hlin : LinearIndependent (GaloisField 2 f) ![a₁, a₂])
    (h : ∃ v w₁ w₂ : Fin 2 → (GaloisField 2 f),
        bmsdop_r2_kappa f a₁ = Matrix.vecMulVec w₁ v ∧
        bmsdop_r2_kappa f a₂ = Matrix.vecMulVec w₂ v) :
    ∃ h' : Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 f),
      siegelGroup (Spin.quadPlus 2 (GaloisField 2 f)) a₁ a₂ =
        siegelGroup (Spin.quadPlus 2 (GaloisField 2 f))
          ((bmsdop_r2_kappa f).symm ((!![1, 0; 0, 0] : Matrix (Fin 2) (Fin 2) (GaloisField 2 f)) *
              (h' : Matrix (Fin 2) (Fin 2) (GaloisField 2 f))))
          ((bmsdop_r2_kappa f).symm ((!![0, 0; 1, 0] : Matrix (Fin 2) (Fin 2) (GaloisField 2 f)) *
              (h' : Matrix (Fin 2) (Fin 2) (GaloisField 2 f)))) := by
  obtain ⟨v, w₁, w₂, ha₁, ha₂⟩ := h
  have hT₁ : (bmsdop_r2_kappa f) (bmsdop_r2_transpose f a₁) = Matrix.vecMulVec v w₁ := by
    rw [bmsdop_r2_transpose_apply, ha₁, bmsdop_r2_transpose_vecMulVec]
  have hT₂ : (bmsdop_r2_kappa f) (bmsdop_r2_transpose f a₂) = Matrix.vecMulVec v w₂ := by
    rw [bmsdop_r2_transpose_apply, ha₂, bmsdop_r2_transpose_vecMulVec]
  obtain ⟨g, hg⟩ := bmsdop_r2_siegelGroup_family1 f (bmsdop_r2_transpose f a₁) (bmsdop_r2_transpose
      f a₂)
    (bmsdop_r2_transpose_hlin f a₁ a₂ hlin) ⟨v, w₁, w₂, hT₁, hT₂⟩
  refine ⟨⟨(↑g : Matrix (Fin 2) (Fin 2) (GaloisField 2 f)).transpose, ?_⟩, ?_⟩
  · rw [Matrix.det_transpose, Matrix.SpecialLinearGroup.det_coe]
  · rw [← bmsdop_r2_transpose_siegelGroup f a₁ a₂, hg,
      bmsdop_r2_siegelGroup_conj f (bmsdop_r2_transpose f) (bmsdop_r2_transpose_mem f)
        ((bmsdop_r2_kappa f).symm ((↑g : Matrix (Fin 2) (Fin 2) (GaloisField 2 f)) * (!![1, 0; 0, 0]
            : Matrix (Fin 2) (Fin 2) (GaloisField 2 f))))
        ((bmsdop_r2_kappa f).symm ((↑g : Matrix (Fin 2) (Fin 2) (GaloisField 2 f)) * (!![0, 1; 0, 0]
            : Matrix (Fin 2) (Fin 2) (GaloisField 2 f))))]
    congr 1
    · rw [bmsdop_r2_transpose_symm_apply, (bmsdop_r2_transpose_mul_E f ↑g).1]
    · rw [bmsdop_r2_transpose_symm_apply, (bmsdop_r2_transpose_mul_E f ↑g).2]

private lemma bmsdop_r2_lagrangian_dichotomy (f : ℕ)
    (hcard : Nat.card (GaloisField 2 f) ≠ 2)
    (a₁ a₂ : Fin 2 ⊕ Fin 2 → (GaloisField 2 f))
    (ha₁ : a₁ ≠ 0) (ha₂ : a₂ ≠ 0)
    (hlin : LinearIndependent (GaloisField 2 f) ![a₁, a₂])
    (hQ₁ : (Spin.quadPlus 2 (GaloisField 2 f)) a₁ = 0)
    (hQ₂ : (Spin.quadPlus 2 (GaloisField 2 f)) a₂ = 0)
    (hpol : QuadraticMap.polar (Spin.quadPlus 2 (GaloisField 2 f)) a₁ a₂ = 0) :
    (∃ g : Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 f),
      siegelGroup (Spin.quadPlus 2 (GaloisField 2 f)) a₁ a₂ =
        siegelGroup (Spin.quadPlus 2 (GaloisField 2 f))
        ((bmsdop_r2_kappa f).symm (((g : Matrix (Fin 2) (Fin 2) (GaloisField 2 f)) * (!![1, 0; 0, 0]
            : Matrix (Fin 2) (Fin 2) (GaloisField 2 f)))))
        ((bmsdop_r2_kappa f).symm (((g : Matrix (Fin 2) (Fin 2) (GaloisField 2 f)) * (!![0, 1; 0, 0]
            : Matrix (Fin 2) (Fin 2) (GaloisField 2 f)))))) ∨
    (∃ h : Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 f),
      siegelGroup (Spin.quadPlus 2 (GaloisField 2 f)) a₁ a₂ =
        siegelGroup (Spin.quadPlus 2 (GaloisField 2 f))
        ((bmsdop_r2_kappa f).symm (((!![1, 0; 0, 0] : Matrix (Fin 2) (Fin 2) (GaloisField 2 f)) * (h
            : Matrix (Fin 2) (Fin 2) (GaloisField 2 f)))))
        ((bmsdop_r2_kappa f).symm (((!![0, 0; 1, 0] : Matrix (Fin 2) (Fin 2) (GaloisField 2 f)) * (h
            : Matrix (Fin 2) (Fin 2) (GaloisField 2 f)))))) := by
  rcases bmsdop_r2_lagrangian_image_or_kernel f hcard a₁ a₂ ha₁ ha₂ hlin hQ₁ hQ₂ hpol with
    himg | hker
  · exact Or.inl (bmsdop_r2_siegelGroup_family1 f a₁ a₂ hlin himg)
  · exact Or.inr (bmsdop_r2_siegelGroup_family2 f a₁ a₂ hlin hker)

private lemma bmsdop_r2_polar_family2_a (f : ℕ) (w : Fin 2 → (GaloisField 2 f))
    (X : Fin 2 ⊕ Fin 2 → (GaloisField 2 f)) :
    QuadraticMap.polar (Spin.quadPlus 2 (GaloisField 2 f)) X ((bmsdop_r2_kappa f).symm
        (Matrix.vecMulVec ![1, 0] w)) =
      (bmsdop_r2_kappa f X) 1 1 * w 0 - (bmsdop_r2_kappa f X) 1 0 * w 1 := by
  rw [bmsdop_r2_polar_rank1]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.head_fin_const,
    mul_one, mul_zero, add_zero, zero_mul, sub_zero]
  ring

private lemma bmsdop_r2_polar_family2_b (f : ℕ) (w : Fin 2 → (GaloisField 2 f))
    (X : Fin 2 ⊕ Fin 2 → (GaloisField 2 f)) :
    QuadraticMap.polar (Spin.quadPlus 2 (GaloisField 2 f)) X ((bmsdop_r2_kappa f).symm
        (Matrix.vecMulVec ![0, 1] w)) =
      (bmsdop_r2_kappa f X) 0 0 * w 1 - (bmsdop_r2_kappa f X) 0 1 * w 0 := by
  rw [bmsdop_r2_polar_rank1]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.head_fin_const,
    mul_one, mul_zero, add_zero, zero_mul, sub_zero]
  ring

private lemma bmsdop_r2_eichler_apply_family2 (f : ℕ) (w : Fin 2 → (GaloisField 2 f)) (c :
    (GaloisField 2 f))
    (X : Fin 2 ⊕ Fin 2 → (GaloisField 2 f)) :
    (bmsdop_r2_kappa f) (CFSG.ClassicalGroups.Orthogonal.eichler (Spin.quadPlus 2 (GaloisField 2 f))
        ((bmsdop_r2_kappa f).symm (Matrix.vecMulVec ![1, 0] w)) (c • ((bmsdop_r2_kappa f).symm
            (Matrix.vecMulVec ![0, 1] w))) X) =
      (bmsdop_r2_kappa f X) +
        c • (QuadraticMap.polar (Spin.quadPlus 2 (GaloisField 2 f)) X ((bmsdop_r2_kappa f).symm
            (Matrix.vecMulVec ![1, 0] w))) • Matrix.vecMulVec ![0, 1] w -
        c • (QuadraticMap.polar (Spin.quadPlus 2 (GaloisField 2 f)) X ((bmsdop_r2_kappa f).symm
            (Matrix.vecMulVec ![0, 1] w))) • Matrix.vecMulVec ![1, 0] w := by
  have hQ : (Spin.quadPlus 2 (GaloisField 2 f)) ((bmsdop_r2_kappa f).symm (Matrix.vecMulVec ![1, 0]
      w)) = 0 := by
    rw [← bmsdop_r2_kappa_det, LinearEquiv.apply_symm_apply, Matrix.det_vecMulVec]
  have hQ2 : (Spin.quadPlus 2 (GaloisField 2 f)) ((bmsdop_r2_kappa f).symm (Matrix.vecMulVec ![0, 1]
      w)) = 0 := by
    rw [← bmsdop_r2_kappa_det, LinearEquiv.apply_symm_apply, Matrix.det_vecMulVec]
  have hpol : QuadraticMap.polar (Spin.quadPlus 2 (GaloisField 2 f)) ((bmsdop_r2_kappa f).symm
      (Matrix.vecMulVec ![1, 0] w)) (c • ((bmsdop_r2_kappa f).symm (Matrix.vecMulVec ![0, 1] w))) =
          0 := by
    rw [QuadraticMap.polar_smul_right, QuadraticMap.polar_comm, bmsdop_r2_polar_rank1]
    simp only [LinearEquiv.apply_symm_apply, Matrix.vecMulVec, Matrix.of_apply,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.head_fin_const,
      mul_one, mul_zero, add_zero, zero_mul, sub_zero]
    ring
  rw [CFSG.ClassicalGroups.Orthogonal.eichler_apply hQ hpol X]
  simp only [map_add, map_sub, map_smul, LinearEquiv.apply_symm_apply, hQ2,
    QuadraticMap.map_smul, QuadraticMap.polar_smul_right, smul_eq_mul]
  rw [bmsdop_r2_polar_family2_a, bmsdop_r2_polar_family2_b]
  simp only [Matrix.vecMulVec, Matrix.of_apply]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp only [Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, Matrix.of_apply,
      Fin.reduceFinMk, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      Matrix.head_fin_const] <;> ring_nf

private lemma bmsdop_r2_matrix_identity_family2 (f : ℕ) (w : Fin 2 → (GaloisField 2 f)) (c :
    (GaloisField 2 f))
    (Y : Matrix (Fin 2) (Fin 2) (GaloisField 2 f)) :
    Y + c • (Y 1 1 * w 0 - Y 1 0 * w 1) • Matrix.vecMulVec ![0, 1] w -
        c • (Y 0 0 * w 1 - Y 0 1 * w 0) • Matrix.vecMulVec ![1, 0] w =
      Y * (1 + c • (!![w 1 * w 0, w 1 * w 1; w 0 * w 0, w 0 * w 1] : Matrix (Fin 2) (Fin 2)
          (GaloisField 2 f))) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp only [Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, Matrix.mul_apply,
      Matrix.one_apply, Matrix.vecMulVec, Matrix.of_apply, Fin.sum_univ_two,
      Fin.reduceFinMk, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      Matrix.head_fin_const, sub_eq_add_neg, CharTwo.neg_eq] <;> norm_num <;> ring_nf

private lemma bmsdop_r2_kappa_eichler_family2 (f : ℕ) (w : Fin 2 → (GaloisField 2 f)) (c :
    (GaloisField 2 f))
    (X : Fin 2 ⊕ Fin 2 → (GaloisField 2 f)) :
    (bmsdop_r2_kappa f) (CFSG.ClassicalGroups.Orthogonal.eichler (Spin.quadPlus 2 (GaloisField 2 f))
        ((bmsdop_r2_kappa f).symm (Matrix.vecMulVec ![1, 0] w))
        (c • (bmsdop_r2_kappa f).symm (Matrix.vecMulVec ![0, 1] w)) X) =
      ((bmsdop_r2_kappa f) X) *
        (1 + c • (!![w 1 * w 0, w 1 * w 1; w 0 * w 0, w 0 * w 1] : Matrix (Fin 2) (Fin 2)
            (GaloisField 2 f))) := by
  rw [bmsdop_r2_eichler_apply_family2, bmsdop_r2_polar_family2_a, bmsdop_r2_polar_family2_b,
    bmsdop_r2_matrix_identity_family2]

private lemma bmsdop_r2_family2_sq (f : ℕ) (w : Fin 2 → (GaloisField 2 f)) (c : (GaloisField 2 f)) :
    (1 + c • (!![w 1 * w 0, w 1 * w 1; w 0 * w 0, w 0 * w 1] : Matrix (Fin 2) (Fin 2) (GaloisField 2
        f))) * (1 + c • (!![w 1 * w 0, w 1 * w 1; w 0 * w 0, w 0 * w 1] : Matrix (Fin 2) (Fin 2)
            (GaloisField 2 f))) = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp only [Matrix.mul_apply, Matrix.add_apply, Matrix.one_apply, Matrix.smul_apply,
      Matrix.zero_apply, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons, Matrix.head_fin_const, Matrix.of_apply, Fin.reduceFinMk] <;>
    norm_num <;> ring_nf <;>
    rw [show (2 : GaloisField 2 f) = 0 from CharP.cast_eq_zero _ 2, mul_zero] <;> ring

private lemma bmsdop_r2_family2_det (f : ℕ) (w : Fin 2 → (GaloisField 2 f)) (c : (GaloisField 2 f))
    :
    (1 + c • (!![w 1 * w 0, w 1 * w 1; w 0 * w 0, w 0 * w 1] : Matrix (Fin 2) (Fin 2) (GaloisField 2
        f))).det = 1 := by
  rw [Matrix.det_fin_two]
  simp only [Matrix.add_apply, Matrix.one_apply, Matrix.smul_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.head_fin_const, Matrix.of_apply,
    Fin.reduceFinMk] <;> norm_num <;> ring_nf <;>
  rw [show (2 : GaloisField 2 f) = 0 from CharP.cast_eq_zero _ 2, mul_zero] <;> ring

private lemma bmsdop_r2_family2_eichler_mem_rhoR (f : ℕ) (w : Fin 2 → (GaloisField 2 f)) (c :
    (GaloisField 2 f)) :
    CFSG.ClassicalGroups.Orthogonal.eichler (Spin.quadPlus 2 (GaloisField 2 f)) ((bmsdop_r2_kappa
        f).symm (Matrix.vecMulVec ![1, 0] w)) (c • ((bmsdop_r2_kappa f).symm (Matrix.vecMulVec ![0,
            1] w))) ∈
      (bmsdop_r2_rhoR f).range.map (Subgroup.subtype
          (CFSG.RankThree.OrthogonalInvolutions.omegaGroup (Spin.quadPlus 2 (GaloisField 2 f))
              (Spin.nondegenerate_polarBilin_quadPlus 2 (GaloisField 2 f)))) := by
  let g : Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 f) :=
    ⟨1 + c • (!![w 1 * w 0, w 1 * w 1; w 0 * w 0, w 0 * w 1] : Matrix (Fin 2) (Fin 2) (GaloisField 2
        f)), bmsdop_r2_family2_det f w c⟩
  have hg : (g : Matrix (Fin 2) (Fin 2) (GaloisField 2 f)) = 1 + c • (!![w 1 * w 0, w 1 * w 1; w 0 *
      w 0, w 0 * w 1] : Matrix (Fin 2) (Fin 2) (GaloisField 2 f)) := rfl
  refine Subgroup.mem_map.mpr
    ⟨(⟨bmsdop_r2_rhoR f g, ⟨g, rfl⟩⟩ : (bmsdop_r2_rhoR f).range), ?_, ?_⟩
  · exact (⟨bmsdop_r2_rhoR f g, ⟨g, rfl⟩⟩ : (bmsdop_r2_rhoR f).range).property
  · apply LinearEquiv.ext
    intro X
    change bmsdop_r2_rhoRFun f g X =
      (CFSG.ClassicalGroups.Orthogonal.eichler (Spin.quadPlus 2 (GaloisField 2 f)) ((bmsdop_r2_kappa
          f).symm (Matrix.vecMulVec ![1, 0] w)) (c • ((bmsdop_r2_kappa f).symm (Matrix.vecMulVec
              ![0, 1] w))) X)
    rw [bmsdop_r2_rhoRFun_apply]
    apply (bmsdop_r2_kappa f).injective
    rw [LinearEquiv.apply_symm_apply]
    have hgg : g * g = 1 := by
      apply Subtype.ext
      rw [Matrix.SpecialLinearGroup.coe_mul, hg, bmsdop_r2_family2_sq,
        Matrix.SpecialLinearGroup.coe_one]
    rw [show g⁻¹ = g from inv_eq_of_mul_eq_one_right hgg, hg,
      bmsdop_r2_kappa_eichler_family2]

private lemma bmsdop_r2_siegelGroup_family2_le_rhoR (f : ℕ) (w : Fin 2 → (GaloisField 2 f)) :
    siegelGroup (Spin.quadPlus 2 (GaloisField 2 f)) ((bmsdop_r2_kappa f).symm (Matrix.vecMulVec ![1,
        0] w))
        ((bmsdop_r2_kappa f).symm (Matrix.vecMulVec ![0, 1] w)) ≤
      (bmsdop_r2_rhoR f).range.map (Subgroup.subtype
          (CFSG.RankThree.OrthogonalInvolutions.omegaGroup (Spin.quadPlus 2 (GaloisField 2 f))
              (Spin.nondegenerate_polarBilin_quadPlus 2 (GaloisField 2 f)))) := by
  rw [siegelGroup, Subgroup.closure_le]
  rintro x ⟨c, rfl⟩
  exact bmsdop_r2_family2_eichler_mem_rhoR f w c

private lemma bmsdop_r2_map_inf_bot (f : ℕ) (hcard : Nat.card (GaloisField 2 f) ≠ 2) :
    (bmsdop_r2_rhoL f).range.map (Subgroup.subtype (CFSG.RankThree.OrthogonalInvolutions.omegaGroup
        (Spin.quadPlus 2 (GaloisField 2 f)) (Spin.nondegenerate_polarBilin_quadPlus 2 (GaloisField 2
            f)))) ⊓
        (bmsdop_r2_rhoR f).range.map (Subgroup.subtype
            (CFSG.RankThree.OrthogonalInvolutions.omegaGroup (Spin.quadPlus 2 (GaloisField 2 f))
                (Spin.nondegenerate_polarBilin_quadPlus 2 (GaloisField 2 f)))) = ⊥ := by
  rw [eq_bot_iff]
  intro g hg
  obtain ⟨hgL, hgR⟩ := Subgroup.mem_inf.mp hg
  obtain ⟨aL, haL, hEqL⟩ := Subgroup.mem_map.mp hgL
  obtain ⟨aR, haR, hEqR⟩ := Subgroup.mem_map.mp hgR
  have hsub : Subgroup.subtype (CFSG.RankThree.OrthogonalInvolutions.omegaGroup (Spin.quadPlus 2
      (GaloisField 2 f)) (Spin.nondegenerate_polarBilin_quadPlus 2 (GaloisField 2 f))) aL =
          Subgroup.subtype (CFSG.RankThree.OrthogonalInvolutions.omegaGroup (Spin.quadPlus 2
              (GaloisField 2 f)) (Spin.nondegenerate_polarBilin_quadPlus 2 (GaloisField 2 f))) aR :=
                  by
    rw [hEqL, hEqR]
  have haeq : aL = aR := Subgroup.subtype_injective (CFSG.RankThree.OrthogonalInvolutions.omegaGroup
      (Spin.quadPlus 2 (GaloisField 2 f)) (Spin.nondegenerate_polarBilin_quadPlus 2 (GaloisField 2
          f))) hsub
  have hbot : aL ∈ (⊥ : Subgroup (CFSG.RankThree.OrthogonalInvolutions.omegaGroup (Spin.quadPlus 2
      (GaloisField 2 f)) (Spin.nondegenerate_polarBilin_quadPlus 2 (GaloisField 2 f)))) := by
    rw [← (bmsdop_r2_split f hcard).2.2.2.2.1]
    exact ⟨haL, haeq ▸ haR⟩
  rw [Subgroup.mem_bot] at hbot
  rw [← hEqL, hbot]
  rfl

private lemma bmsdop_r2_family2_M_ne_zero (f : ℕ) (w : Fin 2 → (GaloisField 2 f)) (hw : w ≠ 0) :
    (!![w 1 * w 0, w 1 * w 1; w 0 * w 0, w 0 * w 1] : Matrix (Fin 2) (Fin 2) (GaloisField 2 f)) ≠ 0
        := by
  intro hM
  have h1 : w 1 = 0 := by
    have h := congrFun (congrFun hM 0) 1
    simp only [Matrix.zero_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      Matrix.of_apply] at h
    exact mul_self_eq_zero.mp h
  have h0 : w 0 = 0 := by
    have h := congrFun (congrFun hM 1) 0
    simp only [Matrix.zero_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      Matrix.of_apply] at h
    exact mul_self_eq_zero.mp h
  exact hw (funext fun i => by fin_cases i <;> simp [h0, h1])

private lemma bmsdop_r2_family2_eichler_one_apply (f : ℕ) (w : Fin 2 → (GaloisField 2 f))
    (X : Fin 2 ⊕ Fin 2 → (GaloisField 2 f)) (h1 : CFSG.ClassicalGroups.Orthogonal.eichler
        (Spin.quadPlus 2 (GaloisField 2 f)) ((bmsdop_r2_kappa f).symm (Matrix.vecMulVec ![1, 0] w))
            ((bmsdop_r2_kappa f).symm (Matrix.vecMulVec ![0, 1] w)) = 1) :
    CFSG.ClassicalGroups.Orthogonal.eichler (Spin.quadPlus 2 (GaloisField 2 f)) ((bmsdop_r2_kappa
        f).symm (Matrix.vecMulVec ![1, 0] w)) ((bmsdop_r2_kappa f).symm (Matrix.vecMulVec ![0, 1]
            w)) X = X := by
  rw [congrArg (fun g : (Fin 2 ⊕ Fin 2 → (GaloisField 2 f)) ≃ₗ[(GaloisField 2 f)] (Fin 2 ⊕ Fin 2 →
      (GaloisField 2 f)) => g X) h1]
  rfl

private lemma bmsdop_r2_family2_Q_U1_zero (f : ℕ) (w : Fin 2 → (GaloisField 2 f)) :
    (Spin.quadPlus 2 (GaloisField 2 f)) ((bmsdop_r2_kappa f).symm (Matrix.vecMulVec ![1, 0] w)) = 0
        := by
  rw [← bmsdop_r2_kappa_det, LinearEquiv.apply_symm_apply, Matrix.det_vecMulVec]

private lemma bmsdop_r2_family2_Q_U2_zero (f : ℕ) (w : Fin 2 → (GaloisField 2 f)) :
    (Spin.quadPlus 2 (GaloisField 2 f)) ((bmsdop_r2_kappa f).symm (Matrix.vecMulVec ![0, 1] w)) = 0
        := by
  rw [← bmsdop_r2_kappa_det, LinearEquiv.apply_symm_apply, Matrix.det_vecMulVec]

private lemma bmsdop_r2_family2_polar_one (f : ℕ) (w : Fin 2 → (GaloisField 2 f)) :
    QuadraticMap.polar (Spin.quadPlus 2 (GaloisField 2 f)) ((bmsdop_r2_kappa f).symm
        (Matrix.vecMulVec ![1, 0] w)) (1 • ((bmsdop_r2_kappa f).symm (Matrix.vecMulVec ![0, 1] w)))
            = 0 := by
  rw [one_smul, QuadraticMap.polar_comm, bmsdop_r2_polar_rank1]
  simp only [LinearEquiv.apply_symm_apply, Matrix.vecMulVec, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.head_fin_const,
    mul_one, mul_zero, add_zero, zero_mul, sub_zero]
  ring

private lemma bmsdop_r2_family2_eichler_apply_one (f : ℕ) (w : Fin 2 → (GaloisField 2 f))
    (X : Fin 2 ⊕ Fin 2 → (GaloisField 2 f)) :
    (bmsdop_r2_kappa f) (CFSG.ClassicalGroups.Orthogonal.eichler (Spin.quadPlus 2 (GaloisField 2 f))
        ((bmsdop_r2_kappa f).symm (Matrix.vecMulVec ![1, 0] w)) (1 • ((bmsdop_r2_kappa f).symm
            (Matrix.vecMulVec ![0, 1] w))) X) =
      (bmsdop_r2_kappa f) X +
        (((bmsdop_r2_kappa f) X) 1 1 * w 0 - ((bmsdop_r2_kappa f) X) 1 0 * w 1) • Matrix.vecMulVec
            ![0, 1] w -
        (((bmsdop_r2_kappa f) X) 0 0 * w 1 - ((bmsdop_r2_kappa f) X) 0 1 * w 0) • Matrix.vecMulVec
            ![1, 0] w := by
  have hQ := bmsdop_r2_family2_Q_U1_zero f w
  have hQ2 := bmsdop_r2_family2_Q_U2_zero f w
  have hpol := bmsdop_r2_family2_polar_one f w
  rw [CFSG.ClassicalGroups.Orthogonal.eichler_apply hQ hpol X]
  simp only [map_add, map_sub, map_smul, LinearEquiv.apply_symm_apply, one_smul, hQ2,
    QuadraticMap.map_smul, QuadraticMap.polar_smul_right, smul_eq_mul,
    bmsdop_r2_polar_family2_a, bmsdop_r2_polar_family2_b, zero_mul, add_zero]

private lemma bmsdop_r2_family2_mul_one_add_M_of_eichler_eq_one (f : ℕ) (w : Fin 2 → (GaloisField 2
    f))
    (X : Fin 2 ⊕ Fin 2 → (GaloisField 2 f)) (h1 : CFSG.ClassicalGroups.Orthogonal.eichler
        (Spin.quadPlus 2 (GaloisField 2 f)) ((bmsdop_r2_kappa f).symm (Matrix.vecMulVec ![1, 0] w))
            ((bmsdop_r2_kappa f).symm (Matrix.vecMulVec ![0, 1] w)) = 1) :
    (bmsdop_r2_kappa f) X * (1 + 1 • (!![w 1 * w 0, w 1 * w 1; w 0 * w 0, w 0 * w 1] : Matrix (Fin
        2) (Fin 2) (GaloisField 2 f))) = (bmsdop_r2_kappa f) X := by
  have hmi : (bmsdop_r2_kappa f) X +
        (((bmsdop_r2_kappa f) X) 1 1 * w 0 - ((bmsdop_r2_kappa f) X) 1 0 * w 1) • Matrix.vecMulVec
            ![0, 1] w -
        (((bmsdop_r2_kappa f) X) 0 0 * w 1 - ((bmsdop_r2_kappa f) X) 0 1 * w 0) • Matrix.vecMulVec
            ![1, 0] w =
      (bmsdop_r2_kappa f) X * (1 + 1 • (!![w 1 * w 0, w 1 * w 1; w 0 * w 0, w 0 * w 1] : Matrix (Fin
          2) (Fin 2) (GaloisField 2 f))) := by
    simpa only [one_smul] using bmsdop_r2_matrix_identity_family2 f w 1 (((bmsdop_r2_kappa f) X))
  have hX : CFSG.ClassicalGroups.Orthogonal.eichler (Spin.quadPlus 2 (GaloisField 2 f))
      ((bmsdop_r2_kappa f).symm (Matrix.vecMulVec ![1, 0] w))
      (1 • ((bmsdop_r2_kappa f).symm (Matrix.vecMulVec ![0, 1] w))) X = X := by
    rw [one_smul]
    exact bmsdop_r2_family2_eichler_one_apply f w X h1
  have h := congrArg (bmsdop_r2_kappa f) hX
  rw [bmsdop_r2_family2_eichler_apply_one] at h
  rw [← hmi]
  exact h

private lemma bmsdop_r2_family2_mul_M_zero_of_mul_one_add_M (f : ℕ) (w : Fin 2 → (GaloisField 2 f))
    (X : Fin 2 ⊕ Fin 2 → (GaloisField 2 f))
    (h : (bmsdop_r2_kappa f) X * (1 + 1 • (!![w 1 * w 0, w 1 * w 1; w 0 * w 0, w 0 * w 1] : Matrix
        (Fin 2) (Fin 2) (GaloisField 2 f))) = (bmsdop_r2_kappa f) X) :
    (bmsdop_r2_kappa f) X * (!![w 1 * w 0, w 1 * w 1; w 0 * w 0, w 0 * w 1] : Matrix (Fin 2) (Fin 2)
        (GaloisField 2 f)) = 0 := by
  rw [Matrix.mul_add, Matrix.mul_one, Matrix.mul_smul, one_smul] at h
  exact add_left_cancel (h.trans (add_zero _).symm)

private lemma bmsdop_r2_family2_mul_M_eq_zero (f : ℕ) (w : Fin 2 → (GaloisField 2 f))
    (X : Fin 2 ⊕ Fin 2 → (GaloisField 2 f)) (h1 : CFSG.ClassicalGroups.Orthogonal.eichler
        (Spin.quadPlus 2 (GaloisField 2 f)) ((bmsdop_r2_kappa f).symm (Matrix.vecMulVec ![1, 0] w))
            ((bmsdop_r2_kappa f).symm (Matrix.vecMulVec ![0, 1] w)) = 1) :
    (bmsdop_r2_kappa f) X * (!![w 1 * w 0, w 1 * w 1; w 0 * w 0, w 0 * w 1] : Matrix (Fin 2) (Fin 2)
        (GaloisField 2 f)) = 0 := by
  exact bmsdop_r2_family2_mul_M_zero_of_mul_one_add_M f w X
    (bmsdop_r2_family2_mul_one_add_M_of_eichler_eq_one f w X h1)

private lemma bmsdop_r2_family2_E11_mul_M_eq_zero (f : ℕ) (w : Fin 2 → (GaloisField 2 f)) (h1 :
    CFSG.ClassicalGroups.Orthogonal.eichler (Spin.quadPlus 2 (GaloisField 2 f)) ((bmsdop_r2_kappa
        f).symm (Matrix.vecMulVec ![1, 0] w)) ((bmsdop_r2_kappa f).symm (Matrix.vecMulVec ![0, 1]
            w)) = 1) :
    (!![1, 0; 0, 0] : Matrix (Fin 2) (Fin 2) (GaloisField 2 f)) * (!![w 1 * w 0, w 1 * w 1; w 0 * w
        0, w 0 * w 1] : Matrix (Fin 2) (Fin 2) (GaloisField 2 f)) = 0 := by
  have h := bmsdop_r2_family2_mul_M_eq_zero f w
    ((bmsdop_r2_kappa f).symm (!![1, 0; 0, 0] : Matrix (Fin 2) (Fin 2) (GaloisField 2 f))) h1
  simpa only [LinearEquiv.apply_symm_apply] using h

private lemma bmsdop_r2_family2_E22_mul_M_eq_zero (f : ℕ) (w : Fin 2 → (GaloisField 2 f)) (h1 :
    CFSG.ClassicalGroups.Orthogonal.eichler (Spin.quadPlus 2 (GaloisField 2 f)) ((bmsdop_r2_kappa
        f).symm (Matrix.vecMulVec ![1, 0] w)) ((bmsdop_r2_kappa f).symm (Matrix.vecMulVec ![0, 1]
            w)) = 1) :
    (!![0, 0; 0, 1] : Matrix (Fin 2) (Fin 2) (GaloisField 2 f)) * (!![w 1 * w 0, w 1 * w 1; w 0 * w
        0, w 0 * w 1] : Matrix (Fin 2) (Fin 2) (GaloisField 2 f)) = 0 := by
  have h := bmsdop_r2_family2_mul_M_eq_zero f w
    ((bmsdop_r2_kappa f).symm (!![0, 0; 0, 1] : Matrix (Fin 2) (Fin 2) (GaloisField 2 f))) h1
  simpa only [LinearEquiv.apply_symm_apply] using h

private lemma bmsdop_r2_family2_M_eq_zero_of_E11_E22 (f : ℕ) (w : Fin 2 → (GaloisField 2 f))
    (hE1 : (!![1, 0; 0, 0] : Matrix (Fin 2) (Fin 2) (GaloisField 2 f)) * (!![w 1 * w 0, w 1 * w 1; w
        0 * w 0, w 0 * w 1] : Matrix (Fin 2) (Fin 2) (GaloisField 2 f)) = 0)
    (hE2 : (!![0, 0; 0, 1] : Matrix (Fin 2) (Fin 2) (GaloisField 2 f)) * (!![w 1 * w 0, w 1 * w 1; w
        0 * w 0, w 0 * w 1] : Matrix (Fin 2) (Fin 2) (GaloisField 2 f)) = 0) :
    (!![w 1 * w 0, w 1 * w 1; w 0 * w 0, w 0 * w 1] : Matrix (Fin 2) (Fin 2) (GaloisField 2 f)) = 0
        := by
  ext i j
  fin_cases i <;> fin_cases j
  · have h := congrFun (congrFun hE1 0) 0
    simpa [Matrix.mul_apply, Matrix.zero_apply, Fin.sum_univ_two, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.head_cons, Matrix.head_fin_const, Matrix.of_apply] using h
  · have h := congrFun (congrFun hE1 0) 1
    simpa [Matrix.mul_apply, Matrix.zero_apply, Fin.sum_univ_two, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.head_cons, Matrix.head_fin_const, Matrix.of_apply] using h
  · have h := congrFun (congrFun hE2 1) 0
    simpa [Matrix.mul_apply, Matrix.zero_apply, Fin.sum_univ_two, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.head_cons, Matrix.head_fin_const, Matrix.of_apply] using h
  · have h := congrFun (congrFun hE2 1) 1
    simpa [Matrix.mul_apply, Matrix.zero_apply, Fin.sum_univ_two, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.head_cons, Matrix.head_fin_const, Matrix.of_apply] using h

private lemma bmsdop_r2_family2_M_eq_zero_of_eichler_eq_one (f : ℕ) (w : Fin 2 → (GaloisField 2 f))
    (h1 : CFSG.ClassicalGroups.Orthogonal.eichler (Spin.quadPlus 2 (GaloisField 2 f))
        ((bmsdop_r2_kappa f).symm (Matrix.vecMulVec ![1, 0] w)) ((bmsdop_r2_kappa f).symm
            (Matrix.vecMulVec ![0, 1] w)) = 1) :
    (!![w 1 * w 0, w 1 * w 1; w 0 * w 0, w 0 * w 1] : Matrix (Fin 2) (Fin 2) (GaloisField 2 f)) = 0
        := by
  exact bmsdop_r2_family2_M_eq_zero_of_E11_E22 f w
    (bmsdop_r2_family2_E11_mul_M_eq_zero f w h1)
    (bmsdop_r2_family2_E22_mul_M_eq_zero f w h1)

private lemma bmsdop_r2_eichler_family2_ne_one (f : ℕ) (w : Fin 2 → (GaloisField 2 f))
    (hw : w ≠ 0) :
    CFSG.ClassicalGroups.Orthogonal.eichler (Spin.quadPlus 2 (GaloisField 2 f)) ((bmsdop_r2_kappa
        f).symm (Matrix.vecMulVec ![1, 0] w))
        ((bmsdop_r2_kappa f).symm (Matrix.vecMulVec ![0, 1] w)) ≠ 1 := by
  exact fun h1 => bmsdop_r2_family2_M_ne_zero f w hw
    (bmsdop_r2_family2_M_eq_zero_of_eichler_eq_one f w h1)

private lemma bmsdop_r2_lagrangian_family2_excl (f : ℕ)
    (hcard : Nat.card (GaloisField 2 f) ≠ 2)
    (a₁ a₂ : Fin 2 ⊕ Fin 2 → (GaloisField 2 f))
    (ha₁ : a₁ ≠ 0) (ha₂ : a₂ ≠ 0)
    (hlin : LinearIndependent (GaloisField 2 f) ![a₁, a₂])
    (hQ₁ : (Spin.quadPlus 2 (GaloisField 2 f)) a₁ = 0)
    (hQ₂ : (Spin.quadPlus 2 (GaloisField 2 f)) a₂ = 0)
    (hpol : QuadraticMap.polar (Spin.quadPlus 2 (GaloisField 2 f)) a₁ a₂ = 0)
    (hle : siegelGroup (Spin.quadPlus 2 (GaloisField 2 f)) a₁ a₂ ≤
      (bmsdop_r2_rhoL f).range.map (Subgroup.subtype
        (CFSG.RankThree.OrthogonalInvolutions.omegaGroup (Spin.quadPlus 2 (GaloisField 2 f))
          (Spin.nondegenerate_polarBilin_quadPlus 2 (GaloisField 2 f)))))
    (h : Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 f))
    (hh : siegelGroup (Spin.quadPlus 2 (GaloisField 2 f)) a₁ a₂ =
      siegelGroup (Spin.quadPlus 2 (GaloisField 2 f))
        ((bmsdop_r2_kappa f).symm (((!![1, 0; 0, 0] : Matrix (Fin 2) (Fin 2) (GaloisField 2 f)) * (h
            : Matrix (Fin 2) (Fin 2) (GaloisField 2 f)))))
        ((bmsdop_r2_kappa f).symm (((!![0, 0; 1, 0] : Matrix (Fin 2) (Fin 2) (GaloisField 2 f)) * (h
            : Matrix (Fin 2) (Fin 2) (GaloisField 2 f)))))) :
    False := by
  have hw : (fun j => (↑h : Matrix (Fin 2) (Fin 2) (GaloisField 2 f)) 0 j) ≠ 0 := by
    intro h0
    have hdet : (↑h : Matrix (Fin 2) (Fin 2) (GaloisField 2 f)).det = 1 :=
        Matrix.SpecialLinearGroup.det_coe h
    rw [Matrix.det_fin_two] at hdet
    have h00 : (↑h : Matrix (Fin 2) (Fin 2) (GaloisField 2 f)) 0 0 = 0 := by
      simpa using congrFun h0 0
    have h01 : (↑h : Matrix (Fin 2) (Fin 2) (GaloisField 2 f)) 0 1 = 0 := by
      simpa using congrFun h0 1
    simp only [h00, h01, zero_mul, sub_zero, neg_zero] at hdet
    exact zero_ne_one hdet
  have hE1 : (!![1, 0; 0, 0] : Matrix (Fin 2) (Fin 2) (GaloisField 2 f)) * (↑h : Matrix (Fin 2) (Fin
      2) (GaloisField 2 f)) = Matrix.vecMulVec ![1, 0] (fun j => (↑h : Matrix (Fin 2) (Fin 2)
          (GaloisField 2 f)) 0 j) := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.vecMulVec, Matrix.of_apply]
  have hE2 : (!![0, 0; 1, 0] : Matrix (Fin 2) (Fin 2) (GaloisField 2 f)) * (↑h : Matrix (Fin 2) (Fin
      2) (GaloisField 2 f)) = Matrix.vecMulVec ![0, 1] (fun j => (↑h : Matrix (Fin 2) (Fin 2)
          (GaloisField 2 f)) 0 j) := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.vecMulVec, Matrix.of_apply]
  have hleR : siegelGroup (Spin.quadPlus 2 (GaloisField 2 f)) a₁ a₂ ≤ (bmsdop_r2_rhoR f).range.map
      (Subgroup.subtype (CFSG.RankThree.OrthogonalInvolutions.omegaGroup (Spin.quadPlus 2
          (GaloisField 2 f)) (Spin.nondegenerate_polarBilin_quadPlus 2 (GaloisField 2 f)))) := by
    rw [hh, hE1, hE2]
    exact bmsdop_r2_siegelGroup_family2_le_rhoR f (fun j => (↑h : Matrix (Fin 2) (Fin 2)
        (GaloisField 2 f)) 0 j)
  have hbot : siegelGroup (Spin.quadPlus 2 (GaloisField 2 f)) a₁ a₂ ≤ ⊥ := by
    rw [← bmsdop_r2_map_inf_bot f hcard]
    exact le_inf hle hleR
  have hmem : CFSG.ClassicalGroups.Orthogonal.eichler (Spin.quadPlus 2 (GaloisField 2 f))
      ((bmsdop_r2_kappa f).symm ((!![1, 0; 0, 0] : Matrix (Fin 2) (Fin 2) (GaloisField 2 f)) * (↑h :
          Matrix (Fin 2) (Fin 2) (GaloisField 2 f))))
      ((bmsdop_r2_kappa f).symm ((!![0, 0; 1, 0] : Matrix (Fin 2) (Fin 2) (GaloisField 2 f)) * (↑h :
          Matrix (Fin 2) (Fin 2) (GaloisField 2 f)))) ∈ siegelGroup (Spin.quadPlus 2 (GaloisField 2
              f)) a₁ a₂ := by
    rw [hh]
    exact Subgroup.subset_closure ⟨1, by rw [one_smul]⟩
  have hone : CFSG.ClassicalGroups.Orthogonal.eichler (Spin.quadPlus 2 (GaloisField 2 f))
      ((bmsdop_r2_kappa f).symm ((!![1, 0; 0, 0] : Matrix (Fin 2) (Fin 2) (GaloisField 2 f)) * (↑h :
          Matrix (Fin 2) (Fin 2) (GaloisField 2 f))))
      ((bmsdop_r2_kappa f).symm ((!![0, 0; 1, 0] : Matrix (Fin 2) (Fin 2) (GaloisField 2 f)) * (↑h :
          Matrix (Fin 2) (Fin 2) (GaloisField 2 f)))) = 1 := by
    have := hbot hmem
    simpa using this
  rw [hE1, hE2] at hone
  exact bmsdop_r2_eichler_family2_ne_one f (fun j => (↑h : Matrix (Fin 2) (Fin 2) (GaloisField 2 f))
      0 j) hw hone

private lemma bmsdop_r2_closure_Qstd_left_classify (f : ℕ)
    (hcard : Nat.card (GaloisField 2 f) ≠ 2)
    (a₁ a₂ : Fin 2 ⊕ Fin 2 → (GaloisField 2 f))
    (ha₁ : a₁ ≠ 0) (ha₂ : a₂ ≠ 0)
    (hlin : LinearIndependent (GaloisField 2 f) ![a₁, a₂])
    (hQ₁ : (Spin.quadPlus 2 (GaloisField 2 f)) a₁ = 0)
    (hQ₂ : (Spin.quadPlus 2 (GaloisField 2 f)) a₂ = 0)
    (hpol : QuadraticMap.polar (Spin.quadPlus 2 (GaloisField 2 f)) a₁ a₂ = 0)
    (hle : siegelGroup (Spin.quadPlus 2 (GaloisField 2 f)) a₁ a₂ ≤
      (bmsdop_r2_rhoL f).range.map (Subgroup.subtype
          (CFSG.RankThree.OrthogonalInvolutions.omegaGroup (Spin.quadPlus 2 (GaloisField 2 f))
          (Spin.nondegenerate_polarBilin_quadPlus 2 (GaloisField 2 f))))) :
    ∃ g : Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 f),
      siegelGroup (Spin.quadPlus 2 (GaloisField 2 f)) a₁ a₂ =
        siegelGroup (Spin.quadPlus 2 (GaloisField 2 f))
          ((bmsdop_r2_kappa f).symm ((g : Matrix (Fin 2) (Fin 2) (GaloisField 2 f)) * (!![1, 0; 0,
              0] : Matrix (Fin 2) (Fin 2) (GaloisField 2 f))))
          ((bmsdop_r2_kappa f).symm ((g : Matrix (Fin 2) (Fin 2) (GaloisField 2 f)) * (!![0, 1; 0,
              0] : Matrix (Fin 2) (Fin 2) (GaloisField 2 f)))) := by
  rcases bmsdop_r2_lagrangian_dichotomy f hcard a₁ a₂ ha₁ ha₂ hlin hQ₁ hQ₂ hpol with ⟨g, hg⟩ | ⟨h,
      hh⟩
  · exact ⟨g, hg⟩
  · exact (bmsdop_r2_lagrangian_family2_excl f hcard a₁ a₂ ha₁ ha₂ hlin hQ₁ hQ₂ hpol hle
      h hh).elim

private lemma bmsdop_r2_i0_mem_roots (f : ℕ) :
    (Pi.single (bmsdop_r2_i0 f) 1) ∈ (SpecialLinear.rootDatum 1 (GaloisField 2 f)).roots := by
  exact single_mem_roots (D := SpecialLinear.rootDatum 1 (GaloisField 2 f)) (bmsdop_r2_i0 f)

private lemma bmsdop_r2_i0_GGLongRoot (f : ℕ) (hcard : Nat.card (GaloisField 2 f) ≠ 2) :
    GGLongRoot (SpecialLinear.rootDatum 1 (GaloisField 2 f))
      (Pi.single (bmsdop_r2_i0 f) 1) :=
  bmsdop_r2_root_long f hcard

private lemma bmsdop_r2_omegaGroup_le_orthogonalGroup (f : ℕ) :
    (CFSG.RankThree.OrthogonalInvolutions.omegaGroup (Spin.quadPlus 2 (GaloisField 2 f))
        (Spin.nondegenerate_polarBilin_quadPlus 2 (GaloisField 2 f))) ≤
            (TauCeti.QuadraticMap.orthogonalGroup (Spin.quadPlus 2 (GaloisField 2 f))) := by
  intro x hx
  have hx' : x ∈ TauCeti.QuadraticMap.orthogonalGroup (Spin.quadPlus 2 (GaloisField 2 f)) :=
    (CFSG.RankThree.OrthogonalInvolutions.mem_omegaGroup.mp hx).1
  rw [TauCeti.QuadraticMap.mem_orthogonalGroup_iff] at hx' ⊢
  exact hx'

private lemma bmsdop_r2_rhoL_mem_orthogonalGroup (f : ℕ)
    (g : Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 f)) :
    ((bmsdop_r2_rhoL f g : (Fin 2 ⊕ Fin 2 → (GaloisField 2 f)) ≃ₗ[(GaloisField 2 f)] (Fin 2 ⊕ Fin 2
        → (GaloisField 2 f)))) ∈ (TauCeti.QuadraticMap.orthogonalGroup (Spin.quadPlus 2 (GaloisField
            2 f))) := by
  exact bmsdop_r2_omegaGroup_le_orthogonalGroup f (bmsdop_r2_rhoL f g).property

private lemma bmsdop_r2_siegelGroup_map_conj_eq (f : ℕ) (g : (Fin 2 ⊕ Fin 2 → (GaloisField 2 f))
    ≃ₗ[(GaloisField 2 f)] (Fin 2 ⊕ Fin 2 → (GaloisField 2 f)))
    (hg : g ∈ (TauCeti.QuadraticMap.orthogonalGroup (Spin.quadPlus 2 (GaloisField 2 f)))) (u w :
        (Fin 2 ⊕ Fin 2 → (GaloisField 2 f))) :
    Subgroup.map (MulEquiv.toMonoidHom (MulAut.conj g)) (siegelGroup (Spin.quadPlus 2 (GaloisField 2
        f)) u w) =
      siegelGroup (Spin.quadPlus 2 (GaloisField 2 f)) (g u) (g w) := by
  simpa only [MulEquiv.coe_toMonoidHom] using bmsdop_r2_siegelGroup_conj f g hg u w

private lemma bmsdop_r2_siegelGroup_family1_eq_conj (f : ℕ)
    (g : Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 f)) :
    siegelGroup (Spin.quadPlus 2 (GaloisField 2 f)) ((bmsdop_r2_kappa f).symm ((g : Matrix (Fin 2)
        (Fin 2) (GaloisField 2 f)) * (!![1, 0; 0, 0] : Matrix (Fin 2) (Fin 2) (GaloisField 2 f))))
        ((bmsdop_r2_kappa f).symm ((g : Matrix (Fin 2) (Fin 2) (GaloisField 2 f)) * (!![0, 1; 0, 0]
            : Matrix (Fin 2) (Fin 2) (GaloisField 2 f)))) =
      (siegelGroup (Spin.quadPlus 2 (GaloisField 2 f)) (bmsdop_r2_e11 f) (bmsdop_r2_e12 f)).map
        (MulAut.conj (((bmsdop_r2_rhoL f g : (Fin 2 ⊕ Fin 2 → (GaloisField 2 f)) ≃ₗ[(GaloisField 2
            f)] (Fin 2 ⊕ Fin 2 → (GaloisField 2 f)))))).toMonoidHom := by
  rw [show (siegelGroup (Spin.quadPlus 2 (GaloisField 2 f)) (bmsdop_r2_e11 f) (bmsdop_r2_e12 f)).map
      (MulAut.conj (((bmsdop_r2_rhoL f g : (Fin 2 ⊕ Fin 2 → (GaloisField 2 f)) ≃ₗ[(GaloisField 2 f)]
          (Fin 2 ⊕ Fin 2 → (GaloisField 2 f)))))).toMonoidHom =
    Subgroup.map (MulEquiv.toMonoidHom (MulAut.conj (((bmsdop_r2_rhoL f g : (Fin 2 ⊕ Fin 2 →
        (GaloisField 2 f)) ≃ₗ[(GaloisField 2 f)] (Fin 2 ⊕ Fin 2 → (GaloisField 2 f)))))))
      (siegelGroup (Spin.quadPlus 2 (GaloisField 2 f)) (bmsdop_r2_e11 f) (bmsdop_r2_e12 f))
          from rfl]
  rw [bmsdop_r2_siegelGroup_map_conj_eq f (((bmsdop_r2_rhoL f g : (Fin 2 ⊕ Fin 2 → (GaloisField 2
      f)) ≃ₗ[(GaloisField 2 f)] (Fin 2 ⊕ Fin 2 → (GaloisField 2 f)))))
    (bmsdop_r2_rhoL_mem_orthogonalGroup f g) (bmsdop_r2_e11 f) (bmsdop_r2_e12 f)]
  rfl

private lemma bmsdop_r2_rhoL_conj (f : ℕ)
    (u t : Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 f)) :
    ((bmsdop_r2_rhoL f (u * t * u⁻¹) : (Fin 2 ⊕ Fin 2 → (GaloisField 2 f)) ≃ₗ[(GaloisField 2 f)]
        (Fin 2 ⊕ Fin 2 → (GaloisField 2 f)))) =
      ((bmsdop_r2_rhoL f u : (Fin 2 ⊕ Fin 2 → (GaloisField 2 f)) ≃ₗ[(GaloisField 2 f)] (Fin 2 ⊕ Fin
          2 → (GaloisField 2 f)))) *
        ((bmsdop_r2_rhoL f t : (Fin 2 ⊕ Fin 2 → (GaloisField 2 f)) ≃ₗ[(GaloisField 2 f)] (Fin 2 ⊕
            Fin 2 → (GaloisField 2 f)))) *
        (((bmsdop_r2_rhoL f u : (Fin 2 ⊕ Fin 2 → (GaloisField 2 f)) ≃ₗ[(GaloisField 2 f)] (Fin 2 ⊕
            Fin 2 → (GaloisField 2 f)))))⁻¹ := by
  simp only [map_mul, map_inv, Subgroup.coe_mul, Subgroup.coe_inv]

private lemma bmsdop_r2_conj_toMonoidHom_apply (f : ℕ)
    (u t : Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 f)) :
    (MulEquiv.toMonoidHom (MulAut.conj u)) t = u * t * u⁻¹ := by
  exact MulAut.conj_apply u t

private lemma bmsdop_r2_conj_rhoL_apply (f : ℕ)
    (u t : Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 f)) :
    (MulAut.conj (((bmsdop_r2_rhoL f u : (Fin 2 ⊕ Fin 2 → (GaloisField 2 f)) ≃ₗ[(GaloisField 2 f)]
        (Fin 2 ⊕ Fin 2 → (GaloisField 2 f)))))) ((bmsdop_r2_rhoL f t : (Fin 2 ⊕ Fin 2 → (GaloisField
            2 f)) ≃ₗ[(GaloisField 2 f)] (Fin 2 ⊕ Fin 2 → (GaloisField 2 f)))) =
      ((bmsdop_r2_rhoL f u : (Fin 2 ⊕ Fin 2 → (GaloisField 2 f)) ≃ₗ[(GaloisField 2 f)] (Fin 2 ⊕ Fin
          2 → (GaloisField 2 f)))) *
        ((bmsdop_r2_rhoL f t : (Fin 2 ⊕ Fin 2 → (GaloisField 2 f)) ≃ₗ[(GaloisField 2 f)] (Fin 2 ⊕
            Fin 2 → (GaloisField 2 f)))) *
        (((bmsdop_r2_rhoL f u : (Fin 2 ⊕ Fin 2 → (GaloisField 2 f)) ≃ₗ[(GaloisField 2 f)] (Fin 2 ⊕
            Fin 2 → (GaloisField 2 f)))))⁻¹ := by
  exact MulAut.conj_apply (((bmsdop_r2_rhoL f u : (Fin 2 ⊕ Fin 2 → (GaloisField 2 f))
      ≃ₗ[(GaloisField 2 f)] (Fin 2 ⊕ Fin 2 → (GaloisField 2 f))))) ((bmsdop_r2_rhoL f t : (Fin 2 ⊕
          Fin 2 → (GaloisField 2 f)) ≃ₗ[(GaloisField 2 f)] (Fin 2 ⊕ Fin 2 → (GaloisField 2 f))))

private lemma bmsdop_r2_rhoL_conj_pt (f : ℕ)
    (u t : Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 f)) :
    ((bmsdop_r2_rhoL f ((MulEquiv.toMonoidHom (MulAut.conj u)) t) : (Fin 2 ⊕ Fin 2 → (GaloisField 2
        f)) ≃ₗ[(GaloisField 2 f)] (Fin 2 ⊕ Fin 2 → (GaloisField 2 f)))) =
      (MulAut.conj (((bmsdop_r2_rhoL f u : (Fin 2 ⊕ Fin 2 → (GaloisField 2 f)) ≃ₗ[(GaloisField 2 f)]
          (Fin 2 ⊕ Fin 2 → (GaloisField 2 f)))))) ((bmsdop_r2_rhoL f t : (Fin 2 ⊕ Fin 2 →
              (GaloisField 2 f)) ≃ₗ[(GaloisField 2 f)] (Fin 2 ⊕ Fin 2 → (GaloisField 2 f)))) := by
  rw [bmsdop_r2_conj_toMonoidHom_apply, bmsdop_r2_rhoL_conj, bmsdop_r2_conj_rhoL_apply]

private lemma bmsdop_r2_comp_conj_eq (f : ℕ)
    (u : Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 f)) :
    ((Subgroup.subtype (CFSG.RankThree.OrthogonalInvolutions.omegaGroup (Spin.quadPlus 2
        (GaloisField 2 f)) (Spin.nondegenerate_polarBilin_quadPlus 2 (GaloisField 2 f)))).comp
            (bmsdop_r2_rhoL f)).comp (MulAut.conj u).toMonoidHom =
      (MulAut.conj (((bmsdop_r2_rhoL f u : (Fin 2 ⊕ Fin 2 → (GaloisField 2 f)) ≃ₗ[(GaloisField 2 f)]
          (Fin 2 ⊕ Fin 2 → (GaloisField 2 f)))))).toMonoidHom.comp
        ((Subgroup.subtype (CFSG.RankThree.OrthogonalInvolutions.omegaGroup (Spin.quadPlus 2
            (GaloisField 2 f)) (Spin.nondegenerate_polarBilin_quadPlus 2 (GaloisField 2 f)))).comp
                (bmsdop_r2_rhoL f)) := by
  apply MonoidHom.ext
  intro t
  exact bmsdop_r2_rhoL_conj_pt f u t

private lemma bmsdop_r2_rootGroup_conj_map (f : ℕ) (hcard : Nat.card (GaloisField 2 f) ≠ 2)
    (u : Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 f)) :
    (((((SpecialLinear.rootDatum 1 (GaloisField 2 f))).rootGroup (Pi.single (bmsdop_r2_i0 f) 1)).map
        (MulAut.conj u).toMonoidHom).map
        ((Subgroup.subtype (CFSG.RankThree.OrthogonalInvolutions.omegaGroup (Spin.quadPlus 2
            (GaloisField 2 f)) (Spin.nondegenerate_polarBilin_quadPlus 2 (GaloisField 2 f)))).comp
                (bmsdop_r2_rhoL f))) =
      (siegelGroup (Spin.quadPlus 2 (GaloisField 2 f)) (bmsdop_r2_e11 f) (bmsdop_r2_e12 f)).map
        (MulAut.conj (((bmsdop_r2_rhoL f u : (Fin 2 ⊕ Fin 2 → (GaloisField 2 f)) ≃ₗ[(GaloisField 2
            f)] (Fin 2 ⊕ Fin 2 → (GaloisField 2 f)))))).toMonoidHom := by
  rw [Subgroup.map_map, bmsdop_r2_comp_conj_eq, ← Subgroup.map_map,
    bmsdop_r2_rootGroup_upper f hcard]

private lemma bmsdop_r2_rootGroup_conj_eq (f : ℕ) (hcard : Nat.card (GaloisField 2 f) ≠ 2)
    (u : Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 f)) :
    ((((SpecialLinear.rootDatum 1 (GaloisField 2 f))).rootGroup (Pi.single (bmsdop_r2_i0 f) 1)).map
        (MulAut.conj u).toMonoidHom).map
        ((Subgroup.subtype (CFSG.RankThree.OrthogonalInvolutions.omegaGroup (Spin.quadPlus 2
            (GaloisField 2 f)) (Spin.nondegenerate_polarBilin_quadPlus 2 (GaloisField 2 f)))).comp
                (bmsdop_r2_rhoL f)) =
      (siegelGroup (Spin.quadPlus 2 (GaloisField 2 f)) (bmsdop_r2_e11 f) (bmsdop_r2_e12 f)).map
        (MulAut.conj (((bmsdop_r2_rhoL f u : (Fin 2 ⊕ Fin 2 → (GaloisField 2 f)) ≃ₗ[(GaloisField 2
            f)] (Fin 2 ⊕ Fin 2 → (GaloisField 2 f)))))).toMonoidHom := by
  simpa only [MulEquiv.coe_toMonoidHom] using bmsdop_r2_rootGroup_conj_map f hcard u

private lemma bmsdop_r2_closure_Qstd_left_eichler (f : ℕ)
    (hcard : Nat.card (GaloisField 2 f) ≠ 2)
    (a₁ a₂ : Fin 2 ⊕ Fin 2 → (GaloisField 2 f))
    (ha₁ : a₁ ≠ 0) (ha₂ : a₂ ≠ 0)
    (hlin : LinearIndependent (GaloisField 2 f) ![a₁, a₂])
    (hQ₁ : (Spin.quadPlus 2 (GaloisField 2 f)) a₁ = 0)
    (hQ₂ : (Spin.quadPlus 2 (GaloisField 2 f)) a₂ = 0)
    (hpol : QuadraticMap.polar (Spin.quadPlus 2 (GaloisField 2 f)) a₁ a₂ = 0)
    (hle : siegelGroup (Spin.quadPlus 2 (GaloisField 2 f)) a₁ a₂ ≤
      (bmsdop_r2_rhoL f).range.map (Subgroup.subtype
          (CFSG.RankThree.OrthogonalInvolutions.omegaGroup (Spin.quadPlus 2 (GaloisField 2 f))
          (Spin.nondegenerate_polarBilin_quadPlus 2 (GaloisField 2 f)))))
    (g : Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 f))
    (hg : siegelGroup (Spin.quadPlus 2 (GaloisField 2 f)) a₁ a₂ =
      siegelGroup (Spin.quadPlus 2 (GaloisField 2 f))
          ((bmsdop_r2_kappa f).symm ((g : Matrix (Fin 2) (Fin 2) (GaloisField 2 f)) * (!![1, 0; 0,
              0] : Matrix (Fin 2) (Fin 2) (GaloisField 2 f))))
          ((bmsdop_r2_kappa f).symm ((g : Matrix (Fin 2) (Fin 2) (GaloisField 2 f)) * (!![0, 1; 0,
              0] : Matrix (Fin 2) (Fin 2) (GaloisField 2 f))))) :
    ∃ (β : Fin (SpecialLinear.rootDatum 1 (GaloisField 2 f)).rank → ℤ)
      (u : Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 f)),
      β ∈ (SpecialLinear.rootDatum 1 (GaloisField 2 f)).roots ∧
      GGLongRoot (SpecialLinear.rootDatum 1 (GaloisField 2 f)) β ∧
      (((SpecialLinear.rootDatum 1 (GaloisField 2 f)).rootGroup β).map
          (MulAut.conj u).toMonoidHom).map
        ((Subgroup.subtype (CFSG.RankThree.OrthogonalInvolutions.omegaGroup
          (Spin.quadPlus 2 (GaloisField 2 f))
          (Spin.nondegenerate_polarBilin_quadPlus 2 (GaloisField 2 f)))).comp
          (bmsdop_r2_rhoL f)) =
        siegelGroup (Spin.quadPlus 2 (GaloisField 2 f)) a₁ a₂ := by
  refine ⟨Pi.single (bmsdop_r2_i0 f) 1, g, bmsdop_r2_i0_mem_roots f,
    bmsdop_r2_i0_GGLongRoot f hcard, ?_⟩
  rw [bmsdop_r2_rootGroup_conj_eq f hcard g, ← bmsdop_r2_siegelGroup_family1_eq_conj f g, hg]

private lemma bmsdop_r2_closure_Qstd_left (f : ℕ)
    (hcard : Nat.card (GaloisField 2 f) ≠ 2)
    (a₁ a₂ : Fin 2 ⊕ Fin 2 → GaloisField 2 f)
    (ha₁ : a₁ ≠ 0) (ha₂ : a₂ ≠ 0)
    (hlin : LinearIndependent (GaloisField 2 f) ![a₁, a₂])
    (hQ₁ : (Spin.quadPlus 2 (GaloisField 2 f)) a₁ = 0)
    (hQ₂ : (Spin.quadPlus 2 (GaloisField 2 f)) a₂ = 0)
    (hpol : QuadraticMap.polar (Spin.quadPlus 2 (GaloisField 2 f)) a₁ a₂ = 0)
    (hle : siegelGroup (Spin.quadPlus 2 (GaloisField 2 f)) a₁ a₂ ≤
      (bmsdop_r2_rhoL f).range.map (Subgroup.subtype
        (CFSG.RankThree.OrthogonalInvolutions.omegaGroup (Spin.quadPlus 2 (GaloisField 2 f))
          (Spin.nondegenerate_polarBilin_quadPlus 2 (GaloisField 2 f))))) :
    ∃ (β : Fin (SpecialLinear.rootDatum 1 (GaloisField 2 f)).rank → ℤ)
      (u : Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 f)),
      β ∈ (SpecialLinear.rootDatum 1 (GaloisField 2 f)).roots ∧
      GGLongRoot (SpecialLinear.rootDatum 1 (GaloisField 2 f)) β ∧
      (((SpecialLinear.rootDatum 1 (GaloisField 2 f)).rootGroup β).map
          (MulAut.conj u).toMonoidHom).map
        ((Subgroup.subtype (CFSG.RankThree.OrthogonalInvolutions.omegaGroup
          (Spin.quadPlus 2 (GaloisField 2 f))
          (Spin.nondegenerate_polarBilin_quadPlus 2 (GaloisField 2 f)))).comp
          (bmsdop_r2_rhoL f)) =
        siegelGroup (Spin.quadPlus 2 (GaloisField 2 f)) a₁ a₂ := by
  obtain ⟨g, hg⟩ :=
    bmsdop_r2_closure_Qstd_left_classify f hcard a₁ a₂ ha₁ ha₂ hlin hQ₁ hQ₂ hpol hle
  exact bmsdop_r2_closure_Qstd_left_eichler f hcard a₁ a₂ ha₁ ha₂ hlin hQ₁ hQ₂ hpol hle g hg

private lemma bmsdop_r2_siegelGroup_family2_eq_conj (f : ℕ)
    (h : Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 f)) :
    siegelGroup (Spin.quadPlus 2 (GaloisField 2 f)) ((bmsdop_r2_kappa f).symm ((!![0, 0; 0, 1] :
        Matrix (Fin 2) (Fin 2) (GaloisField 2 f)) * (((h⁻¹ : Matrix.SpecialLinearGroup (Fin 2)
            (GaloisField 2 f)) : Matrix (Fin 2) (Fin 2) (GaloisField 2 f)))))
        ((bmsdop_r2_kappa f).symm ((!![0, 1; 0, 0] : Matrix (Fin 2) (Fin 2) (GaloisField 2 f)) *
            (((h⁻¹ : Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 f)) : Matrix (Fin 2) (Fin 2)
                (GaloisField 2 f))))) =
      (siegelGroup (Spin.quadPlus 2 (GaloisField 2 f)) (bmsdop_r2_e22 f) (bmsdop_r2_e12 f)).map
        (MulAut.conj (((bmsdop_r2_rhoR f h : (Fin 2 ⊕ Fin 2 → (GaloisField 2 f)) ≃ₗ[(GaloisField 2
            f)] (Fin 2 ⊕ Fin 2 → (GaloisField 2 f)))))).toMonoidHom := by
  rw [show (siegelGroup (Spin.quadPlus 2 (GaloisField 2 f)) (bmsdop_r2_e22 f) (bmsdop_r2_e12 f)).map
      (MulAut.conj (((bmsdop_r2_rhoR f h : (Fin 2 ⊕ Fin 2 → (GaloisField 2 f)) ≃ₗ[(GaloisField 2 f)]
          (Fin 2 ⊕ Fin 2 → (GaloisField 2 f)))))).toMonoidHom =
    Subgroup.map (MulEquiv.toMonoidHom (MulAut.conj (((bmsdop_r2_rhoR f h : (Fin 2 ⊕ Fin 2 →
        (GaloisField 2 f)) ≃ₗ[(GaloisField 2 f)] (Fin 2 ⊕ Fin 2 → (GaloisField 2 f)))))))
      (siegelGroup (Spin.quadPlus 2 (GaloisField 2 f)) (bmsdop_r2_e22 f) (bmsdop_r2_e12 f))
          from rfl]
  rw [bmsdop_r2_siegelGroup_map_conj_eq f (((bmsdop_r2_rhoR f h : (Fin 2 ⊕ Fin 2 → (GaloisField 2
      f)) ≃ₗ[(GaloisField 2 f)] (Fin 2 ⊕ Fin 2 → (GaloisField 2 f)))))
    (bmsdop_r2_omegaGroup_le_orthogonalGroup f (bmsdop_r2_rhoR f h).property)
    (bmsdop_r2_e22 f) (bmsdop_r2_e12 f)]
  congr 1

private lemma bmsdop_r2_rhoR_conj (f : ℕ)
    (u t : Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 f)) :
    ((bmsdop_r2_rhoR f (u * t * u⁻¹) : (Fin 2 ⊕ Fin 2 → (GaloisField 2 f)) ≃ₗ[(GaloisField 2 f)]
        (Fin 2 ⊕ Fin 2 → (GaloisField 2 f)))) =
      ((bmsdop_r2_rhoR f u : (Fin 2 ⊕ Fin 2 → (GaloisField 2 f)) ≃ₗ[(GaloisField 2 f)] (Fin 2 ⊕ Fin
          2 → (GaloisField 2 f)))) *
        ((bmsdop_r2_rhoR f t : (Fin 2 ⊕ Fin 2 → (GaloisField 2 f)) ≃ₗ[(GaloisField 2 f)] (Fin 2 ⊕
            Fin 2 → (GaloisField 2 f)))) *
        (((bmsdop_r2_rhoR f u : (Fin 2 ⊕ Fin 2 → (GaloisField 2 f)) ≃ₗ[(GaloisField 2 f)] (Fin 2 ⊕
            Fin 2 → (GaloisField 2 f)))))⁻¹ := by
  simp only [map_mul, map_inv, Subgroup.coe_mul, Subgroup.coe_inv]

private lemma bmsdop_r2_conj_rhoR_apply (f : ℕ)
    (u t : Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 f)) :
    (MulAut.conj (((bmsdop_r2_rhoR f u : (Fin 2 ⊕ Fin 2 → (GaloisField 2 f)) ≃ₗ[(GaloisField 2 f)]
        (Fin 2 ⊕ Fin 2 → (GaloisField 2 f)))))) ((bmsdop_r2_rhoR f t : (Fin 2 ⊕ Fin 2 → (GaloisField
            2 f)) ≃ₗ[(GaloisField 2 f)] (Fin 2 ⊕ Fin 2 → (GaloisField 2 f)))) =
      ((bmsdop_r2_rhoR f u : (Fin 2 ⊕ Fin 2 → (GaloisField 2 f)) ≃ₗ[(GaloisField 2 f)] (Fin 2 ⊕ Fin
          2 → (GaloisField 2 f)))) *
        ((bmsdop_r2_rhoR f t : (Fin 2 ⊕ Fin 2 → (GaloisField 2 f)) ≃ₗ[(GaloisField 2 f)] (Fin 2 ⊕
            Fin 2 → (GaloisField 2 f)))) *
        (((bmsdop_r2_rhoR f u : (Fin 2 ⊕ Fin 2 → (GaloisField 2 f)) ≃ₗ[(GaloisField 2 f)] (Fin 2 ⊕
            Fin 2 → (GaloisField 2 f)))))⁻¹ := by
  exact MulAut.conj_apply (((bmsdop_r2_rhoR f u : (Fin 2 ⊕ Fin 2 → (GaloisField 2 f))
      ≃ₗ[(GaloisField 2 f)] (Fin 2 ⊕ Fin 2 → (GaloisField 2 f))))) ((bmsdop_r2_rhoR f t : (Fin 2 ⊕
          Fin 2 → (GaloisField 2 f)) ≃ₗ[(GaloisField 2 f)] (Fin 2 ⊕ Fin 2 → (GaloisField 2 f))))

private lemma bmsdop_r2_rhoR_conj_pt (f : ℕ)
    (u t : Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 f)) :
    ((bmsdop_r2_rhoR f ((MulEquiv.toMonoidHom (MulAut.conj u)) t) : (Fin 2 ⊕ Fin 2 → (GaloisField 2
        f)) ≃ₗ[(GaloisField 2 f)] (Fin 2 ⊕ Fin 2 → (GaloisField 2 f)))) =
      (MulAut.conj (((bmsdop_r2_rhoR f u : (Fin 2 ⊕ Fin 2 → (GaloisField 2 f)) ≃ₗ[(GaloisField 2 f)]
          (Fin 2 ⊕ Fin 2 → (GaloisField 2 f)))))) ((bmsdop_r2_rhoR f t : (Fin 2 ⊕ Fin 2 →
              (GaloisField 2 f)) ≃ₗ[(GaloisField 2 f)] (Fin 2 ⊕ Fin 2 → (GaloisField 2 f)))) := by
  rw [bmsdop_r2_conj_toMonoidHom_apply, bmsdop_r2_rhoR_conj, bmsdop_r2_conj_rhoR_apply]

private lemma bmsdop_r2_comp_conj_R_eq (f : ℕ)
    (u : Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 f)) :
    ((Subgroup.subtype (CFSG.RankThree.OrthogonalInvolutions.omegaGroup (Spin.quadPlus 2
        (GaloisField 2 f)) (Spin.nondegenerate_polarBilin_quadPlus 2 (GaloisField 2 f)))).comp
            (bmsdop_r2_rhoR f)).comp (MulAut.conj u).toMonoidHom =
      (MulAut.conj (((bmsdop_r2_rhoR f u : (Fin 2 ⊕ Fin 2 → (GaloisField 2 f)) ≃ₗ[(GaloisField 2 f)]
          (Fin 2 ⊕ Fin 2 → (GaloisField 2 f)))))).toMonoidHom.comp
        ((Subgroup.subtype (CFSG.RankThree.OrthogonalInvolutions.omegaGroup (Spin.quadPlus 2
            (GaloisField 2 f)) (Spin.nondegenerate_polarBilin_quadPlus 2 (GaloisField 2 f)))).comp
                (bmsdop_r2_rhoR f)) := by
  apply MonoidHom.ext
  intro t
  exact bmsdop_r2_rhoR_conj_pt f u t

private lemma bmsdop_r2_rootGroup_R_conj_eq (f : ℕ) (hcard : Nat.card (GaloisField 2 f) ≠ 2)
    (u : Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 f)) :
    (((((SpecialLinear.rootDatum 1 (GaloisField 2 f))).rootGroup (Pi.single (bmsdop_r2_i0 f) 1)).map
        (MulAut.conj u).toMonoidHom).map
        ((Subgroup.subtype (CFSG.RankThree.OrthogonalInvolutions.omegaGroup (Spin.quadPlus 2
            (GaloisField 2 f)) (Spin.nondegenerate_polarBilin_quadPlus 2 (GaloisField 2 f)))).comp
                (bmsdop_r2_rhoR f))) =
      (siegelGroup (Spin.quadPlus 2 (GaloisField 2 f)) (bmsdop_r2_e22 f) (bmsdop_r2_e12 f)).map
        (MulAut.conj (((bmsdop_r2_rhoR f u : (Fin 2 ⊕ Fin 2 → (GaloisField 2 f)) ≃ₗ[(GaloisField 2
            f)] (Fin 2 ⊕ Fin 2 → (GaloisField 2 f)))))).toMonoidHom := by
  rw [Subgroup.map_map, bmsdop_r2_comp_conj_R_eq, ← Subgroup.map_map,
    bmsdop_r2_rootGroup_R_upper f hcard]

private lemma bmsdop_r2_mul_E11_eq_vecMulVec (f : ℕ) (g : Matrix (Fin 2) (Fin 2) (GaloisField 2 f))
    :
    g * (!![1, 0; 0, 0] : Matrix (Fin 2) (Fin 2) (GaloisField 2 f)) =
      Matrix.vecMulVec (fun i => g i 0) ![1, 0] := by
  ext i j
  fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.vecMulVec, Matrix.of_apply]

private lemma bmsdop_r2_mul_E12_eq_vecMulVec (f : ℕ) (g : Matrix (Fin 2) (Fin 2) (GaloisField 2 f))
    :
    g * (!![0, 1; 0, 0] : Matrix (Fin 2) (Fin 2) (GaloisField 2 f)) =
      Matrix.vecMulVec (fun i => g i 0) ![0, 1] := by
  ext i j
  fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.vecMulVec, Matrix.of_apply]

private lemma bmsdop_r2_family1_eichler_apply (f : ℕ)
    (g : Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 f)) (X : (Fin 2 ⊕ Fin 2 → (GaloisField 2
        f))) :
    (bmsdop_r2_kappa f) (CFSG.ClassicalGroups.Orthogonal.eichler (Spin.quadPlus 2 (GaloisField 2 f))
      ((bmsdop_r2_kappa f).symm ((g : Matrix (Fin 2) (Fin 2) (GaloisField 2 f)) * (!![1, 0; 0, 0] :
          Matrix (Fin 2) (Fin 2) (GaloisField 2 f)))) ((bmsdop_r2_kappa f).symm ((g : Matrix (Fin 2)
              (Fin 2) (GaloisField 2 f)) * (!![0, 1; 0, 0] : Matrix (Fin 2) (Fin 2) (GaloisField 2
                  f)))) X) =
      (bmsdop_r2_kappa f) X + Matrix.vecMulVec (fun i => (g : Matrix (Fin 2) (Fin 2) (GaloisField 2
          f)) i 0) (fun j =>
        (((bmsdop_r2_kappa f X) 1 1 * (g : Matrix (Fin 2) (Fin 2) (GaloisField 2 f)) 0 0 -
            (bmsdop_r2_kappa f X) 0 1 * (g : Matrix (Fin 2) (Fin 2) (GaloisField 2 f)) 1 0)) * ![0,
                1] j - (((bmsdop_r2_kappa f X) 0 0 * (g : Matrix (Fin 2) (Fin 2) (GaloisField 2 f))
                    1 0 - (bmsdop_r2_kappa f X) 1 0 * (g : Matrix (Fin 2) (Fin 2) (GaloisField 2 f))
                        0 0)) * ![1, 0] j) := by
  rw [bmsdop_r2_mul_E11_eq_vecMulVec f (g : Matrix (Fin 2) (Fin 2) (GaloisField 2 f)),
    bmsdop_r2_mul_E12_eq_vecMulVec f (g : Matrix (Fin 2) (Fin 2) (GaloisField 2 f))]
  simpa only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.head_fin_const, mul_one, mul_zero, add_zero, zero_mul, sub_zero, one_mul, one_smul,
    zero_add] using
    bmsdop_r2_eichler_action_rank1 f (fun i => (g : Matrix (Fin 2) (Fin 2) (GaloisField 2 f)) i 0)
      ![1, 0] ![0, 1] 1 X

private lemma bmsdop_r2_eichler_family1_ne_one (f : ℕ)
    (g : Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 f)) :
    CFSG.ClassicalGroups.Orthogonal.eichler (Spin.quadPlus 2 (GaloisField 2 f))
      ((bmsdop_r2_kappa f).symm ((g : Matrix (Fin 2) (Fin 2) (GaloisField 2 f)) * (!![1, 0; 0, 0] :
          Matrix (Fin 2) (Fin 2) (GaloisField 2 f))))
      ((bmsdop_r2_kappa f).symm ((g : Matrix (Fin 2) (Fin 2) (GaloisField 2 f)) * (!![0, 1; 0, 0] :
          Matrix (Fin 2) (Fin 2) (GaloisField 2 f)))) ≠ 1 := by
  intro h1
  set u : Fin 2 → GaloisField 2 f := fun i => (g : Matrix (Fin 2) (Fin 2) (GaloisField 2 f)) i 0
      with hu
  have hu_ne : u ≠ 0 := by
    intro h0
    have h00 : (g : Matrix (Fin 2) (Fin 2) (GaloisField 2 f)) 0 0 = 0 := by
      simpa [hu] using congrFun h0 0
    have h10 : (g : Matrix (Fin 2) (Fin 2) (GaloisField 2 f)) 1 0 = 0 := by
      simpa [hu] using congrFun h0 1
    have hdet := Matrix.SpecialLinearGroup.det_coe g
    rw [Matrix.det_fin_two, h00, h10] at hdet
    simp only [zero_mul, mul_zero, sub_zero] at hdet
    exact zero_ne_one hdet
  obtain ⟨i, hi⟩ : ∃ i, u i ≠ 0 := by
    by_contra h
    exact hu_ne (funext fun j => not_not.mp (not_exists.mp h j))
  have hfix : ∀ X : Fin 2 ⊕ Fin 2 → GaloisField 2 f,
      CFSG.ClassicalGroups.Orthogonal.eichler (Spin.quadPlus 2 (GaloisField 2 f))
        ((bmsdop_r2_kappa f).symm ((g : Matrix (Fin 2) (Fin 2) (GaloisField 2 f)) * (!![1, 0; 0, 0]
            : Matrix (Fin 2) (Fin 2) (GaloisField 2 f))))
        ((bmsdop_r2_kappa f).symm ((g : Matrix (Fin 2) (Fin 2) (GaloisField 2 f)) * (!![0, 1; 0, 0]
            : Matrix (Fin 2) (Fin 2) (GaloisField 2 f)))) X = X := by
    intro X
    have := congrArg (fun (e : (Fin 2 ⊕ Fin 2 → GaloisField 2 f) ≃ₗ[GaloisField 2 f]
        (Fin 2 ⊕ Fin 2 → GaloisField 2 f)) => e X) h1
    simpa using this
  have hu1 : (g : Matrix (Fin 2) (Fin 2) (GaloisField 2 f)) 1 0 = 0 := by
    have hκ := congrArg (bmsdop_r2_kappa f)
      (hfix ((bmsdop_r2_kappa f).symm (!![1, 0; 0, 0] : Matrix (Fin 2) (Fin 2) (GaloisField 2 f))))
    rw [LinearEquiv.apply_symm_apply] at hκ
    have happ := bmsdop_r2_family1_eichler_apply f g
      ((bmsdop_r2_kappa f).symm (!![1, 0; 0, 0] : Matrix (Fin 2) (Fin 2) (GaloisField 2 f)))
    rw [hκ, LinearEquiv.apply_symm_apply] at happ
    have hzero := by
      have htmp := congrArg (fun M => M -
        (!![1, 0; 0, 0] : Matrix (Fin 2) (Fin 2) (GaloisField 2 f))) happ.symm
      simpa using htmp
    have hZ := hzero.resolve_left hu_ne
    have hZ0 := congrFun hZ 0
    simpa only [Pi.zero_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      Matrix.head_fin_const, mul_one, CharTwo.neg_eq] using hZ0
  have hu0 : (g : Matrix (Fin 2) (Fin 2) (GaloisField 2 f)) 0 0 = 0 := by
    have hκ := congrArg (bmsdop_r2_kappa f)
      (hfix ((bmsdop_r2_kappa f).symm (!![0, 0; 0, 1] : Matrix (Fin 2) (Fin 2) (GaloisField 2 f))))
    rw [LinearEquiv.apply_symm_apply] at hκ
    have happ := bmsdop_r2_family1_eichler_apply f g
      ((bmsdop_r2_kappa f).symm (!![0, 0; 0, 1] : Matrix (Fin 2) (Fin 2) (GaloisField 2 f)))
    rw [hκ, LinearEquiv.apply_symm_apply] at happ
    have hzero := by
      have htmp := congrArg (fun M => M -
        (!![0, 0; 0, 1] : Matrix (Fin 2) (Fin 2) (GaloisField 2 f))) happ.symm
      simpa using htmp
    have hZ := hzero.resolve_left hu_ne
    have hZ1 := congrFun hZ 1
    simpa only [Pi.zero_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      Matrix.head_fin_const, mul_one] using hZ1
  exact hu_ne (funext fun j => by
    fin_cases j
    · simpa [hu] using hu0
    · simpa [hu] using hu1)

private lemma bmsdop_r2_lagrangian_family1_excl (f : ℕ)
    (hcard : Nat.card (GaloisField 2 f) ≠ 2)
    (a₁ a₂ : Fin 2 ⊕ Fin 2 → (GaloisField 2 f))
    (ha₁ : a₁ ≠ 0) (ha₂ : a₂ ≠ 0)
    (hlin : LinearIndependent (GaloisField 2 f) ![a₁, a₂])
    (hQ₁ : (Spin.quadPlus 2 (GaloisField 2 f)) a₁ = 0)
    (hQ₂ : (Spin.quadPlus 2 (GaloisField 2 f)) a₂ = 0)
    (hpol : QuadraticMap.polar (Spin.quadPlus 2 (GaloisField 2 f)) a₁ a₂ = 0)
    (hle : siegelGroup (Spin.quadPlus 2 (GaloisField 2 f)) a₁ a₂ ≤
      (bmsdop_r2_rhoR f).range.map (Subgroup.subtype
          (CFSG.RankThree.OrthogonalInvolutions.omegaGroup (Spin.quadPlus 2 (GaloisField 2 f))
              (Spin.nondegenerate_polarBilin_quadPlus 2 (GaloisField 2 f)))))
    (g : Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 f))
    (hg : siegelGroup (Spin.quadPlus 2 (GaloisField 2 f)) a₁ a₂ =
      siegelGroup (Spin.quadPlus 2 (GaloisField 2 f)) ((bmsdop_r2_kappa f).symm ((g : Matrix (Fin 2)
          (Fin 2) (GaloisField 2 f)) * (!![1, 0; 0, 0] : Matrix (Fin 2) (Fin 2) (GaloisField 2 f))))
        ((bmsdop_r2_kappa f).symm ((g : Matrix (Fin 2) (Fin 2) (GaloisField 2 f)) * (!![0, 1; 0, 0]
            : Matrix (Fin 2) (Fin 2) (GaloisField 2 f))))) :
    False := by
  have hleL : siegelGroup (Spin.quadPlus 2 (GaloisField 2 f)) a₁ a₂ ≤ (bmsdop_r2_rhoL f).range.map
      (Subgroup.subtype (CFSG.RankThree.OrthogonalInvolutions.omegaGroup (Spin.quadPlus 2
          (GaloisField 2 f)) (Spin.nondegenerate_polarBilin_quadPlus 2 (GaloisField 2 f)))) := by
    rw [hg, bmsdop_r2_siegelGroup_family1_eq_conj f g, ← bmsdop_r2_rootGroup_conj_eq f hcard g]
    exact le_trans
      (Subgroup.map_le_range ((Subgroup.subtype (CFSG.RankThree.OrthogonalInvolutions.omegaGroup
          (Spin.quadPlus 2 (GaloisField 2 f)) (Spin.nondegenerate_polarBilin_quadPlus 2 (GaloisField
              2 f)))).comp (bmsdop_r2_rhoL f))
        ((((SpecialLinear.rootDatum 1 (GaloisField 2 f))).rootGroup (Pi.single (bmsdop_r2_i0 f)
            1)).map (MulAut.conj g).toMonoidHom))
      (le_of_eq (MonoidHom.range_comp (Subgroup.subtype
          (CFSG.RankThree.OrthogonalInvolutions.omegaGroup (Spin.quadPlus 2 (GaloisField 2 f))
              (Spin.nondegenerate_polarBilin_quadPlus 2 (GaloisField 2 f)))) (bmsdop_r2_rhoL f)))
  have hbot : siegelGroup (Spin.quadPlus 2 (GaloisField 2 f)) a₁ a₂ ≤ ⊥ := by
    rw [← bmsdop_r2_map_inf_bot f hcard]
    exact le_inf hleL hle
  have hmem : CFSG.ClassicalGroups.Orthogonal.eichler (Spin.quadPlus 2 (GaloisField 2 f))
      ((bmsdop_r2_kappa f).symm ((g : Matrix (Fin 2) (Fin 2) (GaloisField 2 f)) * (!![1, 0; 0, 0] :
          Matrix (Fin 2) (Fin 2) (GaloisField 2 f))))
      ((bmsdop_r2_kappa f).symm ((g : Matrix (Fin 2) (Fin 2) (GaloisField 2 f)) * (!![0, 1; 0, 0] :
          Matrix (Fin 2) (Fin 2) (GaloisField 2 f)))) ∈ siegelGroup (Spin.quadPlus 2 (GaloisField 2
              f)) a₁ a₂ := by
    rw [hg]
    exact Subgroup.subset_closure ⟨1, by rw [one_smul]⟩
  have hone : CFSG.ClassicalGroups.Orthogonal.eichler (Spin.quadPlus 2 (GaloisField 2 f))
      ((bmsdop_r2_kappa f).symm ((g : Matrix (Fin 2) (Fin 2) (GaloisField 2 f)) * (!![1, 0; 0, 0] :
          Matrix (Fin 2) (Fin 2) (GaloisField 2 f))))
      ((bmsdop_r2_kappa f).symm ((g : Matrix (Fin 2) (Fin 2) (GaloisField 2 f)) * (!![0, 1; 0, 0] :
          Matrix (Fin 2) (Fin 2) (GaloisField 2 f)))) = 1 := by
    have := hbot hmem
    simpa using this
  exact bmsdop_r2_eichler_family1_ne_one f g hone

private lemma bmsdop_r2_siegelGroup_basis_invariant_kernel (f : ℕ)
    (a₁ a₂ b₁ b₂ : Fin 2 ⊕ Fin 2 → (GaloisField 2 f))
    (v w₁ w₂ w₁' w₂' : Fin 2 → (GaloisField 2 f))
    (ha₁ : (bmsdop_r2_kappa f) a₁ = Matrix.vecMulVec w₁ v)
    (ha₂ : (bmsdop_r2_kappa f) a₂ = Matrix.vecMulVec w₂ v)
    (hb₁ : (bmsdop_r2_kappa f) b₁ = Matrix.vecMulVec w₁' v)
    (hb₂ : (bmsdop_r2_kappa f) b₂ = Matrix.vecMulVec w₂' v)
    (hdetw : w₁ 0 * w₂ 1 - w₁ 1 * w₂ 0 ≠ 0)
    (hdetw' : w₁' 0 * w₂' 1 - w₁' 1 * w₂' 0 ≠ 0) :
    siegelGroup (Spin.quadPlus 2 (GaloisField 2 f)) a₁ a₂ =
      siegelGroup (Spin.quadPlus 2 (GaloisField 2 f)) b₁ b₂ := by
  have ht₁ : (bmsdop_r2_kappa f) (bmsdop_r2_transpose f a₁) = Matrix.vecMulVec v w₁ := by
    rw [bmsdop_r2_transpose_apply, ha₁, bmsdop_r2_transpose_vecMulVec]
  have ht₂ : (bmsdop_r2_kappa f) (bmsdop_r2_transpose f a₂) = Matrix.vecMulVec v w₂ := by
    rw [bmsdop_r2_transpose_apply, ha₂, bmsdop_r2_transpose_vecMulVec]
  have ht₁' : (bmsdop_r2_kappa f) (bmsdop_r2_transpose f b₁) = Matrix.vecMulVec v w₁' := by
    rw [bmsdop_r2_transpose_apply, hb₁, bmsdop_r2_transpose_vecMulVec]
  have ht₂' : (bmsdop_r2_kappa f) (bmsdop_r2_transpose f b₂) = Matrix.vecMulVec v w₂' := by
    rw [bmsdop_r2_transpose_apply, hb₂, bmsdop_r2_transpose_vecMulVec]
  calc siegelGroup (Spin.quadPlus 2 (GaloisField 2 f)) a₁ a₂
      = (siegelGroup (Spin.quadPlus 2 (GaloisField 2 f)) (bmsdop_r2_transpose f a₁)
          (bmsdop_r2_transpose f a₂)).map
            (MulAut.conj (bmsdop_r2_transpose f)).toMonoidHom :=
        (bmsdop_r2_transpose_siegelGroup f a₁ a₂).symm
    _ = (siegelGroup (Spin.quadPlus 2 (GaloisField 2 f)) (bmsdop_r2_transpose f b₁)
          (bmsdop_r2_transpose f b₂)).map
            (MulAut.conj (bmsdop_r2_transpose f)).toMonoidHom := by
        rw [bmsdop_r2_siegelGroup_basis_invariant f (bmsdop_r2_transpose f a₁)
          (bmsdop_r2_transpose f a₂) (bmsdop_r2_transpose f b₁) (bmsdop_r2_transpose f b₂)
          v w₁ w₂ w₁' w₂' ht₁ ht₂ ht₁' ht₂' hdetw hdetw']
    _ = siegelGroup (Spin.quadPlus 2 (GaloisField 2 f)) b₁ b₂ :=
        bmsdop_r2_transpose_siegelGroup f b₁ b₂

private lemma bmsdop_r2_siegelGroup_family2_rhoR_normal (f : ℕ)
    (hcard : Nat.card (GaloisField 2 f) ≠ 2)
    (a₁ a₂ : Fin 2 ⊕ Fin 2 → (GaloisField 2 f))
    (ha₁ : a₁ ≠ 0) (ha₂ : a₂ ≠ 0)
    (hlin : LinearIndependent (GaloisField 2 f) ![a₁, a₂])
    (hQ₁ : (Spin.quadPlus 2 (GaloisField 2 f)) a₁ = 0)
    (hQ₂ : (Spin.quadPlus 2 (GaloisField 2 f)) a₂ = 0)
    (hpol : QuadraticMap.polar (Spin.quadPlus 2 (GaloisField 2 f)) a₁ a₂ = 0)
    (hle : siegelGroup (Spin.quadPlus 2 (GaloisField 2 f)) a₁ a₂ ≤
      (bmsdop_r2_rhoR f).range.map (Subgroup.subtype
          (CFSG.RankThree.OrthogonalInvolutions.omegaGroup (Spin.quadPlus 2 (GaloisField 2 f))
              (Spin.nondegenerate_polarBilin_quadPlus 2 (GaloisField 2 f))))) :
    ∃ h : Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 f),
      siegelGroup (Spin.quadPlus 2 (GaloisField 2 f)) a₁ a₂ =
        siegelGroup (Spin.quadPlus 2 (GaloisField 2 f)) ((bmsdop_r2_kappa f).symm ((!![0, 0; 0, 1] :
            Matrix (Fin 2) (Fin 2) (GaloisField 2 f)) * ((h : Matrix (Fin 2) (Fin 2) (GaloisField 2
                f)))⁻¹))
          ((bmsdop_r2_kappa f).symm ((!![0, 1; 0, 0] : Matrix (Fin 2) (Fin 2) (GaloisField 2 f)) *
              ((h : Matrix (Fin 2) (Fin 2) (GaloisField 2 f)))⁻¹)) := by
  rcases bmsdop_r2_lagrangian_dichotomy f hcard a₁ a₂ ha₁ ha₂ hlin hQ₁ hQ₂ hpol with
    ⟨g, hg⟩ | ⟨h, hh⟩
  · exact (bmsdop_r2_lagrangian_family1_excl f hcard a₁ a₂ ha₁ ha₂ hlin hQ₁ hQ₂ hpol hle
      g hg).elim
  · let S : Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 f) :=
      ⟨!![0, 1; 1, 0], by
        rw [Matrix.det_fin_two]
        simp only [Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
          mul_one, mul_zero, zero_mul, sub_zero, zero_sub]
        exact CharTwo.neg_eq (1 : GaloisField 2 f)⟩
    have hSmat : (S : Matrix (Fin 2) (Fin 2) (GaloisField 2 f)) =
        (!![0, 1; 1, 0] : Matrix (Fin 2) (Fin 2) (GaloisField 2 f)) := rfl
    let M : Matrix (Fin 2) (Fin 2) (GaloisField 2 f) :=
      (S : Matrix (Fin 2) (Fin 2) (GaloisField 2 f)) *
        (h : Matrix (Fin 2) (Fin 2) (GaloisField 2 f))
    have hMdet : M.det = 1 := by
      show ((S : Matrix (Fin 2) (Fin 2) (GaloisField 2 f)) *
        (h : Matrix (Fin 2) (Fin 2) (GaloisField 2 f))).det = 1
      rw [Matrix.det_mul, Matrix.SpecialLinearGroup.det_coe h, hSmat, Matrix.det_fin_two]
      simp only [Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
        mul_one, mul_zero, zero_mul, sub_zero, zero_sub]
      exact CharTwo.neg_eq (1 : GaloisField 2 f)
    let k : Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 f) :=
      ⟨M⁻¹, by
        rw [Matrix.det_nonsing_inv, hMdet]
        simp⟩
    have hkinv : ((k : Matrix (Fin 2) (Fin 2) (GaloisField 2 f)))⁻¹ = M := by
      show (M⁻¹)⁻¹ = M
      refine Matrix.inv_eq_left_inv (A := M⁻¹) (B := M) ?_
      exact Matrix.mul_nonsing_inv M (by rw [hMdet]; exact isUnit_one)
    have hE22 : (!![0, 0; 0, 1] : Matrix (Fin 2) (Fin 2) (GaloisField 2 f)) *
        ((k : Matrix (Fin 2) (Fin 2) (GaloisField 2 f)))⁻¹ =
        (!![0, 0; 1, 0] : Matrix (Fin 2) (Fin 2) (GaloisField 2 f)) *
          (h : Matrix (Fin 2) (Fin 2) (GaloisField 2 f)) := by
      rw [hkinv]
      show (!![0, 0; 0, 1] : Matrix (Fin 2) (Fin 2) (GaloisField 2 f)) *
        ((S : Matrix (Fin 2) (Fin 2) (GaloisField 2 f)) *
          (h : Matrix (Fin 2) (Fin 2) (GaloisField 2 f))) = _
      rw [← Matrix.mul_assoc, hSmat]
      rw [show (!![0, 0; 0, 1] : Matrix (Fin 2) (Fin 2) (GaloisField 2 f)) *
          (!![0, 1; 1, 0] : Matrix (Fin 2) (Fin 2) (GaloisField 2 f)) =
          (!![0, 0; 1, 0] : Matrix (Fin 2) (Fin 2) (GaloisField 2 f)) from by
        ext i j
        fin_cases i <;> fin_cases j <;>
          simp [Matrix.mul_apply, Fin.sum_univ_two]]
    have hE12 : (!![0, 1; 0, 0] : Matrix (Fin 2) (Fin 2) (GaloisField 2 f)) *
        ((k : Matrix (Fin 2) (Fin 2) (GaloisField 2 f)))⁻¹ =
        (!![1, 0; 0, 0] : Matrix (Fin 2) (Fin 2) (GaloisField 2 f)) *
          (h : Matrix (Fin 2) (Fin 2) (GaloisField 2 f)) := by
      rw [hkinv]
      show (!![0, 1; 0, 0] : Matrix (Fin 2) (Fin 2) (GaloisField 2 f)) *
        ((S : Matrix (Fin 2) (Fin 2) (GaloisField 2 f)) *
          (h : Matrix (Fin 2) (Fin 2) (GaloisField 2 f))) = _
      rw [← Matrix.mul_assoc, hSmat]
      rw [show (!![0, 1; 0, 0] : Matrix (Fin 2) (Fin 2) (GaloisField 2 f)) *
          (!![0, 1; 1, 0] : Matrix (Fin 2) (Fin 2) (GaloisField 2 f)) =
          (!![1, 0; 0, 0] : Matrix (Fin 2) (Fin 2) (GaloisField 2 f)) from by
        ext i j
        fin_cases i <;> fin_cases j <;>
          simp [Matrix.mul_apply, Fin.sum_univ_two]]
    refine ⟨k, ?_⟩
    rw [hh, hE22, hE12]
    exact bmsdop_r2_siegelGroup_basis_invariant_kernel f
      ((bmsdop_r2_kappa f).symm ((!![1, 0; 0, 0] : Matrix (Fin 2) (Fin 2) (GaloisField 2 f)) *
        (h : Matrix (Fin 2) (Fin 2) (GaloisField 2 f))))
      ((bmsdop_r2_kappa f).symm ((!![0, 0; 1, 0] : Matrix (Fin 2) (Fin 2) (GaloisField 2 f)) *
        (h : Matrix (Fin 2) (Fin 2) (GaloisField 2 f))))
      ((bmsdop_r2_kappa f).symm ((!![0, 0; 1, 0] : Matrix (Fin 2) (Fin 2) (GaloisField 2 f)) *
        (h : Matrix (Fin 2) (Fin 2) (GaloisField 2 f))))
      ((bmsdop_r2_kappa f).symm ((!![1, 0; 0, 0] : Matrix (Fin 2) (Fin 2) (GaloisField 2 f)) *
        (h : Matrix (Fin 2) (Fin 2) (GaloisField 2 f))))
      (fun j => (h : Matrix (Fin 2) (Fin 2) (GaloisField 2 f)) 0 j) ![1, 0] ![0, 1] ![0, 1] ![1, 0]
      (by
        rw [LinearEquiv.apply_symm_apply]
        ext i j
        fin_cases i <;> fin_cases j <;>
          simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.vecMulVec, Matrix.of_apply])
      (by
        rw [LinearEquiv.apply_symm_apply]
        ext i j
        fin_cases i <;> fin_cases j <;>
          simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.vecMulVec, Matrix.of_apply])
      (by
        rw [LinearEquiv.apply_symm_apply]
        ext i j
        fin_cases i <;> fin_cases j <;>
          simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.vecMulVec, Matrix.of_apply])
      (by
        rw [LinearEquiv.apply_symm_apply]
        ext i j
        fin_cases i <;> fin_cases j <;>
          simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.vecMulVec, Matrix.of_apply])
      (by
        simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
          Matrix.head_fin_const, mul_one, mul_zero, zero_mul, sub_zero]
        exact (one_ne_zero : (1 : GaloisField 2 f) ≠ 0))
      (by
        simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
          Matrix.head_fin_const, zero_mul, mul_zero, mul_one, zero_sub, CharTwo.neg_eq]
        exact (one_ne_zero : (1 : GaloisField 2 f) ≠ 0))

private lemma bmsdop_r2_matrix_inv_coe (f : ℕ)
    (h : Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 f)) :
    ((h : Matrix (Fin 2) (Fin 2) (GaloisField 2 f)))⁻¹ =
      (((h⁻¹ : Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 f)) :
        Matrix (Fin 2) (Fin 2) (GaloisField 2 f))) := by
  rw [Matrix.inv_def, Matrix.SpecialLinearGroup.det_coe,
    Matrix.SpecialLinearGroup.coe_inv]
  simp

private lemma bmsdop_r2_closure_Qstd_right (f : ℕ)
    (hcard : Nat.card (GaloisField 2 f) ≠ 2)
    (a₁ a₂ : Fin 2 ⊕ Fin 2 → GaloisField 2 f)
    (ha₁ : a₁ ≠ 0) (ha₂ : a₂ ≠ 0)
    (hlin : LinearIndependent (GaloisField 2 f) ![a₁, a₂])
    (hQ₁ : (Spin.quadPlus 2 (GaloisField 2 f)) a₁ = 0)
    (hQ₂ : (Spin.quadPlus 2 (GaloisField 2 f)) a₂ = 0)
    (hpol : QuadraticMap.polar (Spin.quadPlus 2 (GaloisField 2 f)) a₁ a₂ = 0)
    (hle : siegelGroup (Spin.quadPlus 2 (GaloisField 2 f)) a₁ a₂ ≤
      (bmsdop_r2_rhoR f).range.map (Subgroup.subtype
        (CFSG.RankThree.OrthogonalInvolutions.omegaGroup (Spin.quadPlus 2 (GaloisField 2 f))
          (Spin.nondegenerate_polarBilin_quadPlus 2 (GaloisField 2 f))))) :
    ∃ (β : Fin (SpecialLinear.rootDatum 1 (GaloisField 2 f)).rank → ℤ)
      (u : Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 f)),
      β ∈ (SpecialLinear.rootDatum 1 (GaloisField 2 f)).roots ∧
      GGLongRoot (SpecialLinear.rootDatum 1 (GaloisField 2 f)) β ∧
      (((SpecialLinear.rootDatum 1 (GaloisField 2 f)).rootGroup β).map
          (MulAut.conj u).toMonoidHom).map
        ((Subgroup.subtype (CFSG.RankThree.OrthogonalInvolutions.omegaGroup
          (Spin.quadPlus 2 (GaloisField 2 f))
          (Spin.nondegenerate_polarBilin_quadPlus 2 (GaloisField 2 f)))).comp
          (bmsdop_r2_rhoR f)) =
        siegelGroup (Spin.quadPlus 2 (GaloisField 2 f)) a₁ a₂ := by
  obtain ⟨h, hh⟩ := bmsdop_r2_siegelGroup_family2_rhoR_normal f hcard a₁ a₂ ha₁ ha₂ hlin
    hQ₁ hQ₂ hpol hle
  refine ⟨Pi.single (bmsdop_r2_i0 f) 1, h, bmsdop_r2_i0_mem_roots f,
    bmsdop_r2_i0_GGLongRoot f hcard, ?_⟩
  rw [bmsdop_r2_rootGroup_R_conj_eq f hcard h,
    ← bmsdop_r2_siegelGroup_family2_eq_conj f h]
  rw [← bmsdop_r2_matrix_inv_coe f h]
  exact hh.symm

private lemma bmsdop_r2_closure_V_aux (k f : ℕ)
    (S : Set (GL (Fin (k + 3) ⊕ Fin (k + 3)) (GaloisField 2 f)))
    {e : Matrix (Fin (k + 3) ⊕ Fin (k + 3)) (Fin (k + 3) ⊕ Fin (k + 3)) (GaloisField 2 f)}
    {J' : Subgroup ↥(spinGroup (bmsdop_Q k f))}
    (h1 : bmsdop_geom₁ k f S e) (h2 : bmsdop_geom₂ k f S e)
    (hJe : IsComponentOf J' ⁅bmsdop_Ge k f S e, bmsdop_Ge k f S e⁆)
    (θ : (Fin 2 ⊕ Fin 2 → GaloisField 2 f) ≃ₗ[GaloisField 2 f] ↥(bmsdop_W k f e))
    (hθ : ∀ x, (bmsdop_blockForm k f e) (θ x) = (Spin.quadPlus 2 (GaloisField 2 f)) x)
    (E : ((Fin 2 ⊕ Fin 2 → GaloisField 2 f) ≃ₗ[GaloisField 2 f]
        (Fin 2 ⊕ Fin 2 → GaloisField 2 f)) →*
        (bmsdop_V k f ≃ₗ[GaloisField 2 f] bmsdop_V k f))
    (hE : bmsdop_ExtProps k f S e (Spin.quadPlus 2 (GaloisField 2 f))
        (Spin.nondegenerate_polarBilin_quadPlus 2 (GaloisField 2 f)) θ E)
    (r : ↥(CFSG.RankThree.OrthogonalInvolutions.omegaGroup (Spin.quadPlus 2 (GaloisField 2 f))
          (Spin.nondegenerate_polarBilin_quadPlus 2 (GaloisField 2 f))) →*
        ↥(spinGroup (bmsdop_Q k f)))
    (hr : Function.Injective r ∧ r.range = bmsdop_Ge k f S e ∧
      ∀ g, Spin.spinAction (bmsdop_Q k f) (r g) = E g)
    (ρ : Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 f) →*
        ↥(CFSG.RankThree.OrthogonalInvolutions.omegaGroup (Spin.quadPlus 2 (GaloisField 2 f))
          (Spin.nondegenerate_polarBilin_quadPlus 2 (GaloisField 2 f))))
    (hJ : J' = Subgroup.map r ρ.range)
    {a₁ a₂ : bmsdop_V k f}
    (ha₁ : a₁ ≠ 0) (ha₂ : a₂ ≠ 0)
    (hlin : LinearIndependent (GaloisField 2 f) ![a₁, a₂])
    (hQ₁ : (bmsdop_Q k f) a₁ = 0) (hQ₂ : (bmsdop_Q k f) a₂ = 0)
    (hpol : QuadraticMap.polar (bmsdop_Q k f) a₁ a₂ = 0)
    (hle : siegelGroup (bmsdop_Q k f) a₁ a₂ ≤ J'.map (Spin.spinAction (bmsdop_Q k f))) :
    ∃ (b₁ b₂ : Fin 2 ⊕ Fin 2 → GaloisField 2 f),
      a₁ = (θ b₁ : bmsdop_V k f) ∧ a₂ = (θ b₂ : bmsdop_V k f) ∧
      b₁ ≠ 0 ∧ b₂ ≠ 0 ∧ LinearIndependent (GaloisField 2 f) ![b₁, b₂] ∧
      (Spin.quadPlus 2 (GaloisField 2 f)) b₁ = 0 ∧
      (Spin.quadPlus 2 (GaloisField 2 f)) b₂ = 0 ∧
      QuadraticMap.polar (Spin.quadPlus 2 (GaloisField 2 f)) b₁ b₂ = 0 ∧
      siegelGroup (Spin.quadPlus 2 (GaloisField 2 f)) b₁ b₂ ≤
        ρ.range.map (Subgroup.subtype
          (CFSG.RankThree.OrthogonalInvolutions.omegaGroup (Spin.quadPlus 2 (GaloisField 2 f))
            (Spin.nondegenerate_polarBilin_quadPlus 2 (GaloisField 2 f)))) := by
  have hJ'le : J' ≤ bmsdop_Ge k f S e :=
    ((CFSG.Assembly.isComponentOf_iff_open).mp hJe).1.trans
      (Subgroup.commutator_le_self (bmsdop_Ge k f S e))
  have hEr : (Spin.spinAction (bmsdop_Q k f)).comp r =
      E.comp (Subgroup.subtype (CFSG.RankThree.OrthogonalInvolutions.omegaGroup
        (Spin.quadPlus 2 (GaloisField 2 f))
        (Spin.nondegenerate_polarBilin_quadPlus 2 (GaloisField 2 f)))) :=
    MonoidHom.ext hr.2.2
  have hfix : ∀ c : GaloisField 2 f, ∀ v ∈ bmsdop_W' k f e,
      CFSG.ClassicalGroups.Orthogonal.eichler (bmsdop_Q k f) a₁ (c • a₂) v = v := by
    intro c v hv
    have hg : CFSG.ClassicalGroups.Orthogonal.eichler (bmsdop_Q k f) a₁ (c • a₂) ∈
        siegelGroup (bmsdop_Q k f) a₁ a₂ := Subgroup.subset_closure ⟨c, rfl⟩
    obtain ⟨x, hxJ, hxeq⟩ := Subgroup.mem_map.mp (hle hg)
    rw [hJ] at hxJ
    obtain ⟨y, _hy, hyx⟩ := Subgroup.mem_map.mp hxJ
    rw [← hxeq, ← hyx, hr.2.2 y]
    exact hE.2.2.1 y v hv
  have hpolar : ∀ w' ∈ bmsdop_W' k f e,
      QuadraticMap.polar (bmsdop_Q k f) w' a₁ = 0 ∧
      QuadraticMap.polar (bmsdop_Q k f) w' a₂ = 0 := by
    intro w' hw'
    have h := hfix 1 w' hw'
    rw [one_smul, CFSG.ClassicalGroups.Orthogonal.eichler_apply hQ₁ hpol, hQ₂, zero_mul,
      add_zero] at h
    have h' : QuadraticMap.polar (bmsdop_Q k f) w' a₁ • a₂ =
        QuadraticMap.polar (bmsdop_Q k f) w' a₂ • a₁ := by
      have hc : w' + (QuadraticMap.polar (bmsdop_Q k f) w' a₁ • a₂ -
          QuadraticMap.polar (bmsdop_Q k f) w' a₂ • a₁) = w' + 0 := by
        rw [add_zero, ← add_sub_assoc]
        exact h
      exact sub_eq_zero.mp (add_left_cancel hc)
    have hli := (LinearIndependent.pair_iff.mp hlin)
      (QuadraticMap.polar (bmsdop_Q k f) w' a₂)
      (-(QuadraticMap.polar (bmsdop_Q k f) w' a₁)) (by
        rw [neg_smul, h'.symm]
        simp)
    exact ⟨neg_eq_zero.mp hli.2, hli.1⟩
  have hmem₁ : a₁ ∈ bmsdop_W k f e :=
    bmsdop_mem_W_of_polar_W'_eq_zero k f S h1 h2 (fun w' hw' => by
      rw [QuadraticMap.polar_comm]
      exact (hpolar w' hw').1)
  have hmem₂ : a₂ ∈ bmsdop_W k f e :=
    bmsdop_mem_W_of_polar_W'_eq_zero k f S h1 h2 (fun w' hw' => by
      rw [QuadraticMap.polar_comm]
      exact (hpolar w' hw').2)
  let u₁ : Fin 2 ⊕ Fin 2 → GaloisField 2 f := θ.symm ⟨a₁, hmem₁⟩
  let u₂ : Fin 2 ⊕ Fin 2 → GaloisField 2 f := θ.symm ⟨a₂, hmem₂⟩
  have hθu₁ : (θ u₁ : bmsdop_V k f) = a₁ := by
    change (θ (θ.symm ⟨a₁, hmem₁⟩) : bmsdop_V k f) = a₁
    rw [LinearEquiv.apply_symm_apply]
  have hθu₂ : (θ u₂ : bmsdop_V k f) = a₂ := by
    change (θ (θ.symm ⟨a₂, hmem₂⟩) : bmsdop_V k f) = a₂
    rw [LinearEquiv.apply_symm_apply]
  have hu₁ne : u₁ ≠ 0 := by
    intro h0
    apply ha₁
    rw [← hθu₁, h0]
    simp
  have hu₂ne : u₂ ≠ 0 := by
    intro h0
    apply ha₂
    rw [← hθu₂, h0]
    simp
  have hlin_u : LinearIndependent (GaloisField 2 f) ![u₁, u₂] := by
    rw [LinearIndependent.pair_iff] at hlin ⊢
    intro s t hst
    apply hlin s t
    have hc := congrArg (fun x => (θ x : bmsdop_V k f)) hst
    simpa only [map_add, map_smul, Submodule.coe_add, Submodule.coe_smul, hθu₁,
      hθu₂, map_zero, Submodule.coe_zero] using hc
  have hQstd₁ : (Spin.quadPlus 2 (GaloisField 2 f)) u₁ = 0 := by
    rw [← hθ u₁]
    change (bmsdop_Q k f) (↑(θ u₁) : bmsdop_V k f) = 0
    rw [hθu₁, hQ₁]
  have hQstd₂ : (Spin.quadPlus 2 (GaloisField 2 f)) u₂ = 0 := by
    rw [← hθ u₂]
    change (bmsdop_Q k f) (↑(θ u₂) : bmsdop_V k f) = 0
    rw [hθu₂, hQ₂]
  have hpolstd : QuadraticMap.polar (⇑(Spin.quadPlus 2 (GaloisField 2 f))) u₁ u₂ = 0 := by
    rw [← bmsdop_polar_theta k f (Spin.quadPlus 2 (GaloisField 2 f)) θ hθ u₁ u₂]
    rw [hθu₁, hθu₂]
    exact hpol
  have hmapE : (siegelGroup (Spin.quadPlus 2 (GaloisField 2 f)) u₁ u₂).map E =
      siegelGroup (bmsdop_Q k f) a₁ a₂ := by
    rw [bmsdop_ext_siegel k f S h1 h2 (Spin.quadPlus 2 (GaloisField 2 f))
      (Spin.nondegenerate_polarBilin_quadPlus 2 (GaloisField 2 f)) θ hθ E hE u₁ u₂
      hQstd₁ hpolstd, hθu₁, hθu₂]
  have hJmap : J'.map (Spin.spinAction (bmsdop_Q k f)) =
      Subgroup.map E (ρ.range.map (Subgroup.subtype
        (CFSG.RankThree.OrthogonalInvolutions.omegaGroup (Spin.quadPlus 2 (GaloisField 2 f))
          (Spin.nondegenerate_polarBilin_quadPlus 2 (GaloisField 2 f))))) := by
    rw [hJ, Subgroup.map_map, hEr, ← Subgroup.map_map]
  refine ⟨u₁, u₂, hθu₁.symm, hθu₂.symm, hu₁ne, hu₂ne, hlin_u, hQstd₁, hQstd₂, hpolstd, ?_⟩
  intro x hx
  have hxE : E x ∈ Subgroup.map E (ρ.range.map (Subgroup.subtype
      (CFSG.RankThree.OrthogonalInvolutions.omegaGroup (Spin.quadPlus 2 (GaloisField 2 f))
        (Spin.nondegenerate_polarBilin_quadPlus 2 (GaloisField 2 f))))) := by
    rw [← hJmap]
    exact hle (by
      rw [← hmapE]
      exact Subgroup.mem_map.mpr ⟨x, hx, rfl⟩)
  obtain ⟨y, hy, hyx⟩ := Subgroup.mem_map.mp hxE
  have hyx' : y = x := hE.2.1 hyx
  rwa [hyx'] at hy

private lemma bmsdop_r2_closure_V_left (k f : ℕ)
    (S : Set (GL (Fin (k + 3) ⊕ Fin (k + 3)) (GaloisField 2 f)))
    {e : Matrix (Fin (k + 3) ⊕ Fin (k + 3)) (Fin (k + 3) ⊕ Fin (k + 3)) (GaloisField 2 f)}
    {J' : Subgroup ↥(spinGroup (bmsdop_Q k f))}
    (h1 : bmsdop_geom₁ k f S e) (h2 : bmsdop_geom₂ k f S e)
    (hJe : IsComponentOf J' ⁅bmsdop_Ge k f S e, bmsdop_Ge k f S e⁆)
    (θ : (Fin 2 ⊕ Fin 2 → GaloisField 2 f) ≃ₗ[GaloisField 2 f] ↥(bmsdop_W k f e))
    (hθ : ∀ x, (bmsdop_blockForm k f e) (θ x) = (Spin.quadPlus 2 (GaloisField 2 f)) x)
    (E : ((Fin 2 ⊕ Fin 2 → GaloisField 2 f) ≃ₗ[GaloisField 2 f]
        (Fin 2 ⊕ Fin 2 → GaloisField 2 f)) →*
        (bmsdop_V k f ≃ₗ[GaloisField 2 f] bmsdop_V k f))
    (hE : bmsdop_ExtProps k f S e (Spin.quadPlus 2 (GaloisField 2 f))
        (Spin.nondegenerate_polarBilin_quadPlus 2 (GaloisField 2 f)) θ E)
    (r : ↥(CFSG.RankThree.OrthogonalInvolutions.omegaGroup (Spin.quadPlus 2 (GaloisField 2 f))
          (Spin.nondegenerate_polarBilin_quadPlus 2 (GaloisField 2 f))) →*
        ↥(spinGroup (bmsdop_Q k f)))
    (hr : Function.Injective r ∧ r.range = bmsdop_Ge k f S e ∧
      ∀ g, Spin.spinAction (bmsdop_Q k f) (r g) = E g)
    (hJ : J' = Subgroup.map r (bmsdop_r2_rhoL f).range)
    {a₁ a₂ : bmsdop_V k f}
    (ha₁ : a₁ ≠ 0) (ha₂ : a₂ ≠ 0)
    (hlin : LinearIndependent (GaloisField 2 f) ![a₁, a₂])
    (hQ₁ : (bmsdop_Q k f) a₁ = 0) (hQ₂ : (bmsdop_Q k f) a₂ = 0)
    (hpol : QuadraticMap.polar (bmsdop_Q k f) a₁ a₂ = 0)
    (hle : siegelGroup (bmsdop_Q k f) a₁ a₂ ≤ J'.map (Spin.spinAction (bmsdop_Q k f))) :
    ∃ (b₁ b₂ : Fin 2 ⊕ Fin 2 → GaloisField 2 f),
      a₁ = (θ b₁ : bmsdop_V k f) ∧ a₂ = (θ b₂ : bmsdop_V k f) ∧
      b₁ ≠ 0 ∧ b₂ ≠ 0 ∧ LinearIndependent (GaloisField 2 f) ![b₁, b₂] ∧
      (Spin.quadPlus 2 (GaloisField 2 f)) b₁ = 0 ∧
      (Spin.quadPlus 2 (GaloisField 2 f)) b₂ = 0 ∧
      QuadraticMap.polar (Spin.quadPlus 2 (GaloisField 2 f)) b₁ b₂ = 0 ∧
      siegelGroup (Spin.quadPlus 2 (GaloisField 2 f)) b₁ b₂ ≤
        (bmsdop_r2_rhoL f).range.map (Subgroup.subtype
          (CFSG.RankThree.OrthogonalInvolutions.omegaGroup (Spin.quadPlus 2 (GaloisField 2 f))
            (Spin.nondegenerate_polarBilin_quadPlus 2 (GaloisField 2 f)))) := by
  exact bmsdop_r2_closure_V_aux k f S h1 h2 hJe θ hθ E hE r hr (bmsdop_r2_rhoL f) hJ
    ha₁ ha₂ hlin hQ₁ hQ₂ hpol hle

private lemma bmsdop_r2_closure_V_right (k f : ℕ)
    (S : Set (GL (Fin (k + 3) ⊕ Fin (k + 3)) (GaloisField 2 f)))
    {e : Matrix (Fin (k + 3) ⊕ Fin (k + 3)) (Fin (k + 3) ⊕ Fin (k + 3)) (GaloisField 2 f)}
    {J' : Subgroup ↥(spinGroup (bmsdop_Q k f))}
    (h1 : bmsdop_geom₁ k f S e) (h2 : bmsdop_geom₂ k f S e)
    (hJe : IsComponentOf J' ⁅bmsdop_Ge k f S e, bmsdop_Ge k f S e⁆)
    (θ : (Fin 2 ⊕ Fin 2 → GaloisField 2 f) ≃ₗ[GaloisField 2 f] ↥(bmsdop_W k f e))
    (hθ : ∀ x, (bmsdop_blockForm k f e) (θ x) = (Spin.quadPlus 2 (GaloisField 2 f)) x)
    (E : ((Fin 2 ⊕ Fin 2 → GaloisField 2 f) ≃ₗ[GaloisField 2 f]
        (Fin 2 ⊕ Fin 2 → GaloisField 2 f)) →*
        (bmsdop_V k f ≃ₗ[GaloisField 2 f] bmsdop_V k f))
    (hE : bmsdop_ExtProps k f S e (Spin.quadPlus 2 (GaloisField 2 f))
        (Spin.nondegenerate_polarBilin_quadPlus 2 (GaloisField 2 f)) θ E)
    (r : ↥(CFSG.RankThree.OrthogonalInvolutions.omegaGroup (Spin.quadPlus 2 (GaloisField 2 f))
          (Spin.nondegenerate_polarBilin_quadPlus 2 (GaloisField 2 f))) →*
        ↥(spinGroup (bmsdop_Q k f)))
    (hr : Function.Injective r ∧ r.range = bmsdop_Ge k f S e ∧
      ∀ g, Spin.spinAction (bmsdop_Q k f) (r g) = E g)
    (hJ : J' = Subgroup.map r (bmsdop_r2_rhoR f).range)
    {a₁ a₂ : bmsdop_V k f}
    (ha₁ : a₁ ≠ 0) (ha₂ : a₂ ≠ 0)
    (hlin : LinearIndependent (GaloisField 2 f) ![a₁, a₂])
    (hQ₁ : (bmsdop_Q k f) a₁ = 0) (hQ₂ : (bmsdop_Q k f) a₂ = 0)
    (hpol : QuadraticMap.polar (bmsdop_Q k f) a₁ a₂ = 0)
    (hle : siegelGroup (bmsdop_Q k f) a₁ a₂ ≤ J'.map (Spin.spinAction (bmsdop_Q k f))) :
    ∃ (b₁ b₂ : Fin 2 ⊕ Fin 2 → GaloisField 2 f),
      a₁ = (θ b₁ : bmsdop_V k f) ∧ a₂ = (θ b₂ : bmsdop_V k f) ∧
      b₁ ≠ 0 ∧ b₂ ≠ 0 ∧ LinearIndependent (GaloisField 2 f) ![b₁, b₂] ∧
      (Spin.quadPlus 2 (GaloisField 2 f)) b₁ = 0 ∧
      (Spin.quadPlus 2 (GaloisField 2 f)) b₂ = 0 ∧
      QuadraticMap.polar (Spin.quadPlus 2 (GaloisField 2 f)) b₁ b₂ = 0 ∧
      siegelGroup (Spin.quadPlus 2 (GaloisField 2 f)) b₁ b₂ ≤
        (bmsdop_r2_rhoR f).range.map (Subgroup.subtype
          (CFSG.RankThree.OrthogonalInvolutions.omegaGroup (Spin.quadPlus 2 (GaloisField 2 f))
            (Spin.nondegenerate_polarBilin_quadPlus 2 (GaloisField 2 f)))) := by
  exact bmsdop_r2_closure_V_aux k f S h1 h2 hJe θ hθ E hE r hr (bmsdop_r2_rhoR f) hJ
    ha₁ ha₂ hlin hQ₁ hQ₂ hpol hle

private lemma bmsdop_r2_closure_data
    (k f : ℕ) (hf : 1 ≤ f)
    (S : Set (GL (Fin (k + 3) ⊕ Fin (k + 3)) (GaloisField 2 f)))
    {e : Matrix (Fin (k + 3) ⊕ Fin (k + 3)) (Fin (k + 3) ⊕ Fin (k + 3)) (GaloisField 2 f)}
    {J' : Subgroup ↥(spinGroup (bmsdop_Q k f))}
    (h1 : bmsdop_geom₁ k f S e) (h2 : bmsdop_geom₂ k f S e)
    (hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s')
    (heA : e ∈ Algebra.adjoin (GaloisField 2 f) (Units.val '' S))
    (hJe : IsComponentOf J' ⁅bmsdop_Ge k f S e, bmsdop_Ge k f S e⁆)
    (θ : (Fin 2 ⊕ Fin 2 → GaloisField 2 f) ≃ₗ[GaloisField 2 f] ↥(bmsdop_W k f e))
    (hθ : ∀ x, (bmsdop_blockForm k f e) (θ x) = (Spin.quadPlus 2 (GaloisField 2 f)) x)
    (hrank : e.rank = 4)
    (hcard : Nat.card (GaloisField 2 f) ≠ 2) :
    bmsdop_r2_PSLClosureData k f S e J' := by
  obtain ⟨E, hE⟩ := bmsdop_ext k f S h1 h2 (Spin.quadPlus 2 (GaloisField 2 f)) θ hθ
    (Spin.nondegenerate_polarBilin_quadPlus 2 (GaloisField 2 f))
  obtain ⟨r, hrinj, hrrange, hrspin⟩ :=
    bmsdop_r2_restrict k f S h1 h2 hS heA θ hθ E hE
  obtain ⟨hOmega, hq₁, hq₂, hcomm, -, -, -⟩ := bmsdop_r2_split f hcard
  have hcomp := bmsdop_r2_component k f S hJe r ⟨hrinj, hrrange⟩
    ((bmsdop_r2_rhoL f).range) ((bmsdop_r2_rhoR f).range) hOmega hq₁ hq₂ hcomm
  have hEr : (Spin.spinAction (bmsdop_Q k f)).comp r =
      E.comp (Subgroup.subtype (CFSG.RankThree.OrthogonalInvolutions.omegaGroup
        (Spin.quadPlus 2 (GaloisField 2 f))
        (Spin.nondegenerate_polarBilin_quadPlus 2 (GaloisField 2 f)))) :=
    MonoidHom.ext hrspin
  rcases hcomp with hJ | hJ
  · let ρ : (ggU .PSL 2 f).K →*
        ↥(CFSG.RankThree.OrthogonalInvolutions.omegaGroup (Spin.quadPlus 2 (GaloisField 2 f))
          (Spin.nondegenerate_polarBilin_quadPlus 2 (GaloisField 2 f))) := bmsdop_r2_rhoL f
    have hρ : ρ = bmsdop_r2_rhoL f := rfl
    refine ⟨r.comp ρ, ?_, ?_, ?_⟩
    · exact bmsdop_r2_model_data_center k f S E r ⟨hrinj, hrrange⟩ ρ (Or.inl hρ)
    · rw [MonoidHom.range_comp, hρ]
      exact hJ.symm
    · intro a₁ a₂ ha₁ ha₂ hlin hQ₁ hQ₂ hpol hle
      obtain ⟨b₁, b₂, hb₁, hb₂, hb₁ne, hb₂ne, hblin, hbQ₁, hbQ₂, hbpol, hble⟩ :=
        bmsdop_r2_closure_V_left k f S h1 h2 hJe θ hθ E hE r ⟨hrinj, hrrange, hrspin⟩ hJ
          ha₁ ha₂ hlin hQ₁ hQ₂ hpol hle
      obtain ⟨β, u, hβroot, hβlong, heq⟩ :=
        bmsdop_r2_closure_Qstd_left f hcard b₁ b₂ hb₁ne hb₂ne hblin hbQ₁ hbQ₂ hbpol hble
      refine ⟨β, u, hβroot, hβlong, ?_⟩
      show Subgroup.map (Spin.spinAction (bmsdop_Q k f))
          (Subgroup.map (r.comp (bmsdop_r2_rhoL f))
            (Subgroup.map (MulAut.conj u).toMonoidHom
              ((SpecialLinear.rootDatum 1 (GaloisField 2 f)).rootGroup β))) =
        siegelGroup (bmsdop_Q k f) a₁ a₂
      rw [Subgroup.map_map, ← MonoidHom.comp_assoc, hEr, MonoidHom.comp_assoc,
        ← Subgroup.map_map]
      rw [heq]
      rw [bmsdop_ext_siegel k f S h1 h2 (Spin.quadPlus 2 (GaloisField 2 f))
        (Spin.nondegenerate_polarBilin_quadPlus 2 (GaloisField 2 f)) θ hθ E hE b₁ b₂ hbQ₁ hbpol]
      rw [hb₁, hb₂]
  · let ρ : (ggU .PSL 2 f).K →*
        ↥(CFSG.RankThree.OrthogonalInvolutions.omegaGroup (Spin.quadPlus 2 (GaloisField 2 f))
          (Spin.nondegenerate_polarBilin_quadPlus 2 (GaloisField 2 f))) := bmsdop_r2_rhoR f
    have hρ : ρ = bmsdop_r2_rhoR f := rfl
    refine ⟨r.comp ρ, ?_, ?_, ?_⟩
    · exact bmsdop_r2_model_data_center k f S E r ⟨hrinj, hrrange⟩ ρ (Or.inr hρ)
    · rw [MonoidHom.range_comp, hρ]
      exact hJ.symm
    · intro a₁ a₂ ha₁ ha₂ hlin hQ₁ hQ₂ hpol hle
      obtain ⟨b₁, b₂, hb₁, hb₂, hb₁ne, hb₂ne, hblin, hbQ₁, hbQ₂, hbpol, hble⟩ :=
        bmsdop_r2_closure_V_right k f S h1 h2 hJe θ hθ E hE r ⟨hrinj, hrrange, hrspin⟩ hJ
          ha₁ ha₂ hlin hQ₁ hQ₂ hpol hle
      obtain ⟨β, u, hβroot, hβlong, heq⟩ :=
        bmsdop_r2_closure_Qstd_right f hcard b₁ b₂ hb₁ne hb₂ne hblin hbQ₁ hbQ₂ hbpol hble
      refine ⟨β, u, hβroot, hβlong, ?_⟩
      show Subgroup.map (Spin.spinAction (bmsdop_Q k f))
          (Subgroup.map (r.comp (bmsdop_r2_rhoR f))
            (Subgroup.map (MulAut.conj u).toMonoidHom
              ((SpecialLinear.rootDatum 1 (GaloisField 2 f)).rootGroup β))) =
        siegelGroup (bmsdop_Q k f) a₁ a₂
      rw [Subgroup.map_map, ← MonoidHom.comp_assoc, hEr, MonoidHom.comp_assoc,
        ← Subgroup.map_map]
      rw [heq]
      rw [bmsdop_ext_siegel k f S h1 h2 (Spin.quadPlus 2 (GaloisField 2 f))
        (Spin.nondegenerate_polarBilin_quadPlus 2 (GaloisField 2 f)) θ hθ E hE b₁ b₂ hbQ₁ hbpol]
      rw [hb₁, hb₂]

private lemma bmsdop_geom_rank_ne_zero (k f : ℕ)
    (S : Set (GL (Fin (k + 3) ⊕ Fin (k + 3)) (GaloisField 2 f)))
    {e : Matrix (Fin (k + 3) ⊕ Fin (k + 3)) (Fin (k + 3) ⊕ Fin (k + 3)) (GaloisField 2 f)}
    (h1 : bmsdop_geom₁ k f S e) : e.rank ≠ 0 := by
  have hrank_eq : e.rank = Module.finrank (GaloisField 2 f)
      (LinearMap.range (Matrix.toLin' e)) := by
    rw [Matrix.rank_eq_finrank_range_toLin e (Pi.basisFun (GaloisField 2 f) _)
      (Pi.basisFun (GaloisField 2 f) _), Matrix.toLin_eq_toLin']
  intro h0
  have hbot : LinearMap.range (Matrix.toLin' e) = ⊥ := by
    rw [← Submodule.finrank_eq_zero, ← hrank_eq]
    exact h0
  have hzero : Matrix.toLin' e = Matrix.toLin' (0 : Matrix (Fin (k + 3) ⊕ Fin (k + 3))
      (Fin (k + 3) ⊕ Fin (k + 3)) (GaloisField 2 f)) := by
    rw [LinearMap.range_eq_bot.mp hbot, Matrix.toLin'_apply', Matrix.mulVecLin_zero]
  exact h1.2.1 (Matrix.toLin'.injective hzero)

private lemma bmsdop_component_bot_false
    (k f : ℕ)
    (S : Set (GL (Fin (k + 3) ⊕ Fin (k + 3)) (GaloisField 2 f)))
    {e : Matrix (Fin (k + 3) ⊕ Fin (k + 3)) (Fin (k + 3) ⊕ Fin (k + 3)) (GaloisField 2 f)}
    {J' : Subgroup ↥(spinGroup (bmsdop_Q k f))}
    (hJe : IsComponentOf J' ⁅bmsdop_Ge k f S e, bmsdop_Ge k f S e⁆)
    (hcomm : ⁅bmsdop_Ge k f S e, bmsdop_Ge k f S e⁆ = ⊥) : False := by
  have hle : J' ≤ (⊥ : Subgroup ↥(spinGroup (bmsdop_Q k f))) := by
    simpa only [hcomm] using hJe.1
  have hJbot : J' = ⊥ := le_bot_iff.mp hle
  haveI : Subsingleton J' := by rw [hJbot]; infer_instance
  obtain ⟨-, hsimpleJ⟩ := hJe.2.2
  haveI : Nontrivial (J' ⧸ Subgroup.center J') := hsimpleJ.toNontrivial
  haveI : Nontrivial J' :=
    Function.Surjective.nontrivial (QuotientGroup.mk'_surjective (Subgroup.center J'))
  exact (not_subsingleton_iff_nontrivial.mpr (inferInstance : Nontrivial J'))
    (inferInstance : Subsingleton J')

private lemma bmsdop_commutator_bot_of_two_dim
    (k f : ℕ)
    (S : Set (GL (Fin (k + 3) ⊕ Fin (k + 3)) (GaloisField 2 f)))
    {e : Matrix (Fin (k + 3) ⊕ Fin (k + 3)) (Fin (k + 3) ⊕ Fin (k + 3)) (GaloisField 2 f)}
    (h1 : bmsdop_geom₁ k f S e) (h2 : bmsdop_geom₂ k f S e)
    (hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s')
    (heA : e ∈ Algebra.adjoin (GaloisField 2 f) (Units.val '' S))
    {Vstd : Type} [AddCommGroup Vstd] [Module (GaloisField 2 f) Vstd]
    [FiniteDimensional (GaloisField 2 f) Vstd]
    (Qstd : QuadraticForm (GaloisField 2 f) Vstd)
    (hnd : (QuadraticMap.polarBilin Qstd).Nondegenerate)
    (hfr : Module.finrank (GaloisField 2 f) Vstd = 2)
    (θ : Vstd ≃ₗ[GaloisField 2 f] ↥(bmsdop_W k f e))
    (hθ : ∀ x, (bmsdop_blockForm k f e) (θ x) = Qstd x) :
    ⁅bmsdop_Ge k f S e, bmsdop_Ge k f S e⁆ = ⊥ := by
  classical
  have hb := bmsdop_glue_basic k f S h1 h2 Qstd θ hθ
  have hE : bmsdop_ExtProps k f S e Qstd hnd θ (bmsdop_glue k f S h1 θ) :=
    ⟨hb.1, hb.2.1, hb.2.2.1, hb.2.2.2,
      fun g => bmsdop_glue_omegaGroup k f S h1 h2 Qstd θ hθ hnd g⟩
  have hmap := bmsdop_block_group_eq_ext k f S h1 h2 hS heA Qstd hnd
    (bmsdop_glue k f S h1 θ) θ hE
  have hωcomm : ∀ x y : Vstd ≃ₗ[GaloisField 2 f] Vstd,
      x ∈ CFSG.RankThree.OrthogonalInvolutions.omegaGroup Qstd hnd →
      y ∈ CFSG.RankThree.OrthogonalInvolutions.omegaGroup Qstd hnd → x * y = y * x := by
    intro x y hx hy
    have hxO : x ∈ TauCeti.QuadraticMap.orthogonalGroup Qstd := hx.1
    have hyO : y ∈ TauCeti.QuadraticMap.orthogonalGroup Qstd := hy.1
    have hdick : ∀ (z : Vstd ≃ₗ[GaloisField 2 f] Vstd)
        (hz : z ∈ CFSG.RankThree.OrthogonalInvolutions.omegaGroup Qstd hnd),
        CFSG.RankThree.OrthogonalInvolutions.dicksonHom Qstd hnd ⟨z, hz.1⟩ = 1 := by
      intro z hz
      have hzker : (⟨z, hz.1⟩ : TauCeti.QuadraticMap.orthogonalGroup Qstd) ∈
          (CFSG.RankThree.OrthogonalInvolutions.dicksonHom Qstd hnd).ker := by
        rw [CFSG.RankThree.OrthogonalInvolutions.dicksonHom_ker, Subgroup.mem_subgroupOf]
        exact hz
      exact MonoidHom.mem_ker.mp hzker
    exact CFSG.RankThree.PartOne.KCOrthogonal.commute_of_dicksonHom_eq_one hnd hfr hxO hyO
      (hdick x hx) (hdick y hy)
  have hcommG : IsMulCommutative ↥(bmsdop_Ge k f S e) := by
    refine isMulCommutative_iff.mpr ?_
    intro a b
    apply Subtype.ext
    apply bmsdop_spinAction_injective k f
    simp only [Subgroup.coe_mul]
    rw [map_mul, map_mul]
    have ha : Spin.spinAction (bmsdop_Q k f) a ∈
        (CFSG.RankThree.OrthogonalInvolutions.omegaGroup Qstd hnd).map
          (bmsdop_glue k f S h1 θ) := by
      rw [← hmap]
      exact Subgroup.mem_map.mpr ⟨a, a.2, rfl⟩
    have hbm : Spin.spinAction (bmsdop_Q k f) b ∈
        (CFSG.RankThree.OrthogonalInvolutions.omegaGroup Qstd hnd).map
          (bmsdop_glue k f S h1 θ) := by
      rw [← hmap]
      exact Subgroup.mem_map.mpr ⟨b, b.2, rfl⟩
    obtain ⟨a', ha'mem, ha'eq⟩ := Subgroup.mem_map.mp ha
    obtain ⟨b', hb'mem, hb'eq⟩ := Subgroup.mem_map.mp hbm
    rw [← ha'eq, ← hb'eq, ← map_mul, ← map_mul, hωcomm a' b' ha'mem hb'mem]
  have hmap2 : Subgroup.map (Subgroup.subtype (bmsdop_Ge k f S e))
      (commutator ↥(bmsdop_Ge k f S e)) =
        ⁅bmsdop_Ge k f S e, bmsdop_Ge k f S e⁆ := by
    rw [commutator_def, Subgroup.map_commutator, Subgroup.map_top, Subgroup.range_subtype]
  rw [← hmap2, (commutator_eq_bot_iff ↥(bmsdop_Ge k f S e)).mpr hcommG,
    Subgroup.map_bot]

private lemma bmsdop_minus_two_no_singular_pair
    (f : ℕ) (β γ : GaloisField 2 f)
    (hirr : ∀ s : GaloisField 2 f, s ^ 2 + β * s + γ ≠ 0)
    (x y : Fin (2 - 1) ⊕ Fin (2 - 1) ⊕ Fin 2 → GaloisField 2 f)
    (hx : (Spin.quadMinus 2 (GaloisField 2 f) β γ) x = 0)
    (hy : (Spin.quadMinus 2 (GaloisField 2 f) β γ) y = 0)
    (hpol : QuadraticMap.polar (Spin.quadMinus 2 (GaloisField 2 f) β γ) x y = 0) :
    ¬ LinearIndependent (GaloisField 2 f) ![x, y] := by
  intro hLI
  set T : Submodule (GaloisField 2 f)
      (Fin (2 - 1) ⊕ Fin (2 - 1) ⊕ Fin 2 → GaloisField 2 f) :=
    Submodule.span (GaloisField 2 f) ({x, y} : Set _) with hTdef
  have hrange : Set.range ![x, y] = ({x, y} : Set _) := by
    ext z
    constructor
    · rintro ⟨i, rfl⟩
      fin_cases i <;> simp
    · intro hz
      rcases hz with rfl | rfl
      · exact ⟨0, by simp⟩
      · exact ⟨1, by simp⟩
  have hfinT : Module.finrank (GaloisField 2 f) T = 2 := by
    rw [hTdef, ← hrange, finrank_span_eq_card hLI]
    simp
  have hsing : ∀ w ∈ T, (Spin.quadMinus 2 (GaloisField 2 f) β γ) w = 0 := by
    intro w hw
    rw [hTdef, Submodule.mem_span_pair] at hw
    obtain ⟨a, b, rfl⟩ := hw
    rw [QuadraticMap.map_add (Spin.quadMinus 2 (GaloisField 2 f) β γ),
      QuadraticMap.map_smul, QuadraticMap.map_smul, hx, hy,
      QuadraticMap.polar_smul_left, QuadraticMap.polar_smul_right, hpol]
    simp
  have hminus := CFSG.ClassicalGroups.Orthogonal.isMinus_quadMinus (K := GaloisField 2 f)
    (m := 2) (b := β) (c := γ) (by norm_num) hirr
  obtain ⟨u, hu, hune⟩ := hminus.noTS T hfinT
  exact hune (hsing u hu)

private lemma bmsdop_minus_two_block_no_singular_pair
    (k f : ℕ) (S : Set (GL (Fin (k + 3) ⊕ Fin (k + 3)) (GaloisField 2 f)))
    {e : Matrix (Fin (k + 3) ⊕ Fin (k + 3)) (Fin (k + 3) ⊕ Fin (k + 3)) (GaloisField 2 f)}
    (h1 : bmsdop_geom₁ k f S e) (h2 : bmsdop_geom₂ k f S e)
    (β γ : GaloisField 2 f)
    (hirr : ∀ s : GaloisField 2 f, s ^ 2 + β * s + γ ≠ 0)
    (θ : (Fin (2 - 1) ⊕ Fin (2 - 1) ⊕ Fin 2 → GaloisField 2 f) ≃ₗ[GaloisField 2 f]
      ↥(bmsdop_W k f e))
    (hθ : ∀ x, (bmsdop_blockForm k f e) (θ x) = (Spin.quadMinus 2 (GaloisField 2 f) β γ) x) :
    ∀ x y : (Fin (k + 3) ⊕ Fin (k + 3)) → (GaloisField 2 f),
      Matrix.mulVec e x = x → Matrix.mulVec e y = y →
      (bmsdop_Q k f) x = 0 → (bmsdop_Q k f) y = 0 →
      QuadraticMap.polar (bmsdop_Q k f) x y = 0 →
      ¬ LinearIndependent (GaloisField 2 f) ![x, y] := by
  intro x y hx hy hQx hQy hpol hLI
  let x' : ↥(bmsdop_W k f e) := ⟨x, ⟨x, by rw [Matrix.toLin'_apply]; exact hx⟩⟩
  let y' : ↥(bmsdop_W k f e) := ⟨y, ⟨y, by rw [Matrix.toLin'_apply]; exact hy⟩⟩
  have hLI' : LinearIndependent (GaloisField 2 f) ![x', y'] := by
    have hfun : (⇑(bmsdop_W k f e).subtype ∘ ![x', y']) = ![x, y] := by
      funext i
      fin_cases i <;> rfl
    refine LinearIndependent.of_comp (bmsdop_W k f e).subtype ?_
    rw [hfun]
    exact hLI
  let u : Fin (2 - 1) ⊕ Fin (2 - 1) ⊕ Fin 2 → GaloisField 2 f := θ.symm x'
  let w : Fin (2 - 1) ⊕ Fin (2 - 1) ⊕ Fin 2 → GaloisField 2 f := θ.symm y'
  have hbx : (bmsdop_blockForm k f e) x' = 0 := hQx
  have hby : (bmsdop_blockForm k f e) y' = 0 := hQy
  have hqu : (Spin.quadMinus 2 (GaloisField 2 f) β γ) u = 0 := by
    have h := hθ u
    rw [show θ u = x' from LinearEquiv.apply_symm_apply θ x'] at h
    rw [← h]
    exact hbx
  have hqw : (Spin.quadMinus 2 (GaloisField 2 f) β γ) w = 0 := by
    have h := hθ w
    rw [show θ w = y' from LinearEquiv.apply_symm_apply θ y'] at h
    rw [← h]
    exact hby
  have hpolar : QuadraticMap.polar (Spin.quadMinus 2 (GaloisField 2 f) β γ) u w = 0 := by
    have h := bmsdop_polar_theta k f (Spin.quadMinus 2 (GaloisField 2 f) β γ) θ hθ u w
    have hθu : (θ u : bmsdop_V k f) = x := by
      rw [show θ u = x' from LinearEquiv.apply_symm_apply θ x']
    have hθw : (θ w : bmsdop_V k f) = y := by
      rw [show θ w = y' from LinearEquiv.apply_symm_apply θ y']
    rw [← h, hθu, hθw, hpol]
  have hLIu : LinearIndependent (GaloisField 2 f) ![u, w] := by
    have hfun : (⇑θ.symm.toLinearMap ∘ ![x', y']) = ![u, w] := by
      funext i
      fin_cases i <;> rfl
    have hmap := LinearIndependent.map' hLI' θ.symm.toLinearMap
      (LinearMap.ker_eq_bot.mpr θ.symm.injective)
    simpa only [hfun] using hmap
  exact bmsdop_minus_two_no_singular_pair f β γ hirr u w hqu hqw hpolar hLIu

private lemma bmsdopx_rank_eq_finrank_range {ι F : Type} [Fintype ι] [DecidableEq ι] [Field F]
    (e : Matrix ι ι F) :
    e.rank = Module.finrank F (LinearMap.range (Matrix.toLin' e)) := by
  rw [Matrix.range_toLin' e]
  rw [← Matrix.rank_transpose e, Matrix.rank_eq_finrank_span_row (Matrix.transpose e)]
  rw [show (Matrix.transpose e).row = Matrix.col e from by ext i j; rfl]

private def bmsdopx_FrozenConcl
    (k f : ℕ)
    (S : Set (GL (Fin (k + 3) ⊕ Fin (k + 3)) (GaloisField 2 f)))
    (e : Matrix (Fin (k + 3) ⊕ Fin (k + 3)) (Fin (k + 3) ⊕ Fin (k + 3)) (GaloisField 2 f))
    (J' : Subgroup ↥(spinGroup (bmsdop_Q k f))) : Prop :=
  ∃ (t' : StatedLieTag) (m : ℕ)
    (ι : (ggU t' m f).K →* ↥(spinGroup (bmsdop_Q k f)))
    (β₀ : Fin (ggU t' m f).D.rank → ℤ),
    (((t' = .POmegaPlus ∨ t' = .POmegaMinus) ∧ 3 ≤ m ∧ 2 * m =
        Module.finrank (GaloisField 2 f) (LinearMap.range (Matrix.toLin' e))) ∨
      (t' = .PSL ∧ m = 2 ∧
        Module.finrank (GaloisField 2 f) (LinearMap.range (Matrix.toLin' e)) = 4)) ∧
    GGLongRoot (ggU t' m f).D β₀ ∧
    (∀ y, ι y ∈ Subgroup.center ↥(spinGroup (bmsdop_Q k f)) →
      y ∈ Subgroup.center (ggU t' m f).K) ∧ ι.range = J' ∧
    ∃ a₁ a₂ b₁ b₂ : (Fin (k + 3) ⊕ Fin (k + 3)) → (GaloisField 2 f),
      ((bmsdop_Q k f) a₁ = 0 ∧ (bmsdop_Q k f) a₂ = 0 ∧ (bmsdop_Q k f) b₁ = 0 ∧
        (bmsdop_Q k f) b₂ = 0) ∧
      QuadraticMap.polar (bmsdop_Q k f) a₁ b₁ = 1 ∧
      QuadraticMap.polar (bmsdop_Q k f) a₂ b₂ = 1 ∧
      (QuadraticMap.polar (bmsdop_Q k f) a₁ a₂ = 0 ∧
        QuadraticMap.polar (bmsdop_Q k f) b₁ b₂ = 0 ∧
        QuadraticMap.polar (bmsdop_Q k f) a₁ b₂ = 0 ∧
        QuadraticMap.polar (bmsdop_Q k f) a₂ b₁ = 0) ∧
      (((ggU t' m f).D.rootGroup β₀).map ι).map (Spin.spinAction (bmsdop_Q k f)) =
        siegelGroup (bmsdop_Q k f) a₁ a₂ ∧
      (((ggU t' m f).D.rootGroup (-β₀)).map ι).map (Spin.spinAction (bmsdop_Q k f)) =
        siegelGroup (bmsdop_Q k f) b₁ b₂

private def bmsdopx_FrozenClosure
    (k f : ℕ)
    (S : Set (GL (Fin (k + 3) ⊕ Fin (k + 3)) (GaloisField 2 f)))
    (e : Matrix (Fin (k + 3) ⊕ Fin (k + 3)) (Fin (k + 3) ⊕ Fin (k + 3)) (GaloisField 2 f))
    (J' : Subgroup ↥(spinGroup (bmsdop_Q k f))) : Prop :=
  ∃ (t' : StatedLieTag) (m : ℕ)
    (ι : (ggU t' m f).K →* ↥(spinGroup (bmsdop_Q k f))),
    (((t' = .POmegaPlus ∨ t' = .POmegaMinus) ∧ 3 ≤ m ∧ 2 * m =
        Module.finrank (GaloisField 2 f) (LinearMap.range (Matrix.toLin' e))) ∨
      (t' = .PSL ∧ m = 2 ∧
        Module.finrank (GaloisField 2 f) (LinearMap.range (Matrix.toLin' e)) = 4)) ∧
    (∀ y, ι y ∈ Subgroup.center ↥(spinGroup (bmsdop_Q k f)) →
      y ∈ Subgroup.center (ggU t' m f).K) ∧ ι.range = J' ∧
    (∀ a₁ a₂ : ((Fin (k + 3) ⊕ Fin (k + 3)) → GaloisField 2 f), a₁ ≠ 0 → a₂ ≠ 0 →
        LinearIndependent (GaloisField 2 f) ![a₁, a₂] → (bmsdop_Q k f) a₁ = 0 →
        (bmsdop_Q k f) a₂ = 0 → QuadraticMap.polar (bmsdop_Q k f) a₁ a₂ = 0 →
        siegelGroup (bmsdop_Q k f) a₁ a₂ ≤ J'.map (Spin.spinAction (bmsdop_Q k f)) →
      ∃ (β : Fin (ggU t' m f).D.rank → ℤ) (u : (ggU t' m f).K),
        β ∈ (ggU t' m f).D.roots ∧ GGLongRoot (ggU t' m f).D β ∧
        ((((ggU t' m f).D.rootGroup β).map (MulAut.conj u).toMonoidHom).map ι).map
          (Spin.spinAction (bmsdop_Q k f)) = siegelGroup (bmsdop_Q k f) a₁ a₂)

private lemma bmsdopx_frozenConcl_plus_of_data
    (k f : ℕ)
    (S : Set (GL (Fin (k + 3) ⊕ Fin (k + 3)) (GaloisField 2 f)))
    {e : Matrix (Fin (k + 3) ⊕ Fin (k + 3)) (Fin (k + 3) ⊕ Fin (k + 3)) (GaloisField 2 f)}
    {J' : Subgroup ↥(spinGroup (bmsdop_Q k f))}
    (ρ : ℕ) (hρ3 : 3 ≤ ρ) (hrank : e.rank = 2 * ρ)
    (data : ∃ (β₀ : Fin (Spin.plusDatum ρ (GaloisField 2 f) hρ3).rank → ℤ)
      (ι : spinGroup (Spin.quadPlus ρ (GaloisField 2 f)) →* ↥(spinGroup (bmsdop_Q k f))),
      GGPosTag .POmegaPlus ∧ 1 ≤ f ∧
      GGLongRoot (Spin.plusDatum ρ (GaloisField 2 f) hρ3) β₀ ∧
      (∀ y, ι y ∈ Subgroup.center ↥(spinGroup (bmsdop_Q k f)) →
        y ∈ Subgroup.center (spinGroup (Spin.quadPlus ρ (GaloisField 2 f)))) ∧
      ι.range = J' ∧
      ∃ a₁ a₂ b₁ b₂ : ((Fin (k + 3) ⊕ Fin (k + 3)) → GaloisField 2 f),
        ((bmsdop_Q k f) a₁ = 0 ∧ (bmsdop_Q k f) a₂ = 0 ∧
          (bmsdop_Q k f) b₁ = 0 ∧ (bmsdop_Q k f) b₂ = 0) ∧
        QuadraticMap.polar (bmsdop_Q k f) a₁ b₁ = 1 ∧
        QuadraticMap.polar (bmsdop_Q k f) a₂ b₂ = 1 ∧
        (QuadraticMap.polar (bmsdop_Q k f) a₁ a₂ = 0 ∧
          QuadraticMap.polar (bmsdop_Q k f) b₁ b₂ = 0 ∧
          QuadraticMap.polar (bmsdop_Q k f) a₁ b₂ = 0 ∧
          QuadraticMap.polar (bmsdop_Q k f) a₂ b₁ = 0) ∧
        ((((Spin.plusDatum ρ (GaloisField 2 f) hρ3).rootGroup β₀).map ι).map
          (Spin.spinAction (bmsdop_Q k f)) = siegelGroup (bmsdop_Q k f) a₁ a₂) ∧
        ((((Spin.plusDatum ρ (GaloisField 2 f) hρ3).rootGroup (-β₀)).map ι).map
          (Spin.spinAction (bmsdop_Q k f)) = siegelGroup (bmsdop_Q k f) b₁ b₂)) :
    bmsdopx_FrozenConcl k f S e J' := by
  obtain ⟨β₀, ι, -, -, hlong, hcenter, hrange, a₁, a₂, b₁, b₂, hframe, hgrp₁, hgrp₂⟩ := data
  have hgg : ggU .POmegaPlus ρ f =
      ⟨spinGroup (Spin.quadPlus ρ (GaloisField 2 f)),
        Spin.plusDatum ρ (GaloisField 2 f) hρ3⟩ := by
    simp only [ggU, lieUniversal, hρ3, ↓reduceDIte]
  have hrank' : 2 * ρ = Module.finrank (GaloisField 2 f)
      (LinearMap.range (Matrix.toLin' e)) := by
    rw [← bmsdopx_rank_eq_finrank_range e]
    exact hrank.symm
  have hgoal : ∃ (ι : (ggU .POmegaPlus ρ f).K →* ↥(spinGroup (bmsdop_Q k f)))
      (β₀ : Fin (ggU .POmegaPlus ρ f).D.rank → ℤ),
      ((((.POmegaPlus : StatedLieTag) = .POmegaPlus ∨
          (.POmegaPlus : StatedLieTag) = .POmegaMinus) ∧ 3 ≤ ρ ∧ 2 * ρ =
        Module.finrank (GaloisField 2 f) (LinearMap.range (Matrix.toLin' e))) ∨
        ((.POmegaPlus : StatedLieTag) = .PSL ∧ ρ = 2 ∧
          Module.finrank (GaloisField 2 f) (LinearMap.range (Matrix.toLin' e)) = 4)) ∧
      GGLongRoot (ggU .POmegaPlus ρ f).D β₀ ∧
      (∀ y, ι y ∈ Subgroup.center ↥(spinGroup (bmsdop_Q k f)) →
        y ∈ Subgroup.center (ggU .POmegaPlus ρ f).K) ∧ ι.range = J' ∧
      ∃ a₁ a₂ b₁ b₂ : ((Fin (k + 3) ⊕ Fin (k + 3)) → GaloisField 2 f),
        ((bmsdop_Q k f) a₁ = 0 ∧ (bmsdop_Q k f) a₂ = 0 ∧
          (bmsdop_Q k f) b₁ = 0 ∧ (bmsdop_Q k f) b₂ = 0) ∧
        QuadraticMap.polar (bmsdop_Q k f) a₁ b₁ = 1 ∧
        QuadraticMap.polar (bmsdop_Q k f) a₂ b₂ = 1 ∧
        (QuadraticMap.polar (bmsdop_Q k f) a₁ a₂ = 0 ∧
          QuadraticMap.polar (bmsdop_Q k f) b₁ b₂ = 0 ∧
          QuadraticMap.polar (bmsdop_Q k f) a₁ b₂ = 0 ∧
          QuadraticMap.polar (bmsdop_Q k f) a₂ b₁ = 0) ∧
        ((((ggU .POmegaPlus ρ f).D.rootGroup β₀).map ι).map
          (Spin.spinAction (bmsdop_Q k f)) = siegelGroup (bmsdop_Q k f) a₁ a₂) ∧
        ((((ggU .POmegaPlus ρ f).D.rootGroup (-β₀)).map ι).map
          (Spin.spinAction (bmsdop_Q k f)) = siegelGroup (bmsdop_Q k f) b₁ b₂) :=
    hgg.symm ▸ ⟨ι, β₀, Or.inl ⟨Or.inl rfl, hρ3, hrank'⟩, hlong, hcenter, hrange,
      a₁, a₂, b₁, b₂, hframe, hgrp₁, hgrp₂⟩
  obtain ⟨ι', β₀', hdisj', hlong', hcenter', hrange', a₁', a₂', b₁', b₂', hframe',
    hrest'⟩ := hgoal
  exact ⟨.POmegaPlus, ρ, ι', β₀', hdisj', hlong', hcenter', hrange', a₁', a₂', b₁', b₂',
    hframe', hrest'⟩

private theorem bmsdopx_frozenConcl_psl_of_data
    (k f : ℕ) (hf : 1 ≤ f)
    (S : Set (GL (Fin (k + 3) ⊕ Fin (k + 3)) (GaloisField 2 f)))
    {e : Matrix (Fin (k + 3) ⊕ Fin (k + 3)) (Fin (k + 3) ⊕ Fin (k + 3)) (GaloisField 2 f)}
    {J' : Subgroup ↥(spinGroup (bmsdop_Q k f))}
    (hrank4 : Module.finrank (GaloisField 2 f) (LinearMap.range (Matrix.toLin' e)) = 4)
    (data : bmsdop_r2_PSLData k f S e J') :
    bmsdopx_FrozenConcl k f S e J' := by
  obtain ⟨ι, β₀, hlong, hcenter, hrange, hrest⟩ := data
  exact ⟨.PSL, 2, ι, β₀, Or.inr ⟨rfl, rfl, hrank4⟩, hlong, hcenter, hrange, hrest⟩

private theorem bmsdopx_r2_model
    (k f : ℕ) (S : Set (GL (Fin (k + 3) ⊕ Fin (k + 3)) (GaloisField 2 f)))
    {e : Matrix (Fin (k + 3) ⊕ Fin (k + 3)) (Fin (k + 3) ⊕ Fin (k + 3)) (GaloisField 2 f)}
    {J' : Subgroup ↥(spinGroup (bmsdop_Q k f))}
    (h1 : bmsdop_geom₁ k f S e) (h2 : bmsdop_geom₂ k f S e)
    (hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s')
    (heA : e ∈ Algebra.adjoin (GaloisField 2 f) (Units.val '' S))
    (hJe : IsComponentOf J' ⁅bmsdop_Ge k f S e, bmsdop_Ge k f S e⁆)
    (θ : (Fin 2 ⊕ Fin 2 → GaloisField 2 f) ≃ₗ[GaloisField 2 f] ↥(bmsdop_W k f e))
    (hθ : ∀ x, (bmsdop_blockForm k f e) (θ x) = (Spin.quadPlus 2 (GaloisField 2 f)) x)
    (hrank : e.rank = 4) : bmsdopx_FrozenConcl k f S e J' := by
  by_cases hcard : Nat.card (GaloisField 2 f) = 2
  · exact (bmsdop_r2_degenerate k f S h1 h2 hS heA hJe θ hθ hcard).elim
  · have hf : 1 ≤ f := by
      by_contra h
      have hf0 : f = 0 := by omega
      rw [hf0] at hcard
      exact hcard CFSG.RankThree.PartTwo.Sec21.natCard_galoisField_two_zero
    have hrank4 : Module.finrank (GaloisField 2 f)
        (LinearMap.range (Matrix.toLin' e)) = 4 := by
      rw [← bmsdopx_rank_eq_finrank_range e]; exact hrank
    exact bmsdopx_frozenConcl_psl_of_data k f hf S hrank4
      (bmsdop_r2_model_data k f hf S h1 h2 hS heA hJe θ hθ hrank hcard)

private lemma bmsdopx_frozenConcl_minus_of_data
    (k f : ℕ)
    (S : Set (GL (Fin (k + 3) ⊕ Fin (k + 3)) (GaloisField 2 f)))
    {e : Matrix (Fin (k + 3) ⊕ Fin (k + 3)) (Fin (k + 3) ⊕ Fin (k + 3)) (GaloisField 2 f)}
    {J' : Subgroup ↥(spinGroup (bmsdop_Q k f))}
    (ρ : ℕ) (hρ3 : 3 ≤ ρ) (hrank : e.rank = 2 * ρ)
    (data : ∃ (β₀ : Fin (Spin.Twisted.minusDatum ρ (minusCoeffs_irr 2 f)).rank → ℤ)
      (ι : spinGroup (Spin.quadMinus ρ (GaloisField 2 f) (minusCoeffs 2 f).1
        (minusCoeffs 2 f).2) →* ↥(spinGroup (bmsdop_Q k f))),
      GGLongRoot (Spin.Twisted.minusDatum ρ (minusCoeffs_irr 2 f)) β₀ ∧
      (∀ y, ι y ∈ Subgroup.center ↥(spinGroup (bmsdop_Q k f)) →
        y ∈ Subgroup.center (spinGroup (Spin.quadMinus ρ (GaloisField 2 f)
          (minusCoeffs 2 f).1 (minusCoeffs 2 f).2))) ∧
      ι.range = J' ∧
      ∃ a₁ a₂ b₁ b₂ : ((Fin (k + 3) ⊕ Fin (k + 3)) → GaloisField 2 f),
        ((bmsdop_Q k f) a₁ = 0 ∧ (bmsdop_Q k f) a₂ = 0 ∧
          (bmsdop_Q k f) b₁ = 0 ∧ (bmsdop_Q k f) b₂ = 0) ∧
        QuadraticMap.polar (bmsdop_Q k f) a₁ b₁ = 1 ∧
        QuadraticMap.polar (bmsdop_Q k f) a₂ b₂ = 1 ∧
        (QuadraticMap.polar (bmsdop_Q k f) a₁ a₂ = 0 ∧
          QuadraticMap.polar (bmsdop_Q k f) b₁ b₂ = 0 ∧
          QuadraticMap.polar (bmsdop_Q k f) a₁ b₂ = 0 ∧
          QuadraticMap.polar (bmsdop_Q k f) a₂ b₁ = 0) ∧
        ((((Spin.Twisted.minusDatum ρ (minusCoeffs_irr 2 f)).rootGroup β₀).map ι).map
          (Spin.spinAction (bmsdop_Q k f)) = siegelGroup (bmsdop_Q k f) a₁ a₂) ∧
        ((((Spin.Twisted.minusDatum ρ (minusCoeffs_irr 2 f)).rootGroup (-β₀)).map ι).map
          (Spin.spinAction (bmsdop_Q k f)) = siegelGroup (bmsdop_Q k f) b₁ b₂)) :
    bmsdopx_FrozenConcl k f S e J' := by
  obtain ⟨β₀, ι, hlong, hcenter, hrange, a₁, a₂, b₁, b₂, hframe, hgrp₁, hgrp₂⟩ := data
  have hgg : ggU .POmegaMinus ρ f =
      ⟨spinGroup (Spin.quadMinus ρ (GaloisField 2 f) (minusCoeffs 2 f).1 (minusCoeffs 2 f).2),
        Spin.Twisted.minusDatum ρ (minusCoeffs_irr 2 f)⟩ := by
    simp only [ggU, lieUniversal, ↓reduceDIte]
  have hrank' : 2 * ρ = Module.finrank (GaloisField 2 f)
      (LinearMap.range (Matrix.toLin' e)) := by
    rw [← bmsdopx_rank_eq_finrank_range e]
    exact hrank.symm
  have hgoal : ∃ (ι : (ggU .POmegaMinus ρ f).K →* ↥(spinGroup (bmsdop_Q k f)))
      (β₀ : Fin (ggU .POmegaMinus ρ f).D.rank → ℤ),
      ((((.POmegaMinus : StatedLieTag) = .POmegaPlus ∨
          (.POmegaMinus : StatedLieTag) = .POmegaMinus) ∧ 3 ≤ ρ ∧ 2 * ρ =
        Module.finrank (GaloisField 2 f) (LinearMap.range (Matrix.toLin' e))) ∨
        ((.POmegaMinus : StatedLieTag) = .PSL ∧ ρ = 2 ∧
          Module.finrank (GaloisField 2 f) (LinearMap.range (Matrix.toLin' e)) = 4)) ∧
      GGLongRoot (ggU .POmegaMinus ρ f).D β₀ ∧
      (∀ y, ι y ∈ Subgroup.center ↥(spinGroup (bmsdop_Q k f)) →
        y ∈ Subgroup.center (ggU .POmegaMinus ρ f).K) ∧ ι.range = J' ∧
      ∃ a₁ a₂ b₁ b₂ : ((Fin (k + 3) ⊕ Fin (k + 3)) → GaloisField 2 f),
        ((bmsdop_Q k f) a₁ = 0 ∧ (bmsdop_Q k f) a₂ = 0 ∧
          (bmsdop_Q k f) b₁ = 0 ∧ (bmsdop_Q k f) b₂ = 0) ∧
        QuadraticMap.polar (bmsdop_Q k f) a₁ b₁ = 1 ∧
        QuadraticMap.polar (bmsdop_Q k f) a₂ b₂ = 1 ∧
        (QuadraticMap.polar (bmsdop_Q k f) a₁ a₂ = 0 ∧
          QuadraticMap.polar (bmsdop_Q k f) b₁ b₂ = 0 ∧
          QuadraticMap.polar (bmsdop_Q k f) a₁ b₂ = 0 ∧
          QuadraticMap.polar (bmsdop_Q k f) a₂ b₁ = 0) ∧
        ((((ggU .POmegaMinus ρ f).D.rootGroup β₀).map ι).map
          (Spin.spinAction (bmsdop_Q k f)) = siegelGroup (bmsdop_Q k f) a₁ a₂) ∧
        ((((ggU .POmegaMinus ρ f).D.rootGroup (-β₀)).map ι).map
          (Spin.spinAction (bmsdop_Q k f)) = siegelGroup (bmsdop_Q k f) b₁ b₂) :=
    hgg.symm ▸ ⟨ι, β₀, Or.inl ⟨Or.inr rfl, hρ3, hrank'⟩, hlong, hcenter, hrange,
      a₁, a₂, b₁, b₂, hframe, hgrp₁, hgrp₂⟩
  obtain ⟨ι', β₀', hdisj', hlong', hcenter', hrange', a₁', a₂', b₁', b₂', hframe',
    hrest'⟩ := hgoal
  exact ⟨.POmegaMinus, ρ, ι', β₀', hdisj', hlong', hcenter', hrange', a₁', a₂', b₁', b₂',
    hframe', hrest'⟩

private lemma bmsdopx_frozenConcl_of_plus_plane
    (k f : ℕ)
    (S : Set (GL (Fin (k + 3) ⊕ Fin (k + 3)) (GaloisField 2 f)))
    {e : Matrix (Fin (k + 3) ⊕ Fin (k + 3)) (Fin (k + 3) ⊕ Fin (k + 3)) (GaloisField 2 f)}
    {J' : Subgroup ↥(spinGroup (bmsdop_Q k f))}
    (h1 : bmsdop_geom₁ k f S e) (h2 : bmsdop_geom₂ k f S e)
    (hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s')
    (heA : e ∈ Algebra.adjoin (GaloisField 2 f) (Units.val '' S))
    (hJe : IsComponentOf J' ⁅bmsdop_Ge k f S e, bmsdop_Ge k f S e⁆)
    (hf : 1 ≤ f)
    (θ : (Fin 1 ⊕ Fin 1 → GaloisField 2 f) ≃ₗ[GaloisField 2 f] ↥(bmsdop_W k f e))
    (hθ : ∀ x, (bmsdop_blockForm k f e) (θ x) = (Spin.quadPlus 1 (GaloisField 2 f)) x) :
    bmsdopx_FrozenConcl k f S e J' :=
  False.elim (bmsdop_component_bot_false k f S hJe
    (bmsdop_commutator_bot_of_two_dim k f S h1 h2 hS heA
      (Spin.quadPlus 1 (GaloisField 2 f))
      (Spin.nondegenerate_polarBilin_quadPlus 1 (GaloisField 2 f)) (by simp) θ hθ))

private lemma bmsdopx_frozenConcl_of_plus_ge_two
    (k f : ℕ)
    (S : Set (GL (Fin (k + 3) ⊕ Fin (k + 3)) (GaloisField 2 f)))
    {e : Matrix (Fin (k + 3) ⊕ Fin (k + 3)) (Fin (k + 3) ⊕ Fin (k + 3)) (GaloisField 2 f)}
    {J' : Subgroup ↥(spinGroup (bmsdop_Q k f))}
    (h1 : bmsdop_geom₁ k f S e) (h2 : bmsdop_geom₂ k f S e)
    (hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s')
    (heA : e ∈ Algebra.adjoin (GaloisField 2 f) (Units.val '' S))
    (hJe : IsComponentOf J' ⁅bmsdop_Ge k f S e, bmsdop_Ge k f S e⁆)
    (hf : 1 ≤ f)
    (ρ : ℕ) (hρ : e.rank = 2 * ρ) (hρ2 : 2 ≤ ρ)
    (θ : (Fin ρ ⊕ Fin ρ → GaloisField 2 f) ≃ₗ[GaloisField 2 f] ↥(bmsdop_W k f e))
    (hθ : ∀ x, (bmsdop_blockForm k f e) (θ x) = (Spin.quadPlus ρ (GaloisField 2 f)) x) :
    bmsdopx_FrozenConcl k f S e J' := by
  rcases Nat.lt_or_ge ρ 3 with h | h
  · have hρe : ρ = 2 := by omega
    subst hρe
    exact bmsdopx_r2_model k f S h1 h2 hS heA hJe θ hθ (by omega)
  · exact bmsdopx_frozenConcl_plus_of_data k f S ρ h hρ
      (bmsdop_plus_model_data k f S h1 h2 hS heA hJe ρ h hρ hf θ hθ)

private lemma bmsdopx_frozenConcl_of_minus_lt_three
    (k f : ℕ)
    (S : Set (GL (Fin (k + 3) ⊕ Fin (k + 3)) (GaloisField 2 f)))
    {e : Matrix (Fin (k + 3) ⊕ Fin (k + 3)) (Fin (k + 3) ⊕ Fin (k + 3)) (GaloisField 2 f)}
    {J' : Subgroup ↥(spinGroup (bmsdop_Q k f))}
    (h1 : bmsdop_geom₁ k f S e) (h2 : bmsdop_geom₂ k f S e)
    (hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s')
    (heA : e ∈ Algebra.adjoin (GaloisField 2 f) (Units.val '' S))
    (hJe : IsComponentOf J' ⁅bmsdop_Ge k f S e, bmsdop_Ge k f S e⁆)
    (hnm : ¬ (e.rank = 4 ∧ ∀ x y : (Fin (k + 3) ⊕ Fin (k + 3)) → (GaloisField 2 f),
      Matrix.mulVec e x = x → Matrix.mulVec e y = y → (bmsdop_Q k f) x = 0 →
      (bmsdop_Q k f) y = 0 → QuadraticMap.polar (bmsdop_Q k f) x y = 0 →
      ¬ LinearIndependent (GaloisField 2 f) ![x, y]))
    (ρ : ℕ) (hρ : e.rank = 2 * ρ) (hρ1 : 1 ≤ ρ) (hρlt : ρ < 3) (hf : 1 ≤ f)
    (β γ : GaloisField 2 f) (hirr : ∀ s : GaloisField 2 f, s ^ 2 + β * s + γ ≠ 0)
    (θ : (Fin (ρ - 1) ⊕ Fin (ρ - 1) ⊕ Fin 2 → GaloisField 2 f) ≃ₗ[GaloisField 2 f]
      ↥(bmsdop_W k f e))
    (hθ : ∀ x, (bmsdop_blockForm k f e) (θ x) = (Spin.quadMinus ρ (GaloisField 2 f) β γ) x) :
    bmsdopx_FrozenConcl k f S e J' := by
  rcases Nat.lt_or_ge ρ 2 with hlt | hge
  · have hρe : ρ = 1 := by omega
    subst hρe
    exact False.elim (bmsdop_component_bot_false k f S hJe
      (bmsdop_commutator_bot_of_two_dim k f S h1 h2 hS heA
        (Spin.quadMinus 1 (GaloisField 2 f) β γ)
        (Spin.nondegenerate_polarBilin_quadMinus_of_finite 1 (GaloisField 2 f) hirr)
        (by simp) θ hθ))
  · have hρe : ρ = 2 := by omega
    subst hρe
    exact absurd ⟨by simpa using hρ,
      bmsdop_minus_two_block_no_singular_pair k f S h1 h2 β γ hirr θ hθ⟩ hnm

private lemma bmsdopx_frozenConcl_of_minus_ge_three
    (k f : ℕ)
    (S : Set (GL (Fin (k + 3) ⊕ Fin (k + 3)) (GaloisField 2 f)))
    {e : Matrix (Fin (k + 3) ⊕ Fin (k + 3)) (Fin (k + 3) ⊕ Fin (k + 3)) (GaloisField 2 f)}
    {J' : Subgroup ↥(spinGroup (bmsdop_Q k f))}
    (h1 : bmsdop_geom₁ k f S e) (h2 : bmsdop_geom₂ k f S e)
    (hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s')
    (heA : e ∈ Algebra.adjoin (GaloisField 2 f) (Units.val '' S))
    (hJe : IsComponentOf J' ⁅bmsdop_Ge k f S e, bmsdop_Ge k f S e⁆)
    (hf : 1 ≤ f)
    (ρ : ℕ) (hρ : e.rank = 2 * ρ) (hρ3 : 3 ≤ ρ)
    (β γ : GaloisField 2 f) (hirr : ∀ s : GaloisField 2 f, s ^ 2 + β * s + γ ≠ 0)
    (θ : (Fin (ρ - 1) ⊕ Fin (ρ - 1) ⊕ Fin 2 → GaloisField 2 f) ≃ₗ[GaloisField 2 f]
      ↥(bmsdop_W k f e))
    (hθ : ∀ x, (bmsdop_blockForm k f e) (θ x) = (Spin.quadMinus ρ (GaloisField 2 f) β γ) x) :
    bmsdopx_FrozenConcl k f S e J' := by
  obtain ⟨eiso⟩ := bmsdop_minus_arf_isometry f ρ β γ hirr
  have hθ' : ∀ x, (bmsdop_blockForm k f e) ((((eiso.toLinearEquiv).symm).trans θ) x) =
      (Spin.quadMinus ρ (GaloisField 2 f) (minusCoeffs 2 f).1 (minusCoeffs 2 f).2) x := by
    intro x
    rw [LinearEquiv.trans_apply, hθ]
    rw [← QuadraticMap.IsometryEquiv.map_app eiso ((eiso.toLinearEquiv).symm x)]
    exact congrArg (Spin.quadMinus ρ (GaloisField 2 f) (minusCoeffs 2 f).1
      (minusCoeffs 2 f).2) (LinearEquiv.apply_symm_apply eiso.toLinearEquiv x)
  by_cases hρ4 : 4 ≤ ρ
  · exact bmsdopx_frozenConcl_minus_of_data k f S ρ hρ3 hρ
      (bmsdop_minus_model_data k f S h1 h2 hS heA hJe ρ hρ3 hρ hf
        (minusCoeffs 2 f).1 (minusCoeffs 2 f).2 (minusCoeffs_irr 2 f)
        (bmsdop_std_quasisimple_minus f ρ hρ4 (minusCoeffs 2 f).1 (minusCoeffs 2 f).2
          (minusCoeffs_irr 2 f))
        (bmsdop_minus_range_of_four ρ f hρ4 (minusCoeffs 2 f).1 (minusCoeffs 2 f).2
          (minusCoeffs_irr 2 f))
        (bmsdop_ambient_minus_of_four ρ f hρ4 (minusCoeffs 2 f).1 (minusCoeffs 2 f).2
          (minusCoeffs_irr 2 f))
        (((eiso.toLinearEquiv).symm).trans θ) hθ')
  · have hρ3eq : ρ = 3 := by omega
    subst hρ3eq
    exact bmsdopx_frozenConcl_minus_of_data k f S 3 (by norm_num) hρ
      (bmsdop_minus_model_data k f S h1 h2 hS heA hJe 3 (by norm_num) hρ hf
        (minusCoeffs 2 f).1 (minusCoeffs 2 f).2 (minusCoeffs_irr 2 f)
        (bmsdop_r3m_quasisimple f (minusCoeffs 2 f).1 (minusCoeffs 2 f).2 (minusCoeffs_irr 2 f))
        (bmsdop_r3m_range f (minusCoeffs 2 f).1 (minusCoeffs 2 f).2 (minusCoeffs_irr 2 f))
        (bmsdop_r3m_ambient f (minusCoeffs 2 f).1 (minusCoeffs 2 f).2 (minusCoeffs_irr 2 f))
        (((eiso.toLinearEquiv).symm).trans θ) hθ')

private theorem bmsdopx_model_of_geom
    (k f : ℕ)
    (S : Set (GL (Fin (k + 3) ⊕ Fin (k + 3)) (GaloisField 2 f)))
    {e : Matrix (Fin (k + 3) ⊕ Fin (k + 3)) (Fin (k + 3) ⊕ Fin (k + 3)) (GaloisField 2 f)}
    {J' : Subgroup ↥(spinGroup (bmsdop_Q k f))}
    (h1 : bmsdop_geom₁ k f S e) (h2 : bmsdop_geom₂ k f S e)
    (hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s')
    (heA : e ∈ Algebra.adjoin (GaloisField 2 f) (Units.val '' S))
    (hJe : IsComponentOf J' ⁅bmsdop_Ge k f S e, bmsdop_Ge k f S e⁆)
    (hnm : ¬ (e.rank = 4 ∧ ∀ x y : (Fin (k + 3) ⊕ Fin (k + 3)) → (GaloisField 2 f),
      Matrix.mulVec e x = x → Matrix.mulVec e y = y → (bmsdop_Q k f) x = 0 →
      (bmsdop_Q k f) y = 0 → QuadraticMap.polar (bmsdop_Q k f) x y = 0 →
      ¬ LinearIndependent (GaloisField 2 f) ![x, y]))
    (hf : 1 ≤ f) :
    bmsdopx_FrozenConcl k f S e J' := by
  have hrankne : e.rank ≠ 0 := bmsdop_geom_rank_ne_zero k f S h1
  obtain ⟨ρ, hρ'⟩ := Nat.even_iff.mpr h1.2.2.2.2
  have hρ : e.rank = 2 * ρ := by omega
  have hρ1 : 1 ≤ ρ := by omega
  rcases bmsdop_theta k f S h1 h2 ρ hρ hρ1 with ⟨θ, hθ⟩ | ⟨β, γ, hirr, θ, hθ⟩
  · rcases Nat.lt_or_ge ρ 2 with h2lt | h2ge
    · have hρe : ρ = 1 := by omega
      subst hρe
      exact bmsdopx_frozenConcl_of_plus_plane k f S h1 h2 hS heA hJe hf θ hθ
    · exact bmsdopx_frozenConcl_of_plus_ge_two k f S h1 h2 hS heA hJe hf ρ hρ h2ge θ hθ
  · rcases Nat.lt_or_ge ρ 3 with h3lt | h3ge
    · exact bmsdopx_frozenConcl_of_minus_lt_three k f S h1 h2 hS heA hJe hnm ρ hρ hρ1
        h3lt hf β γ hirr θ hθ
    · exact bmsdopx_frozenConcl_of_minus_ge_three k f S h1 h2 hS heA hJe hf ρ hρ h3ge
        β γ hirr θ hθ

private theorem bmsdopx_frozenClosure_psl_of_data
    (k f : ℕ) (hf : 1 ≤ f)
    (S : Set (GL (Fin (k + 3) ⊕ Fin (k + 3)) (GaloisField 2 f)))
    {e : Matrix (Fin (k + 3) ⊕ Fin (k + 3)) (Fin (k + 3) ⊕ Fin (k + 3)) (GaloisField 2 f)}
    {J' : Subgroup ↥(spinGroup (bmsdop_Q k f))}
    (hrank4 : Module.finrank (GaloisField 2 f) (LinearMap.range (Matrix.toLin' e)) = 4)
    (data : bmsdop_r2_PSLClosureData k f S e J') :
    bmsdopx_FrozenClosure k f S e J' := by
  obtain ⟨ι, hcenter, hrange, hrest⟩ := data
  exact ⟨.PSL, 2, ι, Or.inr ⟨rfl, rfl, hrank4⟩, hcenter, hrange, hrest⟩

private theorem bmsdopx_r2_closure
    (k f : ℕ) (S : Set (GL (Fin (k + 3) ⊕ Fin (k + 3)) (GaloisField 2 f)))
    {e : Matrix (Fin (k + 3) ⊕ Fin (k + 3)) (Fin (k + 3) ⊕ Fin (k + 3)) (GaloisField 2 f)}
    {J' : Subgroup ↥(spinGroup (bmsdop_Q k f))}
    (h1 : bmsdop_geom₁ k f S e) (h2 : bmsdop_geom₂ k f S e)
    (hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s')
    (heA : e ∈ Algebra.adjoin (GaloisField 2 f) (Units.val '' S))
    (hJe : IsComponentOf J' ⁅bmsdop_Ge k f S e, bmsdop_Ge k f S e⁆)
    (θ : (Fin 2 ⊕ Fin 2 → GaloisField 2 f) ≃ₗ[GaloisField 2 f] ↥(bmsdop_W k f e))
    (hθ : ∀ x, (bmsdop_blockForm k f e) (θ x) = (Spin.quadPlus 2 (GaloisField 2 f)) x)
    (hrank : e.rank = 4) : bmsdopx_FrozenClosure k f S e J' := by
  by_cases hcard : Nat.card (GaloisField 2 f) = 2
  · exact (bmsdop_r2_degenerate k f S h1 h2 hS heA hJe θ hθ hcard).elim
  · have hf : 1 ≤ f := by
      by_contra h
      have hf0 : f = 0 := by omega
      rw [hf0] at hcard
      exact hcard CFSG.RankThree.PartTwo.Sec21.natCard_galoisField_two_zero
    have hrank4 : Module.finrank (GaloisField 2 f)
        (LinearMap.range (Matrix.toLin' e)) = 4 := by
      rw [← bmsdopx_rank_eq_finrank_range e]; exact hrank
    exact bmsdopx_frozenClosure_psl_of_data k f hf S hrank4
      (bmsdop_r2_closure_data k f hf S h1 h2 hS heA hJe θ hθ hrank hcard)

private theorem bmsdopx_generic_closure_plus
    (k f : ℕ) (S : Set (GL (Fin (k + 3) ⊕ Fin (k + 3)) (GaloisField 2 f)))
    {e : Matrix (Fin (k + 3) ⊕ Fin (k + 3)) (Fin (k + 3) ⊕ Fin (k + 3)) (GaloisField 2 f)}
    {J' : Subgroup ↥(spinGroup (bmsdop_Q k f))}
    (h1 : bmsdop_geom₁ k f S e) (h2 : bmsdop_geom₂ k f S e)
    (hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s')
    (heA : e ∈ Algebra.adjoin (GaloisField 2 f) (Units.val '' S))
    (hJe : IsComponentOf J' ⁅bmsdop_Ge k f S e, bmsdop_Ge k f S e⁆)
    (ρ : ℕ) (hρ3 : 3 ≤ ρ) (hrank : e.rank = 2 * ρ) (hf : 1 ≤ f)
    (θ : (Fin ρ ⊕ Fin ρ → GaloisField 2 f) ≃ₗ[GaloisField 2 f] ↥(bmsdop_W k f e))
    (hθ : ∀ x, (bmsdop_blockForm k f e) (θ x) = (Spin.quadPlus ρ (GaloisField 2 f)) x) :
    bmsdopx_FrozenClosure k f S e J' := by
  obtain ⟨ι₁, hι₁inj, hι₁range, hι₁E, hι₁center, hJ'⟩ :=
    bmsdop_plus_embedding k f S h1 h2 hS heA hJe ρ hρ3 hrank θ hθ
  have hnd_std : (QuadraticMap.polarBilin (Spin.quadPlus ρ (GaloisField 2 f))).Nondegenerate :=
    Spin.nondegenerate_polarBilin_quadPlus ρ (GaloisField 2 f)
  have hE : bmsdop_ExtProps k f S e (Spin.quadPlus ρ (GaloisField 2 f)) hnd_std θ
      (bmsdop_glue k f S h1 θ) := bmsdop_plus_extProps k f S h1 h2 ρ hρ3 θ hθ
  have hclos := bmsdop_closure k f S h1 h2 hJe (Spin.quadPlus ρ (GaloisField 2 f)) hnd_std θ hθ
    (Spin.plusDatum ρ (GaloisField 2 f) hρ3) ι₁ ⟨hι₁inj, hι₁range⟩ (bmsdop_glue k f S h1 θ) hE
    hι₁E (bmsdop_plus_ambient f ρ hρ3) (bmsdop_plus_hext f ρ hρ3)
  have hgg : ggU .POmegaPlus ρ f =
      ⟨spinGroup (Spin.quadPlus ρ (GaloisField 2 f)),
        Spin.plusDatum ρ (GaloisField 2 f) hρ3⟩ := by
    simp only [ggU, lieUniversal, hρ3, ↓reduceDIte]
  have hrank' : 2 * ρ = Module.finrank (GaloisField 2 f)
      (LinearMap.range (Matrix.toLin' e)) := by
    rw [← bmsdopx_rank_eq_finrank_range e]
    exact hrank.symm
  have hgoal : ∃ (ι : (ggU .POmegaPlus ρ f).K →* ↥(spinGroup (bmsdop_Q k f))),
      ((((.POmegaPlus : StatedLieTag) = .POmegaPlus ∨
          (.POmegaPlus : StatedLieTag) = .POmegaMinus) ∧ 3 ≤ ρ ∧ 2 * ρ =
        Module.finrank (GaloisField 2 f) (LinearMap.range (Matrix.toLin' e))) ∨
        ((.POmegaPlus : StatedLieTag) = .PSL ∧ ρ = 2 ∧
          Module.finrank (GaloisField 2 f) (LinearMap.range (Matrix.toLin' e)) = 4)) ∧
      (∀ y, ι y ∈ Subgroup.center ↥(spinGroup (bmsdop_Q k f)) →
        y ∈ Subgroup.center (ggU .POmegaPlus ρ f).K) ∧
      ι.range = J' ∧
      (∀ a₁ a₂ : ((Fin (k + 3) ⊕ Fin (k + 3)) → GaloisField 2 f), a₁ ≠ 0 → a₂ ≠ 0 →
          LinearIndependent (GaloisField 2 f) ![a₁, a₂] → (bmsdop_Q k f) a₁ = 0 →
          (bmsdop_Q k f) a₂ = 0 → QuadraticMap.polar (bmsdop_Q k f) a₁ a₂ = 0 →
          siegelGroup (bmsdop_Q k f) a₁ a₂ ≤ J'.map (Spin.spinAction (bmsdop_Q k f)) →
        ∃ (β : Fin (ggU .POmegaPlus ρ f).D.rank → ℤ) (u : (ggU .POmegaPlus ρ f).K),
          β ∈ (ggU .POmegaPlus ρ f).D.roots ∧
          GGLongRoot (ggU .POmegaPlus ρ f).D β ∧
          ((((ggU .POmegaPlus ρ f).D.rootGroup β).map (MulAut.conj u).toMonoidHom).map ι).map
            (Spin.spinAction (bmsdop_Q k f)) = siegelGroup (bmsdop_Q k f) a₁ a₂) :=
    hgg.symm ▸ ⟨ι₁, Or.inl ⟨Or.inl rfl, hρ3, hrank'⟩, hι₁center, hι₁range.trans hJ'.symm, hclos⟩
  obtain ⟨ι', hdisj', hcenter', hrange', hclos'⟩ := hgoal
  exact ⟨.POmegaPlus, ρ, ι', hdisj', hcenter', hrange', hclos'⟩

private theorem bmsdopx_generic_closure_minus
    (k f : ℕ) (S : Set (GL (Fin (k + 3) ⊕ Fin (k + 3)) (GaloisField 2 f)))
    {e : Matrix (Fin (k + 3) ⊕ Fin (k + 3)) (Fin (k + 3) ⊕ Fin (k + 3)) (GaloisField 2 f)}
    {J' : Subgroup ↥(spinGroup (bmsdop_Q k f))}
    (h1 : bmsdop_geom₁ k f S e) (h2 : bmsdop_geom₂ k f S e)
    (hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s')
    (heA : e ∈ Algebra.adjoin (GaloisField 2 f) (Units.val '' S))
    (hJe : IsComponentOf J' ⁅bmsdop_Ge k f S e, bmsdop_Ge k f S e⁆)
    (ρ : ℕ) (hρ3 : 3 ≤ ρ) (hrank : e.rank = 2 * ρ) (hf : 1 ≤ f)
    (hq : IsQuasisimple (spinGroup (Spin.quadMinus ρ (GaloisField 2 f)
      (minusCoeffs 2 f).1 (minusCoeffs 2 f).2)))
    (hΩ : (Spin.spinAction (Spin.quadMinus ρ (GaloisField 2 f)
        (minusCoeffs 2 f).1 (minusCoeffs 2 f).2)).range =
      CFSG.RankThree.OrthogonalInvolutions.omegaGroup (Spin.quadMinus ρ (GaloisField 2 f)
        (minusCoeffs 2 f).1 (minusCoeffs 2 f).2)
        (Spin.nondegenerate_polarBilin_quadMinus_of_finite ρ (GaloisField 2 f)
          (minusCoeffs_irr 2 f)))
    (hD : bmsdop_AmbientMinus ρ f (minusCoeffs 2 f).1 (minusCoeffs 2 f).2
      (minusCoeffs_irr 2 f))
    (θ : (Fin (ρ - 1) ⊕ Fin (ρ - 1) ⊕ Fin 2 → GaloisField 2 f) ≃ₗ[GaloisField 2 f]
      ↥(bmsdop_W k f e))
    (hθ : ∀ x, (bmsdop_blockForm k f e) (θ x) = (Spin.quadMinus ρ (GaloisField 2 f)
      (minusCoeffs 2 f).1 (minusCoeffs 2 f).2) x) :
    bmsdopx_FrozenClosure k f S e J' := by
  have hnd_std : (QuadraticMap.polarBilin (Spin.quadMinus ρ (GaloisField 2 f)
      (minusCoeffs 2 f).1 (minusCoeffs 2 f).2)).Nondegenerate :=
    Spin.nondegenerate_polarBilin_quadMinus_of_finite ρ (GaloisField 2 f) (minusCoeffs_irr 2 f)
  haveI : Algebra.IsCentral (GaloisField 2 f)
      (CliffordAlgebra (Spin.quadMinus ρ (GaloisField 2 f) (minusCoeffs 2 f).1
        (minusCoeffs 2 f).2)) :=
    Spin.isCentral_cliffordAlgebra_quadMinus ρ (minusCoeffs 2 f).1 (minusCoeffs 2 f).2
      (minusCoeffs_irr 2 f)
  have hE : bmsdop_ExtProps k f S e (Spin.quadMinus ρ (GaloisField 2 f) (minusCoeffs 2 f).1
      (minusCoeffs 2 f).2) hnd_std θ (bmsdop_glue k f S h1 θ) := by
    have hb := bmsdop_glue_basic k f S h1 h2 (Spin.quadMinus ρ (GaloisField 2 f)
      (minusCoeffs 2 f).1 (minusCoeffs 2 f).2) θ hθ
    exact ⟨hb.1, hb.2.1, hb.2.2.1, hb.2.2.2,
      fun g => bmsdop_glue_omegaGroup k f S h1 h2 (Spin.quadMinus ρ (GaloisField 2 f)
        (minusCoeffs 2 f).1 (minusCoeffs 2 f).2) θ hθ hnd_std g⟩
  obtain ⟨ι₁, hι₁inj, hι₁range, hι₁E, hι₁center⟩ :=
    bmsdop_iota₁ k f S h1 h2 hS heA (Spin.quadMinus ρ (GaloisField 2 f) (minusCoeffs 2 f).1
      (minusCoeffs 2 f).2) hnd_std (bmsdop_glue k f S h1 θ) θ hE hθ hΩ
  have hJ' : J' = bmsdop_Ge k f S e :=
    bmsdop_component_eq k f S h1 h2 (Spin.quadMinus ρ (GaloisField 2 f) (minusCoeffs 2 f).1
      (minusCoeffs 2 f).2) hq ι₁ ⟨hι₁inj, hι₁range⟩ hJe
  have hD' : ∀ a₁ a₂ b₁ b₂ : (Fin (ρ - 1) ⊕ Fin (ρ - 1) ⊕ Fin 2 → GaloisField 2 f),
      ((Spin.quadMinus ρ (GaloisField 2 f) (minusCoeffs 2 f).1 (minusCoeffs 2 f).2) a₁ = 0 ∧
        (Spin.quadMinus ρ (GaloisField 2 f) (minusCoeffs 2 f).1 (minusCoeffs 2 f).2) a₂ = 0 ∧
        (Spin.quadMinus ρ (GaloisField 2 f) (minusCoeffs 2 f).1 (minusCoeffs 2 f).2) b₁ = 0 ∧
        (Spin.quadMinus ρ (GaloisField 2 f) (minusCoeffs 2 f).1 (minusCoeffs 2 f).2) b₂ = 0) →
      QuadraticMap.polar (Spin.quadMinus ρ (GaloisField 2 f) (minusCoeffs 2 f).1
        (minusCoeffs 2 f).2) a₁ b₁ = 1 →
      QuadraticMap.polar (Spin.quadMinus ρ (GaloisField 2 f) (minusCoeffs 2 f).1
        (minusCoeffs 2 f).2) a₂ b₂ = 1 →
      (QuadraticMap.polar (Spin.quadMinus ρ (GaloisField 2 f) (minusCoeffs 2 f).1
          (minusCoeffs 2 f).2) a₁ a₂ = 0 ∧
        QuadraticMap.polar (Spin.quadMinus ρ (GaloisField 2 f) (minusCoeffs 2 f).1
          (minusCoeffs 2 f).2) b₁ b₂ = 0 ∧
        QuadraticMap.polar (Spin.quadMinus ρ (GaloisField 2 f) (minusCoeffs 2 f).1
          (minusCoeffs 2 f).2) a₁ b₂ = 0 ∧
        QuadraticMap.polar (Spin.quadMinus ρ (GaloisField 2 f) (minusCoeffs 2 f).1
          (minusCoeffs 2 f).2) a₂ b₁ = 0) →
      ∃ β : Fin (Spin.Twisted.minusDatum ρ (minusCoeffs_irr 2 f)).rank → ℤ,
        β ∈ (Spin.Twisted.minusDatum ρ (minusCoeffs_irr 2 f)).roots ∧
        GGLongRoot (Spin.Twisted.minusDatum ρ (minusCoeffs_irr 2 f)) β ∧
        ∃ u : spinGroup (Spin.quadMinus ρ (GaloisField 2 f) (minusCoeffs 2 f).1
            (minusCoeffs 2 f).2),
          (((Spin.Twisted.minusDatum ρ (minusCoeffs_irr 2 f)).rootGroup β).map
            (MulAut.conj u).toMonoidHom).map
            (Spin.spinAction (Spin.quadMinus ρ (GaloisField 2 f) (minusCoeffs 2 f).1
              (minusCoeffs 2 f).2)) = siegelGroup (Spin.quadMinus ρ (GaloisField 2 f)
                (minusCoeffs 2 f).1 (minusCoeffs 2 f).2) a₁ a₂ ∧
          (((Spin.Twisted.minusDatum ρ (minusCoeffs_irr 2 f)).rootGroup (-β)).map
            (MulAut.conj u).toMonoidHom).map
            (Spin.spinAction (Spin.quadMinus ρ (GaloisField 2 f) (minusCoeffs 2 f).1
              (minusCoeffs 2 f).2)) = siegelGroup (Spin.quadMinus ρ (GaloisField 2 f)
                (minusCoeffs 2 f).1 (minusCoeffs 2 f).2) b₁ b₂ := by
    intro a₁ a₂ b₁ b₂ hQ h₁ h₂ h₀
    obtain ⟨β, hβroot, hβlong, u, hu₁, hu₂⟩ := hD a₁ a₂ b₁ b₂ hQ h₁ h₂ h₀
    exact ⟨β, hβroot, hβlong, u, hu₁, hu₂⟩
  have hclos := bmsdop_closure k f S h1 h2 hJe (Spin.quadMinus ρ (GaloisField 2 f)
      (minusCoeffs 2 f).1 (minusCoeffs 2 f).2) hnd_std θ hθ
    (Spin.Twisted.minusDatum ρ (minusCoeffs_irr 2 f)) ι₁ ⟨hι₁inj, hι₁range⟩
    (bmsdop_glue k f S h1 θ) hE hι₁E hD'
    (bmsdop_minus_hext f ρ hρ3 (minusCoeffs 2 f).1 (minusCoeffs 2 f).2 (minusCoeffs_irr 2 f))
  have hgg : ggU .POmegaMinus ρ f =
      ⟨spinGroup (Spin.quadMinus ρ (GaloisField 2 f) (minusCoeffs 2 f).1
        (minusCoeffs 2 f).2), Spin.Twisted.minusDatum ρ (minusCoeffs_irr 2 f)⟩ := by
    simp only [ggU, lieUniversal, ↓reduceDIte]
  have hrank' : 2 * ρ = Module.finrank (GaloisField 2 f)
      (LinearMap.range (Matrix.toLin' e)) := by
    rw [← bmsdopx_rank_eq_finrank_range e]
    exact hrank.symm
  have hgoal : ∃ (ι : (ggU .POmegaMinus ρ f).K →* ↥(spinGroup (bmsdop_Q k f))),
      ((((.POmegaMinus : StatedLieTag) = .POmegaPlus ∨
          (.POmegaMinus : StatedLieTag) = .POmegaMinus) ∧ 3 ≤ ρ ∧ 2 * ρ =
        Module.finrank (GaloisField 2 f) (LinearMap.range (Matrix.toLin' e))) ∨
        ((.POmegaMinus : StatedLieTag) = .PSL ∧ ρ = 2 ∧
          Module.finrank (GaloisField 2 f) (LinearMap.range (Matrix.toLin' e)) = 4)) ∧
      (∀ y, ι y ∈ Subgroup.center ↥(spinGroup (bmsdop_Q k f)) →
        y ∈ Subgroup.center (ggU .POmegaMinus ρ f).K) ∧
      ι.range = J' ∧
      (∀ a₁ a₂ : ((Fin (k + 3) ⊕ Fin (k + 3)) → GaloisField 2 f), a₁ ≠ 0 → a₂ ≠ 0 →
          LinearIndependent (GaloisField 2 f) ![a₁, a₂] → (bmsdop_Q k f) a₁ = 0 →
          (bmsdop_Q k f) a₂ = 0 → QuadraticMap.polar (bmsdop_Q k f) a₁ a₂ = 0 →
          siegelGroup (bmsdop_Q k f) a₁ a₂ ≤ J'.map (Spin.spinAction (bmsdop_Q k f)) →
        ∃ (β : Fin (ggU .POmegaMinus ρ f).D.rank → ℤ) (u : (ggU .POmegaMinus ρ f).K),
          β ∈ (ggU .POmegaMinus ρ f).D.roots ∧
          GGLongRoot (ggU .POmegaMinus ρ f).D β ∧
          ((((ggU .POmegaMinus ρ f).D.rootGroup β).map
            (MulAut.conj u).toMonoidHom).map ι).map
            (Spin.spinAction (bmsdop_Q k f)) = siegelGroup (bmsdop_Q k f) a₁ a₂) :=
    hgg.symm ▸ ⟨ι₁, Or.inl ⟨Or.inr rfl, hρ3, hrank'⟩, hι₁center, hι₁range.trans hJ'.symm, hclos⟩
  obtain ⟨ι', hdisj', hcenter', hrange', hclos'⟩ := hgoal
  exact ⟨.POmegaMinus, ρ, ι', hdisj', hcenter', hrange', hclos'⟩

private lemma bmsdopx_frozenClosure_of_plus_plane
    (k f : ℕ)
    (S : Set (GL (Fin (k + 3) ⊕ Fin (k + 3)) (GaloisField 2 f)))
    {e : Matrix (Fin (k + 3) ⊕ Fin (k + 3)) (Fin (k + 3) ⊕ Fin (k + 3)) (GaloisField 2 f)}
    {J' : Subgroup ↥(spinGroup (bmsdop_Q k f))}
    (h1 : bmsdop_geom₁ k f S e) (h2 : bmsdop_geom₂ k f S e)
    (hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s')
    (heA : e ∈ Algebra.adjoin (GaloisField 2 f) (Units.val '' S))
    (hJe : IsComponentOf J' ⁅bmsdop_Ge k f S e, bmsdop_Ge k f S e⁆)
    (hf : 1 ≤ f)
    (θ : (Fin 1 ⊕ Fin 1 → GaloisField 2 f) ≃ₗ[GaloisField 2 f] ↥(bmsdop_W k f e))
    (hθ : ∀ x, (bmsdop_blockForm k f e) (θ x) = (Spin.quadPlus 1 (GaloisField 2 f)) x) :
    bmsdopx_FrozenClosure k f S e J' :=
  False.elim (bmsdop_component_bot_false k f S hJe
    (bmsdop_commutator_bot_of_two_dim k f S h1 h2 hS heA
      (Spin.quadPlus 1 (GaloisField 2 f))
      (Spin.nondegenerate_polarBilin_quadPlus 1 (GaloisField 2 f)) (by simp) θ hθ))

private lemma bmsdopx_frozenClosure_of_plus_ge_two
    (k f : ℕ)
    (S : Set (GL (Fin (k + 3) ⊕ Fin (k + 3)) (GaloisField 2 f)))
    {e : Matrix (Fin (k + 3) ⊕ Fin (k + 3)) (Fin (k + 3) ⊕ Fin (k + 3)) (GaloisField 2 f)}
    {J' : Subgroup ↥(spinGroup (bmsdop_Q k f))}
    (h1 : bmsdop_geom₁ k f S e) (h2 : bmsdop_geom₂ k f S e)
    (hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s')
    (heA : e ∈ Algebra.adjoin (GaloisField 2 f) (Units.val '' S))
    (hJe : IsComponentOf J' ⁅bmsdop_Ge k f S e, bmsdop_Ge k f S e⁆)
    (hf : 1 ≤ f) (ρ : ℕ) (hρ : e.rank = 2 * ρ) (hρ2 : 2 ≤ ρ)
    (θ : (Fin ρ ⊕ Fin ρ → GaloisField 2 f) ≃ₗ[GaloisField 2 f] ↥(bmsdop_W k f e))
    (hθ : ∀ x, (bmsdop_blockForm k f e) (θ x) = (Spin.quadPlus ρ (GaloisField 2 f)) x) :
    bmsdopx_FrozenClosure k f S e J' := by
  rcases Nat.lt_or_ge ρ 3 with h | h
  · have hρe : ρ = 2 := by omega
    subst hρe
    exact bmsdopx_r2_closure k f S h1 h2 hS heA hJe θ hθ (by omega)
  · exact bmsdopx_generic_closure_plus k f S h1 h2 hS heA hJe ρ h hρ hf θ hθ

private lemma bmsdopx_frozenClosure_of_minus_lt_three
    (k f : ℕ)
    (S : Set (GL (Fin (k + 3) ⊕ Fin (k + 3)) (GaloisField 2 f)))
    {e : Matrix (Fin (k + 3) ⊕ Fin (k + 3)) (Fin (k + 3) ⊕ Fin (k + 3)) (GaloisField 2 f)}
    {J' : Subgroup ↥(spinGroup (bmsdop_Q k f))}
    (h1 : bmsdop_geom₁ k f S e) (h2 : bmsdop_geom₂ k f S e)
    (hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s')
    (heA : e ∈ Algebra.adjoin (GaloisField 2 f) (Units.val '' S))
    (hJe : IsComponentOf J' ⁅bmsdop_Ge k f S e, bmsdop_Ge k f S e⁆)
    (hnm : ¬ (e.rank = 4 ∧ ∀ x y : (Fin (k + 3) ⊕ Fin (k + 3)) → (GaloisField 2 f),
      Matrix.mulVec e x = x → Matrix.mulVec e y = y → (bmsdop_Q k f) x = 0 →
      (bmsdop_Q k f) y = 0 → QuadraticMap.polar (bmsdop_Q k f) x y = 0 →
      ¬ LinearIndependent (GaloisField 2 f) ![x, y]))
    (ρ : ℕ) (hρ : e.rank = 2 * ρ) (hρ1 : 1 ≤ ρ) (hρlt : ρ < 3) (hf : 1 ≤ f)
    (β γ : GaloisField 2 f) (hirr : ∀ s : GaloisField 2 f, s ^ 2 + β * s + γ ≠ 0)
    (θ : (Fin (ρ - 1) ⊕ Fin (ρ - 1) ⊕ Fin 2 → GaloisField 2 f) ≃ₗ[GaloisField 2 f]
      ↥(bmsdop_W k f e))
    (hθ : ∀ x, (bmsdop_blockForm k f e) (θ x) = (Spin.quadMinus ρ (GaloisField 2 f) β γ) x) :
    bmsdopx_FrozenClosure k f S e J' := by
  rcases Nat.lt_or_ge ρ 2 with hlt | hge
  · have hρe : ρ = 1 := by omega
    subst hρe
    exact False.elim (bmsdop_component_bot_false k f S hJe
      (bmsdop_commutator_bot_of_two_dim k f S h1 h2 hS heA
        (Spin.quadMinus 1 (GaloisField 2 f) β γ)
        (Spin.nondegenerate_polarBilin_quadMinus_of_finite 1 (GaloisField 2 f) hirr)
        (by simp) θ hθ))
  · have hρe : ρ = 2 := by omega
    subst hρe
    exact False.elim (absurd ⟨by simpa using hρ,
      bmsdop_minus_two_block_no_singular_pair k f S h1 h2 β γ hirr θ hθ⟩ hnm)

private lemma bmsdopx_frozenClosure_of_minus_ge_three
    (k f : ℕ)
    (S : Set (GL (Fin (k + 3) ⊕ Fin (k + 3)) (GaloisField 2 f)))
    {e : Matrix (Fin (k + 3) ⊕ Fin (k + 3)) (Fin (k + 3) ⊕ Fin (k + 3)) (GaloisField 2 f)}
    {J' : Subgroup ↥(spinGroup (bmsdop_Q k f))}
    (h1 : bmsdop_geom₁ k f S e) (h2 : bmsdop_geom₂ k f S e)
    (hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s')
    (heA : e ∈ Algebra.adjoin (GaloisField 2 f) (Units.val '' S))
    (hJe : IsComponentOf J' ⁅bmsdop_Ge k f S e, bmsdop_Ge k f S e⁆)
    (hf : 1 ≤ f)
    (ρ : ℕ) (hρ : e.rank = 2 * ρ) (hρ3 : 3 ≤ ρ)
    (β γ : GaloisField 2 f) (hirr : ∀ s : GaloisField 2 f, s ^ 2 + β * s + γ ≠ 0)
    (θ : (Fin (ρ - 1) ⊕ Fin (ρ - 1) ⊕ Fin 2 → GaloisField 2 f) ≃ₗ[GaloisField 2 f]
      ↥(bmsdop_W k f e))
    (hθ : ∀ x, (bmsdop_blockForm k f e) (θ x) = (Spin.quadMinus ρ (GaloisField 2 f) β γ) x) :
    bmsdopx_FrozenClosure k f S e J' := by
  obtain ⟨eiso⟩ := bmsdop_minus_arf_isometry f ρ β γ hirr
  have hθ' : ∀ x, (bmsdop_blockForm k f e) ((((eiso.toLinearEquiv).symm).trans θ) x) =
      (Spin.quadMinus ρ (GaloisField 2 f) (minusCoeffs 2 f).1 (minusCoeffs 2 f).2) x := by
    intro x
    rw [LinearEquiv.trans_apply, hθ]
    rw [← QuadraticMap.IsometryEquiv.map_app eiso ((eiso.toLinearEquiv).symm x)]
    exact congrArg (Spin.quadMinus ρ (GaloisField 2 f) (minusCoeffs 2 f).1
      (minusCoeffs 2 f).2) (LinearEquiv.apply_symm_apply eiso.toLinearEquiv x)
  by_cases hρ4 : 4 ≤ ρ
  · exact bmsdopx_generic_closure_minus k f S h1 h2 hS heA hJe ρ hρ3 hρ hf
      (bmsdop_std_quasisimple_minus f ρ hρ4 (minusCoeffs 2 f).1 (minusCoeffs 2 f).2
        (minusCoeffs_irr 2 f))
      (bmsdop_minus_range_of_four ρ f hρ4 (minusCoeffs 2 f).1 (minusCoeffs 2 f).2
        (minusCoeffs_irr 2 f))
      (bmsdop_ambient_minus_of_four ρ f hρ4 (minusCoeffs 2 f).1 (minusCoeffs 2 f).2
        (minusCoeffs_irr 2 f))
      (((eiso.toLinearEquiv).symm).trans θ) hθ'
  · have hρ3eq : ρ = 3 := by omega
    subst hρ3eq
    exact bmsdopx_generic_closure_minus k f S h1 h2 hS heA hJe 3 (by norm_num) hρ hf
      (bmsdop_r3m_quasisimple f (minusCoeffs 2 f).1 (minusCoeffs 2 f).2 (minusCoeffs_irr 2 f))
      (bmsdop_r3m_range f (minusCoeffs 2 f).1 (minusCoeffs 2 f).2 (minusCoeffs_irr 2 f))
      (bmsdop_r3m_ambient f (minusCoeffs 2 f).1 (minusCoeffs 2 f).2 (minusCoeffs_irr 2 f))
      (((eiso.toLinearEquiv).symm).trans θ) hθ'

private theorem bmsdopx_closure_of_geom
    (k f : ℕ)
    (S : Set (GL (Fin (k + 3) ⊕ Fin (k + 3)) (GaloisField 2 f)))
    {e : Matrix (Fin (k + 3) ⊕ Fin (k + 3)) (Fin (k + 3) ⊕ Fin (k + 3)) (GaloisField 2 f)}
    {J' : Subgroup ↥(spinGroup (bmsdop_Q k f))}
    (h1 : bmsdop_geom₁ k f S e) (h2 : bmsdop_geom₂ k f S e)
    (hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s')
    (heA : e ∈ Algebra.adjoin (GaloisField 2 f) (Units.val '' S))
    (hJe : IsComponentOf J' ⁅bmsdop_Ge k f S e, bmsdop_Ge k f S e⁆)
    (hnm : ¬ (e.rank = 4 ∧ ∀ x y : (Fin (k + 3) ⊕ Fin (k + 3)) → (GaloisField 2 f),
      Matrix.mulVec e x = x → Matrix.mulVec e y = y → (bmsdop_Q k f) x = 0 →
      (bmsdop_Q k f) y = 0 → QuadraticMap.polar (bmsdop_Q k f) x y = 0 →
      ¬ LinearIndependent (GaloisField 2 f) ![x, y]))
    (hf : 1 ≤ f) :
    bmsdopx_FrozenClosure k f S e J' := by
  have hrankne : e.rank ≠ 0 := bmsdop_geom_rank_ne_zero k f S h1
  obtain ⟨ρ, hρ'⟩ := Nat.even_iff.mpr h1.2.2.2.2
  have hρ : e.rank = 2 * ρ := by omega
  have hρ1 : 1 ≤ ρ := by omega
  rcases bmsdop_theta k f S h1 h2 ρ hρ hρ1 with ⟨θ, hθ⟩ | ⟨β, γ, hirr, θ, hθ⟩
  · rcases Nat.lt_or_ge ρ 2 with h2lt | h2ge
    · have hρe : ρ = 1 := by omega
      subst hρe
      exact bmsdopx_frozenClosure_of_plus_plane k f S h1 h2 hS heA hJe hf θ hθ
    · exact bmsdopx_frozenClosure_of_plus_ge_two k f S h1 h2 hS heA hJe hf ρ hρ h2ge θ hθ
  · rcases Nat.lt_or_ge ρ 3 with h3lt | h3ge
    · exact bmsdopx_frozenClosure_of_minus_lt_three k f S h1 h2 hS heA hJe hnm ρ hρ hρ1
        h3lt hf β γ hirr θ hθ
    · exact bmsdopx_frozenClosure_of_minus_ge_three k f S h1 h2 hS heA hJe hf ρ hρ h3ge
        β γ hirr θ hθ

theorem exists_blockModel_selfDual_POmegaPlus_explicit
    (k f : ℕ) (hf : 1 ≤ f) (S : Set (GL (Fin (k + 3) ⊕ Fin (k + 3)) (GaloisField 2 f)))
    (hSU : ∀ s ∈ S, s ∈ (Spin.spinMatrix (Spin.quadPlus (k + 3) (GaloisField 2 f))).range)
    (hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s') (hodd : ∀ s ∈ S, Odd (orderOf s))
    {e : Matrix (Fin (k + 3) ⊕ Fin (k + 3)) (Fin (k + 3) ⊕ Fin (k + 3)) (GaloisField 2 f)}
    (he : IsPrimIdemIn (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e)
    (hadj : formAdj (RingHom.id (GaloisField 2 f))
      (LinearMap.toMatrix₂' (GaloisField 2 f)
      (QuadraticMap.polarBilin (Spin.quadPlus (k + 3) (GaloisField 2 f)))) e = e)
      (hdeg : blockDegree (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e < 2)
    (hnm : ¬
      (e.rank = 4 ∧ ∀ x y : (Fin (k + 3) ⊕ Fin (k + 3)) → (GaloisField 2 f), Matrix.mulVec e x = x →
      Matrix.mulVec e y = y →
      (Spin.quadPlus (k + 3) (GaloisField 2 f)) x = 0 → (Spin.quadPlus (k + 3) (GaloisField 2 f)) y
      = 0 → QuadraticMap.polar (Spin.quadPlus (k + 3) (GaloisField 2 f)) x y = 0 → ¬
      LinearIndependent (GaloisField 2 f) ![x, y]))
    {J' : Subgroup ↥(spinGroup (Spin.quadPlus (k + 3) (GaloisField 2 f)))}
    (hJe : IsComponentOf J'
      ⁅glBlockCentralizer (Spin.spinMatrix (Spin.quadPlus (k + 3) (GaloisField 2 f))) S (e),
      glBlockCentralizer (Spin.spinMatrix (Spin.quadPlus (k + 3) (GaloisField 2 f))) S (e)⁆) :
    ∃ (t' : StatedLieTag) (m : ℕ)
      (ι : (ggU t' m f).K →* ↥(spinGroup (Spin.quadPlus (k + 3) (GaloisField 2 f))))
      (β₀ : Fin (ggU t' m f).D.rank → ℤ), (((t' = .POmegaPlus ∨ t' = .POmegaMinus) ∧ 3 ≤ m ∧ 2 * m =
        Module.finrank (GaloisField 2 f) (LinearMap.range (Matrix.toLin' e))) ∨
        (t' = .PSL ∧ m = 2 ∧
          Module.finrank (GaloisField 2 f) (LinearMap.range (Matrix.toLin' e)) = 4)) ∧
      GGLongRoot (ggU t' m f).D β₀ ∧
      (∀ y, ι y ∈ Subgroup.center ↥(spinGroup (Spin.quadPlus (k + 3) (GaloisField 2 f))) → y ∈
        Subgroup.center (ggU t' m f).K) ∧ ι.range = J' ∧
      ∃ a₁ a₂ b₁ b₂ : (Fin (k + 3) ⊕ Fin (k + 3)) → (GaloisField 2 f),
        ((Spin.quadPlus (k + 3) (GaloisField 2 f)) a₁ = 0 ∧
          (Spin.quadPlus (k + 3) (GaloisField 2 f)) a₂ = 0 ∧
          (Spin.quadPlus (k + 3) (GaloisField 2 f)) b₁ = 0 ∧
          (Spin.quadPlus (k + 3) (GaloisField 2 f)) b₂ = 0) ∧
        QuadraticMap.polar (Spin.quadPlus (k + 3) (GaloisField 2 f)) a₁ b₁ = 1 ∧ QuadraticMap.polar
          (Spin.quadPlus (k + 3) (GaloisField 2 f)) a₂ b₂ = 1 ∧
        (QuadraticMap.polar (Spin.quadPlus (k + 3) (GaloisField 2 f)) a₁ a₂ = 0 ∧ QuadraticMap.polar
          (Spin.quadPlus (k + 3) (GaloisField 2 f)) b₁ b₂ = 0 ∧
          QuadraticMap.polar (Spin.quadPlus (k + 3) (GaloisField 2 f)) a₁ b₂ = 0 ∧
            QuadraticMap.polar (Spin.quadPlus (k + 3) (GaloisField 2 f)) a₂ b₁ = 0) ∧
        (((ggU t' m f).D.rootGroup β₀).map ι).map
        (Spin.spinAction (Spin.quadPlus (k + 3) (GaloisField 2 f))) = siegelGroup
        (Spin.quadPlus (k + 3) (GaloisField 2 f)) a₁ a₂ ∧
        (((ggU t' m f).D.rootGroup (-β₀)).map ι).map
        (Spin.spinAction (Spin.quadPlus (k + 3) (GaloisField 2 f))) = siegelGroup
        (Spin.quadPlus (k + 3) (GaloisField 2 f)) b₁ b₂ := by
  exact bmsdopx_model_of_geom k f S
    (bmsdop_block_idem_and_degree k f S hS hodd he hadj hdeg hnm)
    (bmsdop_block_trivial_and_split k f S hSU hS hodd he hadj hdeg hnm)
    hS he.1 hJe hnm hf

theorem exists_blockModelClosure_selfDual_POmegaPlus_explicit
    (k f : ℕ) (hf : 1 ≤ f) (S : Set (GL (Fin (k + 3) ⊕ Fin (k + 3)) (GaloisField 2 f)))
    (hSU : ∀ s ∈ S, s ∈ (Spin.spinMatrix (Spin.quadPlus (k + 3) (GaloisField 2 f))).range)
    (hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s') (hodd : ∀ s ∈ S, Odd (orderOf s))
    {e : Matrix (Fin (k + 3) ⊕ Fin (k + 3)) (Fin (k + 3) ⊕ Fin (k + 3)) (GaloisField 2 f)}
    (he : IsPrimIdemIn (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e)
    (hadj : formAdj (RingHom.id (GaloisField 2 f))
      (LinearMap.toMatrix₂' (GaloisField 2 f)
      (QuadraticMap.polarBilin (Spin.quadPlus (k + 3) (GaloisField 2 f)))) e = e)
      (hdeg : blockDegree (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e < 2)
    (hnm : ¬
      (e.rank = 4 ∧ ∀ x y : (Fin (k + 3) ⊕ Fin (k + 3)) → (GaloisField 2 f), Matrix.mulVec e x = x →
      Matrix.mulVec e y = y →
      (Spin.quadPlus (k + 3) (GaloisField 2 f)) x = 0 → (Spin.quadPlus (k + 3) (GaloisField 2 f)) y
      = 0 → QuadraticMap.polar (Spin.quadPlus (k + 3) (GaloisField 2 f)) x y = 0 → ¬
      LinearIndependent (GaloisField 2 f) ![x, y]))
    {J' : Subgroup ↥(spinGroup (Spin.quadPlus (k + 3) (GaloisField 2 f)))}
    (hJe : IsComponentOf J'
      ⁅glBlockCentralizer (Spin.spinMatrix (Spin.quadPlus (k + 3) (GaloisField 2 f))) S (e),
      glBlockCentralizer (Spin.spinMatrix (Spin.quadPlus (k + 3) (GaloisField 2 f))) S (e)⁆) :
    ∃ (t' : StatedLieTag) (m : ℕ) (ι : (ggU t' m f).K →* ↥(spinGroup (Spin.quadPlus (k + 3)
        (GaloisField 2 f)))),
      (((t' = .POmegaPlus ∨ t' = .POmegaMinus) ∧ 3 ≤ m ∧ 2 * m =
        Module.finrank (GaloisField 2 f) (LinearMap.range (Matrix.toLin' e))) ∨
        (t' = .PSL ∧ m = 2 ∧
          Module.finrank (GaloisField 2 f) (LinearMap.range (Matrix.toLin' e)) = 4)) ∧
      (∀ y, ι y ∈ Subgroup.center ↥(spinGroup (Spin.quadPlus (k + 3) (GaloisField 2 f))) → y ∈
          Subgroup.center (ggU t' m f).K) ∧
      ι.range = J' ∧
      (∀ a₁ a₂ : ((Fin (k + 3) ⊕ Fin (k + 3)) → GaloisField 2 f), a₁ ≠ 0 → a₂ ≠ 0 →
          LinearIndependent (GaloisField 2 f) ![a₁, a₂] → (Spin.quadPlus (k + 3) (GaloisField 2 f))
          a₁ = 0 → (Spin.quadPlus (k + 3) (GaloisField 2 f)) a₂ = 0 →
        QuadraticMap.polar (Spin.quadPlus (k + 3) (GaloisField 2 f)) a₁ a₂ = 0 → siegelGroup
            (Spin.quadPlus (k + 3) (GaloisField 2 f)) a₁ a₂ ≤ J'.map (Spin.spinAction
            (Spin.quadPlus (k + 3) (GaloisField 2 f))) →
        ∃ (β : Fin (ggU t' m f).D.rank → ℤ) (u : (ggU t' m f).K), β ∈ (ggU t' m f).D.roots ∧
            GGLongRoot (ggU t' m f).D β ∧
          ((((ggU t' m f).D.rootGroup β).map (MulAut.conj u).toMonoidHom).map ι).map
              (Spin.spinAction (Spin.quadPlus (k + 3) (GaloisField 2 f))) = siegelGroup
              (Spin.quadPlus (k + 3) (GaloisField 2 f)) a₁ a₂) := by
  exact bmsdopx_closure_of_geom k f S
    (bmsdop_block_idem_and_degree k f S hS hodd he hadj hdeg hnm)
    (bmsdop_block_trivial_and_split k f S hSU hS hodd he hadj hdeg hnm)
    hS he.1 hJe hnm hf

end CFSG.StandardType.ClassicalPosition
