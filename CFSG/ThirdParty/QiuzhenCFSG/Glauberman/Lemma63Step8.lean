module

public import CFSG.ThirdParty.QiuzhenCFSG.Glauberman.QdMulEquivOfComplement
public import Mathlib.GroupTheory.Complement
public import Mathlib.LinearAlgebra.GeneralLinearGroup.Basic

namespace CFSG
end CFSG
open CFSG

noncomputable section

namespace CFSG.Glauberman

universe u

open scoped IsMulCommutative Pointwise

/-- Glauberman Lemma 6.3, step 8.  If the Step 7 Sylow normalizer is a
complement to `H`, then the compatible Step 6 linear coordinates identify the
ambient group with `Qd(p)`. -/
public theorem qd_equiv_of_step7_complement_data
    {p : ℕ} [Fact p.Prime]
    {Q : Type u} [Group Q]
    (H C K : Subgroup Q) [C.Normal]
    (hHnormal : H.Normal)
    [IsMulCommutative H] [Module (ZMod p) (Additive H)]
    (hgen : K ⊔ H = ⊤)
    (hE : C ⊓ K = ⊥)
    (hCH : C = H)
    (rho : Q ⧸ C →*
      LinearMap.GeneralLinearGroup (ZMod p) (Additive H))
    (hrho_eval : ∀ (g : Q) (v : Additive H),
      Additive.toMul
          (((rho (QuotientGroup.mk' C g) :
            Additive H →ₗ[ZMod p] Additive H) v)) =
        MulAut.conjNormal (H := H) g (Additive.toMul v))
    (coord : Additive H ≃ₗ[ZMod p] qdSpace p)
    (e : (Q ⧸ C) ≃* qdSL p)
    (hintertwine :
      ∀ (g : Q ⧸ C) (v : Additive H),
        coord (((rho g : Additive H →ₗ[ZMod p] Additive H) v)) =
          Matrix.SpecialLinearGroup.toLin' (e g) (coord v)) :
    Nonempty (Q ≃* Qd p) := by
  subst C
  let : H.Normal := hHnormal
  have hdisj : Disjoint H K := by
    rw [disjoint_iff]
    exact hE
  have hcomp : H.IsComplement' K := by
    refine ⟨Subgroup.mul_injective_of_disjoint hdisj, ?_⟩
    intro g
    have hg : g ∈ (H : Set Q) * (K : Set Q) := by
      rw [← Subgroup.normal_mul H K, sup_comm, hgen]
      trivial
    rcases hg with ⟨h, hh, k, hk, rfl⟩
    exact ⟨⟨⟨h, hh⟩, ⟨k, hk⟩⟩, rfl⟩
  let eH : H ≃* Multiplicative (qdSpace p) :=
    AddEquiv.toMultiplicativeRight coord.toAddEquiv
  let eK : K ≃* qdSL p :=
    (hcomp.symm.QuotientMulEquiv).symm.trans e
  have heK (k : K) :
      eK k = e (QuotientGroup.mk' H (k : Q)) := by
    rfl
  have haction : ∀ k : K,
      (((H.normalizerMonoidHom).comp
          (Subgroup.inclusion (H.normalizer_eq_top ▸ le_top))) k).trans eH =
        eH.trans (qdAction p (eK k)) := by
    intro k
    apply MulEquiv.ext
    intro h
    apply Multiplicative.ext
    change coord
        (Additive.ofMul
          (MulAut.conjNormal (H := H) (k : Q) h)) =
      Matrix.SpecialLinearGroup.toLin' (eK k) (coord (Additive.ofMul h))
    rw [heK]
    rw [← hintertwine (QuotientGroup.mk' H (k : Q)) (Additive.ofMul h)]
    congr 1
    exact congrArg Additive.ofMul
      (hrho_eval (k : Q) (Additive.ofMul h)).symm
  exact ⟨qd_mulEquiv_of_complement H K hcomp eH eK haction⟩

end CFSG.Glauberman
