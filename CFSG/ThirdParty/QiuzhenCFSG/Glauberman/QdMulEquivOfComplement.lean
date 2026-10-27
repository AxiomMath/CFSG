module

public import CFSG.ThirdParty.QiuzhenCFSG.Glauberman.Definitions
public import Mathlib.GroupTheory.Complement
public import Mathlib.GroupTheory.SemidirectProduct

namespace CFSG
end CFSG
open CFSG

noncomputable section

namespace CFSG.Glauberman

universe u

/-- A complement acting naturally on an elementary-abelian subgroup reconstructs
the quadratic group `Qd(p)`.  This is the semidirect-product endpoint used in
step 8 of Glauberman's Lemma 6.3. -/
public noncomputable def qd_mulEquiv_of_complement
    {p : ℕ} [Fact p.Prime]
    {Q : Type u} [Group Q]
    (H K : Subgroup Q)
    [H.Normal]
    (hcomp : H.IsComplement' K)
    (eH : H ≃* Multiplicative (qdSpace p))
    (eK : K ≃* qdSL p)
    (haction : ∀ k : K,
      (((H.normalizerMonoidHom).comp
          (Subgroup.inclusion (H.normalizer_eq_top ▸ le_top))) k).trans eH =
        eH.trans (qdAction p (eK k))) :
    Q ≃* Qd p := by
  exact (SemidirectProduct.mulEquivSubgroup hcomp).symm.trans
    (SemidirectProduct.congr eH eK haction)

end CFSG.Glauberman
