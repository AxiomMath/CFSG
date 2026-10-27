module

public import CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.Sec8.L82.Basic
public import CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.Sec8.L82.Local
public import CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.Sec8.L82.Comp

public section

open CFSG.Open

universe u

namespace CFSG.SignalizerFunctorTheorem.McBride.Nonsolv

namespace Counterexample

variable {p : ℕ} {G : Type u} [Group G] [Finite G] {A : Subgroup G} {θ : G → Subgroup G}
  {r : ℕ} {S : Subgroup G}

theorem lemma_8_2
    (h : Counterexample p A θ) (hr : InPiTheta A θ r) (hS : IsSr p A θ r S)
    {E K : Subgroup G} (hB : TypeB p A θ E K) :
    CFSG.inSubgroup CFSG.generalizedFitting (thetaOf θ E) ≤ thetaOf θ A ⊔ zOf S := by
  have hE := hB.mem
  have hE0 : E ≠ ⊥ := h.ne_bot_of_mem_E1 hE
  rw [L82.inSubgroup_generalizedFitting_eq_kOf (h.sol_thetaOf hE.1 hE0)]
  have hrank : p ^ 2 * Nat.card E ≤ Nat.card A := by
    rw [hE.2, h.card, pow_one]
    exact (by ring : p ^ 2 * p = p ^ 3).le
  have hAX : A ≤ Subgroup.normalizer ((kOf (thetaOf θ E) : Subgroup G) : Set G) :=
    le_normalizer_kOf_of_le_normalizer (h.isFunctor.normalizes_thetaOf hE.1)
  have hX : Nat.Coprime p (Nat.card (kOf (thetaOf θ E))) :=
    (h.isFunctor.coprime_thetaOf hE.1 hE0).of_dvd_right
      (Subgroup.card_dvd_of_le (kOf_le (thetaOf θ E)))
  calc kOf (thetaOf θ E)
      = ⨆ (b : G) (_ : b ∈ A) (_ : b ∉ E), kOf (thetaOf θ E) ⊓ Subgroup.centralizer {b} :=
        (iSup_inf_centralizer_sdiff h.prime h.elemAbelian hE.1 hrank hAX hX).symm
    _ ≤ thetaOf θ A ⊔ zOf S :=
        iSup_le fun b => iSup_le fun hb => iSup_le fun hbE =>
          L82.kOf_inf_centralizer_le h hr hS hB hb hbE

end Counterexample

end CFSG.SignalizerFunctorTheorem.McBride.Nonsolv
