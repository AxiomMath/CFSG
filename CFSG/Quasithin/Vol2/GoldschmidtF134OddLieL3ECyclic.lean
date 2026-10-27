module

public import CFSG.Quasithin.Vol2.F134Basic
public import CFSG.Quasithin.Vol2.GoldschmidtF134OddLieCfg
public import CFSG.LocalAnalysis.SectionRank.OddCover.CyclicSylow

public section

namespace CFSG.Quasithin.H13.NQCore.Psl3Even

open CFSG.Assembly.LowTwoRank

variable {A : Type} [Group A] {p : ℕ} {L P T : Subgroup A}

theorem false_of_not_dvd_pred [Finite A] [Fact p.Prime] (h : OddCfg p L P T) {K : Type} [Field K]
    [Finite K] (hq : ¬ p ∣ Nat.card K) (hq1 : ¬ p ∣ Nat.card K - 1)
    (e : ↥L ≃* StatedProj (StatedSL 3 K)) : False := by
  have hcyc : ∀ Q : Subgroup (StatedProj (StatedSL 3 K)), IsPGroup p Q → IsCyclic Q :=
    fun Q hQ => CFSG.Quasithin.F134.isCyclic_of_isPGroup_of_surjective
      (QuotientGroup.mk'_surjective _) (fun S =>
        CFSG.SectionRank.OddCover.isCyclic_of_isPGroup_of_le_GL_three hq hq1 S.isPGroup') Q hQ
  have h1 : IsPGroup p (P.subgroupOf L) :=
    h.isPGroup.of_equiv (Subgroup.subgroupOfEquivOfLe h.le).symm
  have h2 : IsCyclic ((P.subgroupOf L).map e.toMonoidHom) := hcyc _ (h1.map _)
  have h3 : IsCyclic (P.subgroupOf L) :=
    ((P.subgroupOf L).equivMapOfInjective e.toMonoidHom e.injective).isCyclic.mpr h2
  exact h.not_isCyclic ((Subgroup.subgroupOfEquivOfLe h.le).isCyclic.mp h3)

end CFSG.Quasithin.H13.NQCore.Psl3Even
