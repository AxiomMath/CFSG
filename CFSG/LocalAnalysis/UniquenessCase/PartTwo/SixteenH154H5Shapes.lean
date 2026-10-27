module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154H5Cfg

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {W : Type} [CommGroup W]

private theorem s16h_finite_mulAut [Finite W] : Finite (MulAut W) := by
  classical
  exact Finite.of_injective (fun f : MulAut W => (f : W → W))
    (fun f g h => MulEquiv.ext (congrFun h))

private theorem s16h_eq_of_subnormal_of_quasisimple {A L K : Subgroup (MulAut W)}
    (hLq : CFSG.Open.IsQuasisimple ↥L) (hKsn : CFSG.Open.IsSubnormal K A)
    (hLA : L ≤ A) (hKq : CFSG.Open.IsQuasisimple ↥K) (hKL : K ≤ L) (hKne : K ≠ ⊥) :
    K = L := by
  have hKsnL : CFSG.Open.IsSubnormal K L := by
    have h := hKsn.inf_of_le hLA
    rwa [inf_eq_left.2 hKL] at h
  haveI : Group.IsPerfect ↥(K.subgroupOf L) :=
    ⟨(CFSG.Open.IsQuasisimple.of_mulEquiv (Subgroup.subgroupOfEquivOfLe hKL) hKq).1⟩
  have hsub : CFSG.Open.IsSubnormal (K.subgroupOf L) (⊤ : Subgroup ↥L) :=
    CFSG.Open.IsSubnormal.of_mathlib (CFSG.Open.IsSubnormal.subgroupOf hKsnL)
  rcases CFSG.ComponentClassification.Quasisimple.perfect_subnormal_eq_bot_or_eq_top
      hLq (K.subgroupOf L) hsub with hbot | htop
  · exfalso
    have hdisj : Disjoint K L := Subgroup.subgroupOf_eq_bot.mp hbot
    exact hKne (hdisj.eq_bot_of_le hKL)
  · exact le_antisymm hKL (Subgroup.subgroupOf_eq_top.mp htop)

theorem s16h_H5_not_pgroup [Finite W] {A L : Subgroup (MulAut W)} {t : MulAut W}
    (hc : s16h_H5Cfg A L t) (h : Conc4_133 A t L) : False := by
  classical
  obtain ⟨p, hp, hLp, hcomm, -⟩ := h
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : Finite (MulAut W) := s16h_finite_mulAut
  have hLne : L ≠ ⊥ := by
    intro hbot
    exact hcomm (by rw [hbot, Subgroup.commutator_bot_left])
  haveI : Nontrivial ↥L := (Subgroup.nontrivial_iff_ne_bot L).2 hLne
  have hpg : IsPGroup p ↥L := by
    have hpA : IsPGroup p (pCoreOf p A) := by
      unfold CFSG.Open.pCoreOf
      exact (CFSG.pCore_isPGroup (p := p) (G := ↥A)).map A.subtype
    exact hpA.to_le hLp
  have hnil : Group.IsNilpotent ↥L := hpg.isNilpotent
  haveI : Group.IsPerfect ↥L := ⟨hc.comp.2.2.1⟩
  exact Group.IsPerfect.not_isNilpotent ↥L hnil

theorem s16h_H5_not_tensor [Finite W] {A L : Subgroup (MulAut W)} {t : MulAut W}
    (hc : s16h_H5Cfg A L t)
    (h : ∃ K ∈ {K | IsComponentOf K A}, ∃ g ∈ A, K ≠ K.map (MulAut.conj g).toMonoidHom ∧
        L = K ⊔ K.map (MulAut.conj g).toMonoidHom ∧
        ((IsL3 ↥K 1 ∧ NatTensor L (commSub ⊤ L) ⊥ 3 1) ∨
          (UC22.IsL2 ↥K 2 ∧ NatTensor L (commSub ⊤ L) ⊥ 2 2) ∨
          (UC22.IsL2 ↥K 3 ∧ NatTensor L (commSub ⊤ L) ⊥ 2 3))) : False := by
  classical
  obtain ⟨K, hKA, g, _, hKgne, hLK, -⟩ := h
  have hKleL : K ≤ L := by rw [hLK]; exact le_sup_left
  have hKg_le_L : K.map (MulAut.conj g).toMonoidHom ≤ L := by
    rw [hLK]; exact le_sup_right
  have hKne : K ≠ ⊥ := by
    intro hbot
    exact hKgne (by rw [hbot, Subgroup.map_bot])
  have hKL : K = L :=
    s16h_eq_of_subnormal_of_quasisimple hc.comp.2.2 hKA.2.1 hc.comp.1 hKA.2.2 hKleL hKne
  have hKg_le_K : K.map (MulAut.conj g).toMonoidHom ≤ K := by
    simpa only [← hKL] using hKg_le_L
  haveI : Finite (MulAut W) := s16h_finite_mulAut
  have hcard : Nat.card ↥(K.map (MulAut.conj g).toMonoidHom) = Nat.card ↥K :=
    Subgroup.card_map_of_injective (MulAut.conj g).injective
  have hKgeq : K.map (MulAut.conj g).toMonoidHom = K :=
    Subgroup.eq_of_le_of_card_ge hKg_le_K (le_of_eq hcard.symm)
  exact hKgne hKgeq.symm

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
