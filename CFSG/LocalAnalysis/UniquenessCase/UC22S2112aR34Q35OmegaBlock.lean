module

public import CFSG.GroupTheory.SylowPQMaximal.Defs
public import CFSG.Blueprint.Catalog
import CFSG.GroupTheory.SylowPQMaximal.Extension
import CFSG.GroupTheory.SylowPQMaximal.Basic
import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec3ClSmall
import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.BridgeLowCent
import TauCeti.GroupTheory.Elementary
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec2Block

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.Q35Omega7

open CFSG.OddStandard.SmallF3.Omega CFSG.GroupTheory CFSG.Blueprint

variable {V : Type} [AddCommGroup V] [Module (ZMod 3) V] [FiniteDimensional (ZMod 3) V]
  {Q : QuadraticForm (ZMod 3) V}

theorem sylowPQMaximal_omegaGroup_inf_centralizer (hQ : Q.Nondegenerate) {s : OGroup Q}
    (hs : s * s = 1)
    (hfix : SylowPQMaximal 2 5 (omegaGroup (nondegenerate_restrict_fixSp hQ hs)))
    (hcomm : SylowPQMaximal 2 5 (omegaGroup (nondegenerate_restrict_commSp hQ hs))) :
    SylowPQMaximal 2 5 ↥(omegaGroup hQ ⊓ Subgroup.centralizer ({s} : Set (OGroup Q))) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Finite (OGroup Q) := CFSG.ClassicalInvolution.finite_orthogonalGroup_of_finite
  let C : Subgroup (OGroup Q) := Subgroup.centralizer ({s} : Set (OGroup Q))
  let M : Subgroup (OGroup Q) := omegaGroup hQ ⊓ C
  let N : Subgroup (OGroup Q) := blockOmega hQ hs
  let A : Subgroup (OGroup (Q.restrict (fixSp s))) :=
    omegaGroup (nondegenerate_restrict_fixSp hQ hs)
  let B : Subgroup (OGroup (Q.restrict (commSp s))) :=
    omegaGroup (nondegenerate_restrict_commSp hQ hs)
  have hNmap : N = (Subgroup.prod A B).map (blockHom hs) := rfl
  have hNle : N ≤ M := by
    refine le_inf ?_ ?_
    · intro x hx
      rw [hNmap] at hx
      obtain ⟨p, hp, rfl⟩ := Subgroup.mem_map.mp hx
      have hp' : p.1 ∈ A ∧ p.2 ∈ B := Subgroup.mem_prod.mp hp
      have h1 := cl_blockHom_left_mem_omegaGroup hQ hs hp'.1
      have h2 := cl_blockHom_right_mem_omegaGroup hQ hs hp'.2
      have hpdecomp : p = (p.1, 1) * (1, p.2) := by
        ext <;> simp
      rw [hpdecomp, map_mul]
      exact mul_mem h1 h2
    · intro x hx
      rw [hNmap] at hx
      obtain ⟨p, -, rfl⟩ := Subgroup.mem_map.mp hx
      have hxr : blockHom hs p ∈ (blockHom hs).range := MonoidHom.mem_range.mpr ⟨p, rfl⟩
      rwa [range_blockHom hQ hs] at hxr
  let N' : Subgroup M := N.subgroupOf M
  have hN'normal : N'.Normal := by
    have hCN : (N.subgroupOf C).Normal := blockOmega_normal_in_centralizer hQ hs
    have hleC : N ≤ C := hNle.trans inf_le_right
    have hCle : C ≤ Subgroup.normalizer N :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer hleC).mp hCN
    exact (Subgroup.normal_subgroupOf_iff_le_normalizer hNle).mpr (inf_le_right.trans hCle)
  have : N'.Normal := hN'normal
  have hEprod : SylowPQMaximal 2 5 ↥(Subgroup.prod A B) :=
    SylowPQMaximal.of_mulEquiv (Subgroup.prodEquiv A B).symm (SylowPQMaximal.prod hfix hcomm)
  have e : ↥(Subgroup.prod A B) ≃* ↥N' :=
    (Subgroup.equivMapOfInjective (Subgroup.prod A B) (blockHom hs)
      (blockHom_injective hs)).trans (Subgroup.subgroupOfEquivOfLe hNle).symm
  have hE : SylowPQMaximal 2 5 ↥N' := SylowPQMaximal.of_mulEquiv e hEprod
  have hquot : IsPGroup 2 (M ⧸ N') := by
    refine TauCeti.isPGroup_quotient_of_forall_exists_pow_mem (C := N') ?_
    intro g
    refine ⟨1, ?_⟩
    have hg : ((g : M) : OGroup Q) ∈ Subgroup.centralizer ({s} : Set (OGroup Q)) :=
      (g : M).2.2
    have hsq : ((g : M) : OGroup Q) * ((g : M) : OGroup Q) ∈ N :=
      mul_self_mem_blockOmega hQ hs hg
    simpa [N', N, Subgroup.mem_subgroupOf, pow_two] using hsq
  exact SylowPQMaximal.of_normal_of_isPGroup_quotient N' hE hquot

theorem sylowPQMaximal_omegaGroup_of_small (hQ : Q.Nondegenerate)
    (h : Module.finrank (ZMod 3) V ≤ 3 ∨
      (Module.finrank (ZMod 3) V = 4 ∧ quadSign Q = 1)) :
    SylowPQMaximal 2 5 (omegaGroup hQ) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Finite (OGroup Q) := CFSG.ClassicalInvolution.finite_orthogonalGroup_of_finite
  have : Finite (omegaGroup hQ) := Subtype.finite
  apply sylowPQMaximal_of_not_dvd
  intro h5
  have hdvd : 5 ∣ Nat.card (OGroup Q) :=
    h5.trans (Subgroup.card_subgroup_dvd_card (omegaGroup hQ))
  rcases h with h3 | ⟨h4, hs4⟩
  · rcases le_or_gt (Module.finrank (ZMod 3) V) 1 with h1 | h1
    · rw [cl_omegaGroup_eq_bot_of_finrank_le_one hQ h1, Subgroup.card_bot] at h5
      norm_num at h5
    · have h2 : Module.finrank (ZMod 3) V = 2 ∨ Module.finrank (ZMod 3) V = 3 := by omega
      rcases h2 with h2 | h3
      · rcases Int.units_eq_one_or (quadSign Q) with hs | hs
        · rw [natCard_oGroup_two_plus hQ h2 hs] at hdvd
          norm_num at hdvd
        · rw [natCard_oGroup_two_minus hQ h2 hs] at hdvd
          norm_num at hdvd
      · rw [natCard_oGroup_three hQ h3] at hdvd
        norm_num at hdvd
  · rw [natCard_oGroup_four_plus hQ h4 hs4] at hdvd
    norm_num at hdvd

theorem sylowPQMaximal_omegaGroup_five
    (hE5 : ∀ (X : Type) [Group X], LieModel X .PSp 2 3 1 → SylowPQMaximal 2 5 X)
    (hQ : Q.Nondegenerate) (hdim : Module.finrank (ZMod 3) V = 5) :
    SylowPQMaximal 2 5 (omegaGroup hQ) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Finite (OGroup Q) := CFSG.ClassicalInvolution.finite_orthogonalGroup_of_finite
  have : Finite (omegaGroup hQ) := Subtype.finite
  have hZcard : Nat.card (Subgroup.center (omegaGroup hQ)) = 1 :=
    natCard_center_omegaGroup_five hQ hdim
  have hZ : IsPGroup 2 (Subgroup.center (omegaGroup hQ)) :=
    IsPGroup.of_card (n := 0) (by rw [hZcard]; norm_num)
  exact SylowPQMaximal.of_quotient_of_isPGroup (Subgroup.center (omegaGroup hQ)) hZ
    (hE5 _ (lieModel_quotient_center_omegaGroup_five hQ hdim))

theorem sylowPQMaximal_omegaGroup_six_minus
    (hE6 : ∀ (X : Type) [Group X], LieModel X .PSU 4 3 1 → SylowPQMaximal 2 5 X)
    (hQ : Q.Nondegenerate) (hdim : Module.finrank (ZMod 3) V = 6) (hs : quadSign Q = -1) :
    SylowPQMaximal 2 5 (omegaGroup hQ) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Finite (OGroup Q) := CFSG.ClassicalInvolution.finite_orthogonalGroup_of_finite
  have : Finite (omegaGroup hQ) := Subtype.finite
  have hZcard : Nat.card (Subgroup.center (omegaGroup hQ)) = 2 :=
    natCard_center_omegaGroup_six_minus hQ hdim hs
  have hZ : IsPGroup 2 (Subgroup.center (omegaGroup hQ)) :=
    IsPGroup.of_card (n := 1) (by rw [hZcard]; norm_num)
  exact SylowPQMaximal.of_quotient_of_isPGroup (Subgroup.center (omegaGroup hQ)) hZ
    (hE6 _ (lieModel_quotient_center_omegaGroup_six_minus hQ hdim hs))

end CFSG.LocalAnalysis.UniquenessCase.UC22.Q35Omega7
