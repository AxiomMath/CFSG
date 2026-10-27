module

public import CFSG.Monster.Existence.StdOdd.Cert.Cent7B
public import CFSG.Monster.Existence.StdOdd.Cert.Sylow57
public import CFSG.LieType.Chevalley.C2E6NativeF4Building
public import CFSG.Monster.Existence.BabyW2Classes

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.StandardType.SporadicShape

open CFSG.Monster.Existence.StdOdd CFSG.Monster.Existence.StdOdd.Cert
open CFSG.LieType.Chevalley.C2E6Std

theorem gk7c_stdGroup_exists_not_dvd_nine :
    ∀ P : Subgroup Rgrp, Nat.card P = 49 →
      ∃ s ∈ P, s ≠ 1 ∧ ¬ 9 ∣ Nat.card (Subgroup.centralizer ({s} : Set Rgrp)) := by
  intro P hP
  haveI : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  haveI : Finite Rgrp := rgrp_finite
  have h343 : ¬ 343 ∣ Nat.card Rgrp := by
    rw [card_stdGroup]
    norm_num
  have hP7 : IsPGroup 7 P := IsPGroup.of_card (n := 2) (by rw [hP]; norm_num)
  have hnot : ¬ 7 ∣ P.index := by
    intro h7
    apply h343
    rw [← P.index_mul_card, hP]
    obtain ⟨k, hk⟩ := h7
    exact ⟨k, by rw [hk]; ring⟩
  let Psyl : Sylow 7 Rgrp := hP7.toSylow hnot
  have hPsyl : (Psyl : Subgroup Rgrp) = P := rfl
  have hzpow7 : IsPGroup 7 (Subgroup.zpowers rep7B) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, orderOf_rep7B]; norm_num)
  obtain ⟨S, hS⟩ := hzpow7.exists_le_sylow
  haveI : Finite (Sylow 7 Rgrp) :=
    Finite.of_injective (fun S : Sylow 7 Rgrp => (S : Set Rgrp)) SetLike.coe_injective
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq Rgrp S Psyl
  have hconj : IsConj rep7B (g * rep7B * g⁻¹) := by
    rw [isConj_iff]
    exact ⟨g, rfl⟩
  refine ⟨g * rep7B * g⁻¹, ?_, ?_, ?_⟩
  · have hmem : g * rep7B * g⁻¹ ∈ (Psyl : Subgroup Rgrp) := by
      rw [← hg, Sylow.coe_subgroup_smul]
      rw [Subgroup.mem_smul_pointwise_iff_exists]
      exact ⟨rep7B, hS (Subgroup.mem_zpowers rep7B),
        by rw [MulAut.smul_def, MulAut.conj_apply]⟩
    simpa only [hPsyl] using hmem
  · intro hs1
    have h1 : IsConj rep7B 1 := by rw [← hs1]; exact hconj
    have hord : orderOf rep7B = 7 := orderOf_rep7B
    rw [isConj_one_left.mp h1, orderOf_one] at hord
    norm_num at hord
  · have hcard : Nat.card (Subgroup.centralizer ({g * rep7B * g⁻¹} : Set Rgrp)) = 1176 := by
      rw [CFSG.Monster.Existence.natCard_centralizer_eq_of_isConj hconj.symm,
        card_centralizer_rep7B]
    rw [hcard]
    norm_num

end CFSG.StandardType.SporadicShape
