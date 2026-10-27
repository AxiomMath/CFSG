module

public import CFSG.Monster.B.TwoA.Sp8.P0Rank
public import CFSG.Monster.B.TwoA.Sp8.TwoRankTransport

public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.B.TwoA.Sp8.WordRel

open CFSG.Monster.Code CFSG.Monster.B CFSG.Monster.B.TwoA CFSG.Open


theorem card_le_of_isElemAbelian_Cbar :
    ∀ E : Subgroup Cbar, IsElemAbelian 2 E → Nat.card E ≤ 2 ^ 14 := by
  intro E hE
  let E' : Subgroup Dfull := E.map iotaD
  have hE'card : Nat.card E' = Nat.card E :=
    Subgroup.card_map_of_injective (K := E) (f := iotaD) iotaD_injective
  have hE'ab : IsElemAbelian 2 E' := IsElemAbelian.map hE iotaD
  have hE'p : IsPGroup 2 E' := hE'ab.isPGroup
  obtain ⟨-, -, -, -, -, -, -, ⟨m, hm_odd, hm_eq⟩, -⟩ :=
    full_short_centralizer_odd_index
  have hm0 : m ≠ 0 := hm_odd.pos.ne'
  have hm2 : m.factorization 2 = 0 :=
    Nat.factorization_eq_zero_of_not_dvd hm_odd.not_two_dvd_nat
  have hDfac : (Nat.card Dfull).factorization 2 = 41 := by
    rw [hm_eq, Nat.factorization_mul (by norm_num) hm0, Finsupp.add_apply,
      Nat.factorization_pow_self Nat.prime_two, hm2, add_zero]
  have hXeq : Nat.card Xgrp = 2 ^ 41 * 722925 := by
    rw [natCard_Xgrp]
    norm_num
  have hXfac : (Nat.card Xgrp).factorization 2 = 41 := by
    rw [hXeq, Nat.factorization_mul (by norm_num) (by norm_num), Finsupp.add_apply,
      Nat.factorization_pow_self Nat.prime_two,
      Nat.factorization_eq_zero_of_not_dvd (by norm_num : ¬ 2 ∣ 722925), add_zero]
  have hA8X : A8 ≤ Xgrp :=
    (A8_le_Lgrp).trans ((Lgrp_le_PLam lam0).trans inf_le_left)
  let N : Subgroup Xgrp := A8.subgroupOf Xgrp
  have hNcard : Nat.card N = 2 ^ 8 :=
    (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hA8X).toEquiv).trans natCard_A8
  have hNp : IsPGroup 2 N := IsPGroup.of_card hNcard
  obtain ⟨Q, hNQ⟩ := hNp.exists_le_sylow
  let Qd : Subgroup Dfull := (Q : Subgroup Xgrp).map Xgrp.subtype
  have hQcard : Nat.card (Q : Subgroup Xgrp) = 2 ^ 41 := by
    rw [Sylow.card_eq_multiplicity, hXfac]
  have hQdcard : Nat.card Qd = 2 ^ 41 :=
    (Subgroup.card_map_of_injective (K := (Q : Subgroup Xgrp)) (f := Xgrp.subtype)
      Xgrp.subtype_injective).trans hQcard
  have hQdX : Qd ≤ Xgrp := Subgroup.map_subtype_le (Q : Subgroup Xgrp)
  let P : Sylow 2 Dfull := Sylow.ofCard Qd (by rw [hQdcard, hDfac])
  have hPcoe : (P : Subgroup Dfull) = Qd := rfl
  have hA8Qd : A8 ≤ Qd := by
    intro a ha
    have haN : (⟨a, hA8X ha⟩ : Xgrp) ∈ N := Subgroup.mem_subgroupOf.2 ha
    exact Subgroup.mem_map_of_mem Xgrp.subtype (hNQ haN)
  obtain ⟨R, hE'R⟩ := hE'p.exists_le_sylow
  obtain ⟨h, hh⟩ := MulAction.exists_smul_eq Dfull R P
  let E'' : Subgroup Dfull := E'.map (MulAut.conj h).toMonoidHom
  have hE''Qd : E'' ≤ Qd := by
    rw [← hPcoe]
    rintro _ ⟨y, hy, rfl⟩
    rw [← hh, Sylow.coe_subgroup_smul]
    exact Subgroup.smul_mem_pointwise_smul y (MulAut.conj h) _ (hE'R hy)
  have hE''card : Nat.card E'' = Nat.card E' :=
    Subgroup.card_map_of_injective (K := E') (f := (MulAut.conj h).toMonoidHom)
      (MulAut.conj h).injective
  have hE''ab : IsElemAbelian 2 E'' := IsElemAbelian.map hE'ab _
  have hbound : Nat.card E'' ≤ 2 ^ 14 :=
    card_le_of_le_Xgrp hQdX hA8Qd lam0_isotropic finrank_lam0 card_le_of_le_P0
      E'' hE''Qd hE''ab
  calc Nat.card E = Nat.card E' := hE'card.symm
    _ = Nat.card E'' := hE''card.symm
    _ ≤ 2 ^ 14 := hbound

end CFSG.Monster.B.TwoA.Sp8.WordRel
