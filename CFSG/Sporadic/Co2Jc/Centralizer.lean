module

public import CFSG.Sporadic.Co2Smith.QNormal
public import CFSG.Sporadic.Co2Schreier.OddCore
public import CFSG.Sporadic.Co2Schreier.FullAut
public import CFSG.Monster.GMS.Transport

public section

namespace CFSG.Sporadic.Co2Jc

open CFSG.Sporadic.Co2Smith CFSG.Sporadic.Co2Cert CFSG.Sporadic.Co2Schreier

attribute [local irreducible] Matrix.instHMulOfFintypeOfMulOfAddCommMonoid

private theorem permEquiv_z0_mul_self :
    co2PermEquiv z0 * co2PermEquiv z0 = 1 := by
  rw [← map_mul, seedA_mul_self, map_one]

private theorem permEquiv_z0_ne_one :
    co2PermEquiv z0 ≠ 1 := by
  intro h
  exact z0_ne_one (co2PermEquiv.injective (by rw [h, map_one]))

private theorem card_centralizer_permEquiv_z0 :
    Nat.card (Subgroup.centralizer ({co2PermEquiv z0} : Set co2P)) = 743178240 :=
  calc Nat.card (Subgroup.centralizer ({co2PermEquiv z0} : Set co2P))
      = Nat.card (Subgroup.centralizer ({z0} : Set K)) :=
        (Nat.card_congr (CFSG.Monster.GMS.centralizerMulEquiv co2PermEquiv z0).toEquiv).symm
    _ = 743178240 := natCard_centralizer_z0

private theorem card_centralizer_tP :
    Nat.card (Subgroup.centralizer ({tP} : Set co2P)) = 41287680 :=
  calc Nat.card (Subgroup.centralizer ({tP} : Set co2P))
      = Nat.card (locD.subgroupOf co2P) := by rw [locD_subgroupOf_eq]
    _ = Nat.card locD := Nat.card_congr (Subgroup.subgroupOfEquivOfLe locD_le_P).toEquiv
    _ = 41287680 := card_locD

private theorem card_centralizer_uP :
    Nat.card (Subgroup.centralizer ({uP} : Set co2P)) = 1474560 :=
  calc Nat.card (Subgroup.centralizer ({uP} : Set co2P))
      = Nat.card (locH3.subgroupOf co2P) := by rw [centralizer_uP]
    _ = Nat.card locH3 :=
        Nat.card_congr (Subgroup.subgroupOfEquivOfLe (inf_le_left : locH3 ≤ co2P)).toEquiv
    _ = 1474560 := card_locH3

private theorem isConj_permEquiv_z0_zP :
    IsConj (co2PermEquiv z0) zP := by
  rcases invol_cases (co2PermEquiv z0) permEquiv_z0_mul_self permEquiv_z0_ne_one with
    h | h | h
  · exact h
  · exfalso
    obtain ⟨c, hc⟩ := isConj_iff.1 h
    have hcard : Nat.card (Subgroup.centralizer ({co2PermEquiv z0} : Set co2P)) =
        Nat.card (Subgroup.centralizer ({tP} : Set co2P)) :=
      Nat.card_congr (centralizerConj c (co2PermEquiv z0) tP hc).toEquiv
    rw [card_centralizer_permEquiv_z0, card_centralizer_tP] at hcard
    exact absurd hcard (by norm_num)
  · exfalso
    obtain ⟨c, hc⟩ := isConj_iff.1 h
    have hcard : Nat.card (Subgroup.centralizer ({co2PermEquiv z0} : Set co2P)) =
        Nat.card (Subgroup.centralizer ({uP} : Set co2P)) :=
      Nat.card_congr (centralizerConj c (co2PermEquiv z0) uP hc).toEquiv
    rw [card_centralizer_permEquiv_z0, card_centralizer_uP] at hcard
    exact absurd hcard (by norm_num)

private theorem exists_conj_permEquiv_z0_zP :
    ∃ c : co2P, c * co2PermEquiv z0 * c⁻¹ = zP :=
  isConj_iff.1 isConj_permEquiv_z0_zP

private noncomputable def czEquivLocC
    (c : co2P)
    (hc : c * co2PermEquiv z0 * c⁻¹ = zP) :
    ↥(Subgroup.centralizer ({z0} : Set K)) ≃* locC :=
  (CFSG.Monster.GMS.centralizerMulEquiv co2PermEquiv z0).trans
    ((centralizerConj c (co2PermEquiv z0) zP hc).trans
      ((MulEquiv.subgroupCongr locC_subgroupOf_eq.symm).trans
        (Subgroup.subgroupOfEquivOfLe locC_le_P)))

theorem commutator_Cz_eq_top :
    commutator ↥(Subgroup.centralizer ({z0} : Set K)) = ⊤ := by
  obtain ⟨c, hc⟩ := exists_conj_permEquiv_z0_zP
  haveI : Group.IsPerfect locC := locC_perfect_and_inner.1
  have hperf : Group.IsPerfect ↥(Subgroup.centralizer ({z0} : Set K)) :=
    Group.IsPerfect.ofSurjective (f := (czEquivLocC c hc).symm.toMonoidHom)
      (czEquivLocC c hc).symm.surjective
  exact hperf.commutator_eq_top

theorem exists_eq_conj_Cz
    (α : MulAut ↥(Subgroup.centralizer ({z0} : Set K))) :
    ∃ g, α = MulAut.conj g := by
  obtain ⟨c, hc⟩ := exists_conj_permEquiv_z0_zP
  exact forall_inner_of_mulEquiv (czEquivLocC c hc) locC_perfect_and_inner.2 α

end CFSG.Sporadic.Co2Jc
