module

public import CFSG.Sporadic.Co2Schreier.SylowMain
public import CFSG.Sporadic.Co2Schreier.Centralizers
public import CFSG.Sporadic.SchreierLemmas.LocalRestrictionSchreier

public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Sporadic.Co2Schreier

open CFSG.Certificates CFSG.Monster.B.Co2 CFSG.Sporadic.Co2Cert
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)

theorem subgroupOf_mono {H K : Subgroup (Equiv.Perm (Fin 2300))} (h : H ≤ K) :
    H.subgroupOf co2P ≤ K.subgroupOf co2P := fun _ hx =>
  Subgroup.mem_subgroupOf.2 (h (Subgroup.mem_subgroupOf.1 hx))

theorem isPGroup_subgroupOf_P {H : Subgroup (Equiv.Perm (Fin 2300))} (hH : H ≤ co2P) {n : ℕ}
    (hc : Nat.card H = 2 ^ n) : IsPGroup 2 (H.subgroupOf co2P) :=
  IsPGroup.of_card (n := n) (by rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hH).toEquiv, hc])

theorem normal_subgroupOf_subgroupOf {H K : Subgroup (Equiv.Perm (Fin 2300))}
    (h : ∀ c ∈ K, ∀ x ∈ H, c * x * c⁻¹ ∈ H) :
    ((H.subgroupOf co2P).subgroupOf (K.subgroupOf co2P)).Normal := by
  refine ⟨fun n hn g => ?_⟩
  rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf] at hn ⊢
  exact h _ (Subgroup.mem_subgroupOf.1 g.2) _ hn

theorem inf_centralizer_subgroupOf_le {H K : Subgroup (Equiv.Perm (Fin 2300))} (hHP : H ≤ co2P)
    (h : K ⊓ Subgroup.centralizer (H : Set (Equiv.Perm (Fin 2300))) ≤ H) :
    K.subgroupOf co2P ⊓ Subgroup.centralizer (H.subgroupOf co2P : Set co2P) ≤
      H.subgroupOf co2P := by
  intro x hx
  obtain ⟨hxK, hxc⟩ := Subgroup.mem_inf.1 hx
  rw [Subgroup.mem_subgroupOf] at hxK ⊢
  refine h (Subgroup.mem_inf.2 ⟨hxK, Subgroup.mem_centralizer_iff.2 fun y hy => ?_⟩)
  have := Subgroup.mem_centralizer_iff.1 hxc ⟨y, hHP hy⟩ (Subgroup.mem_subgroupOf.2 hy)
  exact congrArg Subtype.val this

theorem conj_mem_Q :
    ∀ c ∈ locC, ∀ x ∈ locQ, c * x * c⁻¹ ∈ locQ := fun _ hc _ hx =>
  enumQ_facts.conj_mem repTuple_q repTuple_c wordFacts.invC (coreOK_spec coreQ_check.1).2.1 hc hx

theorem conj_mem_R :
    ∀ c ∈ locD, ∀ x ∈ locR, c * x * c⁻¹ ∈ locR := fun _ hc _ hx =>
  enumR_facts.conj_mem repTuple_r repTuple_d wordFacts.invD (coreOK_spec coreR_check.1).2.1 hc hx

theorem centerIn_le_self (H : Subgroup (Equiv.Perm (Fin 2300))) : CFSG.centerIn H ≤ H :=
  inf_le_left

theorem locC_sup_locD_subgroupOf :
    locC.subgroupOf co2P ⊔ locD.subgroupOf co2P = ⊤ := by
  apply Subgroup.map_injective co2P.subtype_injective
  rw [Subgroup.map_sup, Subgroup.subgroupOf_map_subtype, Subgroup.subgroupOf_map_subtype,
    inf_eq_left.2 locC_le_P, inf_eq_left.2 locD_le_P, locC_sup_locD, ← MonoidHom.range_eq_map,
    Subgroup.range_subtype]

theorem zP_mem_sylow :
    zP ∈ (locSylow : Subgroup co2P) := by
  rw [coe_locSylow, Subgroup.mem_subgroupOf]
  exact locZ_mem_S

theorem tP_mem_sylow :
    tP ∈ (locSylow : Subgroup co2P) := by
  rw [coe_locSylow, Subgroup.mem_subgroupOf]
  exact locT_mem_S

theorem isPGroup_mulAut_sylow :
    IsPGroup 2 (MulAut (locSylow : Subgroup co2P)) := by
  rw [coe_locSylow]
  exact AT_Co2_Sylow_Frattini_profiles.2.2.2.1.of_equiv
    (MulAut.congr (Subgroup.subgroupOfEquivOfLe locS_le_P).symm)

instance finite_mulAut_P : Finite (MulAut co2P) :=
  Finite.of_injective (fun σ : MulAut co2P => (σ : co2P → co2P)) fun _ _ h =>
    MulEquiv.ext (congrFun h)

theorem AT_Co2_permutation_Schreier :
    Finite (Outer co2P) ∧ IsPGroup 2 (Outer co2P) ∧ Group.IsSolvable (Outer co2P) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hcrit := CFSG.Sporadic.SchreierLemmas.two_centralizer_Schreier_criterion locSylow
    zP_mem_sylow tP_mem_sylow (locC.subgroupOf co2P) locC_subgroupOf_eq
    (locD.subgroupOf co2P) locD_subgroupOf_eq (locQ.subgroupOf co2P) (locR.subgroupOf co2P)
    (isPGroup_subgroupOf_P (locQ_le_C.trans locC_le_P) (n := 9) (by rw [card_locQ]; norm_num))
    (isPGroup_subgroupOf_P (locR_le_D.trans locD_le_P) (n := 11) (by rw [card_locR]; norm_num))
    (by rw [coe_locSylow]; exact subgroupOf_mono locQ_le_S)
    (by rw [coe_locSylow]; exact subgroupOf_mono locR_le_S)
    (subgroupOf_mono locQ_le_C) (subgroupOf_mono locR_le_D)
    (normal_subgroupOf_subgroupOf conj_mem_Q) (normal_subgroupOf_subgroupOf conj_mem_R)
    (inf_centralizer_subgroupOf_le (locQ_le_C.trans locC_le_P)
      (locC_inf_centralizer_Q.trans_le (centerIn_le_self _)))
    (inf_centralizer_subgroupOf_le (locR_le_D.trans locD_le_P)
      (locD_inf_centralizer_R.trans_le (centerIn_le_self _)))
    locC_sup_locD_subgroupOf
  have hp : IsPGroup 2 (Outer co2P) := hcrit.2.2.2 isPGroup_mulAut_sylow
  have : Group.IsNilpotent (Outer co2P) := hp.isNilpotent
  exact ⟨inferInstance, hp, inferInstance⟩

end CFSG.Sporadic.Co2Schreier
