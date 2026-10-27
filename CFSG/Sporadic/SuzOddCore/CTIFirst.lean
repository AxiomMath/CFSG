module

public import CFSG.Sporadic.SuzOddCore.CTICheck
public import Certificates.Certificate2291

public noncomputable section

namespace CFSG.Sporadic.SuzOddCore

open CFSG CFSG.Certificates CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.PSL3Four.Native
  CFSG.ComponentClassification.PSL3Four
open scoped commutatorElement

theorem hm0 : (fixList 0).length = 42 := cti_fix0

@[expose] def rho0 : invE 0 →* Equiv.Perm (Fin 42) := cRho (i := 0) (by norm_num) hm0

theorem rho0_enumerates : Enumerates rho0.range (enumOf 42 (kGens 0) 40320).tabs.toList :=
  enumerates_rho0Of hm0

theorem card_range_rho0 : Nat.card rho0.range = 40320 :=
  card_range_rho0Of hm0

theorem card_ker_rho0 : Nat.card rho0.ker = 4 := by
  have h := card_ker_cRho (i := 0) (by norm_num) hm0
  rw [show cRho (i := 0) (by norm_num) hm0 = rho0 from rfl, card_range_rho0] at h
  simp only [invInnerOrders, List.getD_cons_zero] at h
  exact Nat.eq_of_mul_eq_mul_right (by norm_num : 0 < 40320) (h.trans (by norm_num))

@[expose] def kperm (k : ℕ) : Equiv.Perm (Fin 42) := rho0 (innerGenE (i := 0) (by norm_num) k)

theorem kperm_mem (k : ℕ) : kperm k ∈ rho0.range := ⟨_, rfl⟩

theorem tabRep_kperm {k : ℕ} (hk : k < 22) : TabRep (kGens 0)[k]! (kperm k) :=
  tabRep_kpermOf hm0 hk

theorem tabRep_kperm_inv {k : ℕ} (hk : k < 22) : TabRep (kInvs 0)[k]! (kperm k)⁻¹ :=
  tabRep_kpermOf_inv hm0 hk

@[expose] def dperm (j : ℕ) : Equiv.Perm (Fin 42) := ⁅kperm 1, kperm (j + 2)⁆

theorem tabRep_dperm {j : ℕ} (hj : j < 5) : TabRep dGens[j]! (dperm j) :=
  tabRep_dpermOf hm0 hj

@[expose] def dGenSet : Set (Equiv.Perm (Fin 42)) := {g | ∃ j < 5, dperm j = g}

@[expose] def suzD : Subgroup (Equiv.Perm (Fin 42)) := Subgroup.closure dGenSet

theorem d_hA : ∀ a ∈ dGenSet, ∃ j < dGens.size, TabRep dGens[j]! a := by
  rintro _ ⟨j, hj, rfl⟩
  exact ⟨j, by rw [dGens_size]; exact hj, tabRep_dperm hj⟩

theorem d_hgens : ∀ j < dGens.size, ∃ a ∈ dGenSet, TabRep dGens[j]! a := by
  intro j hj
  rw [dGens_size] at hj
  exact ⟨_, ⟨j, hj, rfl⟩, tabRep_dperm hj⟩

theorem card_suzD : Nat.card suzD = 20160 :=
  card_suzDOf hm0

theorem suzD_enumerates : Enumerates suzD (enumOf 42 dGens 20160).tabs.toList :=
  enumerates_suzDOf hm0

theorem suzD_le : suzD ≤ rho0.range := by
  rw [suzD, Subgroup.closure_le]
  rintro _ ⟨j, -, rfl⟩
  rw [SetLike.mem_coe, dperm, commutatorElement_def]
  have h1 := kperm_mem 1
  have h2 := kperm_mem (j + 2)
  exact rho0.range.mul_mem (rho0.range.mul_mem (rho0.range.mul_mem h1 h2)
    (rho0.range.inv_mem h1)) (rho0.range.inv_mem h2)

theorem conj_mem_suzD {k : ℕ} (hk : k < 22) {x : Equiv.Perm (Fin 42)} (hx : x ∈ suzD) :
    kperm k * x * (kperm k)⁻¹ ∈ suzD ∧ (kperm k)⁻¹ * x * kperm k ∈ suzD :=
  conj_mem_suzDOf hm0 hk hx

theorem range_rho0_eq : rho0.range = Subgroup.closure {g | ∃ k < 22, kperm k = g} := by
  rw [rho0, range_cRho]
  apply congrArg Subgroup.closure
  ext g
  simp only [kGenSet, Set.mem_ofPred_eq, kperm, rho0, invInnerGenArrs_size0]

theorem suzD_normal : (suzD.subgroupOf rho0.range).Normal := by
  rw [Subgroup.normal_subgroupOf_iff_le_normalizer suzD_le, range_rho0_eq, Subgroup.closure_le]
  rintro _ ⟨k, hk, rfl⟩
  exact mem_normalizer_of_conj_mem fun x hx => (conj_mem_suzD hk hx).1

theorem suzD_index : (suzD.subgroupOf rho0.range).index = 2 := by
  have h := (suzD.subgroupOf rho0.range).card_mul_index
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe suzD_le).toEquiv, card_suzD,
    card_range_rho0] at h
  omega

@[expose] def repPerm (l : ℕ) : Equiv.Perm (Fin 42) := ((classWords.getD l []).map dperm).prod

theorem tabRep_repPerm (l : ℕ) : TabRep (classRep l) (repPerm l) :=
  tabRep_repPermOf hm0 l

theorem repPerm_mem (l : ℕ) : repPerm l ∈ suzD := by
  refine suzD.list_prod_mem fun x hx => ?_
  obtain ⟨j, hj, rfl⟩ := List.mem_map.1 hx
  have := classWords_lt l j hj
  rw [dGens_size] at this
  exact Subgroup.subset_closure ⟨j, this, rfl⟩

theorem repPerm_zero : repPerm 0 = 1 := by
  simp [repPerm, classWords]

@[expose] def classFun (l : Fin 10) : ConjClasses suzD :=
  ConjClasses.mk ⟨repPerm l, repPerm_mem l⟩

theorem classFun_injective : Function.Injective classFun :=
  classFunOf_injective hm0

theorem classFun_surjective : Function.Surjective classFun :=
  classFunOf_surjective hm0

@[expose] def classEquiv : Fin 10 ≃ ConjClasses suzD :=
  Equiv.ofBijective classFun ⟨classFun_injective, classFun_surjective⟩

theorem card_class (l : Fin 10) :
    Nat.card (classEquiv l).carrier = classSizes.getD l 0 :=
  card_classFunOf hm0 l

theorem classEquiv_zero : classEquiv 0 = ConjClasses.mk 1 := by
  change classFun 0 = ConjClasses.mk 1
  rw [classFun]
  congr 1

theorem classSizes_sums : ∀ U : Finset (Fin 10), 0 ∈ U →
    (∑ l ∈ U, classSizes.getD l 0) ∣ 20160 → U = {0} ∨ U = Finset.univ :=
  Certificates.certificate2291

theorem suzD_simple : IsSimpleGroup suzD :=
  isSimpleGroup_of_classes classEquiv (fun l => classSizes.getD l 0) card_class 0
    classEquiv_zero (by rw [card_suzD]; norm_num) (by rw [card_suzD]; exact classSizes_sums)

theorem suzD_noncomm : ∃ a b : suzD, a * b ≠ b * a :=
  exists_mul_ne_of_class (classEquiv 1) (by rw [card_class]; decide)

theorem CTI_Suz_first_involution_local_component_simple_quotient_order
    (B : Subgroup (invE 0)) (hB : IsComponent B) :
    Nat.card (B ⧸ Subgroup.center B) = 20160 := by
  set ρ' : invE 0 →* rho0.range := rho0.rangeRestrict
  have hsurj : Function.Surjective ρ' := MonoidHom.rangeRestrict_surjective rho0
  have hker : Group.IsSolvable ρ'.ker := by
    rw [MonoidHom.ker_rangeRestrict]
    have hp : IsPGroup 2 rho0.ker := IsPGroup.of_card (n := 2) (by rw [card_ker_rho0]; norm_num)
    have : Group.IsNilpotent rho0.ker := hp.isNilpotent
    infer_instance
  have e : suzD.subgroupOf rho0.range ≃* suzD := Subgroup.subgroupOfEquivOfLe suzD_le
  have hs : IsSimpleGroup (suzD.subgroupOf rho0.range) := by
    have := suzD_simple
    exact e.isSimpleGroup
  have hnc : ∃ a b : suzD.subgroupOf rho0.range, a * b ≠ b * a := by
    obtain ⟨a, b, hab⟩ := suzD_noncomm
    refine ⟨e.symm a, e.symm b, fun h => hab ?_⟩
    have := congrArg e h
    simpa using this
  rw [card_quotient_center_of_component ρ' hsurj hker _ suzD_index hs hnc hB,
    Nat.card_congr e.toEquiv, card_suzD]

end CFSG.Sporadic.SuzOddCore
