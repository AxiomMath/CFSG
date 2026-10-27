module

public import CFSG.Sporadic.SuzOddCore.CTICheck
public import CFSG.Sporadic.SuzOddCore.ThreeLocalC
public import CFSG.Sporadic.SuzOddCore.CompQuot

public noncomputable section

namespace CFSG.Sporadic.SuzOddCore

open CFSG CFSG.LocalCores CFSG.Certificates CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native
  CFSG.PSL3Four.Native CFSG.ComponentClassification.PSL3Four

theorem hm1 : (fixList 1).length = 54 := cti_fix1


@[expose] def rho1 : invE 1 →* Equiv.Perm (Fin 54) := rho1Of hm1

@[expose] def kperm1 (k : ℕ) : Equiv.Perm (Fin 54) := kperm1Of hm1 k

theorem kperm1_mem (k : ℕ) : kperm1 k ∈ rho1.range := ⟨_, rfl⟩

theorem tabRep_kperm1 {k : ℕ} (hk : k < 10) : TabRep (kGens 1)[k]! (kperm1 k) :=
  tabRep_kperm1Of hm1 hk

theorem range_rho1_eq : rho1.range = Subgroup.closure {g | ∃ k < 10, kperm1 k = g} := by
  rw [rho1, rho1Of, range_cRho]
  apply congrArg Subgroup.closure
  ext g
  simp only [kGenSet, Set.mem_ofPred_eq, kperm1, kperm1Of, rho1Of, invInnerGenArrs_size1]

theorem card_range_rho1 : Nat.card rho1.range = 1658880 := card_range_rho1Of hm1

theorem card_ker_rho1 : Nat.card rho1.ker = 2 := by
  have h := card_ker_cRho (i := 1) (by norm_num) hm1
  rw [show cRho (i := 1) (by norm_num) hm1 = rho1 from rfl, card_range_rho1] at h
  simp only [invInnerOrders, List.getD_cons_succ, List.getD_cons_zero] at h
  exact Nat.eq_of_mul_eq_mul_right (by norm_num : 0 < 1658880) (h.trans (by norm_num))

theorem tabRep_kperm1_inv {k : ℕ} (hk : k < 10) : TabRep (kInvs 1)[k]! (kperm1 k)⁻¹ :=
  tabRep_kperm1Of_inv hm1 hk

@[expose] def qperm (j : ℕ) : Equiv.Perm (Fin 54) := qpermOf hm1 j

theorem tabRep_qperm {j : ℕ} (hj : j < 6) : TabRep qGens[j]! (qperm j) := tabRep_qpermOf hm1 hj

@[expose] def suzQbar : Subgroup (Equiv.Perm (Fin 54)) := suzQbarOf hm1

theorem card_qbar : Nat.card suzQbar = 64 := card_suzQbarOf hm1

theorem qperm_mem_range (j : ℕ) : qperm j ∈ rho1.range :=
  rho1.range.list_prod_mem fun x hx => by
    obtain ⟨k, -, rfl⟩ := List.mem_map.1 hx
    exact kperm1_mem k

theorem qbar_le : suzQbar ≤ rho1.range := by
  rw [suzQbar, suzQbarOf, Subgroup.closure_le]
  rintro _ ⟨j, -, rfl⟩
  exact qperm_mem_range j

theorem conj_mem_qbar {k : ℕ} (hk : k < 10) {x : Equiv.Perm (Fin 54)} (hx : x ∈ suzQbar) :
    kperm1 k * x * (kperm1 k)⁻¹ ∈ suzQbar :=
  conj_mem_suzQbarOf hm1 hk hx

theorem range_le_normalizer : rho1.range ≤ Subgroup.normalizer (suzQbar : Set _) := by
  rw [range_rho1_eq, Subgroup.closure_le]
  rintro _ ⟨k, hk, rfl⟩
  exact mem_normalizer_of_conj_mem fun x hx => conj_mem_qbar hk hx

theorem qperm_comm {i j : ℕ} (hi : i < 6) (hj : j < 6) : qperm i * qperm j = qperm j * qperm i :=
  qpermOf_comm hm1 hi hj

theorem qbar_le_centralizer :
    suzQbar ≤ Subgroup.centralizer (suzQbar : Set (Equiv.Perm (Fin 54))) := by
  rw [suzQbar, suzQbarOf, Subgroup.centralizer_closure, Subgroup.closure_le]
  rintro _ ⟨i, hi, rfl⟩
  rw [SetLike.mem_coe, Subgroup.mem_centralizer_iff]
  rintro _ ⟨j, hj, rfl⟩
  exact qperm_comm hj hi

theorem centralizer_qbar {y : Equiv.Perm (Fin 54)} (hy : y ∈ rho1.range)
    (hc : ∀ j < 6, y * qperm j = qperm j * y) : y ∈ suzQbar :=
  mem_suzQbarOf_of_comm hm1 hy hc

@[expose] def suzQ128 : Subgroup (invE 1) := suzQbar.comap rho1

theorem suzQ128_normal : suzQ128.Normal := by
  constructor
  intro n hn g
  rw [suzQ128, Subgroup.mem_comap] at hn ⊢
  rw [map_mul, map_mul, map_inv]
  exact (Subgroup.mem_normalizer_iff.1 (range_le_normalizer ⟨g, rfl⟩) _).1 hn

theorem ker_le_suzQ128 : rho1.ker ≤ suzQ128 := by
  intro x hx
  rw [suzQ128, Subgroup.mem_comap, MonoidHom.mem_ker.1 hx]
  exact suzQbar.one_mem

theorem suzQ128_map : suzQ128.map rho1 = suzQbar := by
  rw [suzQ128, Subgroup.map_comap_eq, inf_eq_right.2 qbar_le]

theorem card_suzQ128 : Nat.card suzQ128 = 128 := by
  rw [card_eq_map_mul_ker rho1 suzQ128, suzQ128_map, card_qbar,
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe ker_le_suzQ128).toEquiv, card_ker_rho1]

theorem centralizer_suzQ128 : Subgroup.centralizer (suzQ128 : Set (invE 1)) ≤ suzQ128 := by
  intro x hx
  rw [suzQ128, Subgroup.mem_comap]
  refine centralizer_qbar ⟨x, rfl⟩ fun j hj => ?_
  have hq : qperm j ∈ suzQbar := Subgroup.subset_closure ⟨j, hj, rfl⟩
  obtain ⟨q, hq', hqj⟩ := (suzQ128_map ▸ hq : qperm j ∈ suzQ128.map rho1)
  rw [← hqj, ← map_mul, ← map_mul]
  congr 1
  exact ((Subgroup.mem_centralizer_iff.1 hx) q hq').symm

theorem suzQ128_pgroup : IsPGroup 2 suzQ128 :=
  IsPGroup.of_card (n := 7) (by rw [card_suzQ128]; norm_num)

theorem CTI_Suz_second_involution_centralizer_has_no_components :
    (∃ Q : Subgroup (invE 1), Q.Normal ∧ Nat.card Q = 128 ∧
      Subgroup.centralizer (Q : Set (invE 1)) ≤ Q) ∧
    ∀ B : Subgroup (invE 1), ¬ IsComponent B := by
  refine ⟨⟨suzQ128, suzQ128_normal, card_suzQ128, centralizer_suzQ128⟩, fun B hB => ?_⟩
  have hBQ : B ≤ suzQ128 := by
    rcases component_normal_subgroup hB suzQ128_normal with h | h
    · exact h
    · refine le_trans ?_ centralizer_suzQ128
      exact Subgroup.commutator_eq_bot_iff_le_centralizer.1 h
  exact not_isComponent_of_le_pgroup suzQ128_pgroup hBQ hB

end CFSG.Sporadic.SuzOddCore
