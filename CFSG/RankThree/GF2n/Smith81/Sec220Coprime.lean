module

public import CFSG.GroupTheory.SolvableHallNodes
public import Mathlib.GroupTheory.Nilpotent
public import Mathlib.Tactic.ContinuousFunctionalCalculus
public import Mathlib.Tactic.Positivity.Finset

public section

namespace CFSG.RankThree.GF2n.Smith81

open scoped commutatorElement Pointwise

variable {G : Type*} [Group G]

theorem eq_one_of_mem_of_orderOf_dvd_odd {P : Subgroup G} (hP : IsPGroup 2 P) {x : G}
    (hx : x ∈ P) {m : ℕ} (hm : Odd m) (hdvd : orderOf x ∣ m) : x = 1 := by
  obtain ⟨k, hk⟩ := hP ⟨x, hx⟩
  have h1 : orderOf x ∣ 2 ^ k := by
    apply orderOf_dvd_of_pow_eq_one
    have := congrArg Subtype.val hk
    simpa using this
  have h2 : Nat.Coprime (orderOf x) (2 ^ k) :=
    Nat.Coprime.pow_right k ((Nat.coprime_two_right.mpr (hm.of_dvd_nat hdvd)))
  exact orderOf_eq_one_iff.mp (Nat.Coprime.eq_one_of_dvd h2 h1)

theorem exists_mem_centralizer_conj_of_fixed [Finite G] {Q : Subgroup G} (hQ : IsPGroup 2 Q)
    {v : G} (hvQ : v ∈ Subgroup.normalizer (Q : Set G)) (hv : Odd (orderOf v)) {t s q : G}
    (hvt : v * t = t * v) (hvs : v * s = s * v) (hq : q ∈ Q) (hs : s = q * t * q⁻¹) :
    ∃ r ∈ Q ⊓ Subgroup.centralizer ({v} : Set G), s = r * t * r⁻¹ := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set A : Subgroup G := Subgroup.zpowers v with hA
  set u : G := q⁻¹ * v * q with hu
  set B : Subgroup G := Subgroup.zpowers u with hB
  set Ct : Subgroup G := Subgroup.centralizer ({t} : Set G) with hCt
  set T : Subgroup G := (Q ⊔ A) ⊓ Ct with hT
  set S : Subgroup G := Q ⊓ Ct with hS
  have hqn : q ∈ Subgroup.normalizer (Q : Set G) := Subgroup.le_normalizer hq
  have hAn : A ≤ Subgroup.normalizer (Q : Set G) := Subgroup.zpowers_le.mpr hvQ
  have hun : u ∈ Subgroup.normalizer (Q : Set G) := mul_mem (mul_mem (inv_mem hqn) hvQ) hqn
  have hBn : B ≤ Subgroup.normalizer (Q : Set G) := Subgroup.zpowers_le.mpr hun
  have hvC : v ∈ Ct := Subgroup.mem_centralizer_singleton_iff.mpr hvt
  have huC : u ∈ Ct := by
    refine Subgroup.mem_centralizer_singleton_iff.mpr ?_
    have h1 : q * t = s * q := by rw [hs]; group
    have h1' : t * q⁻¹ = q⁻¹ * s := by rw [hs]; group
    calc u * t = q⁻¹ * v * (q * t) := by rw [hu]; group
      _ = q⁻¹ * v * (s * q) := by rw [h1]
      _ = q⁻¹ * (v * s) * q := by group
      _ = q⁻¹ * (s * v) * q := by rw [hvs]
      _ = (q⁻¹ * s) * v * q := by group
      _ = (t * q⁻¹) * v * q := by rw [h1']
      _ = t * u := by rw [hu]; group
  have hQAT : Q ⊔ A ≤ Subgroup.normalizer (Q : Set G) := sup_le Subgroup.le_normalizer hAn
  have hAT : A ≤ T := le_inf le_sup_right (Subgroup.zpowers_le.mpr hvC)
  have huQA : u ∈ Q ⊔ A :=
    mul_mem (mul_mem (Subgroup.mem_sup_left (inv_mem hq))
      (Subgroup.mem_sup_right (Subgroup.mem_zpowers v))) (Subgroup.mem_sup_left hq)
  have hBT : B ≤ T := le_inf (Subgroup.zpowers_le.mpr huQA) (Subgroup.zpowers_le.mpr huC)
  have hST : S ≤ T := inf_le_inf_right Ct le_sup_left
  have hQB : Q ⊔ B = Q ⊔ A := by
    refine le_antisymm (sup_le le_sup_left (hBT.trans inf_le_left)) (sup_le le_sup_left ?_)
    refine Subgroup.zpowers_le.mpr ?_
    have : v = q * u * q⁻¹ := by rw [hu]; group
    rw [this]
    exact mul_mem (mul_mem (Subgroup.mem_sup_left hq)
      (Subgroup.mem_sup_right (Subgroup.mem_zpowers u))) (Subgroup.mem_sup_left (inv_mem hq))
  have hTS : T ≤ Subgroup.normalizer (S : Set G) := fun x hx =>
    Subgroup.inf_normalizer_le_normalizer_inf ⟨hQAT hx.1, Subgroup.le_normalizer hx.2⟩
  haveI hNn : (S.subgroupOf T).Normal := Subgroup.normal_subgroupOf_of_le_normalizer hTS
  have hodd_u : orderOf u ∣ orderOf v := by
    apply orderOf_dvd_of_pow_eq_one
    have h := map_pow (MulAut.conj q⁻¹) v (orderOf v)
    rw [pow_orderOf_eq_one, map_one] at h
    simpa [MulAut.conj_apply, hu] using h.symm
  have hQA : ∀ x ∈ Q, x ∈ A → x = 1 := fun x hxQ hxA =>
    eq_one_of_mem_of_orderOf_dvd_odd hQ hxQ hv (orderOf_dvd_of_mem_zpowers hxA)
  have hQB' : ∀ x ∈ Q, x ∈ B → x = 1 := fun x hxQ hxB =>
    eq_one_of_mem_of_orderOf_dvd_odd hQ hxQ hv
      ((orderOf_dvd_of_mem_zpowers hxB).trans hodd_u)
  set N : Subgroup T := S.subgroupOf T with hN
  set H : Subgroup T := A.subgroupOf T with hH
  set K : Subgroup T := B.subgroupOf T with hK
  have hprod : ∀ A' : Subgroup G, A' ≤ Subgroup.normalizer (Q : Set G) → A' ≤ T →
      Q ⊔ A' = Q ⊔ A → (N : Set T) * (A'.subgroupOf T : Set T) = Set.univ := by
    intro A' hA'n hA'T hQA'
    refine Set.eq_univ_of_forall fun x => ?_
    have hx : (x : G) ∈ ((Q ⊔ A' : Subgroup G) : Set G) := by
      rw [hQA']; exact x.2.1
    rw [Subgroup.coe_mul_of_right_le_normalizer_left Q A' hA'n] at hx
    obtain ⟨r, hr, a, ha, hra⟩ := hx
    have haT : a ∈ T := hA'T ha
    have hrT : r ∈ T := by
      have : r = (x : G) * a⁻¹ := by rw [← hra]; group
      rw [this]
      exact T.mul_mem x.2 (T.inv_mem haT)
    exact Set.mem_mul.mpr ⟨⟨r, hrT⟩, (show r ∈ S from ⟨hr, hrT.2⟩), ⟨a, haT⟩,
      (show a ∈ A' from ha), Subtype.ext hra⟩
  have hNH : (N : Set T) * (H : Set T) = Set.univ := hprod A hAn hAT rfl
  have hNK : (N : Set T) * (K : Set T) = Set.univ := hprod B hBn hBT hQB
  have hdisj : ∀ A' : Subgroup G, (∀ x ∈ Q, x ∈ A' → x = 1) → N ⊓ A'.subgroupOf T = ⊥ := by
    intro A' hA'
    refine (Subgroup.eq_bot_iff_forall _).mpr fun x hx => ?_
    have h1 : (x : G) ∈ S := hx.1
    have h2 : (x : G) ∈ A' := hx.2
    exact Subtype.ext (hA' _ h1.1 h2)
  have hNH' : N ⊓ H = ⊥ := hdisj A hQA
  have hNK' : N ⊓ K = ⊥ := hdisj B hQB'
  have hNp : IsPGroup 2 N := (hQ.to_le (inf_le_left : S ≤ Q)).comap_subtype
  have hHc : Subgroup.IsComplement' N H :=
    Subgroup.isComplement'_of_disjoint_and_mul_eq_univ (disjoint_iff.mpr hNH') hNH
  have hcardH : Nat.card H = orderOf v := by
    rw [hH, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAT).toEquiv, hA, Nat.card_zpowers]
  have hindex : N.index = orderOf v := by
    rw [← hcardH]
    exact hHc.symm.index_eq_card
  have hcop : Nat.Coprime (Nat.card N) N.index := by
    obtain ⟨k, hk⟩ := (IsPGroup.iff_card (p := 2)).mp hNp
    rw [hk, hindex]
    exact Nat.Coprime.pow_left k (Nat.coprime_two_left.mpr hv)
  haveI : Group.IsNilpotent N := hNp.isNilpotent
  obtain ⟨n, hn, hnK⟩ := CFSG.SolvableHall.solvable_normal_hall_complement_conjugacy N
    inferInstance hcop hNH hNK hNH' hNK'
  have huK : (⟨u, hBT (Subgroup.mem_zpowers u)⟩ : T) ∈ K := Subgroup.mem_zpowers u
  rw [hnK] at huK
  obtain ⟨h, hh, hhu⟩ := Subgroup.mem_map.mp huK
  have hhA : (h : G) ∈ A := hh
  obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp hhA
  have hnS : (n : G) ∈ S := hn
  have hu_eq : u = (n : G)⁻¹ * v ^ j * (n : G) := by
    have := congrArg Subtype.val hhu
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, Subgroup.coe_mul, Subgroup.coe_inv,
      inv_inv] at this
    rw [← hj] at this
    exact this.symm
  have hvj : v ^ j = v := by
    have e1 : v⁻¹ * u ∈ Q := by
      have : v⁻¹ * u = (v⁻¹ * q⁻¹ * v⁻¹⁻¹) * q := by rw [hu]; group
      rw [this]
      refine Q.mul_mem ?_ hq
      have := (Subgroup.mem_normalizer_iff.mp (inv_mem hvQ) q⁻¹).mp (inv_mem hq)
      simpa using this
    have e2 : (v ^ j)⁻¹ * u ∈ Q := by
      have hvjn : v ^ j ∈ Subgroup.normalizer (Q : Set G) := zpow_mem hvQ j
      have : (v ^ j)⁻¹ * u = ((v ^ j)⁻¹ * (n : G)⁻¹ * (v ^ j)⁻¹⁻¹) * (n : G) := by
        rw [hu_eq]; group
      rw [this]
      refine Q.mul_mem ?_ hnS.1
      have := (Subgroup.mem_normalizer_iff.mp (inv_mem hvjn) (n : G)⁻¹).mp (Q.inv_mem hnS.1)
      simpa using this
    have e3 : (v ^ j)⁻¹ * v = 1 := by
      have hy : (v ^ j)⁻¹ * v ∈ Q := by
        have : (v ^ j)⁻¹ * v = ((v ^ j)⁻¹ * u) * (v⁻¹ * u)⁻¹ := by group
        rw [this]
        exact Q.mul_mem e2 (Q.inv_mem e1)
      exact hQA _ hy (mul_mem (inv_mem (Subgroup.zpow_mem_zpowers v j))
        (Subgroup.mem_zpowers v))
    exact inv_mul_eq_one.mp e3
  rw [hvj] at hu_eq
  have hkey : (q * (n : G)⁻¹) * v * (q * (n : G)⁻¹)⁻¹ = v := by
    calc (q * (n : G)⁻¹) * v * (q * (n : G)⁻¹)⁻¹ = q * ((n : G)⁻¹ * v * (n : G)) * q⁻¹ := by
          group
      _ = q * u * q⁻¹ := by rw [hu_eq]
      _ = v := by rw [hu]; group
  refine ⟨q * (n : G)⁻¹, ⟨Q.mul_mem hq (Q.inv_mem hnS.1), ?_⟩, ?_⟩
  · refine Subgroup.mem_centralizer_singleton_iff.mpr ?_
    calc q * (n : G)⁻¹ * v = ((q * (n : G)⁻¹) * v * (q * (n : G)⁻¹)⁻¹) * (q * (n : G)⁻¹) := by
          group
      _ = v * (q * (n : G)⁻¹) := by rw [hkey]
  · have hnt : (n : G) * t = t * (n : G) := Subgroup.mem_centralizer_singleton_iff.mp hnS.2
    calc s = q * t * q⁻¹ := hs
      _ = q * ((n : G)⁻¹ * (t * (n : G))) * q⁻¹ := by
          rw [← mul_assoc, ← hnt]; group
      _ = (q * (n : G)⁻¹) * t * (q * (n : G)⁻¹)⁻¹ := by group

end CFSG.RankThree.GF2n.Smith81
