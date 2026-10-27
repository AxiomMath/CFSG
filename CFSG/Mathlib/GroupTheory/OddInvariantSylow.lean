module

public import Mathlib.GroupTheory.Solvable
public import Mathlib.GroupTheory.Sylow
import CFSG.GroupTheory.SolvableHallNodes
import CFSG.FeitThompson.OddOrderTheorem

@[expose] public section

open scoped Pointwise

namespace CFSG.OddInvariantSylow

theorem exists_isPGroup_normalizer {G : Type*} [Group G] [Finite G] {Y D : Subgroup G}
    (hY : Odd (Nat.card Y)) (hD : D ≤ Subgroup.normalizer (Y : Set G)) (hDs : IsSolvable D)
    (hD23 : ∀ p : ℕ, p.Prime → p ∣ Nat.card D → p = 2 ∨ p = 3) :
    ∃ S : Subgroup G, S ≤ Y ∧ IsPGroup 3 S ∧
      (∀ R : Subgroup G, R ≤ Y → IsPGroup 3 R → S ≤ R → R = S) ∧
      D ≤ Subgroup.normalizer (S : Set G) := by
  classical
  let H : Subgroup G := Y ⊔ D
  have hYH_le : Y ≤ H := le_sup_left
  have hDH_le : D ≤ H := le_sup_right
  let YH : Subgroup H := Y.subgroupOf H
  let DH : Subgroup H := D.subgroupOf H
  have hHnorm : H ≤ Subgroup.normalizer (Y : Set G) := sup_le Y.le_normalizer hD
  have hYHnormal : YH.Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hYH_le).mpr hHnorm
  have hYsolv : Group.IsSolvable Y := CFSG.FeitThompson.isSolvable_of_odd_natCard _ hY
  have : Group.IsSolvable Y := hYsolv
  have : Group.IsSolvable YH :=
    Group.isSolvable_of_isSolvable_injective
      (f := (Subgroup.subgroupOfEquivOfLe hYH_le).toMonoidHom)
      (Subgroup.subgroupOfEquivOfLe hYH_le).injective
  have : Group.IsSolvable D := hDs
  have : Group.IsSolvable DH :=
    Group.isSolvable_of_isSolvable_injective
      (f := (Subgroup.subgroupOfEquivOfLe hDH_le).toMonoidHom)
      (Subgroup.subgroupOfEquivOfLe hDH_le).injective
  have hYHDH_top : YH ⊔ DH = ⊤ := by
    rw [← Subgroup.subgroupOf_sup (A := Y) (A' := D) (B := H) hYH_le hDH_le]
    exact Subgroup.subgroupOf_self (H := Y ⊔ D)
  have : Group.IsSolvable (H ⧸ YH) := by
    let φ : DH →* H ⧸ YH := (QuotientGroup.mk' YH).comp DH.subtype
    have hφ : Function.Surjective φ := by
      intro x
      obtain ⟨h, rfl⟩ := QuotientGroup.mk'_surjective YH x
      have hmem : (h : H) ∈ (YH : Set H) * (DH : Set H) := by
        rw [← Subgroup.normal_mul YH DH, hYHDH_top]
        exact Subgroup.mem_top h
      obtain ⟨y, hy, d, hd, hyd⟩ := Set.mem_mul.mp hmem
      refine ⟨⟨d, hd⟩, ?_⟩
      change QuotientGroup.mk' YH (d : H) = QuotientGroup.mk' YH h
      rw [← hyd, map_mul]
      have hy1 : QuotientGroup.mk' YH y = 1 := by
        show (y : H ⧸ YH) = 1
        exact (QuotientGroup.eq_one_iff y).mpr hy
      rw [hy1, one_mul]
    exact Group.isSolvable_of_surjective (f := φ) hφ
  have hHsolv : Group.IsSolvable H := Group.isSolvable_of_subgroup_quotient YH
  let π : Set Nat.Primes := {p | p.val = 2 ∨ p.val = 3}
  have hUπ : IsPiSubgroup π DH := by
    intro p hp
    have hpD : p.val ∣ Nat.card D := by
      rwa [show Nat.card DH = Nat.card D from
        Nat.card_congr (Subgroup.subgroupOfEquivOfLe hDH_le).toEquiv] at hp
    exact hD23 p.val p.2 hpD
  obtain ⟨K, hKhall, hDK⟩ := CFSG.SolvableHall.solvable_hall_containment hHsolv π DH hUπ
  have hKindex : ¬ 3 ∣ K.index := by
    intro h3
    exact (hKhall.p_in_pi_of_p_dvd_index ⟨3, Nat.prime_three⟩ h3)
      (Or.inr rfl)
  let S_H : Subgroup H := K ⊓ YH
  have hYHcard : Nat.card YH = Nat.card Y :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hYH_le).toEquiv
  have hS3 : IsPGroup 3 S_H := by
    rw [isPGroup_iff_primeFactors_card_subset (p := 3) (by norm_num)]
    intro q hq
    rw [Nat.mem_primeFactors] at hq
    obtain ⟨hqprime, hq_dvd, -⟩ := hq
    have hq_dvd_K : q ∣ Nat.card K := hq_dvd.trans (Subgroup.card_dvd_of_le inf_le_left)
    have hqp : (⟨q, hqprime⟩ : Nat.Primes) ∈ π :=
      hKhall.p_in_pi_of_p_dvd_card ⟨q, hqprime⟩ hq_dvd_K
    have hq_dvd_YH : q ∣ Nat.card YH := hq_dvd.trans (Subgroup.card_dvd_of_le inf_le_right)
    have hqne2 : q ≠ 2 := by
      intro h2
      have h2dvd : 2 ∣ Nat.card Y := by
        rw [← hYHcard]
        exact h2 ▸ hq_dvd_YH
      have hnot2 : ¬ 2 ∣ Nat.card Y := by
        rw [← even_iff_two_dvd]
        exact (Nat.not_even_iff_odd).mpr hY
      exact hnot2 h2dvd
    have hq3 : q = 3 := by
      rcases hqp with h | h
      · exact absurd h hqne2
      · exact h
    rw [hq3, Nat.prime_three.primeFactors]
    simp
  have hsup : K ⊔ YH = ⊤ := by
    apply eq_top_iff.mpr
    calc (⊤ : Subgroup H) = YH ⊔ DH := hYHDH_top.symm
      _ ≤ YH ⊔ K := sup_le_sup le_rfl hDK
      _ = K ⊔ YH := sup_comm YH K
  have hYHrel : YH.relIndex K = YH.index := by
    rw [← Subgroup.relIndex_top_right (H := YH), ← hsup]
    exact (Subgroup.relIndex_sup_right (H := K) (K := YH)).symm
  have hKrel : K.relIndex YH = K.index := by
    have h1 : K.relIndex YH * YH.index = K.index * YH.index := by
      rw [← Subgroup.index_inf (H := K) (K := YH)]
      rw [inf_comm, Subgroup.index_inf (H := YH) (K := K), hYHrel, mul_comm K.index YH.index]
    exact mul_right_cancel₀ (Subgroup.index_ne_zero_of_finite) h1
  let SY : Subgroup YH := S_H.subgroupOf YH
  have hSY3 : IsPGroup 3 SY :=
    hS3.of_equiv (Subgroup.subgroupOfEquivOfLe inf_le_right).symm
  have hSidx : ¬ 3 ∣ SY.index := by
    have hSYidx : SY.index = K.index := by
      change (S_H.subgroupOf YH).index = K.index
      rw [show (S_H.subgroupOf YH).index = (K ⊓ YH).relIndex YH from rfl,
        Subgroup.inf_relIndex_right, hKrel]
    rw [hSYidx]
    exact hKindex
  let hSyl : Sylow 3 YH := hSY3.toSylow hSidx
  have hmaxH : ∀ R : Subgroup H, R ≤ YH → IsPGroup 3 R → S_H ≤ R → R = S_H := by
    intro R hRY hR3 hSR
    let RY : Subgroup YH := R.subgroupOf YH
    have hRY3 : IsPGroup 3 RY := hR3.of_equiv (Subgroup.subgroupOfEquivOfLe hRY).symm
    have hle : SY ≤ RY := Subgroup.subgroupOf_mono YH hSR
    have hmax : RY = SY := by simpa [hSyl] using hSyl.is_maximal' hRY3 hle
    calc R = RY.map YH.subtype := (Subgroup.map_subgroupOf_eq_of_le hRY).symm
      _ = SY.map YH.subtype := by rw [hmax]
      _ = S_H := Subgroup.map_subgroupOf_eq_of_le inf_le_right
  let S : Subgroup G := S_H.map H.subtype
  have hS_le_Y : S ≤ Y := by
    calc S = S_H.map H.subtype := rfl
      _ ≤ YH.map H.subtype := Subgroup.map_mono inf_le_right
      _ = Y := Subgroup.map_subgroupOf_eq_of_le hYH_le
  have hS_ispg : IsPGroup 3 S :=
    hS3.of_equiv (Subgroup.equivMapOfInjective S_H H.subtype H.subtype_injective)
  have hSmax : ∀ R : Subgroup G, R ≤ Y → IsPGroup 3 R → S ≤ R → R = S := by
    intro R hRY hR3 hSR
    have hRHle : R.subgroupOf H ≤ YH := by
      intro x hx
      exact hRY (Subgroup.mem_subgroupOf.mp hx)
    have hRH : R ≤ H := hRY.trans hYH_le
    have hRH3 : IsPGroup 3 (R.subgroupOf H) :=
      hR3.of_equiv (Subgroup.subgroupOfEquivOfLe hRH).symm
    have hSRH : S_H ≤ R.subgroupOf H := by
      intro x hx
      exact Subgroup.mem_subgroupOf.mpr (hSR (Subgroup.mem_map.mpr ⟨x, hx, rfl⟩))
    have hEq : R.subgroupOf H = S_H := hmaxH _ hRHle hRH3 hSRH
    calc R = (R.subgroupOf H).map H.subtype := (Subgroup.map_subgroupOf_eq_of_le hRH).symm
      _ = S_H.map H.subtype := by rw [hEq]
      _ = S := rfl
  have hD_norm : D ≤ Subgroup.normalizer (S : Set G) := by
    have hKnorm : K ≤ Subgroup.normalizer (S_H : Set H) := by
      have h1 : K ≤ Subgroup.normalizer (K : Set H) := Subgroup.le_normalizer
      have h2 : K ≤ Subgroup.normalizer (YH : Set H) := Subgroup.le_normalizer_of_normal
      exact (le_inf h1 h2).trans Subgroup.inf_normalizer_le_normalizer_inf
    have hDHnorm : DH ≤ Subgroup.normalizer (S_H : Set H) := hDK.trans hKnorm
    have hmap : DH.map H.subtype ≤ (Subgroup.normalizer (S_H : Set H)).map H.subtype :=
      Subgroup.map_mono hDHnorm
    have hgoal : DH.map H.subtype ≤ Subgroup.normalizer (S : Set G) :=
      hmap.trans (Subgroup.le_normalizer_map H.subtype)
    rwa [Subgroup.map_subgroupOf_eq_of_le hDH_le] at hgoal
  exact ⟨S, hS_le_Y, hS_ispg, hSmax, hD_norm⟩

end CFSG.OddInvariantSylow

end
