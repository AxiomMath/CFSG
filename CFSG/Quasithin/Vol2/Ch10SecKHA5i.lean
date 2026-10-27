module

public import CFSG.Quasithin.Vol2.Ch10SecKHA5f
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.G3J4N3Done

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecF.C10KH

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique

theorem four_dvd_card_centralizer {B : Type} [Group B] [Finite B] {y a b : B}
    (ha : a ∈ CFSG.pCore 2 B) (hb : b ∈ CFSG.pCore 2 B) (ha1 : a ≠ 1) (hb1 : b ≠ 1)
    (hab : a ≠ b) (hya : y * a = a * y) (hyb : y * b = b * y) :
    4 ∣ Nat.card ↥(CFSG.pCore 2 B ⊓ Subgroup.centralizer ({y} : Set B)) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set W := CFSG.pCore 2 B ⊓ Subgroup.centralizer ({y} : Set B) with hWdef
  have haW : a ∈ W := ⟨ha, Subgroup.mem_centralizer_singleton_iff.2 hya.symm⟩
  have hbW : b ∈ W := ⟨hb, Subgroup.mem_centralizer_singleton_iff.2 hyb.symm⟩
  have hW3 : 3 ≤ Nat.card W := by
    let f : Fin 3 → W := ![1, ⟨a, haW⟩, ⟨b, hbW⟩]
    have key : ∀ i : Fin 3, ((f i : W) : B) = ![(1 : B), a, b] i := by
      intro i
      fin_cases i <;> rfl
    have hf : Function.Injective f := by
      intro i j hij
      have h2 : ![(1 : B), a, b] i = ![(1 : B), a, b] j := by
        rw [← key, ← key, hij]
      fin_cases i <;> fin_cases j <;> simp at h2 ⊢
      all_goals first
        | exact ha1 h2 | exact ha1 h2.symm | exact hb1 h2 | exact hb1 h2.symm
        | exact hab h2 | exact hab h2.symm
    have := Nat.card_le_card_of_injective f hf
    simpa using this
  have hW2 : IsPGroup 2 W := (CFSG.pCore_isPGroup (G := B) (p := 2)).to_le inf_le_left
  obtain ⟨m, hm⟩ := hW2.exists_card_eq
  have hm2 : 2 ≤ m := by
    by_contra h
    push Not at h
    interval_cases m <;> rw [hm] at hW3 <;> norm_num at hW3
  rw [hm]
  exact (pow_dvd_pow 2 hm2 : 2 ^ 2 ∣ 2 ^ m)

theorem sl25_exists_normalizer_dvd {X : Type} [Group X] [Finite X] {T B : Subgroup X}
    (hT : IsSylowTwoOf T ⊤) (hcard : Nat.card T = 2 ^ 21) (hD : IsSL25Group ↥B)
    (hTB : T ≤ Subgroup.normalizer (B : Set X)) :
    ∃ P N : Subgroup X, Nat.card P = 3 ∧ N ≤ Subgroup.normalizer (P : Set X) ∧
      2 ^ 16 ∣ Nat.card N := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨j, hj1, hj2, hnorm, hq⟩ := sl25_sup_data hT hD hTB
  have hj : j = 14 := by
    have h2 : 2 ^ (7 + j) = 2 ^ 21 := by rw [← hj1, hcard]
    have := Nat.pow_right_injective (le_refl 2) h2
    omega
  subst hj
  have hBY : B ≤ B ⊔ T := le_sup_left
  have : (B.subgroupOf (B ⊔ T)).Normal := hnorm
  obtain ⟨y, hy3, a, ha, b, hb, ha1, hb1, hab, hya, hyb⟩ := hD.four
  have hW4 := four_dvd_card_centralizer ha hb ha1 hb1 hab hya hyb
  let ι : ↥B →* ↥(B ⊔ T) := Subgroup.inclusion hBY
  have hι : Function.Injective ι := Subgroup.inclusion_injective hBY
  have hy'3 : orderOf (ι y) = 3 := (orderOf_injective ι hι y).trans hy3
  set P : Subgroup ↥(B ⊔ T) := Subgroup.zpowers (ι y) with hP
  have hP3 : Nat.card P = 3 := by rw [hP, Nat.card_zpowers, hy'3]
  have hPN : P ≤ B.subgroupOf (B ⊔ T) :=
    (Subgroup.zpowers_le).mpr (show ι y ∈ B.subgroupOf (B ⊔ T) from y.2)
  have hPgrp : IsPGroup 3 ↥P := IsPGroup.of_card (n := 1) (by rw [hP3]; norm_num)
  have hindex : ¬ 3 ∣ P.index := by
    have h1 := Subgroup.index_mul_card P
    rw [hP3, hj2] at h1
    omega
  let P₃ : Sylow 3 ↥(B ⊔ T) := hPgrp.toSylow hindex
  have hFr : Subgroup.normalizer (P : Set ↥(B ⊔ T)) ⊔ B.subgroupOf (B ⊔ T) = ⊤ :=
    Sylow.normalizer_sup_eq_top' P₃ hPN
  set M : Subgroup ↥(B ⊔ T) := Subgroup.normalizer (P : Set ↥(B ⊔ T)) with hM
  have hrel : (B.subgroupOf (B ⊔ T)).relIndex M = 2 ^ 14 := by
    have h1 := Subgroup.relIndex_sup_right (H := M) (K := B.subgroupOf (B ⊔ T))
    rw [hFr, Subgroup.relIndex_top_right] at h1
    rw [← h1]
    exact hq
  have hMcard : Nat.card M = Nat.card ((B.subgroupOf (B ⊔ T)).subgroupOf M) * 2 ^ 14 := by
    rw [← hrel]
    exact (Subgroup.card_mul_index ((B.subgroupOf (B ⊔ T)).subgroupOf M)).symm
  have hWM : ∀ w : ↥(CFSG.pCore 2 ↥B ⊓ Subgroup.centralizer ({y} : Set ↥B)), ι w ∈ M := by
    intro w
    have hwc : ι w ∈ Subgroup.centralizer (P : Set ↥(B ⊔ T)) := by
      rw [Subgroup.mem_centralizer_iff]
      intro h hh
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hh
      have hc : Commute (ι y) (ι w) := by
        show ι y * ι w = ι w * ι y
        rw [← map_mul, ← map_mul, Subgroup.mem_centralizer_singleton_iff.1 w.2.2]
      exact (hc.zpow_left k).eq
    exact Subgroup.centralizer_le_normalizer (P : Set ↥(B ⊔ T)) hwc
  let f : ↥(CFSG.pCore 2 ↥B ⊓ Subgroup.centralizer ({y} : Set ↥B)) →*
      ↥((B.subgroupOf (B ⊔ T)).subgroupOf M) :=
    { toFun := fun w => ⟨⟨ι w, hWM w⟩, (w : ↥B).2⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
  have hf : Function.Injective f := by
    intro w w' hww
    have h1 : ι w = ι w' := congrArg Subtype.val (congrArg Subtype.val hww)
    exact Subtype.ext (hι h1)
  have h4 : 4 ∣ Nat.card ((B.subgroupOf (B ⊔ T)).subgroupOf M) :=
    hW4.trans (Subgroup.card_dvd_of_injective f hf)
  refine ⟨P.map (B ⊔ T).subtype, M.map (B ⊔ T).subtype, ?_,
    A5.G3.map_subtype_le_normalizer (le_refl M), ?_⟩
  · rw [Subgroup.card_map_of_injective (B ⊔ T).subtype_injective, hP3]
  · rw [Subgroup.card_map_of_injective (B ⊔ T).subtype_injective, hMcard]
    obtain ⟨c, hc⟩ := h4
    exact ⟨c, by rw [hc]; ring⟩

theorem noSL25Norm_j4
    {X : Type} [Group X] [Finite X] (h : IsSporadic .J4 X) : NoSL25Norm X := by
  intro T B hT hTB hD
  have hXcard : Nat.card X = 2 ^ 21 * 41377816699065 := by
    obtain ⟨e⟩ := h
    rw [Nat.card_congr e.toEquiv]
    exact CFSG.Sporadic.J4.card_J4.trans (by norm_num)
  have hTcard : Nat.card T = 2 ^ 21 := A5.G3.card_eq_of_isSylowTwoOf hT (by norm_num) hXcard
  obtain ⟨P, N, hP3, hN, hdvd⟩ := sl25_exists_normalizer_dvd hT hTcard hD hTB
  exact A5.G3.j4Normalizer3 X h P N hP3 hN hdvd

end CFSG.Quasithin.Vol2.Ch10.SecF.C10KH
