module

public import CFSG.Quasithin.H13.A5S136sp7
public import CFSG.Quasithin.H13.A5S136sp3

public section

namespace CFSG.Quasithin.H13.A5.SpBorel

open CFSG.Open CFSG.Quasithin CFSG.Assembly.LowTwoRank
open CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag
open CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher

theorem proj_normalizer_le {K : Type} [Field K] [Finite K] {f : ℕ} (hf : 1 ≤ f)
    (hK : Nat.card K = 2 ^ f) {D : Subgroup (StatedProj (StatedSp 2 K))}
    (hDU : D ≤ projUnipotent 2 K) (hD2 : D.relIndex (projUnipotent 2 K) = 2)
    (hK4 : 4 ≤ Nat.card K) :
    Subgroup.normalizer (D : Set (StatedProj (StatedSp 2 K))) ≤ projBorel 2 K := by
  have hinj := proj_injective (f := f) (r := 2) hf (by norm_num) hK
  have hsurj : Function.Surjective (proj 2 K) := QuotientGroup.mk'_surjective _
  have hD₀U : D.comap (proj 2 K) ≤ unipotent 2 K := by
    intro x hx
    obtain ⟨u, hu, hux⟩ := Subgroup.mem_map.mp (hDU hx)
    rw [← hinj hux]
    exact hu
  have hD₀2 : (D.comap (proj 2 K)).relIndex (unipotent 2 K) = 2 := by
    rw [Subgroup.relIndex_comap]
    exact hD2
  intro y hy
  obtain ⟨g, rfl⟩ := hsurj y
  have hg : g ∈ Subgroup.normalizer ((D.comap (proj 2 K) : Subgroup (StatedSp 2 K)) :
      Set (StatedSp 2 K)) := by
    rw [Subgroup.mem_normalizer_iff] at hy ⊢
    intro x
    rw [Subgroup.mem_comap, Subgroup.mem_comap, map_mul, map_mul, map_inv]
    exact hy (proj 2 K x)
  exact Subgroup.mem_map.mpr ⟨g, normalizer_le_borel hD₀U hD₀2 hK4 hg, rfl⟩

theorem normalizer_le_of_relIndex_two {X : Type} [Group X] [Finite X] {f : ℕ} (hf : 2 ≤ f)
    (hX : StatedClassicalModel X .PSp 2 2 f) (P : Sylow 2 X) {D : Subgroup X}
    (hDP : D ≤ P) (hD2 : D.relIndex P = 2) :
    Subgroup.normalizer (D : Set X) ≤ Subgroup.normalizer ((P : Subgroup X) : Set X) := by
  obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := hX
  have : CharP K 2 := charP_two_of_card hK
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨U, hU⟩ := exists_sylow_projUnipotent (r := 2) (K := K) 2 (by norm_num)
  obtain ⟨φ, hφ⟩ := exists_mulEquiv_sylow e P U
  rw [hU] at hφ
  have hK4 : 4 ≤ Nat.card K := by
    rw [hK]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
  have hDφ : ∀ x, x ∈ D ↔ φ x ∈ D.map φ.toMonoidHom := by
    intro x
    constructor
    · intro h
      exact Subgroup.mem_map.mpr ⟨x, h, rfl⟩
    · intro h
      obtain ⟨y, hy, hyx⟩ := Subgroup.mem_map.mp h
      rw [← φ.injective hyx]
      exact hy
  have hUbar : (P : Subgroup X).map φ.toMonoidHom = projUnipotent 2 K := by
    ext y
    obtain ⟨x, rfl⟩ := φ.surjective y
    rw [← hφ]
    constructor
    · intro h
      obtain ⟨x', hx', hxx⟩ := Subgroup.mem_map.mp h
      rw [← φ.injective hxx]
      exact hx'
    · intro h
      exact Subgroup.mem_map.mpr ⟨x, h, rfl⟩
  have hDU : D.map φ.toMonoidHom ≤ projUnipotent 2 K := by
    rw [← hUbar]
    exact Subgroup.map_mono hDP
  have hD2' : (D.map φ.toMonoidHom).relIndex (projUnipotent 2 K) = 2 := by
    rw [← hUbar, Subgroup.relIndex_map_map_of_injective _ _ φ.injective, hD2]
  intro x hx
  rw [mem_normalizer_iff_of_mulEquiv φ hφ x, normalizer_projUnipotent 2 (by norm_num)]
  exact proj_normalizer_le (f := f) (by omega) hK hDU hD2' hK4
    ((mem_normalizer_iff_of_mulEquiv φ hDφ x).mp hx)

theorem le_normalizer_or_of_relIndex_three {X : Type} [Group X] [Finite X] {P H : Subgroup X}
    (hPH : P ≤ H) (h3 : P.relIndex H = 3) :
    H ≤ Subgroup.normalizer (P : Set X) ∨
      ∃ D : Subgroup X, D ≤ P ∧ D.relIndex P = 2 ∧ H ≤ Subgroup.normalizer (D : Set X) := by
  have hCP : (P.subgroupOf H).normalCore ≤ P.subgroupOf H := Subgroup.normalCore_le _
  have hdvd : (P.subgroupOf H).normalCore.index ∣ 2 * 3 := by
    have := Subgroup.index_normalCore_dvd_factorial_index (P.subgroupOf H)
    rw [show (P.subgroupOf H).index = 3 from h3] at this
    exact this
  have hmul := Subgroup.relIndex_mul_index hCP
  rw [show (P.subgroupOf H).index = 3 from h3] at hmul
  have hr : (P.subgroupOf H).normalCore.relIndex (P.subgroupOf H) ∣ 2 := by
    refine Nat.dvd_of_mul_dvd_mul_right (k := 3) (by norm_num) ?_
    rw [hmul]
    exact hdvd
  rcases (Nat.dvd_prime Nat.prime_two).mp hr with h1 | h2
  · left
    have hle : P.subgroupOf H ≤ (P.subgroupOf H).normalCore := Subgroup.relIndex_eq_one.mp h1
    have hN : (P.subgroupOf H).Normal := by
      rw [show P.subgroupOf H = (P.subgroupOf H).normalCore from le_antisymm hle hCP]
      exact Subgroup.normalCore_normal _
    exact (Subgroup.normal_subgroupOf_iff_le_normalizer hPH).mp hN
  · right
    refine ⟨(P.subgroupOf H).normalCore.map H.subtype, ?_, ?_, ?_⟩
    · calc (P.subgroupOf H).normalCore.map H.subtype ≤ (P.subgroupOf H).map H.subtype :=
            Subgroup.map_mono hCP
        _ = P := Subgroup.map_subgroupOf_eq_of_le hPH
    · have h := Subgroup.relIndex_map_map_of_injective (P.subgroupOf H).normalCore
        (P.subgroupOf H) H.subtype_injective
      rw [Subgroup.map_subgroupOf_eq_of_le hPH] at h
      exact h.trans h2
    · have hN : (((P.subgroupOf H).normalCore.map H.subtype).subgroupOf H).Normal := by
        rw [show ((P.subgroupOf H).normalCore.map H.subtype).subgroupOf H =
            (P.subgroupOf H).normalCore from
          Subgroup.comap_map_eq_self_of_injective H.subtype_injective _]
        exact Subgroup.normalCore_normal _
      exact (Subgroup.normal_subgroupOf_iff_le_normalizer (Subgroup.map_subtype_le _)).mp hN

theorem clause3 {X : Type} [Group X] [Finite X] {f : ℕ} (hf : 2 ≤ f)
    (hX : StatedClassicalModel X .PSp 2 2 f) (P : Sylow 2 X) (H : Subgroup X)
    (hPH : (P : Subgroup X) ≤ H)
    (hH : ∀ p : ℕ, p.Prime → p ∣ Nat.card H → p = 2 ∨ p = 3) (h9 : ¬ 9 ∣ Nat.card H) :
    H ≤ Subgroup.normalizer ((P : Subgroup X) : Set X) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hnH : (P : Subgroup X).relIndex H ∣ Nat.card H := Subgroup.relIndex_dvd_card _ _
  have hn0 : (P : Subgroup X).relIndex H ≠ 0 := (Nat.pos_of_dvd_of_pos hnH Nat.card_pos).ne'
  have hn2 : ¬ 2 ∣ (P : Subgroup X).relIndex H := fun h =>
    P.not_dvd_index (h.trans (Subgroup.relIndex_dvd_index_of_le hPH))
  obtain ⟨k, hk⟩ : ∃ k, (P : Subgroup X).relIndex H = 3 ^ k :=
    ⟨_, Nat.eq_prime_pow_of_unique_prime_dvd hn0 fun {d} hd hdn => by
      rcases hH d hd (hdn.trans hnH) with h | h
      · subst h
        exact absurd hdn hn2
      · exact h⟩
  have hk1 : k ≤ 1 := by
    by_contra hk1
    apply h9
    refine Dvd.dvd.trans ?_ hnH
    rw [hk]
    exact Dvd.dvd.trans (by norm_num : (9 : ℕ) ∣ 3 ^ 2) (pow_dvd_pow 3 (by omega))
  interval_cases k
  · rw [pow_zero] at hk
    exact (Subgroup.relIndex_eq_one.mp hk).trans Subgroup.le_normalizer
  · rw [pow_one] at hk
    rcases le_normalizer_or_of_relIndex_three hPH hk with h | ⟨D, hDP, hD2, hHD⟩
    · exact h
    · exact hHD.trans (normalizer_le_of_relIndex_two hf hX P hDP hD2)

end CFSG.Quasithin.H13.A5.SpBorel
