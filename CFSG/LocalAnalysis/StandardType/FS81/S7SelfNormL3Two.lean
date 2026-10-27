module

public import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
import CFSG.LocalAnalysis.StandardType.FS81.S7L3TwoSection
import CFSG.LocalAnalysis.StandardType.FS81.S7BurnsideSelfNorm
public import Mathlib.Data.Rat.Floor
public import Mathlib.GroupTheory.PGroup

public section

namespace CFSG.StandardType.FrameRoute.FS81

private theorem mem_of_odd_order_of_normalComplement {X : Type} [Group X]
    {S P O : Subgroup X} (hOS : O ≤ S) (hPS : P ≤ S) (hP : IsPGroup 2 P)
    [hO : (O.subgroupOf S).Normal] (hSOP : S ≤ O ⊔ P)
    {s : X} (hs : s ∈ S) (hodd : Odd (orderOf s)) : s ∈ O := by
  have hsup : O.subgroupOf S ⊔ P.subgroupOf S = ⊤ := by
    rw [← Subgroup.subgroupOf_sup hOS hPS]
    exact Subgroup.subgroupOf_eq_top.mpr hSOP
  have hmem : (⟨s, hs⟩ : ↥S) ∈ O.subgroupOf S ⊔ P.subgroupOf S := by
    rw [hsup]
    exact Subgroup.mem_top _
  obtain ⟨o, ho, p, hp, hop⟩ := Subgroup.mem_sup_of_normal_left.mp hmem
  let π : ↥S →* (↥S ⧸ O.subgroupOf S) := QuotientGroup.mk' (O.subgroupOf S)
  have hπo : π o = 1 := (QuotientGroup.eq_one_iff (N := O.subgroupOf S) o).mpr ho
  have hπeq : π p = π ⟨s, hs⟩ := by
    have h : π o * π p = π ⟨s, hs⟩ := by
      simpa only [map_mul] using congrArg π hop
    rwa [hπo, one_mul] at h
  have hdivS : orderOf (π ⟨s, hs⟩) ∣ orderOf s := by
    simpa only [Subgroup.orderOf_mk] using orderOf_map_dvd π (⟨s, hs⟩ : ↥S)
  obtain ⟨k, hk⟩ := hP.exists_orderOf_eq_pow
    (⟨(p : X), Subgroup.mem_subgroupOf.mp hp⟩ : ↥P)
  have hkp : orderOf p = 2 ^ k := by
    rw [← Subgroup.orderOf_coe p,
      ← Subgroup.orderOf_mk (p : X) (Subgroup.mem_subgroupOf.mp hp)]
    exact hk
  have hdiv2 : orderOf (π ⟨s, hs⟩) ∣ 2 ^ k := by
    rw [← hπeq, ← hkp]
    exact orderOf_map_dvd π p
  have hcop : Nat.Coprime (orderOf s) (2 ^ k) :=
    Nat.Prime.coprime_pow_of_not_dvd Nat.prime_two hodd.not_two_dvd_nat
  have h1 : orderOf (π ⟨s, hs⟩) = 1 :=
    Nat.eq_one_of_dvd_coprimes hcop hdivS hdiv2
  have hmemO : (⟨s, hs⟩ : ↥S) ∈ O.subgroupOf S :=
    (QuotientGroup.eq_one_iff (N := O.subgroupOf S) (⟨s, hs⟩ : ↥S)).mp
      (orderOf_eq_one_iff.mp h1)
  exact Subgroup.mem_subgroupOf.mp hmemO

private theorem conj_mem_of_mem_of_odd_normal {X : Type} [Group X] {S O : Subgroup X} {d : X}
    (hdS : d ∈ Subgroup.normalizer (S : Set X)) (hOS : O ≤ S) (hOodd : Odd (Nat.card O))
    (hmem : ∀ {s : X}, s ∈ S → Odd (orderOf s) → s ∈ O) :
    ∀ o ∈ O, d * o * d⁻¹ ∈ O := by
  intro o ho
  have hconjS : d * o * d⁻¹ ∈ S :=
    (Subgroup.mem_normalizer_iff.mp hdS o).mp (hOS ho)
  refine hmem hconjS ?_
  have hdiv : orderOf o ∣ Nat.card O := by
    rw [← Subgroup.orderOf_mk o ho]
    exact orderOf_dvd_natCard (⟨o, ho⟩ : ↥O)
  have hconj : orderOf (d * o * d⁻¹) = orderOf o :=
    orderOf_injective (MulAut.conj d).toMonoidHom (MulAut.conj d).injective o
  rw [hconj]
  exact hOodd.of_dvd_nat hdiv

private theorem le_normalizer_of_odd_normalComplement {X : Type} [Group X] {S O D : Subgroup X}
    (hDS : D ≤ Subgroup.normalizer (S : Set X)) (hOS : O ≤ S) (hOodd : Odd (Nat.card O))
    (hmem : ∀ {s : X}, s ∈ S → Odd (orderOf s) → s ∈ O) :
    D ≤ Subgroup.normalizer (O : Set X) := by
  intro d hd
  rw [Subgroup.mem_normalizer_iff]
  intro o
  constructor
  · exact conj_mem_of_mem_of_odd_normal (hDS hd) hOS hOodd hmem o
  · intro ho'
    have h := conj_mem_of_mem_of_odd_normal (hDS (D.inv_mem hd)) hOS hOodd hmem
      (d * o * d⁻¹) ho'
    rwa [show d⁻¹ * (d * o * d⁻¹) * (d⁻¹)⁻¹ = o from by group] at h

private theorem eq_one_of_mem_normalComplement_of_commute {X : Type} [Group X]
    {S P O : Subgroup X} {b : X} (hOS : O ≤ S) (hOodd : Odd (Nat.card O))
    (hP : IsPGroup 2 P) (hC : ∀ x ∈ S, x * b = b * x → x ∈ P) :
    ∀ x ∈ O, x * b = b * x → x = 1 := by
  intro x hx hxb
  have hxP : x ∈ P := hC x (hOS hx) hxb
  have hdivO : orderOf x ∣ Nat.card O := by
    rw [← Subgroup.orderOf_mk x hx]
    exact orderOf_dvd_natCard (⟨x, hx⟩ : ↥O)
  obtain ⟨k, hk⟩ := hP.exists_orderOf_eq_pow (⟨x, hxP⟩ : ↥P)
  have hx2 : orderOf x = 2 ^ k := by
    rw [← Subgroup.orderOf_mk x hxP]
    exact hk
  have hcop : Nat.Coprime (Nat.card O) (2 ^ k) :=
    Nat.Prime.coprime_pow_of_not_dvd Nat.prime_two hOodd.not_two_dvd_nat
  have h1 : orderOf x = 1 :=
    Nat.eq_one_of_dvd_coprimes hcop hdivO (hx2 ▸ dvd_rfl)
  exact orderOf_eq_one_iff.mp h1

theorem le_of_selfNormalizing_l3Two {X : Type} [Group X] [Finite X] {S P D : Subgroup X}
    {σ b : X} (hPS : P ≤ S) (hP : IsPGroup 2 P) (hσP : σ ∈ P)
    (hSσ : ∀ s ∈ S, s * σ = σ * s)
    (hPP : ∀ x ∈ P, ∀ y ∈ P, x * y * x⁻¹ * y⁻¹ ∈ Subgroup.zpowers σ)
    (hDS : D ≤ Subgroup.normalizer (S : Set X)) (hDP : D ≤ Subgroup.normalizer (P : Set X))
    (hD : Nonempty (↥D ≃* Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)))
    (hbD : b ∈ D) (hb : orderOf b = 3)
    (hC : ∀ x ∈ S, x * b = b * x → x ∈ P) : S ≤ P := by
  have hN : ∀ x ∈ S, x ∈ Subgroup.normalizer (P : Set X) → x ∈ P := by
    have hNd : D ≤ Subgroup.normalizer
        ((Subgroup.normalizer (P : Set X) : Subgroup X) : Set X) :=
      fun d hd => Subgroup.le_normalizer (H := Subgroup.normalizer (P : Set X)) (hDP hd)
    have hle : S ⊓ Subgroup.normalizer (P : Set X) ≤ P := by
      refine le_of_centralizer_le_l3Two
        (T := S ⊓ Subgroup.normalizer (P : Set X)) (T₀ := P) (D := D)
        hP (le_inf hPS Subgroup.le_normalizer) inf_le_right ?_ hDP hD hbD hb ?_
      · intro d hd
        rw [Subgroup.mem_normalizer_iff]
        intro h
        rw [Subgroup.mem_inf, Subgroup.mem_inf]
        constructor
        · rintro ⟨hhS, hhN⟩
          exact ⟨(Subgroup.mem_normalizer_iff.mp (hDS hd) h).mp hhS,
            (Subgroup.mem_normalizer_iff.mp (hNd hd) h).mp hhN⟩
        · rintro ⟨hhS, hhN⟩
          exact ⟨(Subgroup.mem_normalizer_iff.mp (hDS hd) h).mpr hhS,
            (Subgroup.mem_normalizer_iff.mp (hNd hd) h).mpr hhN⟩
      · intro x hxT hxb
        exact hC x hxT.1 hxb
    intro x hxS hxN
    exact hle ⟨hxS, hxN⟩
  obtain ⟨O, hOS, hO, hOodd, hSOP⟩ :=
    exists_normalComplement_of_selfNormalizing hPS hP hσP hSσ hPP hN
  have hmemO : ∀ {s : X}, s ∈ S → Odd (orderOf s) → s ∈ O :=
    fun {s} hs hodd =>
      mem_of_odd_order_of_normalComplement (hO := hO) hOS hPS hP hSOP hs hodd
  have hDO : D ≤ Subgroup.normalizer (O : Set X) :=
    le_normalizer_of_odd_normalComplement hDS hOS hOodd hmemO
  have hCO : ∀ x ∈ O, x * b = b * x → x ∈ (⊥ : Subgroup X) := by
    intro x hx hxb
    rw [Subgroup.mem_bot]
    exact eq_one_of_mem_normalComplement_of_commute hOS hOodd hP hC x hx hxb
  have hOle : O ≤ (⊥ : Subgroup X) := by
    refine le_of_centralizer_le_l3Two (T := O) (T₀ := ⊥) (D := D)
      IsPGroup.of_bot bot_le ?_ hDO ?_ hD hbD hb hCO
    · rw [Subgroup.normalizer_eq_top_iff.mpr
        (inferInstance : (⊥ : Subgroup X).Normal)]
      exact le_top
    · rw [Subgroup.normalizer_eq_top_iff.mpr
        (inferInstance : (⊥ : Subgroup X).Normal)]
      exact le_top
  exact hSOP.trans (sup_le (hOle.trans bot_le) le_rfl)

end CFSG.StandardType.FrameRoute.FS81

end
