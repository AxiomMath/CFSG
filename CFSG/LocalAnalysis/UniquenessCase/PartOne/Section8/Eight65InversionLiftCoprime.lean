module

public import Mathlib.GroupTheory.PGroup
import CFSG.GroupTheory.ABGLocalTools.CoreLemmas
public import Mathlib.Data.Rat.Floor

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8

theorem exists_inverts_of_quotient_inverts {Γ : Type} [Group Γ] [Finite Γ]
    {O Z : Subgroup Γ} [O.Normal] (hO : Nat.Coprime 3 (Nat.card O)) (hZ : Nat.card Z = 3)
    {t : Γ ⧸ O} (h : ∀ z ∈ Z, t * (z : Γ ⧸ O) * t⁻¹ = (z : Γ ⧸ O)⁻¹) :
    ∃ n ∈ Subgroup.normalizer (Z : Set Γ), ∀ z ∈ Z, n * z * n⁻¹ = z⁻¹ := by
  classical
  have hprime : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨t1, ht1⟩ := QuotientGroup.mk'_surjective O t
  set Z' : Subgroup Γ := Z.map (MulAut.conj t1) with hZ'def
  have hZ'card : Nat.card Z' = 3 := by
    rw [hZ'def, Subgroup.card_map_of_injective (MulAut.conj t1).injective, hZ]
  have hq_conj : ∀ z ∈ Z, QuotientGroup.mk' O (t1 * z * t1⁻¹) = (QuotientGroup.mk' O z)⁻¹ := by
    intro z hz
    rw [map_mul, map_mul, map_inv, ht1]
    exact h z hz
  have hZ'le : Z' ≤ O ⊔ Z := by
    rw [hZ'def]
    rintro x ⟨z, hz, rfl⟩
    change t1 * z * t1⁻¹ ∈ O ⊔ Z
    rw [Subgroup.mem_sup_of_normal_left]
    refine ⟨(t1 * z * t1⁻¹) * z, ?_, z⁻¹, Z.inv_mem hz, by group⟩
    refine (QuotientGroup.eq_one_iff (N := O) ((t1 * z * t1⁻¹) * z)).mp ?_
    show QuotientGroup.mk' O ((t1 * z * t1⁻¹) * z) = 1
    rw [map_mul, hq_conj z hz, inv_mul_cancel]
  have hZo : Z ⊓ O = (⊥ : Subgroup Γ) :=
    (Subgroup.disjoint_of_coprime_natCard (by rw [hZ]; exact hO)).eq_bot
  have hZrel_sup : Z.relIndex (O ⊔ Z) = Nat.card O := by
    rw [CFSG.ABGLocalTools.relIndex_sup_eq_relIndex_of_normal O Z,
      ← Subgroup.inf_relIndex_right Z O, hZo, Subgroup.relIndex_bot_left]
  have hcardH : Nat.card (O ⊔ Z : Subgroup Γ) = 3 * Nat.card O := by
    have h := Subgroup.relIndex_mul_card (H := Z) (K := O ⊔ Z)
    rw [inf_eq_left.mpr (le_sup_right : Z ≤ O ⊔ Z), hZrel_sup, hZ] at h
    rw [← h, mul_comm]
  have hZ'o : Z' ⊓ O = (⊥ : Subgroup Γ) :=
    (Subgroup.disjoint_of_coprime_natCard (by rw [hZ'card]; exact hO)).eq_bot
  have hZ'rel_sup : Z'.relIndex (O ⊔ Z') = Nat.card O := by
    rw [CFSG.ABGLocalTools.relIndex_sup_eq_relIndex_of_normal O Z',
      ← Subgroup.inf_relIndex_right Z' O, hZ'o, Subgroup.relIndex_bot_left]
  have hcardH' : Nat.card (O ⊔ Z' : Subgroup Γ) = 3 * Nat.card O := by
    have h := Subgroup.relIndex_mul_card (H := Z') (K := O ⊔ Z')
    rw [inf_eq_left.mpr (le_sup_right : Z' ≤ O ⊔ Z'), hZ'rel_sup, hZ'card] at h
    rw [← h, mul_comm]
  have hHZ' : O ⊔ Z' = O ⊔ Z := by
    refine Subgroup.eq_of_le_of_card_ge (sup_le le_sup_left hZ'le) ?_
    rw [hcardH, hcardH']
  have hZ'rel_H : Z'.relIndex (O ⊔ Z) = Nat.card O := by
    rw [← hHZ', hZ'rel_sup]
  have hSylowZ : CFSG.ABGLocalTools.IsSylowOf 3 Z (O ⊔ Z) := by
    rw [CFSG.ABGLocalTools.isSylowOf_iff]
    exact ⟨le_sup_right, IsPGroup.of_card (n := 1) (by rw [hZ]; norm_num),
      by rw [hZrel_sup]; exact (Nat.prime_three.coprime_iff_not_dvd).mp hO⟩
  have hSylowZ' : CFSG.ABGLocalTools.IsSylowOf 3 Z' (O ⊔ Z) := by
    rw [CFSG.ABGLocalTools.isSylowOf_iff]
    exact ⟨hZ'le, IsPGroup.of_card (n := 1) (by rw [hZ'card]; norm_num),
      by rw [hZ'rel_H]; exact (Nat.prime_three.coprime_iff_not_dvd).mp hO⟩
  obtain ⟨k, hkH, hconj⟩ := hSylowZ.exists_mem_conj hSylowZ'
  obtain ⟨o, ho, z0, hz0, hk⟩ := Subgroup.mem_sup_of_normal_left.mp hkH
  have hkconj : ∀ x : Γ, k⁻¹ * x * k = z0⁻¹ * (o⁻¹ * x * o) * z0 := by
    intro x
    rw [← hk]
    group
  have hmemZ' : ∀ x : Γ, x ∈ Z' ↔ t1⁻¹ * x * t1 ∈ Z := by
    intro x
    rw [hZ'def, Subgroup.mem_map]
    constructor
    · rintro ⟨y, hy, hyx⟩
      rw [← hyx]
      change t1⁻¹ * (t1 * y * t1⁻¹) * t1 ∈ Z
      rwa [show t1⁻¹ * (t1 * y * t1⁻¹) * t1 = y by group]
    · intro hx
      exact ⟨t1⁻¹ * x * t1, hx, by
        change t1 * (t1⁻¹ * x * t1) * t1⁻¹ = x
        group⟩
  have hkey : ∀ x : Γ, o⁻¹ * x * o ∈ Z ↔ t1⁻¹ * x * t1 ∈ Z := by
    intro x
    have hz0iff : z0⁻¹ * (o⁻¹ * x * o) * z0 ∈ Z ↔ o⁻¹ * x * o ∈ Z := by
      constructor
      · intro hx
        have h2 : z0 * (z0⁻¹ * (o⁻¹ * x * o) * z0) * z0⁻¹ ∈ Z :=
          Z.mul_mem (Z.mul_mem hz0 hx) (Z.inv_mem hz0)
        rwa [show z0 * (z0⁻¹ * (o⁻¹ * x * o) * z0) * z0⁻¹ = o⁻¹ * x * o by group] at h2
      · intro hx
        exact Z.mul_mem (Z.mul_mem (Z.inv_mem hz0) hx) hz0
    have hx : x ∈ Z' ↔ z0⁻¹ * (o⁻¹ * x * o) * z0 ∈ Z := by
      rw [hconj x, hkconj x]
    exact (hz0iff.symm.trans hx.symm).trans (hmemZ' x)
  set n : Γ := o⁻¹ * t1 with hn_def
  have hn_mem : n ∈ Subgroup.normalizer (Z : Set Γ) := by
    rw [Subgroup.mem_normalizer_iff]
    intro z
    constructor
    · intro hz
      have h1 : t1⁻¹ * (t1 * z * t1⁻¹) * t1 ∈ Z := by
        rwa [show t1⁻¹ * (t1 * z * t1⁻¹) * t1 = z by group]
      have h2 : o⁻¹ * (t1 * z * t1⁻¹) * o ∈ Z := (hkey (t1 * z * t1⁻¹)).mpr h1
      convert h2 using 1
      rw [hn_def]
      group
    · intro hz
      have h2 : o⁻¹ * (t1 * z * t1⁻¹) * o ∈ Z := by
        convert hz using 1
        rw [hn_def]
        group
      have h1 : t1⁻¹ * (t1 * z * t1⁻¹) * t1 ∈ Z := (hkey (t1 * z * t1⁻¹)).mp h2
      rwa [show t1⁻¹ * (t1 * z * t1⁻¹) * t1 = z by group] at h1
  refine ⟨n, hn_mem, fun z hz => ?_⟩
  have hmem : n * z * n⁻¹ ∈ Z := (Subgroup.mem_normalizer_iff.mp hn_mem z).mp hz
  have hnq : QuotientGroup.mk' O n = t := by
    rw [hn_def, map_mul, map_inv]
    have ho1 : QuotientGroup.mk' O o = 1 := (QuotientGroup.eq_one_iff (N := O) o).mpr ho
    rw [ho1, inv_one, one_mul, ht1]
  have hq : QuotientGroup.mk' O (n * z * n⁻¹) = (QuotientGroup.mk' O z)⁻¹ := by
    rw [map_mul, map_mul, map_inv, hnq]
    exact h z hz
  have hO_mem : (n * z * n⁻¹) * z ∈ O := by
    refine (QuotientGroup.eq_one_iff (N := O) ((n * z * n⁻¹) * z)).mp ?_
    show QuotientGroup.mk' O ((n * z * n⁻¹) * z) = 1
    rw [map_mul, hq, inv_mul_cancel]
  have hbot : (n * z * n⁻¹) * z ∈ (⊥ : Subgroup Γ) := by
    have : (n * z * n⁻¹) * z ∈ Z ⊓ O :=
      Subgroup.mem_inf.mpr ⟨Z.mul_mem hmem hz, hO_mem⟩
    rwa [hZo] at this
  exact mul_eq_one_iff_eq_inv.mp (Subgroup.mem_bot.mp hbot)

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8
