module

public import Mathlib.GroupTheory.Sylow

public section

namespace CFSG

open scoped Pointwise

namespace FiveTransitive.PGroupSylowSimultaneousCorrection

open MulAction

private theorem exists_normalized_sylow
    {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    (K H : Subgroup G) (hH : IsPGroup p H)
    (hHK : H ≤ Subgroup.normalizer (K : Set G)) :
    ∃ T : Sylow p K,
      H ≤ Subgroup.normalizer (((T : Subgroup K).map K.subtype) : Set G) := by
  let φ : H →* MulAut K := K.normalizerMonoidHom.comp (Subgroup.inclusion hHK)
  let _ : MulDistribMulAction H K := MulDistribMulAction.compHom K φ
  let _ : MulAction H (Sylow p K) := Sylow.pointwiseMulAction
  have hnot : ¬ p ∣ Nat.card (Sylow p K) := by
    have hm : Nat.card (Sylow p K) ≡ 1 [MOD p] := card_sylow_modEq_one p K
    exact fun hd => (Fact.out : p.Prime).not_dvd_one ((hm.dvd_iff (dvd_refl p)).mp hd)
  obtain ⟨T, hT⟩ := hH.nonempty_fixed_point_of_prime_not_dvd_card (Sylow p K) hnot
  refine ⟨T, ?_⟩
  intro h hh
  let hH' : H := ⟨h, hh⟩
  have hmap : (T : Subgroup K).map (φ hH').toMonoidHom = T :=
    congrArg Sylow.toSubgroup (hT hH')
  apply Subgroup.mem_normalizer_iff_map_conj_eq.mpr
  change ((T : Subgroup K).map K.subtype).map (MulAut.conj h).toMonoidHom = _
  rw [Subgroup.map_map]
  have he : (MulAut.conj h).toMonoidHom.comp K.subtype =
      K.subtype.comp (φ hH').toMonoidHom := rfl
  rw [he, ← Subgroup.map_map, hmap]

theorem exists_correction
    {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    (K H : Subgroup G) (hH : IsPGroup p H)
    (hHK : H ≤ Subgroup.normalizer (K : Set G)) (P : Sylow p K) :
    ∃ k : K, ∀ h : H, k.val * h.val * k.val⁻¹ ∈
      Subgroup.normalizer (((P : Subgroup K).map K.subtype) : Set G) := by
  obtain ⟨T, hT⟩ := exists_normalized_sylow K H hH hHK
  obtain ⟨k, hk⟩ := exists_smul_eq K T P
  have hmap : ((T : Subgroup K).map K.subtype).map (MulAut.conj k.val).toMonoidHom =
      (P : Subgroup K).map K.subtype := by
    calc
      _ = ((k • T : Sylow p K) : Subgroup K).map K.subtype := by
        change ((T : Subgroup K).map K.subtype).map (MulAut.conj k.val).toMonoidHom =
          ((T : Subgroup K).map (MulAut.conj k).toMonoidHom).map K.subtype
        rw [Subgroup.map_map, Subgroup.map_map]
        rfl
      _ = _ := by rw [hk]
  refine ⟨k, ?_⟩
  intro h
  have hm : k.val * h.val * k.val⁻¹ ∈
      (Subgroup.normalizer (((T : Subgroup K).map K.subtype) : Set G)).map
        (MulAut.conj k.val).toMonoidHom := ⟨h.val, hT h.property, rfl⟩
  rwa [Subgroup.map_normalizer_eq_of_bijective _ (MulAut.conj k.val).bijective, hmap] at hm

end FiveTransitive.PGroupSylowSimultaneousCorrection

end CFSG
