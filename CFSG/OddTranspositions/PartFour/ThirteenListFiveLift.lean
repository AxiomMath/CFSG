module

public import Mathlib.LinearAlgebra.Matrix.ProjectiveSpecialLinearGroup
import CFSG.Quasithin.Background.KnownMultL2
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PSL2PerfectOfCard

public section

namespace CFSG.OddTranspositions.PartFour.ListFive

open scoped commutatorElement Pointwise

private theorem commutatorElement_mul_center {X : Type} [Group X] {a b z w : X}
    (hz : z ∈ Subgroup.center X) (hw : w ∈ Subgroup.center X) : ⁅a * z, b * w⁆ = ⁅a, b⁆ := by
  have hz' := Subgroup.mem_center_iff.mp hz
  have hw' := Subgroup.mem_center_iff.mp hw
  rw [commutatorElement_def, commutatorElement_def]
  calc a * z * (b * w) * (a * z)⁻¹ * (b * w)⁻¹
      = a * (z * b) * (w * z⁻¹) * a⁻¹ * w⁻¹ * b⁻¹ := by group
    _ = a * (b * z) * (z⁻¹ * w) * a⁻¹ * w⁻¹ * b⁻¹ := by
        rw [hz' b, ← Subgroup.mem_center_iff.mp (Subgroup.inv_mem _ hz) w]
    _ = a * b * (w * a⁻¹) * w⁻¹ * b⁻¹ := by group
    _ = a * b * (a⁻¹ * w) * w⁻¹ * b⁻¹ := by rw [hw' a⁻¹]
    _ = a * b * a⁻¹ * b⁻¹ := by group

private theorem eq_one_of_mul_self_of_mem_center {X : Type} [Group X] [Finite X]
    (hZ : Odd (Nat.card (Subgroup.center X))) {x : X} (hx : x ∈ Subgroup.center X)
    (h2 : x * x = 1) : x = 1 := by
  have hdvd2 : orderOf x ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [pow_two, h2])
  have hdvdZ : orderOf x ∣ Nat.card (Subgroup.center X) := by
    rw [← Subgroup.orderOf_mk x hx]
    exact orderOf_dvd_natCard _
  have h1 : orderOf x = 1 := by
    rcases (Nat.dvd_prime Nat.prime_two).mp hdvd2 with h | h
    · exact h
    · rw [h] at hdvdZ
      exact absurd (even_iff_two_dvd.mpr hdvdZ) (Nat.not_even_iff_odd.mpr hZ)
  exact orderOf_eq_one_iff.mp h1

theorem exists_lift_of_psl_two {X : Type} [Group X] [Finite X]
    (hZ : Odd (Nat.card (Subgroup.center X))) {s : X} (hs : s * s = 1)
    {K : Type} [Field K] [Finite K] {p f : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    (hK : Nat.card K = p ^ f) (h9 : p ^ f ≠ 9) (h3 : 3 < Nat.card K)
    (C : Subgroup (X ⧸ Subgroup.center X))
    (eC : C ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 2) K)
    (hsC : (QuotientGroup.mk s : X ⧸ Subgroup.center X) ∈ Subgroup.normalizer C) :
    ∃ L : Subgroup X, s ∈ L ∧ L ⊓ Subgroup.center X = ⊥ ∧
      L.map (QuotientGroup.mk' (Subgroup.center X)) =
        C ⊔ Subgroup.zpowers (QuotientGroup.mk s) := by
  classical
  set π := QuotientGroup.mk' (Subgroup.center X) with hπdef
  have hπs : Function.Surjective π := QuotientGroup.mk'_surjective _
  have hker : ∀ x : X, π x = 1 ↔ x ∈ Subgroup.center X := fun x => QuotientGroup.eq_one_iff x
  have hCperf : ⁅C, C⁆ = C := by
    haveI := CFSG.GorensteinWalter.psl2_isPerfect_of_card_gt_three K h3
    haveI : Group.IsPerfect C := Group.IsPerfect.ofSurjective (f := eC.symm.toMonoidHom)
      eC.symm.surjective
    exact Subgroup.isPerfect_iff.mp inferInstance
  set N := C.comap π with hN
  set Q : Subgroup X := ⁅N, N⁆ with hQ
  have hNmap : N.map π = C := Subgroup.map_comap_eq_self_of_surjective hπs C
  have hQmap : Q.map π = C := by rw [hQ, Subgroup.map_commutator, hNmap, hCperf]
  have hQperf : ⁅Q, Q⁆ = Q := by
    refine le_antisymm (Subgroup.commutator_le_self Q) ?_
    rw [hQ, Subgroup.commutator_le]
    intro a ha b hb
    have hdec : ∀ y ∈ N, ∃ q ∈ Q, ∃ z ∈ Subgroup.center X, y = q * z := fun y hy => by
      have : π y ∈ Q.map π := hQmap ▸ hy
      obtain ⟨q, hq, hqy⟩ := this
      refine ⟨q, hq, q⁻¹ * y, (hker _).mp (by rw [map_mul, map_inv, hqy, inv_mul_cancel]), ?_⟩
      group
    obtain ⟨q, hq, z, hz, rfl⟩ := hdec a ha
    obtain ⟨q', hq', z', hz', rfl⟩ := hdec b hb
    rw [commutatorElement_mul_center hz hz']
    exact Subgroup.commutator_mem_commutator hq hq'
  have hQZ : Q ⊓ Subgroup.center X = ⊥ := by
    haveI : Group.IsPerfect Q := Subgroup.isPerfect_iff.mpr hQperf
    let ρ₀ : Q →* C := (π.comp Q.subtype).codRestrict C fun q => hQmap ▸ ⟨q, q.2, rfl⟩
    let ρ : Q →* Matrix.ProjectiveSpecialLinearGroup (Fin 2) K := eC.toMonoidHom.comp ρ₀
    have hρ : Function.Surjective ρ := by
      intro g
      obtain ⟨q, hq, hqc⟩ : ((eC.symm g : C) : X ⧸ Subgroup.center X) ∈ Q.map π :=
        hQmap.symm ▸ (eC.symm g).2
      refine ⟨⟨q, hq⟩, ?_⟩
      have : ρ₀ ⟨q, hq⟩ = eC.symm g := Subtype.ext hqc
      simp only [ρ, MonoidHom.comp_apply, this, MulEquiv.coe_toMonoidHom, MulEquiv.apply_symm_apply]
    have hρker : ∀ q : Q, ρ q = 1 ↔ (q : X) ∈ Subgroup.center X := fun q => by
      simp only [ρ, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, EmbeddingLike.map_eq_one_iff]
      rw [← hker]
      exact ⟨fun h => congrArg Subtype.val h, fun h => Subtype.ext h⟩
    have hρZ : ρ.ker ≤ Subgroup.center Q := fun q hq =>
      Subgroup.mem_center_iff.mpr fun r => Subtype.ext
        (Subgroup.mem_center_iff.mp ((hρker q).mp hq) r)
    have h2 := CFSG.Quasithin.isPGroup_two_ker_psl_two_odd hp2 hK h9 ρ hρ hρZ
    rw [eq_bot_iff]
    intro x hx
    obtain ⟨hxQ, hxZ⟩ := Subgroup.mem_inf.mp hx
    have hxk : (⟨x, hxQ⟩ : Q) ∈ ρ.ker := (hρker _).mpr hxZ
    obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.mp h2) ⟨⟨x, hxQ⟩, hxk⟩
    have hox : orderOf x = 2 ^ k := by
      rw [← hk, Subgroup.orderOf_mk, Subgroup.orderOf_mk]
    have hdvdZ : orderOf x ∣ Nat.card (Subgroup.center X) := by
      rw [← Subgroup.orderOf_mk x hxZ]
      exact orderOf_dvd_natCard _
    have hk0 : k = 0 := by
      by_contra hk0
      rw [hox] at hdvdZ
      exact (Nat.not_even_iff_odd.mpr hZ) (even_iff_two_dvd.mpr
        ((dvd_pow_self 2 hk0).trans hdvdZ))
    rw [hk0, pow_zero] at hox
    exact Subgroup.mem_bot.mpr (orderOf_eq_one_iff.mp hox)
  have hsN : s ∈ Subgroup.normalizer N := by
    have h := Subgroup.comap_normalizer_eq_of_le_range (H := C) (f := π)
      (by rw [MonoidHom.range_eq_top_of_surjective _ hπs]; exact le_top)
    rw [← hN] at h
    rw [← h]
    exact hsC
  have hsQ : s ∈ Subgroup.normalizer Q := by
    rw [Subgroup.mem_normalizer_iff_map_conj_eq] at hsN ⊢
    rw [hQ, Subgroup.map_commutator, hsN]
  have hle : Subgroup.zpowers s ≤ Subgroup.normalizer Q := Subgroup.zpowers_le.mpr hsQ
  refine ⟨Q ⊔ Subgroup.zpowers s, Subgroup.mem_sup_right (Subgroup.mem_zpowers s), ?_, ?_⟩
  · rw [eq_bot_iff]
    intro x hx
    obtain ⟨hxL, hxZ⟩ := Subgroup.mem_inf.mp hx
    have hxL' : x ∈ (Q : Set X) * (Subgroup.zpowers s : Set X) := by
      rw [← Subgroup.coe_mul_of_right_le_normalizer_left Q (Subgroup.zpowers s) hle]
      exact hxL
    obtain ⟨q, hq, y, hy, rfl⟩ := hxL'
    have hyy : y * y = 1 := by
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
      rw [← zpow_add, ← two_mul, zpow_mul, show (s ^ (2 : ℤ)) = s * s by
        rw [zpow_two], hs, one_zpow]
    have hyq : y * q * y⁻¹ ∈ Q := (Subgroup.mem_normalizer_iff.mp (hle hy) q).mp hq
    have hsq : q * y * (q * y) ∈ Q := by
      have : q * y * (q * y) = q * (y * q * y⁻¹) * (y * y) := by group
      rw [this, hyy, mul_one]
      exact Q.mul_mem hq hyq
    have hsqZ : q * y * (q * y) ∈ Subgroup.center X := Subgroup.mul_mem _ hxZ hxZ
    have h1 : q * y * (q * y) = 1 := by
      have : q * y * (q * y) ∈ Q ⊓ Subgroup.center X := Subgroup.mem_inf.mpr ⟨hsq, hsqZ⟩
      rw [hQZ] at this
      exact Subgroup.mem_bot.mp this
    exact Subgroup.mem_bot.mpr (eq_one_of_mul_self_of_mem_center hZ hxZ h1)
  · rw [Subgroup.map_sup, hQmap, MonoidHom.map_zpowers]
    rfl

end CFSG.OddTranspositions.PartFour.ListFive
