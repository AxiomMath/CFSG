module

public import CFSG.RankThree.PartTwo.Sec17.Item1721StepsProofDefs
import CFSG.RankThree.PartTwo.KFacts.KP2Alternating7
import CFSG.RankThree.PartTwo.KFacts.KP4

public section

namespace CFSG.RankThree.PartTwo.Sec17

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
  CFSG.RankThree.PartTwo.Sec13

@[expose] def KS1721InvertL3 : Prop :=
  ∀ (X : Type) [Group X] [Finite X], IsLThreePi X →
    ∀ E : Subgroup X, Nat.card E = 9 → (∀ x ∈ E, x ^ 3 = 1) → ¬ 27 ∣ Nat.card X →
      ∃ g ∈ Subgroup.normalizer (E : Set X), ∀ x ∈ E, g * x * g⁻¹ = x⁻¹

namespace Proof1721

theorem mem_normalizer_of_conj_eq_inv {X : Type*} [Group X] [Finite X] {E : Subgroup X} {g : X}
    (hg : ∀ x ∈ E, g * x * g⁻¹ = x⁻¹) : g ∈ Subgroup.normalizer (E : Set X) :=
  Subgroup.mem_normalizer_fintype fun x hx => by
    rw [SetLike.mem_coe, hg x hx]
    exact inv_mem hx

theorem ks1721Invert_alt7 {X : Type} [Group X] [Finite X]
    (hX : Nonempty (X ≃* alternatingGroup (Fin 7))) {E : Subgroup X} (hE9 : Nat.card E = 9) :
    ∃ g ∈ Subgroup.normalizer (E : Set X), ∀ x ∈ E, g * x * g⁻¹ = x⁻¹ := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨φ⟩ := hX
  set A7 := alternatingGroup (Fin 7) with hA7
  set P : Subgroup A7 := KFacts.KP2.eNine.subgroupOf A7 with hP
  have hPcard : Nat.card P = 9 := by
    rw [hP, Nat.card_congr (Subgroup.subgroupOfEquivOfLe KFacts.KP2.eNine_le_alternatingGroup
      ).toEquiv]
    exact KFacts.KP2.card_eNine
  have hfac : Nat.card P = 3 ^ (Nat.card A7).factorization 3 := by
    rw [hPcard, hA7, nat_card_alternatingGroup, Nat.card_eq_fintype_card, Fintype.card_fin,
      Asc83Table.factorization_eq_of_eq Nat.prime_three (show Nat.factorial 7 / 2 = 3 ^ 2 * 280
        by decide) (by norm_num)]
    norm_num
  set B : Subgroup A7 := E.map φ.toMonoidHom with hB
  have hBcard : Nat.card B = 9 := by rw [hB, Subgroup.card_map_of_injective φ.injective, hE9]
  have hB3 : IsPGroup 3 B := IsPGroup.of_card (n := 2) (by rw [hBcard]; norm_num)
  obtain ⟨m, hm⟩ := Asc83Table.exists_map_conj_le hfac hB3
  set t : A7 := ⟨KFacts.KP2.tInv, KFacts.KP2.tInv_mem_alternatingGroup⟩ with ht
  have htP : ∀ y ∈ P, t * y * t⁻¹ = y⁻¹ := fun y hy => Subtype.ext
    (KFacts.KP2.tInv_conj_eq_inv (Subgroup.mem_subgroupOf.mp hy))
  set u : A7 := m⁻¹ * t * m with hu
  refine ⟨φ.symm u, mem_normalizer_of_conj_eq_inv fun x hx => ?_, fun x hx => ?_⟩ <;>
  · have hφx : φ x ∈ B := ⟨x, hx, rfl⟩
    have hmx : m * φ x * m⁻¹ ∈ P := hm ⟨φ x, hφx, rfl⟩
    have h1 : u * φ x * u⁻¹ = (φ x)⁻¹ := by
      calc u * φ x * u⁻¹ = m⁻¹ * (t * (m * φ x * m⁻¹) * t⁻¹) * m := by rw [hu]; group
        _ = m⁻¹ * (m * φ x * m⁻¹)⁻¹ * m := by rw [htP _ hmx]
        _ = (φ x)⁻¹ := by group
    apply φ.injective
    rw [map_mul, map_mul, map_inv, map_inv, MulEquiv.apply_symm_apply, h1]

theorem ks1721Invert_m22 {X : Type} [Group X] [Finite X]
    (hX : Nonempty (X ≃* CFSG.Blueprint.NativeSporadic.M22)) {E : Subgroup X}
    (hE9 : Nat.card E = 9) :
    ∃ g ∈ Subgroup.normalizer (E : Set X), ∀ x ∈ E, g * x * g⁻¹ = x⁻¹ := by
  obtain ⟨ψ, hψ⟩ := KFacts.KP4.exists_equiv_P0 hX hE9
  set t := Asc83Table.M22.GI ^ 2 with ht
  have htX : t * Asc83Table.M22.X * t⁻¹ = Asc83Table.M22.X⁻¹ := by
    have h1 := Asc83Table.M22.GI_X
    have h2 := Asc83Table.M22.GI_Y
    rw [pow_zero, one_mul, pow_one] at h1
    rw [pow_zero, mul_one] at h2
    calc t * Asc83Table.M22.X * t⁻¹ =
          Asc83Table.M22.GI * (Asc83Table.M22.GI * Asc83Table.M22.X * Asc83Table.M22.GI⁻¹) *
            Asc83Table.M22.GI⁻¹ := by rw [ht, sq]; group
      _ = Asc83Table.M22.X ^ 2 := by rw [h1, h2]
      _ = Asc83Table.M22.X⁻¹ := by
          rw [eq_inv_iff_mul_eq_one, ← pow_succ, Asc83Table.M22.X_cube]
  have htY : t * Asc83Table.M22.Y * t⁻¹ = Asc83Table.M22.Y⁻¹ := by
    have h1 := Asc83Table.M22.GI_X
    have h2 := Asc83Table.M22.GI_Y
    rw [pow_zero, one_mul, pow_one] at h1
    rw [pow_zero, mul_one] at h2
    calc t * Asc83Table.M22.Y * t⁻¹ =
          Asc83Table.M22.GI * (Asc83Table.M22.GI * Asc83Table.M22.Y * Asc83Table.M22.GI⁻¹) *
            Asc83Table.M22.GI⁻¹ := by rw [ht, sq]; group
      _ = (Asc83Table.M22.GI * Asc83Table.M22.X * Asc83Table.M22.GI⁻¹) ^ 2 := by
          rw [h2, conj_pow]
      _ = Asc83Table.M22.Y ^ 2 := by rw [h1]
      _ = Asc83Table.M22.Y⁻¹ := by
          rw [eq_inv_iff_mul_eq_one, ← pow_succ, Asc83Table.M22.Y_cube]
  have hcomm := Asc83Table.M22.XY_comm
  have htP : ∀ y ∈ KFacts.KP4.P0, t * y * t⁻¹ = y⁻¹ := by
    intro y hy
    induction hy using Subgroup.closure_induction with
    | mem z hz =>
      rcases hz with rfl | rfl
      · exact htX
      · exact htY
    | one => simp
    | mul z w hz hw ihz ihw =>
      have hzw : Commute z w := by
        have hab := (Subgroup.closure_le_centralizer_centralizer
          ({Asc83Table.M22.E.a, Asc83Table.M22.E.b} : Set _))
        have hzC := hab hz
        have hwC := hab hw
        refine (Subgroup.mem_centralizer_iff.mp hzC w ?_).symm
        exact (Subgroup.closure_le (K := Subgroup.centralizer
          ({Asc83Table.M22.E.a, Asc83Table.M22.E.b} : Set _))).mpr (by
            rintro _ (rfl | rfl)
            · exact Subgroup.mem_centralizer_iff.mpr fun s hs => by
                rcases hs with rfl | rfl
                · rfl
                · exact hcomm.eq.symm
            · exact Subgroup.mem_centralizer_iff.mpr fun s hs => by
                rcases hs with rfl | rfl
                · exact hcomm.eq
                · rfl) hw
      calc t * (z * w) * t⁻¹ = (t * z * t⁻¹) * (t * w * t⁻¹) := by group
        _ = z⁻¹ * w⁻¹ := by rw [ihz, ihw]
        _ = (z * w)⁻¹ := by rw [mul_inv_rev, (Commute.inv_inv hzw).eq]
    | inv z hz ihz =>
      calc t * z⁻¹ * t⁻¹ = (t * z * t⁻¹)⁻¹ := by group
        _ = z⁻¹⁻¹ := by rw [ihz]
  refine ⟨ψ t, mem_normalizer_of_conj_eq_inv fun x hx => ?_, fun x hx => ?_⟩ <;>
  · rw [← hψ] at hx
    obtain ⟨y, hy, rfl⟩ := hx
    rw [MulEquiv.coe_toMonoidHom, ← map_mul, ← map_inv, ← map_mul, htP y hy, map_inv]

end Proof1721

open Proof1721 in
theorem ks1721Invert_of (hL3 : KS1721InvertL3) :
    KS1721Invert := by
  intro X _ _ htype E hE9 hE3 h27
  rcases htype with hL | hA7 | hM22
  · exact hL3 X hL E hE9 hE3 h27
  · exact ks1721Invert_alt7 hA7 hE9
  · exact ks1721Invert_m22 hM22 hE9

end CFSG.RankThree.PartTwo.Sec17
