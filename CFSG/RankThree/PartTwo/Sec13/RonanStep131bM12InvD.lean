module

public import CFSG.RankThree.PartTwo.Sec13.RonanStep131bM12InvPlan
import CFSG.RankThree.PartTwo.Sec13.RonanStep131bM12InvTools
import CFSG.LocalAnalysis.SignalizerFunctor.InvariantSylowAmbient

public section

namespace CFSG.RankThree.PartTwo.Sec13.RonanStep131b

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo

open M12Inv in
theorem invPartD_holds : InvPartD := by
  classical
  intro G _ _ E Y b hEe hE27 hEY hbY hbE hdec V hV1 hV2 hBV
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hE3 : IsPGroup 3 E := fun g => ⟨1, Subtype.ext (by simpa using hEe.2 g g.2)⟩
  set N := aschbacherSolvableCore 3 Y with hN
  set π := QuotientGroup.mk' N with hπ
  set T := V.comap π with hT
  set T' := T.map Y.subtype with hT'
  have hTcard : Nat.card T = Nat.card N * Nat.card V :=
    QuotientGroup.card_preimage_mk N (V : Set (Y ⧸ N))
  obtain ⟨k, hk⟩ := hV2.exists_card_eq
  have hk0 : k ≠ 0 := by
    rintro rfl
    exact hV1 (Subgroup.card_eq_one.mp (by rw [hk, pow_zero]))
  have hT'card : Nat.card T' = Nat.card N * 2 ^ k := by
    rw [hT', Subgroup.card_map_of_injective Y.subtype_injective, hTcard, hk]
  have hcop : Nat.Coprime 3 (Nat.card T') := by
    rw [hT'card]
    exact Nat.Coprime.mul_right ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2
      three_not_dvd_card_aschbacherSolvableCore) (Nat.Coprime.pow_right k (by norm_num))
  have h2 : 2 ∣ Nat.card T' := by
    rw [hT'card]
    exact Dvd.dvd.mul_left (dvd_pow_self 2 hk0) _
  have hKb : (E ⊓ Y : Subgroup G) ≤ Subgroup.centralizer ({b} : Set G) := fun x hx =>
    Subgroup.mem_centralizer_singleton_iff.mpr (hbY x hx.2)
  have hEN : E ≤ Subgroup.normalizer (T' : Set G) := by
    intro e he
    refine Subgroup.mem_normalizer_fintype fun x hx => ?_
    obtain ⟨y, hy, rfl⟩ := hx
    have he' : e ∈ Subgroup.zpowers b ⊔ (E ⊓ Y) := hdec ▸ he
    obtain ⟨i, z, hz, rfl⟩ := exists_zpow_mul_of_mem_zpowers_sup' hKb he'
    have hzY : z ∈ Y := hz.2
    have hz'B : π ⟨z, hzY⟩ ∈ ((E ⊓ Y).subgroupOf Y).map π :=
      Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr hz)
    have hyV : π y ∈ V := hy
    have hconjV : π ⟨z, hzY⟩ * π y * (π ⟨z, hzY⟩)⁻¹ ∈ V :=
      (Subgroup.mem_normalizer_iff.mp (hBV hz'B) (π y)).mp hyV
    refine ⟨⟨z, hzY⟩ * y * ⟨z, hzY⟩⁻¹, ?_, ?_⟩
    · show π (⟨z, hzY⟩ * y * ⟨z, hzY⟩⁻¹) ∈ V
      rw [map_mul, map_mul, map_inv]
      exact hconjV
    ·
      have hcomm : (b ^ i) * ((z * (y : G) * z⁻¹)) = (z * (y : G) * z⁻¹) * b ^ i := by
        have : Commute b (z * (y : G) * z⁻¹) :=
          (hbY _ (Y.mul_mem (Y.mul_mem hzY y.2) (Y.inv_mem hzY))).symm
        exact (this.zpow_left i).eq
      calc ((⟨z, hzY⟩ * y * ⟨z, hzY⟩⁻¹ : Y) : G) = z * (y : G) * z⁻¹ := rfl
        _ = (b ^ i * z) * (y : G) * (b ^ i * z)⁻¹ := by
          have h1 : (b ^ i * z) * (y : G) * (b ^ i * z)⁻¹ =
              b ^ i * (z * (y : G) * z⁻¹) * (b ^ i)⁻¹ := by group
          rw [h1, hcomm]
          group
  obtain ⟨S, hSN, hS1⟩ :=
    CFSG.SignalizerFunctor.Helpers.normalized_subgroup_invariant_sylow_nontrivial
      3 2 Nat.prime_three Nat.prime_two E T' hE3 hEN hcop h2
  exact ⟨hEe, hE27, _, hS1, S.isPGroup'.map _, hSN⟩

end CFSG.RankThree.PartTwo.Sec13.RonanStep131b
