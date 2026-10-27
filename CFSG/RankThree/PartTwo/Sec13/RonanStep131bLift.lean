module

public import CFSG.RankThree.PartTwo.Sec13.RonanStep131bNorm2e
import CFSG.LocalAnalysis.SignalizerFunctor.InvariantSylowAmbient

public section

namespace CFSG.RankThree.PartTwo.Sec13.RonanStep131b

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo

theorem partTwoE_of_norm2e {G : Type} [Group G] [Finite G] {E Y : Subgroup G} {b : G}
    (hEe : CFSG.Assembly.IsElemAbelian 3 E) (hE27 : Nat.card E = 27) (hbE : b ∈ E)
    (hb1 : b ≠ 1) (hbY : b ∈ Sec4.thetaQuotCentralizer Y)
    (hEY : E ≤ Subgroup.normalizer (Y : Set G))
    (h : Norm2e (Y ⧸ aschbacherSolvableCore 3 Y)) : E ∈ partTwoE G := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hE3 : IsPGroup 3 E := fun g => ⟨1, Subtype.ext (by simpa using hEe.2 g g.2)⟩
  set P := Sec4.autThetaQuot E Y with hPdef
  have hPexp : ∀ τ ∈ P, τ ^ 3 = 1 := by
    intro τ hτ
    obtain ⟨x, hN, hxe, hτ'⟩ := Sec4.mem_autThetaQuot_iff.mp hτ
    have hx3 : (⟨x, hN⟩ : Subgroup.normalizer (Y : Set G)) ^ 3 = 1 :=
      Subtype.ext (by simpa using hEe.2 x hxe)
    rw [← hτ', ← map_pow, ← map_pow, hx3, map_one, map_one]
  have hP3 : IsPGroup 3 P := fun τ => ⟨1, Subtype.ext (by simpa using hPexp τ τ.2)⟩
  have hcard := Sec13.card_inf_mul_card_autThetaQuot hEY
  rw [hE27] at hcard
  have hb' : b ∈ E ⊓ Sec4.thetaQuotCentralizer Y := ⟨hbE, hbY⟩
  have h3le : 3 ≤ Nat.card (E ⊓ Sec4.thetaQuotCentralizer Y : Subgroup G) := by
    have hb3 : orderOf b = 3 := orderOf_eq_prime (hEe.2 b hbE) hb1
    have hd := Subgroup.card_dvd_of_le (Subgroup.zpowers_le.mpr hb')
    rw [Nat.card_zpowers, hb3] at hd
    exact Nat.le_of_dvd Nat.card_pos hd
  have hP9 : Nat.card P ≤ 9 := by
    by_contra hgt
    push Not at hgt
    nlinarith
  obtain ⟨V, hV1, hV2, hV⟩ := h P hP3 hPexp hP9
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
  have hEN : E ≤ Subgroup.normalizer (T' : Set G) := by
    intro e he
    refine Subgroup.mem_normalizer_fintype fun x hx => ?_
    obtain ⟨y, hy, rfl⟩ := hx
    have heN := hEY he
    have hσP : Sec4.thetaQuotMulAut Y (Y.normalizerMonoidHom ⟨e, heN⟩) ∈ P :=
      Sec4.mem_autThetaQuot_iff.mpr ⟨e, heN, he, rfl⟩
    have hVσ := hV _ hσP
    have hyV : π y ∈ V := hy
    have hmem : π (Y.normalizerMonoidHom ⟨e, heN⟩ y) ∈ V := by
      have h1 : π (Y.normalizerMonoidHom ⟨e, heN⟩ y) =
          Sec4.thetaQuotMulAut Y (Y.normalizerMonoidHom ⟨e, heN⟩) (π y) := by
        rw [hπ, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply]
        exact (Sec4.thetaQuotMulAut_mk _ _).symm
      rw [h1]
      have h2' : Sec4.thetaQuotMulAut Y (Y.normalizerMonoidHom ⟨e, heN⟩) (π y) ∈
          V.map (Sec4.thetaQuotMulAut Y (Y.normalizerMonoidHom ⟨e, heN⟩)).toMonoidHom :=
        ⟨π y, hyV, rfl⟩
      rwa [hVσ] at h2'
    exact ⟨Y.normalizerMonoidHom ⟨e, heN⟩ y, hmem, Sec4.normalizerMonoidHom_apply_coe heN y⟩
  obtain ⟨S, hSN, hS1⟩ :=
    CFSG.SignalizerFunctor.Helpers.normalized_subgroup_invariant_sylow_nontrivial
      3 2 Nat.prime_three Nat.prime_two E T' hE3 hEN hcop h2
  exact ⟨hEe, hE27, _, hS1, S.isPGroup'.map _, hSN⟩

end CFSG.RankThree.PartTwo.Sec13.RonanStep131b
