module

public import CFSG.RankThree.PartTwo.Sec6.Item611Res6ProofField
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PSL2OddInnerFixingKleinFour
import CFSG.RankThree.PartTwo.KFacts.K72FieldKind
import CFSG.RankThree.PartTwo.Sec4.ProjSLEquiv
import CFSG.RankThree.PartTwo.Sec6.Item612Local

public section

namespace CFSG.RankThree.PartTwo.Sec6

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec4
open CFSG.Assembly.RankThreeEven (projSL projSU)


namespace Res611Res6

variable {G : Type} [Group G]

theorem exists_two_ne_one_of_card_four {T : Subgroup G} (hT4 : Nat.card T = 4) :
    ∃ t₁ ∈ T, ∃ t₂ ∈ T, t₁ ≠ 1 ∧ t₂ ≠ 1 ∧ t₁ ≠ t₂ := by
  by_contra h
  push Not at h
  have : Finite T := Nat.finite_of_card_ne_zero (by rw [hT4]; norm_num)
  obtain ⟨t₀, ht₀, ht₀1⟩ : ∃ t₀ ∈ T, t₀ ≠ 1 := by
    by_contra h'
    push Not at h'
    have hbot : T = ⊥ := (Subgroup.eq_bot_iff_forall T).mpr h'
    rw [hbot, Subgroup.card_bot] at hT4
    norm_num at hT4
  have hsub : (T : Set G) ⊆ {1, t₀} := by
    intro x hx
    by_cases hx1 : x = 1
    · exact Or.inl hx1
    · exact Or.inr (h x hx t₀ ht₀ hx1 ht₀1)
  have hle := Set.ncard_le_ncard hsub (Set.toFinite _)
  rw [← Nat.card_coe_set_eq, SetLike.coe_sort_coe, hT4] at hle
  have h2 : ({1, t₀} : Set G).ncard ≤ 2 := by
    have := Set.ncard_insert_le (1 : G) ({t₀} : Set G)
    rwa [Set.ncard_singleton] at this
  omega

end Res611Res6

open Res611Res6

section Certs


theorem item611FieldL2DField_holds (h45 : Sec4.Item4_5) : Item611FieldL2DField := by
  intro G _ _ hst A hA hrank c hcA hc1 L hL hCA E hE hLE T hT hTL hTθ he hcE d hd hdc
  obtain ⟨-, -, m, hm, ⟨φ⟩, -⟩ := he
  set K := GaloisField 3 (3 * m) with hK
  set e' : L ⧸ aschbacherSolvableCore 3 L ≃* GorensteinWalter.PSL2 K :=
    φ.trans (Sec4.projSLEquivPSL K) with he'
  have hdA : d ∈ A := hE.2 hd.1
  have hdN : d ∈ Subgroup.normalizer (L : Set G) :=
    le_normalizer_of_mem_thetaComponentsAt h45 hst.toTheoremFourHyp hA.1.1 hcA hc1 L hL.1 hdA
  have hd3 : d ^ 3 = 1 := hA.1.1.2 d hdA
  set σ := thetaQuotMulAut L (compAction L ⟨d, hdN⟩) with hσ
  have hσ3 : σ ^ 3 = 1 := by
    have h1 : (⟨d, hdN⟩ : Subgroup.normalizer (L : Set G)) ^ 3 = 1 := Subtype.ext hd3
    rw [hσ, ← map_pow, ← map_pow, h1, map_one, map_one]
  have hσT : ∀ (t : G) (ht : t ∈ T),
      σ ((⟨t, hTL ht⟩ : L) : L ⧸ aschbacherSolvableCore 3 L) =
        ((⟨t, hTL ht⟩ : L) : L ⧸ aschbacherSolvableCore 3 L) := by
    intro t ht
    rw [hσ, thetaQuotMulAut_mk]
    congr 1
    apply Subtype.ext
    rw [compAction, normalizerMonoidHom_apply_coe]
    have hdt : d * t = t * d := Subgroup.mem_centralizer_iff.mp hd.2 t ht |>.symm
    rw [hdt, mul_inv_cancel_right]
  have himg : ∀ (t : G) (ht : t ∈ T),
      ((⟨t, hTL ht⟩ : L) : L ⧸ aschbacherSolvableCore 3 L) = 1 → t = 1 := by
    intro t ht h1
    rw [QuotientGroup.eq_one_iff] at h1
    have hmem : t ∈ T ⊓ inSubgroup (aschbacherSolvableCore 3) L := ⟨ht, ⟨_, h1, rfl⟩⟩
    rw [hTθ, Subgroup.mem_bot] at hmem
    exact hmem
  obtain ⟨hEN, hTab, hT4⟩ := mem_fourGroups_iff.mp hT.1
  obtain ⟨t₁, ht₁, t₂, ht₂, ht₁1, ht₂1, ht₁₂⟩ := exists_two_ne_one_of_card_four hT4
  set x₁ : L ⧸ aschbacherSolvableCore 3 L := QuotientGroup.mk (⟨t₁, hTL ht₁⟩ : L) with hx₁
  set x₂ : L ⧸ aschbacherSolvableCore 3 L := QuotientGroup.mk (⟨t₂, hTL ht₂⟩ : L) with hx₂
  have hx₁1 : x₁ ≠ 1 := fun h => ht₁1 (himg t₁ ht₁ h)
  have hx₂1 : x₂ ≠ 1 := fun h => ht₂1 (himg t₂ ht₂ h)
  have hx₁₂ : x₁ ≠ x₂ := by
    intro h
    apply ht₁₂
    have h' : ((⟨t₁ * t₂⁻¹, hTL (T.mul_mem ht₁ (T.inv_mem ht₂))⟩ : L) :
        L ⧸ aschbacherSolvableCore 3 L) = 1 := by
      have : ((⟨t₁ * t₂⁻¹, hTL (T.mul_mem ht₁ (T.inv_mem ht₂))⟩ : L) :
          L ⧸ aschbacherSolvableCore 3 L) = x₁ * x₂⁻¹ := rfl
      rw [this, h, mul_inv_cancel]
    have := himg _ (T.mul_mem ht₁ (T.inv_mem ht₂)) h'
    exact mul_inv_eq_one.mp this
  have hsq : ∀ (t : G) (ht : t ∈ T),
      ((⟨t, hTL ht⟩ : L) : L ⧸ aschbacherSolvableCore 3 L) ^ 2 = 1 := by
    intro t ht
    have h2 : t ^ 2 = 1 := hTab.2 t ht
    rw [← QuotientGroup.mk_pow]
    have : (⟨t, hTL ht⟩ : L) ^ 2 = 1 := Subtype.ext (by simpa using h2)
    rw [this, QuotientGroup.mk_one]
  have hcomm : Commute x₁ x₂ := by
    have h := hTab.1.is_comm.comm ⟨t₁, ht₁⟩ ⟨t₂, ht₂⟩
    have h' : t₁ * t₂ = t₂ * t₁ := congrArg Subtype.val h
    change ((⟨t₁, hTL ht₁⟩ : L) : L ⧸ aschbacherSolvableCore 3 L) *
        ((⟨t₂, hTL ht₂⟩ : L) : _) = ((⟨t₂, hTL ht₂⟩ : L) : _) * ((⟨t₁, hTL ht₁⟩ : L) : _)
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
    congr 1
    exact Subtype.ext h'
  have hout : Sec4.InducesOuterTheta d L := by
    refine ⟨hdN, fun ⟨y, hy⟩ => ?_⟩
    change MulAut.conj y = σ at hy
    have hcard : GorensteinWalter.IsOddPrimePower (Nat.card K) := by
      refine ⟨3, 3 * m, Nat.prime_three, by decide, by omega, ?_⟩
      rw [hK, GaloisField.card 3 (3 * m) (by omega)]
    set ψ : MulAut (GorensteinWalter.PSL2 K) := MulAut.conj (e' y) with hψ
    have hψe : ∀ z, ψ (e' z) = e' (σ z) := by
      intro z
      rw [← hy, hψ, MulAut.conj_apply, MulAut.conj_apply, map_mul, map_mul, map_inv]
    have hψ3 : ψ ^ 3 = 1 := by
      ext z
      obtain ⟨w, rfl⟩ := e'.surjective z
      have h1 : (ψ ^ 3) (e' w) = e' ((σ ^ 3) w) := by
        rw [pow_succ, pow_succ, pow_one, MulAut.mul_apply, MulAut.mul_apply, hψe, hψe, hψe,
          pow_succ, pow_succ, pow_one, MulAut.mul_apply, MulAut.mul_apply]
      rw [h1, hσ3, MulAut.one_apply, MulAut.one_apply]
    have hψ1 := GorensteinWalter.psl2_odd_inner_fixing_commuting_involutions_eq_one K hcard ψ 3
      (by decide) hψ3 (e' x₁) (e' x₂)
      ⟨(map_ne_one_iff e' e'.injective).mpr hx₁1, by rw [← map_pow, hsq t₁ ht₁, map_one]⟩
      ⟨(map_ne_one_iff e' e'.injective).mpr hx₂1, by rw [← map_pow, hsq t₂ ht₂, map_one]⟩
      (fun h => hx₁₂ (e'.injective h)) (hcomm.map e')
      (by rw [hψe, hσT t₁ ht₁]) (by rw [hψe, hσT t₂ ht₂]) ⟨e' y, rfl⟩
    have hσ1 : σ = 1 := by
      ext z
      have h1 := congrArg (fun α : MulAut (GorensteinWalter.PSL2 K) => α (e' z)) hψ1
      simp only [hψe, MulAut.one_apply] at h1
      rw [MulAut.one_apply]
      exact e'.injective h1
    have hdC : d ∈ thetaQuotCentralizer L := ⟨⟨d, hdN⟩, hσ1, rfl⟩
    have : d ∈ A ⊓ thetaQuotCentralizer L := ⟨hdA, hdC⟩
    rw [hCA] at this
    exact hdc this
  have hfield := KFacts.inducesKind_field_of_pow_three L hd3 hout e'
  exact KFacts.InducesStdKind.psl2 K ⟨e', hfield⟩

end Certs

end CFSG.RankThree.PartTwo.Sec6
