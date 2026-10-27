module

public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2ExcCommon
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Thm14_5.SmallG2Inv
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Thm14_5.SmallG2Nat
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Thm14_5.SmallRep
import CFSG.Quasithin.Background.SmithB42G2FNat
import CFSG.Quasithin.Background.SmithB42L2Sl2
import CFSG.LocalAnalysis.UniquenessCase.UC22K147Excl
import CFSG.GroupTheory.E3Params
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X7Basic
public import CFSG.Quasithin.Background.SmithB42G2Id

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.Quasithin.F6
open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719
open CFSG.Blueprint (LieModel)
open scoped commutatorElement Pointwise

theorem w135c2_four_le_mQuot_g2
    {W : Type} [CommGroup W] [Finite W] (hW : ∀ w : W, w ^ 2 = 1)
    {Y L : Subgroup (MulAut W)} {t : MulAut W} (hctx : Is135Context Y L) (htY : t ∈ Y)
    (ht2 : orderOf t = 2) {n f : ℕ}
    (hlie : LieModel (↥L ⧸ Subgroup.center ↥L) .G2 n 2 f) :
    4 ≤ E3.mQuot ⊤ (fixV (Subgroup.zpowers t)) := by
  open CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.Thm14_5
    CFSG.Quasithin.Explicit CFSG.QuasithinUnique.Setup.Layer
    CFSG.QuasithinUnique.Setup.Layer.Actor CFSG.QuasithinUnique.Setup.X7b in
  classical
  haveI : Finite (MulAut W) := MulEquiv.finite_left
  have hq : IsQuasisimple ↥L := hctx.2.2.2.2.1
  have : Group.IsPerfect ↥L := hq.1
  have hmodel := CFSG.Blueprint.LieModel.chevalleyExceptionalModel hlie (by decide)
  have hZ : Subgroup.center ↥L = ⊥ := by
    have h0 := CFSG.SectionRank.g2_even_perfect_odd_cover_trivial hmodel
      (QuotientGroup.mk' (Subgroup.center ↥L)) (QuotientGroup.mk'_surjective _)
      (QuotientGroup.ker_mk' _).le
      (by rw [QuotientGroup.ker_mk']; exact w135_odd_card_center hctx)
    rwa [QuotientGroup.ker_mk'] at h0
  obtain ⟨he2, K, hKfield, hKfin, hKchar, hKcard, ⟨χ⟩⟩ :=
    CFSG.Quasithin.B42G2Id.exists_cayleyGroup_of_model_center_eq_bot hZ hmodel
  letI : Field K := hKfield
  letI : CharP K 2 := hKchar
  haveI : Fintype K := Fintype.ofFinite K
  have hF : Fintype.card K = 2 ^ f := by rw [← Nat.card_eq_fintype_card, hKcard]
  obtain ⟨M, _, _, _, ⟨θ⟩⟩ := Actor.exists_binModel_of_binary (V := W) fun v => by
    rw [← pow_two]
    exact hW v
  obtain ⟨hlt, -, -, hirrW⟩ := hctx.2.2.2.2.2
  have hWnt : Nontrivial W := by
    obtain ⟨v, -, hv⟩ := SetLike.exists_of_lt hlt
    exact ⟨⟨v, 1, fun h => hv (h ▸ Subgroup.one_mem _)⟩⟩
  have hMnt : Nontrivial M := by
    obtain ⟨v, hv⟩ := exists_ne (1 : W)
    refine ⟨⟨Multiplicative.toAdd (θ v), 0, fun h => hv ?_⟩⟩
    have h1 : θ v = 1 := Multiplicative.toAdd.injective (by simpa using h)
    simpa using congrArg θ.symm h1
  let π : ↥(cayleyGroup K) →* (M ≃ₗ[ZMod 2] M) :=
    (binPsi θ).toMonoidHom.comp (L.subtype.comp χ.symm.toMonoidHom)
  have hπ : Function.Injective π :=
    (binPsi θ).injective.comp (L.subtype_injective.comp χ.symm.injective)
  have hirrπ : ∀ U : Submodule (ZMod 2) M, (∀ g, ∀ u ∈ U, π g u ∈ U) → U = ⊥ ∨ U = ⊤ :=
    fun U hU => CFSG.Quasithin.B42L2.irr_map θ (fun J hJ => hirrW J hJ bot_le le_top) U (by
      rintro _ ⟨l, hl, rfl⟩ u hu
      have h := hU (χ ⟨l, hl⟩) u hu
      simpa [π] using h)
  set a : M ≃ₗ[ZMod 2] M := binPsi θ t with hadef
  have htt : t * t = 1 := by rw [← pow_two, ← ht2, pow_orderOf_eq_one]
  have ha2 : a * a = 1 := by rw [hadef, ← map_mul, htt, map_one]
  have ha1 : a ≠ 1 := by
    intro h
    have h1 : t = 1 := (binPsi θ).injective (h.trans (map_one _).symm)
    rw [h1, orderOf_one] at ht2
    exact absurd ht2 (by norm_num)
  have hN : t ∈ Subgroup.normalizer (L : Set (MulAut W)) :=
    w135c2_mem_normalizer_of_ctx hctx htY ht2
  have hnorm : ∀ x, ∃ y, a * π x * a⁻¹ = π y := by
    intro x
    have hmem : t * ((χ.symm x : ↥L) : MulAut W) * t⁻¹ ∈ L :=
      (Subgroup.mem_normalizer_iff.mp hN _).mp (χ.symm x).2
    refine ⟨χ ⟨_, hmem⟩, ?_⟩
    simp only [π, hadef, MonoidHom.coe_comp, Function.comp_apply, MulEquiv.coe_toMonoidHom,
      MulEquiv.symm_apply_apply, Subgroup.coe_subtype, map_mul, map_inv]
  have hrk : dispRank a = rkIdx (fixV (Subgroup.zpowers t)) := by
    haveI : Module.Finite (ZMod 2) M := Module.Finite.of_finite
    let t' : ↥Y := ⟨t, htY⟩
    have ht' : orderOf t' = 2 := by rw [Subgroup.orderOf_mk]; exact ht2
    have h1 := finrank_quotient_fixSub_subRep θ Y (Subgroup.zpowers t')
    rw [MonoidHom.map_zpowers,
      CFSG.LocalAnalysis.UniquenessCase.UC22.Excl147.fixSub_zpowers_eq_ker (subRep θ Y) ht']
      at h1
    have h2 := (LinearMap.ker (subRep θ Y t' - 1)).finrank_quotient_add_finrank
    have h3 := LinearMap.finrank_range_add_finrank_ker (a.toLinearMap - 1)
    have hsame : subRep θ Y t' - 1 = a.toLinearMap - 1 := rfl
    rw [hsame] at h1 h2
    have ht'val : (Y.subtype t' : MulAut W) = t := rfl
    rw [ht'val] at h1
    unfold dispRank
    omega
  let ρ : Representation (ZMod 2) ↥(cayleyGroup K) M :=
    LinearEquiv.automorphismGroup.toLinearMapMonoidHom.comp π
  have : Fact ρ.IsIrreducible :=
    ⟨(CFSG.QuasithinUnique.Setup.X7.isIrreducible_iff ρ).2
      ⟨hMnt, fun U hU => hirrπ U hU⟩⟩
  have hntρ : ∃ g, ρ g ≠ 1 := by
    have : Nontrivial ↥(cayleyGroup K) :=
      nontrivial_cayleyGroup (by rw [hKcard]; exact Nat.one_lt_two_pow (by omega))
    obtain ⟨g, hg⟩ := exists_ne (1 : ↥(cayleyGroup K))
    refine ⟨g, fun h => hg (hπ (LinearEquiv.ext fun w => ?_))⟩
    have h1 := LinearMap.congr_fun h w
    simpa [ρ] using h1
  have hdisp : 4 ≤ dispRank a := by
    rcases CFSG.Quasithin.B42G2F.natural_or_large_displacement hF (by omega) hntρ with
      ⟨φ, hφ⟩ | hlarge
    · have h := two_mul_le_dispRank_of_natural hKcard he2 π hπ hirrπ φ hφ a ha2 ha1 hnorm
      omega
    · obtain ⟨z, hz2, hz1, hzr⟩ :=
        exists_involution_dispRank_le_two_mul hF he2 π hπ hMnt hirrπ a ha2 ha1 hnorm
      have h := hlarge z hz2 hz1
      change 3 * f + 2 ≤ dispRank (π z) at h
      omega
  rw [CFSG.GroupTheory.mQuot_top_eq_rkIdx, ← hrk]
  exact hdisp

end CFSG.LocalAnalysis.WeakClosure81
