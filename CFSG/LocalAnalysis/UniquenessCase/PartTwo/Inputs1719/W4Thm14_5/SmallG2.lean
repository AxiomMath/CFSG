module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Thm14_5.SmallRows
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Thm14_5.SmallG2Par
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Thm14_5.SmallG2Inv
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Thm14_5.SmallG2Nat
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Thm14_5.SmallRep
import CFSG.Quasithin.Background.E3MParamAttained
import CFSG.Quasithin.Background.SmithB42G2FNat
import CFSG.Quasithin.Background.SmithB42L2Sl2
import CFSG.LocalAnalysis.UniquenessCase.UC22K147Excl
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X7Basic

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.Thm14_5

open CFSG.Quasithin CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22 Subgroup
open CFSG.QuasithinUnique.Setup.Layer CFSG.Quasithin.Explicit CFSG.QuasithinUnique.Setup.X7b

theorem k14_5SmallFor_g2 :
    K14_5SmallFor fun L _ e => IsG2 L e := by
  intro I _ _ hI X L P e n hLX hLn hq hirr hS hPL hpar hinf hN hn hm
  classical
  exfalso
  have : Finite (MulAut I) :=
    Finite.of_injective (fun f : MulAut I => (f : I → I)) DFunLike.coe_injective
  have hne : n = e := nParam_eq_of_isG2_parabolic hS hPL hpar hinf hN
  obtain ⟨he2, K, _, _, _, hKcard, ⟨χ⟩⟩ :=
    CFSG.Quasithin.B42G2Id.exists_cayleyGroup_of_chevalleyExceptionalModel
      (CFSG.Blueprint.LieModel.chevalleyExceptionalModel hS (by decide))
  have : Fintype K := Fintype.ofFinite K
  have hF : Fintype.card K = 2 ^ e := by rw [← Nat.card_eq_fintype_card, hKcard]
  obtain ⟨W, _, _, _, ⟨θ⟩⟩ := Actor.exists_binModel_of_binary (V := I) fun v => by
    rw [← pow_two]
    exact hI v
  have hirr' := hirr
  obtain ⟨hlt, -, -, hJ⟩ := hirr'
  have : Nontrivial I := by
    obtain ⟨v, -, hv⟩ := SetLike.exists_of_lt hlt
    exact ⟨⟨v, 1, fun h => hv (h ▸ Subgroup.one_mem _)⟩⟩
  have : Nontrivial W := by
    obtain ⟨v, hv⟩ := exists_ne (1 : I)
    refine ⟨⟨Multiplicative.toAdd (θ v), 0, fun h => hv ?_⟩⟩
    have h1 : θ v = 1 := Multiplicative.toAdd.injective (by simpa using h)
    simpa using congrArg θ.symm h1
  let π : ↥(cayleyGroup K) →* (W ≃ₗ[ZMod 2] W) :=
    (binPsi θ).toMonoidHom.comp (L.subtype.comp χ.symm.toMonoidHom)
  have hπ : Function.Injective π :=
    (binPsi θ).injective.comp (L.subtype_injective.comp χ.symm.injective)
  have hirrπ : ∀ U : Submodule (ZMod 2) W, (∀ g, ∀ u ∈ U, π g u ∈ U) → U = ⊥ ∨ U = ⊤ :=
    fun U hU => CFSG.Quasithin.B42L2.irr_map θ (fun J hJ' => hJ J hJ' bot_le le_top) U (by
      rintro _ ⟨l, hl, rfl⟩ u hu
      have h := hU (χ ⟨l, hl⟩) u hu
      simpa [π] using h)
  have hev : Even (Nat.card ↥X) := by
    have h2 : 2 ∣ Nat.card ↥L := by
      rw [Nat.card_congr χ.toEquiv, CFSG.Quasithin.Vol2.KGNat.card_cayleyGroup, hKcard]
      exact dvd_mul_of_dvd_left (dvd_pow (dvd_pow_self 2 (by omega)) (by norm_num)) _
    exact even_iff_two_dvd.2 (h2.trans (Subgroup.card_dvd_of_le hLX))
  obtain ⟨t, htX, ht2, htm⟩ := CFSG.Quasithin.E3.exists_involution_rkIdx_fixV_eq_mParam X hev
  have hXN : X ≤ normalizer (L : Set (MulAut I)) :=
    (normal_subgroupOf_iff_le_normalizer hLX).mp hLn
  set a : W ≃ₗ[ZMod 2] W := binPsi θ t with hadef
  have htt : t * t = 1 := by rw [← pow_two, ← ht2, pow_orderOf_eq_one]
  have ha2 : a * a = 1 := by rw [hadef, ← map_mul, htt, map_one]
  have ha1 : a ≠ 1 := by
    intro h
    have h1 : t = 1 := (binPsi θ).injective (h.trans (map_one _).symm)
    rw [h1, orderOf_one] at ht2
    exact absurd ht2 (by norm_num)
  have hnorm : ∀ x, ∃ y, a * π x * a⁻¹ = π y := by
    intro x
    have hmem : t * ((χ.symm x : ↥L) : MulAut I) * t⁻¹ ∈ L :=
      (Subgroup.mem_normalizer_iff.mp (hXN htX) _).mp (χ.symm x).2
    refine ⟨χ ⟨_, hmem⟩, ?_⟩
    simp only [π, hadef, MonoidHom.coe_comp, Function.comp_apply, MulEquiv.coe_toMonoidHom,
      MulEquiv.symm_apply_apply, Subgroup.coe_subtype, map_mul, map_inv]
  have hrk : dispRank a ≤ e + 1 := by
    have hfin : Module.Finite (ZMod 2) W := Module.Finite.of_finite
    let t' : ↥X := ⟨t, htX⟩
    have ht' : orderOf t' = 2 := by rw [Subgroup.orderOf_mk]; exact ht2
    have h1 := finrank_quotient_fixSub_subRep θ X (zpowers t')
    rw [MonoidHom.map_zpowers, CFSG.LocalAnalysis.UniquenessCase.UC22.Excl147.fixSub_zpowers_eq_ker
      (subRep θ X) ht'] at h1
    have h2 := (LinearMap.ker (subRep θ X t' - 1)).finrank_quotient_add_finrank
    have h3 := LinearMap.finrank_range_add_finrank_ker (a.toLinearMap - 1)
    have hsame : subRep θ X t' - 1 = a.toLinearMap - 1 := rfl
    rw [hsame] at h1 h2
    have h4 : rkIdx (fixV (zpowers (X.subtype t'))) = E3.mParam X := htm
    change Module.finrank (ZMod 2) ↥(LinearMap.range (a.toLinearMap - 1)) ≤ e + 1
    omega
  let ρ : Representation (ZMod 2) ↥(cayleyGroup K) W :=
    LinearEquiv.automorphismGroup.toLinearMapMonoidHom.comp π
  have : Fact ρ.IsIrreducible :=
    ⟨(CFSG.QuasithinUnique.Setup.X7.isIrreducible_iff ρ).2 ⟨inferInstance, fun U hU => hirrπ U hU⟩⟩
  have hntρ : ∃ g, ρ g ≠ 1 := by
    have : Nontrivial ↥(cayleyGroup K) := nontrivial_cayleyGroup (by rw [hKcard]; exact Nat.one_lt_two_pow (by omega))
    obtain ⟨g, hg⟩ := exists_ne (1 : ↥(cayleyGroup K))
    refine ⟨g, fun h => hg (hπ (LinearEquiv.ext fun w => ?_))⟩
    have h1 := LinearMap.congr_fun h w
    rw [map_one]
    exact h1
  rcases CFSG.Quasithin.B42G2F.natural_or_large_displacement hF (by omega) hntρ with
    ⟨φ, hφ⟩ | hlarge
  ·
    have h := two_mul_le_dispRank_of_natural hKcard he2 π hπ hirrπ φ hφ a ha2 ha1 hnorm
    omega
  ·
    obtain ⟨z, hz2, hz1, hzr⟩ :=
      exists_involution_dispRank_le_two_mul hF he2 π hπ inferInstance hirrπ a ha2 ha1 hnorm
    have h := hlarge z hz2 hz1
    change 3 * e + 2 ≤ dispRank (π z) at h
    omega

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.Thm14_5
