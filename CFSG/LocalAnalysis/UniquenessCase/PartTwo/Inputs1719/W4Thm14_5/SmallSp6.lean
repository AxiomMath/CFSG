module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Thm14_5.SmallRows
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Thm14_5.SmallNatural
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Thm14_5.SmallSp6Par
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Thm14_5.SmallSp6Spin
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Thm14_5.SmallSp6Nat
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Thm14_5.SmallOuter
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Thm14_5.SmallSp6Bridge
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Thm14_5.MBound
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Thm14_5.SmallRep
import CFSG.LocalAnalysis.UniquenessCase.UC22K147Excl
import CFSG.Quasithin.Background.E3MParamAttained
import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotSetup
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Thm14_5.SmallL4Label

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.Thm14_5

open CFSG.LieType.Universal.Symplectic CFSG.LieType.Universal.Symplectic.SpExtras CFSG.Open
  CFSG.ClassicalInvolution.Models.SymplecticPairs CFSG.Quasithin.SmithCurtis Module
open scoped TensorProduct

section Facts

theorem finrank_range_conj_sub_one {G k V : Type*} [Group G] [Field k] [AddCommGroup V]
    [Module k V] [FiniteDimensional k V] (ρ : Representation k G V) (g a : G) :
    finrank k (LinearMap.range (ρ (g * a * g⁻¹) - 1)) = finrank k (LinearMap.range (ρ a - 1)) := by
  have hgg : ∀ v, ρ g (ρ g⁻¹ v) = v := fun v => by
    rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]
  have hgg' : ∀ v, ρ g⁻¹ (ρ g v) = v := fun v => by
    rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]
  let e : V ≃ₗ[k] V := LinearEquiv.ofLinear (ρ g) (ρ g⁻¹) (LinearMap.ext hgg) (LinearMap.ext hgg')
  have hcomp : ρ (g * a * g⁻¹) - 1 = e.toLinearMap ∘ₗ (ρ a - 1) ∘ₗ e.symm.toLinearMap := by
    refine LinearMap.ext fun v => ?_
    simp only [e, LinearMap.sub_apply, Module.End.one_apply, LinearMap.coe_comp,
      Function.comp_apply, LinearEquiv.coe_coe, LinearEquiv.ofLinear_apply,
      LinearEquiv.ofLinear_symm_apply, map_sub, map_mul, Module.End.mul_apply, hgg]
  rw [hcomp, LinearMap.range_comp, LinearMap.range_comp_of_range_eq_top _ e.symm.range,
    LinearEquiv.finrank_map_eq]

theorem finrank_range_sub_one_eq_of_conj {G k V : Type*} [Group G] [Field k] [AddCommGroup V]
    [Module k V] [FiniteDimensional k V] (ρ : Representation k G V) {g a b : G}
    (h : g * a * g⁻¹ = b) :
    finrank k (LinearMap.range (ρ b - 1)) = finrank k (LinearMap.range (ρ a - 1)) := by
  subst h
  exact finrank_range_conj_sub_one ρ g a

variable {K : Type} [Field K] [Fintype K] [CharP K 2] {k V : Type*} [Field k] [CharP k 2]
  [AddCommGroup V] [Module k V]

theorem rep_eq_one_of_isCurtisType_one {ρ : Representation k (StatedSp 3 K) V}
    (hρ : IsSimpleRep ρ) {y₀ : V} {χ : StatedSp 3 K → k}
    (ht : (spCurtisDatum 3 K).IsCurtisType ρ y₀ χ 0) (hχ : ∀ i (a : Kˣ), χ (corootSp i a) = 1)
    (g : StatedSp 3 K) : ρ g = 1 := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have e2 : ∀ a, epsChar χ 2 a = 1 := fun a => by rw [epsChar_two_eq ht, hχ]
  have e1 : ∀ a, epsChar χ 1 a = 1 := fun a => by rw [epsChar_one_eq ht, hχ, e2, one_mul]
  have e0 : ∀ a, epsChar χ 0 a = 1 := fun a => by rw [epsChar_zero_eq ht, hχ, e1, one_mul]
  have hH : ∀ h ∈ (spCurtisDatum 3 K).H, χ h = 1 := by
    intro h hh
    obtain ⟨t, rfl⟩ := spCurtisDatum_H_le hh
    rw [chi_diagHom_eq ht, e0, e1, e2, one_mul, one_mul]
  let τ : Representation k (StatedSp 3 K) k := Representation.trivial k (StatedSp 3 K) k
  have hτ : IsSimpleRep τ := ⟨inferInstance, fun U _ => eq_bot_or_eq_top U⟩
  have htτ : (spCurtisDatum 3 K).IsCurtisType τ 1 χ 0 := by
    refine ⟨fun u _ => rfl, one_ne_zero, fun h hh => by rw [hH h hh, one_smul]; rfl, fun s => ?_⟩
    have : Fintype ((spCurtisDatum 3 K).X s) := Fintype.ofFinite _
    have hbij : Function.Bijective (fun c : K => (⟨elt (simpleIdx s) c,
        (mem_X_iff s).mpr ⟨c, rfl⟩⟩ : (spCurtisDatum 3 K).X s)) := by
      refine ⟨fun c d hcd => elt_injective _ (congrArg Subtype.val hcd), fun x => ?_⟩
      obtain ⟨c, hc⟩ := (mem_X_iff s).mp x.2
      exact ⟨c, Subtype.ext hc.symm⟩
    erw [CurtisDatum.heckeT_apply (spCurtisDatum 3 K) τ s 1]
    simp only [τ, Representation.trivial_apply, Finset.sum_const,
      Finset.card_univ, Pi.zero_apply, zero_smul]
    rw [← Fintype.card_of_bijective hbij, ← Nat.cast_smul_eq_nsmul k,
      natCast_card_eq_zero_charTwo, zero_smul]
  obtain ⟨β, hβ⟩ := (spCurtisDatum 3 K).iso_of_isCurtisType hρ hτ ht htτ
  refine LinearMap.ext fun v => β.injective ?_
  rw [hβ, Module.End.one_apply]
  rfl

end Facts

section Row

open CFSG.QuasithinUnique.Setup CFSG.QuasithinUnique.Setup.X7b CFSG.QuasithinUnique.Setup.Layer
  Subgroup
open CFSG.Quasithin (rkIdx fixV)
open CFSG.Quasithin.E3 (mParam)

abbrev BridgeStatement : Prop :=
  ∀ {K : Type} [Field K] [Fintype K] [CharP K 2] {e : ℕ}, Fintype.card K = 2 ^ e → 3 ≤ e →
    ∀ {W : Type} [AddCommGroup W] [Module (ZMod 2) W] [Finite W]
      (ρ : Representation (ZMod 2) (StatedSp 3 K) W) [ρ.IsIrreducible] {y : StatedSp 3 K},
      y * y = 1 → y ≠ 1 → finrank (ZMod 2) (LinearMap.range (ρ y - 1)) < 3 * e → ∀ i : Fin 3,
      finrank (AlgebraicClosure (Module.End (MonoidAlgebra (ZMod 2) (StatedSp 3 K)) ρ.asModule))
        (fixSub (CFSG.Theory.Representation.extendScalars
          (AlgebraicClosure (Module.End (MonoidAlgebra (ZMod 2) (StatedSp 3 K)) ρ.asModule))
          (CFSG.endFieldRep ρ)) ((spCurtisDatum 3 K).Us i)) ≤ 2

abbrev PlacementStatement : Prop :=
  ∀ {K : Type} [Field K] [Finite K] [CharP K 2] {e : ℕ}, Nat.card K = 2 ^ e → 1 ≤ e →
    ∀ {W : Type} [AddCommGroup W] [Module (ZMod 2) W] [Finite W]
      (ρ : StatedSp 3 K →* (W ≃ₗ[ZMod 2] W)), Function.Injective ρ → ∀ {y : StatedSp 3 K},
      y * y = 1 → dispRank (ρ y) < 3 * e →
      ∃ (g : StatedSp 3 K) (z : StatedSp 2 K),
        g * y * g⁻¹ = spEmbed Fin.succ (Fin.succ_injective 2) z

theorem k14_5SmallFor_sp6_of (hbridge : BridgeStatement) (hplace : PlacementStatement) :
    K14_5SmallFor fun L _ e => CFSG.Blueprint.LieModel L .PSp 3 2 e := by
  intro I _ _ hI X L P e n hLX hLn hq hirr hS hPL hpar hinf hN hn hm
  classical
  have hne : n = e := nParam_eq_of_lieModel_psp6_parabolic hS hPL hpar hinf hN hn
  subst hne
  obtain ⟨K, _, _, _, hKcard, ⟨φ⟩⟩ :=
    CFSG.SeitzReduction.SymplecticPilot.exists_mulEquiv_statedSp_of_lieModel hS
  have : Fintype K := Fintype.ofFinite K
  have hKf : Fintype.card K = 2 ^ n := by rw [← Nat.card_eq_fintype_card, hKcard]
  have h8 : 8 ≤ Fintype.card K := by
    rw [hKf]
    exact le_trans (by norm_num) (Nat.pow_le_pow_right (by norm_num) (show 3 ≤ n by omega))
  have h4' : 4 ≤ Nat.card K := by rw [Nat.card_eq_fintype_card]; omega
  obtain ⟨W, _, _, _, ⟨θ⟩⟩ := Layer.Actor.exists_binModel_of_binary (V := I) fun v => by
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
  let π : StatedSp 3 K →* (W ≃ₗ[ZMod 2] W) :=
    (binPsi θ).toMonoidHom.comp (L.subtype.comp φ.symm.toMonoidHom)
  have hπ : Function.Injective π :=
    (binPsi θ).injective.comp (L.subtype_injective.comp φ.symm.injective)
  have hirrπ : ∀ U : Submodule (ZMod 2) W, (∀ g, ∀ u ∈ U, π g u ∈ U) → U = ⊥ ∨ U = ⊤ :=
    fun U hU => CFSG.Quasithin.B42L2.irr_map θ (fun J hJ' => hJ J hJ' bot_le le_top) U (by
      rintro _ ⟨l, hl, rfl⟩ u hu
      have h := hU (φ ⟨l, hl⟩) u hu
      simpa [π] using h)
  let ρ : Representation (ZMod 2) (StatedSp 3 K) W :=
    LinearEquiv.automorphismGroup.toLinearMapMonoidHom.comp π
  have hρπ : ∀ g w, ρ g w = π g w := fun _ _ => rfl
  have hρirr : ρ.IsIrreducible :=
    (CFSG.QuasithinUnique.Setup.X7.isIrreducible_iff ρ).2 ⟨inferInstance, fun U hU => hirrπ U hU⟩
  have hρinj : Function.Injective ρ := fun g g' h => hπ (LinearEquiv.ext fun w => by
    have := LinearMap.congr_fun h w
    exact this)
  have hπφ : ∀ (l : ↥L) (w : W), π (φ l) w = binPsi θ (l : MulAut I) w := fun l w => by
    simp [π]
  let u₀ : StatedSp 3 K := elt (.positiveLong 0) 1
  have hu₀2 : u₀ * u₀ = 1 := by rw [← elt_add, CharTwo.add_self_eq_zero, elt_zero]
  have hu₀1 : u₀ ≠ 1 := fun h => by
    have : elt (F := K) (.positiveLong (0 : Fin 3)) 1 = elt (.positiveLong 0) 0 := by
      rw [elt_zero]; exact h
    exact one_ne_zero (elt_injective _ this)
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hord : ∀ {M : Type} [Group M] (x : M), x * x = 1 → x ≠ 1 → orderOf x = 2 :=
    fun x hx hx1 => orderOf_eq_prime (by rw [pow_two]; exact hx) hx1
  have hevL : Even (Nat.card ↥L) := by
    have hu : orderOf (φ.symm u₀) = 2 :=
      hord _ (by rw [← map_mul, hu₀2, map_one]) (fun h => hu₀1 (by
        rw [← φ.apply_symm_apply u₀, h, map_one]))
    exact even_iff_two_dvd.2 (hu ▸ orderOf_dvd_natCard _)
  have hev : Even (Nat.card ↥X) := by
    obtain ⟨r, hr⟩ := hevL
    exact even_iff_two_dvd.2 ((even_iff_two_dvd.1 ⟨r, hr⟩).trans (Subgroup.card_dvd_of_le hLX))
  obtain ⟨t, htX, ht2, htm⟩ := CFSG.Quasithin.E3.exists_involution_rkIdx_fixV_eq_mParam X hev
  have hXN : X ≤ normalizer (L : Set (MulAut I)) :=
    (normal_subgroupOf_iff_le_normalizer hLX).mp hLn
  set a : W ≃ₗ[ZMod 2] W := binPsi θ t with hadef
  have htt : t * t = 1 := by rw [← pow_two, ← ht2, pow_orderOf_eq_one]
  have ha2 : ∀ w, a (a w) = w := fun w => by
    rw [hadef, ← LinearEquiv.mul_apply, ← map_mul, htt, map_one]
    rfl
  have ha1 : a ≠ 1 := by
    intro h
    have h1 : t = 1 := (binPsi θ).injective (h.trans (map_one _).symm)
    rw [h1, orderOf_one] at ht2
    exact absurd ht2 (by norm_num)
  have hrk : dispRank a ≤ n + 1 := by
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
    have h4 : rkIdx (fixV (zpowers (X.subtype t'))) = mParam X := htm
    change Module.finrank (ZMod 2) ↥(LinearMap.range (a.toLinearMap - 1)) ≤ n + 1
    omega
  have htc : ∃ x ∈ L, t * x ≠ x * t := by
    by_contra hall
    push Not at hall
    have h1 := eq_one_of_commute_of_isIrrOn hI hirr (by rw [pow_two]; exact htt) hall
    rw [h1, orderOf_one] at ht2
    exact absurd ht2 (by norm_num)
  have : IsSimpleGroup (StatedSp 3 K) :=
    CFSG.SeitzReduction.SymplecticPilot.isSimpleGroup_statedSp_of_four_le h4' (by norm_num)
  have : IsSimpleGroup ↥L := φ.isSimpleGroup
  obtain ⟨l, hlL, j, hyL, hy1, hy2⟩ := exists_involution_pow_mul_conj
    (fun N hN hodd => eq_bot_of_odd_of_isSimpleGroup hevL N hN hodd) (hXN htX) htt htc
  let ψ : Representation (ZMod 2) (MulAut I) W :=
    LinearEquiv.automorphismGroup.toLinearMapMonoidHom.comp (binPsi θ).toMonoidHom
  have hyrk := finrank_range_pow_mul_conj_le ψ t l j
  obtain ⟨z, hzdef⟩ : ∃ z : StatedSp 3 K, z = φ ⟨_, hyL⟩ := ⟨_, rfl⟩
  have hρz : ∀ w, ρ z w = ψ ((t * (l⁻¹ * t * l)) ^ j) w := fun w => by
    rw [hρπ, hzdef, hπφ]
    rfl
  have hz2 : z * z = 1 := by
    rw [hzdef, ← map_mul, show (⟨_, hyL⟩ : ↥L) * ⟨_, hyL⟩ = 1 from Subtype.ext hy2, map_one]
  have hz1 : z ≠ 1 := fun h => hy1 (by
    have h1 : (⟨_, hyL⟩ : ↥L) = 1 := by
      rw [← φ.symm_apply_apply ⟨_, hyL⟩, ← hzdef, h, map_one]
    exact congrArg Subtype.val h1)
  have hzd : finrank (ZMod 2) (LinearMap.range (ρ z - 1)) ≤ 2 * (n + 1) := by
    have e1 : ρ z - 1 = (ψ ((t * (l⁻¹ * t * l)) ^ j) : W →ₗ[ZMod 2] W) - 1 :=
      LinearMap.ext fun w => by rw [LinearMap.sub_apply, LinearMap.sub_apply, hρz]
    have e2 : (ψ t : W →ₗ[ZMod 2] W) - 1 = a.toLinearMap - 1 := rfl
    rw [e1]
    rw [e2] at hyrk
    exact hyrk.trans (by unfold dispRank at hrk; omega)
  have hzlt : finrank (ZMod 2) (LinearMap.range (ρ z - 1)) < 3 * n := by omega
  let E := Module.End (MonoidAlgebra (ZMod 2) (StatedSp 3 K)) ρ.asModule
  have : CharP E 2 := CFSG.HardMathSupport.GuralnickMalle.endField_charP ρ 2
  let k := AlgebraicClosure E
  let _ : Algebra K k :=
    (CFSG.HardMathSupport.GuralnickMalle.nonempty_ringHom_algebraicClosure
      (K := E) (F₀ := K) (p := 2)).some.toAlgebra
  have : CharP k 2 := charP_of_injective_algebraMap (algebraMap E k).injective 2
  have : FiniteDimensional E ρ.asModule :=
    CFSG.HardMathSupport.GuralnickMalle.finiteDimensional_endField ρ
  have hsplit : SplitOver k (spCurtisDatum 3 K).H := spCurtisDatum_splitOver k
  have hsimp : IsSimpleRep (CFSG.Theory.Representation.extendScalars k (CFSG.endFieldRep ρ)) :=
    CFSG.HardMathSupport.Meierfrankenfeld.PSUScalar.isSimpleRep_extendScalars_endFieldRep ρ k
  obtain ⟨y₀, χ, μ, ht⟩ := (spCurtisDatum 3 K).exists_isCurtisType hsplit hsimp
  have hC3 : ∀ i : Fin 3, μ i = 0 ∧ ((∀ a, χ (corootSp i a) = 1) ∨
      ∃ φ' : K →+* k, ∀ a : Kˣ, χ (corootSp i a) = φ' a) := fun i =>
    spRankOne_of_finrank_le h4' hsplit hsimp ht i (hbridge hKf (by omega) ρ hz2 hz1 hzlt i)
  have hμ : μ = 0 := funext fun i => (hC3 i).1
  subst hμ
  have htriv : ∃ i a, χ (corootSp i a) ≠ 1 := by
    by_contra hall
    push Not at hall
    have h1 := rep_eq_one_of_isCurtisType_one hsimp ht hall z
    have h2 : ρ z = 1 :=
      (CFSG.HardMathSupport.Meierfrankenfeld.PSUScalar.extendScalars_endFieldRep_eq_one_iff
        ρ k z).mp h1
    exact hz1 (hρinj (h2.trans (map_one ρ).symm))
  obtain ⟨i₀, a₀, ha₀⟩ := htriv
  obtain ⟨φ₀, hφ₀⟩ := (hC3 i₀).2.resolve_left fun h => ha₀ (h a₀)
  obtain ⟨s, hs1, hE⟩ :=
    CFSG.HardMathSupport.Meierfrankenfeld.PSUScalar.exists_card_endField_eq_two_pow ρ
  have hsn : n ≤ s := le_of_ringHom_pow_eq φ₀ hKf hs1 fun a => by
    have h := CFSG.HardMathSupport.GuralnickMalle.isCurtisType_chi_pow_card ρ
      (spCurtisDatum 3 K) k ht (corootSp_mem_H i₀ a)
    rwa [hE, hφ₀] at h
  have hrankz := finrank_range_sub_one_eq_mul ρ hE k z
  have hzk : finrank k (LinearMap.range
      (CFSG.Theory.Representation.extendScalars k (CFSG.endFieldRep ρ) z - 1)) ≤ 2 := by
    by_contra hc
    push Not at hc
    have h1 : s * 3 ≤ s * finrank k (LinearMap.range
        (CFSG.Theory.Representation.extendScalars k (CFSG.endFieldRep ρ) z - 1)) :=
      Nat.mul_le_mul_left s hc
    have h2 : n * 3 ≤ s * 3 := Nat.mul_le_mul_right 3 hsn
    omega
  have hzdisp : dispRank (π z) < 3 * n := hzlt
  obtain ⟨g, z', hgz⟩ := hplace hKcard (by omega) π hπ hz2 hzdisp
  have hz'1 : z' ≠ 1 := fun h => hz1 (by
    rw [h, map_one] at hgz
    have := congrArg (fun x => g⁻¹ * x * g) hgz
    simpa [mul_assoc] using this)
  have hrk' : finrank k (LinearMap.range (CFSG.Theory.Representation.extendScalars k
      (CFSG.endFieldRep ρ) (spEmbed Fin.succ (Fin.succ_injective 2) z') - 1)) ≤ 2 := by
    exact (finrank_range_sub_one_eq_of_conj _ hgz).trans_le hzk
  rcases natural_or_spin_of_finrank_le_two h8 ht (fun i => (hC3 i).2) hz'1 hrk' with
    htr | ⟨φ₁, h0, h1, h2⟩ | ⟨φ₁, h0, h1, h2⟩
  · exact absurd (htr i₀ a₀) ha₀
  ·
    obtain ⟨β, hβ⟩ := exists_addEquiv_natural_of_isCurtisType hKf (by omega) ρ ht φ₁ h0 h1 h2
    have hSpn : IsSpn ↥L 6 n := ⟨⟨3, rfl⟩, K, inferInstance, inferInstance, hKcard, ⟨φ⟩⟩
    have hNat : NatSpn L ⊤ ⊥ 6 n := by
      refine ⟨⟨3, rfl⟩, K, inferInstance, inferInstance, hKcard, ?_⟩
      refine realizes_nat_of_equiv θ φ β fun l w => ?_
      have h := hβ (φ l) w
      rwa [hρπ, hπφ] at h
    exact Or.inl ⟨n, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
      (Or.inl ⟨hSpn, hNat⟩))))))))), Or.inl rfl⟩
  ·
    exfalso
    have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_left htt
    have hconj : ∀ x ∈ L, t * x * t⁻¹ ∈ L := fun x hx =>
      (Subgroup.mem_normalizer_iff.mp (hXN htX) x).mp hx
    let cL : ↥L ≃* ↥L :=
      { toFun := fun x => ⟨t * x * t⁻¹, hconj x x.2⟩
        invFun := fun x => ⟨t * x * t⁻¹, hconj x x.2⟩
        left_inv := fun x => Subtype.ext (by
          change t * (t * (x : MulAut I) * t⁻¹) * t⁻¹ = x
          rw [htinv, ← mul_assoc, ← mul_assoc, htt, one_mul, mul_assoc, htt, mul_one])
        right_inv := fun x => Subtype.ext (by
          change t * (t * (x : MulAut I) * t⁻¹) * t⁻¹ = x
          rw [htinv, ← mul_assoc, ← mul_assoc, htt, one_mul, mul_assoc, htt, mul_one])
        map_mul' := fun x x' => Subtype.ext (by
          change t * ((x : MulAut I) * x') * t⁻¹ = t * x * t⁻¹ * (t * x' * t⁻¹)
          group) }
    let α : MulAut (StatedSp 3 K) := φ.symm.trans (cL.trans φ)
    have hα : ∀ g w, a (ρ g (a w)) = ρ (α g) w := by
      intro g w
      have e1 : ρ (α g) w = binPsi θ (t * ((φ.symm g : ↥L) : MulAut I) * t⁻¹) w := by
        rw [hρπ]
        change π (φ (cL (φ.symm g))) w = _
        rw [hπφ]
        rfl
      rw [e1, htinv, map_mul, map_mul, LinearEquiv.mul_apply, LinearEquiv.mul_apply, hρπ]
      rfl
    rcases two_mul_le_or_inner_of_spin hKf (by omega) ρ hρinj k hsimp ht φ₁ h0 h1 h2 a ha2 α hα
      with hle | ⟨g₀, hg₀2, hg₀⟩
    · unfold dispRank at hrk
      omega
    ·
      have hg₀1 : g₀ ≠ 1 := fun h => ha1 (LinearEquiv.ext fun w => by
        rw [hg₀, h, map_one]
        rfl)
      have hag : (a : W →ₗ[ZMod 2] W) - 1 = ρ g₀ - 1 :=
        LinearMap.ext fun w => by
          rw [LinearMap.sub_apply, LinearMap.sub_apply, LinearEquiv.coe_coe, hg₀]
      have hg₀d : finrank (ZMod 2) (LinearMap.range (ρ g₀ - 1)) ≤ n + 1 := by
        rw [← hag]
        exact hrk
      have hg₀disp : dispRank (π g₀) < 3 * n := by
        have h3 : n + 1 < 3 * n := by omega
        exact lt_of_le_of_lt hg₀d h3
      obtain ⟨g', z'', hgz''⟩ := hplace hKcard (by omega) π hπ hg₀2 hg₀disp
      have hz''1 : z'' ≠ 1 := fun h => hg₀1 (by
        rw [h, map_one] at hgz''
        have := congrArg (fun x => g'⁻¹ * x * g') hgz''
        simpa [mul_assoc] using this)
      have h2le := two_le_finrank_of_spin (by omega) ht φ₁ h0 h1 h2 hz''1
      rw [finrank_range_sub_one_eq_of_conj _ hgz''] at h2le
      have hrank := finrank_range_sub_one_eq_mul ρ hE k g₀
      have h1 : s * 2 ≤ s * finrank k (LinearMap.range
          (CFSG.Theory.Representation.extendScalars k (CFSG.endFieldRep ρ) g₀ - 1)) :=
        Nat.mul_le_mul_left s h2le
      have h2 : n * 2 ≤ s * 2 := Nat.mul_le_mul_right 2 hsn
      omega

theorem k14_5SmallFor_sp6 : K14_5SmallFor fun L _ e => CFSG.Blueprint.LieModel L .PSp 3 2 e :=
  k14_5SmallFor_sp6_of @finrank_fixSub_Us_le_two @exists_conj_eq_spEmbed_of_dispRank_lt

end Row

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.Thm14_5
