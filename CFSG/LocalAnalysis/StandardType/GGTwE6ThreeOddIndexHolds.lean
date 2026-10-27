module

public import CFSG.LocalAnalysis.StandardType.GGTwE6ThreeLangLayer
public import CFSG.LocalAnalysis.StandardType.GGTwE6ThreeChoice
public import CFSG.LocalAnalysis.StandardType.GGTwE6ThreeLift
public import CFSG.LocalAnalysis.StandardType.GGSixAutKFinerTagsExcBasic

public section

namespace CFSG.StandardType

open CFSG.Blueprint.Chevalley CFSG.HardMathSupport.Timmesfeld.LangTorus
  CFSG.LieType.AlgebraicGroups CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.StandardType.TwE6ThreeB CFSG.StandardType.ExcThreeAtTwo
  CFSG.HardMathSupport.Timmesfeld.CrossChar

theorem ggLayerExcThreeOddIndexAtTwoTwE6_holds :
    GGLayerExcThreeOddIndexAtTwoTwE6 := by
  intro G _ _ n ψ G₀ hpres hCG y hy1 hy3 hyN hdiag C hC hType
  classical
  obtain ⟨-, ⟨hrange, hker⟩, -, -⟩ := hpres
  subst hrange
  have hf : 1 ≤ 1 := le_rfl
  obtain ⟨π, hπ, hkerπ, -, hπval⟩ := LayerSixE.exists_model_twistedE6 hf
  have hkπ : ψ.ker ≤ π.ker := hker.trans hkerπ.ge
  have hkerEq : ψ.ker = π.ker := by
    refine le_antisymm hkπ ?_
    rw [hkerπ]
    intro z hz
    rw [MonoidHom.mem_ker]
    have h : ψ z ∈ Subgroup.centralizer (ψ.range : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      rintro _ ⟨u, rfl⟩
      rw [← map_mul, ← map_mul]
      exact congrArg ψ (Subgroup.mem_center_iff.mp hz u)
    rw [hCG, Subgroup.mem_bot] at h
    exact h
  set χ := MonoidHom.liftOfSurjective π hπ ⟨ψ, hkerEq.ge⟩ with hχdef
  have hχπ : ∀ x : (ggU .twistedE6 n 1).K, χ (π x) = ψ x := fun x =>
    MonoidHom.liftOfRightInverse_comp_apply _ _ _ _ x
  have hχinj : Function.Injective χ := by
    rw [injective_iff_map_eq_one]
    intro c hc
    obtain ⟨x, rfl⟩ := hπ c
    erw [hχπ] at hc
    have hx : x ∈ ψ.ker := hc
    rw [hkerEq] at hx
    exact hx
  have hχrange : χ.range = ψ.range := by
    ext g
    constructor
    · rintro ⟨c, rfl⟩
      obtain ⟨x, rfl⟩ := hπ c
      exact ⟨x, (hχπ x).symm⟩
    · rintro ⟨x, rfl⟩
      exact ⟨π x, hχπ x⟩
  obtain ⟨α, hαD, hα⟩ := LayerSixE.exists_induces_twistedE6 hf hπval ψ hker hkπ hyN hdiag
  have hα3 : α ^ 3 = 1 := by
    have h1 := hα.pow hkπ hyN 3
    rw [hy3] at h1
    exact LayerSixE.GGInduces.unique hπ (Subgroup.one_mem _) h1 (LayerSixE.GGInduces.one hkπ)
  have hαχ : ∀ c, χ (α c) = y * χ c * y⁻¹ := by
    intro c
    obtain ⟨x, rfl⟩ := hπ c
    obtain ⟨x', hx'⟩ := LayerSixE.exists_conj_eq hyN x
    rw [← hα x x' hx']
    erw [hχπ, hχπ]
    exact hx'
  have hα1 : α ≠ 1 := by
    rintro rfl
    apply hy1
    have hmem : y ∈ Subgroup.centralizer (ψ.range : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      rintro _ ⟨x, rfl⟩
      have := hαχ (π x)
      rw [MulAut.one_apply] at this
      erw [hχπ] at this
      calc ψ x * y = y * ψ x * y⁻¹ * y := by rw [← this]
        _ = y * ψ x := by group
    rw [hCG, Subgroup.mem_bot] at hmem
    exact hmem
  rw [NoOffTwE6Three.twInndiagAut_eq_range_twistedE6InndiagConj hf] at hαD
  obtain ⟨hg, rfl⟩ := hαD
  have hinjC := NoOffTwE6Three.twistedE6InndiagConj_injective_galoisField hf
  have hh3 : (hg : ModGL TwistTag.E6.tag (GaloisField 2 (2 * 1))) ^ 3 = 1 := by
    have : hg ^ 3 = 1 := hinjC ((map_pow _ _ _).trans (hα3.trans (map_one _).symm))
    rw [← Subgroup.coe_pow, this, Subgroup.coe_one]
  have hh1 : (hg : ModGL TwistTag.E6.tag (GaloisField 2 (2 * 1))) ≠ 1 := by
    intro h
    apply hα1
    have : hg = 1 := Subtype.ext h
    rw [this]
    exact map_one _
  have hK : Nat.card (GaloisField 2 (2 * 1)) = (2 ^ 1) ^ 2 := by
    rw [GaloisField.card 2 (2 * 1) (by norm_num)]; norm_num
  obtain ⟨S, a, ι, hq, -, hT, hap, h1, hinj, hιrange, hconj⟩ :=
    CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.exists_langSetup_of_inndiag_twE6_of_prime
      Nat.prime_two hf hK (frobQEquiv hf)
      (fun c => CFSG.LieType.Steinberg.Exceptional.frobQ_apply (p := 2) (f := 1) c)
      Nat.prime_three (by decide)
      (p₀ := 5) (by norm_num) (by decide) (Or.inl le_rfl) monomialToralAt_E6_three
      (twistedE6InndiagConj _ _ hg) (hg : ModGL TwistTag.E6.tag (GaloisField 2 (2 * 1))) hg.2
      (fun c => twistedE6InndiagConj_apply hg c) hh3 hh1
  have hq2 : S.D.q = 2 := by rw [hq, pow_one]
  haveI : CharP (AlgebraicClosure (GaloisField 2 (2 * 1))) 2 :=
    charP_two_of_langSetup_q_eq_two S hq2
  have hAlg : S.IsAlgebraic := S.isAlgebraic_of_algebraic (GaloisField 2 (2 * 1)) 2 (by rw [hK, hq])
  have h3L : ((3 : ℕ) : AlgebraicClosure (GaloisField 2 (2 * 1))) ≠ 0 := by
    have h2 : ((2 : ℕ) : AlgebraicClosure (GaloisField 2 (2 * 1))) = 0 :=
      CharP.cast_eq_zero _ 2
    rw [show (3 : ℕ) = 2 + 1 from rfl, Nat.cast_add, h2, zero_add, Nat.cast_one]
    exact one_ne_zero
  set β := twistedE6InndiagConj (GaloisField 2 (2 * 1)) (frobQEquiv hf) hg with hβdef
  have hfixχ : (CFSG.HardMathSupport.Solomon.Coordinator.fixSubgroup β).map χ =
      χ.range ⊓ Subgroup.centralizer {y} :=
    CFSG.HardMathSupport.Solomon.Coordinator.LieComp.map_fixSubgroup_eq_of_conj χ hχinj β y hαχ
  have hCr : C ≤ χ.range := hχrange ▸ (hC.1.trans inf_le_left)
  rw [← hχrange, ← hfixχ] at hC
  have hJ := CFSG.StandardType.TagsExc.isComponentOf_comap χ hχinj hC
  have hTame := CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.langSetup_hTame_of_prime S
    Nat.prime_three h3L (fun h' => absurd h' (by decide)) hT hap h1
  obtain ⟨i, hqs, hJR⟩ := CFSG.HardMathSupport.Solomon.Coordinator.LieComp.components_of_langSetup
    S Nat.prime_three ι hinj hιrange β hconj hT hap h1 hTame
    (CFSG.Assembly.isComponentOf_iff_open.mp hJ)
  rcases ratComp_excThree_layer_E6' S hq2 hAlg hT hap h1 i hqs with hne | ⟨hZ, h2⟩
  · exfalso
    have hcq : ggCQ C = ggCQ (rationalComponent S.ρ S.Γ (rootCharHom a) i) := by
      exact (ggCQ_comap_of_injective χ hχinj hCr).symm.trans
        ((ggCQ_map_of_injective ι hinj _).symm.trans (congrArg ggCQ hJR))
    exact not_excThreeType_of_notExcThreeOrder (hcq ▸ hne) hType
  · refine ⟨?_, fun r hr hr2 => ?_⟩
    · let e : C ≃* rationalComponent S.ρ S.Γ (rootCharHom a) i :=
        ((MulEquiv.subgroupCongr (Subgroup.map_comap_eq_self hCr)).symm.trans
          (Subgroup.equivMapOfInjective (C.comap χ) χ hχinj).symm).trans
          ((Subgroup.equivMapOfInjective (C.comap χ) ι hinj).trans (MulEquiv.subgroupCongr hJR))
      have hm := Subgroup.map_center_eq e
      rw [hZ] at hm
      exact (Subgroup.map_eq_bot_iff_of_injective _ e.injective).mp hm
    · rw [← hχrange, ← hfixχ] at hr
      obtain ⟨c, hc, rfl⟩ := hr
      have hc2 : c ^ 2 = 1 := hχinj (by rw [map_pow, hr2, map_one])
      have hιfix := CFSG.HardMathSupport.Solomon.Coordinator.LieComp.map_fixSubgroup_eq_of_conj
        ι hinj β _ hconj
      have hmem : ι c ∈ S.Γ ⊓ Subgroup.centralizer {rootDiagUnit Tag.E6 a} := by
        rw [← hιrange, ← hιfix]
        exact ⟨c, hc, rfl⟩
      have hR := h2 (ι c) hmem 1 (by
        rw [pow_one]
        exact (map_pow ι c 2).symm.trans ((congrArg ι hc2).trans (map_one ι)))
      rw [← hJR] at hR
      obtain ⟨j, hj, hjc⟩ := hR
      rw [← hinj hjc]
      exact hj

end CFSG.StandardType

end
