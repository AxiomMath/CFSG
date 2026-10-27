module

public import CFSG.LocalAnalysis.StandardType.GGKGRootDatumFrame
public import CFSG.LocalAnalysis.StandardType.GGKGForkExcRootRefl1
public import CFSG.LocalAnalysis.StandardType.GGTwE6SplitRootGenComp
public import CFSG.LocalAnalysis.StandardType.GGTwE6SplitRootGenReal
public import CFSG.LocalAnalysis.StandardType.GGTwE6SplitRootGenSCThree
public import CFSG.LocalAnalysis.StandardType.GGTableBTwE6Dvd
public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.Exc.CatTw
public import CFSG.GroupTheory.ConjTransport
public import CFSG.LocalAnalysis.StandardType.GGRealKGThree
public import CFSG.LocalAnalysis.StandardType.GGNbrInnerWeylTwE6SplitLift
public import CFSG.LocalAnalysis.StandardType.GGTableBNbrInner937TwE6Inn
public import CFSG.LocalAnalysis.StandardType.GGTableBNbrInner937TwE6Center

public section

namespace CFSG.StandardType.TwE6SplitRootGen

open CFSG CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley
  CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Exceptional Multiplicative


theorem ggKGRootDatumAt_range_twE6SplitFrame_three {n : ℕ} (hn : 1 ≤ n)
    (h3 : 3 ∣ 2 ^ n - 1) {ζ : (GaloisField 2 (2 * n))ˣ} (hζo : orderOf ζ = 3)
    (hζ : ζ ^ 3 = 1) (hζσ : frobQ 2 n (ζ : GaloisField 2 (2 * n)) = ζ) :
    GGKGRootDatumAt 3 (ExcFrames.twE6SplitFrameHom (frobQ 2 n) ζ hζ hζσ).range := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let K := GaloisField 2 (2 * n)
  let R := ↥(graphFixedRootGroup TwistTag.E6 K (frobQ 2 n))
  let T := ExcFrames.twE6SplitFrameHom (frobQ 2 n) ζ hζ hζσ
  let E : Subgroup R := T.range
  have hTinj : Function.Injective T := twE6SplitFrameHom_injective_of_orderOf
    (frobQ 2 n) hζo hζ hζσ
  have hE : CFSG.Open.IsElemAbelian 3 E := ExcFrames.isElemAbelian_range_frame T
  choose m hmJ hms using fun i : Fin Tag.F4.rank =>
    exists_mem_orbitRankOneGroup_conj_twE6SplitFrameHom (frobQ 2 n) hζ hζσ i
  let J : Fin Tag.F4.rank → Subgroup R := fun i =>
    (orbitRankOneGroup TwistTag.E6 K (frobQ 2 n) i).subgroupOf
      (graphFixedRootGroup TwistTag.E6 K (frobQ 2 n))
  have hJcomp : ∀ i, IsComponentOf (J i)
      (Subgroup.centralizer ((E ⊓ Subgroup.centralizer ({m i} : Set R) : Subgroup R) : Set R)) := by
    intro i
    have hfix : ((E ⊓ Subgroup.centralizer ({m i} : Set R) : Subgroup R) : Set R) =
        SuSplitRootGen.torusFix T (TableBExc.torusAct .F4 3 (simple .F4 i)) := by
      ext a
      constructor
      · rintro ⟨⟨s, rfl⟩, hs⟩
        refine ⟨s, ?_, rfl⟩
        apply ofAdd.injective
        apply hTinj
        rw [← hms i (toAdd s), ofAdd_toAdd, mul_inv_eq_iff_eq_mul]
        exact (Subgroup.mem_centralizer_singleton_iff.mp hs).symm
      · rintro ⟨s, hs, rfl⟩
        refine ⟨⟨s, rfl⟩, Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩
        have hh := hms i (toAdd s)
        rw [hs, ofAdd_toAdd, mul_inv_eq_iff_eq_mul] at hh
        exact hh.symm
    rw [hfix]
    exact isComponentOf_orbitRankOneGroup_twE6Split (frobQ 2 n) (by decide) hζo hζ hζσ i
  have h3' : ¬ 3 ∣ 2 ^ n + 1 := by
    have hpos : 1 ≤ 2 ^ n := Nat.one_le_two_pow
    omega
  have hframe : ExcFrames.twE6ThreeFrameHom hn h3' ζ hζ = T := by
    ext s
    rfl
  have hnorm : ∀ w₀ ∈ Subgroup.normalizer (E : Set R), ∃ v : WeylGroup .F4,
      ∀ s : Fin Tag.F4.rank → ZMod 3, w₀ * T (ofAdd s) * w₀⁻¹ =
        T (ofAdd (TableBExc.torusAct .F4 3 v s)) := by
    intro w₀ hw₀
    have hxM := ExcFrames.mem_graphFixedRootMonomial_of_normalizes_twE6ThreeFrame
      hn h3' hζo hζ (x := w₀) (by
        intro s
        rw [hframe]
        exact (Subgroup.mem_normalizer_iff.mp hw₀ (T s)).mp ⟨s, rfl⟩)
    let v : relWeylTwist TwistTag.E6 :=
      ⟨graphFixedRootWeylHom TwistTag.E6 K (frobQ 2 n)
          ⟨(w₀ : ModGL TwistTag.E6.tag K), hxM⟩,
        (graphFixedRootWeylHom_range TwistTag.E6 K (frobQ 2 n)).le
          ⟨⟨(w₀ : ModGL TwistTag.E6.tag K), hxM⟩, rfl⟩⟩
    exact ⟨foldedWeylEquiv TwistTag.E6 v, fun s =>
      ExcFrames.twE6SplitFrameHom_conj (frobQ 2 n) hζ hζσ hxM s⟩
  have hcover : ∀ w₀ : R, GGKGIsReflAt 3 E w₀ →
      ∃ i, ∃ u ∈ Subgroup.normalizer (E : Set R),
        ∀ e ∈ E, w₀ * e * w₀⁻¹ =
          (u * m i * u⁻¹) * e * (u * m i * u⁻¹)⁻¹ := by
    intro w₀ hw₀
    obtain ⟨v, hv⟩ := hnorm w₀ hw₀.1
    have hinv : ∀ s : Fin Tag.F4.rank → ZMod 3,
        TableBExc.torusAct .F4 3 v (TableBExc.torusAct .F4 3 v s) = s := by
      intro s
      have hh := hw₀.2.1 (T (ofAdd s)) ⟨ofAdd s, rfl⟩
      rw [hv s, hv (TableBExc.torusAct .F4 3 v s)] at hh
      exact ofAdd.injective (hTinj hh)
    have hv2 : v * v = 1 := NoOffExc.eq_one_of_torusAct (p := 3) (by decide) (by
      intro s
      rw [TableBExc.torusAct_mul]
      exact hinv s)
    let eT : (Fin Tag.F4.rank → ZMod 3) ≃ E :=
      (Multiplicative.ofAdd : (Fin Tag.F4.rank → ZMod 3) ≃
        Multiplicative (Fin Tag.F4.rank → ZMod 3)).trans (MonoidHom.ofInjective hTinj).toEquiv
    have hcardE : Nat.card E = 3 ^ Tag.F4.rank := by
      rw [← Nat.card_congr eT, Nat.card_fun, Nat.card_zmod, Nat.card_fin]
    have hfixv : Nat.card {s : Fin Tag.F4.rank → ZMod 3 //
        TableBExc.torusAct .F4 3 v s = s} * 3 = 3 ^ Tag.F4.rank := by
      have hfixeq : Nat.card {s : Fin Tag.F4.rank → ZMod 3 //
          TableBExc.torusAct .F4 3 v s = s} =
          Nat.card {e : E // w₀ * (e : R) * w₀⁻¹ = e} := by
        refine Nat.card_congr (Equiv.subtypeEquiv eT fun s => ?_)
        change TableBExc.torusAct .F4 3 v s = s ↔ w₀ * T (ofAdd s) * w₀⁻¹ = T (ofAdd s)
        rw [hv s]
        exact (hTinj.comp ofAdd.injective).eq_iff.symm
      rw [hfixeq, hw₀.2.2, hcardE]
    have hfix : Nat.card {s : Fin Tag.F4.rank → ZMod 3 //
        TableBExc.torusAct .F4 3 v s = s} = 3 ^ (Tag.F4.rank - 1) := by
      norm_num [Tag.rank] at hfixv ⊢
      omega
    obtain ⟨β, hβ, hvβ⟩ := exists_rootReflection_of_natCard_fix_torusAct (p := 3) (by decide)
      (by decide : 0 < Tag.F4.rank) hv2 hfix
    obtain ⟨w, i, hwi⟩ := isRoot_iff_exists_smul_single.mp hβ
    have hvs : v = w * simple .F4 i * w⁻¹ := hvβ.trans (rootReflection_eq_conj hwi)
    obtain ⟨u, hu⟩ := ExcFrames.exists_realization_twE6Split_weyl (frobQ 2 n) hζ hζσ w
    have huN : u ∈ Subgroup.normalizer (E : Set R) := by
      refine CFSG.GroupTheory.mem_normalizer_of_conj_mem ?_
      rintro a ⟨s, rfl⟩
      exact ⟨ofAdd (TableBExc.torusAct .F4 3 w (toAdd s)), (hu (toAdd s)).symm⟩
    have huinv : ∀ s : Fin Tag.F4.rank → ZMod 3,
        u⁻¹ * T (ofAdd s) * u = T (ofAdd (TableBExc.torusAct .F4 3 w⁻¹ s)) := by
      intro s
      have hh := hu (TableBExc.torusAct .F4 3 w⁻¹ s)
      rw [← TableBExc.torusAct_mul, mul_inv_cancel, TableBExc.torusAct_one] at hh
      rw [← hh]
      group
      rfl
    refine ⟨i, u, huN, ?_⟩
    rintro a ⟨s, rfl⟩
    rw [← ofAdd_toAdd s, hv (toAdd s), hvs]
    calc
      T (ofAdd (TableBExc.torusAct .F4 3 (w * simple .F4 i * w⁻¹) (toAdd s))) =
          u * (m i * (u⁻¹ * T (ofAdd (toAdd s)) * u) * (m i)⁻¹) * u⁻¹ := by
        rw [huinv (toAdd s), hms, hu, TableBExc.torusAct_mul, TableBExc.torusAct_mul]
      _ = (u * m i * u⁻¹) * T (ofAdd (toAdd s)) * (u * m i * u⁻¹)⁻¹ := by group
  have hK : Nat.card K = (2 ^ n) ^ 2 :=
    CFSG.LieType.Universal.card_galoisField_two_mul 2 n hn
  obtain ⟨e⟩ := TwE6Rank.exists_mulEquiv_graphFixedRootGroup hn hK (frobQ 2 n) (frobQ_apply 2 n)
  obtain ⟨hS₀, hnc₀⟩ := TwE6Dvd.isSimpleGroup_recipeR hn hK
  have hS : IsSimpleGroup R := e.symm.isSimpleGroup
  have hnc : ∃ a b : R, a * b ≠ b * a := by
    obtain ⟨a, b, hab⟩ := hnc₀
    exact ⟨e a, e b, fun h => hab (e.injective (by simpa only [map_mul] using h))⟩
  have hchev : CFSG.Yardstones.Md0ec50421ce4.IsChevSimple 2 R := by
    let q : TauCeti.PrimePower := ⟨2, n, Nat.prime_two, by omega⟩
    have hq : q.card = 2 ^ n := by rw [TauCeti.PrimePower.card_def]
    let σ := iterateFrobeniusEquiv K 2 n
    have hσ : ∀ c, σ c = c ^ q.card := by
      intro c
      rw [hq, iterateFrobeniusEquiv_def]
    have hσeq : σ.toRingHom = frobQ 2 n := by
      ext c
      change σ c = (frobQ 2 n) c
      rw [hσ, hq, frobQ_apply]
    have hvq := TauCeti.LieTypeIndex.valid_twistedE6 q
    obtain ⟨ec⟩ := CFSG.HardMathSupport.Solomon.Coordinator.LieComp.catEquiv_twistedE6_of_field
      q hvq K (by rw [hq]; exact hK) σ hσ
    have hct := CFSG.HardMathSupport.Solomon.Coordinator.LieComp.isChevSimple_of_lie
      (⟨TauCeti.LieTypeIndex.twistedE6 q, hvq⟩ : TauCeti.ValidLieTypeIndex)
      (by rw [TauCeti.LieTypeIndex.characteristic_twistedE6]) ec.symm
    change CFSG.Yardstones.Md0ec50421ce4.IsChevSimple 2
      ↥(graphFixedRootGroup TwistTag.E6 K (frobQ 2 n))
    change CFSG.Yardstones.Md0ec50421ce4.IsChevSimple 2
      ↥(graphFixedRootGroup TwistTag.E6 K σ.toRingHom) at hct
    rw [hσeq] at hct
    exact hct
  exact ggKGRootDatumAt_of_componentCover hS hnc hchev Nat.prime_three (by decide) hE m J
    (fun i => hmJ i) hJcomp
    (fun i => dvd_card_orbitRankOneGroup_subgroupOf_twE6Split (frobQ 2 n) hζo hζσ i) hcover

theorem ggKGRootDatum_recipeR_twE6Split_three {K : Type} [Field K] [Finite K] {n : ℕ}
    (hn : 1 ≤ n) (hK : Nat.card K = (2 ^ n) ^ 2) (h3 : 3 ∣ 2 ^ n - 1) :
    GGKGRootDatum 3 4 (TwE6Delta.RecipeR K n) := by
  classical
  have hchar : CharP K 2 := charP_two_of_card (m := n * 2) (by rw [hK, pow_mul])
  set σ : K →+* K := iterateFrobenius K 2 n
  have hσ : ∀ c, σ c = c ^ 2 ^ n := fun c => iterateFrobenius_def 2 n c
  have := Fintype.ofFinite K
  have := Fintype.ofFinite (GaloisField 2 (2 * n))
  have hcardK : Fintype.card (GaloisField 2 (2 * n)) = Fintype.card K := by
    rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card,
      CFSG.LieType.Universal.card_galoisField_two_mul 2 n hn, hK]
  let τ := FiniteField.ringEquivOfCardEq hcardK
  have hτ : ∀ c : GaloisField 2 (2 * n), τ (frobQ 2 n c) = σ (τ c) := fun c => by
    rw [frobQ_apply, hσ, map_pow]
  obtain ⟨e⟩ := TwE6Rank.exists_mulEquiv_graphFixedRootGroup (K := K) hn hK σ hσ
  obtain ⟨e₂⟩ := Irred937.graphFixedRootGroup_mulEquiv_of_ringEquiv
    (K := GaloisField 2 (2 * n)) (K' := K) τ (frobQ 2 n) σ fun c => (hτ c).symm
  let φ := e.trans e₂.symm
  apply ggKGRootDatum_of_mulEquiv φ
  intro E hE _ h4 hsc
  have h3' : ¬ 3 ∣ 2 ^ n + 1 := by
    have hpos : 1 ≤ 2 ^ n := Nat.one_le_two_pow
    omega
  obtain ⟨ζ, hζ, -, hζo, -⟩ := ExcFrames.exists_threeFrame hn h3'
  have hζσ : frobQ 2 n (ζ : GaloisField 2 (2 * n)) = ζ := by
    rw [frobQ_apply]
    obtain ⟨k, hk⟩ := h3
    have hpos : 1 ≤ 2 ^ n := Nat.one_le_two_pow
    have hpow : 2 ^ n = 3 * k + 1 := by omega
    have hζ3 : (ζ : GaloisField 2 (2 * n)) ^ 3 = 1 := by
      rw [← Units.val_pow_eq_pow_val, hζ, Units.val_one]
    rw [hpow, pow_succ, pow_mul, hζ3, one_pow, one_mul]
  obtain ⟨c, hc⟩ := ExcFrames.twistedE6ThreeSCReference_holds hn h3' hζo hζ hE h4
    fun g hg hg3 => hsc g (fun a ha => (Subgroup.mem_centralizer_iff.mp hg a ha).symm) hg3
  have hframe : ExcFrames.twE6ThreeFrameHom hn h3' ζ hζ =
      ExcFrames.twE6SplitFrameHom (frobQ 2 n) ζ hζ hζσ := by
    ext s
    rfl
  apply ggKGRootDatumAt_of_mulEquiv (MulAut.conj c).symm
  have hback : E.map (MulAut.conj c).symm.toMonoidHom =
      (ExcFrames.twE6SplitFrameHom (frobQ 2 n) ζ hζ hζσ).range := by
    rw [hc, hframe, Subgroup.map_map]
    have hcomp : (MulAut.conj c).symm.toMonoidHom.comp (MulAut.conj c).toMonoidHom =
        MonoidHom.id _ := by
      apply MonoidHom.ext
      intro x
      exact (MulAut.conj c).symm_apply_apply x
    rw [hcomp, Subgroup.map_id]
  rw [hback]
  exact ggKGRootDatumAt_range_twE6SplitFrame_three hn h3 hζo hζ hζσ

theorem ggTorusRootSL2_recipeR_twE6Split_three {K : Type} [Field K] [Finite K] {n : ℕ}
    (hn : 1 ≤ n) (hK : Nat.card K = (2 ^ n) ^ 2) (h3 : 3 ∣ 2 ^ n - 1) :
    GGTorusRootSL2 3 4 (TwE6Delta.RecipeR K n) (TwE6Delta.RecipeI K n) := by
  have h3' : ¬ 3 ∣ 2 ^ n + 1 := by
    have hpos : 1 ≤ 2 ^ n := Nat.one_le_two_pow
    omega
  exact ggTorusRootSL2_of_rootDatum Nat.prime_three
    (fun φ hφ _ => TwE6Delta.recipeI_subset_inn_of_not_dvd hn hK h3' hφ)
    (TwE6Delta.center_recipeR_eq_bot hn hK)
    (TwE6Delta.ggCenterPrime_three_twE6 hn hK h3')
    (ggKGRootDatum_recipeR_twE6Split_three hn hK h3)

end CFSG.StandardType.TwE6SplitRootGen

namespace CFSG.StandardType

open CFSG.Assembly

theorem ggRealKGThreeRow_twe6Split
    : GGRealKGThreeRow .twe6Split := by
  intro p lab hp hlab _ hs
  obtain ⟨hp3, ⟨htag, hpn⟩, _⟩ := hs
  subst hp3
  refine TwE6Delta.labelAll htag ?_
  intro K _ _ hK
  have hn : 1 ≤ lab.n := hlab.1
  exact ⟨4, ggTorusLift_twE6Dvd_holds hn hK Nat.prime_three (by decide) hpn,
    TwE6SplitRootGen.ggTorusRootSL2_recipeR_twE6Split_three hn hK hpn⟩

end CFSG.StandardType
