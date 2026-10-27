module

public import CFSG.LocalAnalysis.StandardType.GGTBJNoB2derA1
public import CFSG.LocalAnalysis.GLTheoremA.CatB.FStdDiagExcHolds
public import CFSG.LocalAnalysis.StandardType.GGTBJNoB2derA6
public import CFSG.LocalAnalysis.StandardType.GGTCJDatum
public import CFSG.LocalAnalysis.StandardType.GGTableBExcBasic
public import CFSG.LocalAnalysis.StandardType.GGTableBTwE6DeltaOutdiag
public import CFSG.LocalAnalysis.GLTheoremA.S12.CanonTriLHolds
public import CFSG.Assembly.InCatalogConverse
public import CFSG.Assembly.Subnormal
public import CFSG.Sporadic.Fi24.ExtCentralizer
public import CFSG.Quasithin.Background.A3Structure36BPrime
public import CFSG.LocalAnalysis.GLTheoremA.S12.CanonSubcomp

public section

namespace CFSG.StandardType.S2MathAs4B2der1822

open CFSG CFSG.Assembly


private theorem a1big_smallOrd_b2der {S : Type} [Group S] (J : Subgroup S)
    (h : GGHasLabel (⟨.B2der, 0, 1⟩ : LargeEvenLabel) (↥J ⧸ Subgroup.center ↥J)) :
    CFSG.LocalAnalysis.GLTheoremA.HStdExcl.SmallOrd J := by
  obtain ⟨e⟩ := CFSG.StandardType.ggB2der_label_iso_A6 h
  right
  rw [Nat.card_congr e.toEquiv, nat_card_alternatingGroup, Nat.card_fin]
  norm_num

private theorem a1big_nab_of_simple_center_bot {R : Type} [Group R] (hsimple : IsSimpleGroup R)
    (hcen : Subgroup.center R = ⊥) : ∃ a b : R, a * b ≠ b * a := by
  haveI : Nontrivial R := hsimple.toNontrivial
  by_contra h
  push Not at h
  have htop : Subgroup.center R = ⊤ := by
    rw [eq_top_iff]
    intro x _
    rw [Subgroup.mem_center_iff]
    intro y
    exact h y x
  exact bot_ne_top (hcen.symm.trans htop)

theorem noB2derInput_exceptionalBig :
    SimpleNoB2derInput fun lab => lab.tag = .F4 ∨ lab.tag = .E6 ∨ lab.tag = .E7 ∨
      lab.tag = .E8 ∨ lab.tag = .twE6 := by
  intro lab hIn hP
  obtain ⟨t, l, n⟩ := lab
  rcases hP with hF4 | hE6 | hE7 | hE8 | hTwE6
  ·
    subst hF4
    intro Q hQ
    dsimp only [CFSG.StandardType.LargeEvenRawDatum, LargeEvenRecipeChevalley] at hQ
    obtain ⟨K, hfield, hfin, hcard, hQK⟩ := hQ
    dsimp only [CFSG.StandardType.LargeEvenRawDatum, LargeEvenRecipeChevalley]
    refine ⟨K, hfield, hfin, hcard, hQK, ?_⟩
    intro φ hφ1 hφ3 hφI J hJ hJlab
    have hn : 1 ≤ n := hIn.1
    let q : TauCeti.PrimePower := ⟨2, n, Nat.prime_two, by omega⟩
    have hq : q.card = 2 ^ n := TauCeti.PrimePower.card_def q
    have hv : (TauCeti.LieTypeIndex.F4 q).Valid := by simp
    let d : TauCeti.ValidLieTypeIndex := ⟨TauCeti.LieTypeIndex.F4 q, hv⟩
    obtain ⟨eQ⟩ := CFSG.StandardType.centerQuot_chevGroup_equiv K CFSG.Blueprint.Chevalley.Tag.F4
    obtain ⟨eB⟩ := CFSG.TauCetiBridge.Even.chevalleyBridgesAll.f4 q hv K (by rw [hq]; exact hcard)
    let e : LargeEvenCenterQuot (LargeEvenChevH LargeEvenCartanF4 K false) ≃*
        (TauCeti.CFSGIndex.lie d).Group := eQ.trans eB
    haveI : Finite (TauCeti.CFSGIndex.lie d).Group := (CFSG.Assembly.lie_finite_simple d).1
    haveI : Finite (LargeEvenCenterQuot (LargeEvenChevH LargeEvenCartanF4 K false)) :=
      Finite.of_equiv _ e.symm.toEquiv
    have hsimple : IsSimpleGroup (LargeEvenCenterQuot (LargeEvenChevH LargeEvenCartanF4 K false)) :=
      e.isSimpleGroup_congr.mpr (CFSG.Assembly.lie_finite_simple d).2
    have hcen : Subgroup.center
        (LargeEvenCenterQuot (LargeEvenChevH LargeEvenCartanF4 K false)) = ⊥ :=
      CFSG.StandardType.TableBExc.center_recipeGroup_eq_bot CFSG.Blueprint.Chevalley.Tag.F4 K
    have hna := a1big_nab_of_simple_center_bot hsimple hcen
    have hcan : CFSG.Assembly.LargeEvenRawDatum ⟨.F4, l, n⟩
        (fun R' _ I' _ =>
          ∃ e : LargeEvenCenterQuot (LargeEvenChevH LargeEvenCartanF4 K false) ≃* R',
          ∀ φ, φ ∈ LargeEvenChevIDImage LargeEvenCartanF4 K
              (LargeEvenChevH LargeEvenCartanF4 K false) →
            MulAut.congr e φ ∈ I') := by
      dsimp only [CFSG.Assembly.LargeEvenRawDatum, CFSG.Assembly.LargeEvenRecipeChevalley]
      exact ⟨K, hfield, hfin, hcard, ⟨MulEquiv.refl _, fun φ hφ => by
        rw [TCJ.tcjDatum_congr_refl]; exact hφ⟩⟩
    have hInnDiag : CFSG.LocalAnalysis.GLTheoremA.Y10GField.InnDiagKind
        (LargeEvenCenterQuot (LargeEvenChevH LargeEvenCartanF4 K false)) ⟨.F4, l, n⟩ φ :=
      TCJ.tcjDatum_innDiagKind_of_can (lab := ⟨.F4, l, n⟩) hIn hsimple hna hcan φ hφI
    have hφder : φ ∈ CFSG.ComponentClassification.OuterAutomorphisms.innAutDerived
        (LargeEvenCenterQuot (LargeEvenChevH LargeEvenCartanF4 K false)) :=
      CFSG.LocalAnalysis.GLTheoremA.CanonTriL.mem_innAutDerived_of_innDiagKind_exc
        hcen (Or.inl rfl) hInnDiag
    have hsmallJ : CFSG.LocalAnalysis.GLTheoremA.HStdExcl.SmallOrd J := a1big_smallOrd_b2der J hJlab
    have hJopen : CFSG.Open.IsComponentOf J
        (CFSG.HardMathSupport.Solomon.Coordinator.fixSubgroup φ) :=
      (show ggFixSub φ = CFSG.HardMathSupport.Solomon.Coordinator.fixSubgroup φ from by
        ext x; rfl) ▸ (CFSG.Assembly.isComponentOf_iff_open.mp hJ)
    have hc : (TauCeti.LieTypeIndex.F4 q).characteristic = 2 := by
      rw [TauCeti.LieTypeIndex.characteristic_F4]
    exact CFSG.LocalAnalysis.GLTheoremA.FStdDiag.smallExcRes_holds
      _ d (Or.inl (by
        change CFSG.HardMathSupport.Dickson.Sec6.FamF4 (TauCeti.LieTypeIndex.F4 q); trivial)) hc e φ
      hφder hφ3 hφ1 J hJopen hsmallJ
  ·
    subst hE6
    intro Q hQ
    dsimp only [CFSG.StandardType.LargeEvenRawDatum, LargeEvenRecipeChevalley] at hQ
    obtain ⟨K, hfield, hfin, hcard, hQK⟩ := hQ
    dsimp only [CFSG.StandardType.LargeEvenRawDatum, LargeEvenRecipeChevalley]
    refine ⟨K, hfield, hfin, hcard, hQK, ?_⟩
    intro φ hφ1 hφ3 hφI J hJ hJlab
    have hn : 1 ≤ n := hIn.1
    let q : TauCeti.PrimePower := ⟨2, n, Nat.prime_two, by omega⟩
    have hq : q.card = 2 ^ n := TauCeti.PrimePower.card_def q
    have hv : (TauCeti.LieTypeIndex.E6 q).Valid := by simp
    let d : TauCeti.ValidLieTypeIndex := ⟨TauCeti.LieTypeIndex.E6 q, hv⟩
    obtain ⟨eQ⟩ := CFSG.StandardType.centerQuot_chevGroup_equiv K CFSG.Blueprint.Chevalley.Tag.E6
    obtain ⟨eB⟩ := CFSG.TauCetiBridge.Even.chevalleyBridgesAll.e6 q hv K (by rw [hq]; exact hcard)
    let e : LargeEvenCenterQuot (LargeEvenChevH (LargeEvenCartanE 6) K false) ≃*
        (TauCeti.CFSGIndex.lie d).Group := eQ.trans eB
    haveI : Finite (TauCeti.CFSGIndex.lie d).Group := (CFSG.Assembly.lie_finite_simple d).1
    haveI : Finite (LargeEvenCenterQuot (LargeEvenChevH (LargeEvenCartanE 6) K false)) :=
      Finite.of_equiv _ e.symm.toEquiv
    have hsimple : IsSimpleGroup
        (LargeEvenCenterQuot (LargeEvenChevH (LargeEvenCartanE 6) K false)) :=
      e.isSimpleGroup_congr.mpr (CFSG.Assembly.lie_finite_simple d).2
    have hcen : Subgroup.center
        (LargeEvenCenterQuot (LargeEvenChevH (LargeEvenCartanE 6) K false)) = ⊥ :=
      CFSG.StandardType.TableBExc.center_recipeGroup_eq_bot CFSG.Blueprint.Chevalley.Tag.E6 K
    have hna := a1big_nab_of_simple_center_bot hsimple hcen
    have hcan : CFSG.Assembly.LargeEvenRawDatum ⟨.E6, l, n⟩
        (fun R' _ I' _ =>
          ∃ e : LargeEvenCenterQuot (LargeEvenChevH (LargeEvenCartanE 6) K false) ≃* R',
          ∀ φ, φ ∈ LargeEvenChevIDImage (LargeEvenCartanE 6) K
            (LargeEvenChevH (LargeEvenCartanE 6) K false) → MulAut.congr e φ ∈ I') := by
      dsimp only [CFSG.Assembly.LargeEvenRawDatum, CFSG.Assembly.LargeEvenRecipeChevalley]
      exact ⟨K, hfield, hfin, hcard, ⟨MulEquiv.refl _, fun φ hφ => by
        rw [TCJ.tcjDatum_congr_refl]; exact hφ⟩⟩
    have hInnDiag : CFSG.LocalAnalysis.GLTheoremA.Y10GField.InnDiagKind
        (LargeEvenCenterQuot (LargeEvenChevH (LargeEvenCartanE 6) K false)) ⟨.E6, l, n⟩ φ :=
      TCJ.tcjDatum_innDiagKind_of_can (lab := ⟨.E6, l, n⟩) hIn hsimple hna hcan φ hφI
    have hφder : φ ∈ CFSG.ComponentClassification.OuterAutomorphisms.innAutDerived
        (LargeEvenCenterQuot (LargeEvenChevH (LargeEvenCartanE 6) K false)) :=
      CFSG.LocalAnalysis.GLTheoremA.CanonTriL.mem_innAutDerived_of_innDiagKind_exc
        hcen (Or.inr (Or.inl rfl)) hInnDiag
    have hsmallJ : CFSG.LocalAnalysis.GLTheoremA.HStdExcl.SmallOrd J := a1big_smallOrd_b2der J hJlab
    have hJopen : CFSG.Open.IsComponentOf J
        (CFSG.HardMathSupport.Solomon.Coordinator.fixSubgroup φ) :=
      (show ggFixSub φ = CFSG.HardMathSupport.Solomon.Coordinator.fixSubgroup φ from by
        ext x; rfl) ▸ (CFSG.Assembly.isComponentOf_iff_open.mp hJ)
    have hc : (TauCeti.LieTypeIndex.E6 q).characteristic = 2 := by
      rw [TauCeti.LieTypeIndex.characteristic_E6]
    exact CFSG.LocalAnalysis.GLTheoremA.FStdDiag.smallExcRes_holds
      _ d (Or.inr (Or.inl (by
        change CFSG.HardMathSupport.Dickson.Sec6.FamE6 (TauCeti.LieTypeIndex.E6 q); trivial)))
      hc e φ hφder hφ3 hφ1 J hJopen hsmallJ
  ·
    subst hE7
    intro Q hQ
    dsimp only [CFSG.StandardType.LargeEvenRawDatum, LargeEvenRecipeChevalley] at hQ
    obtain ⟨K, hfield, hfin, hcard, hQK⟩ := hQ
    dsimp only [CFSG.StandardType.LargeEvenRawDatum, LargeEvenRecipeChevalley]
    refine ⟨K, hfield, hfin, hcard, hQK, ?_⟩
    intro φ hφ1 hφ3 hφI J hJ hJlab
    have hn : 1 ≤ n := hIn.1
    let q : TauCeti.PrimePower := ⟨2, n, Nat.prime_two, by omega⟩
    have hq : q.card = 2 ^ n := TauCeti.PrimePower.card_def q
    have hv : (TauCeti.LieTypeIndex.E7 q).Valid := by simp
    let d : TauCeti.ValidLieTypeIndex := ⟨TauCeti.LieTypeIndex.E7 q, hv⟩
    obtain ⟨eQ⟩ := CFSG.StandardType.centerQuot_chevGroup_equiv K CFSG.Blueprint.Chevalley.Tag.E7
    obtain ⟨eB⟩ := CFSG.TauCetiBridge.Even.chevalleyBridgesAll.e7 q hv K (by rw [hq]; exact hcard)
    let e : LargeEvenCenterQuot (LargeEvenChevH (LargeEvenCartanE 7) K false) ≃*
        (TauCeti.CFSGIndex.lie d).Group := eQ.trans eB
    haveI : Finite (TauCeti.CFSGIndex.lie d).Group := (CFSG.Assembly.lie_finite_simple d).1
    haveI : Finite (LargeEvenCenterQuot (LargeEvenChevH (LargeEvenCartanE 7) K false)) :=
      Finite.of_equiv _ e.symm.toEquiv
    have hsimple : IsSimpleGroup
        (LargeEvenCenterQuot (LargeEvenChevH (LargeEvenCartanE 7) K false)) :=
      e.isSimpleGroup_congr.mpr (CFSG.Assembly.lie_finite_simple d).2
    have hcen : Subgroup.center
        (LargeEvenCenterQuot (LargeEvenChevH (LargeEvenCartanE 7) K false)) = ⊥ :=
      CFSG.StandardType.TableBExc.center_recipeGroup_eq_bot CFSG.Blueprint.Chevalley.Tag.E7 K
    have hna := a1big_nab_of_simple_center_bot hsimple hcen
    have hcan : CFSG.Assembly.LargeEvenRawDatum ⟨.E7, l, n⟩
        (fun R' _ I' _ =>
          ∃ e : LargeEvenCenterQuot (LargeEvenChevH (LargeEvenCartanE 7) K false) ≃* R',
          ∀ φ, φ ∈ LargeEvenChevIDImage (LargeEvenCartanE 7) K
            (LargeEvenChevH (LargeEvenCartanE 7) K false) → MulAut.congr e φ ∈ I') := by
      dsimp only [CFSG.Assembly.LargeEvenRawDatum, CFSG.Assembly.LargeEvenRecipeChevalley]
      exact ⟨K, hfield, hfin, hcard, ⟨MulEquiv.refl _, fun φ hφ => by
        rw [TCJ.tcjDatum_congr_refl]; exact hφ⟩⟩
    have hInnDiag : CFSG.LocalAnalysis.GLTheoremA.Y10GField.InnDiagKind
        (LargeEvenCenterQuot (LargeEvenChevH (LargeEvenCartanE 7) K false)) ⟨.E7, l, n⟩ φ :=
      TCJ.tcjDatum_innDiagKind_of_can (lab := ⟨.E7, l, n⟩) hIn hsimple hna hcan φ hφI
    have hφder : φ ∈ CFSG.ComponentClassification.OuterAutomorphisms.innAutDerived
        (LargeEvenCenterQuot (LargeEvenChevH (LargeEvenCartanE 7) K false)) :=
      CFSG.LocalAnalysis.GLTheoremA.CanonTriL.mem_innAutDerived_of_innDiagKind_exc
        hcen (Or.inr (Or.inr (Or.inl rfl))) hInnDiag
    have hsmallJ : CFSG.LocalAnalysis.GLTheoremA.HStdExcl.SmallOrd J := a1big_smallOrd_b2der J hJlab
    have hJopen : CFSG.Open.IsComponentOf J
        (CFSG.HardMathSupport.Solomon.Coordinator.fixSubgroup φ) :=
      (show ggFixSub φ = CFSG.HardMathSupport.Solomon.Coordinator.fixSubgroup φ from by
        ext x; rfl) ▸ (CFSG.Assembly.isComponentOf_iff_open.mp hJ)
    have hc : (TauCeti.LieTypeIndex.E7 q).characteristic = 2 := by
      rw [TauCeti.LieTypeIndex.characteristic_E7]
    exact CFSG.LocalAnalysis.GLTheoremA.FStdDiag.smallExcRes_holds
      _ d (Or.inr (Or.inr (Or.inr (Or.inl (by
        change CFSG.HardMathSupport.Dickson.Sec6.FamE7 (TauCeti.LieTypeIndex.E7 q); trivial)))))
      hc e φ hφder hφ3 hφ1 J hJopen hsmallJ
  ·
    subst hE8
    intro Q hQ
    dsimp only [CFSG.StandardType.LargeEvenRawDatum, LargeEvenRecipeChevalley] at hQ
    obtain ⟨K, hfield, hfin, hcard, hQK⟩ := hQ
    dsimp only [CFSG.StandardType.LargeEvenRawDatum, LargeEvenRecipeChevalley]
    refine ⟨K, hfield, hfin, hcard, hQK, ?_⟩
    intro φ hφ1 hφ3 hφI J hJ hJlab
    have hn : 1 ≤ n := hIn.1
    let q : TauCeti.PrimePower := ⟨2, n, Nat.prime_two, by omega⟩
    have hq : q.card = 2 ^ n := TauCeti.PrimePower.card_def q
    have hv : (TauCeti.LieTypeIndex.E8 q).Valid := by simp
    let d : TauCeti.ValidLieTypeIndex := ⟨TauCeti.LieTypeIndex.E8 q, hv⟩
    obtain ⟨eQ⟩ := CFSG.StandardType.centerQuot_chevGroup_equiv K CFSG.Blueprint.Chevalley.Tag.E8
    obtain ⟨eB⟩ := CFSG.TauCetiBridge.Even.chevalleyBridgesAll.e8 q hv K (by rw [hq]; exact hcard)
    let e : LargeEvenCenterQuot (LargeEvenChevH (LargeEvenCartanE 8) K false) ≃*
        (TauCeti.CFSGIndex.lie d).Group := eQ.trans eB
    haveI : Finite (TauCeti.CFSGIndex.lie d).Group := (CFSG.Assembly.lie_finite_simple d).1
    haveI : Finite (LargeEvenCenterQuot (LargeEvenChevH (LargeEvenCartanE 8) K false)) :=
      Finite.of_equiv _ e.symm.toEquiv
    have hsimple : IsSimpleGroup
        (LargeEvenCenterQuot (LargeEvenChevH (LargeEvenCartanE 8) K false)) :=
      e.isSimpleGroup_congr.mpr (CFSG.Assembly.lie_finite_simple d).2
    have hcen : Subgroup.center
        (LargeEvenCenterQuot (LargeEvenChevH (LargeEvenCartanE 8) K false)) = ⊥ :=
      CFSG.StandardType.TableBExc.center_recipeGroup_eq_bot CFSG.Blueprint.Chevalley.Tag.E8 K
    have hna := a1big_nab_of_simple_center_bot hsimple hcen
    have hcan : CFSG.Assembly.LargeEvenRawDatum ⟨.E8, l, n⟩
        (fun R' _ I' _ =>
          ∃ e : LargeEvenCenterQuot (LargeEvenChevH (LargeEvenCartanE 8) K false) ≃* R',
          ∀ φ, φ ∈ LargeEvenChevIDImage (LargeEvenCartanE 8) K
            (LargeEvenChevH (LargeEvenCartanE 8) K false) → MulAut.congr e φ ∈ I') := by
      dsimp only [CFSG.Assembly.LargeEvenRawDatum, CFSG.Assembly.LargeEvenRecipeChevalley]
      exact ⟨K, hfield, hfin, hcard, ⟨MulEquiv.refl _, fun φ hφ => by
        rw [TCJ.tcjDatum_congr_refl]; exact hφ⟩⟩
    have hInnDiag : CFSG.LocalAnalysis.GLTheoremA.Y10GField.InnDiagKind
        (LargeEvenCenterQuot (LargeEvenChevH (LargeEvenCartanE 8) K false)) ⟨.E8, l, n⟩ φ :=
      TCJ.tcjDatum_innDiagKind_of_can (lab := ⟨.E8, l, n⟩) hIn hsimple hna hcan φ hφI
    have hφder : φ ∈ CFSG.ComponentClassification.OuterAutomorphisms.innAutDerived
        (LargeEvenCenterQuot (LargeEvenChevH (LargeEvenCartanE 8) K false)) :=
      CFSG.LocalAnalysis.GLTheoremA.CanonTriL.mem_innAutDerived_of_innDiagKind_exc
        hcen (Or.inr (Or.inr (Or.inr (Or.inl rfl)))) hInnDiag
    have hsmallJ : CFSG.LocalAnalysis.GLTheoremA.HStdExcl.SmallOrd J := a1big_smallOrd_b2der J hJlab
    have hJopen : CFSG.Open.IsComponentOf J
        (CFSG.HardMathSupport.Solomon.Coordinator.fixSubgroup φ) :=
      (show ggFixSub φ = CFSG.HardMathSupport.Solomon.Coordinator.fixSubgroup φ from by
        ext x; rfl) ▸ (CFSG.Assembly.isComponentOf_iff_open.mp hJ)
    have hc : (TauCeti.LieTypeIndex.E8 q).characteristic = 2 := by
      rw [TauCeti.LieTypeIndex.characteristic_E8]
    exact CFSG.LocalAnalysis.GLTheoremA.FStdDiag.smallExcRes_holds
      _ d (Or.inr (Or.inr (Or.inr (Or.inr (by
        change CFSG.HardMathSupport.Dickson.Sec6.FamE8 (TauCeti.LieTypeIndex.E8 q); trivial)))))
      hc e φ hφder hφ3 hφ1 J hJopen hsmallJ
  ·
    subst hTwE6
    intro Q hQ
    dsimp only [CFSG.StandardType.LargeEvenRawDatum, LargeEvenRecipeTwisted] at hQ
    obtain ⟨K, hfield, hfin, hcard, hQK⟩ := hQ
    dsimp only [CFSG.StandardType.LargeEvenRawDatum, LargeEvenRecipeTwisted]
    refine ⟨K, hfield, hfin, hcard, hQK, ?_⟩
    intro φ hφ1 hφ3 hφI J hJ hJlab
    have hn : 1 ≤ n := hIn.1
    let q : TauCeti.PrimePower := ⟨2, n, Nat.prime_two, by omega⟩
    have hq : q.card = 2 ^ n := TauCeti.PrimePower.card_def q
    have hv : (TauCeti.LieTypeIndex.twistedE6 q).Valid := by simp
    let d : TauCeti.ValidLieTypeIndex := ⟨TauCeti.LieTypeIndex.twistedE6 q, hv⟩
    haveI : CharP K 2 := TCJ.tcjDatum_charP_two_of_card (m := n * 2) (by rw [hcard, pow_mul])
    let σ : K →+* K := iterateFrobenius K 2 n
    have hσ : ∀ c, σ c = c ^ 2 ^ n := fun c => by
      change (iterateFrobenius K 2 n) c = c ^ 2 ^ n
      rw [iterateFrobenius_def]
    have hKq : Nat.card K = q.card ^ CFSG.Blueprint.Chevalley.TwistTag.E6.order := by
      rw [hq, show CFSG.Blueprint.Chevalley.TwistTag.E6.order = 2 from rfl]
      exact hcard
    obtain ⟨eQ⟩ := CFSG.StandardType.centerQuot_twistedH_equiv K
      CFSG.Blueprint.Chevalley.TwistTag.E6 n σ hσ
    obtain ⟨eB⟩ := CFSG.TauCetiBridge.Even.chevalleyBridgesAll.twistedE6 q hv K hKq σ
      (fun x => by rw [hσ, hq])
    let e : LargeEvenCenterQuot
        (LargeEvenTwistedH (LargeEvenCartanE 6) K LargeEvenRhoE6 n) ≃*
        (TauCeti.CFSGIndex.lie d).Group := eQ.trans eB
    haveI : Finite (TauCeti.CFSGIndex.lie d).Group := (CFSG.Assembly.lie_finite_simple d).1
    haveI : Finite
        (LargeEvenCenterQuot (LargeEvenTwistedH (LargeEvenCartanE 6) K LargeEvenRhoE6 n)) :=
      Finite.of_equiv _ e.symm.toEquiv
    have hsimple : IsSimpleGroup
        (LargeEvenCenterQuot (LargeEvenTwistedH (LargeEvenCartanE 6) K LargeEvenRhoE6 n)) :=
      e.isSimpleGroup_congr.mpr (CFSG.Assembly.lie_finite_simple d).2
    have hcen : Subgroup.center
        (LargeEvenCenterQuot (LargeEvenTwistedH (LargeEvenCartanE 6) K LargeEvenRhoE6 n)) = ⊥ :=
      CFSG.StandardType.TwE6Delta.center_recipeR_eq_bot hn hcard
    have hna := a1big_nab_of_simple_center_bot hsimple hcen
    have hcan : CFSG.Assembly.LargeEvenRawDatum ⟨.twE6, l, n⟩
        (fun R' _ I' _ =>
          ∃ e : LargeEvenCenterQuot
              (LargeEvenTwistedH (LargeEvenCartanE 6) K LargeEvenRhoE6 n) ≃* R',
          ∀ φ, φ ∈ LargeEvenChevIDImage (LargeEvenCartanE 6) K
            (LargeEvenTwistedH (LargeEvenCartanE 6) K LargeEvenRhoE6 n) →
            MulAut.congr e φ ∈ I') := by
      dsimp only [CFSG.Assembly.LargeEvenRawDatum, CFSG.Assembly.LargeEvenRecipeTwisted]
      exact ⟨K, hfield, hfin, hcard, ⟨MulEquiv.refl _, fun φ hφ => by
        rw [TCJ.tcjDatum_congr_refl]; exact hφ⟩⟩
    have hInnDiag : CFSG.LocalAnalysis.GLTheoremA.Y10GField.InnDiagKind
        (LargeEvenCenterQuot
          (LargeEvenTwistedH (LargeEvenCartanE 6) K LargeEvenRhoE6 n)) ⟨.twE6, l, n⟩ φ :=
      TCJ.tcjDatum_innDiagKind_of_can (lab := ⟨.twE6, l, n⟩) hIn hsimple hna hcan φ hφI
    have hφder : φ ∈ CFSG.ComponentClassification.OuterAutomorphisms.innAutDerived
        (LargeEvenCenterQuot
          (LargeEvenTwistedH (LargeEvenCartanE 6) K LargeEvenRhoE6 n)) :=
      CFSG.LocalAnalysis.GLTheoremA.CanonTriL.mem_innAutDerived_of_innDiagKind_exc
        hcen (Or.inr (Or.inr (Or.inr (Or.inr rfl)))) hInnDiag
    have hsmallJ : CFSG.LocalAnalysis.GLTheoremA.HStdExcl.SmallOrd J := a1big_smallOrd_b2der J hJlab
    have hJopen : CFSG.Open.IsComponentOf J
        (CFSG.HardMathSupport.Solomon.Coordinator.fixSubgroup φ) :=
      (show ggFixSub φ = CFSG.HardMathSupport.Solomon.Coordinator.fixSubgroup φ from by
        ext x; rfl) ▸ (CFSG.Assembly.isComponentOf_iff_open.mp hJ)
    have hc : (TauCeti.LieTypeIndex.twistedE6 q).characteristic = 2 := by
      rw [TauCeti.LieTypeIndex.characteristic_twistedE6]
    exact CFSG.LocalAnalysis.GLTheoremA.FStdDiag.smallExcRes_holds
      _ d (Or.inr (Or.inr (Or.inl (by
        change CFSG.HardMathSupport.Dickson.Sec6.FamTwE6 (TauCeti.LieTypeIndex.twistedE6 q);
          trivial)))) hc e φ hφder hφ3 hφ1 J hJopen hsmallJ

end CFSG.StandardType.S2MathAs4B2der1822

end
