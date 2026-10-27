module

public import CFSG.LocalAnalysis.StandardType.GGExcFieldRankTransfer
public import CFSG.LocalAnalysis.StandardType.GGExcFieldRankE6
public import CFSG.LocalAnalysis.StandardType.GGExcFieldAutCentRankF4Rank
public import CFSG.LieType.SeitzGeneration.ExcTorusRankTw
public import CFSG.LieType.SeitzGeneration.ExcTorusThreeTwRank
public import CFSG.LieType.SeitzGeneration.ExcTwistedClasses
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcInnerSylow
public import CFSG.LieType.SeitzGeneration.ExcHighThree.TwE6InF4Sylow
public import CFSG.HardMathSupport.Lang.AnisoE6.TwPlane
public import CFSG.HardMathSupport.Lang.AnisoE6.F4GraphFixed
public import CFSG.LieType.Chevalley.GraphFixedData
public import CFSG.LieType.Chevalley.TwistMapFixed
public import CFSG.GroupTheory.HallHigmanPiCore
public import CFSG.LieType.Ree.LargeReeEightTorus
public import CFSG.LieType.SeitzGeneration.ExcHighThree.TwE6InF4Close
public import CFSG.LocalAnalysis.ComponentClassification.AutL2FactsCentModel
public import CFSG.LocalAnalysis.ComponentClassification.AutL2FactsFieldAut
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalSixStructure
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueUStatement
public import CFSG.LocalAnalysis.ComponentClassification.GSLitType
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogSpExclusion
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCorrCentralSylowMaximality
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedGSAContainedSource
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedLayerOddCoreUnbalancingTriple
public import CFSG.LocalAnalysis.ComponentInitial.SuzukiModelSchreier
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherEvenOrthogonalModel
public import CFSG.LocalAnalysis.QuasithinUnique.SQTK.TypeB2
public import CFSG.LocalAnalysis.QuasithinUnique.SQTK.Unitary
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.SuzukiModelPointStructure
public import CFSG.RankThree.CentralLiftSO.SplitTorusWeyl
public import CFSG.RankThree.Classical.SteinbergBJSymplecticSquareZeroCentralizer
public import CFSG.RankThree.Lattice.SteinbergBIOrbitQuotFull
public import CFSG.RankThree.PartOne.CTP.SeitzFineG2
public import CFSG.RankThree.PartOne.CTP.StrongPBridgeRest
public import CFSG.RankThree.PartOne.KC.LinearCommutatorOdd
public import CFSG.RankThree.PartOne.KC.LinearDegreeFive
public import CFSG.RankThree.PartOne.KC.OrthogonalD4WitnessEven
public import CFSG.RankThree.PartOne.KC.OrthogonalD4WitnessOdd
public import CFSG.RankThree.PartOne.KC.UnitaryHigherCrossPrimeTorus
public import CFSG.RankThree.PartOne.KC.UnitaryPlaneEndpoints
public import CFSG.RankThree.PartOne.KE.A1SL2
public import CFSG.RankThree.PartOne.KE.A1Torus
public import CFSG.RankThree.PartOne.KE.A2Family
public import CFSG.RankThree.PartOne.KE.A2Shape
public import CFSG.RankThree.PartOne.KE.SigmaUntwisted
public import CFSG.RankThree.PartOne.KLR.Master
public import CFSG.RankThree.PartOne.KLR.SectorAssembly
public import CFSG.RankThree.PartOne.S11d.OutExceptional
public import CFSG.RankThree.PartOne.S11d.OutLinear
public import CFSG.RankThree.PartOne.S8.Statements
public import CFSG.RankThree.PartTwo.KFacts.KS14SzLie
public import CFSG.RankThree.PartTwo.Sec4.Census.Interface
public import CFSG.RankThree.SteinbergR3EOrthogonalCoprimeCyclic
public import CFSG.SignalizerFunctorTheorem.Nonsolvable.SolComponent
public import CFSG.Sporadic.Schreier.TitsOther
public import CFSG.StronglyEmbedded.ParityCriterion
public import Certificates.Certificate1
public import Certificates.Certificate2

public section

namespace CFSG.StandardType

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.SeitzGeneration
  CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.HardMathSupport.Lang.AnisoE6
  CFSG.RankThree.Lattice CFSG.RankThree.PartOne.KE Polynomial
open scoped Matrix
open CFSG.Open (IsElemAbelian)

private theorem degCountTw_one : degCountTw 1 = 4 := by
  rw [degCountTw, show ennola 1 = 2 from by decide]
  decide

private theorem degCountTw_two : degCountTw 2 = 6 := by
  rw [degCountTw, show ennola 2 = 1 from by decide]
  decide

private theorem degCountTw_three : degCountTw 3 = 2 := by
  rw [degCountTw, show ennola 3 = 6 from by decide]
  decide

private theorem degCountTw_four : degCountTw 4 = 2 := by
  rw [degCountTw, show ennola 4 = 4 from by decide]
  decide

private theorem degCountTw_six : degCountTw 6 = 3 := by
  rw [degCountTw, show ennola 6 = 3 from by decide]
  decide

private theorem not_dvd_small_of_three_lt {p k : ℕ} (hp : p.Prime) (hp3 : 3 < p)
    (hk0 : 0 < k) (hk : k ≤ 6) (hk5 : k ≠ 5) : ¬ p ∣ k := by
  intro h
  have hle : p ≤ k := Nat.le_of_dvd hk0 h
  have hp4 : 4 ≤ p := by omega
  have hp6 : p ≤ 6 := by omega
  interval_cases p
  · exact absurd hp (by norm_num)
  · have hk6 : k = 6 := by omega
    subst k
    norm_num at h
  · exact absurd hp (by norm_num)

private theorem not_dvd_of_charP_two {ℓ f p : ℕ} (hℓ : ℓ.Prime) {K : Type} [Field K]
    [CharP K 2] (hK : Nat.card K = (ℓ ^ f) ^ 2) (hp : p.Prime) (hp2 : p ≠ 2) :
    ¬ p ∣ ℓ ^ f := by
  have hKne : Nat.card K ≠ 0 := by
    rw [hK]
    exact pow_ne_zero 2 (pow_ne_zero f hℓ.ne_zero)
  haveI : Finite K := Nat.finite_of_card_ne_zero hKne
  haveI : Fintype K := Fintype.ofFinite K
  obtain ⟨n, -, hncard⟩ := FiniteField.card (K := K) 2
  have hKpow : Nat.card K = 2 ^ (n : ℕ) := by
    rw [Nat.card_eq_fintype_card]
    exact hncard
  intro h
  have hd : p ∣ Nat.card K := by
    rw [hK]
    exact h.trans (dvd_pow_self (ℓ ^ f) (by norm_num))
  rw [hKpow] at hd
  exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 (hp.dvd_of_dvd_pow hd))

theorem rankLE_twistedE6 {ℓ f : ℕ} (hℓ : ℓ.Prime) (hf : 1 ≤ f) (K : Type) [Field K]
    [CharP K 2] (hK : Nat.card K = (ℓ ^ f) ^ 2) (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ (ℓ ^ f))
    {p e : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2)
    (he : orderOf (((ℓ ^ f : ℕ)) : ZMod p) = e) :
    GGElemAbelianRankLE (twistedE6RootGroup K σ) p (degCountTw e) := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  have hKne : Nat.card K ≠ 0 := by
    rw [hK]
    exact pow_ne_zero 2 (pow_ne_zero f hℓ.ne_zero)
  haveI : Finite K := Nat.finite_of_card_ne_zero hKne
  have hpq : ¬ p ∣ ℓ ^ f := not_dvd_of_charP_two hℓ hK hp hp2
  have he0 : e ≠ 0 := he ▸ orderOf_natCast_ne_zero hp hpq
  intro E hE
  by_cases h0 : degCountTw e = 0
  ·
    have hp3 : 3 < p := by
      by_contra hle
      have hp_eq : p = 3 := by
        have hp2le := hp.two_le
        have hp3le : p ≤ 3 := by omega
        interval_cases p
        · exact absurd rfl hp2
        · rfl
      subst p
      have hq0 : (((ℓ ^ f : ℕ)) : ZMod 3) ≠ 0 := fun h =>
        hpq ((ZMod.natCast_eq_zero_iff _ _).1 h)
      have hedvd : e ∣ 3 - 1 := he ▸ ZMod.orderOf_dvd_card_sub_one hq0
      have hepos : 1 ≤ e := Nat.pos_of_ne_zero (he ▸ orderOf_natCast_ne_zero hp hpq)
      have hele : e ≤ 2 := Nat.le_of_dvd (by norm_num) hedvd
      interval_cases e
      · rw [degCountTw_one] at h0; omega
      · rw [degCountTw_two] at h0; omega
    have hE1 : Nat.card E = 1 :=
      elemAbelian_card_eq_one_of_degCountTw_zero hℓ hf K hK σ hσ hp hp3 hpq he h0 hE
    rw [hE1, h0, pow_zero]
  · by_cases h1 : degCountTw e = 1
    ·
      have hcnt : degCountTw (orderOf (((ℓ ^ f : ℕ)) : ZMod p)) ≤ 1 := by
        rw [he]
        omega
      simpa [h1] using (rankLE1_twistedE6 hℓ hf K hK σ hσ hp hpq hcnt) E hE
    · by_cases h2 : degCountTw e = 2
      ·
        rcases degCountTw_eq_two h2 with rfl | rfl
        · simpa [degCountTw_three] using
            (sylowTorus_twistedE6_three hℓ hf K hK σ hσ hp he).rank_le hp hE
        · simpa [degCountTw_four] using
            (sylowTorus_twistedE6_four hℓ hf K hK σ hσ hp he).rank_le hp hE
      ·
        have hcnt3 : 3 ≤ degCountTw e := by omega
        rcases eq_of_three_le_degCountTw hcnt3 with rfl | rfl | rfl
        ·
          by_cases hp3eq : p = 3
          ·
            subst p
            have hkcard : Nat.card (fixSubfield σ) = ℓ ^ f := by
              simpa [fixSubfield] using
                CFSG.RankThree.Chevalley.card_eqLocusField_of_pow (p := ℓ) (f := f) hℓ hf
                  (K := K) hK (σ := σ.toRingHom) hσ
            have hkpos : 1 ≤ Nat.card (fixSubfield σ) := Nat.card_pos
            have hk2 : 2 ≤ Nat.card (fixSubfield σ) := by
              rw [hkcard]
              exact Nat.one_lt_pow (by omega : f ≠ 0) hℓ.one_lt
            have hx : (((ℓ ^ f : ℕ)) : ZMod 3) = 1 := orderOf_eq_one_iff.1 he
            have hkord : orderOf ((Nat.card (fixSubfield σ) : ℕ) : ZMod 3) = 1 := by
              rw [hkcard, hx, orderOf_one]
            have hk3 : ((Nat.card (fixSubfield σ) : ℕ) : ZMod 3) = 1 :=
              orderOf_eq_one_iff.1 hkord
            have hq1 : Nat.card (fixSubfield σ) % 3 = 1 := by
              rw [← ZMod.val_natCast 3 (Nat.card (fixSubfield σ)), hk3]
              exact ZMod.val_one'' (by norm_num : (3 : ℕ) ≠ 1)
            have hσk : ∀ c : K, σ c = c ^ Nat.card (fixSubfield σ) := by
              intro c
              rw [hσ, hkcard]
            have hKk : Nat.card K = Nat.card (fixSubfield σ) ^ 2 := by
              rw [hK, hkcard]
            haveI : Finite (fixSubfield σ) :=
              Finite.of_injective (fun x : fixSubfield σ => (x : K)) Subtype.val_injective
            have hfix : ∀ c : fixSubfield σ, σ (algebraMap (fixSubfield σ) K c) =
                algebraMap (fixSubfield σ) K c := fun c => c.2
            obtain ⟨g, hg⟩ :=
              ExcHighThree.threeSubgroup_conj_into_F4 (k := fixSubfield σ) (K := K) σ hσk hKk
                hfix hq1 hk2 E (fun x hx => hE.2 x hx)
            set φ : adjointGroup .F4 (fixSubfield σ) →* twistedE6RootGroup K σ :=
              (phiG σ hfix).comp (e6FixedF4EquivAll (fixSubfield σ)).symm.toMonoidHom
              with hφdef
            have hφ : Function.Injective φ :=
              (phiG_injective σ hfix).comp (MulEquiv.injective _)
            set E₃ : Subgroup (adjointGroup .F4 (fixSubfield σ)) :=
              (E.map (MulAut.conj g).toMonoidHom).comap φ with hE₃def
            have hE₃ : IsElemAbelian 3 E₃ :=
              isElemAbelian_comap_of_injective φ hφ (hE.map _)
            have hd3 : 3 ∣ Nat.card (fixSubfield σ) ^ 2 - 1 :=
              (dvd_pow_sub_one_iff_orderOf (p := 3) (q := Nat.card (fixSubfield σ)) (e := 1)
                (d := 2) hkpos hkord).2 (by norm_num : 1 ∣ 2)
            have h4 : Nat.card E₃ ≤ 3 ^ 4 :=
              ExcFieldAutCentRankF4.card_le_pow_four (K := fixSubfield σ) (p := 3)
                Nat.prime_three (by norm_num) hd3 hE₃
            have hcard1 : Nat.card (E.map (MulAut.conj g).toMonoidHom) = Nat.card E :=
              Subgroup.card_map_of_injective (MulAut.conj g).injective
            have hmap : E₃.map φ = E.map (MulAut.conj g).toMonoidHom :=
              Subgroup.map_comap_eq_self hg
            have hcard2 : Nat.card E₃ = Nat.card (E.map (MulAut.conj g).toMonoidHom) := by
              rw [← Subgroup.card_map_of_injective (K := E₃) (f := φ) hφ, hmap]
            calc Nat.card E = Nat.card (E.map (MulAut.conj g).toMonoidHom) := hcard1.symm
              _ = Nat.card E₃ := hcard2.symm
              _ ≤ 3 ^ 4 := h4
              _ = 3 ^ degCountTw 1 := by rw [degCountTw_one]
          ·
            have hp3 : 3 < p := by
              by_contra hle
              have hp2le := hp.two_le
              have hp3le : p ≤ 3 := by omega
              interval_cases p
              · exact absurd rfl hp2
              · exact absurd rfl hp3eq
            have hS : SylowTorus (twistedE6RootGroup K σ) p 4 := by
              have hv : ∀ x, ((coxeterSystem TwistTag.E6.tag).wordProd twE6OneWord) • x =
                  toMat TwistTag.E6.tag.rank twE6OneMat *ᵥ permLattice TwistTag.E6.perm x :=
                fun x => by
                  rw [wordProd_smul_eq_wordMat_mulVec, twE6One_wordMat, toMat_lmul,
                    permLattice_E6_eq, Matrix.mulVec_mulVec]
              have he' : orderOf (((-((ℓ ^ f : ℕ) : ℤ) : ℤ)) : ZMod p) = 2 := by
                have h := orderOf_neg_natCast_zmod hp hp2 hpq he
                rwa [show ennola 1 = 2 from by decide] at h
              have hΦ : ∀ x : ℤ, ((cyclotomic 2 ℤ).eval (-x)).natAbs =
                  ((cyclotomic 1 ℤ).eval x).natAbs := fun x => by
                rw [cyclotomic_two, cyclotomic_one, eval_add, eval_sub, eval_X, eval_one,
                  eval_X, eval_one, show -x + 1 = -(x - 1) by ring, Int.natAbs_neg]
              have hdeg : ∀ d ∈ degreesE Tag.E6, (2 : ℕ) ∣ d → ¬ p ∣ d / 2 := by
                intro d hd h2d
                simp only [degreesE, List.mem_cons, List.not_mem_nil, or_false] at hd
                rcases hd with rfl | rfl | rfl | rfl | rfl | rfl
                · norm_num at h2d ⊢
                  exact hp.ne_one
                · norm_num at h2d
                · norm_num at h2d ⊢
                  exact not_dvd_small_of_three_lt (k := 3) hp hp3 (by norm_num) (by norm_num)
                    (by norm_num)
                · norm_num at h2d ⊢
                  exact not_dvd_small_of_three_lt (k := 4) hp hp3 (by norm_num) (by norm_num)
                    (by norm_num)
                · norm_num at h2d
                · norm_num at h2d ⊢
                  exact not_dvd_small_of_three_lt (k := 6) hp hp3 (by norm_num) (by norm_num)
                    (by norm_num)
              exact sylowTorus_twistedE6_of_blocks_of_three_lt hℓ hf K hK σ hσ hp hp3 hpq _ hv
                [1, 1, 1, 1, 2, 2] twE6One_charpoly (by norm_num) twE6One_pow (Or.inr (by decide))
                he he' hΦ (by decide) hdeg (by decide)
            simpa [degCountTw_one] using hS.rank_le hp hE
        ·
          have he1 : orderOf ((Nat.card K : ℕ) : ZMod p) = 1 := by
            rw [hK]
            have hsq : (((ℓ ^ f : ℕ)) : ZMod p) ^ 2 = 1 := by
              have h := pow_orderOf_eq_one (((ℓ ^ f : ℕ)) : ZMod p)
              rwa [he] at h
            have hcast : ((((ℓ ^ f) ^ 2 : ℕ)) : ZMod p) = 1 := by
              rw [Nat.cast_pow, hsq]
            rw [hcast, orderOf_one]
          have hR : GGElemAbelianRankLE (adjointGroup TwistTag.E6.tag K) p (degCount .E6 1) :=
            rankLE_E6 (K := K) (p := p) (e := 1) hp hp2 he1
          have hle : twistedE6RootGroup K σ ≤ adjointGroup TwistTag.E6.tag K :=
            (graphFixedRootGroup_le TwistTag.E6 K σ.toRingHom).trans
              (twistedFixedGroup_le_adjointGroup TwistTag.E6 K σ.toRingHom)
          let φ : twistedE6RootGroup K σ →* adjointGroup TwistTag.E6.tag K :=
            MonoidHom.codRestrict (twistedE6RootGroup K σ).subtype _
              (fun x => hle x.2)
          have hφ : Function.Injective φ := by
            intro x y hxy
            exact Subtype.ext (congrArg
              (fun z : adjointGroup TwistTag.E6.tag K => (z : ModGL TwistTag.E6.tag K)) hxy)
          have hR' : GGElemAbelianRankLE (twistedE6RootGroup K σ) p (degCount .E6 1) := by
            intro F hF
            have h' := hR (F.map φ) (hF.map φ)
            rwa [Subgroup.card_map_of_injective hφ] at h'
          have hdeg : degCountTw 2 = degCount .E6 1 := by
            rw [degCountTw_two, show degCount .E6 1 = 6 from by decide]
          simpa [hdeg] using hR' E hE
        ·
          have hq0 : (((ℓ ^ f : ℕ)) : ZMod p) ≠ 0 := fun h =>
            hpq ((ZMod.natCast_eq_zero_iff _ _).1 h)
          have hedvd : 6 ∣ p - 1 := he ▸ ZMod.orderOf_dvd_card_sub_one hq0
          have hp3 : 3 < p := by
            have hp2' : 2 ≤ p := hp.two_le
            have h6 : 6 ≤ p - 1 := Nat.le_of_dvd (by omega) hedvd
            omega
          have hS : SylowTorus (twistedE6RootGroup K σ) p 3 := by
            have hv : ∀ x, ((coxeterSystem TwistTag.E6.tag).wordProd twE6SixWord) • x =
                toMat TwistTag.E6.tag.rank twE6SixMat *ᵥ permLattice TwistTag.E6.perm x :=
              fun x => by
                rw [wordProd_smul_eq_wordMat_mulVec, twE6Six_wordMat, toMat_lmul,
                  permLattice_E6_eq, Matrix.mulVec_mulVec]
            have he' : orderOf (((-((ℓ ^ f : ℕ) : ℤ) : ℤ)) : ZMod p) = 3 := by
              have h := orderOf_neg_natCast_zmod hp hp2 hpq he
              rwa [show ennola 6 = 3 from by decide] at h
            have hΦ : ∀ x : ℤ, ((cyclotomic 3 ℤ).eval (-x)).natAbs =
                ((cyclotomic 6 ℤ).eval x).natAbs := fun x => by
              rw [cyclotomic_six_eq, cyclotomic_three_eq]
              simp only [eval_add, eval_sub, eval_pow, eval_X, eval_one]
              congr 1
              ring
            have hdeg : ∀ d ∈ degreesE Tag.E6, (3 : ℕ) ∣ d → ¬ p ∣ d / 3 := by
              intro d hd h3d
              simp only [degreesE, List.mem_cons, List.not_mem_nil, or_false] at hd
              rcases hd with rfl | rfl | rfl | rfl | rfl | rfl
              · norm_num at h3d
              · norm_num at h3d
              · norm_num at h3d ⊢
                exact not_dvd_small_of_three_lt (k := 2) hp hp3 (by norm_num) (by norm_num)
                  (by norm_num)
              · norm_num at h3d
              · norm_num at h3d ⊢
                exact not_dvd_small_of_three_lt (k := 3) hp hp3 (by norm_num) (by norm_num)
                  (by norm_num)
              · norm_num at h3d ⊢
                exact not_dvd_small_of_three_lt (k := 4) hp hp3 (by norm_num) (by norm_num)
                  (by norm_num)
            exact sylowTorus_twistedE6_of_blocks_of_three_lt hℓ hf K hK σ hσ hp hp3 hpq _ hv
              [6, 6, 6] twE6Six_charpoly (by norm_num) twE6Six_pow (Or.inl rfl) he he' hΦ
              (by decide) hdeg (by decide)
          simpa [degCountTw_six] using hS.rank_le hp hE

theorem exists_twistedE6 {ℓ f : ℕ} (hℓ : ℓ.Prime) (hf : 1 ≤ f) (K : Type) [Field K]
    [CharP K 2] (hK : Nat.card K = (ℓ ^ f) ^ 2) (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ (ℓ ^ f))
    {p e : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2)
    (he : orderOf (((ℓ ^ f : ℕ)) : ZMod p) = e) :
    GGExcElemAbelianExists (twistedE6RootGroup K σ) p (degCountTw e - 1) := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  have hpq : ¬ p ∣ ℓ ^ f := not_dvd_of_charP_two hℓ hK hp hp2
  by_cases h0 : degCountTw e = 0
  · refine ⟨⊥, CFSG.Open.isElemAbelian_bot p, ?_⟩
    rw [h0]
    simp
  · by_cases h1 : degCountTw e = 1
    · refine ⟨⊥, CFSG.Open.isElemAbelian_bot p, ?_⟩
      rw [h1]
      simp
    · by_cases h2 : degCountTw e = 2
      ·
        rcases degCountTw_eq_two h2 with rfl | rfl
        · obtain ⟨E, hE, hcard⟩ :=
            (sylowTorus_twistedE6_three hℓ hf K hK σ hσ hp he).exists_elemAbelian
          refine ⟨E, hE, ?_⟩
          rw [hcard, degCountTw_three]
          exact Nat.pow_le_pow_right hp.pos (by norm_num : 2 - 1 ≤ 2)
        · obtain ⟨E, hE, hcard⟩ :=
            (sylowTorus_twistedE6_four hℓ hf K hK σ hσ hp he).exists_elemAbelian
          refine ⟨E, hE, ?_⟩
          rw [hcard, degCountTw_four]
          exact Nat.pow_le_pow_right hp.pos (by norm_num : 2 - 1 ≤ 2)
      ·
        have hcnt3 : 3 ≤ degCountTw e := by omega
        rcases eq_of_three_le_degCountTw hcnt3 with rfl | rfl | rfl
        ·
          by_cases hp3eq : p = 3
          · subst p
            obtain ⟨E, hE, hle⟩ := exists_elemAbelian_twistedE6_three_one hℓ hf K hK σ hσ he
            refine ⟨E, hE, ?_⟩
            rw [degCountTw_one]
            have h : 3 * 3 ^ 3 ≤ 3 * Nat.card E := by
              calc 3 * 3 ^ 3 = 3 ^ 4 := by norm_num
                _ ≤ 3 * Nat.card E := hle
            show 3 ^ 3 ≤ Nat.card E
            exact Nat.le_of_mul_le_mul_left h (by norm_num)
          · have hp3 : 3 < p := by
              by_contra hle
              have hp2le := hp.two_le
              have hp3le : p ≤ 3 := by omega
              interval_cases p
              · exact absurd rfl hp2
              · exact absurd rfl hp3eq
            obtain ⟨E, hE, hcard⟩ :=
              exists_elemAbelian_twistedE6_one hℓ hf K hK σ hσ hp hp3 he
            refine ⟨E, hE, ?_⟩
            rw [hcard, degCountTw_one]
            exact Nat.pow_le_pow_right hp.pos (by norm_num : 4 - 1 ≤ 4)
        ·
          by_cases hp3eq : p = 3
          · subst p
            obtain ⟨E, hE, hle⟩ := exists_elemAbelian_twistedE6_three_two hℓ hf K hK σ hσ he
            refine ⟨E, hE, ?_⟩
            rw [degCountTw_two]
            have h : 3 * 3 ^ 5 ≤ 3 * Nat.card E := by
              calc 3 * 3 ^ 5 = 3 ^ 6 := by norm_num
                _ ≤ 3 * Nat.card E := hle
            show 3 ^ 5 ≤ Nat.card E
            exact Nat.le_of_mul_le_mul_left h (by norm_num)
          · have hp3 : 3 < p := by
              by_contra hle
              have hp2le := hp.two_le
              have hp3le : p ≤ 3 := by omega
              interval_cases p
              · exact absurd rfl hp2
              · exact absurd rfl hp3eq
            obtain ⟨E, hE, hcard⟩ :=
              exists_elemAbelian_twistedE6_two hℓ hf K hK σ hσ hp hp3 he
            refine ⟨E, hE, ?_⟩
            rw [hcard, degCountTw_two]
            exact Nat.pow_le_pow_right hp.pos (by norm_num : 6 - 1 ≤ 6)
        ·
          obtain ⟨E, hE, hcard⟩ :=
            exists_elemAbelian_twistedE6_six hℓ hf K hK σ hσ hp he
          refine ⟨E, hE, ?_⟩
          rw [hcard, degCountTw_six]
          exact Nat.pow_le_pow_right hp.pos (by norm_num : 3 - 1 ≤ 3)

end CFSG.StandardType
