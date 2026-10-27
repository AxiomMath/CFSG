module

public import CFSG.LocalAnalysis.StandardType.GGTriD4InnerCompDefs
import CFSG.LocalAnalysis.GLTheoremA.S12.CanonTriCentHolds
import CFSG.LocalAnalysis.GLTheoremA.S12.CanonL2Holds
import CFSG.LocalAnalysis.StandardType.GGTableBTypeATransport
import CFSG.LocalAnalysis.StandardType.GGTableBExcSmallRestTri
import CFSG.LocalAnalysis.StandardType.GGLemmaThreeThirteenFourteen
import CFSG.RankThree.PartTwo.Sec11.KS11Lie6ProofACent
import CFSG.RankThree.PartTwo.Sec11.KS11Lie6ProofBCent
import CFSG.RankThree.PartTwo.Sec11.KS11Lie6ProofShort
import CFSG.RankThree.PartTwo.Sec21.Item219LieProofD4A

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

private theorem ggTriD4InnerCompAux_quot_equiv {X Y : Type} [Group X] [Group Y] (e : X ≃* Y)
    (N : Subgroup Y) [N.Normal] (hZ : Subgroup.center Y = N) :
    Nonempty (X ⧸ Subgroup.center X ≃* Y ⧸ N) :=
  ⟨QuotientGroup.congr (Subgroup.center X) N e
    ((CFSG.LocalAnalysis.GLTheoremA.tcent_map_center e).trans hZ)⟩

private theorem ggTriD4InnerCompAux_threeA_solvable
    {ℓ f : ℕ} [Fact ℓ.Prime] (hf : 1 ≤ f) (hℓ3 : ℓ ≠ 3) (hq2 : ℓ ^ f = 2)
    {K : Type} [Field K] [Finite K] (hK : Nat.card K = (ℓ ^ f) ^ 3) {σ : K ≃+* K}
    (hσ : ∀ c, σ c = c ^ (ℓ ^ f))
    {z : CFSG.LieType.Chevalley.graphFixedRootGroup CFSG.Blueprint.Chevalley.TwistTag.D4 K
      σ.toRingHom}
    (hzS : z ∈ CFSG.RankThree.PartTwo.Sec11.KS11Lie4Proof.d4ShortSL2 K σ.toRingHom)
    (hz3 : z ^ 3 = 1) (hz1 : z ≠ 1) :
    Group.IsSolvable (Subgroup.centralizer ({z} : Set _)) := by
  classical
  have hℓp : ℓ.Prime := Fact.out
  have hσ3 : σ ^ 3 = 1 := by
    refine RingEquiv.ext fun c => ?_
    have := CFSG.LieType.Chevalley.ringEquiv_cube_apply_eq hK hσ c
    simpa [pow_succ] using this
  haveI : CharP K ℓ :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic hℓp
      (k := f * 3) (by omega) (by rw [hK, pow_mul])
  set L := AlgebraicClosure K with hL
  haveI : CharP L ℓ := charP_of_injective_algebraMap (algebraMap K L).injective ℓ
  have h3L : (3 : L) ≠ 0 := by
    intro h
    have h' : ((3 : ℕ) : L) = 0 := by exact_mod_cast h
    rw [CharP.cast_eq_zero_iff L ℓ] at h'
    exact hℓ3 ((Nat.prime_dvd_prime_iff_eq hℓp Nat.prime_three).1 h')
  obtain ⟨ζ, hζ⟩ :=
    CFSG.RankThree.PartTwo.Sec11.KS11Lie6Proof.exists_units_orderOf_three L h3L
  have hζ3 : ζ ^ 3 = 1 :=
    CFSG.RankThree.PartTwo.Sec11.KS11Lie5Proof.pow_three_of_orderOf hζ
  set Fr : L →+* L := iterateFrobenius L ℓ f with hFrdef
  have hFr : ∀ c, Fr c = c ^ (ℓ ^ f) := fun c => iterateFrobenius_def ℓ f c
  have hε : ((-1 : ℤ) = 1 ∨ (-1 : ℤ) = -1) := Or.inr rfl
  have hqε : (((ℓ ^ f : ℕ)) : ZMod 3) = (-1 : ℤ) := by
    rw [hq2]; decide
  obtain ⟨g, hgG, hFg⟩ :=
    CFSG.RankThree.PartOne.KGD.lang_conjugator_D4 (K := K) (ℓ := ℓ) hf L
      (CFSG.RankThree.Chevalley.threeSixN L (-1))
      (CFSG.RankThree.Chevalley.threeSixN_mem_adjointGroup (Or.inr rfl))
  have hFg' : CFSG.RankThree.Chevalley.trialityFrob L Fr g =
      g * CFSG.RankThree.Chevalley.threeSixN L (-1) := hFg
  have ha := CFSG.RankThree.PartTwo.Sec11.KS11Lie6Proof.mem_threeSixTorus_tup_gT
    (L := L) hFr hε hqε hζ3
  obtain ⟨x, hx⟩ := CFSG.RankThree.Chevalley.exists_threeSixEmb_eq_conj hℓp hf hK hσ hFr hgG
    hFg' ha
  have hord := CFSG.RankThree.PartTwo.Sec11.KS11Lie6Proof.orderOf_rootDiagUnit_tup_gT hζ
  have hv := CFSG.RankThree.PartTwo.Sec11.KS11Lie6Proof.survivingRoots_tup_gT hζ
  have hsol : Group.IsSolvable
      (Subgroup.centralizer ({x} :
        Set (CFSG.LieType.Chevalley.graphFixedRootGroup CFSG.Blueprint.Chevalley.TwistTag.D4 K
          σ.toRingHom))) :=
    CFSG.RankThree.PartTwo.Sec11.KS11Lie6Proof.threeSix_solvable_two hℓp hℓ3 hf hq2 K hK σ hσ L
      Fr hFr g hgG hFg'
      (CFSG.RankThree.PartTwo.Sec11.KS11Lie5Proof.tup ζ
        CFSG.RankThree.PartTwo.Sec11.KS11Lie6Proof.gT) ha hord
      CFSG.RankThree.PartTwo.Sec11.KS11Lie6Proof.vT hv x hx
  have hd : CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley.rootDiagUnit
        CFSG.Blueprint.Chevalley.TwistTag.D4.tag
        (CFSG.RankThree.PartTwo.Sec11.KS11Lie5Proof.tup ζ
          CFSG.RankThree.PartTwo.Sec11.KS11Lie6Proof.gT) =
      (CFSG.LieType.Chevalley.canonicalRep
        (CFSG.LieType.Chevalley.coxeterSystem CFSG.Blueprint.Chevalley.TwistTag.D4.tag) L
        ((CFSG.LieType.Chevalley.coxeterSystem CFSG.Blueprint.Chevalley.TwistTag.D4.tag).wordProd
          [3, 2, 1, 0, 2, 3]))⁻¹ *
      CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley.rootDiagUnit
        CFSG.Blueprint.Chevalley.TwistTag.D4.tag
        (CFSG.RankThree.PartTwo.Sec11.KS11Lie5Proof.tup ζ
          CFSG.RankThree.PartTwo.Sec11.KS11Lie5Proof.gA) *
      CFSG.LieType.Chevalley.canonicalRep
        (CFSG.LieType.Chevalley.coxeterSystem CFSG.Blueprint.Chevalley.TwistTag.D4.tag) L
        ((CFSG.LieType.Chevalley.coxeterSystem CFSG.Blueprint.Chevalley.TwistTag.D4.tag).wordProd
          [3, 2, 1, 0, 2, 3]) := by
    rw [CFSG.RankThree.PartTwo.Sec11.KS11Lie5Proof.rootDiagUnit_tup_eq_conj hζ3
        [3, 2, 1, 0, 2, 3] CFSG.RankThree.PartTwo.Sec11.KS11Lie6Proof.gT,
      show CFSG.RankThree.PartTwo.Sec11.KS11Lie5Proof.wordExp [3, 2, 1, 0, 2, 3]
          CFSG.RankThree.PartTwo.Sec11.KS11Lie6Proof.gT =
          CFSG.RankThree.PartTwo.Sec11.KS11Lie5Proof.gA by decide]
  set k := g * (CFSG.LieType.Chevalley.canonicalRep
      (CFSG.LieType.Chevalley.coxeterSystem CFSG.Blueprint.Chevalley.TwistTag.D4.tag) L
      ((CFSG.LieType.Chevalley.coxeterSystem CFSG.Blueprint.Chevalley.TwistTag.D4.tag).wordProd
        [3, 2, 1, 0, 2, 3]))⁻¹ with hkdef
  have hk : k ∈ CFSG.Blueprint.Chevalley.adjointGroup
      CFSG.Blueprint.Chevalley.TwistTag.D4.tag L :=
    mul_mem hgG (inv_mem (CFSG.LieType.Chevalley.canonicalRep_mem_adjointGroup _ L _))
  have hxk : CFSG.RankThree.PartOne.KGD.triEmb K σ L x =
      k * CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley.rootDiagUnit
        CFSG.Blueprint.Chevalley.TwistTag.D4.tag
        (CFSG.RankThree.PartTwo.Sec11.KS11Lie5Proof.tup ζ
          CFSG.RankThree.PartTwo.Sec11.KS11Lie5Proof.gA) * k⁻¹ := by
    change CFSG.RankThree.Chevalley.threeSixEmb K L σ x = _
    rw [hx, hd, hkdef]
    group
  obtain ⟨k', hk', hzk⟩ :=
    CFSG.RankThree.PartTwo.Sec11.KS11Lie6Proof.exists_conj_dA_of_mem_short hσ3 hζ hzS hz3 hz1
  obtain ⟨c, hc⟩ :=
    CFSG.RankThree.PartTwo.Sec11.KS11Lie6Proof.exists_conj_of_triEmb_conj hf hK hσ
      (CFSG.RankThree.PartTwo.Sec11.KS11Lie5Proof.isPointIrreducible_gA hζ) hk' hk hzk hxk
  have hmap : (Subgroup.centralizer ({z} : Set (CFSG.LieType.Chevalley.graphFixedRootGroup
        CFSG.Blueprint.Chevalley.TwistTag.D4 K σ.toRingHom))).map
      (MulAut.conj c).toMonoidHom =
      Subgroup.centralizer ({x} : Set (CFSG.LieType.Chevalley.graphFixedRootGroup
        CFSG.Blueprint.Chevalley.TwistTag.D4 K σ.toRingHom)) := by
    rw [CFSG.LocalAnalysis.GLTheoremA.tcent_map_centralizer, show MulAut.conj c z = x from by
      rw [MulAut.conj_apply]; exact hc]
  let e : ↥(Subgroup.centralizer ({z} : Set (CFSG.LieType.Chevalley.graphFixedRootGroup
        CFSG.Blueprint.Chevalley.TwistTag.D4 K σ.toRingHom))) ≃*
      ↥(Subgroup.centralizer ({x} : Set (CFSG.LieType.Chevalley.graphFixedRootGroup
        CFSG.Blueprint.Chevalley.TwistTag.D4 K σ.toRingHom))) :=
    ((Subgroup.centralizer ({z} : Set _)).equivMapOfInjective _ (MulAut.conj c).injective).trans
      (MulEquiv.subgroupCongr hmap)
  haveI : Group.IsSolvable ↥(Subgroup.centralizer ({x} :
      Set (CFSG.LieType.Chevalley.graphFixedRootGroup CFSG.Blueprint.Chevalley.TwistTag.D4 K
        σ.toRingHom))) := hsol
  exact Group.isSolvable_of_isSolvable_injective (f := e.toMonoidHom) e.injective

private theorem ggTriD4InnerCompAux_model
    {n : ℕ} (hn1 : 1 ≤ n) (hn3 : n = 1 ∨ 3 ∣ 2 ^ n - 1) {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = (2 ^ n) ^ 3) {Fr : K ≃+* K} (hFr : ∀ c, Fr c = c ^ 2 ^ n)
    {X : Type} [Group X]
    (ψ : X ≃* CFSG.LieType.Chevalley.graphFixedRootGroup
      CFSG.Blueprint.Chevalley.TwistTag.D4 K Fr.toRingHom)
    {r : X} (hr3 : r ^ 3 = 1) (hr1 : r ≠ 1) {Q : Subgroup X}
    (hQ : IsComponentOf Q (Subgroup.centralizer ({r} : Set X))) :
    (∃ (E : Type) (_ : Field E) (_ : Finite E), Nat.card E = (2 ^ n) ^ 3 ∧
      Nonempty (↥Q ⧸ Subgroup.center ↥Q ≃* LargeEvenProj (LargeEvenSLGroup (Fin 2) E))) ∨
    (2 ≤ n ∧ ∃ (E : Type) (_ : Field E) (_ : Finite E), Nat.card E = 2 ^ n ∧
      Nonempty (↥Q ⧸ Subgroup.center ↥Q ≃* LargeEvenProj (LargeEvenSLGroup (Fin 3) E))) := by
  classical
  have h3q : ¬ 3 ∣ 2 ^ n := fun h => by
    have h32 : 3 ∣ 2 := Nat.prime_three.dvd_of_dvd_pow h
    norm_num at h32
  set z := ψ r with hzdef
  have hz3 : z ^ 3 = 1 := by rw [hzdef, ← map_pow, hr3, map_one]
  have hz1 : z ≠ 1 := fun h => hr1 (ψ.injective (h.trans (map_one ψ).symm))
  obtain ⟨g, hg | hg⟩ :=
    CFSG.RankThree.PartTwo.Sec11.KS11Lie6Proof.d4ThreeConj_holds K (2 ^ n) Fr hK hFr h3q z hz3
      hz1
  ·
    have hy3 : (g * z * g⁻¹) ^ 3 = 1 := by rw [conj_pow, hz3, mul_one, mul_inv_cancel]
    have hy1 : g * z * g⁻¹ ≠ 1 := by
      intro h1
      apply hz1
      calc z = g⁻¹ * (g * z * g⁻¹) * g := by group
        _ = 1 := by rw [h1]; group
    rcases hn3 with hn_eq | hdvd
    ·
      subst hn_eq
      exfalso
      haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
      have hsol : Group.IsSolvable (Subgroup.centralizer ({g * z * g⁻¹} :
          Set (CFSG.LieType.Chevalley.graphFixedRootGroup
            CFSG.Blueprint.Chevalley.TwistTag.D4 K Fr.toRingHom))) :=
        ggTriD4InnerCompAux_threeA_solvable (ℓ := 2) (f := 1) (by norm_num)
          (by norm_num : (2 : ℕ) ≠ 3) (by norm_num : 2 ^ 1 = 2) hK hFr hg hy3 hy1
      set ψ' : X ≃* CFSG.LieType.Chevalley.graphFixedRootGroup
          CFSG.Blueprint.Chevalley.TwistTag.D4 K Fr.toRingHom :=
        ψ.trans (MulAut.conj g) with hψ'def
      have hψ' : ψ' r = g * z * g⁻¹ := by
        rw [hψ'def, MulEquiv.trans_apply, MulAut.conj_apply, ← hzdef]
      have hQm := CFSG.LocalAnalysis.GLTheoremA.tcent_isComponentOf_map ψ' hQ
      rw [CFSG.LocalAnalysis.GLTheoremA.tcent_map_centralizer, hψ'] at hQm
      exact absurd hQm.1 (ggComponent_not_le_of_isSolvable hQm hsol)
    ·
      right
      have hq1 : 2 ^ n % 3 = 1 := by
        have h1 : (1 : ℕ) ≤ 2 ^ n := Nat.one_le_two_pow
        have hmod := (Nat.modEq_iff_dvd' h1).2 hdvd
        rw [Nat.ModEq, Nat.mod_eq_of_lt (by norm_num : 1 < 3)] at hmod
        exact hmod.symm
      have hn2 : 2 ≤ n := by
        rcases Nat.lt_or_ge n 2 with h | h
        · interval_cases n
          norm_num at hq1
        · exact h
      refine ⟨hn2, ?_⟩
      obtain ⟨c, R, hRc, hRcent, hcomm, hRq, F, hFld, hFfin, hF, ⟨eRU⟩⟩ :=
        CFSG.RankThree.PartTwo.Sec21.Item219LieProof.d4_threeA_model Nat.prime_two hn1
          (by norm_num : (2 : ℕ) ≠ 3) hq1 hK hFr hg hy3 hy1
      letI : Field F := hFld
      letI : Finite F := hFfin
      set ψ' : X ≃* CFSG.LieType.Chevalley.graphFixedRootGroup
          CFSG.Blueprint.Chevalley.TwistTag.D4 K Fr.toRingHom :=
        ψ.trans (MulAut.conj (c * g)) with hψ'def
      have hψ' : ψ' r = c * (g * z * g⁻¹) * c⁻¹ := by
        rw [hψ'def, MulEquiv.trans_apply, MulAut.conj_apply, ← hzdef]
        group
      have hQm := CFSG.LocalAnalysis.GLTheoremA.tcent_isComponentOf_map ψ' hQ
      rw [CFSG.LocalAnalysis.GLTheoremA.tcent_map_centralizer, hψ'] at hQm
      have hQR := CFSG.LocalAnalysis.GLTheoremA.tcent_component_eq hQm hRcent hcomm hRq
      let eQ : ↥Q ≃* Matrix.SpecialLinearGroup (Fin 3) F :=
        (Q.equivMapOfInjective ψ'.toMonoidHom ψ'.injective).trans
          ((MulEquiv.subgroupCongr hQR).trans eRU)
      let eQ2 : ↥Q ≃* ↥(LargeEvenSLGroup (Fin 3) F) :=
        eQ.trans (TypeA.slKerEquiv 3 F).symm
      have hcenter : Subgroup.center ↥(LargeEvenSLGroup (Fin 3) F) =
          (LargeEvenScalars (Fin 3) F).subgroupOf (LargeEvenSLGroup (Fin 3) F) := by
        have hmap : (Subgroup.center ↥(LargeEvenSLGroup (Fin 3) F)).map
            (TypeA.slKerEquiv 3 F).toMonoidHom =
            Subgroup.center (Matrix.SpecialLinearGroup (Fin 3) F) :=
          CFSG.LocalAnalysis.GLTheoremA.tcent_map_center (TypeA.slKerEquiv 3 F)
        have hmaps : ((LargeEvenScalars (Fin 3) F).subgroupOf
              (LargeEvenSLGroup (Fin 3) F)).map (TypeA.slKerEquiv 3 F).toMonoidHom =
            CFSG.LocalAnalysis.ComponentInitial.LinearFlag.scalars 3 F := by
          simpa using TypeA.map_scalars_slKerEquiv (d := 3) (K := F)
        exact Subgroup.map_injective (f := (TypeA.slKerEquiv 3 F).toMonoidHom)
          (TypeA.slKerEquiv 3 F).injective (by
            rw [hmap, hmaps,
              CFSG.LocalAnalysis.ComponentInitial.LinearFlag.scalars_eq_center])
      exact ⟨F, hFld, hFfin, hF, ggTriD4InnerCompAux_quot_equiv eQ2 _ hcenter⟩
  ·
    left
    have hy3 : (g * z * g⁻¹) ^ 3 = 1 := by rw [conj_pow, hz3, mul_one, mul_inv_cancel]
    have hy1 : g * z * g⁻¹ ≠ 1 := by
      intro h1
      apply hz1
      calc z = g⁻¹ * (g * z * g⁻¹) * g := by group
        _ = 1 := by rw [h1]; group
    obtain ⟨hcomm, -⟩ :=
      CFSG.RankThree.PartTwo.Sec11.KS11Lie6Proof.d4ThreeBCent_holds K (2 ^ n) Fr hK hFr h3q
        (g * z * g⁻¹) hg hy3 hy1
    have hSC : (CFSG.RankThree.PartTwo.Sec11.KS11Lie4Proof.d4ShortSL2 K Fr.toRingHom :
        Subgroup (CFSG.LieType.Chevalley.graphFixedRootGroup
          CFSG.Blueprint.Chevalley.TwistTag.D4 K Fr.toRingHom)) ≤
          Subgroup.centralizer ({g * z * g⁻¹} : Set _) := by
      intro s hs
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact Subgroup.mem_centralizer_iff.mp hg s hs
    set ψ' : X ≃* CFSG.LieType.Chevalley.graphFixedRootGroup
        CFSG.Blueprint.Chevalley.TwistTag.D4 K Fr.toRingHom :=
      ψ.trans (MulAut.conj g) with hψ'def
    have hψ' : ψ' r = g * z * g⁻¹ := by
      rw [hψ'def, MulEquiv.trans_apply, MulAut.conj_apply, ← hzdef]
    have hQm := CFSG.LocalAnalysis.GLTheoremA.tcent_isComponentOf_map ψ' hQ
    rw [CFSG.LocalAnalysis.GLTheoremA.tcent_map_centralizer, hψ'] at hQm
    have hσ3 : Fr ^ 3 = 1 := by
      refine RingEquiv.ext fun c => ?_
      have := CFSG.LieType.Chevalley.ringEquiv_cube_apply_eq hK hFr c
      simpa [pow_succ] using this
    have hK4 : 4 ≤ Nat.card K := by
      rw [hK]
      have h2n : 2 ≤ 2 ^ n := by
        have := Nat.pow_le_pow_right (show (0 : ℕ) < 2 by norm_num) hn1
        simpa using this
      calc 4 ≤ 2 ^ 3 := by norm_num
        _ ≤ (2 ^ n) ^ 3 := Nat.pow_le_pow_left h2n 3
    have hSq := CFSG.RankThree.PartTwo.Sec11.KS11Lie4Proof.isQuasisimple_d4ShortSL2 hσ3 hK4
    have hQS := CFSG.LocalAnalysis.GLTheoremA.tcent_component_eq hQm hSC hcomm hSq
    obtain ⟨eS⟩ := CFSG.RankThree.PartTwo.Sec11.KS11Lie4Proof.nonempty_mulEquiv_d4ShortSL2 hσ3
    set F : Subfield K := CFSG.LieType.Chevalley.orbitField
      CFSG.Blueprint.Chevalley.TwistTag.D4 K Fr.toRingHom
      CFSG.RankThree.PartTwo.Sec11.KS11Lie4Proof.d4Outer with hFdef
    haveI : Finite ↥F := Subtype.finite
    have hFcard : Nat.card ↥F = 2 ^ (3 * n) := by
      rw [hFdef, CFSG.RankThree.PartTwo.Sec11.KS11Lie4Proof.natCard_orbitField_d4Outer hσ3,
        hK, ← pow_mul, mul_comm]
    haveI : CharP ↥F 2 :=
      CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic Nat.prime_two
        (k := 3 * n) (by omega) hFcard
    let isoQ : ↥Q ≃* LargeEvenProj (LargeEvenSLGroup (Fin 2) ↥F) :=
      (Q.equivMapOfInjective ψ'.toMonoidHom ψ'.injective).trans
        ((MulEquiv.subgroupCongr hQS).trans
          (eS.symm.trans (CFSG.LocalAnalysis.GLTheoremA.projEquiv ↥F).symm))
    have hcentR : Subgroup.center (LargeEvenProj (LargeEvenSLGroup (Fin 2) ↥F)) = ⊥ :=
      CFSG.LocalAnalysis.GLTheoremA.tcent_center_bot_of_equiv
        (CFSG.LocalAnalysis.GLTheoremA.projEquiv ↥F)
        (CFSG.HardMathSupport.Timmesfeld.ComponentBalance.SL2Char2.center_eq_bot ↥F)
    have hZQ : Subgroup.center ↥Q = ⊥ :=
      CFSG.LocalAnalysis.GLTheoremA.tcent_center_bot_of_equiv isoQ hcentR
    refine ⟨↥F, inferInstance, inferInstance, ?_, ?_⟩
    · rw [hFcard, show 3 * n = n * 3 by omega, pow_mul]
    · exact ⟨(QuotientGroup.quotientMulEquivOfEq hZQ).trans
        (QuotientGroup.quotientBot.trans isoQ)⟩

theorem ggTriD4InnerCompInput_holds :
    GGTriD4InnerCompInput := by
  intro n hn1 hn3 K _ _ hK h hh1 hh3 Q hQ
  haveI : CharP K 2 :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic Nat.prime_two
      (k := n * 3) (by omega) (by rw [hK, pow_mul])
  set σ₀ := iterateFrobeniusEquiv K 2 n with hσ₀def
  have hσ₀ : ∀ c, σ₀ c = c ^ 2 ^ n := fun c => by
    rw [hσ₀def, iterateFrobeniusEquiv_apply, iterateFrobenius_def]
  obtain ⟨e₀⟩ := TableBExcSmallRest.nonempty_triD4_equiv hn1 K hK σ₀ hσ₀
  exact ggTriD4InnerCompAux_model hn1 hn3 hK hσ₀ e₀ hh3 hh1 hQ

end CFSG.StandardType
