module

public import CFSG.RankThree.PartTwo.Sec4.Ronan148LH1Rows
public import CFSG.RankThree.PartTwo.Sec4.Ronan148LT1Gen
public import CFSG.RankThree.PartTwo.Sec8.Item8KFacts2ProofReeConj
public import CFSG.SignalizerFunctorTheorem.CatalogBridge.NonLocalLargeReeMain

public section

namespace CFSG.RankThree.PartTwo.Sec4.Ronan148L

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec14.Ronan148K
open CFSG.RankThree.PartTwo.Sec4.Ronan148S
open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Ree
open CFSG.HardMathSupport.Solomon.Coordinator CFSG.HardMathSupport.Solomon.Coordinator.LieComp
open TauCeti (PrimePower LieTypeIndex ValidLieTypeIndex)


section Gen

variable {G : Type} [Group G] [Finite G]

theorem eq_of_le_quasisimple {J N C : Subgroup G} (hJN : J ≤ N) (hNC : N ≤ C)
    (hsub : (J.subgroupOf C).IsSubnormal) (hN : CFSG.IsQuasisimple ↥N)
    (hJ : CFSG.IsQuasisimple ↥J) : J = N := by
  have hsN : (J.subgroupOf N).IsSubnormal := by
    have h := hsub.comap (Subgroup.inclusion hNC)
    have heq : (J.subgroupOf C).comap (Subgroup.inclusion hNC) = J.subgroupOf N := by
      ext x
      simp [Subgroup.mem_subgroupOf]
    rwa [heq] at h
  rcases CFSG.LocalAnalysis.ComponentInitial.quasisimple_subnormal_subgroups hN hsN with h | h
  · refine le_antisymm hJN fun x hx => ?_
    have : (⟨x, hx⟩ : ↥N) ∈ J.subgroupOf N := h ▸ Subgroup.mem_top _
    exact this
  · exfalso
    have hJo : CFSG.Open.IsQuasisimple ↥J :=
      (CFSG.ComponentClassification.AssemblyBPredicates.isQuasisimple_iff_open _).1
        ((CFSG.ComponentClassification.AssemblyBPredicates.isQuasisimple_iff_native _).2 hJ)
    obtain ⟨a, b, hab⟩ := exists_ne_comm_of_isQuasisimple hJo
    apply hab
    have hb : (⟨b, hJN b.2⟩ : ↥N) ∈ Subgroup.center ↥N := h b.2
    apply Subtype.ext
    exact congrArg (fun x : ↥N => (x : G)) ((Subgroup.mem_center_iff.1 hb) ⟨a, hJN a.2⟩)

theorem card_le_of_A5 {J : Type*} [Group J] [Finite J]
    (hZ : Nat.card (Subgroup.center J) ∣ 3)
    (e : J ⧸ Subgroup.center J ≃* alternatingGroup (Fin 5)) : Nat.card J ≤ 180 := by
  have h60 : Nat.card (J ⧸ Subgroup.center J) = 60 := by
    rw [Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card, card_alternatingGroup,
      Fintype.card_fin]
    decide
  have hcard := Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.center J)
  rw [h60] at hcard
  have hZ3 : Nat.card (Subgroup.center J) ≤ 3 := Nat.le_of_dvd (by norm_num) hZ
  omega

theorem isEmpty_A5_of_le {J N C : Subgroup G} (hJN : J ≤ N) (hNC : N ≤ C)
    (hsub : (J.subgroupOf C).IsSubnormal) (hN : CFSG.IsQuasisimple ↥N)
    (hZN : Nat.card (Subgroup.center ↥N) ∣ 3) (hcN : 180 < Nat.card N)
    (hJ : CFSG.IsQuasisimple ↥J) : IsEmpty (↥J ⧸ Subgroup.center ↥J ≃* alternatingGroup (Fin 5)) := by
  have hJeq := eq_of_le_quasisimple hJN hNC hsub hN hJ
  subst hJeq
  exact ⟨fun e => absurd (card_le_of_A5 hZN e) (by omega)⟩

theorem card_center_of_mulEquiv {X T : Type*} [Group X] [Group T] (e : X ≃* T) :
    Nat.card (Subgroup.center X) = Nat.card (Subgroup.center T) := by
  rw [← Subgroup.map_center_eq e, Subgroup.card_map_of_injective e.injective]

theorem card_center_of_simple {T : Type*} [Group T] (hT : IsSimpleGroup T)
    (hna : ∃ a b : T, a * b ≠ b * a) : Nat.card (Subgroup.center T) = 1 := by
  rw [b3Lie_center_eq_bot hna, Subgroup.card_bot]

theorem noA5_of_mulEquiv {T M : Type} [Group T] [Group M] (e : T ≃* M)
    (h : ∀ τ : MulAut M, τ ^ 3 = 1 → ∀ C J : Subgroup M, (∀ z, z ∈ C ↔ τ z = z) → J ≤ C →
      (J.subgroupOf C).IsSubnormal → CFSG.IsQuasisimple ↥J →
        IsEmpty (↥J ⧸ Subgroup.center ↥J ≃* alternatingGroup (Fin 5))) :
    ∀ τ : MulAut T, τ ^ 3 = 1 → ∀ C J : Subgroup T, (∀ z, z ∈ C ↔ τ z = z) → J ≤ C →
      (J.subgroupOf C).IsSubnormal → CFSG.IsQuasisimple ↥J →
        IsEmpty (↥J ⧸ Subgroup.center ↥J ≃* alternatingGroup (Fin 5)) := by
  intro τ hτ C J hC hJC hsn hJ
  set f : T →* M := e.toMonoidHom with hf
  have hfz : ∀ z, z ∈ C.map f ↔ MulAut.congr e τ z = z := by
    intro z
    rw [MulAut.congr_apply]
    constructor
    · rintro ⟨c, hc, rfl⟩
      simp [(hC c).mp hc, hf]
    · intro hz
      refine ⟨e.symm z, (hC _).mpr ?_, by simp [hf]⟩
      apply e.injective
      simpa using hz
  have hsn' : ((J.map f).subgroupOf (C.map f)).IsSubnormal := by
    rw [← Sec6.BThreeCensus.map_subgroupOf_subgroupMap]
    exact hsn.map (e.subgroupMap C).surjective
  let eJ : ↥J ≃* ↥(J.map f) := J.equivMapOfInjective f e.injective
  have hJ' : CFSG.IsQuasisimple ↥(J.map f) := CFSG.LocalCores.isQuasisimple_of_mulEquiv eJ hJ
  have key := h (MulAut.congr e τ) (by rw [← map_pow, hτ, map_one]) (C.map f) (J.map f) hfz
    (Subgroup.map_mono hJC) hsn' hJ'
  exact ⟨fun a => key.false ((QuotientGroup.congr _ _ eJ (Subgroup.map_center_eq eJ)).symm.trans a)⟩

end Gen

theorem rowOf427_of_not_three_dvd
    {X : Type} [Group X] (h3 : ¬ 3 ∣ Nat.card X) :
    RowOf427 X := by
  intro S _ _ hs hna ⟨eS⟩
  refine row427_of_noA5ON fun T _ _ ⟨eT⟩ τ _ => ?_
  intro J _ _ _ hX
  apply h3
  rw [← Nat.card_congr ((eT.trans eS).toEquiv)]
  refine Dvd.dvd.trans ?_ (Subgroup.card_subgroup_dvd_card J)
  refine Dvd.dvd.trans ?_ (Subgroup.card_quotient_dvd_card (Subgroup.center ↥J))
  rcases hX with h5 | hO
  · obtain ⟨e⟩ := h5
    rw [Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card, card_alternatingGroup,
      Fintype.card_fin]
    decide
  · obtain ⟨e⟩ := hO
    rw [Nat.card_congr e.toEquiv, CFSG.Sporadic.ON.card_ON_eq]
    norm_num

theorem kH1_seven_Sz :
    ∀ (m : ℕ) (hm : (LieTypeIndex.suzuki m).Valid),
      RowOf427 (TauCeti.CFSGIndex.lie ⟨.suzuki m, hm⟩).Group := by
  intro m hm
  refine rowOf427_of_not_three_dvd ?_
  obtain ⟨-, a, -, F, _, _, hf, hK', ⟨θ⟩⟩ := Census.suzukiModel_of_index m hm
  have hK : Nat.card F = 2 ^ (2 * a + 1) := by rw [hK', hf]
  rw [Nat.card_congr θ.toEquiv]
  exact KFacts.not_three_dvd_card_suzukiGroup hK

section Ree


theorem lt_ordTwistedF4 (b : ℕ) : 180 < CFSG.Open.ordTwistedF4 (2 ^ (2 * b + 1)) := by
  unfold CFSG.Open.ordTwistedF4
  set x := 2 ^ (2 * b + 1) with hx
  have h2 : 2 ≤ x := by
    rw [hx]
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ (2 * b + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have h12 : 2 ^ 12 ≤ x ^ 12 := Nat.pow_le_pow_left h2 12
  have h6 : 1 ≤ x ^ 6 + 1 := by omega
  have h4 : 1 ≤ x ^ 4 - 1 := by
    have : 2 ^ 4 ≤ x ^ 4 := Nat.pow_le_pow_left h2 4
    omega
  have h3 : 1 ≤ x ^ 3 + 1 := by omega
  have h1 : 1 ≤ x - 1 := by omega
  have hprod : 1 ≤ (x ^ 6 + 1) * (x ^ 4 - 1) * (x ^ 3 + 1) * (x - 1) :=
    Nat.one_le_iff_ne_zero.mpr (by positivity)
  calc 180 < 2 ^ 12 := by norm_num
    _ ≤ x ^ 12 := h12
    _ = x ^ 12 * 1 := (mul_one _).symm
    _ ≤ x ^ 12 * ((x ^ 6 + 1) * (x ^ 4 - 1) * (x ^ 3 + 1) * (x - 1)) :=
      Nat.mul_le_mul_left _ hprod
    _ = x ^ 12 * (x ^ 6 + 1) * (x ^ 4 - 1) * (x ^ 3 + 1) * (x - 1) := by ring

theorem lt_card_statedSU_three {F : Type} [Field F] [Finite F] {f : ℕ} (hf : 3 ≤ f)
    (hF : Nat.card F = 2 ^ (2 * f)) :
    180 < Nat.card (CFSG.Open.StatedSU 3 (2 ^ f) F) := by
  have h : CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData 2 f F :=
    ⟨Nat.prime_two, by omega, hF⟩
  have hc := CFSG.GH74.GLS.Stage2.Final.ModelOrd.card_statedSU_int h (n := 3) (by norm_num)
  have hIcc : Finset.Icc 2 3 = {2, 3} := by decide
  rw [hIcc, Finset.prod_pair (by norm_num)] at hc
  have h8 : (8 : ℤ) ≤ ((2 ^ f : ℕ) : ℤ) := by
    have : 2 ^ 3 ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
    exact_mod_cast this
  have hpos : (180 : ℤ) < (Nat.card (CFSG.Open.StatedSU 3 (2 ^ f) F) : ℤ) := by
    rw [hc]
    set x : ℤ := ((2 ^ f : ℕ) : ℤ) with hx
    have h1 : (3 * (3 - 1) / 2 : ℕ) = 3 := by norm_num
    rw [h1]
    norm_num
    have h2 : (1 : ℤ) ≤ x ^ 2 - 1 := by nlinarith
    have h3 : (1 : ℤ) ≤ x ^ 3 + 1 := by nlinarith
    have hx3 : (512 : ℤ) ≤ x ^ 3 := by nlinarith
    have h23 : (1 : ℤ) ≤ (x ^ 2 - 1) * (x ^ 3 + 1) := by nlinarith
    nlinarith
  exact_mod_cast hpos

theorem reeF4_noA5 {a : ℕ} (ha : 1 ≤ a) {K : Type} [Field K] [Finite K]
    [CharP K ReeTag.F4.prime] (hK : Nat.card K = 2 ^ (2 * a + 1)) :
    ∀ τ : MulAut (ReeTag.F4.reeGamma K a), τ ^ 3 = 1 →
      ∀ C J : Subgroup (ReeTag.F4.reeGamma K a), (∀ z, z ∈ C ↔ τ z = z) → J ≤ C →
        (J.subgroupOf C).IsSubnormal → CFSG.IsQuasisimple ↥J →
          IsEmpty (↥J ⧸ Subgroup.center ↥J ≃* alternatingGroup (Fin 5)) := by
  classical
  intro τ hτ C J hC hJC hsub hJ
  haveI : Finite (ModGL ReeTag.F4.tag K) := finite_modGL
  haveI : Finite (ReeTag.F4.reeGamma K a) := Subtype.finite
  have hZ : Subgroup.center (ReeTag.F4.reeGamma K a) = ⊥ :=
    ReeTag.large_Ree_fixed_group_center_trivial a K hK
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hsimple : ∀ {T : Type} [Group T] [Finite T], IsSimpleGroup T →
      (∃ x y : T, x * y ≠ y * x) → 180 < Nat.card T → ∀ eC : ↥C ≃* T,
      IsEmpty (↥J ⧸ Subgroup.center ↥J ≃* alternatingGroup (Fin 5)) := by
    intro T _ _ hT hnc hcT eC
    have hCq : CFSG.IsQuasisimple ↥C := CFSG.LocalCores.isQuasisimple_of_mulEquiv eC.symm
      (CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.isQuasisimple_of_isSimpleGroup hT hnc)
    refine isEmpty_A5_of_le hJC le_rfl hsub hCq ?_ ?_ hJ
    · rw [card_center_of_mulEquiv eC, card_center_of_simple hT hnc]
      norm_num
    · rw [Nat.card_congr eC.toEquiv]
      exact hcT
  have hnc0 : ∀ {b : ℕ} {k : Type} [Field k] [Finite k] [CharP k ReeTag.F4.prime],
      1 ≤ b → Nat.card k = 2 ^ (2 * b + 1) →
      ∃ x y : ↥(ReeTag.F4.reeGamma k b), x * y ≠ y * x := by
    intro b k _ _ _ hb hk
    haveI : Finite ↥(ReeTag.F4.reeGamma k b) := Subtype.finite
    haveI : IsSimpleGroup ↥(ReeTag.F4.reeGamma k b) :=
      CFSG.SignalizerFunctorTheorem.CatalogBridge.isSimpleGroup_reeGamma_F4 hb hk
    by_contra hcon
    push Not at hcon
    have hperf : commutator (ReeTag.F4.reeGamma k b) = ⊤ :=
      ReeTag.commutator_reeGamma_eq_top (t := ReeTag.F4) hb hk
    have hc : commutator ↥(ReeTag.F4.reeGamma k b) = ⊥ := by
      rw [commutator_def, Subgroup.commutator_eq_bot_iff_le_centralizer]
      intro x _
      rw [Subgroup.mem_centralizer_iff]
      intro y _
      exact hcon y x
    rw [hperf] at hc
    exact top_ne_bot hc
  by_cases hτ1 : τ = 1
  ·
    subst hτ1
    have hCtop : C = ⊤ := Subgroup.ext fun z => by simp [hC]
    subst hCtop
    exact hsimple (CFSG.SignalizerFunctorTheorem.CatalogBridge.isSimpleGroup_reeGamma_F4 ha hK)
      (hnc0 ha hK)
      (by rw [Sec8.Item86ResProof.card_of_mulEquiv_reeGamma a K hK (MulEquiv.refl _)]
          exact lt_ordTwistedF4 a)
      Subgroup.topEquiv
  by_cases hin : ∃ g : ReeTag.F4.reeGamma K a, τ = MulAut.conj g
  ·
    obtain ⟨g, hg⟩ := hin
    obtain ⟨y, hy, hy3, hy1⟩ :=
      CFSG.HardMathSupport.Dickson.SuzukiReeB.exists_eq_conj_of_mem_range hZ ⟨g, hg.symm⟩ hτ hτ1
    have hyo : orderOf y = 3 := orderOf_eq_prime hy3 hy1
    obtain ⟨eU⟩ := Sec8.Item8KFacts2Proof.centralizer_mulEquiv_unitarySU a K hK y hyo
    have hCeq : C = Subgroup.centralizer ({y} : Set (ReeTag.F4.reeGamma K a)) := by
      ext z
      rw [hC, hy, Subgroup.mem_centralizer_singleton_iff, MulAut.conj_apply]
      constructor
      · intro h
        calc z * y = y * z * y⁻¹ * y := by rw [h]
          _ = y * z := by group
      · intro h
        rw [← h]
        group
    subst hCeq
    have hF'card : Nat.card (GaloisField 2 (2 * (2 * a + 1))) = (2 ^ (2 * a + 1)) ^ 2 := by
      rw [GaloisField.card 2 _ (by omega), ← pow_mul, mul_comm]
    have hF'card' : Nat.card (GaloisField 2 (2 * (2 * a + 1))) = 2 ^ (2 * (2 * a + 1)) :=
      GaloisField.card 2 _ (by omega)
    obtain ⟨hq, hZU⟩ := Sec8.Item87Proof.isQuasisimple_statedSU_three
      (F := GaloisField 2 (2 * (2 * a + 1))) (f := 2 * a + 1) hF'card (by omega)
    have hCq : CFSG.IsQuasisimple ↥(Subgroup.centralizer ({y} : Set (ReeTag.F4.reeGamma K a))) :=
      CFSG.LocalCores.isQuasisimple_of_mulEquiv eU.symm hq
    refine isEmpty_A5_of_le hJC le_rfl hsub hCq ?_ ?_ hJ
    · rw [card_center_of_mulEquiv eU]
      exact hZU
    · rw [Nat.card_congr eU.toEquiv]
      exact lt_card_statedSU_three (by omega) hF'card'
  ·
    push Not at hin
    obtain ⟨g, σ, hσ, hg⟩ := SeitzOuterCube.Exc.reeF4_stdDescent_odd ha hK Nat.prime_three τ
      ⟨orderOf_eq_prime hτ hτ1, hin⟩
    obtain ⟨b, hkcard, hchar, ⟨eC⟩⟩ := exists_fixSubgroup_fieldAut_equiv hK Nat.prime_three
      (by norm_num) σ hσ
    haveI := hchar
    haveI : Finite (fixSubfield σ) := Subtype.finite
    haveI : Finite (ModGL ReeTag.F4.tag (fixSubfield σ)) := finite_modGL
    haveI : Finite ↥(ReeTag.F4.reeGamma (fixSubfield σ) b) := Subtype.finite
    set δ := ReeTag.F4.reeGammaFieldAut K a σ with hδ
    have hCeq : C = Sec4.autFix (MulAut.conj g * δ * (MulAut.conj g)⁻¹) :=
      Subgroup.ext fun z => (hC z).trans (by rw [hg]; exact Sec4.mem_autFix.symm)
    have hfix : Sec4.autFix δ = fixSubgroup δ := Subgroup.ext fun _ => Iff.rfl
    let eCδ : ↥C ≃* ReeTag.F4.reeGamma (fixSubfield σ) b :=
      (((MulEquiv.subgroupCongr hCeq).trans
        (RonanK429Lie.autFixConjEquiv (MulAut.conj g) δ)).trans
          (MulEquiv.subgroupCongr hfix)).trans eC
    rcases Nat.eq_zero_or_pos b with rfl | hb
    ·
      have hk2 : Nat.card (fixSubfield σ) = 2 := by simpa using hkcard
      have hv : LieTypeIndex.tits.Valid := by
        refine (LieTypeIndex.valid_iff _).2 ⟨?_, ?_⟩
        · simp [LieTypeIndex.inStandardRange_iff]
        · simp [LieTypeIndex.isDuplicateRepresentative_iff]
      let eR : ↥C ≃* ↥(reeFixed ReeTag.F4 (fixSubfield σ) 0) :=
        eCδ.trans (ReeTag.reeFixedEquivReeGamma (fixSubfield σ) 0).symm
      have hT := (CFSG.LieType.Simplicity.titsData (fixSubfield σ) hk2).isQuasisimple hk2
      obtain ⟨eT⟩ := nonempty_commutator_reeFixed_equiv_cat_tits hk2 hv
      haveI : Finite ↥(reeFixed ReeTag.F4 (fixSubfield σ) 0) := Subtype.finite
      haveI : Finite ↥(commutator ↥(reeFixed ReeTag.F4 (fixSubfield σ) 0)) := Subtype.finite
      haveI : Finite (TauCeti.CFSGIndex.lie ⟨.tits, hv⟩).Group := Finite.of_equiv _ eT.toEquiv
      haveI : IsSimpleGroup (TauCeti.CFSGIndex.lie ⟨.tits, hv⟩).Group :=
        (CFSG.LieType.Simplicity.fam_tits_simplicity _ 2 1
          (CFSG.RankThree.PartOne.CTP.reeTitsModel_tits ⟨hv, ⟨MulEquiv.refl _⟩⟩)).2
      haveI hTs : IsSimpleGroup ↥(commutator ↥(reeFixed ReeTag.F4 (fixSubfield σ) 0)) :=
        (MulEquiv.isSimpleGroup_congr eT).2 inferInstance
      obtain ⟨N, hNC, hJN, ⟨eN⟩⟩ := exists_le_of_equiv_comm eR
        (Q := commutator ↥(reeFixed ReeTag.F4 (fixSubfield σ) 0))
        (fun x y => Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _))
        hJC (by haveI := hJ.1; exact ⟨hJ.1.commutator_eq_top⟩)
      have hNq : CFSG.IsQuasisimple ↥N := CFSG.LocalCores.isQuasisimple_of_mulEquiv eN.symm hT
      have hncT : ∃ x y : ↥(commutator ↥(reeFixed ReeTag.F4 (fixSubfield σ) 0)),
          x * y ≠ y * x := by
        obtain ⟨x, y, hxy⟩ := exists_noncomm_of_isQuasisimple hT
        exact ⟨x, y, hxy⟩
      refine isEmpty_A5_of_le hJN hNC hsub hNq ?_ ?_ hJ
      · rw [card_center_of_mulEquiv eN, card_center_of_simple hTs hncT]
        norm_num
      · rw [Nat.card_congr eN.toEquiv, Nat.card_congr eT.toEquiv,
          lieOrderBridge_holds ⟨_, hv⟩ _ ⟨MulEquiv.refl _⟩]
        change 180 < CFSG.HardMathSupport.Solomon.Coordinator.I1420.lieOrderFormula .tits
        norm_num [CFSG.HardMathSupport.Solomon.Coordinator.I1420.lieOrderFormula,
          CFSG.Open.orderTits]
    ·
      have hs : IsSimpleGroup ↥(ReeTag.F4.reeGamma (fixSubfield σ) b) :=
        CFSG.SignalizerFunctorTheorem.CatalogBridge.isSimpleGroup_reeGamma_F4 hb hkcard
      exact hsimple hs (hnc0 hb hkcard)
        (by rw [Sec8.Item86ResProof.card_of_mulEquiv_reeGamma b (fixSubfield σ) hkcard
              (MulEquiv.refl _)]
            exact lt_ordTwistedF4 b)
        eCδ

end Ree

section Row


theorem noONAt_of_lie {S : Type} [Group S] [Finite S] (hs : IsSimpleGroup S)
    (hna : ∃ a b : S, a * b ≠ b * a) (idx : ValidLieTypeIndex)
    (he : Nonempty (S ≃* (TauCeti.CFSGIndex.lie idx).Group)) (β : MulAut S) (hβ : β ^ 3 = 1)
    (J : Subgroup S) (hJ : J ≤ Sec4.autFix β) (hq : CFSG.IsQuasisimple ↥J)
    (hsn : (J.subgroupOf (Sec4.autFix β)).IsSubnormal) :
    IsEmpty (↥J ⧸ Subgroup.center ↥J ≃* Blueprint.NativeSporadic.ON) := by
  refine ⟨fun e => ?_⟩
  have hJo : CFSG.Open.IsQuasisimple ↥J :=
    (CFSG.ComponentClassification.AssemblyBPredicates.isQuasisimple_iff_open _).1
      ((CFSG.ComponentClassification.AssemblyBPredicates.isQuasisimple_iff_native _).2 hq)
  have h3 : 3 ∣ Nat.card J := by
    refine Dvd.dvd.trans ?_ (Subgroup.card_quotient_dvd_card (Subgroup.center ↥J))
    rw [Nat.card_congr e.toEquiv]
    exact three_dvd_card_ON
  have hd := (lieComp_holds S hs hna idx he β hβ J (glaPComponent_of_autFix hJ hq hsn h3)).1
  obtain ⟨e₁⟩ := centerQuot_equiv hJo.1 (CFSG.Open.GLAPPrimeCore 3 ↥J)
    (glaPPrimeCore_le_center hJo h3)
  exact not_isChevSimple_ON lieOrderBridge_holds (isChevSimple_congr (e₁.trans e) hd.chev)

theorem kH1_seven_F4 (m : ℕ) (hm : (LieTypeIndex.reeF4 m).Valid) :
    RowOf427 (TauCeti.CFSGIndex.lie ⟨.reeF4 m, hm⟩).Group := by
  intro S _ _ hs hna ⟨eS⟩
  refine row427_of_noA5ON fun T _ _ ⟨eT⟩ τ hτ => ?_
  obtain ⟨hsT, hnaT⟩ := simple_nonab_of_mulEquiv eT hs hna
  have hR := CFSG.HardMathSupport.Timmesfeld.DefChar.lot_reeTitsModel_twistedF4_of_index m hm
    (eT.trans eS)
  obtain ⟨-, a, ha, -, K, _, _, _, hK, ⟨e⟩⟩ := CFSG.RankThree.PartTwo.Sec4.exists_mulEquiv_reeGamma hR
  intro J hJ hq hsn hX
  rcases hX with h5 | hO
  · exact (noA5_of_mulEquiv e (reeF4_noA5 ha hK) τ hτ (Sec4.autFix τ) J (fun z => Iff.rfl) hJ
      hsn hq).false h5.some
  · exact (noONAt_of_lie hsT hnaT ⟨_, hm⟩ ⟨eT.trans eS⟩ τ hτ J hJ hq hsn).false hO.some

end Row

end CFSG.RankThree.PartTwo.Sec4.Ronan148L
