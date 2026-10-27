module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PFsection8.Basic

namespace CFSG
end CFSG
open CFSG

noncomputable section

namespace CFSG.Section8

universe v
universe w
universe u


/-- Peterfalvi `(8.9)`. -/


private theorem theorem_8_8_ti_nonidentity_of_ti
    {G : Type u} [Group G] [Finite G]
    {X : Set G}
    (hTI : section16TISubset X) :
    section16TISubset (section16NonidentityElements X) := by
  intro g
  rcases hTI g with hEq | hSub
  · left
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      rcases hx with ⟨hxX, hxne⟩
      refine ⟨?_, ?_⟩
      · have : g * x * g⁻¹ ∈ section16ConjugateSet X g := ⟨x, hxX, rfl⟩
        simpa [hEq] using this
      · intro h
        apply hxne
        calc
          x = g⁻¹ * (g * x * g⁻¹) * g := by group
          _ = 1 := by simp [h]
    · intro hy
      rcases hy with ⟨hyX, hyne⟩
      have hyConj : y ∈ section16ConjugateSet X g := by
        simpa [hEq] using hyX
      rcases hyConj with ⟨x, hxX, hxy⟩
      have hxne : x ≠ 1 := by
        intro hxone
        apply hyne
        simpa [hxone] using hxy
      exact ⟨x, ⟨hxX, hxne⟩, hxy⟩
  · right
    intro y hy
    apply hSub
    refine ⟨hy.1.1, ?_⟩
    rcases hy.2 with ⟨x, hx, hxy⟩
    exact ⟨x, hx.1, hxy⟩

private theorem theorem_8_8_complement_exponent_dvd_of_quotientExponentDvd
    {G : Type u} [Group G] [Finite G]
    {H M U : Subgroup G} {n : ℕ}
    (hcomp : section12ComplementIn M H U)
    (hquot : section16QuotientExponentDvd H M n) :
    Monoid.exponent U ∣ n := by
  classical
  rcases hcomp with ⟨hHM, hUM, hsup, hdisj⟩
  rcases hquot with ⟨_hHM, hNorm, hDvd⟩
  haveI : (H.subgroupOf M).Normal := hNorm
  have hsup_local : U.subgroupOf M ⊔ H.subgroupOf M = ⊤ := by
    calc
      U.subgroupOf M ⊔ H.subgroupOf M = (U ⊔ H).subgroupOf M := by
        symm
        exact Subgroup.subgroupOf_sup (A := U) (A' := H) (B := M) hUM hHM
      _ = ⊤ := by
        rw [sup_comm, hsup]
        simp
  have hcomp' : (U.subgroupOf M).IsComplement' (H.subgroupOf M) := by
    refine Subgroup.isComplement'_of_disjoint_and_mul_eq_univ ?_ ?_
    · rw [Subgroup.disjoint_def]
      intro x hxU hxH
      apply Subtype.ext
      exact hdisj.le_bot ⟨by simpa [Subgroup.mem_subgroupOf] using hxH,
        by simpa [Subgroup.mem_subgroupOf] using hxU⟩
    · simpa [hsup_local] using
        (Subgroup.mul_normal (U.subgroupOf M) (H.subgroupOf M)).symm
  let eQ : M ⧸ H.subgroupOf M ≃* U.subgroupOf M := hcomp'.QuotientMulEquiv
  have hUsub_exp : Monoid.exponent (U.subgroupOf M) = Monoid.exponent U := by
    simpa using Monoid.exponent_eq_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hUM)
  have hquot_exp : Monoid.exponent (M ⧸ H.subgroupOf M) = Monoid.exponent U := by
    calc
      Monoid.exponent (M ⧸ H.subgroupOf M) =
          Monoid.exponent (U.subgroupOf M) := by
        simpa using Monoid.exponent_eq_of_mulEquiv eQ
      _ = Monoid.exponent U := hUsub_exp
  simpa [hquot_exp] using hDvd

private theorem theorem_8_8_typeI_to_source
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    {M MF : Subgroup G}
    (hM : M ∈ section9MaximalSubgroups G)
    (hMF : section16MFSubgroup M MF)
    (hType : section16TypeI M MF) :
    typeIDefinitionData M MF := by
  classical
  rcases section15_exists_KUData_for_maximal (G := G) (M := M) hM with
    ⟨K, U, hKU15⟩
  have hKU : section16KUData M K U := by
    simpa [section16KUData] using hKU15
  have hProp :=
    proposition_16_1 (G := G) (M := M) (MF := MF) (K := K) (U := U)
      hM hMF hKU
  rcases hProp with
    ⟨hIiff, _hIIiff, _hIIIIViff, _hViff, _hDeriff, hMFiff⟩
  have hFcase : section16CaseF K U := hIiff.mp hType
  have hMF_eq : MF = section10Msigma M := hMFiff.mpr (Or.inl hType)
  rcases hFcase with ⟨hKbot, hUne⟩
  have hCompMFU : section12ComplementIn M MF U := by
    simpa [section16KUData, hKbot, ← hMF_eq] using hKU15.2.2.1
  rcases hType with
    ⟨hMFpos, hMFlt, hAbelianControl, hFrobComp, _hKappa, _hQuotRank, hAlt⟩
  rcases hAbelianControl U hCompMFU with
    ⟨U1, hU1le, hU1comm, hU1norm, hCent⟩
  rcases hFrobComp U hCompMFU with ⟨U0, hU0le, hExp, hFrob⟩
  refine ⟨U, U1, U0, ?_, ?_⟩
  · refine ⟨?_, ?_, hMF, hMFpos, hMFlt, hUne, hCompMFU, hU1le,
      hU1comm, hU1norm, hCent, hU0le, hExp, hFrob⟩
    · exact IsMinCE.proper_subgroups_solvable M (lt_top_iff_ne_top.2 hM.1)
    · exact odd_of_card_dvd IsMinCE.odd_order (Subgroup.card_subgroup_dvd_card M)
  · rcases hAlt with hTI | hRest
    · exact Or.inl (theorem_8_8_ti_nonidentity_of_ti hTI)
    · rcases hRest with hRank | hCond
      · exact Or.inr (Or.inl hRank)
      · rcases hCond with ⟨hExpQuot, p, hpMF, _hpPi, hpCycMF⟩
        refine Or.inr (Or.inr ⟨?_, ?_⟩)
        · intro q hqMF
          exact theorem_8_8_complement_exponent_dvd_of_quotientExponentDvd
            hCompMFU (hExpQuot q hqMF).2
        · exact ⟨p, hpMF, hpCycMF⟩

private theorem theorem_8_8_typeCommon_W1_le_M
    {G : Type u} [Group G] [Finite G]
    {M MF U W1 W2 : Subgroup G}
    (hCommon : section16TypeCommon M MF U W1 W2) :
    W1 ≤ M := by
  rcases hCommon with
    ⟨_hHallD, _hMFleD, _hCompMFU, _hUnil, hW1norm, _hW1cyc, _hW1card,
      _hMFnotCyclic, _hSecondLe, _hFittingEq, _hFittingLeD, _hW2leMF,
      _hW2ne, _hW2cyc, _hCentralizer, _hHatW, _hT6⟩
  intro x hx
  exact (mem_subgroupNormalizerIn.mp (hW1norm hx)).2

private theorem theorem_8_8_typeCommon_W1_hall
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    {M MF U W1 W2 : Subgroup G}
    (hCommon : section16TypeCommon M MF U W1 W2) :
    section16HallSubgroupOf W1 M := by
  classical
  have hW1M : W1 ≤ M :=
    theorem_8_8_typeCommon_W1_le_M hCommon
  have hHallCompl :
      IsHallSubgroup (subgroupPrimeSet (ambientDerivedSubgroup M))ᶜ
        (W1.subgroupOf M) :=
    section16_W1_hall_compl_derived_of_typeCommon (G := G) hCommon
  refine ⟨hW1M, ?_⟩
  refine isHallSubgroup_of (G := M) (π := subgroupPrimeSet W1)
    (H := W1.subgroupOf M) ?_ ?_
  · intro p hpW1
    have hcardW1 : Nat.card (W1.subgroupOf M) = Nat.card W1 :=
      natCard_subgroupOf_eq W1 M hW1M
    simpa [subgroupPrimeSet, hcardW1] using hpW1
  · intro p hpW1 hpidx
    have hpW1sub : p.val ∣ Nat.card (W1.subgroupOf M) := by
      have hcardW1 : Nat.card (W1.subgroupOf M) = Nat.card W1 :=
        natCard_subgroupOf_eq W1 M hW1M
      simpa [subgroupPrimeSet, hcardW1] using hpW1
    have hpCompl : p ∈ (subgroupPrimeSet (ambientDerivedSubgroup M))ᶜ :=
      hHallCompl.p_in_pi_of_p_dvd_card p hpW1sub
    exact (hHallCompl.p_in_pi_of_p_dvd_index p hpidx) hpCompl

public theorem theorem_8_8_typeCommon_W1_complement
    {G : Type u} [Group G] [Finite G]
    {M MF V W1 W2 : Subgroup G}
    (hCommon : section16TypeCommon M MF V W1 W2) :
    section12ComplementIn M (ambientDerivedSubgroup M) W1 := by
  classical
  let D : Subgroup G := ambientDerivedSubgroup M
  have hCommon' : section16TypeCommon M MF V W1 W2 := hCommon
  rcases hCommon with
    ⟨hHallD, _hMFleD, _hCompMFV, _hVnil, _hW1norm, _hW1cyc, _hW1card,
      _hMFnotCyclic, _hSecondLe, _hFittingEq, _hFittingLeD, _hW2leMF,
      _hW2ne, _hW2cyc, _hCentralizer, _hHatW, _hT6⟩
  rcases hHallD with ⟨hDleM, hDHall⟩
  have hW1M : W1 ≤ M :=
    theorem_8_8_typeCommon_W1_le_M hCommon'
  have hW1HallCompl :
      IsHallSubgroup (subgroupPrimeSet D)ᶜ (W1.subgroupOf M) := by
    simpa [D] using
      section16_W1_hall_compl_derived_of_typeCommon (G := G) hCommon'
  have hcompLocal : (D.subgroupOf M).IsComplement' (W1.subgroupOf M) :=
    section11_isComplement_of_isHall_compl hDHall hW1HallCompl
  refine ⟨by simpa [D] using hDleM, hW1M, ?_, ?_⟩
  · apply le_antisymm
    · intro x hxM
      let xM : M := ⟨x, hxM⟩
      have hxSup : xM ∈ D.subgroupOf M ⊔ W1.subgroupOf M := by
        simp [hcompLocal.sup_eq_top]
      have hxSub : xM ∈ (D ⊔ W1).subgroupOf M := by
        have hsub_eq :
            (D ⊔ W1).subgroupOf M = D.subgroupOf M ⊔ W1.subgroupOf M := by
          exact Subgroup.subgroupOf_sup (A := D) (A' := W1) (B := M)
            hDleM hW1M
        simpa [hsub_eq] using hxSup
      simpa [xM, D, Subgroup.mem_subgroupOf] using hxSub
    · exact sup_le hDleM hW1M
  · rw [Subgroup.disjoint_def]
    intro x hxD hxW1
    let xM : M := ⟨x, hDleM hxD⟩
    have hxDloc : xM ∈ D.subgroupOf M := by
      simpa [xM, Subgroup.mem_subgroupOf] using hxD
    have hxW1loc : xM ∈ W1.subgroupOf M := by
      simpa [xM, Subgroup.mem_subgroupOf] using hxW1
    have hxbot : xM ∈ (⊥ : Subgroup M) :=
      Subgroup.disjoint_def.mp hcompLocal.disjoint hxDloc hxW1loc
    change (xM : G) = (1 : G)
    exact congrArg Subtype.val (by simpa using hxbot)

private theorem theorem_8_8_hallSubgroup_in_intermediate_of_hall_overgroup
    {G : Type u} [Group G] [Finite G]
    {H D M : Subgroup G}
    (hHD : H ≤ D) (hDM : D ≤ M)
    (hHallHM : IsHallSubgroup (subgroupPrimeSet H) (H.subgroupOf M)) :
    IsHallSubgroup (subgroupPrimeSet H) (H.subgroupOf D) := by
  classical
  let Dsub : Subgroup M := D.subgroupOf M
  have hHcardM : Nat.card (H.subgroupOf M) = Nat.card H :=
    natCard_subgroupOf_eq H M (hHD.trans hDM)
  have hHcardD : Nat.card (H.subgroupOf D) = Nat.card H :=
    natCard_subgroupOf_eq H D hHD
  have hHsub_le_Dsub : H.subgroupOf M ≤ Dsub := by
    intro x hx
    exact hHD hx
  refine isHallSubgroup_of (G := D) (π := subgroupPrimeSet H)
    (H := H.subgroupOf D) ?_ ?_
  · intro p hp
    exact hHallHM.p_in_pi_of_p_dvd_card p
      (by simpa [hHcardM, hHcardD] using hp)
  · intro p hpπ hpidx
    have hrel_eq :
        (H.subgroupOf D).index = (H.subgroupOf M).relIndex Dsub := by
      have hsub :=
        Subgroup.relIndex_subgroupOf (H := H) (K := D) (L := M) hDM
      simpa [Dsub, Subgroup.relIndex] using hsub.symm
    have hidx_dvd :
        (H.subgroupOf D).index ∣ (H.subgroupOf M).index := by
      have hrel_dvd :
          (H.subgroupOf M).relIndex Dsub ∣ (H.subgroupOf M).index :=
        Subgroup.relIndex_dvd_index_of_le hHsub_le_Dsub
      simpa [hrel_eq] using hrel_dvd
    exact (hHallHM.p_in_pi_of_p_dvd_index p (hpidx.trans hidx_dvd)) hpπ

private theorem theorem_8_8_hallSubgroup_in_overgroup_of_hall_intermediate
    {G : Type u} [Group G] [Finite G]
    {H D M : Subgroup G}
    (hHD : H ≤ D) (hDM : D ≤ M)
    (hHallHD : IsHallSubgroup (subgroupPrimeSet H) (H.subgroupOf D))
    (hHallDM : IsHallSubgroup (subgroupPrimeSet D) (D.subgroupOf M)) :
    IsHallSubgroup (subgroupPrimeSet H) (H.subgroupOf M) := by
  classical
  refine isHallSubgroup_of (G := M) (π := subgroupPrimeSet H)
    (H := H.subgroupOf M) ?_ ?_
  · intro p hp
    have hcardM : Nat.card (H.subgroupOf M) = Nat.card H :=
      natCard_subgroupOf_eq H M (hHD.trans hDM)
    simpa [subgroupPrimeSet, hcardM] using hp
  · intro p hpH hpidxM
    let Dsub : Subgroup M := D.subgroupOf M
    have hHsubM_le_Dsub : H.subgroupOf M ≤ Dsub := by
      intro x hx
      exact hHD hx
    have hrel_eq : (H.subgroupOf M).relIndex Dsub = (H.subgroupOf D).index := by
      have hsub :=
        Subgroup.relIndex_subgroupOf (H := H) (K := D) (L := M) hDM
      simpa [Dsub, Subgroup.relIndex] using hsub
    have hidx_eq : (H.subgroupOf M).index =
        (H.subgroupOf D).index * (D.subgroupOf M).index := by
      calc
        (H.subgroupOf M).index =
            (H.subgroupOf M).relIndex Dsub * Dsub.index := by
          exact (Subgroup.relIndex_mul_index hHsubM_le_Dsub).symm
        _ = (H.subgroupOf D).index * (D.subgroupOf M).index := by
          rw [hrel_eq]
    have hpProd : p.val ∣ (H.subgroupOf D).index * (D.subgroupOf M).index := by
      simpa [hidx_eq] using hpidxM
    rcases (p.property.dvd_mul).mp hpProd with hpHD | hpDMidx
    · exact (hHallHD.p_in_pi_of_p_dvd_index p hpHD) hpH
    · have hpHcard : p.val ∣ Nat.card H := by
        simpa [subgroupPrimeSet] using hpH
      have hpD : p ∈ subgroupPrimeSet D :=
        hpHcard.trans (Subgroup.card_dvd_of_le hHD)
      exact (hHallDM.p_in_pi_of_p_dvd_index p hpDMidx) hpD

private theorem theorem_8_8_mem_normalizer_of_conjBy_le_self
    {G : Type u} [Group G] [Finite G] {H : Subgroup G} {g : G}
    (hg : H.conjBy g ≤ H) :
    g ∈ Subgroup.normalizer (H : Set G) := by
  have hcard : Nat.card (H.conjBy g) = Nat.card H := by
    simpa [Subgroup.conjBy] using
      (Subgroup.card_map_of_injective (K := H) (f := (MulAut.conj g).toMonoidHom)
        (hf := EquivLike.injective (MulAut.conj g)))
  have hEq : H.conjBy g = H := Subgroup.eq_of_le_of_card_ge hg (by simp [hcard])
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · intro hx
    have hx' : g * x * g⁻¹ ∈ H.conjBy g := by
      refine Subgroup.mem_map.mpr ?_
      exact ⟨x, hx, by simp [MulAut.conj_apply]⟩
    simpa [hEq] using hx'
  · intro hx
    have hx' : g * x * g⁻¹ ∈ H.conjBy g := by
      simpa [hEq] using hx
    rcases Subgroup.mem_map.mp hx' with ⟨y, hy, hyx⟩
    have hxy : x = y := by
      calc
        x = g⁻¹ * (g * x * g⁻¹) * g := by group
        _ = g⁻¹ * (g * y * g⁻¹) * g := by
          rw [show g * x * g⁻¹ = g * y * g⁻¹ by
            simpa [MulAut.conj_apply] using hyx.symm]
        _ = y := by group
    simpa [hxy] using hy

private theorem theorem_8_8_normal_in_overgroup_of_normal_hall_intermediate
    {G : Type u} [Group G] [Finite G]
    {H D M : Subgroup G}
    (hHD : H ≤ D) (hDM : D ≤ M)
    (hNormHD : (H.subgroupOf D).Normal)
    (hNormDM : (D.subgroupOf M).Normal)
    (hHallHD : IsHallSubgroup (subgroupPrimeSet H) (H.subgroupOf D)) :
    (H.subgroupOf M).Normal := by
  classical
  have hM_norm_D : M ≤ Subgroup.normalizer (D : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hDM).1 hNormDM
  have hHM : H ≤ M := hHD.trans hDM
  refine (Subgroup.normal_subgroupOf_iff_le_normalizer hHM).2 ?_
  intro m hmM
  have hmNormD : (m : G) ∈ Subgroup.normalizer (D : Set G) := hM_norm_D hmM
  let mD : Subgroup.normalizer (D : Set G) := ⟨m, hmNormD⟩
  let φ : MulAut D := Subgroup.normalizerMonoidHom D mD
  letI : (H.subgroupOf D).Normal := hNormHD
  have hEqLocal : (H.subgroupOf D).map φ.toMonoidHom = H.subgroupOf D := by
    exact hHallHD.eq_of_normal (hHallHD.map_mulAut φ)
  apply theorem_8_8_mem_normalizer_of_conjBy_le_self
  intro y hy
  rcases Subgroup.mem_map.mp hy with ⟨x, hxH, rfl⟩
  have hxD : x ∈ D := hHD hxH
  let xD : D := ⟨x, hxD⟩
  let xH : H.subgroupOf D := ⟨xD, by simpa [xD, Subgroup.mem_subgroupOf] using hxH⟩
  have hxMap : φ xD ∈ (H.subgroupOf D).map φ.toMonoidHom := by
    refine Subgroup.mem_map.mpr ?_
    exact ⟨xH, xH.property, rfl⟩
  rw [hEqLocal] at hxMap
  change (m : G) * x * (m : G)⁻¹ ∈ H
  simpa [φ, mD, xD, Subgroup.normalizerMonoidHom_apply_apply_coe,
    Subgroup.mem_subgroupOf, MulAut.conj_apply] using hxMap

private theorem theorem_8_8_derived_mfSubgroup_of_typeCommon
    {G : Type u} [Group G] [Finite G]
    {M MF U W1 W2 : Subgroup G}
    (hMF : section16MFSubgroup M MF)
    (hCommon : section16TypeCommon M MF U W1 W2) :
    section16MFSubgroup (ambientDerivedSubgroup M) MF := by
  classical
  let D : Subgroup G := ambientDerivedSubgroup M
  rcases hCommon with
    ⟨hHallD, hMFleD, _hCompMFU, _hUnil, _hW1norm, _hW1cyc, _hW1card,
      _hMFnotCyclic, _hSecondLe, _hFittingEq, _hFittingLeD, _hW2leMF,
      _hW2ne, _hW2cyc, _hCentralizer, _hHatW, _hT6, _hW2Second⟩
  rcases hHallD with ⟨hDleM, hDHall⟩
  rcases hMF.1 with ⟨hMFM, hMFnormM, hMFnil, hMFHallM⟩
  have hDnormM : (D.subgroupOf M).Normal := by
    simpa [D] using (section12_normalIn_ambientDerivedSubgroup (G := G) (E := M)).2
  have hMFnormD : (MF.subgroupOf D).Normal := by
    have hM_le_norm_MF : M ≤ Subgroup.normalizer (MF : Set G) :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer hMFM).1 hMFnormM
    exact (Subgroup.normal_subgroupOf_iff_le_normalizer hMFleD).2
      (hDleM.trans hM_le_norm_MF)
  have hMFHallD : IsHallSubgroup (subgroupPrimeSet MF) (MF.subgroupOf D) :=
    theorem_8_8_hallSubgroup_in_intermediate_of_hall_overgroup
      (H := MF) (D := D) (M := M) hMFleD hDleM hMFHallM
  refine ⟨⟨hMFleD, hMFnormD, hMFnil, hMFHallD⟩, ?_⟩
  intro H hH
  rcases hH with ⟨hHD, hHnormD, hHnil, hHHallD⟩
  have hHnormM : (H.subgroupOf M).Normal :=
    theorem_8_8_normal_in_overgroup_of_normal_hall_intermediate
      (H := H) (D := D) (M := M) hHD hDleM hHnormD hDnormM hHHallD
  have hHHallM : IsHallSubgroup (subgroupPrimeSet H) (H.subgroupOf M) :=
    theorem_8_8_hallSubgroup_in_overgroup_of_hall_intermediate
      (H := H) (D := D) (M := M) hHD hDleM hHHallD hDHall
  exact hMF.2 H ⟨hHD.trans hDleM, hHnormM, hHnil, hHHallM⟩

public theorem theorem_8_8_typeCommon_to_typePDefinitionData
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    {M MF K KU U W1 W2 : Subgroup G}
    (hM : M ∈ section9MaximalSubgroups G)
    (hMF : section16MFSubgroup M MF)
    (hKU : section16KUData M K KU)
    (hCommon : section16TypeCommon M MF U W1 W2) :
    typePDefinitionData M MF U W1 W2 := by
  have hW1ne : W1 ≠ ⊥ :=
    section16_W1_ne_bot_of_typeCommon (G := G) hM hMF hKU hCommon
  have hW1Hall : section16HallSubgroupOf W1 M :=
    theorem_8_8_typeCommon_W1_hall hCommon
  have hW1Comp : section12ComplementIn M (ambientDerivedSubgroup M) W1 :=
    theorem_8_8_typeCommon_W1_complement hCommon
  rcases hCommon with
    ⟨_hHallD, _hMFleD, hCompMFU, hUnil, hW1norm, hW1cyc, _hW1card,
      hMFnotCyclic, hSecondLe, hFittingEq, hFittingLeD, hW2leMF,
      hW2ne, hW2cyc, hCentralizer, hHatW, _hT6, hW2Second⟩
  refine ⟨hMF, hW1cyc, hW1ne, hW1Hall, hW1Comp, hCompMFU.2.1, hUnil,
    hW1norm, hCompMFU, hMFnotCyclic, hSecondLe, ?_, hFittingLeD, ?_,
    hW2cyc, hW2ne, hCentralizer, hHatW⟩
  · exact hFittingEq.symm
  · intro x hx
    exact ⟨hW2leMF hx, hW2Second hx⟩

private theorem theorem_8_8_typeII_typeFData_of_canonical
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    {M MF K U : Subgroup G}
    (hM : M ∈ section9MaximalSubgroups G)
    (hMF : section16MFSubgroup M MF)
    (hKU : section16KUData M K U)
    (hType : section16TypeII M MF) :
    ∃ U1 U0 : Subgroup G,
      typeFData (ambientDerivedSubgroup M) MF U U1 U0 := by
  classical
  let D : Subgroup G := ambientDerivedSubgroup M
  rcases section16_typeII_canonical_caseP2_data
      (G := G) (M := M) (MF := MF) (K := K) (U := U)
      hM hMF hKU hType with
    ⟨hCommon, _hExtra, hUcomm, hUne, _hNormNotLe, hMF_eq⟩
  have hMFD : section16MFSubgroup D MF := by
    simpa [D] using
      theorem_8_8_derived_mfSubgroup_of_typeCommon (G := G) hMF hCommon
  have hKU15 : section15KUData M K U := by
    simpa [section16KUData] using hKU
  rcases hCommon with
    ⟨hHallD, hMFleD, hCompMFU, _hUnil, _hW1norm, _hW1cyc, _hW1card,
      hMFnotCyclic, _hSecondLe, _hFittingEq, _hFittingLeD, _hW2leMF,
      _hW2ne, _hW2cyc, _hCentralizer, _hHatW, _hT6, _hW2Second⟩
  rcases hHallD with ⟨hDleM, _hDHall⟩
  have hDneTop : D ≠ ⊤ := by
    intro hDtop
    have htop_le_M : (⊤ : Subgroup G) ≤ M := by
      intro x _hx
      exact hDleM (by simp [D, hDtop])
    exact hM.1 (top_le_iff.mp htop_le_M)
  have hsolvD : IsSolvable D :=
    IsMinCE.proper_subgroups_solvable D (lt_top_iff_ne_top.2 hDneTop)
  have hoddD : Odd (Nat.card D) :=
    odd_of_card_dvd IsMinCE.odd_order (Subgroup.card_subgroup_dvd_card D)
  have hMFne : MF ≠ ⊥ := by
    intro hMFbot
    exact hMFnotCyclic (by
      rw [hMFbot]
      infer_instance)
  have hMFpos : ⊥ < MF := bot_lt_iff_ne_bot.2 hMFne
  have hMFltD : MF < D := by
    refine lt_of_le_of_ne hMFleD ?_
    intro hMFD
    have hUleMF : U ≤ MF := by
      simpa [D, hMFD] using hCompMFU.2.1
    have hUbot : U = ⊥ := by
      apply le_bot_iff.mp
      intro x hxU
      exact hCompMFU.2.2.2.le_bot ⟨hUleMF hxU, hxU⟩
    exact hUne hUbot
  have hUnormU : section10NormalIn U U := by
    refine ⟨le_rfl, ?_⟩
    simp
  rcases lemma_15_1_e_join (G := G) (M := M) (K := K) (U := U)
      hM hKU15 hUne with
    ⟨U0, hU0le, hExp, hFrobSigma⟩
  have hFrobMF : section12FrobeniusJoinWithKernel MF U0 := by
    simpa [hMF_eq] using hFrobSigma
  refine ⟨U, U0, ?_⟩
  exact ⟨hsolvD, hoddD, by simpa [D] using hMFD, hMFpos, hMFltD, hUne,
    by simpa [D] using hCompMFU,
    le_rfl, hUcomm, hUnormU, (by
      intro x hxMF hxne y hy
      exact hy.1), hU0le, hExp, hFrobMF⟩


private theorem theorem_8_8_typeII_to_source_of_canonical
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    {M MF : Subgroup G}
    (hM : M ∈ section9MaximalSubgroups G)
    (hMF : section16MFSubgroup M MF)
    (hType : section16TypeII M MF) :
    typeIIDefinitionData M MF := by
  classical
  rcases section15_exists_KUData_for_maximal (G := G) (M := M) hM with
    ⟨K, U, hKU15⟩
  have hKU : section16KUData M K U := by
    simpa [section16KUData] using hKU15
  rcases section16_typeII_canonical_caseP2_data
      (G := G) (M := M) (MF := MF) (K := K) (U := U)
      hM hMF hKU hType with
    ⟨hCommon, hExtra, hUcomm, hUne, hNormNotLe, _hMF_eq⟩
  have hP : typePDefinitionData M MF U K (section16Kstar M K) :=
    theorem_8_8_typeCommon_to_typePDefinitionData
      (G := G) hM hMF hKU hCommon
  rcases theorem_8_8_typeII_typeFData_of_canonical
      (G := G) (M := M) (MF := MF) (K := K) (U := U)
      hM hMF hKU hType with
    ⟨U1, U0, hF⟩
  exact ⟨U, K, section16Kstar M K, U1, U0, hP,
    ⟨hUne, hExtra.1, theorem_8_8_ti_nonidentity_of_ti hExtra.2⟩,
    hUcomm, hNormNotLe, hF⟩

/-- Public Type-II adapter preserving a specified Section 16 `KUData`
complement.

The older public adapter chooses an arbitrary canonical `K`.  This version is
the source-facing bridge needed when a later source argument has already fixed
the displayed complement, for instance one of the two factors in a PF
`(8.8)(b)` pair. -/
public theorem theorem_8_8_typeII_to_source_with_KUData_public
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    {M MF K U : Subgroup G}
    (hM : M ∈ section9MaximalSubgroups G)
    (hMF : section16MFSubgroup M MF)
    (hKU : section16KUData M K U)
    (hType : section16TypeII M MF) :
    ∃ U1 U0 : Subgroup G,
      typePData M MF U K (section16Kstar M K) ∧
        typePDefinitionData M MF U K (section16Kstar M K) ∧
          typeIIToIVSourceCondition M U K ∧
            IsMulCommutative U ∧
              ¬ Subgroup.normalizer (U : Set G) ≤ M ∧
                typeFData (ambientDerivedSubgroup M) MF U U1 U0 := by
  classical
  rcases section16_typeII_canonical_caseP2_data
      (G := G) (M := M) (MF := MF) (K := K) (U := U)
      hM hMF hKU hType with
    ⟨hCommon, hExtra, hUcomm, hUne, hNormNotLe, _hMF_eq⟩
  have hP : typePDefinitionData M MF U K (section16Kstar M K) :=
    theorem_8_8_typeCommon_to_typePDefinitionData
      (G := G) hM hMF hKU hCommon
  rcases theorem_8_8_typeII_typeFData_of_canonical
      (G := G) (M := M) (MF := MF) (K := K) (U := U)
      hM hMF hKU hType with
    ⟨U1, U0, hF⟩
  exact ⟨U1, U0, ⟨hMF, hCommon⟩, hP,
    ⟨hUne, hExtra.1, theorem_8_8_ti_nonidentity_of_ti hExtra.2⟩,
    hUcomm, hNormNotLe, hF⟩

private theorem theorem_8_8_typeIII_to_source_of_typeP_adapter
    {G : Type u} [Group G] [Finite G]
    {M MF : Subgroup G}
    (hM : M ∈ section9MaximalSubgroups G)
    (hType : section16TypeIII M MF)
    (hP : ∀ U W1 W2 : Subgroup G,
      section16TypeCommon M MF U W1 W2 → typePDefinitionData M MF U W1 W2) :
    typeIIIDefinitionData M MF := by
  rcases hType with ⟨U, W1, W2, hCommon, hExtra, hUcomm, hNormLe⟩
  have hUne : U ≠ ⊥ := by
    intro hUbot
    have htop_le_M : (⊤ : Subgroup G) ≤ M := by
      intro g _hg
      exact hNormLe (by
        rw [Subgroup.mem_normalizer_iff]
        intro x
        simp [hUbot])
    exact hM.1 (top_le_iff.mp htop_le_M)
  exact ⟨U, W1, W2, hP U W1 W2 hCommon,
    ⟨hUne, hExtra.1, theorem_8_8_ti_nonidentity_of_ti hExtra.2⟩,
    hUcomm, hNormLe⟩

private theorem theorem_8_8_typeIV_to_source_of_typeP_adapter
    {G : Type u} [Group G] [Finite G]
    {M MF : Subgroup G}
    (hType : section16TypeIV M MF)
    (hP : ∀ U W1 W2 : Subgroup G,
      section16TypeCommon M MF U W1 W2 → typePDefinitionData M MF U W1 W2) :
    typeIVDefinitionData M MF := by
  rcases hType with ⟨U, W1, W2, hCommon, hExtra, hUncomm, hNormLe⟩
  have hUne : U ≠ ⊥ := by
    intro hUbot
    exact hUncomm (by
      rw [hUbot]
      infer_instance)
  exact ⟨U, W1, W2, hP U W1 W2 hCommon,
    ⟨hUne, hExtra.1, theorem_8_8_ti_nonidentity_of_ti hExtra.2⟩,
    hUncomm, hNormLe⟩

private theorem theorem_8_8_typeV_to_source_of_typeP_adapter
    {G : Type u} [Group G] [Finite G]
    {M MF : Subgroup G}
    (hType : section16TypeV M MF)
    (hP : ∀ U W1 W2 : Subgroup G,
      section16TypeCommon M MF U W1 W2 → typePDefinitionData M MF U W1 W2) :
    typeVDefinitionData M MF := by
  rcases hType with ⟨U, W1, W2, hCommon, hUbot, hAlt⟩
  refine ⟨U, W1, W2, hP U W1 W2 hCommon, hUbot, ?_⟩
  rcases hAlt with hTI | hRest
  · exact Or.inl (theorem_8_8_ti_nonidentity_of_ti hTI.2)
  · rcases hRest with hDvd | hCard
    · rcases hDvd with ⟨p, hpMF, _hpPi, hpCyc, hCardDvd⟩
      exact Or.inr <| Or.inl ⟨p, hpMF, hCardDvd, hpCyc⟩
    · rcases hCard with ⟨p, hpMF, _hpPi, hpCyc, hpCard, hCardDvd⟩
      exact Or.inr <| Or.inr ⟨p, hpMF, hpCard, hCardDvd, hpCyc⟩


private theorem theorem_8_8_case_b_data_to_source
    {G : Type u} [Group G] [Finite G]
    {W W1 W2 S T SF TF : Subgroup G}
    (hcase : theorem_8_8_case_b_data W W1 W2 S T SF TF)
    (hI : ∀ M MF : Subgroup G, M ∈ section9MaximalSubgroups G →
      section16MFSubgroup M MF →
      section16TypeI M MF → typeIDefinitionData M MF)
    (hII : ∀ M MF : Subgroup G, M ∈ section9MaximalSubgroups G →
      section16MFSubgroup M MF →
      section16TypeII M MF → typeIIDefinitionData M MF)
    (hIII : ∀ M MF : Subgroup G, M ∈ section9MaximalSubgroups G →
      section16MFSubgroup M MF →
      section16TypeIII M MF → typeIIIDefinitionData M MF)
    (hIV : ∀ M MF : Subgroup G, M ∈ section9MaximalSubgroups G →
      section16MFSubgroup M MF →
      section16TypeIV M MF → typeIVDefinitionData M MF)
    (hV : ∀ M MF : Subgroup G, M ∈ section9MaximalSubgroups G →
      section16MFSubgroup M MF →
      section16TypeV M MF → typeVDefinitionData M MF) :
    theorem_8_8_source_case_b_data W W1 W2 S T SF TF := by
  classical
  rcases hcase with
    ⟨hprod, hcyc, hW1ne, hW2ne, hnorm, hSmax, hTmax, hSF, hTF,
      _hSnotI, _hTnotI, hS_eq, hT_eq, hSinf, hTinf, _hW2S, _hW1T,
      hST, hcover, hTypeII, hSType, hTType, _hCommon⟩
  refine ⟨hprod, hcyc, hW1ne, hW2ne, hnorm, hSmax, hTmax, hSF, hTF,
    ?_, ?_, ?_, ?_, hST, ?_, ?_, ?_, ?_⟩
  · simpa [sup_comm] using hS_eq
  · simpa [sup_comm] using hT_eq
  · rw [disjoint_iff]
    simpa using hSinf.le
  · rw [disjoint_iff]
    simpa using hTinf.le
  · exact hTypeII.elim (fun h => Or.inl (hII S SF hSmax hSF h))
      (fun h => Or.inr (hII T TF hTmax hTF h))
  · rcases hSType with h | h | h | h
    · exact Or.inl (hII S SF hSmax hSF h)
    · exact Or.inr <| Or.inl (hIII S SF hSmax hSF h)
    · exact Or.inr <| Or.inr <| Or.inl (hIV S SF hSmax hSF h)
    · exact Or.inr <| Or.inr <| Or.inr (hV S SF hSmax hSF h)
  · rcases hTType with h | h | h | h
    · exact Or.inl (hII T TF hTmax hTF h)
    · exact Or.inr <| Or.inl (hIII T TF hTmax hTF h)
    · exact Or.inr <| Or.inr <| Or.inl (hIV T TF hTmax hTF h)
    · exact Or.inr <| Or.inr <| Or.inr (hV T TF hTmax hTF h)
  · intro M hM
    rcases hcover M hM with hS | hT | hIcase
    · exact Or.inl hS
    · exact Or.inr <| Or.inl hT
    · rcases hIcase with ⟨MF, hMF, hTypeI⟩
      exact Or.inr <| Or.inr ⟨MF, hMF, hI M MF hM hMF hTypeI⟩

/-- A Section 12 internal direct product can be reoriented by swapping its two
factors. -/
public theorem section12InternalDirectProduct_swap
    {G : Type u} [Group G]
    {W1 W2 W : Subgroup G}
    (hprod : section12InternalDirectProduct W1 W2 W) :
    section12InternalDirectProduct W2 W1 W := by
  rcases hprod with ⟨hW1le, hW2le, hW, hdisj, hcent⟩
  refine ⟨hW2le, hW1le, ?_, hdisj.symm, ?_⟩
  · simpa [sup_comm] using hW
  · intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    exact (Subgroup.mem_centralizer_iff.mp (hcent hy) x hx).symm

/-- The source-facing PF `(8.8)(b)` case package can be reoriented by swapping
the two cyclic factors and the two distinguished maximal subgroups. -/
public theorem theorem_8_8_source_case_b_data_swap
    {G : Type u} [Group G] [Finite G]
    {W W1 W2 S T SF TF : Subgroup G}
    (hcase : theorem_8_8_source_case_b_data W W1 W2 S T SF TF) :
    theorem_8_8_source_case_b_data W W2 W1 T S TF SF := by
  rcases hcase with
    ⟨hprod, hcyc, hW1ne, hW2ne, hnorm, hSmax, hTmax, hSF, hTF,
      hSeq, hTeq, hSdisj, hTdisj, hST, hTypeII, hSType, hTType, hCover⟩
  refine ⟨section12InternalDirectProduct_swap hprod, hcyc, hW2ne, hW1ne,
    ?_, hTmax, hSmax, hTF, hSF, hTeq, hSeq, hTdisj, hSdisj, ?_, ?_, hTType,
    hSType, ?_⟩
  · intro W0 hW0ne hW0sub
    exact hnorm W0 hW0ne (by
      intro x hx
      simpa [Set.union_comm] using hW0sub hx)
  · simpa [inf_comm] using hST
  · rcases hTypeII with hSII | hTII
    · exact Or.inr hSII
    · exact Or.inl hTII
  · intro M hM
    rcases hCover M hM with hS | hT | hI
    · exact Or.inr (Or.inl hS)
    · exact Or.inl hT
    · exact Or.inr (Or.inr hI)

/-- Source-facing type fields for the fixed witnesses in the BG16-aligned
case `(8.8)(b)` package.

The literal PF `(8.8)(b)` source package records source Type II--V and Type I
fields for these same witnesses. The BG16-aligned package records the
corresponding BG predicates, so this bridge uses the established BG-to-source
type adapters from the proof of `(8.8)`. -/
public theorem theorem_8_8_source_type_fields_of_case_b_data
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    {W W1 W2 S T SF TF : Subgroup G}
    (hcase : theorem_8_8_case_b_data W W1 W2 S T SF TF) :
    (typeIIDefinitionData S SF ∨ typeIIDefinitionData T TF) ∧
      (typeIIDefinitionData S SF ∨
        typeIIIDefinitionData S SF ∨
          typeIVDefinitionData S SF ∨ typeVDefinitionData S SF) ∧
      (typeIIDefinitionData T TF ∨
        typeIIIDefinitionData T TF ∨
          typeIVDefinitionData T TF ∨ typeVDefinitionData T TF) ∧
      (∀ M : Subgroup G, M ∈ section9MaximalSubgroups G →
        (∃ g : G, M = S.conjBy g) ∨
          (∃ g : G, M = T.conjBy g) ∨
            ∃ MF : Subgroup G, section16MFSubgroup M MF ∧ typeIDefinitionData M MF) := by
  classical
  let hTypeP :
      ∀ M MF : Subgroup G,
        M ∈ section9MaximalSubgroups G →
        section16MFSubgroup M MF →
        ∀ U W1 W2 : Subgroup G,
          section16TypeCommon M MF U W1 W2 →
            typePDefinitionData M MF U W1 W2 := by
    intro M MF hM hMF U W1 W2 hCommon
    rcases section15_exists_KUData_for_maximal (G := G) (M := M) hM with
      ⟨K, KU, hKU15⟩
    have hKU : section16KUData M K KU := by
      simpa [section16KUData] using hKU15
    exact theorem_8_8_typeCommon_to_typePDefinitionData
      (G := G) hM hMF hKU hCommon
  let hI :
      ∀ M MF : Subgroup G, M ∈ section9MaximalSubgroups G →
        section16MFSubgroup M MF →
        section16TypeI M MF → typeIDefinitionData M MF := by
    intro M MF hM hMF hType
    exact theorem_8_8_typeI_to_source
      (G := G) hM hMF hType
  let hII :
      ∀ M MF : Subgroup G, M ∈ section9MaximalSubgroups G →
        section16MFSubgroup M MF →
        section16TypeII M MF → typeIIDefinitionData M MF := by
    intro M MF hM hMF hType
    exact theorem_8_8_typeII_to_source_of_canonical
      (G := G) hM hMF hType
  let hIII :
      ∀ M MF : Subgroup G, M ∈ section9MaximalSubgroups G →
        section16MFSubgroup M MF →
        section16TypeIII M MF → typeIIIDefinitionData M MF := by
    intro M MF hM hMF hType
    exact theorem_8_8_typeIII_to_source_of_typeP_adapter
      (G := G) hM hType (hTypeP M MF hM hMF)
  let hIV :
      ∀ M MF : Subgroup G, M ∈ section9MaximalSubgroups G →
        section16MFSubgroup M MF →
        section16TypeIV M MF → typeIVDefinitionData M MF := by
    intro M MF hM hMF hType
    exact theorem_8_8_typeIV_to_source_of_typeP_adapter
      (G := G) hType (hTypeP M MF hM hMF)
  let hV :
      ∀ M MF : Subgroup G, M ∈ section9MaximalSubgroups G →
        section16MFSubgroup M MF →
        section16TypeV M MF → typeVDefinitionData M MF := by
    intro M MF hM hMF hType
    exact theorem_8_8_typeV_to_source_of_typeP_adapter
      (G := G) hType (hTypeP M MF hM hMF)
  rcases theorem_8_8_case_b_data_to_source hcase hI hII hIII hIV hV with
    ⟨_hprod, _hcyc, _hW1ne, _hW2ne, _hnorm, _hSmax, _hTmax, _hSF, _hTF,
      _hSeq, _hTeq, _hSdisj, _hTdisj, _hST, hTypeII, hSType, hTType, hCover⟩
  exact ⟨hTypeII, hSType, hTType, hCover⟩


/-- Public source-facing adapter from BG16 Type I to PF8 Type I data. -/
public theorem theorem_8_8_typeI_to_source_public
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    {M MF : Subgroup G}
    (hM : M ∈ section9MaximalSubgroups G)
    (hMF : section16MFSubgroup M MF)
    (hType : section16TypeI M MF) :
    typeIDefinitionData M MF :=
  theorem_8_8_typeI_to_source (G := G) hM hMF hType

/-- Public source-facing adapter from BG16 Type II to PF8 Type II data. -/
public theorem theorem_8_8_typeII_to_source_public
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    {M MF : Subgroup G}
    (hM : M ∈ section9MaximalSubgroups G)
    (hMF : section16MFSubgroup M MF)
    (hType : section16TypeII M MF) :
    typeIIDefinitionData M MF :=
  theorem_8_8_typeII_to_source_of_canonical (G := G) hM hMF hType


/-- Public source-facing adapter from BG16 Type III to PF8 Type III data. -/
public theorem theorem_8_8_typeIII_to_source_public
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    {M MF : Subgroup G}
    (hM : M ∈ section9MaximalSubgroups G)
    (hMF : section16MFSubgroup M MF)
    (hType : section16TypeIII M MF) :
    typeIIIDefinitionData M MF := by
  classical
  let hTypeP :
      ∀ U W1 W2 : Subgroup G,
        section16TypeCommon M MF U W1 W2 →
          typePDefinitionData M MF U W1 W2 := by
    intro U W1 W2 hCommon
    rcases section15_exists_KUData_for_maximal (G := G) (M := M) hM with
      ⟨K, KU, hKU15⟩
    have hKU : section16KUData M K KU := by
      simpa [section16KUData] using hKU15
    exact theorem_8_8_typeCommon_to_typePDefinitionData
      (G := G) hM hMF hKU hCommon
  exact theorem_8_8_typeIII_to_source_of_typeP_adapter
    (G := G) hM hType hTypeP

/-- Public source-facing adapter from BG16 Type IV to PF8 Type IV data. -/
public theorem theorem_8_8_typeIV_to_source_public
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    {M MF : Subgroup G}
    (hM : M ∈ section9MaximalSubgroups G)
    (hMF : section16MFSubgroup M MF)
    (hType : section16TypeIV M MF) :
    typeIVDefinitionData M MF := by
  classical
  let hTypeP :
      ∀ U W1 W2 : Subgroup G,
        section16TypeCommon M MF U W1 W2 →
          typePDefinitionData M MF U W1 W2 := by
    intro U W1 W2 hCommon
    rcases section15_exists_KUData_for_maximal (G := G) (M := M) hM with
      ⟨K, KU, hKU15⟩
    have hKU : section16KUData M K KU := by
      simpa [section16KUData] using hKU15
    exact theorem_8_8_typeCommon_to_typePDefinitionData
      (G := G) hM hMF hKU hCommon
  exact theorem_8_8_typeIV_to_source_of_typeP_adapter
    (G := G) hType hTypeP

/-- Public source-facing adapter from BG16 Type V to PF8 Type V data. -/
public theorem theorem_8_8_typeV_to_source_public
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    {M MF : Subgroup G}
    (hM : M ∈ section9MaximalSubgroups G)
    (hMF : section16MFSubgroup M MF)
    (hType : section16TypeV M MF) :
    typeVDefinitionData M MF := by
  classical
  let hTypeP :
      ∀ U W1 W2 : Subgroup G,
        section16TypeCommon M MF U W1 W2 →
          typePDefinitionData M MF U W1 W2 := by
    intro U W1 W2 hCommon
    rcases section15_exists_KUData_for_maximal (G := G) (M := M) hM with
      ⟨K, KU, hKU15⟩
    have hKU : section16KUData M K KU := by
      simpa [section16KUData] using hKU15
    exact theorem_8_8_typeCommon_to_typePDefinitionData
      (G := G) hM hMF hKU hCommon
  exact theorem_8_8_typeV_to_source_of_typeP_adapter
    (G := G) hType hTypeP

/-- A nontrivial Type-P kernel and its distinguished cyclic complement form
the Frobenius subgroup used in the quotient arguments of PF Sections 10 and
13. -/
public theorem typePDefinitionData_frobeniusJoinWithKernel
    {G : Type u} [Group G] [Finite G]
    {M MF U W1 W2 : Subgroup G}
    (hP : typePDefinitionData M MF U W1 W2)
    (hUne : U ≠ ⊥) :
    section12FrobeniusJoinWithKernel U W1 := by
  classical
  rcases hP with
    ⟨_hMF, _hW1cyc, hW1ne, _hW1Hall, hMcomp, _hUleD, _hUnil, hW1norm,
      hDercomp, _hMFnotcyc, _hsecond, _hfit, _hfitDer, hW2leInf, _hW2cyc,
      _hW2ne, hcentralizer, _hnorm⟩
  rcases hDercomp with ⟨_hMFleD, hUleD, _hD_eq, hMFUdisj⟩
  let S : Subgroup G := U ⊔ W1
  have hDdisjW1 : Disjoint (ambientDerivedSubgroup M) W1 := hMcomp.2.2.2
  have hUWdisj : Disjoint U W1 := by
    rw [disjoint_iff] at hDdisjW1 ⊢
    apply le_antisymm
    · exact (inf_le_inf_right W1 hUleD).trans (le_of_eq hDdisjW1)
    · exact bot_le
  have hW1leNormU : W1 ≤ Subgroup.normalizer (U : Set G) := by
    intro x hx
    exact (mem_subgroupNormalizerIn.mp (hW1norm hx)).1
  have hUnormalS : (U.subgroupOf S).Normal := by
    apply (Subgroup.normal_subgroupOf_iff_le_normalizer
      (H := U) (K := S) (by simp [S])).2
    simpa [S] using sup_le Subgroup.le_normalizer hW1leNormU
  have hUWdisjSub : Disjoint (U.subgroupOf S) (W1.subgroupOf S) := by
    rw [disjoint_iff] at hUWdisj ⊢
    apply le_antisymm
    · intro x hx
      have hxAmb : (x : G) ∈ U ⊓ W1 := by
        exact ⟨by simpa [Subgroup.mem_subgroupOf, S] using hx.1,
          by simpa [Subgroup.mem_subgroupOf, S] using hx.2⟩
      have hxBot : (x : G) ∈ (⊥ : Subgroup G) := by
        simpa [hUWdisj] using hxAmb
      ext
      simpa using hxBot
    · exact bot_le
  have hUWsupTop :
      U.subgroupOf S ⊔ W1.subgroupOf S = ⊤ := by
    rw [← Subgroup.subgroupOf_sup (A := U) (A' := W1) (B := S)
      (by simp [S]) (by simp [S])]
    exact Subgroup.subgroupOf_eq_top.2 (by simp [S])
  have hUWcompSub : (U.subgroupOf S).IsComplement' (W1.subgroupOf S) := by
    letI : (U.subgroupOf S).Normal := hUnormalS
    exact isComplement'_of_disjoint_sup_eq_top_of_normal
      (U.subgroupOf S) (W1.subgroupOf S) hUWdisjSub hUWsupTop
  have hUsub_ne : U.subgroupOf S ≠ ⊥ := by
    intro hbot
    apply hUne
    have hcard :
        Nat.card (U.subgroupOf S) = 1 :=
      (Subgroup.eq_bot_iff_card (H := U.subgroupOf S)).1 hbot
    have hcardU : Nat.card U = 1 := by
      rw [natCard_subgroupOf_eq U S (by simp [S])] at hcard
      exact hcard
    exact (Subgroup.eq_bot_iff_card (H := U)).2 hcardU
  have hW1sub_ne : W1.subgroupOf S ≠ ⊥ := by
    intro hbot
    apply hW1ne
    have hcard :
        Nat.card (W1.subgroupOf S) = 1 :=
      (Subgroup.eq_bot_iff_card (H := W1.subgroupOf S)).1 hbot
    have hcardW1 : Nat.card W1 = 1 := by
      rw [natCard_subgroupOf_eq W1 S (by simp [S])] at hcard
      exact hcard
    exact (Subgroup.eq_bot_iff_card (H := W1)).2 hcardW1
  have hcent :
      ∀ x : W1.subgroupOf S, x ≠ 1 →
        elementCentralizerIn (U.subgroupOf S) (x : S) = ⊥ := by
    intro x hxne
    rw [Subgroup.eq_bot_iff_forall]
    intro y hy
    have hyParts :
        y ∈ U.subgroupOf S ∧
          y ∈ Subgroup.centralizer ({(x : S)} : Set S) := by
      simpa [elementCentralizerIn] using hy
    let xG : G := ((x : S) : G)
    have hxW1 : xG ∈ W1 := by
      simpa [xG] using
        (Subgroup.mem_subgroupOf.mp x.property : ((x : S) : G) ∈ W1)
    have hxGne : xG ≠ 1 := by
      intro hxG
      apply hxne
      ext
      exact hxG
    have hyU : (y : G) ∈ U := by
      simpa [Subgroup.mem_subgroupOf, S] using hyParts.1
    have hyDer : (y : G) ∈ ambientDerivedSubgroup M := hUleD hyU
    have hcentx : elementCentralizerIn (ambientDerivedSubgroup M) xG = W2 :=
      hcentralizer xG hxW1 hxGne
    have hyCommS : (y : S) * (x : S) = (x : S) * (y : S) :=
      Subgroup.mem_centralizer_singleton_iff.mp hyParts.2
    have hyCommG : (y : G) * xG = xG * (y : G) := by
      simpa [xG] using congrArg Subtype.val hyCommS
    have hyCentX : (y : G) ∈ Subgroup.centralizer ({xG} : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro z hz
      have hz_eq : z = xG := by simpa using hz
      subst z
      exact hyCommG.symm
    have hyElem :
        (y : G) ∈ elementCentralizerIn (ambientDerivedSubgroup M) xG := by
      simpa [elementCentralizerIn] using And.intro hyDer hyCentX
    have hyW2 : (y : G) ∈ W2 := by
      simpa [hcentx] using hyElem
    have hyMF : (y : G) ∈ MF := (hW2leInf hyW2).1
    have hyBot : (y : G) ∈ (⊥ : Subgroup G) :=
      (Subgroup.disjoint_def.mp hMFUdisj) hyMF hyU
    ext
    simpa using hyBot
  exact (lemma_3_1 (G := S) (K := U.subgroupOf S) (R := W1.subgroupOf S)
    hUsub_ne hW1sub_ne hUnormalS hUWcompSub).2 hcent


end CFSG.Section8
