module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PFsection1.PFsection1_7
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PFsection4.PFsection4_3
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PFsection4.PFsection4_4
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PFsection4.PFsection4_5_to_10
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PFsection5.PFsection5_3
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PFsection8.PFsection8_5_b
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PFsection9.PFsection9_3
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PFsection9.PFsection9_7
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PFsection9.Basic

namespace CFSG
end CFSG
open CFSG

noncomputable section

open scoped IsMulCommutative commutatorElement

namespace CFSG.Section9

universe u v w

@[expose] public noncomputable def reducibleCharacterFilter_sec9

    {G : Type u} [Group G] [Finite G]
    (M : Subgroup G)
    (S : Finset (Section1.ClassFunction M)) : Finset (Section1.ClassFunction M) := by
  classical
  exact S.filter fun χ => ¬ Section1.IsIrreducibleCharacterOnGroup χ

@[expose] public noncomputable def linearHCCharacterFilter_sec9
    {G : Type u} [Group G] [Finite G]
    (M MF C : Subgroup G)
    (S : Finset (Section1.ClassFunction M)) : Finset (Section1.ClassFunction M) := by
  classical
  exact S.filter fun χ => inducedFromLinearCharacterOfHC M MF C χ


@[expose] public noncomputable def quotientSubgroupOfMapToAmbientQuotientOfInf_sec9
    {G : Type u} [Group G] [Finite G]
    {M MF H0 K : Subgroup G}
    (hMF_M : MF ≤ M)
    [hNMF : (H0.subgroupOf MF).Normal]
    [hKM : (K.subgroupOf M).Normal]
    (hH0K : H0 ≤ K) :
    (MF ⧸ H0.subgroupOf MF) →* (M ⧸ K.subgroupOf M) := by
  refine QuotientGroup.lift (H0.subgroupOf MF)
    ((QuotientGroup.mk' (K.subgroupOf M)).comp (Subgroup.inclusion hMF_M)) ?_
  intro x hx
  change QuotientGroup.mk' (K.subgroupOf M) (Subgroup.inclusion hMF_M x) = 1
  apply (QuotientGroup.eq_one_iff (N := K.subgroupOf M)
    (x := Subgroup.inclusion hMF_M x)).2
  exact hH0K (by simpa [Subgroup.mem_subgroupOf] using hx)

public theorem quotientSubgroupOfMapToAmbientQuotientOfInf_injective_sec9
    {G : Type u} [Group G] [Finite G]
    {M MF H0 K : Subgroup G}
    (hMF_M : MF ≤ M)
    [hNMF : (H0.subgroupOf MF).Normal]
    [hKM : (K.subgroupOf M).Normal]
    (hH0K : H0 ≤ K)
    (hKinf : K ⊓ MF = H0) :
    Function.Injective
      (quotientSubgroupOfMapToAmbientQuotientOfInf_sec9 (M := M) (MF := MF)
        (H0 := H0) (K := K) hMF_M hH0K) := by
  let f := quotientSubgroupOfMapToAmbientQuotientOfInf_sec9 (M := M) (MF := MF)
    (H0 := H0) (K := K) hMF_M hH0K
  rw [← (MonoidHom.ker_eq_bot_iff f)]
  ext x
  constructor
  · intro hx
    rcases QuotientGroup.mk'_surjective (H0.subgroupOf MF) x with ⟨y, rfl⟩
    have hfy : f (QuotientGroup.mk' (H0.subgroupOf MF) y) = 1 := hx
    have hqK :
        QuotientGroup.mk' (K.subgroupOf M) (Subgroup.inclusion hMF_M y) = 1 := by
      simpa [f, quotientSubgroupOfMapToAmbientQuotientOfInf_sec9] using hfy
    have hyKM : Subgroup.inclusion hMF_M y ∈ K.subgroupOf M :=
      (QuotientGroup.eq_one_iff (N := K.subgroupOf M)
        (x := Subgroup.inclusion hMF_M y)).1 hqK
    have hyK : (y : G) ∈ K := by
      simpa [Subgroup.mem_subgroupOf] using hyKM
    have hyInf : (y : G) ∈ K ⊓ MF := ⟨hyK, y.property⟩
    have hyH0 : (y : G) ∈ H0 := by
      simpa [hKinf] using hyInf
    have hyH0MF : y ∈ H0.subgroupOf MF := by
      simpa [Subgroup.mem_subgroupOf] using hyH0
    exact (QuotientGroup.eq_one_iff (N := H0.subgroupOf MF) (x := y)).2 hyH0MF
  · intro hx
    have hx1 : x = 1 := by simpa using hx
    simp [hx1]

public theorem quotientSubgroupOfMapToAmbientQuotientOfInf_map_subgroup_eq_sec9
    {G : Type u} [Group G] [Finite G]
    {M MF H0 K L : Subgroup G}
    (hL_MF : L ≤ MF) (hMF_M : MF ≤ M)
    [hNMF : (H0.subgroupOf MF).Normal]
    [hKM : (K.subgroupOf M).Normal]
    (hH0K : H0 ≤ K) :
    let f := quotientSubgroupOfMapToAmbientQuotientOfInf_sec9 (M := M) (MF := MF)
      (H0 := H0) (K := K) hMF_M hH0K
    ((L.subgroupOf MF).map (QuotientGroup.mk' (H0.subgroupOf MF))).map f =
      (L.subgroupOf M).map (QuotientGroup.mk' (K.subgroupOf M)) := by
  intro f
  ext x
  constructor
  · intro hx
    rcases hx with ⟨ybar, hybar, rfl⟩
    rcases hybar with ⟨y, hyL, rfl⟩
    refine ⟨Subgroup.inclusion hMF_M y, ?_, ?_⟩
    · simpa [Subgroup.mem_subgroupOf] using hyL
    · simp [f, quotientSubgroupOfMapToAmbientQuotientOfInf_sec9]
  · intro hx
    rcases hx with ⟨y, hyL, rfl⟩
    let yMF : MF := ⟨(y : G),
      hL_MF (by simpa [Subgroup.mem_subgroupOf] using hyL)⟩
    have hyIncl : Subgroup.inclusion hMF_M yMF = y := by
      ext
      rfl
    refine ⟨QuotientGroup.mk' (H0.subgroupOf MF) yMF, ?_, ?_⟩
    · exact ⟨yMF, by simpa [yMF, Subgroup.mem_subgroupOf] using hyL, rfl⟩
    · simp [f, quotientSubgroupOfMapToAmbientQuotientOfInf_sec9, hyIncl]

public theorem quotientSubgroupOfMapToAmbientQuotientOfInf_map_subgroup_card_eq_sec9
    {G : Type u} [Group G] [Finite G]
    {M MF H0 K L : Subgroup G}
    (hL_MF : L ≤ MF) (hMF_M : MF ≤ M)
    [hNMF : (H0.subgroupOf MF).Normal]
    [hKM : (K.subgroupOf M).Normal]
    (hH0K : H0 ≤ K)
    (hKinf : K ⊓ MF = H0) :
    Nat.card ((L.subgroupOf M).map (QuotientGroup.mk' (K.subgroupOf M))) =
      Nat.card ((L.subgroupOf MF).map (QuotientGroup.mk' (H0.subgroupOf MF))) := by
  let f := quotientSubgroupOfMapToAmbientQuotientOfInf_sec9 (M := M) (MF := MF)
    (H0 := H0) (K := K) hMF_M hH0K
  have hf : Function.Injective f :=
    quotientSubgroupOfMapToAmbientQuotientOfInf_injective_sec9
      (M := M) (MF := MF) (H0 := H0) (K := K) hMF_M hH0K hKinf
  have hmap :
      ((L.subgroupOf MF).map (QuotientGroup.mk' (H0.subgroupOf MF))).map f =
        (L.subgroupOf M).map (QuotientGroup.mk' (K.subgroupOf M)) :=
    quotientSubgroupOfMapToAmbientQuotientOfInf_map_subgroup_eq_sec9
      (M := M) (MF := MF) (H0 := H0) (K := K) (L := L)
      hL_MF hMF_M hH0K
  calc
    Nat.card ((L.subgroupOf M).map (QuotientGroup.mk' (K.subgroupOf M))) =
        Nat.card (((L.subgroupOf MF).map (QuotientGroup.mk' (H0.subgroupOf MF))).map f) := by
          rw [hmap]
    _ = Nat.card ((L.subgroupOf MF).map (QuotientGroup.mk' (H0.subgroupOf MF))) :=
        Subgroup.card_map_of_injective hf

public theorem theorem_9_nb_redM_W2_map_mk_H0_MF_card_eq_of_source_sec9
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    {M MF U W1 W2 H0 : Subgroup G}
    {p q : ℕ}
    [hH0normalMF : (H0.subgroupOf MF).Normal] :
    hypothesis_9_2_statement M MF U W1 W2 q →
      (∃ hp : Nat.Primes,
        hp.val = p ∧
          hoReductionData M MF U W2 H0 hp ∧
            quotientChiefFactorData_9_6 M MF H0 W1 hp) →
        Nat.card ((W2.subgroupOf MF).map (QuotientGroup.mk' (H0.subgroupOf MF))) = p := by
  intro h92 hpData
  rcases hpData with ⟨hp, hp_eq, hho, h96⟩
  rcases hho with
    ⟨_hH0_le_MF, hMF_le_M, hH0_normal_M, _hH0_normal_MF, _hH0lt,
      _helem, _htypeIIIIV⟩
  rcases h96 with
    ⟨_hH0_le_MF96, _hMF_le_M96, _hnormal96, _hchief, hWbar, _hcard⟩
  rcases h92.mf.1 with ⟨hMF_le_M92, hMF_normal_M, _hMFnil, _hMFhall⟩
  rcases h92.typePDefinitionData with
    ⟨_hMFsource, _hW1cyc, _hW1ne, ⟨hW1_le_M, _hW1hall⟩,
      _hcompMW1, _hUleD, _hUnil, _hW1normU, _hcompDU, _hMFnotcyc,
      _hsecond, _hfitEq, _hfitLeD, _hW2le, _hW2cyc, _hW2ne,
      _hcentW1, _hnormX⟩
  have hM_norm_MF : M ≤ Subgroup.normalizer (MF : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hMF_le_M92).1 hMF_normal_M
  have hW1_norm_MF : W1 ≤ Subgroup.normalizer (MF : Set G) :=
    hW1_le_M.trans hM_norm_MF
  letI : Subgroup.Normalizes W1 MF := ⟨hW1_norm_MF⟩
  have hH0_inv_W1 : IsInvariant W1 MF (H0.subgroupOf MF) :=
    subgroupOf_MF_isInvariant_of_subgroupOf_M_normal_sec9 M MF W1 H0
      hMF_le_M hW1_le_M hH0_normal_M hW1_norm_MF
  rcases hWbar with ⟨_hnormalSrc, hsourceCard⟩
  have hsourceCard' :
      Nat.card {x : MF ⧸ H0.subgroupOf MF //
        ∀ h : MF, QuotientGroup.mk' (H0.subgroupOf MF) h = x →
          ∀ w : G, w ∈ W1 → ⁅w, (h : G)⁆ ∈ H0} = p := by
    simpa [hp_eq] using hsourceCard
  have hsource_eq_fixed :
      Nat.card {x : MF ⧸ H0.subgroupOf MF //
        ∀ h : MF, QuotientGroup.mk' (H0.subgroupOf MF) h = x →
          ∀ w : G, w ∈ W1 → ⁅w, (h : G)⁆ ∈ H0} =
        Nat.card (fixedPointSubgroup W1 (MF ⧸ H0.subgroupOf MF)) := by
    simpa using
      quotient_W1_fixedPointSubgroup_card_eq_barW2_subtype_sec9
        MF W1 H0 hH0_inv_W1 hH0normalMF
  have hfixed_card :
      Nat.card (fixedPointSubgroup W1 (MF ⧸ H0.subgroupOf MF)) = p :=
    hsource_eq_fixed.symm.trans hsourceCard'
  have hfixed_eq :
      fixedPointSubgroup W1 (MF ⧸ H0.subgroupOf MF) =
        (W2.subgroupOf MF).map (QuotientGroup.mk' (H0.subgroupOf MF)) :=
    quotient_W1_fixedPointSubgroup_eq_W2_map_of_hypothesis_9_2_sec9
      M MF U W1 W2 H0 q h92 hH0normalMF hH0_inv_W1
  simpa [hfixed_eq] using hfixed_card

public theorem theorem_9_nb_redM_W2_map_mk_K_card_eq_source_core_sec9
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    (M MF U W1 W2 H0 K : Subgroup G)
    (p q : ℕ) :
    hypothesis_9_2_statement M MF U W1 W2 q →
      H0 ≤ MF →
        Nat.Prime p →
          (∃ hp : Nat.Primes,
            hp.val = p ∧
              hoReductionData M MF U W2 H0 hp ∧
                quotientChiefFactorData_9_6 M MF H0 W1 hp) →
            (hKnormal : (K.subgroupOf M).Normal) →
              K ≤ ambientDerivedSubgroup M →
                K ⊓ MF = H0 →
                  letI : (K.subgroupOf M).Normal := hKnormal
                  Nat.card ((W2.subgroupOf M).map (QuotientGroup.mk' (K.subgroupOf M))) = p := by
  intro h92 _hH0MF _hpprime hpData hKnormal _hKD hKinf
  letI : (K.subgroupOf M).Normal := hKnormal
  have hpDataFull := hpData
  rcases hpData with ⟨_hp, _hp_eq, hho, _h96⟩
  rcases hho with
    ⟨_hH0_le_MF, hMF_le_M, _hH0_normal_M, hH0normalMF, _hH0lt,
      _helem, _htypeIIIIV⟩
  letI : (H0.subgroupOf MF).Normal := hH0normalMF
  have hW2MF : W2 ≤ MF := by
    rcases h92.typePDefinitionData with
      ⟨_hMFsource, _hW1cyc, _hW1ne, _hW1hall, _hcompMW1, _hUleD,
        _hUnil, _hW1normU, _hcompDU, _hMFnotcyc, _hSecondLe, _hFittingEq,
        _hFittingLeD, hW2le, _hW2cyc, _hW2ne, _hCent, _hHatW⟩
    exact hW2le.trans inf_le_left
  have hH0K : H0 ≤ K := by
    intro x hx
    have hxInf : x ∈ K ⊓ MF := by
      simpa [hKinf] using hx
    exact hxInf.1
  have hcard_eq :
      Nat.card ((W2.subgroupOf M).map (QuotientGroup.mk' (K.subgroupOf M))) =
        Nat.card ((W2.subgroupOf MF).map (QuotientGroup.mk' (H0.subgroupOf MF))) :=
    quotientSubgroupOfMapToAmbientQuotientOfInf_map_subgroup_card_eq_sec9
      (M := M) (MF := MF) (H0 := H0) (K := K) (L := W2)
      hW2MF hMF_le_M hH0K hKinf
  have hcard_H0 :
      Nat.card ((W2.subgroupOf MF).map (QuotientGroup.mk' (H0.subgroupOf MF))) = p :=
    theorem_9_nb_redM_W2_map_mk_H0_MF_card_eq_of_source_sec9
      (M := M) (MF := MF) (U := U) (W1 := W1) (W2 := W2) (H0 := H0)
      (p := p) (q := q) h92 hpDataFull
  exact hcard_eq.trans hcard_H0

public theorem theorem_9_nb_redM_W2_map_mk_K_isCyclic_source_core_sec9
    {G : Type u} [Group G] [Finite G]
    (M MF U W1 W2 _H0 K : Subgroup G)
    (q : ℕ) :
    hypothesis_9_2_statement M MF U W1 W2 q →
      (hKnormal : (K.subgroupOf M).Normal) →
        letI : (K.subgroupOf M).Normal := hKnormal
        let qM : M →* M ⧸ K.subgroupOf M :=
          QuotientGroup.mk' (K.subgroupOf M)
        IsCyclic ((W2.subgroupOf M).map qM) := by
  intro h92 hKnormal
  letI : (K.subgroupOf M).Normal := hKnormal
  let qM : M →* M ⧸ K.subgroupOf M := QuotientGroup.mk' (K.subgroupOf M)
  change IsCyclic ((W2.subgroupOf M).map qM)
  have hW2cyc : IsCyclic W2 := by
    rcases h92.typePDefinitionData with
      ⟨_hMFsource, _hW1cyc, _hW1ne, _hW1hall, _hcompMW1, _hUleD,
        _hUnil, _hW1normU, _hcompDU, _hMFnotcyc, _hSecondLe, _hFittingEq,
        _hFittingLeD, _hW2le, hW2cyc, _hW2ne, _hCent, _hHatW⟩
    exact hW2cyc
  have hW2M : W2 ≤ M :=
    W2_le_M_of_hypothesis_9_2_sec9 M MF U W1 W2 q h92
  have hW2sub_cyclic : IsCyclic (W2.subgroupOf M) :=
    (Subgroup.subgroupOfEquivOfLe (H := W2) (K := M) hW2M).isCyclic.mpr hW2cyc
  letI : IsCyclic (W2.subgroupOf M) := hW2sub_cyclic
  exact isCyclic_of_surjective
    (f := qM.subgroupMap (W2.subgroupOf M))
    (MonoidHom.subgroupMap_surjective qM (W2.subgroupOf M))

public theorem natCard_ne_one_of_eq_prime_sec9
    {α : Type u} [Finite α] {p : ℕ}
    (hp : Nat.Prime p) :
    Nat.card α = p → Nat.card α ≠ 1 := by
  intro hcard hone
  exact hp.ne_one (by
    rw [← hcard]
    exact hone)

public theorem theorem_9_nb_redM_W2_le_ambientDerived_sec9
    {G : Type u} [Group G] [Finite G]
    (M MF U W1 W2 : Subgroup G)
    (q : ℕ) :
    hypothesis_9_2_statement M MF U W1 W2 q →
      W2 ≤ ambientDerivedSubgroup M := by
  intro h92
  rcases h92.typePDefinitionData with
    ⟨_hMFsource, _hW1cyc, _hW1ne, _hW1hall, _hcompMW1, _hUleD,
      _hUnil, _hW1normU, _hcompDU, _hMFnotCyc, _hSecondLe, _hFittingEq,
      _hFittingLeD, hW2le, _hW2cyc, _hW2ne, _hCent, _hHatW⟩
  intro x hx
  have hSecond_le_D :
      section16SecondDerivedSubgroup M ≤ ambientDerivedSubgroup M := by
    simpa [section16SecondDerivedSubgroup] using
      (section12_ambientDerivedSubgroup_le (G := G)
        (E := ambientDerivedSubgroup M))
  exact hSecond_le_D (hW2le hx).2

public theorem theorem_9_nb_redM_W1_inf_W2_eq_bot_sec9
    {G : Type u} [Group G] [Finite G]
    (M MF U W1 W2 : Subgroup G)
    (q : ℕ) :
    hypothesis_9_2_statement M MF U W1 W2 q →
      W1 ⊓ W2 = ⊥ := by
  intro h92
  rcases h92.typePDefinitionData with
    ⟨_hMFsource, _hW1cyc, _hW1ne, _hW1hall, hcompMW1, _hUleD,
      _hUnil, _hW1normU, _hcompDU, _hMFnotCyc, _hSecondLe, _hFittingEq,
      _hFittingLeD, _hW2le, _hW2cyc, _hW2ne, _hCent, _hHatW⟩
  apply le_antisymm
  · intro x hx
    have hxD : x ∈ ambientDerivedSubgroup M :=
      theorem_9_nb_redM_W2_le_ambientDerived_sec9 M MF U W1 W2 q h92 hx.2
    have hxInf : x ∈ ambientDerivedSubgroup M ⊓ W1 := ⟨hxD, hx.1⟩
    simpa using hcompMW1.2.2.2.le_bot hxInf
  · exact bot_le

public theorem theorem_9_nb_redM_W2_le_centralizer_W1_sec9
    {G : Type u} [Group G] [Finite G]
    (M MF U W1 W2 : Subgroup G)
    (q : ℕ) :
    hypothesis_9_2_statement M MF U W1 W2 q →
      W2 ≤ Subgroup.centralizer (W1 : Set G) := by
  intro h92
  rcases h92.typePDefinitionData with
    ⟨_hMFsource, _hW1cyc, _hW1ne, _hW1hall, _hcompMW1, _hUleD,
      _hUnil, _hW1normU, _hcompDU, _hMFnotCyc, _hSecondLe, _hFittingEq,
      _hFittingLeD, _hW2le, _hW2cyc, _hW2ne, hCent, _hHatW⟩
  intro y hy
  rw [Subgroup.mem_centralizer_iff]
  intro x hx
  by_cases hx1 : x = 1
  · simp [hx1]
  · have hyCent : y ∈ elementCentralizerIn (ambientDerivedSubgroup M) x := by
      simpa [hCent x hx hx1] using hy
    exact (Subgroup.mem_centralizer_singleton_iff.mp hyCent.2).symm

public theorem theorem_9_nb_redM_W_internalDirectProduct_sec9
    {G : Type u} [Group G] [Finite G]
    (M MF U W1 W2 : Subgroup G)
    (q : ℕ) :
    hypothesis_9_2_statement M MF U W1 W2 q →
      Section2.IsInternalDirectProduct
        ((W1 ⊔ W2).subgroupOf M) (W1.subgroupOf M) (W2.subgroupOf M) := by
  classical
  intro h92
  have hW2centW1 : W2 ≤ Subgroup.centralizer (W1 : Set G) :=
    theorem_9_nb_redM_W2_le_centralizer_W1_sec9 M MF U W1 W2 q h92
  have hW1infW2 : W1 ⊓ W2 = ⊥ :=
    theorem_9_nb_redM_W1_inf_W2_eq_bot_sec9 M MF U W1 W2 q h92
  rcases h92.typePDefinitionData with
    ⟨_hMFsource, _hW1cyc, _hW1ne, hW1hall, _hcompMW1, _hUleD,
      _hUnil, _hW1normU, _hcompDU, _hMFnotCyc, _hSecondLe, _hFittingEq,
      _hFittingLeD, _hW2le, _hW2cyc, _hW2ne, _hCent, _hHatW⟩
  rcases hW1hall with ⟨hW1M, _hW1HallSub⟩
  have hW2M : W2 ≤ M :=
    W2_le_M_of_hypothesis_9_2_sec9 M MF U W1 W2 q h92
  have hW1_norm_W2 : W1 ≤ Subgroup.normalizer (W2 : Set G) := by
    intro a ha
    rw [Subgroup.mem_normalizer_iff]
    intro y
    constructor
    · intro hy
      have hcomm : a * y = y * a :=
        Subgroup.mem_centralizer_iff.mp (hW2centW1 hy) a ha
      have hconj : a * y * a⁻¹ = y := by
        calc
          a * y * a⁻¹ = y * a * a⁻¹ := by rw [hcomm]
          _ = y := by simp [mul_assoc]
      simpa [hconj] using hy
    · intro hy
      let y' : G := a * y * a⁻¹
      have hy'W2 : y' ∈ W2 := by simpa [y'] using hy
      have hcomm' : a * y' = y' * a :=
        Subgroup.mem_centralizer_iff.mp (hW2centW1 hy'W2) a ha
      have hconj : a⁻¹ * y' * a = y' := by
        have h := congrArg (fun t : G => a⁻¹ * t) hcomm'
        simpa [mul_assoc] using h.symm
      have hy_eq : y = y' := by
        calc
          y = a⁻¹ * y' * a := by simp [y', mul_assoc]
          _ = y' := hconj
      simpa [hy_eq] using hy'W2
  let W : Subgroup G := W1 ⊔ W2
  let W1W : Subgroup W := W1.subgroupOf W
  let W2W : Subgroup W := W2.subgroupOf W
  haveI : W2W.Normal := by
    simpa [W, W2W] using
      (Subgroup.normal_subgroupOf_sup_of_le_normalizer
        (H := W1) (N := W2) hW1_norm_W2)
  have hW1W_W2W_top : W1W ⊔ W2W = ⊤ := by
    calc
      W1W ⊔ W2W = W.subgroupOf W := by
        symm
        exact Subgroup.subgroupOf_sup
          (A := W1) (A' := W2) (B := W)
          (by simp [W])
          (by simp [W])
      _ = ⊤ := by simp
  refine
    { left_le := ?_
      right_le := ?_
      commute := ?_
      inf_eq_bot := ?_
      mul_surjective := ?_ }
  · intro x hx
    have hxW1 : ((x : M) : G) ∈ W1 := by
      simpa [Subgroup.mem_subgroupOf] using hx
    simpa [Subgroup.mem_subgroupOf] using
      ((le_sup_left : W1 ≤ W1 ⊔ W2) hxW1)
  · intro x hx
    have hxW2 : ((x : M) : G) ∈ W2 := by
      simpa [Subgroup.mem_subgroupOf] using hx
    simpa [Subgroup.mem_subgroupOf] using
      ((le_sup_right : W2 ≤ W1 ⊔ W2) hxW2)
  · intro h hh k hk
    have hhW1 : ((h : M) : G) ∈ W1 := by
      simpa [Subgroup.mem_subgroupOf] using hh
    have hkW2 : ((k : M) : G) ∈ W2 := by
      simpa [Subgroup.mem_subgroupOf] using hk
    apply Subtype.ext
    exact Subgroup.mem_centralizer_iff.mp (hW2centW1 hkW2) ((h : M) : G) hhW1
  · apply le_antisymm
    · intro x hx
      have hxAmb : ((x : M) : G) ∈ W1 ⊓ W2 := by
        constructor
        · simpa [Subgroup.mem_subgroupOf] using hx.1
        · simpa [Subgroup.mem_subgroupOf] using hx.2
      have hxBotG : ((x : M) : G) ∈ (⊥ : Subgroup G) := by
        simpa [hW1infW2] using hxAmb
      ext
      simpa using hxBotG
    · exact bot_le
  · intro c hc
    let cW : W := ⟨((c : M) : G), by simpa [W, Subgroup.mem_subgroupOf] using hc⟩
    have hcSup : cW ∈ W1W ⊔ W2W := by
      rw [hW1W_W2W_top]
      simp
    rcases (Subgroup.mem_sup_of_normal_right (s := W1W) (t := W2W) (x := cW)).1
        hcSup with
      ⟨aW, haW, bW, hbW, hab⟩
    have haW1 : (aW : G) ∈ W1 := by
      simpa [W1W, Subgroup.mem_subgroupOf] using haW
    have hbW2 : (bW : G) ∈ W2 := by
      simpa [W2W, Subgroup.mem_subgroupOf] using hbW
    let aM : M := ⟨(aW : G), hW1M haW1⟩
    let bM : M := ⟨(bW : G), hW2M hbW2⟩
    refine ⟨aM, ?_, bM, ?_, ?_⟩
    · simpa [aM, Subgroup.mem_subgroupOf] using haW1
    · simpa [bM, Subgroup.mem_subgroupOf] using hbW2
    · apply Subtype.ext
      have hval := congrArg (fun z : W => (z : G)) hab
      simpa [aM, bM, cW] using hval.symm

public theorem theorem_9_nb_redM_M_mod_K_quotient_semidirect_sec9
    {G : Type u} [Group G] [Finite G]
    (M MF U W1 W2 K : Subgroup G)
    (q : ℕ) :
    hypothesis_9_2_statement M MF U W1 W2 q →
      (hKnormal : (K.subgroupOf M).Normal) →
        K ≤ ambientDerivedSubgroup M →
          letI : (K.subgroupOf M).Normal := hKnormal
          let qM : M →* M ⧸ K.subgroupOf M :=
            QuotientGroup.mk' (K.subgroupOf M)
          Section2.IsInternalSemidirectProduct
            (⊤ : Subgroup (M ⧸ K.subgroupOf M))
            (((ambientDerivedSubgroup M).subgroupOf M).map qM)
            ((W1.subgroupOf M).map qM) := by
  intro h92 hKnormal hKD
  letI : (K.subgroupOf M).Normal := hKnormal
  let qM : M →* M ⧸ K.subgroupOf M := QuotientGroup.mk' (K.subgroupOf M)
  change Section2.IsInternalSemidirectProduct
    (⊤ : Subgroup (M ⧸ K.subgroupOf M))
    (((ambientDerivedSubgroup M).subgroupOf M).map qM)
    ((W1.subgroupOf M).map qM)
  have hNleD : K.subgroupOf M ≤ (ambientDerivedSubgroup M).subgroupOf M := by
    intro x hx
    have hxK : (x : G) ∈ K := by
      simpa [Subgroup.mem_subgroupOf] using hx
    exact hKD hxK
  have hcomp :
      ((ambientDerivedSubgroup M).subgroupOf M).IsComplement' (W1.subgroupOf M) :=
    ambientDerived_W1_isComplement'_subgroupOf_M_of_hypothesis_9_2_sec9
      M MF U W1 W2 q h92
  have hcompQuot :
      (((ambientDerivedSubgroup M).subgroupOf M).map qM).IsComplement'
        ((W1.subgroupOf M).map qM) :=
    isComplement'_map_mk'_of_le_isComplement'
      ((ambientDerivedSubgroup M).subgroupOf M) (W1.subgroupOf M)
      (K.subgroupOf M) hNleD hcomp
  have hDnormal : ((ambientDerivedSubgroup M).subgroupOf M).Normal := by
    simpa using (section12_normalIn_ambientDerivedSubgroup (G := G) (E := M)).2
  letI : ((ambientDerivedSubgroup M).subgroupOf M).Normal := hDnormal
  have hDmapNormal :
      (((ambientDerivedSubgroup M).subgroupOf M).map qM).Normal :=
    hDnormal.map qM (QuotientGroup.mk'_surjective (K.subgroupOf M))
  letI : (((ambientDerivedSubgroup M).subgroupOf M).map qM).Normal := hDmapNormal
  exact internalSemidirectProduct_top_of_normal_isComplement'_sec9 hcompQuot

public theorem theorem_9_nb_redM_W1_map_mk_K_card_eq_sec9
    {G : Type u} [Group G] [Finite G]
    (M MF U W1 W2 K : Subgroup G)
    (q : ℕ) :
    hypothesis_9_2_statement M MF U W1 W2 q →
      (hKnormal : (K.subgroupOf M).Normal) →
        K ≤ ambientDerivedSubgroup M →
          letI : (K.subgroupOf M).Normal := hKnormal
          Nat.card ((W1.subgroupOf M).map (QuotientGroup.mk' (K.subgroupOf M))) =
            Nat.card W1 := by
  intro h92 hKnormal hKD
  letI : (K.subgroupOf M).Normal := hKnormal
  have hNleD : K.subgroupOf M ≤ (ambientDerivedSubgroup M).subgroupOf M := by
    intro x hx
    have hxK : (x : G) ∈ K := by
      simpa [Subgroup.mem_subgroupOf] using hx
    exact hKD hxK
  have hcomp :
      ((ambientDerivedSubgroup M).subgroupOf M).IsComplement' (W1.subgroupOf M) :=
    ambientDerived_W1_isComplement'_subgroupOf_M_of_hypothesis_9_2_sec9
      M MF U W1 W2 q h92
  have hW1M : W1 ≤ M :=
    W1_le_M_of_hypothesis_9_2_sec9 M MF U W1 W2 q h92
  calc
    Nat.card ((W1.subgroupOf M).map (QuotientGroup.mk' (K.subgroupOf M)))
        = Nat.card (W1.subgroupOf M) :=
          natCard_map_mk'_eq_of_le_isComplement'
            ((ambientDerivedSubgroup M).subgroupOf M) (W1.subgroupOf M)
            (K.subgroupOf M) hNleD hcomp
    _ = Nat.card W1 := natCard_subgroupOf_eq W1 M hW1M

public theorem theorem_9_nb_redM_W1_map_mk_K_card_ne_one_sec9
    {G : Type u} [Group G] [Finite G]
    (M MF U W1 W2 K : Subgroup G)
    (q : ℕ) :
    hypothesis_9_2_statement M MF U W1 W2 q →
      (hKnormal : (K.subgroupOf M).Normal) →
        K ≤ ambientDerivedSubgroup M →
          letI : (K.subgroupOf M).Normal := hKnormal
          Nat.card ((W1.subgroupOf M).map (QuotientGroup.mk' (K.subgroupOf M))) ≠ 1 := by
  intro h92 hKnormal hKD
  letI : (K.subgroupOf M).Normal := hKnormal
  have hcard :
      Nat.card ((W1.subgroupOf M).map (QuotientGroup.mk' (K.subgroupOf M))) =
        Nat.card W1 :=
    theorem_9_nb_redM_W1_map_mk_K_card_eq_sec9
      M MF U W1 W2 K q h92 hKnormal hKD
  have h92W1 : hypothesis_9_2_statement M MF U W1 W2 (Nat.card W1) :=
    hypothesis_9_2_with_card_W1_sec9 h92
  have hW1prime : Nat.Prime (Nat.card W1) :=
    nat_card_W1_prime_of_hypothesis_9_2_sec9 M MF U W1 W2 h92W1
  intro hcard1
  exact hW1prime.ne_one (by
    rw [← hcard]
    exact hcard1)

public theorem theorem_9_nb_redM_W1_map_mk_K_isCyclic_sec9
    {G : Type u} [Group G] [Finite G]
    (M MF U W1 W2 K : Subgroup G)
    (q : ℕ) :
    hypothesis_9_2_statement M MF U W1 W2 q →
      (hKnormal : (K.subgroupOf M).Normal) →
        letI : (K.subgroupOf M).Normal := hKnormal
        let qM : M →* M ⧸ K.subgroupOf M :=
          QuotientGroup.mk' (K.subgroupOf M)
        IsCyclic ((W1.subgroupOf M).map qM) := by
  intro h92 hKnormal
  letI : (K.subgroupOf M).Normal := hKnormal
  let qM : M →* M ⧸ K.subgroupOf M := QuotientGroup.mk' (K.subgroupOf M)
  change IsCyclic ((W1.subgroupOf M).map qM)
  have hW1cyc : IsCyclic W1 := by
    rcases h92.typePDefinitionData with
      ⟨_hMFsource, hW1cyc, _hW1ne, _hW1hall, _hrest⟩
    exact hW1cyc
  have hW1M : W1 ≤ M :=
    W1_le_M_of_hypothesis_9_2_sec9 M MF U W1 W2 q h92
  have hW1sub_cyclic : IsCyclic (W1.subgroupOf M) :=
    (Subgroup.subgroupOfEquivOfLe (H := W1) (K := M) hW1M).isCyclic.mpr hW1cyc
  letI : IsCyclic (W1.subgroupOf M) := hW1sub_cyclic
  exact isCyclic_of_surjective
    (f := qM.subgroupMap (W1.subgroupOf M))
    (MonoidHom.subgroupMap_surjective qM (W1.subgroupOf M))

public theorem theorem_9_nb_redM_W1_map_mk_K_isHall_sec9
    {G : Type u} [Group G] [Finite G]
    (M MF U W1 W2 K : Subgroup G)
    (q : ℕ) :
    hypothesis_9_2_statement M MF U W1 W2 q →
      (hKnormal : (K.subgroupOf M).Normal) →
        letI : (K.subgroupOf M).Normal := hKnormal
        let qM : M →* M ⧸ K.subgroupOf M :=
          QuotientGroup.mk' (K.subgroupOf M)
        ∃ π : Set Nat.Primes,
          IsHallSubgroup π ((W1.subgroupOf M).map qM) := by
  intro h92 hKnormal
  letI : (K.subgroupOf M).Normal := hKnormal
  let qM : M →* M ⧸ K.subgroupOf M := QuotientGroup.mk' (K.subgroupOf M)
  change ∃ π : Set Nat.Primes, IsHallSubgroup π ((W1.subgroupOf M).map qM)
  rcases h92.typePDefinitionData with
    ⟨_hMFsource, _hW1cyc, _hW1ne, hW1hall, _hcompMW1, _hrest⟩
  rcases hW1hall with ⟨_hW1M, hHall⟩
  exact ⟨subgroupPrimeSet W1,
    isHallSubgroup_map_of_surjective_sec9 hHall qM
      (QuotientGroup.mk'_surjective (K.subgroupOf M))⟩

public theorem theorem_9_nb_redM_M_mod_K_quotient_internalDirectProduct_sec9
    {G : Type u} [Group G] [Finite G]
    (M MF U W1 W2 K : Subgroup G)
    (q : ℕ) :
    hypothesis_9_2_statement M MF U W1 W2 q →
      (hKnormal : (K.subgroupOf M).Normal) →
        K ≤ ambientDerivedSubgroup M →
          letI : (K.subgroupOf M).Normal := hKnormal
          let qM : M →* M ⧸ K.subgroupOf M :=
            QuotientGroup.mk' (K.subgroupOf M)
          Section2.IsInternalDirectProduct
            (((W1 ⊔ W2).subgroupOf M).map qM)
            ((W1.subgroupOf M).map qM)
            ((W2.subgroupOf M).map qM) := by
  classical
  intro h92 hKnormal hKD
  letI : (K.subgroupOf M).Normal := hKnormal
  let qM : M →* M ⧸ K.subgroupOf M := QuotientGroup.mk' (K.subgroupOf M)
  change Section2.IsInternalDirectProduct
    (((W1 ⊔ W2).subgroupOf M).map qM)
    ((W1.subgroupOf M).map qM)
    ((W2.subgroupOf M).map qM)
  let Wq : Subgroup (M ⧸ K.subgroupOf M) :=
    ((W1 ⊔ W2).subgroupOf M).map qM
  let W1q : Subgroup (M ⧸ K.subgroupOf M) :=
    (W1.subgroupOf M).map qM
  let W2q : Subgroup (M ⧸ K.subgroupOf M) :=
    (W2.subgroupOf M).map qM
  let Dq : Subgroup (M ⧸ K.subgroupOf M) :=
    ((ambientDerivedSubgroup M).subgroupOf M).map qM
  have hWprod :
      Section2.IsInternalDirectProduct
        ((W1 ⊔ W2).subgroupOf M) (W1.subgroupOf M) (W2.subgroupOf M) :=
    theorem_9_nb_redM_W_internalDirectProduct_sec9 M MF U W1 W2 q h92
  have hsemi :
      Section2.IsInternalSemidirectProduct
        (⊤ : Subgroup (M ⧸ K.subgroupOf M)) Dq W1q := by
    simpa [Dq, W1q, qM] using
      (theorem_9_nb_redM_M_mod_K_quotient_semidirect_sec9
        M MF U W1 W2 K q h92 hKnormal hKD)
  have hW2Dsub :
      W2.subgroupOf M ≤ (ambientDerivedSubgroup M).subgroupOf M := by
    intro x hx
    have hxW2 : ((x : M) : G) ∈ W2 := by
      simpa [Subgroup.mem_subgroupOf] using hx
    have hxD : ((x : M) : G) ∈ ambientDerivedSubgroup M :=
      theorem_9_nb_redM_W2_le_ambientDerived_sec9 M MF U W1 W2 q h92 hxW2
    simpa [Subgroup.mem_subgroupOf] using hxD
  have hW2q_le_Dq : W2q ≤ Dq := by
    intro x hx
    rcases hx with ⟨y, hyW2, hxy⟩
    exact ⟨y, hW2Dsub hyW2, hxy⟩
  refine
    { left_le := ?_
      right_le := ?_
      commute := ?_
      inf_eq_bot := ?_
      mul_surjective := ?_ }
  · intro x hx
    rcases hx with ⟨y, hyW1, hxy⟩
    exact ⟨y, hWprod.left_le hyW1, hxy⟩
  · intro x hx
    rcases hx with ⟨y, hyW2, hxy⟩
    exact ⟨y, hWprod.right_le hyW2, hxy⟩
  · intro h hh k hk
    rcases hh with ⟨h0, hh0, hqh⟩
    rcases hk with ⟨k0, hk0, hqk⟩
    have hcomm : h0 * k0 = k0 * h0 :=
      hWprod.commute h0 hh0 k0 hk0
    calc
      h * k = qM h0 * qM k0 := by rw [← hqh, ← hqk]
      _ = qM (h0 * k0) := by rw [map_mul]
      _ = qM (k0 * h0) := by rw [hcomm]
      _ = qM k0 * qM h0 := by rw [map_mul]
      _ = k * h := by rw [← hqh, ← hqk]
  · apply le_antisymm
    · intro x hx
      have hxDq : x ∈ Dq := hW2q_le_Dq hx.2
      have hxInf : x ∈ Dq ⊓ W1q := ⟨hxDq, hx.1⟩
      have hxBot : x ∈ (⊥ : Subgroup (M ⧸ K.subgroupOf M)) := by
        simpa [hsemi.inf_eq_bot] using hxInf
      simpa using hxBot
    · exact bot_le
  · intro c hc
    rcases hc with ⟨c0, hc0, hqc⟩
    rcases hWprod.mul_surjective c0 hc0 with
      ⟨h0, hh0, k0, hk0, hc0eq⟩
    refine ⟨qM h0, ⟨h0, hh0, rfl⟩, qM k0, ⟨k0, hk0, rfl⟩, ?_⟩
    calc
      c = qM c0 := hqc.symm
      _ = qM (h0 * k0) := by rw [hc0eq]
      _ = qM h0 * qM k0 := by rw [map_mul]

public theorem theorem_9_nb_redM_M_mod_K_quotient_W_odd_sec9
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    (M W1 W2 K : Subgroup G)
    (hKnormal : (K.subgroupOf M).Normal) :
    letI : (K.subgroupOf M).Normal := hKnormal
    let qM : M →* M ⧸ K.subgroupOf M :=
      QuotientGroup.mk' (K.subgroupOf M)
    Odd (Nat.card (((W1 ⊔ W2).subgroupOf M).map qM)) := by
  intro
  let qM : M →* M ⧸ K.subgroupOf M := QuotientGroup.mk' (K.subgroupOf M)
  change Odd (Nat.card (((W1 ⊔ W2).subgroupOf M).map qM))
  have hWq_dvd_quot :
      Nat.card (((W1 ⊔ W2).subgroupOf M).map qM) ∣
        Nat.card (M ⧸ K.subgroupOf M) :=
    Subgroup.card_subgroup_dvd_card (((W1 ⊔ W2).subgroupOf M).map qM)
  have hquot_dvd_M :
      Nat.card (M ⧸ K.subgroupOf M) ∣ Nat.card M :=
    Subgroup.card_quotient_dvd_card (K.subgroupOf M)
  have hM_dvd_G : Nat.card M ∣ Nat.card G :=
    Subgroup.card_subgroup_dvd_card M
  exact Odd.of_dvd_nat IsMinCE.odd_order
    (hWq_dvd_quot.trans (hquot_dvd_M.trans hM_dvd_G))

public theorem theorem_9_nb_redM_centralizerIn_ambientDerived_subgroupOf_M_eq_W2_sec9
    {G : Type u} [Group G] [Finite G]
    (M MF U W1 W2 : Subgroup G)
    (q : ℕ) :
    hypothesis_9_2_statement M MF U W1 W2 q →
      ∀ x : W1.subgroupOf M, x ≠ 1 →
        Section2.centralizerIn ((ambientDerivedSubgroup M).subgroupOf M) (x : M) =
          W2.subgroupOf M := by
  intro h92 x hx
  rcases h92.typePDefinitionData with
    ⟨_hMFsource, _hW1cyc, _hW1ne, _hW1hall, _hcompMW1, _hUleD,
      _hUnil, _hW1normU, _hcompDU, _hMFnotCyc, _hSecondLe, _hFittingEq,
      _hFittingLeD, _hW2le, _hW2cyc, _hW2ne, hCent, _hHatW⟩
  have hxW1 : ((x : M) : G) ∈ W1 :=
    Subgroup.mem_subgroupOf.mp x.property
  have hxGne : ((x : M) : G) ≠ 1 := by
    intro hxG
    have hxM : (x : M) = 1 := Subtype.ext hxG
    exact hx (Subtype.ext hxM)
  ext y
  constructor
  · intro hy
    have hyDG : ((y : M) : G) ∈ ambientDerivedSubgroup M := by
      simpa [Subgroup.mem_subgroupOf] using hy.1
    have hyCommM : y * (x : M) = (x : M) * y :=
      Subgroup.mem_centralizer_singleton_iff.mp hy.2
    have hyCommG :
        ((y : M) : G) * ((x : M) : G) =
          ((x : M) : G) * ((y : M) : G) :=
      congrArg Subtype.val hyCommM
    have hyCentG :
        ((y : M) : G) ∈
          elementCentralizerIn (ambientDerivedSubgroup M) ((x : M) : G) :=
      ⟨hyDG, Subgroup.mem_centralizer_singleton_iff.mpr hyCommG⟩
    have hyW2G : ((y : M) : G) ∈ W2 := by
      simpa [hCent ((x : M) : G) hxW1 hxGne] using hyCentG
    simpa [Subgroup.mem_subgroupOf] using hyW2G
  · intro hy
    have hyW2G : ((y : M) : G) ∈ W2 := by
      simpa [Subgroup.mem_subgroupOf] using hy
    have hyCentG :
        ((y : M) : G) ∈
          elementCentralizerIn (ambientDerivedSubgroup M) ((x : M) : G) := by
      simpa [hCent ((x : M) : G) hxW1 hxGne] using hyW2G
    constructor
    · simpa [Subgroup.mem_subgroupOf] using hyCentG.1
    · have hyCommG :
          ((y : M) : G) * ((x : M) : G) =
            ((x : M) : G) * ((y : M) : G) :=
        Subgroup.mem_centralizer_singleton_iff.mp hyCentG.2
      have hyCommM : y * (x : M) = (x : M) * y := by
        apply Subtype.ext
        exact hyCommG
      exact Subgroup.mem_centralizer_singleton_iff.mpr hyCommM

public theorem theorem_9_nb_redM_M_mod_K_quotient_centralizer_sec9
    {G : Type u} [Group G] [Finite G]
    (M MF U W1 W2 K : Subgroup G)
    (q : ℕ) :
    hypothesis_9_2_statement M MF U W1 W2 q →
      (hKnormal : (K.subgroupOf M).Normal) →
        K ≤ ambientDerivedSubgroup M →
          letI : (K.subgroupOf M).Normal := hKnormal
          let qM : M →* M ⧸ K.subgroupOf M :=
            QuotientGroup.mk' (K.subgroupOf M)
          ∀ x : (W1.subgroupOf M).map qM, x ≠ 1 →
            Section2.centralizerIn
              (((ambientDerivedSubgroup M).subgroupOf M).map qM)
              (x : M ⧸ K.subgroupOf M) =
              (W2.subgroupOf M).map qM := by
  classical
  intro h92 hKnormal hKD
  letI : (K.subgroupOf M).Normal := hKnormal
  let qM : M →* M ⧸ K.subgroupOf M := QuotientGroup.mk' (K.subgroupOf M)
  change ∀ x : (W1.subgroupOf M).map qM, x ≠ 1 →
    Section2.centralizerIn
      (((ambientDerivedSubgroup M).subgroupOf M).map qM)
      (x : M ⧸ K.subgroupOf M) =
      (W2.subgroupOf M).map qM
  have hP : Section8.typePDefinitionData M MF U W1 W2 := h92.typePDefinitionData
  have hDleM : ambientDerivedSubgroup M ≤ M := section12_ambientDerivedSubgroup_le
  have hDnormal : ((ambientDerivedSubgroup M).subgroupOf M).Normal := by
    simpa using (section12_normalIn_ambientDerivedSubgroup (G := G) (E := M)).2
  letI : ((ambientDerivedSubgroup M).subgroupOf M).Normal := hDnormal
  have hsolvD : Group.IsSolvable (ambientDerivedSubgroup M) :=
    typePDefinitionData_ambientDerived_solvable_sec9 hP
  have hsolvDsub : Group.IsSolvable ((ambientDerivedSubgroup M).subgroupOf M) := by
    let e := Subgroup.subgroupOfEquivOfLe (H := ambientDerivedSubgroup M)
      (K := M) hDleM
    letI : Group.IsSolvable (ambientDerivedSubgroup M) := hsolvD
    exact Group.isSolvable_of_isSolvable_injective
      (f := e.toMonoidHom) e.injective
  have hDcard :
      Nat.card ((ambientDerivedSubgroup M).subgroupOf M) =
        Nat.card (ambientDerivedSubgroup M) :=
    natCard_subgroupOf_eq (ambientDerivedSubgroup M) M hDleM
  have hW1M : W1 ≤ M :=
    W1_le_M_of_hypothesis_9_2_sec9 M MF U W1 W2 q h92
  have hW1card : Nat.card (W1.subgroupOf M) = Nat.card W1 :=
    natCard_subgroupOf_eq W1 M hW1M
  have hcopW1D :
      Nat.Coprime (Nat.card W1) (Nat.card (ambientDerivedSubgroup M)) :=
    typePDefinitionData_W1_card_coprime_ambientDerived_sec9 hP
  have hcopD_W1sub :
      Nat.Coprime (Nat.card ((ambientDerivedSubgroup M).subgroupOf M))
        (Nat.card (W1.subgroupOf M)) := by
    rw [hDcard, hW1card]
    exact hcopW1D.symm
  have hcentW1 :
      ∀ x : W1.subgroupOf M, x ≠ 1 →
        Section2.centralizerIn ((ambientDerivedSubgroup M).subgroupOf M) (x : M) =
          W2.subgroupOf M :=
    theorem_9_nb_redM_centralizerIn_ambientDerived_subgroupOf_M_eq_W2_sec9
      M MF U W1 W2 q h92
  intro r hr
  apply le_antisymm
  · intro y hy
    have hyElem :
        y ∈ elementCentralizerIn
          (((ambientDerivedSubgroup M).subgroupOf M).map qM)
          (r : M ⧸ K.subgroupOf M) := by
      simpa [Section2.centralizerIn, Section2.elementCentralizer,
        elementCentralizerIn] using hy
    rcases r.property with ⟨w, hwW1, hwq⟩
    have hw_sub_ne : (⟨w, hwW1⟩ : W1.subgroupOf M) ≠ 1 := by
      intro hwone
      apply hr
      apply Subtype.ext
      calc
        (r : M ⧸ K.subgroupOf M) = qM w := hwq.symm
        _ = 1 := by
          have hwoneM : w = 1 := congrArg Subtype.val hwone
          simp [qM, hwoneM]
    let R0 : Subgroup M := Subgroup.zpowers w
    have hR0_le_W1 : R0 ≤ W1.subgroupOf M :=
      (Subgroup.zpowers_le).2 hwW1
    have hR0normD :
        R0 ≤ Subgroup.normalizer (((ambientDerivedSubgroup M).subgroupOf M) : Set M) := by
      exact hR0_le_W1.trans
        (Subgroup.le_normalizer_of_normal
          (H := (ambientDerivedSubgroup M).subgroupOf M))
    have hR0card_dvd_W1 : Nat.card R0 ∣ Nat.card (W1.subgroupOf M) := by
      rw [← natCard_subgroupOf_eq R0 (W1.subgroupOf M) hR0_le_W1]
      exact Subgroup.card_subgroup_dvd_card (R0.subgroupOf (W1.subgroupOf M))
    have hcopDR0 :
        Nat.Coprime (Nat.card ((ambientDerivedSubgroup M).subgroupOf M))
          (Nat.card R0) :=
      Nat.Coprime.of_dvd_right hR0card_dvd_W1 hcopD_W1sub
    have hKinv : ∀ r0 : R0, ∀ x ∈ K.subgroupOf M,
        (r0 : M) * x * (r0 : M)⁻¹ ∈ K.subgroupOf M := by
      intro r0 x hx
      exact (inferInstance : (K.subgroupOf M).Normal).conj_mem x hx (r0 : M)
    have hcentSubQuot :
        subgroupCentralizerIn
            (((ambientDerivedSubgroup M).subgroupOf M).map qM) (R0.map qM) =
          (subgroupCentralizerIn ((ambientDerivedSubgroup M).subgroupOf M) R0).map qM :=
      subgroupCentralizerIn_map_mk'_eq_map_of_solvable_coprime
        ((ambientDerivedSubgroup M).subgroupOf M) R0 (K.subgroupOf M)
        hR0normD hsolvDsub hcopDR0 hKinv
    have hySub :
        y ∈ subgroupCentralizerIn
          (((ambientDerivedSubgroup M).subgroupOf M).map qM) (R0.map qM) := by
      refine ⟨hyElem.1, ?_⟩
      change y ∈ Subgroup.centralizer
        ((R0.map qM : Subgroup (M ⧸ K.subgroupOf M)) :
          Set (M ⧸ K.subgroupOf M))
      rw [Subgroup.mem_centralizer_iff]
      intro z hz
      rcases hz with ⟨b, hbR0, hbz⟩
      rcases Subgroup.mem_zpowers_iff.mp hbR0 with ⟨n, hn⟩
      have hcomm_r :
          y * (r : M ⧸ K.subgroupOf M) =
            (r : M ⧸ K.subgroupOf M) * y :=
        Subgroup.mem_centralizer_singleton_iff.mp hyElem.2
      have hcomm_qw : Commute y (qM w) := by
        change y * qM w = qM w * y
        rw [hwq]
        exact hcomm_r
      have hcomm_qb : Commute y (qM b) := by
        rw [← hn]
        simpa [qM] using hcomm_qw.zpow_right n
      calc
        z * y = qM b * y := by rw [hbz]
        _ = y * qM b := hcomm_qb.eq.symm
        _ = y * z := by rw [hbz]
    have hymap :
        y ∈ (subgroupCentralizerIn ((ambientDerivedSubgroup M).subgroupOf M) R0).map qM := by
      simpa [hcentSubQuot] using hySub
    rcases hymap with ⟨z, hzcent, hzy⟩
    have hcent_w :
        elementCentralizerIn ((ambientDerivedSubgroup M).subgroupOf M) w =
          W2.subgroupOf M := by
      simpa [Section2.centralizerIn, Section2.elementCentralizer,
        elementCentralizerIn] using hcentW1 ⟨w, hwW1⟩ hw_sub_ne
    have hzElem :
        z ∈ elementCentralizerIn ((ambientDerivedSubgroup M).subgroupOf M) w := by
      refine ⟨hzcent.1, ?_⟩
      apply Subgroup.mem_centralizer_singleton_iff.mpr
      have hcomm : w * z = z * w :=
        Subgroup.mem_centralizer_iff.mp hzcent.2 w (Subgroup.mem_zpowers w)
      exact hcomm.symm
    have hzW2 : z ∈ W2.subgroupOf M := by
      simpa [hcent_w] using hzElem
    exact ⟨z, hzW2, hzy⟩
  · intro y hy
    rcases r.property with ⟨w, hwW1, hwq⟩
    rcases hy with ⟨z, hzW2, hzy⟩
    have hw_sub_ne : (⟨w, hwW1⟩ : W1.subgroupOf M) ≠ 1 := by
      intro hwone
      apply hr
      apply Subtype.ext
      calc
        (r : M ⧸ K.subgroupOf M) = qM w := hwq.symm
        _ = 1 := by
          have hwoneM : w = 1 := congrArg Subtype.val hwone
          simp [qM, hwoneM]
    have hcent_w :
        elementCentralizerIn ((ambientDerivedSubgroup M).subgroupOf M) w =
          W2.subgroupOf M := by
      simpa [Section2.centralizerIn, Section2.elementCentralizer,
        elementCentralizerIn] using hcentW1 ⟨w, hwW1⟩ hw_sub_ne
    have hzElem :
        z ∈ elementCentralizerIn ((ambientDerivedSubgroup M).subgroupOf M) w := by
      simpa [hcent_w] using hzW2
    have hyD : y ∈ (((ambientDerivedSubgroup M).subgroupOf M).map qM) :=
      ⟨z, hzElem.1, hzy⟩
    have hcomm_zw : z * w = w * z :=
      Subgroup.mem_centralizer_singleton_iff.mp hzElem.2
    have hycomm :
        y * (r : M ⧸ K.subgroupOf M) =
          (r : M ⧸ K.subgroupOf M) * y := by
      calc
        y * (r : M ⧸ K.subgroupOf M) = qM z * qM w := by rw [hzy, hwq]
        _ = qM (z * w) := by rw [map_mul]
        _ = qM (w * z) := by rw [hcomm_zw]
        _ = qM w * qM z := by rw [map_mul]
        _ = (r : M ⧸ K.subgroupOf M) * y := by rw [hzy, hwq]
    refine ⟨hyD, ?_⟩
    exact Subgroup.mem_centralizer_singleton_iff.mpr hycomm

public theorem theorem_9_nb_redM_M_mod_K_hypothesis_4_2_sec9
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    (M MF U W1 W2 H0 K : Subgroup G)
    (p q : ℕ) :
    hypothesis_9_2_statement M MF U W1 W2 q →
      H0 ≤ MF →
        Nat.Prime p →
          (∃ hp : Nat.Primes,
            hp.val = p ∧
              hoReductionData M MF U W2 H0 hp ∧
                quotientChiefFactorData_9_6 M MF H0 W1 hp) →
            (hKnormal : (K.subgroupOf M).Normal) →
              K ≤ ambientDerivedSubgroup M →
                K ⊓ MF = H0 →
                  letI : (K.subgroupOf M).Normal := hKnormal
                  let qM : M →* M ⧸ K.subgroupOf M :=
                    QuotientGroup.mk' (K.subgroupOf M)
                  Section4.hypothesis_4_2_statement
                    (((ambientDerivedSubgroup M).subgroupOf M).map qM)
                    ((W1.subgroupOf M).map qM)
                    ((W2.subgroupOf M).map qM)
                    (((W1 ⊔ W2).subgroupOf M).map qM) := by
  intro h92 hH0MF hpprime hpData hKnormal hKD hKinf
  letI : (K.subgroupOf M).Normal := hKnormal
  let qM : M →* M ⧸ K.subgroupOf M := QuotientGroup.mk' (K.subgroupOf M)
  change Section4.hypothesis_4_2_statement
    (((ambientDerivedSubgroup M).subgroupOf M).map qM)
    ((W1.subgroupOf M).map qM)
    ((W2.subgroupOf M).map qM)
    (((W1 ⊔ W2).subgroupOf M).map qM)
  have hdirect :
      Section2.IsInternalDirectProduct
        (((W1 ⊔ W2).subgroupOf M).map qM)
        ((W1.subgroupOf M).map qM)
        ((W2.subgroupOf M).map qM) :=
    theorem_9_nb_redM_M_mod_K_quotient_internalDirectProduct_sec9
      M MF U W1 W2 K q h92 hKnormal hKD
  exact
    ⟨theorem_9_nb_redM_M_mod_K_quotient_semidirect_sec9
        M MF U W1 W2 K q h92 hKnormal hKD,
      theorem_9_nb_redM_W1_map_mk_K_isHall_sec9
        M MF U W1 W2 K q h92 hKnormal,
      theorem_9_nb_redM_W1_map_mk_K_isCyclic_sec9
        M MF U W1 W2 K q h92 hKnormal,
      theorem_9_nb_redM_W1_map_mk_K_card_ne_one_sec9
        M MF U W1 W2 K q h92 hKnormal hKD,
      theorem_9_nb_redM_W2_map_mk_K_isCyclic_source_core_sec9
        M MF U W1 W2 H0 K q h92 hKnormal,
      natCard_ne_one_of_eq_prime_sec9 hpprime
        (theorem_9_nb_redM_W2_map_mk_K_card_eq_source_core_sec9
          M MF U W1 W2 H0 K p q h92 hH0MF hpprime hpData hKnormal hKD hKinf),
      theorem_9_nb_redM_M_mod_K_quotient_centralizer_sec9
        M MF U W1 W2 K q h92 hKnormal hKD,
      hdirect.left_le,
      hdirect.right_le,
      hdirect,
      theorem_9_nb_redM_M_mod_K_quotient_W_odd_sec9
        M W1 W2 K hKnormal⟩



end CFSG.Section9
