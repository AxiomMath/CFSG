module

public import CFSG.LocalAnalysis.StandardType.GGKGroupFusionFlatBasic
public import CFSG.LocalAnalysis.StandardType.GGKGroupFusionSeitzExcLTwoEight
public import CFSG.LocalAnalysis.StandardType.GGKGroupFusionSeitzExcSolv
public import CFSG.LocalAnalysis.StandardType.GGKGroupFusionSeitzExcSz
public import CFSG.LocalAnalysis.StandardType.GGKGroupFusionSeitzExcGenuine

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.AGLEmbeddingD2

theorem ggKGroupFusionAtFlat_seitzException_of (h₁ : GGKGroupFusionAtFlat GGKFSeitzLTwoEight)
    (h₂ : GGKGroupFusionAtFlat GGKFSeitzLThreeFour) (h₃ : GGKGroupFusionAtFlat GGKFSeitzUFourTwo)
    (h₄ : GGKGroupFusionAtFlat GGKFSeitzSpSixTwo) (h₅ : GGKGroupFusionAtFlat GGKFSeitzSpEightTwo)
    (h₆ : GGKGroupFusionAtFlat GGKFSeitzTitsThree) (h₇ : GGKGroupFusionAtFlat GGKFSeitzTitsFive)
    (h₈ : GGKGroupFusionAtFlat GGKFSeitzSzThirtyTwo) :
    GGKGroupFusionAtFlat GGKFLieSeitzException := by
  intro W _ _ p H E i ⟨d, hi, hex⟩ hyp hL hK he
  rcases hex with ⟨rfl, ⟨q, hq2, hq3, hd⟩ | ⟨q, hq2, hq3, hd⟩ | ⟨q, hq2, hq3, hd⟩ |
    ⟨q, hq2, hq3, hd | hd⟩ | hd⟩ | ⟨rfl, hd | hd⟩
  · exact h₁ W 3 H E i ⟨rfl, d, q, hi, hq2, hq3, hd⟩ hyp hL hK he
  · exact h₂ W 3 H E i ⟨rfl, d, q, hi, hq2, hq3, hd⟩ hyp hL hK he
  · exact h₃ W 3 H E i ⟨rfl, d, q, hi, hq2, hq3, hd⟩ hyp hL hK he
  · exact h₄ W 3 H E i ⟨rfl, d, q, hi, hq2, hq3, hd⟩ hyp hL hK he
  · exact h₅ W 3 H E i ⟨rfl, d, q, hi, hq2, hq3, hd⟩ hyp hL hK he
  · exact h₆ W 3 H E i ⟨rfl, d, hi, hd⟩ hyp hL hK he
  · exact h₇ W 5 H E i ⟨rfl, d, hi, hd⟩ hyp hL hK he
  · exact h₈ W 5 H E i ⟨rfl, d, hi, hd⟩ hyp hL hK he

section Common

variable {W : Type} [Group W] [Finite W] {p : ℕ} {H E : Subgroup W}

theorem ggHypThreeSixteenFlat_exists_ne_one (hyp : GGHypThreeSixteenFlat p H E) :
    ∃ e ∈ E, e ≠ 1 := by
  obtain ⟨⟨hp, -, -, hEcard, -⟩, -⟩ := hyp
  by_contra hcon
  push Not at hcon
  have hbot : E = ⊥ := (Subgroup.eq_bot_iff_forall E).mpr hcon
  rw [hbot, Subgroup.card_bot] at hEcard
  have h1 := hp.one_lt
  have : 1 < p ^ 2 := Nat.one_lt_pow (by norm_num) h1
  omega

theorem ggSeitzExc_not_dvd_index_flat (hyp : GGHypThreeSixteenFlat p H E) :
    ¬ p ∣ (H.subgroupOf (CFSG.generalizedFitting W)).index := by
  obtain ⟨e, heE, he1⟩ := ggHypThreeSixteenFlat_exists_ne_one hyp
  obtain ⟨⟨hp, -, hE, -, hfus⟩, -⟩ := hyp
  have : Fact p.Prime := ⟨hp⟩
  have : (CFSG.generalizedFitting W).Normal :=
    CFSG.LocalCores.generalized_fitting_characteristic.2
  have h := hfus.not_dvd_relIndex_inf hE heE he1 (CFSG.generalizedFitting W)
  rwa [Subgroup.relIndex, Subgroup.inf_subgroupOf_right] at h

theorem ggSeitzExc_not_isSolvable_flat
    (hSch : CFSG.LocalAnalysis.ComponentInitial.SchreierFor InCatalog)
    (hyp : GGHypThreeSixteenFlat p H E) (hL : LargeEvenLayer (⊤ : Subgroup (GGHypQuot H)) ≠ ⊥) :
    ¬ Group.IsSolvable ↥(H.subgroupOf (CFSG.generalizedFitting W)) := by
  intro hX
  have : (CFSG.generalizedFitting W).Normal :=
    CFSG.LocalCores.generalized_fitting_characteristic.2
  set N := ((QuotientGroup.mk' (CFSG.generalizedFitting W)).comp H.subtype).ker
  have hN : Group.IsSolvable ↥N :=
    Group.isSolvable_of_isSolvable_injective
      (f := (ggSubgroupOfEquivKer H (CFSG.generalizedFitting W)).symm.toMonoidHom)
      (ggSubgroupOfEquivKer H (CFSG.generalizedFitting W)).symm.injective
  have hQ := ggIsSolvable_quot_inf_generalizedFitting_flat hSch hyp
  exact ggNot_isSolvable_of_layer_ne_bot hL (Group.isSolvable_of_subgroup_quotient N)

end Common

theorem ggKGroupFusionAtFlat_of_solvable
    (hSch : CFSG.LocalAnalysis.ComponentInitial.SchreierFor InCatalog)
    {S : TauCeti.CFSGIndex → ℕ → Prop}
    (h : ∀ (i : TauCeti.CFSGIndex) (p : ℕ), S i p → ∀ (K : Type) [Group K] [Finite K],
      IsSimpleGroup K → Nonempty (K ≃* i.Group) →
        ∀ X : Subgroup K, X ≠ ⊤ → ¬ p ∣ X.index → Group.IsSolvable ↥X) :
    GGKGroupFusionAtFlat S := by
  intro W _ _ p H E i hi hyp hL hKH he
  exact (ggSeitzExc_not_isSolvable_flat hSch hyp hL (h i p hi _ hyp.2.1.1 he _
    (ggSeitzExc_subgroupOf_ne_top hKH) (ggSeitzExc_not_dvd_index_flat hyp))).elim

section Hyp

variable {W : Type} [Group W] [Finite W] {p : ℕ} {H E : Subgroup W}

theorem ggSeitzExc_quotComponent_equiv_flat
    (hSch : CFSG.LocalAnalysis.ComponentInitial.SchreierFor InCatalog)
    (hyp : GGHypThreeSixteenFlat p H E)
    (hs : IsSimpleGroup ↥(commutator ↥(H.subgroupOf (CFSG.generalizedFitting W))))
    (hns : ¬ Group.IsSolvable ↥(H.subgroupOf (CFSG.generalizedFitting W)))
    {C : Subgroup (GGHypQuot H)} (hC : IsComponentOf C ⊤) :
    Nonempty (↥C ≃* ↥(commutator ↥(H.subgroupOf (CFSG.generalizedFitting W)))) := by
  classical
  have : (CFSG.generalizedFitting W).Normal :=
    CFSG.LocalCores.generalized_fitting_characteristic.2
  set N : Subgroup ↥H := ((QuotientGroup.mk' (CFSG.generalizedFitting W)).comp H.subtype).ker
    with hN
  let φ := ggSubgroupOfEquivKer H (CFSG.generalizedFitting W)
  set M : Subgroup ↥H := ⁅N, N⁆ with hM
  let eM : ↥M ≃* ↥(commutator ↥(H.subgroupOf (CFSG.generalizedFitting W))) :=
    (ggCommutatorEquiv N).trans (ggCommutatorCongr φ.symm)
  have hMs : IsSimpleGroup ↥M := eM.isSimpleGroup
  have hMns : ¬ Group.IsSolvable ↥M := fun h => hns (ggIsSolvable_of_commutator
    (Group.isSolvable_of_isSolvable_injective (f := eM.symm.toMonoidHom) eM.symm.injective))
  have hQ := ggIsSolvable_quot_inf_generalizedFitting_flat hSch hyp
  obtain ⟨k, hk⟩ := ggExists_derivedSeries_le_of_isSolvable N hQ
  have hk' : derivedSeries ↥H (k + 1) ≤ M := by
    rw [derivedSeries_succ]
    exact Subgroup.commutator_mono hk hk
  set Q : Subgroup ↥H := CFSG.pCore 2 ↥H with hQdef
  set π : ↥H →* GGHypQuot H := QuotientGroup.mk' Q with hπ
  have hπs : Function.Surjective π := QuotientGroup.mk'_surjective Q
  have hCM : C ≤ M.map π := by
    have h1 := ggLe_derivedSeries_of_perfect (ggComponent_perfect hC) (k + 1)
    rw [← map_derivedSeries_eq hπs (k + 1)] at h1
    exact h1.trans (Subgroup.map_mono hk')
  have hMQ : Q.subgroupOf M = ⊥ := by
    have hQn : (Q.subgroupOf M).Normal := Subgroup.Normal.subgroupOf inferInstance M
    rcases @IsSimpleGroup.eq_bot_or_eq_top_of_normal _ _ hMs _ hQn with h | h
    · exact h
    · exfalso
      apply hMns
      have hle : M ≤ Q := Subgroup.subgroupOf_eq_top.mp h
      have h2 : IsPGroup 2 ↥M := (CFSG.pCore_isPGroup (p := 2) (G := ↥H)).to_le hle
      have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
      have : Group.IsNilpotent ↥M := h2.isNilpotent
      infer_instance
  let ρ : ↥M →* GGHypQuot H := π.comp M.subtype
  have hρ : Function.Injective ρ := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro x hx
    have hxQ : (x : ↥H) ∈ Q := by
      rw [MonoidHom.mem_ker] at hx
      exact (QuotientGroup.eq_one_iff _).mp hx
    have : x ∈ Q.subgroupOf M := Subgroup.mem_subgroupOf.mpr hxQ
    rwa [hMQ] at this
  have hρr : ρ.range = M.map π := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
  let eρ : ↥M ≃* ↥(M.map π) := (MonoidHom.ofInjective hρ).trans (MulEquiv.subgroupCongr hρr)
  have hMbs : IsSimpleGroup ↥(M.map π) := eρ.symm.isSimpleGroup
  have hsub := ggIsSubnormal_inf hC.2.1 (M.map π)
  rw [inf_eq_left.mpr hCM, top_inf_eq] at hsub
  have hCeq : C = M.map π :=
    ggEq_of_isSubnormal_of_isSimpleGroup hsub hMbs (ggComponent_ne_bot hC)
  exact ⟨(MulEquiv.subgroupCongr hCeq).trans (eρ.symm.trans eM)⟩

theorem ggSeitzExc_card_quotComponent_dvd_flat
    (hSch : CFSG.LocalAnalysis.ComponentInitial.SchreierFor InCatalog)
    (hyp : GGHypThreeSixteenFlat p H E) {C : Subgroup (GGHypQuot H)}
    (hC : IsComponentOf C ⊤) :
    Nat.card ↥C ∣ Nat.card ↥(H.subgroupOf (CFSG.generalizedFitting W)) := by
  have : (CFSG.generalizedFitting W).Normal :=
    CFSG.LocalCores.generalized_fitting_characteristic.2
  set N : Subgroup ↥H := ((QuotientGroup.mk' (CFSG.generalizedFitting W)).comp H.subtype).ker
    with hN
  have hQ := ggIsSolvable_quot_inf_generalizedFitting_flat hSch hyp
  obtain ⟨k, hk⟩ := ggExists_derivedSeries_le_of_isSolvable N hQ
  set Q : Subgroup ↥H := CFSG.pCore 2 ↥H with hQdef
  set π : ↥H →* GGHypQuot H := QuotientGroup.mk' Q with hπ
  have hCN : C ≤ N.map π := by
    have h1 := ggLe_derivedSeries_of_perfect (ggComponent_perfect hC) k
    rw [← map_derivedSeries_eq (QuotientGroup.mk'_surjective Q) k] at h1
    exact h1.trans (Subgroup.map_mono hk)
  calc Nat.card ↥C ∣ Nat.card ↥(N.map π) := Subgroup.card_dvd_of_le hCN
    _ ∣ Nat.card ↥N := Subgroup.card_map_dvd (H := N) π
    _ = Nat.card ↥(H.subgroupOf (CFSG.generalizedFitting W)) :=
      Nat.card_congr (ggSubgroupOfEquivKer H (CFSG.generalizedFitting W)).symm.toEquiv

end Hyp

section Transport

variable {W : Type} [Group W] [Finite W] {p : ℕ} {H E : Subgroup W}

theorem ggSeitzExc_transport_flat (hyp : GGHypThreeSixteenFlat p H E) :
    ∃ E' : Subgroup (MulAut ↥(CFSG.generalizedFitting W)), IsElemAbelian p E' ∧
      Nat.card E' = p ^ 2 ∧ ggFixedClosure E' ≤ H.subgroupOf (CFSG.generalizedFitting W) ∧
        (IsPGroup p ↥(ggFixedSubgroup E') →
          IsPGroup p ↥(CFSG.generalizedFitting W ⊓ Subgroup.centralizer (E : Set W))) := by
  obtain ⟨⟨hp, -, hE, hEcard, hfus⟩, ⟨hsimple, hnab, -⟩, -⟩ := hyp
  set K := CFSG.generalizedFitting W
  have : K.Normal := CFSG.LocalCores.generalized_fitting_characteristic.2
  have hψ : Function.Injective (MulAut.conjNormal (H := K)) := by
    rw [injective_iff_map_eq_one]
    intro x hx
    refine ggEq_one_of_commute_generalizedFitting hsimple hnab fun k hk => ?_
    have h1 := congrArg Subtype.val (DFunLike.congr_fun hx ⟨k, hk⟩)
    rw [MulAut.conjNormal_apply, MulAut.one_apply] at h1
    exact mul_inv_eq_iff_eq_mul.mp h1
  have hfix : ∀ (a : W) (k : K), MulAut.conjNormal (H := K) a k = k ↔ a * (k : W) * a⁻¹ = k := by
    intro a k
    rw [← Subtype.coe_inj, MulAut.conjNormal_apply]
  refine ⟨E.map (MulAut.conjNormal (H := K)),
    CFSG.PreuniquenessRankFour.Helpers.elementary_abelian_map p ⟨hE.1, hE.2⟩ _,
    by rw [Subgroup.card_map_of_injective hψ, hEcard], ?_, fun hP => ?_⟩
  ·
    rw [ggFixedClosure, Subgroup.closure_le]
    rintro k ⟨_, ⟨a, haE, rfl⟩, hε1, hεk⟩
    have ha1 : a ≠ 1 := by
      rintro rfl
      exact hε1 (map_one _)
    have hfixa : a * (k : W) * a⁻¹ = k := (hfix a k).mp hεk
    refine Subgroup.mem_subgroupOf.mpr (hfus.centralizer_le haE ha1 ?_)
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact (mul_inv_eq_iff_eq_mul.mp hfixa).symm
  ·
    refine (hP.map K.subtype).to_le ?_
    rintro w ⟨hwK, hwC⟩
    refine ⟨⟨w, hwK⟩, ?_, rfl⟩
    rintro _ ⟨a, haE, rfl⟩
    refine (hfix a ⟨w, hwK⟩).mpr ?_
    have h1 := Subgroup.mem_centralizer_iff.mp hwC a haE
    rw [h1, mul_inv_cancel_right]

end Transport

theorem ggKGroupFusionAtFlat_lTwoEight
    (hSch : CFSG.LocalAnalysis.ComponentInitial.SchreierFor InCatalog) :
    GGKGroupFusionAtFlat GGKFSeitzLTwoEight :=
  ggKGroupFusionAtFlat_of_solvable hSch
    fun _ _ ⟨hp, d, q, hi, hq2, hq3, hd⟩ K _ _ _ ⟨e⟩ _ hX h3 => by
      subst hp hi
      exact ggIsSolvable_of_not_dvd_index_of_card_eq_504 (ggCard_lTwoEight d q hq2 hq3 hd e) hX h3

theorem ggKGroupFusionAtFlat_uFourTwo
    (hSch : CFSG.LocalAnalysis.ComponentInitial.SchreierFor InCatalog)
    (hU : GGSeitzExcUFourTwoInput) : GGKGroupFusionAtFlat GGKFSeitzUFourTwo :=
  ggKGroupFusionAtFlat_of_solvable hSch
    fun _ _ ⟨hp, d, q, hi, hq2, hq1, hd⟩ K _ _ _ he _ hX h3 => by
      subst hp hi
      exact hU K d q hq2 hq1 hd he _ hX h3

section Marked


theorem ggKGroupFusionAtFlat_of_derived_card
    (hSch : CFSG.LocalAnalysis.ComponentInitial.SchreierFor InCatalog)
    {S : TauCeti.CFSGIndex → ℕ → Prop} (m : ℕ) (hm : m = 5616 ∨ m = 7800)
    (h : ∀ (i : TauCeti.CFSGIndex) (p : ℕ), S i p → ∀ (K : Type) [Group K] [Finite K],
      IsSimpleGroup K → Nonempty (K ≃* i.Group) →
        ∀ X : Subgroup K, X ≠ ⊤ → ¬ p ∣ X.index →
          Group.IsSolvable ↥X ∨
            (IsSimpleGroup ↥(commutator ↥X) ∧ Nat.card ↥(commutator ↥X) = m)) :
    GGKGroupFusionAtFlat S := by
  intro W _ _ p H E i hi hyp hL hKH he
  exfalso
  have hns := ggSeitzExc_not_isSolvable_flat hSch hyp hL
  rcases h i p hi _ hyp.2.1.1 he _ (ggSeitzExc_subgroupOf_ne_top hKH)
      (ggSeitzExc_not_dvd_index_flat hyp) with hsol | ⟨hs, hcard⟩
  · exact hns hsol
  obtain ⟨C, hC⟩ := ggExists_component_of_layer_ne_bot hL
  obtain ⟨eC⟩ := ggSeitzExc_quotComponent_equiv_flat hSch hyp hs hns hC
  have hCs : IsSimpleGroup ↥C := eC.isSimpleGroup
  have hXns : ¬ Group.IsSolvable ↥(commutator ↥(H.subgroupOf (CFSG.generalizedFitting W))) :=
    fun h' => hns (ggIsSolvable_of_commutator h')
  have hCns : ¬ Group.IsSolvable ↥C := fun h' =>
    hXns (Group.isSolvable_of_isSolvable_injective (f := eC.symm.toMonoidHom) eC.symm.injective)
  have hZ := ggCenter_eq_bot_of_not_isSolvable hCns
  have hcardC : Nat.card (↥C ⧸ Subgroup.center ↥C) = m := by
    rw [Nat.card_congr ((QuotientGroup.quotientMulEquivOfEq hZ).trans
      QuotientGroup.quotientBot).toEquiv, Nat.card_congr eC.toEquiv, hcard]
  obtain ⟨-, hmark⟩ := hyp.2.2.1 C hC
  obtain ⟨lab, -, hmod⟩ := largeEvenMarking_markedModel_centerQuot hmark
  have hne := ggMarkedModel_card_ne hmod
  rcases hm with rfl | rfl
  · exact hne.1 hcardC
  · exact hne.2 hcardC

theorem ggKGroupFusionAtFlat_titsThree
    (hSch : CFSG.LocalAnalysis.ComponentInitial.SchreierFor InCatalog)
    (hT : GGSeitzExcTitsThreeInput) : GGKGroupFusionAtFlat GGKFSeitzTitsThree :=
  ggKGroupFusionAtFlat_of_derived_card hSch 5616 (Or.inl rfl)
    fun _ _ ⟨hp, d, hi, hd⟩ K _ _ _ he _ hX h3 => by
      subst hp hi
      exact hT K d hd he _ hX h3

theorem ggKGroupFusionAtFlat_titsFive
    (hSch : CFSG.LocalAnalysis.ComponentInitial.SchreierFor InCatalog)
    (hT : GGSeitzExcTitsFiveInput) : GGKGroupFusionAtFlat GGKFSeitzTitsFive :=
  ggKGroupFusionAtFlat_of_derived_card hSch 7800 (Or.inr rfl)
    fun _ _ ⟨hp, d, hi, hd⟩ K _ _ _ he _ hX h5 => by
      subst hp hi
      exact hT K d hd he _ hX h5

theorem ggKGroupFusionAtFlat_szThirtyTwo
    (hSch : CFSG.LocalAnalysis.ComponentInitial.SchreierFor InCatalog) :
    GGKGroupFusionAtFlat GGKFSeitzSzThirtyTwo := by
  rintro W _ _ p H E i ⟨rfl, d, rfl, hd⟩ hyp hL hKH ⟨e⟩
  exfalso
  obtain ⟨C, hC⟩ := ggExists_component_of_layer_ne_bot hL
  obtain ⟨-, hmark⟩ := hyp.2.2.1 C hC
  obtain ⟨lab, -, R, _, I, F, θ, -, -, ⟨htag, -⟩, hmod⟩ :=
    largeEvenMarking_exists_markedModel hmark
  refine ggMarkedModel_not_dvd_szThirtyTwo htag hmod ?_
  rw [← Nat.card_congr θ.toEquiv, ← ggCard_szThirtyTwo d hd e]
  exact (Subgroup.card_quotient_dvd_card _).trans
    ((ggSeitzExc_card_quotComponent_dvd_flat hSch hyp hC).trans
      (Subgroup.card_subgroup_dvd_card _))

end Marked

theorem ggKGroupFusionAtFlat_spEightTwo
    (hSch : CFSG.LocalAnalysis.ComponentInitial.SchreierFor InCatalog)
    (hO : GGSeitzExcSpEightOvergroupInput) (hC : GGSeitzExcSpEightCentralizerInput) :
    GGKGroupFusionAtFlat GGKFSeitzSpEightTwo := by
  rintro W _ _ p H E i ⟨rfl, d, q, rfl, hq2, hq1, hd⟩ hyp hL hKH ⟨e⟩
  have hns := ggSeitzExc_not_isSolvable_flat hSch hyp hL
  have hXns : ¬ Group.IsSolvable ↥(commutator ↥(H.subgroupOf (CFSG.generalizedFitting W))) :=
    fun h => hns (ggIsSolvable_of_commutator h)
  obtain ⟨E', hE'el, hE'card, hD, hP⟩ := ggSeitzExc_transport_flat hyp
  have hD' : ggFixedClosure E' ≠ ⊤ := fun h =>
    ggSeitzExc_subgroupOf_ne_top hKH (top_le_iff.mp (h ▸ hD))
  obtain ⟨hs, hmod⟩ := hO _ d q hq2 hq1 hd ⟨e⟩ E' hE'el hE'card hD' _ hD
    (ggSeitzExc_subgroupOf_ne_top hKH) hns
  refine Or.inr (Or.inr (Or.inl ⟨hP (hC _ d q hq2 hq1 hd ⟨e⟩ E' hE'el hE'card hD'),
    Or.inl ⟨rfl, ggLieModel_symplectic_two d q hq2 hq1 4 (by norm_num) hd e, fun C hCc => ?_⟩⟩))
  obtain ⟨eC⟩ := ggSeitzExc_component_quot_equiv hs hXns hCc
  exact lieModel_of_mulEquiv' eC.symm hmod

theorem ggKGroupFusionAtFlat_spSixTwo
    (hSch : CFSG.LocalAnalysis.ComponentInitial.SchreierFor InCatalog)
    (hO : GGSeitzExcSpSixOvergroupInput) (hC : GGSeitzExcSpSixCentralizerInput) :
    GGKGroupFusionAtFlat GGKFSeitzSpSixTwo := by
  rintro W _ _ p H E i ⟨rfl, d, q, rfl, hq2, hq1, hd⟩ hyp hL hKH ⟨e⟩
  have hns := ggSeitzExc_not_isSolvable_flat hSch hyp hL
  have hXns : ¬ Group.IsSolvable ↥(commutator ↥(H.subgroupOf (CFSG.generalizedFitting W))) :=
    fun h => hns (ggIsSolvable_of_commutator h)
  obtain ⟨E', hE'el, hE'card, hD, hP⟩ := ggSeitzExc_transport_flat hyp
  have hD' : ggFixedClosure E' ≠ ⊤ := fun h =>
    ggSeitzExc_subgroupOf_ne_top hKH (top_le_iff.mp (h ▸ hD))
  rcases hO _ d q hq2 hq1 hd ⟨e⟩ _ (ggSeitzExc_subgroupOf_ne_top hKH)
      (ggSeitzExc_not_dvd_index_flat hyp) with hsol | ⟨hs, hmod⟩
  · exact absurd hsol hns
  refine Or.inr (Or.inr (Or.inl ⟨hP (hC _ d q hq2 hq1 hd ⟨e⟩ E' hE'el hE'card hD'),
    Or.inr (Or.inl ⟨rfl, ggLieModel_symplectic_two d q hq2 hq1 3 le_rfl hd e,
      fun C hCc => ?_⟩)⟩))
  obtain ⟨eC⟩ := ggSeitzExc_component_quot_equiv hs hXns hCc
  exact lieModel_of_mulEquiv' eC.symm hmod

theorem ggKGroupFusionAtFlat_lThreeFour
    (hSch : CFSG.LocalAnalysis.ComponentInitial.SchreierFor InCatalog)
    (hO : GGSeitzExcLThreeFourOvergroupInput) (hC : GGSeitzExcLThreeFourCentralizerInput) :
    GGKGroupFusionAtFlat GGKFSeitzLThreeFour := by
  rintro W _ _ p H E i ⟨rfl, d, q, rfl, hq2, hq3, hd⟩ hyp hL hKH ⟨e⟩
  have hns := ggSeitzExc_not_isSolvable_flat hSch hyp hL
  have hXns : ¬ Group.IsSolvable ↥(commutator ↥(H.subgroupOf (CFSG.generalizedFitting W))) :=
    fun h => hns (ggIsSolvable_of_commutator h)
  obtain ⟨E', hE'el, hE'card, -, hP⟩ := ggSeitzExc_transport_flat hyp
  rcases hO _ d q hq2 hq3 hd ⟨e⟩ _ (ggSeitzExc_subgroupOf_ne_top hKH)
      (ggSeitzExc_not_dvd_index_flat hyp) with hsol | ⟨hs, ⟨eA⟩⟩
  · exact absurd hsol hns
  refine Or.inr (Or.inr (Or.inl ⟨hP (hC _ d q hq2 hq3 hd ⟨e⟩ E' hE'el hE'card),
    Or.inr (Or.inr (Or.inl ⟨rfl, ggLieModel_lThreeFour d q hq2 hq3 hd e,
      fun C hCc => ?_⟩))⟩))
  obtain ⟨eC⟩ := ggSeitzExc_component_quot_equiv hs hXns hCc
  exact ⟨eC.trans eA⟩

end CFSG.StandardType
