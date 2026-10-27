module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.SeventeenFortyFour
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.SeventeenFortySix
public import CFSG.RankThree.PartTwo.Sec3.TwoThreeStructure

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17

open Subgroup CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem Ctx17_42.conjSubgroup_C_le {D : Data G} {V₀ V L X : Subgroup G} {p n l : ℕ}
    {C Dc : Subgroup G} {Gamma : Set G}
    (ctx : Ctx17_42 D V₀ V L X p n l C Dc Gamma) (γ : G) :
    CFSG.Quasithin.conjSubgroup C γ ≤ CFSG.Quasithin.conjSubgroup L γ := by
  simpa only [CFSG.Quasithin.conjSubgroup] using
    (Subgroup.map_mono (f := (MulAut.conj γ⁻¹).toMonoidHom) ctx.cartan.1)

theorem Ctx17_42.conjSubgroup_injOn_Gamma {D : Data G} {V₀ V L X : Subgroup G} {p n l : ℕ}
    {C Dc : Subgroup G} {Gamma : Set G}
    (ctx : Ctx17_42 D V₀ V L X p n l C Dc Gamma) :
    Set.InjOn (fun γ => CFSG.Quasithin.conjSubgroup L γ) Gamma := by
  intro γ hγ δ hδ heq
  have heq' : CFSG.Quasithin.conjSubgroup L γ = CFSG.Quasithin.conjSubgroup L δ := heq
  let K : Subgroup G := D.M ⊓ Subgroup.normalizer ((D.T ⊓ X : Subgroup G) : Set G)
  let H : Subgroup G := K ⊓ Subgroup.normalizer (L : Set G)
  have hγK : γ ∈ K := ctx.reps.1 hγ
  have hδK : δ ∈ K := ctx.reps.1 hδ
  have hmap : CFSG.Quasithin.conjSubgroup L (γ * δ⁻¹) = L := by
    calc CFSG.Quasithin.conjSubgroup L (γ * δ⁻¹)
        = CFSG.Quasithin.conjSubgroup (CFSG.Quasithin.conjSubgroup L γ) δ⁻¹ :=
          (CFSG.Quasithin.conjSubgroup_conjSubgroup L γ δ⁻¹).symm
      _ = CFSG.Quasithin.conjSubgroup (CFSG.Quasithin.conjSubgroup L δ) δ⁻¹ := by rw [heq']
      _ = CFSG.Quasithin.conjSubgroup L (δ * δ⁻¹) :=
          CFSG.Quasithin.conjSubgroup_conjSubgroup L δ δ⁻¹
      _ = L := by rw [mul_inv_cancel, CFSG.Quasithin.conjSubgroup_one]
  have hN : γ * δ⁻¹ ∈ Subgroup.normalizer (L : Set G) :=
    (CFSG.Quasithin.conjSubgroup_eq_iff_mem_normalizer).mp hmap
  have hK : γ * δ⁻¹ ∈ K := K.mul_mem hγK (K.inv_mem hδK)
  have hH : γ * δ⁻¹ ∈ H := Subgroup.mem_inf.mpr ⟨hK, hN⟩
  obtain ⟨γ₀, -, huniq⟩ := ctx.reps.2 γ hγK
  have hPγ : γ ∈ Gamma ∧ ∃ h ∈ H, γ = h * γ :=
    ⟨hγ, ⟨1, H.one_mem, by simp⟩⟩
  have hPδ : δ ∈ Gamma ∧ ∃ h ∈ H, γ = h * δ :=
    ⟨hδ, ⟨γ * δ⁻¹, hH, by group⟩⟩
  exact (huniq γ hPγ).trans (huniq δ hPδ).symm

theorem Ctx17_42.barImage_conjSubgroup_injOn_Gamma {D : Data G} {V₀ V L X : Subgroup G}
    {p n l : ℕ} {C Dc : Subgroup G} {Gamma : Set G}
    (ctx : Ctx17_42 D V₀ V L X p n l C Dc Gamma) :
    Set.InjOn (fun γ => barImage X (CFSG.Quasithin.conjSubgroup L γ)) Gamma := by
  classical
  intro γ hγ δ hδ heq
  have hmemγ : CFSG.Quasithin.conjSubgroup L γ ∈ conjSetOf D.M L :=
    ⟨γ⁻¹, D.M.inv_mem (ctx.reps.1 hγ).1, rfl⟩
  have hmemδ : CFSG.Quasithin.conjSubgroup L δ ∈ conjSetOf D.M L :=
    ⟨δ⁻¹, D.M.inv_mem (ctx.reps.1 hδ).1, rfl⟩
  have hcalCγ : CFSG.Quasithin.conjSubgroup L γ ∈ calC X :=
    mem_calC_of_mem_conjSetOf ctx hmemγ
  have hcalCδ : CFSG.Quasithin.conjSubgroup L δ ∈ calC X :=
    mem_calC_of_mem_conjSetOf ctx hmemδ
  have hcγ : CFSG.Quasithin.conjSubgroup L γ ∈ CFSG.Quasithin.cComp X :=
    uc22p20e_cComp_of_calC hcalCγ
  have hcδ : CFSG.Quasithin.conjSubgroup L δ ∈ CFSG.Quasithin.cComp X :=
    uc22p20e_cComp_of_calC hcalCδ
  have hsubγ : (CFSG.Quasithin.conjSubgroup L γ).subgroupOf X ∈
      CFSG.Quasithin.cComp (⊤ : Subgroup ↥X) :=
    CFSG.Quasithin.subgroupOf_mem_cComp hcγ
  have hsubδ : (CFSG.Quasithin.conjSubgroup L δ).subgroupOf X ∈
      CFSG.Quasithin.cComp (⊤ : Subgroup ↥X) :=
    CFSG.Quasithin.subgroupOf_mem_cComp hcδ
  have hbij := CFSG.Quasithin.cComp_quotient_bijOn (CFSG.pCore 2 ↥X)
    (uc22p20d_pCore_solvable X)
  have h1 : (CFSG.Quasithin.conjSubgroup L γ).subgroupOf X =
      (CFSG.Quasithin.conjSubgroup L δ).subgroupOf X := hbij.injOn hsubγ hsubδ heq
  have h2 : CFSG.Quasithin.conjSubgroup L γ ⊓ X =
      CFSG.Quasithin.conjSubgroup L δ ⊓ X := Subgroup.subgroupOf_inj.mp h1
  have h3 : CFSG.Quasithin.conjSubgroup L γ = CFSG.Quasithin.conjSubgroup L δ := by
    rwa [inf_eq_left.mpr (CFSG.Quasithin.le_of_mem_cComp hcγ),
      inf_eq_left.mpr (CFSG.Quasithin.le_of_mem_cComp hcδ)] at h2
  exact ctx.conjSubgroup_injOn_Gamma hγ hδ h3

theorem Ctx17_42.card_center_barImage_conjSubgroup {D : Data G} {V₀ V L X : Subgroup G}
    {p n l : ℕ} {C Dc : Subgroup G} {Gamma : Set G}
    (ctx : Ctx17_42 D V₀ V L X p n l C Dc Gamma) {γ : G} (hγ : γ ∈ Gamma) :
    Nat.card (Subgroup.center (barImage X (CFSG.Quasithin.conjSubgroup L γ))) =
      Nat.card (Subgroup.center (Bar2 L)) := by
  have hmem : CFSG.Quasithin.conjSubgroup L γ ∈ conjSetOf D.M L :=
    ⟨γ⁻¹, D.M.inv_mem (ctx.reps.1 hγ).1, rfl⟩
  have hcalC : CFSG.Quasithin.conjSubgroup L γ ∈ calC X :=
    mem_calC_of_mem_conjSetOf ctx hmem
  obtain ⟨e1⟩ := bar2_conj_equiv L γ⁻¹
  obtain ⟨e2⟩ := s13_bar_equiv hcalC
  exact (Nat.card_congr (Subgroup.centerCongr (e1.trans e2)).toEquiv).symm

theorem Ctx17_42.Dc_le_X {D : Data G} {V₀ V L X : Subgroup G} {p n l : ℕ} {C Dc : Subgroup G}
    {Gamma : Set G} (ctx : Ctx17_42 D V₀ V L X p n l C Dc Gamma) : Dc ≤ X := by
  rw [ctx.Dc_eq]
  refine iSup₂_le fun γ hγ => ?_
  have hmem : CFSG.Quasithin.conjSubgroup L γ ∈ conjSetOf D.M L :=
    ⟨γ⁻¹, D.M.inv_mem (ctx.reps.1 hγ).1, rfl⟩
  have hcalC : CFSG.Quasithin.conjSubgroup L γ ∈ calC X :=
    mem_calC_of_mem_conjSetOf ctx hmem
  exact (ctx.conjSubgroup_C_le γ).trans hcalC.1.le

theorem Ctx17_42.pRank_barImage_conjSubgroup_C {D : Data G} {V₀ V L X : Subgroup G} {p n l : ℕ}
    {C Dc : Subgroup G} {Gamma : Set G}
    (ctx : Ctx17_42 D V₀ V L X p n l C Dc Gamma) {γ : G} (hγ : γ ∈ Gamma) {r : ℕ}
    (hr : r.Prime) (hr2 : r ≠ 2) :
    CFSG.Open.pRank r (barImage X (CFSG.Quasithin.conjSubgroup C γ)) =
      CFSG.Open.pRank r C := by
  have hmem : CFSG.Quasithin.conjSubgroup L γ ∈ conjSetOf D.M L :=
    ⟨γ⁻¹, D.M.inv_mem (ctx.reps.1 hγ).1, rfl⟩
  have hcalC : CFSG.Quasithin.conjSubgroup L γ ∈ calC X :=
    mem_calC_of_mem_conjSetOf ctx hmem
  have hC_le_X : CFSG.Quasithin.conjSubgroup C γ ≤ X :=
    (ctx.conjSubgroup_C_le γ).trans hcalC.1.le
  have hcop : ¬ r ∣ Nat.card (CFSG.pCore 2 ↥X) :=
    CFSG.LocalAnalysis.SQTKTwoCoreQuotient.not_dvd_card_pCore_two hr hr2
  have hq := CFSG.PreuniquenessRankFour.Helpers.pRank_quotient_map_of_coprime_normal
    (source := ↥X) r hr (CFSG.pCore 2 ↥X) hcop
    (Subgroup.subgroupOf (CFSG.Quasithin.conjSubgroup C γ) X)
  have hsub : CFSG.Open.pRank r
        (Subgroup.subgroupOf (CFSG.Quasithin.conjSubgroup C γ) X) =
      CFSG.Open.pRank r (CFSG.Quasithin.conjSubgroup C γ) :=
    CFSG.HardMathSupport.Malle.OvergroupTransport.pRank_subgroupOf r hC_le_X
  calc CFSG.Open.pRank r (barImage X (CFSG.Quasithin.conjSubgroup C γ))
      = CFSG.Open.pRank r
          (Subgroup.subgroupOf (CFSG.Quasithin.conjSubgroup C γ) X) := hq
    _ = CFSG.Open.pRank r (CFSG.Quasithin.conjSubgroup C γ) := hsub
    _ = CFSG.Open.pRank r C := pRank_conjSubgroup_eq (C := C) (g := γ) hr

theorem Ctx17_42.pRank_barImage_Dc {D : Data G} {V₀ V L X : Subgroup G} {p n l : ℕ}
    {C Dc : Subgroup G} {Gamma : Set G} (ctx : Ctx17_42 D V₀ V L X p n l C Dc Gamma) {r : ℕ}
    (hr : r.Prime) (hr2 : r ≠ 2) :
    CFSG.Open.pRank r (barImage X Dc) = CFSG.Open.pRank r Dc := by
  have hcop : ¬ r ∣ Nat.card (CFSG.pCore 2 ↥X) :=
    CFSG.LocalAnalysis.SQTKTwoCoreQuotient.not_dvd_card_pCore_two hr hr2
  have hq := CFSG.PreuniquenessRankFour.Helpers.pRank_quotient_map_of_coprime_normal
    (source := ↥X) r hr (CFSG.pCore 2 ↥X) hcop (Subgroup.subgroupOf Dc X)
  have hsub : CFSG.Open.pRank r (Subgroup.subgroupOf Dc X) = CFSG.Open.pRank r Dc :=
    CFSG.HardMathSupport.Malle.OvergroupTransport.pRank_subgroupOf r (ctx.Dc_le_X)
  calc CFSG.Open.pRank r (barImage X Dc) =
        CFSG.Open.pRank r (Subgroup.subgroupOf Dc X) := hq
    _ = CFSG.Open.pRank r Dc := hsub

theorem Ctx17_42.ncard_mul_pRank_le_pRank_Dc {D : Data G} {V₀ V L X : Subgroup G} {p n l : ℕ}
    {C Dc : Subgroup G} {Gamma : Set G}
    (ctx : Ctx17_42 D V₀ V L X p n l C Dc Gamma) {r : ℕ} (hr : r.Prime) (hr2 : r ≠ 2)
    (hZ : ¬ r ∣ Nat.card (Subgroup.center (Bar2 L))) :
    Gamma.ncard * CFSG.Open.pRank r C ≤ CFSG.Open.pRank r Dc := by
  classical
  let K : G → Subgroup (Bar2 X) := fun γ => barImage X (CFSG.Quasithin.conjSubgroup L γ)
  have hΓfin : Gamma.Finite := Set.toFinite Gamma
  let s : Finset G := hΓfin.toFinset
  have hs : ∀ γ, γ ∈ s ↔ γ ∈ Gamma := fun γ => hΓfin.mem_toFinset
  have hscard : Gamma.ncard = s.card := Set.ncard_eq_toFinset_card Gamma hΓfin
  have hmemConj : ∀ γ ∈ Gamma, CFSG.Quasithin.conjSubgroup L γ ∈ conjSetOf D.M L := by
    intro γ hγ
    exact ⟨γ⁻¹, D.M.inv_mem (ctx.reps.1 hγ).1, rfl⟩
  have hcalC : ∀ γ ∈ Gamma, CFSG.Quasithin.conjSubgroup L γ ∈ calC X :=
    fun γ hγ => mem_calC_of_mem_conjSetOf ctx (hmemConj γ hγ)
  have hcomp : ∀ γ ∈ s, CFSG.IsComponent (K γ) := by
    intro γ hγ
    exact s13_barImage_isComponent (hcalC γ ((hs γ).mp hγ))
  let A : G → Subgroup (Bar2 X) := fun γ =>
    (CFSG.SectionRank.exists_pRank hr.one_lt
      (barImage X (CFSG.Quasithin.conjSubgroup C γ))).choose
  have hA_le : ∀ γ, A γ ≤ barImage X (CFSG.Quasithin.conjSubgroup C γ) := fun γ =>
    (CFSG.SectionRank.exists_pRank hr.one_lt
      (barImage X (CFSG.Quasithin.conjSubgroup C γ))).choose_spec.1
  have hA_el : ∀ γ, IsElemAbelian r (A γ) := fun γ =>
    (CFSG.SectionRank.exists_pRank hr.one_lt
      (barImage X (CFSG.Quasithin.conjSubgroup C γ))).choose_spec.2.1
  have hA_card : ∀ γ, Nat.card (A γ) =
      r ^ CFSG.Open.pRank r (barImage X (CFSG.Quasithin.conjSubgroup C γ)) := fun γ =>
    (CFSG.SectionRank.exists_pRank hr.one_lt
      (barImage X (CFSG.Quasithin.conjSubgroup C γ))).choose_spec.2.2
  have hA_pRank : ∀ γ ∈ s, CFSG.Open.pRank r (A γ) = CFSG.Open.pRank r C := by
    intro γ hγ
    have h1 : Nat.card (A γ) = r ^ CFSG.Open.pRank r (A γ) :=
      CFSG.GroupTheory.card_eq_pow_pRank_of_isElemAbelian hr (hA_el γ)
    have h2 : Nat.card (A γ) =
        r ^ CFSG.Open.pRank r (barImage X (CFSG.Quasithin.conjSubgroup C γ)) := hA_card γ
    have h3 : r ^ CFSG.Open.pRank r (A γ) =
        r ^ CFSG.Open.pRank r (barImage X (CFSG.Quasithin.conjSubgroup C γ)) :=
      h1.symm.trans h2
    have h4 : CFSG.Open.pRank r (A γ) =
        CFSG.Open.pRank r (barImage X (CFSG.Quasithin.conjSubgroup C γ)) :=
      Nat.pow_right_injective hr.two_le h3
    rw [h4, ctx.pRank_barImage_conjSubgroup_C ((hs γ).mp hγ) hr hr2]
  have hA_le_K : ∀ γ ∈ s, A γ ≤ K γ := by
    intro γ hγ
    exact (hA_le γ).trans
      (Subgroup.map_mono (Subgroup.subgroupOf_mono X (ctx.conjSubgroup_C_le γ)))
  have hZcenter : ∀ γ ∈ s, ¬ r ∣ Nat.card (Subgroup.center (K γ)) := by
    intro γ hγ
    have h := ctx.card_center_barImage_conjSubgroup ((hs γ).mp hγ)
    intro hdvd
    rw [h] at hdvd
    exact hZ hdvd
  have hdisj_center : ∀ γ ∈ s,
      A γ ⊓ (Subgroup.center (K γ)).map (K γ).subtype = ⊥ := by
    intro γ hγ
    have hZcard : ¬ r ∣ Nat.card ((Subgroup.center (K γ)).map (K γ).subtype) := by
      rw [Subgroup.card_map_of_injective (K γ).subtype_injective]
      exact hZcenter γ hγ
    haveI : Fact r.Prime := ⟨hr⟩
    have hEA : IsPGroup r (A γ) := (hA_el γ).isPGroup
    rw [inf_comm]
    exact disjoint_iff.mp (TauCeti.disjoint_of_not_dvd_natCard_of_isPGroup hZcard hEA)
  have hcomm : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → ∀ a ∈ A i, ∀ b ∈ A j, a * b = b * a := by
    intro i hi j hj hij a ha b hb
    have hKij : K i ≠ K j := by
      intro heq
      exact hij (ctx.barImage_conjSubgroup_injOn_Gamma ((hs i).mp hi) ((hs j).mp hj) heq)
    rcases CFSG.LocalCores.distinct_components_commute (hcomp i hi) (hcomp j hj) with
      heq | hcommut
    · exact absurd heq hKij
    · have hcent : K i ≤ Subgroup.centralizer (K j : Set (Bar2 X)) :=
        Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcommut
      exact (Subgroup.mem_centralizer_iff.mp (hcent (hA_le_K i hi ha)) b
        (hA_le_K j hj hb)).symm
  have hcentral : ∀ i ∈ s, A i ⊓ (⨆ j ∈ s.erase i, A j) = ⊥ := by
    intro i hi
    have hAleKi : A i ≤ K i := hA_le_K i hi
    have hBleCent : (⨆ j ∈ s.erase i, A j) ≤
        Subgroup.centralizer (K i : Set (Bar2 X)) := by
      refine iSup₂_le fun j hj => ?_
      have hji : j ≠ i := (Finset.mem_erase.mp hj).1
      have hcompj := hcomp j (Finset.mem_of_mem_erase hj)
      rcases CFSG.LocalCores.distinct_components_commute hcompj (hcomp i hi) with
        heq | hcommut
      · exact absurd (ctx.barImage_conjSubgroup_injOn_Gamma
          ((hs j).mp (Finset.mem_of_mem_erase hj)) ((hs i).mp hi) heq) hji
      · exact (hA_le_K j (Finset.mem_of_mem_erase hj)).trans
          (Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcommut)
    have hcenter_le : K i ⊓ Subgroup.centralizer (K i : Set (Bar2 X)) ≤
        (Subgroup.center (K i)).map (K i).subtype := by
      intro x hx
      refine Subgroup.mem_map.mpr ⟨⟨x, hx.1⟩, ?_, rfl⟩
      rw [Subgroup.mem_center_iff]
      intro y
      exact Subtype.ext (Subgroup.mem_centralizer_iff.mp hx.2 (y : Bar2 X) y.2)
    have hle : A i ⊓ (⨆ j ∈ s.erase i, A j) ≤
        A i ⊓ (Subgroup.center (K i)).map (K i).subtype :=
      le_inf inf_le_left ((inf_le_inf hAleKi hBleCent).trans hcenter_le)
    exact le_bot_iff.mp (hle.trans_eq (hdisj_center i hi))
  have hsum := (CFSG.LocalAnalysis.UniquenessCase.PartTwo.s13_pRank_iSup_eq_sum hr s A
    (fun i hi j hj hij a ha => Subgroup.mem_centralizer_iff.mpr fun b hb =>
      (hcomm i hi j hj hij a ha b hb).symm) hcentral).ge
  have hsum_eq : (∑ i ∈ s, CFSG.Open.pRank r (A i)) = s.card * CFSG.Open.pRank r C :=
    Finset.sum_const_nat (fun i hi => hA_pRank i hi)
  have hjoin_le : CFSG.Open.pRank r (⨆ i ∈ s, A i) ≤
      CFSG.Open.pRank r (barImage X Dc) := by
    refine CFSG.SectionRank.pRank_mono hr.one_lt (iSup₂_le fun i hi => ?_)
    have hCDc : CFSG.Quasithin.conjSubgroup C i ≤ Dc := by
      rw [ctx.Dc_eq]
      exact le_iSup₂_of_le i ((hs i).mp hi) le_rfl
    exact (hA_le i).trans (Subgroup.map_mono (Subgroup.subgroupOf_mono X hCDc))
  calc Gamma.ncard * CFSG.Open.pRank r C = s.card * CFSG.Open.pRank r C := by rw [hscard]
    _ = ∑ i ∈ s, CFSG.Open.pRank r (A i) := hsum_eq.symm
    _ ≤ CFSG.Open.pRank r (⨆ i ∈ s, A i) := hsum
    _ ≤ CFSG.Open.pRank r (barImage X Dc) := hjoin_le
    _ = CFSG.Open.pRank r Dc := ctx.pRank_barImage_Dc hr hr2

theorem Ctx17_42.ncard_le_pRank_Dc {D : Data G} {V₀ V L X : Subgroup G} {p n l : ℕ}
    {C Dc : Subgroup G} {Gamma : Set G}
    (ctx : Ctx17_42 D V₀ V L X p n l C Dc Gamma) {r : ℕ} (hr : r.Prime) (hr2 : r ≠ 2)
    (hZ : ¬ r ∣ Nat.card (Subgroup.center (Bar2 L))) (hC : 1 ≤ CFSG.Open.pRank r C) :
    Gamma.ncard ≤ CFSG.Open.pRank r Dc := by
  calc Gamma.ncard = Gamma.ncard * 1 := (Nat.mul_one _).symm
    _ ≤ Gamma.ncard * CFSG.Open.pRank r C := Nat.mul_le_mul_left _ hC
    _ ≤ CFSG.Open.pRank r Dc := ctx.ncard_mul_pRank_le_pRank_Dc hr hr2 hZ

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17
