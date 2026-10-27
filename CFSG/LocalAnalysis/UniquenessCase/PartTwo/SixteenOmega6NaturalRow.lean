module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC1677ThreeSig
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC1677ThreeStar
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightKStarNat
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenFixedQuotientCentralizer
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC1SchurU4
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenKAutRank
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSimpleComponentRank
public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81TwelveLeU42O8U42
public import CFSG.Quasithin.Vol2.GoldschmidtF431U42Model

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {G : Type} [Group G] [Finite G] {D : Data G} {V₀ V L : Subgroup G}
  {hV : IsElemAbelian 2 V}

theorem case153_1_of_omega_minus_six_natural
    {G : Type} [Group G] [Finite G]
    {D : Data G} {V₀ V L : Subgroup G} {hV : IsElemAbelian 2 V}
    (c : S168e3Ctx D V₀ V L hV)
    (hcomp : IsComponentOf (lBar V₀ V hV L) (Mbar D.M V₀ V hV))
    (hOm : IsOmegaMinus ↥(lBar V₀ V hV L) 6 1)
    (hNat : NatOmegaMinus (lBar V₀ V hV L)
      (commSub (⊤ : Subgroup (Vtil V₀ V hV)) (lBar V₀ V hV L))
      (commSub (⊤ : Subgroup (Vtil V₀ V hV)) (lBar V₀ V hV L) ⊓
        fixV (lBar V₀ V hV L)) 6 1) :
    Case153_1 D V₀ V hV L := by
  classical
  have hU4 : IsU4 ↥(lBar V₀ V hV L) 1 := isU4_of_isOmegaMinus_six hOm
  have hsimple : IsSimpleGroup ↥(lBar V₀ V hV L) :=
    CFSG.Quasithin.H13.F431.U42.isSimpleGroup_of_lieModel_PSU_four_two hU4
  have hrank : 3 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup ↥(lBar V₀ V hV L)) := by
    obtain ⟨F, hF, hFcard⟩ :=
      CFSG.LocalAnalysis.RankThreeTheoremC.TwelveLe.U42O8.UFourTwo.exists_isElemAbelian_card_27
        (X := ↥(lBar V₀ V hV L)) hU4
    exact CFSG.SectionRank.le_pRank (p := 3) (k := 3) (by norm_num) le_top hF
      (by rw [hFcard]; norm_num)
  have hcover : ∀ (Q : Type) [Group Q] [Finite Q], CFSG.Open.IsQuasisimple Q →
      Nonempty ((Q ⧸ Subgroup.center Q) ≃* ↥(lBar V₀ V hV L)) →
      IsPGroup 2 ↥(Subgroup.center Q) := by
    intro Q _ _ hQ ⟨e⟩
    have hU4Q : IsU4 (Q ⧸ Subgroup.center Q) 1 :=
      CFSG.Blueprint.LieModel.of_mulEquiv e.symm hU4
    have hdvd : Nat.card (Subgroup.center Q) ∣ 2 := rSchurOm6_holds Q hQ hU4Q
    rcases (Nat.dvd_prime Nat.prime_two).1 hdvd with h1 | h1
    · exact IsPGroup.of_card (p := 2) (n := 0) (by rw [h1]; norm_num)
    · exact IsPGroup.of_card (p := 2) (n := 1) (by rw [h1]; norm_num)
  have hs : s15 D.M V₀ V hV L = 1 :=
    s15_eq_one_of_simple_component_of_three_rank c hcomp hsimple (r := 3) (by norm_num) hrank
      hcover
  have hcomm : commSub (⊤ : Subgroup (Vtil V₀ V hV)) (lBar V₀ V hV L) = ⊤ := by
    simpa only [wTil, lBar] using wTil_eq_top_of_case163_2 c.conc hs
  have hstar : wStar D.M V₀ V hV L = ⊤ :=
    s15_Three_wStar_eq_top D c.std.h1217 c.setting.hyp151 hV c.ne hs
  obtain ⟨q, θ, hq, heq, hker⟩ := s168e3_star c hs
  have hNat' : NatOmegaMinus (lBar V₀ V hV L) (⊤ : Subgroup (Vtil V₀ V hV))
      (fixV (lBar V₀ V hV L)) 6 1 := by
    simpa only [hcomm, top_inf_eq] using hNat
  have hNatQ : NatOmegaMinus (lStar D.M V₀ V hV L)
      (⊤ : Subgroup (vStar D.M V₀ V hV L)) ⊥ 6 1 := by
    have h := s16k_natOmegaMinus_map (H := lBar V₀ V hV L)
      (H' := lStar D.M V₀ V hV L) hNat' q hker θ.toMonoidHom θ.surjective heq
    simpa only [Subgroup.map_top_of_surjective q hq] using h
  have hNatStar : NatOmegaMinus (lStar D.M V₀ V hV L) (wStar D.M V₀ V hV L) ⊥ 6 1 := by
    simpa only [hstar] using hNatQ
  let rho : ↥(lBar V₀ V hV L) →* MulAut (vStar D.M V₀ V hV L) :=
    (lStar D.M V₀ V hV L).subtype.comp θ.toMonoidHom
  have hrho : rho.range = lStar D.M V₀ V hV L := by
    ext x
    constructor
    · rintro ⟨h, rfl⟩
      exact (θ h).2
    · intro hx
      obtain ⟨h, hh⟩ := θ.surjective ⟨x, hx⟩
      exact ⟨h, congrArg Subtype.val hh⟩
  have hker_iff : ∀ w : Vtil V₀ V hV, q w = 1 ↔ w ∈ fixV (lBar V₀ V hV L) := by
    intro w
    rw [← MonoidHom.mem_ker, hker]
  have hn : ∀ a ∈ Subgroup.centralizer (rho.range : Set (MulAut (vStar D.M V₀ V hV L))),
      a ^ 1 = 1 := by
    intro a ha
    rw [pow_one]
    refine natOmegaMinus_centralizer_eq_one (H := lStar D.M V₀ V hV L) hNatQ (x := a) ?_
    intro φ hφ
    have ha' : a ∈ Subgroup.centralizer
        (lStar D.M V₀ V hV L : Set (MulAut (vStar D.M V₀ V hV L))) := by
      rwa [hrho] at ha
    exact (Subgroup.mem_centralizer_iff.mp ha' φ hφ).symm
  have hcent : ∀ a ∈ Subgroup.centralizer
      (lBar V₀ V hV L : Set (MulAut (Vtil V₀ V hV))), a = 1 := by
    intro a ha
    have h := centralizer_pow_eq_one_of_fixed_quotient (H := lBar V₀ V hV L) (n := 1)
      q rho hq hker_iff heq hcomm hn a ha
    simpa using h
  have hHA : lBar V₀ V hV L ≤ Mbar D.M V₀ V hV := hcomp.1
  have hAnorm : Mbar D.M V₀ V hV ≤ Subgroup.normalizer
      (lBar V₀ V hV L : Set (MulAut (Vtil V₀ V hV))) := by
    intro g hg
    exact Subgroup.mem_normalizer_iff_map_conj_eq.2 (lBar_conj_eq_of_s15_eq_one hs hg)
  let f : ↥(lBar V₀ V hV L) →* ↥(Mbar D.M V₀ V hV) := Subgroup.inclusion hHA
  have hf : Function.Injective f := Subgroup.inclusion_injective hHA
  have hfn : f.range.Normal := by
    change (Subgroup.inclusion hHA).range.Normal
    rw [Subgroup.inclusion_range hHA]
    exact Subgroup.normal_subgroupOf_of_le_normalizer hAnorm
  have hc : ∀ h : ↥(Mbar D.M V₀ V hV),
      (∀ s : ↥(lBar V₀ V hV L), h * f s = f s * h) → h = 1 := by
    intro h hh
    have hmem : (h : MulAut (Vtil V₀ V hV)) ∈
        Subgroup.centralizer (lBar V₀ V hV L : Set (MulAut (Vtil V₀ V hV))) := by
      rw [Subgroup.mem_centralizer_iff]
      intro s hs
      have hs' := congrArg (fun z : ↥(Mbar D.M V₀ V hV) =>
        (z : MulAut (Vtil V₀ V hV))) (hh ⟨s, hs⟩)
      simpa [f] using hs'.symm
    have h1 := hcent (h : MulAut (Vtil V₀ V hV)) hmem
    exact Subtype.ext (by simpa using h1)
  have hfour := (rAutRank153_holds (S := ↥(lBar V₀ V hV L))
    (H := ↥(Mbar D.M V₀ V hV)) f hf hfn hc).2 (Or.inl hOm)
  have hrankA : ∀ p : ℕ, p.Prime → p ≠ 2 → p ≠ 3 →
      CFSG.Open.pRank p (Mbar D.M V₀ V hV) ≤ 1 := by
    intro p hp hp2 hp3
    simpa only [CFSG.SectionRank.pRank_eq_pRank_top_subgroup (p := p)
      (Mbar D.M V₀ V hV)] using hfour.1 p hp hp2 hp3
  have hsig : D.sig = {3} := by
    refine c.sig_eq_singleton_of_pRank_lt_two 3 (fun q hq hq2 hq3 => ?_)
    have h := hrankA q hq hq2 hq3
    omega
  have hrank3 : CFSG.Open.pRank 3 D.M = 3 :=
    c.std.pRank_eq_three (p := 3) (by rw [hsig]; exact Set.mem_singleton 3)
  exact ⟨hOm, hNatStar, hsig, hrank3, hs, c.setting.hyp16.small⟩

theorem concl163F_of_omega_minus_six_natural
    {G : Type} [Group G] [Finite G]
    {D : Data G} {V₀ V L : Subgroup G} {hV : IsElemAbelian 2 V}
    (c : S168e3Ctx D V₀ V L hV)
    (hcomp : IsComponentOf (lBar V₀ V hV L) (Mbar D.M V₀ V hV))
    (hOm : IsOmegaMinus ↥(lBar V₀ V hV L) 6 1)
    (hNat : NatOmegaMinus (lBar V₀ V hV L)
      (commSub (⊤ : Subgroup (Vtil V₀ V hV)) (lBar V₀ V hV L))
      (commSub (⊤ : Subgroup (Vtil V₀ V hV)) (lBar V₀ V hV L) ⊓
        fixV (lBar V₀ V hV L)) 6 1) :
    Concl163F D V₀ V hV L :=
  Or.inl (Or.inl (Or.inl
    (case153_1_of_omega_minus_six_natural c hcomp hOm hNat)))

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
