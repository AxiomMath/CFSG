module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenG2DerivedQuotient
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenComponentKernelFixers
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSimpleComponentRank
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightKQuotFix
public import CFSG.Quasithin.EmptyFaithful.S153G93DCovG2

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {G : Type} [Group G] [Finite G] {D : Data G} {V₀ V L : Subgroup G}
  {hV : IsElemAbelian 2 V}

theorem s168e3_false_of_g2_component_of_s1
    (c : S168e3Ctx D V₀ V L hV)
    (hcomp : CFSG.Open.IsComponentOf (lBar V₀ V hV L) (Mbar D.M V₀ V hV))
    (hN : G2NaturalDerived (lBar V₀ V hV L)
      (commSub ⊤ (lBar V₀ V hV L))
      (commSub ⊤ (lBar V₀ V hV L) ⊓ fixV (lBar V₀ V hV L)) 1)
    (hs : s15 D.M V₀ V hV L = 1) : False := by
  classical
  let W : Type := Vtil V₀ V hV
  let H : Subgroup (MulAut W) := lBar V₀ V hV L
  have hPSU : IsPSU 3 3 1 ↥H := s168e3_g2_isPSU hN
  have hsimple : IsSimpleGroup ↥H :=
    CFSG.Open.StatedAPI.isSimpleGroup_of_statedClassicalModel hPSU
  obtain ⟨Q, hQc, hQf, q, ρ, hqsurj, hqker, hρinj, heq, hNq, hcentH, hRanks, hsig, hM3,
    hbar3⟩ := s168e3_g2_quotient_data c hcomp hN hs
  obtain ⟨ψ, hψ⟩ := exists_barLift_of_hyp125 c.setting.hyp16.hyp125
  have hQnt : Nontrivial Q := by
    by_contra hnt
    rw [not_nontrivial_iff_subsingleton] at hnt
    have hsub : Subsingleton (MulAut Q) := ⟨fun a b => by
      ext x
      exact hnt.elim ((a : Q ≃* Q) x) ((b : Q ≃* Q) x)⟩
    obtain ⟨a, b, hab⟩ := hsimple.toNontrivial.exists_pair_ne
    have h1 : ρ a = ρ b := hsub.elim _ _
    exact hab (hρinj h1)
  obtain ⟨w0, hw0⟩ := exists_ne (1 : Q)
  have hcov : CFSG.Quasithin.S153G93D.CovOrder3 ρ.range :=
    CFSG.Quasithin.S153G93D.CovG2.covG2Der_holds (W := Q) (J := ρ.range) hNq
  have hfixH : ∀ x : W, x ≠ 1 →
      ∃ bH : MulAut W, bH ∈ H ∧ orderOf bH = 3 ∧ bH x = x := by
    intro x hx
    obtain ⟨y, hyH, hyord, hyfix⟩ :=
      s16k_transport_fix_ord_quot Nat.prime_three (by norm_num) hqsurj hqker hρinj heq
        ⟨w0, hw0⟩ hcov x hx
    exact ⟨y, hyH, hyord, hyfix⟩
  obtain ⟨K, hKcal, hKbar, ⟨eK⟩⟩ :=
    exists_calC_cover_of_simple_component c.setting.hyp16.hyp125 c.std.h127 c.std.h119
      hcomp hsimple
  let C : Subgroup (Bar2 D.M) := UC22.barImage D.M K
  have hCcomp : CFSG.IsComponent C := UC22.uc22p22l_barImage_isComponent hKcal
  have hCq : CFSG.Open.IsQuasisimple ↥C :=
    CFSG.Quasithin.A3.isQuasisimple_iff_open.mp hCcomp.1
  obtain ⟨eBar, -⟩ := uc22p22l_barImage_equiv hKcal
  have hcenterImage : (Subgroup.center (Bar2 K)).map eBar.toMonoidHom =
      Subgroup.center C := CFSG.ASVolI.ChA.map_center_equiv eBar
  have eCquot : (C ⧸ Subgroup.center C) ≃* ↥H :=
    ((QuotientGroup.congr (Subgroup.center (Bar2 K)) (Subgroup.center C) eBar
      hcenterImage).symm).trans eK
  have hcenterC : Subgroup.center C = ⊥ :=
    s168e3_center_eq_bot_of_cover hPSU hCq eCquot
  have himageC : C.map ψ = H :=
    barImage_map_eq_of_mem_calC c.setting.hyp16.hyp125 hKcal hKbar ψ hψ
  let f : C →* MulAut W := ψ.comp C.subtype
  have hfker : f.ker = Subgroup.center C :=
    ker_comp_subtype_eq_center_of_mem_calC c.setting.hyp16.hyp125 hKcal hKbar hsimple ψ hψ
  have hinj : Function.Injective (ψ.comp C.subtype) := by
    apply (MonoidHom.ker_eq_bot_iff f).mp
    rw [hfker, hcenterC]
  have hψeq : ψ.comp (QuotientGroup.mk' (CFSG.pCore 2 ↥D.M)) =
      barHom V₀ V hV c.m_le_stabTil := by
    ext b x
    change ψ (QuotientGroup.mk b) x =
      (actTil V₀ V hV) ⟨(b : G), c.m_le_stabTil b.2⟩ x
    rw [hψ b]
  have hrangeψ : ψ.range = Mbar D.M V₀ V hV := by
    show ψ.range = barSub V₀ V hV D.M
    rw [← range_barHom V₀ V hV c.m_le_stabTil]
    ext y
    constructor
    · rintro ⟨x, rfl⟩
      obtain ⟨m, rfl⟩ := QuotientGroup.mk_surjective x
      exact ⟨m, (hψ m).symm⟩
    · rintro ⟨m, rfl⟩
      exact ⟨QuotientGroup.mk m, hψ m⟩
  have hfix : ∀ w : W, w ≠ 1 → ∃ b ∈ C.map ψ, orderOf b = 3 ∧ b w = w := by
    intro w hw
    obtain ⟨bH, hbHmem, hbHord, hbHfix⟩ := hfixH w hw
    exact ⟨bH, by rw [himageC]; exact hbHmem, hbHord, hbHfix⟩
  exact s168e3_false_of_faithful_component_fixers c
    (by rw [hsig]; exact Set.mem_singleton 3) ψ hψeq C hCcomp hinj
    (by rw [hrangeψ]; exact hRanks) hfix

theorem s168e3_false_of_g2_component
    (c : S168e3Ctx D V₀ V L hV)
    (hcomp : CFSG.Open.IsComponentOf (lBar V₀ V hV L) (Mbar D.M V₀ V hV))
    (hN : G2NaturalDerived (lBar V₀ V hV L)
      (commSub ⊤ (lBar V₀ V hV L))
      (commSub ⊤ (lBar V₀ V hV L) ⊓ fixV (lBar V₀ V hV L)) 1) : False := by
  let H : Subgroup (MulAut (Vtil V₀ V hV)) := lBar V₀ V hV L
  have hPSU : IsPSU 3 3 1 ↥H := s168e3_g2_isPSU hN
  have hsimple : IsSimpleGroup ↥H :=
    CFSG.Open.StatedAPI.isSimpleGroup_of_statedClassicalModel hPSU
  have hs : s15 D.M V₀ V hV L = 1 :=
    s15_eq_one_of_simple_component_of_two_rank_centerbot c hcomp hsimple
      (by rw [CFSG.Quasithin.pRank_three_psu33 hPSU])
      (fun Q _ _ hq he => s168e3_center_eq_bot_of_cover hPSU hq he.some)
  exact s168e3_false_of_g2_component_of_s1 c hcomp hN hs

theorem s168e3_concl163F_of_g2_component
    (c : S168e3Ctx D V₀ V L hV)
    (hcomp : CFSG.Open.IsComponentOf (lBar V₀ V hV L) (Mbar D.M V₀ V hV))
    (hN : G2NaturalDerived (lBar V₀ V hV L)
      (commSub ⊤ (lBar V₀ V hV L))
      (commSub ⊤ (lBar V₀ V hV L) ⊓ fixV (lBar V₀ V hV L)) 1) :
    Concl163F D V₀ V hV L :=
  (s168e3_false_of_g2_component c hcomp hN).elim

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
