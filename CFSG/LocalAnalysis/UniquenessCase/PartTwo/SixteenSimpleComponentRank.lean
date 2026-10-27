module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC1677ThreeDefs
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.ExceptionalComponentCover
public import CFSG.LocalAnalysis.AGLEmbedding.RankTools
public import CFSG.Quasithin.EmptyFaithful.R3cBase
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC165ExclDirect
public import CFSG.Quasithin.EmptyFaithful.S1422Basic

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {G : Type} [Group G] [Finite G] {D : Data G} {V₀ V L : Subgroup G}
  {hV : IsElemAbelian 2 V}

theorem s15_eq_one_of_simple_component_of_three_rank
    (c : S168e3Ctx D V₀ V L hV)
    (hcomp : IsComponentOf (lBar V₀ V hV L) (Mbar D.M V₀ V hV))
    (hsimple : IsSimpleGroup ↥(lBar V₀ V hV L))
    {r : ℕ} (hlarge : 3 < r + r)
    (hrank : r ≤ CFSG.Open.pRank 3 (⊤ : Subgroup ↥(lBar V₀ V hV L)))
    (hcover : ∀ (Q : Type) [Group Q] [Finite Q], CFSG.Open.IsQuasisimple Q →
      Nonempty ((Q ⧸ Subgroup.center Q) ≃* ↥(lBar V₀ V hV L)) →
      IsPGroup 2 ↥(Subgroup.center Q)) :
    s15 D.M V₀ V hV L = 1 := by
  classical
  by_contra hsne
  have hs1 : 1 ≤ s15 D.M V₀ V hV L := Om8Excl.one_le_s15 D.M V₀ V hV L
  have hs2 : 2 ≤ s15 D.M V₀ V hV L := by omega
  let S : Set (Subgroup (MulAut (Vtil V₀ V hV))) :=
    {X | ∃ φ ∈ Mbar D.M V₀ V hV,
      X = (barSub V₀ V hV L).map (MulAut.conj φ).toMonoidHom}
  have hS : 1 < S.ncard := by
    simpa only [S, s15] using (show 1 < s15 D.M V₀ V hV L by omega)
  obtain ⟨X, hXmem, hXne⟩ := Set.exists_ne_of_one_lt_ncard hS (lBar V₀ V hV L)
  obtain ⟨φ, hφM, hXeq⟩ := hXmem
  have hcompA : CFSG.Assembly.IsComponentOf (lBar V₀ V hV L) (Mbar D.M V₀ V hV) :=
    CFSG.Assembly.isComponentOf_iff_open.mpr hcomp
  have hMbarConj : (Mbar D.M V₀ V hV).map (MulAut.conj φ).toMonoidHom =
      Mbar D.M V₀ V hV :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp (Subgroup.le_normalizer hφM)
  have hcompX : CFSG.Open.IsComponentOf X (Mbar D.M V₀ V hV) := by
    rw [hXeq]
    have h := CFSG.LocalAnalysis.ComponentInitial.isComponentOf_map_conj hcompA φ
    rw [hMbarConj] at h
    exact CFSG.Assembly.isComponentOf_iff_open.mp h
  have hconjEquiv : ↥(lBar V₀ V hV L) ≃* ↥((lBar V₀ V hV L).map
      (MulAut.conj φ).toMonoidHom) :=
    Subgroup.equivMapOfInjective (lBar V₀ V hV L) (MulAut.conj φ).toMonoidHom
      (MulAut.conj φ).injective
  have hsimpleX : IsSimpleGroup ↥X := by
    rw [hXeq]
    exact hconjEquiv.symm.isSimpleGroup_congr.mpr hsimple
  have eHX : ↥X ≃* ↥(lBar V₀ V hV L) := hXeq ▸ hconjEquiv.symm
  have hrankX : r ≤ CFSG.Open.pRank 3 (⊤ : Subgroup ↥X) := by
    rw [hXeq]
    calc r ≤ CFSG.Open.pRank 3 (⊤ : Subgroup ↥(lBar V₀ V hV L)) := hrank
      _ = CFSG.Open.pRank 3 (⊤ : Subgroup ↥((lBar V₀ V hV L).map
            (MulAut.conj φ).toMonoidHom)) :=
          CFSG.SectionRank.pRank_top_eq_of_mulEquiv (p := 3) (by norm_num) hconjEquiv
  obtain ⟨K, hKcal, hKbar, -⟩ :=
    exists_calC_cover_of_simple_component (D := D) (V₀ := V₀) (V := V) (hV := hV)
      c.setting.hyp16.hyp125 c.std.h127 c.std.h119 hcomp hsimple
  obtain ⟨K', hK'cal, hK'bar, -⟩ :=
    exists_calC_cover_of_simple_component (D := D) (V₀ := V₀) (V := V) (hV := hV)
      c.setting.hyp16.hyp125 c.std.h127 c.std.h119 hcompX hsimpleX
  obtain ⟨ψ, hψ⟩ := exists_barLift_of_hyp125 c.setting.hyp16.hyp125
  let C : Subgroup (Bar2 D.M) := UC22.barImage D.M K
  let C' : Subgroup (Bar2 D.M) := UC22.barImage D.M K'
  have hCcomp : CFSG.IsComponent C := UC22.uc22p22l_barImage_isComponent hKcal
  have hC'comp : CFSG.IsComponent C' := UC22.uc22p22l_barImage_isComponent hK'cal
  have hCne : C ≠ C' := by
    intro heq
    have himageC : C.map ψ = lBar V₀ V hV L :=
      barImage_map_eq_of_mem_calC c.setting.hyp16.hyp125 hKcal hKbar ψ hψ
    have himageC' : C'.map ψ = X :=
      barImage_map_eq_of_mem_calC c.setting.hyp16.hyp125 hK'cal hK'bar ψ hψ
    have hmap : C.map ψ = C'.map ψ := congrArg (fun E => E.map ψ) heq
    rw [himageC, himageC'] at hmap
    exact hXne hmap.symm
  have component_data : ∀ {K : Subgroup G} (hK : K ∈ calC D.M)
      {H' : Subgroup (MulAut (Vtil V₀ V hV))} (hbar : barSub V₀ V hV K = H')
      (hsimpleH' : IsSimpleGroup ↥H') (eH : ↥H' ≃* ↥(lBar V₀ V hV L))
      (hrH : r ≤ CFSG.Open.pRank 3 (⊤ : Subgroup ↥H')),
      r ≤ CFSG.Open.pRank 3 (UC22.barImage D.M K) ∧
        IsPGroup 2 ↥(Subgroup.center (UC22.barImage D.M K)) := by
    intro K hK H' hbar hsimpleH' eH hrH
    let E : Subgroup (Bar2 D.M) := UC22.barImage D.M K
    have hEcomp : CFSG.IsComponent E := UC22.uc22p22l_barImage_isComponent hK
    have himage : E.map ψ = H' :=
      barImage_map_eq_of_mem_calC c.setting.hyp16.hyp125 hK hbar ψ hψ
    let f : E →* MulAut (Vtil V₀ V hV) := ψ.comp E.subtype
    have hfker : f.ker = Subgroup.center E :=
      ker_comp_subtype_eq_center_of_mem_calC c.setting.hyp16.hyp125 hK hbar hsimpleH' ψ hψ
    have hfrange : f.range = H' := by
      rw [show f.range = E.map ψ from by
        ext y
        constructor
        · rintro ⟨x, rfl⟩
          exact Subgroup.mem_map.mpr ⟨(x : Bar2 D.M), x.2, rfl⟩
        · intro hy
          obtain ⟨e, he, heψ⟩ := Subgroup.mem_map.mp hy
          exact ⟨⟨e, he⟩, heψ⟩]
      exact himage
    have hEquot : (E ⧸ Subgroup.center E) ≃* ↥H' := by
      have h' : E ⧸ f.ker ≃* ↥H' := by
        have h := QuotientGroup.quotientKerEquivRange f
        rw [hfrange] at h
        exact h
      exact (QuotientGroup.quotientMulEquivOfEq hfker).symm.trans h'
    have hqE : CFSG.Open.IsQuasisimple ↥E :=
      (CFSG.Quasithin.A3.isQuasisimple_iff_open (Q := ↥E)).mp hEcomp.1
    have hEquotL : (E ⧸ Subgroup.center E) ≃* ↥(lBar V₀ V hV L) := hEquot.trans eH
    have hcenterP : IsPGroup 2 ↥(Subgroup.center E) :=
      hcover ↥E hqE ⟨hEquotL⟩
    have hquotRank : r ≤ CFSG.Open.pRank 3
        (⊤ : Subgroup (E ⧸ Subgroup.center E)) := by
      rw [CFSG.SectionRank.pRank_top_eq_of_mulEquiv (p := 3) (by norm_num) hEquot]
      exact hrH
    have htopEq : CFSG.Open.pRank 3 (⊤ : Subgroup (E ⧸ Subgroup.center E)) =
        CFSG.Open.pRank 3 (⊤ : Subgroup E) :=
      CFSG.SectionRank.pRank_quotient_two_group (Subgroup.center E) hcenterP
        Nat.prime_three (by norm_num)
    have hEtop : r ≤ CFSG.Open.pRank 3 (⊤ : Subgroup E) := by
      rwa [htopEq] at hquotRank
    refine ⟨?_, hcenterP⟩
    change r ≤ CFSG.Open.pRank 3 E
    rw [CFSG.SectionRank.pRank_eq_pRank_top_subgroup (p := 3) E]
    exact hEtop
  have hCdata := component_data hKcal hKbar hsimple (MulEquiv.refl _) hrank
  have hC'data := component_data hK'cal hK'bar hsimpleX eHX hrankX
  have hCrank : r ≤ CFSG.Open.pRank 3 C := hCdata.1
  have hC'rank : r ≤ CFSG.Open.pRank 3 C' := hC'data.1
  have hcenterC : IsPGroup 2 ↥(Subgroup.center C) := hCdata.2
  have hcommC : C ≤ Subgroup.centralizer (C' : Set (Bar2 D.M)) :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.mp
      ((CFSG.LocalCores.distinct_components_commute hCcomp hC'comp).resolve_left hCne)
  have hinf_le_center : (C ⊓ C').subgroupOf C ≤ Subgroup.center C := by
    intro x hx
    rw [Subgroup.mem_subgroupOf] at hx
    rw [Subgroup.mem_center_iff]
    intro cc
    apply Subtype.ext
    exact (Subgroup.mem_centralizer_iff.mp (hcommC cc.2) (x : Bar2 D.M)
      (Subgroup.mem_inf.mp hx).2).symm
  have hPinf : IsPGroup 2 ↥((C ⊓ C').subgroupOf C) := hcenterC.to_le hinf_le_center
  have hcardSubEq : Nat.card ↥((C ⊓ C').subgroupOf C) = Nat.card ↥(C ⊓ C') :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe (H := C ⊓ C') (K := C) inf_le_left).toEquiv
  have hcop : Nat.Coprime 3 (Nat.card ↥(C ⊓ C')) := by
    obtain ⟨k, hk⟩ := hPinf.exists_card_eq
    rw [← hcardSubEq, hk]
    exact Nat.Coprime.pow_right k ((Nat.coprime_primes Nat.prime_three Nat.prime_two).2
      (by norm_num))
  have hcommute : ∀ x ∈ C, ∀ y ∈ C', x * y = y * x := by
    intro x hx y hy
    exact (Subgroup.mem_centralizer_iff.mp (hcommC hx) y hy).symm
  have hadd := CFSG.AGLEmbedding.pRank_add_le_pRank_sup_of_coprime
    (q := 3) Nat.prime_three hcommute hcop
  have hsup : r + r ≤ CFSG.Open.pRank 3 (C ⊔ C') :=
    (add_le_add hCrank hC'rank).trans hadd
  have htop : CFSG.Open.pRank 3 (C ⊔ C') ≤
      CFSG.Open.pRank 3 (⊤ : Subgroup (Bar2 D.M)) :=
    CFSG.SectionRank.pRank_mono (p := 3) (by norm_num) le_top
  have hbar : r + r ≤ CFSG.Open.pRank 3 (⊤ : Subgroup (Bar2 D.M)) := hsup.trans htop
  have hM : r + r ≤ CFSG.Open.pRank 3 D.M := by
    rw [CFSG.Quasithin.R3c.pRank_three_eq_pCore_quotient D.M]
    exact hbar
  have hbound : CFSG.Open.pRank 3 D.M ≤ CFSG.Open.evenRank G :=
    CFSG.RankThreeCoreUniqueness.Helpers.local_pRank_le_evenRank 3 Nat.prime_three
      (by norm_num) D.M D.maxLocal.1
  have h3 : CFSG.Open.evenRank G = 3 := c.std.h3
  omega

theorem s15_eq_one_of_simple_component_of_two_rank_centerbot
    (c : S168e3Ctx D V₀ V L hV)
    (hcomp : IsComponentOf (lBar V₀ V hV L) (Mbar D.M V₀ V hV))
    (hsimple : IsSimpleGroup ↥(lBar V₀ V hV L))
    (hrank : 2 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup ↥(lBar V₀ V hV L)))
    (hcenter : ∀ (Q : Type) [Group Q] [Finite Q], CFSG.Open.IsQuasisimple Q →
      Nonempty ((Q ⧸ Subgroup.center Q) ≃* ↥(lBar V₀ V hV L)) →
      Subgroup.center Q = ⊥) :
    s15 D.M V₀ V hV L = 1 :=
  s15_eq_one_of_simple_component_of_three_rank c hcomp hsimple (r := 2) (by norm_num) hrank
    fun Q _ _ hq he => by
      rw [hcenter Q hq he]
      exact IsPGroup.of_card (n := 0) (by simp)

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
