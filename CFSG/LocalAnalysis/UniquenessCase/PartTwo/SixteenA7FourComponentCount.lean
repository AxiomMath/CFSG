module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC1677ThreeDefs
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.ExceptionalComponentCover
import CFSG.LocalAnalysis.RankThreeUC.AGL81CZComm
public import CFSG.HardMathSupport.Timmesfeld.ComponentBalance.I_6_8
public import CFSG.LocalAnalysis.UniquenessCase.UC22P2214b
public import CFSG.Quasithin.Background.F918V5GComp
public import CFSG.Quasithin.Background.FFC8A
public import CFSG.Quasithin.EmptyFaithful.R3cBase
public import CFSG.Quasithin.Vol2.Ch12Sec2Lem8Rank

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G]

private theorem s16a7f_simple_of_a7Four {W : Type*} [CommGroup W]
    {H : Subgroup (MulAut W)} {U Z : Subgroup W} (hrow : A7Four H U Z) :
    IsSimpleGroup ↥H := by
  simp only [A7Four, FFModel.Realizes] at hrow
  obtain ⟨α, π, hπ⟩ := hrow
  exact (FFC.equivOfRealizes (FFC.a7Four_faithful α) hπ).isSimpleGroup_congr.mp
    (alternatingGroup.isSimpleGroup (by simp))

private theorem s16a7f_two_le_pRank_of_a7Four {W : Type*} [CommGroup W] [Finite W]
    {H : Subgroup (MulAut W)} {U Z : Subgroup W} (hrow : A7Four H U Z) :
    2 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup ↥H) := by
  haveI : Finite (MulAut W) := MulEquiv.finite_left
  simp only [A7Four, FFModel.Realizes] at hrow
  obtain ⟨α, π, hπ⟩ := hrow
  haveI : Finite (FFModel.a7Four α).Gam :=
    inferInstanceAs (Finite ↥(alternatingGroup (Fin 7)))
  calc 2 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup ↥(alternatingGroup (Fin 7))) :=
        CFSG.Quasithin.H13.Rank8.two_le_pRank_alternating_seven
    _ = CFSG.Open.pRank 3 (⊤ : Subgroup ↥H) :=
        CFSG.SectionRank.pRank_top_eq_of_mulEquiv (p := 3) (by norm_num)
          (FFC.equivOfRealizes (FFC.a7Four_faithful α) hπ)

private theorem s16a7f_actual_of_conj
    {D : Data G} {V₀ V L : Subgroup G} {hV : IsElemAbelian 2 V}
    (c : S168e3Ctx D V₀ V L hV)
    (hcomp : IsComponentOf (lBar V₀ V hV L) (Mbar D.M V₀ V hV))
    (hrow : A7Four (lBar V₀ V hV L)
      (commSub (⊤ : Subgroup (Vtil V₀ V hV)) (lBar V₀ V hV L))
      (commSub (⊤ : Subgroup (Vtil V₀ V hV)) (lBar V₀ V hV L) ⊓
        fixV (lBar V₀ V hV L)))
    {φ : MulAut (Vtil V₀ V hV)} (hφ : φ ∈ Mbar D.M V₀ V hV)
    {ψ : Bar2 D.M →* MulAut (Vtil V₀ V hV)}
    (hψ : ∀ m : D.M, ψ (QuotientGroup.mk m) =
      actTil V₀ V hV ⟨m, le_stabTil c.setting.hyp16.hyp125.pairFacts.le_normalizer
        c.setting.hyp16.hyp125.pairFacts.le_normalizer₀ m.2⟩) :
    ∃ C : Subgroup (Bar2 D.M), CFSG.IsComponent C ∧
      C.map ψ = (lBar V₀ V hV L).map (MulAut.conj φ).toMonoidHom ∧
      2 ≤ CFSG.Open.pRank 3 C ∧
      ∃ e ∈ C, orderOf e = 3 ∧ ∃ z ∈ C, e * z ≠ z * e := by
  classical
  let W := Vtil V₀ V hV
  haveI : Finite W := inferInstanceAs (Finite (Vtil V₀ V hV))
  haveI : Finite (MulAut W) := MulEquiv.finite_left
  let H : Subgroup (MulAut W) := lBar V₀ V hV L
  let A : Subgroup (MulAut W) := Mbar D.M V₀ V hV
  let H' : Subgroup (MulAut W) := H.map (MulAut.conj φ).toMonoidHom
  have hsimpleH : IsSimpleGroup ↥H := s16a7f_simple_of_a7Four hrow
  have hsimple : IsSimpleGroup ↥H' :=
    (H.equivMapOfInjective (MulAut.conj φ).toMonoidHom (MulAut.conj φ).injective).isSimpleGroup_congr.mp
      hsimpleH
  have hcomp' : IsComponentOf H' A := by
    simpa [H', H, A] using CFSG.Quasithin.F918V5G.isComponentOf_map_conj hcomp hφ
  have hrankH : 2 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup ↥H) :=
    s16a7f_two_le_pRank_of_a7Four hrow
  have hrankH' : 2 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup ↥H') := by
    calc 2 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup ↥H) := hrankH
      _ = CFSG.Open.pRank 3 (⊤ : Subgroup ↥H') :=
          CFSG.SectionRank.pRank_top_eq_of_mulEquiv (p := 3) (by norm_num)
            (H.equivMapOfInjective (MulAut.conj φ).toMonoidHom (MulAut.conj φ).injective)
  obtain ⟨K, hK, hbarK, -⟩ :=
    exists_calC_cover_of_simple_component c.setting.hyp16.hyp125 c.std.h127 c.std.h119
      hcomp' hsimple
  let C : Subgroup (Bar2 D.M) := UC22.barImage D.M K
  have hCcomp : CFSG.IsComponent C := UC22.uc22p22l_barImage_isComponent hK
  have hCmap : C.map ψ = H' := by
    simpa [C, H'] using
      barImage_map_eq_of_mem_calC c.setting.hyp16.hyp125 hK hbarK ψ hψ
  let f : ↥C →* ↥H' := (ψ.comp C.subtype).codRestrict H' (by
    intro x
    rw [← hCmap]
    exact Subgroup.mem_map_of_mem ψ x.2)
  have hf : Function.Surjective f := by
    intro y
    have hy : (y : MulAut W) ∈ C.map ψ := by rw [hCmap]; exact y.2
    obtain ⟨x, hxC, hxy⟩ := Subgroup.mem_map.mp hy
    exact ⟨⟨x, hxC⟩, Subtype.ext hxy⟩
  have hCrank : 2 ≤ CFSG.Open.pRank 3 C :=
    UC22.uc22p2214_two_le_pRank_of_surj (K := C) f hf Nat.prime_three (by norm_num) hrankH'
  have hpos : 0 < CFSG.Open.pRank 3 (⊤ : Subgroup ↥C) := by
    rw [← CFSG.SectionRank.pRank_eq_pRank_top_subgroup C]
    omega
  have h3C : 3 ∣ Nat.card C := by
    simpa using CFSG.RankThreeCoreUniqueness.Helpers.prime_dvd_card_of_pRank_pos
      3 (⊤ : Subgroup ↥C) hpos
  have hqC : CFSG.Open.IsQuasisimple ↥C :=
    CFSG.Quasithin.A3.isQuasisimple_iff_open.mp hCcomp.1
  obtain ⟨x, hxord, hxcent⟩ :=
    CFSG.HardMathSupport.Timmesfeld.ComponentBalance.exists_orderOf_eq_prime_not_mem_center
      hqC Nat.prime_three (by norm_num) h3C
  rw [Subgroup.mem_center_iff] at hxcent
  push Not at hxcent
  obtain ⟨z, hz⟩ := hxcent
  have hzne : (x : Bar2 D.M) * (z : Bar2 D.M) ≠ (z : Bar2 D.M) * (x : Bar2 D.M) := by
    intro h
    exact hz (Subtype.ext h.symm)
  exact ⟨C, hCcomp, hCmap, hCrank,
    (x : Bar2 D.M), x.2, (Subgroup.orderOf_coe x).trans hxord,
    (z : Bar2 D.M), z.2, hzne⟩

theorem s15_le_two_of_a7Four_component
    {D : Data G} {V₀ V L : Subgroup G} {hV : IsElemAbelian 2 V}
    (c : S168e3Ctx D V₀ V L hV)
    (hcomp : IsComponentOf (lBar V₀ V hV L) (Mbar D.M V₀ V hV))
    (hrow : A7Four (lBar V₀ V hV L)
      (commSub (⊤ : Subgroup (Vtil V₀ V hV)) (lBar V₀ V hV L))
      (commSub (⊤ : Subgroup (Vtil V₀ V hV)) (lBar V₀ V hV L) ⊓
        fixV (lBar V₀ V hV L))) :
    s15 D.M V₀ V hV L ≤ 2 := by
  classical
  haveI : Finite (MulAut (Vtil V₀ V hV)) := MulEquiv.finite_left
  have hsS : s15 D.M V₀ V hV L =
      (conjSet (lBar V₀ V hV L) (Mbar D.M V₀ V hV)).ncard := rfl
  by_contra hle
  have h2 : 2 < (conjSet (lBar V₀ V hV L) (Mbar D.M V₀ V hV)).ncard := by
    rw [← hsS]; omega
  obtain ⟨H₁, H₂, H₃, hH₁, hH₂, hH₃, h12, h13, h23⟩ :=
    (Set.two_lt_ncard_iff (Set.toFinite _)).1 h2
  obtain ⟨ψ, hψ⟩ := exists_barLift_of_hyp125 c.setting.hyp16.hyp125
  simp only [conjSet] at hH₁ hH₂ hH₃
  obtain ⟨φ₁, hφ₁, rfl⟩ := hH₁
  obtain ⟨φ₂, hφ₂, rfl⟩ := hH₂
  obtain ⟨φ₃, hφ₃, rfl⟩ := hH₃
  obtain ⟨C₁, hC₁c, hC₁map, hC₁rank, -⟩ :=
    s16a7f_actual_of_conj c hcomp hrow hφ₁ (ψ := ψ) hψ
  obtain ⟨C₂, hC₂c, hC₂map, -, hC₂nc⟩ :=
    s16a7f_actual_of_conj c hcomp hrow hφ₂ (ψ := ψ) hψ
  obtain ⟨C₃, hC₃c, hC₃map, -, hC₃nc⟩ :=
    s16a7f_actual_of_conj c hcomp hrow hφ₃ (ψ := ψ) hψ
  have hC₁₂ : C₁ ≠ C₂ := by
    intro heq
    exact h12 (hC₁map.symm.trans ((by rw [heq] : C₁.map ψ = C₂.map ψ).trans hC₂map))
  have hC₁₃ : C₁ ≠ C₃ := by
    intro heq
    exact h13 (hC₁map.symm.trans ((by rw [heq] : C₁.map ψ = C₃.map ψ).trans hC₃map))
  have hC₂₃ : C₂ ≠ C₃ := by
    intro heq
    exact h23 (hC₂map.symm.trans ((by rw [heq] : C₂.map ψ = C₃.map ψ).trans hC₃map))
  obtain ⟨B, hBC₁, hBab, hBcard⟩ :=
    CFSG.SectionRank.exists_pRank (p := 3) (by norm_num) C₁
  have hboundbar : CFSG.Open.pRank 3 C₁ + 2 ≤
      CFSG.pRank 3 (⊤ : Subgroup (Bar2 D.M)) :=
    CFSG.LocalAnalysis.RankThreeUC.AGL81C.add_two_le_pRank_of_three_components
      (p := 3) Nat.prime_three hC₁c hC₂c hC₃c hC₁₂ hC₁₃ hC₂₃ hBC₁ hBab hBcard hC₂nc hC₃nc
  have hboundopen : CFSG.Open.pRank 3 C₁ + 2 ≤
      CFSG.Open.pRank 3 (⊤ : Subgroup (Bar2 D.M)) := by
    rw [← CFSG.SectionRank.pRank_coe_eq_openPRank 3 (⊤ : Subgroup (Bar2 D.M))]
    exact hboundbar
  have hboundM : CFSG.Open.pRank 3 C₁ + 2 ≤ CFSG.Open.pRank 3 D.M := by
    rw [CFSG.Quasithin.R3c.pRank_three_eq_pCore_quotient D.M]
    exact hboundopen
  have hupper : CFSG.Open.pRank 3 D.M ≤ 3 := by
    have h := CFSG.RankThreeCoreUniqueness.Helpers.local_pRank_le_evenRank 3
      Nat.prime_three (by norm_num) D.M D.maxLocal.1
    rw [c.std.h3] at h
    exact h
  omega

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
