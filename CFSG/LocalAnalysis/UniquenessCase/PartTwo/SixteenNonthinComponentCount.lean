module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC1677ThreeDefs
import CFSG.LocalAnalysis.AGLEmbedding.RankTools
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.ExceptionalComponentCover
import CFSG.LocalAnalysis.RankThreeUC.AGL81CZComm
public import CFSG.HardMathSupport.Timmesfeld.ComponentBalance.I_6_8
public import CFSG.LocalAnalysis.UniquenessCase.UC22P2214b
public import CFSG.Quasithin.Background.F918V5GComp

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G]

private theorem s168e3_actual_of_conj
    {D : Data G} {V₀ V L : Subgroup G} {hV : IsElemAbelian 2 V}
    (c : S168e3Ctx D V₀ V L hV)
    (hcomp : IsComponentOf (lBar V₀ V hV L) (Mbar D.M V₀ V hV))
    {q : ℕ} (hq : q.Prime) (hq2 : q ≠ 2)
    (hrank : 2 ≤ CFSG.Open.pRank q (lBar V₀ V hV L))
    {φ : MulAut (Vtil V₀ V hV)} (hφ : φ ∈ Mbar D.M V₀ V hV)
    {ψ : Bar2 D.M →* MulAut (Vtil V₀ V hV)}
    (hψ : ∀ m : D.M, ψ (QuotientGroup.mk m) =
      actTil V₀ V hV ⟨m, le_stabTil c.setting.hyp16.hyp125.pairFacts.le_normalizer
        c.setting.hyp16.hyp125.pairFacts.le_normalizer₀ m.2⟩) :
    ∃ C : Subgroup (Bar2 D.M), CFSG.IsComponent C ∧
      C.map ψ = (lBar V₀ V hV L).map (MulAut.conj φ).toMonoidHom ∧
      2 ≤ CFSG.Open.pRank q C ∧
      ∃ e ∈ C, orderOf e = q ∧ ∃ z ∈ C, e * z ≠ z * e := by
  classical
  let W := Vtil V₀ V hV
  have : Finite W := inferInstanceAs (Finite (Vtil V₀ V hV))
  have : Finite (MulAut W) := MulEquiv.finite_left
  let H : Subgroup (MulAut W) := lBar V₀ V hV L
  let A : Subgroup (MulAut W) := Mbar D.M V₀ V hV
  let H' : Subgroup (MulAut W) := H.map (MulAut.conj φ).toMonoidHom
  have hcomp' : IsComponentOf H' A := by
    simpa [H', H, A] using CFSG.Quasithin.F918V5G.isComponentOf_map_conj hcomp hφ
  have hrankH : 2 ≤ CFSG.Open.pRank q (⊤ : Subgroup ↥H) := by
    rw [← CFSG.SectionRank.pRank_eq_pRank_top_subgroup H]
    exact hrank
  have hrankH' : 2 ≤ CFSG.Open.pRank q (⊤ : Subgroup ↥H') := by
    calc 2 ≤ CFSG.Open.pRank q (⊤ : Subgroup ↥H) := hrankH
      _ = CFSG.Open.pRank q (⊤ : Subgroup ↥H') :=
          CFSG.SectionRank.pRank_top_eq_of_mulEquiv (p := q) hq.one_lt
            (H.equivMapOfInjective (MulAut.conj φ).toMonoidHom (MulAut.conj φ).injective)
  obtain ⟨K, hK, hbarK⟩ :=
    exists_calC_cover_of_component c.setting.hyp16.hyp125 c.std.h127 c.std.h119 hcomp'
  let C : Subgroup (Bar2 D.M) := UC22.barImage D.M K
  have hCcomp : CFSG.IsComponent C := UC22.uc22p22l_barImage_isComponent hK
  have hCmap : C.map ψ = H' := by
    simpa [C, H'] using
      barImage_map_eq_of_mem_calC c.setting.hyp16.hyp125 hK hbarK ψ hψ
  let f : ↥C →* ↥H' := (MulEquiv.subgroupCongr hCmap).toMonoidHom.comp (ψ.subgroupMap C)
  have hf : Function.Surjective f :=
    (MulEquiv.subgroupCongr hCmap).surjective.comp (ψ.subgroupMap_surjective C)
  have hCrank : 2 ≤ CFSG.Open.pRank q C :=
    UC22.uc22p2214_two_le_pRank_of_surj (K := C) f hf hq hq2 hrankH'
  have hpos : 0 < CFSG.Open.pRank q (⊤ : Subgroup ↥C) := by
    rw [← CFSG.SectionRank.pRank_eq_pRank_top_subgroup C]
    omega
  have hqC : q ∣ Nat.card C := by
    simpa using CFSG.RankThreeCoreUniqueness.Helpers.prime_dvd_card_of_pRank_pos
      q (⊤ : Subgroup ↥C) hpos
  have hqs : CFSG.Open.IsQuasisimple ↥C :=
    CFSG.Quasithin.A3.isQuasisimple_iff_open.mp hCcomp.1
  obtain ⟨x, hxord, hxcent⟩ :=
    CFSG.HardMathSupport.Timmesfeld.ComponentBalance.exists_orderOf_eq_prime_not_mem_center
      hqs hq hq2 hqC
  rw [Subgroup.mem_center_iff] at hxcent
  push Not at hxcent
  obtain ⟨z, hz⟩ := hxcent
  have hzne : (x : Bar2 D.M) * (z : Bar2 D.M) ≠ (z : Bar2 D.M) * (x : Bar2 D.M) := by
    intro h
    exact hz (Subtype.ext h.symm)
  exact ⟨C, hCcomp, hCmap, hCrank,
    (x : Bar2 D.M), x.2, (Subgroup.orderOf_coe x).trans hxord,
    (z : Bar2 D.M), z.2, hzne⟩

theorem s168e3_s_le_two_of_component_odd_pRank
    {D : Data G} {V₀ V L : Subgroup G} {hV : IsElemAbelian 2 V}
    (c : S168e3Ctx D V₀ V L hV)
    (hcomp : IsComponentOf (lBar V₀ V hV L) (Mbar D.M V₀ V hV))
    {q : ℕ} (hq : q.Prime) (hq2 : q ≠ 2)
    (hrank : 2 ≤ CFSG.Open.pRank q (lBar V₀ V hV L)) :
    s15 D.M V₀ V hV L ≤ 2 := by
  classical
  have : Finite (MulAut (Vtil V₀ V hV)) := MulEquiv.finite_left
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
    s168e3_actual_of_conj c hcomp hq hq2 hrank hφ₁ (ψ := ψ) hψ
  obtain ⟨C₂, hC₂c, hC₂map, -, hC₂nc⟩ :=
    s168e3_actual_of_conj c hcomp hq hq2 hrank hφ₂ (ψ := ψ) hψ
  obtain ⟨C₃, hC₃c, hC₃map, -, hC₃nc⟩ :=
    s168e3_actual_of_conj c hcomp hq hq2 hrank hφ₃ (ψ := ψ) hψ
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
    CFSG.SectionRank.exists_pRank (p := q) hq.one_lt C₁
  have hboundbar : CFSG.Open.pRank q C₁ + 2 ≤
      CFSG.pRank q (⊤ : Subgroup (Bar2 D.M)) :=
    CFSG.LocalAnalysis.RankThreeUC.AGL81C.add_two_le_pRank_of_three_components
      (p := q) hq hC₁c hC₂c hC₃c hC₁₂ hC₁₃ hC₂₃ hBC₁ hBab hBcard hC₂nc hC₃nc
  have hboundopen : CFSG.Open.pRank q C₁ + 2 ≤
      CFSG.Open.pRank q (⊤ : Subgroup (Bar2 D.M)) := by
    rw [← CFSG.SectionRank.pRank_coe_eq_openPRank q (⊤ : Subgroup (Bar2 D.M))]
    exact hboundbar
  have hboundM : CFSG.Open.pRank q C₁ + 2 ≤ CFSG.Open.pRank q D.M := by
    have hbar : CFSG.Open.pRank q (CFSG.AGLEmbedding.barM D.M D.M) = CFSG.Open.pRank q D.M :=
      CFSG.AGLEmbedding.pRank_barM_eq hq hq2 D.M D.M le_rfl
    have htop : CFSG.AGLEmbedding.barM D.M D.M = ⊤ := by
      simp [CFSG.AGLEmbedding.barM, Subgroup.subgroupOf_self]
      exact Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective _)
    rw [← hbar, htop]
    exact hboundopen
  have hupper : CFSG.Open.pRank q D.M ≤ 3 := by
    have h := CFSG.RankThreeCoreUniqueness.Helpers.local_pRank_le_evenRank q hq hq2 D.M D.maxLocal.1
    rw [c.std.h3] at h
    exact h
  omega

theorem s168e3_s_eq_two_of_nonThin_component
    {D : Data G} {V₀ V L : Subgroup G} {hV : IsElemAbelian 2 V}
    (c : S168e3Ctx D V₀ V L hV)
    (hcomp : IsComponentOf (lBar V₀ V hV L) (Mbar D.M V₀ V hV))
    (hs : 1 < s15 D.M V₀ V hV L)
    (hodd : ∃ q : ℕ, q.Prime ∧ q ≠ 2 ∧
      2 ≤ CFSG.Open.pRank q (lBar V₀ V hV L)) :
    s15 D.M V₀ V hV L = 2 := by
  obtain ⟨q, hq, hq2, hrank⟩ := hodd
  have hle := s168e3_s_le_two_of_component_odd_pRank c hcomp hq hq2 hrank
  omega

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
