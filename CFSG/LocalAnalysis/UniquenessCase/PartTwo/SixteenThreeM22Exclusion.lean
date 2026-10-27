module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.M22ConjugateSections
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenElevenA
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.M22ConjugateCoverRank
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.ExceptionalComponentCover
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenThreeM22S1

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22
open Subgroup

variable {G : Type} [Group G] [Finite G]

theorem s15_eq_one_of_m22_component_rank_ten
    {D : Data G} {V₀ V L : Subgroup G} {hV : IsElemAbelian 2 V}
    (c : S168e3Ctx D V₀ V L hV)
    (hcomp : IsComponentOf (lBar V₀ V hV L) (Mbar D.M V₀ V hV))
    (hM22 : IsSpor (lBar V₀ V hV L) .M22)
    (hirr : commSub (⊤ : Subgroup (Vtil V₀ V hV)) (lBar V₀ V hV L) ∈
      irrSet (lBar V₀ V hV L))
    (hdim : E3.mQuot
      (commSub (⊤ : Subgroup (Vtil V₀ V hV)) (lBar V₀ V hV L))
      (commSub (⊤ : Subgroup (Vtil V₀ V hV)) (lBar V₀ V hV L) ⊓
        fixV (lBar V₀ V hV L)) = 10) :
    s15 D.M V₀ V hV L = 1 := by
  classical
  let W := Vtil V₀ V hV
  let H : Subgroup (MulAut W) := lBar V₀ V hV L
  let A : Subgroup (MulAut W) := Mbar D.M V₀ V hV
  set S : Set (Subgroup (MulAut W)) :=
    {X | ∃ ψ ∈ A, X = H.map (MulAut.conj ψ).toMonoidHom} with hSdef
  have hSW : S.ncard = s15 D.M V₀ V hV L := by
    simp only [S, H, A, s15, lBar, Mbar]
    rfl
  have hpos : 0 < s15 D.M V₀ V hV L := s15_Eleven_pos_s D c.setting.hyp151 hV
  by_contra hs1
  have hsS : 1 < S.ncard := by rw [hSW]; omega
  obtain ⟨t, htA, ht2, htne, hrk, φ, hφA, hN0, hOuter0, hCent⟩ :=
    exists_m22_active_conjugate (D := D) (V₀ := V₀) (V := V) (L := L) (hV := hV)
      c hM22 hirr hdim
  set H0 : Subgroup (MulAut W) := H.map (MulAut.conj φ).toMonoidHom with hH0def
  obtain ⟨H1, hH1S, hH1ne⟩ := Set.exists_ne_of_one_lt_ncard hsS H0
  rw [hSdef] at hH1S
  obtain ⟨ψ, hψA, hH1eq⟩ := hH1S
  have hcompA : CFSG.Assembly.IsComponentOf H A :=
    CFSG.Assembly.isComponentOf_iff_open.mpr (by simpa [H, A] using hcomp)
  have hconjA : A.map (MulAut.conj φ).toMonoidHom = A :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp (Subgroup.le_normalizer hφA)
  have hconjAψ : A.map (MulAut.conj ψ).toMonoidHom = A :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp (Subgroup.le_normalizer hψA)
  have hcompH0 : IsComponentOf H0 A := by
    rw [hH0def]
    have h := CFSG.LocalAnalysis.ComponentInitial.isComponentOf_map_conj hcompA φ
    rw [hconjA] at h
    exact CFSG.Assembly.isComponentOf_iff_open.mp h
  have hcompH1 : IsComponentOf H1 A := by
    rw [hH1eq]
    have h := CFSG.LocalAnalysis.ComponentInitial.isComponentOf_map_conj hcompA ψ
    rw [hconjAψ] at h
    exact CFSG.Assembly.isComponentOf_iff_open.mp h
  have hM22H : IsSpor H .M22 := by simpa [H] using hM22
  have hM22H0 : IsSpor H0 .M22 := by
    rw [hH0def]
    obtain ⟨e⟩ := hM22H
    exact ⟨(Subgroup.equivMapOfInjective H (MulAut.conj φ).toMonoidHom
      (MulAut.conj φ).injective).symm.trans e⟩
  have hM22H1 : IsSpor H1 .M22 := by
    rw [hH1eq]
    obtain ⟨e⟩ := hM22H
    exact ⟨(Subgroup.equivMapOfInjective H (MulAut.conj ψ).toMonoidHom
      (MulAut.conj ψ).injective).symm.trans e⟩
  have hsimple0 : IsSimpleGroup ↥H0 := by
    obtain ⟨e⟩ := hM22H0
    exact (MulEquiv.isSimpleGroup_congr e).mpr
      CFSG.Quasithin.KGC31.KG443.isSimpleGroup_m22
  have hsimple1 : IsSimpleGroup ↥H1 := by
    obtain ⟨e⟩ := hM22H1
    exact (MulEquiv.isSimpleGroup_congr e).mpr
      CFSG.Quasithin.KGC31.KG443.isSimpleGroup_m22
  obtain ⟨K0, hK0mem, hK0bar, -⟩ :=
    exists_calC_cover_of_simple_component (D := D) (V₀ := V₀) (V := V) (hV := hV)
      c.setting.hyp16.hyp125 c.std.h127 c.std.h119 hcompH0 hsimple0
  obtain ⟨K1, hK1mem, hK1bar, -⟩ :=
    exists_calC_cover_of_simple_component (D := D) (V₀ := V₀) (V := V) (hV := hV)
      c.setting.hyp16.hyp125 c.std.h127 c.std.h119 hcompH1 hsimple1
  obtain ⟨ψM, hψM⟩ := exists_barLift_of_hyp125 (D := D) (V₀ := V₀) (V := V) (hV := hV)
    c.setting.hyp16.hyp125
  have himage0 : (UC22.barImage D.M K0).map ψM = H0 :=
    barImage_map_eq_of_mem_calC (D := D) (V₀ := V₀) (V := V) (hV := hV)
      c.setting.hyp16.hyp125 hK0mem hK0bar ψM hψM
  have himage1 : (UC22.barImage D.M K1).map ψM = H1 :=
    barImage_map_eq_of_mem_calC (D := D) (V₀ := V₀) (V := V) (hV := hV)
      c.setting.hyp16.hyp125 hK1mem hK1bar ψM hψM
  obtain ⟨g0, hg0M, hg0t⟩ := (mem_barSub V₀ V hV D.M t).1 htA
  let m : D.M := ⟨(g0 : G), hg0M⟩
  let x : Bar2 D.M := QuotientGroup.mk m
  have hψx : ψM x = t := by
    have h := hψM m
    have hsub : (⟨((m : D.M) : G),
        le_stabTil c.setting.hyp16.hyp125.pairFacts.le_normalizer
          c.setting.hyp16.hyp125.pairFacts.le_normalizer₀ (m : D.M).2⟩ : stabTil V₀ V) = g0 :=
      Subtype.ext rfl
    rw [hsub] at h
    exact h.trans hg0t
  have hH1ne' : H.map (MulAut.conj ψ).toMonoidHom ≠ H0 := by
    rw [← hH1eq]
    exact hH1ne
  have hxN : ψM x ∈ Subgroup.normalizer (H0 : Set (MulAut W)) := by
    rw [hψx]
    exact hN0
  have hxOuter : ¬ ∃ h0 ∈ H0, ∀ h ∈ H0,
      ψM x * h * (ψM x)⁻¹ = h0 * h * h0⁻¹ := by
    rw [hψx]
    exact hOuter0
  have hxC : ψM x ∈ Subgroup.centralizer (H1 : Set (MulAut W)) := by
    rw [hψx, hH1eq]
    exact hCent ψ hψA hH1ne'
  have hG := barImage_inf_eq_bot_and_four_le_pRank_three_of_m22_outer_centralizer
    (M := D.M) (K1 := K0) (K2 := K1) (Y := MulAut W) (ψ := ψM)
    (H1 := H0) (H2 := H1)
    hK0mem hK1mem himage0 himage1 hM22H0 hM22H1 hH1ne.symm x hxN hxOuter hxC
  obtain ⟨-, h4⟩ := hG
  have hbound : CFSG.Open.pRank 3 D.M ≤ CFSG.Open.evenRank G :=
    CFSG.RankThreeCoreUniqueness.Helpers.local_pRank_le_evenRank 3 Nat.prime_three
      (by norm_num) D.M D.maxLocal.1
  have h3 : CFSG.Open.evenRank G = 3 := c.std.h3
  omega

theorem s168e3_m22_false
    {D : Data G} {V₀ V L : Subgroup G} {hV : IsElemAbelian 2 V}
    (c : S168e3Ctx D V₀ V L hV)
    (hcomp : IsComponentOf (lBar V₀ V hV L) (Mbar D.M V₀ V hV))
    (hM22 : IsSpor (lBar V₀ V hV L) .M22)
    (hirr : commSub (⊤ : Subgroup (Vtil V₀ V hV)) (lBar V₀ V hV L) ∈
      irrSet (lBar V₀ V hV L))
    (hdim : E3.mQuot
      (commSub (⊤ : Subgroup (Vtil V₀ V hV)) (lBar V₀ V hV L))
      (commSub (⊤ : Subgroup (Vtil V₀ V hV)) (lBar V₀ V hV L) ⊓
        fixV (lBar V₀ V hV L)) = 10) :
    False :=
  s168e3_m22_s1_false c
    (s15_eq_one_of_m22_component_rank_ten c hcomp hM22 hirr hdim) hM22 hirr hdim

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
