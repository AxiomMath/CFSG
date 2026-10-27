module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.L34ConjugateSections
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.L34ConjugateCoverRank
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.ExceptionalComponentCover
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenThreeL34S1
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenElevenA

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

theorem s15_eq_one_of_l34_component_rank_nine
    {G : Type} [Group G] [Finite G]
    {D : Data G} {V₀ V L : Subgroup G} {hV : IsElemAbelian 2 V}
    (c : S168e3Ctx D V₀ V L hV)
    (hcomp : CFSG.Open.IsComponentOf
      (lBar V₀ V hV L) (Mbar D.M V₀ V hV))
    (hL34 : IsLn ↥(lBar V₀ V hV L) 3 2)
    (hirr : commSub (⊤ : Subgroup (Vtil V₀ V hV)) (lBar V₀ V hV L)
      ∈ irrSet (lBar V₀ V hV L))
    (hdim : E3.mQuot
      (commSub (⊤ : Subgroup (Vtil V₀ V hV)) (lBar V₀ V hV L))
      (commSub (⊤ : Subgroup (Vtil V₀ V hV)) (lBar V₀ V hV L)
        ⊓ fixV (lBar V₀ V hV L)) = 9) :
    s15 D.M V₀ V hV L = 1 := by
  classical
  let W := Vtil V₀ V hV
  let A : Subgroup (MulAut W) := Mbar D.M V₀ V hV
  let H : Subgroup (MulAut W) := lBar V₀ V hV L
  by_contra hsne
  have hpos : 0 < s15 D.M V₀ V hV L := s15_Eleven_pos_s D c.setting.hyp151 hV
  have hs2 : 2 ≤ s15 D.M V₀ V hV L := by
    rcases Nat.eq_or_lt_of_le (Nat.succ_le_of_lt hpos) with h | h
    · exact absurd h.symm hsne
    · exact h
  obtain ⟨t, htA, ht2, htne, hrk, φ, hφA, hrest⟩ :=
    exists_l34_active_conjugate (D := D) (V₀ := V₀) (V := V) (L := L) (hV := hV)
      c hL34 hirr hdim
  dsimp only at hrest
  obtain ⟨htN0, hfield, hcentral⟩ := hrest
  obtain ⟨F, hFfield, hFfin, hFchar, hFcard, π, hπsurj, hπker, B, hB⟩ := hfield
  letI : Field F := hFfield
  letI : Finite F := hFfin
  letI : CharP F 2 := hFchar
  let S : Set (Subgroup (MulAut W)) :=
    {X | ∃ φ ∈ A, X = H.map (MulAut.conj φ).toMonoidHom}
  have hS1 : 1 < S.ncard := by
    have h2 : 2 ≤ S.ncard := by
      simpa [S, s15, A, H, W, lBar] using hs2
    omega
  obtain ⟨H1, hH1S, hH1ne⟩ := Set.exists_ne_of_one_lt_ncard hS1
    (H.map (MulAut.conj φ).toMonoidHom)
  obtain ⟨σ, hσA, hH1eq⟩ := hH1S
  let H1' : Subgroup (MulAut W) := H.map (MulAut.conj σ).toMonoidHom
  have hH1eq' : H1' = H1 := hH1eq.symm
  have hH1ne' : H1' ≠ H.map (MulAut.conj φ).toMonoidHom := by
    rw [hH1eq']
    exact hH1ne
  have hcompA : CFSG.Assembly.IsComponentOf H A :=
    CFSG.Assembly.isComponentOf_iff_open.mpr hcomp
  have hAconjφ : A.map (MulAut.conj φ).toMonoidHom = A :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp (Subgroup.le_normalizer hφA)
  have hAconjσ : A.map (MulAut.conj σ).toMonoidHom = A :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp (Subgroup.le_normalizer hσA)
  have hcomp0 : CFSG.Open.IsComponentOf
      (H.map (MulAut.conj φ).toMonoidHom) A := by
    have h := CFSG.LocalAnalysis.ComponentInitial.isComponentOf_map_conj hcompA φ
    rw [hAconjφ] at h
    exact CFSG.Assembly.isComponentOf_iff_open.mp h
  have hcomp1 : CFSG.Open.IsComponentOf H1' A := by
    have h := CFSG.LocalAnalysis.ComponentInitial.isComponentOf_map_conj hcompA σ
    rw [hAconjσ] at h
    exact CFSG.Assembly.isComponentOf_iff_open.mp h
  have hL0 : IsLn ↥(H.map (MulAut.conj φ).toMonoidHom) 3 2 := by
    change CFSG.Blueprint.LieModel ↥(H.map (MulAut.conj φ).toMonoidHom) .PSL 3 2 2
    exact CFSG.Blueprint.LieModel.of_mulEquiv
      (Subgroup.equivMapOfInjective H (MulAut.conj φ).toMonoidHom
        (MulAut.conj φ).injective) hL34
  have hL1 : IsLn ↥H1' 3 2 := by
    change CFSG.Blueprint.LieModel ↥H1' .PSL 3 2 2
    exact CFSG.Blueprint.LieModel.of_mulEquiv
      (Subgroup.equivMapOfInjective H (MulAut.conj σ).toMonoidHom
        (MulAut.conj σ).injective) hL34
  have hsimple0 : IsSimpleGroup ↥(H.map (MulAut.conj φ).toMonoidHom) :=
    CFSG.Quasithin.H13.E54.isSimpleGroup_of_lieModel hL0
  have hsimple1 : IsSimpleGroup ↥H1' :=
    CFSG.Quasithin.H13.E54.isSimpleGroup_of_lieModel hL1
  obtain ⟨K0, hK0mem, hbar0, -⟩ :=
    exists_calC_cover_of_simple_component (D := D) (V₀ := V₀) (V := V) (hV := hV)
      c.setting.hyp16.hyp125 c.std.h127 c.std.h119 hcomp0 hsimple0
  obtain ⟨K1, hK1mem, hbar1, -⟩ :=
    exists_calC_cover_of_simple_component (D := D) (V₀ := V₀) (V := V) (hV := hV)
      c.setting.hyp16.hyp125 c.std.h127 c.std.h119 hcomp1 hsimple1
  obtain ⟨ψ, hψ⟩ := exists_barLift_of_hyp125 c.setting.hyp16.hyp125
  have himage0 : (UC22.barImage D.M K0).map ψ =
      H.map (MulAut.conj φ).toMonoidHom :=
    barImage_map_eq_of_mem_calC c.setting.hyp16.hyp125 hK0mem hbar0 ψ hψ
  have himage1 : (UC22.barImage D.M K1).map ψ = H1' :=
    barImage_map_eq_of_mem_calC c.setting.hyp16.hyp125 hK1mem hbar1 ψ hψ
  have htRange : t ∈ (barHom V₀ V hV c.m_le_stabTil).range := by
    rw [range_barHom V₀ V hV c.m_le_stabTil]
    exact htA
  obtain ⟨m, hm⟩ := htRange
  let x : Bar2 D.M := QuotientGroup.mk m
  have hψx : ψ x = t := by
    rw [show ψ x = actTil V₀ V hV ⟨m, c.m_le_stabTil m.2⟩ from hψ m]
    rw [← hm]
    rfl
  have h4 := barImage_inf_eq_bot_and_four_le_pRank_three_of_l34_field_centralizer
    hK0mem hK1mem ψ himage0 himage1 hL0 hL1 hH1ne'.symm
    hFcard π hπsurj hπker B x
    (by rw [hψx]; exact htN0)
    (by
      intro g
      rw [hψx]
      exact hB g)
    (by
      rw [hψx]
      have h := hcentral σ hσA
      exact h (by simpa [H1'] using hH1ne'))
  have hrank : 4 ≤ CFSG.Open.pRank 3 D.M := h4.2
  have hbound : CFSG.Open.pRank 3 D.M ≤ CFSG.Open.evenRank G :=
    CFSG.RankThreeCoreUniqueness.Helpers.local_pRank_le_evenRank 3 Nat.prime_three
      (by norm_num) D.M D.maxLocal.1
  have h3 : CFSG.Open.evenRank G = 3 := c.std.h3
  omega

theorem s168e3_l34_false
    {G : Type} [Group G] [Finite G]
    {D : Data G} {V₀ V L : Subgroup G} {hV : IsElemAbelian 2 V}
    (c : S168e3Ctx D V₀ V L hV)
    (hcomp : CFSG.Open.IsComponentOf
      (lBar V₀ V hV L) (Mbar D.M V₀ V hV))
    (hL34 : IsLn ↥(lBar V₀ V hV L) 3 2)
    (hirr : commSub (⊤ : Subgroup (Vtil V₀ V hV)) (lBar V₀ V hV L)
      ∈ irrSet (lBar V₀ V hV L))
    (hdim : E3.mQuot
      (commSub (⊤ : Subgroup (Vtil V₀ V hV)) (lBar V₀ V hV L))
      (commSub (⊤ : Subgroup (Vtil V₀ V hV)) (lBar V₀ V hV L)
        ⊓ fixV (lBar V₀ V hV L)) = 9) :
    False :=
  s168e3_l34_s1_false c
    (s15_eq_one_of_l34_component_rank_nine c hcomp hL34 hirr hdim) hL34 hirr hdim

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
