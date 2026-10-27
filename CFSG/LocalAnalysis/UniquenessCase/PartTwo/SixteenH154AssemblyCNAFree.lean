module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154AssemblyCNLB
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154CoverMap
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC1677ThreeComp
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154Cover

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.RankThree.PartOne (IsStronglyPEmbedded)

variable {G : Type} [Group G] [Finite G]

theorem s16h_concl163_of_concl163F {D : Data G} {V₀ V L : Subgroup G} {hV : IsElemAbelian 2 V}
    (hs : 1 < s15 D.M V₀ V hV L) (h : Concl163F D V₀ V hV L) : Concl163 D V₀ V hV L := by
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr (Or.inl h))
  · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))
  · have h1 := h.2.2.1
    omega
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
      (Or.inl h)))))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
      (Or.inr (Or.inl h))))))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
      (Or.inr (Or.inr (Or.inl h)))))))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
      (Or.inr (Or.inr (Or.inr h)))))))))))

theorem s16h_nonthin_shape_F (D : Data G) (h163 : R16_3FComp D) {V₀ V L : Subgroup G}
    (h : Setting16 D V₀ V L) (hc : Conc4_136 D V₀ V h.hyp151.isElemAbelian L)
    (hs : 1 < s15 D.M V₀ V h.hyp151.isElemAbelian L)
    (hcomp : IsComponentOf (lBar V₀ V h.hyp151.isElemAbelian L)
      (Mbar D.M V₀ V h.hyp151.isElemAbelian))
    {q : ℕ} (hq : q.Prime) (hq2 : q ≠ 2)
    (hr : 2 ≤ CFSG.Open.pRank q (lBar V₀ V h.hyp151.isElemAbelian L)) :
    UC22.IsAlt ↥(lBar V₀ V h.hyp151.isElemAbelian L) 6 ∨
      UC22.IsAlt ↥(lBar V₀ V h.hyp151.isElemAbelian L) 7 ∨
      UC22.IsAlt ↥(lBar V₀ V h.hyp151.isElemAbelian L) 8 := by
  have hV := h.hyp151.isElemAbelian
  exact s16h_nonthin_shape_concl163 D hV hs hcomp hq hq2 hr
    (s16h_concl163_of_concl163F hs (h163 V₀ V L hV h hc hs hcomp ⟨q, hq, hq2, hr⟩))

private theorem s16h_free_sq_dvd_card_of_two_le_pRank {X : Type} [Group X] [Finite X]
    {q : ℕ} (hq : q.Prime) {H : Subgroup X} (hr : 2 ≤ CFSG.Open.pRank q H) :
    q ^ 2 ∣ Nat.card H := by
  obtain ⟨E, hE, -, hEcard⟩ := CFSG.SectionRank.exists_pRank hq.one_lt H
  have hdiv : q ^ 2 ∣ q ^ CFSG.Open.pRank q H := pow_dvd_pow q hr
  rw [← hEcard] at hdiv
  exact hdiv.trans (Subgroup.card_dvd_of_le hE)

private theorem s16h_free_q_eq_three_of_sq_dvd_factorial_div_two {q n : ℕ} (hq : q.Prime)
    (hq2 : q ≠ 2) (h2n : 2 ≤ n) (hn : n ≤ 8) (h : q ^ 2 ∣ n.factorial / 2) : q = 3 := by
  have hq_dvd : q ∣ n.factorial / 2 := by
    rw [pow_two] at h
    exact dvd_trans (dvd_mul_right q q) h
  have hq_fact : q ∣ n.factorial := by
    obtain ⟨k, hk⟩ := hq_dvd
    refine ⟨k * 2, ?_⟩
    rw [← Nat.div_mul_cancel (Nat.dvd_factorial (by norm_num) h2n), hk]
    ring
  have hq_le : q ≤ 8 := by
    have hqn : q ≤ n := (Nat.Prime.dvd_factorial hq).mp hq_fact
    omega
  have hq2le : 2 ≤ q := hq.two_le
  interval_cases q
  · norm_num at hq2
  · rfl
  · norm_num at hq
  · exfalso; interval_cases n <;> norm_num at h
  · norm_num at hq
  · exfalso; interval_cases n <;> norm_num at h
  · norm_num at hq

private theorem s16h_free_list880_of_isA6Z3 {X : Type} [Group X] (h : F08.IsA6Z3 X) :
    F08.List880 X :=
  Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))

private theorem s16h_free_list880_of_isA7Z3 {X : Type} [Group X] (h : F08.IsA7Z3 X) :
    F08.List880 X :=
  Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))

private theorem s16h_free_list880_of_isAlt_six {X : Type} [Group X] (h : UC22.IsAlt X 6) :
    F08.List880 X :=
  Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))

private theorem s16h_free_list880_of_isAlt_seven {X : Type} [Group X] (h : UC22.IsAlt X 7) :
    F08.List880 X :=
  Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))

private theorem s16h_free_list880_of_isAlt_eight {X : Type} [Group X] (h : UC22.IsAlt X 8) :
    F08.List880 X :=
  Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
    (Or.inl h))))))))))

private theorem s16h_free_list880_and_alt_center_of_isAlt_cover
    (D : Data G) {V₀ V : Subgroup G} {hV : IsElemAbelian 2 V} {K : Subgroup G}
    (h : Hyp125 D V₀ V) (hK : K ∈ calC D.M) (hne : barSub V₀ V hV K ≠ ⊥)
    {n : ℕ} (hn : n = 6 ∨ n = 7 ∨ n = 8) (hAlt : UC22.IsAlt ↥(barSub V₀ V hV K) n)
    (hSchur : RSchur153) :
    F08.List880 (Bar2 K) ∧ UC22.IsAlt (Bar2 K ⧸ Subgroup.center (Bar2 K)) n := by
  obtain ⟨hQS, hOdd⟩ := s15_Three_bar2_facts hK
  obtain ⟨f, hf, hfker⟩ := s16h_exists_central_cover_map D h hK hne
  obtain ⟨e⟩ := hAlt
  let g : Bar2 K →* alternatingGroup (Fin n) := e.toMonoidHom.comp f
  have hg : Function.Surjective g := e.surjective.comp hf
  have hgker : g.ker = Subgroup.center (Bar2 K) := by
    apply le_antisymm
    · intro x hx
      exact hfker (e.injective (by simpa [g] using hx))
    · intro z hz
      show e (f z) = 1
      have hfz : f z ∈ Subgroup.center ↥(barSub V₀ V hV K) := by
        rw [Subgroup.mem_center_iff]
        intro y
        obtain ⟨x, rfl⟩ := hf y
        rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.1 hz x]
      have he : e (f z) ∈ Subgroup.center (alternatingGroup (Fin n)) := by
        rw [Subgroup.mem_center_iff]
        intro y
        obtain ⟨w, rfl⟩ := e.surjective y
        rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.1 hfz w]
      have hbot : Subgroup.center (alternatingGroup (Fin n)) = ⊥ := by
        apply alternatingGroup.center_eq_bot
        rcases hn with rfl | rfl | rfl <;> norm_num
      rw [hbot] at he
      exact Subgroup.mem_bot.1 he
  have hAltCenter : UC22.IsAlt (Bar2 K ⧸ Subgroup.center (Bar2 K)) n := by
    refine ⟨((QuotientGroup.quotientMulEquivOfEq hgker.symm).trans
      (QuotientGroup.quotientKerEquivRange g)).trans
      ((MulEquiv.subgroupCongr (MonoidHom.range_eq_top.mpr hg)).trans Subgroup.topEquiv)⟩
  have hsch := hSchur (Bar2 K) hQS hOdd
  refine ⟨?_, hAltCenter⟩
  rcases hn with rfl | rfl | rfl
  · rcases hsch.1 hAltCenter with h | h
    · exact s16h_free_list880_of_isAlt_six h
    · exact s16h_free_list880_of_isA6Z3 h
  · rcases hsch.2.1 hAltCenter with h | h
    · exact s16h_free_list880_of_isAlt_seven h
    · exact s16h_free_list880_of_isA7Z3 h
  · exact s16h_free_list880_of_isAlt_eight (hsch.2.2.1 hAltCenter)

theorem s16h_nonthin_dichotomy_free
    (D : Data G) (h127 : R127 D) (h119 : F11.R119 D) (h880 : F08.R880 D) (h163 : R16_3FComp D)
    (hSchur : RSchur153) {V₀ V L : Subgroup G} (h : Setting16 D V₀ V L)
    (hs : 1 < s15 D.M V₀ V h.hyp151.isElemAbelian L)
    {t : MulAut (Vtil V₀ V h.hyp151.isElemAbelian)} (ht : t ∈ Mbar D.M V₀ V h.hyp151.isElemAbelian)
    (ht2 : t ^ 2 = 1) (ht1 : t ≠ 1) (htr : rk ↥(commSub ⊤ (zpowers t)) ≤ 3)
    (hW : Conc4_136W (Mbar D.M V₀ V h.hyp151.isElemAbelian) t
      (lBar V₀ V h.hyp151.isElemAbelian L))
    (hcomp : IsComponentOf (lBar V₀ V h.hyp151.isElemAbelian L)
      (Mbar D.M V₀ V h.hyp151.isElemAbelian))
    {q : ℕ} (hq : q.Prime) (hq2 : q ≠ 2)
    (hr : 2 ≤ CFSG.Open.pRank q (lBar V₀ V h.hyp151.isElemAbelian L)) :
    q = 3 ∧ IsStronglyPEmbedded 3 D.M := by
  have hV := h.hyp151.isElemAbelian
  have hc : Conc4_136 D V₀ V hV L := ⟨t, ht, ht2, ht1, htr, hW⟩
  have hshape := s16h_nonthin_shape_F D h163 h hc hs hcomp hq hq2 hr
  have hq3 : q = 3 := by
    have hdiv : q ^ 2 ∣ Nat.card ↥(lBar V₀ V hV L) :=
      s16h_free_sq_dvd_card_of_two_le_pRank hq hr
    rcases hshape with h6 | h7 | h8
    · have hcard : Nat.card ↥(lBar V₀ V hV L) = Nat.factorial 6 / 2 := by
        obtain ⟨e⟩ := h6
        rw [Nat.card_congr e.toEquiv, nat_card_alternatingGroup, Nat.card_eq_fintype_card,
          Fintype.card_fin]
      rw [hcard] at hdiv
      exact s16h_free_q_eq_three_of_sq_dvd_factorial_div_two (n := 6) hq hq2 (by norm_num)
        (by norm_num) hdiv
    · have hcard : Nat.card ↥(lBar V₀ V hV L) = Nat.factorial 7 / 2 := by
        obtain ⟨e⟩ := h7
        rw [Nat.card_congr e.toEquiv, nat_card_alternatingGroup, Nat.card_eq_fintype_card,
          Fintype.card_fin]
      rw [hcard] at hdiv
      exact s16h_free_q_eq_three_of_sq_dvd_factorial_div_two (n := 7) hq hq2 (by norm_num)
        (by norm_num) hdiv
    · have hcard : Nat.card ↥(lBar V₀ V hV L) = Nat.factorial 8 / 2 := by
        obtain ⟨e⟩ := h8
        rw [Nat.card_congr e.toEquiv, nat_card_alternatingGroup, Nat.card_eq_fintype_card,
          Fintype.card_fin]
      rw [hcard] at hdiv
      exact s16h_free_q_eq_three_of_sq_dvd_factorial_div_two (n := 8) hq hq2 (by norm_num)
        (by norm_num) hdiv
  refine ⟨hq3, ?_⟩
  by_contra hnot
  obtain ⟨K, hK, hKbar⟩ := s16h_exists_cover D h127 h119 h.hyp151.hyp125 hcomp
  have hne : barSub V₀ V hV K ≠ ⊥ := by
    rw [hKbar]
    haveI := hcomp.2.2.2
    have hnt : Nontrivial ↥(lBar V₀ V hV L) :=
      (QuotientGroup.mk'_surjective (Subgroup.center ↥(lBar V₀ V hV L))).nontrivial
    exact (Subgroup.nontrivial_iff_ne_bot _).mp hnt
  obtain ⟨n, hn, hAlt⟩ : ∃ n : ℕ, (n = 6 ∨ n = 7 ∨ n = 8) ∧
      UC22.IsAlt ↥(lBar V₀ V hV L) n := by
    rcases hshape with h6 | h7 | h8
    · exact ⟨6, Or.inl rfl, h6⟩
    · exact ⟨7, Or.inr (Or.inl rfl), h7⟩
    · exact ⟨8, Or.inr (Or.inr rfl), h8⟩
  have hAlt' : UC22.IsAlt ↥(barSub V₀ V hV K) n := by
    rw [hKbar]
    exact hAlt
  obtain ⟨hList, hAltCenter⟩ :=
    s16h_free_list880_and_alt_center_of_isAlt_cover D h.hyp151.hyp125 hK hne hn hAlt' hSchur
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨P, hP⟩ := CFSG.ABGLocalTools.exists_isSylowOf 3 D.M
  have hJ2 : IsSpor (Bar2 K) .J2 := (h880 K hK hList hnot P hP).1
  have hcardJ2 : Nat.card (Bar2 K) = 604800 := by
    obtain ⟨e⟩ := hJ2
    rw [Nat.card_congr e.toEquiv]
    change Nat.card CFSG.Blueprint.NativeSporadic.J2 = 604800
    exact CFSG.RankThree.PartTwo.KFacts.KS14.card_nativeJ2
  obtain ⟨-, hOdd⟩ := s15_Three_bar2_facts hK
  haveI : Nontrivial (Fin n) := by
    rcases hn with rfl | rfl | rfl <;> infer_instance
  have hquot : Nat.card (Bar2 K ⧸ Subgroup.center (Bar2 K)) = Nat.factorial n / 2 := by
    obtain ⟨e⟩ := hAltCenter
    rw [Nat.card_congr e.toEquiv, nat_card_alternatingGroup, Nat.card_eq_fintype_card,
      Fintype.card_fin]
  have hmul := Subgroup.card_eq_card_quotient_mul_card_subgroup
    (Subgroup.center (Bar2 K) : Subgroup (Bar2 K))
  rw [hquot, hcardJ2] at hmul
  obtain ⟨k, hk⟩ := hOdd
  rcases hn with rfl | rfl | rfl <;> norm_num at hmul <;> omega

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
