module

public import CFSG.LocalAnalysis.StandardType.GGDepELNatBase

public section

namespace CFSG.StandardType

open Certificates.DepED4Low Certificates.TwoDepSmall Certificates.DepASmall

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem ggDepELNGen_valid {news : List GGDepANPair} (hnews : ∀ q ∈ news, GGDepELNValid q)
    {g : ℕ} (hg : g < 6 + news.length) : GGDepELNValid (ggDepELNGen news g) := by
  unfold ggDepELNGen
  by_cases h : g < 6
  · rw [if_pos h]
    exact ggDepELNFrame_valid h
  · rw [if_neg h]
    have hk : g - 6 < news.length := by omega
    rw [List.getD_eq_getElem (l := news) (d := ([], [])) (n := g - 6) hk]
    exact hnews _ (List.getElem_mem hk)

theorem ggDepELNGen_mem {news : List GGDepANPair} {g : ℕ} (hg : g < 6 + news.length) :
    ggDepELNRflOf (ggDepELNGen news g) ∈ Submonoid.closure (ggDepELGens (ggDepELNNews news)) := by
  unfold ggDepELNGen
  by_cases h : g < 6
  · rw [if_pos h]
    show ggDepARefl (ggDepELToZ (ggDepELNH g)) (ggDepELToZ (ggDepELNA g)) ∈
      Submonoid.closure (ggDepELGens (ggDepELNNews news))
    rw [ggDepELNH_toZ ⟨g, h⟩, ggDepELNA_toZ ⟨g, h⟩]
    exact Submonoid.subset_closure (Or.inl ⟨⟨g, h⟩, rfl⟩)
  · rw [if_neg h]
    have hk : g - 6 < news.length := by omega
    rw [List.getD_eq_getElem (l := news) (d := ([], [])) (n := g - 6) hk]
    refine Submonoid.subset_closure (Or.inr ?_)
    exact ⟨(ggDepELToZ (news[g - 6]).1, ggDepELToZ (news[g - 6]).2),
      ⟨news[g - 6], List.getElem_mem hk, rfl⟩, rfl⟩

theorem ggDepELNWord_valid_mem {news : List GGDepANPair}
    (hnews : ∀ q ∈ news, GGDepELNValid q) {q : GGDepANPair} (hq : GGDepELNValid q)
    (hqm : ggDepELNRflOf q ∈ Submonoid.closure (ggDepELGens (ggDepELNNews news)))
    {w : List ℕ} (hw : ∀ g ∈ w, g < 6 + news.length) :
    GGDepELNValid (ggDepELNWord news q w) ∧
      ggDepELNRflOf (ggDepELNWord news q w) ∈
        Submonoid.closure (ggDepELGens (ggDepELNNews news)) := by
  revert hw q hq hqm
  induction w with
  | nil =>
      intro q hq hqm hw
      simpa [ggDepELNWord] using ⟨hq, hqm⟩
  | cons g w ih =>
      intro q hq hqm hw
      have hg : g < 6 + news.length := hw g (by simp)
      have hw' : ∀ g' ∈ w, g' < 6 + news.length := fun g' hg' => hw g' (by simp [hg'])
      obtain ⟨ihv, ihm⟩ := ih hq hqm hw'
      have hgenv : GGDepELNValid (ggDepELNGen news g) := ggDepELNGen_valid hnews hg
      have hgenm : ggDepELNRflOf (ggDepELNGen news g) ∈
          Submonoid.closure (ggDepELGens (ggDepELNNews news)) := ggDepELNGen_mem hg
      have hconj := ggDepELNConj_rfl ihv hgenv
      have hword : ggDepELNWord news q (g :: w) =
          ggDepANConj 3 (ggDepELNWord news q w) (ggDepELNGen news g) := by
        simp [ggDepELNWord]
      rw [hword]
      exact ⟨hconj.1, by
        rw [hconj.2]
        exact Submonoid.mul_mem _ (Submonoid.mul_mem _ hgenm ihm) hgenm⟩

theorem ggDepELTv_sound {news : List GGDepANPair} (hnews : ∀ q ∈ news, GGDepELNValid q)
    (w : GGDepANWit) (hv : ggDepELTvValid (6 + news.length) w = true)
    (ht : ggDepELTvTest news w = true) :
    ∃ g ∈ Submonoid.closure (ggDepELGens (ggDepELNNews news)), GGDepAIsTv g := by
  have hv' := hv
  simp only [ggDepELTvValid, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at hv'
  obtain ⟨⟨⟨hvg1, hvg2⟩, hvw1⟩, hvw2⟩ := hv'
  have ht' : ggDepANTestPair 3 (ggDepELNWord news (ggDepELNGen news w.g1) w.w1)
      (ggDepELNWord news (ggDepELNGen news w.g2) w.w2) = true := by
    simpa only [ggDepELTvTest] using ht
  obtain ⟨hv1, hm1⟩ := ggDepELNWord_valid_mem hnews (ggDepELNGen_valid hnews hvg1)
    (ggDepELNGen_mem hvg1) hvw1
  obtain ⟨hv2, hm2⟩ := ggDepELNWord_valid_mem hnews (ggDepELNGen_valid hnews hvg2)
    (ggDepELNGen_mem hvg2) hvw2
  have hp2 : (3 : ℕ) ≠ 2 := by norm_num
  have hd1 : ggDepANDot 3 (ggDepELNWord news (ggDepELNGen news w.g1) w.w1).2
      (ggDepELNWord news (ggDepELNGen news w.g1) w.w1).1 = 2 % 3 := by
    rw [show (2 : ℕ) % 3 = 2 from by norm_num]
    exact hv1.2.2
  have hd2 : ggDepANDot 3 (ggDepELNWord news (ggDepELNGen news w.g2) w.w2).2
      (ggDepELNWord news (ggDepELNGen news w.g2) w.w2).1 = 2 % 3 := by
    rw [show (2 : ℕ) % 3 = 2 from by norm_num]
    exact hv2.2.2
  have htv := ggDepANTestPair_sound (p := 3) (N := 6) hp2 _
    _ hv1.1 hv1.2.1 hv2.1 hv2.2.1 hd1 hd2 ht'
  refine ⟨ggDepELNRflOf (ggDepELNWord news (ggDepELNGen news w.g1) w.w1) *
      ggDepELNRflOf (ggDepELNWord news (ggDepELNGen news w.g2) w.w2),
    Submonoid.mul_mem _ hm1 hm2, ?_⟩
  exact htv.2.2

end CFSG.StandardType

end
