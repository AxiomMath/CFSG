module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.R76Sig
public import CFSG.LocalAnalysis.UniquenessCase.UC22DataExt
public import CFSG.LocalAnalysis.UniquenessCase.UC6S846e
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Thirteen6aCases
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Thirteen6aConcl
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Thirteen6aThree
import CFSG.LocalAnalysis.UniquenessCase.UC22S2121E3S13
public import CFSG.CGT.PushingUpLit.Transport
public import CFSG.LocalAnalysis.SeitzReduction.EPilotPosition
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Bridge13
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.StatementsA
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.StatementsC
public import CFSG.RankThree.PartTwo.Sec3.TwoThreeStructure

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.S136a

open Subgroup CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22

variable {G : Type} [Group G] [Finite G]

private theorem s136a_compsP_exists_mem_calC {D : Data G} {p : ℕ} (hpp : p.Prime)
    (hp2 : p ≠ 2) {F : Finset (Subgroup (Bar2 D.M))}
    (hF : s13_compsP (Bar2 D.M) p = F) {J : Subgroup (Bar2 D.M)} (hJ : J ∈ F) :
    ∃ L ∈ calC D.M, barImage D.M L = J ∧ CFSG.Open.pRank p J = CFSG.Open.pRank p L := by
  classical
  rw [← hF] at hJ
  obtain ⟨hcomp, _⟩ := s13_mem_compsP.mp hJ
  obtain ⟨L, hL, rfl⟩ := s13_exists_calC_of_component D.M hcomp
  exact ⟨L, hL, rfl, s13_pRank_barImage hpp hp2 (s13_le_of_mem_calC hL)⟩

private theorem s136a_false_of_three_of_card_three
    {D : Data G} {V₀ V : Subgroup G} {hV : Hyp125 D V₀ V} (c : Ctx D V₀ V hV)
    {p : ℕ} (hp : p ∈ D.sig) {F : Finset (Subgroup (Bar2 D.M))}
    (hF : s13_compsP (Bar2 D.M) p = F) (hcard : 2 < F.card) : False := by
  obtain ⟨hpp, hp2⟩ := D.sig_prime p hp
  obtain ⟨J₁, hJ₁, J₂, hJ₂, J₃, hJ₃, h12, h13, h23⟩ := Finset.two_lt_card.mp hcard
  obtain ⟨L₁, hL₁, rfl, -⟩ := s136a_compsP_exists_mem_calC hpp hp2 hF hJ₁
  obtain ⟨L₂, hL₂, rfl, -⟩ := s136a_compsP_exists_mem_calC hpp hp2 hF hJ₂
  obtain ⟨L₃, hL₃, rfl, -⟩ := s136a_compsP_exists_mem_calC hpp hp2 hF hJ₃
  exact s136a_false_of_three_members c.thin c.s13 c.r82 c.r1 hL₁ hL₂ hL₃ h12 h13 h23
    (c.shape _ hL₁) (c.shape _ hL₂) (c.shape _ hL₃)

private theorem s136a_hall_of_card_two
    {D : Data G} {V₀ V : Subgroup G} {hV : Hyp125 D V₀ V} (c : Ctx D V₀ V hV)
    {L K : Subgroup G} (hL : L ∈ calC D.M) (hK : K ∈ calC D.M)
    (hne : barImage D.M L ≠ barImage D.M K) :
    ∀ J : Subgroup (Bar2 D.M), CFSG.IsComponent J →
      J = barImage D.M L ∨ J = barImage D.M K := by
  classical
  intro J hJc
  by_contra hnot
  obtain ⟨X, hX, rfl⟩ := s13_exists_calC_of_component D.M hJc
  refine s136a_false_of_three_members c.thin c.s13 c.r82 c.r1 hL hK hX ?_ ?_ ?_
    (c.shape _ hL) (c.shape _ hK) (c.shape _ hX)
  · exact hne
  · intro h
    exact hnot (Or.inl h.symm)
  · intro h
    exact hnot (Or.inr h.symm)

private theorem s136a_two_of_card_two
    {D : Data G} {V₀ V : Subgroup G} {hV : Hyp125 D V₀ V} (c : Ctx D V₀ V hV)
    {p : ℕ} (hp : p ∈ D.sig) (h3 : 3 ∉ D.sig) {F : Finset (Subgroup (Bar2 D.M))}
    (hF : s13_compsP (Bar2 D.M) p = F) (hcard : F.card = 2)
    (hsum : CFSG.Open.pRank p D.M =
      (∑ J ∈ F, CFSG.Open.pRank p J) + CFSG.Open.pRank p (F13.Sp D.M p)) :
    Hinf D.M = F13.Lp D.M p ∧ ∃ n : ℕ, F13.Concl136 D p n := by
  classical
  obtain ⟨hpp, hp2⟩ := D.sig_prime p hp
  obtain ⟨J₁, J₂, h12, hJ⟩ := Finset.card_eq_two.mp hcard
  have hJ₁ : J₁ ∈ F := by rw [hJ]; exact Finset.mem_insert_self _ _
  have hJ₂ : J₂ ∈ F := by
    rw [hJ]
    exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
  obtain ⟨L, hL, hLb, hpLeq⟩ := s136a_compsP_exists_mem_calC hpp hp2 hF hJ₁
  obtain ⟨K, hK, hKb, hpKeq⟩ := s136a_compsP_exists_mem_calC hpp hp2 hF hJ₂
  have hdiv₁ : p ∣ Nat.card J₁ := (s13_mem_compsP.mp (by rw [hF]; exact hJ₁)).2
  have hdiv₂ : p ∣ Nat.card J₂ := (s13_mem_compsP.mp (by rw [hF]; exact hJ₂)).2
  have hpL : p ∣ Nat.card (barImage D.M L) := by rw [hLb]; exact hdiv₁
  have hpK : p ∣ Nat.card (barImage D.M K) := by rw [hKb]; exact hdiv₂
  have hne : barImage D.M L ≠ barImage D.M K := by rw [hLb, hKb]; exact h12
  have hsum' : CFSG.Open.pRank p D.M = CFSG.Open.pRank p L + CFSG.Open.pRank p K +
      CFSG.Open.pRank p (F13.Sp D.M p) := by
    rw [hsum, hJ, Finset.sum_pair h12, hpLeq, hpKeq]
  obtain ⟨n, hn, hpn, hsh⟩ := s136a_case_two c hp h3 hL hK hne hpL hpK hsum'
  obtain ⟨hH, hE⟩ := s136a_hinf_eq_and_equiv c.thin c.s13 hp hL hK hne
    (s136a_hall_of_card_two c hL hK hne) hpL hpK
  exact ⟨hH, n, s136a_concl136 hn hpn hsh hE⟩

theorem r136a_at
    (hThin : ThinList13)
    (hCyc : CFSG.RankThree.PartTwo.Sec11.CyclicSylowThreeOutAbelian) {D : Data G}
    (hx : DataExt D) (hSg : UC6S846.SigmaStd D) (hS : Setting13 D) (h82 : F08.R82 D)
    (h76 : F07.R76Sig D) (h614 : UC6.R6_14 D) (h638 : UC6.R6_38 D)
    (hshape : ∀ L ∈ calC D.M, ∃ n, IsPowTwo n ∧ (IsL2 (Bar2 L) n ∨ IsU3 (Bar2 L) n))
    {V₀ V : Subgroup G} (hV : Hyp125 D V₀ V) (r1 : S17.R17_1At D V₀ V hV)
    (r22 : S17.R17_2_2At D V₀ V hV) (r23 : S17.R17_2_3At D V₀ V hV)
    (r332 : S17.R17_33_2At D V₀ V) (r333 : S17.R17_33_3At D V₀ V) {p : ℕ}
    (hp : p ∈ D.sig) : Hinf D.M = F13.Lp D.M p ∧ ∃ n : ℕ, F13.Concl136 D p n := by
  classical
  let c : Ctx D V₀ V hV :=
    ⟨hThin, hCyc, hx, hSg, hS, h82, h76, h614, h638, hshape, r1, r22, r23, r332, r333⟩
  have h3 : 3 ∉ D.sig := s136a_three_not_mem c.thin c.cyc c.ext c.sg c.s13 c.shape c.r1
  have hp3 : p ≠ 3 := by
    rintro rfl
    exact h3 hp
  obtain ⟨hpp, hp2⟩ := D.sig_prime p hp
  have hsum := uc22s2121e3_pRank_eq_sum c.thin c.cyc c.s13 c.sg hp
  generalize hF : s13_compsP (Bar2 D.M) p = F at hsum
  rcases Nat.lt_or_ge 2 F.card with hc | hc
  · exfalso
    exact s136a_false_of_three_of_card_three c hp hF hc
  rcases Nat.lt_or_ge 1 F.card with hc1 | hc1
  · have hcard2 : F.card = 2 := by omega
    exact s136a_two_of_card_two c hp h3 hF hcard2 hsum
  rcases Nat.lt_or_ge 0 F.card with hc0 | hc0
  · exfalso
    have hcard1 : F.card = 1 := by omega
    obtain ⟨J, hJ⟩ := Finset.card_eq_one.mp hcard1
    have hmemJ : J ∈ F := by rw [hJ]; exact Finset.mem_singleton_self J
    obtain ⟨L, hL, hLb, hpLeq⟩ := s136a_compsP_exists_mem_calC hpp hp2 hF hmemJ
    have hpL : p ∣ Nat.card (barImage D.M L) := by
      rw [hLb]
      exact (s13_mem_compsP.mp (by rw [hF]; exact hmemJ)).2
    rw [hJ, Finset.sum_singleton, hpLeq] at hsum
    exact s136a_false_of_one_member c hp hp3 hL hpL hsum
  · exfalso
    have hcard0 : F.card = 0 := by omega
    have hF0 : F = ∅ := Finset.card_eq_zero.mp hcard0
    rw [hF0, Finset.sum_empty] at hsum
    have hS1 : CFSG.Open.pRank p (F13.Sp D.M p) ≤ 1 := c.s13.hyp131.smallS p hp
    have hM3 : 3 ≤ CFSG.Open.pRank p D.M := c.ext.three_le p hp
    omega

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.S136a
