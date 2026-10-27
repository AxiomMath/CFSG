module

public import CFSG.Quasithin.EmptyFaithful.S151T3
public import CFSG.Quasithin.EmptyFaithful.S151U8
public import CFSG.Quasithin.EmptyFaithful.S151T2

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank
open scoped Pointwise commutatorElement

theorem s151t_three_distinct {α : Type*} {a b u v w : α} (hab : a ≠ b) (hu : u = a ∨ u = b)
    (hv : v = a ∨ v = b) (hw : w = a ∨ w = b) (huv : u ≠ v) (hwu : w ≠ u) (hwv : w ≠ v) : False := by
  rcases hu with rfl | rfl <;> rcases hv with rfl | rfl <;> rcases hw with rfl | rfl <;> simp_all

theorem input15122L3WreathMinPar_of (h37 : A37ForSQTK) (h38 : A38ForSQTK) :
    Input15122L3WreathMinPar := by
  intro G _ _ T Mc M Z₁ Z₂ V₁ V₂ L P hc h2B h3 hSN hpar hbig
  have hq := hc.ctx.qtfe
  have hMf := hc.ctx.mf
  have hSet := hc.ctx.setting
  have hpc : pCoreOf 2 (g1_1516 Z₁) ≠ ⊥ := hSet.pCore_g1_ne_bot hq hMf
  have hLcomp : L ∈ cComp (g1_1516 Z₁) := hc.hL.comp
  have hLG : L ≤ g1_1516 Z₁ := le_of_mem_cComp hLcomp
  obtain ⟨s, hsS, hsN⟩ : ∃ s ∈ s1516 T Z₁, s ∉ Subgroup.normalizer (L : Set G) := by
    by_contra hcon
    push Not at hcon
    exact hSN (fun x hx => hcon x hx)
  have hsG : s ∈ g1_1516 Z₁ := s1516_le_g1 T Z₁ hsS
  rcases lemma_1_2_1_three hq.qtke hq.simple hq.nonabelian h37 h38 hpc hLcomp with hn | ⟨hcard2, -⟩
  · exact absurd ((Subgroup.normal_subgroupOf_iff_le_normalizer hLG).mp hn hsG) hsN
  have hLL' : B6.conjSub s L ≠ L := fun h => hsN (s151t_mem_normalizer_of_conjSub h)
  have hL'comp : B6.conjSub s L ∈ cComp (g1_1516 Z₁) := map_conj_mem_cComp hLcomp hsG
  obtain ⟨a, b, hab, hset⟩ := Set.ncard_eq_two.mp hcard2
  have hmemL : L ∈ conjSubgroupsBy (g1_1516 Z₁) L :=
    ⟨1, (g1_1516 Z₁).one_mem, by ext x; simp⟩
  have hmemL' : B6.conjSub s L ∈ conjSubgroupsBy (g1_1516 Z₁) L := ⟨s, hsG, rfl⟩
  have hconj : ∀ x ∈ g1_1516 Z₁, B6.conjSub x L = L ∨ B6.conjSub x L = B6.conjSub s L := by
    intro x hx
    have hmemx : B6.conjSub x L ∈ conjSubgroupsBy (g1_1516 Z₁) L := ⟨x, hx, rfl⟩
    rw [hset] at hmemL hmemL' hmemx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hmemL hmemL' hmemx
    by_contra hcon
    push Not at hcon
    exact s151t_three_distinct hab hmemL hmemL' hmemx hLL'.symm hcon.1 hcon.2
  have hSH : ∀ x ∈ s1516 T Z₁, x ∈ Subgroup.normalizer (L : Set G) ∨
      s⁻¹ * x ∈ Subgroup.normalizer (L : Set G) := by
    intro x hx
    rcases hconj x (s1516_le_g1 T Z₁ hx) with h | h
    · exact Or.inl (s151t_mem_normalizer_of_conjSub h)
    · right
      apply s151t_mem_normalizer_of_conjSub
      rw [B6.conjSub_mul, h, ← B6.conjSub_mul, inv_mul_cancel, B6.conjSub_one]
  have hcfg : WreathCfg L P (s1516 T Z₁) s :=
    { s2 := hc.h18.four.2.1
      hs := hsS
      hsN := hsN
      hSH := hSH
      blk := h3
      perf := perfect_of_mem_cComp hLcomp
      nLL' := le_normalizer_of_mem_cComp hL'comp hLcomp
      nL'L := le_normalizer_of_mem_cComp hLcomp hL'comp
      comm := fun x hx =>
        ((lemma_1_2_1_two hq.qtke hq.simple hq.nonabelian h37 hpc hLcomp hL'comp hLL'.symm).1 hx).1
      par := hpar
      big := hbig }
  have hHG : P ⊔ s1516 T Z₁ ≤ g1_1516 Z₁ := sup_le (hpar.le.trans hLG) (s1516_le_g1 T Z₁)
  have hSyl : IsSylowTwoOf (s1516 T Z₁) (P ⊔ s1516 T Z₁) :=
    ya7_isSylowTwoOf_restrict hc.h18.four le_sup_right hHG
  exact ⟨hcfg.charTwo, hcfg.isMinParabolic hSyl, hcfg.not_C126Third⟩

theorem input15122L3WreathStar_holds (h118 : TheoremC118) (h126 : TheoremC126) (h37 : A37ForSQTK)
    (h38 : A38ForSQTK) : Input15122L3WreathStar :=
  input15122L3WreathStar_of_minPar h118 h126 (input15122L3WreathMinPar_of h37 h38)

end CFSG.Quasithin
