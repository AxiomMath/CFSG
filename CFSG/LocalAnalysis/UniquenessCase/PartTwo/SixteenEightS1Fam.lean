module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightS1Sym
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightS1E9
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightS1SigElem
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightS1Red
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightS1Rk

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

private theorem s16e_normal_subgroupOf_of_conj {W : Type} [CommGroup W]
    {A L : Subgroup (MulAut W)} (h : ∀ g ∈ A, L.map (MulAut.conj g).toMonoidHom = L) :
    (L.subgroupOf A).Normal := by
  constructor
  intro n hn g
  rw [Subgroup.mem_subgroupOf] at hn ⊢
  have hg := h g g.2
  have hmem : (MulAut.conj (g : MulAut W)).toMonoidHom (n : MulAut W) ∈
      L.map (MulAut.conj (g : MulAut W)).toMonoidHom := Subgroup.mem_map_of_mem _ hn
  rw [hg] at hmem
  simpa [MulAut.conj_apply] using hmem

variable {G : Type} [Group G] [Finite G]

theorem s16e_s1_case4_of_elem (D : Data G) (hx : DataExt D) (h4 : 3 < CFSG.Open.evenRank G)
    (hSg : UC6S846.SigmaStd D) (h61 : UC6.R6_1 D) (h127 : R127 D) (h1214 : F12.R1214 D)
    (h638 : UC6.R6_38 D) (h1110 : R1110Core D) (h63 : UC6.R6_3 D) (h126 : R126 D)
    (h1211 : R1211_1 D) (h111 : W3Thm111 G) (h6161ii : W3Lem616_1ii G) (h77 : F07.R77Eq D)
    (h1219 : ∀ V₀ V : Subgroup G, Hyp125 D V₀ V → D.sig = D.sig1) {V₀ V L : Subgroup G}
    (hV : IsElemAbelian 2 V) (hset : Setting16 D V₀ V L) (hconc : Conc4_136 D V₀ V hV L)
    (hs : s15 D.M V₀ V hV L = 1) {p r : ℕ} (hp : p = 3 ∨ p = 7) (hr : 2 ≤ r)
    (hE : IsElemAbelianOfRank p r ↥(lBar V₀ V hV L))
    (hrk : rk ↥(wTil V₀ V hV L) = (r + 1) * dParam p) : Case168_4 D V₀ V hV L := by
  have hwT : wTil V₀ V hV L = ⊤ := wTil_eq_top_of_case163_2 hconc hs
  have hrkV : rk ↥(⊤ : Subgroup (Vtil V₀ V hV)) = (r + 1) * dParam p := by
    rw [← hwT]
    exact hrk
  have hLA : lBar V₀ V hV L ≤ Mbar D.M V₀ V hV := barSub_mono V₀ V hV hset.hyp151.le
  have hLn : ∀ g ∈ Mbar D.M V₀ V hV,
      (lBar V₀ V hV L).map (MulAut.conj g).toMonoidHom = lBar V₀ V hV L :=
    fun g hg => lBar_conj_eq_of_s15_eq_one hs hg
  obtain ⟨t, htA, ht2, ht1, htrk, hW⟩ := id hconc
  have hsym : SymSumOfConj (Mbar D.M V₀ V hV) ⊤ r (dParam p) := by
    refine s16e_symSum_of_conc4136W hp hr hE hwT hrkV hW ?_
    rintro rfl rfl hinv
    have hT := s15_Infra_vtil_sq_eq_one V₀ V hV
    rw [s16c1610_dParam_three] at hrkV
    have hcard : Nat.card (Vtil V₀ V hV) = 2 ^ 6 := by
      rw [s16e_card_eq_two_pow_rk_top hT, hrkV]
    have hsig := s16e_sig_eq_three_of_rk_le_eight D hx h4 h61 h127 hset.hyp16 hV
      (by omega : rk ↥(⊤ : Subgroup (Vtil V₀ V hV)) ≤ 8)
    have h3 : 3 ∈ D.sig := by
      rw [hsig]
      exact Set.mem_singleton 3
    have hLcard : Nat.card ↥(lBar V₀ V hV L) = 9 := by
      have := A38.card_eq_of_isElemAbelianOfRank Nat.prime_three hE
      simpa using this
    have hX1 : lBar V₀ V hV L ≠ ⊥ := by
      intro hb
      have := Subgroup.card_eq_one.mpr hb
      omega
    have htr : IrrSpanTrans (Mbar D.M V₀ V hV) (lBar V₀ V hV L) :=
      twelve_seventeen D hx h61 h127 h1214 hset.hyp16.hyp125 (lBar V₀ V hV L) hX1 hLA
        (s16e_normal_subgroupOf_of_conj hLn) (Or.inl (by rw [hLcard]; exact ⟨4, by norm_num⟩))
    have hO3 : ∀ N : Subgroup ↥(Mbar D.M V₀ V hV), N.Normal → N.index ≠ 3 := by
      intro N hN
      haveI := hN
      exact s16e_mbar_index_ne_three D h638 h3 hset.hyp16 hV N
    exact s16e_symSum_two_of_E9 hT hcard hLA hLn hE hwT htr hO3
  have hsig := s16e_mem_sig_of_elem D hx h4 hSg h61 h127 h1110 h63 h126 h1211 h111 h6161ii h77
    h1219 hV hset hconc hs hp hr hE hsym
  exact ⟨p, r, hp, by omega, hE, hsym, hsig⟩

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
