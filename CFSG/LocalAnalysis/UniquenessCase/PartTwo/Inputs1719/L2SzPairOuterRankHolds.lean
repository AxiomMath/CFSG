module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.OuterRSplitBar
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.L2SzOuterRSplit
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.OuterRSplitCube
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.L2SzFieldKFacts
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section21.ProofsFifteenRank
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.SeventeenFiftyFive
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC23Odd
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.ConjClosureSimple
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15R1511A
public import CFSG.LocalAnalysis.UniquenessCase.UC22InE229Cong

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719

open CFSG.Open
open CFSG.LocalAnalysis.UniquenessCase.UC22 (calC conjClosure conjSetOf Opp Bar2 barImage IsL2 IsSz)

variable {G : Type} [Group G] [Finite G]

theorem k_L2SzPairOuterRank_of
    (hfam : ∀ (X : Type) [Group X] [Finite X] (n r : ℕ), (IsL2 X n ∨ IsSz X n) →
        r.Prime → 5 < r → r ∣ 2 ^ n - 1 → OuterRSplit X r 1) :
    K_L2SzPairOuterRank := by
  intro H _ _ M L n r hL hshape hcl hr hr5 hrdvd hne
  rw [CFSG.SectionRank.pRank_eq_open_pRank_top, ← CFSG.SectionRank.pRank_eq_pRank_top_subgroup]
  have hr2 : r ≠ 2 := by omega
  have hs : IsSimpleGroup (Bar2 L) := S17.isSimpleGroup_bar2_of_isL2_or_isSz hshape
  have hsplit := hfam (Bar2 L) n r hshape hr hr5 hrdvd
  have hZ : Subgroup.center (Bar2 L) = ⊥ := UC22.uc22p21k_center_eq_bot hL.2.2
  obtain ⟨E, -, hEcard⟩ := hsplit.exists_elemAbelian
  have hdvd : r ∣ Nat.card (Bar2 L) := by
    have h1 := Subgroup.card_subgroup_dvd_card E
    rwa [hEcard, pow_one] at h1
  have hkle := UC22.ncard_conjSetOf_le_pRank hL hr hr2
    (by rw [hZ, Subgroup.card_bot]; exact hr.not_dvd_one) hdvd
  obtain ⟨K, hKmem, hKne⟩ := exists_mem_conjSetOf_ne_of_conjClosure_ne hcl
  have hLmem : L ∈ conjSetOf M L := ⟨1, M.one_mem, by ext; simp⟩
  have h2le : 2 ≤ (conjSetOf M L).ncard := by
    have h := Set.ncard_le_ncard (s := ({L, K} : Set (Subgroup H))) (t := conjSetOf M L)
      (Set.insert_subset hLmem (Set.singleton_subset_iff.2 hKmem)) (Set.toFinite _)
    rwa [Set.ncard_pair (Ne.symm hKne)] at h
  by_cases h3 : 3 ≤ (conjSetOf M L).ncard
  · omega
  have hk2 : (conjSetOf M L).ncard = 2 := by omega
  obtain ⟨g, hgM, rfl⟩ := hKmem
  set L₂ : Subgroup H := L.map (MulAut.conj g).toMonoidHom with hL₂def
  have hL₂ : L₂ ∈ calC M := UC22.uc22p2214_calC_of_mem_conjSetOf hL ⟨g, hgM, rfl⟩
  have hLM : L ≤ M := CFSG.Quasithin.A3.subnormal_le hL.1
  have hL₂M : L₂ ≤ M := CFSG.Quasithin.A3.subnormal_le hL₂.1
  have hcl2 : conjClosure M L = L ⊔ L₂ := UC22.uc22p22d_conjClosure_pair hgM hKne hk2
  obtain ⟨x, hxM, hxN, k, hk⟩ := CFSG.LocalAnalysis.RankThreeUC.S15.exists_pElement_not_mem r M
    (conjClosure M L) fun h => hne (le_antisymm (conjClosure_le_opp hL hs hr hr2 hdvd) h)
  have hxodd : Odd (r ^ k) := (hr.odd_of_ne_two hr2).pow
  have hS : ∀ Y ∈ conjSetOf M L, Y.map (MulAut.conj x).toMonoidHom ∈ conjSetOf M L := by
    rintro _ ⟨h, hhM, rfl⟩
    refine ⟨x * h, M.mul_mem hxM hhM, ?_⟩
    rw [Subgroup.map_map, map_mul]
    rfl
  have hxpow : x ^ r ^ k = 1 := by rw [← hk]; exact pow_orderOf_eq_one x
  have hxL : x ∈ Subgroup.normalizer (L : Set H) := by
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    exact c23_map_conj_eq_of_odd_order hk2 hxodd hxpow hS hLmem
  have hxL₂ : x ∈ Subgroup.normalizer (L₂ : Set H) := by
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    exact c23_map_conj_eq_of_odd_order hk2 hxodd hxpow hS ⟨g, hgM, rfl⟩
  rw [hcl2] at hxN
  obtain ⟨j, hj1, hj2⟩ :=
    exists_pow_pow_not_mem hxN (k := k) (by rw [hxpow]; exact Subgroup.one_mem _)
  have hij : orderOf (x ^ r ^ j) ∣ r ^ k := hk ▸ orderOf_pow_dvd _
  obtain ⟨i, -, hi⟩ := (Nat.dvd_prime_pow hr).1 hij
  have hyM : x ^ r ^ j ∈ M := M.pow_mem hxM _
  have hne₂ : L ≠ L₂ := Ne.symm hKne
  have hc := UC22.uc22p22l_barImage_commute hL hL₂ hne₂
  obtain ⟨e⟩ := s13_bar_equiv hL
  obtain ⟨e₂⟩ := UC22.uc22p20d_bar2_conj g L
  obtain ⟨e₂'⟩ := s13_bar_equiv hL₂
  have hZ₁ := center_barImage_eq_bot hL hZ
  have hZ₂ := center_barImage_eq_bot hL₂ (by
    have h := Subgroup.map_center_eq e₂
    rw [hZ, Subgroup.map_bot] at h
    exact h.symm)
  have hsplit₁ : OuterRSplit (barImage M L) r 1 := hsplit.of_mulEquiv e
  have hsplit₂ : OuterRSplit (barImage M L₂) r 1 := (hsplit.of_mulEquiv e₂).of_mulEquiv e₂'
  have hO₂ : pCoreOf 2 M ≤ Subgroup.normalizer ((L ⊔ L₂ : Subgroup H) : Set H) := by
    intro t ht
    have h1 := UC22.uc22p22u_pCore_normalizes_calC hL ht
    have h2 := UC22.uc22p22u_pCore_normalizes_calC hL₂ ht
    rw [Subgroup.mem_normalizer_iff_map_conj_eq] at h1 h2 ⊢
    rw [Subgroup.map_sup, h1, h2]
  have hy1 := UC22.uc22ine229_mk_mem_normalizer (x := ⟨x ^ r ^ j, hyM⟩) (Subgroup.pow_mem _ hxL _)
  have hy2 := UC22.uc22ine229_mk_mem_normalizer (x := ⟨x ^ r ^ j, hyM⟩) (Subgroup.pow_mem _ hxL₂ _)
  have hy3 := mk_not_mem_barImage hO₂ hr2 hr hyM hi hj1
  rw [s13_barImage_sup hLM hL₂M] at hy3
  have hy4 : (QuotientGroup.mk' (CFSG.pCore 2 ↥M) (⟨x ^ r ^ j, hyM⟩ : ↥M)) ^ r ∈
      barImage M L ⊔ barImage M L₂ := by
    rw [← s13_barImage_sup hLM hL₂M, ← map_pow]
    have : ((⟨x ^ r ^ j, hyM⟩ : ↥M) ^ r) = ⟨(x ^ r ^ j) ^ r, M.pow_mem hyM r⟩ := rfl
    rw [this]
    exact UC22.uc22p21c_mem_barImage.2 ⟨⟨(x ^ r ^ j) ^ r, M.pow_mem hyM r⟩, hj2, rfl⟩
  obtain ⟨E₃, hE₃, hE₃card⟩ :=
    exists_elemAbelian_cube_of_pair hr hc hZ₁ hZ₂ hsplit₁ hsplit₂ hy1 hy2
      (exists_orderOf_mk_eq hyM hr hi) hy3 hy4
  exact le_pRank_of_bar2 hr hr2 hE₃ hE₃card

theorem k_L2SzPairOuterRank_holds : K_L2SzPairOuterRank :=
  k_L2SzPairOuterRank_of fun X _ _ n r h hr _ hrn =>
    h.elim (fun h => outerRSplit_one_of_isL2 h hr hrn) (fun h => outerRSplit_one_of_isSz h hr hrn)

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719
