module

public import CFSG.Quasithin.Vol2.Ch10SecB6Prep
public import CFSG.Quasithin.Vol2.Ch10SecB6C27
public import CFSG.Quasithin.Vol2.Ch10SecB6Lt
public import CFSG.Quasithin.Vol2.Ch10SecB6Rank
public import CFSG.Quasithin.Vol2.Ch10SecB6S21
public import CFSG.Quasithin.Vol2.Ch10SecB6Syl

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecB

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Quasithin.H13

variable {G : Type} [Group G] [Finite G] {T L I : Subgroup G}

theorem false_of_lt
    (hF2 : Fact10_2_6Rank) (hgap : Gap10_2_6Nonquasi)
    (hC27 : C27NoL2pJ1) (hList : Vol2Native.A312ListFactsCat)
    (hSL2 : A312SL2Fact) (h36 : Vol2Native.A36CoreForSQTKCat) (h37 : Vol2Native.A37ForSQTKCat)
    (h38 : Vol2Native.A38ForSQTKCat) (h39 : Vol2Native.A39ForSQTKCat) (h331 : Stmt3_3_1)
    (h1011 : Stmt10_1_1) (hyp : Hyp10 G T L I) {t : G} (ht : t ∈ T)
    (htn : t ∉ Subgroup.normalizer (L : Set G)) {X Y H K K' : Subgroup G}
    (hX : X = L ∨ X = CFSG.conjugate L t) (hY : Y = L ∨ Y = CFSG.conjugate L t)
    (hH : InM (fsuL0 T L ⊔ T1 T L) H) (hHM : H ≠ fsuM T L) (hS : IsSylowTwoOf (T1 T L) H)
    (hKc : K ∈ cComp H) (hK'c : K' ∈ cComp H) (hKK' : K ≠ K')
    (hKn : H ≤ Subgroup.normalizer (K : Set G)) (hXK : X < K) (hYK' : Y ≤ K') : False := by
  have := hyp.fsu.simple
  have hK : LocalSQTK G := (qtkeCore_of_cat hyp.fsu.nonabelian hyp.fsu.qtke).1
  have hH2 : pCoreOf 2 H ≠ ⊥ := (inH_of_inM hH).2
  have hL0H : fsuL0 T L ≤ H := le_sup_left.trans hH.2
  have hT1M : T1 T L ≤ fsuM T L := inf_le_left.trans (le_fsuM T L)
  obtain ⟨hXc, -, hXL0, ⟨eX⟩⟩ := li_data h37 h38 hyp ht hX
  obtain ⟨-, -, hYL0, ⟨eY⟩⟩ := li_data h37 h38 hyp ht hY
  have hXH : X ≤ H := hXL0.trans hL0H
  have hXfam := cComp_subset_lFamily hT1M hXc
  obtain ⟨fX⟩ := nonempty_modO2_modO2Image hXH
  have hOK : A37.oddCoreOf K = ⊥ := le_bot_iff.mp ((oddCoreOf_eq_bot h37 h38 h331 h1011 hyp hH) ▸
    A37.oddCoreOf_le_of_subnormal (subnormal_of_mem_cComp hKc))
  have hsL : IsSimpleGroup (ModO2 L) := SecA.isSimpleGroup_of_not_normal h37 h38
    hyp.fsu.simple hyp.fsu.nonabelian hyp.fsu.qtke hyp.fsu.faithful hyp.not_normal
  obtain ⟨a, b, hab⟩ := exists_mul_ne_mul_modO2 hyp
  have hrk : ¬ ∃ p : ℕ, p.Prime ∧ p ≠ 2 ∧ p ∣ Nat.card (ModO2 (modO2Image H X)) ∧
      2 ≤ CFSG.Open.pRank p (modO2Image H K) := by
    rintro ⟨p, hp, hp2, hpd, h2p⟩
    have h1 := pRank_modO2Image_le_one hyp.fsu.qtke hH2
      (commutator_le_pCoreOf_H hK h37 hH2 hKc hK'c hKK') hYK' (hYL0.trans hL0H)
      eY.isSimpleGroup ⟨eY.symm a, eY.symm b, fun h => hab (eY.symm.injective (by
        rw [map_mul, map_mul]
        exact h))⟩ hp hp2
      (by rw [Nat.card_congr eY.toEquiv, ← Nat.card_congr (fX.trans eX).toEquiv]; exact hpd)
    omega
  have hQ := Vol2Native.sqtkHypCat_quotient_of_pCoreOf_ne_bot hK hH2
  obtain ⟨L', hL'c, -, huniq, hcases⟩ := a312Refined_of_facts hList hSL2 h36 h37 h39 hQ _
    (isSylowTwoOf_modO2Image hS) _ (modO2Image_mem_lFamily hS hXH hXfam)
  obtain rfl : modO2Image H K = L' :=
    huniq _ (modO2Image_mem_cComp hKc) (modO2Image_mono' hXK.le)
  rcases hcases with heq | ⟨hq, hcase⟩ | ⟨hnq, hnonq⟩
  · exact modO2Image_ne hS hXfam hKc hXK heq
  ·
    obtain ⟨h1, h2⟩ := hF2 _ _ _ hcase
    rcases lbar_type h1011 hyp (fX.trans eX) with hty | hty
    · exact hrk (h1 hty)
    rcases h2 hty with h | ⟨hO2, hC⟩
    · exact hrk h
    by_cases hch : CharTwo K
    · obtain ⟨eK⟩ := modO2_mulEquiv hKc
      refine false_of_c27 hC27 hK h331 h37 h38 hyp ht hX hH hS hKc hKn hXK hch
        (CFSG.LocalCores.isQuasisimple_of_mulEquiv eK.symm hq) ?_
      rcases hC with (⟨p, hp, hp3, -, hL2⟩ | ⟨-, p, hp, hL1, h5, h8⟩) | ⟨-, hJ1⟩
      · exact Or.inr (Or.inl ⟨p, hp, hp3, hL2⟩)
      · exact Or.inl ⟨p, hp, hL1, h5, h8⟩
      · exact Or.inr (Or.inr hJ1)
    · exact pCore_modO2Image_ne_bot h37 h38 hyp ht hX hKc hXK.le
        (isQuasisimple_of_not_charTwo hKc hOK hch) hO2
  ·
    by_cases hch : CharTwo K
    · by_cases h21 : modO2Image H K = modO2Image H X ⊔
          (CFSG.oddCore ↥(modO2Image H K)).map (modO2Image H K).subtype
      · exact false_of_shape21 hK h36 h331 h37 h38 h1011 hyp ht hX hH hS hKc hKn hXK hnq h21
      · exact hgap G T L I hyp H hH hHM X K (hX.imp id fun h => ⟨t, ht, htn, h⟩) hKc hXK hch
          hnonq h21
    · exact hnq (isQuasisimple_modO2Image hKc (isQuasisimple_of_not_charTwo hKc hOK hch))

theorem unique_L0T1
    (hF1 : Fact10_2_6Pair) (hF2 : Fact10_2_6Rank)
    (hgap : Gap10_2_6Nonquasi) (hC27 : C27NoL2pJ1)
    (hList : Vol2Native.A312ListFactsCat) (hSL2 : A312SL2Fact)
    (h36 : Vol2Native.A36CoreForSQTKCat) (h37 : Vol2Native.A37ForSQTKCat)
    (h38 : Vol2Native.A38ForSQTKCat) (h39 : Vol2Native.A39ForSQTKCat) (h331 : Stmt3_3_1)
    (h1011 : Stmt10_1_1) (h1025 : Stmt10_2_5) (hyp : Hyp10 G T L I) :
    IsUniqueM (fsuL0 T L ⊔ T1 T L) (fsuM T L) := by
  have := hyp.fsu.simple
  have hK : LocalSQTK G := (qtkeCore_of_cat hyp.fsu.nonabelian hyp.fsu.qtke).1
  refine ⟨⟨fsuM_isMaxTwoLocal h331 hyp,
    sup_le (SecA.fsuL0_le_fsuM T L) (inf_le_left.trans (le_fsuM T L))⟩, fun H hH => ?_⟩
  by_contra hHM
  obtain ⟨t, ht, htn⟩ := IsConcreteLE.not_le_iff_exists.mp hyp.not_normal
  have hS := isSylowTwoOf_T1_of_inM h331 h37 h38 h1025 hyp hH hHM
  have hL0H : fsuL0 T L ≤ H := le_sup_left.trans hH.2
  obtain ⟨hc₁, hn₁, hle₁, -⟩ := li_data h37 h38 hyp ht (X := L) (Or.inl rfl)
  obtain ⟨hc₂, hn₂, hle₂, -⟩ := li_data h37 h38 hyp ht (X := CFSG.conjugate L t) (Or.inr rfl)
  obtain ⟨K₁, hK₁, hLK₁, hN₁⟩ :=
    exists_cComp_of_inM hK h37 h38 h39 hH hS hc₁ (hle₁.trans hL0H) hn₁
  obtain ⟨K₂, hK₂, hLK₂, hN₂⟩ :=
    exists_cComp_of_inM hK h37 h38 h39 hH hS hc₂ (hle₂.trans hL0H) hn₂
  have hne : K₁ ≠ K₂ := fun h =>
    false_of_le_cComp hF1 hK h37 h38 hyp ht htn hH hS hK₁ hLK₁ (by rw [h]; exact hLK₂)
  have hK₁H := le_of_mem_cComp hK₁
  have hK₂H := le_of_mem_cComp hK₂
  rcases lt_or_lt h331 h37 h38 hyp ht htn hH hHM hLK₁ hLK₂ hK₁H hK₂H hN₁ hN₂ with h | h
  · exact false_of_lt hF2 hgap hC27 hList hSL2 h36 h37 h38 h39 h331 h1011 hyp ht htn
      (Or.inl rfl) (Or.inr rfl) hH hHM hS hK₁ hK₂ hne
      ((Subgroup.normal_subgroupOf_iff_le_normalizer hK₁H).mp hN₁) h hLK₂
  · exact false_of_lt hF2 hgap hC27 hList hSL2 h36 h37 h38 h39 h331 h1011 hyp ht htn
      (Or.inr rfl) (Or.inl rfl) hH hHM hS hK₂ hK₁ hne.symm
      ((Subgroup.normal_subgroupOf_iff_le_normalizer hK₂H).mp hN₂) h hLK₁

theorem stmt10_2_6_of
    (hF1 : Fact10_2_6Pair) (hF2 : Fact10_2_6Rank)
    (hgap : Gap10_2_6Nonquasi) (hC27 : C27NoL2pJ1)
    (hList : Vol2Native.A312ListFactsCat) (hSL2 : A312SL2Fact)
    (h36 : Vol2Native.A36CoreForSQTKCat) (h37 : Vol2Native.A37ForSQTKCat)
    (h38 : Vol2Native.A38ForSQTKCat) (h39 : Vol2Native.A39ForSQTKCat) (h331 : Stmt3_3_1)
    (h1011 : Stmt10_1_1) (h1025 : Stmt10_2_5) : Stmt10_2_6 := by
  intro G _ _ T L I hyp
  have hU := unique_L0T1 hF1 hF2 hgap hC27 hList hSL2 h36 h37 h38 h39 h331 h1011 h1025 hyp
  exact ⟨hU, two_of_unique h37 h38 h1011 hyp hU⟩

end CFSG.Quasithin.Vol2.Ch10.SecB
