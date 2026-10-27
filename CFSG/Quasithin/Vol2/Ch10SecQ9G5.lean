module

public import CFSG.Quasithin.Vol2.Ch10SecQ9G4
public import CFSG.Quasithin.Vol2.Ch10SecB6Prep
public import CFSG.Quasithin.Vol2.Ch10SecB6Lt
public import CFSG.Quasithin.Vol2.Ch10SecB6Rank
public import CFSG.Quasithin.Vol2.Ch10SecQ9G3

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecC.C10P4F

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Quasithin.H13

variable {G : Type} [Group G] [Finite G]

namespace RCtx

variable {T L I R H : Subgroup G} (c : RCtx T L I R H)
include c

theorem false_of_nonquasi (hK : LocalSQTK G)
    (h36 : Vol2Native.A36CoreForSQTKCat) (h37 : Vol2Native.A37ForSQTKCat)
    (h38 : Vol2Native.A38ForSQTKCat) (h331 : Stmt3_3_1) {t : G} (ht : t ∈ T)
    {X K : Subgroup G} (hX : X = L ∨ X = CFSG.conjugate L t) (hKc : K ∈ cComp H)
    (hKn : H ≤ Subgroup.normalizer (K : Set G)) (hXK : X < K)
    (hNQ : A312Nonquasi (modO2Image H X) (modO2Image H K))
    (hne : modO2Image H K ≠ modO2Image H X ⊔
      (CFSG.oddCore ↥(modO2Image H K)).map (modO2Image H K).subtype) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hcase, hcommon, -⟩ := Vol2Native.lemma_1_2_1_four_core hK h36 c.two hKc
  rcases hNQ with ⟨-, h21, -⟩ | ⟨hcomm, ⟨p, hp, hp5, -, hSLp⟩, N, hNn, hNeq, hSL5⟩
  · exact hne h21
  rcases hcase with hc | ⟨p', hp', hp'3, -, he0, hnat⟩ | ⟨-, -, hSL5', -⟩
  ·
    rcases SecB.C10P34.le_center_or_comm hc.1 (CFSG.oddCore ↥(modO2Image H K)) with hz | hab
    · apply hcomm
      rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
      rintro _ ⟨o, ho, rfl⟩ k hk
      exact congrArg Subtype.val (Subgroup.mem_center_iff.mp (hz ho) ⟨k, hk⟩)
    · obtain ⟨a, b, hab'⟩ := hcommon.2.1.2.2
      obtain ⟨a', rfl⟩ := QuotientGroup.mk_surjective a
      obtain ⟨b', rfl⟩ := QuotientGroup.mk_surjective b
      obtain ⟨a'', rfl⟩ := QuotientGroup.mk_surjective a'
      obtain ⟨b'', rfl⟩ := QuotientGroup.mk_surjective b'
      apply hab'
      have h1 := hab (QuotientGroup.mk a'') (QuotientGroup.mk b'')
      rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq] at h1
      have h2 : (QuotientGroup.mk (a'' * b'') :
          ↥(modO2Image H K) ⧸ CFSG.fittingSubgroup ↥(modO2Image H K)) =
          QuotientGroup.mk (b'' * a'') := by
        rw [QuotientGroup.eq, hcommon.1]
        exact h1
      simp only [← QuotientGroup.mk_mul]
      rw [h2]
  ·
    have := hNn
    exact c.false_of_natural hK h331 h37 h38 ht hX hKn hXK.le hp' hp'3 he0 hnat
      (by rw [hcommon.1]) N hNeq hSL5
  ·
    obtain ⟨e5⟩ := hSL5'
    obtain ⟨ep⟩ := hSLp
    have : Fact p.Prime := ⟨hp⟩
    have h5 := SecB.C10P34.eq_five_of_sl2_equiv
      ((e5.symm.trans (QuotientGroup.quotientMulEquivOfEq hcommon.1)).trans ep)
    rw [h5] at hp5
    norm_num at hp5

theorem false_of_lt (hF2 : SecB.Fact10_2_6Rank)
    (hC27 : C27NoL2pJ1)
    (hList : Vol2Native.A312ListFactsCat) (hSL2 : A312SL2Fact)
    (h36 : Vol2Native.A36CoreForSQTKCat) (h37 : Vol2Native.A37ForSQTKCat)
    (h38 : Vol2Native.A38ForSQTKCat) (h39 : Vol2Native.A39ForSQTKCat) (h331 : Stmt3_3_1)
    (h1011 : Stmt10_1_1) {t : G} (ht : t ∈ T) {X Y K K' : Subgroup G}
    (hX : X = L ∨ X = CFSG.conjugate L t) (hY : Y = L ∨ Y = CFSG.conjugate L t)
    (hKc : K ∈ cComp H) (hK'c : K' ∈ cComp H) (hKK' : K ≠ K')
    (hKn : H ≤ Subgroup.normalizer (K : Set G)) (hXK : X < K) (hYK' : Y ≤ K') : False := by
  have hyp := c.hyp
  have := hyp.fsu.simple
  have hK : LocalSQTK G := (qtkeCore_of_cat hyp.fsu.nonabelian hyp.fsu.qtke).1
  have hH2 := c.two
  have hL0H := c.fsuL0_le
  obtain ⟨hXc, -, hXL0, ⟨eX⟩⟩ := SecB.li_data h37 h38 hyp ht hX
  obtain ⟨-, -, hYL0, ⟨eY⟩⟩ := SecB.li_data h37 h38 hyp ht hY
  have hXH : X ≤ H := hXL0.trans hL0H
  have hXfam := cComp_subset_lFamily c.R_le_fsuM hXc
  obtain ⟨fX⟩ := SecB.nonempty_modO2_modO2Image hXH
  have hOK : A37.oddCoreOf K = ⊥ := le_bot_iff.mp ((c.oddCoreOf_eq_bot h37 h38 h331) ▸
    A37.oddCoreOf_le_of_subnormal (subnormal_of_mem_cComp hKc))
  have hsL : IsSimpleGroup (ModO2 L) := SecA.isSimpleGroup_of_not_normal h37 h38
    hyp.fsu.simple hyp.fsu.nonabelian hyp.fsu.qtke hyp.fsu.faithful hyp.not_normal
  obtain ⟨a, b, hab⟩ := SecB.exists_mul_ne_mul_modO2 hyp
  have hrk : ¬ ∃ p : ℕ, p.Prime ∧ p ≠ 2 ∧ p ∣ Nat.card (ModO2 (modO2Image H X)) ∧
      2 ≤ CFSG.Open.pRank p (modO2Image H K) := by
    rintro ⟨p, hp, hp2, hpd, h2p⟩
    have h1 := SecB.pRank_modO2Image_le_one hyp.fsu.qtke hH2
      (SecB.commutator_le_pCoreOf_H hK h37 hH2 hKc hK'c hKK') hYK' (hYL0.trans hL0H)
      eY.isSimpleGroup ⟨eY.symm a, eY.symm b, fun h => hab (eY.symm.injective (by
        rw [map_mul, map_mul]
        exact h))⟩ hp hp2
      (by rw [Nat.card_congr eY.toEquiv, ← Nat.card_congr (fX.trans eX).toEquiv]; exact hpd)
    omega
  have hQ := Vol2Native.sqtkHypCat_quotient_of_pCoreOf_ne_bot hK hH2
  obtain ⟨L', hL'c, -, huniq, hcases⟩ := SecB.a312Refined_of_facts hList hSL2 h36 h37 h39 hQ _
    (SecB.isSylowTwoOf_modO2Image c.sylow) _ (modO2Image_mem_lFamily c.sylow hXH hXfam)
  obtain rfl : modO2Image H K = L' :=
    huniq _ (modO2Image_mem_cComp hKc) (SecB.modO2Image_mono' hXK.le)
  rcases hcases with heq | ⟨hq, hcase⟩ | ⟨hnq, hnonq⟩
  · exact SecB.modO2Image_ne c.sylow hXfam hKc hXK heq
  ·
    obtain ⟨h1, h2⟩ := hF2 _ _ _ hcase
    rcases SecB.lbar_type h1011 hyp (fX.trans eX) with hty | hty
    · exact hrk (h1 hty)
    rcases h2 hty with h | ⟨hO2, hC⟩
    · exact hrk h
    by_cases hch : CharTwo K
    · obtain ⟨eK⟩ := modO2_mulEquiv hKc
      refine c.false_of_c27 hC27 hK h331 h37 h38 ht hX hKc hKn hXK hch
        (CFSG.LocalCores.isQuasisimple_of_mulEquiv eK.symm hq) ?_
      rcases hC with (⟨p, hp, hp3, -, hL2⟩ | ⟨-, p, hp, hL1, h5, h8⟩) | ⟨-, hJ1⟩
      · exact Or.inr (Or.inl ⟨p, hp, hp3, hL2⟩)
      · exact Or.inl ⟨p, hp, hL1, h5, h8⟩
      · exact Or.inr (Or.inr hJ1)
    · exact SecB.pCore_modO2Image_ne_bot h37 h38 hyp ht hX hKc hXK.le
        (SecB.isQuasisimple_of_not_charTwo hKc hOK hch) hO2
  ·
    by_cases hch : CharTwo K
    · by_cases h21 : modO2Image H K = modO2Image H X ⊔
          (CFSG.oddCore ↥(modO2Image H K)).map (modO2Image H K).subtype
      · exact c.false_of_shape21 hK h36 h331 h37 h38 ht hX hKc hKn hXK hnq h21
      · exact c.false_of_nonquasi hK h36 h37 h38 h331 ht hX hKc hKn hXK hnonq h21
    · exact hnq (SecB.isQuasisimple_modO2Image hKc
        (SecB.isQuasisimple_of_not_charTwo hKc hOK hch))

theorem false_main (hF1 : SecB.Fact10_2_6Pair)
    (hF2 : SecB.Fact10_2_6Rank)
    (hC27 : C27NoL2pJ1) (hList : Vol2Native.A312ListFactsCat)
    (hSL2 : A312SL2Fact) (h36 : Vol2Native.A36CoreForSQTKCat) (h37 : Vol2Native.A37ForSQTKCat)
    (h38 : Vol2Native.A38ForSQTKCat) (h39 : Vol2Native.A39ForSQTKCat) (h331 : Stmt3_3_1)
    (h1011 : Stmt10_1_1) : False := by
  have hyp := c.hyp
  have := hyp.fsu.simple
  have hK : LocalSQTK G := (qtkeCore_of_cat hyp.fsu.nonabelian hyp.fsu.qtke).1
  obtain ⟨t, ht, htn⟩ := IsConcreteLE.not_le_iff_exists.mp hyp.not_normal
  have hL0H := c.fsuL0_le
  obtain ⟨hc₁, hn₁, hle₁, -⟩ := SecB.li_data h37 h38 hyp ht (X := L) (Or.inl rfl)
  obtain ⟨hc₂, hn₂, hle₂, -⟩ :=
    SecB.li_data h37 h38 hyp ht (X := CFSG.conjugate L t) (Or.inr rfl)
  obtain ⟨K₁, hK₁, hLK₁, hN₁⟩ :=
    c.exists_cComp hK h37 h38 h39 hc₁ (hle₁.trans hL0H) (c.le_T1.trans hn₁)
  obtain ⟨K₂, hK₂, hLK₂, hN₂⟩ :=
    c.exists_cComp hK h37 h38 h39 hc₂ (hle₂.trans hL0H) (c.le_T1.trans hn₂)
  have hne : K₁ ≠ K₂ := fun h =>
    c.false_of_le_cComp hF1 hK h37 h38 ht htn hK₁ hLK₁ (by rw [h]; exact hLK₂)
  have hK₁H := le_of_mem_cComp hK₁
  have hK₂H := le_of_mem_cComp hK₂
  rcases c.lt_or_lt h37 h38 ht htn hLK₁ hLK₂ hK₁H hK₂H hN₁ hN₂ with h | h
  · exact c.false_of_lt hF2 hC27 hList hSL2 h36 h37 h38 h39 h331 h1011 ht (Or.inl rfl)
      (Or.inr rfl) hK₁ hK₂ hne ((Subgroup.normal_subgroupOf_iff_le_normalizer hK₁H).mp hN₁) h hLK₂
  · exact c.false_of_lt hF2 hC27 hList hSL2 h36 h37 h38 h39 h331 h1011 ht (Or.inr rfl)
      (Or.inl rfl) hK₂ hK₁ hne.symm ((Subgroup.normal_subgroupOf_iff_le_normalizer hK₂H).mp hN₂)
      h hLK₁

end RCtx

end CFSG.Quasithin.Vol2.Ch10.SecC.C10P4F
