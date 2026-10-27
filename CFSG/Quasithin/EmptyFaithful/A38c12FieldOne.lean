module

public import CFSG.Quasithin.Background.GoldschmidtS146RAut
public import CFSG.Quasithin.Background.GoldschmidtS146RProper
public import CFSG.Quasithin.Background.GoldschmidtS146RFour
public import CFSG.Quasithin.EmptyFaithful.S146F4
public import CFSG.Quasithin.Background.GoldschmidtS146RArith
public import CFSG.Quasithin.Background.E2Two
public import CFSG.Quasithin.Background.E2TwoNoNStmt
public import CFSG.Sporadic.Schreier.J4SProfileNode
public import CFSG.LocalAnalysis.ComponentInitial.SylowPointRecovery

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.GoldS146R

namespace A38c12

section Field

variable {Γ : Type} [Group Γ]

@[expose] def E22Field (H T M K : Subgroup Γ) (n : ℕ) : Prop :=
  (2 ≤ n ∧ (IsPSL 2 2 n ↥(E2.star M H K) ∨ IsSz n ↥(E2.star M H K)) ∧
      E2.IsBorelIn (E2.star M H K) (E2.star M H (M ⊓ K))) ∨
    (E2.IsBenderOf n ↥(E2.star M H K) ∧ E2.IsBorelIn (E2.star M H K) (E2.star M H (M ⊓ K))) ∨
    (1 ≤ n ∧ (IsPSL 3 2 n ↥(E2.star M H K) ∨ E2.IsSp4Prime n ↥(E2.star M H K)) ∧
      E2.IsDiagramNontrivial (E2.star M H T) (E2.star M H K) (E2.star M H (T ⊓ K)) ∧
      E2.IsBorelIn (E2.star M H K) (E2.star M H (M ⊓ K)))

theorem E22Field.one_le {H T M K : Subgroup Γ} {n : ℕ} (h : E22Field H T M K n) : 1 ≤ n := by
  unfold E22Field at h
  rcases h with ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩
  · omega
  · have := h.1
    omega
  · exact h

end Field

@[expose] def FieldOne146 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M : Subgroup G), Setting146 G T M →
    ∀ H₂ K₂ : Subgroup G, IsHStar T M H₂ → ¬ Group.IsSolvable ↥H₂ → K₂ ∈ cComp H₂ → H₂ = K₂ ⊔ T →
      E2.E22CasesNoN H₂ T (H₂ ⊓ M) K₂ → ∀ n : ℕ, E22Field H₂ T (H₂ ⊓ M) K₂ n → n = 1

section Cases

variable {G : Type} [Group G]

theorem e22_cases_false' (hA : ArithAll) {H₂ T M' K₂ : Subgroup G} {m : ℕ} (hm : 2 ≤ m)
    (hcard : Nat.card ↥(E2.star M' H₂ K₂) = ordL2 m)
    (hF1 : ∀ n : ℕ, E22Field H₂ T M' K₂ n → n = 1)
    (h : E2.E22CasesNoN H₂ T M' K₂) : False := by
  have hprof : SrcProfile (ordL2 m) := Or.inl ⟨m, hm, rfl⟩
  have ht0 := hA.t0 m hm
  unfold E2.E22CasesNoN at h
  dsimp only at h
  rcases h with ⟨hker, t', ht'T, hne', hMeq, h1⟩ | ⟨hTN, hker2, h2⟩
  · rcases h1 with ⟨n, hn2, hsh, hB⟩ | ⟨p, hp, hp8, hPSL, -, -⟩
    · have h4 : n = 1 := hF1 n (Or.inl ⟨hn2, hsh, hB⟩)
      omega
    · have hp3 : 3 < p := by
        have := hp.two_le
        omega
      have hT1 : IsT1 p 1 := ⟨hp, hp3, Or.inl rfl, by simpa using hp8⟩
      have := hA.t1 (ordL2 m) p 1 hprof hT1 _ hPSL hcard
      exact ht0.1 this.1
  · rcases h2 with ⟨n, hBn, hB⟩ | ⟨n, hn1', hshape, hdiag, hB⟩ |
        ⟨p, e, hp, hp3, he, h8, hPSL, -, -⟩ | ⟨p, hp, -, hcase, -⟩
    · have h4 : n = 1 := hF1 n (Or.inr (Or.inl ⟨hBn, hB⟩))
      have := hBn.1
      omega
    · have h4 : n = 1 := hF1 n (Or.inr (Or.inr ⟨hn1', hshape, hdiag, hB⟩))
      subst h4
      rcases card_of_shape_two_b hshape with h5 | h5
      · exact ht0.1 (hcard.symm.trans h5)
      · exact ht0.2 (hcard.symm.trans h5)
    · have hT1 : IsT1 p e := ⟨hp, hp3, he, h8⟩
      have := hA.t1 (ordL2 m) p e hprof hT1 _ hPSL hcard
      exact ht0.1 this.1
    · rcases hcase with ⟨h4, hPSU⟩ | ⟨h4, hPSL, -⟩
      · exact hA.t2 (ordL2 m) p hprof hp h4 _ hPSU hcard
      · exact hA.t3 (ordL2 m) p hprof hp h4 _ hPSL hcard

theorem e22_cases_full' (hA : ArithAll) {H T M' K₂ : Subgroup G} {c : ℕ} (hprof : SrcProfile c)
    (hcard : Nat.card ↥(E2.star M' H K₂) = c)
    (hF1 : ∀ n : ℕ, E22Field H T M' K₂ n → n = 1)
    (hTK : T ≤ Subgroup.normalizer (K₂ : Set G)) (h : E2.E22CasesNoN H T M' K₂) :
    ((IsPSL 3 2 1 ↥(E2.star M' H K₂) ∨ IsAlt 6 ↥(E2.star M' H K₂)) ∧
        E2.IsDiagramNontrivial (E2.star M' H T) (E2.star M' H K₂) (E2.star M' H (T ⊓ K₂))) ∨
      (IsPSL 2 7 1 ↥(E2.star M' H K₂) ∧
        8 < E2.autCard (E2.star M' H T) (E2.star M' H K₂)) := by
  unfold E2.E22CasesNoN at h
  dsimp only at h
  rcases h with ⟨hker, t', ht'T, hne', hMeq, h1⟩ | ⟨hTN, hker2, h2⟩
  · exfalso
    exact hne' (Subgroup.mem_normalizer_iff_map_conj_eq.mp (hTK ht'T))
  · rcases h2 with ⟨n, hBn, hB⟩ | ⟨n, hn1', hshape, hdiag, hB⟩ |
        ⟨p, e, hp, hp3, he, h8, hPSL, -, hauto⟩ | ⟨p, hp, -, hcase, -⟩
    · exfalso
      have h4 : n = 1 := hF1 n (Or.inr (Or.inl ⟨hBn, hB⟩))
      have := hBn.1
      omega
    · have h4 : n = 1 := hF1 n (Or.inr (Or.inr ⟨hn1', hshape, hdiag, hB⟩))
      subst h4
      left
      exact ⟨hshape.imp_right isSp4Prime_one_iff.mp, hdiag⟩
    · right
      have hT1 : IsT1 p e := ⟨hp, hp3, he, h8⟩
      obtain ⟨-, rfl, rfl⟩ := hA.t1 c p e hprof hT1 _ hPSL hcard
      exact ⟨hPSL, hauto⟩
    · exfalso
      rcases hcase with ⟨h4, hPSU⟩ | ⟨h4, hPSL, -⟩
      · exact hA.t2 c p hprof hp h4 _ hPSU hcard
      · exact hA.t3 c p hprof hp h4 _ hPSL hcard

end Cases

section Main

variable {G : Type} [Group G] [Finite G] {T M K : Subgroup G}

theorem e22_apply' (hE22 : E2.E22StatementNoN) (hF : FieldOne146) (S : Setting146 G T M)
    {H₂ : Subgroup G} (hStar : IsHStar T M H₂) (hns : ¬ Group.IsSolvable ↥H₂) :
    ∃ K₂ : Subgroup G, K₂ ∈ cComp H₂ ∧ H₂ = K₂ ⊔ T ∧
      E2.E22CasesNoN H₂ T (H₂ ⊓ M) K₂ ∧ ∀ n : ℕ, E22Field H₂ T (H₂ ⊓ M) K₂ n → n = 1 := by
  have hMinP : MinParabolic H₂ T (H₂ ⊓ M) := S.hyp.minParabolic hStar
  have hsqtk : SQTKGroup ↥H₂ := S.sqtkGroup_of_isHTM ⟨hStar.1, hStar.2.1⟩
  obtain ⟨⟨K₂, hK₂c, hHK₂, -, hcases⟩, -⟩ := hE22 G H₂ T (H₂ ⊓ M) hMinP hsqtk hns
  exact ⟨K₂, hK₂c, hHK₂, hcases, fun n hn => hF G T M S H₂ K₂ hStar hns hK₂c hHK₂ hcases n hn⟩

theorem full_case' (hE22 : E2.E22StatementNoN) (hF : FieldOne146) (hA : ArithAll)
    (c : Ctx146 T M K) (hprof : SrcProfile (Nat.card (KBar K)))
    (hStar : IsHStar T M (K ⊔ T)) :
    (KbarIsL3Two K ∨ KbarIsA6 K) ∧
      ∃ s ∈ T ⊓ Subgroup.normalizer (K : Set G), KbarNontrivialOnDynkin K s := by
  have hns : ¬ Group.IsSolvable ↥(K ⊔ T) := fun hs =>
    not_isSolvable_of_mem_cComp c.comp
      (Group.isSolvable_of_isSolvable_injective (f := Subgroup.inclusion c.le_H)
        (Subgroup.inclusion_injective c.le_H))
  obtain ⟨K₂, hK₂c, hHK₂, hcases, hF1⟩ := e22_apply' hE22 hF c.setting hStar hns
  have hK₂K : K₂ ≤ K := le_of_mem_cComp_of_le_sup c le_rfl hK₂c
  have hK₂ : K₂ = K := by
    have h1 : K₂ ∈ cComp K := cComp_mem_of_le hK₂c hK₂K c.le_H
    rw [cComp_self_eq_singleton c.comp] at h1
    exact h1
  rw [hK₂] at hcases hF1
  obtain ⟨e⟩ := nonempty_kbar_equiv_imgJ (J := kerIn ((K ⊔ T) ⊓ M) (K ⊔ T)) c.le_H c.inf_kerIn
  have hcard : Nat.card ↥(E2.star ((K ⊔ T) ⊓ M) (K ⊔ T) K) = Nat.card (KBar K) :=
    (Nat.card_congr e.toEquiv).symm
  rcases e22_cases_full' hA hprof hcard hF1 c.norm hcases with ⟨hKs, hdiag⟩ | ⟨hL27, h8⟩
  · exact dynkin_of_diag c hKs hdiag
  · exact outer_of_autCard c hL27 h8

theorem proper_case_false' (hE22 : E2.E22StatementNoN) (hF : FieldOne146)
    (h1435 : Lemma1435) (hA : ArithAll) (c : Ctx146 T M K)
    (hLat : LatShape (KBar K) (imgJ K (pCoreOf 2 K) (T ⊓ K)))
    {H₂ : Subgroup G} (hStar : IsHStar T M H₂) (hH₂ : H₂ ≤ K ⊔ T) (hne : H₂ ⊓ K ≠ K) :
    False := by
  have hTM := c.le_M
  have hTH₂ : T ≤ H₂ := hStar.1.1
  have hYK : H₂ ⊓ K ≤ K := inf_le_right
  have hYH : H₂ ⊓ K ≤ H₂ := inf_le_left
  have hSY : T ⊓ K ≤ H₂ ⊓ K := inf_le_inf_right K hTH₂
  have hJS : pCoreOf 2 K ≤ T ⊓ K := c.pCore_le
  have hJY : pCoreOf 2 K ≤ H₂ ⊓ K := hJS.trans hSY
  have hsupY : H₂ = T ⊔ (H₂ ⊓ K) :=
    A3.eq_sup_inf_of_le_sup c.norm hTH₂ (hH₂.trans (sup_comm K T).le)
  have hH₂norm : H₂ ≤ Subgroup.normalizer (K : Set G) :=
    hH₂.trans (sup_le Subgroup.le_normalizer c.norm)
  have hYnorm : ((H₂ ⊓ K).subgroupOf H₂).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hYH).mpr (fun h hh =>
      Subgroup.inf_normalizer_le_normalizer_inf ⟨Subgroup.le_normalizer hh, hH₂norm hh⟩)
  have hU : imgJ K (pCoreOf 2 K) (T ⊓ K) ≤ imgJ K (pCoreOf 2 K) (H₂ ⊓ K) := imgJ_mono hSY
  have htop : imgJ K (pCoreOf 2 K) (H₂ ⊓ K) ≠ ⊤ := fun h => hne ((imgJ_eq_top_iff hJY hYK).mp h)
  have hH₂M : ¬ H₂ ≤ M := hStar.2.1
  rcases hLat _ hU htop with h1 | h2 | ⟨m, hm, hns, Q, _, π, hπ, hker, hQ, hQcard⟩
  ·
    apply hH₂M
    have hYB : H₂ ⊓ K ≤ Subgroup.normalizer ((T ⊓ K : Subgroup G) : Set G) :=
      le_normalizer_of_imgJ hJS hSY hYK h1
    calc H₂ = T ⊔ (H₂ ⊓ K) := hsupY
      _ ≤ M := sup_le hTM ((le_inf hYK hYB).trans c.borel)
  ·
    apply hH₂M
    have e1 := card_imgJ_mul hJY hYK (H := K)
    have e2 := card_imgJ_mul hJS (hSY.trans hYK) (H := K)
    have h3 : Nat.card ↥(H₂ ⊓ K) = 3 * Nat.card ↥(T ⊓ (H₂ ⊓ K)) := by
      have e : T ⊓ (H₂ ⊓ K) = T ⊓ K := by rw [← inf_assoc, inf_of_le_left hTH₂]
      rw [e, ← e1, ← e2, h2]
      ring
    have hrel : T.relIndex H₂ = 3 := relIndex_eq_of_card hTH₂ hYH hsupY hYnorm h3
    exact h1435 G T M c.setting.hyp c.setting.notSix H₂ hStar.1 (Or.inl hrel)
  ·
    have hnsH₂ : ¬ Group.IsSolvable ↥H₂ := by
      intro hs
      apply hns
      have : Group.IsSolvable ↥(H₂ ⊓ K) :=
        Group.isSolvable_of_isSolvable_injective (f := Subgroup.inclusion hYH)
          (Subgroup.inclusion_injective hYH)
      exact isSolvable_imgJ hYK this
    obtain ⟨K₂, hK₂c, hH₂K₂, hcases, hF1⟩ := e22_apply' hE22 hF c.setting hStar hnsH₂
    have hK₂H₂ : K₂ ≤ H₂ := le_of_mem_cComp hK₂c
    have hK₂K : K₂ ≤ K := le_of_mem_cComp_of_le_sup c hH₂ hK₂c
    have hK₂Y : K₂ ≤ H₂ ⊓ K := le_inf hK₂H₂ hK₂K
    have hsub : IsSubnormal K₂ (H₂ ⊓ K) :=
      A3.subnormal_of_le_of_le (subnormal_of_mem_cComp hK₂c) hK₂Y hYH
    have heq := imgJ_eq_perfectCore hK₂Y hYK hsub (perfect_of_mem_cComp hK₂c)
      (not_isSolvable_of_mem_cComp hK₂c) π hπ hker hQ
    have hQnab := nonab_of_card_ordL2 hQ hm hQcard
    obtain ⟨e₂⟩ := exists_kbar_equiv hK₂Y hYK heq π hπ hker hQ hQnab
    have hsimp₂ : IsSimpleGroup (KBar K₂) := by
      have := hQ
      exact e₂.isSimpleGroup
    have hsylH₂ : IsSylowTwoOf T H₂ :=
      isSylowTwoOf_of_quasithinIsSylowTwo c.setting.hyp.sylow hTH₂
    have hJ₂H₂ : kerIn (H₂ ⊓ M) H₂ ≤ H₂ := kerIn_le.trans inf_le_left
    have hOJ₂ : pCoreOf 2 K₂ ≤ kerIn (H₂ ⊓ M) H₂ :=
      (A4.pCoreOf_le_of_subnormal 2 (subnormal_of_mem_cComp hK₂c)).trans
        (pCoreOf_le_kerIn c hsylH₂)
    have hK₂J₂ : ¬ K₂ ≤ kerIn (H₂ ⊓ M) H₂ := by
      intro h
      apply hH₂M
      calc H₂ = K₂ ⊔ T := hH₂K₂
        _ ≤ M := sup_le (h.trans (kerIn_le.trans inf_le_right)) hTM
    have hKJ : K₂ ⊓ kerIn (H₂ ⊓ M) H₂ = pCoreOf 2 K₂ :=
      inf_eq_pCoreOf_of_simple hK₂H₂ hJ₂H₂ hOJ₂ hK₂J₂ hsimp₂
    obtain ⟨eKs⟩ := nonempty_kbar_equiv_imgJ (J := kerIn (H₂ ⊓ M) H₂) hK₂H₂ hKJ
    have hcard : Nat.card ↥(E2.star (H₂ ⊓ M) H₂ K₂) = ordL2 m :=
      (Nat.card_congr eKs.toEquiv).symm.trans ((Nat.card_congr e₂.toEquiv).trans hQcard)
    exact e22_cases_false' hA hm hcard hF1 hcases

theorem rank2_main' (hE22 : E2.E22StatementNoN) (hF : FieldOne146) (h1435 : Lemma1435)
    (hA : ArithAll) (c : Ctx146 T M K) (hprof : SrcProfile (Nat.card (KBar K)))
    (hLat : LatShape (KBar K) (imgJ K (pCoreOf 2 K) (T ⊓ K))) :
    (KbarIsL3Two K ∨ KbarIsA6 K) ∧
      ∃ s ∈ T ⊓ Subgroup.normalizer (K : Set G), KbarNontrivialOnDynkin K s := by
  obtain ⟨H₂, hStar, hH₂⟩ := exists_hstar_below c.htm.1 c.htm.2
  by_cases hY : H₂ ⊓ K = K
  · have hKH₂ : K ≤ H₂ := hY ▸ inf_le_left
    have hH : H₂ = K ⊔ T := le_antisymm hH₂ (sup_le hKH₂ hStar.1.1)
    rw [hH] at hStar
    exact full_case' hE22 hF hA c hprof hStar
  · exact (proper_case_false' hE22 hF h1435 hA c hLat hStar hH₂ hY).elim

end Main

theorem input14620Rank2_of' (hE22 : E2.E22StatementNoN) (hF : FieldOne146) (h1435 : Lemma1435) :
    Input14620Rank2 := by
  intro G _ _ T M S K hHTM hKc hTN hsimp hR2 hBM
  have c : GoldS146R.Ctx146 T M K := ⟨S, hHTM, hKc, hTN, hsimp, hBM⟩
  obtain ⟨hFour, h7, hM, h45⟩ := hR2
  have h4 : ¬ IsPSL 4 2 1 (KBar K) := fun h => h45 (Or.inl h)
  have h5 : ¬ IsPSL 5 2 1 (KBar K) := fun h => h45 (Or.inr h)
  have hSyl : IsSylowTwoOf (imgJ K (pCoreOf 2 K) (T ⊓ K)) ⊤ :=
    isSylowTwoOf_imgJ c.sylow_inf c.pCore_le
  exact rank2_main' hE22 hF h1435 arithAll c (srcProfile_of_fourList hFour h7 hM h4 h5)
    (latShape_of_fourList hFour h7 hM h4 h5 hSyl)

theorem input14620Bender_of'
    (hE22 : E2.E22StatementNoN) (hF : FieldOne146) : Input14620Bender := by
  intro G _ _ T M S K hHTM hKc hpair hsimp hshape hBM
  obtain ⟨t, htT, htK, hK₀, hcomm⟩ := hpair
  set K₀ : Subgroup G := conjClosure K T with hK₀def
  set H : Subgroup G := K₀ ⊔ T with hHdef
  set Kt : Subgroup G := K.map (MulAut.conj t).toMonoidHom with hKtdef
  have hsyl : IsSylowTwoOf T H := isSylowTwoOf_of_quasithinIsSylowTwo S.hyp.sylow le_sup_right
  have hBen : fusionIsBenderGroup (KBar K) := fusionIsBenderGroup_of_shape hshape
  obtain ⟨hdich, hclass⟩ := pair_facts hsyl hKc htT htK hK₀ hcomm hsimp hBen
  have hTM : T ≤ M := S.hyp.m_max.1.2
  have hStar : IsHStar T M H := by
    refine ⟨hHTM.1, hHTM.2, fun Y hY hYH hYM => ?_⟩
    by_contra hne
    apply hYM
    rcases hdich Y hY.1 hYH with hfull | hnorm
    · exact absurd (le_antisymm hYH (sup_le hfull hY.1)) hne
    · have hY0 : Y ⊓ K₀ ≤ M := (le_inf inf_le_right hnorm).trans hBM
      have hYeq : Y = T ⊔ (Y ⊓ K₀) :=
        A3.eq_sup_inf_of_le_sup (le_normalizer_conjClosure K T) hY.1
          (hYH.trans (sup_comm K₀ T).le)
      rw [hYeq]
      exact sup_le hTM hY0
  have hMinP : MinParabolic H T (H ⊓ M) := S.hyp.minParabolic hStar
  have hsqtk : SQTKGroup ↥H := S.sqtkGroup_of_isHTM hHTM
  have hKH : K ≤ H := le_of_mem_cComp hKc
  have hnonsolv : ¬ Group.IsSolvable ↥H := fun hs => by
    have : Group.IsSolvable ↥H := hs
    exact not_isSolvable_of_mem_cComp hKc
      (Group.isSolvable_of_isSolvable_injective (f := Subgroup.inclusion hKH)
        (Subgroup.inclusion_injective hKH))
  obtain ⟨⟨K₂, hK₂c, hHK₂, hqs, hcases⟩, -⟩ := hE22 G H T (H ⊓ M) hMinP hsqtk hnonsolv
  have hK₂cl := hclass K₂ hK₂c
  have hF1 : ∀ n : ℕ, E22Field H T (H ⊓ M) K₂ n → n = 1 := fun n hn =>
    hF G T M S H K₂ hStar hnonsolv hK₂c hHK₂ hcases n hn
  unfold E2.E22CasesNoN at hcases
  dsimp only at hcases
  rcases hcases with ⟨hker, t', ht'T, hne', hMeq, h1⟩ | ⟨hTN, hker2, h2⟩
  ·
    rcases h1 with ⟨n, hn2, hsh, hB⟩ | ⟨p, hp, hp8, hPSL, -, -⟩
    · have h4 : n = 1 := hF1 n (Or.inl ⟨hn2, hsh, hB⟩)
      omega
    ·
      have hK₂H : K₂ ≤ H := le_of_mem_cComp hK₂c
      have hKJ : K₂ ⊓ kerIn (H ⊓ M) H = pCoreOf 2 K₂ := by
        rw [hker]
        exact inf_pCoreOf_eq_of_mem_cComp hK₂c
      obtain ⟨eKs⟩ := nonempty_kbar_equiv_imgJ (J := kerIn (H ⊓ M) H) hK₂H hKJ
      have hcard : Nat.card (KBar K) = Nat.card ↥(E2.star (H ⊓ M) H K₂) := by
        rcases hK₂cl with rfl | rfl
        · exact Nat.card_congr eKs.toEquiv
        · obtain ⟨ec⟩ := nonempty_kbar_conj t K
          exact (Nat.card_congr ec.toEquiv).symm.trans (Nat.card_congr eKs.toEquiv)
      exact false_of_shape_card_eq_psl_two_odd hp8 hPSL hshape hcard
  ·
    rcases hK₂cl with rfl | rfl
    · exact htK (hTN htT)
    · apply htK
      have h5 : t ∈ Subgroup.normalizer
          ((K.map (MulAut.conj t).toMonoidHom : Subgroup G) : Set G) := hTN htT
      have h6 := Subgroup.mem_normalizer_iff_map_conj_eq.mp h5
      exact A38.map_conj_eq_iff.mp (Subgroup.map_injective (MulAut.conj t).injective (h6.trans rfl))

theorem input14620Rank2_Bender_of_fieldOne (hE22 : E2.E22StatementNoN) (hF : FieldOne146)
    (h1435 : Lemma1435) : Input14620Rank2 ∧ Input14620Bender :=
  ⟨input14620Rank2_of' hE22 hF h1435, input14620Bender_of' hE22 hF⟩

end A38c12

end CFSG.Quasithin
