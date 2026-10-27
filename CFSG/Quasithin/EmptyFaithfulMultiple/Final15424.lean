module

public import CFSG.Quasithin.EmptyFaithfulMultiple.Lemma15423

public section

namespace CFSG.Quasithin.EmptyFaithfulMultiple

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique

section Helpers

variable {G : Type*} [Group G]

private theorem isSixTwoData_swap {T M Y Y₁ Y₂ : Subgroup G} (h : IsSixTwoData T M Y Y₁ Y₂) :
    IsSixTwoData T M Y Y₂ Y₁ := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, ⟨t, ht, h14⟩, h15, h16,
    h17⟩ := h
  refine ⟨by rw [h1, sup_comm], h3, h2, h5, h4, by rw [h6, sup_comm], by rw [inf_comm, h7], h9,
    h8, h11, h10, h13, h12, ⟨t⁻¹, T.inv_mem ht, ?_⟩, h15, h17, h16⟩
  rw [h14, Subgroup.map_map]
  conv_lhs => rw [← Subgroup.map_id Y₁]
  congr 1
  ext x
  simp [MulAut.conj_apply, mul_assoc]

private theorem sup_eq_of_card_eq_four [Finite G] {A B Q : Subgroup G} (hAQ : A ≤ Q) (hBQ : B ≤ Q)
    (hQ : Nat.card Q = 4) (hA : A ≠ ⊥) (hB : B ≠ ⊥) (hAB : A ⊓ B = ⊥) : A ⊔ B = Q := by
  refine Subgroup.eq_of_le_of_card_ge (sup_le hAQ hBQ) ?_
  rw [hQ]
  by_contra hlt
  push Not at hlt
  have hdvd : Nat.card ↥(A ⊔ B) ∣ 4 := hQ ▸ Subgroup.card_dvd_of_le (sup_le hAQ hBQ)
  have hA2 : 1 < Nat.card A := (Subgroup.one_lt_card_iff_ne_bot _).mpr hA
  have hle := Nat.le_of_dvd Nat.card_pos (Subgroup.card_dvd_of_le (le_sup_left : A ≤ A ⊔ B))
  have heqA : A = A ⊔ B := by
    refine Subgroup.eq_of_le_of_card_ge le_sup_left ?_
    have hc := Nat.le_of_dvd (by norm_num) hdvd
    generalize Nat.card ↥(A ⊔ B) = c at hdvd hle hlt hc ⊢
    interval_cases c <;> omega
  exact hB (le_bot_iff.mp (hAB ▸ le_inf (le_sup_right.trans heqA.ge) le_rfl))

end Helpers

variable {G : Type} [Group G] [Finite G] {T : Subgroup G}

theorem Setting15419.pCoreOf_structure (hyp : MultipleCentralizerHypothesis G T)
    (h11 : Stmt15411 G T) (h12 : Stmt15412 G T) (h19 : Stmt15419 G T) (h20 : Stmt15420 G T)
    (h22 : Stmt15422 G T) (h23 : Stmt15423 G T) (s : Setting15419 G T) (hL₁ : s.L₁ = s.X₁)
    (hL₂ : s.L₂ = s.Y₁) :
    Nat.card (pCoreOf 2 s.L₁) = 4 ∧ Nat.card (pCoreOf 2 s.L₂) = 4 ∧
      pCoreOf 2 s.L₁ ⊓ pCoreOf 2 s.L₂ ≠ ⊥ ∧
      ∃ a ∈ pCoreOf 2 s.L₁ ⊔ pCoreOf 2 s.L₂, ∃ b ∈ pCoreOf 2 s.L₁ ⊔ pCoreOf 2 s.L₂,
        a * b ≠ b * a := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨K, hK, -, ⟨ψ⟩, -⟩ := h22 s (h23 s)
  have hT₀ : IsSylowTwoOf s.T₀ s.I := h20 s s.I ⟨le_rfl, (h19 s).2.2.1⟩
  have hKI : K ≤ s.I := hK.le.trans (oTwoUpper_le s.I)
  have hIK : s.I ≤ Subgroup.normalizer (K : Set G) := by
    rw [hK]
    exact le_normalizer_oTwoUpper s.I
  have hS8 : Nat.card (s.T₀ ⊓ K : Subgroup G) = 8 :=
    AltSix.card_eq_eight_of_isSylowTwoOf (A4.isSylowTwoOf_inf_normal hT₀ hKI hIK)
      (AltSix.card_eq_of_mulEquiv ψ)
  obtain ⟨xa, hxa, xb, hxb, hxab⟩ := AltSix.exists_mul_ne_of_le ψ inf_le_right hS8
  have key : ∀ M W L : Subgroup G, InM T M → IsYFamily T W → W ≤ M → IsSixTwoFactor T M W L →
      L ≤ s.I → s.T₀ ≤ Subgroup.normalizer (L : Set G) →
      pCoreOf 2 L ≤ s.T₀ ⊓ K ∧ Nat.card (pCoreOf 2 L) = 4 := by
    intro M W L hM hW hWM hf hLI hT₀L
    have hLK : L ≤ K := hf.eq_oTwoUpper.le.trans ((oTwoUpper_mono hLI).trans hK.ge)
    have hQT : pCoreOf 2 L ≤ s.T₀ := by
      have hTQ : s.T₀ ≤ Subgroup.normalizer (pCoreOf 2 L : Set G) :=
        hT₀L.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 L)
      have hp : IsPGroup 2 ↥(pCoreOf 2 L ⊔ s.T₀) :=
        IsPGroup.to_sup_of_normal_left' (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 L) hT₀.2.1
          hTQ
      have hle : pCoreOf 2 L ⊔ s.T₀ ≤ s.I :=
        sup_le ((CFSG.LieType.BorelTits.pCoreOf_le 2 L).trans hLI) hT₀.1
      exact le_sup_left.trans
        ((A4.isSylowTwoOf_iff_maximal.mp hT₀).2.2 _ hle hp le_sup_right)
    have hQS : pCoreOf 2 L ≤ s.T₀ ⊓ K :=
      le_inf hQT ((CFSG.LieType.BorelTits.pCoreOf_le 2 L).trans hLK)
    refine ⟨hQS, ?_⟩
    have h4 := hf.four_le_card hyp h12 hM hW hWM
    have hdvd : Nat.card (pCoreOf 2 L) ∣ 8 := hS8 ▸ Subgroup.card_dvd_of_le hQS
    have h8 : Nat.card (pCoreOf 2 L) ≠ 8 := by
      intro h8
      have heq : pCoreOf 2 L = s.T₀ ⊓ K :=
        Subgroup.eq_of_le_of_card_ge hQS (by rw [h8, hS8])
      have hV := hf.commutator_le_pCoreOf hyp h12 hM hW hWM
      have hcen : pCoreOf 2 L ≤ Subgroup.centralizer ((⁅VZ T M, L⁆ : Subgroup G) : Set G) := by
        intro x hx
        have hxM := hf.pCoreOf_le_pCoreOf h12 hM hW hWM hx
        rw [(h11 M hM).1] at hxM
        exact Subgroup.centralizer_le (hf.commutator_le_vZ hWM) hxM.2
      rw [heq] at hV hcen
      exact hxab (mul_comm_of_le_centralizer hV hcen (by rw [hS8, hf.card_commutator]) hxa hxb)
    have hc8 := Nat.le_of_dvd (by norm_num) hdvd
    generalize Nat.card (pCoreOf 2 L) = c at h4 hdvd h8 hc8 ⊢
    interval_cases c <;> simp_all
  have hT₀L₁ : s.T₀ ≤ Subgroup.normalizer (s.L₁ : Set G) := by
    rw [hL₁]
    exact inf_le_right
  have hT₀L₂ : s.T₀ ≤ Subgroup.normalizer (s.L₂ : Set G) := by
    rw [hL₂]
    exact inf_le_left.trans inf_le_right
  have hf₁ : IsSixTwoFactor T s.M₁ s.X s.L₁ := by
    rw [hL₁]
    exact s.dataX.factor_left
  have hf₂ : IsSixTwoFactor T s.M₂ s.Y s.L₂ := by
    rw [hL₂]
    exact s.dataY.factor_left
  obtain ⟨hQ₁S, hQ₁4⟩ := key s.M₁ s.X s.L₁ s.inM₁ s.famX s.le_X hf₁
    (le_sup_left.trans le_sup_left) hT₀L₁
  obtain ⟨hQ₂S, hQ₂4⟩ := key s.M₂ s.Y s.L₂ s.inM₂ s.famY s.le_Y hf₂
    (le_sup_left.trans le_sup_right) hT₀L₂
  have hne : pCoreOf 2 s.L₁ ≠ pCoreOf 2 s.L₂ := by
    intro heq
    have h1 : s.L₁ ≤ Subgroup.normalizer (pCoreOf 2 s.L₁ : Set G) :=
      CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 s.L₁
    have h2 : s.L₂ ≤ Subgroup.normalizer (pCoreOf 2 s.L₁ : Set G) := by
      rw [heq]
      exact CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 s.L₂
    have h3 : s.T₀ ≤ Subgroup.normalizer (pCoreOf 2 s.L₁ : Set G) :=
      hT₀L₁.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 s.L₁)
    have hIN : s.I ≤ Subgroup.normalizer (pCoreOf 2 s.L₁ : Set G) :=
      sup_le (sup_le h1 h3) (sup_le h2 h3)
    have := AltSix.isSimpleGroup_of_mulEquiv ψ
    have hN : ((pCoreOf 2 s.L₁).subgroupOf K).Normal :=
      Subgroup.normal_subgroupOf_of_le_normalizer (hKI.trans hIN)
    rcases Subgroup.Normal.eq_bot_or_eq_top ((pCoreOf 2 s.L₁).subgroupOf K) with h | h
    · rw [Subgroup.subgroupOf_eq_bot, disjoint_iff,
        inf_eq_left.mpr (hQ₁S.trans inf_le_right)] at h
      rw [h, Subgroup.card_bot] at hQ₁4
      exact absurd hQ₁4 (by norm_num)
    · rw [Subgroup.subgroupOf_eq_top] at h
      have hle := Subgroup.card_le_of_le h
      rw [AltSix.card_eq_of_mulEquiv ψ, hQ₁4] at hle
      exact absurd hle (by norm_num)
  have hr : ∀ Q : Subgroup G, Q ≤ s.T₀ ⊓ K → Nat.card Q = 4 → Q.relIndex (s.T₀ ⊓ K) = 2 := by
    intro Q hQ hQ4
    have h := Subgroup.relIndex_mul_card Q (s.T₀ ⊓ K)
    rw [inf_eq_left.mpr hQ, hQ4, hS8] at h
    omega
  have hinf : pCoreOf 2 s.L₁ ⊓ pCoreOf 2 s.L₂ ≠ ⊥ := by
    intro hbot
    have h := Subgroup.relIndex_inf_le (H := pCoreOf 2 s.L₁) (K := pCoreOf 2 s.L₂)
      (L := s.T₀ ⊓ K)
    rw [hbot, Subgroup.relIndex_bot_left, hS8, hr _ hQ₁S hQ₁4, hr _ hQ₂S hQ₂4] at h
    omega
  have hsup : pCoreOf 2 s.L₁ ⊔ pCoreOf 2 s.L₂ = s.T₀ ⊓ K := by
    refine Subgroup.eq_of_le_of_card_ge (sup_le hQ₁S hQ₂S) ?_
    rw [hS8]
    have hdvd1 : 4 ∣ Nat.card ↥(pCoreOf 2 s.L₁ ⊔ pCoreOf 2 s.L₂) :=
      hQ₁4 ▸ Subgroup.card_dvd_of_le le_sup_left
    have hdvd2 : Nat.card ↥(pCoreOf 2 s.L₁ ⊔ pCoreOf 2 s.L₂) ∣ 8 :=
      hS8 ▸ Subgroup.card_dvd_of_le (sup_le hQ₁S hQ₂S)
    have hne4 : Nat.card ↥(pCoreOf 2 s.L₁ ⊔ pCoreOf 2 s.L₂) ≠ 4 := by
      intro h4
      have e1 : pCoreOf 2 s.L₁ = pCoreOf 2 s.L₁ ⊔ pCoreOf 2 s.L₂ :=
        Subgroup.eq_of_le_of_card_ge le_sup_left (by rw [h4, hQ₁4])
      have e2 : pCoreOf 2 s.L₂ = pCoreOf 2 s.L₁ ⊔ pCoreOf 2 s.L₂ :=
        Subgroup.eq_of_le_of_card_ge le_sup_right (by rw [h4, hQ₂4])
      exact hne (e1.trans e2.symm)
    have hc := Nat.le_of_dvd (by norm_num) hdvd2
    have hpos : 0 < Nat.card ↥(pCoreOf 2 s.L₁ ⊔ pCoreOf 2 s.L₂) := Nat.card_pos
    omega
  exact ⟨hQ₁4, hQ₂4, hinf, xa, hsup.ge hxa, xb, hsup.ge hxb, hxab⟩

theorem false_of_stmts {G : Type} [Group G] [Finite G] {T : Subgroup G}
    (hyp : MultipleCentralizerHypothesis G T) (hnot : ¬ IsLThreeTwoOrASix G)
    (h8 : Stmt1548 G T) (h11 : Stmt15411 G T) (h12 : Stmt15412 G T) (h18 : Stmt15418 G T)
    (h19 : Stmt15419 G T) (h20 : Stmt15420 G T) (h22 : Stmt15422 G T) (h23 : Stmt15423 G T) :
    False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨M₁, M₂, hne, hM₁, hM₂, hC₁, hC₂⟩ := hyp.two_centralizer_maximal
  have hiM₁ : InM T M₁ := ⟨hM₁, h8.ge.trans hC₁⟩
  have hiM₂ : InM T M₂ := ⟨hM₂, h8.ge.trans hC₂⟩
  obtain ⟨⟨X, hX, hXM⟩, -⟩ := h12 M₁ hiM₁
  obtain ⟨⟨Y, hY, hYM⟩, -⟩ := h12 M₂ hiM₂
  have hdata : ∀ M W : Subgroup G, InM T M → IsYFamily T W → W ≤ M →
      ∃ W₁ W₂ : Subgroup G, IsSixTwoData T M W W₁ W₂ := by
    intro M W hM hW hWM
    have h6 := ((h12 M hM).2 W hW hWM).2.2.2.2.2.2.1
    rcases concl15412Six_iff.mp h6 with h | ⟨-, -, h⟩
    · rw [h18 hnot W hW] at h
      exact absurd h.1 (by norm_num)
    · exact h
  obtain ⟨X₁, X₂, hdX⟩ := hdata M₁ X hiM₁ hX hXM
  obtain ⟨Y₁, Y₂, hdY⟩ := hdata M₂ Y hiM₂ hY hYM
  let sa : Setting15419 G T := ⟨M₁, M₂, X, Y, X₁, X₂, Y₁, Y₂, X₁, Y₁, hiM₁, hiM₂, hne, hX, hXM,
    hY, hYM, hdX, hdY, Or.inl rfl, Or.inl rfl⟩
  let sb : Setting15419 G T := ⟨M₁, M₂, X, Y, X₂, X₁, Y₁, Y₂, X₂, Y₁, hiM₁, hiM₂, hne, hX, hXM,
    hY, hYM, isSixTwoData_swap hdX, hdY, Or.inl rfl, Or.inl rfl⟩
  obtain ⟨hA4, hB4, hAB, a, ha, b, hb, hab⟩ :=
    Setting15419.pCoreOf_structure hyp h11 h12 h19 h20 h22 h23 sa rfl rfl
  obtain ⟨hA4', -, hAB', -⟩ :=
    Setting15419.pCoreOf_structure hyp h11 h12 h19 h20 h22 h23 sb rfl rfl
  change Nat.card (pCoreOf 2 X₁) = 4 at hA4
  change Nat.card (pCoreOf 2 Y₁) = 4 at hB4
  change pCoreOf 2 X₁ ⊓ pCoreOf 2 Y₁ ≠ ⊥ at hAB
  change a ∈ pCoreOf 2 X₁ ⊔ pCoreOf 2 Y₁ at ha
  change b ∈ pCoreOf 2 X₁ ⊔ pCoreOf 2 Y₁ at hb
  change Nat.card (pCoreOf 2 X₂) = 4 at hA4'
  change pCoreOf 2 X₂ ⊓ pCoreOf 2 Y₁ ≠ ⊥ at hAB'
  have hfX₁ := hdX.factor_left
  have hfX₂ := hdX.factor_right
  have hO₁ : pCoreOf 2 X₁ = ⁅VZ T M₁, X₁⁆ :=
    (Subgroup.eq_of_le_of_card_ge (hfX₁.commutator_le_pCoreOf hyp h12 hiM₁ hX hXM)
      (by rw [hA4, hfX₁.card_commutator])).symm
  have hO₂ : pCoreOf 2 X₂ = ⁅VZ T M₁, X₂⁆ :=
    (Subgroup.eq_of_le_of_card_ge (hfX₂.commutator_le_pCoreOf hyp h12 hiM₁ hX hXM)
      (by rw [hA4', hfX₂.card_commutator])).symm
  have hX₁V : pCoreOf 2 X₁ ≤ VZ T M₁ := hO₁ ▸ hfX₁.commutator_le_vZ hXM
  have hX₂V : pCoreOf 2 X₂ ≤ VZ T M₁ := hO₂ ▸ hfX₂.commutator_le_vZ hXM
  have hX₁₂ : pCoreOf 2 X₁ ⊓ pCoreOf 2 X₂ = ⊥ := by
    rw [hO₁, hO₂]
    exact hdX.inf_commutator_eq_bot
  have hAB0 : (pCoreOf 2 X₁ ⊓ pCoreOf 2 Y₁) ⊓ (pCoreOf 2 X₂ ⊓ pCoreOf 2 Y₁) = ⊥ :=
    le_bot_iff.mp ((inf_le_inf inf_le_left inf_le_left).trans hX₁₂.le)
  have hsupY : (pCoreOf 2 X₁ ⊓ pCoreOf 2 Y₁) ⊔ (pCoreOf 2 X₂ ⊓ pCoreOf 2 Y₁) = pCoreOf 2 Y₁ :=
    sup_eq_of_card_eq_four inf_le_right inf_le_right hB4 hAB hAB' hAB0
  have hY₁V : pCoreOf 2 Y₁ ≤ VZ T M₁ := by
    rw [← hsupY]
    exact sup_le (inf_le_left.trans hX₁V) (inf_le_left.trans hX₂V)
  have hsV : pCoreOf 2 X₁ ⊔ pCoreOf 2 Y₁ ≤ VZ T M₁ := sup_le hX₁V hY₁V
  have := (vZ_le_pCoreOf hyp hiM₁).2.1
  exact hab (congrArg Subtype.val (mul_comm' (⟨a, hsV ha⟩ : VZ T M₁) ⟨b, hsV hb⟩))

end CFSG.Quasithin.EmptyFaithfulMultiple
