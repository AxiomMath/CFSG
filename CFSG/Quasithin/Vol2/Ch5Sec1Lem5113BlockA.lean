module

public import CFSG.Quasithin.Vol2.Ch5Sec1Lem5113BlockSteps
public import CFSG.Quasithin.EmptyFaithful.S151YC

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin

namespace Main513

variable {G : Type} [Group G] [Finite G] {T M L V H B D K₁ X Kh₁ : Subgroup G} {n : ℕ}

theorem exists_c126_dichotomy (h511 : Stmt5_1_1) (h432 : Stmt4_3_2) (hC126 : TheoremC126)
    (hGN : TheoremC118) (m : Main513 G T M L V H B D K₁ X Kh₁ n)
    (hZL : quasithinOmegaOneCenter T ⊓ Subgroup.centralizer (L : Set G) = ⊥)
    (hZK : quasithinOmegaOneCenter T ⊓ Subgroup.centralizer (oTwoUpper H : Set G) = ⊥) :
    ∃ C : Subgroup G, C ≠ ⊥ ∧ IsPGroup 2 C ∧ C ≤ baum T ∧ (C.subgroupOf (baum T)).Characteristic ∧
      (C126Third (L ⊔ T) T ∨ C126Third H T) ∧
      (¬ C126Third H T → H ≤ Subgroup.normalizer (C : Set G)) ∧
      (¬ C126Third (L ⊔ T) T → L ⊔ T ≤ Subgroup.normalizer (C : Set G)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h := m.hyp.toHyp5_0_1
  have hT2 : IsPGroup 2 T := h.sylow.1
  obtain ⟨C₁, C₂, hC⟩ := exists_isGNChoice (G := G) hGN
  have hs := hC126 G C₁ C₂ hC
  obtain ⟨-, hHmin, -, N, hLmin⟩ := h511 G T M L V n h m.module
  obtain ⟨hparL, hsylL, -⟩ := minParabolic_iff.mp hLmin
  obtain ⟨hparH, hsylH, -⟩ := minParabolic_iff.mp (hHmin H m.hyp.hStar).1
  have hpcL : pCoreOf 2 (L ⊔ T) ≠ ⊥ := h.maximal.1.2.2.2
  have hpcH : pCoreOf 2 H ≠ ⊥ := m.hyp.hStar.1.2
  have hcharL : CharTwo (L ⊔ T) := charTwo_of_inH' h.qtke h.sylow ⟨le_sup_right, hpcL⟩
  have hcharH : CharTwo H := charTwo_of_inH' h.qtke h.sylow m.hyp.hStar.1
  have hSQ : ∀ {Y : Subgroup G}, pCoreOf 2 Y ≠ ⊥ → IsSQTKTC Y := fun hY =>
    ⟨kGroup_of_pCoreOf_ne_bot h.qtke h.simple h.nonabelian hY,
      stronglyQuasithin_of_pCoreOf_ne_bot h.qtke hY⟩
  have hT0 : T ≠ ⊥ := by
    intro hT
    apply hpcL
    have hle := CFSG.Quasithin.pCoreOf_two_le_of_isSylowTwoOf hsylL
    exact le_bot_iff.mp (hle.trans hT.le)
  obtain ⟨h1ne, h1Z, -, h2ne, h2B, h2ch, -⟩ := hC.pair T hT2 hT0
  have h1Z' : C₁ T ≤ quasithinOmegaOneCenter T := h1Z
  have h2T : C₂ T ≤ T := h2B.trans (C1GN.baum_le T)
  have h22 : IsPGroup 2 ↥(C₂ T) := hT2.to_le h2T
  have hno1 : ∀ {Y W : Subgroup G}, W ≤ Y →
      quasithinOmegaOneCenter T ⊓ Subgroup.centralizer (W : Set G) = ⊥ →
      ¬ C₁ T ≤ centerOf Y := by
    intro Y W hWY hZW hle
    apply h1ne
    rw [eq_bot_iff, ← hZW]
    intro x hx
    refine ⟨h1Z' hx, Subgroup.mem_centralizer_iff.mpr fun w hw => ?_⟩
    exact Subgroup.mem_centralizer_iff.mp (hle hx).2 w (hWY hw)
  have hLT := hs (L ⊔ T) T (hSQ hpcL) hsylL hcharL hparL
  have hHT := hs H T (hSQ hpcH) hsylH hcharH hparH
  have hn1L := hno1 (Y := L ⊔ T) le_sup_left hZL
  have hn1H := hno1 (Y := H) (oTwoUpper_le H) hZK
  have hnot : ¬ (L ⊔ T ≤ Subgroup.normalizer (C₂ T : Set G) ∧
      H ≤ Subgroup.normalizer (C₂ T : Set G)) := by
    rintro ⟨hL2, hH2⟩
    obtain ⟨huniq, -⟩ := h432 G T M L h.simple h.nonabelian h.qtke h.sylow h.maxTwoLocal h.T_le
      h.maximal h.faithful h.L_le h.normal ⟨n, h.two_le, h.lie⟩
    have hloc : IsTwoLocal (Subgroup.normalizer (C₂ T : Set G)) := ⟨C₂ T, h2ne, h22, rfl⟩
    obtain ⟨M', hM', hle⟩ := exists_maxTwoLocal_ge hloc
    have hM'eq : M' = M := huniq M' hM' ((le_sup_left.trans hL2).trans hle)
    exact m.hyp.hStar.2.1 (hM'eq ▸ hH2.trans hle)
  refine ⟨C₂ T, h2ne, h22, h2B, h2ch, ?_, ?_, ?_⟩
  · rcases hLT with h1 | h2 | h3
    · exact absurd h1 hn1L
    · rcases hHT with h1' | h2' | h3'
      · exact absurd h1' hn1H
      · exact absurd ⟨h2, h2'⟩ hnot
      · exact Or.inr h3'
    · exact Or.inl h3
  · intro hnb
    rcases hHT with h1' | h2' | h3'
    · exact absurd h1' hn1H
    · exact h2'
    · exact absurd h3' hnb
  · intro hnb
    rcases hLT with h1 | h2 | h3
    · exact absurd h1 hn1L
    · exact h2
    · exact absurd h3 hnb

end Main513

@[expose] def Stmt5_1_13_four_block_bcd : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M L V H B D K₁ X Kh₁ : Subgroup G) (n : ℕ),
    Main513 G T M L V H B D K₁ X Kh₁ n → Case5_512 T H X Kh₁ →
    Type513 T D X (conjClosure Kh₁ T) (oTwoUpper H) →
    quasithinIsMaximalLocal T (conjClosure Kh₁ T) →
    ¬ conjClosure Kh₁ T ≤ Subgroup.centralizer (quasithinOmegaOneCenter T : Set G) →
    Nonempty (O2Q (conjClosure Kh₁ T) ≃* alternatingGroup (Fin 7)) →
    quasithinOmegaOneCenter T ⊓ Subgroup.centralizer (L : Set G) = ⊥ →
    quasithinOmegaOneCenter T ⊓ Subgroup.centralizer (oTwoUpper H : Set G) = ⊥ →
    ∀ V' : Subgroup G, IsCh5Module T L V' → quasithinOmegaOneCenter T ≤ V' →
      IsNatQuotCh5 L V' n →
    ∀ C : Subgroup G, C ≠ ⊥ → C ≤ baum T → (C.subgroupOf (baum T)).Characteristic →
      (C126Third (L ⊔ T) T ∨ C126Third H T) →
      (¬ C126Third H T → H ≤ Subgroup.normalizer (C : Set G)) →
      (¬ C126Third (L ⊔ T) T → L ⊔ T ≤ Subgroup.normalizer (C : Set G)) →
      ¬ C126Third H T ∧ 2 < n ∧ D ⊔ T ≤ Subgroup.normalizer (C : Set G)

theorem stmt5_1_13_four_block_of (h511 : Stmt5_1_1) (h432 : Stmt4_3_2) (hC126 : TheoremC126)
    (hGN : TheoremC118) (hbcd : Stmt5_1_13_four_block_bcd) : Stmt5_1_13_four_block := by
  intro G _ _ T M L V H B D K₁ X Kh₁ n m hc5 hty hX hnZ hA7 hZL hZK V' hV' hZV' hnat
  obtain ⟨C, hC0, hC2, hCB, hCch, hdich, hHN, hLN⟩ :=
    m.exists_c126_dichotomy h511 h432 hC126 hGN hZL hZK
  obtain ⟨hnb, hn, hDT⟩ := hbcd G T M L V H B D K₁ X Kh₁ n m hc5 hty hX hnZ hA7 hZL hZK V' hV'
    hZV' hnat C hC0 hCB hCch hdich hHN hLN
  exact ⟨hn, C, hC0, hC2, sup_le ((oTwoUpper_le H).trans (hHN hnb))
    (m.hyp.hStar.1.1.trans (hHN hnb)), hDT⟩

end CFSG.Quasithin.H13
