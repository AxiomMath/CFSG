module

public import CFSG.Quasithin.Vol2.Ch10SecB4Aux
public import CFSG.Quasithin.Vol2.Ch10SecB4Lift2

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecB

open CFSG.Open CFSG.Blueprint CFSG.Quasithin.H13 CFSG.Quasithin CFSG.QuasithinUnique
open scoped MatrixGroups

variable {G : Type} [Group G] [Finite G]

theorem exists_isSylowIn_three (X : Subgroup G) : ∃ P : Subgroup G, IsSylowIn 3 P X := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨S⟩ := (inferInstance : Nonempty (Sylow 3 ↥X))
  refine ⟨(S : Subgroup ↥X).map X.subtype, isSylowIn_of_card_eq (Subgroup.map_subtype_le _) ?_⟩
  rw [Subgroup.card_map_of_injective X.subtype_injective]
  exact Sylow.card_eq_multiplicity S

omit [Finite G] in
theorem not_mem_of_three {P Q : Subgroup G} (hP : IsPGroup 3 P) (hQ : IsPGroup 2 Q) {x : G}
    (hxP : x ∈ P) (hx1 : x ≠ 1) : x ∉ Q := fun hxQ => by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hd := IsPGroup.disjoint_of_ne 3 2 (by norm_num) P Q hP hQ
  exact hx1 (Subgroup.disjoint_def.mp hd hxP hxQ)

variable {T L I : Subgroup G} {t : G} {Ψ : ↥(fsuL0 T L) →* L32.Γ × L32.Γ} {c : L32.Γ}
  {A K E : Subgroup L32.Γ}

theorem kof_cases
    (h134 : EmptyFaithfulMultiple.Prop134E9He) (hFa : FactL33M11)
    (hFc : FactL4L5) (h : MaxCtx T L I t Ψ c) (hD : ParData A K E) {H : Subgroup G}
    (hH : InH (XOf T L Ψ A ⊔ T) H) :
    conjClosure (XOf T L Ψ A) H = XOf T L Ψ A ∨
    (∃ K₁ : Subgroup G, ∃ s ∈ T, quasithinIsCComponent K₁ H ∧
        s ∉ Subgroup.normalizer (K₁ : Set G) ∧
        conjClosure (XOf T L Ψ A) H = K₁ ⊔ CFSG.conjugate K₁ s ∧
        ((∃ m : ℕ, 0 < m ∧ Even m ∧ ∃ (F : Type) (_ : Field F) (_ : Finite F),
            Nat.card F = 2 ^ m ∧
            Nonempty (↥K₁ ⧸ CFSG.pCore 2 ↥K₁ ≃* Matrix.SpecialLinearGroup (Fin 2) F)) ∨
          ∃ p : ℕ, p.Prime ∧ p ≠ 2 ∧ Nonempty (↥K₁ ⧸ CFSG.pCore 2 ↥K₁ ≃* PSL(2, ZMod p)))) ∨
    (quasithinIsCComponent (conjClosure (XOf T L Ψ A) H) H ∧ ∃ k : ℕ, (k = 4 ∨ k = 5) ∧
        CFSG.Assembly.LowTwoRank.StatedClassicalModel
          (↥(conjClosure (XOf T L Ψ A) H) ⧸ CFSG.pCore 2 ↥(conjClosure (XOf T L Ψ A) H))
          .PSL k 2 1 ∧
        Nonempty (↥(conjClosure (XOf T L Ψ A) H ⊔ T) ⧸
            CFSG.pCore 2 ↥(conjClosure (XOf T L Ψ A) H ⊔ T) ≃*
          MulAut (Matrix.SpecialLinearGroup (Fin k) (ZMod 2)))) ∨
    (∃ K₁ : Subgroup G, K₁ ∈ cComp H ∧ H ≤ Subgroup.normalizer (K₁ : Set G) ∧
        XOf T L Ψ A ≤ K₁ ∧
        Nonempty ((↥K₁ ⧸ CFSG.pCore 2 ↥K₁) ≃* CFSG.Blueprint.NativeSporadic.Carrier .He)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set X := XOf T L Ψ A with hXdef
  have hyp := h.hyp
  have hT := hyp.fsu.sylow
  have := hyp.fsu.simple
  have hK : LocalSQTK G := (qtkeCore_of_cat hyp.fsu.nonabelian hyp.fsu.qtke).1
  have hXH : X ≤ H := le_sup_left.trans hH.1
  have hTH : T ≤ H := le_sup_right.trans hH.1
  have hTsyl : IsSylowTwoOf T H := ⟨hTH, hT.1, SecA.not_two_dvd_index_of_le hT hTH⟩
  have hXi := isXi_XOf h hD
  have hrel := relIndex_XOf h hD
  have h3 : 3 ∣ Nat.card X := by
    rw [card_eq_card_pCoreOf_mul_relIndex, hrel]
    exact Dvd.dvd.mul_left (by norm_num) _
  obtain ⟨P3, hP3⟩ := exists_isSylowIn_three X
  have hP3card : Nat.card P3 = 9 := by rw [hXi.card_sylow (by norm_num) h3 hP3, hrel]
  have hP3ne : ∃ x ∈ P3, x ≠ 1 := by
    rcases Subgroup.bot_or_exists_ne_one P3 with hb | hx
    · rw [hb, Subgroup.card_bot] at hP3card; omega
    · exact hx
  have hKn : H ≤ Subgroup.normalizer (conjClosure X H : Set G) := le_normalizer_conjClosure X H
  have hXK : X ≤ conjClosure X H := le_conjClosure X H
  have hpow3 : ∀ x ∈ X, x ^ 3 ∈ pCoreOf 2 X := fun x hx => pow_three_mem h hD hx
  rcases h134 G H T X P3 (hK H hH.2) hH.2 hTsyl hXH hXi hrel hP3.le hP3.isPGroup hP3card with
    hN | ⟨L', hL', -, hXL', hcases⟩
  · exact Or.inl (conjClosure_eq_self hN)
  have hHN : H ≤ Subgroup.normalizer (conjClosure L' T : Set G) :=
    Vol2Native.normal_conjClosure_of_pCoreOf_ne_bot hK h.h37 h.h38 hH.2 hTsyl hL'
  have hKle : conjClosure X H ≤ conjClosure L' T := conjClosure_le fun s hs x hx =>
    (Subgroup.mem_normalizer_iff.mp (hHN hs) x).mp (hXL' hx)
  rcases hcases with ⟨⟨t', ⟨ht'T, -⟩, ht'n, hPeq, -⟩, htype⟩ | ⟨hTL, htype⟩ |
      ⟨-, -, hcyc⟩ | ⟨hTL, htype⟩ | ⟨hHL, hHe⟩
  ·
    right; left
    rcases Vol2Native.lemma_1_2_1_three hK h.h37 h.h38 hH.2 hL' with hnorm | ⟨hcard, htypes⟩
    · exfalso
      apply ht'n
      rw [Subgroup.mem_normalizer_iff]
      intro x
      constructor
      · intro hx
        have := hnorm.conj_mem ⟨x, le_of_mem_cComp hL' hx⟩ hx ⟨t', hTH ht'T⟩
        rw [Subgroup.mem_subgroupOf] at this
        simpa using this
      · intro hx
        have := hnorm.conj_mem ⟨t' * x * t'⁻¹, le_of_mem_cComp hL' hx⟩ hx
          ⟨t'⁻¹, H.inv_mem (hTH ht'T)⟩
        rw [Subgroup.mem_subgroupOf] at this
        simpa [mul_assoc] using this
    · have hsup := conjClosure_eq_sup_of_ncard hTH hcard ht'T ht'n
      have hsimple := Vol2Native.L122A.isSimpleGroup_of_a38Types htypes
      obtain ⟨x, hxP, hxL, hx1⟩ : ∃ x ∈ P3, x ∈ L' ∧ x ≠ 1 := by
        by_contra hcon
        push Not at hcon
        have hbot : P3 ⊓ L' = ⊥ := (Subgroup.eq_bot_iff_forall _).mpr fun x hx =>
          hcon x hx.1 hx.2
        rw [hbot, conjByElt, Subgroup.map_bot, sup_bot_eq] at hPeq
        rw [hPeq, Subgroup.card_bot] at hP3card
        omega
      have hL'K : L' ≤ conjClosure X H := le_of_isSimpleGroup hL' hKn hsimple
        (hXK (hP3.le hxP)) hxL (not_mem_of_three hP3.isPGroup
          (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 L') hxP hx1)
      have hL'tK : CFSG.conjugate L' t' ≤ conjClosure X H := by
        intro y hy
        rw [SecA.mem_conjugate_iff] at hy
        have := (Subgroup.mem_normalizer_iff.mp (hKn (H.inv_mem (hTH ht'T))) _).mp (hL'K hy)
        simpa [mul_assoc] using this
      refine ⟨L', t', ht'T, hL', ht'n, le_antisymm (hKle.trans hsup.le) (sup_le hL'K hL'tK), ?_⟩
      rcases htype with ⟨n, hn, hmod⟩ | ⟨q, hq, hq2, hmod⟩
      · obtain ⟨hn0, F, hF, hFin, hcardF, he⟩ := sl_two_of_model hmod
        exact Or.inl ⟨n, hn0, hn, F, hF, hFin, hcardF, he⟩
      · exact Or.inr ⟨q, hq, hq2, psl_two_of_model hq hmod⟩
  ·
    exfalso
    obtain ⟨s, hs, x, hx, hne⟩ := exists_pow_four_not_mem hFa hTsyl hL' (by
      rcases htype with h1 | h1
      · exact Or.inl h1
      · exact Or.inr (Or.inl h1)) (hXL'.trans (conjClosure_eq_self hTL).le)
      hXi.1 hXi.2.1 hpow3 hrel
    exact hne (pow_four_mem h hD hs hx)
  ·
    exact absurd hcyc (not_autCyclic h hD hP3)
  ·
    have hXL : X ≤ L' := hXL'.trans (conjClosure_eq_self hTL).le
    have case4 : ∀ k : ℕ, (k = 4 ∨ k = 5) →
        CFSG.Assembly.LowTwoRank.StatedClassicalModel (↥L' ⧸ CFSG.pCore 2 ↥L') .PSL k 2 1 →
        quasithinIsCComponent (conjClosure X H) H ∧ ∃ k : ℕ, (k = 4 ∨ k = 5) ∧
          CFSG.Assembly.LowTwoRank.StatedClassicalModel
            (↥(conjClosure X H) ⧸ CFSG.pCore 2 ↥(conjClosure X H)) .PSL k 2 1 ∧
          Nonempty (↥(conjClosure X H ⊔ T) ⧸ CFSG.pCore 2 ↥(conjClosure X H ⊔ T) ≃*
            MulAut (Matrix.SpecialLinearGroup (Fin k) (ZMod 2))) := by
      intro k hk45 hk
      obtain ⟨x, hxP, hx1⟩ := hP3ne
      have hsimple := (CFSG.LieType.Simplicity.fam_PSL_simplicity _ _ _ _ hk).2
      have hL'K : L' ≤ conjClosure X H := le_of_isSimpleGroup hL' hKn hsimple
        (hXK (hP3.le hxP)) (hXL (hP3.le hxP)) (not_mem_of_three hP3.isPGroup
          (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 L') hxP hx1)
      have hKeq : conjClosure X H = L' :=
        le_antisymm (hKle.trans (conjClosure_eq_self hTL).le) hL'K
      rw [hKeq]
      exact ⟨hL', k, hk45, hk, nonempty_aut_of hFc hTsyl hL' hTL hk45 hk hXL hXi.1 hXi.2.1
        hpow3 hrel (exists_noncomm h hD)⟩
    rcases htype with hM | hk | hk
    · exfalso
      obtain ⟨s, hs, x, hx, hne⟩ := exists_pow_four_not_mem hFa hTsyl hL' (Or.inr (Or.inr hM))
        hXL hXi.1 hXi.2.1 hpow3 hrel
      exact hne (pow_four_mem h hD hs hx)
    · exact Or.inr (Or.inr (Or.inl (case4 4 (Or.inl rfl) hk)))
    · exact Or.inr (Or.inr (Or.inl (case4 5 (Or.inr rfl) hk)))
  ·
    exact Or.inr (Or.inr (Or.inr ⟨L', hL', hHL,
      hXL'.trans (conjClosure_eq_self (hTH.trans hHL)).le, hHe⟩))
