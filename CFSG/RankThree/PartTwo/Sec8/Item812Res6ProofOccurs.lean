module

public import CFSG.RankThree.PartTwo.Sec8.Item812Res4ProofConfig
public import CFSG.RankThree.PartTwo.Sec8.Item86Res2Proof84

public section

namespace CFSG.RankThree.PartTwo.Sec8

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open Item86ResProof
open CFSG.Assembly.RankThreeEven (projSp)


@[expose] def Choice86Partner : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G) (a d : G) (n : ℕ),
    Sec8Std G A c L a d n → ∃ (c' : G) (L' : Subgroup G) (a' b' : G) (X' : Subgroup G),
      Sec8Pair G A c' L' a' b' X' n ∧ ((c', L') = (c, L) ∨ (b', X') = (c, L))

@[expose] def Pair89OmegaStd : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G) (a b : G)
    (X : Subgroup G) (n : ℕ), Sec8Pair G A c L a b X n →
    ∀ p ∈ pairOmega A, ∃ (x d : G) (m : ℕ), Sec8Std G A p.1 p.2 x d m

theorem pair89Occurs_of_std (hS : Pair89OmegaStd) (hch : Choice86Partner) : Pair89Occurs := by
  intro G _ _ A c L a b X n h p hp
  obtain ⟨x, d, m, hstd⟩ := hS G A c L a b X n h p hp
  obtain ⟨c', L', a', b', X', hpair, hcase⟩ := hch G A p.1 p.2 x d m hstd
  exact ⟨c', L', a', b', X', m, hpair, hcase.symm⟩


theorem choice86Partner_of_narrowU (h84 : Pair84PartnerU) (h85 : Pair85Exists)
    (h86 : Pair86Exists) (hC : Pair86Center) (hGN : Pair86GTwoN) : Choice86Partner := by
  intro G _ _ A c L a d n h
  have hd := h.data83
  have hn1 : 1 ≤ n := hd.odd.pos
  have hA81 : Nat.card A = 81 := hd.card_eq
  have hdΓ : IsGammaIndex A L d n := isGammaIndex_of_data83 hd
  have hLtype := isGammaType_of_isGammaIndex hdΓ
  have hcL : L ≤ Subgroup.centralizer ({c} : Set G) :=
    Sec6.le_centralizer_of_mem_thetaComponentsAt h.mem_thetaComponentsAt
  have hγn : ∀ b ∈ gammaSet A L, IsGammaIndex A L b n := by
    rintro b ⟨m, hm⟩
    have hmn := eq_of_isGammaType (one_le_of_isGammaIndex hm) hn1
      (isGammaType_of_isGammaIndex hm) hLtype
    rwa [hmn] at hm
  have mkPair : ∀ (a' b : G) (X : Subgroup G), Hyp81 G A c L a' →
      b ∈ Subgroup.closure ({c, d} : Set G) → PairRel A c L b X →
      (∀ m : ℕ, ¬ IsUnitaryTwo (X ⧸ aschbacherSolvableCore 3 X) m) →
      ((∃ m : ℕ, IsUnitaryTwo (L ⧸ aschbacherSolvableCore 3 L) m) →
        IsoGTwoEven (barCentralizer (Subgroup.zpowers a') X) n ∨
          Nonempty (barCentralizer (Subgroup.zpowers a') X ≃* projSp 2 (GaloisField 2 n))) →
      Sec8PairGTwo L a' n → (∀ m : ℕ, Sec8PairGTwo X a' m) → Sec8Pair G A c L a' b X n :=
    fun a' b X h81 hb hrel hXU hcent hg hgX =>
    { toHyp81 := h81
      card_eq := hA81
      pairRel := hrel
      isGammaIndex := hγn b hrel.2.1
      mem_pairOmega := (h84 G A c L a d n h b X hb hrel).1
      not_unitary := hXU
      centralizer_of_unitary := hcent
      gTwo := hg
      gTwoPartner := hgX }
  by_cases hLU : ∃ m : ℕ, IsUnitaryTwo (L ⧸ aschbacherSolvableCore 3 L) m
  ·
    have hLU3 : IsUnitaryTwo (L ⧸ aschbacherSolvableCore 3 L) (3 * n) := by
      obtain ⟨m, hm⟩ := hLU
      rcases hd.cases with ⟨hD | hG, -, -⟩ | ⟨hR, -, -⟩ | ⟨hS, -, -⟩ | ⟨hU, -, -⟩ | ⟨⟨e⟩, -, -⟩
      · exact ((sigD4_of_isoTrialityD4 hn1 hD).not_isUnitaryTwo hn1 m hm).elim
      · exact ((sigG2_of_isoGTwo hn1 (isoGTwo_of_isoGTwoEven (by omega) hG)).not_isUnitaryTwo
          hn1 m hm).elim
      · obtain ⟨k, hk, hkn, he⟩ := reeF4_of_isoReeF4 (by omega) hR
        exact ((sigF4_of_reeF4 hn1 ⟨k, hk, hkn, he⟩).not_isUnitaryTwo hn1 m hm).elim
      · exact Or.inr hS
      · exact Or.inl hU
      · exact ((sigSp4_of_projSp hn1 e).not_isUnitaryTwo hn1 m hm).elim
    obtain ⟨b, hb, -, X, hrel, hlist, halt⟩ := h86 G A c L a d n h hLU3
    have hXU := not_isUnitaryTwo_of_isList86 hn1 hlist
    have hg : ∀ a' : G, Sec8PairGTwo L a' n := fun _ => sec8PairGTwo_of_isUnitaryTwo hn1 hLU3
    rcases halt with hG2 | ⟨ε, -, hG2'⟩ | hSpC
    · exact ⟨c, L, a, b, X,
        mkPair a b X h.toHyp81 hb hrel hXU (fun _ => Or.inl hG2) (hg a)
          (sec8PairGTwo_forall_of_isList86 hn1 hlist hG2), Or.inl rfl⟩
    · exact ⟨c, L, a * c ^ ε, b, X,
        mkPair (a * c ^ ε) b X (hyp81_mul_zpow h.toHyp81 ε (mul_zpow_ne_one h.toHyp81 ε)) hb
          hrel hXU (fun _ => Or.inl hG2') (hg (a * c ^ ε))
          (sec8PairGTwo_forall_of_isList86 hn1 hlist hG2'), Or.inl rfl⟩
    · exact ⟨c, L, a, b, X,
        mkPair a b X h.toHyp81 hb hrel hXU (fun _ => Or.inr hSpC) (hg a)
          (sec8PairGTwo_forall_of_projSp hd.odd hlist hSpC), Or.inl rfl⟩
  ·
    have hLU' : ∀ m : ℕ, ¬ IsUnitaryTwo (L ⧸ aschbacherSolvableCore 3 L) m :=
      fun m hm => hLU ⟨m, hm⟩
    obtain ⟨b, hb, hb1, X, hrel⟩ := h85 G A c L a d n h hLU'
    by_cases hXU : ∃ m : ℕ, IsUnitaryTwo (X ⧸ aschbacherSolvableCore 3 X) m
    ·
      obtain ⟨hΩX, hU⟩ := h84 G A c L a d n h b X hb hrel
      obtain ⟨hcγ, hkind, hrel'⟩ := hU hXU
      have hbΓ := hγn b hrel.2.1
      have hcentL : IsoGTwoEven (barCentralizer (Subgroup.zpowers a) L) n ∨
          Nonempty (barCentralizer (Subgroup.zpowers a) L ≃* projSp 2 (GaloisField 2 n)) := by
        rcases hd.cases with ⟨hL1, -, -⟩ | ⟨hR, -, -⟩ | ⟨hS, -, -⟩ | ⟨hU, -, -⟩ | ⟨-, hSpC, -⟩
        · exact Or.inl (h.gTwo hL1)
        · exfalso
          obtain ⟨k, hk, hkn, he⟩ := reeF4_of_isoReeF4 (by omega) hR
          have hF := sigF4_of_reeF4 hn1 ⟨k, hk, hkn, he⟩
          have hSU := isoSUThree_of_isGammaIndex_of_sigF4 hbΓ hF
          obtain ⟨m, hm⟩ := hXU
          have hL2 := projSL_of_isGammaIndex_of_isUnitaryTwo hcγ hm
          have hKL : inSubgroup perfectResidual (L ⊓ Subgroup.centralizer ({b} : Set G)) ≤ L :=
            (Subgroup.map_subtype_le _).trans inf_le_left
          have hKM : inSubgroup perfectResidual (L ⊓ Subgroup.centralizer ({b} : Set G)) ≤
              inSubgroup perfectResidual (X ⊓ Subgroup.centralizer ({c} : Set G)) :=
            KFacts.le_inSubgroup_perfectResidual (isPerfect_inSubgroup_perfectResidual' _)
              (le_inf hrel.2.2.2.1 (hKL.trans hcL))
          exact false_of_isoSUThree_le_projSL hKL hKM
            ((Subgroup.map_subtype_le _).trans inf_le_left) hd.odd hSU hL2
        · exact absurd (Or.inr hS) (hLU' (3 * n))
        · exact absurd (Or.inl hU) (hLU' (3 * n))
        · exact Or.inr hSpC
      have h81 : Hyp81 G A b X a :=
        hyp81_of_partner h.toHyp81 hA81 hbΓ.1 hb1 hrel.2.2.1 hΩX hkind
          (hC G A c L a d n h b X hb hrel hLU' hXU)
      have hgX : Sec8PairGTwo X a n := by
        obtain ⟨k, hk⟩ := hXU
        exact sec8PairGTwo_of_isUnitaryTwo hn1 hk
      exact ⟨b, X, a, c, L,
        { toHyp81 := h81
          card_eq := hA81
          pairRel := hrel'
          isGammaIndex := hcγ
          mem_pairOmega := hrel.1
          not_unitary := hLU'
          centralizer_of_unitary := fun _ => hcentL
          gTwo := hgX
          gTwoPartner := sec8PairGTwo_forall hn1 hLtype h.gTwo }, Or.inr rfl⟩
    ·
      have hXU' : ∀ m : ℕ, ¬ IsUnitaryTwo (X ⧸ aschbacherSolvableCore 3 X) m :=
        fun m hm => hXU ⟨m, hm⟩
      obtain ⟨k, hk⟩ := hGN G A c L a d n h hLU' b X hb hrel hXU'
      exact ⟨c, L, a * c ^ k, b, X,
        mkPair (a * c ^ k) b X (hyp81_mul_zpow h.toHyp81 k (mul_zpow_ne_one h.toHyp81 k)) hb
          hrel hXU' (fun hU => absurd hU hLU) (sec8PairGTwo_mul_zpow h.toHyp81 h.gTwo k) hk,
        Or.inl rfl⟩

theorem pair89Occurs_of_narrowU (hS : Pair89OmegaStd) (h84 : Pair84PartnerU)
    (h85 : Pair85Exists) (h86 : Pair86Exists) (hC : Pair86Center) (hGN : Pair86GTwoN) :
    Pair89Occurs :=
  pair89Occurs_of_std hS (choice86Partner_of_narrowU h84 h85 h86 hC hGN)

theorem pair89Occurs_of_narrowU_item45 (hS : Pair89OmegaStd) (h45 : Sec4.Item4_5)
    (h84 : Pair84PartnerU) (h85 : Pair85Exists) (h86 : Pair86Exists) (hKB : Item83Proof.KF83KBarTwo)
    (hG2 : KF83IndepGTwo) (hGN : Pair86GTwoN) : Pair89Occurs :=
  pair89Occurs_of_narrowU hS h84 h85 h86 (pair86Center_ofU h45 h84 hKB hG2) hGN

end CFSG.RankThree.PartTwo.Sec8
