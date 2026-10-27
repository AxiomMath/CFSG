module

public import CFSG.Quasithin.EmptyFaithful.S146F3
public import CFSG.Quasithin.EmptyFaithful.S146F2
public import CFSG.Quasithin.EmptyFaithful.S146F1

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique CFSG.Quasithin.F7

section Vocabulary

variable {G : Type} [Group G]

@[expose] def KbarIsA7 (K : Subgroup G) : Prop := IsAlt 7 (KBar K)

@[expose] def KbarIsM22 (K : Subgroup G) : Prop := IsSporadic .M22 (KBar K)

@[expose] def KbarIsL4L5 (K : Subgroup G) : Prop := IsPSL 4 2 1 (KBar K) ∨ IsPSL 5 2 1 (KBar K)

@[expose] def KbarRankLeTwo (K : Subgroup G) : Prop :=
  FourList (KBar K) ∧ ¬ KbarIsA7 K ∧ ¬ KbarIsM22 K ∧ ¬ KbarIsL4L5 K

@[expose] def IsPairIn (T K : Subgroup G) : Prop :=
  ∃ t ∈ T, t ∉ Subgroup.normalizer (K : Set G) ∧ conjClosure K T = K ⊔ conjSub t K ∧
    ⁅K, conjSub t K⁆ ≤ pCoreOf 2 (conjClosure K T ⊔ T)

end Vocabulary

@[expose] def Input14620A7 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (K T : Subgroup G), IsSylowTwoOf T (K ⊔ T) →
    T ≤ Subgroup.normalizer (K : Set G) → KbarIsA7 K → solvGen T (K ⊔ T) = K ⊔ T

@[expose] def Input14620M22 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (K T : Subgroup G), IsSylowTwoOf T (K ⊔ T) →
    T ≤ Subgroup.normalizer (K : Set G) → KbarIsM22 K →
      SecExt (oTwoUpper (solvGen T (K ⊔ T)) ⊔ pCoreOf 2 K) (pCoreOf 2 K) (IsE2 4) (IsAlt 6)

@[expose] def Input14620L45 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (K T : Subgroup G), IsSylowTwoOf T (K ⊔ T) →
    T ≤ Subgroup.normalizer (K : Set G) → KbarIsL4L5 K →
      ∃ P : Subgroup G, P ≤ K ∧ T ≤ Subgroup.normalizer (P : Set G) ∧
        Group.IsSolvable ↥(P ⊔ T) ∧ 2 ≤ CFSG.Open.pRank 3 P

@[expose] def Input14620Borel : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (K T : Subgroup G), IsSylowTwoOf T (conjClosure K T ⊔ T) →
    K ∈ cComp (conjClosure K T ⊔ T) → IsSimpleGroup (KBar K) →
      (T ≤ Subgroup.normalizer (K : Set G) ∨ IsPairIn T K) →
      (KbarRankLeTwo K ∨ KbarIsL4L5 K ∨ FiveShape (KBar K)) →
        Group.IsSolvable ↥((conjClosure K T ⊓
          Subgroup.normalizer ((T ⊓ conjClosure K T : Subgroup G) : Set G)) ⊔ T)

@[expose] def Input14620Rank2 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M : Subgroup G), Setting146 G T M →
    ∀ K : Subgroup G, IsHTM T M (K ⊔ T) → K ∈ cComp (K ⊔ T) → T ≤ Subgroup.normalizer (K : Set G) →
      IsSimpleGroup (KBar K) → KbarRankLeTwo K →
        K ⊓ Subgroup.normalizer ((T ⊓ K : Subgroup G) : Set G) ≤ M →
          (KbarIsL3Two K ∨ KbarIsA6 K) ∧
            ∃ s ∈ T ⊓ Subgroup.normalizer (K : Set G), KbarNontrivialOnDynkin K s

@[expose] def Input14620Bender : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M : Subgroup G), Setting146 G T M →
    ∀ K : Subgroup G, IsHTM T M (conjClosure K T ⊔ T) → K ∈ cComp (conjClosure K T ⊔ T) → IsPairIn T K →
      IsSimpleGroup (KBar K) →
        ((∃ n, IsPSL 2 2 n (KBar K)) ∨ (∃ n, IsSz n (KBar K)) ∨ IsAlt 5 (KBar K)) →
          ¬ (conjClosure K T ⊓ Subgroup.normalizer ((T ⊓ conjClosure K T : Subgroup G) : Set G) ≤ M)

@[expose] def Input14620K0 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (K T : Subgroup G), IsSylowTwoOf T (conjClosure K T ⊔ T) →
    K ∈ cComp (conjClosure K T ⊔ T) → IsPairIn T K → KbarIsL3Two K →
      (∀ s ∈ T ⊓ Subgroup.normalizer (K : Set G), ¬ KbarInducesOuter K s) →
        solvGen T (conjClosure K T ⊔ T) = conjClosure K T ⊔ T

section Final

variable {G : Type} [Group G] [Finite G] {T M : Subgroup G}

theorem stage14620_of_named_inputs
    (h37 : A37ForSQTK) (h38 : A38ForSQTK)
    (hD36 : D36) (hD37 : D37) (hD321 : D321) (hI5 : Insp5a)
    (hD310 : D310) (hD391 : D391) (hI4 : Insp4)
    (i1 : Input14620A7) (i2 : Input14620M22) (i3 : Input14620L45) (i4 : Input14620Borel)
    (i5 : Input14620Rank2) (i6 : Input14620Bender) (i7 : Input14620K0) : Stage14620 := by
  intro G _ _ T M S hB c19 H hH K hK
  have hHTM : IsHTM T M (conjClosure K T ⊔ T) := S.isHTM_conjClosure_sup_of_isHTM h37 h38 hH hK
  have hS' : IsSimpleGroup (KBar K) := (c19 H hH).2 K hK
  have hKH : K ≤ H := le_of_mem_cComp hK
  have hTH : T ≤ H := hH.1.1
  have hle : conjClosure K T ⊔ T ≤ H := conjClosure_sup_le hKH hTH
  have hKH' : K ∈ cComp (conjClosure K T ⊔ T) :=
    cComp_mem_of_le hK ((le_conjClosure K T).trans le_sup_left) hle
  have hF := hypF918_of_isHTM h37 h38 S hH hK hS'
  have hsq : SQTKGroup ↥(conjClosure K T ⊔ T) := S.sqtkGroup_of_isHTM hHTM
  have hsyl : IsSylowTwoOf T (conjClosure K T ⊔ T) :=
    isSylowTwoOf_of_quasithinIsSylowTwo S.hyp.sylow le_sup_right
  have hTK0 : T ≤ conjClosure K T ⊔ T := le_sup_right
  have hB0 : conjClosure K T ⊓ Subgroup.normalizer ((T ⊓ conjClosure K T : Subgroup G) : Set G) ≤
      conjClosure K T ⊔ T := inf_le_left.trans le_sup_left
  have hBM : ∀ hsolv : Group.IsSolvable ↥((conjClosure K T ⊓
      Subgroup.normalizer ((T ⊓ conjClosure K T : Subgroup G) : Set G)) ⊔ T),
      conjClosure K T ⊓ Subgroup.normalizer ((T ⊓ conjClosure K T : Subgroup G) : Set G) ≤ M :=
    fun hsolv => le_sup_left.trans
      (S.le_M_of_solvable hB hHTM le_sup_right (sup_le hB0 hTK0) hsolv)
  by_cases hK0K : conjClosure K T = K
  ·
    have hFour : FourList (KBar K) := fourList_kbar hF hsq hK0K hS' hD310 hD391 hI4
    have hTN : T ≤ Subgroup.normalizer (K : Set G) := hK0K ▸ le_normalizer_conjClosure K T
    have hHK : conjClosure K T ⊔ T = K ⊔ T := by rw [hK0K]
    have hsylK : IsSylowTwoOf T (K ⊔ T) := hHK ▸ hsyl
    have hHTMK : IsHTM T M (K ⊔ T) := hHK ▸ hHTM
    by_cases hA7 : KbarIsA7 K
    · exact absurd (i1 G K T hsylK hTN hA7) (S.solvGen_ne hB hHTMK)
    by_cases hM22 : KbarIsM22 K
    · exfalso
      have hext := i2 G K T hsylK hTN hM22
      have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
      have hrk := two_le_pRank_of_secExt (pCoreOf_isPGroup 2 K) hext
      have hJM : solvGen T (K ⊔ T) ≤ M := S.solvGen_le_M hB hHTMK
      have hY := oTwoUpper_le (solvGen T (K ⊔ T))
      have hQ : pCoreOf 2 K ≤ T := by
        have hKT : K ⊔ T ≤ Subgroup.normalizer (pCoreOf 2 K : Set G) :=
          sup_le (le_normalizer_pCoreOf 2 K) (hTN.trans (normalizer_le_normalizer_pCoreOf 2 K))
        have h1 : pCoreOf 2 K ≤ pCoreOf 2 (K ⊔ T) :=
          le_pCoreOf_of_le_normalizer 2 ((pCoreOf_le 2 K).trans le_sup_left) hKT
            (pCoreOf_isPGroup 2 K)
        exact h1.trans (pCoreOf_two_le_of_isSylowTwoOf hsylK)
      have hYH : oTwoUpper (solvGen T (K ⊔ T)) ⊔ pCoreOf 2 K ≤ K ⊔ T :=
        sup_le (hY.trans solvGen_le_right) (hQ.trans le_sup_right)
      have hYM : oTwoUpper (solvGen T (K ⊔ T)) ⊔ pCoreOf 2 K ≤ M :=
        sup_le (hY.trans hJM) (hQ.trans S.hyp.m_max.1.2)
      have := S.pRank_three_le_one_of_le_M hHTMK hYH hYM
      omega
    by_cases hL45 : KbarIsL4L5 K
    · exfalso
      obtain ⟨P, hPK, hTP, hsolv, hrk⟩ := i3 G K T hsylK hTN hL45
      have hPTH : P ⊔ T ≤ K ⊔ T := sup_le (hPK.trans le_sup_left) le_sup_right
      have hPM : P ⊔ T ≤ M := S.le_M_of_solvable hB hHTMK le_sup_right hPTH hsolv
      have := S.pRank_three_le_one_of_le_M hHTMK (le_sup_left.trans hPTH) (le_sup_left.trans hPM)
      omega
    have hR2 : KbarRankLeTwo K := ⟨hFour, hA7, hM22, hL45⟩
    have hsolv := i4 G K T hsyl hKH' hS' (Or.inl hTN) (Or.inl hR2)
    have hBM' := hBM hsolv
    rw [hK0K] at hBM'
    exact i5 G T M S K hHTMK (hHK ▸ hKH') hTN hS' hR2 hBM'
  ·
    have hFive : FiveShape (KBar K) :=
      fiveShape_kbar hF hsq hK0K hS' hD36 hD37 hD321 hI5 h37 h38
    have hpair : IsPairIn T K := by
      obtain ⟨t₀, ht₀T, ht₀K⟩ : ∃ t ∈ T, t ∉ Subgroup.normalizer (K : Set G) := by
        by_contra hcon
        push Not at hcon
        apply hK0K
        apply le_antisymm
        · refine conjClosure_le fun t ht z hz => ?_
          exact (Subgroup.mem_normalizer_iff.mp (hcon t ht) z).mp hz
        · exact le_conjClosure K T
      obtain ⟨-, hdata⟩ := five_group_data hF hsq h37 h38 hK0K
      obtain ⟨-, hKK0, hcomm, -⟩ := hdata t₀ ht₀T ht₀K
      exact ⟨t₀, ht₀T, ht₀K, hKK0, hcomm⟩
    have hbender : ((∃ n, IsPSL 2 2 n (KBar K)) ∨ (∃ n, IsSz n (KBar K)) ∨ IsAlt 5 (KBar K)) →
        False := fun hb => by
      have hsolv := i4 G K T hsyl hKH' hS' (Or.inr hpair) (Or.inr (Or.inr hFive))
      exact i6 G T M S K hHTM hKH' hpair hS' hb (hBM hsolv)
    rcases hFive with ⟨n, hn⟩ | ⟨n, hn⟩ | hA5 | hL32
    · exact (hbender (Or.inl ⟨n, hn⟩)).elim
    · exact (hbender (Or.inr (Or.inl ⟨n, hn⟩))).elim
    · exact (hbender (Or.inr (Or.inr hA5))).elim
    ·
      have hL3 : KbarIsL3Two K := kbarIsL3Two_of_isPSL hL32
      refine ⟨Or.inl hL3, ?_⟩
      by_contra hcon
      push Not at hcon
      have hinner : ∀ s ∈ T ⊓ Subgroup.normalizer (K : Set G), ¬ KbarInducesOuter K s :=
        fun s hs hout => hcon s hs (Or.inl ⟨hL3, hout⟩)
      exact S.solvGen_ne hB hHTM (i7 G K T hsyl hKH' hpair hL3 hinner)

end Final

end CFSG.Quasithin
