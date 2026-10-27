module

public import CFSG.Quasithin.EmptyFaithful.S152He8Ii
public import CFSG.Quasithin.Vol2.Ch1Rank
public import CFSG.Quasithin.EmptyFaithful.Der6DMain
public import CFSG.Quasithin.EmptyFaithful.S152He8Facts

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Assembly.LowTwoRank
open scoped commutatorElement Pointwise
open CFSG.Quasithin.C1Pack12
open CFSG.Quasithin.EmptyFaithfulMultiple
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)

namespace He8

variable {G : Type} [Group G] [Finite G]

theorem eq_of_model (hF : A318Facts) (h36 : A36ForSQTK) (h38 : A38ForSQTK) {Mc Kc : Subgroup G}
    (hSQ : SQTKGroup ↥Mc) (hKc : Kc ∈ cComp Mc) {S : Type} [Group S] [Finite S]
    (e : (↥Kc ⧸ CFSG.pCore 2 ↥Kc) ≃* S) (hS : A318Exclusion S) : Kc = oPrimeResidualOf 3 Mc :=
  eq_oPrimeResidualOf_three_of_exclusion hF h36 h38 hSQ hKc (isQuasisimple_of_exclusion e hS) e hS

theorem eq_of_caseii (hF : A318Facts) (h36 : A36ForSQTK) (h38 : A38ForSQTK)
    (hK : KnownFacts15122Types) {T Mc Kc : Subgroup G} (hSQ : SQTKGroup ↥Mc)
    (hT : T ≤ Subgroup.normalizer (Kc : Set G)) (h : Case15212ii T Mc Kc) :
    Kc = oPrimeResidualOf 3 Mc := by
  obtain ⟨-, hKc, n, hn, ⟨e⟩⟩ := h
  have hn3 : 3 ≤ n := by omega
  have hmod := statedModel_psl_two_n hn3
  have : Finite (Matrix.ProjectiveSpecialLinearGroup (Fin n) (ZMod 2)) :=
    CFSG.LieType.Simplicity.finite_of_statedClassicalModel hmod
  have hS : A318Exclusion (Matrix.ProjectiveSpecialLinearGroup (Fin n) (ZMod 2)) := by
    rcases hn with rfl | rfl
    · exact hK.l42 _ hmod
    · exact hK.l52 _ hmod
  have : Group.IsSolvable (Outer (Matrix.ProjectiveSpecialLinearGroup (Fin n) (ZMod 2))) :=
    isSolvable_outer_psl_two_n hn3
  obtain ⟨f⟩ := quot_equiv_of_isAut (perfect_of_mem_cComp hKc) (ne_bot_of_mem_cComp hKc) hT
    hS.simple hS.center_eq_bot e
  exact eq_of_model hF h36 h38 hSQ hKc f hS

theorem eq_of_caseHe (hF : A318Facts) (h36 : A36ForSQTK) (h38 : A38ForSQTK)
    (hK : KnownFacts15122Types) {T Mc Kc : Subgroup G} (hSQ : SQTKGroup ↥Mc)
    (h : Case15212He T Mc Kc) : Kc = oPrimeResidualOf 3 Mc := by
  obtain ⟨-, hKc, ⟨e⟩⟩ := h
  have : Finite (CFSG.Blueprint.NativeSporadic.Carrier .He) := Finite.of_equiv _ e.toEquiv
  exact eq_of_model hF h36 h38 hSQ hKc ((Der6D.oTwoQuotEquiv Kc).symm.trans e)
    (hK.he _ ⟨MulEquiv.refl _⟩)

theorem le_of_caseiii (hA3 : A3Orbits G) (h122 : Lemma122A) {T Mc M : Subgroup G}
    (hs : Setting152 T Mc M) {Kc : Subgroup G} (h : Case15212iii T Mc Kc) :
    oPrimeResidualOf 3 Mc ≤ Kc := by
  classical
  obtain ⟨L, t, -, hL, ht, htN, hKc, -, hquot⟩ := h
  have hTMc : T ≤ Mc := hs.qtfe.t_le_mc
  have hPMc : pCoreOf 2 Mc ≠ ⊥ := pCoreOf_ne_bot_of_isTwoLocal hs.qtfe.mc_max.1
  have hsylMc : IsSylowTwoOf T Mc := isSylowTwoOf_of_quasithinIsSylowTwo hs.qtfe.sylow hTMc
  have hSQ : IsSQTKIn Mc :=
    sqtkGroup_of_pCoreOf_ne_bot hs.qtfe.qtke hs.qtfe.simple hs.qtfe.nonabelian hPMc
  obtain ⟨horb, hcase⟩ := hA3 Mc T L hSQ hsylMc hL
  obtain ⟨t', ht'T, ht'N, hpair⟩ : ∃ t' ∈ T, t' ∉ Subgroup.normalizer (L : Set G) ∧
      conjSubgroupsBy T L = {L, conjByElt t' L} := by
    rcases hcase with hn | ⟨t', ht', hn', hpair, -⟩
    · exact absurd (hn t ht) htN
    · exact ⟨t', ht', hn', hpair⟩
  have hne : L ≠ conjByElt t' L := fun h => ht'N (A38.map_conj_eq_iff.mp h.symm)
  have hnc : Set.ncard (conjSubgroupsBy Mc L) = 2 := by
    rw [horb, hpair]
    exact Set.ncard_pair hne
  have h3 : 3 ∣ Nat.card (↥L ⧸ CFSG.pCore 2 ↥L) := by
    rw [← Nat.card_congr (Der6D.oTwoQuotEquiv L).toEquiv]
    rcases hquot with ⟨f, -, ⟨e'⟩⟩ | ⟨p, hp, -, ⟨e'⟩⟩
    · rw [Nat.card_congr e'.toEquiv]
      exact three_dvd_card_psl_two (GaloisField 2 f)
    · have : Fact p.Prime := ⟨hp⟩
      rw [Nat.card_congr e'.toEquiv]
      exact three_dvd_card_psl_two (ZMod p)
  have hcl := h122 G hs.qtfe.simple hs.qtfe.qtke hs.qtfe.nonabelian Mc L hPMc hL 3 Nat.prime_three
    (by norm_num) hnc h3
  have hY := Der6D.conjClosure_eq_sup_of_orbit (hTMc ht'T) (horb.trans hpair)
  have hLt : conjSub t L = conjByElt t' L := by
    have hmem : conjByElt t L ∈ conjSubgroupsBy T L := ⟨t, ht, rfl⟩
    rw [hpair] at hmem
    rcases hmem with h | h
    · exact absurd (A38.map_conj_eq_iff.mp h) htN
    · exact h
  show Subgroup.closure {x : G | x ∈ Mc ∧ ∃ k : ℕ, orderOf x = 3 ^ k} ≤ Kc
  rw [hcl, hY, hKc, hLt]

end He8

end CFSG.Quasithin
