module

public import CFSG.Quasithin.EmptyFaithful.S146zXGPrime
public import CFSG.Quasithin.EmptyFaithful.S146zXGFour
public import CFSG.Quasithin.EmptyFaithful.S146zXGIndex
public import CFSG.Quasithin.EmptyFaithful.S146zXGCenter
public import CFSG.Quasithin.EmptyFaithful.S146zXComp
public import CFSG.Quasithin.EmptyFaithful.S146zXF918
public import CFSG.Quasithin.EmptyFaithful.S146zXOut
public import CFSG.Quasithin.EmptyFaithful.S146zXPA5
public import CFSG.Quasithin.EmptyFaithful.S146zXAAut
public import CFSG.Quasithin.EmptyFaithful.S146zXTAux
public import CFSG.Quasithin.EmptyFaithful.S146zXTInsp
public import CFSG.Quasithin.EmptyFaithfulMultiple.Facts15420Proof
public import CFSG.Quasithin.H13.NQCoreP134Setup

public section

namespace CFSG.Quasithin.S146zX

open CFSG.Open hiding StatedClassicalModel StatedSL StatedLieTag
open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.F7 CFSG.Assembly.LowTwoRank
open CFSG.Quasithin.EmptyFaithfulMultiple
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G] {T M : Subgroup G}

@[expose] def ListsOut (T : Subgroup G) (p : ℕ) (Kz : Subgroup G) : Prop :=
  ∃ K₁ : Subgroup G, K₁ ∈ cComp (mcOf T) ∧
    ((∃ s : G, s ∈ T ∧ s ∉ Subgroup.normalizer (K₁ : Set G) ∧ Kz = K₁ ⊔ conjSub s K₁ ∧
        ListI p (OTwoQuot K₁)) ∨
      (p = 3 ∧ Kz = K₁ ∧ ∃ n : ℕ, (n = 4 ∨ n = 5) ∧
        Nonempty (OTwoQuot (K₁ ⊔ T) ≃* MulAut (Matrix.SpecialLinearGroup (Fin n) (ZMod 2)))))

theorem listI_congr {p : ℕ} {X Y : Type} [Group X] [Group Y] (e : X ≃* Y) (h : ListI p X) :
    ListI p Y := by
  rcases h with ⟨m, hm, hd, ⟨f⟩⟩ | ⟨hp, ⟨f⟩⟩
  · exact Or.inl ⟨m, hm, hd, ⟨e.symm.trans f⟩⟩
  · exact Or.inr ⟨hp, ⟨e.symm.trans f⟩⟩

theorem pair_case (hA37 : A37ForSQTK) (hA38 : A38ForSQTK)
    (hD36 : D36) (hD37 : D37) (hD321 : D321) (hI5 : Insp5a) (hA3 : A3Orbits G)
    (S : Setting146 G T M) {p : ℕ} [Fact p.Prime] (hp : p = 3 ∨ p = 5) {K L P : Subgroup G}
    (hL : L ∈ cComp (mcOf T)) (hq : CFSG.IsQuasisimple (↥L ⧸ CFSG.pCore 2 ↥L))
    (hXL : K ≤ conjClosure L T) (hPK : P ≤ K) (hPp : IsPGroup p P)
    (hnL : ¬ T ≤ Subgroup.normalizer (L : Set G)) (hPL : P ⊓ L ≠ ⊥)
    (htype : (∃ n : ℕ, p ∣ 2 ^ n - 1 ∧
        StatedClassicalModel (↥L ⧸ CFSG.pCore 2 ↥L) StatedLieTag.PSL 2 2 n) ∨
      ∃ q : ℕ, q.Prime ∧ q ≠ 2 ∧
        StatedClassicalModel (↥L ⧸ CFSG.pCore 2 ↥L) StatedLieTag.PSL 2 q 1) :
    ∃ s : G, s ∈ T ∧ s ∉ Subgroup.normalizer (L : Set G) ∧
      conjClosure K (mcOf T) = L ⊔ conjSub s L ∧
      (ListI p (OTwoQuot L) ∨ (p = 5 ∧ Nat.card (↥L ⧸ CFSG.pCore 2 ↥L) = 60 ∧
        IsSimpleGroup (↥L ⧸ CFSG.pCore 2 ↥L))) := by
  have hp2 : p ≠ 2 := by rcases hp with rfl | rfl <;> norm_num
  have hTMc : T ≤ mcOf T := S.isHTM_mcOf.1.1
  have hsylMc : IsSylowTwoOf T (mcOf T) := isSylowTwoOf_of_quasithinIsSylowTwo S.hyp.sylow hTMc
  have hSQ : IsSQTKIn (mcOf T) := S.sqtkGroup_of_isHTM S.isHTM_mcOf
  obtain ⟨horb, hcase⟩ := hA3 (mcOf T) T L hSQ hsylMc hL
  rcases hcase with hnorm | ⟨t', ht'T, ht'N, hpair, -, -, -⟩
  · exact absurd (fun t ht => hnorm t ht) hnL
  have hY := Der6D.conjClosure_eq_sup_of_orbit (hTMc ht'T) (horb.trans hpair)
  have hZ : Subgroup.center (↥L ⧸ CFSG.pCore 2 ↥L) = ⊥ := by
    rcases htype with ⟨n, -, hm⟩ | ⟨q, -, -, hm⟩
    · exact facts15420_centerPSL _ 2 2 n hm
    · exact facts15420_centerPSL _ 2 q 1 hm
  have hKc := conjClosure_eq_sup_of_pair' hp2 hL hTMc ht'T hY hXL hq hZ hPK hPp hPL
  refine ⟨t', ht'T, ht'N, hKc, ?_⟩
  have e : OTwoQuot L ≃* (↥L ⧸ CFSG.pCore 2 ↥L) := Der6D.oTwoQuotEquiv L
  rcases htype with ⟨n, hdvd, hm⟩ | ⟨q, hqp, hq2, hm⟩
  · exact Or.inl (listI_congr e.symm (listI_of_psl2_even (Fact.out) hm hdvd))
  · have hs := isSimpleGroup_kbar_of_isQuasisimple hq hZ
    have h5 := fiveShape_of_not_invariant hA37 hA38 hD36 hD37 hD321 hI5 S hL hs hnL
    have h5' : FiveShape (↥L ⧸ CFSG.pCore 2 ↥L) := fiveShape_congr (kbarEquiv L) h5
    have hdvd : p ∣ Nat.card (↥L ⧸ CFSG.pCore 2 ↥L) := dvd_card_kbar_of_inf_ne_bot hp2 hPp hPL
    rcases listI_of_psl2_prime hp hqp hq2 hm h5' hdvd with h | ⟨hp5, hc⟩
    · exact Or.inl (listI_congr e.symm h)
    · exact Or.inr ⟨hp5, hc, MulEquiv.isSimpleGroup (kbarEquiv L).symm⟩

theorem le_normalizer_of_invariant {Mc L : Subgroup G} (hA3 : A3Orbits G) (hSQ : IsSQTKIn Mc)
    (hsyl : IsSylowTwoOf T Mc) (hL : L ∈ cComp Mc) (hTL : T ≤ Subgroup.normalizer (L : Set G)) :
    Mc ≤ Subgroup.normalizer (L : Set G) := by
  obtain ⟨horb, -⟩ := hA3 Mc T L hSQ hsyl hL
  intro g hg
  have hmem : conjByElt g L ∈ conjSubgroupsBy Mc L := ⟨g, hg, rfl⟩
  rw [horb] at hmem
  obtain ⟨t, ht, hgt⟩ := hmem
  have h1 : conjByElt t L = L := A38.map_conj_eq_iff.mpr (hTL ht)
  have h2 : conjByElt g L = L := by rw [hgt]; exact h1
  exact A38.map_conj_eq_iff.mp h2

section FourListCerts


theorem inv_case_three
    (hA37 : A37ForSQTK) (hA38 : A38ForSQTK) (hD310 : D310) (hD391 : D391) (hI4 : Insp4)
    (hA3 : A3Orbits G) (S : Setting146 G T M) {H PQ : Subgroup G} (hred : IsRedCE T M H PQ 3)
    {H₀ H₁ H₂ : Subgroup G} {t₀ : G} (hdec : IsDecP T M H 3 H₀ H₁ H₂ t₀) {P : Subgroup G}
    (hP : IsSylowIn 3 P (oTwoUpper H)) (hPne : P ≠ ⊥) {L : Subgroup G}
    (hL : L ∈ cComp (mcOf T)) (hq : CFSG.IsQuasisimple (↥L ⧸ CFSG.pCore 2 ↥L))
    (hXL : oTwoUpper H ≤ conjClosure L T) (hTL : T ≤ Subgroup.normalizer (L : Set G))
    (htype : InvTypeThree (↥L ⧸ CFSG.pCore 2 ↥L)) :
    ListsOut T 3 (conjClosure (oTwoUpper H) (mcOf T)) := by
  have hTMc : T ≤ mcOf T := S.isHTM_mcOf.1.1
  have hsylMc : IsSylowTwoOf T (mcOf T) := isSylowTwoOf_of_quasithinIsSylowTwo S.hyp.sylow hTMc
  have hSQ : IsSQTKIn (mcOf T) := S.sqtkGroup_of_isHTM S.isHTM_mcOf
  have hMcL := le_normalizer_of_invariant hA3 hSQ hsylMc hL hTL
  have hKL : oTwoUpper H ≤ L := hXL.trans (conjClosure_le fun g hg l hl =>
    (Subgroup.mem_normalizer_iff.mp (hTL hg) l).mp hl)
  have hcenter : Subgroup.center (↥L ⧸ CFSG.pCore 2 ↥L) = ⊥ := by
    rcases htype with h | h | h | h | h | h
    · exact facts15420_centerPSL _ 3 3 1 h
    · exact facts15420_centerSL33M11 _ (Or.inl h)
    · exact facts15420_centerSL33M11 _ (Or.inr h)
    · exact facts15420_centerPSL _ 4 2 1 h
    · exact facts15420_centerPSL _ 5 2 1 h
    · exact facts15420_centerHe _ h
  have hKc : conjClosure (oTwoUpper H) (mcOf T) = L :=
    conjClosure_eq_of_invariant' (by norm_num) hL hMcL hKL hq hcenter hP.le hP.isPGroup hPne
  by_cases hHe : Nonempty ((↥L ⧸ CFSG.pCore 2 ↥L) ≃*
      CFSG.Blueprint.NativeSporadic.Carrier TauCeti.SporadicName.He)
  · exfalso
    obtain ⟨eHe⟩ := hHe
    have hs := isSimpleGroup_kbar_of_isQuasisimple hq hcenter
    have h4 := fourList_of_invariant hA37 hA38 hD310 hD391 hI4 S hL hs hTL
    exact not_fourList_of_he ⟨(kbarEquiv L).trans eHe⟩ h4
  · have hlist : StatedClassicalModel (↥L ⧸ CFSG.pCore 2 ↥L) StatedLieTag.PSL 3 3 1 ∨
        Nonempty ((↥L ⧸ CFSG.pCore 2 ↥L) ≃* ↥(StatedSL 3 (ZMod 3))) ∨
        Nonempty ((↥L ⧸ CFSG.pCore 2 ↥L) ≃*
          CFSG.Blueprint.NativeSporadic.Carrier TauCeti.SporadicName.M11) ∨
        StatedClassicalModel (↥L ⧸ CFSG.pCore 2 ↥L) StatedLieTag.PSL 4 2 1 ∨
        StatedClassicalModel (↥L ⧸ CFSG.pCore 2 ↥L) StatedLieTag.PSL 5 2 1 := by
      rcases htype with h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr (Or.inl h))
      · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
      · exact Or.inr (Or.inr (Or.inr (Or.inr h)))
      · exact absurd h hHe
    have hTH : T ≤ H := hred.isHTM.1.1
    obtain ⟨n, hn, hAut⟩ := insp_of_card S.hyp.sylow hTMc hTH hMcL hKL
      (card_eq_seventyTwo_mul S hred hdec) hlist
    exact ⟨L, hL, Or.inr ⟨rfl, hKc, n, hn, hAut⟩⟩

theorem false_of_inv_five (hA37 : A37ForSQTK) (hA38 : A38ForSQTK) (hD310 : D310)
    (hD391 : D391) (hI4 : Insp4) (S : Setting146 G T M) {p : ℕ} [Fact p.Prime] (hp : p = 5)
    {L : Subgroup G} (hL : L ∈ cComp (mcOf T))
    (hq : CFSG.IsQuasisimple (↥L ⧸ CFSG.pCore 2 ↥L))
    (hTL : T ≤ Subgroup.normalizer (L : Set G))
    (htype : InvTypeFive p (↥L ⧸ CFSG.pCore 2 ↥L)) : False := by
  have hcenter : Subgroup.center (↥L ⧸ CFSG.pCore 2 ↥L) = ⊥ := by
    rcases htype with h | h
    · exact facts15420_centerPSL _ 3 p 1 h
    · exact center_eq_bot_of_sl3 hp h
  have hs := isSimpleGroup_kbar_of_isQuasisimple hq hcenter
  have h4 := fourList_of_invariant hA37 hA38 hD310 hD391 hI4 S hL hs hTL
  refine not_fourList_of_l35 hp (X := KBar L) ?_ h4
  rcases htype with h | h
  · exact Or.inl (CFSG.SectionRank.statedClassicalModel_of_mulEquiv (kbarEquiv L) h)
  · obtain ⟨e⟩ := h
    exact Or.inr ⟨(kbarEquiv L).trans e⟩

theorem lists_of_out134
    (hA37 : A37ForSQTK) (hA38 : A38ForSQTK) (hD36 : D36) (hD37 : D37) (hD321 : D321)
    (hI5 : Insp5a) (hD310 : D310) (hD391 : D391) (hI4 : Insp4) (hA3 : A3Orbits G)
    (S : Setting146 G T M) {H PQ : Subgroup G} {p : ℕ} [Fact p.Prime]
    (hred : IsRedCE T M H PQ p) (hp : p = 3 ∨ p = 5) {H₀ H₁ H₂ : Subgroup G} {t₀ : G}
    (hdec : IsDecP T M H p H₀ H₁ H₂ t₀) (hne : conjClosure (oTwoUpper H) (mcOf T) ≠ oTwoUpper H)
    (hX : IsXi T (oTwoUpper H)) {P : Subgroup G} (hP : IsSylowIn p P (oTwoUpper H))
    (hPc : Nat.card P = p ^ 2) (hout : Out134 p T (mcOf T) (oTwoUpper H) P) :
    ListsOut T p (conjClosure (oTwoUpper H) (mcOf T)) := by
  have hp2 : p ≠ 2 := hred.odd
  have hTMc : T ≤ mcOf T := S.isHTM_mcOf.1.1
  have hsylMc : IsSylowTwoOf T (mcOf T) := isSylowTwoOf_of_quasithinIsSylowTwo S.hyp.sylow hTMc
  have hKMc : oTwoUpper H ≤ mcOf T := (oTwoUpper_le H).trans (S.le_mcOf hred.isHTM)
  have hPne : P ≠ ⊥ := by
    intro h
    rw [h, Subgroup.card_bot] at hPc
    have h2 := (Fact.out : p.Prime).two_le
    nlinarith
  rcases hout with hN | ⟨L, hL, hq, hXL, ⟨hnL, hPL, htype⟩ | ⟨hTL, htype⟩ | ⟨hTL, hcyc⟩⟩
  · exact absurd (le_antisymm (conjClosure_le fun g hg k hk =>
      (Subgroup.mem_normalizer_iff.mp (hN hg) k).mp hk) (le_conjClosure _ _)) hne
  · obtain ⟨s, hsT, hsN, hKc, hres⟩ := pair_case hA37 hA38 hD36 hD37 hD321 hI5 hA3 S hp hL hq
      hXL hP.le hP.isPGroup hnL hPL htype
    rcases hres with hI | ⟨hp5, hc, hs⟩
    · exact ⟨L, hL, Or.inl ⟨s, hsT, hsN, hKc, hI⟩⟩
    · exfalso
      have hpX : p ∣ Nat.card (oTwoUpper H) := by
        rw [card_eq_card_pCoreOf_mul_relIndex, relIndex_pCoreOf_oTwoUpper_of_isDecP S hred hdec]
        exact Dvd.dvd.mul_left (dvd_pow_self p two_ne_zero) _
      have hmul := H13.NQCore.mul_subset_of_sylow hsylMc hKMc hX hp2 hpX hP
      exact false_of_card_sixty hp5 hsylMc hL hmul hP.isPGroup hPL hc
        (fun A => by have := hs; exact not_index_three_of_card_sixty hc A)
  · rcases htype with ⟨hp3, h3⟩ | ⟨hp5, h5⟩
    · subst hp3
      exact inv_case_three hA37 hA38 hD310 hD391 hI4 hA3 S hred hdec hP hPne hL hq hXL hTL h3
    · exact (false_of_inv_five hA37 hA38 hD310 hD391 hI4 S hp5 hL hq hTL h5).elim
  · exact absurd hcyc (not_autCyclic_of_isDecP S hred hdec hP hPc)

end FourListCerts

end CFSG.Quasithin.S146zX
