module

public import CFSG.RankThree.PartTwo.Sec8.Item812Res6ProofOccurs
import CFSG.RankThree.PartTwo.Sec8.Item83ProofRee
import CFSG.RankThree.PartTwo.Sec8.Item812Res2ProofXNormal

public section

namespace CFSG.RankThree.PartTwo.Sec8

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open Item86ResProof
open CFSG.Assembly.RankThreeEven (projSL projSU projSp)

section NoCert

namespace Item812Res7

variable {G : Type} [Group G] [Finite G]

theorem ne_bot_of_isGammaIndex {A Le : Subgroup G} {d : G} {m : ℕ} (hd : IsGammaIndex A Le d m)
    (hodd : Odd m) :
    inSubgroup perfectResidual (Le ⊓ Subgroup.centralizer ({d} : Set G)) ≠ ⊥ := by
  have hm : 1 ≤ m := one_le_of_isGammaIndex hd
  have himg : imageModTheta Le
      (inSubgroup perfectResidual (Le ⊓ Subgroup.centralizer ({d} : Set G))) ≠ ⊥ := by
    obtain ⟨-, -, -, ⟨-, -, -, -, hSU⟩ | ⟨-, ⟨ι⟩⟩⟩ := hd
    · have := Item83Proof.nontrivial_of_isoSUThree hodd hSU
      exact (Subgroup.nontrivial_iff_ne_bot _).mp this
    · have := Item83Proof.nontrivial_projSL_two (m := 3 * m) (by omega)
      exact Item83Proof.ne_bot_of_mulEquiv ι
  intro h0
  apply himg
  rw [h0, imageModTheta, Subgroup.bot_subgroupOf, Subgroup.map_bot]

end Item812Res7

end NoCert

@[expose] def Pair89OmegaCent : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G) (a b : G)
    (X : Subgroup G) (n : ℕ), Sec8Pair G A c L a b X n →
    ∀ p ∈ pairOmega A,
      Late.sectionCentralizer A p.2 ((aschbacherSolvableCore 3 p.2).map p.2.subtype) =
        (Subgroup.zpowers p.1 : Set G)

@[expose] def Pair89GammaInner : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G) (a b : G)
    (X : Subgroup G) (n : ℕ), Sec8Pair G A c L a b X n →
    ∀ p ∈ pairOmega A, ∀ d ∈ gammaSet A p.2,
      KFacts.InducesStdKind p.2 d .inner ∨ KFacts.InducesStdKind p.2 d .diagonal

@[expose] def Pair89OmegaD4 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G) (a b : G)
    (X : Subgroup G) (n : ℕ), Sec8Pair G A c L a b X n →
    ∀ p ∈ pairOmega A, ∀ m : ℕ, Odd m →
      IsoTrialityD4 (p.2 ⧸ aschbacherSolvableCore 3 p.2) m →
        ∃ x ∈ A, (KFacts.InducesStdKind p.2 x .field ∨ KFacts.InducesStdKind p.2 x .graphField) ∧
          IsoGTwoEven (barCentralizer (Subgroup.zpowers x) p.2) m

namespace Item812Res7

variable {G : Type} [Group G] [Finite G]

theorem ne_one_of_inducesStdKind {Le : Subgroup G} {x : G}
    (hk : KFacts.InducesStdKind Le x .field ∨ KFacts.InducesStdKind Le x .graphField) :
    x ≠ 1 := by
  rintro rfl
  have hout : Sec4.InducesOuterTheta (1 : G) Le := by
    rcases hk with hk | hk
    · exact KFacts.InducesStdKind.inducesOuterTheta Le hk (by decide)
    · exact KFacts.InducesStdKind.inducesOuterTheta Le hk (by decide)
  obtain ⟨hN, hnot⟩ := hout
  apply hnot
  rw [KFacts.thetaQuotMulAut_compAction_eq_one hN (fun y _ => by simp)]
  exact ⟨1, map_one _⟩

theorem hyp81_of_mem_pairOmega {A L : Subgroup G} {c a : G} (h : Hyp81 G A c L a)
    (hA81 : Nat.card A = 81) {e x : G} {Le : Subgroup G} (hΩ : (e, Le) ∈ pairOmega A)
    (hcent : Late.sectionCentralizer A Le ((aschbacherSolvableCore 3 Le).map Le.subtype) =
      (Subgroup.zpowers e : Set G)) (hxA : x ∈ A)
    (hk : KFacts.InducesStdKind Le x .field ∨ KFacts.InducesStdKind Le x .graphField) :
    Hyp81 G A e Le x where
  toPartTwoStanding := h.toPartTwoStanding
  mem_partTwoF := h.mem_partTwoF
  mem_A := hΩ.1
  ne_one := hΩ.2.1
  mem_thetaComponentsAt := hΩ.2.2.1
  sectionCentralizer_eq := hcent
  a_mem := hxA
  a_ne_one := ne_one_of_inducesStdKind hk
  inducesStdKind := hk
  exists_invariant_two := fun _ => exists_partTwoE_of_mem_pairOmega h.mem_partTwoF.1 hA81 hΩ
  partTwoE_eq := fun h27 => absurd (h27.symm.trans hA81) (by norm_num)

theorem projSL_of_isGammaIndex_of_not_sigF4 {A Le : Subgroup G} {d : G} {m : ℕ}
    (hd : IsGammaIndex A Le d m) (hF : ¬ SigF4 (Le ⧸ aschbacherSolvableCore 3 Le) m) :
    Nonempty (imageModTheta Le
      (inSubgroup perfectResidual (Le ⊓ Subgroup.centralizer ({d} : Set G))) ≃*
        projSL 2 (GaloisField 2 (3 * m))) := by
  have hm : 1 ≤ m := one_le_of_isGammaIndex hd
  obtain ⟨-, -, -, ⟨k, hk, hkm, he, -⟩ | ⟨-, hL2⟩⟩ := hd
  · exact (hF (sigF4_of_reeF4 hm ⟨k, hk, hkm, he⟩)).elim
  · exact hL2

theorem cases83_of_cases83 {Le : Subgroup G} {x : G} {A₀ A : Subgroup G} {d₀ d : G} {m : ℕ}
    (hC : Cases83 Le x A₀ d₀ m) (hd : IsGammaIndex A Le d m) (hg : Sec8PairGTwo Le x m) :
    Cases83 Le x A d m := by
  have hm : 1 ≤ m := one_le_of_isGammaIndex hd
  rcases hC with ⟨hT, -, -⟩ | ⟨hR, hRC, -⟩ | ⟨hS, hSC, -⟩ | ⟨hU, hUC, -⟩ | ⟨hSp, hSpC, -⟩
  · refine Or.inl ⟨hT, projSL_of_isGammaIndex_of_not_sigF4 hd fun hF => ?_, Or.inl (hg hT)⟩
    rcases hT with hD | hG
    · exact hF.false_of_sigD4 (sigD4_of_isoTrialityD4 hm hD) hm
    · exact hF.false_of_sigG2 (sigG2_of_isoGTwo hm (isoGTwo_of_isoGTwoEven (by omega) hG)) hm
  · obtain ⟨k, hk, hkm, he⟩ := reeF4_of_isoReeF4 (by omega) hR
    exact Or.inr (Or.inl ⟨hR, hRC,
      isoSUThree_of_isGammaIndex_of_sigF4 hd (sigF4_of_reeF4 hm ⟨k, hk, hkm, he⟩)⟩)
  · refine Or.inr (Or.inr (Or.inl ⟨hS, hSC, projSL_of_isGammaIndex_of_not_sigF4 hd fun hF => ?_⟩))
    exact hF.false_of_sigU (sigU_of_unitarySig (unitarySig_of_isoSUThree (by omega) hS)) hm
  · refine Or.inr (Or.inr (Or.inr (Or.inl ⟨hU, hUC,
      projSL_of_isGammaIndex_of_not_sigF4 hd fun hF => ?_⟩)))
    obtain ⟨e⟩ := hU
    exact hF.false_of_sigU (sigU_of_unitarySig (unitarySig_of_projSU (by omega) e)) hm
  · refine Or.inr (Or.inr (Or.inr (Or.inr ⟨hSp, hSpC,
      projSL_of_isGammaIndex_of_not_sigF4 hd fun hF => ?_⟩)))
    obtain ⟨e⟩ := hSp
    exact hF.false_of_sigSp4 (sigSp4_of_projSp hm e) hm

end Item812Res7

open Item812Res7

theorem pair89OmegaStd_of (h83 : Item83) (hC : Pair89OmegaCent) (hI : Pair89GammaInner)
    (hD4 : Pair89OmegaD4) : Pair89OmegaStd := by
  intro G _ _ A c L a b X n h p hp
  obtain ⟨e, Le⟩ := p
  have hΩ := hp
  obtain ⟨heA, -, -, ⟨x, hxA, hxk⟩, -, ⟨d, m, hdm⟩⟩ := hp
  have hA81 : Nat.card A = 81 := h.card_eq
  have h27 : 27 < Nat.card A := by rw [hA81]; norm_num
  have hcent := hC G A c L a b X n h (e, Le) hΩ
  have hm1 : 1 ≤ m := one_le_of_isGammaIndex hdm
  have hodd : Odd m := by
    obtain ⟨A₀, d₀, n₀, hD⟩ :=
      h83 G A e Le x (hyp81_of_mem_pairOmega h.toHyp81 hA81 hΩ hcent hxA hxk) h27
    have hmn : m = n₀ := eq_of_isGammaType hm1 hD.odd.pos (isGammaType_of_isGammaIndex hdm)
      (isGammaType_of_data83 hD)
    rw [hmn]
    exact hD.odd
  obtain ⟨x', hx'A, hx'k, hx'g⟩ : ∃ x' ∈ A,
      (KFacts.InducesStdKind Le x' .field ∨ KFacts.InducesStdKind Le x' .graphField) ∧
        Sec8PairGTwo Le x' m := by
    by_cases hD : IsoTrialityD4 (Le ⧸ aschbacherSolvableCore 3 Le) m
    · obtain ⟨x', hx'A, hk, hG2⟩ := hD4 G A c L a b X n h (e, Le) hΩ m hodd hD
      exact ⟨x', hx'A, hk, fun _ => hG2⟩
    · by_cases hG : IsoGTwoEven (Le ⧸ aschbacherSolvableCore 3 Le) (3 * m)
      · refine ⟨x, hxA, hxk, fun _ => ?_⟩
        obtain ⟨K, _, _, hK, ⟨eK⟩⟩ := hG
        have hout : Sec4.InducesOuterTheta x Le := by
          rcases hxk with hk | hk
          · exact KFacts.InducesStdKind.inducesOuterTheta Le hk (by decide)
          · exact KFacts.InducesStdKind.inducesOuterTheta Le hk (by decide)
        obtain ⟨-, k, hk, hkf, hkc, hC'⟩ :=
          KFacts.barCentralizer_mulEquiv_g2 (by omega) hK (h.mem_partTwoF.1.2 x hxA) hout eK
        exact ⟨k, hk, hkf, hkc, hC'⟩
      · exact ⟨x, hxA, hxk, fun hh => (hh.elim hD hG).elim⟩
  have h81 := hyp81_of_mem_pairOmega h.toHyp81 hA81 hΩ hcent hx'A hx'k
  obtain ⟨A₀, d₀, n₀, hD⟩ := h83 G A e Le x' h81 h27
  have hmn : m = n₀ := eq_of_isGammaType hm1 hD.odd.pos (isGammaType_of_isGammaIndex hdm)
    (isGammaType_of_data83 hD)
  subst hmn
  have hAc : ∀ u ∈ A, ∀ v ∈ A, u * v = v * u := fun u hu v hv =>
    congrArg Subtype.val (h.mem_partTwoF.1.1.is_comm.comm ⟨u, hu⟩ ⟨v, hv⟩)
  refine ⟨x', d, m, { toHyp81 := h81, data83 := ?_, gTwo := hx'g }⟩
  exact
    { le_normalizer := fun u hu => Item812Res2.mem_normalizer_zpowers_of_commute (hAc u hu e heA)
      c_mem := heA
      a_mem := hx'A
      isElemAbelian := h.mem_partTwoF.1
      card_eq := hA81
      sectionCentralizer_eq := hcent
      d_mem := hdm.1
      d_ne_one := hdm.2.1
      innerDiag := hI G A c L a b X n h (e, Le) hΩ d ⟨m, hdm⟩
      odd := hodd
      ne_bot := ne_bot_of_isGammaIndex hdm hodd
      cases := cases83_of_cases83 hD.cases hdm hx'g }

end CFSG.RankThree.PartTwo.Sec8
