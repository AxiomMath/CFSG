module

public import CFSG.Quasithin.Background.ONanE68Act
public import CFSG.Quasithin.H13.KGFact68Spor
public import CFSG.Quasithin.H13.KGFact68CSLin
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.L239ListedMain
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_8Small

public section

namespace CFSG.Quasithin

namespace E6

namespace E68Proof

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.H13.KG68 CFSG.Assembly
  CFSG.Assembly.LowTwoRank CFSG.Blueprint CFSG.QuasithinUnique.Vol2Native.L239

section Generic

variable {Y : Type} [Group Y] [Finite Y] {L A R : Subgroup Y}

omit [Finite Y] in
theorem inner_of_isInnerAut (hb : E6.E68BaseHyp L A R)
    (hI : ∀ β : ↥L ≃* ↥L, (∀ x, β (β x) = x) →
      (∃ P : Sylow 2 ↥L, ∀ t ∈ (P : Subgroup ↥L), β t = t) → Ch1.IsInnerAut β) :
    ∀ a (ha : a ∈ A), ∃ g : ↥L, conjOn L a (leN_base hb ha) = MulAut.conj g := by
  intro a ha
  have hsq := conjOn_sq_base hb ha
  have hinv : ∀ x, conjOn L a (leN_base hb ha) (conjOn L a (leN_base hb ha) x) = x := fun x => by
    have := congrArg (fun γ : MulAut ↥L => γ x) hsq
    simpa using this
  obtain ⟨l, hl⟩ := hI (conjOn L a (leN_base hb ha)) hinv
    ⟨sylowInB hb, fun t ht => conjOn_fix_base hb ha ht⟩
  refine ⟨l⁻¹, ?_⟩
  ext x
  rw [hl x, MulAut.conj_apply, inv_inv]

theorem relIndex_le_two_of_inner_cyc (hb : E6.E68BaseHyp L A R) (hZ : Subgroup.center ↥L = ⊥)
    (hI : ∀ β : ↥L ≃* ↥L, (∀ x, β (β x) = x) →
      (∃ P : Sylow 2 ↥L, ∀ t ∈ (P : Subgroup ↥L), β t = t) → Ch1.IsInnerAut β)
    (hcyc : ∀ P : Sylow 2 ↥L, IsCyclic (Subgroup.center ↥(P : Subgroup ↥L))) :
    (A ⊓ Subgroup.centralizer (L : Set Y)).relIndex A ≤ 2 :=
  (relIndex_le_of_inner_base hb hZ (inner_of_isInnerAut hb hI)).trans
    (card_omegaZ_le_two _ (hcyc _))

theorem relIndex_le_two_of_smallList (hb : E6.E68BaseHyp L A R)
    (hS : SmallListFacts ↥L) (hF : FixPointwiseInner ↥L) :
    (A ⊓ Subgroup.centralizer (L : Set Y)).relIndex A ≤ 2 := by
  set P := ((sylowInB hb : Sylow 2 ↥L) : Subgroup ↥L) with hPdef
  have hPsyl : IsSylowTwoOf P ⊤ := isSylowTwoOf_top_of_sylow (sylowInB hb)
  have hshape := hS.sylow_shape P hPsyl
  have hP2 : IsPGroup 2 P := (sylowInB hb).isPGroup'
  have hcZ : Nat.card (Subgroup.center ↥P) = 2 := card_center_of_shape P hP2 hshape
  have hP8 : 8 ≤ Nat.card ↥P := by
    rcases hshape with ⟨n, hn, ⟨e⟩⟩ | he
    · rw [Nat.card_congr e.toEquiv, DihedralGroup.nat_card]
      omega
    · obtain ⟨e⟩ := he
      rw [Nat.card_congr e.toEquiv, CFSG.Semidihedral.card 4 (by norm_num)]
      norm_num
  have hZ : Subgroup.center ↥L = ⊥ := by
    have := hS.simple
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center ↥L) with h1 | h1
    · exact h1
    · exfalso
      have h2 : Subgroup.center ↥P = ⊤ := by
        rw [eq_top_iff]
        intro x _
        rw [Subgroup.mem_center_iff]
        intro y
        have h3 : (x : ↥L) ∈ Subgroup.center ↥L := by rw [h1]; trivial
        exact Subtype.ext (Subgroup.mem_center_iff.mp h3 (y : ↥L))
      rw [h2, Subgroup.card_top] at hcZ
      omega
  refine (relIndex_le_of_inner_base hb hZ (fun a ha => ?_)).trans
    ((card_omegaZ_le_card_center P).trans hcZ.le)
  obtain ⟨g, hg⟩ := hF P hPsyl (conjOn L a (leN_base hb ha)) fun y hy => conjOn_fix_base hb ha hy
  exact ⟨g, hg.symm⟩

end Generic

section Numerics

variable {G : Type} [Group G] [Finite G] {T M V U L : Subgroup G}

omit [Finite G] in
theorem le_centralizer_of_le_centralizer {V L : Subgroup G}
    (h : V ≤ Subgroup.centralizer (L : Set G)) : L ≤ Subgroup.centralizer (V : Set G) :=
  fun l hl => Subgroup.mem_centralizer_iff.2 fun _ hv =>
    (Subgroup.mem_centralizer_iff.1 (h hv) l hl).symm

theorem mQuot_ne_zero_of_not_le (h : HypE61 T M V) (hLM : ¬ L ≤ M) :
    E3.mQuot V (V ⊓ Subgroup.centralizer (L : Set G)) ≠ 0 := fun h0 => hLM (by
  have hV : V ⊓ Subgroup.centralizer (L : Set G) = V :=
    (E3.mQuot_eq_zero_iff h.isPGroup_V inf_le_left).1 h0
  exact (le_centralizer_of_le_centralizer (hV ▸ inf_le_right)).trans h.centralizer_le)

theorem mQuot_eq_one_of_relIndex_le_two (h : HypE61 T M V) (hLM : ¬ L ≤ M)
    (hle : (V ⊓ Subgroup.centralizer (L : Set G)).relIndex V ≤ 2) :
    E3.mQuot V (V ⊓ Subgroup.centralizer (L : Set G)) = 1 := by
  have hpow := E3.relIndex_eq_two_pow h.isPGroup_V (V ⊓ Subgroup.centralizer (L : Set G))
  have hne := mQuot_ne_zero_of_not_le h hLM
  have hle1 : E3.mQuot V (V ⊓ Subgroup.centralizer (L : Set G)) ≤ 1 := by
    by_contra hlt
    push Not at hlt
    have h4 : 2 ^ 2 ≤ 2 ^ E3.mQuot V (V ⊓ Subgroup.centralizer (L : Set G)) :=
      Nat.pow_le_pow_right (by norm_num) hlt
    rw [← hpow] at h4
    omega
  omega

theorem rParam_eq_one_of (h : HypE61 T M V) {A : Subgroup G} (hAV : A ≤ V)
    (hm : E3.mQuot V A = 1) (hC : ¬ Subgroup.centralizer (A : Set G) ≤ M) :
    E3.rParam V = 1 := by
  unfold E3.rParam
  apply le_antisymm
  · exact (iInf₂_le A ⟨hAV, fun hle => hC (hle.trans h.normalizer_le)⟩).trans (by rw [hm]; simp)
  · refine le_iInf₂ fun W hW => ?_
    have hne : E3.mQuot V W ≠ 0 := fun h0 => hW.2 (by
      rw [(E3.mQuot_eq_zero_iff h.isPGroup_V hW.1).1 h0]
      exact Subgroup.centralizer_le_normalizer _)
    exact_mod_cast Nat.one_le_iff_ne_zero.2 hne

theorem case5_of_relIndex_le_two (h : HypE61 T M V) (hU : U ∈ gammaE64 V M)
    (hL : IsComponentIn L (Subgroup.centralizer (U : Set G)))
    (hmodel : (∃ p : ℕ, Ch1.IsFermatOrMersennePrime p ∧
        LowTwoRank.StatedClassicalModel ↥L .PSL 2 p 1) ∨
      LowTwoRank.StatedClassicalModel ↥L .PSL 3 3 1 ∨
      Nonempty (↥L ≃* NativeSporadic.Carrier .M11))
    (hle : (V ⊓ Subgroup.centralizer (L : Set G)).relIndex V ≤ 2) : E68Case5 M V U L := by
  have hLM := not_le_of_component h hU.1 hL
  have hm := mQuot_eq_one_of_relIndex_le_two h hLM hle
  exact ⟨hmodel, fun hHM => eq_inf_centralizer_of_hypOrMax h hU hL hHM, hm,
    rParam_eq_one_of h inf_le_left hm fun hC => hLM ((le_centralizer_inf_centralizer V L).trans hC)⟩

theorem case5_l33
    (hcat : ∀ (X : Type) [Group X] [Finite X], LowTwoRank.StatedClassicalModel X .PSL 3 3 1 →
      SmallListFacts X ∧ FixPointwiseInner X)
    (h : HypE61 T M V) (hU : U ∈ gammaE64 V M)
    (hL : IsComponentIn L (Subgroup.centralizer (U : Set G)))
    (hmodel : LowTwoRank.StatedClassicalModel ↥L .PSL 3 3 1) : E68Case5 M V U L := by
  obtain ⟨hS, hF⟩ := hcat ↥L hmodel
  exact case5_of_relIndex_le_two h hU hL (Or.inr (Or.inl hmodel))
    (relIndex_le_two_of_smallList (baseHyp h hU hL) hS hF)

theorem case5_l2p
    (hcat : ∀ (X : Type) [Group X] [Finite X] (p : ℕ), Ch1.IsFermatOrMersennePrime p → 7 ≤ p →
      LowTwoRank.StatedClassicalModel X .PSL 2 p 1 → SmallListFacts X ∧ FixPointwiseInner X)
    (h : HypE61 T M V) (hU : U ∈ gammaE64 V M)
    (hL : IsComponentIn L (Subgroup.centralizer (U : Set G))) {p : ℕ}
    (hFM : Ch1.IsFermatOrMersennePrime p) (h7 : 7 ≤ p)
    (hmodel : LowTwoRank.StatedClassicalModel ↥L .PSL 2 p 1) : E68Case5 M V U L := by
  obtain ⟨hS, hF⟩ := hcat ↥L p hFM h7 hmodel
  exact case5_of_relIndex_le_two h hU hL (Or.inl ⟨p, hFM, hmodel⟩)
    (relIndex_le_two_of_smallList (baseHyp h hU hL) hS hF)

theorem case5_m11 (hInn : Ch1.SporadicAutInner) (hcyc : SporadicSylowCenterCyclic)
    (hcov : L239Covers) (h : HypE61 T M V) (hU : U ∈ gammaE64 V M)
    (hL : IsComponentIn L (Subgroup.centralizer (U : Set G)))
    (e : (↥L ⧸ CFSG.pCore 2 ↥L) ≃* NativeSporadic.Carrier .M11) : E68Case5 M V U L := by
  have hq : CFSG.IsQuasisimple ↥L := BenderBranch.isQuasisimple_of_isComponentIn hL
  have : Group.IsPerfect ↥L := hq.1
  have hZ : Subgroup.center ↥L = ⊥ := hcov G L hq (Or.inl ⟨e⟩)
  have hpc : CFSG.pCore 2 ↥L = ⊥ := le_bot_iff.mp ((pCore_two_le_center hq.2.1).trans hZ.le)
  obtain ⟨e'⟩ : Nonempty (↥L ≃* NativeSporadic.Carrier .M11) :=
    ⟨(mulEquivQuotientPCore hpc).trans e⟩
  have hs : Ch1.IsLemma115SporadicName .M11 := Or.inl rfl
  obtain ⟨hsq, hne⟩ := isSQTK_of_isLemma115 hs
  have hle : (V ⊓ Subgroup.centralizer (L : Set G)).relIndex V ≤ 2 :=
    relIndex_le_two_of_inner_cyc (baseHyp h hU hL) hZ
      (fun β hβ hP => hInn .M11 hsq hne ↥L ⟨e'⟩ β hβ hP)
      (fun P => isCyclic_center_sylow_of_mulEquiv e' (hcyc .M11 hs) P)
  exact case5_of_relIndex_le_two h hU hL (Or.inr (Or.inr ⟨e'⟩)) hle

end Numerics

end E68Proof

end E6

end CFSG.Quasithin
