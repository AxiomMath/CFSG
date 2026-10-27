module

public import CFSG.RankThree.PartTwo.Sec15.Liebeck155R1T150LieChev
public import CFSG.RankThree.PartTwo.Sec4.Ronan148LComp
import CFSG.RankThree.PartTwo.Sec4.Ronan148LH1
import CFSG.LocalAnalysis.StandardType.GGStructSOnePrimeCent
import CFSG.Quasithin.Background.C126RFSurj
public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.Export
public import CFSG.RankThree.PartTwo.Sec15.Liebeck155R1T150Core
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I142TInd
public import CFSG.LocalAnalysis.StandardType.GGStructSOneHolds

public section

namespace CFSG.RankThree.PartTwo.Sec15.Liebeck155R1T150

open CFSG CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec4
open CFSG.RankThree.PartTwo.Sec4.Ronan148L
open CFSG.HardMathSupport.Solomon.Coordinator CFSG.HardMathSupport.Solomon.LocalBalance
open scoped commutatorElement

theorem k150_exists_component_quot_of_perfect_subnormal_le_layer {G Q : Type} [Group G]
    [Finite G] [Group Q] [IsSimpleGroup Q] (hZ : Subgroup.center Q = ⊥) {X P : Subgroup G}
    (hPX : P ≤ X) (hsn : (P.subgroupOf X).IsSubnormal) (hP : Group.IsPerfect P)
    (hle : P ≤ CFSG.Open.GLALayer X) (f : P →* Q) (hf : Function.Surjective f) :
    ∃ E : Subgroup G, CFSG.Open.IsComponentOf E X ∧ E ≤ P ∧
      Nonempty (E ⧸ Subgroup.center E ≃* Q) := by
  classical
  obtain ⟨𝒜, h𝒜⟩ : ∃ 𝒜 : Set (Subgroup G),
      𝒜 = {K : Subgroup G | CFSG.Open.IsComponentOf K X ∧ K ≤ P} := ⟨_, rfl⟩
  have hmem : ∀ K : Subgroup G, K ∈ 𝒜 ↔ CFSG.Open.IsComponentOf K X ∧ K ≤ P := by
    intro K
    rw [h𝒜]
    exact Iff.rfl
  have hPeq : P = sSup 𝒜 := by
    rw [h𝒜]
    exact CFSG.StandardType.eq_sSup_components_of_perfect_isSubnormal
      (open_isSubnormal_of_subgroupOf hPX hsn) (Subgroup.isPerfect_iff.mp hP) hle
  obtain ⟨φ, hφ⟩ : ∃ φ : Subgroup G → Subgroup Q,
      ∀ (K : Subgroup G) (y : Q), y ∈ φ K ↔ ∃ x : P, (x : G) ∈ K ∧ f x = y :=
    ⟨fun K => (K.subgroupOf P).map f, fun K y => Iff.rfl⟩
  have hgen : ∀ S : Subgroup Q, (∀ K ∈ 𝒜, φ K ≤ S) → S = ⊤ := by
    intro S hS
    rw [eq_top_iff]
    intro y _
    obtain ⟨x, rfl⟩ := hf y
    have hsub : sSup 𝒜 ≤ (S.comap f).map P.subtype := by
      refine sSup_le fun K hK k hk => ?_
      have hkP : k ∈ P := ((hmem K).1 hK).2 hk
      exact ⟨⟨k, hkP⟩, hS K hK ((hφ K _).2 ⟨⟨k, hkP⟩, hk, rfl⟩), rfl⟩
    obtain ⟨m, hm, hmx⟩ := hsub (hPeq.le x.2)
    obtain rfl : m = x := Subtype.ext hmx
    exact hm
  obtain ⟨K₀, hK₀, hne⟩ : ∃ K ∈ 𝒜, φ K ≠ ⊥ := by
    by_contra hno
    push Not at hno
    exact bot_ne_top (hgen ⊥ fun K hK => (hno K hK).le)
  have hK₀c := (hmem K₀).1 hK₀
  have hnorm : (φ K₀).Normal := by
    rw [← Subgroup.normalizer_eq_top_iff]
    refine hgen _ fun K hK => ?_
    by_cases hKK : K = K₀
    · subst hKK
      exact Subgroup.le_normalizer
    · have hKc := (hmem K).1 hK
      have hcomm : ⁅K, K₀⁆ = ⊥ :=
        (LocalAnalysis.GLTheoremA.I142N.isComponent_commute_or_eq hKc.1 hK₀c.1).resolve_left hKK
      refine le_trans ?_ (Subgroup.centralizer_le_normalizer _)
      intro a ha
      obtain ⟨x, hx, rfl⟩ := (hφ K a).1 ha
      rw [Subgroup.mem_centralizer_iff]
      intro b hb
      obtain ⟨y, hy, rfl⟩ := (hφ K₀ b).1 hb
      rw [← map_mul, ← map_mul]
      congr 1
      refine Subtype.ext ?_
      have h1 : ⁅(x : G), (y : G)⁆ ∈ ⁅K, K₀⁆ := Subgroup.commutator_mem_commutator hx hy
      rw [hcomm, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at h1
      exact h1.symm
  have htop : φ K₀ = ⊤ :=
    (IsSimpleGroup.eq_bot_or_eq_top_of_normal (φ K₀)).resolve_left hne
  have hg : Function.Surjective (f.comp (Subgroup.inclusion hK₀c.2)) := by
    intro y
    have hy : y ∈ φ K₀ := htop ▸ Subgroup.mem_top y
    obtain ⟨x, hx, rfl⟩ := (hφ K₀ y).1 hy
    exact ⟨⟨(x : G), hx⟩, rfl⟩
  exact ⟨K₀, hK₀c.1, hK₀c.2,
    CFSG.Quasithin.C126.nonempty_quot_center_mulEquiv hK₀c.1.2.2 _ hg hZ⟩

@[expose] def NoCompAtFor (J : Type) [Group J] {S : Type} [Group S] (β : MulAut S) : Prop :=
  ∀ E : Subgroup S, CFSG.Open.IsComponentOf E (Sec4.autFix β) →
    IsEmpty (↥E ⧸ Subgroup.center ↥E ≃* J)

theorem k150_noCompAt_of_data {J : Type} [Group J] (hF : K150Facts J) {S : Type} [Group S]
    [Finite S] {β : MulAut S} {q : ℕ}
    (h : ∀ E : Subgroup S, CFSG.Open.GLAPComponent 3 (Lemma510Ns.fixSub β) E →
      LieComp.LieCompData q (barOf 3 E)) : NoCompAtFor J β := by
  intro E hE
  refine ⟨fun e => ?_⟩
  have hEo : CFSG.Open.IsQuasisimple ↥E := hE.2.2
  have h3 : 3 ∣ Nat.card E := by
    have h3Q : 3 ∣ Nat.card (↥E ⧸ Subgroup.center ↥E) := by
      rw [Nat.card_congr e.toEquiv]
      exact hF.three_dvd
    exact h3Q.trans (Subgroup.card_quotient_dvd_card _)
  have hd := h E (by rw [← autFix_eq_fixSub]; exact glaPComponent_three_of_isComponentOf hE h3)
  obtain ⟨e₁⟩ := centerQuot_equiv hEo.1 (CFSG.Open.GLAPPrimeCore 3 ↥E)
    (glaPPrimeCore_le_center hEo h3)
  exact hF.not_chev q (LieComp.isChevSimple_congr (e₁.trans e) hd.chev)

theorem k150_goodAll_of_layer {J : Type} [Group J] (hF : K150Facts J) {S : Type} [Group S]
    [Finite S] {β : MulAut S} (hN : NoCompAtFor J β) (hL : PerfectInLayer β) :
    GoodAllFor J (Sec4.autFix β) := by
  intro P hPC hPs hPp N hNn
  refine ⟨fun e => ?_⟩
  have hfix : Sec4.autFix β = fixSubgroup β := Subgroup.ext fun _ => Iff.rfl
  have hle : P ≤ CFSG.Open.GLALayer (Sec4.autFix β) := by
    rw [hfix]
    exact hL P (hPC.trans hfix.le) (Subgroup.isPerfect_iff.mp hPp)
  have := hF.simple
  obtain ⟨E, hE, -, ⟨e'⟩⟩ := k150_exists_component_quot_of_perfect_subnormal_le_layer hF.center
    hPC hPs hPp hle (e.toMonoidHom.comp (QuotientGroup.mk' N))
    (e.surjective.comp (QuotientGroup.mk'_surjective N))
  exact (hN E hE).false e'

theorem k150_rowAll_of_lie {J : Type} [Group J] (hF : K150Facts J) (hLSC : LieSemisimpleCent)
    (hLC : LieComp.LieComp) {X : Type} [Group X] (idx : TauCeti.ValidLieTypeIndex)
    (hchar : idx.1.characteristic ≠ 3)
    (hX : Nonempty (X ≃* (TauCeti.CFSGIndex.lie idx).Group)) : RowAllOfK150 J X := by
  intro S _ _ hs hna ⟨eS⟩ σ h3 h1
  obtain ⟨eX⟩ := hX
  have he : Nonempty (S ≃* (TauCeti.CFSGIndex.lie idx).Group) := ⟨eS.trans eX⟩
  exact k150_goodAll_of_layer hF
    (k150_noCompAt_of_data hF fun E hE => (hLC S hs hna idx he σ h3 E hE).1)
    (hLSC S hs hna idx he 3 Nat.prime_three (by norm_num) (Ne.symm hchar) σ h3 h1)

end CFSG.RankThree.PartTwo.Sec15.Liebeck155R1T150
