module

public import CFSG.LocalAnalysis.UniquenessCase.UCFront05
public import CFSG.LocalAnalysis.RankThreeUC.Section5.BinaryActionRankAlternatives
import all CFSG.LocalAnalysis.RankThreeUC.Section5.Context

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.F05

open CFSG.Open CFSG.RankThree.FFModules Subgroup
open CFSG.LocalAnalysis.RankThreeUC

variable {G : Type} [Group G] [Finite G] {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]

theorem ne_bot_of_one_lt_pRank {p : ℕ} (hp : p.Prime) {Y : Subgroup G} (h : 1 < CFSG.Open.pRank p Y) :
    Y ≠ ⊥ := by
  rintro rfl
  have h0 : CFSG.Open.pRank p (⊥ : Subgroup G) ≤ 0 := by
    refine csSup_le' fun k hk => ?_
    obtain ⟨E, hE, -, hcard⟩ := hk
    have hE1 : E = ⊥ := le_bot_iff.1 hE
    rw [hE1, Subgroup.card_bot] at hcard
    exact (Nat.pow_eq_one.1 hcard.symm).resolve_left hp.one_lt.ne' |>.le
  omega

theorem exponent_eq_of_pow_eq_one {X : Subgroup G} {p : ℕ} (hp : p.Prime) (h : ∀ x ∈ X, x ^ p = 1) (hX : X ≠ ⊥) :
    Monoid.exponent ↥X = p := by
  haveI : Nontrivial ↥X := (Subgroup.nontrivial_iff_ne_bot X).2 hX
  rcases (Nat.dvd_prime hp).1 (Monoid.exponent_dvd_of_forall_pow_eq_one fun x : ↥X =>
      Subtype.ext (by simpa using h x x.2)) with h1 | h1
  · exact absurd (Monoid.exp_eq_one_iff.1 h1) (not_subsingleton _)
  · exact h1

theorem pCoreOf_ne_bot_of_dvd {B : Subgroup G} (hB : IsMulCommutative B) {r : ℕ} (hr : r.Prime)
    (hd : r ∣ Nat.card B) : CFSG.Open.pCoreOf r B ≠ ⊥ := by
  haveI : Fact r.Prime := ⟨hr⟩
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := ↥B) r hd
  have hxo : orderOf (x : G) = r := by rw [Subgroup.orderOf_coe]; exact hx
  have hN : zpowers (x : G) ≤ B := zpowers_le.2 x.2
  have hNp : IsPGroup r ↥(zpowers (x : G)) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hxo, pow_one])
  have hnorm : B ≤ normalizer (zpowers (x : G) : Set G) := by
    refine le_trans (fun b hb => ?_) (Subgroup.centralizer_le_normalizer (zpowers (x : G) : Set G))
    rw [Subgroup.mem_centralizer_iff]
    intro n hn
    have := hB.is_comm.comm (⟨n, hN hn⟩ : ↥B) ⟨b, hb⟩
    exact congrArg Subtype.val this
  have hle := CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer r hN hnorm hNp
  intro hbot
  have hxbot : (x : G) ∈ CFSG.Open.pCoreOf r B := hle (mem_zpowers _)
  rw [hbot, Subgroup.mem_bot] at hxbot
  have : x = 1 := Subtype.ext hxbot
  rw [this, orderOf_one] at hx
  exact hr.one_lt.ne hx

theorem fixedSubmodule_eq_fixSub (ρ : Representation (ZMod 2) G V) (E : Subgroup G) :
    fixedSubmodule ρ E = fixSub ρ E := by
  ext v
  unfold fixedSubmodule
  rw [Representation.mem_invariants, mem_fixSub]
  exact ⟨fun h a ha => h ⟨a, ha⟩, fun h a => h a a.2⟩

theorem moduleM_eq_mGV (ρ : Representation (ZMod 2) G V) : moduleM ρ = mGV ρ := by
  have hset : involutionDisplacements ρ = {n | ∃ t : G, orderOf t = 2 ∧
      n = Module.finrank (ZMod 2) (V ⧸ fixSub ρ (zpowers t))} := by
    ext n
    constructor
    · rintro ⟨t, ht, hn⟩
      refine ⟨t, ht, ?_⟩
      rw [hn, fixedSubmodule_eq_fixSub]
    · rintro ⟨t, ht, hn⟩
      refine ⟨t, ht, ?_⟩
      rw [hn, fixedSubmodule_eq_fixSub]
  unfold moduleM mGV
  rw [hset]

theorem oddPrimeClassTwoAction_of_F05 {p : ℕ} {P T B : Subgroup G} {e : ℕ} (h : Hyp51 p P T B e)
    (hP : P ≠ ⊥) : Section5.OddPrimeClassTwoAction G p P T B e where
  setting :=
    { prime := h.prime
      odd := h.prime.odd_of_ne_two h.odd
      pGroup := h.pGroup
      exponent := exponent_eq_of_pow_eq_one h.prime h.exponent hP
      class_le_two := h.classTwo
      twoGroup := h.twoGroup
      abelian := h.abelian
      oddOrder := h.oddOrder
      prod_comm := h.permutes.symm
      normT := le_sup_right.trans h.acts
      normB := le_sup_left.trans h.acts }
  cyclic_centralizer := h.cyclic
  two_lt := h.eGt
  pi_eq := Set.ext fun r => ⟨fun hr => ⟨hr.1, (h.piB r hr.1).1 hr.2⟩, fun hr => ⟨hr.1, (h.piB r hr.1).2 hr.2⟩⟩
  exponent_Or := fun r hr =>
    exponent_eq_of_pow_eq_one hr.1 (h.expB r hr.1 hr.2) (pCoreOf_ne_bot_of_dvd h.abelian hr.1 hr.2)
  normalizes := h.normT

theorem faithfulBinaryIrreducibleAction_of_F05 {ρ : Representation (ZMod 2) G V} {p : ℕ} {P T B : Subgroup G}
    (h : Hyp53 ρ p P T B) : Section5.FaithfulBinaryIrreducibleAction G p P T B ρ where
  faithful := h.faithful
  irreducible := h.irreducible
  sylow := h.sylow
  comm_Z_B := fun z hz b hb => by
    have hz' : z ∈ fixSub ρ T := by
      change z ∈ fixedSubmodule ρ T at hz
      rwa [fixedSubmodule_eq_fixSub] at hz
    exact h.centralizesZ hz' b hb
  normal := h.normal
  rank_gt := h.rank
  minimal := fun Q hQ hr hle => h.minimal Q hle hQ hr

theorem mem_calQ_of_mem_scriptQ {q : ℕ} {Q : Subgroup G} (h : Q ∈ Section5.scriptQ G q) :
    Q ∈ calQ (G := G) q :=
  ⟨h.1, h.2.2.1, h.2.1, fun x hx => by
    have := Monoid.pow_exponent_eq_one (⟨x, hx⟩ : ↥Q)
    rw [h.2.2.2.1] at this
    simpa using congrArg Subtype.val this, h.2.2.2.2.1, h.2.2.2.2.2⟩

theorem cyclicCentralizersAndFewComponentConjugates_of_F05 {B : Subgroup G} (h : Hyp515 B) :
    Section5.CyclicCentralizersAndFewComponentConjugates G B where
  cyclic_centralizer := fun q hq Q hQ b hb hb1 => h.cyclic q hq Q (mem_calQ_of_mem_scriptQ hQ) b hb hb1
  few_conjugates := h.components

theorem binaryActionRankCounterexample_of_F05 {ρ : Representation (ZMod 2) G V} {p : ℕ} {P T B : Subgroup G}
    {e : ℕ} (h51 : Hyp51 p P T B e) (h53 : Hyp53 ρ p P T B) (h515 : Hyp515 B)
    (hn : ¬ (e + 1 < mGV ρ ∨
      (∃ q ∈ alphaSet G, q ∣ Nat.card B ∧ ∃ Q ∈ calQ (G := G) q, 3 < CFSG.Open.pRank q Q) ∨
      (P ⊓ centralizer (B : Set G) ≠ ⊥ ∧ 3 < CFSG.Open.pRank p P ∧ ¬ InvertedIn ⊤ B))) :
    Section5.BinaryActionRankCounterexample G p P T B e ρ where
  oddPrimeClassTwoAction :=
    oddPrimeClassTwoAction_of_F05 h51 (ne_bot_of_one_lt_pRank h51.prime h53.rank)
  faithfulBinaryIrreducibleAction := faithfulBinaryIrreducibleAction_of_F05 h53
  cyclicCentralizersAndFewComponentConjugates := cyclicCentralizersAndFewComponentConjugates_of_F05 h515
  not_concl := fun hc => hn (by
    rcases hc with h1 | ⟨q, hq, Q, hQ, hr⟩ | ⟨h3, h4, h5⟩
    · exact Or.inl (by rwa [moduleM_eq_mGV] at h1)
    · exact Or.inr (Or.inl ⟨q, hq.2, hq.1.2, Q, mem_calQ_of_mem_scriptQ hQ, hr⟩)
    · exact Or.inr (Or.inr ⟨h3, h4, fun ⟨g, _, hg⟩ => h5 ⟨g, hg⟩⟩))

theorem k516_of_section5
    (h : ∀ (G : Type) [Group G] [Finite G] (V : Type) [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
      (ρ : Representation (ZMod 2) G V) (p : ℕ) (P T B : Subgroup G) (e : ℕ),
      Section5.BinaryActionRankCounterexample G p P T B e ρ → False) : K516 := by
  intro G _ _ V _ _ _ ρ p P T B e h51 h53 h515
  by_contra hn
  exact h G V ρ p P T B e (binaryActionRankCounterexample_of_F05 h51 h53 h515 hn)

end CFSG.LocalAnalysis.UniquenessCase.UC22.F05
