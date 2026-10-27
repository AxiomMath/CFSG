module

public import CFSG.Quasithin.EmptyFaithful.Setting
import CFSG.Milestones.OO_odd_order_solvable
public import CFSG.LieType.BorelTits.Basic

public section

namespace CFSG.Quasithin.EmptyFaithfulMultiple

open CFSG.Open

structure MultipleCentralizerHypothesis (G : Type) [Group G] [Finite G] (T : Subgroup G) :
    Prop where
  simple : IsSimpleGroup G
  nonabelian : ∃ a b : G, a * b ≠ b * a
  qtke : CFSG.QuasithinUnique.quasithinIsQTKECat G
  sylow : quasithinIsSylowTwo T
  faithful_empty : ∀ L : Subgroup G, ¬ quasithinIsFaithfulLocal T L
  two_centralizer_maximal : ∃ M₁ M₂ : Subgroup G, M₁ ≠ M₂ ∧
    quasithinIsMaxTwoLocal M₁ ∧ quasithinIsMaxTwoLocal M₂ ∧
    Subgroup.centralizer (quasithinOmegaOneCenter T : Set G) ≤ M₁ ∧
    Subgroup.centralizer (quasithinOmegaOneCenter T : Set G) ≤ M₂

@[expose] def MultipleCentralizerRecognitionStatement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T : Subgroup G), MultipleCentralizerHypothesis G T →
    Nonempty (G ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 3) (ZMod 2)) ∨
      Nonempty (G ≃* alternatingGroup (Fin 6))

@[expose] def SixModelsNative (G : Type) [Group G] : Prop :=
  Nonempty (G ≃* CFSG.Blueprint.NativeSporadic.J2) ∨
    Nonempty (G ≃* CFSG.Blueprint.NativeSporadic.J3) ∨
    CFSG.Blueprint.LieModel G .trialityD4 0 2 1 ∨
    CFSG.Blueprint.LieModel G .Tits 0 2 1 ∨
    (∃ (k : Type) (_ : Field k) (_ : Finite k), Nat.card k = 2 ∧
      Nonempty (G ≃* ↥⁅CFSG.Blueprint.Chevalley.adjointGroup .G2 k,
        CFSG.Blueprint.Chevalley.adjointGroup .G2 k⁆)) ∨
    Nonempty (G ≃* CFSG.Blueprint.NativeSporadic.M12)

@[expose] def UniqueCentralizerRecognitionStatement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T Mc : Subgroup G),
    CFSG.Quasithin.quasithinQTFE14Cat G T Mc → SixModelsNative G

theorem isSQTKCat_of_hyp {G : Type} [Group G] [Finite G] {T : Subgroup G}
    (hyp : MultipleCentralizerHypothesis G T) {H : Subgroup G} (hH : pCoreOf 2 H ≠ ⊥) :
    CFSG.SectionRank.IsSQTKCat ↥H :=
  haveI := hyp.simple
  (CFSG.QuasithinUnique.qtkeCore_of_cat hyp.nonabelian hyp.qtke).1 H hH

theorem pRank_le_two_of_isTwoLocal_cat {G : Type} [Group G] [Finite G]
    (hK : CFSG.QuasithinUnique.quasithinIsQTKECat G) {H : Subgroup G}
    (hH : IsTwoLocal H) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) : CFSG.Open.pRank p H ≤ 2 := by
  have hbdd : BddAbove {k | ∃ (p : ℕ) (H : Subgroup G), p.Prime ∧ p ≠ 2 ∧ IsTwoLocal H ∧
      CFSG.Open.pRank p H = k} := by
    refine ⟨Nat.card G, ?_⟩
    rintro k ⟨q, K, hq, -, -, rfl⟩
    obtain ⟨E, -, -, hE⟩ := CFSG.SectionRank.exists_pRank hq.one_lt K
    have h1 : CFSG.Open.pRank q K < q ^ CFSG.Open.pRank q K := Nat.lt_pow_self hq.one_lt
    have h2 : Nat.card E ≤ Nat.card G := Subgroup.card_le_card_group E
    omega
  have h : CFSG.Open.evenRank G ≤ 2 := hK.2.2
  unfold CFSG.Open.evenRank at h
  exact (le_csSup hbdd ⟨p, H, hp, hp2, hH, rfl⟩).trans h

theorem pRank_le_two_of_pCoreOf_ne_bot_cat {G : Type} [Group G] [Finite G]
    (hK : CFSG.QuasithinUnique.quasithinIsQTKECat G) {H : Subgroup G}
    (hH : pCoreOf 2 H ≠ ⊥) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) : CFSG.Open.pRank p H ≤ 2 := by
  have hloc : IsTwoLocal (Subgroup.normalizer (pCoreOf 2 H : Set G)) :=
    ⟨pCoreOf 2 H, hH, CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 H, rfl⟩
  exact (CFSG.SectionRank.pRank_mono hp.one_lt
    (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 H)).trans
      (pRank_le_two_of_isTwoLocal_cat hK hloc hp hp2)

theorem exists_maxTwoLocal_ge {G : Type} [Group G] [Finite G] {H : Subgroup G}
    (hH : IsTwoLocal H) :
    ∃ M : Subgroup G, quasithinIsMaxTwoLocal M ∧ H ≤ M := by
  classical
  let s : Set (Subgroup G) := {K | IsTwoLocal K ∧ H ≤ K}
  have hfin : s.Finite := Set.toFinite s
  obtain ⟨M, ⟨hM2, hHM⟩, hmax⟩ := hfin.exists_maximal ⟨H, hH, le_rfl⟩
  refine ⟨M, ⟨hM2, fun K hK hMK => ?_⟩, hHM⟩
  exact (hmax ⟨hK, hHM.trans hMK⟩ hMK).antisymm hMK

theorem sylow_ne_bot {G : Type} [Group G] [Finite G] [IsSimpleGroup G]
    (hnonab : ∃ a b : G, a * b ≠ b * a) (T : Sylow 2 G) : (T : Subgroup G) ≠ ⊥ := by
  intro hT
  have hodd : Odd (Nat.card G) := by
    have hidx := T.not_dvd_index
    rw [hT, Subgroup.index_bot] at hidx
    exact Nat.odd_iff.mpr (Nat.two_dvd_ne_zero.mp hidx)
  have hsolv := CFSG.Milestones.odd_order_solvable hodd
  obtain ⟨a, b, hab⟩ := hnonab
  have hcomm : ∀ x y : G, x * y = y * x := by
    have hab' := IsSimpleGroup.comm_iff_isSolvable.mpr hsolv
    exact fun x y => hab' x y
  exact hab (hcomm a b)

theorem isTwoLocal_normalizer_omegaOneCenter {G : Type} [Group G] [Finite G] {T : Subgroup G}
    (hT : IsPGroup 2 T) (hne : T ≠ ⊥) :
    IsTwoLocal (Subgroup.normalizer (quasithinOmegaOneCenter T : Set G)) := by
  refine ⟨quasithinOmegaOneCenter T, CFSG.Quasithin.quasithinOmegaOneCenter_ne_bot hT hne, ?_,
    rfl⟩
  exact hT.to_le ((Subgroup.closure_le _).mpr fun z hz => hz.1.1)

end CFSG.Quasithin.EmptyFaithfulMultiple
