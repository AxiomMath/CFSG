module

public import CFSG.Quasithin.EmptyFaithfulMultiple.Statements
public import CFSG.Quasithin.Background.A4V
import CFSG.Quasithin.Background.OrderingMax
import CFSG.LocalAnalysis.QuasithinUnique.CharTwoInheritance
public import CFSG.Quasithin.EmptyFaithfulMultiple.TheoremE

public section

namespace CFSG.Quasithin.EmptyFaithfulMultiple

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique

section General

variable {G : Type*} [Group G]

private theorem le_centralizer_omegaOneCenter_self (T : Subgroup G) :
    T ≤ Subgroup.centralizer (quasithinOmegaOneCenter T : Set G) :=
  Subgroup.le_centralizer_iff.mp
    (((Subgroup.closure_le _).mpr fun _ hz => hz.1 :
      quasithinOmegaOneCenter T ≤ T ⊓ Subgroup.centralizer (T : Set G)).trans inf_le_right)

theorem ne_bot_of_isXi {T X : Subgroup G} (h : IsXi T X) : X ≠ ⊥ := by
  rintro rfl
  obtain ⟨-, -, -, p, hp, -, -, hidx, -⟩ := h
  rw [Subgroup.relIndex_bot_right] at hidx
  rcases hidx with h2 | ⟨h3, -⟩
  · exact (Nat.one_lt_pow two_ne_zero hp.one_lt).ne h2
  · exact (Nat.one_lt_pow three_ne_zero hp.one_lt).ne h3

theorem relIndex_eq_three_pow_or_five_pow_of_isXiMinus {T X : Subgroup G}
    (h : IsXiMinus T X) :
    (∃ k : ℕ, (pCoreOf 2 X).relIndex X = 3 ^ k) ∨ ∃ k : ℕ, (pCoreOf 2 X).relIndex X = 5 ^ k := by
  obtain ⟨⟨-, -, -, p, hp, hp2, -, hidx, -⟩, hcase⟩ := h
  obtain ⟨k, hk0, hk⟩ : ∃ k : ℕ, k ≠ 0 ∧ (pCoreOf 2 X).relIndex X = p ^ k := by
    rcases hidx with h2 | ⟨h3, -⟩
    · exact ⟨2, two_ne_zero, h2⟩
    · exact ⟨3, three_ne_zero, h3⟩
  have hpd : p ∣ (pCoreOf 2 X).relIndex X := hk ▸ dvd_pow_self p hk0
  rcases hcase with ha | ⟨hb, -⟩
  · have hp3 : p = 3 :=
      (ha p hp (hpd.trans (Subgroup.relIndex_dvd_card _ _))).resolve_left hp2
    exact Or.inl ⟨k, hp3 ▸ hk⟩
  · exact Or.inr ⟨k, hb p hp hpd ▸ hk⟩

end General

section Finite

variable {G : Type*} [Group G] [Finite G]

theorem quasithinOmegaOneCenter_le_omegaOneCenterOf (T : Sylow 2 G) {H : Subgroup G}
    (hTH : (T : Subgroup G) ≤ H) (hH : CharTwo H) :
    quasithinOmegaOneCenter (T : Subgroup G) ≤ omegaOneCenterOf (pCoreOf 2 H) := by
  refine (Subgroup.closure_le _).mpr fun z hz => Subgroup.subset_closure ⟨?_, hz.2⟩
  have hzC : z ∈ Subgroup.centralizer (pCoreOf 2 H : Set G) :=
    Subgroup.centralizer_le (pCoreOf_two_le_sylow H T hTH) hz.1.2
  exact ⟨hH ⟨hTH hz.1.1, hzC⟩, hzC⟩

theorem isXClass_of_inH (hEven : quasithinEvenCharacteristic G) (T : Sylow 2 G)
    {X : Subgroup G} (hne : X ≠ ⊥) (hX : X = oTwoUpper X)
    (hTX : (T : Subgroup G) ≤ Subgroup.normalizer (X : Set G))
    (hH : InH (T : Subgroup G) (X ⊔ (T : Subgroup G))) : IsXClass X :=
  ⟨hne, hX, (charTwo_of_inH hEven T hH).of_normal le_sup_left
    (Subgroup.normal_subgroupOf_of_le_normalizer (sup_le Subgroup.le_normalizer hTX))⟩

theorem isXf_of_inH (hEven : quasithinEvenCharacteristic G) (T : Sylow 2 G) {X : Subgroup G}
    (hXc : IsXClass X) (hTX : (T : Subgroup G) ≤ Subgroup.normalizer (X : Set G))
    (hH : InH (T : Subgroup G) (X ⊔ (T : Subgroup G)))
    (hZX : ⁅quasithinOmegaOneCenter (T : Subgroup G), X⁆ ≠ ⊥) : IsXf X := by
  have hn : (X.subgroupOf (X ⊔ (T : Subgroup G))).Normal :=
    Subgroup.normal_subgroupOf_of_le_normalizer (sup_le Subgroup.le_normalizer hTX)
  have hZ := quasithinOmegaOneCenter_le_omegaOneCenterOf T le_sup_right
    (charTwo_of_inH hEven T hH)
  refine ⟨hXc, (a4_9 hXc (A4.subnormal_of_normal le_sup_left hn)).mp fun h => hZX ?_⟩
  exact le_bot_iff.mp (h ▸ Subgroup.commutator_mono hZ le_rfl)

end Finite

theorem stmt1542Three_of_xiMinus {G : Type} [Group G] [Finite G]
    {T : Subgroup G} (hyp : MultipleCentralizerHypothesis G T) (h1 : Stmt1542One G T)
    (h137loc : ∀ X : Subgroup G, IsXi T X →
      IsUniqueM (X ⊔ T) (Subgroup.normalizer (X : Set G)))
    (h3213loc : ∀ X : Subgroup G, IsXiStarF T X → IsXiMinus T X) :
    Stmt1542Three G T := by
  intro X hX
  obtain ⟨S, rfl⟩ := exists_sylow_of_quasithinIsSylowTwo hyp.sylow
  have hXs : IsXiStar (S : Subgroup G) X := ⟨hX, fun L hL _ => (h1 L hL).elim⟩
  have hU := h137loc X hX
  have hZX : ⁅quasithinOmegaOneCenter (S : Subgroup G), X⁆ ≠ ⊥ := by
    intro h
    have hXT : X ⊔ (S : Subgroup G) ≤
        Subgroup.centralizer (quasithinOmegaOneCenter (S : Subgroup G) : Set G) :=
      sup_le (Subgroup.le_centralizer_iff.mp (Subgroup.commutator_eq_bot_iff_le_centralizer.mp h))
        (le_centralizer_omegaOneCenter_self _)
    obtain ⟨M₁, M₂, hne, hM₁, hM₂, hCM₁, hCM₂⟩ := hyp.two_centralizer_maximal
    exact hne ((hU.2 M₁ ⟨hM₁, hXT.trans hCM₁⟩).trans (hU.2 M₂ ⟨hM₂, hXT.trans hCM₂⟩).symm)
  have hH : InH (S : Subgroup G) (X ⊔ (S : Subgroup G)) := ⟨le_sup_right, hX.2.2.1⟩
  have hXf : IsXiStarF (S : Subgroup G) X := ⟨hXs, isXf_of_inH hyp.qtke.2.1 S
    (isXClass_of_inH hyp.qtke.2.1 S (ne_bot_of_isXi hX) hX.1 hX.2.1 hH) hX.2.1 hH hZX⟩
  have hXm := h3213loc X hXf
  exact ⟨hZX, hXf, fun hp => hp.2 hXm, relIndex_eq_three_pow_or_five_pow_of_isXiMinus hXm⟩

end CFSG.Quasithin.EmptyFaithfulMultiple
