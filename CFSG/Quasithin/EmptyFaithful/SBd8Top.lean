module

public import CFSG.Quasithin.EmptyFaithful.SBd8Perm8
public import CFSG.Quasithin.EmptyFaithful.SBd8Psl2
public import CFSG.Quasithin.EmptyFaithful.SBd8Rk2SL
public import CFSG.Quasithin.EmptyFaithful.SBd8Rk2Sp
public import CFSG.Quasithin.EmptyFaithful.SBd8G2B
public import CFSG.Quasithin.EmptyFaithful.R3c2Types
public import CFSG.Quasithin.EmptyFaithful.SBd8SmallA6
public import CFSG.Quasithin.EmptyFaithful.SBd8SmallL32
public import CFSG.Quasithin.EmptyFaithful.SBd8SmallU33

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits

namespace SBd8

variable {X : Type} [Group X] [Finite X] {A : Subgroup (MulAut X)} {U K : Subgroup X}

@[expose] def FamL4 : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (A : Subgroup (MulAut X)) (U K : Subgroup X),
    OvgData X A U K → Nonempty (X ≃* ↥(CFSG.Assembly.LowTwoRank.StatedSL 4 (ZMod 2))) →
      IsAlt 8 X ∧ IsMinParabolicOf (⊤ : Subgroup X) K ∧ ∃ α ∈ A, ∀ x : X, α ≠ MulAut.conj x

@[expose] def FamL5 : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (A : Subgroup (MulAut X)) (U K : Subgroup X),
    OvgData X A U K → Nonempty (X ≃* ↥(CFSG.Assembly.LowTwoRank.StatedSL 5 (ZMod 2))) → False

theorem one_le_of_card_two_pow' {F : Type} [Field F] [Finite F] {n : ℕ} (hF : Nat.card F = 2 ^ n) : 1 ≤ n := by
  by_contra h
  have h0 : n = 0 := by omega
  have := Finite.one_lt_card (α := F)
  rw [hF, h0] at this
  norm_num at this

theorem model_concl (hG2 : FactG2Cayley) (hL4 : FamL4) (hL5 : FamL5) (d : OvgData X A U K)
    (hl : B56QuasisimpleList X) (h7 : ¬ IsAlt 7 X)
    (hn3 : ¬ ∃ n : ℕ, Even n ∧ IsSL3 (2 ^ n) X) (hh : ¬ IsHat X ↥(alternatingGroup (Fin 6))) :
    ModelConcl X A U K := by
  have hU := d.U_syl
  rcases hl with ⟨n, F, hF, hFin, hcard, ⟨e⟩⟩ | ⟨n, F, hF, hFin, hcard, ⟨e⟩⟩ |
      ⟨n, F, hF, hFin, hcard, ⟨e⟩⟩ | ⟨n, F, hF, hFin, hcard, ⟨e⟩⟩ | hA6 | hA7 | hhat |
      ⟨F, hF, hFin, hcard, ⟨e⟩⟩ | hSL4 | hSL5
  ·
    exact Or.inl (famSL2 d hcard e)
  ·
    have hn1 := one_le_of_card_two_pow' hcard
    rcases Nat.lt_or_ge n 2 with hlt | hge
    · have hn1' : n = 1 := by omega
      subst hn1'
      have hF2 : Nat.card F = 2 := by simpa using hcard
      have h3 := trioShape_L32 hF2 e hU
      right; left
      refine ⟨Or.inl ?_, trioConcl_of_shape d h3⟩
      exact R3c2.isPSL_two_of_statedSL (n := 3) (by norm_num) (e.trans (Insp9.statedSLEquivZMod2 F hF2 3))
    · rcases Nat.even_or_odd n with hev | hodd
      · exact absurd ⟨n, hev, F, hF, hFin, hcard, ⟨e⟩⟩ hn3
      · exact (famSL3 d hcard hodd (by
          rcases hodd with ⟨k, rfl⟩
          omega) e).elim
  ·
    have hn1 := one_le_of_card_two_pow' hcard
    rcases Nat.lt_or_ge n 2 with hlt | hge
    · have hn1' : n = 1 := by omega
      subst hn1'
      have hF2 : Nat.card F = 2 := by simpa using hcard
      exact (R3c2.not_isQuasisimple_statedSp_two hF2 e d.quasi).elim
    · exact (famSp4 d hcard hge e).elim
  ·
    have hn1 := one_le_of_card_two_pow' hcard
    rcases Nat.lt_or_ge n 2 with hlt | hge
    · have hn1' : n = 1 := by omega
      subst hn1'
      have hF2 : Nat.card F = 2 := by simpa using hcard
      exact (R3c2.not_isQuasisimple_quasithinG2_two hF2 e d.quasi).elim
    · exact (famG2 hG2 d hcard hge e).elim
  ·
    right; left
    exact ⟨Or.inr (Or.inl hA6), trioConcl_of_shape d (trioShape_A6 hA6 hU)⟩
  · exact absurd hA7 h7
  · exact absurd hhat hh
  ·
    right; left
    have h : ∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = 2 ∧
        Nonempty (X ≃* ↥⁅CFSG.Open.quasithinG2 F, CFSG.Open.quasithinG2 F⁆) :=
      ⟨F, hF, hFin, hcard, ⟨e⟩⟩
    exact ⟨Or.inr (Or.inr (trioIsPSU33 h)), trioConcl_of_shape d (trioShape_U33 h hU)⟩
  ·
    right; right
    exact hL4 X A U K d hSL4
  · exact (hL5 X A U K d hSL5).elim

theorem insp28Pure_of_flags (hG2 : FactG2Cayley) (hL4 : FamL4) (hL5 : FamL5) : Insp28Pure := by
  intro Γ _ _ X J S₀ K d hl h7 hn3 hh
  refine insp28Concl_of_modelConcl d (fun α hα h8 hnon => nonempty_perm8_of_alt8 d h8 hα hnon) ?_
  exact model_concl hG2 hL4 hL5 (ovgData_of_insp28Data d) hl h7 hn3 hh

theorem input28Insp_of_flags (hG2 : FactG2Cayley) (hL4 : FamL4) (hL5 : FamL5) : Input28Insp :=
  input28Insp_of_pure (insp28Pure_of_flags hG2 hL4 hL5)

end SBd8

end CFSG.Quasithin
