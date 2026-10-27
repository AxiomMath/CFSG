module

public import CFSG.Monster.B.TwoA.Base.Subspaces
public import CFSG.Quasithin.Vol2.Ch12Sec9Lemma4DIFacts

public section

namespace CFSG.Quasithin.H13.C1294

open Module MulAction

section Action

variable {I : Type} [AddCommGroup I] [Module (ZMod 2) I]

theorem map_eq_iff_mem_stabS (S : Submodule (ZMod 2) I) (g : I ≃ₗ[ZMod 2] I) :
    S.map (g : I →ₗ[ZMod 2] I) = S ↔ g ∈ stabS S := by
  show S.map (g : I →ₗ[ZMod 2] I) = S ↔ ∀ v, v ∈ S ↔ g v ∈ S
  constructor
  · intro h v
    constructor
    · intro hv
      rw [← h]
      exact ⟨v, hv, rfl⟩
    · intro hv
      rw [← h] at hv
      obtain ⟨w, hw, hwv⟩ := hv
      have : w = v := g.injective hwv
      rw [← this]
      exact hw
  · intro h
    apply le_antisymm
    · rintro _ ⟨x, hx, rfl⟩
      exact (h x).1 hx
    · intro y hy
      exact ⟨g.symm y, (h (g.symm y)).2 (by simpa using hy), by simp⟩

instance instMulActionSubspaceDim (j : ℕ) :
    MulAction (I ≃ₗ[ZMod 2] I) (CFSG.Monster.B.TwoA.SubspaceDim (ZMod 2) I j) where
  smul g T := ⟨T.1.map (g : I →ₗ[ZMod 2] I), by rw [LinearEquiv.finrank_map_eq]; exact T.2⟩
  one_smul T := Subtype.ext (Submodule.map_id _)
  mul_smul g h T := Subtype.ext (by
    show T.1.map ((g * h : I ≃ₗ[ZMod 2] I) : I →ₗ[ZMod 2] I) =
      (T.1.map (h : I →ₗ[ZMod 2] I)).map (g : I →ₗ[ZMod 2] I)
    rw [← Submodule.map_comp]
    rfl)

instance isPretransitive_subspaceDim [FiniteDimensional (ZMod 2) I] (j : ℕ) :
    IsPretransitive (I ≃ₗ[ZMod 2] I) (CFSG.Monster.B.TwoA.SubspaceDim (ZMod 2) I j) := by
  constructor
  rintro ⟨S, hS⟩ ⟨T, hT⟩
  obtain ⟨g, hg⟩ := CFSG.Monster.B.TwoA.exists_linearEquiv_map_eq (hS.trans hT.symm)
  exact ⟨g, Subtype.ext hg⟩

theorem stabilizer_subspaceDim_eq (S : Submodule (ZMod 2) I) :
    stabilizer (I ≃ₗ[ZMod 2] I)
        (⟨S, rfl⟩ : CFSG.Monster.B.TwoA.SubspaceDim (ZMod 2) I (finrank (ZMod 2) S)) =
      stabS S := by
  ext g
  rw [MulAction.mem_stabilizer_iff, ← map_eq_iff_mem_stabS]
  constructor
  · intro h
    have := congrArg Subtype.val h
    exact this
  · intro h
    exact Subtype.ext h

theorem index_stabS_eq_card [FiniteDimensional (ZMod 2) I] (S : Submodule (ZMod 2) I) :
    (stabS S).index =
      Nat.card (CFSG.Monster.B.TwoA.SubspaceDim (ZMod 2) I (finrank (ZMod 2) S)) := by
  rw [← stabilizer_subspaceDim_eq S, MulAction.index_stabilizer_of_transitive]

end Action

section Counts

variable {I : Type} [AddCommGroup I] [Module (ZMod 2) I] [FiniteDimensional (ZMod 2) I]

theorem card_subspaceDim_four {j : ℕ} (hI : finrank (ZMod 2) I = 4) (hj : j ≤ 4) :
    Nat.card (CFSG.Monster.B.TwoA.SubspaceDim (ZMod 2) I j) =
      CFSG.Monster.B.TwoA.qBinom 2 4 j := by
  haveI : Finite I := Module.finite_of_finite (ZMod 2)
  have h := CFSG.Monster.B.TwoA.card_subspaces (K := ZMod 2) (V := I) (j := j) (by omega)
  rw [hI] at h
  rw [h]
  rfl

theorem index_stabS_one {S : Submodule (ZMod 2) I} (hS : finrank (ZMod 2) S = 1)
    (hI : finrank (ZMod 2) I = 4) : (stabS S).index = 15 := by
  rw [index_stabS_eq_card, hS, card_subspaceDim_four hI (by norm_num)]
  rfl

theorem index_stabS_two {S : Submodule (ZMod 2) I} (hS : finrank (ZMod 2) S = 2)
    (hI : finrank (ZMod 2) I = 4) : (stabS S).index = 35 := by
  rw [index_stabS_eq_card, hS, card_subspaceDim_four hI (by norm_num)]
  rfl

theorem index_stabS_three {S : Submodule (ZMod 2) I} (hS : finrank (ZMod 2) S = 3)
    (hI : finrank (ZMod 2) I = 4) : (stabS S).index = 15 := by
  rw [index_stabS_eq_card, hS, card_subspaceDim_four hI (by norm_num)]
  rfl

end Counts

end CFSG.Quasithin.H13.C1294
