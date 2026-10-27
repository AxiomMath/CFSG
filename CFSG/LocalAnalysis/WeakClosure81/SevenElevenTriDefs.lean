module

public import CFSG.LocalAnalysis.WeakClosure81.SevenElevenCls

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open Subgroup

structure TrialityMarked (X : Type) [Group X] (s : X) (ε : X →* Equiv.Perm (Fin 3)) : Prop where
  surjective : Function.Surjective ε
  isSwap : (ε s).IsSwap
  centralizer_gen : ∀ r : X, IsConj s r → Subgroup.centralizer ({r} : Set X) =
    Subgroup.closure ({x : X | IsConj s x} ∩ (Subgroup.centralizer ({r} : Set X) : Set X))
  config : ∃ a b t : X, IsConj s a ∧ IsConj s b ∧ IsConj s t ∧ ε a = ε b ∧ ε t ≠ ε a ∧
    orderOf (a * b) = 3 ∧ orderOf (t * a) = 3 ∧ orderOf (t * b) = 3 ∧
    orderOf (t * (b * a * b⁻¹)) = 3

structure TrialityData (X : Type) [Group X] (s : X) (ε : X →* Equiv.Perm (Fin 3)) : Prop where
  surjective : Function.Surjective ε
  isSwap : (ε s).IsSwap
  centralizer_ker : Subgroup.centralizer (ε.ker : Set X) = ⊥
  orth : ∃ (f : ℕ) (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = 2 ^ f ∧
    ∃ e : (↥(ε.ker ⊔ Subgroup.zpowers s) ⧸ Subgroup.center ↥(ε.ker ⊔ Subgroup.zpowers s)) ≃*
        ↥(CFSG.PGLModel.orthogonalPlus 4 F),
      haveI := Fintype.ofFinite F
      IsRankOneIn ((e (QuotientGroup.mk
        ⟨s, Subgroup.mem_sup_right (Subgroup.mem_zpowers s)⟩) : GL (Fin 4 ⊕ Fin 4) F))

@[expose] def IsTrialityOddTransp (X : Type) [Group X] (s : X) : Prop :=
  ∃ ε : X →* Equiv.Perm (Fin 3), TrialityData X s ε

@[expose] def HasTrialityMarked (X : Type) [Group X] (s : X) : Prop :=
  ∃ ε : X →* Equiv.Perm (Fin 3), TrialityMarked X s ε

@[expose] def TrialityMarkedInput : Prop :=
  ∀ (X : Type) [Group X] (s : X), IsTrialityOddTransp X s → HasTrialityMarked X s

end CFSG.LocalAnalysis.WeakClosure81
