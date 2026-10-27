module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveWeylBLevi
public import CFSG.LocalAnalysis.StandardType.GGTableBSymplecticLift
public import CFSG.LocalAnalysis.ComponentInitial.SymplecticTorusWeylMatrices

public section

namespace CFSG.StandardType.SpJoin

open CFSG.Open CFSG.LocalAnalysis.ComponentInitial.SymplecticTorusWeyl Matrix

variable {F : Type} [Field F] {p : ℕ}

@[expose] noncomputable def spPlaneTorus (n : ℕ) (ζ : Multiplicative (ZMod p) →* SpecialLinearGroup (Fin 2) F) :
    (Fin n → Multiplicative (ZMod p)) →* StatedSp n F :=
  MonoidHom.noncommPiCoprod (fun i => (lam i).comp ζ) fun _ _ hij _ _ => commute_lam_lam hij _ _

theorem spPlaneTorus_mulSingle {n : ℕ} (ζ : Multiplicative (ZMod p) →* SpecialLinearGroup (Fin 2) F)
    (i : Fin n) (a : Multiplicative (ZMod p)) :
    spPlaneTorus n ζ (Pi.mulSingle i a) = lam i (ζ a) := by
  exact MonoidHom.noncommPiCoprod_mulSingle (fun i => (lam i).comp ζ) i a

@[expose] def spRefl (n p : ℕ) (k : Fin n) (f : Fin n → Multiplicative (ZMod p)) :
    Fin n → Multiplicative (ZMod p) :=
  if h : k.val + 1 < n then fun i => f (Equiv.swap k ⟨k.val + 1, h⟩ i)
  else Function.update f k (f k)⁻¹

@[expose] def spCompanion (t : F) : SpecialLinearGroup (Fin 2) F :=
  ⟨!![0, -1; 1, -t], by simp [det_fin_two_of]⟩

theorem coe_spCompanion (t : F) :
    ((spCompanion t : SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) =
      !![0, -1; 1, -t] := rfl

@[expose] noncomputable def spPlaneZetaSplit (ω : Fˣ) (hω : ω ^ p = 1) :
    Multiplicative (ZMod p) →* SpecialLinearGroup (Fin 2) F :=
  sl2Diag.comp (CFSG.StandardType.TableBSymp.zmodPowHom hω)

@[expose] noncomputable def spPlaneZetaCompanion (t : F) (ht : spCompanion t ^ p = 1) :
    Multiplicative (ZMod p) →* SpecialLinearGroup (Fin 2) F :=
  CFSG.StandardType.TableBSymp.zmodPowHom ht

@[expose] def SpPlaneConj (F : Type) [Field F] (p : ℕ)
    (ζ : Multiplicative (ZMod p) →* SpecialLinearGroup (Fin 2) F) : Prop :=
  ∀ (n : ℕ) (E : Subgroup (StatedSp n F)), IsElemAbelian p E → p ^ n ≤ Nat.card E →
    ∃ c : StatedSp n F, E.map (MulAut.conj c).toMonoidHom = (spPlaneTorus n ζ).range

end CFSG.StandardType.SpJoin
