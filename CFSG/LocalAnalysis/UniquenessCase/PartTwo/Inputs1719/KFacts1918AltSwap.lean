module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.KFacts1918Perm
import CFSG.HardMathSupport.Cooperstein.AlternatingGeometry.ExtensionPCore
import CFSG.HardMathSupport.RichardWeiss.Proving.PLType.SymCent

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719

open Subgroup CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase.PartTwo

theorem kFacts1918_of_alt_swap {X : Type} [Group X] [Finite X] (Y : Subgroup X) {n : ℕ}
    (hn : 7 ≤ n) (e : X ≃* alternatingGroup (Fin n)) {a b : Fin n} (hab : a ≠ b)
    (hY : Y.map e.toMonoidHom =
      (Subgroup.centralizer ({Equiv.swap a b} : Set (Equiv.Perm (Fin n)))).comap
        (alternatingGroup (Fin n)).subtype) :
    (∀ Nn : Subgroup X, Nn ≤ Opp 2 Y → (Nn.subgroupOf (Opp 2 Y)).Normal →
      ¬ Nn ≤ pCoreOf 2 (Opp 2 Y) → S17.oUpperTwo (Opp 2 Y) ≤ Nn ⊔ pCoreOf 2 (Opp 2 Y)) ∧
    Nat.card (Bar2 (S17.oUpperTwo (Opp 2 Y))) = (n - 2).factorial / 2 := by
  let C : Subgroup (Equiv.Perm (Fin n)) :=
    Subgroup.centralizer ({Equiv.swap a b} : Set (Equiv.Perm (Fin n)))
  let A : Subgroup (Equiv.Perm (Fin n)) := alternatingGroup (Fin n)
  have hmap : (C.comap A.subtype).map A.subtype = C ⊓ A := by
    rw [Subgroup.comap_subtype C A, Subgroup.subgroupOf_map_subtype C A]
  let e1 : ↥Y ≃* ↥(Y.map e.toMonoidHom) :=
    Subgroup.equivMapOfInjective Y e.toMonoidHom e.injective
  let e2 : ↥(Y.map e.toMonoidHom) ≃* ↥(C.comap A.subtype) := MulEquiv.subgroupCongr hY
  let e3 : ↥(C.comap A.subtype) ≃* ↥(C ⊓ A) :=
    (Subgroup.equivMapOfInjective (C.comap A.subtype) A.subtype A.subtype_injective).trans
      (MulEquiv.subgroupCongr hmap)
  let e4 : ↥(C ⊓ A) ≃* Equiv.Perm (Fin (n - 2)) :=
    (CFSG.HardMathSupport.RichardWeiss.Proving.PLType.altCentSwapEquiv (m := n) hab).symm
  let φ : ↥Y ≃* Equiv.Perm (Fin (n - 2)) := ((e1.trans e2).trans e3).trans e4
  have hcore : CFSG.pCore 2 ↥Y = ⊥ := by
    have h := CFSG.pCore_map_iso 2 φ.symm
    rw [CFSG.HardMathSupport.Cooperstein.AlternatingGeometry.pCore_perm_eq_bot
          (Or.inr (Or.inr (by omega)))] at h
    simpa using h.symm
  exact kFacts1918_of_perm Y (k := n - 2) (Or.inr (by omega)) φ.toMonoidHom
    (by intro x; exact ⟨φ.symm x, φ.apply_symm_apply x⟩)
    (by rw [hcore, MonoidHom.ker_eq_bot_iff]; exact φ.injective)

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719
