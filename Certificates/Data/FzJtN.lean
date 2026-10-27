module

public import Certificates.Data.FzFusN

public section

namespace Certificates.FzJt

open Certificates.FzJ36 Certificates.FzFus

@[expose] def zList (_ : Unit := ()) : List Model :=
  [z1M, z2M, z3M] ++ (allQ ()).map fun p => mkY p p⁻¹ 1

@[expose] def InZ (m : Model) : Prop := ∃ z ∈ zList (), KEq m z

instance inZDecidable (m : Model) : Decidable (InZ m) := by
  unfold InZ
  infer_instance

@[expose] def inZb (zs : List Model) (m : Model) : Bool := zs.any (kb m)

theorem inZb_iff {m : Model} : inZb (zList ()) m = true ↔ InZ m := by
  simp only [inZb, InZ, List.any_eq_true, kb_iff]

theorem inZb_eq_false {m : Model} : inZb (zList ()) m = false ↔ ¬ InZ m := by
  rw [← inZb_iff, Bool.not_eq_true]

theorem lamConj_mem (g : Model) : g * lamM * g⁻¹ ∈ zList () := by
  revert g
  decide +kernel

theorem mkY_eq_conj (p : Q8) : mkY p p⁻¹ 1 = mkE p 1 1 * lamM * (mkE p 1 1)⁻¹ := by
  revert p
  decide +kernel

theorem zList_invol : ∀ z ∈ zList (), IsInvM z := by
  decide +kernel

theorem z2M_keq_prod : KEq z2M (z1M * z3M) := by
  decide +kernel

theorem z1M_z3M_comm : z1M * z3M = z3M * z1M := by
  decide +kernel

theorem clsOf_of_not_inZ (m : Model) (hm : IsInvM m) (h : ¬ InZ m) :
    clsOf m ∈ rzList ++ [Cls.oI, Cls.oJ, Cls.oK] := by
  revert m
  decide +kernel

end Certificates.FzJt
