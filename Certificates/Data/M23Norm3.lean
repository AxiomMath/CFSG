module

public import Certificates.Data.M23Heptad
public import CFSG.Quasithin.Vol2.Ch5Sec2M23L34DataInputs
public import CFSG.LocalAnalysis.ComponentClassification.WittDesignM22Count

public section

namespace CFSG.M23Norm3

open Equiv CFSG.A7Fano CFSG.QuasithinUnique.Vol2Native.L239 CFSG.QuasithinUnique.Setup.X1

@[expose] def k4a : Perm (Fin 7) := mkPerm7 ![1, 0, 3, 2, 4, 5, 6] ![1, 0, 3, 2, 4, 5, 6]

@[expose] def k4b : Perm (Fin 7) := mkPerm7 ![2, 3, 0, 1, 4, 5, 6] ![2, 3, 0, 1, 4, 5, 6]

@[expose] def k4c : Perm (Fin 7) := mkPerm7 ![3, 2, 1, 0, 4, 5, 6] ![3, 2, 1, 0, 4, 5, 6]

@[expose] def k4List : List (Perm (Fin 7)) := [1, k4a, k4b, k4c]

@[expose] def c123 : Perm (Fin 7) := mkPerm7 ![0, 2, 3, 1, 4, 5, 6] ![0, 3, 1, 2, 4, 5, 6]

@[expose] def c456 : Perm (Fin 7) := mkPerm7 ![0, 1, 2, 3, 5, 6, 4] ![0, 1, 2, 3, 6, 4, 5]

@[expose] def c33 : Perm (Fin 7) := c123 * c456

@[expose] def e9List : List (Perm (Fin 7)) :=
  [1, c456, c456 ^ 2, c123, c123 * c456, c123 * c456 ^ 2, c123 ^ 2, c123 ^ 2 * c456,
    c123 ^ 2 * c456 ^ 2]

@[expose] def s1245 : Perm (Fin 7) := mkPerm7 ![0, 2, 1, 3, 5, 4, 6] ![0, 2, 1, 3, 5, 4, 6]

@[expose] def yBar : ↥CFSG.Blueprint.NativeSporadic.M23 :=
  evalN CFSG.Blueprint.NativeSporadic.M23 M23Insp.ks [1, 4, 1, 3, 4, 2, -1, 2, 1]

@[expose] def y1Bar : ↥CFSG.Blueprint.NativeSporadic.M23 :=
  evalN CFSG.Blueprint.NativeSporadic.M23 M23Insp.ks [1, 3, -1, 3, 1, 4]

@[expose] def uBar : ↥CFSG.Blueprint.NativeSporadic.M23 := M23Insp.es.getD 6 1

@[expose] def rBar : ↥CFSG.Blueprint.NativeSporadic.M23 :=
  evalN CFSG.Blueprint.NativeSporadic.M23 M23Insp.ks [4, 2, 3, 1, 2, -1, 3]

open CFSG.Quasithin.H13 CFSG.Quasithin.Asc94 in
@[expose] def borelP (σ : Fin 22 → Fin 22) : Prop :=
  σ 0 = 0 ∧ σ 1 = 1 ∧ ∀ p ∈ m22HexadL, σ p ∈ m22HexadL

open CFSG.Quasithin.H13 in
@[expose] def ker1P (σ : Fin 22 → Fin 22) : Prop := ∀ h ∈ m22Hex01L, ∀ p ∈ h, σ p ∈ h

open CFSG.Quasithin.Asc94 in
@[expose] def ker2P (σ : Fin 22 → Fin 22) : Prop := ∀ p ∈ m22HexadL, σ p = p

@[expose] def invP (σ : Fin 22 → Fin 22) : Prop := ∀ p, σ (σ p) = p

@[expose] def commP (x σ : Fin 22 → Fin 22) : Prop := ∀ p, x (σ p) = σ (x p)

instance : DecidablePred borelP := fun σ => by unfold borelP; infer_instance

instance : DecidablePred ker1P := fun σ => by unfold ker1P; infer_instance

instance : DecidablePred ker2P := fun σ => by unfold ker2P; infer_instance

instance : DecidablePred invP := fun σ => by unfold invP; infer_instance

instance (x : Fin 22 → Fin 22) : DecidablePred (commP x) := fun σ => by
  unfold commP; infer_instance

open CFSG.ComponentClassification.WittDesign in
@[expose] def borelInvCentCount (x : Fin 22 → Fin 22) : ℕ :=
  m22Count (fun y => borelP y ∧ invP y ∧ commP x y)

@[expose] def badBorel (x : Fin 22 → Fin 22) : Bool :=
  if borelP x ∧ invP x ∧ ¬ ker1P x ∧ ¬ ker2P x then decide (16 ≤ borelInvCentCount x) else false

end CFSG.M23Norm3
