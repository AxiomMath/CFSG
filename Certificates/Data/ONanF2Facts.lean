module

public import Certificates.Data.ONanF2Tools

public section

namespace CFSG.OddStandard.ONanRec.F2

open AlpE

@[expose] def allInvs : List AlpE := allE.filter fun u => u * u = 1 ∧ u ≠ 1

@[expose] def classLists : List (List AlpE) := invEL.map fun r => orbitC genE r

@[expose] def factCentre : Prop :=
  (∀ i : Fin 5, gen i * zc = zc * gen i) ∧
    ∀ x : AlpE, (∀ i : Fin 5, gen i * x = x * gen i) → x = 1 ∨ x = zc

@[expose] def factClasses : Prop :=
  (∀ i, invE i * invE i = 1 ∧ invE i ≠ 1) ∧
  (∀ u ∈ allInvs, ∃ i : Fin 7, u ∈ classLists.getD i []) ∧
  (∀ i : Fin 7, ClassOK genE (invE i) (classLists.getD i []) (![1, 2, 4, 16, 32, 16, 16] i)) ∧
  (∀ i j : Fin 7, i ≠ j → ∀ u ∈ classLists.getD i [], u ∉ classLists.getD j []) ∧
  (Finset.univ.filter fun u : AlpE => u * u = 1 ∧ u ≠ 1).card = 87 ∧
  (∀ i : Fin 7, (Finset.univ.filter fun g : AlpE =>
    g * invEL.getD i 1 = invEL.getD i 1 * g).card = ![512, 256, 128, 32, 16, 32, 32] i)

@[expose] def factNonV : Prop :=
  ∀ x : AlpE, x.d ≠ 0 → (Finset.univ.filter fun g : AlpE => g * x = x * g).card ≤ 32


@[expose] def ballV0 : List AlpE := ballFix genV0E
@[expose] def ballPd : List AlpE := ballFix genPdE
@[expose] def ballComm : List AlpE := ballFix genCommE
@[expose] def genVE : List AlpE := [AlpE.gen 0, AlpE.gen 1, AlpE.gen 2]
@[expose] def genWE : List AlpE := [AlpE.gen 0 ^ 2, AlpE.gen 1 ^ 2, AlpE.gen 2 ^ 2]
@[expose] def genVtE : List AlpE := [AlpE.gen 0, AlpE.gen 1, AlpE.gen 2, AlpE.gen 4]
@[expose] def genRE : List AlpE := [AlpE.gen 3]
@[expose] def ballV : List AlpE := ballFix genVE
@[expose] def ballW : List AlpE := ballFix genWE
@[expose] def ballVt : List AlpE := ballFix genVtE
@[expose] def ballQ : List AlpE := ballFix genQE
@[expose] def ballR : List AlpE := ballFix genRE
@[expose] def ballMaxL : List (List AlpE) := (List.finRange 7).map fun i => ballFix (genMaxE i)
@[expose] def ballCentL : List (List AlpE) := (List.finRange 3).map fun i => ballFix (genCentE i)

@[expose] def factSub : Prop :=
  SubOK genV0E ballV0 32 ∧ SubOK genPdE ballPd 64 ∧ SubOK genCommE ballComm 64 ∧
  SubOK genVE ballV 64 ∧ SubOK genWE ballW 8 ∧ SubOK genVtE ballVt 128 ∧
  SubOK genQE ballQ 32 ∧ SubOK genRE ballR 16 ∧
  (∀ i : Fin 7, SubOK (genMaxE i) (ballMaxL.getD i []) 256) ∧
  (∀ i : Fin 3, SubOK (genCentE i) (ballCentL.getD i []) 32)

@[expose] def maxTable : Fin 7 → Fin 7 → Bool :=
  ![![true, true, true, true, false, false, false], ![true, true, true, true, false, true, true],
    ![true, true, true, true, true, false, false], ![true, true, true, false, true, true, false],
    ![true, true, true, false, false, false, true], ![true, true, true, false, false, true, false],
    ![true, true, true, false, true, false, true]]

@[expose] def centCount : Fin 3 → Fin 7 → ℕ :=
  ![![1, 2, 0, 4, 0, 4, 4], ![1, 0, 2, 4, 0, 4, 4], ![1, 0, 2, 4, 0, 4, 4]]

@[expose] def factMax : Prop :=
  ∀ i j : Fin 7, (∃ u ∈ ballMaxL.getD i [], u ∈ classLists.getD j []) ↔ maxTable i j = true

@[expose] def factQR : Prop :=
  (∀ x ∈ ballQ, x ∈ ballR → x = 1) ∧
  (∀ x : AlpE, ∃ r ∈ ballR, x * r⁻¹ ∈ ballQ) ∧
  (∀ u ∈ ballQ, u * u = 1 → u ≠ 1 →
    u ∈ classLists.getD 1 [] ∨ u ∈ classLists.getD 2 [] ∨ u ∈ classLists.getD 4 []) ∧
  (∀ x ∈ ballR, x * x = 1 → x = 1 ∨ x = zc)

@[expose] def factCent : Prop :=
  (∀ i : Fin 3, ∀ g : AlpE, g * invE (![3, 5, 6] i) = invE (![3, 5, 6] i) * g ↔
    g ∈ ballCentL.getD i []) ∧
  (∀ i : Fin 3, ∀ j : Fin 7, ((ballCentL.getD i []).filter fun u =>
    u * u = 1 ∧ u ≠ 1 ∧ u ∈ classLists.getD j []).length = centCount i j) ∧
  (∀ g : AlpE, g * (AlpE.gen 1 ^ 2) = (AlpE.gen 1 ^ 2) * g ↔ g ∈ ballVt) ∧
  (∀ g : AlpE, g * (AlpE.gen 0 * AlpE.gen 2) = (AlpE.gen 0 * AlpE.gen 2) * g ↔
    g ∈ ballMaxL.getD 0 []) ∧
  (∀ g : AlpE, g * xE = xE * g ↔ g ∈ ballMaxL.getD 1 [])

@[expose] def factDerived : Prop :=
  (∀ x ∈ ballPd, x ∈ ballComm) ∧
  (∀ x : AlpE, x ∈ ballPd ↔ x ∈ ballMaxL.getD 0 [] ∧ x ∈ ballMaxL.getD 1 [] ∧
    x ∈ ballMaxL.getD 3 [])

@[expose] def factOrders : Prop :=
  (∀ x : AlpE, x.d = 0 → x ^ 4 = 1) ∧
  (∀ x : AlpE, (x.d = 1 ∨ x.d = 3) → x ^ 16 = 1 ∧ x ^ 8 ≠ 1) ∧
  (∀ x : AlpE, (x.d = 2 ∨ x.d = 4 ∨ x.d = 5 ∨ x.d = 6 ∨ x.d = 7) → x ^ 8 = 1) ∧
  (∀ x : AlpE, (x.d = 2 ∨ x.d = 4 ∨ x.d = 6) → x ^ 4 = 1 → x ^ 2 ≠ 1 → x ^ 2 = zc) ∧
  (∀ x : AlpE, x.d = 5 → x ^ 4 = 1 → x ^ 2 ≠ 1 → x ^ 2 = gen 0 ^ 2 * gen 1 ^ 2) ∧
  (∀ x : AlpE, x.d = 7 → x ^ 4 = 1 → x ^ 2 ≠ 1 → x ^ 2 = gen 1 ^ 2 * gen 2 ^ 2)

@[expose] def genCV : Fin 7 → List AlpE :=
  ![[gen 0 * gen 2], [gen 0 * (gen 2)⁻¹, gen 1 ^ 2], [gen 0 * gen 2, gen 0 ^ 2 * gen 1 ^ 2],
    [gen 0 * (gen 1)⁻¹, gen 0 ^ 2 * gen 2 ^ 2], [xE],
    [gen 0 ^ 2 * gen 2 ^ 2, gen 1 ^ 2 * gen 2 ^ 2], [zc]]

@[expose] def condCV (i : Fin 7) (g : AlpE) : Bool :=
  match i.val with
  | 0 => decide (g * gen 3 = gen 3 * g)
  | 1 => decide (g * gen 4 = gen 4 * g)
  | 2 => decide (g * gen 3 ^ 2 = gen 3 ^ 2 * g)
  | 3 => decide (g * (gen 3 * gen 4) = (gen 3 * gen 4) * g)
  | 4 => decide (g * gen 3 ^ 2 = gen 3 ^ 2 * g ∧ g * gen 4 = gen 4 * g)
  | 5 => decide (g * gen 3 ^ 2 = gen 3 ^ 2 * g ∧ g * (gen 3 * gen 4) = (gen 3 * gen 4) * g)
  | _ => decide (g * gen 3 = gen 3 * g ∧ g * gen 4 = gen 4 * g)

@[expose] def cardCV : Fin 7 → ℕ := ![4, 8, 8, 8, 4, 4, 2]

@[expose] def ballCVL : List (List AlpE) := (List.finRange 7).map fun i => ballFix (genCV i)

@[expose] def factCV : Prop :=
  ∀ i : Fin 7, SubOK (genCV i) (ballCVL.getD i []) (cardCV i) ∧
    ∀ g : AlpE, g.d = 0 → (condCV i g = true ↔ g ∈ ballCVL.getD i [])

@[expose] def factW : Prop :=
  (∀ x : AlpE, x.d = 0 → (x * x = 1 ↔ x ∈ ballW)) ∧
  (∀ g : AlpE, (∀ w ∈ genWE, g * w = w * g) ↔ g.d = 0) ∧
  (∀ g : AlpE, (∀ v ∈ genVE, g * v = v * g) ↔ g.d = 0) ∧
  (∀ g : AlpE, ∀ w ∈ ballW, g * w * g⁻¹ ∈ ballW)

instance : Decidable factCentre := by
  unfold factCentre
  infer_instance
instance : Decidable factClasses := by
  unfold factClasses
  infer_instance
instance : Decidable factNonV := by
  unfold factNonV
  infer_instance
instance : Decidable factSub := by
  unfold factSub
  infer_instance
instance : Decidable factMax := by
  unfold factMax
  infer_instance
set_option synthInstance.maxSize 512 in
instance : Decidable factQR := by
  unfold factQR
  infer_instance
instance : Decidable factCent := by
  unfold factCent
  infer_instance
instance : Decidable factDerived := by
  unfold factDerived
  infer_instance
instance : Decidable factOrders := by
  unfold factOrders
  infer_instance
instance : Decidable factCV := by
  unfold factCV
  infer_instance
instance : Decidable factW := by
  unfold factW
  infer_instance

@[expose] def f2Check : Bool :=
  decide factCentre && decide factClasses && decide factNonV && decide factSub &&
    decide factMax && decide factQR && decide factCent && decide factDerived &&
    decide factOrders && decide factCV && decide factW

end CFSG.OddStandard.ONanRec.F2
