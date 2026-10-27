module

public import CFSG.LocalAnalysis.WeakClosure81.W183FinSp44Pack

public section

namespace CFSG.LocalAnalysis.WeakClosure81.Sp44

@[expose] def packLK (w : Nat) (L : List Nat) : Nat := L.foldr (fun x acc => x + (acc <<< w)) 0

@[expose] def laneK (w T p : Nat) : Nat := (T >>> (w * p)) &&& (2 ^ w - 1)

theorem getD_eq_laneK (w : Nat) : ∀ (L : List Nat), (∀ x ∈ L, x < 2 ^ w) → ∀ p,
    L.getD p 0 = laneK w (packLK w L) p
  | [], _, p => by simp [laneK, packLK]
  | x :: L, h, p => by
    have hx : x < 2 ^ w := h x (List.mem_cons_self ..)
    have ih := getD_eq_laneK w L (fun y hy => h y (List.mem_cons_of_mem _ hy))
    have hpos : 0 < 2 ^ w := Nat.two_pow_pos w
    have hdiv : (x + packLK w L * 2 ^ w) / 2 ^ w = packLK w L := by
      rw [Nat.add_mul_div_right _ _ hpos, Nat.div_eq_of_lt hx, Nat.zero_add]
    have hc : packLK w (x :: L) = x + packLK w L * 2 ^ w := by
      simp only [packLK, List.foldr_cons, Nat.shiftLeft_eq]
    cases p with
    | zero =>
      rw [List.getD_cons_zero, laneK, hc, Nat.mul_zero, Nat.shiftRight_zero,
        Nat.and_two_pow_sub_one_eq_mod, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hx]
    | succ p =>
      rw [List.getD_cons_succ, ih p, laneK, laneK, hc, Nat.mul_succ, Nat.add_comm (w * p) w,
        Nat.shiftRight_add, Nat.shiftRight_eq_div_pow (x + _) w, hdiv]

@[expose] def decEl (c : Nat) : El := (c / 4, c % 4)

@[expose] def invsCodesK : List Nat := [
  4299165702, 4299182084, 4299182086, 4299198468, 4299214852, 4299165956, 4299165958, 4299182340,
  4299182342, 4299198724, 4299215108, 4299166212, 4299182596, 4299198980, 4299215364, 4299166468,
  4299182852, 4299199236, 4299215620, 4299231300, 4299231302, 4299247684, 4299247686, 4299264068,
  4299280452, 4299231556, 4299231558, 4299247940, 4299247942, 4299264324, 4299280708, 4299231812,
  4299248196, 4299264580, 4299280964, 4299232068, 4299248452, 4299264836, 4299281220, 4299296900,
  4299313284, 4299329668, 4299346052, 4299297156, 4299313540, 4299329924, 4299346308, 4299297412,
  4299313796, 4299330180, 4299346564, 4299297668, 4299314052, 4299330436, 4299346820, 4299362500,
  4299378884, 4299395268, 4299411652, 4299362756, 4299379140, 4299395524, 4299411908, 4299363012,
  4299379396, 4299395780, 4299412164, 4299363268, 4299379652, 4299396036, 4299412420, 4315942932,
  4315942934, 4315943188, 4315943190, 4315943444, 4315943700, 4316008532, 4316008534, 4316008788,
  4316008790, 4316009044, 4316009300, 4316074132, 4316156054, 4316074388, 4316156310, 4316074644,
  4316074900, 4316139732, 4316090582, 4316139988, 4316090838, 4316140244, 4316140500, 4332720164,
  4332720420, 4332720676, 4332720932, 4332785764, 4332786020, 4332786276, 4332786532, 4332851364,
  4332851620, 4332851876, 4332852132, 4332916964, 4332917220, 4332917476, 4332917732, 4349497396,
  4349497652, 4349497908, 4349498164, 4349562996, 4349563252, 4349563508, 4349563764, 4349628596,
  4349628852, 4349629108, 4349629364, 4349694196, 4349694452, 4349694708, 4349694964]

theorem invs_eq_codesK : invs = invsCodesK.map decEl := by
  have h : (invs == invsCodesK.map decEl) = true := by decide +kernel
  exact eq_of_beq h

theorem invsCodesK_lt : ∀ x ∈ invsCodesK, x < 2 ^ 34 := by
  have h : invsCodesK.all (fun x => decide (x < 2 ^ 34)) = true := by decide +kernel
  intro x hx
  exact of_decide_eq_true (List.all_eq_true.mp h x hx)

@[expose] def invsTabK : Nat := packLK 34 invsCodesK

theorem invsA_getElem_eq (i : Nat) : invsA[i]! = decEl (laneK 34 invsTabK i) := by
  rw [invsTabK, ← getD_eq_laneK 34 invsCodesK invsCodesK_lt i, invsA, invs_eq_codesK,
    List.getElem!_toArray, List.getElem!_eq_getElem?_getD, List.getElem?_map,
    List.getD_eq_getElem?_getD]
  cases invsCodesK[i]? <;> rfl

@[expose] def gmulTab : Nat := 2625168384

@[expose] def gmulK (a b : Nat) : Nat := (gmulTab >>> (2 * (4 * a + b))) &&& 3

theorem gmul_eq_K (a b : Nat) (ha : a < 4) (hb : b < 4) : gmul a b = gmulK a b := by
  have h : ∀ a < 4, ∀ b < 4, gmul a b = gmulK a b := by decide
  exact h a ha b hb

@[expose] def scalK (a b : Nat) : Nat := ((a &&& 1) * b) ^^^ (((a >>> 1) &&& 1) * mulW b)

theorem scal_eq_K (a b : Nat) (ha : a < 4) : scal a b = scalK a b := by
  rcases (by omega : a = 0 ∨ a = 1 ∨ a = 2 ∨ a = 3) with rfl | rfl | rfl | rfl <;>
    simp [scal, scalK]

theorem ent_lt (r k : Nat) : ent r k < 4 := by
  have := Nat.and_le_right (n := r >>> (2 * k)) (m := 3)
  unfold ent
  omega

theorem e2_lt (M i j : Nat) : e2 M i j < 4 := by
  have := Nat.and_le_right (n := M >>> (2 * (4 * i + j))) (m := 3)
  unfold e2
  omega

@[expose] def mulRowK (r B : Nat) : Nat :=
  scalK (ent r 0) (row B 0) ^^^ scalK (ent r 1) (row B 1) ^^^ scalK (ent r 2) (row B 2) ^^^
    scalK (ent r 3) (row B 3)

@[expose] def mmulK (A B : Nat) : Nat :=
  mulRowK (row A 0) B ||| (mulRowK (row A 1) B <<< 8) ||| (mulRowK (row A 2) B <<< 16) |||
    (mulRowK (row A 3) B <<< 24)

theorem mmul_eq_K (A B : Nat) : mmul A B = mmulK A B := by
  simp only [mmul, mmulK, mulRow, mulRowK, scal_eq_K _ _ (ent_lt _ _)]

@[expose] def rhoG (m : Nat → Nat → Nat) (g : Nat) : Nat :=
  let f : Nat → Nat → Nat → Nat → Nat := fun i j k l =>
    m (e2 g i k) (e2 g j l) ^^^ m (e2 g i l) (e2 g j k)
  (f 0 1 0 1) ||| (f 0 1 0 2 <<< 2) ||| (f 0 1 1 3 <<< 4) ||| (f 0 1 2 3 <<< 6) |||
  (f 0 2 0 1 <<< 8) ||| (f 0 2 0 2 <<< 10) ||| (f 0 2 1 3 <<< 12) ||| (f 0 2 2 3 <<< 14) |||
  (f 1 3 0 1 <<< 16) ||| (f 1 3 0 2 <<< 18) ||| (f 1 3 1 3 <<< 20) ||| (f 1 3 2 3 <<< 22) |||
  (f 2 3 0 1 <<< 24) ||| (f 2 3 0 2 <<< 26) ||| (f 2 3 1 3 <<< 28) ||| (f 2 3 2 3 <<< 30)

@[expose] def rhoK (g : Nat) : Nat := rhoG gmulK g

theorem rho_eq_K (g : Nat) : rho g = rhoK g := by
  have h : rho g = rhoG gmul g := rfl
  rw [h, rhoK]
  simp only [rhoG, gmul_eq_K _ _ (e2_lt _ _ _) (e2_lt _ _ _)]

@[expose] noncomputable def forceK {α : Type} (y : Nat) (k : Nat → α) : α :=
  Nat.rec (motive := fun _ => α) (k (nat_lit 0)) (fun n _ => k (Nat.succ n)) y

theorem forceK_apply {α : Type} (y : Nat) (k : Nat → α) : forceK y k = k y := by
  cases y <;> rfl

@[expose] noncomputable def rhoPowK (n : Nat) : Nat → Nat :=
  Nat.rec (motive := fun _ => Nat → Nat) (fun g => g) (fun _ F g => forceK (rhoK g) F) n

theorem rhoPow_eq_K : ∀ (n g : Nat), rhoPow n g = rhoPowK n g
  | 0, _ => rfl
  | n + 1, g => by
    rw [rhoPow, rhoPow_eq_K n (rho g), rho_eq_K]
    exact (forceK_apply (rhoK g) (rhoPowK n)).symm

@[expose] def transpK (M : Nat) : Nat :=
  let t : Nat → Nat → Nat := fun i j => ((M >>> (2 * (4 * i + j))) &&& 3) <<< (2 * (4 * j + i))
  0 ||| t 0 0 ||| t 0 1 ||| t 0 2 ||| t 0 3 ||| t 1 0 ||| t 1 1 ||| t 1 2 ||| t 1 3 |||
    t 2 0 ||| t 2 1 ||| t 2 2 ||| t 2 3 ||| t 3 0 ||| t 3 1 ||| t 3 2 ||| t 3 3

theorem transp_eq_K (M : Nat) : transp M = transpK M := rfl

@[expose] noncomputable def gmulEK (x y : El) : El :=
  forceK x.1 fun a => forceK (rhoPowK x.2 y.1) fun r => (mmulK a r, (x.2 + y.2) % 4)

theorem gmulE_eq_K : gmulE = gmulEK := by
  funext x y
  simp only [gmulE, gmulEK, forceK_apply, mmul_eq_K, rhoPow_eq_K]

@[expose] noncomputable def invEK (x : El) : El :=
  let j' := (4 - x.2) % 4
  (forceK x.1 fun m => rhoPowK j' (mmulK Jm (mmulK (transpK m) Jm)), j')

theorem invE_eq_K : invE = invEK := by
  funext x
  simp only [invE, invEK, mmul_eq_K, rhoPow_eq_K, transp_eq_K, forceK_apply]

end CFSG.LocalAnalysis.WeakClosure81.Sp44

end
