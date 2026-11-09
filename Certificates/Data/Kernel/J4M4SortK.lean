module

public import Certificates.Data.Kernel.J4M4Sets

public section

namespace CFSG.KC.J4M4

@[expose] noncomputable def splitK (l : List Nat) : List Nat × List Nat :=
  List.rec (motive := fun _ => List Nat × List Nat) ([], []) (fun a _ ih => (a :: ih.2, ih.1)) l

@[expose] noncomputable def lenK (l : List Nat) : Nat :=
  List.rec (motive := fun _ => Nat) 0 (fun _ _ ih => Nat.succ ih) l

@[expose] noncomputable def mergeK (n : Nat) : List Nat → List Nat → List Nat :=
  Nat.rec (motive := fun _ => List Nat → List Nat → List Nat) (fun l₁ l₂ => l₁ ++ l₂)
    (fun _ ih l₁ l₂ =>
      List.rec (motive := fun _ => List Nat) l₂ (fun a t₁ _ =>
        List.rec (motive := fun _ => List Nat) (a :: t₁) (fun b t₂ _ =>
          Bool.rec (motive := fun _ => List Nat) (b :: ih (a :: t₁) t₂) (a :: ih t₁ (b :: t₂))
            (Nat.ble a b)) l₂) l₁) n

@[expose] noncomputable def msortFK (n : Nat) : List Nat → List Nat :=
  Nat.rec (motive := fun _ => List Nat → List Nat) (fun l => l)
    (fun _ ih l =>
      List.rec (motive := fun _ => List Nat) [] (fun a t _ =>
        List.rec (motive := fun _ => List Nat) [a] (fun b u _ =>
          mergeK (Nat.succ (Nat.succ (lenK u))) (ih (splitK (a :: b :: u)).1)
            (ih (splitK (a :: b :: u)).2)) t) l) n

@[expose] noncomputable def msortK (l : List Nat) : List Nat := msortFK 20 l

theorem splitK_eq : ∀ l : List Nat, splitK l = splitA l
  | [] => rfl
  | a :: l => by
    change (a :: (splitK l).2, (splitK l).1) = splitA (a :: l)
    rw [splitK_eq l, splitA.eq_2]

theorem lenK_eq : ∀ l : List Nat, lenK l = l.length
  | [] => rfl
  | _ :: l => by
    change Nat.succ (lenK l) = _
    rw [lenK_eq l]
    rfl

theorem mergeK_eq : ∀ (n : Nat) (l₁ l₂ : List Nat), mergeK n l₁ l₂ = mergeF n l₁ l₂
  | 0, _, _ => rfl
  | _ + 1, [], _ => rfl
  | _ + 1, _ :: _, [] => rfl
  | n + 1, a :: t₁, b :: t₂ => by
    change Bool.rec (motive := fun _ => List Nat) (b :: mergeK n (a :: t₁) t₂)
      (a :: mergeK n t₁ (b :: t₂)) (Nat.ble a b) = _
    rw [mergeK_eq n, mergeK_eq n, mergeF]
    cases Nat.ble a b <;> rfl

theorem msortFK_eq : ∀ (n : Nat) (l : List Nat), msortFK n l = msortF n l
  | 0, _ => rfl
  | _ + 1, [] => rfl
  | _ + 1, [_] => rfl
  | n + 1, a :: b :: u => by
    change mergeK (Nat.succ (Nat.succ (lenK u))) (msortFK n (splitK (a :: b :: u)).1)
      (msortFK n (splitK (a :: b :: u)).2) = _
    rw [mergeK_eq, msortFK_eq n, msortFK_eq n, splitK_eq, lenK_eq, msortF]

theorem msortK_eq (l : List Nat) : msortK l = msort l := msortFK_eq 20 l

@[expose] noncomputable def layersOKK (act : Nat → Nat → Nat) (ng : Nat) :
    List Nat → List (List (Nat × Nat × Nat)) → Bool
  | _, [] => true
  | B, ly :: rest =>
    ly.all (fun r => Nat.blt r.2.1 ng && Nat.beq (act r.2.1 r.2.2) r.1) &&
      subF (2 * ly.length + B.length + 1) (msortK (ly.map fun r => r.2.2)) B &&
      layersOKK act ng (msortK (B ++ ly.map fun r => r.1)) rest

@[expose] noncomputable def certOKK (act : Nat → Nat → Nat) (ng root : Nat) (L : List Nat)
    (Y : List (List (Nat × Nat × Nat))) : Bool :=
  Nat.ble Y.length 65 && sortedB L && eqL (msortK (keysY Y)) L &&
    match Y with
    | [] => false
    | y₀ :: rest => eqL (y₀.map fun r => r.1) [root] && layersOKK act ng [root] rest

@[expose] noncomputable def layerOKK (act : Nat → Nat → Nat) (ng : Nat) (B : List Nat)
    (ly : List (Nat × Nat × Nat)) : Bool :=
  ly.all (fun r => Nat.blt r.2.1 ng && Nat.beq (act r.2.1 r.2.2) r.1) &&
    subF (2 * ly.length + B.length + 1) (msortK (ly.map fun r => r.2.2)) B

@[expose] noncomputable def certHeadK (root : Nat) (L : List Nat)
    (Y : List (List (Nat × Nat × Nat))) : Bool :=
  Nat.ble Y.length 65 && sortedB L && eqL (msortK (keysY Y)) L &&
    eqL ((Y.getD 0 []).map fun r => r.1) [root]

@[expose] noncomputable def closeOKK (act : Nat → Nat → Nat) (ng : Nat) (L : List Nat) : Bool :=
  (List.range ng).all fun s => eqL (msortK (L.map (act s))) L

theorem layersOKK_eq (act : Nat → Nat → Nat) (ng : Nat) :
    ∀ (B : List Nat) (Y : List (List (Nat × Nat × Nat))), layersOKK act ng B Y = layersOK act ng B Y
  | _, [] => rfl
  | B, ly :: rest => by
    rw [layersOKK, layersOK, msortK_eq, msortK_eq, layersOKK_eq act ng _ rest]

theorem certOKK_eq (act : Nat → Nat → Nat) (ng root : Nat) (L : List Nat)
    (Y : List (List (Nat × Nat × Nat))) : certOKK act ng root L Y = certOK act ng root L Y := by
  unfold certOKK certOK
  rw [msortK_eq]
  cases Y with
  | nil => rfl
  | cons y₀ rest => simp only [layersOKK_eq]

theorem layerOKK_eq (act : Nat → Nat → Nat) (ng : Nat) (B : List Nat)
    (ly : List (Nat × Nat × Nat)) : layerOKK act ng B ly = layerOK act ng B ly := by
  unfold layerOKK layerOK
  rw [msortK_eq]

theorem certHeadK_eq (root : Nat) (L : List Nat) (Y : List (List (Nat × Nat × Nat))) :
    certHeadK root L Y = certHead root L Y := by
  unfold certHeadK certHead
  rw [msortK_eq]

theorem closeOKK_eq (act : Nat → Nat → Nat) (ng : Nat) (L : List Nat) :
    closeOKK act ng L = closeOK act ng L := by
  unfold closeOKK closeOK
  simp only [msortK_eq]

end CFSG.KC.J4M4
