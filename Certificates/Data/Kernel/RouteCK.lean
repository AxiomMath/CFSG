module

public import Certificates.Data.RouteCCheck

public section

namespace CFSG.CGT.PushingUpLit.CGT6.RouteCK

open CFSG.CGT.PushingUpLit.CGT6.RouteC

@[expose] noncomputable def forceN {β : Sort _} (y : Nat) (k : Nat → β) : β :=
  Nat.rec (motive := fun _ => β) (k 0) (fun m _ => k (Nat.succ m)) y

@[expose] noncomputable def packL (A : List Nat) : Nat :=
  List.rec (motive := fun _ => Nat) 0 (fun a _ ih => Nat.add a (Nat.mul 64 ih)) A

@[expose] noncomputable def mvR (k : Nat) : Nat → Nat → Nat :=
  Nat.rec (motive := fun _ => Nat → Nat → Nat) (fun _ _ => 0)
    (fun _ ih P v => Nat.xor (Nat.mul (Nat.mod P 64) (Nat.mod v 2)) (ih (Nat.div P 64) (Nat.div v 2))) k

@[expose] noncomputable def mv (P v : Nat) : Nat :=
  Nat.xor (Nat.mul (Nat.mod P 64) (Nat.mod v 2))
  (Nat.xor (Nat.mul (Nat.mod (Nat.div P 64) 64) (Nat.mod (Nat.div v 2) 2))
  (Nat.xor (Nat.mul (Nat.mod (Nat.div P 4096) 64) (Nat.mod (Nat.div v 4) 2))
  (Nat.xor (Nat.mul (Nat.mod (Nat.div P 262144) 64) (Nat.mod (Nat.div v 8) 2))
  (Nat.xor (Nat.mul (Nat.mod (Nat.div P 16777216) 64) (Nat.mod (Nat.div v 16) 2))
    (Nat.mul (Nat.mod (Nat.div P 1073741824) 64) (Nat.mod (Nat.div v 32) 2))))))

@[expose] noncomputable def mulR (P : Nat) (k : Nat) : Nat → Nat :=
  Nat.rec (motive := fun _ => Nat → Nat) (fun _ => 0)
    (fun _ ih B => Nat.add (mv P (Nat.mod B 64)) (Nat.mul 64 (ih (Nat.div B 64)))) k

@[expose] noncomputable def mulK (A B : Nat) : Nat :=
  forceN A fun A => forceN B fun B =>
  Nat.add (mv A (Nat.mod B 64))
  (Nat.add (Nat.mul 64 (mv A (Nat.mod (Nat.div B 64) 64)))
  (Nat.add (Nat.mul 4096 (mv A (Nat.mod (Nat.div B 4096) 64)))
  (Nat.add (Nat.mul 262144 (mv A (Nat.mod (Nat.div B 262144) 64)))
  (Nat.add (Nat.mul 16777216 (mv A (Nat.mod (Nat.div B 16777216) 64)))
    (Nat.mul 1073741824 (mv A (Nat.mod (Nat.div B 1073741824) 64)))))))

@[expose] noncomputable def oneK : Nat := 34630287489

@[expose] noncomputable def powK (A k : Nat) : Nat :=
  forceN A fun A => Nat.rec (motive := fun _ => Nat) oneK (fun _ acc => mulK A acc) k

@[expose] noncomputable def swapK (m s M : Nat) : Nat :=
  Nat.lor (Nat.land (Nat.shiftRight m s) M) (Nat.shiftLeft (Nat.land m M) s)

@[expose] noncomputable def selK (m t c : Nat) : Nat := Nat.xor m (Nat.mul (Nat.xor m t) c)

@[expose] noncomputable def bitK (b j : Nat) : Nat := Nat.mod (Nat.div b (Nat.pow 2 j)) 2

@[expose] noncomputable def xl (m b : Nat) : Nat :=
  forceN (selK m (swapK m 1 6148914691236517205) (bitK b 0)) fun m1 =>
  forceN (selK m1 (swapK m1 2 3689348814741910323) (bitK b 1)) fun m2 =>
  forceN (selK m2 (swapK m2 4 1085102592571150095) (bitK b 2)) fun m3 =>
  forceN (selK m3 (swapK m3 8 71777214294589695) (bitK b 3)) fun m4 =>
  forceN (selK m4 (swapK m4 16 281470681808895) (bitK b 4)) fun m5 =>
  selK m5 (swapK m5 32 4294967295) (bitK b 5)

@[expose] noncomputable def smK (l : List Nat) : Nat :=
  List.rec (motive := fun _ => Nat) 1 (fun b _ ih => forceN ih fun m => Nat.lor m (xl m b)) l

@[expose] noncomputable def memK (M v : Nat) : Bool := Nat.beq (bitK M v) 1

@[expose] noncomputable def allL (p : Nat → Bool) (l : List Nat) : Bool :=
  List.rec (motive := fun _ => Bool) true (fun x _ ih => p x && ih) l

@[expose] noncomputable def anyL (p : Nat → Bool) (l : List Nat) : Bool :=
  List.rec (motive := fun _ => Bool) false (fun x _ ih => p x || ih) l

@[expose] noncomputable def allC (p : Nat → Nat → Bool) (k : Nat) : Nat → Nat → Bool :=
  Nat.rec (motive := fun _ => Nat → Nat → Bool) (fun _ _ => true)
    (fun _ ih X Y => p (Nat.mod X 64) (Nat.mod Y 64) && ih (Nat.div X 64) (Nat.div Y 64)) k

@[expose] noncomputable def xorC (k : Nat) : Nat → Nat → List Nat :=
  Nat.rec (motive := fun _ => Nat → Nat → List Nat) (fun _ _ => [])
    (fun _ ih X Y => Nat.xor (Nat.mod X 64) (Nat.mod Y 64) :: ih (Nat.div X 64) (Nat.div Y 64)) k

@[expose] noncomputable def eqModK (KM X Y : Nat) : Bool := allC (fun a b => memK KM (Nat.xor a b)) 6 X Y

@[expose] noncomputable def lettersK (φ ψ : Nat) : Nat :=
  forceN (packL (chartY φ)) fun Y => forceN (packL (chartD ψ)) fun D =>
  Nat.add Y (Nat.mul 68719476736 (Nat.add D (Nat.mul 68719476736 (Nat.add (packL chartT)
    (Nat.mul 68719476736 (Nat.add (mulK Y Y) (Nat.mul 68719476736 (mulK D D))))))))

@[expose] noncomputable def genK (G l : Nat) : Nat :=
  Nat.mod (Nat.div G (Nat.pow 68719476736 (Nat.sub 4 (Nat.sub 4 l)))) 68719476736

@[expose] noncomputable def evalWK (G : Nat) (w : List Nat) : Nat :=
  List.rec (motive := fun _ => Nat → Nat) (fun acc => acc)
    (fun l _ ih acc => forceN (mulK acc (genK G l)) ih) w oneK

@[expose] noncomputable def addVK (b : List Nat) (M v : Nat) (k : List Nat → Nat → Bool) : Bool :=
  Bool.rec (forceN (Nat.lor M (xl M v)) fun M' => k (v :: b) M') (k b M) (memK M v)

@[expose] noncomputable def addImgs (P : Nat) (src : List Nat) :
    List Nat → Nat → (List Nat → Nat → Bool) → Bool :=
  List.rec (motive := fun _ => List Nat → Nat → (List Nat → Nat → Bool) → Bool)
    (fun cur M k => k cur M)
    (fun x _ ih cur M k => forceN (mv P x) fun v => addVK cur M v fun c' M' => ih c' M' k) src

@[expose] noncomputable def addAll (src : List Nat) :
    List Nat → Nat → (List Nat → Nat → Bool) → Bool :=
  List.rec (motive := fun _ => List Nat → Nat → (List Nat → Nat → Bool) → Bool)
    (fun cur M k => k cur M)
    (fun x _ ih cur M k => addVK cur M x fun c' M' => ih c' M' k) src

@[expose] noncomputable def stepK (Y D T : Nat) (b : List Nat) (M : Nat)
    (k : List Nat → Nat → Bool) : Bool :=
  addImgs Y b b M fun b1 M1 => addImgs D b b1 M1 fun b2 M2 => addImgs T b b2 M2 k

@[expose] noncomputable def iterK (Y D T : Nat) (s : Nat) :
    List Nat → Nat → (List Nat → Nat → Bool) → Bool :=
  Nat.rec (motive := fun _ => List Nat → Nat → (List Nat → Nat → Bool) → Bool)
    (fun b M k => k b M)
    (fun _ ih b M k => stepK Y D T b M fun b' M' =>
      Bool.rec (ih b' M' k) (k b M) (Nat.beq b'.length b.length)) s

@[expose] noncomputable def checkBK (G : Nat) (Kb : List Nat) (m : Nat) (g : List Nat) : Bool :=
  forceN (smK Kb) fun KM =>
  forceN (genK G 0) fun Y => forceN (genK G 1) fun D => forceN (genK G 2) fun T =>
  forceN (powK (evalWK G g) m) fun Pm =>
  let km1 := xorC 6 Pm oneK
  forceN (packL km1) fun Q =>
  addAll (Kb ++ km1) [] 1 fun b0 M0 =>
  iterK Y D T 7 b0 M0 fun Wb WM =>
  allL (fun b => memK WM (mv Y b) && memK WM (mv D b) && memK WM (mv T b)) Wb &&
  allL (fun x => memK WM x) km1 &&
  allL (fun b => memK KM (mv Q b)) Wb &&
  anyL (fun x => !memK KM x) km1

@[expose] noncomputable def checkCK (G : Nat) (Kb : List Nat) (a m : Nat) (cw : List Nat) : Bool :=
  forceN (smK Kb) fun KM =>
  forceN (evalWK G cw) fun ct => forceN (evalWK G (invW cw)) fun ci =>
  forceN (genK G 0) fun Y => forceN (genK G 2) fun T =>
  forceN (mulK Y (mulK ct (mulK Y ci))) fun x =>
  eqModK KM (mulK T ct) (mulK ct T) &&
  eqModK KM (mulK ct ci) oneK &&
  m % 3 != 0 &&
  !eqModK KM (powK x a) oneK &&
  eqModK KM (powK (powK x a) m) oneK

@[expose] noncomputable def kerK (P : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) 0
    (fun x ih => forceN ih fun r =>
      Nat.lor r (Nat.shiftLeft (Bool.rec 0 1 (Nat.beq (mv P x) 0)) x)) 64

@[expose] noncomputable def smallM (A : List Nat) : Bool :=
  Nat.ble A.length 6 && allL (fun x => Nat.blt x 64) A

@[expose] noncomputable def checkSK (n φ ψ : Nat) (Kb : List Nat) (s : Mat × Mat × Mat)
    (θ : Mat) : Bool :=
  Nat.ble n 6 && Nat.beq θ.length 6 && allL (fun x => Nat.blt x (Nat.pow 2 n)) θ &&
  smallM s.1 && smallM s.2.1 && smallM s.2.2 &&
  forceN (packL θ) fun P => forceN (smK Kb) fun KM =>
  Nat.beq (mulK P (packL (chartY φ))) (mulK (packL s.1) P) &&
  Nat.beq (mulK P (packL (chartD ψ))) (mulK (packL s.2.1) P) &&
  Nat.beq (mulK P (packL chartT)) (mulK (packL s.2.2) P) &&
  Nat.beq (kerK P) KM &&
  forceN (Nat.pow 2 (Nat.pow 2 n)) fun F =>
  Nat.beq (Nat.mod (smK θ) F) (Nat.sub F 1)

@[expose] noncomputable def memberOkK (surv : List (Mat × Mat × Mat)) (n : Nat) (Kb : List Nat)
    (φ ψ : Nat) (w : List Nat) : Bool :=
  match w with
  | 0 :: m :: g => forceN (lettersK φ ψ) fun G => checkBK G Kb m g
  | 1 :: a :: m :: cw => forceN (lettersK φ ψ) fun G => checkCK G Kb a m cw
  | 3 :: i :: θ =>
    match surv[i]? with
    | some s => checkSK n φ ψ Kb s θ
    | none => false
  | _ => false

@[expose] noncomputable def appR {α : Type} (l r : List α) : List α :=
  List.rec (motive := fun _ => List α) r (fun x _ ih => x :: ih) l

@[expose] noncomputable def rangeR {α : Type} (f : Nat → List α) (lo cnt : Nat) : List α :=
  Nat.rec (motive := fun _ => Nat → List α) (fun _ => [])
    (fun _ ih lo => forceN lo fun lo => appR (f lo) (ih (Nat.succ lo))) cnt lo

@[expose] noncomputable def kListK (r : Nat) : List (List Nat) :=
  Nat.rec (motive := fun _ => List (List Nat)) [[]] (fun r' _ =>
    Nat.rec (motive := fun _ => List (List Nat)) (rangeR (fun v => [[v]]) 1 63)
      (fun r'' _ => Nat.rec (motive := fun _ => List (List Nat))
        (rangeR (fun a => rangeR (fun b => [[a, b]]) (Nat.succ a) (Nat.sub 63 a)) 1 62)
        (fun _ _ => []) r'')
      r') r

@[expose] noncomputable def filterR (p : Nat → Bool) (lo cnt : Nat) : List Nat :=
  rangeR (fun x => Bool.rec [] [x] (p x)) lo cnt

@[expose] noncomputable def mapR {α β : Type} (f : α → β) (l : List α) : List β :=
  List.rec (motive := fun _ => List β) [] (fun x _ ih => f x :: ih) l

@[expose] noncomputable def flatMapR {α β : Type} (f : α → List β) (l : List α) : List β :=
  List.rec (motive := fun _ => List β) [] (fun x _ ih => appR (f x) ih) l

@[expose] noncomputable def invK (Kb : List Nat) (KM P : Nat) : Bool :=
  allL (fun b => memK KM (mv P b)) Kb

@[expose] noncomputable def condTK (Kb : List Nat) (KM : Nat) : Bool :=
  invK Kb KM (packL chartT) && allL (fun x => !memK KM x) [1, 2, 3, 4, 8, 12] &&
    anyL (fun x => !memK KM x) (xorC 6 (packL chartT) oneK)

@[expose] noncomputable def membersK (n : Nat) : List (List Nat × Nat × Nat) :=
  flatMapR (fun Kb => forceN (smK Kb) fun KM =>
    Bool.rec []
      (flatMapR (fun φ => mapR (fun ψ => (Kb, φ, ψ))
          (filterR (fun ψ => invK Kb KM (packL (chartD ψ))) 0 256))
        (filterR (fun φ => invK Kb KM (packL (chartY φ))) 0 16))
      (condTK Kb KM)) (kListK (Nat.sub 6 n))

@[expose] noncomputable def zipAllK (surv : List (Mat × Mat × Mat)) (n : Nat) :
    List (List Nat × Nat × Nat) → List Nat → Bool :=
  List.rec (motive := fun _ => List Nat → Bool)
    (fun d => List.rec (motive := fun _ => Bool) true (fun _ _ _ => false) d)
    (fun m _ ih d => List.rec (motive := fun _ => Bool) false
      (fun x rest _ => memberOkK surv n m.1 m.2.1 m.2.2 (unpack 64 x) && ih rest) d)

@[expose] noncomputable def checkK (surv : List (Mat × Mat × Mat)) (n : Nat) (data : List Nat) :
    Bool :=
  zipAllK surv n (membersK n) data

end CFSG.CGT.PushingUpLit.CGT6.RouteCK
