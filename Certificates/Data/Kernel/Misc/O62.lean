module

public import Certificates.Data.Kernel.Misc.Base

public section

namespace CFSG.KC.Misc.O62

open CFSG.KC.Ord CFSG.KC.LQT.P CFSG.KC.Misc

@[expose] noncomputable def bitK (x k : Nat) : Nat := Nat.land (Nat.shiftRight x k) (nat_lit 1)

@[expose] noncomputable def colK (m j : Nat) : Nat :=
  Nat.land (Nat.shiftRight m (Nat.mul (nat_lit 6) j)) (nat_lit 63)

@[expose] noncomputable def actK (a₀ a₁ a₂ a₃ a₄ a₅ v : Nat) : Nat :=
  Nat.xor (Nat.xor (Nat.xor (Nat.mul (bitK v (nat_lit 0)) a₀) (Nat.mul (bitK v (nat_lit 1)) a₁))
    (Nat.xor (Nat.mul (bitK v (nat_lit 2)) a₂) (Nat.mul (bitK v (nat_lit 3)) a₃)))
    (Nat.xor (Nat.mul (bitK v (nat_lit 4)) a₄) (Nat.mul (bitK v (nat_lit 5)) a₅))

@[expose] noncomputable def packK (c₀ c₁ c₂ c₃ c₄ c₅ : Nat) : Nat :=
  Nat.lor (Nat.lor (Nat.lor c₀ (Nat.shiftLeft c₁ (nat_lit 6))) (Nat.lor (Nat.shiftLeft c₂ (nat_lit 12))
    (Nat.shiftLeft c₃ (nat_lit 18)))) (Nat.lor (Nat.shiftLeft c₄ (nat_lit 24))
    (Nat.shiftLeft c₅ (nat_lit 30)))

@[expose] noncomputable def mulCols (a₀ a₁ a₂ a₃ a₄ a₅ b : Nat) : Nat :=
  packK (actK a₀ a₁ a₂ a₃ a₄ a₅ (colK b (nat_lit 0))) (actK a₀ a₁ a₂ a₃ a₄ a₅ (colK b (nat_lit 1)))
    (actK a₀ a₁ a₂ a₃ a₄ a₅ (colK b (nat_lit 2))) (actK a₀ a₁ a₂ a₃ a₄ a₅ (colK b (nat_lit 3)))
    (actK a₀ a₁ a₂ a₃ a₄ a₅ (colK b (nat_lit 4))) (actK a₀ a₁ a₂ a₃ a₄ a₅ (colK b (nat_lit 5)))

@[expose] noncomputable def tab3 (c₀ c₁ c₂ : Nat) : Nat :=
  letN (Nat.xor c₀ c₁) fun c₀₁ =>
  Nat.lor (Nat.lor (Nat.lor (Nat.shiftLeft c₀ (nat_lit 6)) (Nat.shiftLeft c₁ (nat_lit 12)))
      (Nat.lor (Nat.shiftLeft c₀₁ (nat_lit 18)) (Nat.shiftLeft c₂ (nat_lit 24))))
    (Nat.lor (Nat.lor (Nat.shiftLeft (Nat.xor c₀ c₂) (nat_lit 30))
        (Nat.shiftLeft (Nat.xor c₁ c₂) (nat_lit 36)))
      (Nat.shiftLeft (Nat.xor c₀₁ c₂) (nat_lit 42)))

@[expose] noncomputable def lookT (T v : Nat) : Nat :=
  Nat.land (Nat.shiftRight T (Nat.mul (nat_lit 6) v)) (nat_lit 63)

@[expose] noncomputable def actT (T₀ T₁ v : Nat) : Nat :=
  Nat.xor (lookT T₀ (Nat.land v (nat_lit 7))) (lookT T₁ (Nat.shiftRight v (nat_lit 3)))

@[expose] noncomputable def mulK (a b : Nat) : Nat :=
  letN a fun a => letN b fun b =>
  letN (tab3 (colK a (nat_lit 0)) (colK a (nat_lit 1)) (colK a (nat_lit 2))) fun T₀ =>
  letN (tab3 (colK a (nat_lit 3)) (colK a (nat_lit 4)) (colK a (nat_lit 5))) fun T₁ =>
    packK (actT T₀ T₁ (colK b (nat_lit 0))) (actT T₀ T₁ (colK b (nat_lit 1)))
      (actT T₀ T₁ (colK b (nat_lit 2))) (actT T₀ T₁ (colK b (nat_lit 3)))
      (actT T₀ T₁ (colK b (nat_lit 4))) (actT T₀ T₁ (colK b (nat_lit 5)))

@[expose] noncomputable def oneK : Nat := nat_lit 34630287489

@[expose] noncomputable def reflColK (n j : Nat) : Nat :=
  Nat.xor (Nat.shiftLeft (nat_lit 1) j) (Nat.mul (bitK n (Nat.xor j (nat_lit 1))) (Nat.land n (nat_lit 63)))

@[expose] noncomputable def reflCK (n : Nat) : Nat :=
  packK (reflColK n (nat_lit 0)) (reflColK n (nat_lit 1)) (reflColK n (nat_lit 2))
    (reflColK n (nat_lit 3)) (reflColK n (nat_lit 4)) (reflColK n (nat_lit 5))

@[expose] noncomputable def wordCK (w : List Nat) : Nat :=
  List.rec (motive := fun _ => Nat) oneK (fun n _ acc => mulK (reflCK n) acc) w

@[expose] noncomputable def revN (w : List Nat) : List Nat :=
  List.rec (motive := fun _ => List Nat → List Nat) (fun acc => acc)
    (fun x _ ih acc => ih (List.cons x acc)) w List.nil

@[expose] noncomputable def qBK (m n : Nat) : Bool :=
  Nat.beq (Nat.xor (Nat.xor (Nat.mul (bitK n (nat_lit 0)) (bitK n (nat_lit 1)))
    (Nat.mul (bitK n (nat_lit 2)) (bitK n (nat_lit 3))))
    (Nat.xor (Nat.mul (bitK n (nat_lit 4)) (bitK n (nat_lit 5)))
      (Nat.mul m (Nat.xor (bitK n (nat_lit 4)) (bitK n (nat_lit 5)))))) (nat_lit 1)

@[expose] noncomputable def isInvK (x : Nat) : Bool :=
  andB (Nat.beq (mulK x x) oneK) (notB (Nat.beq x oneK))

@[expose] noncomputable def commK (x y : Nat) : Bool := Nat.beq (mulK x y) (mulK y x)

@[expose] noncomputable def parW (w : List Nat) : Nat :=
  List.rec (motive := fun _ => Nat) (nat_lit 0) (fun _ _ ih => Nat.xor ih (nat_lit 1)) w

@[expose] noncomputable def m36 : Nat := nat_lit 68719476735

@[expose] noncomputable def plCnt (p : Nat) : Nat := Nat.land p (nat_lit 255)

@[expose] noncomputable def plLane (p i : Nat) : Nat :=
  Nat.land (Nat.shiftRight p (Nat.add (nat_lit 8) (Nat.mul (nat_lit 37) i))) (nat_lit 137438953471)

@[expose] noncomputable def plAt (p i : Nat) : Nat := Nat.land (plLane p i) m36

@[expose] noncomputable def plPar (p i : Nat) : Nat := Nat.shiftRight (plLane p i) (nat_lit 36)

@[expose] noncomputable def plPush (p x : Nat) : Nat :=
  letN p fun p => Nat.add (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.shiftRight p (nat_lit 8))
    (nat_lit 37)) x) (nat_lit 8)) (Nat.succ (plCnt p))

@[expose] noncomputable def plMem (p y : Nat) : Bool :=
  letB y fun y => anyN (plCnt p) fun i => Nat.beq (plAt p i) y

@[expose] noncomputable def plOf (l : List Nat) : Nat :=
  List.rec (motive := fun _ => Nat → Nat) (fun acc => acc) (fun x _ ih acc => ih (plPush acc x)) l
    (nat_lit 0)

@[expose] noncomputable def spanAdd (S x : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) S (fun i acc => plPush acc (mulK (plAt S i) x)) (plCnt S)

@[expose] noncomputable def plFilterFrom (C i : Nat) (f : Nat → Bool) : Nat :=
  Nat.rec (motive := fun _ => Nat) (nat_lit 0)
    (fun j acc => Bool.rec (motive := fun _ => Nat) acc (plPush acc (plLane C j))
      (andB (Nat.blt i j) (letB (plAt C j) f))) (plCnt C)

@[expose] noncomputable def plFilter (C : Nat) (f : Nat → Bool) : Nat :=
  Nat.rec (motive := fun _ => Nat) (nat_lit 0)
    (fun j acc => Bool.rec (motive := fun _ => Nat) acc (plPush acc (plLane C j))
      (letB (plAt C j) f))
    (plCnt C)

@[expose] noncomputable def codesK (Tw : List (List Nat)) : List Nat :=
  List.rec (motive := fun _ => List Nat) List.nil (fun w _ ih => List.cons (wordCK w) ih) Tw

@[expose] noncomputable def cntEven (Tw : List (List Nat)) : Nat :=
  List.rec (motive := fun _ => Nat) (nat_lit 0)
    (fun w _ ih => Nat.add ih (Nat.xor (parW w) (nat_lit 1))) Tw

@[expose] noncomputable def lenW (Tw : List (List Nat)) : Nat :=
  List.rec (motive := fun _ => Nat) (nat_lit 0) (fun _ _ ih => Nat.succ ih) Tw

@[expose] noncomputable def isNilN (w : List Nat) : Bool :=
  List.rec (motive := fun _ => Bool) true (fun _ _ _ => false) w

@[expose] noncomputable def sylowK (m : Nat) (Tw : List (List Nat)) (CS : List Nat) : Bool :=
  andB (eqLN (codesK Tw) CS)
  (andB (allLL Tw fun w => allL w (qBK m))
  (andB (anyLL Tw isNilN)
  (andB (allL CS fun x => allL CS fun y => memN (mulK x y) CS)
  (andB (allLL Tw fun w => memN (wordCK (revN w)) CS)
  (andB (nodupN CS)
  (andB (Nat.beq (lenW Tw) (nat_lit 128)) (Nat.beq (cntEven Tw) (nat_lit 64))))))))

@[expose] noncomputable def invsK (CS : List Nat) : List Nat :=
  List.rec (motive := fun _ => List Nat) List.nil
    (fun x _ ih => Bool.rec (motive := fun _ => List Nat) ih (List.cons x ih) (isInvK x)) CS

@[expose] noncomputable def levelK (d : Nat) : Nat → Nat → Bool :=
  Nat.rec (motive := fun _ => Nat → Nat → Bool)
    (fun S C => allN (plCnt C) fun i => letB (plAt C i) fun x => letB (spanAdd S x) fun S' =>
      Nat.beq (plCnt (plFilterFrom C i fun y => andB (commK x y) (notB (plMem S' y)))) (nat_lit 0))
    (fun _ ih S C => allN (plCnt C) fun i => letB (plAt C i) fun x => letB (spanAdd S x) fun S' =>
      letB (plFilterFrom C i fun y => andB (commK x y) (notB (plMem S' y))) fun C' => ih S' C')
    d

@[expose] noncomputable def rankPre (CS IL : List Nat) (IP : Nat) : Bool :=
  andB (eqLN (invsK CS) IL) (andB (Nat.blt (lenN IL) 256)
  (andB (Nat.beq (plOf IL) IP)
  (allL IL fun x => allL IL fun y => impB (andB (notB (Nat.beq x y)) (commK x y))
      (memN (mulK x y) IL))))

@[expose] noncomputable def rankX (IP i : Nat) : Bool :=
  letB (plAt IP i) fun x => letB (spanAdd (plPush (nat_lit 0) oneK) x) fun S' =>
    letB (plFilterFrom IP i fun y => andB (commK x y) (notB (plMem S' y))) fun C' =>
      levelK (nat_lit 2) S' C'

@[expose] noncomputable def invParK (Tw : List (List Nat)) : List Nat :=
  List.rec (motive := fun _ => List Nat) List.nil
    (fun w _ ih => letLN (wordCK w) fun c => Bool.rec (motive := fun _ => List Nat) ih
      (List.cons (Nat.lor c (Nat.shiftLeft (parW w) (nat_lit 36))) ih) (isInvK c)) Tw

@[expose] noncomputable def e8 (E i : Nat) : Nat :=
  Nat.land (Nat.shiftRight E (Nat.mul (nat_lit 36) i)) m36

@[expose] noncomputable def mem8 (E y : Nat) : Bool :=
  letB y fun y => anyN (nat_lit 8) fun i => Nat.beq (e8 E i) y

@[expose] noncomputable def nodup8 (E : Nat) : Bool :=
  allN (nat_lit 8) fun i => allN i fun j => notB (Nat.beq (e8 E i) (e8 E j))

@[expose] noncomputable def key8 (E : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) (nat_lit 0)
    (fun i acc => Nat.add acc (Nat.mul (Nat.mul (e8 E i) (e8 E i)) (e8 E i))) (nat_lit 8)

@[expose] noncomputable def spanE (x y z : Nat) : Nat :=
  letN (mulK oneK x) fun x' => letN (mulK oneK y) fun y' => letN (mulK x' y) fun xy =>
    Nat.lor (Nat.lor (Nat.lor (Nat.shiftLeft oneK (nat_lit 252)) (Nat.shiftLeft x' (nat_lit 216)))
      (Nat.lor (Nat.shiftLeft y' (nat_lit 180)) (Nat.shiftLeft xy (nat_lit 144))))
    (Nat.lor (Nat.lor (Nat.shiftLeft (mulK oneK z) (nat_lit 108)) (Nat.shiftLeft (mulK x' z) (nat_lit 72)))
      (Nat.lor (Nat.shiftLeft (mulK y' z) (nat_lit 36)) (mulK xy z)))

@[expose] noncomputable def certOK8 (E : Nat) (k : List Nat) : Bool :=
  letB (wordCK k) fun K => letB (wordCK (revN k)) fun Ki =>
    andB (allN (nat_lit 8) fun i => letB (mulK (mulK K (e8 E i)) Ki) fun y =>
        allN (nat_lit 8) fun j => mem8 E (mulK (mulK y (e8 E j)) y))
      (anyN (nat_lit 8) fun i => notB (mem8 E (mulK (mulK K (e8 E i)) Ki)))

@[expose] noncomputable def certK (certs : List (Nat × List Nat)) (EP : List Nat) : Bool :=
  List.rec (motive := fun _ => List Nat → Bool)
    (fun EP => List.rec (motive := fun _ => Bool) true (fun _ _ _ => false) EP)
    (fun p _ ih EP => List.rec (motive := fun _ => Bool) false
      (fun E t _ => andB (nodup8 E) (andB (Prod.rec (motive := fun _ => Bool)
        (fun _ k => certOK8 E k) p) (ih t))) EP) certs EP

@[expose] noncomputable def fitK (m ev : Nat) (E : Nat) (certs : List (Nat × List Nat))
    (EP : List Nat) : Bool :=
  letB (key8 E) fun kE => List.rec (motive := fun _ => List Nat → Bool) (fun _ => false)
    (fun p _ ih EP => List.rec (motive := fun _ => Bool) false
      (fun F t _ => orB (Prod.rec (motive := fun _ => Bool) (fun key k =>
          andB (Nat.beq key kE) (andB (allL k (qBK m))
            (andB (impB (Nat.beq ev 1) (Nat.beq (parW k) 0))
              (allN (nat_lit 8) fun i => mem8 F (e8 E i))))) p)
        (ih t)) EP) certs EP

@[expose] noncomputable def wcPre (Tw : List (List Nat)) (IP : Nat) : Bool :=
  andB (Nat.blt (lenN (invParK Tw)) 256) (Nat.beq (plOf (invParK Tw)) IP)

@[expose] noncomputable def wcX (m : Nat) (IP : Nat) (certs : List (Nat × List Nat))
    (EP : List Nat) (i : Nat) : Bool :=
  letB (plAt IP i) fun x => letB (mulK oneK x) fun x' =>
    letB (plFilter IP fun y => andB (commK x y)
        (andB (notB (Nat.beq oneK y)) (notB (Nat.beq x' y)))) fun Cx =>
    allN (plCnt Cx) fun j => letB (plAt Cx j) fun y => letB (mulK oneK y) fun y' =>
      letB (mulK x' y) fun xy =>
      allN (plCnt Cx) fun l => letB (plAt Cx l) fun z =>
        impB (andB (commK y z) (andB (notB (Nat.beq oneK z)) (andB (notB (Nat.beq x' z))
            (andB (notB (Nat.beq y' z)) (notB (Nat.beq xy z))))))
          (letB (spanE x y z) fun E => andB (nodup8 E)
            (letB (Bool.rec (motive := fun _ => Nat) (nat_lit 0) (nat_lit 1)
                (Nat.beq (Nat.add (Nat.add (plPar IP i) (plPar Cx j)) (plPar Cx l)) (nat_lit 0)))
              fun ev => orB (andB (Nat.beq m (nat_lit 0)) (Nat.beq ev (nat_lit 1)))
                (fitK m ev E certs EP)))

end CFSG.KC.Misc.O62

end
