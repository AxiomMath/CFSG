
module

public import CFSG.Quasithin.Recognition.L34AmalgamIsoCertInputs
public import Certificates.Data.Kernel.WittCnt

public section

namespace CFSG.KC.L34

open CFSG.KC.Enum CFSG.KC.WCnt CFSG.Quasithin.L34Amalgam CFSG.Quasithin.Asc94

@[expose] noncomputable def pm (p q : Nat) : Nat := pcomp (nat_lit 22) (nat_lit 5) (nat_lit 31) p q

@[expose] def pI : Nat := 877989843404692497019985071278112

@[expose] noncomputable def pfold (L : Char → Nat) : List Char → Nat → Nat :=
  List.rec (motive := fun _ => Nat → Nat) (fun g => g)
    (fun c _ ih g => strictN (pm g (L c)) ih)

@[expose] noncomputable def pevT (f g : Fin 5 → Nat) : List (Fin 5 × Bool) → Nat :=
  List.rec (motive := fun _ => Nat) pI
    (fun x _ ih => strictN ih (fun h => pm (cond x.2 (f x.1) (g x.1)) h))

@[expose] noncomputable def pwtab (gT gTi : List Nat) (s : String) : Nat :=
  pevT (fun i => gT.getD i pI) (fun i => gTi.getD i pI) (word s)

@[expose] noncomputable def pwtabI (gT gTi : List Nat) (s : String) : Nat :=
  pevT (fun i => gT.getD i pI) (fun i => gTi.getD i pI) (invW (word s))

@[expose] noncomputable def pfixes (x : Nat) : Bool :=
  m22HexadL.all fun y => Nat.beq (pt x y.val) y.val

@[expose] noncomputable def ppres (x : Nat) : Bool :=
  m22HexadL.all fun y => (m22HexadL.map Fin.val).contains (pt x y.val)

@[expose] def pcandT (T₀ T₁ T₂ : Nat) : Fin 5 → Nat := fun i => [T₀, T₁, T₂].getD i pI

@[expose] noncomputable def a2CheckP (gT gTi : List Nat) : Bool :=
  decide ((a2W.map (pwtab gT gTi)).Nodup) && decide (a2W.length = 16) &&
    a2W.all fun s => lettersB s && pfixes (pwtab gT gTi s)

@[expose] noncomputable def pqCheckP (gT gTi crdT : List Nat) : Bool :=
  pfixes (gT.getD 0 pI) && !crdT.contains (gT.getD 0 pI) && crdT.contains (gT.getD 1 pI) &&
    !pfixes (gT.getD 1 pI) &&
    !ppres (pm (pm (gT.getD 3 pI) (gT.getD 0 pI)) (gTi.getD 3 pI)) &&
    !(Nat.beq (pt (pm (pm (gT.getD 4 pI) (gT.getD 1 pI)) (gTi.getD 4 pI)) 1) 1)

@[expose] noncomputable def invCheckP (gT gTi crdT : List Nat) : Bool :=
  bWords.all fun s => strictB (pwtab gT gTi s) fun T =>
    !(Nat.beq (pm T T) pI) || crdT.contains T || pfixes T

@[expose] noncomputable def conjCheckP (gT gTi : List Nat) : Bool :=
  (List.range 192).all fun i => strictB (pwtab gT gTi (bWords.getD i "")) fun T =>
    Nat.beq T pI || !(Nat.beq (pm T (pm T T)) pI) ||
      (lettersB (cjW.getD i "") &&
        strictB (pm (pm (pwtab gT gTi (cjW.getD i "")) T) (pwtabI gT gTi (cjW.getD i ""))) fun U =>
          Nat.beq U (gT.getD 2 pI) || Nat.beq U (gTi.getD 2 pI))

@[expose] noncomputable def s1CheckP (gT gTi : List Nat) : Bool :=
  s1W.all fun σ => lettersB (σ.getD 0 "") && lettersB (σ.getD 1 "") && lettersB (σ.getD 2 "") &&
    (word (σ.getD 3 "")).all (fun x => decide (x.1 ≠ 4)) && decide (σ.getD 4 "" = "") &&
    !ppres (pwtab gT gTi (σ.getD 3 "")) &&
    strictB (pwtab gT gTi (σ.getD 0 "")) fun P0 => strictB (pwtab gT gTi (σ.getD 1 "")) fun P1 =>
    strictB (pwtab gT gTi (σ.getD 2 "")) fun P2 => strictB (pwtab gT gTi (σ.getD 3 "")) fun P3 =>
    strictB (pwtab gT gTi (σ.getD 4 "")) fun P4 =>
    strictB (pwtabI gT gTi (σ.getD 0 "")) fun Q0 => strictB (pwtabI gT gTi (σ.getD 1 "")) fun Q1 =>
    strictB (pwtabI gT gTi (σ.getD 2 "")) fun Q2 => strictB (pwtabI gT gTi (σ.getD 3 "")) fun Q3 =>
    strictB (pwtabI gT gTi (σ.getD 4 "")) fun Q4 =>
    relsP1.all fun w => Nat.beq (pevT (fun i => [P0, P1, P2, P3, P4].getD i.val pI)
      (fun i => [Q0, Q1, Q2, Q3, Q4].getD i.val pI) w) pI

@[expose] noncomputable def rhCheckP (gT gTi : List Nat) : Bool :=
  rhW.all fun ρ => lettersB (ρ.getD 0 "") && lettersB (ρ.getD 1 "") && lettersB (ρ.getD 2 "") &&
    decide (ρ.getD 3 "" = "") && (word (ρ.getD 4 "")).all (fun x => decide (x.1 ≠ 3)) &&
    !(Nat.beq (pt (pwtab gT gTi (ρ.getD 4 "")) 1) 1) &&
    (relsP2.all fun w => Nat.beq (pevT (fun i => pwtab gT gTi (ρ.getD i ""))
      (fun i => pwtabI gT gTi (ρ.getD i "")) w) pI) &&
    (List.range 3).all fun x => lettersB (ρ.getD (x + 5) "") &&
      Nat.beq (pevT (fun i => pwtab gT gTi (ρ.getD i "")) (fun i => pwtabI gT gTi (ρ.getD i ""))
        (word (ρ.getD (x + 5) ""))) (gT.getD x pI)

@[expose] noncomputable def glueCheckP (gT gTi crdT : List Nat) : Bool :=
  (List.range 16).all fun i => (List.range 16).all fun j => (List.range 2).all fun e =>
    strictB (pwtab gT gTi (a2W.getD i "")) fun Tp =>
    strictB (crdT.getD j pI) fun Tq =>
    crdT.contains Tp || pfixes Tq ||
      (let w := witL.getD ((16 * i + j) * 2 + e) (0, 0)
       decide (w.1 < rhW.length) && decide (w.2 < s1W.length) &&
         (List.range 3).all fun x =>
           Nat.beq (pevT (pcandT Tp Tq (if e = 0 then gT.getD 2 pI else gTi.getD 2 pI))
               (pcandT Tp Tq (if e = 0 then gTi.getD 2 pI else gT.getD 2 pI))
               (word ((s1W.getD w.2 []).getD x "")))
             (pwtab gT gTi ((rhW.getD w.1 []).getD x "")))

end CFSG.KC.L34

end
