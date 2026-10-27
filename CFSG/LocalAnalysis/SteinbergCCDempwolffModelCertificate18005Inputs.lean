module

public import CFSG.LocalAnalysis.SteinbergCCDempwolffBasic
public import CFSG.LocalAnalysis.SteinbergCCDempwolffData
public import Certificates.Data.CFSGNative.Th.Tables

public section

namespace CFSG.LocalAnalysis.DempwolffFive

open Matrix CFSG.Sporadic.Th.Native

@[expose] def arrFun (a : Array ℕ) (i : Fin 240) : Fin 240 :=
  ⟨a.getD i.1 0 % 240, Nat.mod_lt _ (by norm_num)⟩

@[expose] def invPerm (a : Array ℕ) (h : ∀ i, arrFun a (arrFun a i) = i) :
    Equiv.Perm (Fin 240) :=
  ⟨arrFun a, arrFun a, h, h⟩

set_option maxHeartbeats 800000 in
theorem rootPermArr_invol : ∀ k : Fin 12, ∀ i : Fin 240,
    arrFun (rootPermArr.getD k #[]) (arrFun (rootPermArr.getD k #[]) i) = i := by
  intro k
  fin_cases k <;> decide +kernel

theorem negArr_invol : ∀ i : Fin 240, arrFun negArr (arrFun negArr i) = i := by
  decide +kernel

@[expose] def gp (k : ℕ) : Equiv.Perm (Fin 240) :=
  if h : k < 12 then invPerm (rootPermArr.getD k #[]) (rootPermArr_invol ⟨k, h⟩) else 1

@[expose] def negP : Equiv.Perm (Fin 240) := invPerm negArr negArr_invol

@[expose] def blockPerm (t : ℕ) (j : Fin 31) : Equiv.Perm (Fin 240) :=
  match (blockWords.getD t #[]).getD j.1 (false, []) with
  | (s, w) => (if s then negP else 1) * (w.map gp).prod

abbrev Blk := Equiv.Perm (Fin 240)

@[expose] def ψ : G →* MulAut (Fin 31 → Blk) where
  toFun g :=
    { toFun := fun k j => k (g⁻¹ • j)
      invFun := fun k j => k (g • j)
      left_inv := fun k => funext fun j => by
        change k (g⁻¹ • g • j) = k j
        rw [inv_smul_smul]
      right_inv := fun k => funext fun j => by
        change k (g • g⁻¹ • j) = k j
        rw [smul_inv_smul]
      map_mul' := fun _ _ => rfl }
  map_one' := MulEquiv.ext fun k => funext fun j => by
    change k (1⁻¹ • j) = k j
    rw [inv_one, one_smul]
  map_mul' g h := MulEquiv.ext fun k => funext fun j => by
    change k ((g * h)⁻¹ • j) = k (h⁻¹ • (g⁻¹ • j))
    rw [_root_.mul_inv_rev, mul_smul]

abbrev M := (Fin 31 → Blk) ⋊[ψ] G

@[expose] def ψ' : Equiv.Perm (Fin 31) →* MulAut (Fin 31 → Blk) where
  toFun σ :=
    { toFun := fun k j => k (σ⁻¹ j)
      invFun := fun k j => k (σ j)
      left_inv := fun k => funext fun j => by
        change k (σ.symm (σ j)) = k j
        rw [Equiv.symm_apply_apply]
      right_inv := fun k => funext fun j => by
        change k (σ (σ.symm j)) = k j
        rw [Equiv.apply_symm_apply]
      map_mul' := fun _ _ => rfl }
  map_one' := MulEquiv.ext fun k => funext fun j => rfl
  map_mul' σ τ := MulEquiv.ext fun k => funext fun j => rfl

abbrev M' := (Fin 31 → Blk) ⋊[ψ'] Equiv.Perm (Fin 31)

@[expose] def toShadow : M →* M' :=
  SemidirectProduct.map (MonoidHom.id _) (MulAction.toPermHom G (Fin 31)) fun _ =>
    MonoidHom.ext fun _ => funext fun _ => rfl

@[expose] def liftM (s : Sym) : M :=
  if s.1 ≠ s.2.1 ∧ s.2.2 = 1 then ⟨fun j => blockPerm (symIdx s.1 s.2.1) j, xg s⟩ else 1

abbrev Pt := Fin 31 × Fin 240

@[expose] def enc (p : Pt) : ℕ := 240 * p.1.1 + p.2.1

@[expose] def dec (q : ℕ) : Pt :=
  (⟨q / 240 % 31, Nat.mod_lt _ (by norm_num)⟩, ⟨q % 240, Nat.mod_lt _ (by norm_num)⟩)

@[expose] def tabOf (x : M') : Table :=
  let r := Array.ofFn x.right
  Array.ofFn (n := 7440) fun q =>
    UInt32.ofNat (enc (r.getD (dec q.1).1.1 0, x.left (r.getD (dec q.1).1.1 0) (dec q.1).2))

@[expose] def tabInvOf (x : M') : Table :=
  let r := Array.ofFn x.right.symm
  Array.ofFn (n := 7440) fun q =>
    UInt32.ofNat (enc (r.getD (dec q.1).1.1 0, (x.left (dec q.1).1).symm (dec q.1).2))

@[expose] def signTab (v : V) : Table :=
  let sg := Array.ofFn fun j : Fin 31 => decide (formOf j ⬝ᵥ v = 1)
  Array.ofFn (n := 7440) fun q =>
    UInt32.ofNat (enc ((dec q.1).1,
      if sg.getD (dec q.1).1.1 false then negP (dec q.1).2 else (dec q.1).2))

@[expose] def symOf (t : ℕ) : Sym :=
  (⟨t / 4 % 5, Nat.mod_lt _ (by norm_num)⟩,
    ⟨if t % 4 < t / 4 % 5 then t % 4 else t % 4 + 1, by split <;> omega⟩, 1)

@[expose] def fwdTabs : Array Table :=
  Array.ofFn (n := 20) fun t => tabOf (toShadow (liftM (symOf t.1)))

@[expose] def invTabs : Array Table :=
  Array.ofFn (n := 20) fun t => tabInvOf (toShadow (liftM (symOf t.1)))

@[expose] def letterTab (l : Sym × Bool) : Table :=
  if l.1.1 ≠ l.1.2.1 ∧ l.1.2.2 = 1 then
    (bif l.2 then fwdTabs else invTabs).getD (symIdx l.1.1 l.1.2.1) #[]
  else idT 7440

@[expose] def evalTab (w : List (Sym × Bool)) : Table :=
  w.foldl (fun T l => compT 7440 T (letterTab l)) (idT 7440)

@[expose] def wordB (i j : Fin 5) (c d : ZMod 2) : List (Sym × Bool) :=
  [((i, j, c), true), ((i, j, d), true), ((i, j, c + d), false)]

@[expose] def wordC (i j k l : Fin 5) (c d : ZMod 2) : List (Sym × Bool) :=
  [((i, j, c), true), ((k, l, d), true), ((i, j, c), false), ((k, l, d), false)] ++
    (if j = k then [((i, l, c * d), false)]
      else if i = l then [((k, j, -(c * d)), false)] else [])

@[expose] def vecOf (k : ℕ) : V := fun b => if k.testBit b.1 then 1 else 0

@[expose] def signTabs : Array Table := Array.ofFn (n := 32) fun k => signTab (vecOf k.1)

@[expose] def signOK (T : Table) : Bool := signTabs.any (· == T)

end CFSG.LocalAnalysis.DempwolffFive
