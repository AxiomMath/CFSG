module

public import CFSG.Monster.B.TwoA.Census.PermCert
public import CFSG.Monster.CodeAut.Perm

public section

namespace CFSG.Monster.B.TwoA.Census

open CFSG.Monster.Code

@[expose] def bfsStep (act : Array ℕ → Array ℕ → Array ℕ) (gens : Array (Array ℕ)) (i : ℕ)
    (st : Array (Array ℕ) × Array ℕ × Array ℕ × Std.HashMap ℕ ℕ) :
    Array (Array ℕ) × Array ℕ × Array ℕ × Std.HashMap ℕ ℕ × Array ℕ :=
  (List.range gens.size).foldl (fun (acc : Array (Array ℕ) × Array ℕ × Array ℕ ×
      Std.HashMap ℕ ℕ × Array ℕ) k =>
    let (pts, par, lab, idx, row) := acc
    let y := act gens[k]! pts[i]!
    let ky := akey y
    match idx.get? ky with
    | some j => (pts, par, lab, idx, row.push j)
    | none => (pts.push y, par.push i, lab.push k, idx.insert ky pts.size, row.push pts.size))
    (st.1, st.2.1, st.2.2.1, st.2.2.2, #[])

@[expose] def bfsLoop (act : Array ℕ → Array ℕ → Array ℕ) (gens : Array (Array ℕ)) :
    ℕ → ℕ → Array (Array ℕ) → Array (Array ℕ) → Array ℕ → Array ℕ → Std.HashMap ℕ ℕ → TreeCert
  | 0, _, pts, edges, par, lab, _ => ⟨pts, edges, par, lab⟩
  | fuel + 1, i, pts, edges, par, lab, idx =>
    if i < pts.size then
      let (pts', par', lab', idx', row) := bfsStep act gens i (pts, par, lab, idx)
      bfsLoop act gens fuel (i + 1) pts' (edges.push row) par' lab' idx'
    else ⟨pts, edges, par, lab⟩

@[expose] def bfsCert (act : Array ℕ → Array ℕ → Array ℕ) (gens : Array (Array ℕ))
    (root : Array ℕ) (fuel : ℕ) : TreeCert :=
  bfsLoop act gens fuel 0 #[root] #[] #[0] #[0] ((∅ : Std.HashMap ℕ ℕ).insert (akey root) 0)

@[expose] def idArr : Array ℕ := ((List.range 24)).toArray

theorem PermArr_idArr : PermArr idArr = true := by decide +kernel

theorem decode_idArr : decode idArr = 1 := by
  ext i
  rw [decode_apply PermArr_idArr, idArr]
  simp

theorem coe_decode {a : Array ℕ} (h : PermArr a = true) : ⇑(decode a) = arrFun a := by
  funext i
  exact Fin.ext ((decode_apply h i).trans (arrFun_val h i).symm)

@[expose] def AutArr (a : Array ℕ) : Prop := ∀ i, B i ∘ arrFun a ∈ C ∧ B i ∘ arrFun (ainv a) ∈ C

instance (a : Array ℕ) : Decidable (AutArr a) := by
  unfold AutArr
  infer_instance

theorem mem_AutPerm_of_arr {a : Array ℕ} (h : PermArr a = true) (ha : AutArr a) :
    decode a ∈ AutPerm := by
  refine mem_AutPerm_of_basis (fun i => ?_) (fun i => ?_)
  · rw [coe_decode h]
    exact (ha i).1
  · rw [← decode_ainv h, coe_decode (PermArr_ainv h)]
    exact (ha i).2

end CFSG.Monster.B.TwoA.Census
