module

public import Certificates.Data.E8Frame

@[expose] public section

namespace Certificates.E8FrameFast

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley.E8Frame

def reflectArr (i : Fin Tag.E8.rank) (a : Array ℤ) : Array ℤ :=
  a.modify i.val fun x => x - ∑ j : Fin Tag.E8.rank, Tag.E8.cartan i j * a.getD j.val 0

def wordActArr (ω : List (Fin Tag.E8.rank)) (a : Array ℤ) : Array ℤ :=
  ω.foldr reflectArr a

def gensCheckFast (_ : Unit := ()) : Bool :=
  frameGens.all fun g =>
    (List.finRange 16).all (fun k =>
      decide (wordActArr g.1 (Array.ofFn (frameVec k)) = Array.ofFn (frameVec (g.2.1 k)))) &&
    decide (g.2.1 * frameNeg = frameNeg * g.2.1) &&
    (List.finRange 8).all (fun i =>
      decide ((g.2.1 (Fin.castLE (by norm_num) i)).val % 8 = (g.2.2 i).val))

theorem reflectArr_ofFn (i : Fin Tag.E8.rank) (v : Fin Tag.E8.rank → ℤ) :
    reflectArr i (Array.ofFn v) = Array.ofFn (reflect Tag.E8 i v) := by
  have hget : ∀ j : Fin Tag.E8.rank, (Array.ofFn v).getD j.val 0 = v j := fun j => by
    simp [Array.getElem?_ofFn]
  refine Array.ext (by simp [reflectArr]) fun k _ _ => ?_
  simp only [reflectArr, Array.getElem_modify, Array.getElem_ofFn, hget, reflect, Pi.sub_apply,
    Pi.smul_apply, smul_eq_mul, Pi.single_apply, Fin.ext_iff]
  by_cases hik : i.val = k
  · simp [hik]
  · simp [hik, Ne.symm hik]

theorem wordActArr_ofFn (ω : List (Fin Tag.E8.rank)) (v : Fin Tag.E8.rank → ℤ) :
    wordActArr ω (Array.ofFn v) = Array.ofFn (wordAct ω v) := by
  induction ω with
  | nil => rfl
  | cons i ω ih =>
    change reflectArr i (wordActArr ω (Array.ofFn v)) = Array.ofFn (reflect Tag.E8 i (wordAct ω v))
    rw [ih, reflectArr_ofFn]

private theorem ofFn_eq_ofFn_iff {n : ℕ} (f g : Fin n → ℤ) :
    Array.ofFn f = Array.ofFn g ↔ f = g := by
  refine ⟨fun h => funext fun k => ?_, fun h => h ▸ rfl⟩
  have := congrArg (fun a : Array ℤ => a.getD k.val 0) h
  simpa [Array.getElem?_ofFn] using this

theorem gensCheck_eq_gensCheckFast : gensCheck () = gensCheckFast () := by
  simp only [gensCheck, gensCheckFast, wordActArr_ofFn, ofFn_eq_ofFn_iff]

end Certificates.E8FrameFast
