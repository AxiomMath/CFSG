module

public import CFSG.Blueprint.NativeSporadic
public import TauCeti.GroupTheory.SpecificGroups.CFSG.Sporadic.Suzuki
public import Certificates.Data.Kernel.Spor.SuzBridge

public section

namespace CFSG.Sporadic.Bridge.SuzMats

open CFSG.KD.SuzB

abbrev Mat64 : Type := Matrix (Fin 64) (Fin 64) (ZMod 3)

noncomputable abbrev mA : Mat64 :=
  Blueprint.NativeSporadic.decode 3 64 1 Blueprint.NativeSporadic.SuzSeed1

noncomputable abbrev mB : Mat64 :=
  Blueprint.NativeSporadic.decode 3 64 1 Blueprint.NativeSporadic.SuzSeed2

@[expose] noncomputable def wordM (G : ℕ → Mat64) (w : List (ℕ × Bool)) : Mat64 :=
  (w.map fun l => if l.2 then G l.1 else (G l.1)⁻¹).prod

theorem wordM_append (G : ℕ → Mat64) (u w : List (ℕ × Bool)) :
    wordM G (u ++ w) = wordM G u * wordM G w := by
  simp [wordM]

theorem wordM_inv_letter (G : ℕ → Mat64) (g : ℕ) : wordM G [(g, false)] = (G g)⁻¹ := by
  simp [wordM]

theorem wordM_shiftW (G : ℕ → Mat64) (k : ℕ) (w : List (ℕ × Bool)) :
    wordM G (shiftW k w) = wordM (fun g => G (g + k)) w := by
  simp [wordM, shiftW, Function.comp_def]

theorem wordM_congr {G G' : ℕ → Mat64} {w : List (ℕ × Bool)} (h : ∀ x ∈ w, G x.1 = G' x.1) :
    wordM G w = wordM G' w := by
  unfold wordM
  exact congrArg List.prod (List.map_congr_left fun x hx => by rw [h x hx])

@[expose] noncomputable def seeds (i : ℕ) : Mat64 := if i = 0 then mA else mB

@[expose] noncomputable def img (k : ℕ) : Mat64 := wordM seeds (wordAt imgWords k)

structure Facts : Prop where
  rels : ∀ v ∈ TauCeti.Sporadic.suzPresentation.relatorLetters, wordM img v = 1
  surjA : wordM img (wordAt surjWords 0) = mA
  surjB : wordM img (wordAt surjWords 1) = mB

end CFSG.Sporadic.Bridge.SuzMats

end
