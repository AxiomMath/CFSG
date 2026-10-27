module

public import CFSG.Quasithin.Background.Harris.Ln2.NoFormNat
public import CFSG.Quasithin.Background.JonesParshallWedge

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Quasithin.G11.Harris.Ln2

open Matrix CFSG.Quasithin.JonesParshall

@[expose] def tw (s : Fin 4) : Matrix (Fin 10) (Fin 10) (ZMod 2) := wedgeMat (tv s)

theorem tw_mul_self : ∀ s : Fin 4, tw s * tw s = 1 := by
  decide +kernel

theorem tw_entries : ∀ (s : Fin 4) (q : Fin 6) (p : Fin 10),
    tw s (Fin.natAdd 4 q) p = if Fin.natAdd 4 q = p then 1 else 0 := by
  decide +kernel

theorem tw_fixed : ∀ x : Fin 10 → ZMod 2, (∀ s : Fin 4, tw s *ᵥ x = x) → ∀ q : Fin 10, 4 ≤ q.val → x q = 0 := by
  decide +kernel

theorem tw_row {s : Fin 4} {q : Fin 10} (hq : 4 ≤ q.val) :
    tw s q = (1 : Matrix (Fin 10) (Fin 10) (ZMod 2)) q := by
  obtain ⟨r, rfl⟩ : ∃ r : Fin 6, q = Fin.natAdd 4 r := ⟨⟨q.val - 4, by omega⟩, Fin.ext (by simp; omega)⟩
  funext p
  rw [tw_entries, Matrix.one_apply]

theorem no_form_wedge (f : LinearMap.BilinForm (ZMod 2) (Fin 10 → ZMod 2)) (hf : f.Nondegenerate)
    (hinv : ∀ s x y, f (tw s *ᵥ x) (tw s *ᵥ y) = f x y) : False := by
  refine no_form (c := 4) tw (fun s y => ⟨tw s *ᵥ y, ?_⟩)
    (Finset.univ.filter fun q : Fin 10 => q.val < 4) ?_ ?_ ?_ f hf hinv
  · rw [mulVec_mulVec, tw_mul_self, one_mulVec]
  · intro s v q hq
    have hq' : 4 ≤ q.val := by simpa using hq
    show tw s q ⬝ᵥ v - v q = 0
    rw [tw_row hq', ← mulVec, one_mulVec, sub_self]
  · refine le_trans (Nat.card_le_card_of_injective
      (fun x => fun i : Fin 4 => x.1 (Fin.castLE (by omega) i)) fun a b h => ?_) (by simp)
    refine Subtype.ext (funext fun q => ?_)
    by_cases hq : q.val < 4
    · exact congr_fun h ⟨q.val, hq⟩
    · rw [tw_fixed a.1 a.2 q (by omega), tw_fixed b.1 b.2 q (by omega)]
  · decide +kernel

end CFSG.Quasithin.G11.Harris.Ln2
