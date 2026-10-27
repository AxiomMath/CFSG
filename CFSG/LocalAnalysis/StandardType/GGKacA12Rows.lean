module

public import CFSG.LocalAnalysis.StandardType.GGKacExcB2

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

theorem ggKacValid_a12_nonqs_unique {lab : LargeEvenLabel} {p : ℕ} (hn : 1 ≤ lab.n)
    (hp : p.Prime) (hd : p ∣ 2 ^ lab.n - 1 ∨ p ∣ 2 ^ lab.n + 1) {D : GGKacDatum}
    (hD : GGKacValid lab p D) (i j : Fin D.orbits.length)
    (hi : D.orbits[i].lab = ⟨.A, 1, 1⟩ ∧ D.orbits[i].qs = false)
    (hj : D.orbits[j].qs = false) : i = j := by
  obtain ⟨hn1, hp3⟩ := ggKacValid_qs_false_p3 hn hp hd hD (List.getElem_mem i.2) hi.2
  obtain ⟨T, tw, -, hT⟩ := hD
  rw [hn1, hp3] at hT
  have key : ∀ (T : GGKacType) (tw : Bool), ∀ D ∈ ggKacTable T tw 3 1,
      D.orbits.Pairwise (fun a b =>
        ¬ (((a.lab.tag = .A ∧ a.lab.rank = 1 ∧ a.lab.n = 1) ∧ a.qs = false) ∧ b.qs = false) ∧
          ¬ (a.qs = false ∧ ((b.lab.tag = .A ∧ b.lab.rank = 1 ∧ b.lab.n = 1) ∧ b.qs = false))) := by
    intro T tw
    cases T <;> cases tw <;> decide +kernel
  have hpw := List.pairwise_iff_getElem.mp (key T tw D hT)
  have hi' : (D.orbits[i].lab.tag = .A ∧ D.orbits[i].lab.rank = 1 ∧ D.orbits[i].lab.n = 1) ∧
      D.orbits[i].qs = false := by
    rw [hi.1]; exact ⟨⟨rfl, rfl, rfl⟩, hi.2⟩
  by_contra hne
  rcases lt_or_gt_of_ne (fun h => hne (Fin.ext h) : i.1 ≠ j.1) with hlt | hlt
  · exact (hpw i.1 j.1 i.2 j.2 hlt).1 ⟨hi', hj⟩
  · exact (hpw j.1 i.1 j.2 i.2 hlt).2 ⟨hj, hi'⟩

theorem ggKacValid_a12_tag {lab : LargeEvenLabel} {p : ℕ} (hn : 1 ≤ lab.n)
    (hp : p.Prime) (hd : p ∣ 2 ^ lab.n - 1 ∨ p ∣ 2 ^ lab.n + 1) {D : GGKacDatum}
    (hD : GGKacValid lab p D) (i : Fin D.orbits.length)
    (hi : D.orbits[i].lab = ⟨.A, 1, 1⟩ ∧ D.orbits[i].qs = false) :
    lab.n = 1 ∧ p = 3 ∧ (lab.tag = .E7 ∨ lab.tag = .twE6) := by
  obtain ⟨hn1, hp3⟩ := ggKacValid_qs_false_p3 hn hp hd hD (List.getElem_mem i.2) hi.2
  refine ⟨hn1, hp3, ?_⟩
  obtain ⟨T, tw, hTl, hT⟩ := hD
  rw [hn1, hp3] at hT
  have ho : ∃ o ∈ D.orbits, (o.lab.tag = .A ∧ o.lab.rank = 1 ∧ o.lab.n = 1) ∧ o.qs = false := by
    refine ⟨D.orbits[i], List.getElem_mem i.2, ?_, hi.2⟩
    rw [hi.1]; exact ⟨rfl, rfl, rfl⟩
  have key : ∀ D ∈ ggKacTable .E6 false 3 1 ++ ggKacTable .E8 false 3 1 ++
      ggKacTable .F4 false 3 1,
      ¬ ∃ o ∈ D.orbits, (o.lab.tag = .A ∧ o.lab.rank = 1 ∧ o.lab.n = 1) ∧ o.qs = false := by
    decide +kernel
  obtain ⟨t, l, n⟩ := lab
  cases t <;> simp only [ggKacTypeOfLabel] at hTl <;> cases hTl <;>
    first
    | exact Or.inl rfl
    | exact Or.inr rfl
    | exact absurd ho (key D (by simp [hT]))

end CFSG.StandardType
