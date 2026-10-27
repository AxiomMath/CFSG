module

public import CFSG.Quasithin.Vol2.GoldschmidtF431L3OutTransport
public import CFSG.Quasithin.Vol2.GoldschmidtF431Main

public section

namespace CFSG.Quasithin.H13.F431

open CFSG.Blueprint CFSG.Quasithin CFSG.QuasithinUnique CFSG.Open
open CFSG.Quasithin.H13.F431.L3

@[expose] def F431L3OutLie (f : ℕ) : Prop :=
  2 ≤ f → ∀ (D : Type) [Group D], LieModel D .PSL 3 2 f → ∀ A : LieAmalgamExt D,
    ¬ Odd (Nat.card ↥A.K / Nat.card D) → Nonempty (L3OutDatum A.Mb1 A.Mb2)

theorem f431Out_PSL3_of_lie {f : ℕ} (hf : 2 ≤ f) (hLie : F431L3OutLie f) :
    F431Out .PSL 3 f := by
  intro G _ _ hG hnab M1 M2 hyps D _ hD E
  by_contra heven
  obtain ⟨O⟩ := hLie hf D hD E.toLieAmalgamExt heven
  obtain ⟨Og⟩ := O.nonempty_transport E.amalgIso
  have := hG
  obtain ⟨z, hz, hz2, hzC⟩ := hyps.2.2.1 ⟨rfl, rfl⟩
  have hz' : z ∈ centerOf Og.S := by rw [Og.S_eq]; exact hz
  have hz1 : z ≠ 1 := by
    intro h; rw [h, orderOf_one] at hz2; omega
  exact Og.false_of_simple hnab hz' hz1 hzC

end CFSG.Quasithin.H13.F431
