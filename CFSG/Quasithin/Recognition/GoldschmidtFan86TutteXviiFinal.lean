module

public import CFSG.Quasithin.Recognition.GoldschmidtFan86TutteXviiMain
public import CFSG.Quasithin.Recognition.GoldschmidtFan86TutteCalcXi

public section

namespace CFSG.Quasithin.Fan86.Tutte

variable {H : Type*} [Group H] {s : ℕ} {r l ξ : H} {Hs : ℕ → Subgroup H}

theorem xviiInput (h : IsTutteSys s r l ξ Hs) : Xvii.XviiInput s r l Hs where
  abel_sq_eq_one := fun hi hab hk hki => abel_sq_eq_one h hi hab hk hki
  abelian_iff := fun hi his => abelian_iff h hi his
  pset_mul := fun hi hab => pset_mul h hi hab
  sq_support := fun hi his hab => sq_support h hi his hab

theorem abel_of_le_two_thirds (h : IsTutteSys s r l ξ Hs) {k : ℕ} (hk : k < s)
    (h3 : 3 * k ≤ 2 * s) : Abel Hs k :=
  Xvii.abel_of_le_two_thirds_of_input h (xviiInput h) hk h3

end CFSG.Quasithin.Fan86.Tutte
