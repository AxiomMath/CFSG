module

public import CFSG.Quasithin.Background.GoldschmidtTDE68Wrap
public import CFSG.Quasithin.Background.GoldschmidtTDE68A6Gen

public section

namespace CFSG.Quasithin.E6.Alt

open Subgroup CFSG.Quasithin.E6.Bar CFSG.QuasithinUnique CFSG.QuasithinUnique.Ch1
  CFSG.QuasithinUnique.Unc25A6

theorem altModel_six : AltModel X0 Dsub where
  encard_le := A6.encard_invSet_le
  gen := A6.gen_six
  cases := fun _ hβ => Or.inl (A6.isSolvable_fixedSub hβ)

theorem card_X0_eq : Nat.card X0 = 8 * 45 := by
  rw [A6.card_X0]

variable {Y : Type} [Group Y] [Finite Y] {L : Subgroup Y}

theorem altRank_caseC {A R : Subgroup Y} {z : Y} (hC : Lemma115CaseC L z)
    (h : E68BaseHyp L A R) :
    (A ⊓ Subgroup.centralizer (L : Set Y)).relIndex A ≤ 4 ∧
      ((A ⊓ Subgroup.centralizer (L : Set Y)).relIndex A = 4 →
        L ≤ ⨆ (a : Y) (_ : a ∈ A ∧ a ∉ Subgroup.centralizer (L : Set Y)),
          L ⊓ Subgroup.centralizer ({a} : Set Y)) := by
  obtain ⟨φ, -, hZ, -, -⟩ := hC
  obtain ⟨ψ, -⟩ := CFSG.QuasithinUnique.DoubleA3.exists_psl_equiv
  exact altRank_of_iso altModel_six card_Dsub (by decide) card_X0_eq (φ.trans ψ.symm) hZ h

theorem false_comp_caseC {R K : Subgroup Y} {u z : Y} (hC : Lemma115CaseC L z)
    (h : E68CentHyp L R u)
    (hK : IsComponentIn K (L ⊓ Subgroup.centralizer ({u} : Set Y))) : False := by
  obtain ⟨φ, -, hZ, -, -⟩ := hC
  obtain ⟨ψ, -⟩ := CFSG.QuasithinUnique.DoubleA3.exists_psl_equiv
  exact false_of_comp_of_iso (fun _ hβ => A6.isSolvable_fixedSub hβ) card_Dsub (by decide)
    card_X0_eq (φ.trans ψ.symm) hZ h hK

end CFSG.Quasithin.E6.Alt
