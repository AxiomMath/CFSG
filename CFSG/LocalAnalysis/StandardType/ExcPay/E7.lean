module

public import CFSG.LocalAnalysis.StandardType.ExcPay.CoreE7
public import CFSG.LocalAnalysis.StandardType.ExcPay.CoverE7
public import CFSG.LocalAnalysis.StandardType.ExcPay.SquareE7

public section

namespace CFSG.StandardType.ExcPay

open CFSG.Open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.ClassicalInvolution.Phan
  CFSG.LieType.Universal CFSG.StandardType CFSG.StandardType.GGFinModel
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley


theorem exists_excPhanPayload_of_marking_E7 {G : Type} [Group G] [Finite G] {p : ℕ}
    {Bs X : Subgroup G} (hp : p.Prime) (hp3 : p ≠ 3) (hBs : IsElemAbelian p Bs)
    (hSC : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ p = 1 → g ∈ Bs)
    (hmark : GGInnerDiagOnLabel (fun p lab => ggRowP_EE7 p lab ∧ 2 ≤ lab.n) p Bs X) :
    GGExcPhanPayloadOf 7 CoxeterMatrix.E₇ .E7 p Bs X := by
  obtain ⟨f, hf, hplus, κ, hinn⟩ := exists_e7Equiv_of_marking hmark
  have hp2 : p ≠ 2 := by
    rintro rfl
    have h1 : 2 ∣ 1 := (Nat.dvd_add_right (dvd_pow_self 2 (by omega : f ≠ 0))).mp hplus
    omega
  have hp5 : 5 ≤ p := by
    have h2 := hp.two_le
    by_contra h
    interval_cases p
    · exact hp2 rfl
    · exact hp3 rfl
    · exact absurd hp (by norm_num)
  obtain ⟨S⟩ := exists_excPaySquare_E7 (ht := Or.inr (Or.inr (Or.inl rfl))) hp hp5
    (by omega) hplus hBs hSC κ hinn
  exact excPhanPayloadOf_E7_of_square hp hp2 hf hplus (isCentralQuotientOf_E7_of_equiv κ) S

end CFSG.StandardType.ExcPay
