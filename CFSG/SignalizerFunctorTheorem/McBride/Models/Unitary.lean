module

public import CFSG.SignalizerFunctorTheorem.McBride.Models.Unitary.Structure
import CFSG.SignalizerFunctorTheorem.McBride.Models.UnitaryHeisenberg
import CFSG.SignalizerFunctorTheorem.NearModels.Unitary.Frobenius

public section

open CFSG.Open

namespace CFSG.SignalizerFunctorTheorem.McBride

open UnitaryFrame CFSG.SignalizerFunctorTheorem.NearModels

theorem exists_aut_psu3 {p : ℕ} (hp : p.Prime)
    (_hcop : Nat.Coprime p (Nat.card (PSU3 2 p))) :
    ∃ f : MulAut (PSU3 2 p), orderOf f = p := by
  obtain ⟨τ, hτ, -⟩ := UnitaryAut.exists_mulAut_frob4 hp
  exact ⟨τ, hτ⟩

theorem heisenbergInput_psu3 {p : ℕ} (hp : p.Prime) (h5 : 5 ≤ p) : HeisenbergInput p :=
  ⟨fun P hPe hPc => psu3_centralizer_eq_of_card_nine hp h5 P hPe hPc,
    fun P hPe hPc => psu3_card_normalizer_dvd hp h5 P hPe hPc,
    fun P C hPe hPc hPC hCP htrans N hN hN6 =>
      psu3_not_normalizes_coprime_six hp h5 P C hPe hPc hPC hCP htrans N hN hN6⟩

theorem frame_psu3
    {p : ℕ} (hp : p.Prime) (hcop : Nat.Coprime p (Nat.card (PSU3 2 p)))
    (hnear : signalizerNearPSolvable p (PSU3 2 p)) (f : MulAut (PSU3 2 p))
    (hf : orderOf f = p) : Frame p 3 f :=
  frame_of_heisenbergInput hp hcop hnear (heisenbergInput_psu3 hp (five_le_of_coprime hp hcop)) f
    hf

theorem isCoatom_fixedNormalizer_psu3
    {p : ℕ} (hp : p.Prime)
    (hcop : Nat.Coprime p (Nat.card (PSU3 2 p)))
    (hnear : signalizerNearPSolvable p (PSU3 2 p)) (f : MulAut (PSU3 2 p)) (hf : orderOf f = p) :
    IsCoatom (fixedNormalizer f) :=
  isCoatom_fixedNormalizer_of_heisenbergInput hp hcop hnear
    (heisenbergInput_psu3 hp (five_le_of_coprime hp hcop)) f hf

theorem fixedNormalizer_psu3 {p : ℕ} (hp : p.Prime)
    (hcop : Nat.Coprime p (Nat.card (PSU3 2 p))) (f : MulAut (PSU3 2 p)) (hf : orderOf f = p) :
    fixedNormalizer f = signalizerFixedSubgroup f :=
  fixedNormalizer_eq_of_heisenbergInput hp hcop
    (heisenbergInput_psu3 hp (five_le_of_coprime hp hcop)) f hf

end CFSG.SignalizerFunctorTheorem.McBride
