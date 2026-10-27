module

public import CFSG.RankThree.GF2n.Tim81.Cited.Sec7
import CFSG.LieType.Universal.Unitary.SUThreeModuleBound

public section

namespace CFSG.RankThree.GF2n.Tim81

open CFSG.LieType.Universal.Unitary

theorem su3ModuleBound : SU3ModuleBound := by
  intro K _ _ X₀ Δ f hf hf2 hSU W _ _ _ ρ hρ _
  obtain ⟨Φ, -, hrange, -⟩ := hSU
  have hF : Nat.card (GaloisField 2 (2 * f)) = (2 ^ f) ^ 2 :=
    CFSG.Timmesfeld.Transvection.card_galoisField_two_mul hf
  have hne : ρ.comp Φ ≠ 1 := by
    intro h
    obtain ⟨x, hx, w, hw⟩ := hρ
    rw [← hrange] at hx
    obtain ⟨y, rfl⟩ := MonoidHom.mem_range.mp hx
    have h1 : (ρ.comp Φ) y w = w := by
      have := congrArg (fun ψ => ψ y w) h
      simpa using this
    exact hw h1
  exact pow_six_le_natCard_of_SU_three hF hf2 (ρ.comp Φ) hne
