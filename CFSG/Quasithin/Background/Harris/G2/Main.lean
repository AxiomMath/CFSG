module

public import CFSG.Quasithin.Background.Harris.G2.Descent
public import CFSG.Quasithin.Background.Harris.G2.Rank
public import CFSG.Quasithin.Background.Harris.G2.Natural
public import CFSG.Quasithin.Background.Harris.G2.End

public section

namespace CFSG.Quasithin.G11.Harris.G2

open CFSG.Open CFSG.Quasithin.Explicit CFSG.Quasithin.JonesParshall
open CFSG.QuasithinUnique.Setup.SL2Modules (EndRing)


theorem oneCompFor_famG2_main : OneCompFor FamG2 := by
  rintro V _ _ _ Γ A L m hs ⟨hsimp, f, hf, hmodel⟩
  classical
  obtain ⟨-, ⟨e⟩⟩ := exists_equiv_cayley hmodel
  have hmf : m ≤ 3 * f := m_le_of_g2 hs hf e
  let _ : Fintype (GaloisField 2 f) := Fintype.ofFinite _
  have hK' : Nat.card (GaloisField 2 f) = 2 ^ f := GaloisField.card 2 f (by omega)
  have hK : Fintype.card (GaloisField 2 f) = 2 ^ f := by rw [← Nat.card_eq_fintype_card, hK']
  have : Fact (repC L e).IsIrreducible := ⟨repC_isIrreducible e hs.L_irr⟩
  have : Nontrivial ↥L := hsimp.toNontrivial
  have : Nontrivial ↥(cayleyGroup (GaloisField 2 f)) := e.injective.nontrivial
  have hb : Module.finrank (ZMod 2) V ≤ 6 * f + 2 := by
    have := hs.bound
    omega
  obtain ⟨hD, h6, φ, hφ⟩ := exists_natural_of_bound hK hf (repC L e) (repC_nontrivial L e) hb
  have hdim : Module.finrank (ZMod 2) V = 6 * f := by
    rw [finrank_eq_mul_of_card hD, h6]
    ring
  have h4 : 4 ≤ Nat.card (GaloisField 2 f) := by
    rw [hK']
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
  refine concl_of_case10 ⟨f, ⟨by omega, hdim, ?_, hmf, ?_⟩, ?_, ?_⟩
  · have := hs.bound
    omega
  · have := hsimp
    exact isG2NaturalModule_of_natural φ h4 e hφ
  · refine endIsField_of_natCard hs.L_irr ?_
    rw [natCard_endCommutant_eq L e, hD]
  · exact selfDual_of_equivariant φ (fun h => e h) (equivariant_apply φ e hφ)

end CFSG.Quasithin.G11.Harris.G2
