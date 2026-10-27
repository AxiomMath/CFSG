module

public import CFSG.Quasithin.Background.Harris.G2.U33Module
public import CFSG.Quasithin.Background.Harris.G2.U33Rank
public import CFSG.Quasithin.Background.Harris.G2.U33End
public import CFSG.Quasithin.Background.Harris.G2.Natural

public section

namespace CFSG.Quasithin.G11.Harris.G2

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.Explicit CFSG.Quasithin.JonesParshall


theorem oneCompFor_famU33_main : OneCompFor FamU33 := by
  rintro V _ _ _ Γ A L m hs ⟨hsimp, hmodel⟩
  classical
  have hP : B42TypeU33 ↥L := b42TypeU33_of_simple hsimp hmodel
  obtain ⟨θ⟩ := B42U33.nonempty_equiv_g2Derived hP
  have hm3 : m ≤ 3 := m_le_three_u33 hs θ
  have hb := hs.bound
  have hdim : Module.finrank (ZMod 2) V = 6 :=
    finrank_eq_six_of_u33 hsimp hmodel hs.L_irr (by omega)
  obtain ⟨K, _, _, _, hK2, φ, e, hφ⟩ := u33_natural_coords hsimp hmodel hdim
  let _ : Fintype K := Fintype.ofFinite K
  let _ : Fintype (GaloisField 2 1) := Fintype.ofFinite _
  have hcard : Fintype.card K = Fintype.card (GaloisField 2 1) := by
    rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, hK2,
      GaloisField.card 2 1 (by norm_num)]
    norm_num
  obtain ⟨e', φ', hφ'⟩ := natural_transport (FiniteField.ringEquivOfCardEq hcard) e φ hφ
  refine concl_of_case10 ⟨1, ⟨le_rfl, by omega, by omega, by omega, ?_⟩, ?_, ?_⟩
  · exact isG2NaturalModule_of_equivariant φ' (derived_le_cayley _) e' hφ'
  · exact endIsField_u33 hsimp hmodel hs.L_irr hdim
  · exact selfDual_of_equivariant φ' (fun h => ⟨(e' h : quasithinZorn (GaloisField 2 1) ≃ₗ[GaloisField 2 1]
      quasithinZorn (GaloisField 2 1)), derived_le_cayley _ (e' h).2⟩) hφ'

end CFSG.Quasithin.G11.Harris.G2
