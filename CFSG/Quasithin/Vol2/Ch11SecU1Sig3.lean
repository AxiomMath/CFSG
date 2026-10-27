module

public import CFSG.Quasithin.Vol2.Ch11SecU1Sig1
public import CFSG.Quasithin.Vol2.Ch11SecU1Sig2
public import CFSG.LocalAnalysis.ComponentClassification.AutL2FactsHilbert90

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecU1

open CFSG.Open CFSG.Quasithin CFSG.GorensteinWalter CFSG.ComponentClassification.AutL2Facts

theorem sigmaPGammaL2_holds :
    ∀ (K : Type) [Field K] [Finite K] (p : ℕ), p.Prime → 5 ≤ p → Nat.card K = p ^ 2 →
      ∀ v : GorensteinWalter.PGammaL2 K, orderOf v = 2 → v.right ≠ 1 →
        SigmaFacts (GorensteinWalter.pGammaL2PSLRange K) v := by
  intro K _ _ p hp hp5 hK v hv hvr
  have hodd : IsOddPrimePower (Nat.card K) :=
    ⟨p, 2, hp, hp.odd_of_ne_two (by omega), by norm_num, hK⟩
  have : (pGammaL2PSLRange K).Normal := pGammaL2PSLRange_normal K hodd (by rw [hK]; nlinarith)
  obtain ⟨C, hC⟩ := exists_conj_inr_of_involution hodd v hv hvr
  have hσ : orderOf v.right = 2 := by
    have h2 : v ^ 2 = 1 := orderOf_dvd_iff_pow_eq_one.mp (by rw [hv])
    have h3 : v.right ^ 2 = 1 := by
      have h := map_pow (SemidirectProduct.rightHom (φ := pgl2FieldAut K)) v 2
      rw [h2, map_one, SemidirectProduct.rightHom_eq_right] at h
      exact h.symm
    exact orderOf_eq_prime h3 hvr
  have h := Sig.sigmaFacts_conj (Sig.sigmaFacts_inr hp hp5 hK hσ) (SemidirectProduct.inl C)
  rwa [← hC, show SemidirectProduct.inl C * ((SemidirectProduct.inl C)⁻¹ * v *
      SemidirectProduct.inl C) * (SemidirectProduct.inl C)⁻¹ = v by group] at h

end CFSG.Quasithin.Vol2.Ch11.SecU1
