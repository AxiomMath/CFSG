module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightKCtx
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenL3Wr
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenSixPrime
import CFSG.Quasithin.Background.HL3WrNPrime

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Quasithin.H CFSG.Quasithin.H.L3Wr CFSG.Quasithin.H13 CFSG.Open Subgroup
  CFSG.LocalAnalysis.UniquenessCase.UC22

variable {G : Type} [Group G] [Finite G] {D : Data G} {V₀ V L : Subgroup G}
  {hV : IsElemAbelian 2 V}

private theorem s16k_card_dvd_of_realizes {A : Subgroup (MulAut (Vtil V₀ V hV))}
    (hT : (tensorPairModel SL32 SL32).RealizesMod A)
    (hnorm : Mbar D.M V₀ V hV ≤ normalizer (A : Set (MulAut (Vtil V₀ V hV)))) :
    Nat.card (Mbar D.M V₀ V hV) ∣ 2 * 168 ^ 2 := by
  obtain ⟨e, he⟩ := CFSG.Quasithin.H.L3Wr.exists_model hT
  have h2 : (Mbar D.M V₀ V hV).map (CFSG.Quasithin.H.congrHom e) ≤
      CFSG.Quasithin.H.L3Wr.norm := by
    have h3 : (Subgroup.normalizer (A : Set (MulAut (Vtil V₀ V hV)))).map
        (CFSG.Quasithin.H.congrHom e) =
        Subgroup.normalizer (A.map (CFSG.Quasithin.H.congrHom e)) :=
      Subgroup.map_equiv_normalizer_eq A (MulAut.congr e)
    have h4 := (Subgroup.map_mono (f := CFSG.Quasithin.H.congrHom e) hnorm).trans
      (le_of_eq h3)
    have h5 := congrArg (fun P : Subgroup (MulAut CFSG.Quasithin.H.L3Wr.WMod) =>
      Subgroup.normalizer (P : Set (MulAut CFSG.Quasithin.H.L3Wr.WMod))) he
    exact h4.trans (le_of_eq h5)
  have hd : Nat.card (Mbar D.M V₀ V hV) ∣ Nat.card CFSG.Quasithin.H.L3Wr.norm := by
    rw [← CFSG.Quasithin.H.card_map_congrHom e (Mbar D.M V₀ V hV)]
    exact Subgroup.card_dvd_of_le h2
  rwa [CFSG.Quasithin.H.L3Wr.card_norm] at hd

theorem s16k_card_mbar_dvd_of_tensor_l3 (h : S16kBase D V₀ V L hV)
    (hT : NatTensor (lBar V₀ V hV L) (commSub ⊤ (lBar V₀ V hV L)) ⊥ 3 1) :
    Nat.card (Mbar D.M V₀ V hV) ∣ 2 * 168 ^ 2 := by
  rw [h.comm_top] at hT
  obtain ⟨K, _, _, hK, hmodel⟩ := hT
  have hK2 : Nat.card K = 2 := by simpa using hK
  have hreal : (tensorPairModel SL32 SL32).RealizesMod (lBar V₀ V hV L) :=
    tensorNat_realizes_zmod_two hK2 hmodel
  exact s16k_card_dvd_of_realizes hreal h.mBar_le_normalizer

theorem s16k_false_of_tensor_l3 (h : S16kBase D V₀ V L hV)
    (hT : NatTensor (lBar V₀ V hV L) (commSub ⊤ (lBar V₀ V hV L)) ⊥ 3 1) : False := by
  obtain ⟨p, hpσ⟩ := h.exists_sig
  obtain ⟨hpp, hp2⟩ := D.sig_prime p hpσ
  have h3 := h.three_le_pRank hpσ
  haveI : Finite (MulAut (Vtil V₀ V hV)) := MulEquiv.finite_left
  obtain ⟨E, hEM, -, hEcard⟩ :=
    c23_exists_elemAbelian_card_pow (G := MulAut (Vtil V₀ V hV)) (M := Mbar D.M V₀ V hV)
      (k := 3) hpp (by rw [UC6.groupPRank_eq_pRank]; exact h3)
  have hdvd : p ^ 3 ∣ 2 * 168 ^ 2 := by
    rw [← hEcard]
    exact (Subgroup.card_dvd_of_le hEM).trans (s16k_card_mbar_dvd_of_tensor_l3 h hT)
  exact s15_Six_not_pow_three_dvd hpp hp2 hdvd

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
