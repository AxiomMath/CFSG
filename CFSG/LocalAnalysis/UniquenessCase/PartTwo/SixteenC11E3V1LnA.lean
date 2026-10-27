module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC11DimD
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC11E3V1LnAA
public import CFSG.Quasithin.Background.E3MParamAttained

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
  CFSG.LocalAnalysis.WeakClosure81

variable {G : Type} [Group G] [Finite G]

section Certified


theorem s1611e3_v1_ln3_dimD {D : Data G} (h : S1611e3Std D) {V L : Subgroup G}
    {hV : IsElemAbelian 2 V} (hc : Counterex16 D ⊥ V L hV) (hs : s15 D.M ⊥ V hV L = 1)
    (hsig : D.sig = {3}) (hK : IsSym ↥(kBar D.M ⊥ V hV L) 3)
    {L₀ : Subgroup (MulAut (Vtil ⊥ V hV))}
    (hdir : IsInternalDirect (kBar D.M ⊥ V hV L) L₀ (Mbar D.M ⊥ V hV))
    (hL₀ : IsLn ↥L₀ 3 1) (hL : IsLn ↥(lBar ⊥ V hV L) 3 1)
    (hsum : SumOfNat (fun H U Z => BinaryNaturalSL H U Z 3 1) (lStar D.M ⊥ V hV L)
      (⊤ : Subgroup (vStar D.M ⊥ V hV L)) ⊥ 2)
    (hV1 : v1Sub D.M ⊥ V hV L ≠ ⊥) {J₀ : Subgroup (Vtil ⊥ V hV)}
    (hM : S16C11Model (Mbar D.M ⊥ V hV) (kBar D.M ⊥ V hV L) J₀) :
    3 ≤ mBar D.M ⊥ V hV ∧ S16C11DimD1 D ⊥ V hV ∧ S16C11DimD2 D ⊥ V hV := by
  obtain ⟨hfix, ha2, ha3⟩ := s1611e3_v1_ln3_model h hc hs hsig hK hdir hL₀ hL hsum hV1 hM
  have hKX : kBar D.M ⊥ V hV L ≤ Mbar D.M ⊥ V hV := hdir.2.2 ▸ le_sup_left
  have hKcard : Nat.card ↥(kBar D.M ⊥ V hV L) = 6 := by
    obtain ⟨e⟩ := hK
    rw [Nat.card_congr e.toEquiv, Nat.card_perm, Nat.card_fin]
    norm_num
  have hm3 : 3 ≤ mBar D.M ⊥ V hV := by
    have hXeven : Even (Nat.card ↥(Mbar D.M ⊥ V hV)) := by
      refine even_iff_two_dvd.2 ?_
      have hdvd := Subgroup.card_dvd_of_le hKX
      rw [hKcard] at hdvd
      exact dvd_trans (by norm_num : 2 ∣ 6) hdvd
    obtain ⟨t, htX, htord, htval⟩ :=
      E3.exists_involution_rkIdx_fixV_eq_mParam (Mbar D.M ⊥ V hV) hXeven
    change 3 ≤ E3.mParam (Mbar D.M ⊥ V hV)
    rw [← htval]
    exact hfix t htX htord
  refine ⟨hm3, ?_, ?_⟩
  · intro E hE _ hmE
    exact absurd (le_trans hmE (ha2 E hE)) (by omega)
  · intro E hE
    exact (ha3 E hE).elim

end Certified

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
