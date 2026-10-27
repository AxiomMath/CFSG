module

public import CFSG.Quasithin.Background.SmithC27RCaseIOrd
public import CFSG.Quasithin.Background.SmithC27RTypeDefs
public import CFSG.Quasithin.Background.SmithC27RMS
public import CFSG.Quasithin.Background.SmithC27RLieClassical
public import CFSG.Quasithin.Vol2.Ch11StatementsInputsAS

public section

namespace CFSG.Quasithin.SmithC27

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin

variable {G : Type} [Group G] [Finite G] {H R M K V : Subgroup G}

theorem false_of_residueRankOne (h : Hyp27 H R M K) (hs : StarHyp R K V)
    (hJ : autOn (thompsonJ R) V ≤ autOn K V) (hnS : ¬ IsSylowTwoOf R (K ⊔ R))
    (ht : ResidueRankOne K V) : False := by
  obtain ⟨n, F, _, _, -, hF, ⟨e⟩, -⟩ := ht
  have hF' : Nat.card F = 2 ^ n := by rw [Nat.card_eq_fintype_card, hF]
  have hBT : IsRadicalParabolic (autOn K V) :=
    (isRadicalParabolic_congr (e.trans Subgroup.topEquiv.symm)).mpr
      (isRadicalParabolic_statedSL 2 hF')
  have hPB : ParabolicIsBorel (autOn K V) :=
    (parabolicIsBorel_congr (e.trans Subgroup.topEquiv.symm)).mpr
      (parabolicIsBorel_statedSL_two hF')
  obtain ⟨hP, hnB⟩ := parabolic_MK h hs hBT hJ hnS
  exact hnB (hPB _ hP (autOn_MK_ne h hs))

theorem three_of_residueRankThree (h : Hyp27 H R M K) (hs : StarHyp R K V)
    (hJ : autOn (thompsonJ R) V ≤ autOn K V) (hnS : ¬ IsSylowTwoOf R (K ⊔ R))
    (ht : ResidueRankThree K V) : C27Three H R M K V := by
  obtain ⟨d, hd, ⟨e⟩, -⟩ := ht
  have hBT : IsRadicalParabolic (autOn K V) :=
    (isRadicalParabolic_congr (e.trans Subgroup.topEquiv.symm)).mpr
      (isRadicalParabolic_statedSL d (K := ZMod 2) (a := 1) (by simp))
  obtain ⟨hP, hnB⟩ := parabolic_MK h hs hBT hJ hnS
  refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨?_, hP, hnB⟩))))))
  rcases hd with rfl | rfl
  · exact Or.inl ⟨e⟩
  · exact Or.inr ⟨e⟩

theorem maxParabolic_msPair (h : Hyp27 H R M K) (hs : StarHyp R K V)
    (hBT : IsRadicalParabolic (autOn K V)) (hMax : MaxParabolicMaximal (autOn K V))
    (hJ : autOn (thompsonJ R) V ≤ autOn K V) (hnS : ¬ IsSylowTwoOf R (K ⊔ R))
    (hr : IsRankTwoLie2Derived
      ((↥K ⧸ CFSG.pCore 2 ↥K) ⧸ Subgroup.center (↥K ⧸ CFSG.pCore 2 ↥K))) :
    IsMaxParabolic2 (autOn K V) (autOn (M ⊓ K) V) ∧
      pCoreOf 2 (autOn (M ⊓ K) V) = autOn (R ⊓ K) V ∧ IsMSPair (K ⊔ R) R := by
  obtain ⟨hmax, hO⟩ := maxParabolic_of h hs hBT hMax hJ hnS
  exact ⟨hmax, hO, isMSPair_of h hr (exists_sylow_le_normalizer_R h hs hmax.1 hO)⟩

theorem three_of_residueRankTwo_of (hC132 : ASInputs.AS_C_1_32) (h : Hyp27 H R M K)
    (hs : StarHyp R K V) (hJ : autOn (thompsonJ R) V ≤ autOn K V)
    (hnS : ¬ IsSylowTwoOf R (K ⊔ R)) (ht : ResidueRankTwo K V)
    (hr : IsRankTwoLie2Derived
      ((↥K ⧸ CFSG.pCore 2 ↥K) ⧸ Subgroup.center (↥K ⧸ CFSG.pCore 2 ↥K)))
    (hBT : IsRadicalParabolic (autOn K V)) (hMax : MaxParabolicMaximal (autOn K V))
    (hHat : IsHatA6Block K → IsHat ↥(autOn K V) ↥(alternatingGroup (Fin 6)) →
      (∃ hV : IsElemAbelian 2 V, TripleA6Six (autI hV K) (commV (autI hV K))
        (fixV (autI hV K) ⊓ commV (autI hV K))) →
      IsMaxParabolic2 (autOn K V) (autOn (M ⊓ K) V) →
      pCoreOf 2 (autOn (M ⊓ K) V) = autOn (R ⊓ K) V → C27Three H R M K V) :
    C27Three H R M K V := by
  obtain ⟨hmax, hO, hMS⟩ := maxParabolic_msPair h hs hBT hMax hJ hnS hr
  have hc := hC132 G (K ⊔ R) R K hMS h.mem_cComp_sup h.coe_sup
  have he : IsAltBlockType K 6 ∨ IsSp4Block K → C27Three H R M K V := fun hb =>
    Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨hb, hmax⟩))))
  rcases ht with ⟨n, F, iF, fF, hn, hF, ⟨e⟩, -⟩ | ⟨n, F, _, _, hn, hF, ⟨e⟩, -⟩ |
    ⟨n, F, _, _, hn, hF, ⟨e⟩, -⟩ | ⟨⟨e⟩, -⟩ | ⟨hhat, htr⟩
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
      ⟨⟨n, F, iF, fF, hn, hF, ⟨e⟩⟩, hmax, hMS⟩))))))
  · exact he (blocks_of_statedSp hs hn hF e hc)
  · exact he (blocks_of_quasithinG2 hs hn hF e hc)
  · exact he (blocks_of_alt6 h hs e hc)
  · rcases blocks_of_isHat_alt6 hs hhat hc with hb | hb
    · exact he hb
    · exact hHat hb hhat htr hmax hO

end CFSG.Quasithin.SmithC27
