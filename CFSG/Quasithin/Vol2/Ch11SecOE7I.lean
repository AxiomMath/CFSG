module

public import CFSG.Quasithin.Vol2.Ch11SecOE7H
public import CFSG.Quasithin.Vol2.Ch11SecOE7A

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecE3.Lie3

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.E1 CFSG.BenderSuzuki.MatrixGroups
open CFSG.Quasithin.Vol2.Ch11.SecE3 (AlmostSimple)

variable {G : Type} [Group G] [Finite G]

theorem nParam_le_of_psu3 {T : Subgroup G} {K : Type} [Field K] [Finite K]
    (J : HermitianForm 3 K) (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0]) {f : ℕ} (hf : 2 ≤ f)
    (hcard : Nat.card K = (2 ^ f) ^ 2) (hfixed : Nat.card {x : K // J.conj x = x} = 2 ^ f)
    (h : AlmostSimple (CFSG.generalizedFitting G)) (hT : quasithinIsSylowTwo T)
    (hLT : CFSG.generalizedFitting G ⊔ T = ⊤)
    (hD : CFSG.Assembly.LowTwoRank.StatedClassicalModel ↥(CFSG.generalizedFitting G) .PSU 3 2 f)
    (e : ↥(CFSG.generalizedFitting G) ≃* ProjectiveSpecialUnitaryMatrixGroup J) :
    E1.nParam (⊤ : Subgroup G) ≤ f := by
  have hLn := h.normal
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hT' : IsSylowIn 2 T ⊤ := ⟨le_top, hT.1, by rw [Subgroup.relIndex_top_right]; exact hT.2⟩
  have hTD : T ≤ Subgroup.normalizer ((T ⊓ CFSG.generalizedFitting G : Subgroup G) : Set G) :=
    SecE3.le_normalizer_inf
  have hDs := isSolvable_normalizer_inf_psu3 J hJ hf hcard hfixed h hT e
  have hDE : InEFor f (Subgroup.normalizer
      ((T ⊓ CFSG.generalizedFitting G : Subgroup G) : Set G)) T := by
    have h1 : InE 1 (Subgroup.normalizer
        ((T ⊓ CFSG.generalizedFitting G : Subgroup G) : Set G)) :=
      (nParam_le_iff Nat.one_pos).mp (by simpa using solvable_nParam_le_one hDs)
    exact (h1 T (B6.isSylowTwoOf_mono hT' hTD le_top)).mono (by omega)
  have hInE := inEFor_top_of_conj_sup hT' hTD hDE
    (fun A _ hA1 hc => SecE3.isE_top_of_card_le h hT' hA1 hc)
    (fun A _ hA hc => exists_member_of_psu3 J hJ hf hcard hfixed h hT hLT hD e hA hc)
  exact (nParam_le_iff (by omega)).mpr ((inE_iff_inEFor hT').mpr hInE)

theorem nParam_le_of_isPSU3 {T : Subgroup G} {n : ℕ}
    (hU : IsPSU 3 2 n ↥(CFSG.generalizedFitting G))
    (hs : IsSimpleGroup ↥(CFSG.generalizedFitting G)) (hT : quasithinIsSylowTwo T)
    (hFT : CFSG.generalizedFitting G ⊔ T = ⊤) : E1.nParam (⊤ : Subgroup G) ≤ n := by
  have hn := two_le_of_isPSU hU
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hD : CFSG.Assembly.LowTwoRank.StatedClassicalModel ↥(CFSG.generalizedFitting G) .PSU 3 2
    n := hU
  obtain ⟨-, k, _, _, hk, ⟨e⟩⟩ := hU
  obtain ⟨J, hJ, -, hfix⟩ :=
    CFSG.UnitaryThreeRecognition.Model.exists_standardHermitianForm (K := k) 2 n hk
  obtain ⟨e'⟩ := CFSG.UnitaryThreeRecognition.Model.nonempty_psu_equiv_statedProj J (2 ^ n) hk hfix
  set e₁ := e.trans e'.symm with he₁
  have hnab : ∃ x y : ↥(CFSG.generalizedFitting G), x * y ≠ y * x := by
    obtain ⟨x, y, hxy⟩ := psu_nonabelian J hJ hn hk hfix
    refine ⟨e₁.symm x, e₁.symm y, fun hc => hxy ?_⟩
    simpa using congrArg e₁ hc
  exact nParam_le_of_psu3 J hJ hn hk hfix
    (SecE3.almostSimple_generalizedFitting hs hnab hT.1 hFT) hT hFT hD e₁

theorem nParam_eq_of_isPSU3 {T : Subgroup G} {n : ℕ}
    (hU : IsPSU 3 2 n ↥(CFSG.generalizedFitting G))
    (hs : IsSimpleGroup ↥(CFSG.generalizedFitting G)) (hT : quasithinIsSylowTwo T)
    (hFT : CFSG.generalizedFitting G ⊔ T = ⊤) : E1.nParam (⊤ : Subgroup G) = n :=
  le_antisymm (nParam_le_of_isPSU3 hU hs hT hFT) (le_nParam_of_isPSU3 hU hs hT hFT)

end CFSG.Quasithin.Vol2.Ch11.SecE3.Lie3
