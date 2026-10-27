module

public import CFSG.Quasithin.Recognition.Stroth.Str83G3Frame2
public import CFSG.Quasithin.Recognition.Stroth.Str83G3Tools2
public import CFSG.Quasithin.Vol2.Ch3g316Red
public import CFSG.Quasithin.Recognition.Stroth.Str83G3Tools

public section

namespace CFSG.Quasithin.Stroth

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Quasithin.F112R
open scoped MatrixGroups

variable {G : Type} [Group G] [Finite G]

theorem str83_natural_bottom_of_not_le_q2
    {L1 L2 S : Subgroup G} {a : ℕ} (hF : F112HypW L1 L2 S)
    (hB : bigB L1 L2 S ≤ Subgroup.normalizer (S : Set G)) (ha : 1 ≤ a)
    (hSz : Nonempty (oTwoQuot ↥L1 ≃* Sz a))
    (hL2 : IsL2Quot (2 * a + 1) (oTwoQuot ↥L2))
    (hZI : L1 ⊔ Q1 L1 L2 S ≤ Subgroup.centralizer (Z1 L1 L2 S : Set G))
    (hJ2 : ¬ thompsonJ S ≤ Q2 L1 L2 S)
    {Y : Subgroup G} (hYZ : Y ≤ Z2 L1 L2 S) (hYH : Y ≤ L2 ⊔ S) (hV : IsElemAbelian 2 Y)
    (hstep : IsChiefStep (L2 ⊔ S) Y ⊥ Y) :
    let hE := CFSG.Quasithin.isElemAbelian_chiefMod hstep hYH hV.isPGroup
    letI _cg : CommGroup ↥(Ch3z.chiefMod ⊥ Y) := l2ChiefSectionCommGroup hE
    letI _mod : Module (ZMod 2) (Additive (Ch3z.chiefMod ⊥ Y)) := l2ChiefSectionModule hE
    ∃ (e : oTwoQuot ↥(L2 ⊔ S) ≃* SL(2, GaloisField 2 (2 * a + 1)))
      (ρ : Representation (ZMod 2) SL(2, GaloisField 2 (2 * a + 1))
        (Additive (Ch3z.chiefMod ⊥ Y)))
      (φ : Additive (Ch3z.chiefMod ⊥ Y) ≃+ (Fin 2 → GaloisField 2 (2 * a + 1))),
      (∀ (h : ↥(L2 ⊔ S)) (w : Ch3z.chiefMod ⊥ Y),
        ρ (e (QuotientGroup.mk h)) (Additive.ofMul w) =
          Additive.ofMul (l2ChiefSectionAction hstep hE h w)) ∧
      (∀ g w, φ (ρ g w) =
        (g : Matrix (Fin 2) (Fin 2) (GaloisField 2 (2 * a + 1))).mulVec (φ w)) := by
  classical
  have hm2 : 2 ≤ 2 * a + 1 := by omega
  have hS2 : S = (S ⊓ L2) ⊔ Q2 L1 L2 S :=
    eq_sup_pCoreOf_of_bender_right hF.1 hB
      (Or.inr (Or.inr ⟨2 * a + 1, by omega, hL2⟩))
  have hQ2S : Q2 L1 L2 S ≤ S := by
    conv_rhs => rw [hS2]
    exact le_sup_right
  have hsup2 : L2 ⊔ S = L2 ⊔ Q2 L1 L2 S := by
    have h1 : L2 ⊔ S = L2 ⊔ ((S ⊓ L2) ⊔ Q2 L1 L2 S) :=
      congrArg (fun X => L2 ⊔ X) hS2
    rw [h1, ← sup_assoc, show L2 ⊔ (S ⊓ L2) = L2 from sup_eq_left.mpr inf_le_right]
  have hpCore2 : pCoreOf 2 (L2 ⊔ S) = Q2 L1 L2 S := by
    rw [hsup2]
    have h := pCoreOf_sup_pCoreOf (L1 := L2) (L2 := L1) (S := S) hF.1.symm
    simpa [Q1, Q2, P1, P2, bigB_comm] using h
  have hL2sup : IsL2Quot (2 * a + 1) (oTwoQuot ↥(L2 ⊔ S)) := by
    have hsupQ : L2 ⊔ S = L2 ⊔ Q1 L2 L1 S := by
      rw [hsup2]
      simp [Q1, Q2, P1, P2, bigB_comm]
    rw [hsupQ]
    obtain ⟨eL⟩ := hL2
    exact ⟨(oTwoQuotSupEquiv hF.1.symm).trans eL⟩
  obtain ⟨A, hAmax, hAQ2⟩ :=
    CFSG.Quasithin.Ch3g316.exists_isMaxElemAbelian_not_le_pCoreOf
      (T := S) (Q := Q2 L1 L2 S) hJ2
  have hYQ2 : Y ≤ Q2 L1 L2 S := hYZ.trans (A4.omegaOneCenterOf_le (Q2 L1 L2 S))
  have hYc : Y ≤ Subgroup.centralizer (Q2 L1 L2 S : Set G) :=
    hYZ.trans ((A4.omegaOneCenterOf_le_centerOf (Q2 L1 L2 S)).trans
      (A4.centerOf_le_centralizer (Q2 L1 L2 S)))
  have hcomm : ⁅Y, A ⊓ Q2 L1 L2 S⁆ = ⊥ :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.mpr
      (hYc.trans (Subgroup.centralizer_le inf_le_right))
  have hTR := thompsonReplacement (R := Q2 L1 L2 S) (S := S) (V := Y) (A := A)
    hQ2S hYQ2 hV hAmax hcomm
  have hbound : (Y ⊓ Subgroup.centralizer (A : Set G)).relIndex Y ≤
      (A ⊓ pCoreOf 2 (L2 ⊔ S)).relIndex A := by
    rw [hpCore2]
    exact hTR.1.trans hTR.2.1
  have hstepZ : IsChiefStep (L2 ⊔ S) (Z2 L1 L2 S) ⊥ Y :=
    ⟨⟨hYZ, hstep.1.2⟩, ⟨bot_le, hstep.2.1.2⟩, hstep.2.2.1,
      fun K hK _ hKY => hstep.2.2.2 K ⟨hKY, hK.2⟩ bot_le hKY⟩
  have hnc : ¬ IsCentralStep (L2 ⊔ S) ⊥ Y :=
    not_isCentralStep_bot_of_caseI hF hB ha hSz hL2 hZI hstepZ
  have hser : IsChiefSeriesFrom (L2 ⊔ S) Y Y 1 :=
    IsChiefSeriesFrom.noncentral hstep hnc IsChiefSeriesFrom.bot
  obtain ⟨L, N, hstep', _hnc', hAeq, _hVeq, hstepeq⟩ :=
    lemmaFF2_one_numeric (H := L2 ⊔ S) (V := Y) (A := A) (m := 2 * a + 1)
      hm2 hL2sup hV hYH hAmax.2.1 (hAmax.1.trans le_sup_right)
      (by rw [hpCore2]; exact hAQ2) hbound hser
  have hLbot : L = ⊥ := by
    rcases hstep.2.2.2 L hstep'.2.1 bot_le hstep'.2.1.1 with h | h
    · exact h
    · have hNL : N ≤ L := by rw [h]; exact hstep'.1.1
      exact absurd hstep'.2.2.1 (not_lt_of_ge hNL)
  have hNY : N = Y := by
    rcases hstep.2.2.2 N hstep'.1 bot_le hstep'.1.1 with h | h
    · rw [h] at hstep'
      exact absurd hstep'.2.2.1 (not_lt_of_ge bot_le)
    · exact h
  rw [hLbot, hNY] at hstepeq
  obtain ⟨e, ρ, φ, -, -, hcompat, hφnat, -⟩ :=
    l2_chiefStep_natural (H := L2 ⊔ S) (V := Y) (L := ⊥) (N := Y) (A := A)
      (m := 2 * a + 1) hm2 hL2sup hV hYH hstep hnc hAmax.2.1
      (hAmax.1.trans le_sup_right) hstepeq hAeq
  exact ⟨e, ρ, φ, hcompat, hφnat⟩

end CFSG.Quasithin.Stroth

end
