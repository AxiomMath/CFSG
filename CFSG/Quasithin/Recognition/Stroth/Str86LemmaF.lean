module

public import CFSG.Quasithin.Recognition.Stroth.Str86ZTwoOrth2
public import CFSG.Quasithin.Recognition.Stroth.BenderCaseIIFacts
public import CFSG.GroupTheory.ChiefSectionPGroup

public section

namespace CFSG.Quasithin.Stroth

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Quasithin.F112R
open CFSG.LieType.BorelTits
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

private theorem lemmaF_S_factor {L1 L2 S : Subgroup G}
    (hF : F112Hyp L1 L2 S) (hSB : bigB L1 L2 S ≤ Subgroup.normalizer (S : Set G))
    (hB2 : VBig L2) (h2 : VL2 L2) :
    S = (S ⊓ L2) ⊔ Q2 L1 L2 S := by
  obtain ⟨n, hL2⟩ := h2
  have hn : 2 ≤ n := two_le_of_isL2Quot_of_vBig hF.1.h2.listed hB2 hL2
  exact eq_sup_pCoreOf_of_bender_right hF.1 hSB (Or.inr (Or.inr ⟨n, hn, hL2⟩))

private theorem lemmaF_oTwoUpper_le_of_not_le {L1 L2 S K : Subgroup G}
    (hF : F112Hyp L1 L2 S) {n : ℕ} (hn : 2 ≤ n) (hL2 : IsL2Quot n (oTwoQuot ↥L2))
    (hK : K ≤ u3H L1 L2 S) (hKn : u3H L1 L2 S ≤ Subgroup.normalizer (K : Set G))
    (hKQ : ¬ K ≤ Q2 L1 L2 S) : oTwoUpper (u3H L1 L2 S) ≤ K := by
  have hQ2H : Q2 L1 L2 S ≤ u3H L1 L2 S := q2_le_u3H L1 L2 S
  have hK'le : K ⊔ Q2 L1 L2 S ≤ u3H L1 L2 S := sup_le hK hQ2H
  have hHK' : u3H L1 L2 S ≤
      Subgroup.normalizer ((K ⊔ Q2 L1 L2 S : Subgroup G) : Set G) :=
    D14.le_normalizer_sup hKn
      ((u3H_le_p2 L1 L2 S).trans (le_normalizer_pCoreOf 2 (P2 L1 L2 S)))
  rcases eq_or_eq_sup_of_normal_of_isL2Quot hF.toW hn hL2 hK'le hHK' le_sup_right with h | h
  · exact absurd (h ▸ le_sup_left) hKQ
  · exact CFSG.Quasithin.Vol2.Ch11.SecD.oTwoUpper_le_of_le_sup'
      (X := u3H L1 L2 S) (Y := K) (T := Q2 L1 L2 S) (le_of_eq h.symm)
      (pCoreOf_isPGroup 2 (P2 L1 L2 S)) (hQ2H.trans hKn)

private theorem lemmaF_double_commutator_eq_bot {L1 L2 S F : Subgroup G}
    (hFQ : F ≤ Q2 L1 L2 S) (hFn : P2 L1 L2 S ≤ Subgroup.normalizer (F : Set G))
    (h : ⁅⁅F, oTwoUpper (u3H L1 L2 S)⁆, oTwoUpper (u3H L1 L2 S)⁆ = ⊥) :
    ⁅F, oTwoUpper (u3H L1 L2 S)⁆ = ⊥ := by
  have hW : IsPGroup 2 F := (pCoreOf_isPGroup 2 (P2 L1 L2 S)).to_le hFQ
  have hWH : F ≤ u3H L1 L2 S := hFQ.trans (q2_le_u3H L1 L2 S)
  have hHW : u3H L1 L2 S ≤ Subgroup.normalizer (F : Set G) :=
    (u3H_le_p2 L1 L2 S).trans hFn
  exact le_bot_iff.mp ((D14.commutator_le_commutator_commutator hW hWH hHW).trans
    (le_of_eq h))

private theorem lemmaF_bigB_le_normalizer_L2 {L1 L2 S : Subgroup G} (hF : F112Hyp L1 L2 S) :
    bigB L1 L2 S ≤ Subgroup.normalizer (L2 : Set G) := by
  have h := bigB_le_normalizer_of_hyp111 hF.1.symm
  rwa [bigB_comm L1 L2 S] at h

private theorem lemmaF_P2_le_normalizer_u3H {L1 L2 S : Subgroup G} (hF : F112Hyp L1 L2 S) :
    P2 L1 L2 S ≤ Subgroup.normalizer (u3H L1 L2 S : Set G) :=
  D14.le_normalizer_sup (sup_le Subgroup.le_normalizer (lemmaF_bigB_le_normalizer_L2 hF))
    (le_normalizer_pCoreOf 2 (P2 L1 L2 S))

private theorem lemmaF_part_i {L1 L2 S F : Subgroup G}
    (hF : F112Hyp L1 L2 S) (hFQ : F ≤ Q2 L1 L2 S)
    (hFn : P2 L1 L2 S ≤ Subgroup.normalizer (F : Set G))
    (hFH : ⁅F, oTwoUpper (u3H L1 L2 S)⁆ ≠ ⊥)
    (hFmin : ∀ F' : Subgroup G, F' ≤ F → P2 L1 L2 S ≤ Subgroup.normalizer (F' : Set G) →
      ⁅F', oTwoUpper (u3H L1 L2 S)⁆ ≠ ⊥ → F' = F) :
    ⁅F, oTwoUpper (u3H L1 L2 S)⁆ = F ∧ F ≤ oTwoUpper (u3H L1 L2 S) := by
  have hP2H : P2 L1 L2 S ≤ Subgroup.normalizer (u3H L1 L2 S : Set G) :=
    lemmaF_P2_le_normalizer_u3H hF
  have hP2H0 : P2 L1 L2 S ≤
      Subgroup.normalizer (oTwoUpper (u3H L1 L2 S) : Set G) :=
    hP2H.trans (normalizer_le_normalizer_oTwoUpper (u3H L1 L2 S))
  have hHNF : u3H L1 L2 S ≤ Subgroup.normalizer (F : Set G) :=
    (u3H_le_p2 L1 L2 S).trans hFn
  have hH0F : oTwoUpper (u3H L1 L2 S) ≤ Subgroup.normalizer (F : Set G) :=
    (oTwoUpper_le (u3H L1 L2 S)).trans hHNF
  have hF1le : ⁅F, oTwoUpper (u3H L1 L2 S)⁆ ≤ F :=
    (Subgroup.le_normalizer_iff_commutator_le_left).mp hH0F
  have hF1n : P2 L1 L2 S ≤
      Subgroup.normalizer (⁅F, oTwoUpper (u3H L1 L2 S)⁆ : Subgroup G) :=
    D14.le_normalizer_commutator hFn hP2H0
  have hF1eq : ⁅F, oTwoUpper (u3H L1 L2 S)⁆ = F := by
    by_contra hne
    have hdouble : ⁅⁅F, oTwoUpper (u3H L1 L2 S)⁆, oTwoUpper (u3H L1 L2 S)⁆ = ⊥ := by
      by_contra h2'
      exact hne (hFmin ⁅F, oTwoUpper (u3H L1 L2 S)⁆ hF1le hF1n h2')
    exact hFH (lemmaF_double_commutator_eq_bot (L1 := L1) (L2 := L2) (S := S)
      (F := F) hFQ hFn hdouble)
  have hFH0N : F ≤ Subgroup.normalizer (oTwoUpper (u3H L1 L2 S) : Set G) :=
    (hFQ.trans (pCoreOf_le 2 (P2 L1 L2 S))).trans hP2H0
  refine ⟨hF1eq, ?_⟩
  rw [← hF1eq]
  exact (Subgroup.le_normalizer_iff_commutator_le_right).mp hFH0N

private theorem lemmaF_part_ii {L1 L2 S F : Subgroup G}
    (hFQ : F ≤ Q2 L1 L2 S) (hFn : P2 L1 L2 S ≤ Subgroup.normalizer (F : Set G))
    (hFne : F ≠ ⊥)
    (hFmin : ∀ F' : Subgroup G, F' ≤ F → P2 L1 L2 S ≤ Subgroup.normalizer (F' : Set G) →
      ⁅F', oTwoUpper (u3H L1 L2 S)⁆ ≠ ⊥ → F' = F) :
    ⁅F, Q2 L1 L2 S⁆ ≤ Subgroup.centralizer (oTwoUpper (u3H L1 L2 S) : Set G) := by
  have hQ2P2 : Q2 L1 L2 S ≤ P2 L1 L2 S := pCoreOf_le 2 (P2 L1 L2 S)
  have hF2lt : ⁅F, Q2 L1 L2 S⁆ < F := by
    have h := CFSG.GroupTheory.commutator_sup_lt_of_isPGroup (p := 2) (X := F)
      (Q := Q2 L1 L2 S) (V := (⊥ : Subgroup G)) hFQ (pCoreOf_isPGroup 2 (P2 L1 L2 S))
      (hQ2P2.trans hFn) (by
        rw [show Subgroup.normalizer ((⊥ : Subgroup G) : Set G) = ⊤ from
          Subgroup.normalizer_eq_top_iff.mpr inferInstance]
        exact le_top) bot_le (Ne.symm hFne)
    simpa using h
  have hF2n : P2 L1 L2 S ≤ Subgroup.normalizer (⁅F, Q2 L1 L2 S⁆ : Subgroup G) :=
    D14.le_normalizer_commutator hFn (le_normalizer_pCoreOf 2 (P2 L1 L2 S))
  have hF2c : ⁅⁅F, Q2 L1 L2 S⁆, oTwoUpper (u3H L1 L2 S)⁆ = ⊥ := by
    by_contra h2'
    exact (ne_of_lt hF2lt) (hFmin ⁅F, Q2 L1 L2 S⁆ hF2lt.le hF2n h2')
  exact Subgroup.commutator_eq_bot_iff_le_centralizer.mp hF2c

private theorem lemmaF_part_iii_YH
    {L1 L2 S F U : Subgroup G}
    (hF : F112Hyp L1 L2 S) (hSB : bigB L1 L2 S ≤ Subgroup.normalizer (S : Set G))
    (hB2 : VBig L2) (h2 : VL2 L2)
    (hFQ : F ≤ Q2 L1 L2 S) (hFn : P2 L1 L2 S ≤ Subgroup.normalizer (F : Set G))
    (hFH : ⁅F, oTwoUpper (u3H L1 L2 S)⁆ ≠ ⊥)
    (hUS : U ≤ S) (hBU : bigB L1 L2 S ≤ Subgroup.normalizer (U : Set G))
    (hUQ2 : ¬ U ≤ Q2 L1 L2 S) :
    ⁅conjClosure (U ⊓ F) (P2 L1 L2 S), oTwoUpper (u3H L1 L2 S)⁆ ≠ ⊥ := by
  classical
  have hS2 : S = (S ⊓ L2) ⊔ Q2 L1 L2 S := lemmaF_S_factor hF hSB hB2 h2
  obtain ⟨n, hL2⟩ := h2
  have hn : 2 ≤ n := two_le_of_isL2Quot_of_vBig hF.1.h2.listed hB2 hL2
  have hQ2S : Q2 L1 L2 S ≤ S := by
    conv_rhs => rw [hS2]
    exact le_sup_right
  have hSleH : S ≤ u3H L1 L2 S := by
    calc S = (S ⊓ L2) ⊔ Q2 L1 L2 S := hS2
      _ ≤ L2 ⊔ Q2 L1 L2 S := sup_le (inf_le_right.trans le_sup_left) le_sup_right
      _ = u3H L1 L2 S := rfl
  have hHleP2 : u3H L1 L2 S ≤ P2 L1 L2 S := u3H_le_p2 L1 L2 S
  have hHNF : u3H L1 L2 S ≤ Subgroup.normalizer (F : Set G) := hHleP2.trans hFn
  have hSNU : S ≤ Subgroup.normalizer (U : Set G) := le_sup_right.trans hBU
  have hFNU : F ≤ Subgroup.normalizer (U : Set G) := (hFQ.trans hQ2S).trans hSNU
  have hUNF : U ≤ Subgroup.normalizer (F : Set G) := (hUS.trans hSleH).trans hHNF
  have hFU_F : ⁅F, U⁆ ≤ F := (Subgroup.le_normalizer_iff_commutator_le_left).mp hUNF
  have hFU_U : ⁅F, U⁆ ≤ U := (Subgroup.le_normalizer_iff_commutator_le_right).mp hFNU
  have hHNC : u3H L1 L2 S ≤ Subgroup.normalizer
      (Subgroup.centralizer (oTwoUpper (u3H L1 L2 S) : Set G) : Set G) :=
    (le_normalizer_oTwoUpper (u3H L1 L2 S)).trans
      (F7.normalizer_le_normalizer_centralizer (oTwoUpper (u3H L1 L2 S)))
  have hHND : u3H L1 L2 S ≤ Subgroup.normalizer
      ((F ⊓ Subgroup.centralizer (oTwoUpper (u3H L1 L2 S) : Set G) : Subgroup G) : Set G) := by
    intro x hx
    exact A4.mem_normalizer_inf (hHNF hx) (hHNC hx)
  intro hYbot
  have hYC : conjClosure (U ⊓ F) (P2 L1 L2 S) ≤
      Subgroup.centralizer (oTwoUpper (u3H L1 L2 S) : Set G) :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.mp hYbot
  have hFU_A : ⁅F, U⁆ ≤ U ⊓ F := le_inf hFU_U hFU_F
  have hFU_D : ⁅F, U⁆ ≤
      F ⊓ Subgroup.centralizer (oTwoUpper (u3H L1 L2 S) : Set G) :=
    le_inf hFU_F (hFU_A.trans
      ((le_conjClosure (U ⊓ F) (P2 L1 L2 S)).trans hYC))
  have hKleH : conjClosure U (u3H L1 L2 S) ≤ u3H L1 L2 S :=
    conjClosure_le fun g hg u hu =>
      (u3H L1 L2 S).mul_mem ((u3H L1 L2 S).mul_mem hg (hSleH (hUS hu)))
        ((u3H L1 L2 S).inv_mem hg)
  have hHNK : u3H L1 L2 S ≤
      Subgroup.normalizer (conjClosure U (u3H L1 L2 S) : Set G) :=
    le_normalizer_conjClosure U (u3H L1 L2 S)
  have hKnotQ : ¬ conjClosure U (u3H L1 L2 S) ≤ Q2 L1 L2 S := fun hKQ =>
    hUQ2 ((le_conjClosure U (u3H L1 L2 S)).trans hKQ)
  have hT5 : oTwoUpper (u3H L1 L2 S) ≤ conjClosure U (u3H L1 L2 S) :=
    lemmaF_oTwoUpper_le_of_not_le hF hn hL2 hKleH hHNK hKnotQ
  have hFK : ⁅F, conjClosure U (u3H L1 L2 S)⁆ ≤
      F ⊓ Subgroup.centralizer (oTwoUpper (u3H L1 L2 S) : Set G) := by
    have hSN : Subgroup.closure {x : G | ∃ h ∈ u3H L1 L2 S, ∃ z ∈ U,
        h * z * h⁻¹ = x} ≤
        Subgroup.normalizer
          ((F ⊓ Subgroup.centralizer (oTwoUpper (u3H L1 L2 S) : Set G) :
            Subgroup G) : Set G) := hKleH.trans hHND
    have hstep : ∀ s ∈ {x : G | ∃ h ∈ u3H L1 L2 S, ∃ z ∈ U,
          h * z * h⁻¹ = x}, ∀ f ∈ F,
        ⁅s, f⁆ ∈ F ⊓ Subgroup.centralizer (oTwoUpper (u3H L1 L2 S) : Set G) := by
      rintro s ⟨g, hg, z, hz, rfl⟩ f hf
      have hgf : g⁻¹ * f * g ∈ F := by
        simpa using
          (Subgroup.mem_normalizer_iff.mp (hHNF ((u3H L1 L2 S).inv_mem hg)) f).mp hf
      have hcommD : ⁅g⁻¹ * f * g, z⁆ ∈
          F ⊓ Subgroup.centralizer (oTwoUpper (u3H L1 L2 S) : Set G) :=
        hFU_D (Subgroup.commutator_mem_commutator hgf hz)
      have hconj : g * ⁅g⁻¹ * f * g, z⁆⁻¹ * g⁻¹ ∈
          F ⊓ Subgroup.centralizer (oTwoUpper (u3H L1 L2 S) : Set G) :=
        (Subgroup.mem_normalizer_iff.mp (hHND hg) _).mp
          ((F ⊓ Subgroup.centralizer (oTwoUpper (u3H L1 L2 S) : Set G)).inv_mem hcommD)
      rw [show ⁅g * z * g⁻¹, f⁆ = g * ⁅g⁻¹ * f * g, z⁆⁻¹ * g⁻¹ by
        simp only [commutatorElement_def]; group]
      exact hconj
    have h := D14.commutator_closure_le
      (S := {x : G | ∃ h ∈ u3H L1 L2 S, ∃ z ∈ U, h * z * h⁻¹ = x})
      (K := F) (N := F ⊓ Subgroup.centralizer (oTwoUpper (u3H L1 L2 S) : Set G))
      hSN hstep
    rw [Subgroup.commutator_comm]
    exact h
  have hFHC : ⁅F, oTwoUpper (u3H L1 L2 S)⁆ ≤
      Subgroup.centralizer (oTwoUpper (u3H L1 L2 S) : Set G) :=
    ((Subgroup.commutator_mono le_rfl hT5).trans hFK).trans inf_le_right
  have hdouble : ⁅⁅F, oTwoUpper (u3H L1 L2 S)⁆, oTwoUpper (u3H L1 L2 S)⁆ = ⊥ :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.mpr hFHC
  exact hFH (lemmaF_double_commutator_eq_bot (L1 := L1) (L2 := L2) (S := S)
    (F := F) hFQ hFn hdouble)

private theorem lemmaF_part_iii_YeqF
    {L1 L2 S F U : Subgroup G}
    (hF : F112Hyp L1 L2 S) (hSB : bigB L1 L2 S ≤ Subgroup.normalizer (S : Set G))
    (hB2 : VBig L2) (h2 : VL2 L2)
    (hFQ : F ≤ Q2 L1 L2 S) (hFn : P2 L1 L2 S ≤ Subgroup.normalizer (F : Set G))
    (hFH : ⁅F, oTwoUpper (u3H L1 L2 S)⁆ ≠ ⊥)
    (hFmin : ∀ F' : Subgroup G, F' ≤ F → P2 L1 L2 S ≤ Subgroup.normalizer (F' : Set G) →
      ⁅F', oTwoUpper (u3H L1 L2 S)⁆ ≠ ⊥ → F' = F)
    (hUS : U ≤ S) (hBU : bigB L1 L2 S ≤ Subgroup.normalizer (U : Set G))
    (hUQ2 : ¬ U ≤ Q2 L1 L2 S) :
    conjClosure (U ⊓ F) (P2 L1 L2 S) = F := by
  have hYH := lemmaF_part_iii_YH hF hSB hB2 h2 hFQ hFn hFH hUS hBU hUQ2
  have hYleF : conjClosure (U ⊓ F) (P2 L1 L2 S) ≤ F :=
    conjClosure_le fun g hg a ha =>
      (Subgroup.mem_normalizer_iff.mp (hFn hg) a).mp ((inf_le_right : U ⊓ F ≤ F) ha)
  have hP2Y : P2 L1 L2 S ≤
      Subgroup.normalizer (conjClosure (U ⊓ F) (P2 L1 L2 S) : Set G) :=
    le_normalizer_conjClosure (U ⊓ F) (P2 L1 L2 S)
  exact hFmin (conjClosure (U ⊓ F) (P2 L1 L2 S)) hYleF hP2Y hYH

private theorem lemmaF_part_iii
    {L1 L2 S F U : Subgroup G}
    (hF : F112Hyp L1 L2 S) (hSB : bigB L1 L2 S ≤ Subgroup.normalizer (S : Set G))
    (hB2 : VBig L2) (h2 : VL2 L2)
    (hFQ : F ≤ Q2 L1 L2 S) (hFn : P2 L1 L2 S ≤ Subgroup.normalizer (F : Set G))
    (hFH : ⁅F, oTwoUpper (u3H L1 L2 S)⁆ ≠ ⊥)
    (hFmin : ∀ F' : Subgroup G, F' ≤ F → P2 L1 L2 S ≤ Subgroup.normalizer (F' : Set G) →
      ⁅F', oTwoUpper (u3H L1 L2 S)⁆ ≠ ⊥ → F' = F)
    (hUS : U ≤ S) (hBU : bigB L1 L2 S ≤ Subgroup.normalizer (U : Set G))
    (hUQ2 : ¬ U ≤ Q2 L1 L2 S) :
    ⁅F, Q2 L1 L2 S⁆ ≤ U := by
  classical
  have hYeq : conjClosure (U ⊓ F) (P2 L1 L2 S) = F :=
    lemmaF_part_iii_YeqF hF hSB hB2 h2 hFQ hFn hFH hFmin hUS hBU hUQ2
  have hFne : F ≠ ⊥ := by
    rintro rfl
    exact hFH (by simp)
  have hF2cent : ⁅F, Q2 L1 L2 S⁆ ≤
      Subgroup.centralizer (oTwoUpper (u3H L1 L2 S) : Set G) :=
    lemmaF_part_ii (L1 := L1) (L2 := L2) (S := S) (F := F) hFQ hFn hFne hFmin
  have hS2 : S = (S ⊓ L2) ⊔ Q2 L1 L2 S := lemmaF_S_factor hF hSB hB2 h2
  obtain ⟨n, hL2⟩ := h2
  have hn : 2 ≤ n := two_le_of_isL2Quot_of_vBig hF.1.h2.listed hB2 hL2
  have hQ2S : Q2 L1 L2 S ≤ S := by
    conv_rhs => rw [hS2]
    exact le_sup_right
  have hHleP2 : u3H L1 L2 S ≤ P2 L1 L2 S := u3H_le_p2 L1 L2 S
  have hSNU : S ≤ Subgroup.normalizer (U : Set G) := le_sup_right.trans hBU
  have hQ2NU : Q2 L1 L2 S ≤ Subgroup.normalizer (U : Set G) := hQ2S.trans hSNU
  have hFNU : F ≤ Subgroup.normalizer (U : Set G) := (hFQ.trans hQ2S).trans hSNU
  have hP2Q2 : P2 L1 L2 S ≤ Subgroup.normalizer (Q2 L1 L2 S : Set G) :=
    le_normalizer_pCoreOf 2 (P2 L1 L2 S)
  have hBA : bigB L1 L2 S ≤ Subgroup.normalizer ((U ⊓ F : Subgroup G) : Set G) := by
    intro x hx
    exact A4.mem_normalizer_inf (hBU hx)
      (((le_sup_right : bigB L1 L2 S ≤ P2 L1 L2 S).trans hFn) hx)
  have hMB : bigB L1 L2 S ≤
      Subgroup.normalizer (⁅U ⊓ F, Q2 L1 L2 S⁆ : Subgroup G) :=
    D14.le_normalizer_commutator hBA
      ((le_sup_right : bigB L1 L2 S ≤ P2 L1 L2 S).trans hP2Q2)
  have hMleC : ⁅U ⊓ F, Q2 L1 L2 S⁆ ≤
      Subgroup.centralizer (oTwoUpper (u3H L1 L2 S) : Set G) :=
    (Subgroup.commutator_mono inf_le_right le_rfl).trans hF2cent
  have hH0M : oTwoUpper (u3H L1 L2 S) ≤
      Subgroup.centralizer (⁅U ⊓ F, Q2 L1 L2 S⁆ : Subgroup G) :=
    Subgroup.le_centralizer_iff.mp hMleC
  have hMH : oTwoUpper (u3H L1 L2 S) ≤
      Subgroup.normalizer (⁅U ⊓ F, Q2 L1 L2 S⁆ : Subgroup G) :=
    hH0M.trans (Subgroup.centralizer_le_normalizer
      ((⁅U ⊓ F, Q2 L1 L2 S⁆ : Subgroup G) : Set G))
  have hP2NM : P2 L1 L2 S ≤
      Subgroup.normalizer (⁅U ⊓ F, Q2 L1 L2 S⁆ : Subgroup G) := by
    have h1 : L2 ≤ oTwoUpper (u3H L1 L2 S) ⊔ bigB L1 L2 S := by
      calc L2 ≤ u3H L1 L2 S := le_sup_left
        _ = oTwoUpper (u3H L1 L2 S) ⊔ Q2 L1 L2 S :=
            str86_u3H_eq_oTwoUpper_sup_q2 hF.toW hn hL2
        _ ≤ oTwoUpper (u3H L1 L2 S) ⊔ bigB L1 L2 S :=
            sup_le le_sup_left ((hQ2S.trans le_sup_right).trans le_sup_right)
    have hP2le : P2 L1 L2 S ≤ oTwoUpper (u3H L1 L2 S) ⊔ bigB L1 L2 S := by
      show L2 ⊔ bigB L1 L2 S ≤ oTwoUpper (u3H L1 L2 S) ⊔ bigB L1 L2 S
      exact sup_le h1 le_sup_right
    exact hP2le.trans (sup_le hMH hMB)
  have hUQ2U : ⁅U, Q2 L1 L2 S⁆ ≤ U :=
    (Subgroup.le_normalizer_iff_commutator_le_left).mp hQ2NU
  have hMleU : ⁅U ⊓ F, Q2 L1 L2 S⁆ ≤ U :=
    (Subgroup.commutator_mono inf_le_left le_rfl).trans hUQ2U
  have hstep2 : ∀ s ∈ {x : G | ∃ h ∈ P2 L1 L2 S, ∃ z ∈ U ⊓ F,
        h * z * h⁻¹ = x}, ∀ q ∈ Q2 L1 L2 S, ⁅s, q⁆ ∈ U := by
    rintro s ⟨g, hg, a, ha, rfl⟩ q hq
    have hgq : g⁻¹ * q * g ∈ Q2 L1 L2 S := by
      simpa using (Subgroup.mem_normalizer_iff.mp (hP2Q2 ((P2 L1 L2 S).inv_mem hg)) q).mp hq
    have hmem : ⁅a, g⁻¹ * q * g⁆ ∈ ⁅U ⊓ F, Q2 L1 L2 S⁆ :=
      Subgroup.commutator_mem_commutator ha hgq
    have hconj : g * ⁅a, g⁻¹ * q * g⁆ * g⁻¹ ∈ ⁅U ⊓ F, Q2 L1 L2 S⁆ :=
      (Subgroup.mem_normalizer_iff.mp (hP2NM hg) _).mp hmem
    rw [show ⁅g * a * g⁻¹, q⁆ = g * ⁅a, g⁻¹ * q * g⁆ * g⁻¹ by
      simp only [commutatorElement_def]; group]
    exact hMleU hconj
  have hSN2 : Subgroup.closure {x : G | ∃ h ∈ P2 L1 L2 S, ∃ z ∈ U ⊓ F,
      h * z * h⁻¹ = x} ≤ Subgroup.normalizer (U : Set G) := by
    have hcls : Subgroup.closure {x : G | ∃ h ∈ P2 L1 L2 S, ∃ z ∈ U ⊓ F,
        h * z * h⁻¹ = x} = conjClosure (U ⊓ F) (P2 L1 L2 S) := rfl
    rw [hcls, hYeq]
    exact hFNU
  have hfin := D14.commutator_closure_le
    (S := {x : G | ∃ h ∈ P2 L1 L2 S, ∃ z ∈ U ⊓ F, h * z * h⁻¹ = x})
    (K := Q2 L1 L2 S) (N := U) hSN2 hstep2
  have hcls : Subgroup.closure {x : G | ∃ h ∈ P2 L1 L2 S, ∃ z ∈ U ⊓ F,
      h * z * h⁻¹ = x} = conjClosure (U ⊓ F) (P2 L1 L2 S) := rfl
  rw [hcls, hYeq] at hfin
  exact hfin

private theorem lemmaF_part_iv
    {L1 L2 S F : Subgroup G}
    (hF : F112Hyp L1 L2 S) (hSB : bigB L1 L2 S ≤ Subgroup.normalizer (S : Set G))
    (hB2 : VBig L2) (h2 : VL2 L2)
    (hFQ : F ≤ Q2 L1 L2 S) (hFn : P2 L1 L2 S ≤ Subgroup.normalizer (F : Set G))
    (hFH : ⁅F, oTwoUpper (u3H L1 L2 S)⁆ ≠ ⊥) :
    ¬ Z1 L1 L2 S ≤ Q2 L1 L2 S → ¬ F ≤ Q1 L1 L2 S := by
  intro hZ hFQ1
  have hS2 : S = (S ⊓ L2) ⊔ Q2 L1 L2 S := lemmaF_S_factor hF hSB hB2 h2
  obtain ⟨n, hL2⟩ := h2
  have hn : 2 ≤ n := two_le_of_isL2Quot_of_vBig hF.1.h2.listed hB2 hL2
  have hSleH : S ≤ u3H L1 L2 S := by
    calc S = (S ⊓ L2) ⊔ Q2 L1 L2 S := hS2
      _ ≤ L2 ⊔ Q2 L1 L2 S := sup_le (inf_le_right.trans le_sup_left) le_sup_right
      _ = u3H L1 L2 S := rfl
  have hHleP2 : u3H L1 L2 S ≤ P2 L1 L2 S := u3H_le_p2 L1 L2 S
  have hHNF : u3H L1 L2 S ≤ Subgroup.normalizer (F : Set G) := hHleP2.trans hFn
  have hQ1S : Q1 L1 L2 S ≤ S :=
    F7.isSylowTwoOf_pCoreOf_le
      (F112W.isSylowTwoOf_parabolic (Hyp111R.of_hyp111 rankOneListedFacts hF.1))
  have hZ1H : Z1 L1 L2 S ≤ u3H L1 L2 S :=
    ((omegaOneCenterOf_le (Q1 L1 L2 S)).trans hQ1S).trans hSleH
  have hFQ1C : F ≤ Subgroup.centralizer (Z1 L1 L2 S : Set G) :=
    hFQ1.trans (Q1_le_centralizer_Z1 L1 L2 S)
  have hZ1C : Z1 L1 L2 S ≤ Subgroup.centralizer (F : Set G) :=
    Subgroup.le_centralizer_iff.mp hFQ1C
  have hKleH : u3H L1 L2 S ⊓ Subgroup.centralizer (F : Set G) ≤ u3H L1 L2 S := inf_le_left
  have hHNK : u3H L1 L2 S ≤ Subgroup.normalizer
      ((u3H L1 L2 S ⊓ Subgroup.centralizer (F : Set G) : Subgroup G) : Set G) := by
    intro x hx
    exact A4.mem_normalizer_inf (Subgroup.le_normalizer hx)
      ((hHNF.trans (F7.normalizer_le_normalizer_centralizer F)) hx)
  have hKnotQ : ¬ u3H L1 L2 S ⊓ Subgroup.centralizer (F : Set G) ≤ Q2 L1 L2 S := by
    intro hKQ
    exact hZ ((le_inf hZ1H hZ1C).trans hKQ)
  have hT5 : oTwoUpper (u3H L1 L2 S) ≤
      u3H L1 L2 S ⊓ Subgroup.centralizer (F : Set G) :=
    lemmaF_oTwoUpper_le_of_not_le hF hn hL2 hKleH hHNK hKnotQ
  have hH0C : oTwoUpper (u3H L1 L2 S) ≤ Subgroup.centralizer (F : Set G) :=
    hT5.trans inf_le_right
  have hFC : F ≤ Subgroup.centralizer (oTwoUpper (u3H L1 L2 S) : Set G) :=
    Subgroup.le_centralizer_iff.mp hH0C
  exact hFH (Subgroup.commutator_eq_bot_iff_le_centralizer.mpr hFC)

theorem str86_lemmaF_exists {L1 L2 S : Subgroup G}
    (hF : F112Hyp L1 L2 S) (hSB : bigB L1 L2 S ≤ Subgroup.normalizer (S : Set G))
    (hB2 : VBig L2) (h2 : VL2 L2) :
    ∃ F : Subgroup G, F ≤ Q2 L1 L2 S ∧ P2 L1 L2 S ≤ Subgroup.normalizer (F : Set G) ∧
      ⁅F, oTwoUpper (u3H L1 L2 S)⁆ ≠ ⊥ ∧
      ∀ F' : Subgroup G, F' ≤ F → P2 L1 L2 S ≤ Subgroup.normalizer (F' : Set G) →
        ⁅F', oTwoUpper (u3H L1 L2 S)⁆ ≠ ⊥ → F' = F := by
  classical
  have hS2 : S = (S ⊓ L2) ⊔ Q2 L1 L2 S := lemmaF_S_factor hF hSB hB2 h2
  obtain ⟨n, hL2⟩ := h2
  have hn : 2 ≤ n := two_le_of_isL2Quot_of_vBig hF.1.h2.listed hB2 hL2
  have hQ2S : Q2 L1 L2 S ≤ S := by
    conv_rhs => rw [hS2]
    exact le_sup_right
  have hHle : u3H L1 L2 S ≤ L2 ⊔ S :=
    sup_le le_sup_left (hQ2S.trans le_sup_right)
  have hHne : ⁅Q2 L1 L2 S, oTwoUpper (u3H L1 L2 S)⁆ ≠ ⊥ := by
    intro hbot
    have hH0c : oTwoUpper (u3H L1 L2 S) ≤
        Subgroup.centralizer (Q2 L1 L2 S : Set G) :=
      Subgroup.le_centralizer_iff.mpr
        (Subgroup.commutator_eq_bot_iff_le_centralizer.mp hbot)
    have hH0Q2 : oTwoUpper (u3H L1 L2 S) ≤ Q2 L1 L2 S :=
      (le_inf ((oTwoUpper_le (u3H L1 L2 S)).trans hHle) hH0c).trans
        (inf_centralizer_pCoreOf_right_of_hyp111 hF.1)
    have hHeq : u3H L1 L2 S = oTwoUpper (u3H L1 L2 S) ⊔ Q2 L1 L2 S :=
      str86_u3H_eq_oTwoUpper_sup_q2 hF.toW hn hL2
    have hHleQ2 : u3H L1 L2 S ≤ Q2 L1 L2 S := by
      rw [hHeq]
      exact sup_le hH0Q2 le_rfl
    have hL2Q2 : L2 ≤ Q2 L1 L2 S :=
      (le_sup_left : L2 ≤ u3H L1 L2 S).trans hHleQ2
    have hL2p : IsPGroup 2 L2 := (pCoreOf_isPGroup 2 (P2 L1 L2 S)).to_le hL2Q2
    have hL2solv : Group.IsSolvable ↥L2 := by
      haveI : Group.IsNilpotent ↥L2 := hL2p.isNilpotent
      infer_instance
    exact (VBig.not_isSolvable hF.1.h2.listed hB2) hL2solv
  have hmem : Q2 L1 L2 S ∈ {F : Subgroup G | F ≤ Q2 L1 L2 S ∧
      P2 L1 L2 S ≤ Subgroup.normalizer (F : Set G) ∧
      ⁅F, oTwoUpper (u3H L1 L2 S)⁆ ≠ ⊥} :=
    ⟨le_rfl, le_normalizer_pCoreOf 2 (P2 L1 L2 S), hHne⟩
  haveI : Finite (Subgroup G) :=
    Finite.of_injective (fun H : Subgroup G => (H : Set G)) SetLike.coe_injective
  obtain ⟨F, hFP, hFmin⟩ := Set.Finite.exists_minimalFor (fun F : Subgroup G => Nat.card F)
    {F : Subgroup G | F ≤ Q2 L1 L2 S ∧
      P2 L1 L2 S ≤ Subgroup.normalizer (F : Set G) ∧
      ⁅F, oTwoUpper (u3H L1 L2 S)⁆ ≠ ⊥} (Set.toFinite _) ⟨Q2 L1 L2 S, hmem⟩
  refine ⟨F, hFP.1, hFP.2.1, hFP.2.2, ?_⟩
  intro F' hF'le hF'n hF'H
  have hF'mem : F' ∈ {F : Subgroup G | F ≤ Q2 L1 L2 S ∧
      P2 L1 L2 S ≤ Subgroup.normalizer (F : Set G) ∧
      ⁅F, oTwoUpper (u3H L1 L2 S)⁆ ≠ ⊥} :=
    ⟨hF'le.trans hFP.1, hF'n, hF'H⟩
  exact Subgroup.eq_of_le_of_card_ge hF'le
    (hFmin hF'mem (Subgroup.card_le_of_le hF'le))

theorem str86_lemmaF {L1 L2 S : Subgroup G}
    (hF : F112Hyp L1 L2 S) (hSB : bigB L1 L2 S ≤ Subgroup.normalizer (S : Set G))
    (hB2 : VBig L2) (h2 : VL2 L2) {F : Subgroup G}
    (hFQ : F ≤ Q2 L1 L2 S) (hFn : P2 L1 L2 S ≤ Subgroup.normalizer (F : Set G))
    (hFH : ⁅F, oTwoUpper (u3H L1 L2 S)⁆ ≠ ⊥)
    (hFmin : ∀ F' : Subgroup G, F' ≤ F → P2 L1 L2 S ≤ Subgroup.normalizer (F' : Set G) →
      ⁅F', oTwoUpper (u3H L1 L2 S)⁆ ≠ ⊥ → F' = F) :
    (⁅F, oTwoUpper (u3H L1 L2 S)⁆ = F ∧ F ≤ oTwoUpper (u3H L1 L2 S)) ∧
      ⁅F, Q2 L1 L2 S⁆ ≤ Subgroup.centralizer (oTwoUpper (u3H L1 L2 S) : Set G) ∧
      (∀ U : Subgroup G, U ≤ S → bigB L1 L2 S ≤ Subgroup.normalizer (U : Set G) →
        ¬ U ≤ Q2 L1 L2 S → ⁅F, Q2 L1 L2 S⁆ ≤ U) ∧
      (¬ Z1 L1 L2 S ≤ Q2 L1 L2 S → ¬ F ≤ Q1 L1 L2 S) := by
  classical
  have hFne : F ≠ ⊥ := by
    rintro rfl
    exact hFH (by simp)
  refine ⟨lemmaF_part_i hF hFQ hFn hFH hFmin, ?_, ?_, ?_⟩
  · exact lemmaF_part_ii hFQ hFn hFne hFmin
  · intro U hUS hBU hUQ2
    exact lemmaF_part_iii hF hSB hB2 h2 hFQ hFn hFH hFmin hUS hBU hUQ2
  · exact lemmaF_part_iv hF hSB hB2 h2 hFQ hFn hFH

end CFSG.Quasithin.Stroth

end
