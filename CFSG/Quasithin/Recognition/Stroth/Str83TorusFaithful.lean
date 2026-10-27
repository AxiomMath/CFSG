module

public import CFSG.Quasithin.Recognition.Stroth.Str83G3CaseIb
public import CFSG.Quasithin.Recognition.Stroth.Hyp111ThompsonJ
public import CFSG.Quasithin.Recognition.Stroth.Str83G3CaseIa
public import CFSG.Quasithin.Recognition.Stroth.Str83G3Torus

public section

namespace CFSG.Quasithin.Stroth

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Quasithin.F112R
open CFSG.LieType.BorelTits CFSG.QuasithinUnique.Setup
open scoped MatrixGroups

variable {G : Type} [Group G] [Finite G]

theorem str83_exists_bottom_chiefStep {L1 L2 S : Subgroup G}
    {a : ℕ} (hF : F112HypW L1 L2 S) (hB : bigB L1 L2 S ≤ Subgroup.normalizer (S : Set G))
    (ha : 1 ≤ a) (hSz : Nonempty (oTwoQuot ↥L1 ≃* Sz a))
    (hL2 : IsL2Quot (2 * a + 1) (oTwoQuot ↥L2))
    (hZI : L1 ⊔ Q1 L1 L2 S ≤ Subgroup.centralizer (Z1 L1 L2 S : Set G)) :
    ∃ Y : Subgroup G, Y ≤ Z2 L1 L2 S ∧ IsChiefStep (L2 ⊔ S) Y ⊥ Y := by
  classical
  have hS2 : S = (S ⊓ L2) ⊔ Q2 L1 L2 S :=
    eq_sup_pCoreOf_of_bender_right hF.1 hB
      (Or.inr (Or.inr ⟨2 * a + 1, by omega, hL2⟩))
  have hsup2 : L2 ⊔ S = L2 ⊔ Q2 L1 L2 S := by
    have h1 : L2 ⊔ S = L2 ⊔ ((S ⊓ L2) ⊔ Q2 L1 L2 S) :=
      congrArg (fun X => L2 ⊔ X) hS2
    rw [h1, ← sup_assoc, show L2 ⊔ (S ⊓ L2) = L2 from sup_eq_left.mpr inf_le_right]
  have hHZ : L2 ⊔ S ≤ Subgroup.normalizer (Z2 L1 L2 S : Set G) := by
    rw [hsup2]
    exact (sup_le le_sup_left (pCoreOf_le 2 (P2 L1 L2 S))).trans
      (SmithC27.le_normalizer_omegaOneCenterOf_pCoreOf (P2 L1 L2 S))
  have hnormal : IsNormalIn (L2 ⊔ S) (Z2 L1 L2 S) (Z2 L1 L2 S) :=
    F112W.isNormalIn_of_le_normalizer le_rfl hHZ
  have hZ2ne : Z2 L1 L2 S ≠ ⊥ := by
    obtain ⟨hZ1eq, hZ1Z2, -, -, -⟩ := str83_caseI_basics hF hB ha hSz hL2 hZI
    intro hbot
    have hZ1ne : Z1 L1 L2 S ≠ ⊥ := by
      rw [hZ1eq]
      exact omegaOneCenterOf_ne_bot_of_hyp111 hF.1
    exact hZ1ne (le_bot_iff.mp (hZ1Z2.trans (le_of_eq hbot)))
  obtain ⟨Y, hYmin⟩ := exists_minimal_of_wellFoundedLT
    (fun Y : Subgroup G => IsNormalIn (L2 ⊔ S) (Z2 L1 L2 S) Y ∧ Y ≠ ⊥)
    ⟨Z2 L1 L2 S, hnormal, hZ2ne⟩
  have hYnorm : IsNormalIn (L2 ⊔ S) (Z2 L1 L2 S) Y := hYmin.1.1
  have hYne : Y ≠ ⊥ := hYmin.1.2
  refine ⟨Y, hYnorm.1, ?_⟩
  refine ⟨⟨le_rfl, fun g hg x hx => hYnorm.2 g hg x hx⟩,
    D15Proof.isNormalIn_bot (L2 ⊔ S) Y, bot_lt_iff_ne_bot.mpr hYne, ?_⟩
  intro K hK _ hKY
  by_cases hKbot : K = ⊥
  · exact Or.inl hKbot
  · refine Or.inr (le_antisymm hKY ?_)
    exact hYmin.2 ⟨⟨hK.1.trans hYnorm.1, hK.2⟩, hKbot⟩ hKY

theorem str83TorusFaithful_of_caseI
    (hR : Str83RqEq) (hI : Str83CaseI) : Str83TorusFaithful := by
  intro G _ _ L1 L2 S a hF hB ha hSz hVBig hVL2 d hdB hodd hcent
  classical
  have hL2 : IsL2Quot (2 * a + 1) (oTwoQuot ↥L2) :=
    hR G L1 L2 S a hF ha hSz hVBig hVL2
  have hZI : L1 ⊔ Q1 L1 L2 S ≤ Subgroup.centralizer (Z1 L1 L2 S : Set G) :=
    caseI_conclusion_of_str83CaseI hI hF hB ha hSz hVBig hVL2
  obtain ⟨Y, hYZ, hstep⟩ := str83_exists_bottom_chiefStep hF hB ha hSz hL2 hZI
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
  have hZ2S : Z2 L1 L2 S ≤ S :=
    (A4.omegaOneCenterOf_le (Q2 L1 L2 S)).trans hQ2S
  have hYS : Y ≤ S := hYZ.trans hZ2S
  have hYH : Y ≤ L2 ⊔ S := hYS.trans le_sup_right
  have hZ2ea : IsElemAbelian 2 (Z2 L1 L2 S) := SmithC27.isElemAbelian_omegaOneCenterOf _
  have hV : IsElemAbelian 2 Y := CFSG.Open.IsElemAbelian.mono hZ2ea hYZ
  have hsylow : IsSylowTwoOf S (L2 ⊔ S) := by
    have h := isSylowTwoOf_sup_pCoreOf (L1 := L2) (L2 := L1) (S := S) hF.1.symm
      (by simpa [Q1, Q2, P1, P2, bigB_comm] using hS2)
    have hQ : Q1 L2 L1 S = Q2 L1 L2 S := by
      simp [Q1, Q2, P1, P2, bigB_comm]
    rw [hQ, show L2 ⊔ Q2 L1 L2 S = L2 ⊔ S from hsup2.symm] at h
    exact h
  obtain ⟨e, ρ, φ, hcompat, hφnat⟩ :=
    if hJ1 : thompsonJ S ≤ Q1 L1 L2 S then
      str83_natural_bottom_of_not_le_q2 hF hB ha hSz hL2 hZI
        (fun hJ2 => not_thompsonJ_le_q1_inf_q2 hF.1 (le_inf hJ1 hJ2)) hYZ hYH hV hstep
    else
      str83_natural_bottom_of_not_le_q1 hF hB ha hSz hL2 hZI hJ1 hYZ hYH hV hstep
  have hdL2 : d ∈ L2 := (CFSG.Quasithin.F1.borelOf_le L2 S) hdB
  have hdH : d ∈ L2 ⊔ S := (le_sup_left : L2 ≤ L2 ⊔ S) hdL2
  have hdBbig : d ∈ bigB L1 L2 S := by
    refine (show borelOf L2 S ≤ bigB L1 L2 S from ?_) hdB
    rw [bigB]
    exact le_sup_right.trans le_sup_left
  have hdN : d ∈ Subgroup.normalizer (S : Set G) := hB hdBbig
  have hYinf : Y ⊓ Subgroup.centralizer (S : Set G) ≤ omegaOneCenterOf S :=
    inf_centralizer_le_omegaOneCenterOf_of_le hYS hV
  have hcentY : d ∈ Subgroup.centralizer
      ((Y ⊓ Subgroup.centralizer (S : Set G) : Subgroup G) : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    exact (hcent x (hYinf hx)).symm
  exact l2_chiefStep_torus_faithful (n := 2 * a + 1) (H := L2 ⊔ S) (Y := Y) (S := S)
    (by omega) hsylow hYH hV hstep e ρ φ hcompat hφnat d hdH hdN hodd hcentY

end CFSG.Quasithin.Stroth

end
