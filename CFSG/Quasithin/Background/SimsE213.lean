module

public import CFSG.Quasithin.Background.SimsE213Four
public import CFSG.Quasithin.Background.SimsE213Six
public import CFSG.Quasithin.Background.SimsE29
public import CFSG.Quasithin.Background.SimsE213L33
public import CFSG.Quasithin.Vol2.Ch3nE213Two

public section

namespace CFSG.Quasithin.SimsE2

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank

theorem e213
    (h27 : E27Stmt) (hD4 : DihFour) :
    ∀ (Γ : Type) [Group Γ] [Finite Γ] (H T M V : Subgroup Γ) (h : E2.Hyp28 H T M V), CharTwo H →
      (∃ I : Subgroup Γ, IsInIHTV H T M V I) ∧
      qhatOf (autI h.elem H) ≤ ((2 : ℚ) : WithTop ℚ) ∧
      ∀ (I : Subgroup Γ) (g : Γ), IsInIHTV H T M V I → g ∈ I → I = V ⊔ conjSubgroup V g →
        ∀ A : Subgroup Γ, A = conjSubgroup V g ⊓ pCoreOf 2 I →
          (A = conjSubgroup V g ⊓ Subgroup.normalizer (V : Set Γ) ∧ ⁅⁅⁅V, A⁆, A⁆, A⁆ = ⊥ ∧
            ⁅V, A⁆ ≠ ⊥ ∧ A ⊓ Subgroup.centralizer (V : Set Γ) = V ⊓ conjSubgroup V g ∧
            E3.mQuot V (V ⊓ Subgroup.centralizer (A : Set Γ)) ≤
              2 * E3.mQuot A (A ⊓ Subgroup.centralizer (V : Set Γ))) ∧
          qhatOf (autI h.elem H) ≤ ((2 : ℚ) : WithTop ℚ) ∧
          ((∀ p a : ℕ, p.Prime → p ≠ 2 → 1 ≤ a →
              Nonempty (E2.StarQuot (M ⊓ I) I ≃* DihedralGroup (p ^ a)) →
              E2.dParamPrime (p ^ a) ≤ rk ↥(autI h.elem A)) ∧
            (∀ k : ℕ, 1 < k → IsPSL 2 2 k (E2.StarQuot (M ⊓ I) I) → k ≤ rk ↥(autI h.elem A)) ∧
            (∀ k : ℕ, IsSz k (E2.StarQuot (M ⊓ I) I) → 2 * k ≤ rk ↥(autI h.elem A)) ∧
            (∀ k : ℕ, 1 ≤ k → IsSp4Full k (E2.StarQuot (M ⊓ I) I) →
              2 * k ≤ rk ↥(autI h.elem A))) ∧
          (V ⊓ conjSubgroup V g = ⊥ → qOf (autI h.elem H) ≤ ((1 : ℚ) : WithTop ℚ)) ∧
          ((∀ x : Γ, (∃ i ∈ I, ∃ v ∈ V, x = i⁻¹ * v * i) → x ∈ T →
              x ∈ Subgroup.centralizer (V : Set Γ)) →
            ¬ ∃ k : ℕ, 1 ≤ k ∧ IsSp4Full k (E2.StarQuot (M ⊓ I) I)) ∧
          (∀ P : Subgroup Γ, P = (pCoreOf 2 I ⊓ V) ⊔ A →
            (∀ x ∈ I, (∀ p ∈ P, x * p * x⁻¹ * p⁻¹ ∈ V ⊓ conjSubgroup V g) → x ∈ pCoreOf 2 I) ∧
            pCoreOf 2 I = kerIn (M ⊓ I) I) := by
  intro Γ _ _ H T M V h hc
  have hq := E2.e213ThreeStatement_of_two E2.e213TwoStatement_holds Γ H T M V h hc
  refine ⟨(e29 h27 H T M V h).2.1 (not_isL33Exception_of_charTwo H T M V h hc), hq,
    fun I g hI hg hIV A hA => ?_⟩
  obtain ⟨h2, h5, h7⟩ := e213_member H T M V h hc I g hI hg hIV A hA
  exact ⟨h2, hq, ⟨hD4 Γ H T M V h hc I g hI hg hIV A hA,
    e213_four_nondih H T M V h hc I g hI hg hIV A hA⟩, h5, e213_six H T M V h hc I hI, h7⟩

end CFSG.Quasithin.SimsE2
