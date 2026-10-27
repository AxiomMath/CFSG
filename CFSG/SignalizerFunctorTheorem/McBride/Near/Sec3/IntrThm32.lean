module

public import CFSG.SignalizerFunctorTheorem.McBride.Near.Sec3.IntrThm32Step1
public import CFSG.SignalizerFunctorTheorem.McBride.Near.Sec3.IntrThm32Step3

public section

open CFSG.Open

namespace CFSG.SignalizerFunctorTheorem.McBride.Near

variable {Γ : Type*} [Group Γ] [Finite Γ] {p : ℕ} {A X Y : Subgroup Γ}

namespace Thm32

omit [Finite Γ] in
theorem le_secCenIn_cen {A B W₁ W₂ : Subgroup Γ} (hBA : B ≤ A)
    (hcomm : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a) (h₁ : A ≤ Subgroup.normalizer (W₁ : Set Γ))
    (h₂ : A ≤ Subgroup.normalizer (W₂ : Set Γ)) :
    B ≤ secCenIn A (cenIn W₁ (B : Set Γ)) (cenIn W₂ (B : Set Γ)) := by
  intro b hb
  have hbA : b ∈ A := hBA hb
  have hbC : b ∈ Subgroup.centralizer (B : Set Γ) :=
    Subgroup.mem_centralizer_iff.mpr fun b' hb' => hcomm b' (hBA hb') b hbA
  have key : ∀ W : Subgroup Γ, A ≤ Subgroup.normalizer (W : Set Γ) →
      b ∈ Subgroup.normalizer ((cenIn W (B : Set Γ) : Subgroup Γ) : Set Γ) := fun W hW =>
    Subgroup.inf_normalizer_le_normalizer_inf
      (Subgroup.mem_inf.mpr ⟨hW hbA, Subgroup.le_normalizer hbC⟩)
  refine Subgroup.mem_inf.mpr ⟨hbA, mem_sectionCentralizer_iff.mpr
    ⟨key W₂ h₂, key W₁ h₁, fun y hy => ?_⟩⟩
  have hyC : y ∈ Subgroup.centralizer (B : Set Γ) := (Subgroup.mem_inf.mp hy).2
  have hby : b * y = y * b := Subgroup.mem_centralizer_iff.mp hyC b hb
  rw [commutatorElement_eq_one_iff_mul_comm.mpr hby]
  exact one_mem _

end Thm32

theorem iThm32
    (h : NearAsolvAction p A X) {X₁ X₂ : Subgroup Γ}
    (hP : (X₁, X₂) ∈ iPairsY A X Y) :
    ∃ Z₁ Z₂ : Subgroup Γ, Z₁ ≤ X₁ ∧ Z₂ ≤ X₂ ∧ (Z₁, Z₂) ∈ iPairsY A X Y ∧
      Group.IsSolvable Z₂ ∧ CyclicMod A (secCenIn A Z₁ Z₂) := by
  obtain ⟨W₁, W₂, hW₁, hW₂, hW, hW₂s⟩ := Thm32.exists_solvable_of_pair h hP
  obtain ⟨B, hBA, ⟨a, ha, hle⟩, hpair⟩ := Thm32.exists_cen_pair h hW
  have hA₁ : A ≤ Subgroup.normalizer (W₁ : Set Γ) :=
    le_sup_right.trans (Thm32.isDAIn_left_of_mem_iPairsY hW).2
  have hA₂ : A ≤ Subgroup.normalizer (W₂ : Set Γ) :=
    le_sup_right.trans (Thm32.isDAIn_right_of_mem_iPairsY hW).2
  have hcomm : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a := fun a ha b hb => by
    have := h.elemAbelian.1
    exact congrArg Subtype.val (mul_comm' (⟨a, ha⟩ : A) ⟨b, hb⟩)
  exact ⟨cenIn W₁ (B : Set Γ), cenIn W₂ (B : Set Γ), inf_le_left.trans hW₁,
    inf_le_left.trans hW₂, hpair, Thm211.isSolvable_of_le inf_le_left hW₂s, a, ha,
    hle.trans (sup_le_sup_right (Thm32.le_secCenIn_cen hBA hcomm hA₁ hA₂) _)⟩

end CFSG.SignalizerFunctorTheorem.McBride.Near
