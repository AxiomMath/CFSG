module

public import Mathlib
public import CFSG.SignalizerFunctorTheorem.McBride.Near.Sec2.Thm211Aux
public import CFSG.SignalizerFunctorTheorem.McBride.Near.Sec3.IntrThm32Chief
public import CFSG.SignalizerFunctorTheorem.McBride.Near.Sec3.IntrThm32Back

public section

open CFSG.Open
open CFSG.SignalizerFunctorTheorem.McBride.Nonsolv

universe u

namespace CFSG.SignalizerFunctorTheorem.McBride.Near.Thm32

variable {Γ : Type u} [Group Γ] {p : ℕ} {A X Y X₁ X₂ : Subgroup Γ}

theorem qimg_le_centralizer {R E F : Subgroup Γ} (h : E ≤ Subgroup.centralizer (F : Set Γ)) :
    AChief.qimg R E ≤ Subgroup.centralizer
      ((AChief.qimg R F : Subgroup (AChief.QG R)) : Set (AChief.QG R)) := by
  intro z hz
  obtain ⟨y, hy, rfl⟩ := (AChief.mem_qimg_iff R E z).mp hz
  rw [Subgroup.mem_centralizer_iff]
  intro w hw
  obtain ⟨x, hx, rfl⟩ := (AChief.mem_qimg_iff R F w).mp hw
  have hxy : x * y = y * x :=
    Subtype.ext (Subgroup.mem_centralizer_iff.mp (h hy) (x : Γ) hx)
  rw [← map_mul, ← map_mul, hxy]

theorem exists_cen_pair [Finite Γ] (h : NearAsolvAction p A X)
    (hP : (X₁, X₂) ∈ iPairsY A X Y) :
    ∃ B : Subgroup Γ, B ≤ A ∧ CyclicMod A B ∧
      (cenIn X₁ (B : Set Γ), cenIn X₂ (B : Set Γ)) ∈ iPairsY A X Y := by
  have hch := chief_of_mem_iPairsY hP
  have hsec := secCen_of_mem_iPairsY hP
  have hinf := inf_eq_of_mem_iPairsY hP
  have hX₁ := isDAIn_left_of_mem_iPairsY hP
  have hX₂ := isDAIn_right_of_mem_iPairsY hP
  set D := cenIn X (A : Set Γ) with hD
  have hDX : D ≤ X := inf_le_left
  have hDA : D ≤ Subgroup.centralizer (A : Set Γ) := inf_le_right
  have hGX : X₁ ⊔ D ≤ X := sup_le hX₁.1 hDX
  have hcop : Nat.Coprime p (Nat.card ↥(X₁ ⊔ D)) :=
    h.nearPSolvable.1.coprime_dvd_right (Subgroup.card_dvd_of_le hGX)
  have S0 : BackSetting p A D X₁ X₂ A := ⟨h.prime, h.elemAbelian, hDA, hcop, hch, le_rfl⟩
  have hG : NearAsolvAction p A (X₁ ⊔ D) := Thm211.nearAsolvAction_of_le h hGX S0.A_le_nor_G
  have hq : NearAsolvAction p (AChief.qimg X₂ A) (AChief.qimg X₂ (X₁ ⊔ D)) :=
    Thm211.nearAsolvAction_qimg hG S0.G_le_nrm S0.A_le_nrm
  have hGX₁ : X₁ ⊔ D ≤ Subgroup.normalizer (X₁ : Set Γ) :=
    sup_le Subgroup.le_normalizer S0.D_le_nor_X₁
  have hCS : ChiefSetting p (AChief.qimg X₂ A) (AChief.qimg X₂ (X₁ ⊔ D)) (AChief.qimg X₂ X₁)
      (AChief.qimg X₂ D) := by
    refine ⟨hq, SolQuot.qimg_mono le_sup_left, SolQuot.qimg_mono le_sup_right,
      qimg_le_centralizer hDA,
      (SolQuot.qimg_sup S0.X₁_le_nrm S0.D_le_nrm).symm, ?_, ?_⟩
    · have h1 := isChiefFactorOf_qimg (R := X₂) S0.E_le_nor_X₂ hch
      rwa [SolQuot.qimg_sup S0.G_le_nrm S0.A_le_nrm] at h1
    · exact qimg_inf_centralizer_eq_bot S0.G_le_nrm le_sup_left hGX₁ hsec.le
  obtain ⟨B', hB'A, hcyc, hns, hch', hsol⟩ := hCS.exists_B
  obtain ⟨B, hBA, hqB, hcycB⟩ := exists_preimage S0.A_le_nrm hB'A hcyc
  subst hqB
  have S : BackSetting p A D X₁ X₂ B := ⟨h.prime, h.elemAbelian, hDA, hcop, hch, hBA⟩
  refine ⟨B, hBA, hcycB, mem_iPairsY_of ?_ ?_ ?_ ?_ ?_⟩
  · exact ⟨inf_le_left.trans hX₁.1, le_normalizer_inf hX₁.2
      ((sup_le S.D_le_cen_B S.A_le_cen_B).trans Subgroup.le_normalizer)⟩
  · exact ⟨inf_le_left.trans hX₂.1, le_normalizer_inf hX₂.2
      ((sup_le S.D_le_cen_B S.A_le_cen_B).trans Subgroup.le_normalizer)⟩
  · exact S.isChiefFactorOf_cen hns hch'
  · exact S.secCenIn_cen h.solvable_cen hns hch' hsol
  · calc cenIn X₂ (B : Set Γ) ⊓ D = X₂ ⊓ D :=
        le_antisymm (inf_le_inf_right _ inf_le_left)
          (le_inf (le_inf inf_le_left (inf_le_right.trans S.D_le_cen_B)) inf_le_right)
      _ = Y := hinf

end CFSG.SignalizerFunctorTheorem.McBride.Near.Thm32
