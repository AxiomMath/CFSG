module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Quasithin.Background.B6Sections
public import CFSG.Quasithin.Background.E1Defs
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixIII.Basic

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits
open scoped commutatorElement Pointwise

namespace LRed10

namespace Frat

theorem commutator_mul_mul_mem {Γ : Type*} [Group Γ] (Q : Subgroup Γ) [Q.Normal] {a b c d : Γ}
    (hcb : ⁅c, b⁆ ∈ Q) (hda : ⁅d, a⁆ ∈ Q) (hcd : ⁅c, d⁆ ∈ Q) :
    ⁅a * c, b * d⁆ * ⁅a, b⁆⁻¹ ∈ Q := by
  have key : ∀ x : Γ, x ∈ Q ↔ QuotientGroup.mk' Q x = 1 := fun x => by
    rw [← MonoidHom.mem_ker, QuotientGroup.ker_mk']
  rw [key, map_mul, map_inv, map_commutatorElement, map_commutatorElement, map_mul, map_mul]
  rw [key, map_commutatorElement, commutatorElement_eq_one_iff_mul_comm] at hcb hda hcd
  generalize QuotientGroup.mk' Q a = A at *
  generalize QuotientGroup.mk' Q b = B at *
  generalize QuotientGroup.mk' Q c = C at *
  generalize QuotientGroup.mk' Q d = D at *
  have hda' : D * A⁻¹ = A⁻¹ * D := (show Commute D A from hda).inv_right
  calc ⁅A * C, B * D⁆ * ⁅A, B⁆⁻¹ = (A * (C * B) * D * C⁻¹ * A⁻¹ * D⁻¹ * B⁻¹) * ⁅A, B⁆⁻¹ := by
        simp only [commutatorElement_def]; group
    _ = (A * (B * C) * D * C⁻¹ * A⁻¹ * D⁻¹ * B⁻¹) * ⁅A, B⁆⁻¹ := by rw [hcb]
    _ = (A * B * (C * D) * C⁻¹ * A⁻¹ * D⁻¹ * B⁻¹) * ⁅A, B⁆⁻¹ := by group
    _ = (A * B * (D * C) * C⁻¹ * A⁻¹ * D⁻¹ * B⁻¹) * ⁅A, B⁆⁻¹ := by rw [hcd]
    _ = (A * B * (D * A⁻¹) * D⁻¹ * B⁻¹) * ⁅A, B⁆⁻¹ := by group
    _ = (A * B * (A⁻¹ * D) * D⁻¹ * B⁻¹) * ⁅A, B⁆⁻¹ := by rw [hda']
    _ = 1 := by simp only [commutatorElement_def]; group

theorem exists_mul_of_perfect_quotient {Γ : Type*} [Group Γ] [Finite Γ] (N R : Subgroup Γ)
    [N.Normal] [R.Normal] [Group.IsPerfect (Γ ⧸ N)] (h2 : ∀ x : Γ, ∃ k : ℕ, x ^ 2 ^ k ∈ R)
    (x : Γ) : ∃ r ∈ R, ∃ n ∈ N, x = r * n := by
  set φ := QuotientGroup.mk' N with hφ
  have hφs : Function.Surjective φ := QuotientGroup.mk'_surjective N
  have hRn : (R.map φ).Normal := Subgroup.Normal.map inferInstance φ hφs
  have h1 : twoResidual (⊤ : Subgroup (Γ ⧸ N)) ≤ R.map φ := by
    refine twoResidual_le_of_isTwoQuotient le_top ?_ ?_
    · exact (Subgroup.normalizer_eq_top_iff.mpr hRn).ge
    · intro y _
      obtain ⟨z, rfl⟩ := hφs y
      obtain ⟨k, hk⟩ := h2 z
      exact ⟨k, ⟨z ^ 2 ^ k, hk, by simp⟩⟩
  have h2' : (⊤ : Subgroup (Γ ⧸ N)) ≤ twoResidual (⊤ : Subgroup (Γ ⧸ N)) :=
    B6.perfect_le_twoResidual (P := ⊤)
  obtain ⟨r, hr, hrx⟩ := h1 (h2' (Subgroup.mem_top (φ x)))
  refine ⟨r, hr, r⁻¹ * x, ?_, by group⟩
  rw [← QuotientGroup.ker_mk' N, MonoidHom.mem_ker, map_mul, map_inv]
  rw [← hφ, hrx, inv_mul_cancel]

theorem exists_mul_of_commutator_quotient {Γ : Type*} [Group Γ] (N : Subgroup Γ) [N.Normal]
    (hN : commutator (Γ ⧸ N) = ⊤) (x : Γ) : ∃ c ∈ commutator Γ, ∃ n ∈ N, x = c * n := by
  set φ := QuotientGroup.mk' N with hφ
  have hφs : Function.Surjective φ := QuotientGroup.mk'_surjective N
  have hmap : (commutator Γ).map φ = ⊤ := by
    have h1 : (commutator Γ).map φ = ⁅(⊤ : Subgroup Γ).map φ, (⊤ : Subgroup Γ).map φ⁆ :=
      Subgroup.map_commutator ⊤ ⊤ φ
    rw [Subgroup.map_top, MonoidHom.range_eq_top_of_surjective φ hφs] at h1
    rw [h1]
    exact hN
  obtain ⟨c, hc, hcx⟩ : φ x ∈ (commutator Γ).map φ := by rw [hmap]; exact Subgroup.mem_top _
  refine ⟨c, hc, c⁻¹ * x, ?_, by group⟩
  rw [← QuotientGroup.ker_mk' N, MonoidHom.mem_ker, map_mul, map_inv]
  rw [← hφ, hcx, inv_mul_cancel]

end Frat

theorem twoResidual_le_sup_pCoreOf_of_case_two {G : Type*} [Group G] [Finite G]
    {H T M C : Subgroup G} (h : MinParabolic H T M) (hHC : H = C ⊔ T)
    (hperf : commutator (↥C ⧸ CFSG.Open.pCore 2 ↥C) = ⊤)
    (hTC : T ≤ Subgroup.normalizer (C : Set G))
    (hJ : ∀ x : G, x ∈ kerIn M H ↔
      x ∈ C ⊔ pCoreOf 2 H ∧ ∀ y ∈ C ⊔ pCoreOf 2 H, x * y * x⁻¹ * y⁻¹ ∈ pCoreOf 2 H)
    {Y : Subgroup G} (hYH : Y ≤ H) (hY : twoResidual H ≤ Y ⊔ kerIn M H) :
    twoResidual H ≤ Y ⊔ pCoreOf 2 H := by
  have hQJ : pCoreOf 2 H ≤ kerIn M H := h.pCoreOf_le_kerIn
  have hJH : kerIn M H ≤ H := h.kerIn_le_H
  have hQH : pCoreOf 2 H ≤ H := pCoreOf_le 2 H
  have hHQ : H ≤ Subgroup.normalizer (pCoreOf 2 H : Set G) := le_normalizer_pCoreOf 2 H
  have hHJ : H ≤ Subgroup.normalizer (kerIn M H : Set G) := le_normalizer_kerIn M H
  have hCH : C ≤ H := by rw [hHC]; exact le_sup_left
  have hHC' : H ≤ Subgroup.normalizer (C : Set G) := by
    rw [hHC]; exact sup_le Subgroup.le_normalizer hTC
  have hRC : twoResidual H ≤ C :=
    twoResidual_le_of_isTwoQuotient hCH hHC'
      (B6.isTwoQuotient_of_sup_eq h.isSylow.2.1 hHC' ((sup_comm T C).trans hHC.symm))
  have hB : ∀ x ∈ C, ∃ r ∈ twoResidual H, ∃ q ∈ pCoreOf 2 C, x = r * q := by
    intro x hx
    have : ((twoResidual H).subgroupOf C).Normal :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer hRC).2
        (hCH.trans (le_normalizer_twoResidual H))
    have : Group.IsPerfect (↥C ⧸ CFSG.Open.pCore 2 ↥C) := ⟨hperf⟩
    obtain ⟨r, hr, n, hn, hrn⟩ := Frat.exists_mul_of_perfect_quotient (CFSG.Open.pCore 2 ↥C)
      ((twoResidual H).subgroupOf C)
      (fun y => by
        obtain ⟨k, hk⟩ := twoResidual_isTwoQuotient H (y : G) (hCH y.2)
        exact ⟨k, hk⟩) ⟨x, hx⟩
    exact ⟨r, hr, n, ⟨n, hn, rfl⟩, congrArg Subtype.val hrn⟩
  have hD : pCoreOf 2 C ≤ pCoreOf 2 H :=
    le_pCoreOf_of_le_normalizer 2 ((pCoreOf_le 2 C).trans hCH)
      (hHC'.trans (normalizer_le_normalizer_pCoreOf 2 C)) (pCoreOf_isPGroup 2 C)
  have hE1 : ∀ x ∈ C, ∃ y ∈ Y, ∃ j ∈ kerIn M H, x = y * j := by
    intro x hx
    obtain ⟨r, hr, q, hq, rfl⟩ := hB x hx
    have hrYJ : r ∈ (Y : Set G) * (kerIn M H : Set G) := by
      rw [← Subgroup.coe_mul_of_left_le_normalizer_right Y (kerIn M H) (hYH.trans hHJ)]
      exact hY hr
    obtain ⟨y, hy, j, hj, rfl⟩ := hrYJ
    exact ⟨y, hy, j * q, (kerIn M H).mul_mem hj (hQJ (hD hq)), by rw [mul_assoc]⟩
  have hE2 : ∀ a ∈ C, ∀ b ∈ C, ⁅a, b⁆ ∈ Y ⊔ pCoreOf 2 H := by
    intro a ha b hb
    obtain ⟨y₁, hy₁, j₁, hj₁, rfl⟩ := hE1 a ha
    obtain ⟨y₂, hy₂, j₂, hj₂, rfl⟩ := hE1 b hb
    have hJA : ∀ j ∈ kerIn M H, j ∈ C ⊔ pCoreOf 2 H := fun j hj => ((hJ j).mp hj).1
    have hy₁A : y₁ ∈ C ⊔ pCoreOf 2 H := by
      have h1 : y₁ * j₁ * j₁⁻¹ ∈ C ⊔ pCoreOf 2 H :=
        Subgroup.mul_mem _ (Subgroup.mem_sup_left ha) (Subgroup.inv_mem _ (hJA j₁ hj₁))
      rwa [mul_inv_cancel_right] at h1
    have hy₂A : y₂ ∈ C ⊔ pCoreOf 2 H := by
      have h1 : y₂ * j₂ * j₂⁻¹ ∈ C ⊔ pCoreOf 2 H :=
        Subgroup.mul_mem _ (Subgroup.mem_sup_left hb) (Subgroup.inv_mem _ (hJA j₂ hj₂))
      rwa [mul_inv_cancel_right] at h1
    have : ((pCoreOf 2 H).subgroupOf H).Normal :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer hQH).2 hHQ
    have key := Frat.commutator_mul_mul_mem ((pCoreOf 2 H).subgroupOf H)
      (a := (⟨y₁, hYH hy₁⟩ : H)) (b := (⟨y₂, hYH hy₂⟩ : H))
      (c := (⟨j₁, hJH hj₁⟩ : H)) (d := (⟨j₂, hJH hj₂⟩ : H))
      (Subgroup.mem_subgroupOf.mpr (((hJ j₁).mp hj₁).2 y₂ hy₂A))
      (Subgroup.mem_subgroupOf.mpr (((hJ j₂).mp hj₂).2 y₁ hy₁A))
      (Subgroup.mem_subgroupOf.mpr (((hJ j₁).mp hj₁).2 j₂ (hJA j₂ hj₂)))
    have key' : ⁅y₁ * j₁, y₂ * j₂⁆ * ⁅y₁, y₂⁆⁻¹ ∈ pCoreOf 2 H := Subgroup.mem_subgroupOf.mp key
    have h12 : ⁅y₁, y₂⁆ ∈ Y :=
      Y.mul_mem (Y.mul_mem (Y.mul_mem hy₁ hy₂) (Y.inv_mem hy₁)) (Y.inv_mem hy₂)
    have := Subgroup.mul_mem _ (Subgroup.mem_sup_right key') (Subgroup.mem_sup_left h12)
    rwa [inv_mul_cancel_right] at this
  have hE3 : C ≤ Y ⊔ pCoreOf 2 H := by
    intro x hx
    obtain ⟨c, hc, n, hn, hcn⟩ :=
      Frat.exists_mul_of_commutator_quotient (CFSG.Open.pCore 2 ↥C) hperf (⟨x, hx⟩ : ↥C)
    have hcle : commutator ↥C ≤ (Y ⊔ pCoreOf 2 H).subgroupOf C :=
      Subgroup.commutator_le.mpr fun a _ b _ => hE2 a a.2 b b.2
    have hc' : (c : G) ∈ Y ⊔ pCoreOf 2 H := Subgroup.mem_subgroupOf.mp (hcle hc)
    have hn' : (n : G) ∈ pCoreOf 2 H := hD ⟨n, hn, rfl⟩
    have hx' : x = (c : G) * (n : G) := congrArg Subtype.val hcn
    rw [hx']
    exact Subgroup.mul_mem _ hc' (Subgroup.mem_sup_right hn')
  exact hRC.trans hE3

end LRed10

end CFSG.Quasithin
