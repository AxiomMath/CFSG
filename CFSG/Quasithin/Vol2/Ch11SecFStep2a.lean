module

public import CFSG.LocalAnalysis.QuasithinUnique.PushingUp.C5Conj
public import CFSG.LocalAnalysis.QuasithinUnique.PushingUp.C5Counting
public import CFSG.Quasithin.Vol2.Ch11SecFBasic
public import CFSG.Quasithin.Vol2.Ch11SecFFacts

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecF

open CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.Quasithin.H13
open CFSG.QuasithinUnique.C5 (conjSubgroup_mono conjSubgroup_normalizer conjSubgroup_le_iff)

variable {G : Type} [Group G] [Finite G] {T L I : Subgroup G} {n : ℕ} {V₁ V₂ V₃ : Subgroup G}

omit [Finite G] in
theorem conj_le_centralizer_conj {A : Subgroup G} (hA : IsMulCommutative ↥A) (g : G) :
    conjSubgroup A g ≤ Subgroup.centralizer (conjSubgroup A g : Set G) := by
  intro x hx
  rw [Subgroup.mem_centralizer_iff]
  intro y hy
  have hy' : y ∈ conjSubgroup A g := hy
  rw [mem_conjSubgroup_iff] at hx hy'
  have hc : g * y * g⁻¹ * (g * x * g⁻¹) = g * x * g⁻¹ * (g * y * g⁻¹) :=
    congrArg Subtype.val (hA.is_comm.comm (⟨_, hy'⟩ : ↥A) ⟨_, hx⟩)
  have h2 : g⁻¹ * (g * y * g⁻¹ * (g * x * g⁻¹)) * g = g⁻¹ * (g * x * g⁻¹ * (g * y * g⁻¹)) * g := by
    rw [hc]
  simpa [mul_assoc] using h2

omit [Finite G] in
theorem conj_fsuV_le_pCoreOf (hQ : fsuV T I ≤ pCoreOf 2 (Subgroup.normalizer (V₁ : Set G)))
    {g : G} (hg : g ∈ Subgroup.normalizer (V₁ : Set G)) :
    conjSubgroup (fsuV T I) g ≤ pCoreOf 2 (Subgroup.normalizer (V₁ : Set G)) :=
  (conjSubgroup_mono hQ g).trans (conjSubgroup_pCoreOf_normalizer hg).le

theorem conj_fsuV_le_ROf (h : Hyp11 G T L I n) (hV₁ : IsVi T L I n 1 V₁)
    (hQ : fsuV T I ≤ pCoreOf 2 (Subgroup.normalizer (V₁ : Set G)))
    {g : G} (hg : g ∈ Subgroup.normalizer (V₁ : Set G)) : conjSubgroup (fsuV T I) g ≤ ROf T L V₁ :=
  (conj_fsuV_le_pCoreOf hQ hg).trans (pCoreOf_normalizer_V₁_le_ROf h hV₁)

theorem commutator_fsuV_conj_le_inf (h : Hyp11 G T L I n) (hV₁ : IsVi T L I n 1 V₁)
    (hQ : fsuV T I ≤ pCoreOf 2 (Subgroup.normalizer (V₁ : Set G)))
    {g : G} (hg : g ∈ Subgroup.normalizer (V₁ : Set G)) :
    ⁅fsuV T I, conjSubgroup (fsuV T I) g⁆ ≤ fsuV T I ⊓ conjSubgroup (fsuV T I) g := by
  have hQT := pCoreOf_normalizer_V₁_le_T h hV₁
  have hTV := SecA.T_le_normalizer_fsuV T I
  refine commutator_le_inf_of_le_normalizer ?_ ((conj_fsuV_le_pCoreOf hQ hg).trans (hQT.trans hTV))
  have h1 : conjSubgroup T g ≤ Subgroup.normalizer (conjSubgroup (fsuV T I) g : Set G) := by
    rw [← conjSubgroup_normalizer]
    exact conjSubgroup_mono hTV g
  have h2 : pCoreOf 2 (Subgroup.normalizer (V₁ : Set G)) ≤ conjSubgroup T g := by
    rw [← conjSubgroup_pCoreOf_normalizer hg]
    exact conjSubgroup_mono hQT g
  exact hQ.trans (h2.trans h1)

theorem exists_line_of_ne_bot (hF : Sp4Facts) (h1102 : Stmt11_0_2) (h1141 : Stmt11_4_1)
    (h : Hyp11 G T L I n) (hV₁ : IsVi T L I n 1 V₁) (hV₂ : IsVi T L I n 2 V₂)
    (hV₃ : IsVi T L I n 3 V₃) (hk : KindSp4 L (fsuV T I) n)
    (hQ : fsuV T I ≤ pCoreOf 2 (Subgroup.normalizer (V₁ : Set G)))
    {g : G} (hg : g ∈ Subgroup.normalizer (V₁ : Set G))
    (hne : ⁅V₃, conjSubgroup (fsuV T I) g⁆ ≠ ⊥) :
    ∃ l ∈ LOf L V₁, fsuV T I ⊓ conjSubgroup (fsuV T I) g = conjSubgroup V₂ l ∧
      ⁅fsuV T I, conjSubgroup (fsuV T I) g⁆ = conjSubgroup V₂ l := by
  have hc := conj_le_centralizer_conj (SecA.isElemAbelian_fsuV h).1 g
  have hcomm := commutator_fsuV_conj_le_inf h hV₁ hQ hg
  obtain ⟨l, hl, hC, hcl⟩ := hF.radLine G T L I n V₁ V₂ V₃
    (SecD.natSetting11_of h1102 h1141 h hV₁) hk hV₁ hV₂ hV₃ _ (conj_fsuV_le_ROf h hV₁ hQ hg)
    (hcomm.trans (inf_le_right.trans hc)) hne
  refine ⟨l, hl, le_antisymm ?_ (hcl ▸ hcomm), hcl⟩
  rw [← hC]
  exact inf_le_inf_left _ hc

theorem not_V₂_le_V₁ (hcV : fsuV T I ⊓ Subgroup.centralizer (L : Set G) = ⊥) (hn : 1 ≤ n)
    (hV₁ : IsVi T L I n 1 V₁) (hV₂ : IsVi T L I n 2 V₂) : ¬ V₂ ≤ V₁ := by
  intro hle
  have h1 := SecA.IsVi.relIndex_eq hV₁
  have h2 := SecA.IsVi.relIndex_eq hV₂
  rw [hcV, Subgroup.relIndex_bot_left] at h1 h2
  have h3 := Subgroup.card_le_of_le hle
  rw [h1, h2] at h3
  have h4 : 2 ^ (n * 2) ≤ 2 ^ (n * 1) := h3
  have h5 := (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).mp h4
  omega

end CFSG.Quasithin.Vol2.Ch11.SecF
