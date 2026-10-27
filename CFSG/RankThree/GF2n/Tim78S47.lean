module

public import CFSG.RankThree.GF2n.Tim78S46

public section

namespace CFSG.RankThree.GF2n.Tim78

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.RankThree.GF2n
open scoped commutatorElement

variable {G : Type} [Group G]

namespace Hyp4

variable [Finite G] {M B Q P T : Subgroup G} (H : Hyp4 M B Q P T)
include H

section Root


theorem le_P_of_inf_conj_P_eq_bot (hCen : BenderCenterInput) (hU : UnitaryTwoGenerationInput)
    {g : G} (hBgB : conjSubgroup g B ≠ B) (hTMg : T ≤ conjSubgroup g M)
    (hPgT : conjSubgroup g P ⊓ T = ⊥) : conjSubgroup g B ≤ P := by
  set Bg := conjSubgroup g B with hBgdef
  set Tg := conjSubgroup g T with hTgdef
  set Pg := conjSubgroup g P with hPgdef
  have hBBg : B ⊓ Bg = ⊥ := inf_conjSubgroup_eq_bot_of_isTI H.ti hBgB
  have hBMg : B ≤ conjSubgroup g M := H.B_le_T.trans hTMg
  have hTNTg : T ≤ Subgroup.normalizer (Tg : Set G) := fun t ht =>
    mem_normalizer_conj_of_mem_conj H.M_le_normalizer_T (hTMg ht)
  have hTNPg : T ≤ Subgroup.normalizer (Pg : Set G) := fun t ht =>
    mem_normalizer_conj_of_mem_conj H.M_le_normalizer_P (hTMg ht)
  have hTgT : Tg ⊓ T = ⊥ := by
    by_contra hne
    have hne' : T ⊓ Tg ≠ ⊥ := by rwa [inf_comm]
    obtain ⟨b, hbD, hbB, hb1⟩ := H.exists_mem_B_of_normalizes H.T_le_Q H.B_le_T
      H.M_le_normalizer_T (inf_le_left : T ⊓ Tg ≤ T) hne'
      (fun t ht => mem_normalizer_inf (Subgroup.le_normalizer ht) (hTNTg ht))
    have : b ∈ B ⊓ Tg := ⟨hbB, hbD.2⟩
    rw [H.inf_B_conj_T_eq_bot hCen hU hBgB, Subgroup.mem_bot] at this
    exact hb1 this
  have hmhoT : CFSG.GroupTheory.HuppertProduct.mho T 2 = B :=
    H.mho_eq_B_of_ne H.B_le_T H.T_le_Q H.M_le_normalizer_T H.B_ne_T
  have hXP := fun {y : G} (hy : y ∈ T) =>
    H.comm_sq_mem_conj H.B_le_P H.P_le_Q hTNPg hPgT hy
  have hXT := fun {y : G} (hy : y ∈ T) =>
    H.comm_sq_mem_conj H.B_le_T H.T_le_Q hTNTg hTgT hy
  have hQg : conjSubgroup g Q = Pg ⊔ Tg := by
    rw [H.Q_eq_sup]
    exact Subgroup.map_sup _ _ _
  have hTgNPg : Tg ≤ Subgroup.normalizer (Pg : Set G) := le_normalizer_of_comm fun s hs a ha =>
    H.conj_T_le_centralizer_conj_P g s hs a ha
  have hBgNormal : ∀ m ∈ conjSubgroup g M, ∀ b ∈ Bg, m * b * m⁻¹ ∈ Bg := fun m hm b hb =>
    (Subgroup.mem_normalizer_iff.mp
      (mem_normalizer_conj_of_mem_conj H.M_le_normalizer_B hm) b).mp hb
  have hgen : ∀ y ∈ T, ∀ s ∈ conjSubgroup g Q, ⁅y ^ 2, s⁆ ∈ Bg := by
    intro y hy s hs
    have hPcomm : ∀ s' ∈ Pg, ⁅y ^ 2, s'⁆ ∈ Bg := by
      intro s' hs'
      have hw := hXP hy s' hs'
      have hs'M : s' ∈ conjSubgroup g M := by
        rw [hPgdef, mem_conjSubgroup] at hs'
        rw [mem_conjSubgroup]
        exact H.P_le_M hs'
      have e : ⁅y ^ 2, s'⁆ = s' * (s'⁻¹ * (y ^ 2 * s' * (y ^ 2)⁻¹)) * s'⁻¹ := by
        simp only [commutatorElement_def]; group
      rw [e]
      exact hBgNormal s' hs'M _ hw
    have hTcomm : ∀ s' ∈ Tg, ⁅y ^ 2, s'⁆ ∈ Bg := by
      intro s' hs'
      have hw := hXT hy s' hs'
      have hs'M : s' ∈ conjSubgroup g M := by
        rw [hTgdef, mem_conjSubgroup] at hs'
        rw [mem_conjSubgroup]
        exact H.Q_le_M (H.T_le_Q hs')
      have e : ⁅y ^ 2, s'⁆ = s' * (s'⁻¹ * (y ^ 2 * s' * (y ^ 2)⁻¹)) * s'⁻¹ := by
        simp only [commutatorElement_def]; group
      rw [e]
      exact hBgNormal s' hs'M _ hw
    rw [hQg] at hs
    obtain ⟨s₁, hs₁, s₂, hs₂, rfl⟩ := exists_mul_of_mem_sup hTgNPg hs
    have hs₁M : s₁ ∈ conjSubgroup g M := by
      rw [hPgdef, mem_conjSubgroup] at hs₁
      rw [mem_conjSubgroup]
      exact H.P_le_M hs₁
    have e : ⁅y ^ 2, s₁ * s₂⁆ = ⁅y ^ 2, s₁⁆ * (s₁ * ⁅y ^ 2, s₂⁆ * s₁⁻¹) := by
      simp only [commutatorElement_def]; group
    rw [e]
    exact Bg.mul_mem (hPcomm s₁ hs₁) (hBgNormal s₁ hs₁M _ (hTcomm s₂ hs₂))
  have hall : ∀ b ∈ B, ∀ s ∈ conjSubgroup g Q, ⁅b, s⁆ ∈ Bg := by
    intro b hb s hs
    rw [← hmhoT] at hb
    refine Subgroup.closure_induction (p := fun b _ => ∀ s ∈ conjSubgroup g Q, ⁅b, s⁆ ∈ Bg)
      ?_ ?_ ?_ ?_ hb s hs
    · rintro _ ⟨y, hy, rfl⟩
      exact fun s hs => hgen y hy s hs
    · intro s _
      rw [commutatorElement_one_left]
      exact Bg.one_mem
    · intro b₁ b₂ hb₁ hb₂ ih₁ ih₂ s hs
      have hb₁B : b₁ ∈ B := hmhoT ▸ hb₁
      have e : ⁅b₁ * b₂, s⁆ = b₁ * ⁅b₂, s⁆ * b₁⁻¹ * ⁅b₁, s⁆ := by
        simp only [commutatorElement_def]; group
      rw [e]
      exact Bg.mul_mem (hBgNormal b₁ (hBMg hb₁B) _ (ih₂ s hs)) (ih₁ s hs)
    · intro b hb ih s hs
      have hbB : b ∈ B := hmhoT ▸ hb
      have e : ⁅b⁻¹, s⁆ = b⁻¹ * ⁅b, s⁆⁻¹ * b := by
        simp only [commutatorElement_def]; group
      rw [e]
      have := hBgNormal b⁻¹ (hBMg (B.inv_mem hbB)) _ (Bg.inv_mem (ih s hs))
      rwa [inv_inv] at this
  have hBQg := H.le_conj_Q_of_commutator_mem hBMg hall
  have h1 : conjSubgroup g⁻¹ B ≤ Q := by
    intro z hz
    rw [mem_conjSubgroup, inv_inv] at hz
    have := hBQg hz
    rwa [mem_conjSubgroup, show g⁻¹ * (g * z * g⁻¹) * g = z by group] at this
  have h2 : Bg ≤ Q := by
    have := H.conj_inv_le_Q h1
    rwa [inv_inv] at this
  exact H.conj_le_P h2

theorem tim78_4_7 (hCen : BenderCenterInput) (hU : UnitaryTwoGenerationInput) :
    ∀ g : G, conjSubgroup g B ⊓ Subgroup.centralizer (T : Set G) ≠ ⊥ → conjSubgroup g B ≤ P := by
  intro g hne
  by_contra hBgP
  have hBgB : conjSubgroup g B ≠ B := fun h => hBgP (by rw [h]; exact H.B_le_P)
  obtain ⟨⟨u, hu⟩, hu1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hne
  have hu1' : u ≠ 1 := fun h => hu1 (Subtype.ext h)
  obtain ⟨huBg, huC⟩ := Subgroup.mem_inf.mp hu
  have hTMg : T ≤ conjSubgroup g M := fun t ht =>
    H.centralizer_le_conj huBg hu1' (Subgroup.mem_centralizer_singleton_iff.mpr
      (Subgroup.mem_centralizer_iff.mp huC t ht))
  by_cases hBPg : B ⊓ conjSubgroup g P = ⊥
  ·
    have hTNPg : T ≤ Subgroup.normalizer (conjSubgroup g P : Set G) := fun t ht =>
      mem_normalizer_conj_of_mem_conj H.M_le_normalizer_P (hTMg ht)
    have hPgT : conjSubgroup g P ⊓ T = ⊥ := by
      by_contra hne'
      have hne'' : T ⊓ conjSubgroup g P ≠ ⊥ := by rwa [inf_comm]
      obtain ⟨b, hbD, hbB, hb1⟩ := H.exists_mem_B_of_normalizes H.T_le_Q H.B_le_T
        H.M_le_normalizer_T (inf_le_left : T ⊓ conjSubgroup g P ≤ T) hne''
        (fun t ht => mem_normalizer_inf (Subgroup.le_normalizer ht) (hTNPg ht))
      have : b ∈ B ⊓ conjSubgroup g P := ⟨hbB, hbD.2⟩
      rw [hBPg, Subgroup.mem_bot] at this
      exact hb1 this
    exact hBgP (H.le_P_of_inf_conj_P_eq_bot hCen hU hBgB hTMg hPgT)
  ·
    have h4 : conjSubgroup g⁻¹ B ⊓ P ≠ ⊥ := by
      intro hbot
      apply hBPg
      have : conjSubgroup g (conjSubgroup g⁻¹ B ⊓ P) = B ⊓ conjSubgroup g P := by
        rw [conjSubgroup_inf, ← conjSubgroup_mul, mul_inv_cancel, conjSubgroup_one]
      rw [← this, hbot]
      exact Subgroup.map_bot _
    have h5 := H.tim78_4_4 hCen hU g⁻¹ h4
    exact hBgP (by simpa using H.conj_inv_le_P_of_conj_le_P h5)

end Root

end Hyp4

end CFSG.RankThree.GF2n.Tim78
