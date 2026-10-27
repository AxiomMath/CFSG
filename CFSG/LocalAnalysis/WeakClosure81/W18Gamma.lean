module

public import CFSG.LocalAnalysis.WeakClosure81.W18Defs

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.QuasithinUnique Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
  CFSG.LocalAnalysis.UniquenessCase.PartTwo

variable {G : Type} [Group G] [Finite G]

namespace MinCex183

variable {D : Data G} {V₀ V H : Subgroup G} {i : ℕ}

theorem exists_gamma_not_le_kerMV (c : MinCex183 D V₀ V H i) :
    ∃ A₀ ∈ E3.gammaSet V i D.T, ¬ A₀ ≤ kerMV V H := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_contra h
  have h' : ∀ A₀, A₀ ∈ E3.gammaSet V i D.T → A₀ ≤ kerMV V H := by
    intro A₀ hA₀
    by_contra hle
    exact h ⟨A₀, hA₀, hle⟩
  let K := kerMV V H
  let S := D.T ⊓ K
  have hKH : K ≤ H := kerMV_le_self V H
  have hHnormK : H ≤ normalizer (K : Set G) :=
    Subgroup.le_normalizer_iff.mpr fun x hx y hy => conj_mem_kerMV hx hy
  have hKn : (K.subgroupOf H).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hKH).mpr hHnormK
  have hΓ : E3.gammaSet V i D.T = E3.gammaSet V i S := by
    apply le_antisymm
    · intro A hA
      have hAK : A ≤ K := h' A hA
      rw [E3.mem_gammaSet_iff] at hA ⊢
      exact ⟨le_inf hA.1 hAK, hA.2⟩
    · exact E3.gammaSet_mono inf_le_left
  have hW : E3.wClos V i S = E3.wClos V i D.T := by
    unfold E3.wClos
    rw [hΓ]
  have hS : IsSylowIn 2 S K := by
    have hT : CFSG.ABGLocalTools.IsSylowOf 2 D.T H :=
      isSylowOf_two_iff_isSylowIn.mpr c.hyp.isSylowIn_T
    exact isSylowOf_two_iff_isSylowIn.mp (hT.inf_of_le_normalizer hKH hHnormK)
  have hHM : H ≤ D.M := by
    intro x hx
    obtain ⟨k, hkK, n, hn, rfl⟩ := frattini_argument hKH hKn hS hx
    have hkM : k ∈ D.M := by
      rw [← c.hyp.setting.normalizer_eq]
      exact kerMV_le_normalizer V H hkK
    have hnM : n ∈ D.M := by
      have hnW : n ∈ normalizer (E3.wClos V i S : Set G) :=
        E3.normalizer_le_normalizer_wClos S hn.2
      rw [hW] at hnW
      exact c.hyp.normW hnW
    exact D.M.mul_mem hkM hnM
  exact c.hyp.notLe hHM

theorem exists_conj_inf_le_T (c : MinCex183 D V₀ V H i) :
    ∃ g : G, conjSubgroup V g ⊓ H ≤ D.T ∧ ¬ conjSubgroup V g ⊓ H ≤ kerMV V H ∧
      E3.mQuot (conjSubgroup V g) (conjSubgroup V g ⊓ H) ≤ i := by
  classical
  obtain ⟨A₀, hA₀Γ, hA₀K⟩ := c.exists_gamma_not_le_kerMV
  obtain ⟨hA₀T, g₀, hA₀Vg, hm₀⟩ := E3.mem_gammaSet_iff.mp hA₀Γ
  have hA₀H : A₀ ≤ H := hA₀T.trans c.hyp.hyp171.2.1
  have hA' : A₀ ≤ conjSubgroup V g₀ ⊓ H := le_inf hA₀Vg hA₀H
  have hA'K : ¬ conjSubgroup V g₀ ⊓ H ≤ kerMV V H :=
    fun hle => hA₀K (hA'.trans hle)
  have hVg : IsElemAbelian 2 (conjSubgroup V g₀) :=
    E3.isElemAbelian_conjSubgroup c.hyp.setting.isElemAbelian g₀
  have hp : IsPGroup 2 (conjSubgroup V g₀ ⊓ H : Subgroup G) :=
    (IsElemAbelian.isPGroup hVg).to_inf_left
  obtain ⟨h, hhH, hA'h⟩ :=
    E3.exists_le_conj_of_isSylowIn c.hyp.isSylowIn_T inf_le_right hp
  have hA'hT : conjSubgroup (conjSubgroup V g₀ ⊓ H) h⁻¹ ≤ D.T :=
    (E3.le_conjSubgroup_iff_inv_le h).mp hA'h
  have hHnormK : H ≤ normalizer (kerMV V H : Set G) :=
    Subgroup.le_normalizer_iff.mpr fun x hx y hy => conj_mem_kerMV hx hy
  have hKh : conjSubgroup (kerMV V H) h = kerMV V H :=
    conjSubgroup_eq_iff_mem_normalizer.mpr (hHnormK hhH)
  have hconj : conjSubgroup (conjSubgroup V g₀ ⊓ H) h⁻¹ =
      conjSubgroup V (g₀ * h⁻¹) ⊓ H := by
    rw [E3.conjSubgroup_inf, conjSubgroup_conjSubgroup,
      conjSubgroup_eq_iff_mem_normalizer.mpr (H.le_normalizer (H.inv_mem hhH))]
  refine ⟨g₀ * h⁻¹, ?_, ?_, ?_⟩
  · rw [hconj] at hA'hT
    exact hA'hT
  · intro hle
    apply hA'K
    have hle' : conjSubgroup (conjSubgroup V g₀ ⊓ H) h⁻¹ ≤ kerMV V H := by
      rwa [hconj]
    have hmono := E3.conjSubgroup_mono_left h hle'
    rw [hKh] at hmono
    rw [E3.conjSubgroup_inv_conj] at hmono
    exact hmono
  · have hA₀g : conjSubgroup A₀ h⁻¹ ≤ conjSubgroup V (g₀ * h⁻¹) ⊓ H := by
      rw [← hconj]
      exact E3.conjSubgroup_mono_left h⁻¹ hA'
    have hm : E3.mQuot (conjSubgroup V (g₀ * h⁻¹)) (conjSubgroup A₀ h⁻¹) = i := by
      have hmc := E3.mQuot_conjSubgroup (conjSubgroup V g₀) A₀ h⁻¹
      rw [conjSubgroup_conjSubgroup] at hmc
      rw [hmc, hm₀]
    calc E3.mQuot (conjSubgroup V (g₀ * h⁻¹)) (conjSubgroup V (g₀ * h⁻¹) ⊓ H)
        ≤ E3.mQuot (conjSubgroup V (g₀ * h⁻¹)) (conjSubgroup A₀ h⁻¹) := E3.mQuot_mono hA₀g
      _ = i := hm

end MinCex183

end CFSG.LocalAnalysis.WeakClosure81

end
