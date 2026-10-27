module

public import CFSG.LocalAnalysis.WeakClosure81.W172Defs
public import CFSG.LocalAnalysis.WeakClosure81.W18Center

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.QuasithinUnique Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
  CFSG.LocalAnalysis.UniquenessCase.PartTwo

variable {G : Type} [Group G] [Finite G]

namespace Hyp183

variable {D : Data G} {V₀ V H : Subgroup G} {i : ℕ}

theorem w172_exists_gamma_not_le_kerMV (h : Hyp183 D V₀ V H i) :
    ∃ A₀ ∈ E3.gammaSet V i D.T, ¬ A₀ ≤ kerMV V H := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_contra hcon
  have h' : ∀ A₀, A₀ ∈ E3.gammaSet V i D.T → A₀ ≤ kerMV V H := by
    intro A₀ hA₀
    by_contra hle
    exact hcon ⟨A₀, hA₀, hle⟩
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
      isSylowOf_two_iff_isSylowIn.mpr h.isSylowIn_T
    exact isSylowOf_two_iff_isSylowIn.mp (hT.inf_of_le_normalizer hKH hHnormK)
  have hHM : H ≤ D.M := by
    intro x hx
    obtain ⟨k, hkK, n, hn, rfl⟩ := frattini_argument hKH hKn hS hx
    have hkM : k ∈ D.M := by
      rw [← h.setting.normalizer_eq]
      exact kerMV_le_normalizer V H hkK
    have hnM : n ∈ D.M := by
      have hnW : n ∈ normalizer (E3.wClos V i S : Set G) :=
        E3.normalizer_le_normalizer_wClos S hn.2
      rw [hW] at hnW
      exact h.normW hnW
    exact D.M.mul_mem hkM hnM
  exact h.notLe hHM

theorem w172_exists_conj_inf_le_T (h : Hyp183 D V₀ V H i) :
    ∃ g : G, conjSubgroup V g ⊓ H ≤ D.T ∧ ¬ conjSubgroup V g ⊓ H ≤ kerMV V H ∧
      E3.mQuot (conjSubgroup V g) (conjSubgroup V g ⊓ H) ≤ i := by
  classical
  obtain ⟨A₀, hA₀Γ, hA₀K⟩ := h.w172_exists_gamma_not_le_kerMV
  obtain ⟨hA₀T, g₀, hA₀Vg, hm₀⟩ := E3.mem_gammaSet_iff.mp hA₀Γ
  have hA₀H : A₀ ≤ H := hA₀T.trans h.hyp171.2.1
  have hA' : A₀ ≤ conjSubgroup V g₀ ⊓ H := le_inf hA₀Vg hA₀H
  have hA'K : ¬ conjSubgroup V g₀ ⊓ H ≤ kerMV V H :=
    fun hle => hA₀K (hA'.trans hle)
  have hVg : IsElemAbelian 2 (conjSubgroup V g₀) :=
    E3.isElemAbelian_conjSubgroup h.setting.isElemAbelian g₀
  have hp : IsPGroup 2 (conjSubgroup V g₀ ⊓ H : Subgroup G) :=
    (IsElemAbelian.isPGroup hVg).to_inf_left
  obtain ⟨h, hhH, hA'h⟩ :=
    E3.exists_le_conj_of_isSylowIn h.isSylowIn_T inf_le_right hp
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

end Hyp183

namespace MinCex172

variable {D : Data G} {V₀ V H : Subgroup G}

private theorem le_normalizer_kerMV (V H : Subgroup G) : H ≤ normalizer (kerMV V H : Set G) :=
  Subgroup.le_normalizer_iff.mpr fun _ hx _ hy => conj_mem_kerMV hx hy

theorem isSylowIn_inf_kerMV (c : MinCex172 D V₀ V H) :
    IsSylowIn 2 (D.T ⊓ kerMV V H) (kerMV V H) :=
  isSylowOf_two_iff_isSylowIn.mp
    ((isSylowOf_two_iff_isSylowIn.mpr c.hyp.isSylowIn_T).inf_of_le_normalizer
      (kerMV_le_self V H) (le_normalizer_kerMV V H))

theorem inf_kerMV_le_pCoreOf (c : MinCex172 D V₀ V H) : D.T ⊓ kerMV V H ≤ pCoreOf 2 H := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set K := kerMV V H with hKdef
  set S := D.T ⊓ K with hSdef
  have hTH : D.T ≤ H := c.hyp.hyp171.2.1
  have hKH : K ≤ H := kerMV_le_self V H
  have hKn : (K.subgroupOf H).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hKH).mpr (le_normalizer_kerMV V H)
  have hSyl : IsSylowIn 2 S K := c.isSylowIn_inf_kerMV
  have hTS : D.T ≤ normalizer (S : Set G) :=
    fun t ht => Subgroup.inf_normalizer_le_normalizer_inf
      ⟨Subgroup.le_normalizer ht, le_normalizer_kerMV V H (hTH ht)⟩
  have hNH : H ⊓ normalizer (S : Set G) = H := by
    by_contra hne
    have hlt : H ⊓ normalizer (S : Set G) < H := lt_of_le_of_ne inf_le_left hne
    have hle : H ⊓ normalizer (S : Set G) ≤ D.M := c.le_M_of_lt (le_inf hTH hTS) hlt
    apply c.hyp.notLe
    intro x hx
    obtain ⟨k, hk, n, hn, rfl⟩ := frattini_argument hKH hKn hSyl hx
    refine D.M.mul_mem ?_ (hle hn)
    rw [← c.hyp.setting.normalizer_eq]
    exact kerMV_le_normalizer V H hk
  exact CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2
    (inf_le_right.trans hKH) (inf_eq_left.mp hNH) hSyl.isPGroup

theorem inf_kerMV_eq (c : MinCex172 D V₀ V H) : D.T ⊓ kerMV V H = pCoreOf 2 H := by
  refine le_antisymm c.inf_kerMV_le_pCoreOf (le_inf c.hyp.pCoreOf_le_T ?_)
  exact (le_inf (Hyp183.pCoreOf_le_self H) c.hyp.pCoreOf_le_centralizer_eOmegaZ).trans
    c.hyp.inf_centralizer_eOmegaZ_le_kerMV

theorem inf_centralizer_eOmegaZ_eq (c : MinCex172 D V₀ V H) :
    D.T ⊓ Subgroup.centralizer (eOmegaZ H D.T : Set G) = pCoreOf 2 H := by
  refine le_antisymm (fun x hx => ?_)
    (le_inf c.hyp.pCoreOf_le_T c.hyp.pCoreOf_le_centralizer_eOmegaZ)
  rw [← c.inf_kerMV_eq]
  exact ⟨hx.1, c.hyp.inf_centralizer_eOmegaZ_le_kerMV ⟨c.hyp.hyp171.2.1 hx.1, hx.2⟩⟩

theorem le_pCoreOf_of_isPGroup (c : MinCex172 D V₀ V H) {X : Subgroup G} (hX : IsPGroup 2 X)
    (hXH : X ≤ H ⊓ Subgroup.centralizer (eOmegaZ H D.T : Set G)) : X ≤ pCoreOf 2 H := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hXK : X ≤ kerMV V H := hXH.trans c.hyp.inf_centralizer_eOmegaZ_le_kerMV
  have hSyl : IsSylowIn 2 (pCoreOf 2 H) (kerMV V H) := by
    rw [← c.inf_kerMV_eq]
    exact c.isSylowIn_inf_kerMV
  obtain ⟨k, hk, hle⟩ := E3.exists_le_conj_of_isSylowIn hSyl hXK hX
  have hkH : k ∈ H := kerMV_le_self V H hk
  have hconj : conjSubgroup (pCoreOf 2 H) k = pCoreOf 2 H :=
    conjSubgroup_eq_iff_mem_normalizer.mpr
      (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 H hkH)
  rwa [hconj] at hle

end MinCex172

end CFSG.LocalAnalysis.WeakClosure81

end
