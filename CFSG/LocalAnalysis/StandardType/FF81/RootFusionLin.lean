module

public import CFSG.LocalAnalysis.StandardType.FF81.Defs
public import CFSG.Adapters.StatedSLTwoField
public import CFSG.LocalAnalysis.StandardType.FF81.RootFusionLinInv
public import CFSG.LocalAnalysis.StandardType.FF81.RootFusionLinMark
public import CFSG.LocalAnalysis.StandardType.FF81.RootFusionLinEmbed
public import CFSG.LocalAnalysis.StandardType.FF81.RootFusionLinNoEmb

public section

namespace CFSG.StandardType.FF81

open CFSG CFSG.Assembly CFSG.Open
open CFSG.Assembly.LowTwoRank (StatedClassicalModel)
open CFSG.StandardType.FrameRoute.FS81 (IsSylow2In)
open CFSG.StandardType.FF81.RootFusionLin

theorem exists_maximal_pGroup_of_isSylow2In {G : Type} {Γ : Type*} [Group G] [Group Γ]
    {Y S : Subgroup G}
    (hS : IsSylow2In S Y) (φ : ↥Y ≃* Γ) :
    ∃ S' : Subgroup Γ, IsPGroup 2 S' ∧ (∀ T : Subgroup Γ, IsPGroup 2 T → S' ≤ T → T = S') ∧
      ∀ y : ↥Y, φ y ∈ S' ↔ (y : G) ∈ S := by
  obtain ⟨hSY, hSp, hmax⟩ := hS
  have hmem : ∀ y : ↥Y, φ y ∈ (S.subgroupOf Y).map φ.toMonoidHom ↔ (y : G) ∈ S := by
    intro y
    rw [show φ y = φ.toMonoidHom y from rfl, Subgroup.mem_map_equiv]
    simp [Subgroup.mem_subgroupOf]
  refine ⟨(S.subgroupOf Y).map φ.toMonoidHom, ?_, ?_, hmem⟩
  · intro z
    have hz : ((φ.symm z.1 : ↥Y) : G) ∈ S := by
      have h := (hmem (φ.symm z.1)).1
      rw [MulEquiv.apply_symm_apply] at h
      exact h z.2
    obtain ⟨k, hk⟩ := hSp ⟨((φ.symm z.1 : ↥Y) : G), hz⟩
    refine ⟨k, ?_⟩
    have h1 : (φ.symm z.1 : ↥Y) ^ 2 ^ k = 1 := by
      apply Subtype.ext
      have h := congrArg Subtype.val hk
      rw [Subgroup.coe_pow, Subgroup.coe_one] at h
      rw [Subgroup.coe_pow, Subgroup.coe_one]
      exact h
    have h3 : (z : Γ) ^ 2 ^ k = 1 := by simpa using congrArg φ h1
    exact (OneMemClass.coe_eq_one).mp (by rw [Subgroup.coe_pow]; exact h3)
  · intro T hTp hST
    have hT₀Y : (T.comap φ.toMonoidHom).map Y.subtype ≤ Y := Subgroup.map_subtype_le _
    have hT₀p : IsPGroup 2 ((T.comap φ.toMonoidHom).map Y.subtype) := by
      rintro ⟨a, ha⟩
      obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp ha
      obtain ⟨k, hk⟩ := hTp ⟨φ y, hy⟩
      refine ⟨k, ?_⟩
      have h1 : (φ y) ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
      have h2 : y ^ 2 ^ k = 1 := by
        apply φ.injective
        rw [map_pow, map_one]
        exact h1
      apply Subtype.ext
      rw [Subgroup.coe_pow, Subgroup.coe_one]
      show (y : G) ^ 2 ^ k = 1
      rw [← Subgroup.coe_pow, h2]
      rfl
    have hST₀ : S ≤ (T.comap φ.toMonoidHom).map Y.subtype := by
      intro s hs
      refine Subgroup.mem_map.mpr ⟨⟨s, hSY hs⟩, ?_, rfl⟩
      exact hST ((hmem ⟨s, hSY hs⟩).2 hs)
    have hEq := hmax _ hT₀Y hT₀p hST₀
    apply le_antisymm
    · intro z hz
      have h1 : ((φ.symm z : ↥Y) : G) ∈ (T.comap φ.toMonoidHom).map Y.subtype :=
        Subgroup.mem_map.mpr ⟨φ.symm z, by simpa using hz, rfl⟩
      rw [hEq] at h1
      have := (hmem (φ.symm z)).2 h1
      simpa using this
    · exact hST

theorem rootFusionLin {G : Type} [Group G] (Y : Subgroup G) (N : ℕ) (hN : N = 8 ∨ N = 9)
    (hY : StatedClassicalModel ↥Y .PSL N 2 1) (S : Subgroup G) (hS : IsSylow2In S Y) (t : G)
    (htS : t ∈ S) (ht : orderOf t = 2) (hc : ∀ s ∈ S, s * t = t * s)
    (hCt : Subgroup.centralizer ({t} : Set G) ≤ Y) :
    ∀ g : G, g * t * g⁻¹ ∈ Y → ∃ y ∈ Y, g * t * g⁻¹ = y * t * y⁻¹ := by
  intro g hx
  have hN3 : 3 ≤ N := by omega
  have htY : t ∈ Y := hS.1 htS
  obtain ⟨φ₀⟩ := CFSG.Open.StatedAPI.nonempty_mulEquiv_specialLinear_zmod_two_of_psl hY
  obtain ⟨φ⟩ := nonempty_mulEquiv_gl_of_sl ⟨φ₀⟩
  have hxord : orderOf (g * t * g⁻¹) = 2 := by
    have h := orderOf_injective (MulAut.conj g).toMonoidHom (MulAut.conj g).injective t
    simpa [MulAut.conj_apply, ht] using h
  have hord : ∀ y : ↥Y, orderOf (y : G) = 2 → orderOf (φ y) = 2 := by
    intro y hy
    have h := orderOf_injective φ.toMonoidHom φ.injective y
    rw [Subgroup.orderOf_coe] at hy
    exact h.trans hy
  obtain ⟨S', hS'p, hS'max, hS'mem⟩ := exists_maximal_pGroup_of_isSylow2In hS φ
  have hT : IsConj (jN N 1) (φ ⟨t, htY⟩) := by
    refine isConj_jN_one_of_central_in_sylow N hN3 S' hS'p hS'max (φ ⟨t, htY⟩)
      ((hS'mem ⟨t, htY⟩).2 htS) (hord ⟨t, htY⟩ ht) ?_
    intro s hs
    obtain ⟨y, rfl⟩ := φ.surjective s
    have hy : (y : G) ∈ S := (hS'mem y).1 hs
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (hc _ hy)
  obtain ⟨r, hr1, h2r, hcj⟩ := exists_isConj_jN N (φ ⟨g * t * g⁻¹, hx⟩)
    (hord ⟨g * t * g⁻¹, hx⟩ hxord)
  by_cases hr : r = 1
  · subst hr
    obtain ⟨c, hc'⟩ := isConj_iff.mp (hT.symm.trans hcj)
    refine ⟨((φ.symm c : ↥Y) : G), (φ.symm c).2, ?_⟩
    have h := congrArg φ.symm hc'
    simp only [map_mul, map_inv, MulEquiv.symm_apply_apply] at h
    have h2 := congrArg Subtype.val h
    simpa using h2.symm
  · exfalso
    have hr2 : 2 ≤ r := by omega
    obtain ⟨eA⟩ := nonempty_mulEquiv_cent_of_isConj N r h2r hcj
    obtain ⟨eB⟩ := nonempty_mulEquiv_cent_of_isConj N 1 (by omega) hT
    obtain ⟨ψ, hψ⟩ := exists_injective_hom_of_centralizer_equiv Y φ t g htY hCt hx eA eB
    exact not_exists_injective_hom N r (N - 2 * r) hN hr2 (by omega) ⟨ψ, hψ⟩

end CFSG.StandardType.FF81

end
