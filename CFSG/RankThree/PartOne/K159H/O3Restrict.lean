module

public import CFSG.ClassicalGroups.Orthogonal.Restrict
public import CFSG.RankThree.OrthogonalInvolutions.Dickson

public section

namespace CFSG.RankThree.PartOne.K159H

open QuadraticMap CFSG.ClassicalGroups.Orthogonal CFSG.RankThree.OrthogonalInvolutions Module

section Regular

variable {K V : Type} [Field K] [AddCommGroup V] [Module K V] {Q : QuadraticForm K V} {S : Submodule K V}

abbrev perp (Q : QuadraticForm K V) (S : Submodule K V) : Submodule K V :=
  LinearMap.BilinForm.orthogonal (polarBilin Q) S

theorem mem_perp_iff' {z : V} : z ∈ perp Q S ↔ ∀ x ∈ S, polar Q z x = 0 := by
  rw [LinearMap.BilinForm.mem_orthogonal_iff]
  constructor
  · intro h x hx
    have := h x hx
    rw [polarBilin_apply_apply] at this
    rw [polar_comm]
    exact this
  · intro h x hx
    show polarBilin Q x z = 0
    rw [polarBilin_apply_apply, polar_comm]
    exact h x hx

theorem isCompl_perp' [FiniteDimensional K V] (hS : (polarBilin (Q.restrict S)).Nondegenerate) :
    IsCompl S (perp Q S) := by
  have h : polarBilin (Q.comp S.subtype) = LinearMap.BilinForm.restrict (polarBilin Q) S := by
    refine LinearMap.ext₂ fun x y => ?_
    simp [polarBilin_apply_apply, polar]
  exact LinearMap.BilinForm.isCompl_orthogonal_of_restrict_nondegenerate
    (isSymm_polarBilin Q).isRefl (by rw [← h]; exact hS)

theorem eq_of_agree_on' [FiniteDimensional K V] (hS : (polarBilin (Q.restrict S)).Nondegenerate)
    {g h : V ≃ₗ[K] V} (hgh : ∀ x ∈ S, g x = h x)
    (hg : ∀ z, (∀ x ∈ S, polar Q z x = 0) → g z = z)
    (hh : ∀ z, (∀ x ∈ S, polar Q z x = 0) → h z = z) : g = h := by
  refine LinearEquiv.ext fun v => ?_
  have hv : v ∈ S ⊔ perp Q S := by
    rw [(isCompl_perp' hS).sup_eq_top]
    trivial
  obtain ⟨x, hx, z, hz, rfl⟩ := Submodule.mem_sup.mp hv
  rw [map_add, map_add, hgh x hx, hg z (mem_perp_iff'.mp hz), hh z (mem_perp_iff'.mp hz)]

@[expose] def resAut (g : V ≃ₗ[K] V) (hg : ∀ x, x ∈ S ↔ g x ∈ S) : S ≃ₗ[K] S where
  toFun r := ⟨g r, (hg r).mp r.2⟩
  map_add' x y := Subtype.ext (map_add g (x : V) (y : V))
  map_smul' c x := Subtype.ext (map_smul g c (x : V))
  invFun r := ⟨g⁻¹ r, (hg (g⁻¹ r)).mpr (by rw [LinearEquiv.apply_inv_apply']; exact r.2)⟩
  left_inv r := Subtype.ext (LinearEquiv.inv_apply_apply' g (r : V))
  right_inv r := Subtype.ext (LinearEquiv.apply_inv_apply' g (r : V))

theorem coe_resAut (g : V ≃ₗ[K] V) (hg : ∀ x, x ∈ S ↔ g x ∈ S) (r : S) :
    ((resAut g hg r : S) : V) = g r := rfl

theorem resAut_mem_orth {g : V ≃ₗ[K] V} (hgO : g ∈ TauCeti.QuadraticMap.orthogonalGroup Q)
    (hg : ∀ x, x ∈ S ↔ g x ∈ S) : resAut g hg ∈ TauCeti.QuadraticMap.orthogonalGroup (Q.restrict S) := by
  refine TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mpr fun x => ?_
  show Q (g x) = Q x
  exact TauCeti.QuadraticMap.map_app_of_mem_orthogonalGroup hgO x

theorem finrank_commSpace_resAut [FiniteDimensional K V] (hS : (polarBilin (Q.restrict S)).Nondegenerate)
    {g : V ≃ₗ[K] V} (hg : ∀ x, x ∈ S ↔ g x ∈ S) (hfix : ∀ z, (∀ x ∈ S, polar Q z x = 0) → g z = z) :
    finrank K (commSpace (resAut g hg)) = finrank K (commSpace g) := by
  have h : commSpace g = (commSpace (resAut g hg)).map S.subtype := by
    ext x
    constructor
    · intro hx
      obtain ⟨v, rfl⟩ := mem_commSpace.mp hx
      have hv : v ∈ S ⊔ perp Q S := by
        rw [(isCompl_perp' hS).sup_eq_top]
        trivial
      obtain ⟨s, hs, z, hz, rfl⟩ := Submodule.mem_sup.mp hv
      refine ⟨resAut g hg ⟨s, hs⟩ - ⟨s, hs⟩, sub_mem_commSpace _ _, ?_⟩
      simp only [Submodule.subtype_apply, Submodule.coe_sub, coe_resAut]
      rw [map_add, hfix z (mem_perp_iff'.mp hz)]
      abel
    · rintro ⟨y, hy, rfl⟩
      obtain ⟨v, rfl⟩ := mem_commSpace.mp hy
      exact mem_commSpace.mpr ⟨(v : V), by simp [coe_resAut]⟩
  rw [h, Submodule.finrank_map_subtype_eq]

theorem resAut_mem_omega [CharP K 2] [FiniteDimensional K V] {hQ : (polarBilin Q).Nondegenerate}
    (hS : (polarBilin (Q.restrict S)).Nondegenerate) {g : V ≃ₗ[K] V}
    (hgΩ : g ∈ CFSG.RankThree.OrthogonalInvolutions.omegaGroup Q hQ) (hg : ∀ x, x ∈ S ↔ g x ∈ S)
    (hfix : ∀ z, (∀ x ∈ S, polar Q z x = 0) → g z = z) :
    resAut g hg ∈ CFSG.RankThree.OrthogonalInvolutions.omegaGroup (Q.restrict S) hS :=
  ⟨resAut_mem_orth hgΩ.1 hg, by rw [finrank_commSpace_resAut hS hg hfix]; exact hgΩ.2⟩

theorem elementary_restrict_le_omega [CharP K 2] [FiniteDimensional K V] {hQ : (polarBilin Q).Nondegenerate}
    (hS : (polarBilin (Q.restrict S)).Nondegenerate)
    (hE : elementaryGroup Q ≤ CFSG.RankThree.OrthogonalInvolutions.omegaGroup Q hQ) :
    elementaryGroup (Q.restrict S) ≤ CFSG.RankThree.OrthogonalInvolutions.omegaGroup (Q.restrict S) hS := by
  intro g' hg'
  obtain ⟨g, hgE, hgx, hgz⟩ := exists_extend_of_mem_elementaryGroup_restrict hg'
  have hgS : ∀ x, x ∈ S ↔ g x ∈ S := by
    intro x
    constructor
    · intro hx
      rw [hgx ⟨x, hx⟩]
      exact (g' ⟨x, hx⟩).2
    · intro hx
      have hv : x ∈ S ⊔ perp Q S := by
        rw [(isCompl_perp' hS).sup_eq_top]
        trivial
      obtain ⟨s, hs, z, hz, rfl⟩ := Submodule.mem_sup.mp hv
      have h1 : g s ∈ S := by
        rw [hgx ⟨s, hs⟩]
        exact (g' ⟨s, hs⟩).2
      have h2 : z ∈ S := by
        have : g (s + z) - g s = z := by
          rw [map_add, hgz z (mem_perp_iff'.mp hz)]
          abel
        rw [← this]
        exact S.sub_mem hx h1
      have h3 : z = 0 := Submodule.disjoint_def.mp (isCompl_perp' hS).disjoint z h2 hz
      rw [h3, add_zero]
      exact hs
  have : resAut g hgS = g' := LinearEquiv.ext fun x => Subtype.ext (hgx x)
  rw [← this]
  exact resAut_mem_omega hS (hE hgE) hgS hgz

theorem comm_of_resAut_comm [FiniteDimensional K V] (hS : (polarBilin (Q.restrict S)).Nondegenerate)
    {g k : V ≃ₗ[K] V} (hg : ∀ x, x ∈ S ↔ g x ∈ S) (hk : ∀ x, x ∈ S ↔ k x ∈ S)
    (hgfix : ∀ z, (∀ x ∈ S, polar Q z x = 0) → g z = z) (hkfix : ∀ z, (∀ x ∈ S, polar Q z x = 0) → k z = z)
    (hcomm : resAut g hg * resAut k hk = resAut k hk * resAut g hg) : g * k = k * g := by
  refine eq_of_agree_on' hS (fun x hx => ?_) (fun z hz => ?_) (fun z hz => ?_)
  · have := congrArg (fun e : S ≃ₗ[K] S => ((e ⟨x, hx⟩ : S) : V)) hcomm
    exact this
  · rw [LinearEquiv.mul_apply, hkfix z hz, hgfix z hz]
  · rw [LinearEquiv.mul_apply, hgfix z hz, hkfix z hz]

theorem coe_eichler_restrict {u w : V} (hu : Q u = 0) (hw : polar Q u w = 0) (huS : u ∈ S) (hwS : w ∈ S)
    (x : S) :
    ((eichler (Q.restrict S) ⟨u, huS⟩ ⟨w, hwS⟩ x : S) : V) = eichler Q u w x := by
  have hu' : (Q.restrict S) ⟨u, huS⟩ = 0 := hu
  have hw' : polar (Q.restrict S) ⟨u, huS⟩ ⟨w, hwS⟩ = 0 := by rw [polar_restrict]; exact hw
  rw [eichler_apply (Q := Q.restrict S) hu' hw', eichler_apply hu hw]
  simp [polar_restrict]

end Regular

section DicksonOne

variable {K W : Type} [Field K] [AddCommGroup W] [Module K W] [FiniteDimensional K W] [CharP K 2]

theorem dicksonHom_eq_one_of_mem_omega {Q' : QuadraticForm K W} (hQ' : (polarBilin Q').Nondegenerate)
    {g : W ≃ₗ[K] W} (hg : g ∈ CFSG.RankThree.OrthogonalInvolutions.omegaGroup Q' hQ') :
    CFSG.RankThree.OrthogonalInvolutions.dicksonHom Q' hQ' ⟨g, hg.1⟩ = 1 := by
  have : (⟨g, hg.1⟩ : TauCeti.QuadraticMap.orthogonalGroup Q') ∈
      (CFSG.RankThree.OrthogonalInvolutions.dicksonHom Q' hQ').ker := by
    rw [CFSG.RankThree.OrthogonalInvolutions.dicksonHom_ker, Subgroup.mem_subgroupOf]
    exact hg
  exact MonoidHom.mem_ker.mp this

end DicksonOne

end CFSG.RankThree.PartOne.K159H
