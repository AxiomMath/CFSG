module

public import CFSG.LocalAnalysis.UniquenessCase.UC6G.S25
public import CFSG.LocalAnalysis.UniquenessCase.UCKInputs3

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC6G

open Subgroup CFSG.Open CFSG.ABGLocalTools
open CFSG.ASVolI.ChIJK (IsWeaklyClosedIn)
open CFSG.Yardstones.Mf4cdcdf2e013 (TheoremCAt)
open CFSG.LocalAnalysis.UniquenessCase.UC6
open CFSG.LocalAnalysis.UniquenessCase.UC22 (Data)

namespace Mz614

variable {G : Type} [Group G] [Finite G] {Dat : Data G} (m : Mz614 Dat)

theorem c625_of_k332' (hK : UCK.K332') (h69 : R6_9 Dat)
    (h623 : m.C623) (hr : 3 < m.r) : m.C625 := by
  haveI : Fact m.r.Prime := ⟨m.hr⟩
  have h5 : 5 ≤ m.r := by
    by_contra h
    have h4 : m.r = 4 := by omega
    exact absurd m.hr (by rw [h4]; norm_num)
  have hKM : CFSG.Open.IsKGroup ↥m.M := Dat.standing.kProper.isKGroup m.M m.M_ne_top
  set Z' : Subgroup ↥m.M := m.Z.subgroupOf m.M with hZ'
  have hZ'card : Nat.card Z' = m.r := by
    rw [hZ', Nat.card_congr (Subgroup.subgroupOfEquivOfLe m.Z_le_M).toEquiv]
    exact m.card_Z
  have hZ'p : IsPGroup m.r Z' :=
    IsPGroup.of_card (n := 1) (by rw [pow_one]; exact hZ'card)
  have hrank : CFSG.Open.pRank m.r (⊤ : Subgroup ↥m.M) ≤ 3 := by
    have h1 := pRank_map_subtype_uc6 m.hr m.M (⊤ : Subgroup ↥m.M)
    have h2 : (⊤ : Subgroup ↥m.M).map m.M.subtype = m.M := by
      rw [← MonoidHom.range_eq_map]; exact Subgroup.range_subtype _
    rw [h2] at h1
    rw [← h1]
    exact m.hk.pRank_le_three m.hr m.d.odd m.hrσ
  obtain ⟨S', hS'syl, hZS'⟩ := exists_isSylowOf_ge (p := m.r) (K := (⊤ : Subgroup ↥m.M))
    (Q := Z') (fun x _ => trivial) hZ'p
  have hS''p : IsPGroup m.r (S'.map m.M.subtype) := hS'syl.isPGroup.map _
  have hS''M : S'.map m.M.subtype ≤ m.M := Subgroup.map_subtype_le _
  obtain ⟨k, hkM, hk⟩ := exists_conj_le_of_isSylowOf m.d.sylow hS''M hS''p
  have hsix := m.hZ.sixteen h69
  have hS'comm : ∀ x ∈ S', x ^ m.r = 1 → ∀ y ∈ S', x * y = y * x := by
    intro x hx hxr y hy
    have hxR : k⁻¹ * (x : G) * k ∈ m.R := hk _ ⟨x, hx, rfl⟩
    have hxA : k⁻¹ * (x : G) * k ∈ m.Z ⊔ m.E := by
      refine hsix.2 _ hxR ?_
      have hx1 : (x : G) ^ m.r = 1 := by simpa using congrArg Subtype.val hxr
      have := conj_pow (a := k⁻¹) (b := (x : G)) (i := m.r)
      rw [inv_inv] at this
      rw [this, hx1]
      simp
    have hyR : k⁻¹ * (y : G) * k ∈ m.R := hk _ ⟨y, hy, rfl⟩
    have hc := hsix.1 _ hxA _ hyR
    apply Subtype.ext
    have h3 : k⁻¹ * ((x : G) * y) * k = k⁻¹ * ((y : G) * x) * k := by
      calc k⁻¹ * ((x : G) * y) * k = (k⁻¹ * x * k) * (k⁻¹ * y * k) := by group
        _ = (k⁻¹ * y * k) * (k⁻¹ * x * k) := hc
        _ = k⁻¹ * ((y : G) * x) * k := by group
    have h4 := congrArg (fun t => k * t * k⁻¹) h3
    simpa [mul_assoc] using h4
  have hS'rank : CFSG.Open.pRank m.r S' ≤ 3 :=
    le_trans (CFSG.PreuniquenessRankFour.Helpers.pRank_mono m.r m.hr (le_top : S' ≤ ⊤)) hrank
  have hS'wc : IsWeaklyClosedIn Z' S' := by
    intro g hg
    have hZk : CFSG.conjugate m.Z k ≤ m.R := by
      intro y hy
      have hz : k * y * k⁻¹ ∈ m.Z := mem_conjugate_iff_uc6.1 hy
      have hzS : (⟨k * y * k⁻¹, m.Z_le_M hz⟩ : ↥m.M) ∈ S' := hZS' hz
      have := hk _ ⟨_, hzS, rfl⟩
      simpa [mul_assoc] using this
    have hZgk : CFSG.conjugate m.Z ((g : G) * k) ≤ m.R := by
      intro y hy
      have hz : (g : G) * k * y * ((g : G) * k)⁻¹ ∈ m.Z := mem_conjugate_iff_uc6.1 hy
      have hwM : k * y * k⁻¹ ∈ m.M := by
        have e : k * y * k⁻¹ = (g : G)⁻¹ * ((g : G) * k * y * ((g : G) * k)⁻¹) * g := by group
        rw [e]
        exact m.M.mul_mem (m.M.mul_mem (m.M.inv_mem g.2) (m.Z_le_M hz)) g.2
      have hw' : (⟨k * y * k⁻¹, hwM⟩ : ↥m.M) ∈ CFSG.conjugate Z' g := by
        rw [mem_conjugate_iff_uc6]
        show (g : G) * (k * y * k⁻¹) * (g : G)⁻¹ ∈ m.Z
        have e : (g : G) * (k * y * k⁻¹) * (g : G)⁻¹ = (g : G) * k * y * ((g : G) * k)⁻¹ := by
          group
        rw [e]
        exact hz
      have := hk _ ⟨_, hg hw', rfl⟩
      simpa [mul_assoc] using this
    have hk1 := h623 k hZk
    have hk2 := h623 ((g : G) * k) hZgk
    have e1 : ∀ y : G, k * y * k⁻¹ ∈ m.Z ↔ y ∈ m.Z := fun y => by
      rw [← mem_conjugate_iff_uc6, hk1]
    have e2 : ∀ y : G, (g : G) * k * y * ((g : G) * k)⁻¹ ∈ m.Z ↔ y ∈ m.Z := fun y => by
      rw [← mem_conjugate_iff_uc6, hk2]
    ext x
    rw [mem_conjugate_iff_uc6]
    show (g : G) * (x : G) * (g : G)⁻¹ ∈ m.Z ↔ (x : G) ∈ m.Z
    have h1 := e2 (k⁻¹ * (x : G) * k)
    have h2 := e1 (k⁻¹ * (x : G) * k)
    have e3 : (g : G) * k * (k⁻¹ * (x : G) * k) * ((g : G) * k)⁻¹ =
        (g : G) * (x : G) * (g : G)⁻¹ := by
      group
    have e4 : k * (k⁻¹ * (x : G) * k) * k⁻¹ = (x : G) := by group
    rw [e3] at h1
    rw [e4] at h2
    exact h1.trans h2.symm
  have h1 := hK ↥m.M hKM m.r m.hr h5 S' hS'syl hS'comm hS'rank Z' hZS' hZ'card hS'wc
  show CFSG.Open.pRank m.r m.K = 1
  rw [m.K_eq_map_normalClosure, pRank_map_subtype_uc6 m.hr m.M]
  exact h1

end Mz614

end CFSG.LocalAnalysis.UniquenessCase.UC6G
