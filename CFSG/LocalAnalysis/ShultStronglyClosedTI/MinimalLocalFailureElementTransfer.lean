module

public import CFSG.Mathlib.GroupTheory.Focal
public import Mathlib.GroupTheory.IndexNormal

public noncomputable section

namespace CFSG.ShultStronglyClosedTI

open scoped IsMulCommutative

variable {G : Type*} [Group G] [Finite G]

theorem element_fusion_index_two_transfer_internal
    (T : Sylow 2 G) (M : Subgroup G) (hTM : (T : Subgroup G) ≤ M)
    (hfusion : ∀ x : G, x ∈ M → (∃ n : ℕ, orderOf x = 2 ^ n) →
      ∀ g : G, g⁻¹ * x * g ∈ M → ∃ m ∈ M, g⁻¹ * x * g = m⁻¹ * x * m)
    (K : Subgroup M) (hK : K.index = 2) :
    ∃ N : Subgroup G, N.Normal ∧ N.index = 2 := by
  classical
  let : K.Normal := Subgroup.normal_of_index_eq_two hK
  let Q := M ⧸ K
  let q : M →* Q := QuotientGroup.mk' K
  have hQcard : Nat.card Q = 2 := hK
  let : IsMulCommutative Q := (isCyclic_of_prime_card hQcard).isMulCommutative
  let j : (T : Subgroup G) →* M := Subgroup.inclusion hTM
  let f : (T : Subgroup G) →* Q := q.comp j
  let P : Sylow 2 M := T.subtype hTM
  let D : Sylow 2 Q := P.mapSurjective (f := q) (QuotientGroup.mk'_surjective K)
  have htwo : IsPGroup 2 Q := IsPGroup.of_card (n := 1) (by
    simpa only [pow_one] using hQcard)
  have hDtop : (D : Subgroup Q) = ⊤ :=
    (D.is_maximal' (htwo.to_subgroup (⊤ : Subgroup Q)) le_top).symm
  have hf : Function.Surjective f := by
    intro a
    have ha : a ∈ (D : Subgroup Q) := by rw [hDtop]; trivial
    change a ∈ (P : Subgroup M).map q at ha
    obtain ⟨t, ht, hta⟩ := Subgroup.mem_map.mp ha
    refine ⟨⟨t.val, ht⟩, ?_⟩
    exact hta
  have hfocal : (T : Subgroup G).focalSubgroup ≤ f.ker.map (T : Subgroup G).subtype := by
    rw [Subgroup.focalSubgroup_eq_closure_isConj, Subgroup.closure_le]
    rintro a ⟨x, hx, y, hy, hxy, rfl⟩
    obtain ⟨g, hgy⟩ := isConj_iff.mp hxy
    have hxorder : ∃ n : ℕ, orderOf x = 2 ^ n := by
      obtain ⟨n, hn⟩ := T.isPGroup'.exists_orderOf_eq_pow
        (⟨x, hx⟩ : (T : Subgroup G))
      exact ⟨n, (Subgroup.orderOf_coe (⟨x, hx⟩ : (T : Subgroup G))).trans hn⟩
    have hconj : g⁻¹⁻¹ * x * g⁻¹ = y := by simpa only [inv_inv] using hgy
    obtain ⟨m, hm, hym⟩ := hfusion x (hTM hx) hxorder g⁻¹ (hconj.symm ▸ hTM hy)
    have hyquot : f (⟨y, hy⟩ : (T : Subgroup G)) =
        f (⟨x, hx⟩ : (T : Subgroup G)) := by
      let xM : M := ⟨x, hTM hx⟩
      let yM : M := ⟨y, hTM hy⟩
      let mM : M := ⟨m, hm⟩
      have hyM : yM = mM⁻¹ * xM * mM := Subtype.ext (hconj.symm.trans hym)
      change q yM = q xM
      rw [hyM, map_mul, map_mul, map_inv,
        mul_comm (q mM)⁻¹ (q xM), mul_assoc, inv_mul_cancel, mul_one]
    have hker : (⟨x⁻¹ * y, (T : Subgroup G).mul_mem ((T : Subgroup G).inv_mem hx) hy⟩ :
        (T : Subgroup G)) ∈ f.ker := by
      change f ((⟨x, hx⟩ : (T : Subgroup G))⁻¹ * ⟨y, hy⟩) = 1
      rw [map_mul, map_inv, hyquot, inv_mul_cancel]
    exact Subgroup.mem_map.mpr ⟨_, hker, rfl⟩
  have hF : (T : Subgroup G).focalSubgroupOf ≤ f.ker := by
    intro a ha
    have haambient : (a : G) ∈ (T : Subgroup G).focalSubgroup := ha
    obtain ⟨b, hb, hba⟩ := Subgroup.mem_map.mp (hfocal haambient)
    exact (Subtype.ext hba : b = a) ▸ hb
  let l : ((T : Subgroup G) ⧸ (T : Subgroup G).focalSubgroupOf) →* Q :=
    QuotientGroup.lift (T : Subgroup G).focalSubgroupOf f hF
  have hl : Function.Surjective l := by
    intro a
    obtain ⟨t, hta⟩ := hf a
    exact ⟨QuotientGroup.mk t, hta⟩
  let v : G →* Q := l.comp (T : Subgroup G).transferFocal
  have hv : Function.Surjective v := hl.comp (Subgroup.transferFocal_surjective T)
  refine ⟨v.ker, inferInstance, ?_⟩
  rw [Subgroup.index_ker, MonoidHom.range_eq_top.mpr hv, Subgroup.card_top]
  exact hQcard

theorem element_fusion_index_two_transfer
    (T : Sylow 2 G) (M : Subgroup G) (hTM : (T : Subgroup G) ≤ M)
    (hfusion : ∀ x : G, x ∈ M → (∃ n : ℕ, orderOf x = 2 ^ n) →
      ∀ g : G, g⁻¹ * x * g ∈ M → ∃ m ∈ M, g⁻¹ * x * g = m⁻¹ * x * m)
    (K : Subgroup G) (_hKM : K ≤ M) (hK : (K.subgroupOf M).index = 2) :
    ∃ N : Subgroup G, N.Normal ∧ N.index = 2 :=
  element_fusion_index_two_transfer_internal T M hTM hfusion (K.subgroupOf M) hK

end CFSG.ShultStronglyClosedTI
