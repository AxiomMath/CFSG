module

public import CFSG.RankThree.PartTwo.Sec11.Item1115Proof

public section

namespace CFSG.RankThree.PartTwo.Sec11.Item1119Sym

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec11


theorem aux_TypeInv_inv_conj {G : Type} [Group G] (c u : G) (huc : u * c * u⁻¹ = c) :
    u⁻¹ * c * u = c := by
  calc u⁻¹ * c * u = u⁻¹ * (u * c * u⁻¹) * u := by rw [huc]
    _ = c := by group

theorem aux_TypeInv_conj_mpr {G : Type} [Group G] [Finite G] (c : G) (L : Subgroup G) (u e : G)
    (hu : u ∈ Subgroup.normalizer (L : Set G)) (huc : u * c * u⁻¹ = c) :
    YNotField c L e → YNotField c L (u * e * u⁻¹) := by
  rintro ⟨Ye, hYe, hKe, hnf⟩
  have hTh : Ye.map (MulAut.conj u).toMonoidHom ∈ thetaComponentsAt 3 (u * e * u⁻¹) := by
    have h1 := map_mem_thetaComponentsAt (MulAut.conj u) hYe
    rw [MulAut.conj_apply] at h1
    exact h1
  have hK : sec11K L (u * e * u⁻¹) ≤ Ye.map (MulAut.conj u).toMonoidHom := by
    have h2 := CFSG.RankThree.PartTwo.Sec11.Item1115Proof.sec11K_map_conj' hu e
    rw [MulAut.conj_apply] at h2
    rw [h2]
    exact Subgroup.map_mono hKe
  have hYY : (Ye.map (MulAut.conj u).toMonoidHom).map (MulAut.conj u⁻¹).toMonoidHom = Ye := by
    rw [Subgroup.map_map]
    have hid : (MulAut.conj u⁻¹).toMonoidHom.comp (MulAut.conj u).toMonoidHom =
        MonoidHom.id G := by
      ext x
      show u⁻¹ * (u * x * u⁻¹) * u⁻¹⁻¹ = x
      group
    rw [hid, Subgroup.map_id]
  have hc' : (MulAut.conj u⁻¹).toMonoidHom c = c := by
    show u⁻¹ * c * u⁻¹⁻¹ = c
    rw [inv_inv]
    exact aux_TypeInv_inv_conj c u huc
  refine ⟨Ye.map (MulAut.conj u).toMonoidHom, hTh, hK, ?_⟩
  intro hfu
  have hfu' := KFacts.InducesStdKind.map (MulAut.conj u⁻¹).toMonoidHom
    (Ye.map (MulAut.conj u).toMonoidHom)
    (KFacts.thetaQuotMap_iff_of_injective _ (MulAut.conj u⁻¹).injective
      (Ye.map (MulAut.conj u).toMonoidHom)) hfu
  rw [hYY, hc'] at hfu'
  exact hnf hfu'

theorem yNotField_inv {G : Type} [Group G] [Finite G] (c : G) (L : Subgroup G) (e : G) :
    YNotField c L e⁻¹ ↔ YNotField c L e := by
  have hzp : Subgroup.zpowers e⁻¹ = Subgroup.zpowers e := Subgroup.zpowers_inv
  have hcent : Subgroup.centralizer ({e⁻¹} : Set G) = Subgroup.centralizer ({e} : Set G) := by
    rw [GroupTheory.SteinbergBY.centralizer_singleton_eq_centralizer_zpowers, hzp,
      ← GroupTheory.SteinbergBY.centralizer_singleton_eq_centralizer_zpowers]
  have hK : sec11K L e⁻¹ = sec11K L e := by
    unfold sec11K
    rw [hcent]
  have hT : thetaComponentsAt 3 e⁻¹ = thetaComponentsAt 3 e := by
    unfold thetaComponentsAt
    rw [hcent]
  unfold YNotField
  rw [hK, hT]

theorem yNotField_conj {G : Type} [Group G] [Finite G] (c : G) (L : Subgroup G) (u e : G)
    (hu : u ∈ Subgroup.normalizer (L : Set G)) (huc : u * c * u⁻¹ = c) :
    YNotField c L (u * e * u⁻¹) ↔ YNotField c L e := by
  refine ⟨fun h => ?_, aux_TypeInv_conj_mpr c L u e hu huc⟩
  have hu' : u⁻¹ ∈ Subgroup.normalizer (L : Set G) := Subgroup.inv_mem _ hu
  have huc' : u⁻¹ * c * u⁻¹⁻¹ = c := by
    rw [inv_inv]
    exact aux_TypeInv_inv_conj c u huc
  have h2 := aux_TypeInv_conj_mpr c L u⁻¹ (u * e * u⁻¹) hu' huc' h
  have he : u⁻¹ * (u * e * u⁻¹) * u⁻¹⁻¹ = e := by group
  rw [he] at h2
  exact h2

end CFSG.RankThree.PartTwo.Sec11.Item1119Sym

end
