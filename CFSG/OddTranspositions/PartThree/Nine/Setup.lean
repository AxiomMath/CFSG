module

public import CFSG.OddTranspositions.PartThree.Nine.Statements
public import CFSG.GroupTheory.PResidualNormalizer
public import CFSG.OddTranspositions.PartThree.HalphaCentralizer

public section

namespace CFSG.OddTranspositions.PartThree.Nine

open CFSG.Timmesfeld CFSG.Timmesfeld.Bridge CFSG.Timmesfeld.Bridge.Asc72

variable {G : Type} [Group G] [Finite G] {D : Set G}

omit [Finite G] in
theorem DalphaStar_eq_commSet (hC : HypothesisC D) (hα : hC.alpha = {hC.d}) :
    DalphaStar D hC.alpha = commSet D hC.d := by
  rw [hα]
  ext x
  constructor
  · rintro ⟨β, ⟨⟨g, rfl⟩, hβD, hβne, hβc⟩, hxβ⟩
    rw [Set.smul_set_singleton] at hβD hβne hxβ hβc
    rw [Set.mem_singleton_iff] at hxβ
    subst hxβ
    refine ⟨hβD rfl, (hβc hC.d rfl _ rfl).symm, fun h => hβne ?_⟩
    rw [h]
  · rintro ⟨hxD, hxc, hxne⟩
    obtain ⟨c, hc⟩ := isConj_iff.mp (isConj_of_isClass hC.setup.isClass hC.hd hxD)
    refine ⟨{x}, ⟨⟨ConjAct.toConjAct c, ?_⟩, ?_, ?_, ?_⟩, rfl⟩
    · rw [Set.smul_set_singleton, ConjAct.toConjAct_smul, hc]
    · simpa using hxD
    · simpa using hxne
    · rintro a rfl b rfl
      exact hxc.symm

theorem d_mem_Halpha (hC : HypothesisC D) (h3 : Conclusion9_3 D hC) :
    hC.d ∈ Halpha D hC.alpha := by
  have hu : hC.d ∈ (CFSG.pCore 2 (Halpha D hC.alpha)).map (Halpha D hC.alpha).subtype := by
    rw [h3.2.1]
    exact Subgroup.mem_zpowers _
  obtain ⟨x, -, hx⟩ := Subgroup.mem_map.mp hu
  rw [← hx]
  exact x.2

theorem mem_or_mul_mem_of_conclusion9_3 (hC : HypothesisC D) (h3 : Conclusion9_3 D hC) {h : G}
    (hh : h ∈ Halpha D hC.alpha) :
    h ∈ CFSG.Quasithin.pResidualOf 2 (Halpha D hC.alpha) ∨
      hC.d * h ∈ CFSG.Quasithin.pResidualOf 2 (Halpha D hC.alpha) := by
  set L := CFSG.Quasithin.pResidualOf 2 (Halpha D hC.alpha)
  set u := hC.d
  have hL : L ≤ Halpha D hC.alpha := Subgroup.map_subtype_le _
  have huH : u ∈ Halpha D hC.alpha := d_mem_Halpha hC h3
  have hcomm : ∀ a ∈ Halpha D hC.alpha, u * a = a * u := fun a ha =>
    (Subgroup.mem_centralizer_singleton_iff.mp (PartThree.Halpha_le_centralizer_d hC ha)).symm
  have hu2 : u * u = 1 := hC.setup.oddT.mul_self_eq_one hC.hd
  have hui : u⁻¹ = u := hC.setup.oddT.inv_eq hC.hd
  have hmemH : ∀ a, u * a ∈ L → a ∈ Halpha D hC.alpha := fun a ha => by
    have : a = u * (u * a) := by rw [← mul_assoc, hu2, one_mul]
    rw [this]
    exact (Halpha D hC.alpha).mul_mem huH (hL ha)
  let K : Subgroup G :=
    { carrier := {g | g ∈ L ∨ u * g ∈ L}
      one_mem' := Or.inl L.one_mem
      mul_mem' := by
        rintro a b (ha | ha) (hb | hb)
        · exact Or.inl (L.mul_mem ha hb)
        · right
          have : u * (a * b) = a * (u * b) := by
            rw [← mul_assoc, hcomm a (hL ha), mul_assoc]
          rw [this]
          exact L.mul_mem ha hb
        · right
          rw [← mul_assoc]
          exact L.mul_mem ha hb
        · left
          have hc := hcomm a (hmemH a ha)
          have : a * b = (u * a) * (u * b) := by
            calc a * b = (u * u) * a * b := by rw [hu2, one_mul]
              _ = u * (u * a) * b := by group
              _ = u * (a * u) * b := by rw [hc]
              _ = (u * a) * (u * b) := by group
          rw [this]
          exact L.mul_mem ha hb
      inv_mem' := by
        rintro a (ha | ha)
        · exact Or.inl (L.inv_mem ha)
        · right
          have hc := hcomm a⁻¹ ((Halpha D hC.alpha).inv_mem (hmemH a ha))
          have : u * a⁻¹ = (u * a)⁻¹ := by rw [mul_inv_rev, hui, hc]
          rw [this]
          exact L.inv_mem ha }
  have hle : Subgroup.zpowers u ⊔ L ≤ K := by
    refine sup_le ?_ ?_
    · rw [Subgroup.zpowers_le]
      exact Or.inr (by rw [hu2]; exact L.one_mem)
    · intro l hl
      exact Or.inl hl
  rw [← h3.2.2.1] at hh
  exact hle hh

theorem mul_mem_of_mem_commSet (hC : HypothesisC D) (h3 : Conclusion9_3 D hC) {x : G}
    (hx : x ∈ commSet D hC.d) :
    hC.d * x ∈ CFSG.Quasithin.pResidualOf 2 (Halpha D hC.alpha) := by
  set L := CFSG.Quasithin.pResidualOf 2 (Halpha D hC.alpha)
  have hstar := DalphaStar_eq_commSet hC h3.1
  have hxs : x ∈ DalphaStar D hC.alpha := hstar ▸ hx
  have hxH : x ∈ Halpha D hC.alpha := Subgroup.subset_closure hxs
  refine (mem_or_mul_mem_of_conclusion9_3 hC h3 hxH).resolve_left fun hxL => ?_
  have hDL : DalphaStar D hC.alpha ⊆ L := by
    intro y hy
    obtain ⟨h, hh, rfl⟩ := hC.Halpha_transitive x hxs y hy
    exact (Subgroup.mem_normalizer_iff.mp (CFSG.Quasithin.normalizer_le_normalizer_pResidualOf 2 _
      (Subgroup.le_normalizer hh)) x).mp hxL
  have hHL : Halpha D hC.alpha ≤ L := Subgroup.closure_le _ |>.mpr hDL
  have huL : hC.d ∈ L := hHL (d_mem_Halpha hC h3)
  exact hC.setup.oddT.ne_one hC.hd
    (Subgroup.disjoint_def.mp h3.2.2.2 (Subgroup.mem_zpowers _) huL)

end CFSG.OddTranspositions.PartThree.Nine
