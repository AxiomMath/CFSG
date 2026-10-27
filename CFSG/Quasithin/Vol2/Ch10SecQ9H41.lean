module

public import CFSG.Quasithin.Vol2.Ch10SecQ9H40
public import CFSG.Quasithin.Vol2.Ch10SecQ9H39

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecC.C10P4F

open Matrix

theorem eq_X3_of_E3 {X : Subgroup (Matrix.SpecialLinearGroup (Fin 5) (ZMod 2))}
    (h3 : InvStd X 3) (htriv : ∀ x ∈ X, ∀ v, x • v + v ∈ stdE 5 3)
    (hq : Nonempty (↥X ⧸ CFSG.pCore 2 ↥X ≃* Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)))
    (hU : uniSL 5 ≤ Subgroup.normalizer (X : Set (Matrix.SpecialLinearGroup (Fin 5) (ZMod 2)))) :
    X = X3 := by
  obtain ⟨e⟩ := hq
  have hcard := card_eq_o2G_mul X e
  have hX : X ≤ stabStd 3 2 := le_stabStd_of_invStd (m := 3) (k := 2) h3
  have hbot : ∀ x : ↥(stabStd 3 2), x.1 ∈ X → botH 3 2 x = 1 := fun x hx =>
    Subtype.ext (botB_eq_one_of_triv (htriv x.1 hx))
  have himg := map_eq_top_of_sq hX (topH 3 2) (fun x hx ht =>
    sq_eq_one_of_blocks x.2 (congrArg Subtype.val ht) (congrArg Subtype.val (hbot x hx))) hcard
  refine le_antisymm (fun x hx => ⟨hX hx, botB_eq_one_of_triv (htriv x hx)⟩) fun g hg => ?_
  have hgx : topH 3 2 ⟨g, hg.1⟩ ∈ (X.subgroupOf (stabStd 3 2)).map (topH 3 2) := by
    rw [himg]; trivial
  obtain ⟨x, hx, hxt⟩ := hgx
  have hxX : x.1 ∈ X := Subgroup.mem_subgroupOf.mp hx
  obtain ⟨s, hs⟩ : ∃ s : ↥(stabStd 3 2), s = ⟨g, hg.1⟩ * x⁻¹ := ⟨_, rfl⟩
  have ht : topH 3 2 s = 1 := by rw [hs, map_mul, map_inv, hxt, mul_inv_cancel]
  have hb : botH 3 2 s = 1 := by
    rw [hs, map_mul, map_inv, hbot x hxX, inv_one, mul_one]
    exact Subtype.ext hg.2
  have hsX : s.1 ∈ X := by
    rw [eq_utSL_of_blocks s.2 (congrArg Subtype.val ht) (congrArg Subtype.val hb)]
    exact utSL_mem_of_E3 h3 htriv ⟨e⟩ hU _
  have hg' : g = s.1 * x.1 := by
    rw [hs, Subgroup.coe_mul, Subgroup.coe_inv, inv_mul_cancel_right]
  rw [hg']
  exact X.mul_mem hsX hxX

theorem eq_X2_of_E2 {X : Subgroup (Matrix.SpecialLinearGroup (Fin 5) (ZMod 2))}
    (h2 : InvStd X 2) (htriv : ∀ x ∈ X, ∀ v ∈ stdE 5 2, x • v = v)
    (hq : Nonempty (↥X ⧸ CFSG.pCore 2 ↥X ≃* Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)))
    (hU : uniSL 5 ≤ Subgroup.normalizer (X : Set (Matrix.SpecialLinearGroup (Fin 5) (ZMod 2)))) :
    X = X2 := by
  obtain ⟨e⟩ := hq
  have hcard := card_eq_o2G_mul X e
  have hX : X ≤ stabStd 2 3 := le_stabStd_of_invStd (m := 2) (k := 3) h2
  have htop : ∀ x : ↥(stabStd 2 3), x.1 ∈ X → topH 2 3 x = 1 := fun x hx =>
    Subtype.ext (topB_eq_one_of_fix fun j => htriv x.1 hx _ (castAdd_mem_stdE (k := 3) j))
  have himg := map_eq_top_of_sq hX (botH 2 3) (fun x hx hb =>
    sq_eq_one_of_blocks x.2 (congrArg Subtype.val (htop x hx)) (congrArg Subtype.val hb)) hcard
  refine le_antisymm (fun x hx => ⟨hX hx, congrArg Subtype.val (htop ⟨x, hX hx⟩ hx)⟩)
    fun g hg => ?_
  have hgx : botH 2 3 ⟨g, hg.1⟩ ∈ (X.subgroupOf (stabStd 2 3)).map (botH 2 3) := by
    rw [himg]; trivial
  obtain ⟨x, hx, hxt⟩ := hgx
  have hxX : x.1 ∈ X := Subgroup.mem_subgroupOf.mp hx
  obtain ⟨s, hs⟩ : ∃ s : ↥(stabStd 2 3), s = ⟨g, hg.1⟩ * x⁻¹ := ⟨_, rfl⟩
  have hb : botH 2 3 s = 1 := by rw [hs, map_mul, map_inv, hxt, mul_inv_cancel]
  have ht : topH 2 3 s = 1 := by
    rw [hs, map_mul, map_inv, htop x hxX, inv_one, mul_one]
    exact Subtype.ext hg.2
  have hsX : s.1 ∈ X := by
    rw [eq_utSL_of_blocks s.2 (congrArg Subtype.val ht) (congrArg Subtype.val hb)]
    exact utSL_mem_of_E2 h2 htriv ⟨e⟩ hU _
  have hg' : g = s.1 * x.1 := by
    rw [hs, Subgroup.coe_mul, Subgroup.coe_inv, inv_mul_cancel_right]
  rw [hg']
  exact X.mul_mem hsX hxX

end CFSG.Quasithin.Vol2.Ch10.SecC.C10P4F
