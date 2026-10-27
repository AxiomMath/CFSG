module

public import CFSG.Quasithin.Vol2.Ch6Sec1Lem5FB

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique CFSG.Quasithin
open CFSG.LieType.BorelTits

variable {G : Type} [Group G] [Finite G] {T M L V H : Subgroup G} {n : ℕ}

namespace Cx615C

theorem isSolvable_borelL_sup_ch615 (c : Cx615C G T M L V H n) :
    Group.IsSolvable ↥(borelL T L ⊔ T) := by
  have h := c.hyp.toHyp5_0_1
  obtain ⟨D, hD⟩ := c.exists_hall_ch615
  have hDcyc := (c.hall_ch615 hD).1
  have hDs : Group.IsSolvable ↥D :=
    Group.isSolvable_of_comm fun a b => (IsCyclic.commGroup).mul_comm a b
  have hTLs : Group.IsSolvable ↥(T ⊓ L) := by
    have := (h.sylow.1.to_le (inf_le_left : T ⊓ L ≤ T)).isNilpotent
    infer_instance
  have hBs : Group.IsSolvable ↥(borelL T L) := by
    rw [← h.borelL_eq_sup hD, sup_comm]
    exact A3.isSolvable_sup_of_le_normalizer (hD.1.trans inf_le_right)
  have : Group.IsSolvable ↥T := by
    have := h.sylow.1.isNilpotent
    infer_instance
  exact A3.isSolvable_sup_of_le_normalizer h.T_le_normalizer_borel


theorem sup_eq_borelL_sup_ch615 (c : Cx615C G T M L V H n) :
    borelL T L ⊔ H = borelL T L ⊔ T ⊔ oTwoUpper H := by
  have hTH : T ≤ H := c.hH.1.1
  have hsup : T ⊔ twoResidual H = H := sup_twoResidual_eq c.toCx615.isSylowTwoOf
  rw [twoResidual_eq_oTwoUpper'] at hsup
  apply le_antisymm
  · refine sup_le (le_sup_left.trans le_sup_left) ?_
    calc H = T ⊔ oTwoUpper H := hsup.symm
      _ ≤ borelL T L ⊔ T ⊔ oTwoUpper H := sup_le_sup_right le_sup_right _
  · exact sup_le (sup_le le_sup_left (hTH.trans le_sup_right))
      ((oTwoUpper_le H).trans le_sup_right)

theorem isSolvable_of_centralizes_ch615 (c : Cx615C G T M L V H n)
    (hU : IsElemAbelian 2 (UX615 T L H)) {N : Subgroup (MulAut (IntMod (UX615 T L H) hU))}
    (hNX : N ≤ autI hU (borelL T L ⊔ H))
    (hBN : autI hU (borelL T L ⊔ T) ≤ Subgroup.normalizer (N : Set (MulAut _)))
    (hKN : autI hU (oTwoUpper H) ≤ Subgroup.centralizer (N : Set (MulAut _))) :
    Group.IsSolvable ↥N := by
  classical
  set Nn := Subgroup.normalizer (N : Set (MulAut (IntMod (UX615 T L H) hU))) with hNn
  set Y := autI hU (borelL T L ⊔ T) with hY
  set Ks := autI hU (oTwoUpper H) with hKs
  have hXN : borelL T L ⊔ H ≤ Subgroup.normalizer (UX615 T L H : Set G) :=
    le_normalizer_conjClosure _ _
  have hBTN : borelL T L ⊔ T ≤ Subgroup.normalizer (UX615 T L H : Set G) :=
    (sup_le le_sup_left (c.hH.1.1.trans le_sup_right)).trans hXN
  have hKN' : oTwoUpper H ≤ Subgroup.normalizer (UX615 T L H : Set G) :=
    ((oTwoUpper_le H).trans le_sup_right).trans hXN
  have hXs : autI hU (borelL T L ⊔ H) = Y ⊔ Ks := by
    rw [c.sup_eq_borelL_sup_ch615, autI_sup hU hBTN hKN']
  have hKNn : Ks ≤ Nn := hKN.trans (Subgroup.centralizer_le_normalizer _)
  have hYs : Group.IsSolvable ↥Y := by
    have := c.isSolvable_borelL_sup_ch615
    rw [hY, ← range_convHom hU _ hBTN]
    exact Group.isSolvable_of_surjective (convHom hU _ hBTN).rangeRestrict_surjective
  set φ := N.normalizerMonoidHom with hφ
  have himg : ((Y ⊔ Ks).subgroupOf Nn).map φ = (Y.subgroupOf Nn).map φ := by
    rw [Subgroup.subgroupOf_sup hBN hKNn, Subgroup.map_sup]
    have hK1 : (Ks.subgroupOf Nn).map φ = ⊥ := by
      rw [eq_bot_iff]
      rintro _ ⟨k, hk, rfl⟩
      rw [Subgroup.mem_bot]
      have hkC := hKN (Subgroup.mem_subgroupOf.mp hk)
      apply MulEquiv.ext
      intro x
      apply Subtype.ext
      simp only [hφ, Subgroup.normalizerMonoidHom_apply_apply_coe, MulAut.one_apply]
      rw [← Subgroup.mem_centralizer_iff.mp hkC x x.2, mul_inv_cancel_right]
    rw [hK1, sup_bot_eq]
  have hYimg : Group.IsSolvable ↥((Y.subgroupOf Nn).map φ) := by
    have : Group.IsSolvable ↥(Y.subgroupOf Nn) :=
      Group.isSolvable_of_surjective (f := (Subgroup.subgroupOfEquivOfLe hBN).symm.toMonoidHom)
        (Subgroup.subgroupOfEquivOfLe hBN).symm.surjective
    have e : (φ.comp (Y.subgroupOf Nn).subtype).range = (Y.subgroupOf Nn).map φ := by
      rw [MonoidHom.range_comp, Subgroup.range_subtype]
    rw [← e]
    exact Group.isSolvable_of_surjective (φ.comp (Y.subgroupOf Nn).subtype).rangeRestrict_surjective
  set ψ : ↥N →* MulAut ↥N := φ.comp (Subgroup.inclusion (Subgroup.le_normalizer)) with hψ
  have hψr : ψ.range ≤ (Y.subgroupOf Nn).map φ := by
    rw [← himg, hψ, MonoidHom.range_comp, Subgroup.inclusion_range]
    refine Subgroup.map_mono fun x hx => ?_
    rw [Subgroup.mem_subgroupOf] at hx ⊢
    rw [← hXs]
    exact hNX hx
  have hψs : Group.IsSolvable ↥ψ.range :=
    Group.isSolvable_of_isSolvable_injective (f := Subgroup.inclusion hψr)
      (Subgroup.inclusion_injective _)
  have hks : Group.IsSolvable ↥ψ.ker := by
    refine Group.isSolvable_of_comm ?_
    rintro ⟨⟨x, hx⟩, hxk⟩ ⟨⟨y, hy⟩, -⟩
    have ha : ψ ⟨x, hx⟩ = 1 := hxk
    have h1 := congrArg (fun f : MulAut ↥N => Subtype.val (f ⟨y, hy⟩)) ha
    simp only [hψ, MonoidHom.comp_apply, hφ, Subgroup.normalizerMonoidHom_apply_apply_coe,
      MulAut.one_apply, Subgroup.coe_inclusion] at h1
    refine Subtype.ext (Subtype.ext ?_)
    show x * y = y * x
    calc x * y = x * y * x⁻¹ * x := by group
      _ = y * x := by rw [h1]
  exact Group.isSolvable_of_ker_le_range ψ.ker.subtype ψ.rangeRestrict (by
    rw [MonoidHom.ker_rangeRestrict, Subgroup.range_subtype])

end Cx615C

end CFSG.Quasithin.H13
