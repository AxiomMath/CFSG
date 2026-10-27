module

public import CFSG.Quasithin.Vol2.Ch12Sec8NonabTen

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G] {T M L : Subgroup G}

namespace Hyp1281Two

section

variable (h : Hyp1281Two G T M L) (hU : ¬ IsMulCommutative ↥(uOfL22 T M)) {g : G}
  (hg : GoodElt128 T L g)

include h hU hg

theorem lemma_12_8_13_one : VZ T M ≤ wOfU T M ⊓ rconj (wOfU T M) g := by
  rw [h.wOfU_inf_rconj_eq hU hg]
  exact h.VZ_le_inf_rconj hU hg

theorem lemma_12_8_13_two :
    rconj (centerOf (uOfL22 T M)) g ≤ Subgroup.centralizer (VZ T M : Set G) := by
  intro z hz
  have hzC : z ∈ centerOf (rconj (uOfL22 T M) g) := by
    rw [centerOf_rconj]
    exact hz
  rw [Subgroup.mem_centralizer_iff]
  intro v hv
  exact Subgroup.mem_centralizer_iff.mp hzC.2 v ((h.VZ_le_inf_rconj hU hg) hv).2

theorem centerOf_sup_eq_bot : centerOf (L ⊔ uOfL22 T M) = ⊥ := by
  by_contra hN
  have h1 := h.omegaOneCenter_inf_centerOf_ne_bot hU hg hN
  obtain ⟨y, hy1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp h1
  obtain ⟨z, hzZ, hz1, hall⟩ := h.exists_zgen
  have hyz : (y : G) = z := (hall y y.2.1).resolve_left fun he => hy1 (Subtype.ext he)
  have hzI : z ∈ centerOf (L ⊔ uOfL22 T M) := hyz ▸ y.2.2
  apply hg.not_mem
  rw [h.normalizer_Z_eq_centralizer, Subgroup.mem_centralizer_iff]
  intro w hw
  rcases hall w hw with h1 | h1
  · rw [h1]
    simp
  · rw [h1]
    exact (Subgroup.mem_centralizer_iff.mp hzI.2 g (hg.mem_sup _)).symm

theorem centerOf_inf_rconj_centerOf_eq_bot :
    centerOf (uOfL22 T M) ⊓ rconj (centerOf (uOfL22 T M)) g = ⊥ := by
  rw [h.lemma_12_8_10_two hU hg]
  exact h.centerOf_sup_eq_bot hU hg

theorem commutator_centerOf_rconj_centerOf_eq_bot :
    ⁅centerOf (uOfL22 T M), rconj (centerOf (uOfL22 T M)) g⁆ = ⊥ := by
  rw [eq_bot_iff, Subgroup.commutator_le]
  intro z hz z' hz'
  have h1 : ⁅z, z'⁆ ∈ centerOf (uOfL22 T M) ⊓ rconj (centerOf (uOfL22 T M)) g := by
    constructor
    · have hz'X : z' ∈ rconj (wOfU T M) g := rconj_centerOf_le_rconj_wOfU T M g hz'
      have hz'N := h.rconj_wOfU_le_normalizer_centerOf hU hg hz'X
      have e : ⁅z, z'⁆ = z * (z' * z⁻¹ * z'⁻¹) := by
        rw [commutatorElement_def]
        group
      rw [e]
      exact (centerOf (uOfL22 T M)).mul_mem hz
        ((Subgroup.mem_normalizer_iff.mp hz'N _).mp ((centerOf (uOfL22 T M)).inv_mem hz))
    · have hzW : z ∈ wOfU T M := centerOf_uOfL22_le_wOfU T M hz
      have hzN := h.pCoreOf_sup_le_normalizer_rconj_centerOf hU hg (h.wOfU_le_pCoreOf hU hg hzW)
      have e : ⁅z, z'⁆ = (z * z' * z⁻¹) * z'⁻¹ := by
        rw [commutatorElement_def]
      rw [e]
      exact (rconj (centerOf (uOfL22 T M)) g).mul_mem
        ((Subgroup.mem_normalizer_iff.mp hzN _).mp hz')
        ((rconj (centerOf (uOfL22 T M)) g).inv_mem hz')
  rw [h.centerOf_inf_rconj_centerOf_eq_bot hU hg] at h1
  exact h1

theorem centralizerMod_rconj_centerOf_eq :
    centralizerMod (centerOf (uOfL22 T M)) (rconj (centerOf (uOfL22 T M)) g) (uOfL22 T M) =
      rconj (quasithinOmegaOneCenter T) g := by
  obtain ⟨e1, e2, e3, e4, -, -⟩ := h.lemma_12_8_10_six hU hg
  rw [e1, e2, e3, e4, h.centerOf_inf_rconj_centerOf_eq_bot hU hg, bot_sup_eq]

theorem exists_mulEquiv_rconj_centerOf :
    ∃ e : ↥(rconj (centerOf (uOfL22 T M)) g) ≃* ↥(centerOf (uOfL22 T M)),
      ∀ z : ↥(rconj (centerOf (uOfL22 T M)) g),
        (z : G) ∈ centralizerMod (centerOf (uOfL22 T M)) (rconj (centerOf (uOfL22 T M)) g)
          (uOfL22 T M) ↔ ((e z : ↥(centerOf (uOfL22 T M))) : G) ∈ quasithinOmegaOneCenter T := by
  have hC := h.centralizerMod_rconj_centerOf_eq hU hg
  refine ⟨{ toFun := fun z => ⟨g * z * g⁻¹, mem_rconj.mp z.2⟩
            invFun := fun y => ⟨g⁻¹ * y * g, inv_mul_mul_mem_rconj y.2⟩
            left_inv := fun z => Subtype.ext (by
              show g⁻¹ * (g * (z : G) * g⁻¹) * g = z
              group)
            right_inv := fun y => Subtype.ext (by
              show g * (g⁻¹ * (y : G) * g) * g⁻¹ = y
              group)
            map_mul' := fun a b => Subtype.ext (by
              show g * ((a : G) * (b : G)) * g⁻¹ = (g * (a : G) * g⁻¹) * (g * (b : G) * g⁻¹)
              group) }, fun z => ?_⟩
  rw [hC]
  exact mem_rconj

theorem lemma_12_8_13_three :
    centerOf (L ⊔ uOfL22 T M) = ⊥ ∧
      centerOf (uOfL22 T M) ⊓ rconj (centerOf (uOfL22 T M)) g = ⊥ ∧
      ⁅centerOf (uOfL22 T M), rconj (centerOf (uOfL22 T M)) g⁆ = ⊥ :=
  ⟨h.centerOf_sup_eq_bot hU hg, h.centerOf_inf_rconj_centerOf_eq_bot hU hg,
    h.commutator_centerOf_rconj_centerOf_eq_bot hU hg⟩

theorem lemma_12_8_13_four (hlt : quasithinOmegaOneCenter T < centerOf (uOfL22 T M)) :
    centralizerMod (centerOf (uOfL22 T M)) (rconj (centerOf (uOfL22 T M)) g) (uOfL22 T M) <
      rconj (centerOf (uOfL22 T M)) g := by
  rw [h.centralizerMod_rconj_centerOf_eq hU hg]
  refine lt_of_le_of_ne (rconj_le_rconj hlt.le g) fun heq => hlt.ne ?_
  have := congrArg (fun K => rconj K g⁻¹) heq
  simp only [rconj_rconj_inv_eq] at this
  exact this

end

end Hyp1281Two

end CFSG.Quasithin
