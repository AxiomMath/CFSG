module

public import CFSG.Quasithin.Vol2.Ch10SecD32A
public import CFSG.Quasithin.Vol2.Ch10SecDTL

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecD

open CFSG.Open CFSG.Blueprint CFSG.Quasithin.H13 CFSG.QuasithinUnique
open scoped IsMulCommutative

variable {G : Type} [Group G]

theorem mem_autOn_iff {H W : Subgroup G} {g : MulAut ↥W} :
    g ∈ autOn H W ↔ ∃ x : ↥(Subgroup.normalizer (W : Set G)), (x : G) ∈ H ∧ conjAct W x = g := by
  simp only [autOn, Subgroup.mem_map, Subgroup.mem_subgroupOf]

theorem pCoreOf_autOn_eq_bot {H W : Subgroup G} [(W.subgroupOf H).Normal] (hWH : W ≤ H)
    (hHN : H ≤ Subgroup.normalizer (W : Set G))
    (hR : CFSG.pCore 2 (↥H ⧸ Subgroup.centralizer ((W.subgroupOf H : Subgroup ↥H) : Set ↥H)) = ⊥) :
    pCoreOf 2 (autOn H W) = ⊥ := by
  let ψ : ↥H →* ↥(autOn H W) :=
    ((conjAct W).comp (Subgroup.inclusion hHN)).codRestrict _
      fun h => ⟨Subgroup.inclusion hHN h, h.2, rfl⟩
  have hψs : Function.Surjective ψ := by
    rintro ⟨y, x, hx, rfl⟩
    exact ⟨⟨x, hx⟩, rfl⟩
  have hker : ψ.ker = Subgroup.centralizer ((W.subgroupOf H : Subgroup ↥H) : Set ↥H) := by
    ext h
    rw [MonoidHom.mem_ker, Subgroup.mem_centralizer_iff]
    constructor
    · intro h1 w hw
      have h2 : conjAct W (Subgroup.inclusion hHN h) = 1 := congrArg Subtype.val h1
      have h3 := (conjAct_eq_one_iff _).mp h2
      exact Subtype.ext ((Subgroup.mem_centralizer_iff.mp h3) w (Subgroup.mem_subgroupOf.mp hw))
    · intro h1
      apply Subtype.ext
      refine (conjAct_eq_one_iff (Subgroup.inclusion hHN h)).mpr ?_
      rw [Subgroup.mem_centralizer_iff]
      intro w hw
      exact congrArg Subtype.val (h1 ⟨w, hWH hw⟩ (Subgroup.mem_subgroupOf.mpr hw))
  let e : ↥(autOn H W) ≃* ↥H ⧸ Subgroup.centralizer ((W.subgroupOf H : Subgroup ↥H) : Set ↥H) :=
    (QuotientGroup.quotientKerEquivOfSurjective ψ hψs).symm.trans
      (QuotientGroup.quotientMulEquivOfEq hker)
  have h1 : CFSG.pCore 2 ↥(autOn H W) = ⊥ := by
    have := CFSG.pCore_map_iso 2 e
    rw [hR] at this
    exact (Subgroup.map_eq_bot_iff_of_injective _ e.injective).mp this
  unfold pCoreOf
  rw [h1, Subgroup.map_bot]

variable [Finite G] {T L I : Subgroup G}

theorem eq_one_or_eq_of_mem_E (h37 : Vol2Native.A37ForSQTKCat) (h38 : Vol2Native.A38ForSQTKCat)
    (h : Hyp10 G T L I) (hc : fsuCVM T L I = ⊥) {t v₁ v₂ : G}
    (hd : IsData10_2_11 T L I t v₁ v₂) {c : G} (hcE : c ∈ Subgroup.closure {v₁, v₂})
    (hc1 : c ∈ fsuUL T L I) : c = 1 ∨ c = v₁ := by
  obtain ⟨ht, htn, hv1, -, hv2, -⟩ := hd
  have hV := SecA.isElemAbelian_fsuVM h
  have hle2 : ⁅fsuVM T L I, CFSG.conjugate L t⁆ ≤ fsuVM T L I :=
    commutator_le_left_of_le_normalizer
      ((SecA.conjugate_le_fsuL0 ht).trans (SecA.fsuL0_le_normalizer_fsuVM T L I))
  have hz1 : Subgroup.zpowers v₁ ≤ fsuUL T L I := (Subgroup.zpowers_le).mpr hv1.1
  have hz2 : Subgroup.zpowers v₂ ≤ ⁅fsuVM T L I, CFSG.conjugate L t⁆ :=
    (Subgroup.zpowers_le).mpr hv2.1
  have hEle : Subgroup.closure {v₁, v₂} ≤ Subgroup.zpowers v₁ ⊔ Subgroup.zpowers v₂ := by
    rw [Subgroup.closure_le]
    rintro w (rfl | rfl)
    · exact Subgroup.mem_sup_left (Subgroup.mem_zpowers _)
    · exact Subgroup.mem_sup_right (Subgroup.mem_zpowers _)
  obtain ⟨a, ha, b, hb, rfl⟩ := exists_mul_of_mem_sup_of_comm
    (fun a ha b hb => commute_V1_V2 h ht a (hz1 ha) b (hz2 hb)) (hEle hcE)
  have hb1 : b = 1 := by
    have hbV1 : b ∈ fsuUL T L I := by
      have := (fsuUL T L I).mul_mem ((fsuUL T L I).inv_mem (hz1 ha)) hc1
      rwa [inv_mul_cancel_left] at this
    have h12 := V1_inf_V2 h37 h38 h hc ht htn
    have hb' : b ∈ fsuUL T L I ⊓ ⁅fsuVM T L I, CFSG.conjugate L t⁆ := ⟨hbV1, hz2 hb⟩
    rw [h12, Subgroup.mem_bot] at hb'
    exact hb'
  rw [hb1, mul_one]
  exact (mem_zpowers_iff_of_sq (hV.2 v₁ (V1_le_V hv1.1))).mp ha

end CFSG.Quasithin.Vol2.Ch10.SecD
