module

public import CFSG.Sporadic.SuzRecog.SuzL34.Centralizer
public import CFSG.Sporadic.SuzRecog.SuzL34.Standard
public import CFSG.GroupTheory.QuasiDihedralFusion.InvolutionCentralizer
public import CFSG.Quasithin.Vol2.Asc94.He42SE3

public section

namespace CFSG.Sporadic.SuzRecog.SuzL34.LocalData

open Subgroup CFSG.PSL3Four.Native CFSG.Sporadic.SuzRecog CFSG.Sporadic.SuzRecog.C1Model
  CFSG.Sporadic.SuzOddCore CFSG.ComponentClassification.AS81.SuzB0 CFSG.ABGLocalTools
  CFSG.Sporadic.SuzRecog.SuzL34Cert CFSG.Open

open scoped Pointwise

variable {G : Type} [Group G] [Finite G] {z : G} (D : LocalData G z)

private theorem exists_conj_t0_eq_of_mem_RG (hF1 : F1Prop) (hF1M : F1MProp) (hF2 : F2Prop)
    (hF3 : F3Prop) (hF4 : F4Prop) (hF5 : F5Prop) (hF6 : F6Prop) (hF6b : F6bProp)
    (hF7 : F7Prop) (hF8 : F8Prop) (hF9 : F9Prop) (hF11 : F11Prop)
    {r : G} (hr : r ∈ D.RG) (hr1 : r ≠ 1) :
    ∃ c ∈ centralizer ({z} : Set G), c * D.t0 * c⁻¹ = r := by
  have ht0C : D.t0 ∈ centralizer ({z} : Set G) := by
    have h := t0_mem_TG D
    rw [TG_eq] at h
    exact (Subgroup.mem_inf.mp h).2
  have hrTG : r ∈ D.TG := RG_le_TG D hF1 hF1M hF2 hF3 hF4 hF5 hF8 hr
  have hrC : r ∈ centralizer ({z} : Set G) := by
    rw [TG_eq] at hrTG
    exact (Subgroup.mem_inf.mp hrTG).2
  have hrT0 : r ∈ centralizer (D.T0G : Set G) :=
    RG_le_centralizer_T0G D hF1 hF1M hF2 hF3 hF4 hF5 hF8 hr
  have hr2 : r * r = 1 := mul_self_eq_one_of_mem_TG_inf D hF7 ⟨hrTG, hrT0⟩
  have ht2 : (⟨D.t0, ht0C⟩ : ↥(centralizer ({z} : Set G))) * ⟨D.t0, ht0C⟩ = 1 :=
    Subtype.ext (t0_mul_self D)
  have hr2' : (⟨r, hrC⟩ : ↥(centralizer ({z} : Set G))) * ⟨r, hrC⟩ = 1 :=
    Subtype.ext hr2
  have hr1' : (⟨r, hrC⟩ : ↥(centralizer ({z} : Set G))) ≠ 1 :=
    fun h => hr1 (congrArg Subtype.val h)
  have ht1 : (⟨D.t0, ht0C⟩ : ↥(centralizer ({z} : Set G))) ≠ 1 :=
    fun h => t0_ne_one D (congrArg Subtype.val h)
  have hconj := D.isConj_of_not_isConj ⟨D.t0, ht0C⟩ ⟨r, hrC⟩ ht2
    ht1 hr2' hr1' (not_isConj_t0 D hF3)
    (not_isConj_of_mem_RG D hF1 hF1M hF2 hF3 hF4 hF5 hF6 hF6b hF7 hF8 hF9 hF11 hr hr1)
  obtain ⟨c, hc⟩ := _root_.isConj_iff.mp hconj
  exact ⟨(c : G), c.2, by simpa using congrArg Subtype.val hc⟩

private theorem oddOrderClosure_centralizer_eq_map {r c : G}
    (hrc : c * D.t0 * c⁻¹ = r) :
    CFSG.GroupTheory.oddOrderClosure (centralizer ({r} : Set G)) =
      (D.AG).map (MulAut.conj c).toMonoidHom := by
  have hmap := CFSG.GroupTheory.map_oddOrderClosure (MulAut.conj c)
    (centralizer ({D.t0} : Set G))
  calc CFSG.GroupTheory.oddOrderClosure (centralizer ({r} : Set G))
      = CFSG.GroupTheory.oddOrderClosure
          ((centralizer ({D.t0} : Set G)).map (MulAut.conj c).toMonoidHom) := by
        rw [CFSG.QuasiDihedralFusion.map_conj_centralizer_singleton c D.t0, hrc]
    _ = (CFSG.GroupTheory.oddOrderClosure
          (centralizer ({D.t0} : Set G))).map (MulAut.conj c).toMonoidHom := by
        simpa using hmap.symm
    _ = (D.AG).map (MulAut.conj c).toMonoidHom := rfl

private theorem mem_map_conj_AG_of_mem_T0G (hF1 : F1Prop) (hF1M : F1MProp) (hF2 : F2Prop)
    (hF3 : F3Prop) (hF4 : F4Prop) (hF5 : F5Prop) (hF8 : F8Prop) {r c x : G}
    (hc : c ∈ centralizer ({z} : Set G)) (hr : r ∈ D.RG) (hrc : c * D.t0 * c⁻¹ = r)
    (hxT : x ∈ D.T0G) (hx2 : x * x = 1) (hx1 : x ≠ 1) :
    x ∈ (D.AG).map (MulAut.conj c).toMonoidHom := by
  have hxZ : x ∈ centralizer ({z} : Set G) := by
    have h := T0G_le_TG D hxT
    rw [TG_eq] at h
    exact (Subgroup.mem_inf.mp h).2
  have hrT0 : r ∈ centralizer (D.T0G : Set G) :=
    RG_le_centralizer_T0G D hF1 hF1M hF2 hF3 hF4 hF5 hF8 hr
  have hxr : x * r = r * x :=
    Subgroup.mem_centralizer_iff.mp hrT0 x hxT
  have ht0eq : D.t0 = c⁻¹ * r * c := by
    rw [← hrc]
    group
  have hyC : c⁻¹ * x * c ∈ centralizer ({D.t0} : Set G) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    calc (c⁻¹ * x * c) * D.t0 = c⁻¹ * (x * r) * c := by rw [ht0eq]; group
      _ = c⁻¹ * (r * x) * c := by rw [hxr]
      _ = D.t0 * (c⁻¹ * x * c) := by rw [ht0eq]; group
  have hyZ : c⁻¹ * x * c ∈ centralizer ({z} : Set G) :=
    mul_mem (mul_mem (inv_mem hc) hxZ) hc
  have hyTG : c⁻¹ * x * c ∈ D.TG := by
    rw [TG_eq]
    exact Subgroup.mem_inf.mpr ⟨hyC, hyZ⟩
  have hy2 : (c⁻¹ * x * c) * (c⁻¹ * x * c) = 1 := by
    calc (c⁻¹ * x * c) * (c⁻¹ * x * c) = c⁻¹ * (x * x) * c := by group
      _ = 1 := by rw [hx2]; group
  have hy1 : c⁻¹ * x * c ≠ 1 := by
    intro h
    apply hx1
    calc x = c * (c⁻¹ * x * c) * c⁻¹ := by group
      _ = 1 := by rw [h]; group
  have hyz : IsConj (c⁻¹ * x * c) z :=
    (_root_.isConj_iff.mpr ⟨c, by group⟩).trans (isConj_of_mem_T0G D hF4 x hxT hx2 hx1)
  have hyT0 : c⁻¹ * x * c ∈ D.T0G :=
    mem_T0G_of_isConj D hF4 _ hyTG hy2 hy1 hyz
  refine Subgroup.mem_map.mpr ⟨c⁻¹ * x * c,
    T0G_le_AG D hF1 hF1M hF2 hF3 hF4 hF5 hF8 hyT0, ?_⟩
  change c * (c⁻¹ * x * c) * c⁻¹ = x
  group

theorem oddOrderClosure_centralizer_eq_AG (hF1 : F1Prop) (hF1M : F1MProp) (hF2 : F2Prop)
    (hF3 : F3Prop) (hF4 : F4Prop) (hF5 : F5Prop) (hF6 : F6Prop) (hF6b : F6bProp)
    (hF7 : F7Prop) (hF8 : F8Prop) (hF9 : F9Prop) (hF11 : F11Prop)
    {r : G} (hr : r ∈ D.RG) (hr1 : r ≠ 1) :
    CFSG.GroupTheory.oddOrderClosure (centralizer ({r} : Set G)) = D.AG := by
  obtain ⟨c, hc, hrc⟩ := exists_conj_t0_eq_of_mem_RG D hF1 hF1M hF2 hF3 hF4 hF5 hF6 hF6b
    hF7 hF8 hF9 hF11 hr hr1
  have hAr := oddOrderClosure_centralizer_eq_map D hrc
  have hLA : D.L ≤ CFSG.GroupTheory.oddOrderClosure (centralizer ({r} : Set G)) := by
    intro x hxL
    by_cases hx1 : x = 1
    · rw [hx1]
      exact Subgroup.one_mem _
    · have hxT : x ∈ D.T0G := L_le_T0G D hF5 hxL
      have hx2 : x * x = 1 := IsElemAbelian.mul_self_eq_one (D.isElemAbelian_L hF1) hxL
      have hmem := mem_map_conj_AG_of_mem_T0G D hF1 hF1M hF2 hF3 hF4 hF5 hF8 hc hr hrc
        hxT hx2 hx1
      rwa [hAr]
  have hMA : D.M2G ≤ CFSG.GroupTheory.oddOrderClosure (centralizer ({r} : Set G)) := by
    intro x hxM
    by_cases hx1 : x = 1
    · rw [hx1]
      exact Subgroup.one_mem _
    · have hxT : x ∈ D.T0G := M2G_le_T0G D hF5 hxM
      have hx2 : x * x = 1 :=
        IsElemAbelian.mul_self_eq_one (D.isElemAbelian_M2G hF1 hF5) hxM
      have hmem := mem_map_conj_AG_of_mem_T0G D hF1 hF1M hF2 hF3 hF4 hF5 hF8 hc hr hrc
        hxT hx2 hx1
      rwa [hAr]
  have hT0A : D.T0G ≤ CFSG.GroupTheory.oddOrderClosure (centralizer ({r} : Set G)) := by
    rw [T0G_eq_sup D hF1 hF5]
    exact sup_le hLA hMA
  obtain ⟨C, -, -, -⟩ :=
    exists_config D hF1 hF1M hF2 hF3 hF4 hF5 hF6 hF6b hF8 hF9 hF11
  have hSimple : IsSimpleGroup ↥D.AG :=
    CFSG.Quasithin.A94.He42SE.typeL34_isSimpleGroup
      (CFSG.Quasithin.L34CIT.typeL34_of_config C)
  have hA_le_normalizer : D.AG ≤ normalizer
      ((D.AG ⊓ CFSG.GroupTheory.oddOrderClosure (centralizer ({r} : Set G)) : Subgroup G) :
        Set G) := by
    refine (le_inf (Subgroup.le_normalizer (H := D.AG)) ?_).trans
      (Subgroup.inf_normalizer_le_normalizer_inf (H := D.AG)
        (K := CFSG.GroupTheory.oddOrderClosure (centralizer ({r} : Set G))))
    intro a ha
    have har : a * r = r * a :=
      Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp hr).1 a ha
    exact (CFSG.GroupTheory.normalizer_le_normalizer_oddOrderClosure
      (centralizer ({r} : Set G)))
      (Subgroup.le_normalizer (H := centralizer ({r} : Set G))
        (Subgroup.mem_centralizer_singleton_iff.mpr har))
  have hnormal : ((D.AG ⊓
      CFSG.GroupTheory.oddOrderClosure (centralizer ({r} : Set G))).subgroupOf D.AG).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer inf_le_left).mpr hA_le_normalizer
  have hbot : (D.AG ⊓
      CFSG.GroupTheory.oddOrderClosure (centralizer ({r} : Set G))).subgroupOf D.AG ≠ ⊥ := by
    intro h
    have hzAr : z ∈ CFSG.GroupTheory.oddOrderClosure (centralizer ({r} : Set G)) :=
      hT0A (L_le_T0G D hF5 (z_mem_L D hF1))
    have hzAG : z ∈ D.AG := z_mem_AG D hF1 hF1M hF2 hF3 hF4 hF5 hF8
    have hzsub : (⟨z, hzAG⟩ : ↥D.AG) ∈
        (D.AG ⊓ CFSG.GroupTheory.oddOrderClosure (centralizer ({r} : Set G))).subgroupOf D.AG :=
      ⟨hzAG, hzAr⟩
    rw [h] at hzsub
    exact z_ne_one D hF1 (congrArg Subtype.val (Subgroup.mem_bot.mp hzsub))
  have hAle : D.AG ≤ CFSG.GroupTheory.oddOrderClosure (centralizer ({r} : Set G)) := by
    haveI : ((D.AG ⊓ CFSG.GroupTheory.oddOrderClosure
        (centralizer ({r} : Set G))).subgroupOf D.AG).Normal := hnormal
    rcases hSimple.eq_bot_or_eq_top_of_normal
      ((D.AG ⊓ CFSG.GroupTheory.oddOrderClosure
        (centralizer ({r} : Set G))).subgroupOf D.AG) with h | h
    · exact absurd h hbot
    · exact (Subgroup.subgroupOf_eq_top.mp h).trans inf_le_right
  have hcard : Nat.card (CFSG.GroupTheory.oddOrderClosure
      (centralizer ({r} : Set G))) = Nat.card D.AG := by
    rw [hAr, Subgroup.card_map_of_injective (MulAut.conj c).injective]
  exact (Subgroup.eq_of_le_of_card_ge hAle (le_of_eq hcard)).symm

theorem centralizer_le_normalizer_AG (hF1 : F1Prop) (hF1M : F1MProp) (hF2 : F2Prop)
    (hF3 : F3Prop) (hF4 : F4Prop) (hF5 : F5Prop) (hF6 : F6Prop) (hF6b : F6bProp)
    (hF7 : F7Prop) (hF8 : F8Prop) (hF9 : F9Prop) (hF11 : F11Prop)
    {r : G} (hr : r ∈ D.RG) (hr1 : r ≠ 1) :
    centralizer ({r} : Set G) ≤ normalizer (D.AG : Set G) := by
  rw [← oddOrderClosure_centralizer_eq_AG D hF1 hF1M hF2 hF3 hF4 hF5 hF6 hF6b hF7 hF8
    hF9 hF11 hr hr1]
  exact (Subgroup.le_normalizer (H := centralizer ({r} : Set G))).trans
    (CFSG.GroupTheory.normalizer_le_normalizer_oddOrderClosure (centralizer ({r} : Set G)))

theorem centralizer_inf_centralizer_AG_le_RG (hF1 : F1Prop) (hF1M : F1MProp)
    (hF2 : F2Prop) (hF3 : F3Prop) (hF4 : F4Prop) (hF5 : F5Prop) (hF6 : F6Prop)
    (hF6b : F6bProp) (hF7 : F7Prop) (hF8 : F8Prop) (hF9 : F9Prop) (hF11 : F11Prop)
    {r : G} (hr : r ∈ D.RG) (hr1 : r ≠ 1) :
    centralizer ({r} : Set G) ⊓ centralizer (D.AG : Set G) ≤ D.RG := by
  obtain ⟨c, hc, hrc⟩ := exists_conj_t0_eq_of_mem_RG D hF1 hF1M hF2 hF3 hF4 hF5 hF6 hF6b
    hF7 hF8 hF9 hF11 hr hr1
  have hAr := oddOrderClosure_centralizer_eq_map D hrc
  have hAG : CFSG.GroupTheory.oddOrderClosure (centralizer ({r} : Set G)) = D.AG :=
    oddOrderClosure_centralizer_eq_AG D hF1 hF1M hF2 hF3 hF4 hF5 hF6 hF6b hF7 hF8 hF9 hF11
      hr hr1
  have hmapAG : (D.AG).map (MulAut.conj c).toMonoidHom = D.AG := hAr.symm.trans hAG
  have hmem : ∀ x : ↥(centralizer ({r} : Set G) ⊓ centralizer (D.AG : Set G)),
      c⁻¹ * (x : G) * c ∈ D.RG := by
    intro x
    obtain ⟨hxr, hxA⟩ := Subgroup.mem_inf.mp x.2
    have hxr' : x * r = r * x := Subgroup.mem_centralizer_singleton_iff.mp hxr
    have ht0eq : D.t0 = c⁻¹ * r * c := by
      rw [← hrc]
      group
    refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
    · rw [Subgroup.mem_centralizer_iff]
      intro a ha
      have hcaA : c * a * c⁻¹ ∈ D.AG := by
        have h1 : c * a * c⁻¹ ∈ (D.AG).map (MulAut.conj c).toMonoidHom :=
          Subgroup.mem_map.mpr ⟨a, ha, by simp [MulAut.conj_apply]⟩
        rwa [hmapAG] at h1
      have hxcomm : (c * a * c⁻¹) * x = x * (c * a * c⁻¹) :=
        Subgroup.mem_centralizer_iff.mp hxA (c * a * c⁻¹) hcaA
      calc a * (c⁻¹ * x * c) = c⁻¹ * ((c * a * c⁻¹) * x) * c := by group
        _ = c⁻¹ * (x * (c * a * c⁻¹)) * c := by rw [hxcomm]
        _ = (c⁻¹ * x * c) * a := by group
    · rw [Subgroup.mem_centralizer_singleton_iff]
      calc (c⁻¹ * x * c) * D.t0 = c⁻¹ * (x * r) * c := by rw [ht0eq]; group
        _ = c⁻¹ * (r * x) * c := by rw [hxr']
        _ = D.t0 * (c⁻¹ * x * c) := by rw [ht0eq]; group
  let f : ↥(centralizer ({r} : Set G) ⊓ centralizer (D.AG : Set G)) → ↥D.RG :=
    fun x => ⟨c⁻¹ * (x : G) * c, hmem x⟩
  have hf : Function.Injective f := by
    intro x y hxy
    have hxy' : c⁻¹ * (x : G) * c = c⁻¹ * (y : G) * c := congrArg Subtype.val hxy
    apply Subtype.ext
    calc (x : G) = c * (c⁻¹ * (x : G) * c) * c⁻¹ := by group
      _ = c * (c⁻¹ * (y : G) * c) * c⁻¹ := by rw [hxy']
      _ = (y : G) := by group
  have hcardle : Nat.card ↥(centralizer ({r} : Set G) ⊓
      centralizer (D.AG : Set G)) ≤ Nat.card D.RG :=
    Nat.card_le_card_of_injective f hf
  have hRle : D.RG ≤ centralizer ({r} : Set G) ⊓ centralizer (D.AG : Set G) := by
    intro x hx
    have hxR : x ∈ D.RG := hx
    refine Subgroup.mem_inf.mpr ⟨?_, (Subgroup.mem_inf.mp hx).1⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact IsElemAbelian.comm (isElemAbelian_RG D hF1 hF1M hF2 hF3 hF4 hF5 hF7 hF8) hxR hr
  exact le_of_eq (Subgroup.eq_of_le_of_card_ge hRle hcardle).symm

theorem suzL34Data (D : LocalData G z) (hF1 : F1Prop) (hF1M : F1MProp) (hF2 : F2Prop)
    (hF3 : F3Prop) (hF4 : F4Prop) (hF5 : F5Prop) (hF6 : F6Prop) (hF6b : F6bProp)
    (hF7 : F7Prop) (hF8 : F8Prop) (hF9 : F9Prop) (hF11 : F11Prop) :
    CFSG.ComponentClassification.AS81.SuzL34Data z := by
  obtain ⟨C, -, -, -⟩ :=
    exists_config D hF1 hF1M hF2 hF3 hF4 hF5 hF6 hF6b hF8 hF9 hF11
  have hT : CFSG.ComponentClassification.AS81.TypeL34 ↥D.AG :=
    CFSG.Quasithin.L34CIT.typeL34_of_config C
  have hA : IsSimpleGroup ↥D.AG :=
    CFSG.Quasithin.A94.He42SE.typeL34_isSimpleGroup hT
  have hz2 : z * z = 1 := by
    have h := (D.isElemAbelian_L hF1).2 z (z_mem_L D hF1)
    simpa [pow_two] using h
  have hK : Nat.card (centralizer (D.AG : Set G)) < Nat.card D.AG := by
    have hle := card_centralizer_AG_le D hF1 hF1M hF2 hF3 hF4 hF5 hF7 hF8
    have hcard : Nat.card D.AG = 20160 := C.card_eq
    omega
  exact suzL34Data_of_fourGroup hA hT (z_mem_AG D hF1 hF1M hF2 hF3 hF4 hF5 hF8)
    (z_ne_one D hF1) hz2
    (fun a ha ha2 ha1 => isConj_z_of_mem_AG D hF1 hF1M hF2 hF3 hF4 hF5 hF8 ha ha2 ha1)
    inf_le_left (isElemAbelian_RG D hF1 hF1M hF2 hF3 hF4 hF5 hF7 hF8)
    (card_RG D hF1 hF1M hF2 hF3 hF4 hF5 hF6 hF6b hF7 hF8 hF9 hF11)
    (fun r hr hr1 =>
      not_isConj_of_mem_RG D hF1 hF1M hF2 hF3 hF4 hF5 hF6 hF6b hF7 hF8 hF9 hF11 hr hr1)
    (fun r hr hr1 =>
      centralizer_le_normalizer_AG D hF1 hF1M hF2 hF3 hF4 hF5 hF6 hF6b hF7 hF8 hF9 hF11
        hr hr1)
    (fun r hr hr1 =>
      centralizer_inf_centralizer_AG_le_RG D hF1 hF1M hF2 hF3 hF4 hF5 hF6 hF6b hF7 hF8
        hF9 hF11 hr hr1)
    hK

end CFSG.Sporadic.SuzRecog.SuzL34.LocalData
