module

public import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
import CFSG.LocalAnalysis.StandardType.FS81.S7SelfNormL3Two
import CFSG.LocalAnalysis.StandardType.FS81.S7L3TwoSection
public import Mathlib.Data.Rat.Floor
public import Mathlib.GroupTheory.PGroup

public section

namespace CFSG.StandardType.FrameRoute.FS81

private theorem mem_map_mk'_iff {G : Type} [Group G] {H U K : Subgroup G}
    [(U.subgroupOf H).Normal] (hKH : K ≤ H) (hUH : U ≤ H) (x : ↥H) :
    QuotientGroup.mk' (U.subgroupOf H) x ∈
        (K.subgroupOf H).map (QuotientGroup.mk' (U.subgroupOf H)) ↔
      (x : G) ∈ K ⊔ U := by
  have hHN : H ≤ Subgroup.normalizer (U : Set G) :=
    Subgroup.le_normalizer_of_normal_subgroupOf hUH
  have hKnormU : K ≤ Subgroup.normalizer (U : Set G) := hKH.trans hHN
  constructor
  · rintro ⟨y, hy, hyx⟩
    have hyx' : (y : ↥H ⧸ U.subgroupOf H) = (x : ↥H ⧸ U.subgroupOf H) := hyx
    have hyU : y⁻¹ * x ∈ U.subgroupOf H := QuotientGroup.eq.mp hyx'
    have hyU' : ((y⁻¹ * x : ↥H) : G) ∈ U := Subgroup.mem_subgroupOf.mp hyU
    have hyK : (y : G) ∈ K := hy
    have hx' : (x : G) = (y : G) * ((y⁻¹ * x : ↥H) : G) := by simp
    rw [hx']
    exact Subgroup.mul_mem_sup hyK hyU'
  · intro hx
    have hxmem : (x : G) ∈ (↑(K ⊔ U) : Set G) := hx
    rw [Subgroup.coe_mul_of_left_le_normalizer_right K U hKnormU, Set.mem_mul] at hxmem
    obtain ⟨k, hkK, u, huU, hku⟩ := hxmem
    refine ⟨⟨k, hKH hkK⟩, hkK, ?_⟩
    have hπu : QuotientGroup.mk' (U.subgroupOf H) ⟨u, hUH huU⟩ = 1 :=
      (QuotientGroup.eq_one_iff _).mpr huU
    have hxeq : x = (⟨k, hKH hkK⟩ : ↥H) * ⟨u, hUH huU⟩ := by
      ext
      simp [hku]
    rw [hxeq, map_mul, hπu, mul_one]

private theorem map_le_normalizer_map {G : Type} [Group G] {H U K L : Subgroup G}
    [(U.subgroupOf H).Normal] (hKH : K ≤ H) (hUH : U ≤ H)
    (hLsup : L ≤ Subgroup.normalizer ((K ⊔ U : Subgroup G) : Set G)) :
    (L.subgroupOf H).map (QuotientGroup.mk' (U.subgroupOf H)) ≤
      Subgroup.normalizer (((K.subgroupOf H).map (QuotientGroup.mk' (U.subgroupOf H)) :
        Subgroup (↥H ⧸ U.subgroupOf H))) := by
  rintro _ ⟨d, hd, rfl⟩
  rw [Subgroup.mem_normalizer_iff]
  intro y
  obtain ⟨z, rfl⟩ := QuotientGroup.mk'_surjective (U.subgroupOf H) y
  have hconj : QuotientGroup.mk' (U.subgroupOf H) d * QuotientGroup.mk' (U.subgroupOf H) z *
      (QuotientGroup.mk' (U.subgroupOf H) d)⁻¹ =
      QuotientGroup.mk' (U.subgroupOf H) (d * z * d⁻¹) := by simp
  rw [mem_map_mk'_iff hKH hUH z, hconj, mem_map_mk'_iff hKH hUH (d * z * d⁻¹)]
  simpa using Subgroup.mem_set_normalizer_iff.mp (hLsup hd) (z : G)

private theorem mk'_comm_of_commutator_mem {G : Type} [Group G] {H U : Subgroup G}
    [(U.subgroupOf H).Normal] {s σ : ↥H}
    (hcomm : ((s * σ * s⁻¹ * σ⁻¹ : ↥H) : G) ∈ U) :
    QuotientGroup.mk' (U.subgroupOf H) s * QuotientGroup.mk' (U.subgroupOf H) σ =
      QuotientGroup.mk' (U.subgroupOf H) σ * QuotientGroup.mk' (U.subgroupOf H) s := by
  have hmem : s * σ * s⁻¹ * σ⁻¹ ∈ U.subgroupOf H := hcomm
  have h1 : QuotientGroup.mk' (U.subgroupOf H) (s * σ * s⁻¹ * σ⁻¹) = 1 :=
    (QuotientGroup.eq_one_iff _).mpr hmem
  have h2 : QuotientGroup.mk' (U.subgroupOf H) s * QuotientGroup.mk' (U.subgroupOf H) σ *
      (QuotientGroup.mk' (U.subgroupOf H) s)⁻¹ *
      (QuotientGroup.mk' (U.subgroupOf H) σ)⁻¹ = 1 := by
    simpa only [map_mul, map_inv] using h1
  have h3 : (QuotientGroup.mk' (U.subgroupOf H) s * QuotientGroup.mk' (U.subgroupOf H) σ) *
      (QuotientGroup.mk' (U.subgroupOf H) σ * QuotientGroup.mk' (U.subgroupOf H) s)⁻¹ = 1 := by
    simpa only [mul_inv_rev, mul_assoc] using h2
  exact mul_inv_eq_one.mp h3

private theorem commutator_mem_of_mk'_comm {G : Type} [Group G] {H U : Subgroup G}
    [(U.subgroupOf H).Normal] {s σ : ↥H}
    (hcomm : QuotientGroup.mk' (U.subgroupOf H) s * QuotientGroup.mk' (U.subgroupOf H) σ =
      QuotientGroup.mk' (U.subgroupOf H) σ * QuotientGroup.mk' (U.subgroupOf H) s) :
    ((s * σ * s⁻¹ * σ⁻¹ : ↥H) : G) ∈ U := by
  have h1 : QuotientGroup.mk' (U.subgroupOf H) ((s * σ) * (σ * s)⁻¹) = 1 := by
    simpa only [map_mul, map_inv] using mul_inv_eq_one.mpr hcomm
  have h2 : (s * σ) * (σ * s)⁻¹ ∈ U.subgroupOf H := (QuotientGroup.eq_one_iff _).mp h1
  have h3 := Subgroup.mem_subgroupOf.mp h2
  simpa [mul_assoc] using h3

private theorem mk'_mem_zpowers {G : Type} [Group G] {H U : Subgroup G}
    [(U.subgroupOf H).Normal] {σ z : ↥H}
    (hz : (z : G) ∈ Subgroup.zpowers (σ : G)) :
    QuotientGroup.mk' (U.subgroupOf H) z ∈
      Subgroup.zpowers (QuotientGroup.mk' (U.subgroupOf H) σ) := by
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hz
  refine Subgroup.mem_zpowers_iff.mpr ⟨k, ?_⟩
  rw [← map_zpow]
  congr 1
  ext
  simpa using hk

private theorem injective_restrict_mk' {G : Type} [Group G] {H U D : Subgroup G}
    [(U.subgroupOf H).Normal] (hDU : ∀ d ∈ D, d ∈ U → d = 1) :
    Function.Injective
      ((QuotientGroup.mk' (U.subgroupOf H)).comp (D.subgroupOf H).subtype) := by
  intro x y hxy
  have hxy' : ((x : ↥H) : ↥H ⧸ U.subgroupOf H) =
      ((y : ↥H) : ↥H ⧸ U.subgroupOf H) := hxy
  have hxU : (x : ↥H)⁻¹ * (y : ↥H) ∈ U.subgroupOf H := QuotientGroup.eq.mp hxy'
  have hxD : (x : ↥H)⁻¹ * (y : ↥H) ∈ D.subgroupOf H :=
    (D.subgroupOf H).mul_mem ((D.subgroupOf H).inv_mem x.2) y.2
  have hU' : (((x : ↥H)⁻¹ * (y : ↥H) : ↥H) : G) ∈ U := Subgroup.mem_subgroupOf.mp hxU
  have hD' : (((x : ↥H)⁻¹ * (y : ↥H) : ↥H) : G) ∈ D := hxD
  have h1 : (((x : ↥H)⁻¹ * (y : ↥H) : ↥H) : G) = 1 := hDU _ hD' hU'
  have h2 : (x : ↥H)⁻¹ * (y : ↥H) = 1 := by
    apply Subtype.ext
    simpa using h1
  exact Subtype.ext (inv_mul_eq_one.mp h2)

private theorem nonempty_map_equiv {G : Type} [Group G] {H U D : Subgroup G}
    [(U.subgroupOf H).Normal] (hDH : D ≤ H) (hDU : ∀ d ∈ D, d ∈ U → d = 1)
    (hD : Nonempty (↥D ≃* Matrix.SpecialLinearGroup (Fin 3) (ZMod 2))) :
    Nonempty (↥((D.subgroupOf H).map (QuotientGroup.mk' (U.subgroupOf H))) ≃*
      Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)) := by
  let f : ↥(D.subgroupOf H) →* (↥H ⧸ U.subgroupOf H) :=
    (QuotientGroup.mk' (U.subgroupOf H)).comp (D.subgroupOf H).subtype
  have hfinj : Function.Injective f := injective_restrict_mk' hDU
  have hrange : f.range = (D.subgroupOf H).map (QuotientGroup.mk' (U.subgroupOf H)) := by
    ext y
    rw [MonoidHom.mem_range, Subgroup.mem_map]
    constructor
    · rintro ⟨x, rfl⟩
      exact ⟨(x : ↥H), x.2, rfl⟩
    · rintro ⟨x, hx, rfl⟩
      exact ⟨⟨x, hx⟩, rfl⟩
  have e : ↥(D.subgroupOf H) ≃*
      ↥((D.subgroupOf H).map (QuotientGroup.mk' (U.subgroupOf H))) :=
    hrange ▸ MonoidHom.ofInjective hfinj
  obtain ⟨e'⟩ := hD
  exact ⟨e.symm.trans ((Subgroup.subgroupOfEquivOfLe hDH).trans e')⟩

private theorem orderOf_mk'_of_mem {G : Type} [Group G] {H U D : Subgroup G}
    [(U.subgroupOf H).Normal] (hDH : D ≤ H) (hDU : ∀ d ∈ D, d ∈ U → d = 1)
    {b : G} (hbD : b ∈ D) :
    orderOf (QuotientGroup.mk' (U.subgroupOf H) ⟨b, hDH hbD⟩) = orderOf b := by
  let f : ↥(D.subgroupOf H) →* (↥H ⧸ U.subgroupOf H) :=
    (QuotientGroup.mk' (U.subgroupOf H)).comp (D.subgroupOf H).subtype
  have hfinj : Function.Injective f := injective_restrict_mk' hDU
  have hval : f ⟨⟨b, hDH hbD⟩, hbD⟩ =
      QuotientGroup.mk' (U.subgroupOf H) ⟨b, hDH hbD⟩ := rfl
  rw [← hval, orderOf_injective f hfinj]
  exact (Subgroup.orderOf_coe (⟨⟨b, hDH hbD⟩, hbD⟩ : ↥(D.subgroupOf H))).symm.trans
    (Subgroup.orderOf_coe (⟨b, hDH hbD⟩ : ↥H)).symm

theorem le_sup_of_selfNormalizing_l3Two_mod {G : Type} [Group G] [Finite G]
    {H U S P D : Subgroup G} [(U.subgroupOf H).Normal] {σ b : G} (hUS : U ≤ S) (hSH : S ≤ H)
    (hPS : P ≤ S) (hP : IsPGroup 2 P) (hσP : σ ∈ P) (hSσ : ∀ s ∈ S, s * σ * s⁻¹ * σ⁻¹ ∈ U)
    (hPP : ∀ x ∈ P, ∀ y ∈ P, x * y * x⁻¹ * y⁻¹ ∈ Subgroup.zpowers σ)
    (hDH : D ≤ H) (hDU : ∀ d ∈ D, d ∈ U → d = 1)
    (hDS : D ≤ Subgroup.normalizer (S : Set G)) (hDP : D ≤ Subgroup.normalizer (P : Set G))
    (hD : Nonempty (↥D ≃* Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)))
    (hbD : b ∈ D) (hb : orderOf b = 3)
    (hC : ∀ x ∈ S, x * b * x⁻¹ * b⁻¹ ∈ U → x ∈ P ⊔ U) : S ≤ P ⊔ U := by
  let UH : Subgroup ↥H := U.subgroupOf H
  let π : ↥H →* (↥H ⧸ UH) := QuotientGroup.mk' UH
  let Hq := ↥H ⧸ UH
  let SH : Subgroup Hq := (S.subgroupOf H).map π
  let PH : Subgroup Hq := (P.subgroupOf H).map π
  let DH : Subgroup Hq := (D.subgroupOf H).map π
  have hUH : U ≤ H := hUS.trans hSH
  have hPH : P ≤ H := hPS.trans hSH
  have hHN : H ≤ Subgroup.normalizer (U : Set G) :=
    Subgroup.le_normalizer_of_normal_subgroupOf hUH
  let σH : ↥H := ⟨σ, hSH (hPS hσP)⟩
  let bH : ↥H := ⟨b, hDH hbD⟩
  have hPSS : PH ≤ SH := Subgroup.map_mono (Subgroup.subgroupOf_mono H hPS)
  have hPH2 : IsPGroup 2 PH := (hP.of_equiv (Subgroup.subgroupOfEquivOfLe hPH).symm).map π
  have hσPH : π σH ∈ PH :=
    (mem_map_mk'_iff hPH hUH σH).mpr (Subgroup.mem_sup_left hσP)
  have hSσ' : ∀ s ∈ SH, s * π σH = π σH * s := by
    intro s hs
    obtain ⟨sH, hsH, rfl⟩ := hs
    have hcomm : ((sH * σH * sH⁻¹ * σH⁻¹ : ↥H) : G) ∈ U := by
      simpa [σH] using hSσ (sH : G) hsH
    exact mk'_comm_of_commutator_mem hcomm
  have hPP' : ∀ x ∈ PH, ∀ y ∈ PH, x * y * x⁻¹ * y⁻¹ ∈ Subgroup.zpowers (π σH) := by
    intro x hx y hy
    obtain ⟨xH, hxH, rfl⟩ := hx
    obtain ⟨yH, hyH, rfl⟩ := hy
    have hz : ((xH * yH * xH⁻¹ * yH⁻¹ : ↥H) : G) ∈ Subgroup.zpowers σ := by
      simpa using hPP (xH : G) hxH (yH : G) hyH
    have hmem := mk'_mem_zpowers (H := H) (U := U) (σ := σH)
      (z := xH * yH * xH⁻¹ * yH⁻¹) hz
    simpa only [map_mul, map_inv] using hmem
  have hDSsup : D ≤ Subgroup.normalizer ((S ⊔ U : Subgroup G) : Set G) := by
    rwa [sup_eq_left.mpr hUS]
  have hDSS : DH ≤ Subgroup.normalizer (SH : Set Hq) :=
    map_le_normalizer_map hSH hUH hDSsup
  have hDPsup : D ≤ Subgroup.normalizer ((P ⊔ U : Subgroup G) : Set G) :=
    (le_inf hDP (hDH.trans hHN)).trans (Subgroup.inf_normalizer_le_normalizer_sup P U)
  have hDPS : DH ≤ Subgroup.normalizer (PH : Set Hq) :=
    map_le_normalizer_map hPH hUH hDPsup
  have hDHbar : Nonempty (↥DH ≃* Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)) :=
    nonempty_map_equiv hDH hDU hD
  have hbDH : π bH ∈ DH := Subgroup.mem_map_of_mem π hbD
  have hborder : orderOf (π bH) = 3 := by
    rw [orderOf_mk'_of_mem hDH hDU hbD, hb]
  have hCbar : ∀ x ∈ SH, x * π bH = π bH * x → x ∈ PH := by
    intro x hx hcomm
    obtain ⟨xH, hxH, rfl⟩ := hx
    have hmem : ((xH * bH * xH⁻¹ * bH⁻¹ : ↥H) : G) ∈ U :=
      commutator_mem_of_mk'_comm hcomm
    have hxC : (xH : G) ∈ P ⊔ U := hC (xH : G) hxH (by simpa [bH] using hmem)
    exact (mem_map_mk'_iff hPH hUH xH).mpr hxC
  have hmain : SH ≤ PH :=
    le_of_selfNormalizing_l3Two (X := Hq) (S := SH) (P := PH) (D := DH) (σ := π σH)
      (b := π bH) hPSS hPH2 hσPH hSσ' hPP' hDSS hDPS hDHbar hbDH hborder hCbar
  intro s hs
  have hsH : π ⟨s, hSH hs⟩ ∈ SH := Subgroup.mem_map_of_mem π hs
  exact (mem_map_mk'_iff hPH hUH ⟨s, hSH hs⟩).mp (hmain hsH)

theorem le_of_centralizer_le_l3Two_mod {G : Type} [Group G] [Finite G]
    {H U T₀ T D : Subgroup G} [(U.subgroupOf H).Normal] {b : G} (hUT₀ : U ≤ T₀)
    (hT₀ : IsPGroup 2 T₀) (hT₀T : T₀ ≤ T) (hTH : T ≤ H)
    (hTN : T ≤ Subgroup.normalizer (T₀ : Set G)) (hDH : D ≤ H)
    (hDU : ∀ d ∈ D, d ∈ U → d = 1)
    (hDT : D ≤ Subgroup.normalizer (T : Set G)) (hDT₀ : D ≤ Subgroup.normalizer (T₀ : Set G))
    (hD : Nonempty (↥D ≃* Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)))
    (hbD : b ∈ D) (hb : orderOf b = 3)
    (hC : ∀ x ∈ T, x * b * x⁻¹ * b⁻¹ ∈ U → x ∈ T₀) : T ≤ T₀ := by
  let UH : Subgroup ↥H := U.subgroupOf H
  let π : ↥H →* (↥H ⧸ UH) := QuotientGroup.mk' UH
  let Hq := ↥H ⧸ UH
  let TH : Subgroup Hq := (T.subgroupOf H).map π
  let T₀H : Subgroup Hq := (T₀.subgroupOf H).map π
  let DH : Subgroup Hq := (D.subgroupOf H).map π
  have hUH : U ≤ H := hUT₀.trans (hT₀T.trans hTH)
  have hT₀H_le : T₀ ≤ H := hT₀T.trans hTH
  have hUT : U ≤ T := hUT₀.trans hT₀T
  let bH : ↥H := ⟨b, hDH hbD⟩
  have hT₀H2 : IsPGroup 2 T₀H := (hT₀.of_equiv (Subgroup.subgroupOfEquivOfLe hT₀H_le).symm).map π
  have hT₀TH : T₀H ≤ TH := Subgroup.map_mono (Subgroup.subgroupOf_mono H hT₀T)
  have hTN_H : TH ≤ Subgroup.normalizer (T₀H : Set Hq) :=
    map_le_normalizer_map hT₀H_le hUH (by rwa [sup_eq_left.mpr hUT₀])
  have hDT_H : DH ≤ Subgroup.normalizer (TH : Set Hq) :=
    map_le_normalizer_map hTH hUH (by rwa [sup_eq_left.mpr hUT])
  have hDT₀_H : DH ≤ Subgroup.normalizer (T₀H : Set Hq) :=
    map_le_normalizer_map hT₀H_le hUH (by rwa [sup_eq_left.mpr hUT₀])
  have hDHbar : Nonempty (↥DH ≃* Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)) :=
    nonempty_map_equiv hDH hDU hD
  have hbDH : π bH ∈ DH := Subgroup.mem_map_of_mem π hbD
  have hborder : orderOf (π bH) = 3 := by
    rw [orderOf_mk'_of_mem hDH hDU hbD, hb]
  have hCbar : ∀ x ∈ TH, x * π bH = π bH * x → x ∈ T₀H := by
    intro x hx hcomm
    obtain ⟨xH, hxH, rfl⟩ := hx
    have hmem : ((xH * bH * xH⁻¹ * bH⁻¹ : ↥H) : G) ∈ U :=
      commutator_mem_of_mk'_comm hcomm
    have hxT₀ : (xH : G) ∈ T₀ := hC (xH : G) hxH (by simpa [bH] using hmem)
    exact (mem_map_mk'_iff hT₀H_le hUH xH).mpr (by rwa [sup_eq_left.mpr hUT₀])
  have hmain : TH ≤ T₀H :=
    le_of_centralizer_le_l3Two (G := Hq) (T := TH) (T₀ := T₀H) (D := DH)
      hT₀H2 hT₀TH hTN_H hDT_H hDT₀_H hDHbar hbDH hborder hCbar
  intro t ht
  have htH : π ⟨t, hTH ht⟩ ∈ TH := Subgroup.mem_map_of_mem π ht
  have hmem := (mem_map_mk'_iff hT₀H_le hUH ⟨t, hTH ht⟩).mp (hmain htH)
  rwa [sup_eq_left.mpr hUT₀] at hmem

end CFSG.StandardType.FrameRoute.FS81

end
