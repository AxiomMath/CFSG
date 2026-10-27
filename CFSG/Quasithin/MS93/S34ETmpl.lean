module

import CFSG.Quasithin.Background.A4V
public import CFSG.Quasithin.MS93.S34DAsm

public section

namespace CFSG.Quasithin.MS93.S34E

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Quasithin.Fan86.Univ
open CFSG.Open hiding StatedSL StatedSp StatedSU StatedOmega StatedQuadMinus StatedQuadPlus
  StatedQuadOdd StatedScalars StatedClassicalModel StatedLieAdmissible
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {M T L : Subgroup G}

omit [Finite G] in
theorem inf_centralizer_characteristic {W : Subgroup G} (hWT : W ≤ T)
    (hW : (W.subgroupOf T).Characteristic) :
    ((T ⊓ Subgroup.centralizer (W : Set G)).subgroupOf T).Characteristic := by
  rw [Subgroup.characteristic_iff_map_le]
  intro φ
  rintro _ ⟨t, ht, rfl⟩
  have ht' : (t : G) ∈ T ⊓ Subgroup.centralizer (W : Set G) := Subgroup.mem_subgroupOf.mp ht
  show φ t ∈ (T ⊓ Subgroup.centralizer (W : Set G)).subgroupOf T
  rw [Subgroup.mem_subgroupOf]
  refine ⟨(φ t).2, Subgroup.mem_centralizer_iff.mpr fun w hw => ?_⟩
  have hw' : φ.symm ⟨w, hWT hw⟩ ∈ W.subgroupOf T :=
    Subgroup.characteristic_iff_map_le.mp hW φ.symm
      ⟨⟨w, hWT hw⟩, Subgroup.mem_subgroupOf.mpr hw, rfl⟩
  have hc := Subgroup.mem_centralizer_iff.mp ht'.2 _ (Subgroup.mem_subgroupOf.mp hw')
  have hc' : φ.symm ⟨w, hWT hw⟩ * t = t * φ.symm ⟨w, hWT hw⟩ := Subtype.ext hc
  have h2 := congrArg φ hc'
  rw [map_mul, map_mul, MulEquiv.apply_symm_apply] at h2
  exact congrArg Subtype.val h2

theorem le_center_of_le_sup (h : PUHyp M T L) (hmin : PUMin M T L)
    (hUD : Uq M T L ⊓ Subgroup.centralizer (L : Set G) = ⊥) {W : Subgroup G} (hWT : W ≤ T)
    (hWc : (W.subgroupOf T).Characteristic) (hW : W ≤ Uq M T L ⊔ Dq M L) :
    T ≤ Subgroup.centralizer (W : Set G) := by
  set T₁ := T ⊓ Subgroup.centralizer (W : Set G) with hT₁
  have hT₁T : T₁ ≤ T := inf_le_left
  have hDU : Dq M L ≤ Subgroup.normalizer (Uq M T L : Set G) :=
    (inf_le_left.trans (pCoreOf_le' M)).trans (le_normalizer_Uq h.le_normalizer)
  have hUQ : Uq M T L ≤ Xq M := h.Uq_le_Xq
  have hgood : (L ⊔ T₁) ⊓ pCoreOf 2 M ≤ T₁ := by
    rintro x ⟨hxLT, hxQ⟩
    refine ⟨h.pCore_le hxQ, Subgroup.mem_centralizer_iff.mpr fun w hw => ?_⟩
    obtain ⟨ℓ, hℓ, t, ht, rfl⟩ :=
      S34D.exists_mul_of_mem_sup (hT₁T.trans (h.le.trans h.le_normalizer)) hxLT
    obtain ⟨u, hu, d, hd, rfl⟩ := S34D.exists_mul_of_mem_sup hDU (hW hw)
    have hxM : ℓ * t ∈ M := pCoreOf_le' M hxQ
    have htw : u * d * t = t * (u * d) :=
      Subgroup.mem_centralizer_iff.mp ht.2 (u * d) hw
    have hdℓ : d * ℓ = ℓ * d := Subgroup.mem_centralizer_iff.mp hd.2 ℓ hℓ |>.symm
    have huZ : u ∈ Subgroup.centralizer (pCoreOf 2 M : Set G) :=
      A4.centerOf_le_centralizer _ (A4.omegaOneCenterOf_le_centerOf _ (hUQ hu))
    have hux : u * (ℓ * t) = ℓ * t * u := (Subgroup.mem_centralizer_iff.mp huZ _ hxQ).symm
    have hud : u * d = d * u := (Subgroup.mem_centralizer_iff.mp huZ _ hd.1).symm
    have e1 : ⁅u * d, ℓ * t⁆ = ⁅u, ℓ⁆ := by
      have htw' : t * (u * d)⁻¹ * t⁻¹ = (u * d)⁻¹ := by
        calc t * (u * d)⁻¹ * t⁻¹ = (u * d)⁻¹ * (u * d * t) * (u * d)⁻¹ * t⁻¹ := by group
          _ = (u * d)⁻¹ * (t * (u * d)) * (u * d)⁻¹ * t⁻¹ := by rw [htw]
          _ = (u * d)⁻¹ := by group
      have hdℓ' : d * ℓ * d⁻¹ = ℓ := by rw [hdℓ, mul_inv_cancel_right]
      calc ⁅u * d, ℓ * t⁆ = u * d * ℓ * (t * (u * d)⁻¹ * t⁻¹) * ℓ⁻¹ := by
            simp only [commutatorElement_def]; group
        _ = u * (d * ℓ * d⁻¹) * u⁻¹ * ℓ⁻¹ := by rw [htw']; group
        _ = ⁅u, ℓ⁆ := by rw [hdℓ', commutatorElement_def]
    have e2 : ⁅u * d, ℓ * t⁆ = ⁅d, ℓ * t⁆ := by
      have hc : u * (d * (ℓ * t) * d⁻¹) = d * (ℓ * t) * d⁻¹ * u := by
        have h1 : Commute u d := hud
        have h2 : Commute u (ℓ * t) := hux
        exact ((h1.mul_right h2).mul_right h1.inv_right).eq
      calc ⁅u * d, ℓ * t⁆ = u * (d * (ℓ * t) * d⁻¹) * u⁻¹ * (ℓ * t)⁻¹ := by
            simp only [commutatorElement_def]; group
        _ = ⁅d, ℓ * t⁆ := by rw [hc, commutatorElement_def]; group
    have hcU : ⁅u * d, ℓ * t⁆ ∈ Uq M T L := by
      rw [e1, commutatorElement_def]
      have : u * ℓ * u⁻¹ * ℓ⁻¹ = u * (ℓ * u⁻¹ * ℓ⁻¹) := by group
      rw [this]
      exact (Uq M T L).mul_mem hu ((Subgroup.mem_normalizer_iff.mp
        (le_normalizer_Uq h.le_normalizer (h.L_le hℓ)) u⁻¹).mp ((Uq M T L).inv_mem hu))
    have hcD : ⁅u * d, ℓ * t⁆ ∈ Dq M L := by
      rw [e2, commutatorElement_def]
      have : d * (ℓ * t) * d⁻¹ * (ℓ * t)⁻¹ = d * ((ℓ * t) * d⁻¹ * (ℓ * t)⁻¹) := by group
      rw [this]
      exact (Dq M L).mul_mem hd ((Subgroup.mem_normalizer_iff.mp
        (le_normalizer_Dq h.le_normalizer hxM) d⁻¹).mp ((Dq M L).inv_mem hd))
    have h1 : ⁅u * d, ℓ * t⁆ = 1 := by
      have hmem : ⁅u * d, ℓ * t⁆ ∈ Uq M T L ⊓ Subgroup.centralizer (L : Set G) :=
        ⟨hcU, hcD.2⟩
      rw [hUD, Subgroup.mem_bot] at hmem
      exact hmem
    exact commutatorElement_eq_one_iff_mul_comm.mp h1
  have hT₁eq := hmin T₁ hT₁T (inf_centralizer_characteristic hWT hWc) hgood
  intro t ht
  rw [← hT₁eq] at ht
  exact ht.2

end CFSG.Quasithin.MS93.S34E
