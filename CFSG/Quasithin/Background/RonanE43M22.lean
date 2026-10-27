module

public import CFSG.Quasithin.Background.RonanE43M22Lat

public section

namespace CFSG.Quasithin.RonanE43

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.E3 CFSG.QuasithinUnique
  CFSG.QuasithinUnique.Vol2Native.A312L.M22Lat

variable {G : Type} [Group G] [Finite G]

section M22


theorem e43_M22 (V : Type) [CommGroup V] [Finite V] (ρ : G →* MulAut V)
    (hρ : Function.Injective ρ) (hO2 : pCoreOf 2 (⊤ : Subgroup G) = ⊥) {T L : Subgroup G}
    (hT : IsSylowIn 2 T ⊤) (hlt : fixV ρ.range < fixV (T.map ρ))
    (hLF : L = CFSG.generalizedFitting G) (hLq : CFSG.IsQuasisimple ↥L)
    (h : IsSporadic .M22 (↥L ⧸ Subgroup.center ↥L))
    (hZ : ∀ g : G, ∀ z ∈ Subgroup.center ↥L, g * (z : G) * g⁻¹ = (z : G)) :
    aParam ρ.range ≤ 3 := by
  classical
  haveI hK : L.Normal := normal_of_generalizedFitting hLF
  have hLT : L ⊔ T = ⊤ := sup_eq_top_of_index_le_two hT (index_le_two_of_M22 hLF hLq h)
  set Z : Subgroup G := (Subgroup.center ↥L).map L.subtype with hZdef
  have hZc : Z ≤ Subgroup.center G := by
    rintro _ ⟨z, hz, rfl⟩
    rw [Subgroup.mem_center_iff]
    intro g
    exact mul_inv_eq_iff_eq_mul.mp (hZ g z hz)
  haveI hZn : Z.Normal := ⟨fun n hn g => by
    have : g * n * g⁻¹ = n := by
      have := Subgroup.mem_center_iff.mp (hZc hn) g
      rw [this]
      group
    rw [this]
    exact hn⟩
  let π : G →* G ⧸ Z := QuotientGroup.mk' Z
  have hπ : Function.Surjective π := QuotientGroup.mk'_surjective Z
  have hker : π.ker ≤ Subgroup.center G := by
    rw [QuotientGroup.ker_mk']
    exact hZc
  have hodd : Nat.Coprime (Nat.card π.ker) 2 := by
    rw [QuotientGroup.ker_mk']
    exact coprime_card_center_of_pCore_bot hO2 hZc
  have hT' : IsSylowIn 2 (T.map π) ⊤ :=
    ⟨le_top, hT.isPGroup.map π, by
      rw [Subgroup.relIndex_top_right]
      exact isSylowIn_map π hπ hT⟩
  have hL'n : (L.map π).Normal := hK.map π hπ
  have hL'T' : L.map π ⊔ T.map π = ⊤ := by
    rw [← Subgroup.map_sup, hLT, Subgroup.map_top_of_surjective π hπ]
  let ψ : ↥L →* G ⧸ Z := π.comp L.subtype
  have hψker : ψ.ker = Subgroup.center ↥L := by
    ext x
    rw [MonoidHom.mem_ker]
    show π (x : G) = 1 ↔ _
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    constructor
    · rintro ⟨y, hy, hyx⟩
      have : y = x := Subtype.ext hyx
      rw [← this]
      exact hy
    · intro hx
      exact ⟨x, hx, rfl⟩
  have hψrange : ψ.range = L.map π := by
    show (π.comp L.subtype).range = L.map π
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
  obtain ⟨e⟩ := h
  have e' : (↥L ⧸ Subgroup.center ↥L) ≃* ↥CFSG.Blueprint.NativeSporadic.M22 := e
  let eM : (↥L ⧸ Subgroup.center ↥L) ≃* ↥Mgrp :=
    e'.trans (MulEquiv.subgroupCongr mGens_closure.symm)
  let eQ : (↥L ⧸ Subgroup.center ↥L) ≃* ↥ψ.range :=
    (QuotientGroup.quotientMulEquivOfEq hψker.symm).trans (QuotientGroup.quotientKerEquivRange ψ)
  let e₀ : ↥(L.map π) ≃* ↥Mgrp :=
    (MulEquiv.subgroupCongr hψrange.symm).trans (eQ.symm.trans eM)
  obtain ⟨A, V', P, hS, hA5, hSP, hP3, hgen, hinv⟩ := m22_data
  have hGF' : GoodFamily (T.map π) 3 :=
    goodFamily_of_normal_S5 hT' hL'n hL'T' e₀ hS hA5 hSP hP3 hgen hinv
  have hGF : GoodFamily T 3 := goodFamily_of_central π hπ hker hodd hT.isPGroup hGF'
  exact aParam_le_of_goodFamily V ρ hρ hO2 hT hLF hLq hLT hlt hGF

theorem e43_M22' (V : Type) [CommGroup V] [Finite V] (ρ : G →* MulAut V)
    (hρ : Function.Injective ρ) (hO2 : pCoreOf 2 (⊤ : Subgroup G) = ⊥) {T L : Subgroup G}
    (hT : IsSylowIn 2 T ⊤) (hlt : fixV ρ.range < fixV (T.map ρ))
    (hLF : L = CFSG.generalizedFitting G) (hLq : CFSG.IsQuasisimple ↥L)
    (h : IsSporadic .M22 (↥L ⧸ Subgroup.center ↥L))
    (hZ : L.index = 1 ∨ Subgroup.center ↥L = ⊥) : aParam ρ.range ≤ 3 := by
  refine e43_M22 V ρ hρ hO2 hT hlt hLF hLq h fun g z hz => ?_
  rcases hZ with h1 | h1
  · rw [Subgroup.index_eq_one] at h1
    have hg : g ∈ L := by rw [h1]; exact Subgroup.mem_top g
    have := Subgroup.mem_center_iff.mp hz ⟨g, hg⟩
    have h2 : g * (z : G) = (z : G) * g := congrArg Subtype.val this
    exact mul_inv_eq_iff_eq_mul.mpr h2
  · rw [h1, Subgroup.mem_bot] at hz
    rw [hz]
    simp

end M22

end CFSG.Quasithin.RonanE43
