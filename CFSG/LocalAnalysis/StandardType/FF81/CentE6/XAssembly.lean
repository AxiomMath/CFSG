module

public import CFSG.LocalAnalysis.StandardType.FF81.CentE6.XKernel
public import CFSG.LocalAnalysis.StandardType.FF81.CentE6.XPair
public import CFSG.LocalAnalysis.StandardType.FF81.CentE6.XInner
public import CFSG.LocalAnalysis.StandardType.FF81.CentE6.CubePlanes

public section

namespace CFSG.StandardType.FF81.CentE6

open scoped MatrixGroups

private theorem img_hom_injective {X : Type} [Group X] (S : CubeSetting X) :
    Function.Injective (S.L.subtype.comp S.eL.symm.toMonoidHom) := by
  intro a b hab
  exact S.eL.symm.injective (Subtype.ext hab)

theorem conj_b_mem_img_of_cubeSetting {X : Type} [Group X] [Finite X] (S : CubeSetting X)
    (hB : ∀ c : X, c * S.z = S.z * c → c * S.b = S.b * c → c ∈ S.img (Sgrp ⊔ Jgrp))
    {c : X} (hc : c * S.z = S.z * c) : c * S.b * c⁻¹ ∈ S.img (Sgrp ⊔ Jgrp) := by
  classical
  let φ : SL(6, ZMod 2) →* X := S.L.subtype.comp S.eL.symm.toMonoidHom
  let b' : X := c * S.b * c⁻¹
  have hz_eq : S.z = φ CFSG.Holt.SL6.stdTransvection := rfl
  have hb_eq : S.b = φ bStd := rfl
  have hbz : S.b * S.z = S.z * S.b := by
    rw [hb_eq, hz_eq, ← map_mul, ← map_mul,
      comm_stdTransvection_of_mem_Jgrp bStd (Dgrp_le_Jgrp bStd_mem_Dgrp)]
  have hc_inv : c⁻¹ * S.z = S.z * c⁻¹ := by
    calc c⁻¹ * S.z = c⁻¹ * S.z * (c * c⁻¹) := by group
      _ = c⁻¹ * (S.z * c) * c⁻¹ := by group
      _ = c⁻¹ * (c * S.z) * c⁻¹ := by rw [hc]
      _ = S.z * c⁻¹ := by group
  have hz' : b' * S.z = S.z * b' := by
    calc b' * S.z = c * S.b * (c⁻¹ * S.z) := by simp only [b']; group
      _ = c * S.b * (S.z * c⁻¹) := by rw [hc_inv]
      _ = c * (S.b * S.z) * c⁻¹ := by group
      _ = c * (S.z * S.b) * c⁻¹ := by rw [hbz]
      _ = (c * S.z) * S.b * c⁻¹ := by group
      _ = (S.z * c) * S.b * c⁻¹ := by rw [hc]
      _ = S.z * b' := by simp only [b']; group
  have hb'3 : b' ^ 3 = 1 := by
    have hbStd3 : bStd ^ 3 = 1 := by
      have h := pow_orderOf_eq_one bStd
      rwa [orderOf_bStd] at h
    have hb3 : S.b ^ 3 = 1 := by
      rw [hb_eq, ← map_pow, hbStd3, map_one]
    have hb'conj : b' = MulAut.conj c S.b := (MulAut.conj_apply c S.b).symm
    rw [hb'conj, ← map_pow, hb3, map_one]
  have hnorm : ∀ x ∈ S.img Sgrp, b' * x * b'⁻¹ ∈ S.img Sgrp :=
    fun x hx => conj_mem_img_Sgrp S hB hz' hx
  have hnonswap : (∀ x ∈ S.img Sone, b' * x * b'⁻¹ ∈ S.img Sone) ∧
      (∀ y ∈ S.img Ssix, b' * y * b'⁻¹ ∈ S.img Ssix) := by
    rcases conj_img_Sone_or_Ssix S hnorm with h | h
    · exact h
    · exfalso
      have hle_img : S.img Sone ≤ S.img Ssix := by
        intro x hx
        have h1 : b' * x * b'⁻¹ ∈ S.img Ssix := h.1 x hx
        have h2 : b' * (b' * x * b'⁻¹) * b'⁻¹ ∈ S.img Sone := h.2 _ h1
        have h3 : b' * (b' * (b' * x * b'⁻¹) * b'⁻¹) * b'⁻¹ ∈ S.img Ssix := h.1 _ h2
        have hx' : b' * (b' * (b' * x * b'⁻¹) * b'⁻¹) * b'⁻¹ = x := by
          have h3' : b'⁻¹ ^ 3 = 1 := by rw [inv_pow, hb'3, inv_one]
          calc b' * (b' * (b' * x * b'⁻¹) * b'⁻¹) * b'⁻¹
              = b' ^ 3 * x * b'⁻¹ ^ 3 := by rw [pow_three', pow_three']; group
            _ = 1 * x * 1 := by rw [hb'3, h3']
            _ = x := by simp
        rwa [hx'] at h3
      have hsub : Sone ≤ Ssix := by
        intro a ha
        have hmem : φ a ∈ S.img Sone := Subgroup.mem_map_of_mem φ ha
        obtain ⟨b, hb, hbφ⟩ := Subgroup.mem_map.mp (hle_img hmem)
        have hba : b = a := img_hom_injective S hbφ
        rwa [← hba]
      have h_eq : Sone = Subgroup.zpowers CFSG.Holt.SL6.stdTransvection := by
        rw [← Sone_inf_Ssix, inf_eq_left.mpr hsub]
      have ht2 : CFSG.Holt.SL6.stdTransvection ^ 2 = 1 := by
        rw [pow_two]
        exact (Sone_comm_and_sq _ _ stdTransvection_mem_Sone stdTransvection_mem_Sone).2
      have hcard_le : Nat.card (Subgroup.zpowers CFSG.Holt.SL6.stdTransvection) ≤ 2 := by
        rw [Nat.card_zpowers]
        exact Nat.le_of_dvd (by norm_num) (orderOf_dvd_of_pow_eq_one ht2)
      have hcard_le' : Nat.card Sone ≤ 2 := by rw [h_eq]; exact hcard_le
      rw [card_Sone] at hcard_le'
      omega
  obtain ⟨g, hg, hconj⟩ := exists_conj_eq_on_img_Sgrp S hnorm hnonswap.1 hnonswap.2
  let d : X := g⁻¹ * b'
  have hd_comm : ∀ x ∈ S.img Sgrp, d * x = x * d := by
    intro x hx
    have h := hconj x hx
    have hdx : d * x * d⁻¹ = x := by
      calc d * x * d⁻¹ = g⁻¹ * (b' * x * b'⁻¹) * g := by simp only [d]; group
        _ = g⁻¹ * (g * x * g⁻¹) * g := by rw [h]
        _ = x := by group
    calc d * x = d * x * d⁻¹ * d := by group
      _ = x * d := by rw [hdx]
  have hle_centralizer : Sgrp ⊔ Jgrp ≤
      Subgroup.centralizer ({CFSG.Holt.SL6.stdTransvection} : Set SL(6, ZMod 2)) :=
    le_of_eq centralizer_stdTransvection_eq.symm
  have hg_z : g * S.z = S.z * g := by
    obtain ⟨a, ha, rfl⟩ := Subgroup.mem_map.mp hg
    have hcomm_a : a * CFSG.Holt.SL6.stdTransvection =
        CFSG.Holt.SL6.stdTransvection * a :=
      (Subgroup.mem_centralizer_iff.mp (hle_centralizer ha)
        CFSG.Holt.SL6.stdTransvection (by simp)).symm
    rw [hz_eq, ← map_mul, ← map_mul, hcomm_a]
  have hg_inv_z : g⁻¹ * S.z = S.z * g⁻¹ := by
    calc g⁻¹ * S.z = g⁻¹ * S.z * (g * g⁻¹) := by group
      _ = g⁻¹ * (S.z * g) * g⁻¹ := by group
      _ = g⁻¹ * (g * S.z) * g⁻¹ := by rw [hg_z]
      _ = S.z * g⁻¹ := by group
  have hd_z : d * S.z = S.z * d := by
    calc d * S.z = g⁻¹ * b' * S.z := by simp only [d]
      _ = g⁻¹ * (b' * S.z) := by group
      _ = g⁻¹ * (S.z * b') := by rw [hz']
      _ = (g⁻¹ * S.z) * b' := by group
      _ = (S.z * g⁻¹) * b' := by rw [hg_inv_z]
      _ = S.z * (g⁻¹ * b') := by group
      _ = S.z * d := by simp only [d]
  have hcomm_rho : ∀ s ∈ Sgrp, S.ρ d ∘ₗ cubeAct s = cubeAct s ∘ₗ S.ρ d := by
    intro s hs
    have hs_rho : S.ρ (φ s) = cubeAct s := by
      have h := S.hρ (S.eL.symm s)
      rw [MulEquiv.apply_symm_apply] at h
      exact h
    have hs' : φ s ∈ S.img Sgrp := Subgroup.mem_map_of_mem φ hs
    have h := hd_comm (φ s) hs'
    have h2 : S.ρ d * S.ρ (φ s) = S.ρ (φ s) * S.ρ d := by
      rw [← map_mul, ← map_mul, h]
    rw [hs_rho] at h2
    exact h2
  have hf : Function.Injective (S.ρ d) := by
    have hleft : Function.LeftInverse (S.ρ d⁻¹) (S.ρ d) := by
      intro x
      change (S.ρ d⁻¹ * S.ρ d) x = x
      rw [← map_mul, inv_mul_cancel, map_one]
      rfl
    exact hleft.injective
  have hfix : ∀ w ∈ Wsp, S.ρ d w = w :=
    fix_of_commute_cubeAct (S.ρ d) hf hcomm_rho
  have hd_mem : d ∈ S.img Sgrp := mem_img_Sgrp_of_trivial_on_Wsp S hB hd_z hfix
  have hb'_eq : b' = g * d := by
    simp only [d]
    group
  show b' ∈ S.img (Sgrp ⊔ Jgrp)
  rw [hb'_eq]
  exact Subgroup.mul_mem _ hg (Subgroup.map_mono (f := φ) le_sup_left hd_mem)

end CFSG.StandardType.FF81.CentE6
