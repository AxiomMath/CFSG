module

public import CFSG.Sporadic.Co2Smith.GlU62Main

public section

namespace CFSG.Sporadic.Co2Smith

open Subgroup CFSG.Sporadic.Co2Cert CFSG.Sporadic.SmallF2 CFSG.Sporadic.SmallF2.Native Matrix
  CFSG.LieType.Universal CFSG.LieType.Universal.Unitary CFSG.LieType.CurtisTits
  CFSG.Sporadic.Co2Rank3

attribute [local irreducible] Matrix.instHMulOfFintypeOfMulOfAddCommMonoid

section Values

variable {G : Type} [Group G] {z : G}
  {φ : centralizer ({z} : Set G) ≃* Cz} {ρ : C0c →* G}

theorem extFun_root
    (hz : z ≠ 1)
    (hm : SmithC0Marking φ α3c ρ) {y : K} (hy : y ∈ rootSet) :
    extFun hz hm y = psiE φ ρ y := by
  rw [extFun_of_mem hz hm (rootSet_mem_G0c hy), psi0Inv_of_mem hz hm (rootSet_mem_G0c hy),
    psi0_symm_root hz hm hy]

theorem extFun_δ1hK
    (hz : z ≠ 1)
    (hm : SmithC0Marking φ α3c ρ) :
    extFun hz hm δ1hK = rhoK ρ δ1hK := by
  rw [extFun_of_not_mem hz hm δ1hK_not_mem_G0c, δ1hK_mul_self, psi0Inv_one, one_mul]

theorem extFun_δ0hK
    (hz : z ≠ 1)
    (hm : SmithC0Marking φ α3c ρ) :
    extFun hz hm δ0hK = rhoK ρ δ0hK := by
  have h01 : δ0hK * δ1hK ∈ G0c :=
    (mul_mem_G0c_iff δ0hK_mem_G1c δ1hK_mem_G1c).2 (iff_of_false δ0hK_not_mem_G0c
      δ1hK_not_mem_G0c)
  have hT : Transp φ ρ (δ0hK * δ1hK) :=
    Transp.mul δ0hK_mem_C0c δ1hK_mem_C0c (transp_d0 hm) (transp_δ1hK hz hm)
  rw [extFun_of_not_mem hz hm δ0hK_not_mem_G0c, psi0Inv_of_mem hz hm h01,
    psi0_symm_eq_rhoK hz hm h01 hT, rhoK_mul ρ δ0hK_mem_C0c δ1hK_mem_C0c, mul_assoc,
    rhoK_δ1hK_sq, mul_one]

theorem extFun_z0
    (hz : z ≠ 1)
    (hm : SmithC0Marking φ α3c ρ) : extFun hz hm z0 = z := by
  rw [← xRootK_12, extFun_root hz hm ⟨12, by norm_num, 1, by norm_num, rfl⟩, xRootK_12, psiE_z0 hz]

theorem xLongK_mem_C0c_lt {k : ℕ} (hk : k < 6) :
    xLongK k ∈ C0c := by
  rcases (by omega : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5) with
    rfl | rfl | rfl | rfl | rfl | rfl
  · exact x16K_mem_C0c
  · exact x25K_mem_C0c
  · exact x34K_mem_C0c
  · exact x61K_mem_C0c
  · exact C0c.mul_mem (C0c.mul_mem δ1hK_mem_C0c x61K_mem_C0c) δ1hK_mem_C0c
  · exact x43K_mem_C0c

theorem psiE_xLongK
    (hm : SmithC0Marking φ α3c ρ) {k : ℕ}
    (hk : k < 6) : psiE φ ρ (xLongK k) = rhoK ρ (xLongK k) := by
  by_cases h3 : k = 3
  · subst h3
    exact psiE_x61K hm
  · have hz' : xLongK k ∈ Cz := by
      by_cases h0 : k = 0
      · subst h0
        rw [xLongK_zero]
        exact z0_mem_Cz
      · exact mem_Cz_of_comm (by
          rw [← xLongK_zero]
          exact xLongK_comm hk (by norm_num) (by omega))
    rw [psiE_of_mem φ ρ hz', rhoK_eq_phiInv hm (xLongK_mem_C0c_lt hk) hz']

theorem extFun_inv
    (hz : z ≠ 1)
    (hm : SmithC0Marking φ α3c ρ) {a : K} (ha : a ∈ G1c) :
    extFun hz hm a⁻¹ = (extFun hz hm a)⁻¹ := by
  have h := map_inv (extG hz hm) ⟨a, ha⟩
  rw [extG_apply, extG_apply] at h
  exact h

theorem extFun_one
    (hz : z ≠ 1)
    (hm : SmithC0Marking φ α3c ρ) : extFun hz hm 1 = 1 := by
  rw [extFun_of_mem hz hm G0c.one_mem, psi0Inv_one]

end Values

section Compat

variable {G : Type} [Group G] {z : G}
  {φ : centralizer ({z} : Set G) ≃* Cz} {ρ : C0c →* G}

theorem extFun_eq_phiInv
    (hz : z ≠ 1)
    (hm : SmithC0Marking φ α3c ρ) {k : K}
    (hk : k ∈ G1c ⊓ Cz) : extFun hz hm k = phiInv φ k := by
  rw [← u62L1_eq, u62L1] at hk
  induction hk using Subgroup.closure_induction with
  | mem x hx =>
    obtain ⟨w, hw, rfl⟩ := hx
    have hC := (u62L1_le (Subgroup.subset_closure ⟨w, hw, rfl⟩)).2
    rcases u62L1_gen hw with h | ⟨r, hr, t, ht, h⟩
    · rw [h, extFun_δ0hK hz hm, rhoK_eq_phiInv hm δ0hK_mem_C0c δ0hK_mem_Cz]
    · rw [h] at hC ⊢
      rw [extFun_root hz hm ⟨r, hr, t, ht, rfl⟩, psiE_of_mem φ ρ hC]
  | one => rw [extFun_one hz hm, phiInv_one]
  | mul x y hx hy ihx ihy =>
    rw [extFun_mul hz hm (u62L1_le hx).1 (u62L1_le hy).1, ihx, ihy,
      phiInv_mul φ (u62L1_le hx).2 (u62L1_le hy).2]
  | inv x hx ih =>
    rw [extFun_inv hz hm (u62L1_le hx).1, ih, phiInv_inv φ (u62L1_le hx).2]

theorem u62C1Frame_lt : ∀ j < 6, Native.u62C1Frame.getD j 0 < 6 := by decide

theorem u62C1K_frame {j : ℕ} (hj : j < 6) :
    u62C1K j = xLongK (Native.u62C1Frame.getD j 0) := by
  have hl : j < Native.u62C1Words.length := by rw [u62C1_spec.2.2.2.1]; omega
  refine eq_of_val_rows (X := Native.glR (Native.u62C1Words.getD j [])) ?_ (xLongK_val _)
    (u62C1_spec.2.2.2.2.2.2 j hj)
  rw [u62C1K, List.getD_eq_getElem _ _ hl]
  exact glE_val (u62C1Words_lt _ (List.getElem_mem hl))

theorem u62C1K_of_ge {j : ℕ} (hj : 8 ≤ j) : u62C1K j = 1 := by
  rw [u62C1K, List.getD_eq_default _ _ (by rw [u62C1_spec.2.2.2.1]; omega), glE_nil]

theorem xLongK_mem_rootSet {k : ℕ} (hk : k < 6) : xLongK k ∈ rootSet :=
  ⟨12 + k, by omega, 1, by norm_num, by rw [xRootK_long (by omega) one_ne_zero,
    Nat.add_sub_cancel_left]⟩

theorem extFun_eq_rhoK
    (hz : z ≠ 1)
    (hm : SmithC0Marking φ α3c ρ) {k : K}
    (hk : k ∈ C1c) : extFun hz hm k = rhoK ρ k := by
  rw [← closure_u62C1K] at hk
  have hle : Subgroup.closure (Set.range u62C1K) ≤ C1c := by rw [closure_u62C1K]
  induction hk using Subgroup.closure_induction with
  | mem x hx =>
    obtain ⟨j, rfl⟩ := hx
    by_cases hj6 : j < 6
    · rw [u62C1K_frame hj6, extFun_root hz hm (xLongK_mem_rootSet (u62C1Frame_lt j hj6)),
        psiE_xLongK hm (u62C1Frame_lt j hj6)]
    · by_cases hj : j = 6
      · rw [hj, u62C1K_six, extFun_δ0hK hz hm]
      · by_cases hj' : j = 7
        · rw [hj', u62C1K_seven, extFun_δ1hK hz hm]
        · rw [u62C1K_of_ge (by omega), extFun_one hz hm, rhoK_one]
  | one => rw [extFun_one hz hm, rhoK_one]
  | mul x y hx hy ihx ihy =>
    rw [extFun_mul hz hm (hle hx).2 (hle hy).2, ihx, ihy, rhoK_mul ρ (hle hx).1 (hle hy).1]
  | inv x hx ih =>
    rw [extFun_inv hz hm (hle hx).2, ih, rhoK_inv ρ (hle hx).1]

end Compat

section Main

variable {G : Type} [Group G] {z : G}
  {φ : centralizer ({z} : Set G) ≃* Cz} {ρ : C0c →* G}

@[expose] noncomputable def psiG
    (hz : z ≠ 1)
    (hm : SmithC0Marking φ α3c ρ) :
    (extG hz hm).range ≃* co2P0 :=
  (MonoidHom.ofInjective (extG_injective hz hm)).symm.trans G1cEquiv

theorem psiG_apply
    (hz : z ≠ 1)
    (hm : SmithC0Marking φ α3c ρ)
    (h : (extG hz hm).range) : (psiG hz hm h : Equiv.Perm (Fin 2300)) =
      psiK ((MonoidHom.ofInjective (extG_injective hz hm)).symm h : K) := by
  rw [psiG, MulEquiv.trans_apply, G1cEquiv_apply]

theorem extFun_ofInjective_symm
    (hz : z ≠ 1)
    (hm : SmithC0Marking φ α3c ρ)
    (h : (extG hz hm).range) :
    extFun hz hm ((MonoidHom.ofInjective (extG_injective hz hm)).symm h : K) = h := by
  rw [← extG_apply, MonoidHom.apply_ofInjective_symm]

theorem psiG_of_mem_centralizer
    (hz : z ≠ 1)
    (hm : SmithC0Marking φ α3c ρ)
    (h : (extG hz hm).range) (hh : (h : G) ∈ centralizer ({z} : Set G)) :
    (psiG hz hm h : Equiv.Perm (Fin 2300)) =
      cPerm * (co2PermEquiv (φ ⟨h, hh⟩ : K) : Equiv.Perm (Fin 2300)) * cPerm⁻¹ := by
  have hk := extFun_ofInjective_symm hz hm h
  rw [psiG_apply]
  generalize (MonoidHom.ofInjective (extG_injective hz hm)).symm h = k at hk ⊢
  have hz0 : z0 ∈ G1c := G0c_le_G1c (by
    rw [← xRootK_12]
    exact xRootK_mem_G0c_lt (by norm_num) (by norm_num))
  have hkC : (k : K) ∈ Cz := by
    refine mem_Cz_of_comm ?_
    have e : extG hz hm (k * ⟨z0, hz0⟩) = extG hz hm (⟨z0, hz0⟩ * k) := by
      rw [map_mul, map_mul, extG_apply, extG_apply, hk]
      show (h : G) * extFun hz hm z0 = extFun hz hm z0 * h
      rw [extFun_z0 hz hm]
      exact mem_centralizer_singleton_iff.1 hh
    exact congrArg Subtype.val (extG_injective hz hm e)
  have hφ : (φ ⟨h, hh⟩ : K) = k := by
    have e : (⟨h, hh⟩ : centralizer ({z} : Set G)) = ⟨phiInv φ k, phiInv_mem φ k⟩ :=
      Subtype.ext (hk.symm.trans (extFun_eq_phiInv hz hm ⟨k.2, hkC⟩))
    rw [e, phi_phiInv φ hkC]
  rw [psiK_apply, co2PermEquiv_apply, hφ]

theorem rho_mem_range
    (hz : z ≠ 1)
    (hm : SmithC0Marking φ α3c ρ) (w : C0c)
    (hw : (w : K) ∈ G1c) : ρ w ∈ (extG hz hm).range :=
  ⟨⟨w, hw⟩, by rw [extG_apply, extFun_eq_rhoK hz hm ⟨w.2, hw⟩, rhoK_of_mem ρ w.2]⟩

theorem psiG_rho
    (hz : z ≠ 1)
    (hm : SmithC0Marking φ α3c ρ) (w : C0c)
    (hw : (w : K) ∈ G1c) :
    (psiG hz hm ⟨ρ w, rho_mem_range hz hm w hw⟩ : Equiv.Perm (Fin 2300)) =
      cPerm * (co2PermEquiv (w : K) : Equiv.Perm (Fin 2300)) * cPerm⁻¹ := by
  have e : (MonoidHom.ofInjective (extG_injective hz hm)).symm
      ⟨ρ w, rho_mem_range hz hm w hw⟩ = ⟨w, hw⟩ := by
    rw [MulEquiv.symm_apply_eq]
    apply Subtype.ext
    rw [MonoidHom.ofInjective_apply, extG_apply, extFun_eq_rhoK hz hm ⟨w.2, hw⟩,
      rhoK_of_mem ρ w.2]
  rw [psiG_apply, e, psiK_apply, co2PermEquiv_apply]

theorem smithU62Input_holds :
    SmithU62Input C0c α3c G1c
    cPerm := by
  intro G _ _ z _ hG φ _ ρ hm
  have hz : z ≠ 1 := fun h => by
    have h2 := hG.orderOf_eq
    rw [h, orderOf_one] at h2
    exact absurd h2 (by norm_num)
  exact ⟨(extG hz hm).range, psiG hz hm, psiG_of_mem_centralizer hz hm,
    fun w hw => ⟨rho_mem_range hz hm w hw, psiG_rho hz hm w hw⟩⟩

end Main

end CFSG.Sporadic.Co2Smith
