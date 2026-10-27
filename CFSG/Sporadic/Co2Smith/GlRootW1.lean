module

public import CFSG.Sporadic.Co2Smith.GlRootD1Main

public section

namespace CFSG.Sporadic.Co2Smith

open Subgroup CFSG.Sporadic.Co2Cert CFSG.Sporadic.SmallF2 CFSG.Sporadic.SmallF2.Native Matrix

attribute [local irreducible] Matrix.instHMulOfFintypeOfMulOfAddCommMonoid

variable {G : Type*} [Group G] {z : G}
  {φ : centralizer ({z} : Set G) ≃* Cz} {ρ : C0c →* G}

theorem w1_root_cases : ∀ r < 18, ∀ t ∈ [1, 2, 3], Native.glInChart r 0 = true →
    Native.glInChart (Native.glWAct 0 r t).1 0 = true →
      Native.glInChart r 1 = true ∨ Native.glInChart (Native.glWAct 1 r t).1 1 = true := by
  decide

theorem w1K_eq_conj_w2K : δ1hK * w2K * δ1hK = w1K := by
  rw [w2K, show δ1hK * (δ1hK * w1K * δ1hK) * δ1hK = (δ1hK * δ1hK) * w1K * (δ1hK * δ1hK) by
    group, δ1hK_mul_self]
  group

theorem w2K_inv : w2K⁻¹ = w2K :=
  inv_eq_of_mul_eq_one_right w2K_mul_self

theorem w1K_inv : w1K⁻¹ = w1K :=
  inv_eq_of_mul_eq_one_right w1K_mul_self

theorem rhoK_w1K :
    rhoK ρ w1K = rhoK ρ δ1hK * rhoK ρ w2K * rhoK ρ δ1hK := by
  rw [← rhoK_mul ρ δ1hK_mem_C0c w2K_mem_C0c,
    ← rhoK_mul ρ (C0c.mul_mem δ1hK_mem_C0c w2K_mem_C0c) δ1hK_mem_C0c, w1K_eq_conj_w2K]

theorem w1_w2_conj (x : K) :
    w1K * (w2K * x * w2K) * w1K = w2K * (w1K * x * w1K) * w2K := by
  have h121 : w2K * w1K * w2K = w1K := by rw [w2K_comm_w1K, mul_assoc, w2K_mul_self, mul_one]
  conv_lhs => rw [← h121]
  rw [show w2K * w1K * w2K * (w2K * x * w2K) * (w2K * w1K * w2K) =
    w2K * w1K * (w2K * w2K) * x * (w2K * w2K) * w1K * w2K by group, w2K_mul_self]
  group

theorem w1Levi_of_mem_Ax25
    {α : Cz} (hm : SmithC0Marking φ α ρ) (hD : D1Core φ ρ)
    {y : K} (hyR : y ∈ rootSet) (hyA : y ∈ Ax25) (hy' : w1K * y * w1K ∈ Cz) :
    rhoK ρ w1K * phiInv φ y * (rhoK ρ w1K)⁻¹ = phiInv φ (w1K * y * w1K) := by
  have hd := rhoK_δ1hK_inv (ρ := ρ)
  have hyC := (mem_Ax25.1 hyA).1
  have hδy : δ1hK * y * δ1hK ∈ Cz := conj_δ1hK_mem_Cz_of_Ax25 hyA
  have hδyR : δ1hK * y * δ1hK ∈ rootSet := by
    have := wGen_rootSet (i := 4) (by norm_num) hyR
    rwa [wGen_four, δ1hK_inv_eq_self] at this
  set u := w2K * (δ1hK * y * δ1hK) * w2K with hu
  have huR : u ∈ rootSet := by
    have := wGen_rootSet (i := 1) (by norm_num) hδyR
    rwa [wGen_one, w2K_inv] at this
  have huC : u ∈ Cz := Cz.mul_mem (Cz.mul_mem w2K_mem_Cz hδy) w2K_mem_Cz
  have hδu : δ1hK * u * δ1hK = w1K * y * w1K := by
    rw [hu, ← w1K_eq_conj_w2K]
    group
  have e1 := hD y hyR hyC hδy
  have e2 := rhoK_conj_phiInv hm w2K_mem_C0c w2K_mem_Cz (δ1hK * y * δ1hK)
  rw [w2K_inv] at e2
  have e3 := hD u huR huC (by rw [hδu]; exact hy')
  rw [hδu] at e3
  rw [rhoK_w1K, show (rhoK ρ δ1hK * rhoK ρ w2K * rhoK ρ δ1hK)⁻¹ =
      (rhoK ρ δ1hK)⁻¹ * (rhoK ρ w2K)⁻¹ * (rhoK ρ δ1hK)⁻¹ by group, hd,
    show rhoK ρ δ1hK * rhoK ρ w2K * rhoK ρ δ1hK * phiInv φ y *
      (rhoK ρ δ1hK * (rhoK ρ w2K)⁻¹ * rhoK ρ δ1hK) =
      rhoK ρ δ1hK * (rhoK ρ w2K * (rhoK ρ δ1hK * phiInv φ y * rhoK ρ δ1hK) *
        (rhoK ρ w2K)⁻¹) * rhoK ρ δ1hK by group]
  rw [hd] at e1 e3
  rw [e1, e2, ← hu, e3]

theorem w1Levi_holds
    (hz : z ≠ 1)
    (hm : SmithC0Marking φ α3c ρ) : W1Levi φ ρ := by
  have hD := d1Core_holds hz hm
  intro y hyR hyC hy'
  obtain ⟨r, hr, t, ht4, rfl⟩ := hyR
  by_cases ht0 : t = 0
  · subst ht0
    rw [xRootK_zero_eq, mul_one, w1K_mul_self, phiInv_one, mul_one, mul_inv_cancel]
  have ht : t ∈ [1, 2, 3] := by simp only [List.mem_cons, List.not_mem_nil, or_false]; omega
  have hc0 := inChart_of_mem_Cz hr ht hyC
  have hc1 : Native.glInChart (Native.glWAct 0 r t).1 0 = true := by
    have h := hy'
    rw [show w1K * xRootK r t * w1K = wGen 0 * xRootK r t * (wGen 0)⁻¹ by
      rw [wGen_zero, w1K_inv], wGen_conj_xRootK (by norm_num) hr ht4] at h
    exact inChart_of_mem_Cz (glWeyl_spec 0 (by norm_num) r hr t ht4).1
      (by
        have : ∀ r < 18, ∀ t ∈ [1, 2, 3], (Native.glWAct 0 r t).2 ∈ [1, 2, 3] := by decide
        exact this r hr t ht) h
  have hmemA : ∀ {r' t' : ℕ}, r' < 18 → t' < 4 → Native.glInChart r' 1 = true →
      xRootK r' t' ∈ Cz → xRootK r' t' ∈ Ax25 := fun hr' ht' h1 hC => mem_Ax25.2 ⟨hC, by
    rw [← xLongK_one]
    exact xRootK_comm_of_inChart hr' (by norm_num) h1 ht'⟩
  rcases w1_root_cases r hr t ht hc0 hc1 with h1 | h1
  · exact w1Levi_of_mem_Ax25 hm hD ⟨r, hr, t, ht4, rfl⟩ (hmemA hr ht4 h1 hyC) hy'
  ·
    have hw : wGen 1 * xRootK r t * (wGen 1)⁻¹ =
        xRootK (Native.glWAct 1 r t).1 (Native.glWAct 1 r t).2 :=
      wGen_conj_xRootK (by norm_num) hr ht4
    rw [wGen_one, w2K_inv] at hw
    set y' := xRootK (Native.glWAct 1 r t).1 (Native.glWAct 1 r t).2 with hy'def
    have hr' := (glWeyl_spec 1 (by norm_num) r hr t ht4).1
    have ht' := (glWeyl_spec 1 (by norm_num) r hr t ht4).2.1
    have hy'C : y' ∈ Cz := by
      rw [← hw]
      exact Cz.mul_mem (Cz.mul_mem w2K_mem_Cz hyC) w2K_mem_Cz
    have hcomm := w2K_comm_w1K
    have hy'w : w1K * y' * w1K ∈ Cz := by
      rw [← hw, w1_w2_conj]
      exact Cz.mul_mem (Cz.mul_mem w2K_mem_Cz hy') w2K_mem_Cz
    have key := w1Levi_of_mem_Ax25 hm hD ⟨_, hr', _, ht', rfl⟩ (hmemA hr' ht' h1 hy'C) hy'w
    have hyy : xRootK r t = w2K * y' * w2K := by
      rw [← hw, show w2K * (w2K * xRootK r t * w2K) * w2K =
        (w2K * w2K) * xRootK r t * (w2K * w2K) by group, w2K_mul_self]
      group
    have hρc : rhoK ρ w1K * rhoK ρ w2K = rhoK ρ w2K * rhoK ρ w1K := by
      rw [← rhoK_mul ρ w1K_mem_C0c w2K_mem_C0c, ← hcomm, rhoK_mul ρ w2K_mem_C0c w1K_mem_C0c]
    have e1 := rhoK_conj_phiInv hm w2K_mem_C0c w2K_mem_Cz y'
    have e2 := rhoK_conj_phiInv hm w2K_mem_C0c w2K_mem_Cz (w1K * y' * w1K)
    rw [w2K_inv] at e1 e2
    rw [hyy, ← e1, show rhoK ρ w1K * (rhoK ρ w2K * phiInv φ y' * (rhoK ρ w2K)⁻¹) *
        (rhoK ρ w1K)⁻¹ = (rhoK ρ w1K * rhoK ρ w2K) * phiInv φ y' *
          (rhoK ρ w1K * rhoK ρ w2K)⁻¹ * (rhoK ρ w1K * (rhoK ρ w1K)⁻¹) by group, hρc,
      mul_inv_cancel, mul_one, show rhoK ρ w2K * rhoK ρ w1K * phiInv φ y' *
        (rhoK ρ w2K * rhoK ρ w1K)⁻¹ = rhoK ρ w2K * (rhoK ρ w1K * phiInv φ y' *
          (rhoK ρ w1K)⁻¹) * (rhoK ρ w2K)⁻¹ by group, key, e2]
    rw [w1_w2_conj]

end CFSG.Sporadic.Co2Smith
