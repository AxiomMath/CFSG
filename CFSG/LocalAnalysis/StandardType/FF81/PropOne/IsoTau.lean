module

public import CFSG.LocalAnalysis.StandardType.FF81.PropOne.Setup

@[expose] public section

namespace CFSG.StandardType.FF81.PropOne

open CFSG.RankThree.PartTwo.Sec4.Item434Kit (vecElt)

private theorem vecElt_inv_of_conj_inv {H : Type*} [Group H] {z : Fin 3 → H}
    (hc : ∀ i j, z i * z j = z j * z i) (v : Fin 3 → ZMod 3) :
    vecElt (fun i => (z i)⁻¹) v = (vecElt z v)⁻¹ := by
  have c01 : Commute ((z 0 ^ (v 0).val)⁻¹) ((z 1 ^ (v 1).val)⁻¹) :=
    (Commute.pow_pow (hc 0 1) _ _).inv_inv
  have c02 : Commute ((z 0 ^ (v 0).val)⁻¹) ((z 2 ^ (v 2).val)⁻¹) :=
    (Commute.pow_pow (hc 0 2) _ _).inv_inv
  have c12 : Commute ((z 1 ^ (v 1).val)⁻¹) ((z 2 ^ (v 2).val)⁻¹) :=
    (Commute.pow_pow (hc 1 2) _ _).inv_inv
  simp only [vecElt, inv_pow, mul_inv_rev]
  calc (z 0 ^ (v 0).val)⁻¹ * (z 1 ^ (v 1).val)⁻¹ * (z 2 ^ (v 2).val)⁻¹
      = (z 1 ^ (v 1).val)⁻¹ * ((z 0 ^ (v 0).val)⁻¹ * (z 2 ^ (v 2).val)⁻¹) := by
        rw [c01.eq]; group
      _ = (z 1 ^ (v 1).val)⁻¹ * ((z 2 ^ (v 2).val)⁻¹ * (z 0 ^ (v 0).val)⁻¹) := by rw [c02.eq]
      _ = (z 2 ^ (v 2).val)⁻¹ * ((z 1 ^ (v 1).val)⁻¹ * (z 0 ^ (v 0).val)⁻¹) := by
        rw [← mul_assoc, c12.eq, mul_assoc]

private theorem conj_vecElt_of_conj_eq {H : Type*} [Group H] {z : Fin 3 → H} {u : H}
    (h : ∀ i, u * z i * u⁻¹ = z i) (v : Fin 3 → ZMod 3) :
    u * vecElt z v * u⁻¹ = vecElt z v := by
  have hmap := GGFF.vecElt_map (MulAut.conj u) z v
  have hfun : (fun i => MulAut.conj u (z i)) = z := by
    funext i; rw [MulAut.conj_apply, h i]
  rw [hfun] at hmap
  simpa [MulAut.conj_apply] using hmap.symm

private theorem eq_one_of_sq_eq_one_of_cube_eq_one {H : Type*} [Group H] {x : H}
    (h2 : x ^ 2 = 1) (h3 : x ^ 3 = 1) : x = 1 := by
  have h : x ^ 3 = x := by rw [show (3 : ℕ) = 2 + 1 from rfl, pow_succ, h2, one_mul]
  rw [h] at h3
  exact h3

private theorem commute_zpow_vecElt {G : Type} [Group G] {b : G} {L : Subgroup G}
    {z : Fin 3 → ↥L} (hS : GGFF.SettingCore b L z) (j : ℤ) (v : Fin 3 → ZMod 3) :
    b ^ j * vecElt (GGFF.zs z) v = vecElt (GGFF.zs z) v * b ^ j := by
  have hb : ∀ i : Fin 3, Commute (b ^ j) (GGFF.zs z i ^ (v i).val) := fun i =>
    (Commute.zpow_left (hS.comm_of_mem (GGFF.SettingCore.zs_mem z i)).symm j).pow_right _
  rw [vecElt]
  exact (((hb 0).mul_right (hb 1)).mul_right (hb 2)).eq

private theorem commute_of_mem_Bt {G : Type} [Group G] {b : G} {L : Subgroup G}
    {z : Fin 3 → ↥L} (hS : GGFF.SettingCore b L z) {p q : G}
    (hp : p ∈ GGFF.Bt b z) (hq : q ∈ GGFF.Bt b z) : p * q = q * p :=
  congrArg Subtype.val (hS.isElemAbelian_Bt.1.is_comm.comm ⟨p, hp⟩ ⟨q, hq⟩)

private theorem mul_eq_mul_iff {G : Type} [Group G] {b : G} {L : Subgroup G}
    {z : Fin 3 → ↥L} (hS : GGFF.SettingCore b L z) {j j' : ℤ} {y y' : G}
    (hy : y ∈ GGFF.tor (GGFF.zs z)) (hy' : y' ∈ GGFF.tor (GGFF.zs z))
    (h : b ^ j * y = b ^ j' * y') : b ^ j = b ^ j' ∧ y = y' := by
  have h1 : b ^ (j - j') = y' * y⁻¹ := by
    have hcong := congrArg (fun t => b ^ (-j') * t * y⁻¹) h
    have hL : b ^ (-j') * (b ^ j * y) * y⁻¹ = b ^ (j - j') := by
      calc b ^ (-j') * (b ^ j * y) * y⁻¹ = (b ^ (-j') * b ^ j) * (y * y⁻¹) := by
            rw [← mul_assoc, mul_assoc]
        _ = b ^ (j - j') := by
            rw [← zpow_add, mul_inv_cancel, mul_one]
            congr 1; ring
    have hR : b ^ (-j') * (b ^ j' * y') * y⁻¹ = y' * y⁻¹ := by
      calc b ^ (-j') * (b ^ j' * y') * y⁻¹ = (b ^ (-j') * b ^ j') * (y' * y⁻¹) := by
            rw [← mul_assoc, mul_assoc]
        _ = y' * y⁻¹ := by rw [← zpow_add, neg_add_cancel, zpow_zero, one_mul]
    rw [hL, hR] at hcong
    exact hcong
  have hmem : y' * y⁻¹ ∈ GGFF.tor (GGFF.zs z) :=
    (GGFF.tor (GGFF.zs z)).mul_mem hy' ((GGFF.tor (GGFF.zs z)).inv_mem hy)
  have hb : b ^ (j - j') = 1 :=
    hS.zpow_eq_one_of_mem (by rw [h1]; exact GGFF.SettingCore.tor_le z hmem)
  have hbj : b ^ j = b ^ j' := by
    have hcong := congrArg (fun t => t * b ^ j') hb
    rwa [← zpow_add, sub_add_cancel, one_mul] at hcong
  refine ⟨hbj, ?_⟩
  rw [hbj] at h
  exact mul_left_cancel h

private theorem conj_fix_zpowers {G : Type} [Group G] {b : G} {L : Subgroup G}
    {z : Fin 3 → ↥L} (hS : GGFF.SettingCore b L z) {u : G} (hub : u * b * u⁻¹ = b)
    (huz : ∀ i, u * GGFF.zs z i * u⁻¹ = (GGFF.zs z i)⁻¹) {x : G}
    (hx : x ∈ GGFF.Bt b z) :
    u * x * u⁻¹ = x ↔ x ∈ Subgroup.zpowers b := by
  constructor
  · intro h
    obtain ⟨j, v, rfl⟩ := hS.mem_Bt.mp hx
    have hy : u * vecElt (GGFF.zs z) v * u⁻¹ = (vecElt (GGFF.zs z) v)⁻¹ := by
      have hmap := GGFF.vecElt_map (MulAut.conj u) (GGFF.zs z) v
      have hfun : (fun i => MulAut.conj u (GGFF.zs z i)) = fun i => (GGFF.zs z i)⁻¹ := by
        funext i; rw [MulAut.conj_apply, huz i]
      rw [hfun, vecElt_inv_of_conj_inv hS.zs_comm v] at hmap
      simpa [MulAut.conj_apply] using hmap.symm
    have hbj : u * b ^ j * u⁻¹ = b ^ j := by rw [← conj_zpow, hub]
    have e : b ^ j * (vecElt (GGFF.zs z) v)⁻¹ = b ^ j * vecElt (GGFF.zs z) v := by
      calc b ^ j * (vecElt (GGFF.zs z) v)⁻¹
          = (u * b ^ j * u⁻¹) * (u * vecElt (GGFF.zs z) v * u⁻¹) := by rw [hbj, hy]
        _ = u * (b ^ j * vecElt (GGFF.zs z) v) * u⁻¹ := by group
        _ = b ^ j * vecElt (GGFF.zs z) v := h
    have hyy : (vecElt (GGFF.zs z) v)⁻¹ = vecElt (GGFF.zs z) v := mul_left_cancel e
    have hy2 : (vecElt (GGFF.zs z) v) ^ 2 = 1 := by
      have h' := mul_inv_cancel (vecElt (GGFF.zs z) v)
      rw [hyy] at h'
      rwa [pow_two]
    have hy3 : (vecElt (GGFF.zs z) v) ^ 3 = 1 :=
      (GGFF.isElemAbelian_tor hS.zs_pow hS.zs_comm).2 _ (GGFF.vecElt_mem_tor _ v)
    have hy1 : vecElt (GGFF.zs z) v = 1 := eq_one_of_sq_eq_one_of_cube_eq_one hy2 hy3
    rw [hy1, mul_one]
    exact Subgroup.zpow_mem_zpowers b j
  · rintro ⟨j, rfl⟩
    rw [← conj_zpow, hub]

private theorem conj_inv_b_fix_tor {G : Type} [Group G] {b : G} {L : Subgroup G}
    {z : Fin 3 → ↥L} (hS : GGFF.SettingCore b L z) {u : G} (hub : u * b * u⁻¹ = b⁻¹)
    (huz : ∀ i, u * GGFF.zs z i * u⁻¹ = GGFF.zs z i) {x : G}
    (hx : x ∈ GGFF.Bt b z) :
    u * x * u⁻¹ = x ↔ x ∈ GGFF.tor (GGFF.zs z) := by
  constructor
  · intro h
    obtain ⟨j, v, rfl⟩ := hS.mem_Bt.mp hx
    have hy : u * vecElt (GGFF.zs z) v * u⁻¹ = vecElt (GGFF.zs z) v :=
      conj_vecElt_of_conj_eq huz v
    have hbj : u * b ^ j * u⁻¹ = b ^ (-j) := by rw [← conj_zpow, hub, inv_zpow, zpow_neg]
    have e : b ^ (-j) * vecElt (GGFF.zs z) v = b ^ j * vecElt (GGFF.zs z) v := by
      calc b ^ (-j) * vecElt (GGFF.zs z) v
          = (u * b ^ j * u⁻¹) * (u * vecElt (GGFF.zs z) v * u⁻¹) := by rw [hbj, hy]
        _ = u * (b ^ j * vecElt (GGFF.zs z) v) * u⁻¹ := by group
        _ = b ^ j * vecElt (GGFF.zs z) v := h
    have hbj_eq : b ^ (-j) = b ^ j := mul_right_cancel e
    have h2 : (b ^ j) ^ 2 = 1 := by
      rw [pow_two]
      nth_rewrite 1 [← hbj_eq]
      rw [← zpow_add, neg_add_cancel, zpow_zero]
    have h3 : (b ^ j) ^ 3 = 1 := by
      rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hS.b_cube, one_zpow]
    have hbj1 : b ^ j = 1 := eq_one_of_sq_eq_one_of_cube_eq_one h2 h3
    rw [hbj1, one_mul]
    exact GGFF.vecElt_mem_tor _ v
  · intro hx'
    obtain ⟨v, rfl⟩ := hS.mem_torG.mp hx'
    exact conj_vecElt_of_conj_eq huz v

private theorem conj_inv_b_inv_zpowers {G : Type} [Group G] {b : G} {L : Subgroup G}
    {z : Fin 3 → ↥L} (hS : GGFF.SettingCore b L z) {u : G} (hub : u * b * u⁻¹ = b⁻¹)
    (huz : ∀ i, u * GGFF.zs z i * u⁻¹ = GGFF.zs z i) {x : G}
    (hx : x ∈ GGFF.Bt b z) :
    u * x * u⁻¹ = x⁻¹ ↔ x ∈ Subgroup.zpowers b := by
  constructor
  · intro h
    obtain ⟨j, v, rfl⟩ := hS.mem_Bt.mp hx
    have hy : u * vecElt (GGFF.zs z) v * u⁻¹ = vecElt (GGFF.zs z) v :=
      conj_vecElt_of_conj_eq huz v
    have hbj : u * b ^ j * u⁻¹ = b ^ (-j) := by rw [← conj_zpow, hub, inv_zpow, zpow_neg]
    have e : b ^ (-j) * vecElt (GGFF.zs z) v = (b ^ j * vecElt (GGFF.zs z) v)⁻¹ := by
      calc b ^ (-j) * vecElt (GGFF.zs z) v
          = (u * b ^ j * u⁻¹) * (u * vecElt (GGFF.zs z) v * u⁻¹) := by rw [hbj, hy]
        _ = u * (b ^ j * vecElt (GGFF.zs z) v) * u⁻¹ := by group
        _ = (b ^ j * vecElt (GGFF.zs z) v)⁻¹ := h
    have h' : b ^ (-j) * vecElt (GGFF.zs z) v
        = (vecElt (GGFF.zs z) v)⁻¹ * b ^ (-j) := by
      rw [e, mul_inv_rev, ← zpow_neg]
    have hcomm : vecElt (GGFF.zs z) v * b ^ (-j) = b ^ (-j) * vecElt (GGFF.zs z) v :=
      (commute_zpow_vecElt hS (-j) v).symm
    have hyy : vecElt (GGFF.zs z) v = (vecElt (GGFF.zs z) v)⁻¹ := by
      have h2 : vecElt (GGFF.zs z) v * b ^ (-j) = (vecElt (GGFF.zs z) v)⁻¹ * b ^ (-j) := by
        rw [hcomm, h']
      exact mul_right_cancel h2
    have hy2 : (vecElt (GGFF.zs z) v) ^ 2 = 1 := by
      have h := mul_inv_cancel (vecElt (GGFF.zs z) v)
      rw [← hyy] at h
      rwa [pow_two]
    have hy3 : (vecElt (GGFF.zs z) v) ^ 3 = 1 :=
      (GGFF.isElemAbelian_tor hS.zs_pow hS.zs_comm).2 _ (GGFF.vecElt_mem_tor _ v)
    have hy1 : vecElt (GGFF.zs z) v = 1 := eq_one_of_sq_eq_one_of_cube_eq_one hy2 hy3
    rw [hy1, mul_one]
    exact Subgroup.zpow_mem_zpowers b j
  · rintro ⟨j, rfl⟩
    rw [← conj_zpow, hub, inv_zpow]

theorem isolated_tau {G : Type} [Group G] [Finite G] {n : ℕ} {b : G} {L : Subgroup G}
    {z : Fin 3 → ↥L} (h : Counterexample G n b L z) {τ : G} (hτL : τ ∈ L) (hτ2 : τ ^ 2 = 1)
    (hτz : ∀ i : Fin 3, τ * GGFF.zs z i * τ⁻¹ = (GGFF.zs z i)⁻¹)
    (hno : ∀ g ∈ nB b z, g * b * g⁻¹ ≠ b⁻¹) :
    ∀ g ∈ nB b z, g * τ * g⁻¹ * τ * (g * τ * g⁻¹)⁻¹ * τ⁻¹ ∈ cB b z →
      g * τ * g⁻¹ * τ⁻¹ ∈ cB b z := by
  intro g hg hcomm
  have hS : GGFF.SettingCore b L z := h.settingCore
  have hb3 : b ^ 3 = 1 := hS.b_cube
  have _ := hτ2
  have _ := hno
  have hτb : τ * b * τ⁻¹ = b := by rw [hS.comm_of_mem hτL, mul_inv_cancel_right]
  have hτN : τ ∈ nB b z := by
    refine GGFF.SettingCore.mem_nor_Bt (hb := ?_) (hz := ?_)
    · rw [hτb]; exact GGFF.SettingCore.b_mem_Bt b z
    · intro i; rw [hτz i]
      exact (GGFF.Bt b z).inv_mem (GGFF.SettingCore.zs_mem_Bt b z i)
  set P : G := g * τ * g⁻¹ with hPdef
  have hPN : P ∈ nB b z := by
    rw [hPdef]
    exact (nB b z).mul_mem ((nB b z).mul_mem hg hτN) ((nB b z).inv_mem hg)
  have hbB : b ∈ GGFF.Bt b z := GGFF.SettingCore.b_mem_Bt b z
  have hb'B : g * b * g⁻¹ ∈ GGFF.Bt b z := (Subgroup.mem_normalizer_iff.mp hg b).mp hbB
  have hb'L : g * b * g⁻¹ ∉ L := h.noL g
  have hτvec : ∀ v : Fin 3 → ZMod 3,
      τ * vecElt (GGFF.zs z) v * τ⁻¹ = (vecElt (GGFF.zs z) v)⁻¹ := by
    intro v
    have hmap := GGFF.vecElt_map (MulAut.conj τ) (GGFF.zs z) v
    have hfun : (fun i => MulAut.conj τ (GGFF.zs z i)) = fun i => (GGFF.zs z i)⁻¹ := by
      funext i; rw [MulAut.conj_apply, hτz i]
    rw [hfun, vecElt_inv_of_conj_inv hS.zs_comm v] at hmap
    simpa [MulAut.conj_apply] using hmap.symm
  have hzp : ∀ x : G,
      (x ∈ Subgroup.zpowers (g * b * g⁻¹) ↔ g⁻¹ * x * g ∈ Subgroup.zpowers b) := by
    intro x
    constructor
    · intro hx
      obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp hx
      exact Subgroup.mem_zpowers_iff.mpr ⟨j, by rw [← hj, conj_zpow]; group⟩
    · intro hx
      obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp hx
      exact Subgroup.mem_zpowers_iff.mpr ⟨j, by rw [conj_zpow, hj]; group⟩
  have hfixP : ∀ x ∈ GGFF.Bt b z,
      P * x * P⁻¹ = x ↔ x ∈ Subgroup.zpowers (g * b * g⁻¹) := by
    intro x hx
    have hgx : g⁻¹ * x * g ∈ GGFF.Bt b z := by
      simpa using (Subgroup.mem_normalizer_iff.mp ((nB b z).inv_mem hg) x).mp hx
    have e : P * x * P⁻¹ = g * (τ * (g⁻¹ * x * g) * τ⁻¹) * g⁻¹ := by
      rw [hPdef]; group
    rw [e]
    constructor
    · intro hh
      have h2 : τ * (g⁻¹ * x * g) * τ⁻¹ = g⁻¹ * x * g := by
        have hcong := congrArg (fun t => g⁻¹ * t * g) hh
        simpa [mul_assoc] using hcong
      exact (hzp x).mpr ((conj_fix_zpowers hS hτb hτz hgx).mp h2)
    · intro hx'
      have h2 : τ * (g⁻¹ * x * g) * τ⁻¹ = g⁻¹ * x * g :=
        (conj_fix_zpowers hS hτb hτz hgx).mpr ((hzp x).mp hx')
      rw [h2]; group
  have hconj : ∀ x ∈ GGFF.Bt b z,
      P * (τ * x * τ⁻¹) * P⁻¹ = τ * (P * x * P⁻¹) * τ⁻¹ := by
    intro x hx
    have hxP : P * x * P⁻¹ ∈ GGFF.Bt b z := (Subgroup.mem_normalizer_iff.mp hPN x).mp hx
    have hτwB : τ * (P * x * P⁻¹) * τ⁻¹ ∈ GGFF.Bt b z :=
      (Subgroup.mem_normalizer_iff.mp hτN _).mp hxP
    have hcw : (τ * (P * x * P⁻¹) * τ⁻¹) * (P * τ * P⁻¹ * τ⁻¹)
        = (P * τ * P⁻¹ * τ⁻¹) * (τ * (P * x * P⁻¹) * τ⁻¹) :=
      (Subgroup.mem_centralizer_iff.mp hcomm) _ hτwB
    have hcτ : P * τ * P⁻¹ = (P * τ * P⁻¹ * τ⁻¹) * τ := by group
    have hcτ' : P * τ⁻¹ * P⁻¹ = τ⁻¹ * (P * τ * P⁻¹ * τ⁻¹)⁻¹ := by group
    calc P * (τ * x * τ⁻¹) * P⁻¹
        = (P * τ * P⁻¹) * (P * x * P⁻¹) * (P * τ⁻¹ * P⁻¹) := by group
      _ = (P * τ * P⁻¹ * τ⁻¹) * (τ * (P * x * P⁻¹) * τ⁻¹)
            * (P * τ * P⁻¹ * τ⁻¹)⁻¹ := by rw [hcτ, hcτ']; group
      _ = τ * (P * x * P⁻¹) * τ⁻¹ := by rw [← hcw, mul_assoc, mul_inv_cancel, mul_one]
  have hfixb' : P * (g * b * g⁻¹) * P⁻¹ = g * b * g⁻¹ := by
    rw [hPdef]
    calc g * τ * g⁻¹ * (g * b * g⁻¹) * (g * τ * g⁻¹)⁻¹
        = g * (τ * b * τ⁻¹) * g⁻¹ := by group
      _ = g * b * g⁻¹ := by rw [hτb]
  have hσb'B : τ * (g * b * g⁻¹) * τ⁻¹ ∈ GGFF.Bt b z :=
    (Subgroup.mem_normalizer_iff.mp hτN _).mp hb'B
  have hσb'fix : P * (τ * (g * b * g⁻¹) * τ⁻¹) * P⁻¹ = τ * (g * b * g⁻¹) * τ⁻¹ := by
    rw [hconj _ hb'B, hfixb']
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp ((hfixP _ hσb'B).mp hσb'fix)
  obtain ⟨i, v, hbv⟩ := hS.mem_Bt.mp hb'B
  have hyB₁ : vecElt (GGFF.zs z) v ∈ GGFF.tor (GGFF.zs z) := GGFF.vecElt_mem_tor _ v
  have hy3 : (vecElt (GGFF.zs z) v) ^ 3 = 1 :=
    (GGFF.isElemAbelian_tor hS.zs_pow hS.zs_comm).2 _ hyB₁
  have hy3z : (vecElt (GGFF.zs z) v) ^ (3 : ℤ) = 1 := by rw [zpow_ofNat]; exact hy3
  have hτy : τ * vecElt (GGFF.zs z) v * τ⁻¹ = (vecElt (GGFF.zs z) v)⁻¹ := hτvec v
  have hτxy : τ * (b ^ i * vecElt (GGFF.zs z) v) * τ⁻¹
      = b ^ i * (vecElt (GGFF.zs z) v)⁻¹ := by
    calc τ * (b ^ i * vecElt (GGFF.zs z) v) * τ⁻¹
        = (τ * b ^ i * τ⁻¹) * (τ * vecElt (GGFF.zs z) v * τ⁻¹) := by group
      _ = b ^ i * (vecElt (GGFF.zs z) v)⁻¹ := by
          rw [show τ * b ^ i * τ⁻¹ = b ^ i by rw [← conj_zpow, hτb], hτy]
  have hLHS : τ * (g * b * g⁻¹) * τ⁻¹ = b ^ i * (vecElt (GGFF.zs z) v)⁻¹ := by
    rw [hbv, hτxy]
  have hRHS : (g * b * g⁻¹) ^ k = b ^ (i * k) * (vecElt (GGFF.zs z) v) ^ k := by
    rw [hbv, ((commute_iff_eq _ _).mpr (commute_zpow_vecElt hS i v)).mul_zpow, zpow_mul]
  have heq : b ^ (i * k) * (vecElt (GGFF.zs z) v) ^ k
      = b ^ i * (vecElt (GGFF.zs z) v)⁻¹ := by
    rw [← hRHS, hk, hLHS]
  have huniq := mul_eq_mul_iff hS (y := (vecElt (GGFF.zs z) v) ^ k)
    (y' := (vecElt (GGFF.zs z) v)⁻¹)
    ((GGFF.tor (GGFF.zs z)).zpow_mem hyB₁ k) ((GGFF.tor (GGFF.zs z)).inv_mem hyB₁) heq
  have hbik : b ^ (i * k) = b ^ i := huniq.1
  have hyk : (vecElt (GGFF.zs z) v) ^ k = (vecElt (GGFF.zs z) v)⁻¹ := huniq.2
  have hbi_ne : b ^ i ≠ 1 := by
    intro h1
    exact hb'L (by rw [hbv, h1, one_mul]; exact GGFF.SettingCore.tor_le z hyB₁)
  have h3dvd : (3 : ℤ) ∣ i * (k - 1) := by
    have hb1 : b ^ (i * k - i) = 1 := by
      rw [show i * k - i = i * k + (-i) by ring, zpow_add, hbik, ← zpow_add, add_neg_cancel,
        zpow_zero]
    rw [show i * k - i = i * (k - 1) by ring] at hb1
    rwa [← orderOf_dvd_iff_zpow_eq_one, hS.ord] at hb1
  have h3ndvd : ¬ (3 : ℤ) ∣ i := by
    intro hd
    apply hbi_ne
    rw [← orderOf_dvd_iff_zpow_eq_one, hS.ord]
    exact hd
  have h3dvd2 : (3 : ℤ) ∣ (k - 1) :=
    (Int.prime_three.dvd_or_dvd h3dvd).resolve_left h3ndvd
  have hyk1 : (vecElt (GGFF.zs z) v) ^ (k + 1) = 1 := by
    rw [zpow_add, zpow_one, hyk, inv_mul_cancel]
  obtain ⟨m, hm⟩ := h3dvd2
  have hy2 : (vecElt (GGFF.zs z) v) ^ 2 = 1 := by
    have hh := hyk1
    rw [show k + 1 = 3 * m + 2 by linarith, zpow_add, zpow_mul, hy3z, one_zpow, one_mul] at hh
    rwa [zpow_ofNat] at hh
  have hy1 : vecElt (GGFF.zs z) v = 1 := eq_one_of_sq_eq_one_of_cube_eq_one hy2 hy3
  have hb'eq : g * b * g⁻¹ = b ^ i := by rw [hbv, hy1, mul_one]
  have hb'ord : orderOf (g * b * g⁻¹) = 3 := by
    have hdvd : orderOf (g * b * g⁻¹) ∣ 3 := by
      rw [orderOf_dvd_iff_pow_eq_one, hb'eq]
      rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hb3, one_zpow]
    rcases Nat.prime_three.eq_one_or_self_of_dvd (orderOf (g * b * g⁻¹)) hdvd with h1 | h3
    · exact absurd (show g * b * g⁻¹ ∈ L from by
        rw [orderOf_eq_one_iff.mp h1]; exact L.one_mem) hb'L
    · exact h3
  have hle : Subgroup.zpowers (g * b * g⁻¹) ≤ Subgroup.zpowers b :=
    Subgroup.zpowers_le.mpr (by rw [hb'eq]; exact Subgroup.zpow_mem_zpowers b i)
  have hcardle : Nat.card (Subgroup.zpowers b) ≤ Nat.card (Subgroup.zpowers (g * b * g⁻¹)) := by
    rw [Nat.card_zpowers, Nat.card_zpowers, hb'ord, hS.ord]
  have heqzp : Subgroup.zpowers (g * b * g⁻¹) = Subgroup.zpowers b :=
    Subgroup.eq_of_le_of_card_ge hle hcardle
  have hPb : P * b * P⁻¹ = b :=
    (hfixP b hbB).mpr (heqzp.symm ▸ Subgroup.mem_zpowers b)
  have hInv_le : ∀ x ∈ GGFF.Bt b z, P * x * P⁻¹ = x⁻¹ → x ∈ GGFF.tor (GGFF.zs z) := by
    intro x hx hxinv
    obtain ⟨j, w, hxw⟩ := hS.mem_Bt.mp hx
    have hwB₁ : vecElt (GGFF.zs z) w ∈ GGFF.tor (GGFF.zs z) := GGFF.vecElt_mem_tor _ w
    have hτw : τ * vecElt (GGFF.zs z) w * τ⁻¹ = (vecElt (GGFF.zs z) w)⁻¹ := hτvec w
    have hτx : τ * x * τ⁻¹ = b ^ j * (vecElt (GGFF.zs z) w)⁻¹ := by
      rw [hxw]
      calc τ * (b ^ j * vecElt (GGFF.zs z) w) * τ⁻¹
          = (τ * b ^ j * τ⁻¹) * (τ * vecElt (GGFF.zs z) w * τ⁻¹) := by group
        _ = b ^ j * (vecElt (GGFF.zs z) w)⁻¹ := by
            rw [show τ * b ^ j * τ⁻¹ = b ^ j by rw [← conj_zpow, hτb], hτw]
    have hτxB : τ * x * τ⁻¹ ∈ GGFF.Bt b z := (Subgroup.mem_normalizer_iff.mp hτN x).mp hx
    have hσx : P * (τ * x * τ⁻¹) * P⁻¹ = (τ * x * τ⁻¹)⁻¹ := by
      rw [hconj x hx, hxinv]; group
    have hcommx : x * (τ * x * τ⁻¹) = (τ * x * τ⁻¹) * x :=
      commute_of_mem_Bt hS hx hτxB
    have hxx : x * (τ * x * τ⁻¹) = b ^ (2 * j) := by
      rw [hτx, hxw, show (2 : ℤ) * j = j + j by ring, zpow_add]
      calc (b ^ j * vecElt (GGFF.zs z) w) * (b ^ j * (vecElt (GGFF.zs z) w)⁻¹)
          = b ^ j * (vecElt (GGFF.zs z) w * b ^ j) * (vecElt (GGFF.zs z) w)⁻¹ := by group
        _ = b ^ j * (b ^ j * vecElt (GGFF.zs z) w) * (vecElt (GGFF.zs z) w)⁻¹ := by
            rw [show vecElt (GGFF.zs z) w * b ^ j = b ^ j * vecElt (GGFF.zs z) w from
              (commute_zpow_vecElt hS j w).symm]
        _ = b ^ j * b ^ j * (vecElt (GGFF.zs z) w * (vecElt (GGFF.zs z) w)⁻¹) := by group
        _ = b ^ j * b ^ j := by rw [mul_inv_cancel, mul_one]
    have hb2j_inv : P * b ^ (2 * j) * P⁻¹ = (b ^ (2 * j))⁻¹ := by
      rw [← hxx]
      calc P * (x * (τ * x * τ⁻¹)) * P⁻¹
          = (P * x * P⁻¹) * (P * (τ * x * τ⁻¹) * P⁻¹) := by group
        _ = x⁻¹ * (τ * x * τ⁻¹)⁻¹ := by rw [hxinv, hσx]
        _ = (x * (τ * x * τ⁻¹))⁻¹ := by
            rw [show (x * (τ * x * τ⁻¹))⁻¹ = (τ * x * τ⁻¹)⁻¹ * x⁻¹ by rw [mul_inv_rev]]
            exact ((commute_iff_eq _ _).mpr hcommx).inv_inv.eq
    have hb2jFix : P * b ^ (2 * j) * P⁻¹ = b ^ (2 * j) := by rw [← conj_zpow, hPb]
    have hb2j_eq : b ^ (2 * j) = (b ^ (2 * j))⁻¹ := hb2jFix.symm.trans hb2j_inv
    have hb2j2 : (b ^ (2 * j)) ^ 2 = 1 := by
      rw [pow_two]; nth_rewrite 1 [hb2j_eq]; exact inv_mul_cancel _
    have hb2j3 : (b ^ (2 * j)) ^ 3 = 1 := by
      rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hb3, one_zpow]
    have hb2j1 : b ^ (2 * j) = 1 := eq_one_of_sq_eq_one_of_cube_eq_one hb2j2 hb2j3
    have hbj2 : (b ^ j) ^ 2 = 1 := by
      rw [pow_two, ← zpow_add, show j + j = 2 * j by ring, hb2j1]
    have hbj3 : (b ^ j) ^ 3 = 1 := by
      rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hb3, one_zpow]
    have hbj1 : b ^ j = 1 := eq_one_of_sq_eq_one_of_cube_eq_one hbj2 hbj3
    rw [show x = vecElt (GGFF.zs z) w by rw [hxw, hbj1, one_mul]]
    exact hwB₁
  have hJle : (GGFF.tor (GGFF.zs z)).map (MulAut.conj g).toMonoidHom
      ≤ GGFF.tor (GGFF.zs z) := by
    intro x hx
    rw [Subgroup.mem_map] at hx
    obtain ⟨w, hw, hwx⟩ := hx
    rw [← hwx]
    simp only [MulEquiv.toMonoidHom_eq_coe, MonoidHom.coe_coe, MulAut.conj_apply]
    apply hInv_le
    · exact (Subgroup.mem_normalizer_iff.mp hg w).mp (GGFF.SettingCore.tor_le_Bt b z hw)
    · have hτw : τ * w * τ⁻¹ = w⁻¹ := by
        obtain ⟨v, rfl⟩ := hS.mem_torG.mp hw
        exact hτvec v
      rw [show P * (g * w * g⁻¹) * P⁻¹ = g * (τ * w * τ⁻¹) * g⁻¹ by rw [hPdef]; group,
        hτw, show g * w⁻¹ * g⁻¹ = (g * w * g⁻¹)⁻¹ by group]
  have hJcard : Nat.card ((GGFF.tor (GGFF.zs z)).map (MulAut.conj g).toMonoidHom)
      = Nat.card (GGFF.tor (GGFF.zs z)) :=
    Subgroup.card_map_of_injective (MulAut.conj g).injective
  have hJeq : (GGFF.tor (GGFF.zs z)).map (MulAut.conj g).toMonoidHom = GGFF.tor (GGFF.zs z) :=
    Subgroup.eq_of_le_of_card_ge hJle (by rw [hJcard])
  have hPy : ∀ y ∈ GGFF.tor (GGFF.zs z), P * y * P⁻¹ = y⁻¹ := by
    intro y hy
    have hyJ : y ∈ (GGFF.tor (GGFF.zs z)).map (MulAut.conj g).toMonoidHom := hJeq.symm ▸ hy
    rw [Subgroup.mem_map] at hyJ
    obtain ⟨w, hw, hwy⟩ := hyJ
    rw [← hwy]
    simp only [MulEquiv.toMonoidHom_eq_coe, MonoidHom.coe_coe, MulAut.conj_apply]
    have hτw : τ * w * τ⁻¹ = w⁻¹ := by
      obtain ⟨v, rfl⟩ := hS.mem_torG.mp hw
      exact hτvec v
    rw [show P * (g * w * g⁻¹) * P⁻¹ = g * (τ * w * τ⁻¹) * g⁻¹ by rw [hPdef]; group,
      hτw, show g * w⁻¹ * g⁻¹ = (g * w * g⁻¹)⁻¹ by group]
  have hPτ : ∀ y ∈ GGFF.Bt b z, P * y * P⁻¹ = τ * y * τ⁻¹ := by
    intro y hy
    obtain ⟨j, w, hyw⟩ := hS.mem_Bt.mp hy
    rw [hyw]
    have hτw : τ * vecElt (GGFF.zs z) w * τ⁻¹ = (vecElt (GGFF.zs z) w)⁻¹ := hτvec w
    calc P * (b ^ j * vecElt (GGFF.zs z) w) * P⁻¹
        = (P * b ^ j * P⁻¹) * (P * vecElt (GGFF.zs z) w * P⁻¹) := by group
      _ = b ^ j * (vecElt (GGFF.zs z) w)⁻¹ := by
          rw [show P * b ^ j * P⁻¹ = b ^ j by rw [← conj_zpow, hPb],
            hPy _ (GGFF.vecElt_mem_tor _ w)]
      _ = (τ * b ^ j * τ⁻¹) * (τ * vecElt (GGFF.zs z) w * τ⁻¹) := by
          rw [show τ * b ^ j * τ⁻¹ = b ^ j by rw [← conj_zpow, hτb], hτw]
      _ = τ * (b ^ j * vecElt (GGFF.zs z) w) * τ⁻¹ := by group
  have hfinal : P * τ⁻¹ ∈ cB b z := by
    refine Subgroup.mem_centralizer_iff.mpr fun x hx => ?_
    have hxτ : τ⁻¹ * x * τ ∈ GGFF.Bt b z := by
      simpa using (Subgroup.mem_normalizer_iff.mp ((nB b z).inv_mem hτN) x).mp hx
    have h1 : P * (τ⁻¹ * x * τ) * P⁻¹ = τ * (τ⁻¹ * x * τ) * τ⁻¹ := hPτ _ hxτ
    have h2 : (P * τ⁻¹) * x * (P * τ⁻¹)⁻¹ = x := by
      rw [show (P * τ⁻¹) * x * (P * τ⁻¹)⁻¹ = P * (τ⁻¹ * x * τ) * P⁻¹ by group, h1]
      group
    have h3 : (P * τ⁻¹) * x = x * (P * τ⁻¹) := by
      have hcong := congrArg (fun t => t * (P * τ⁻¹)) h2
      simpa [mul_assoc] using hcong
    exact h3.symm
  exact hfinal

theorem exists_t_of_inverts {G : Type} [Group G] [Finite G] {n : ℕ} {b : G} {L : Subgroup G}
    {z : Fin 3 → ↥L} (h : Counterexample G n b L z)
    (hinv : ∃ g ∈ nB b z, g * b * g⁻¹ = b⁻¹) :
    ∃ t ∈ nB b z, t * b * t⁻¹ = b⁻¹ ∧ ∀ i : Fin 3, t * GGFF.zs z i * t⁻¹ = GGFF.zs z i := by
  obtain ⟨g, hg, hgb⟩ := hinv
  have hS : GGFF.SettingCore b L z := h.settingCore
  have hgbz : g * b * g⁻¹ ∈ Subgroup.zpowers b := by
    rw [hgb]; exact Subgroup.inv_mem _ (Subgroup.mem_zpowers b)
  choose j e he using fun i => h.facts.stab g hg hgbz i
  have hjinj : Function.Injective j := by
    intro i k hjk
    have hwi : GGFF.zs z i = (g⁻¹ * GGFF.zs z (j i) * g) ^ e i := by
      rw [show (g⁻¹ * GGFF.zs z (j i) * g) ^ e i
          = g⁻¹ * GGFF.zs z (j i) ^ e i * g by
        rw [show g⁻¹ * GGFF.zs z (j i) * g = g⁻¹ * GGFF.zs z (j i) * (g⁻¹)⁻¹ by
          rw [inv_inv]]
        rw [conj_pow, inv_inv]]
      simpa [mul_assoc] using congrArg (fun t => g⁻¹ * t * g) (he i).2
    have hwk' : GGFF.zs z k = (g⁻¹ * GGFF.zs z (j k) * g) ^ e k := by
      rw [show (g⁻¹ * GGFF.zs z (j k) * g) ^ e k
          = g⁻¹ * GGFF.zs z (j k) ^ e k * g by
        rw [show g⁻¹ * GGFF.zs z (j k) * g = g⁻¹ * GGFF.zs z (j k) * (g⁻¹)⁻¹ by
          rw [inv_inv]]
        rw [conj_pow, inv_inv]]
      simpa [mul_assoc] using congrArg (fun t => g⁻¹ * t * g) (he k).2
    have hwk : GGFF.zs z k = (g⁻¹ * GGFF.zs z (j i) * g) ^ e k := by
      rw [← hjk] at hwk'
      exact hwk'
    have hw3 : (g⁻¹ * GGFF.zs z (j i) * g) ^ 3 = 1 := by
      rw [show g⁻¹ * GGFF.zs z (j i) * g = g⁻¹ * GGFF.zs z (j i) * (g⁻¹)⁻¹ by rw [inv_inv],
        conj_pow, hS.zs_pow, mul_one, inv_inv, inv_mul_cancel]
    have h2 : GGFF.zs z i = GGFF.zs z k ∨ GGFF.zs z i = (GGFF.zs z k)⁻¹ := by
      rcases (he i).1 with hi | hi <;> rcases (he k).1 with hk | hk
      · left; rw [hwi, hwk, hi, hk]
      · right; rw [hwi, hwk, hi, hk, pow_one]
        exact eq_inv_iff_mul_eq_one.mpr (by rw [← pow_succ', hw3])
      · right; rw [hwi, hwk, hi, hk, pow_one]
        exact eq_inv_iff_mul_eq_one.mpr (by rw [← pow_succ, hw3])
      · left; rw [hwi, hwk, hi, hk]
    rcases h2 with h2 | h2
    · exact h.model.eq_of_z_eq (Or.inl (Subtype.ext h2))
    · exact h.model.eq_of_z_eq (Or.inr (Subtype.ext (by simpa using h2)))
  let σ : Equiv.Perm (Fin 3) := Equiv.ofBijective j (Finite.injective_iff_bijective.mp hjinj)
  let ε : Fin 3 → ZMod 3 := fun i => (e i : ZMod 3)
  have hε : ∀ i, ε i ≠ 0 := by
    intro i
    rcases (he i).1 with h1 | h2
    · show ((e i : ZMod 3)) ≠ 0
      rw [h1]; decide
    · show ((e i : ZMod 3)) ≠ 0
      rw [h2]; decide
  obtain ⟨m, hm⟩ := h.model.mono σ ε hε
  have hmb : b⁻¹ * (m : G) = (m : G) * b⁻¹ := by
    calc b⁻¹ * (m : G) = b⁻¹ * ((m : G) * b) * b⁻¹ := by group
      _ = b⁻¹ * (b * (m : G)) * b⁻¹ := by rw [hS.comm_of_mem m.2]
      _ = (m : G) * b⁻¹ := by group
  have hm' : ∀ i, (m : G) * GGFF.zs z i * (m : G)⁻¹ = GGFF.zs z (j i) ^ (ε i).val := by
    intro i
    have h := congrArg Subtype.val (hm i)
    simpa [σ] using h
  have hεi : ∀ i, (ε i).val = e i := by
    intro i
    rcases (he i).1 with h1 | h2
    · show ((e i : ZMod 3)).val = e i
      rw [h1]; decide
    · show ((e i : ZMod 3)).val = e i
      rw [h2]; decide
  refine ⟨(m : G)⁻¹ * g, ?_, ?_, ?_⟩
  · refine GGFF.SettingCore.mem_nor_Bt (hb := ?_) (hz := ?_)
    · rw [show (m : G)⁻¹ * g * b * ((m : G)⁻¹ * g)⁻¹ = (m : G)⁻¹ * (g * b * g⁻¹) * (m : G)
        by group, hgb]
      rw [show (m : G)⁻¹ * b⁻¹ * (m : G) = b⁻¹ by rw [mul_assoc, hmb]; group]
      exact (GGFF.Bt b z).inv_mem (GGFF.SettingCore.b_mem_Bt b z)
    · intro i
      rw [show (m : G)⁻¹ * g * GGFF.zs z i * ((m : G)⁻¹ * g)⁻¹
          = (m : G)⁻¹ * (g * GGFF.zs z i * g⁻¹) * (m : G) by group, (he i).2,
        ← hεi i, ← hm' i]
      convert GGFF.SettingCore.zs_mem_Bt b z i using 1
      group
  · rw [show (m : G)⁻¹ * g * b * ((m : G)⁻¹ * g)⁻¹ = (m : G)⁻¹ * (g * b * g⁻¹) * (m : G)
      by group, hgb]
    rw [show (m : G)⁻¹ * b⁻¹ * (m : G) = b⁻¹ by rw [mul_assoc, hmb]; group]
  · intro i
    rw [show (m : G)⁻¹ * g * GGFF.zs z i * ((m : G)⁻¹ * g)⁻¹
        = (m : G)⁻¹ * (g * GGFF.zs z i * g⁻¹) * (m : G) by group, (he i).2,
      ← hεi i, ← hm' i]
    group

theorem isolated_t {G : Type} [Group G] [Finite G] {n : ℕ} {b : G} {L : Subgroup G}
    {z : Fin 3 → ↥L} (h : Counterexample G n b L z) {t : G} (htN : t ∈ nB b z)
    (htb : t * b * t⁻¹ = b⁻¹) (htz : ∀ i : Fin 3, t * GGFF.zs z i * t⁻¹ = GGFF.zs z i) :
    ∀ g ∈ nB b z, g * t * g⁻¹ * t * (g * t * g⁻¹)⁻¹ * t⁻¹ ∈ cB b z →
      g * t * g⁻¹ * t⁻¹ ∈ cB b z := by
  intro g hg hcomm
  have hS : GGFF.SettingCore b L z := h.settingCore
  have hb3 : b ^ 3 = 1 := hS.b_cube
  set P : G := g * t * g⁻¹ with hPdef
  have hPN : P ∈ nB b z := by
    rw [hPdef]
    exact (nB b z).mul_mem ((nB b z).mul_mem hg htN) ((nB b z).inv_mem hg)
  have hbB : b ∈ GGFF.Bt b z := GGFF.SettingCore.b_mem_Bt b z
  have hb'B : g * b * g⁻¹ ∈ GGFF.Bt b z := (Subgroup.mem_normalizer_iff.mp hg b).mp hbB
  have hb'L : g * b * g⁻¹ ∉ L := h.noL g
  have hzp : ∀ x : G,
      (x ∈ Subgroup.zpowers (g * b * g⁻¹) ↔ g⁻¹ * x * g ∈ Subgroup.zpowers b) := by
    intro x
    constructor
    · intro hx
      obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp hx
      exact Subgroup.mem_zpowers_iff.mpr ⟨j, by rw [← hj, conj_zpow]; group⟩
    · intro hx
      obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp hx
      exact Subgroup.mem_zpowers_iff.mpr ⟨j, by rw [conj_zpow, hj]; group⟩
  have hmapmem : ∀ x : G, (x ∈ (GGFF.tor (GGFF.zs z)).map (MulAut.conj g).toMonoidHom
      ↔ g⁻¹ * x * g ∈ GGFF.tor (GGFF.zs z)) := by
    intro x
    rw [Subgroup.mem_map]
    constructor
    · rintro ⟨w, hw, hwx⟩
      rw [← hwx]
      simpa [MulEquiv.toMonoidHom_eq_coe, MonoidHom.coe_coe, MulAut.conj_apply, mul_assoc]
        using hw
    · intro h
      exact ⟨g⁻¹ * x * g, h, by
        simp only [MulEquiv.toMonoidHom_eq_coe, MonoidHom.coe_coe, MulAut.conj_apply]
        group⟩
  have hfixP : ∀ x ∈ GGFF.Bt b z,
      P * x * P⁻¹ = x ↔ x ∈ (GGFF.tor (GGFF.zs z)).map (MulAut.conj g).toMonoidHom := by
    intro x hx
    have hgx : g⁻¹ * x * g ∈ GGFF.Bt b z := by
      simpa using (Subgroup.mem_normalizer_iff.mp ((nB b z).inv_mem hg) x).mp hx
    have e : P * x * P⁻¹ = g * (t * (g⁻¹ * x * g) * t⁻¹) * g⁻¹ := by
      rw [hPdef]; group
    rw [e]
    constructor
    · intro hh
      have h2 : t * (g⁻¹ * x * g) * t⁻¹ = g⁻¹ * x * g := by
        have hcong := congrArg (fun z => g⁻¹ * z * g) hh
        simpa [mul_assoc] using hcong
      exact (hmapmem x).mpr ((conj_inv_b_fix_tor hS htb htz hgx).mp h2)
    · intro hx'
      have h2 : t * (g⁻¹ * x * g) * t⁻¹ = g⁻¹ * x * g :=
        (conj_inv_b_fix_tor hS htb htz hgx).mpr ((hmapmem x).mp hx')
      rw [h2]; group
  have hinvP : ∀ x ∈ GGFF.Bt b z,
      P * x * P⁻¹ = x⁻¹ ↔ x ∈ Subgroup.zpowers (g * b * g⁻¹) := by
    intro x hx
    have hgx : g⁻¹ * x * g ∈ GGFF.Bt b z := by
      simpa using (Subgroup.mem_normalizer_iff.mp ((nB b z).inv_mem hg) x).mp hx
    have e : P * x * P⁻¹ = g * (t * (g⁻¹ * x * g) * t⁻¹) * g⁻¹ := by
      rw [hPdef]; group
    rw [e]
    constructor
    · intro hh
      have h2 : t * (g⁻¹ * x * g) * t⁻¹ = (g⁻¹ * x * g)⁻¹ := by
        have hcong := congrArg (fun z => g⁻¹ * z * g) hh
        simpa [mul_assoc] using hcong
      exact (hzp x).mpr ((conj_inv_b_inv_zpowers hS htb htz hgx).mp h2)
    · intro hx'
      have h2 : t * (g⁻¹ * x * g) * t⁻¹ = (g⁻¹ * x * g)⁻¹ :=
        (conj_inv_b_inv_zpowers hS htb htz hgx).mpr ((hzp x).mp hx')
      rw [h2]; group
  have hconj : ∀ x ∈ GGFF.Bt b z,
      P * (t * x * t⁻¹) * P⁻¹ = t * (P * x * P⁻¹) * t⁻¹ := by
    intro x hx
    have hxP : P * x * P⁻¹ ∈ GGFF.Bt b z := (Subgroup.mem_normalizer_iff.mp hPN x).mp hx
    have htwB : t * (P * x * P⁻¹) * t⁻¹ ∈ GGFF.Bt b z :=
      (Subgroup.mem_normalizer_iff.mp htN _).mp hxP
    have hcw : (t * (P * x * P⁻¹) * t⁻¹) * (P * t * P⁻¹ * t⁻¹)
        = (P * t * P⁻¹ * t⁻¹) * (t * (P * x * P⁻¹) * t⁻¹) :=
      (Subgroup.mem_centralizer_iff.mp hcomm) _ htwB
    have hct : P * t * P⁻¹ = (P * t * P⁻¹ * t⁻¹) * t := by group
    have hct' : P * t⁻¹ * P⁻¹ = t⁻¹ * (P * t * P⁻¹ * t⁻¹)⁻¹ := by group
    calc P * (t * x * t⁻¹) * P⁻¹
        = (P * t * P⁻¹) * (P * x * P⁻¹) * (P * t⁻¹ * P⁻¹) := by group
      _ = (P * t * P⁻¹ * t⁻¹) * (t * (P * x * P⁻¹) * t⁻¹)
            * (P * t * P⁻¹ * t⁻¹)⁻¹ := by rw [hct, hct']; group
      _ = t * (P * x * P⁻¹) * t⁻¹ := by rw [← hcw, mul_assoc, mul_inv_cancel, mul_one]
  have hInvb' : P * (g * b * g⁻¹) * P⁻¹ = (g * b * g⁻¹)⁻¹ := by
    rw [hPdef]
    calc g * t * g⁻¹ * (g * b * g⁻¹) * (g * t * g⁻¹)⁻¹
        = g * (t * b * t⁻¹) * g⁻¹ := by group
      _ = g * b⁻¹ * g⁻¹ := by rw [htb]
      _ = (g * b * g⁻¹)⁻¹ := by group
  have hσb'B : t * (g * b * g⁻¹) * t⁻¹ ∈ GGFF.Bt b z :=
    (Subgroup.mem_normalizer_iff.mp htN _).mp hb'B
  have hσb'Inv : P * (t * (g * b * g⁻¹) * t⁻¹) * P⁻¹ = (t * (g * b * g⁻¹) * t⁻¹)⁻¹ := by
    rw [hconj _ hb'B, hInvb']; group
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp ((hinvP _ hσb'B).mp hσb'Inv)
  obtain ⟨i, v, hbv⟩ := hS.mem_Bt.mp hb'B
  have hyB₁ : vecElt (GGFF.zs z) v ∈ GGFF.tor (GGFF.zs z) := GGFF.vecElt_mem_tor _ v
  have hy3 : (vecElt (GGFF.zs z) v) ^ 3 = 1 :=
    (GGFF.isElemAbelian_tor hS.zs_pow hS.zs_comm).2 _ hyB₁
  have hy3z : (vecElt (GGFF.zs z) v) ^ (3 : ℤ) = 1 := by rw [zpow_ofNat]; exact hy3
  have htw : t * vecElt (GGFF.zs z) v * t⁻¹ = vecElt (GGFF.zs z) v :=
    conj_vecElt_of_conj_eq htz v
  have htx : t * (b ^ i * vecElt (GGFF.zs z) v) * t⁻¹ = b ^ (-i) * vecElt (GGFF.zs z) v := by
    calc t * (b ^ i * vecElt (GGFF.zs z) v) * t⁻¹
        = (t * b ^ i * t⁻¹) * (t * vecElt (GGFF.zs z) v * t⁻¹) := by group
      _ = b ^ (-i) * vecElt (GGFF.zs z) v := by
          rw [show t * b ^ i * t⁻¹ = b ^ (-i) by rw [← conj_zpow, htb, inv_zpow, zpow_neg], htw]
  have hLHS : t * (g * b * g⁻¹) * t⁻¹ = b ^ (-i) * vecElt (GGFF.zs z) v := by
    rw [hbv, htx]
  have hRHS : (g * b * g⁻¹) ^ k = b ^ (i * k) * (vecElt (GGFF.zs z) v) ^ k := by
    rw [hbv, ((commute_iff_eq _ _).mpr (commute_zpow_vecElt hS i v)).mul_zpow, zpow_mul]
  have heq : b ^ (i * k) * (vecElt (GGFF.zs z) v) ^ k
      = b ^ (-i) * vecElt (GGFF.zs z) v := by
    rw [← hRHS, hk, hLHS]
  have huniq := mul_eq_mul_iff hS (y := (vecElt (GGFF.zs z) v) ^ k)
    (y' := vecElt (GGFF.zs z) v)
    ((GGFF.tor (GGFF.zs z)).zpow_mem hyB₁ k) hyB₁ heq
  have hbik : b ^ (i * k) = b ^ (-i) := huniq.1
  have hyk : (vecElt (GGFF.zs z) v) ^ k = vecElt (GGFF.zs z) v := huniq.2
  have hbi_ne : b ^ i ≠ 1 := by
    intro h1
    exact hb'L (by rw [hbv, h1, one_mul]; exact GGFF.SettingCore.tor_le z hyB₁)
  have h3dvd : (3 : ℤ) ∣ i * (1 + k) := by
    have hb1 : b ^ (i * (1 + k)) = 1 := by
      rw [show i * (1 + k) = i + i * k by ring, zpow_add, hbik, ← zpow_add, add_neg_cancel,
        zpow_zero]
    rwa [← orderOf_dvd_iff_zpow_eq_one, hS.ord] at hb1
  have h3ndvd : ¬ (3 : ℤ) ∣ i := by
    intro hd
    apply hbi_ne
    rw [← orderOf_dvd_iff_zpow_eq_one, hS.ord]
    exact hd
  have h3dvd2 : (3 : ℤ) ∣ (1 + k) :=
    (Int.prime_three.dvd_or_dvd h3dvd).resolve_left h3ndvd
  obtain ⟨m, hm⟩ := h3dvd2
  have hyk_inv : (vecElt (GGFF.zs z) v) ^ k = (vecElt (GGFF.zs z) v)⁻¹ := by
    have hk' : k = 3 * m - 1 := by linarith
    rw [hk', show 3 * m - 1 = 3 * m + (-1) by ring, zpow_add, zpow_mul, hy3z, one_zpow,
      one_mul, zpow_neg_one]
  have hy_eq : vecElt (GGFF.zs z) v = (vecElt (GGFF.zs z) v)⁻¹ := by
    rw [← hyk_inv, hyk]
  have hy2 : (vecElt (GGFF.zs z) v) ^ 2 = 1 := by
    have h := mul_inv_cancel (vecElt (GGFF.zs z) v)
    rw [← hy_eq] at h
    rwa [pow_two]
  have hy1 : vecElt (GGFF.zs z) v = 1 := eq_one_of_sq_eq_one_of_cube_eq_one hy2 hy3
  have hb'eq : g * b * g⁻¹ = b ^ i := by rw [hbv, hy1, mul_one]
  have hb'ord : orderOf (g * b * g⁻¹) = 3 := by
    have hdvd : orderOf (g * b * g⁻¹) ∣ 3 := by
      rw [orderOf_dvd_iff_pow_eq_one, hb'eq]
      rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hb3, one_zpow]
    rcases Nat.prime_three.eq_one_or_self_of_dvd (orderOf (g * b * g⁻¹)) hdvd with h1 | h3
    · exact absurd (show g * b * g⁻¹ ∈ L from by
        rw [orderOf_eq_one_iff.mp h1]; exact L.one_mem) hb'L
    · exact h3
  have hle : Subgroup.zpowers (g * b * g⁻¹) ≤ Subgroup.zpowers b :=
    Subgroup.zpowers_le.mpr (by rw [hb'eq]; exact Subgroup.zpow_mem_zpowers b i)
  have hcardle : Nat.card (Subgroup.zpowers b) ≤ Nat.card (Subgroup.zpowers (g * b * g⁻¹)) := by
    rw [Nat.card_zpowers, Nat.card_zpowers, hb'ord, hS.ord]
  have heqzp : Subgroup.zpowers (g * b * g⁻¹) = Subgroup.zpowers b :=
    Subgroup.eq_of_le_of_card_ge hle hcardle
  have hPb : P * b * P⁻¹ = b⁻¹ :=
    (hinvP b hbB).mpr (heqzp.symm ▸ Subgroup.mem_zpowers b)
  have hFix_le : ∀ x ∈ GGFF.Bt b z, P * x * P⁻¹ = x → x ∈ GGFF.tor (GGFF.zs z) := by
    intro x hx hxfix
    obtain ⟨j, w, hxw⟩ := hS.mem_Bt.mp hx
    have hwB₁ : vecElt (GGFF.zs z) w ∈ GGFF.tor (GGFF.zs z) := GGFF.vecElt_mem_tor _ w
    have htw : t * vecElt (GGFF.zs z) w * t⁻¹ = vecElt (GGFF.zs z) w :=
      conj_vecElt_of_conj_eq htz w
    have htx : t * x * t⁻¹ = b ^ (-j) * vecElt (GGFF.zs z) w := by
      rw [hxw]
      calc t * (b ^ j * vecElt (GGFF.zs z) w) * t⁻¹
          = (t * b ^ j * t⁻¹) * (t * vecElt (GGFF.zs z) w * t⁻¹) := by group
        _ = b ^ (-j) * vecElt (GGFF.zs z) w := by
            rw [show t * b ^ j * t⁻¹ = b ^ (-j) by rw [← conj_zpow, htb, inv_zpow, zpow_neg],
              htw]
    have htxFix : P * (t * x * t⁻¹) * P⁻¹ = t * x * t⁻¹ := by
      rw [hconj x hx, hxfix]
    have hxx : x * (t * x * t⁻¹)⁻¹ = b ^ (2 * j) := by
      rw [htx, hxw, show (2 : ℤ) * j = j + j by ring, zpow_add]
      rw [mul_inv_rev, show (b ^ (-j))⁻¹ = b ^ j by rw [zpow_neg, inv_inv]]
      group
    have hb2jB : b ^ (2 * j) ∈ GGFF.Bt b z := (GGFF.Bt b z).zpow_mem hbB (2 * j)
    have hb2jFix : P * b ^ (2 * j) * P⁻¹ = b ^ (2 * j) := by
      rw [← hxx]
      calc P * (x * (t * x * t⁻¹)⁻¹) * P⁻¹
          = (P * x * P⁻¹) * (P * (t * x * t⁻¹) * P⁻¹)⁻¹ := by group
        _ = x * (t * x * t⁻¹)⁻¹ := by rw [hxfix, htxFix]
    have hb2jInv : P * b ^ (2 * j) * P⁻¹ = (b ^ (2 * j))⁻¹ :=
      (hinvP _ hb2jB).mpr (heqzp.symm ▸ Subgroup.zpow_mem_zpowers b (2 * j))
    have hb2j_eq : b ^ (2 * j) = (b ^ (2 * j))⁻¹ := hb2jFix.symm.trans hb2jInv
    have hb2j2 : (b ^ (2 * j)) ^ 2 = 1 := by
      rw [pow_two]; nth_rewrite 1 [hb2j_eq]; exact inv_mul_cancel _
    have hb2j3 : (b ^ (2 * j)) ^ 3 = 1 := by
      rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hb3, one_zpow]
    have hb2j1 : b ^ (2 * j) = 1 := eq_one_of_sq_eq_one_of_cube_eq_one hb2j2 hb2j3
    have hbj2 : (b ^ j) ^ 2 = 1 := by
      rw [pow_two, ← zpow_add, show j + j = 2 * j by ring, hb2j1]
    have hbj3 : (b ^ j) ^ 3 = 1 := by
      rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hb3, one_zpow]
    have hbj1 : b ^ j = 1 := eq_one_of_sq_eq_one_of_cube_eq_one hbj2 hbj3
    rw [show x = vecElt (GGFF.zs z) w by rw [hxw, hbj1, one_mul]]
    exact hwB₁
  have hKle : (GGFF.tor (GGFF.zs z)).map (MulAut.conj g).toMonoidHom
      ≤ GGFF.tor (GGFF.zs z) := by
    intro x hx
    rw [Subgroup.mem_map] at hx
    obtain ⟨w, hw, hwx⟩ := hx
    rw [← hwx]
    simp only [MulEquiv.toMonoidHom_eq_coe, MonoidHom.coe_coe, MulAut.conj_apply]
    apply hFix_le
    · exact (Subgroup.mem_normalizer_iff.mp hg w).mp (GGFF.SettingCore.tor_le_Bt b z hw)
    · obtain ⟨v, rfl⟩ := hS.mem_torG.mp hw
      rw [show P * (g * vecElt (GGFF.zs z) v * g⁻¹) * P⁻¹
          = g * (t * vecElt (GGFF.zs z) v * t⁻¹) * g⁻¹ by rw [hPdef]; group,
        conj_vecElt_of_conj_eq htz v]
  have hKcard : Nat.card ((GGFF.tor (GGFF.zs z)).map (MulAut.conj g).toMonoidHom)
      = Nat.card (GGFF.tor (GGFF.zs z)) :=
    Subgroup.card_map_of_injective (MulAut.conj g).injective
  have hKeq : (GGFF.tor (GGFF.zs z)).map (MulAut.conj g).toMonoidHom
      = GGFF.tor (GGFF.zs z) :=
    Subgroup.eq_of_le_of_card_ge hKle (by rw [hKcard])
  have hPy : ∀ y ∈ GGFF.tor (GGFF.zs z), P * y * P⁻¹ = y := by
    intro y hy
    exact (hfixP y (GGFF.SettingCore.tor_le_Bt b z hy)).mpr (hKeq.symm ▸ hy)
  have hPt : ∀ y ∈ GGFF.Bt b z, P * y * P⁻¹ = t * y * t⁻¹ := by
    intro y hy
    obtain ⟨j, w, hyw⟩ := hS.mem_Bt.mp hy
    rw [hyw]
    have htw : t * vecElt (GGFF.zs z) w * t⁻¹ = vecElt (GGFF.zs z) w :=
      conj_vecElt_of_conj_eq htz w
    calc P * (b ^ j * vecElt (GGFF.zs z) w) * P⁻¹
        = (P * b ^ j * P⁻¹) * (P * vecElt (GGFF.zs z) w * P⁻¹) := by group
      _ = b ^ (-j) * vecElt (GGFF.zs z) w := by
          rw [show P * b ^ j * P⁻¹ = b ^ (-j) by rw [← conj_zpow, hPb, inv_zpow, zpow_neg],
            hPy _ (GGFF.vecElt_mem_tor _ w)]
      _ = (t * b ^ j * t⁻¹) * (t * vecElt (GGFF.zs z) w * t⁻¹) := by
          rw [show t * b ^ j * t⁻¹ = b ^ (-j) by rw [← conj_zpow, htb, inv_zpow, zpow_neg],
            htw]
      _ = t * (b ^ j * vecElt (GGFF.zs z) w) * t⁻¹ := by group
  have hfinal : P * t⁻¹ ∈ cB b z := by
    refine Subgroup.mem_centralizer_iff.mpr fun x hx => ?_
    have hxt : t⁻¹ * x * t ∈ GGFF.Bt b z := by
      simpa using (Subgroup.mem_normalizer_iff.mp ((nB b z).inv_mem htN) x).mp hx
    have h1 : P * (t⁻¹ * x * t) * P⁻¹ = t * (t⁻¹ * x * t) * t⁻¹ := hPt _ hxt
    have h2 : (P * t⁻¹) * x * (P * t⁻¹)⁻¹ = x := by
      rw [show (P * t⁻¹) * x * (P * t⁻¹)⁻¹ = P * (t⁻¹ * x * t) * P⁻¹ by group, h1]
      group
    have h3 : (P * t⁻¹) * x = x * (P * t⁻¹) := by
      have hcong := congrArg (fun z => z * (P * t⁻¹)) h2
      simpa [mul_assoc] using hcong
    exact h3.symm
  exact hfinal

end CFSG.StandardType.FF81.PropOne

end
