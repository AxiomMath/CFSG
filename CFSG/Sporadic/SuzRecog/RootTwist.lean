module

public import CFSG.Sporadic.SuzRecog.RootTwistDefs
public import CFSG.Sporadic.SuzRecog.RootTwistCert
public import CFSG.Sporadic.SuzRecog.ModelGroupsKit
public import CFSG.Sporadic.SuzRecog.C1ModelBase

public noncomputable section

namespace CFSG.Sporadic.SuzRecog.RootTwist

open Subgroup CFSG.Sporadic.SuzOddCore CFSG.Sporadic.SuzRecog.Model CFSG.Monster.B.Co2
  CFSG.Monster.B.Co2.Native CFSG.Sporadic.SuzRecog.RootTwistCheck
  CFSG.Sporadic.SuzRecog.RootTwistData CFSG.Sporadic.SuzRecog.LevelTwoData
  CFSG.Sporadic.SuzRecog.ModelGroups

@[expose] def xTw : Equiv.Perm (Fin 1782) := permC 1782 xTwArr

@[expose] def yTw : Equiv.Perm (Fin 1782) := permC 1782 yTwArr

theorem mem_CW_iff {g : Equiv.Perm (Fin 1782)} :
    g ∈ CW ↔ g * suzInv 1 = suzInv 1 * g ∧ g * aPrime = aPrime * g ∧ g ∈ suzM := by
  rw [CW, mem_inf, mem_centralizer_iff]
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff, forall_eq_or_imp, forall_eq]
  constructor
  · rintro ⟨⟨h1, h2⟩, h3⟩
    exact ⟨h1.symm, h2.symm, h3⟩
  · rintro ⟨h1, h2, h3⟩
    exact ⟨⟨h1.symm, h2.symm⟩, h3⟩

theorem permsOK_parts :
    ModelGroupsCheck.permOK rhoArr = true ∧ ModelGroupsCheck.permOK aPrimeArr = true ∧
      ModelGroupsCheck.permOK vRootArr = true ∧ ModelGroupsCheck.permOK vRoot'Arr = true ∧
      ModelGroupsCheck.permOK xTwArr = true ∧ ModelGroupsCheck.permOK yTwArr = true := by
  have h := perms_check
  simp only [permsOK, Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6⟩

theorem rep_rho1 :
    Rep 1782 rhoArr rho1 := (rep_permC permsOK_parts.1).1

theorem rep_aPrime :
    Rep 1782 aPrimeArr aPrime := (rep_permC permsOK_parts.2.1).1

theorem rep_xTw :
    Rep 1782 xTwArr xTw := (rep_permC permsOK_parts.2.2.2.2.1).1

theorem rep_yTw :
    Rep 1782 yTwArr yTw := (rep_permC permsOK_parts.2.2.2.2.2).1

theorem sq_facts : rho1 ^ 3 = 1 ∧ (xTw * yTw) ^ 2 = 1 ∧
    (xTw * (rho1 * yTw * rho1⁻¹)) ^ 2 ≠ 1 ∧ (xTw * (rho1 ^ 2 * yTw * (rho1 ^ 2)⁻¹)) ^ 2 ≠ 1 := by
  have h := sq_check
  simp only [sqOK, Bool.and_eq_true, Bool.not_eq_true'] at h
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h
  refine ⟨eq_of_eqA (rep_powA rep_rho1 3) rep_idA h1,
    eq_of_eqA (rep_powA (rep_compA rep_xTw rep_yTw) 2) rep_idA h2, fun e => ?_, fun e => ?_⟩
  · rw [(eqA_iff (rep_powA (rep_compA rep_xTw (rep_conjA rep_rho1 rep_yTw)) 2) rep_idA).2 e]
      at h3
    exact Bool.noConfusion h3
  · rw [(eqA_iff (rep_powA (rep_compA rep_xTw (rep_conjA (rep_powA rep_rho1 2) rep_yTw)) 2)
      rep_idA).2 e] at h4
    exact Bool.noConfusion h4

theorem rho1_pow_three : rho1 ^ 3 = 1 := sq_facts.1

theorem sq_xTw_mul_yTw : (xTw * yTw) ^ 2 = 1 := sq_facts.2.1

theorem sq_xTw_mul_conj_ne {k : ℤ} (hk : ¬ (3 : ℤ) ∣ k) :
    (xTw * (rho1 ^ k * yTw * (rho1 ^ k)⁻¹)) ^ 2 ≠ 1 := by
  have hk' : rho1 ^ k = rho1 ^ (k % (3 : ℕ)) := zpow_eq_zpow_emod' k rho1_pow_three
  have hmod : k % ((3 : ℕ) : ℤ) = 1 ∨ k % ((3 : ℕ) : ℤ) = 2 := by omega
  rw [hk']
  rcases hmod with h | h
  · rw [h, zpow_one]
    exact sq_facts.2.2.1
  · rw [h, show rho1 ^ (2 : ℤ) = rho1 ^ (2 : ℕ) from zpow_natCast rho1 2]
    exact sq_facts.2.2.2

theorem rep_t1 : Rep 1782 ModelGroupsCheck.t1A (suzInv 1) :=
  rep_suzInv (by norm_num)

theorem comm_facts :
    rho1 * suzInv 1 = suzInv 1 * rho1 ∧ rho1 * aPrime = aPrime * rho1 ∧
    xTw * suzInv 1 = suzInv 1 * xTw ∧ xTw * aPrime = aPrime * xTw ∧
    yTw * suzInv 1 = suzInv 1 * yTw ∧ yTw * aPrime = aPrime * yTw := by
  have h := comm_check
  simp only [commOK, Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩ := h
  exact ⟨(commA_iff rep_rho1 rep_t1).1 h1, (commA_iff rep_rho1 rep_aPrime).1 h2,
    (commA_iff rep_xTw rep_t1).1 h3, (commA_iff rep_xTw rep_aPrime).1 h4,
    (commA_iff rep_yTw rep_t1).1 h5, (commA_iff rep_yTw rep_aPrime).1 h6⟩

theorem membersOK_parts :
    inM rhoArr = true ∧ inM xTwArr = true ∧ inM yTwArr = true := by
  have h := members_check
  simp only [membersOK, Bool.and_eq_true] at h
  exact ⟨h.1.1, h.1.2, h.2⟩

theorem rho1_mem_CW :
    rho1 ∈ CW :=
  mem_CW_iff.2 ⟨comm_facts.1, comm_facts.2.1, (inM_iff rep_rho1).1 membersOK_parts.1⟩

theorem xTw_mem_CW :
    xTw ∈ CW :=
  mem_CW_iff.2 ⟨comm_facts.2.2.1, comm_facts.2.2.2.1, (inM_iff rep_xTw).1 membersOK_parts.2.1⟩

theorem yTw_mem_CW :
    yTw ∈ CW :=
  mem_CW_iff.2 ⟨comm_facts.2.2.2.2.1, comm_facts.2.2.2.2.2,
    (inM_iff rep_yTw).1 membersOK_parts.2.2⟩

theorem inV_iff {v v₁ z : Array ℕ} {V V₁ Z : Equiv.Perm (Fin 1782)} (hv : Rep 1782 v V)
    (hv₁ : Rep 1782 v₁ V₁) (hz : Rep 1782 z Z) :
    inV v v₁ z = true ↔ Z = V ∨ Z = V₁ ∨ Z = V * V₁ := by
  rw [inV, Bool.or_eq_true, Bool.or_eq_true, eqA_iff hz hv, eqA_iff hz hv₁,
    eqA_iff hz (rep_compA hv hv₁), or_assoc]

theorem mem_normalizer_of_normV {v g : Array ℕ}
    {Vp G : Equiv.Perm (Fin 1782)} (hv : Rep 1782 v Vp) (hg : Rep 1782 g G)
    (h : normV v (ModelGroupsCheck.conjA rhoArr v) g = true) :
    G ∈ normalizer ((closure {Vp, rho1 * Vp * rho1⁻¹} : Subgroup (Equiv.Perm (Fin 1782))) :
      Set (Equiv.Perm (Fin 1782))) := by
  have hv₁ := rep_conjA rep_rho1 hv
  simp only [normV, Bool.and_eq_true] at h
  have hw : ∀ Z : Equiv.Perm (Fin 1782), (Z = Vp ∨ Z = rho1 * Vp * rho1⁻¹ ∨
      Z = Vp * (rho1 * Vp * rho1⁻¹)) → Z ∈ closure {Vp, rho1 * Vp * rho1⁻¹} := by
    rintro Z (rfl | rfl | rfl)
    · exact subset_closure (Set.mem_insert _ _)
    · exact subset_closure (Set.mem_insert_of_mem _ rfl)
    · exact mul_mem (subset_closure (Set.mem_insert _ _))
        (subset_closure (Set.mem_insert_of_mem _ rfl))
  refine C1Model.mem_normalizer_of_forall_conj_mem fun y hy => conj_mem_closure ?_ hy
  rintro x (rfl | rfl)
  · exact hw _ ((inV_iff hv hv₁ (rep_conjA hg hv)).1 h.1)
  · exact hw _ ((inV_iff hv hv₁ (rep_conjA hg hv₁)).1 h.2)

theorem three_dvd_of_twist_at
    {G : Type*} [Group G] (κ κ' : ↥CW →* G)
    (hκ' : Function.Injective κ') {r : ↥CW} (hr : (r : Equiv.Perm (Fin 1782)) = rho1) {k : ℤ}
    (hx : ∀ h : xTw ∈ CW, κ ⟨xTw, h⟩ = κ' ⟨xTw, h⟩)
    (hy : ∀ h : yTw ∈ CW, κ ⟨yTw, h⟩ = κ' (r ^ k * ⟨yTw, h⟩ * (r ^ k)⁻¹)) : (3 : ℤ) ∣ k := by
  by_contra hk
  let x : ↥CW := ⟨xTw, xTw_mem_CW⟩
  let y : ↥CW := ⟨yTw, yTw_mem_CW⟩
  have e1 : κ (x * y) = κ' (x * (r ^ k * y * (r ^ k)⁻¹)) := by
    rw [map_mul, hx xTw_mem_CW, hy yTw_mem_CW, ← map_mul]
  have hsq : (x * y) ^ 2 = 1 := Subtype.ext (by
    show (xTw * yTw) ^ 2 = 1
    exact sq_xTw_mul_yTw)
  have h1 : κ' ((x * (r ^ k * y * (r ^ k)⁻¹)) ^ 2) = κ' 1 := by
    rw [map_pow, ← e1, ← map_pow, hsq, map_one, map_one]
  have h2 := congrArg Subtype.val (hκ' h1)
  apply sq_xTw_mul_conj_ne hk
  simpa [x, y, hr] using h2

theorem CW_le_invE :
    CW ≤ invE 1 := fun _ hg => by
  obtain ⟨h1, -, h3⟩ := mem_CW_iff.1 hg
  rw [invE_eq_centM (by norm_num : 1 < 4)]
  exact mem_inf.2 ⟨mem_centralizer_singleton_iff.2 h1, h3⟩

end CFSG.Sporadic.SuzRecog.RootTwist
