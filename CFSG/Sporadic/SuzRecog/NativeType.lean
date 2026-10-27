module

public import CFSG.Sporadic.SuzRecog.Defs
public import CFSG.LocalAnalysis.ComponentClassification.AS81Sec3B0Model
public import CFSG.LargeExtraspecial.BridgeSetting
public import CFSG.LargeExtraspecial.S2Basic
public import CFSG.LargeExtraspecial.S3Asch
public import CFSG.Monster.GMS.F1Basic
public import CFSG.Monster.GMS.NotConj
public import CFSG.Sporadic.Co2Smith.Defs

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.Sporadic.SuzRecog

open Subgroup CFSG.Open CFSG.ComponentClassification.AS81 CFSG.ComponentClassification.AS81.SuzB0
  CFSG.ComponentClassification.AS81.Sec2Omega CFSG.Sporadic.SuzOddCore CFSG.Sporadic.Co1Patterson

theorem bilM_bitVec : ∀ v < 64, ∀ w < 64,
    bilM (bitVec v) (bitVec w) = ((gammaBit v w + gammaBit w v) % 2 : ℕ) := by
  intro v hv w hw
  rw [bilM, QuadraticMap.polar, qMinusForm_apply, qMinusForm_apply, qMinusForm_apply,
    ← bitVec_xor, qMinus_bitVec _ (xor_lt hv hw), qMinus_bitVec v hv, qMinus_bitVec w hw]
  revert v
  revert w
  decide

local notation "ψ" => Coord.psi (t := suzInv 1) (q := qVec)

section Six


@[expose] noncomputable def phi0 : ↥(invE 1) →* Lm :=
  rho1.codRestrict Lm fun c => by
    rw [Lm, ← range_rho1]
    exact ⟨c, rfl⟩

theorem coe_phi0 (c : ↥(invE 1)) : (phi0 c : (Fin 6 → ZMod 2) ≃ₗ[ZMod 2] (Fin 6 → ZMod 2)) =
    rho1 c := rfl

theorem phi0_surjective : Function.Surjective phi0 := by
  rintro ⟨l, hl⟩
  rw [Lm, ← range_rho1] at hl
  obtain ⟨c, rfl⟩ := hl
  exact ⟨c, rfl⟩

theorem psi_conj (c : ↥(invE 1)) {a : Equiv.Perm (Fin 1782)} (ha : a ∈ coord_qVec.Q) :
    ψ ((c : Equiv.Perm (Fin 1782)) * a * (c : Equiv.Perm (Fin 1782))⁻¹) = rho1 c (ψ a) :=
  (coord_qVec.rho_psi invE_le c ha).symm

theorem comm_t1 (c : ↥(invE 1)) : (c : Equiv.Perm (Fin 1782)) * suzInv 1 =
    suzInv 1 * (c : Equiv.Perm (Fin 1782)) :=
  mem_centralizer_singleton_iff.mp (invE_le_centM (by norm_num) c.2).1

end Six

theorem mem_zpowers_t1_iff
    {a : Equiv.Perm (Fin 1782)} : a ∈ zpowers (suzInv 1) ↔ a = 1 ∨ a = suzInv 1 :=
  CFSG.Monster.GMS.mem_zpowers_iff_of_orderOf_two (orderOf_suzInv (by norm_num))


theorem phi0_eq_one_iff (c : ↥(invE 1)) :
    phi0 c = 1 ↔ (c : Equiv.Perm (Fin 1782)) ∈ coord_qVec.Q := by
  rw [← mem_subgroupOf, ← ker_rho1, MonoidHom.mem_ker, ← Subtype.coe_inj]
  rfl

@[expose] noncomputable def t1C : ↥(invE 1) := ⟨suzInv 1, suzInv_mem_invE⟩

@[expose] noncomputable def nativeType : SuzType ↥(invE 1) where
  φ := phi0
  φ_surj := phi0_surjective
  z := t1C
  vec c := ψ (c : Equiv.Perm (Fin 1782))
  z_mul_self := Subtype.ext (suzInv_sq (by norm_num))
  z_ne_one h := suzInv_ne_one (i := 1) (by norm_num) (congrArg Subtype.val h)
  z_comm c := Subtype.ext (comm_t1 c)
  φ_z := (phi0_eq_one_iff _).2 coord_qVec.t_mem
  vec_mul p q hp hq := coord_qVec.psi_mul ((phi0_eq_one_iff p).1 hp) ((phi0_eq_one_iff q).1 hq)
  vec_eq_zero q hq := by
    rw [coord_qVec.psi_eq_zero_iff ((phi0_eq_one_iff q).1 hq), mem_zpowers_t1_iff,
      Subtype.ext_iff, Subtype.ext_iff]
    rfl
  vec_conj c q hq := psi_conj c ((phi0_eq_one_iff q).1 hq)
  vec_surj w := by
    obtain ⟨x, hx, rfl⟩ := coord_qVec.psi_surj w
    exact ⟨⟨x, Q_le_invE hx⟩, (phi0_eq_one_iff _).2 hx, rfl⟩
  mul_self_eq_one_iff q hq := by
    rw [Subtype.ext_iff]
    exact coord_qVec.mul_self_eq_one_iff ((phi0_eq_one_iff q).1 hq)
  mul_self_eq_z_iff q hq := by
    obtain ⟨v, hv, a, ha, he⟩ := coord_qVec.mem_Q_iff.mp ((phi0_eq_one_iff q).1 hq)
    rw [Subtype.ext_iff]
    change (q : Equiv.Perm (Fin 1782)) * q = suzInv 1 ↔ _
    rw [he, coord_qVec.mul_self_eq hv, coord_qVec.psi_eq hv ha, qMinus_bitVec v hv]
    have hq := qMinusBit_lt v
    interval_cases qMinusBit v
    · simp only [pow_zero, Nat.cast_zero, zero_ne_one, iff_false]
      exact fun h => suzInv_ne_one (i := 1) (by norm_num) h.symm
    · simp
  comm_eq_one_iff p q hp hq := by
    obtain ⟨v, hv, a, ha, hpe⟩ := coord_qVec.mem_Q_iff.mp ((phi0_eq_one_iff p).1 hp)
    obtain ⟨w, hw, b, hb, hqe⟩ := coord_qVec.mem_Q_iff.mp ((phi0_eq_one_iff q).1 hq)
    rw [Subtype.ext_iff]
    change (p : Equiv.Perm (Fin 1782)) * q * (p : Equiv.Perm (Fin 1782))⁻¹ *
      (q : Equiv.Perm (Fin 1782))⁻¹ = 1 ↔ _
    rw [hpe, hqe, coord_qVec.commutator_eq hv hw, coord_qVec.psi_eq hv ha,
      coord_qVec.psi_eq hw hb, bilM_bitVec v hv w hw]
    have hg : (gammaBit v w + gammaBit w v) % 2 < 2 := Nat.mod_lt _ (by norm_num)
    interval_cases (gammaBit v w + gammaBit w v) % 2
    · simp
    · simp only [pow_one, Nat.cast_one, one_ne_zero, iff_false]
      exact suzInv_ne_one (i := 1) (by norm_num)
  comm_eq_z_iff p q hp hq := by
    obtain ⟨v, hv, a, ha, hpe⟩ := coord_qVec.mem_Q_iff.mp ((phi0_eq_one_iff p).1 hp)
    obtain ⟨w, hw, b, hb, hqe⟩ := coord_qVec.mem_Q_iff.mp ((phi0_eq_one_iff q).1 hq)
    rw [Subtype.ext_iff]
    change (p : Equiv.Perm (Fin 1782)) * q * (p : Equiv.Perm (Fin 1782))⁻¹ *
      (q : Equiv.Perm (Fin 1782))⁻¹ = suzInv 1 ↔ _
    rw [hpe, hqe, coord_qVec.commutator_eq hv hw, coord_qVec.psi_eq hv ha,
      coord_qVec.psi_eq hw hb, bilM_bitVec v hv w hw]
    have hg : (gammaBit v w + gammaBit w v) % 2 < 2 := Nat.mod_lt _ (by norm_num)
    interval_cases (gammaBit v w + gammaBit w v) % 2
    · simp only [pow_zero, Nat.cast_zero, zero_ne_one, iff_false]
      exact fun h => suzInv_ne_one (i := 1) (by norm_num) h.symm
    · simp
  center_eq q hq hcomm := by
    have hqQ := (phi0_eq_one_iff q).1 hq
    have h := (coord_qVec.forall_comm_iff hqQ).1 fun y hy =>
      congrArg Subtype.val (hcomm ⟨y, Q_le_invE hy⟩ ((phi0_eq_one_iff _).2 hy)).symm
    rw [mem_zpowers_t1_iff] at h
    rw [Subtype.ext_iff, Subtype.ext_iff]
    exact h

theorem nativeType_φ : nativeType.φ = phi0 := rfl

theorem nativeType_z : nativeType.z = t1C := rfl

theorem nativeType_vec (c : ↥(invE 1)) : nativeType.vec c = ψ (c : Equiv.Perm (Fin 1782)) := rfl

end CFSG.Sporadic.SuzRecog
