module

public import CFSG.Quasithin.EmptyFaithful.S143IA
public import CFSG.Quasithin.EmptyFaithful.S143ID

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique
open CFSG.QuasithinUnique.Lin2

namespace S143

section CaseA

variable {G : Type} [Group G] [Finite G] {T M : Subgroup G} {g : G} (c : Counter T M g)

include c

theorem Counter.iTwo_le_normalizer_VZ : iTwo T M ≤ Subgroup.normalizer (VZ T M : Set G) := by
  rw [c.h1281.normalizer_VZ]
  exact c.iTwo_le_M

variable {r : G} (hrW : r ∈ Hyp1281Two.wOfU T M) (hrV : r ∉ VZ T M) (hr2 : r * r = 1)

include hrW hrV hr2

theorem Counter.exists_order_three_commute (c18a : Concl18a T M g) {t₀ s : G} (htT : t₀ ∈ T)
    (htRQ : t₀ ∉ rOf T M ⊔ qOf T) (hsT : s ∈ T) (hsRQ : s ∉ rOf T M ⊔ qOf T) (hs2 : s * s = 1)
    (hA : ∀ v ∈ VZ T M, s * v = v * s) :
    ∃ x ∈ iTwo T M, orderOf x = 3 ∧ x * s = s * x := by
  have h := c.h1281
  have hs := c.swapData_of_involution hrW hrV hr2 htT htRQ hsT hsRQ hs2 c18a.rq_index
  have hcard : Nat.card (c.Ac hrW hrV hr2) = Nat.card (VZ T M) * Nat.card (VZ T M) := by
    rw [c.card_Ac hrW hrV hr2, h.rank_two]
  have hsN : s ∈ Subgroup.normalizer (iTwo T M : Set G) := c.T_mem_normalizer_iTwo hsT
  have hI2V : ∀ i ∈ iTwo T M, ∀ v ∈ VZ T M, i * v * i⁻¹ ∈ VZ T M := fun i hi v hv =>
    (Subgroup.mem_normalizer_iff.mp (c.iTwo_le_normalizer_VZ hi) v).mp hv
  have hRI : rOf T M ≤ iTwo T M := pCoreOf_le 2 (iTwo T M)
  have hAinv : ∀ v ∈ VZ T M, s⁻¹ * v = v * s⁻¹ := by
    intro v hv
    have h1 := hA v hv
    calc s⁻¹ * v = s⁻¹ * (v * s) * s⁻¹ := by group
      _ = s⁻¹ * (s * v) * s⁻¹ := by rw [h1]
      _ = v * s⁻¹ := by group
  have hfrat : ∀ i ∈ iTwo T M, ∃ ρ ∈ rOf T M, ∃ j ∈ iTwo T M, j * s = s * j ∧ i = ρ * j := by
    intro i hi
    have hs'2 : (i * s * i⁻¹) * (i * s * i⁻¹) = 1 := by
      calc (i * s * i⁻¹) * (i * s * i⁻¹) = i * (s * s) * i⁻¹ := by group
        _ = 1 := by rw [hs2]; group
    have hs'V : ∀ v ∈ VZ T M, (i * s * i⁻¹) * v = v * (i * s * i⁻¹) := by
      intro v hv
      have hv' : i⁻¹ * v * i ∈ VZ T M := by
        have := hI2V i⁻¹ ((iTwo T M).inv_mem hi) v hv
        simpa using this
      have h1 := hA _ hv'
      calc (i * s * i⁻¹) * v = i * (s * (i⁻¹ * v * i)) * i⁻¹ := by group
        _ = i * ((i⁻¹ * v * i) * s) * i⁻¹ := by rw [h1]
        _ = v * (i * s * i⁻¹) := by group
    have hmemI : s⁻¹ * (i * s * i⁻¹) ∈ iTwo T M := by
      have h1 := (Subgroup.mem_normalizer_iff.mp ((Subgroup.inv_mem _ hsN)) i).mp hi
      have e : s⁻¹ * (i * s * i⁻¹) = (s⁻¹ * i * s⁻¹⁻¹) * i⁻¹ := by group
      rw [e]
      exact (iTwo T M).mul_mem h1 ((iTwo T M).inv_mem hi)
    have hmemC : s⁻¹ * (i * s * i⁻¹) ∈ Subgroup.centralizer (VZ T M : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro v hv
      calc v * (s⁻¹ * (i * s * i⁻¹)) = (v * s⁻¹) * (i * s * i⁻¹) := by group
        _ = (s⁻¹ * v) * (i * s * i⁻¹) := by rw [hAinv v hv]
        _ = s⁻¹ * (v * (i * s * i⁻¹)) := by group
        _ = s⁻¹ * ((i * s * i⁻¹) * v) := by rw [hs'V v hv]
        _ = (s⁻¹ * (i * s * i⁻¹)) * v := by group
    have hmem : s⁻¹ * (i * s * i⁻¹) ∈ rOf T M := by
      rw [← c18a.i2_cent]
      exact ⟨hmemI, hmemC⟩
    obtain ⟨ρ, hρR, hρ⟩ := hs.transitive_of_centralizes hA hcard hmem hs'2
    refine ⟨ρ, hρR, ρ⁻¹ * i, (iTwo T M).mul_mem ((iTwo T M).inv_mem (hRI hρR)) hi, ?_, by group⟩
    calc ρ⁻¹ * i * s = (ρ⁻¹ * (i * s * i⁻¹) * ρ) * (ρ⁻¹ * i) := by group
      _ = (ρ⁻¹ * (ρ * s * ρ⁻¹) * ρ) * (ρ⁻¹ * i) := by rw [hρ]
      _ = s * (ρ⁻¹ * i) := by group
  obtain ⟨e⟩ := c18a.i2_sThree
  have hF3 : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hσ : orderOf (finRotate 3) = 3 := orderOf_eq_prime (by decide) (by decide)
  obtain ⟨i, hi⟩ := QuotientGroup.mk_surjective (e.symm (finRotate 3))
  obtain ⟨ρ, hρ, j, hj, hjs, hij⟩ := hfrat (i : G) i.2
  let j' : ↥(iTwo T M) := ⟨j, hj⟩
  let ρ' : ↥(iTwo T M) := ⟨ρ, hRI hρ⟩
  have hρ'1 : (QuotientGroup.mk ρ' : OTwoQuot (iTwo T M)) = 1 := by
    rw [QuotientGroup.eq_one_iff]
    exact (mem_pCore_iff ρ').mpr hρ
  have hmk : (QuotientGroup.mk j' : OTwoQuot (iTwo T M)) = e.symm (finRotate 3) := by
    rw [← hi]
    have : i = ρ' * j' := Subtype.ext hij
    rw [this, QuotientGroup.mk_mul, hρ'1, one_mul]
  have hord3 : orderOf (QuotientGroup.mk j' : OTwoQuot (iTwo T M)) = 3 := by
    rw [hmk, MulEquiv.orderOf_eq, hσ]
  have hdvd : 3 ∣ orderOf j' := by
    have := orderOf_map_dvd (QuotientGroup.mk' (CFSG.Open.pCore 2 ↥(iTwo T M))) j'
    rw [← hord3]
    exact this
  have hj0 : orderOf j' ≠ 0 := (orderOf_pos j').ne'
  set x' : ↥(iTwo T M) := j' ^ (orderOf j' / 3) with hx'
  have hx'3 : orderOf x' = 3 := orderOf_pow_orderOf_div hj0 hdvd
  refine ⟨(x' : G), x'.2, by rw [Subgroup.orderOf_coe]; exact hx'3, ?_⟩
  have hcomm : Commute j s := hjs
  have : (x' : G) = j ^ (orderOf j' / 3) := rfl
  rw [this]
  exact (hcomm.pow_left _).eq

theorem Counter.conj_mem_qOf_of_commute (c18a : Concl18a T M g) {t₀ s y z : G} (htT : t₀ ∈ T)
    (htRQ : t₀ ∉ rOf T M ⊔ qOf T) (hsT : s ∈ T) (hsRQ : s ∉ rOf T M ⊔ qOf T) (hs2 : s * s = 1)
    (hz : z ∈ quasithinOmegaOneCenter T) (hz1 : z ≠ 1) (hys : y * z * y⁻¹ = s)
    (hA : ∀ v ∈ VZ T M, s * v = v * s) : y⁻¹ * z * y ∈ qOf T := by
  have h := c.h1281
  have hs := c.swapData_of_involution hrW hrV hr2 htT htRQ hsT hsRQ hs2 c18a.rq_index
  obtain ⟨x, hxI, hx3, hxs⟩ := c.exists_order_three_commute hrW hrV hr2 c18a htT htRQ hsT hsRQ hs2 hA
  have hVR : VZ T M ≤ rOf T M := hs.N_le_R
  have hI2V : ∀ i ∈ iTwo T M, ∀ v ∈ VZ T M, i * v * i⁻¹ ∈ VZ T M := fun i hi v hv =>
    (Subgroup.mem_normalizer_iff.mp (c.iTwo_le_normalizer_VZ hi) v).mp hv
  have hVab : ∀ a ∈ VZ T M, ∀ b ∈ VZ T M, a * b = b * a := fun a ha b hb =>
    mul_comm_of_sq_eq_one (fun w hw => c.VZ_sq hw) ha hb
  have hxpow : x * x * x = 1 := by
    have := pow_orderOf_eq_one x
    rwa [hx3, pow_three'] at this
  have hzs : z = y⁻¹ * s * y := by rw [← hys]; group
  have hx'H : y⁻¹ * x * y ∈ mcOf T := by
    apply c.mem_mcOf_of_comm hz hz1
    calc y⁻¹ * x * y * z = y⁻¹ * (x * s) * y := by rw [hzs]; group
      _ = y⁻¹ * (s * x) * y := by rw [hxs]
      _ = z * (y⁻¹ * x * y) := by rw [hzs]; group
  have hx'3 : (y⁻¹ * x * y) ^ 3 = 1 := by
    rw [pow_three']
    calc y⁻¹ * x * y * (y⁻¹ * x * y) * (y⁻¹ * x * y) = y⁻¹ * (x * x * x) * y := by group
      _ = 1 := by rw [hxpow]; group
  have hEmem : ∀ w, w ∈ conjSubgroup (VZ T M) y ↔ y * w * y⁻¹ ∈ VZ T M := fun w =>
    mem_conjSubgroup_iff
  have hEH : conjSubgroup (VZ T M) y ≤ mcOf T := by
    intro w hw
    have hwV : y * w * y⁻¹ ∈ VZ T M := (hEmem w).mp hw
    have hcomm := hA _ hwV
    apply c.mem_mcOf_of_comm hz hz1
    have h1 : y * (w * z) * y⁻¹ = y * (z * w) * y⁻¹ := by
      calc y * (w * z) * y⁻¹ = (y * w * y⁻¹) * (y * z * y⁻¹) := by group
        _ = (y * w * y⁻¹) * s := by rw [hys]
        _ = s * (y * w * y⁻¹) := hcomm.symm
        _ = (y * z * y⁻¹) * (y * w * y⁻¹) := by rw [hys]
        _ = y * (z * w) * y⁻¹ := by group
    exact mul_left_cancel (mul_right_cancel h1)
  have hEab : ∀ a ∈ conjSubgroup (VZ T M) y, ∀ b ∈ conjSubgroup (VZ T M) y, a * b = b * a := by
    intro a ha b hb
    have h1 := hVab _ ((hEmem a).mp ha) _ ((hEmem b).mp hb)
    have h2 : y * (a * b) * y⁻¹ = y * (b * a) * y⁻¹ := by
      calc y * (a * b) * y⁻¹ = (y * a * y⁻¹) * (y * b * y⁻¹) := by group
        _ = (y * b * y⁻¹) * (y * a * y⁻¹) := h1
        _ = y * (b * a) * y⁻¹ := by group
    exact mul_left_cancel (mul_right_cancel h2)
  have hEsq : ∀ a ∈ conjSubgroup (VZ T M) y, a * a = 1 := by
    intro a ha
    have h1 := c.VZ_sq ((hEmem a).mp ha)
    have h2 : y * (a * a) * y⁻¹ = y * 1 * y⁻¹ := by
      calc y * (a * a) * y⁻¹ = (y * a * y⁻¹) * (y * a * y⁻¹) := by group
        _ = 1 := h1
        _ = y * 1 * y⁻¹ := by group
    exact mul_left_cancel (mul_right_cancel h2)
  have hxE : ∀ w ∈ conjSubgroup (VZ T M) y, (y⁻¹ * x * y) * w * (y⁻¹ * x * y)⁻¹ ∈
      conjSubgroup (VZ T M) y := by
    intro w hw
    rw [hEmem]
    have e : y * ((y⁻¹ * x * y) * w * (y⁻¹ * x * y)⁻¹) * y⁻¹ = x * (y * w * y⁻¹) * x⁻¹ := by
      group
    rw [e]
    exact hI2V x hxI _ ((hEmem w).mp hw)
  have hK := c.commutator_mem_qOf_of_cube hx'H hx'3 hEH hEab hEsq hxE
  have hC : ∀ w ∈ VZ T M, x * w * x⁻¹ = w → w = 1 := fun w hw hxw =>
    c18a.r_fpf x hxI hx3 w (hVR hw) hxw
  let φ : ↥(VZ T M) → ↥(VZ T M) := fun v =>
    ⟨x * v * x⁻¹ * v⁻¹, (VZ T M).mul_mem (hI2V x hxI v v.2) ((VZ T M).inv_mem v.2)⟩
  have hφ : Function.Injective φ := by
    intro v₁ v₂ h12
    obtain ⟨a, ha⟩ := v₁
    obtain ⟨b, hb⟩ := v₂
    have h12' : x * a * x⁻¹ * a⁻¹ = x * b * x⁻¹ * b⁻¹ := congrArg Subtype.val h12
    have hb' : x * b * x⁻¹ ∈ VZ T M := hI2V x hxI b hb
    have hcomm1 : (x * b * x⁻¹) * (b⁻¹ * a) = (b⁻¹ * a) * (x * b * x⁻¹) :=
      hVab _ hb' _ ((VZ T M).mul_mem ((VZ T M).inv_mem hb) ha)
    have hw : x * (a * b⁻¹) * x⁻¹ = a * b⁻¹ := by
      have e1 : x * (a * b⁻¹) * x⁻¹ = (x * a * x⁻¹ * a⁻¹) * a * (x * b * x⁻¹)⁻¹ := by group
      rw [e1, h12']
      calc (x * b * x⁻¹ * b⁻¹) * a * (x * b * x⁻¹)⁻¹
          = (x * b * x⁻¹) * (b⁻¹ * a) * (x * b * x⁻¹)⁻¹ := by group
        _ = (b⁻¹ * a) * (x * b * x⁻¹) * (x * b * x⁻¹)⁻¹ := by rw [hcomm1]
        _ = b⁻¹ * a := by group
        _ = a * b⁻¹ := hVab _ ((VZ T M).inv_mem hb) _ ha
    have h0 := hC (a * b⁻¹) ((VZ T M).mul_mem ha ((VZ T M).inv_mem hb)) hw
    exact Subtype.ext (mul_inv_eq_one.mp h0)
  have hzV : z ∈ VZ T M := Hyp1281Two.omegaOneCenter_le_VZ T M hz
  obtain ⟨v, hv⟩ := (Finite.injective_iff_surjective.mp hφ) ⟨z, hzV⟩
  have hv' : x * (v : G) * x⁻¹ * (v : G)⁻¹ = z := congrArg Subtype.val hv
  have hvE : y⁻¹ * (v : G) * y ∈ conjSubgroup (VZ T M) y := by
    rw [hEmem]
    have e : y * (y⁻¹ * (v : G) * y) * y⁻¹ = (v : G) := by group
    rw [e]
    exact v.2
  have h1 := hK _ hvE
  have e : (y⁻¹ * x * y) * (y⁻¹ * (v : G) * y) * (y⁻¹ * x * y)⁻¹ * (y⁻¹ * (v : G) * y)⁻¹ =
      y⁻¹ * (x * (v : G) * x⁻¹ * (v : G)⁻¹) * y := by group
  rw [e, hv'] at h1
  exact h1

end CaseA

end S143

end CFSG.Quasithin
