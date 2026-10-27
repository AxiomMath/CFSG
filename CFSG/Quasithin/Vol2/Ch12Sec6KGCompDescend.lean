module

public import CFSG.Quasithin.Vol2.Ch12Sec6KGCompA
public import CFSG.Permutation.FiveTransitive.CharacteristicAutomorphism
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X3A6Abstract

public section

namespace CFSG.Quasithin.H13.S126C

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique
open CFSG.FiveTransitive.CharacteristicAutomorphism (quotient quotient_apply_mk)

variable {X : Type} [Group X] (N : Subgroup X) [N.Characteristic]

theorem quotient_apply_coe (α : MulAut X) (x : X) :
    quotient N α (x : X ⧸ N) = ((α x : X) : X ⧸ N) :=
  quotient_apply_mk N α x

theorem quotient_conj (c : X) : quotient N (MulAut.conj c) = MulAut.conj (c : X ⧸ N) := by
  refine MulEquiv.ext fun x => ?_
  induction x using QuotientGroup.induction_on with
  | H y =>
    rw [quotient_apply_coe, MulAut.conj_apply, MulAut.conj_apply, QuotientGroup.mk_mul,
      QuotientGroup.mk_mul, QuotientGroup.mk_inv]

variable {N}

theorem quotient_injective [Group.IsPerfect X] (hN : N ≤ Subgroup.center X) :
    Function.Injective (quotient N) := by
  rw [injective_iff_map_eq_one]
  intro τ hτ
  have hc : ∀ s : X, s⁻¹ * τ s ∈ Subgroup.center X := fun s => by
    have h1 := congrArg (fun φ : MulAut (X ⧸ N) => φ (s : X ⧸ N)) hτ
    simp only [quotient_apply_coe, MulAut.one_apply] at h1
    have h2 := inv_mem (QuotientGroup.eq.mp h1)
    rw [mul_inv_rev, inv_inv] at h2
    exact hN h2
  let z : X →* X :=
    { toFun := fun s => s⁻¹ * τ s
      map_one' := by simp
      map_mul' := fun s t => by
        have ht := Subgroup.mem_center_iff.mp (hc s)
        calc (s * t)⁻¹ * τ (s * t) = t⁻¹ * (s⁻¹ * τ s) * τ t := by
              rw [map_mul]
              group
          _ = s⁻¹ * τ s * (t⁻¹ * τ t) := by
              rw [ht t⁻¹]
              group }
  have hcomm : ⁅(⊤ : Subgroup X), (⊤ : Subgroup X)⁆ ≤ z.ker := by
    rw [Subgroup.commutator_le]
    intro a _ b _
    rw [MonoidHom.mem_ker, map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
    exact (Subgroup.mem_center_iff.mp (hc a) (z b)).symm
  have htop : ⁅(⊤ : Subgroup X), (⊤ : Subgroup X)⁆ = ⊤ := Group.IsPerfect.commutator_eq_top
  rw [htop] at hcomm
  refine MulEquiv.ext fun s => ?_
  have hs : z s = 1 := hcomm (Subgroup.mem_top s)
  change s⁻¹ * τ s = 1 at hs
  rw [MulAut.one_apply]
  exact (inv_mul_eq_one.mp hs).symm

theorem apply_apply_of_sq {ν : MulAut X} (hν : ν ^ 2 = 1) (x : X) : ν (ν x) = x := by
  have := congrArg (fun φ : MulAut X => φ x) hν
  simpa [pow_two] using this

omit [N.Characteristic] in
theorem pow_card_eq_one_of_mem {z : X} (hz : z ∈ N) : z ^ Nat.card N = 1 := by
  have h1 : (⟨z, hz⟩ : N) ^ Nat.card N = 1 := pow_card_eq_one'
  have h2 := congrArg Subtype.val h1
  rwa [Subgroup.coe_pow, Subgroup.coe_one] at h2

theorem exists_fix_lift (hodd : Odd (Nat.card N)) {ν : MulAut X}
    (hν : ν ^ 2 = 1) (c : X) (hc : ((ν c : X) : X ⧸ N) = c) :
    ∃ c' : X, (c' : X ⧸ N) = c ∧ ν c' = c' := by
  obtain ⟨k, hk⟩ := hodd
  have hz : c⁻¹ * ν c ∈ N := QuotientGroup.eq.mp hc.symm
  set z := c⁻¹ * ν c with hzdef
  have hνz : ν z = z⁻¹ := by
    rw [hzdef, map_mul, map_inv, apply_apply_of_sq hν, mul_inv_rev, inv_inv]
  have hzm : z ^ (2 * k + 1) = 1 := hk ▸ pow_card_eq_one_of_mem hz
  refine ⟨c * z ^ (k + 1), ?_, ?_⟩
  · rw [QuotientGroup.mk_mul, (QuotientGroup.eq_one_iff _).mpr (pow_mem hz _), mul_one]
  · have hνc : ν c = c * z := by rw [hzdef, mul_inv_cancel_left]
    have h2 : z * (z ^ (k + 1))⁻¹ = z ^ (k + 1) := by
      rw [mul_inv_eq_iff_eq_mul, ← pow_add, show k + 1 + (k + 1) = 2 * k + 1 + 1 by ring,
        pow_succ, hzm, one_mul]
    rw [map_mul, map_pow, hνz, inv_pow, hνc, mul_assoc, h2]

theorem exists_inv_lift (hN : N ≤ Subgroup.center X) (hodd : Odd (Nat.card N)) {ν : MulAut X}
    (hν : ν ^ 2 = 1) (x : X) (hx : ((ν x : X) : X ⧸ N) = (x : X ⧸ N)⁻¹) :
    ∃ x' : X, (x' : X ⧸ N) = x ∧ ν x' = x'⁻¹ := by
  obtain ⟨k, hk⟩ := hodd
  have hz : x * ν x ∈ N := by
    rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_mul, hx, mul_inv_cancel]
  set z := x * ν x with hzdef
  have hzc : ∀ g : X, g * z = z * g := Subgroup.mem_center_iff.mp (hN hz)
  have hνz : ν z = z := by
    rw [hzdef, map_mul, apply_apply_of_sq hν]
    calc ν x * x = x⁻¹ * (x * ν x) * x := by group
      _ = x⁻¹ * (x * (x * ν x)) := by rw [mul_assoc, ← hzc x]
      _ = x * ν x := by group
  have hzm : z ^ (2 * k + 1) = 1 := hk ▸ pow_card_eq_one_of_mem hz
  refine ⟨x * z ^ k, ?_, ?_⟩
  · rw [QuotientGroup.mk_mul, (QuotientGroup.eq_one_iff _).mpr (pow_mem hz _), mul_one]
  · have hνx : ν x = x⁻¹ * z := by rw [hzdef, inv_mul_cancel_left]
    have hcen : (z ^ k)⁻¹ ∈ Subgroup.center X := inv_mem (pow_mem (hN hz) k)
    rw [map_mul, map_pow, hνz, hνx, mul_inv_rev, ← Subgroup.mem_center_iff.mp hcen x⁻¹,
      mul_assoc]
    congr 1
    rw [eq_inv_iff_mul_eq_one, ← pow_succ', ← pow_add, show k + 1 + k = 2 * k + 1 by ring, hzm]

variable [Finite X]

theorem AutConf.descend [Group.IsPerfect X] (hN : N ≤ Subgroup.center X)
    (hodd : Odd (Nat.card N)) {ν : MulAut X} {Lb Pb : Subgroup (MulAut X)}
    (h : AutConf X ν Lb Pb) :
    AutConf (X ⧸ N) (quotient N ν) (Lb.map (quotient N)) (Pb.map (quotient N)) where
  sq := by rw [← map_pow, h.sq, map_one]
  ne_one h1 := h.ne_one (quotient_injective hN (h1.trans (map_one _).symm))
  sylow := by
    obtain ⟨S, hS, hSν⟩ := h.sylow
    have h2 := CFSG.QuasithinUnique.Setup.X3.isSylowTwoOf_map_of_odd_ker (QuotientGroup.mk' N)
      (by rw [QuotientGroup.ker_mk']; exact hodd) hS
    rw [MonoidHom.range_eq_top.mpr (QuotientGroup.mk'_surjective _)] at h2
    refine ⟨_, h2, ?_⟩
    rintro _ ⟨s, hs, rfl⟩
    change quotient N ν (s : X ⧸ N) = (s : X ⧸ N)
    rw [quotient_apply_coe, hSν s hs]
  inv x hx hinv := by
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective x
    rw [quotient_apply_coe] at hinv
    obtain ⟨x', hx', hνx'⟩ := exists_inv_lift hN hodd h.sq x hinv
    have hodd' : Odd (orderOf x') := by
      have ho : Odd (orderOf (x' : X ⧸ N)) := by rw [hx']; exact hx
      have hmem : x' ^ orderOf (x' : X ⧸ N) ∈ N := by
        rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_pow, pow_orderOf_eq_one]
      have hpow : x' ^ (orderOf (x' : X ⧸ N) * Nat.card N) = 1 := by
        rw [pow_mul, pow_card_eq_one_of_mem hmem]
      exact Odd.of_dvd_nat (ho.mul hodd) (orderOf_dvd_of_pow_eq_one hpow)
    rcases h.inv x' hodd' hνx' with h3 | h5
    · left
      rw [← hx', ← QuotientGroup.mk_pow, h3, QuotientGroup.mk_one]
    · right
      rw [← hx', ← QuotientGroup.mk_pow, h5, QuotientGroup.mk_one]
  comm := by
    rintro _ ⟨l, hl, rfl⟩
    rw [← map_mul, ← map_mul, h.comm l hl]
  three := by
    rintro _ ⟨l, hl, rfl⟩ hodd'
    have hodd'' : Odd (orderOf l) := by
      rwa [orderOf_injective (quotient N) (quotient_injective hN)] at hodd'
    rw [← map_pow, h.three l hl hodd'', map_one]
  gen := by
    refine le_antisymm (oTwoUpper_le _) (Subgroup.map_le_iff_le_comap.mpr ?_)
    calc Lb = oTwoUpper Lb := h.gen.symm
      _ ≤ _ := (Subgroup.closure_le _).mpr fun x hx => by
          show quotient N x ∈ oTwoUpper (Lb.map (quotient N))
          refine Subgroup.subset_closure ⟨⟨x, hx.1, rfl⟩, ?_⟩
          rw [orderOf_injective (quotient N) (quotient_injective hN)]
          exact hx.2
  ne_bot hb := h.ne_bot (by
    rw [eq_bot_iff]
    intro l hl
    have h1 : quotient N l ∈ Lb.map (quotient N) := ⟨l, hl, rfl⟩
    rw [hb, Subgroup.mem_bot] at h1
    exact (Subgroup.mem_bot).mpr (quotient_injective hN (h1.trans (map_one _).symm)))
  norm c hc := by
    rintro _ ⟨l, hl, rfl⟩
    obtain ⟨c, rfl⟩ := QuotientGroup.mk_surjective c
    rw [quotient_apply_coe] at hc
    obtain ⟨c', hc', hνc'⟩ := exists_fix_lift hodd h.sq c hc
    refine ⟨_, h.norm c' hνc' l hl, ?_⟩
    rw [map_mul, map_mul, map_inv, quotient_conj, hc']
  le := Subgroup.map_mono h.le
  elem := by
    refine ⟨⟨⟨fun a b => ?_⟩⟩, ?_⟩
    · obtain ⟨x, hx, hxa⟩ := a.2
      obtain ⟨y, hy, hyb⟩ := b.2
      apply Subtype.ext
      rw [Subgroup.coe_mul, Subgroup.coe_mul, ← hxa, ← hyb, ← map_mul, ← map_mul]
      congr 1
      exact congrArg Subtype.val (h.elem.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
    · rintro _ ⟨x, hx, rfl⟩
      rw [← map_pow, h.elem.2 x hx, map_one]

end CFSG.Quasithin.H13.S126C
