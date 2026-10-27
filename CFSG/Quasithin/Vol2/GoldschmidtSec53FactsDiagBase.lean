module

public import CFSG.Quasithin.Vol2.GoldschmidtSec53FactsBorAut

public section

namespace CFSG.Quasithin.H13.Sec53F.BA

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Quasithin.H13.F431

variable {Y : Type} [Group Y]

structure BorelBase (U H : Subgroup Y) : Prop where
  center : ∀ y : Y, (∀ x : Y, y * x = x * y) → y = 1
  sylow : IsSylowTwoOf U ⊤
  H_comm : ∀ a ∈ H, ∀ b ∈ H, a * b = b * a
  H_le : H ≤ Subgroup.normalizer (U : Set Y)
  U_inf_H : ∀ x ∈ U, x ∈ H → x = 1
  B_eq : ∀ g ∈ Subgroup.normalizer (U : Set Y), ∃ u ∈ U, ∃ h ∈ H, g = u * h

namespace BorelBase

variable {U H : Subgroup Y} (D : BorelBase U H)

include D

theorem quot_comm (q r : ↥(Subgroup.normalizer (U : Set Y)) ⧸
    U.subgroupOf (Subgroup.normalizer (U : Set Y))) : q * r = r * q := by
  have key : ∀ z : ↥(Subgroup.normalizer (U : Set Y)), ∃ h : ↥(Subgroup.normalizer (U : Set Y)),
      (h : Y) ∈ H ∧ (QuotientGroup.mk z : ↥(Subgroup.normalizer (U : Set Y)) ⧸
        U.subgroupOf (Subgroup.normalizer (U : Set Y))) = QuotientGroup.mk h := by
    intro z
    obtain ⟨u, hu, h, hh, hz⟩ := D.B_eq z.1 z.2
    refine ⟨⟨h, D.H_le hh⟩, hh, ?_⟩
    rw [QuotientGroup.eq, Subgroup.mem_subgroupOf]
    show (z.1)⁻¹ * h ∈ U
    rw [hz, mul_inv_rev, mul_assoc]
    have hinv : h⁻¹ ∈ Subgroup.normalizer (U : Set Y) :=
      (Subgroup.normalizer (U : Set Y)).inv_mem (D.H_le hh)
    have := (Subgroup.mem_normalizer_iff.mp hinv u⁻¹).mp (U.inv_mem hu)
    simpa [mul_assoc] using this
  refine QuotientGroup.induction_on q fun z => QuotientGroup.induction_on r fun w => ?_
  obtain ⟨h, hh, hz⟩ := key z
  obtain ⟨h', hh', hw⟩ := key w
  rw [hz, hw, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
  congr 1
  exact Subtype.ext (D.H_comm _ hh _ hh')

theorem mem_U_of_pow (x : Y) (hx : x ∈ Subgroup.normalizer (U : Set Y)) {a : ℕ}
    (h : x ^ 2 ^ a = 1) : x ∈ U := by
  set B := Subgroup.normalizer (U : Set Y) with hB
  set π := QuotientGroup.mk' (U.subgroupOf B) with hπ
  have hpow : (⟨x, hx⟩ : ↥B) ^ 2 ^ a = 1 := Subtype.ext (by simpa using h)
  have h1 : orderOf (π ⟨x, hx⟩) ∣ 2 ^ a := by
    apply orderOf_dvd_of_pow_eq_one
    rw [← map_pow, hpow, map_one]
  have h2 : orderOf (π ⟨x, hx⟩) ∣ Nat.card (↥B ⧸ U.subgroupOf B) := orderOf_dvd_natCard _
  have hodd : ¬ 2 ∣ Nat.card (↥B ⧸ U.subgroupOf B) := by
    have h3 : Nat.card (↥B ⧸ U.subgroupOf B) = U.relIndex B := rfl
    have h4 := Subgroup.relIndex_mul_relIndex U B ⊤ Subgroup.le_normalizer le_top
    intro hd
    apply D.sylow.2.2
    rw [h3] at hd
    have : (U.subgroupOf ⊤).index = U.relIndex ⊤ := rfl
    rw [this, ← h4]
    exact hd.mul_right _
  have hcop : Nat.Coprime (2 ^ a) (Nat.card (↥B ⧸ U.subgroupOf B)) :=
    Nat.Coprime.pow_left a ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr hodd)
  have h5 : orderOf (π ⟨x, hx⟩) = 1 := Nat.eq_one_of_dvd_one (hcop ▸ Nat.dvd_gcd h1 h2)
  have h6 : π ⟨x, hx⟩ = 1 := orderOf_eq_one_iff.mp h5
  exact (BorelAutData.mk_eq_one_iff U ⟨x, hx⟩).mp h6

theorem isSolvable_B [Finite Y] : Group.IsSolvable ↥(Subgroup.normalizer (U : Set Y)) := by
  set B := Subgroup.normalizer (U : Set Y) with hB
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Group.IsNilpotent U := D.sylow.2.1.isNilpotent
  have : Group.IsSolvable U := inferInstance
  have : Group.IsSolvable (↥B ⧸ U.subgroupOf B) :=
    Group.isSolvable_of_comm fun q r => D.quot_comm q r
  refine Group.isSolvable_of_ker_le_range (Subgroup.inclusion (Subgroup.le_normalizer : U ≤ B))
    (QuotientGroup.mk' (U.subgroupOf B)) ?_
  intro x hx
  rw [MonoidHom.mem_ker] at hx
  exact ⟨⟨x, (BorelAutData.mk_eq_one_iff U x).mp hx⟩, rfl⟩

omit D in
theorem stab_B {σ : MulAut Y} (hU : ∀ x, σ x ∈ U ↔ x ∈ U) (g : Y) :
    σ g ∈ Subgroup.normalizer (U : Set Y) ↔ g ∈ Subgroup.normalizer (U : Set Y) := by
  rw [Subgroup.mem_normalizer_iff, Subgroup.mem_normalizer_iff]
  constructor
  · intro H' y
    have := H' (σ y)
    rwa [hU, ← map_inv, ← map_mul, ← map_mul, hU] at this
  · intro H' y
    obtain ⟨y', rfl⟩ := σ.surjective y
    have := H' y'
    rw [← hU y', ← hU (g * y' * g⁻¹), map_mul, map_mul, map_inv] at this
    exact this

theorem conj_injective : Function.Injective (MulAut.conj : Y →* MulAut Y) := by
  rw [injective_iff_map_eq_one]
  intro d hd
  apply D.center d
  intro y
  have h := congrArg (fun φ : MulAut Y => φ y) hd
  simp only [MulAut.conj_apply, MulAut.one_apply] at h
  rw [mul_inv_eq_iff_eq_mul] at h
  exact h

end BorelBase

end CFSG.Quasithin.H13.Sec53F.BA
