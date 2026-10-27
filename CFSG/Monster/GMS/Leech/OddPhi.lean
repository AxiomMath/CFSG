module

public import CFSG.Monster.GMS.Leech.Pairs
public import CFSG.Monster.GMS.Leech.OddLift

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.GMS

open CFSG.Blueprint.NativeSporadic

namespace LeechSystem

variable {G : Type*} [Group G] {z : G} (L : LeechSystem z)

include L

theorem phi_mul {a b : G} (ha : a ∈ Subgroup.centralizer ({z} : Set G))
    (hb : b ∈ Subgroup.centralizer ({z} : Set G)) :
    L.φ ⟨a * b, mul_mem ha hb⟩ = L.φ ⟨a, ha⟩ * L.φ ⟨b, hb⟩ :=
  map_mul L.φ ⟨a, ha⟩ ⟨b, hb⟩

theorem phi_eq_iff {a b : G} (ha : a ∈ Subgroup.centralizer ({z} : Set G))
    (hb : b ∈ Subgroup.centralizer ({z} : Set G)) :
    L.φ ⟨a, ha⟩ = L.φ ⟨b, hb⟩ ↔ a⁻¹ * b ∈ leechQ z := by
  have hab : a⁻¹ * b ∈ Subgroup.centralizer ({z} : Set G) := mul_mem (inv_mem ha) hb
  rw [← L.φ_ker ⟨a⁻¹ * b, hab⟩]
  have : L.φ ⟨a⁻¹ * b, hab⟩ = (L.φ ⟨a, ha⟩)⁻¹ * L.φ ⟨b, hb⟩ := by
    have := map_mul L.φ (⟨a, ha⟩ : Subgroup.centralizer ({z} : Set G))⁻¹ ⟨b, hb⟩
    rw [map_inv] at this
    exact this
  rw [this, inv_mul_eq_one]

theorem phi_conj {g a : G} (hg : g ∈ Subgroup.centralizer ({z} : Set G))
    (ha : a ∈ Subgroup.centralizer ({z} : Set G)) :
    L.φ ⟨g * a * g⁻¹, mul_mem (mul_mem hg ha) (inv_mem hg)⟩ =
      L.φ ⟨g, hg⟩ * L.φ ⟨a, ha⟩ * (L.φ ⟨g, hg⟩)⁻¹ := by
  have e : (⟨g * a * g⁻¹, mul_mem (mul_mem hg ha) (inv_mem hg)⟩ :
      Subgroup.centralizer ({z} : Set G)) = ⟨g, hg⟩ * ⟨a, ha⟩ * ⟨g, hg⟩⁻¹ := rfl
  rw [e, map_mul, map_mul, map_inv]

theorem inv_mul_conj_mem_of_phi_conj {a b c : G} (ha : a ∈ Subgroup.centralizer ({z} : Set G))
    (hb : b ∈ Subgroup.centralizer ({z} : Set G)) (hc : c ∈ Subgroup.centralizer ({z} : Set G))
    (h : L.φ ⟨c, hc⟩ * L.φ ⟨a, ha⟩ * (L.φ ⟨c, hc⟩)⁻¹ = L.φ ⟨b, hb⟩) :
    b⁻¹ * (c * a * c⁻¹) ∈ leechQ z := by
  have hac : c * a * c⁻¹ ∈ Subgroup.centralizer ({z} : Set G) :=
    mul_mem (mul_mem hc ha) (inv_mem hc)
  refine (L.phi_eq_iff hb hac).1 ?_
  rw [L.phi_conj hc ha, h]

theorem pow_mem_leechQ_of_phi_pow {a : G} (ha : a ∈ Subgroup.centralizer ({z} : Set G)) {n : ℕ}
    (h : (L.φ ⟨a, ha⟩) ^ n = 1) : a ^ n ∈ leechQ z := by
  have h2 : (⟨a, ha⟩ : Subgroup.centralizer ({z} : Set G)) ^ n = ⟨a ^ n, pow_mem ha n⟩ := rfl
  rw [← map_pow, h2] at h
  exact (L.φ_ker _).1 h

theorem orderOf_phi_mul {a b : G} (ha : a ∈ Subgroup.centralizer ({z} : Set G))
    (hb : b ∈ Subgroup.centralizer ({z} : Set G)) (hodd : Odd (orderOf (a * b))) :
    orderOf (L.φ ⟨a, ha⟩ * L.φ ⟨b, hb⟩) = orderOf (a * b) := by
  have hcC : a * b ∈ Subgroup.centralizer ({z} : Set G) := mul_mem ha hb
  rw [← L.phi_mul ha hb]
  apply Nat.dvd_antisymm
  · have := orderOf_map_dvd L.φ (⟨a * b, hcC⟩ : Subgroup.centralizer ({z} : Set G))
    rwa [Subgroup.orderOf_mk] at this
  · have hpow := L.pow_mem_leechQ_of_phi_pow hcC (pow_orderOf_eq_one (L.φ ⟨a * b, hcC⟩))
    have hodd' : Odd (orderOf ((a * b) ^ orderOf (L.φ ⟨a * b, hcC⟩))) :=
      hodd.of_dvd_nat (orderOf_pow_dvd _)
    exact orderOf_dvd_of_pow_eq_one (L.eq_one_of_odd_orderOf hpow hodd')

theorem isLeechFour_iff
    {q : G} : IsLeechFour z q ↔ q ∈ L.typeSet 2 := by
  constructor
  · rintro ⟨hq, h1, hz, hsq, hcard⟩
    rcases L.mem_typeSet_zero_or_two hq h1 hz hsq with h | h
    · exfalso
      have hc := L.card_inf_centralizer_one hq (L.vec_ne_zero_of_mem_typeSet h)
      have ho := Leech.card_co1Stab_mul_ncard_co1Orbit h.2
      rw [Leech.ncard_co1Orbit_zero, CFSG.Sporadic.Co1.card_Co1] at ho
      rw [hc] at hcard
      norm_num at hcard
      omega
    · exact h
  · intro h
    refine ⟨h.1, L.ne_one_of_mem_typeSet h, L.ne_z_of_mem_typeSet h,
      L.mul_self_of_mem_typeSet_two h, ?_⟩
    rw [L.card_inf_centralizer_one h.1 (L.vec_ne_zero_of_mem_typeSet h)]
    have ho := Leech.card_co1Stab_mul_ncard_co1Orbit h.2
    rw [Leech.ncard_co1Orbit_two, CFSG.Sporadic.Co1.card_Co1] at ho
    have : Nat.card ↥(co1Stab (L.vec q)) = 501397585920 := by omega
    rw [this]
    norm_num

end LeechSystem

end CFSG.Monster.GMS
