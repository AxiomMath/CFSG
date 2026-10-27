module

public import CFSG.Monster.GMS.Leech.Involutions
public import CFSG.Monster.GMS.Facts.LeechOddPairs
public import CFSG.Monster.GMS.Facts.Co1OddPairs

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.GMS

open CFSG.Blueprint.NativeSporadic

section Accessors

variable {G : Type*} [Group G] {z t : G}

theorem IsLeechCentralLift.mem_centralizer (h : IsLeechCentralLift z t) :
    t ∈ Subgroup.centralizer ({z} : Set G) := h.1

theorem IsLeechCentralLift.orderOf_eq_two (h : IsLeechCentralLift z t) : orderOf t = 2 := h.2.1

theorem IsLeechCentralLift.not_mem (h : IsLeechCentralLift z t) : t ∉ leechQ z := h.2.2.1

theorem IsLeechCentralLift.card (h : IsLeechCentralLift z t) :
    Nat.card ↥(Subgroup.centralizer ({z} : Set G) ⊓ Subgroup.centralizer {t}) =
      2 ^ 38 * 3 ^ 5 * 5 ^ 2 * 7 := h.2.2.2.1

theorem IsLeechCentralLift.ne_conj (h : IsLeechCentralLift z t) {g : G}
    (hg : g ∈ Subgroup.centralizer ({z} : Set G)) : g * t * g⁻¹ ≠ t * z := h.2.2.2.2 g hg

theorem IsLeechCentralLift.mul_self (h : IsLeechCentralLift z t) : t * t = 1 := by
  rw [← pow_two, ← h.orderOf_eq_two]
  exact pow_orderOf_eq_one t

end Accessors

namespace LeechSystem

variable {G : Type*} [Group G] {z : G} (L : LeechSystem z)

include L

theorem pow_four_eq_one {q : G} (hq : q ∈ leechQ z) : q ^ 4 = 1 := by
  have h2 : q ^ 2 = 1 ∨ q ^ 2 = z := by
    simpa only [pow_two] using L.extraspecial.sq q hq
  rw [show (4 : ℕ) = 2 * 2 by norm_num, pow_mul]
  rcases h2 with h | h
  · rw [h, one_pow]
  · rw [h, pow_two]
    exact L.z_mul_self

theorem eq_one_of_odd_orderOf {q : G} (hq : q ∈ leechQ z) (hodd : Odd (orderOf q)) : q = 1 := by
  have hdvd : orderOf q ∣ 4 := orderOf_dvd_of_pow_eq_one (L.pow_four_eq_one hq)
  have hcop : Nat.Coprime (orderOf q) 4 := by
    have := hodd.coprime_two_right.pow_right 2
    simpa using this
  exact orderOf_eq_one_iff.1 (Nat.Coprime.eq_one_of_dvd hcop hdvd)

theorem z_inv : z⁻¹ = z := inv_eq_of_mul_eq_one_right L.z_mul_self

omit L in
theorem conj_z {g : G} (hg : g ∈ Subgroup.centralizer ({z} : Set G)) : g * z * g⁻¹ = z := by
  have := Subgroup.mem_centralizer_singleton_iff.mp hg
  rw [mul_inv_eq_iff_eq_mul]
  exact this

theorem isLeechCentralLift_conj {t g : G} (h : IsLeechCentralLift z t)
    (hg : g ∈ Subgroup.centralizer ({z} : Set G)) : IsLeechCentralLift z (g * t * g⁻¹) := by
  obtain ⟨ht, h2, hQ, hcard, hnc⟩ := h
  refine ⟨mul_mem (mul_mem hg ht) (inv_mem hg), orderOf_conj_eq_two g h2, L.conj_not_mem hg hQ,
    (card_inf_centralizer_conj hg t).trans hcard, ?_⟩
  intro c hc hcon
  apply hnc (g⁻¹ * c * g) (mul_mem (mul_mem (inv_mem hg) hc) hg)
  have hgz : g⁻¹ * z * g = z := by
    have := conj_z (inv_mem hg)
    simpa using this
  calc g⁻¹ * c * g * t * (g⁻¹ * c * g)⁻¹ = g⁻¹ * (c * (g * t * g⁻¹) * c⁻¹) * g := by group
    _ = g⁻¹ * (g * t * g⁻¹ * z) * g := by rw [hcon]
    _ = t * (g⁻¹ * z * g) := by group
    _ = t * z := by rw [hgz]

theorem isCo1TwoA_phi
    [Finite G] (hI : Co1InvolutionFacts) {t : G} (h : IsLeechCentralLift z t) :
    IsCo1TwoA (L.φ ⟨t, h.mem_centralizer⟩) :=
  ⟨L.orderOf_φ h.mem_centralizer h.orderOf_eq_two h.not_mem,
    (L.central_lift_facts hI h.mem_centralizer h.orderOf_eq_two h.not_mem h.card).1⟩

theorem commute_of_vec_mem_co1Fix
    [Finite G] (hI : Co1InvolutionFacts) {t : G}
    (h : IsLeechCentralLift z t) {q : G} (hq : q ∈ leechQ z)
    (hfix : L.vec q ∈ co1Fix (L.φ ⟨t, h.mem_centralizer⟩)) : t * q = q * t :=
  (L.central_lift_facts hI h.mem_centralizer h.orderOf_eq_two h.not_mem h.card).2.1 q hq hfix

theorem vec_mem_co1Fix_of_comm {t q : G} (ht : t ∈ Subgroup.centralizer ({z} : Set G))
    (hq : q ∈ leechQ z) (hcomm : t * q = q * t) : L.vec q ∈ co1Fix (L.φ ⟨t, ht⟩) := by
  show co1Act (L.φ ⟨t, ht⟩) (L.vec q) = L.vec q
  rw [← L.vec_conj ⟨t, ht⟩ q hq]
  congr 1
  show t * q * t⁻¹ = q
  rw [hcomm]
  group

theorem exists_Qconj_of_lift
    [Finite G] (hI : Co1InvolutionFacts) {t g : G}
    (h : IsLeechCentralLift z t) (hg : g ∈ Subgroup.centralizer ({z} : Set G))
    (hQ : t⁻¹ * (g * t * g⁻¹) ∈ leechQ z) :
    ∃ p ∈ leechQ z, p * t * p⁻¹ = g * t * g⁻¹ := by
  have hx := L.isLeechCentralLift_conj h hg
  obtain ⟨-, hft, -⟩ := L.central_lift_facts hI h.mem_centralizer h.orderOf_eq_two h.not_mem h.card
  obtain ⟨-, hfx, -⟩ :=
    L.central_lift_facts hI hx.mem_centralizer hx.orderOf_eq_two hx.not_mem hx.card
  obtain ⟨p, hp, hpx⟩ := L.exists_conj_of_inv_mem h.mem_centralizer hx.mem_centralizer
    h.mul_self hx.mul_self hQ hft hfx
  rcases hpx with hpx | hpx
  · exact ⟨p, hp, hpx⟩
  · exfalso
    have hu : g⁻¹ * p ∈ Subgroup.centralizer ({z} : Set G) :=
      mul_mem (inv_mem hg) (L.mem_centralizer hp)
    apply h.ne_conj hu
    have h1 : (g⁻¹ * p) * (t * z) * (g⁻¹ * p)⁻¹ = t := by
      calc (g⁻¹ * p) * (t * z) * (g⁻¹ * p)⁻¹ = g⁻¹ * (p * (t * z) * p⁻¹) * g := by group
        _ = g⁻¹ * (g * t * g⁻¹) * g := by rw [hpx]
        _ = t := by group
    have hzu : (g⁻¹ * p) * z * (g⁻¹ * p)⁻¹ = z := conj_z hu
    have h2 : (g⁻¹ * p) * t * (g⁻¹ * p)⁻¹ * z = t := by
      calc (g⁻¹ * p) * t * (g⁻¹ * p)⁻¹ * z
          = (g⁻¹ * p) * t * (g⁻¹ * p)⁻¹ * ((g⁻¹ * p) * z * (g⁻¹ * p)⁻¹) := by rw [hzu]
        _ = (g⁻¹ * p) * (t * z) * (g⁻¹ * p)⁻¹ := by group
        _ = t := h1
    calc (g⁻¹ * p) * t * (g⁻¹ * p)⁻¹ = ((g⁻¹ * p) * t * (g⁻¹ * p)⁻¹ * z) * z⁻¹ := by group
      _ = t * z⁻¹ := by rw [h2]
      _ = t * z := by rw [L.z_inv]

theorem exists_mul_mem_centralizer_of_lift
    [Finite G] (hI : Co1InvolutionFacts) {t g : G}
    (h : IsLeechCentralLift z t) (hg : g ∈ Subgroup.centralizer ({z} : Set G))
    (hQ : t⁻¹ * (g * t * g⁻¹) ∈ leechQ z) :
    ∃ p ∈ leechQ z, p * g ∈ Subgroup.centralizer ({t} : Set G) := by
  obtain ⟨p, hp, hpt⟩ := L.exists_Qconj_of_lift hI h hg hQ
  refine ⟨p⁻¹, inv_mem hp, Subgroup.mem_centralizer_singleton_iff.2 ?_⟩
  have : p⁻¹ * g * t * (p⁻¹ * g)⁻¹ = t := by
    calc p⁻¹ * g * t * (p⁻¹ * g)⁻¹ = p⁻¹ * (g * t * g⁻¹) * p := by group
      _ = p⁻¹ * (p * t * p⁻¹) * p := by rw [hpt]
      _ = t := by group
  rw [mul_inv_eq_iff_eq_mul] at this
  exact this

end LeechSystem

end CFSG.Monster.GMS
