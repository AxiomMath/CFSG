module

public import CFSG.Monster.GMS.Leech.OddType

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.GMS

open CFSG.Blueprint.NativeSporadic

namespace LeechSystem

variable {G : Type*} [Group G] {z : G} (L : LeechSystem z)

include L

theorem exists_odd_conj
    [Finite G] (hI : Co1InvolutionFacts) {t y₀ : G}
    (h : IsLeechCentralLift z t) (h₀ : IsLeechCentralLift z y₀)
    (hodd : Odd (orderOf (L.φ ⟨t, h.mem_centralizer⟩ * L.φ ⟨y₀, h₀.mem_centralizer⟩))) :
    ∃ y, (∃ g ∈ Subgroup.centralizer ({z} : Set G), g * t * g⁻¹ = y) ∧
      ∃ h' : IsLeechCentralLift z y, Odd (orderOf (t * y)) ∧
        L.φ ⟨y, h'.mem_centralizer⟩ = L.φ ⟨y₀, h₀.mem_centralizer⟩ := by
  have ht := h.mem_centralizer
  have hy₀ := h₀.mem_centralizer
  have ht2 := h.mul_self
  have hy₀2 := h₀.mul_self
  have hti : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht2
  have hy₀i : y₀⁻¹ = y₀ := inv_eq_of_mul_eq_one_right hy₀2
  have hdC : t * y₀ ∈ Subgroup.centralizer ({z} : Set G) := mul_mem ht hy₀
  obtain ⟨n, hn⟩ : ∃ n, n = orderOf (L.φ ⟨t, ht⟩ * L.φ ⟨y₀, hy₀⟩) := ⟨_, rfl⟩
  rw [← hn] at hodd
  have hnodd := hodd
  obtain ⟨k', hk'⟩ := hodd
  have ha_mem : (t * y₀) ^ n ∈ leechQ z := by
    refine L.pow_mem_leechQ_of_phi_pow hdC ?_
    rw [L.phi_mul ht hy₀, hn]
    exact pow_orderOf_eq_one _
  obtain ⟨a, ha⟩ : ∃ a, a = (t * y₀) ^ n := ⟨_, rfl⟩
  rw [← ha] at ha_mem
  have hd_t : t * (t * y₀) * t⁻¹ = (t * y₀)⁻¹ := by
    calc t * (t * y₀) * t⁻¹ = (t * t) * y₀ * t⁻¹ := by group
      _ = y₀ * t := by rw [ht2, one_mul, hti]
      _ = (t * y₀)⁻¹ := by rw [mul_inv_rev, hy₀i, hti]
  have hd_y : y₀ * (t * y₀) * y₀⁻¹ = (t * y₀)⁻¹ := by
    calc y₀ * (t * y₀) * y₀⁻¹ = y₀ * t := by group
      _ = (t * y₀)⁻¹ := by rw [mul_inv_rev, hy₀i, hti]
  have ha_inv : y₀ * a * y₀⁻¹ = a⁻¹ := by
    rw [ha, ← conj_pow, hd_y, inv_pow]
  have hfix : L.vec a ∈ co1Fix (L.φ ⟨y₀, hy₀⟩) := by
    show co1Act (L.φ ⟨y₀, hy₀⟩) (L.vec a) = L.vec a
    rw [← L.vec_conj ⟨y₀, hy₀⟩ a ha_mem]
    show L.vec (y₀ * a * y₀⁻¹) = L.vec a
    rw [ha_inv, L.vec_inv ha_mem]
  have ha_comm : y₀ * a = a * y₀ := L.commute_of_vec_mem_co1Fix hI h₀ ha_mem hfix
  have ha2 : a * a = 1 := by
    have h1 : y₀ * a * y₀⁻¹ = a := by rw [ha_comm]; group
    have e : a = a⁻¹ := h1.symm.trans ha_inv
    exact (congrArg (fun x => a * x) e).trans (mul_inv_cancel a)
  obtain ⟨D, hD⟩ : ∃ D, D = (t * y₀) ^ k' := ⟨_, rfl⟩
  have hDC : D ∈ Subgroup.centralizer ({z} : Set G) := hD ▸ pow_mem hdC k'
  have hD_y : y₀ * D * y₀⁻¹ = D⁻¹ := by rw [hD, ← conj_pow, hd_y, inv_pow]
  have hDa : D * (t * y₀) * D = a := by
    rw [hD, ha, hk', ← pow_succ, ← pow_add]
    congr 1
    omega
  have hg : y₀ * D ∈ Subgroup.centralizer ({z} : Set G) := mul_mem hy₀ hDC
  have hg2 : (y₀ * D) * (y₀ * D) = 1 := by
    calc (y₀ * D) * (y₀ * D) = (y₀ * D * y₀⁻¹) * D := by rw [hy₀i]; group
      _ = D⁻¹ * D := by rw [hD_y]
      _ = 1 := inv_mul_cancel D
  have hgi : (y₀ * D)⁻¹ = y₀ * D := inv_eq_of_mul_eq_one_right hg2
  have hconj : (y₀ * D) * t * (y₀ * D)⁻¹ = y₀ * a := by
    rw [hgi]
    calc y₀ * D * t * (y₀ * D) = y₀ * (D * (t * y₀) * D) := by group
      _ = y₀ * a := by rw [hDa]
  have h' : IsLeechCentralLift z (y₀ * a) := hconj ▸ L.isLeechCentralLift_conj h hg
  have haC : a ∈ Subgroup.centralizer ({z} : Set G) := L.mem_centralizer ha_mem
  have hcomm : Commute (t * y₀) a := by
    rw [ha]
    exact (Commute.refl (t * y₀)).pow_right n
  have hpow : (t * (y₀ * a)) ^ n = 1 := by
    calc (t * (y₀ * a)) ^ n = ((t * y₀) * a) ^ n := by rw [mul_assoc]
      _ = (t * y₀) ^ n * a ^ n := hcomm.mul_pow n
      _ = a * a ^ n := by rw [← ha]
      _ = a ^ (n + 1) := (pow_succ' a n).symm
      _ = 1 := by
        rw [hk', show 2 * k' + 1 + 1 = 2 * (k' + 1) by ring, pow_mul, pow_two, ha2, one_pow]
  refine ⟨y₀ * a, ⟨y₀ * D, hg, hconj⟩, h',
    hnodd.of_dvd_nat (orderOf_dvd_of_pow_eq_one hpow), ?_⟩
  rw [show (⟨y₀ * a, h'.mem_centralizer⟩ : Subgroup.centralizer ({z} : Set G)) =
      ⟨y₀, hy₀⟩ * ⟨a, haC⟩ from rfl, map_mul, (L.φ_ker ⟨a, haC⟩).2 ha_mem, mul_one]

omit L in
theorem odd_orderOf_of_co1OddType {r s : Co1} {k : Fin 3} (hk : Co1OddType r s k) :
    Odd (orderOf (r * s)) := by
  fin_cases k
  · rw [hk.1]; decide
  · rw [hk.1]; decide
  · rw [hk.1]; decide

theorem exists_odd_partner
    [Finite G] (hI : Co1InvolutionFacts) (hO : Co1OddPairFacts) {t : G}
    (h : IsLeechCentralLift z t) (k : Fin 3) :
    ∃ y, (∃ g ∈ Subgroup.centralizer ({z} : Set G), g * t * g⁻¹ = y) ∧ y ≠ t ∧
      HasCommonLeechFour z t y ∧ LeechOddType z t y k := by
  obtain ⟨s, hconj, hne, hfour, hk⟩ := (hO _ (L.isCo1TwoA_phi hI h)).2.1 k
  obtain ⟨γ, hγ⟩ := isConj_iff.1 hconj
  obtain ⟨c, rfl⟩ := L.φ_surj γ
  have h₀ := L.isLeechCentralLift_conj h c.2
  have hφ₀ : L.φ ⟨(c : G) * t * (c : G)⁻¹, h₀.mem_centralizer⟩ = s := by
    rw [L.phi_conj c.2 h.mem_centralizer]
    exact hγ
  obtain ⟨y, ⟨g, hg, rfl⟩, h', hodd, hφ⟩ := L.exists_odd_conj hI h h₀
    (by rw [hφ₀]; exact odd_orderOf_of_co1OddType hk)
  rw [hφ₀] at hφ
  refine ⟨g * t * g⁻¹, ⟨g, hg, rfl⟩, fun e => hne ?_, ?_, ?_⟩
  · rw [← hφ]
    congr 1
    exact Subtype.ext e
  · exact (L.hasCommonLeechFour_iff hI h h').2 (by rw [hφ]; exact hfour)
  · exact (L.leechOddType_iff hI h h' hodd k).2 (by rw [hφ]; exact hk)

end LeechSystem

end CFSG.Monster.GMS
