module

public import CFSG.RankThree.PartOne.K1320.Struct
public import CFSG.RankThree.PartOne.S9.OddCore.TorsionCommon

public section

namespace CFSG.RankThree.PartOne.K1320

open CFSG.Assembly CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.GroupTheory
open CFSG.RankThree.PartOne.Torsion37

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

variable {G : Type} [Group G] [Finite G]

section Members

variable {p : ℕ} {A : Subgroup G} {c : G} {L E : Subgroup G} {B : Subgroup G} {c' : G}
  {J : Subgroup G}

theorem not_d12 (hF' : Sec12Facts G p B c' J E) {z : MulAut E}
    (h6 : ∀ g ∈ reflectionGroup p E, g ^ 6 = 1 → g ^ 3 ≠ 1 → g ^ 2 ≠ 1 → g ^ 3 = z)
    (hz : z ∉ torusImage E J) (e : ↥(torusImage E J) ≃* DihedralGroup 6) : False := by
  obtain ⟨g0, hg6, hg3, hg2⟩ := d12_six
  have hle := torusImage_le_reflectionGroup hF'
  set x : ↥(torusImage E J) := e.symm g0 with hx
  have hxe : ∀ n : ℕ, e (x ^ n) = g0 ^ n := fun n => by
    rw [map_pow, hx, MulEquiv.apply_symm_apply]
  have hx6 : x ^ 6 = 1 := e.injective (by rw [hxe, hg6, map_one])
  have hx3 : x ^ 3 ≠ 1 := fun h => hg3 (by rw [← hxe, h, map_one])
  have hx2 : x ^ 2 ≠ 1 := fun h => hg2 (by rw [← hxe, h, map_one])
  have hxX : (x : MulAut E) ∈ reflectionGroup p E := hle x.2
  have e6 : (x : MulAut E) ^ 6 = 1 := by rw [← Subgroup.coe_pow, hx6, Subgroup.coe_one]
  have e3 : (x : MulAut E) ^ 3 ≠ 1 := fun h => hx3 (Subtype.ext (by
    rw [Subgroup.coe_pow, h, Subgroup.coe_one]))
  have e2 : (x : MulAut E) ^ 2 ≠ 1 := fun h => hx2 (Subtype.ext (by
    rw [Subgroup.coe_pow, h, Subgroup.coe_one]))
  apply hz
  rw [← h6 _ hxX e6 e3 e2, ← Subgroup.coe_pow]
  exact (x ^ 3).2

theorem not_d16 (hF' : Sec12Facts G p B c' J E)
    (h8 : ∀ g ∈ reflectionGroup p E, g ^ 8 = 1 → g ^ 4 = 1)
    (e : ↥(torusImage E J) ≃* DihedralGroup 8) : False := by
  obtain ⟨g0, hg8, hg4⟩ := d16_eight
  have hle := torusImage_le_reflectionGroup hF'
  set x : ↥(torusImage E J) := e.symm g0 with hx
  have hxe : ∀ n : ℕ, e (x ^ n) = g0 ^ n := fun n => by
    rw [map_pow, hx, MulEquiv.apply_symm_apply]
  have hx8 : x ^ 8 = 1 := e.injective (by rw [hxe, hg8, map_one])
  have hx4 : x ^ 4 ≠ 1 := fun h => hg4 (by rw [← hxe, h, map_one])
  have hxX : (x : MulAut E) ∈ reflectionGroup p E := hle x.2
  have e8 : (x : MulAut E) ^ 8 = 1 := by rw [← Subgroup.coe_pow, hx8, Subgroup.coe_one]
  have := h8 _ hxX e8
  exact hx4 (Subtype.ext (by rw [Subgroup.coe_pow, this, Subgroup.coe_one]))

theorem member_row (h' : Sec12Hyp G p B c' J E) (hF' : Sec12Facts G p B c' J E)
    (hcard : Nat.card E = p ^ 3) {z : MulAut E}
    (h6 : ∀ g ∈ reflectionGroup p E, g ^ 6 = 1 → g ^ 3 ≠ 1 → g ^ 2 ≠ 1 → g ^ 3 = z)
    (h8 : ∀ g ∈ reflectionGroup p E, g ^ 8 = 1 → g ^ 4 = 1) (hz : z ∉ torusImage E J) :
    ∃ r : ℕ, (r = 1 ∨ r = 5 ∨ r = 6 ∨ r = 7 ∨ r = 8) ∧ RowModel p J r ∧
      RowWeylIso E (torusImage E J) r := by
  obtain ⟨-, r, hr1, hr12, hmodel, hW, -, h9⟩ := hF'.three
  have hr8 : r ≤ 8 := by
    by_contra hlt
    have h4 := h9 (by omega)
    rw [hcard] at h4
    have hp := h'.prime
    have := Nat.pow_right_injective hp.two_le h4
    omega
  refine ⟨r, ?_, hmodel, hW⟩
  interval_cases r
  · exact Or.inl rfl
  · exfalso
    obtain ⟨e⟩ : Nonempty (↥(torusImage E J) ≃* DihedralGroup 6) := hW
    exact not_d12 hF' h6 hz e
  · exfalso
    obtain ⟨e⟩ : Nonempty (↥(torusImage E J) ≃* DihedralGroup 6) := hW
    exact not_d12 hF' h6 hz e
  · exfalso
    obtain ⟨e⟩ : Nonempty (↥(torusImage E J) ≃* DihedralGroup 8) := hW
    exact not_d16 hF' h8 e
  · exact Or.inr (Or.inl rfl)
  · exact Or.inr (Or.inr (Or.inl rfl))
  · exact Or.inr (Or.inr (Or.inr (Or.inl rfl)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr rfl)))

theorem member_package (hF13 : Sec13Facts G p A c L E) (hcard : Nat.card E = p ^ 3)
    {z : MulAut E} (hz : Inverter p E z) {J : Subgroup G} (hJ : J ∈ thetaCompZeroStarE p E) :
    ∃ (B : Subgroup G) (c' : G), Sec12Hyp G p B c' J E ∧ Sec12Facts G p B c' J E ∧ c' ∈ E ∧
      c' ≠ 1 ∧ E = B ∧ ∃ r : ℕ, (r = 1 ∨ r = 5 ∨ r = 6 ∨ r = 7 ∨ r = 8) ∧ RowModel p J r ∧
        RowWeylIso E (torusImage E J) r := by
  obtain ⟨B, c', hB, hc'B, hc'1, h', hF'⟩ := hF13.reinstantiate J hJ
  have hc'E : c' ∈ E := hB.1 hc'B
  have hBE : B = E := Subgroup.eq_of_le_of_card_ge hB.1 (by rw [hcard, hB.2.2.1])
  obtain ⟨r, hr, hmodel, hW⟩ := member_row h' hF' hcard hz.six hz.no_eight
    (inverter_not_mem_torusImage h' hc'E hc'1 hz.inv)
  exact ⟨B, c', h', hF', hc'E, hc'1, hBE.symm, r, hr, hmodel, hW⟩

theorem no_central_reflection (hF13 : Sec13Facts G p A c L E) (h' : Sec12Hyp G p B c' J E)
    (hF' : Sec12Facts G p B c' J E) (hcard : Nat.card E = p ^ 3) (hc'E : c' ∈ E)
    {t : MulAut E} (ht : t ∈ reflectionSet p E) (htJ : t ∈ torusImage E J)
    (hcen : ∀ g ∈ torusImage E J, g * t = t * g) : False := by
  classical
  have hp := h'.prime
  have hp5 := Sec12Three.five_le h'
  obtain ⟨-, -, hℓcard⟩ := hF13.reflection t ht
  have hℓE : autMovedInG E t ≤ E := Subgroup.map_subtype_le _
  have hinv : torusInvariant E J (autMovedInG E t) := by
    intro w hw b hb
    obtain ⟨hwJ, hwN⟩ := Subgroup.mem_inf.1 hw
    have hg : conjAut E w hwN ∈ torusImage E J :=
      Sec12Three.mem_torusImage_iff.2 ⟨w, hwJ, hwN, rfl⟩
    have h1 : conjAut E w hwN * t * (conjAut E w hwN)⁻¹ = t := by
      rw [hcen _ hg]
      group
    have h2 := Equivariance.autMovedInG_conj t hwN
    rw [h1] at h2
    have h3 : w * b * w⁻¹ ∈ conjBy w (autMovedInG E t) := by
      unfold conjBy
      exact Subgroup.mem_map.2 ⟨b, hb, by simp [MulAut.conj_apply]⟩
    rwa [← h2] at h3
  have hℓne : autMovedInG E t ≠ ⊥ := by
    intro h0
    rw [h0, Subgroup.card_bot] at hℓcard
    have := hp.two_le
    omega
  have hℓE' : autMovedInG E t ≠ E := by
    intro h0
    rw [h0, hcard] at hℓcard
    have h3 : p ^ 3 = p ^ 1 := by rw [pow_one]; exact hℓcard
    have := Nat.pow_right_injective hp.two_le h3
    omega
  obtain ⟨w, hwJ, hwN, hwt⟩ := Sec12Three.mem_torusImage_iff.1 htJ
  have hconj : w * c' * w⁻¹ = c' := by
    have := Sec12Three.comm_c_L h' w hwJ
    rw [← this]
    group
  rcases hF'.four.1 _ hℓE hinv hℓne hℓE' with hc | hM
  · have hc'ℓ : c' ∈ autMovedInG E t := by
      rw [hc]
      exact Subgroup.mem_zpowers c'
    obtain ⟨m, hm, hmc⟩ := Subgroup.mem_map.1 hc'ℓ
    have hEel := h'.E_elem
    have hd : RefFacts.ElemData p E :=
      RefFacts.ElemData.of_isElementaryAbelian hp (by omega) hEel
    have hinv' : t m = m⁻¹ := RefFacts.t_apply_inv_of_mem_autMoved hd ht.1 hm
    have hcoe : ((t m : E) : G) = w * (m : G) * w⁻¹ := by
      rw [← hwt]
      exact Equivariance.coe_conjAut hwN m
    rw [hinv'] at hcoe
    have hmc' : (m : G) = c' := hmc
    rw [hmc', hconj] at hcoe
    simp only [Subgroup.coe_inv] at hcoe
    rw [hmc'] at hcoe
    have h2 : c' * c' = 1 := by
      calc c' * c' = c'⁻¹ * c' := by rw [hcoe]
        _ = 1 := inv_mul_cancel c'
    have h3 : c' ^ 2 = 1 := by rw [pow_two]; exact h2
    have h4 : c' ^ p = 1 := Sec12Three.pow_eq_one_of_mem_E h' hc'E
    have h5 : c' ^ Nat.gcd 2 p = 1 := pow_gcd_eq_one.mpr ⟨h3, h4⟩
    have hcop : Nat.gcd 2 p = 1 := by
      have : Nat.Coprime 2 p := (Nat.coprime_primes Nat.prime_two hp).2 (by omega)
      exact this
    rw [hcop, pow_one] at h5
    exact h'.c_ne_one h5
  · rcases hF'.four.2 with ⟨hEsup, hdisj⟩ | ⟨-, hMeq⟩
    · have hEel := h'.E_elem
      have hMcard : Nat.card ↥(⁅E, J ⊓ torusNormalizer E⁆) = p := hM ▸ hℓcard
      have hME : ⁅E, J ⊓ torusNormalizer E⁆ ≤ E := hM ▸ hℓE
      have hcc : ∀ x ∈ Subgroup.zpowers c', ∀ y ∈ ⁅E, J ⊓ torusNormalizer E⁆, x * y = y * x := by
        intro x hx y hy
        have hxE : x ∈ E := by
          obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hx
          exact E.zpow_mem hc'E k
        exact congrArg Subtype.val (hEel.is_comm.comm ⟨x, hxE⟩ ⟨y, hME hy⟩)
      have hcardsup := card_sup_of_commute_disjoint hcc (disjoint_iff.2 hdisj)
      have hEcard : Nat.card ↥(Subgroup.zpowers c' ⊔ ⁅E, J ⊓ torusNormalizer E⁆) = Nat.card ↥E := by
        rw [← hEsup]
      rw [hEcard, hcard, hMcard, Nat.card_zpowers, Sec12Three.orderOf_c h'] at hcardsup
      have h3 : p ^ 3 = p ^ 2 := by rw [hcardsup]; ring
      have := Nat.pow_right_injective hp.two_le h3
      omega
    · exact hℓE' (hM.trans hMeq)


theorem commuting_conj_d8 (hF13 : Sec13Facts G p A c L E) (h' : Sec12Hyp G p B c' J E)
    (hF' : Sec12Facts G p B c' J E) (hcard : Nat.card E = p ^ 3) (hc'E : c' ∈ E)
    (e : ↥(torusImage E J) ≃* DihedralGroup 4) {s t : MulAut E} (hs : s ∈ reflectionSet p E)
    (hsJ : s ∈ torusImage E J) (ht : t ∈ reflectionSet p E) (htJ : t ∈ torusImage E J)
    (hst : s ≠ t) (hcomm : s * t = t * s) : ∃ x ∈ torusImage E J, x * s * x⁻¹ = t := by
  have hs2 : s * s = 1 := RefFacts.mul_self_eq_one hs.1
  have ht2 : t * t = 1 := RefFacts.mul_self_eq_one ht.1
  have hs' : (⟨s, hsJ⟩ : ↥(torusImage E J)) * ⟨s, hsJ⟩ = 1 := Subtype.ext hs2
  have ht' : (⟨t, htJ⟩ : ↥(torusImage E J)) * ⟨t, htJ⟩ = 1 := Subtype.ext ht2
  have ha : e ⟨s, hsJ⟩ * e ⟨s, hsJ⟩ = 1 := by rw [← map_mul, hs', map_one]
  have hb : e ⟨t, htJ⟩ * e ⟨t, htJ⟩ = 1 := by rw [← map_mul, ht', map_one]
  have hne : e ⟨s, hsJ⟩ ≠ e ⟨t, htJ⟩ := fun h =>
    hst (congrArg Subtype.val (e.injective h))
  have hab : e ⟨s, hsJ⟩ * e ⟨t, htJ⟩ = e ⟨t, htJ⟩ * e ⟨s, hsJ⟩ := by
    rw [← map_mul, ← map_mul]
    exact congrArg e (Subtype.ext hcomm)
  rcases d8_commuting _ _ ha hb hne hab with hc | hc | ⟨x, hx⟩
  · exfalso
    refine no_central_reflection hF13 h' hF' hcard hc'E hs hsJ fun g hg => ?_
    have h1 := hc (e ⟨g, hg⟩)
    have h2 : (⟨g, hg⟩ : ↥(torusImage E J)) * ⟨s, hsJ⟩ = ⟨s, hsJ⟩ * ⟨g, hg⟩ :=
      e.injective (by rw [map_mul, map_mul]; exact h1)
    exact congrArg Subtype.val h2
  · exfalso
    refine no_central_reflection hF13 h' hF' hcard hc'E ht htJ fun g hg => ?_
    have h1 := hc (e ⟨g, hg⟩)
    have h2 : (⟨g, hg⟩ : ↥(torusImage E J)) * ⟨t, htJ⟩ = ⟨t, htJ⟩ * ⟨g, hg⟩ :=
      e.injective (by rw [map_mul, map_mul]; exact h1)
    exact congrArg Subtype.val h2
  · refine ⟨((e.symm x : ↥(torusImage E J)) : MulAut E), (e.symm x).2, ?_⟩
    have h1 : e.symm x * ⟨s, hsJ⟩ * (e.symm x)⁻¹ = ⟨t, htJ⟩ := by
      apply e.injective
      rw [map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply]
      exact hx
    have h2 := congrArg Subtype.val h1
    simpa using h2

theorem commuting_conj (hF13 : Sec13Facts G p A c L E) (h' : Sec12Hyp G p B c' J E)
    (hF' : Sec12Facts G p B c' J E) (hcard : Nat.card E = p ^ 3) (hc'E : c' ∈ E) {r : ℕ}
    (hr : r = 1 ∨ r = 5 ∨ r = 6 ∨ r = 7 ∨ r = 8) (hW : RowWeylIso E (torusImage E J) r)
    {s t : MulAut E} (hs : s ∈ reflectionSet p E) (hsJ : s ∈ torusImage E J)
    (ht : t ∈ reflectionSet p E) (htJ : t ∈ torusImage E J) (hst : s ≠ t) (hcomm : s * t = t * s) :
    ∃ x ∈ torusImage E J, x * s * x⁻¹ = t := by
  have hs2 : s * s = 1 := RefFacts.mul_self_eq_one hs.1
  have ht2 : t * t = 1 := RefFacts.mul_self_eq_one ht.1
  rcases hr with rfl | rfl | rfl | rfl | rfl
  · exfalso
    obtain ⟨e⟩ : Nonempty (↥(torusImage E J) ≃* Equiv.Perm (Fin 3)) := hW
    have hs1 : s ≠ 1 := fun h => by
      have := hs.1.1
      rw [h, orderOf_one] at this
      omega
    have ht1 : t ≠ 1 := fun h => by
      have := ht.1.1
      rw [h, orderOf_one] at this
      omega
    refine s3_no_commuting (e ⟨s, hsJ⟩) (e ⟨t, htJ⟩) ?_ ?_ ?_ ?_ ?_ ?_
    · rw [← map_mul]
      have : (⟨s, hsJ⟩ : ↥(torusImage E J)) * ⟨s, hsJ⟩ = 1 := Subtype.ext hs2
      rw [this, map_one]
    · rw [← map_mul]
      have : (⟨t, htJ⟩ : ↥(torusImage E J)) * ⟨t, htJ⟩ = 1 := Subtype.ext ht2
      rw [this, map_one]
    · intro h1
      exact hs1 (congrArg Subtype.val (e.injective (h1.trans (map_one e).symm)))
    · intro h1
      exact ht1 (congrArg Subtype.val (e.injective (h1.trans (map_one e).symm)))
    · intro h1
      exact hst (congrArg Subtype.val (e.injective h1))
    · rw [← map_mul, ← map_mul]
      exact congrArg e (Subtype.ext hcomm)
  all_goals
    obtain ⟨e⟩ : Nonempty (↥(torusImage E J) ≃* DihedralGroup 4) := hW
    exact commuting_conj_d8 hF13 h' hF' hcard hc'E e hs hsJ ht htJ hst hcomm

omit [Finite G] in
theorem row_one_of_order_three {r : ℕ} (hr : r = 1 ∨ r = 5 ∨ r = 6 ∨ r = 7 ∨ r = 8)
    (hW : RowWeylIso E (torusImage E J) r) {g : MulAut E} (hg : g ∈ torusImage E J)
    (h3 : g ^ 3 = 1) (h1 : g ≠ 1) : r = 1 := by
  rcases hr with rfl | rfl | rfl | rfl | rfl
  · rfl
  all_goals
    exfalso
    obtain ⟨e⟩ : Nonempty (↥(torusImage E J) ≃* DihedralGroup 4) := hW
    have h4 : e ⟨g, hg⟩ ^ 3 = 1 := by
      rw [← map_pow]
      have : (⟨g, hg⟩ : ↥(torusImage E J)) ^ 3 = 1 := Subtype.ext (by simpa using h3)
      rw [this, map_one]
    have h5 := d8_no_three _ h4
    exact h1 (congrArg Subtype.val (e.injective (h5.trans (map_one e).symm)))

end Members

end CFSG.RankThree.PartOne.K1320
