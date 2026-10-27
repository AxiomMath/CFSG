module

public import CFSG.Walter.ReeOrder.JT.Section7B

public section

namespace CFSG.Walter.JT

open scoped IsMulCommutative Pointwise MatrixGroups

section Solvable

theorem isSolvable_of_normal {X : Type*} [Group X] (N : Subgroup X) [N.Normal]
    (h1 : Group.IsSolvable N) (h2 : Group.IsSolvable (X ⧸ N)) : Group.IsSolvable X :=
  Group.isSolvable_of_subgroup_quotient N

theorem isSolvable_of_card_eq_two_pow_mul_three_pow {X : Type*} [Group X] [Finite X] {a b : ℕ}
    (hX : Nat.card X = 2 ^ a * 3 ^ b) : Group.IsSolvable X := by
  let _ : Fintype X := Fintype.ofFinite X
  exact Burnside.finite_group_isSolvable_of_card_eq_prime_pow_mul_prime_pow Nat.prime_two
    Nat.prime_three (by norm_num) (by rw [← Nat.card_eq_fintype_card]; exact hX)

theorem isSolvable_of_le {X : Type*} [Group X] {H K : Subgroup X} (hHK : H ≤ K)
    (hK : Group.IsSolvable K) : Group.IsSolvable H :=
  Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective hHK)

theorem isSolvable_of_normal_odd {X : Type*} [Group X] [Finite X] (M : Subgroup X) [M.Normal]
    (hM : Odd (Nat.card M)) {a b : ℕ} (hX : Nat.card (X ⧸ M) = 2 ^ a * 3 ^ b) :
    Group.IsSolvable X :=
  isSolvable_of_normal M (CFSG.FeitThompson.isSolvable_of_odd_natCard _ hM)
    (isSolvable_of_card_eq_two_pow_mul_three_pow hX)

end Solvable

namespace Setup

variable {G : Type} [Group G] [Finite G] {h : JTHyp G} (s : Setup h) (hp : h.p ≠ 2)
include hp

theorem isSolvable_normalizer_T :
    Group.IsSolvable (Subgroup.normalizer (s.T : Set G)) := by
  set N := Subgroup.normalizer (s.T : Set G) with hNdef
  have hQN : s.Q ≤ N := s.Q_le_centralizer_T.trans s.centralizer_T_le_normalizer_T
  have hNQ : N ≤ Subgroup.normalizer (s.Q : Set G) := s.normalizer_T_le_normalizer_Q hp
  have hn : (s.Q.subgroupOf N).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hQN).mpr hNQ
  have hNcard : Nat.card N = 24 * Nat.card s.Q := by
    have h2 := Subgroup.relIndex_mul_card (Subgroup.centralizer (s.T : Set G)) N
    rw [s.relIndex_centralizer_T_normalizer_T hp, inf_eq_left.mpr
      s.centralizer_T_le_normalizer_T, s.card_centralizer_T hp] at h2
    omega
  have hQcard : Nat.card (s.Q.subgroupOf N) = Nat.card s.Q :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hQN).toEquiv
  have hcyc : IsCyclic (s.Q.subgroupOf N) := by
    have := s.isCyclic_Q hp
    exact isCyclic_of_surjective (Subgroup.subgroupOfEquivOfLe hQN).symm (MulEquiv.surjective _)
  have hsolvQ : Group.IsSolvable (s.Q.subgroupOf N) := by
    have := hcyc
    infer_instance
  refine isSolvable_of_normal (s.Q.subgroupOf N) hsolvQ
    (isSolvable_of_card_eq_two_pow_mul_three_pow (a := 3) (b := 1) ?_)
  have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup (s.Q.subgroupOf N)
  rw [hNcard, hQcard] at h1
  have hpos : 0 < Nat.card s.Q := Nat.card_pos
  norm_num
  nlinarith

end Setup

namespace JTHyp

variable {G : Type} [Group G] [Finite G] (h : JTHyp G) (hp3 : h.p = 3)
include hp3

theorem isSolvable_centralizer_of_mem_F
    (hS : SuzukiFourGroupTheorem) {y : G} (hyF : y ∈ h.F)
    {r : ℕ} (hr : r.Prime) (hr2 : r ≠ 2) (hy : orderOf y = r) :
    Group.IsSolvable (Subgroup.centralizer ({y} : Set G)) := by
  classical
  have hp := h.p_ne_two_of_eq_three hp3
  have hq8 := h.q_mod_eight_of_eq_three hp3
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hy1 : y ≠ 1 := fun h0 => by rw [h0, orderOf_one] at hy; exact hr.one_lt.ne' hy.symm
  have hCN : Subgroup.centralizer ({y} : Set G) ≤
      Subgroup.normalizer (Subgroup.zpowers y : Set G) := fun g hg =>
    mem_normalizer_zpowers_of_commute (Subgroup.mem_centralizer_singleton_iff.mp hg)
  by_cases hr3 : r = 3
  ·
    have hN4 := h.not_four_dvd_card_normalizer_of_orderOf_three hp3 hyF (by rw [hy, hr3])
    have hC4 : ¬ 4 ∣ Nat.card (Subgroup.centralizer ({y} : Set G)) := fun h4 =>
      hN4 (h4.trans (Subgroup.card_dvd_of_le hCN))
    set CY := Subgroup.centralizer ({y} : Set G) with hCY
    obtain ⟨Sy⟩ : Nonempty (Sylow 2 CY) := inferInstance
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp Sy.isPGroup'
    have hk1 : k ≤ 1 := by
      by_contra hk1
      apply hC4
      have := Subgroup.card_subgroup_dvd_card (Sy : Subgroup CY)
      rw [hk] at this
      exact (pow_dvd_pow 2 (by omega : 2 ≤ k)).trans this
    have hScyc : IsCyclic (Sy : Subgroup CY) := by
      interval_cases k
      · have : Subsingleton (Sy : Subgroup CY) := by
          rw [← Finite.card_le_one_iff_subsingleton, hk, pow_zero]
        exact isCyclic_of_subsingleton
      · exact isCyclic_of_prime_card (p := 2) (by rw [hk, pow_one])
    obtain ⟨-, -, -, ⟨hKn, hKodd, hKidx, -⟩, -⟩ :=
      cyclic_sylow_normal_odd_complement Sy hScyc
    exact isSolvable_of_normal_odd (pPrimeCore 2 CY) hKodd (a := k) (b := 0) (by
      rw [← Subgroup.index, hKidx, hk, pow_zero, mul_one])
  ·
    have hcop : Nat.Coprime (orderOf y) h.p := by
      rw [hy, hp3]
      exact (Nat.coprime_primes hr Nat.prime_three).mpr hr3
    obtain ⟨C, hCF, hCc, hyC, hCcard⟩ :=
      exists_cyclic_of_coprime h.F h.iso hp h.five_lt hyF hy1 hcop
    rw [← JTHyp.q_eq] at hCcard
    rcases hCcard with hC | hC
    ·
      obtain ⟨M, hMn, hModd, hMcard⟩ :=
        h.exists_normal_odd_normalizer_of_mem_torus hp3 hCF hCc hC hyC hy1
      have hsolv : Group.IsSolvable (Subgroup.normalizer (Subgroup.zpowers y : Set G)) := by
        refine isSolvable_of_normal_odd M hModd (a := 2) (b := 0) ?_
        have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup M
        rw [hMcard] at h1
        have hpos : 0 < Nat.card M := Nat.card_pos
        norm_num
        nlinarith
      exact isSolvable_of_le hCN hsolv
    ·
      obtain ⟨⟨v, hvC⟩, hv⟩ := exists_prime_orderOf_dvd_card' (G := C) 2
        (by omega : 2 ∣ Nat.card C)
      have hv2 : orderOf v = 2 := by rw [← hv, Subgroup.orderOf_mk]
      have hvF : v ∈ h.F := hCF hvC
      have hvv : v * v = 1 := by rw [← pow_two, ← hv2, pow_orderOf_eq_one]
      have hv1 : v ≠ 1 := fun h0 => by rw [h0, orderOf_one] at hv2; omega
      have htv : Commute h.t v := (h.commute_of_mem_F hvF).symm
      have htne : h.t ≠ v := fun h0 => h.t_not_mem (h0 ▸ hvF)
      set T := GorensteinWalter.kleinFourOfCommutingInvolutions h.t v h.t_mul_t hvv htv
        with hTdef
      have hT : IsKleinFour T := GorensteinWalter.isKleinFour_kleinFourOfCommutingInvolutions
        _ _ _ _ h.t_ne_one hv1 htne htv
      have hmemT : ∀ z, z ∈ T ↔ z = h.t * v ∨ z = h.t ∨ z = v ∨ z = 1 := fun z => Iff.rfl
      have htT : h.t ∈ T := (hmemT _).mpr (Or.inr (Or.inl rfl))
      have hT2 : IsPGroup 2 T := IsPGroup.of_card (n := 2) (by rw [hT.card_four]; norm_num)
      obtain ⟨S', hS'⟩ := hT2.exists_le_sylow
      let s : Setup h := ⟨S', hS' htT, T, hS', hT, htT⟩
      have hCab : ∀ a ∈ C, ∀ b ∈ C, a * b = b * a := fun a ha b hb =>
        congrArg Subtype.val ((IsCyclic.commGroup (α := C)).mul_comm ⟨a, ha⟩ ⟨b, hb⟩)
      have hyT : y ∈ Subgroup.centralizer (s.T : Set G) := by
        rw [Subgroup.mem_centralizer_iff]
        intro z hz
        have hty : h.t * y = y * h.t := (h.commute_of_mem_F hyF).symm
        have hvy : v * y = y * v := hCab v hvC y hyC
        rcases (hmemT z).mp hz with rfl | rfl | rfl | rfl
        · rw [mul_assoc, hvy, ← mul_assoc, hty, mul_assoc]
        · exact hty
        · exact hvy
        · rw [one_mul, mul_one]
      have hyodd : Odd (orderOf y) := by rw [hy]; exact hr.odd_of_ne_two hr2
      have hyQ : y ∈ s.Q := (s.mem_Q_iff hp).mpr ⟨hyT, hyodd⟩
      have hR : Subgroup.zpowers y ≤ s.Q := (Subgroup.zpowers_le).mpr hyQ
      have hR1 : Subgroup.zpowers y ≠ ⊥ := by rw [Ne, Subgroup.zpowers_eq_bot]; exact hy1
      have hNy : Subgroup.normalizer (Subgroup.zpowers y : Set G) =
          Subgroup.normalizer (s.T : Set G) := by
        rw [s.lemma_4_3 hp hS hR hR1, s.lemma_7_1_b hp3 hS]
      exact isSolvable_of_le (hCN.trans hNy.le) (s.isSolvable_normalizer_T hp)

theorem lemma_7_7_a
    (hS : SuzukiFourGroupTheorem) {x : G} (hx : x ^ 2 ≠ 1) :
    Group.IsSolvable (Subgroup.centralizer ({x} : Set G)) := by
  classical
  have hp := h.p_ne_two_of_eq_three hp3
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨r, hr, hr2, hrx⟩ : ∃ r : ℕ, r.Prime ∧ r ≠ 2 ∧ r ∣ orderOf x := by
    by_contra hcon
    push Not at hcon
    have h2 : IsPGroup 2 (Subgroup.zpowers x) := by
      refine IsPGroup.of_card (n := (orderOf x).primeFactorsList.length) ?_
      rw [Nat.card_zpowers]
      exact Nat.eq_prime_pow_of_unique_prime_dvd (orderOf_pos x).ne'
        (fun {d} hd hdx => by
          by_contra hd2
          exact hcon d hd hd2 hdx)
    have hxx := h.mul_self_of_isPGroup_two hp3 h2 (Subgroup.mem_zpowers x)
    exact hx (by rw [pow_two]; exact hxx)
  set y := x ^ (orderOf x / r) with hydef
  have hy : orderOf y = r := by
    rw [hydef, orderOf_pow_of_dvd (Nat.div_pos (Nat.le_of_dvd (orderOf_pos x) hrx)
      hr.pos).ne' (Nat.div_dvd_of_dvd hrx), Nat.div_div_self hrx (orderOf_pos x).ne']
  have hCxy : Subgroup.centralizer ({x} : Set G) ≤ Subgroup.centralizer ({y} : Set G) :=
    fun g hg => Subgroup.mem_centralizer_singleton_iff.mpr
      ((Commute.pow_right (Subgroup.mem_centralizer_singleton_iff.mp hg) _).eq)
  refine isSolvable_of_le hCxy ?_
  by_cases hodd : Odd (Nat.card (Subgroup.centralizer ({y} : Set G)))
  · exact CFSG.FeitThompson.isSolvable_of_odd_natCard _ hodd
  rw [Nat.not_odd_iff_even] at hodd
  obtain ⟨⟨u, huC⟩, hu⟩ := exists_prime_orderOf_dvd_card' (G := Subgroup.centralizer
    ({y} : Set G)) 2 (even_iff_two_dvd.mp hodd)
  have hu2 : orderOf u = 2 := by rw [← hu, Subgroup.orderOf_mk]
  obtain ⟨a, ha⟩ := h.exists_conj_eq_t hp hu2
  set y' := a * y * a⁻¹ with hy'def
  have hy' : orderOf y' = r := by rw [hy'def, ← MulAut.conj_apply, MulEquiv.orderOf_eq, hy]
  have hyu : y * u = u * y := (Subgroup.mem_centralizer_singleton_iff.mp huC).symm
  have hy't : y' ∈ Subgroup.centralizer ({h.t} : Set G) := by
    rw [Subgroup.mem_centralizer_singleton_iff, ← ha, hy'def]
    calc a * y * a⁻¹ * (a * u * a⁻¹) = a * (y * u) * a⁻¹ := by group
      _ = a * (u * y) * a⁻¹ := by rw [hyu]
      _ = a * u * a⁻¹ * (a * y * a⁻¹) := by group
  have hy'F : y' ∈ h.F := h.mem_F_of_odd hy't (by rw [hy']; exact hr.odd_of_ne_two hr2)
  have hsolv := h.isSolvable_centralizer_of_mem_F hp3 hS hy'F hr hr2 hy'
  have hmap := map_centralizer_singleton_of_injective (MulAut.conj a).toMonoidHom
    (MulAut.conj a).injective y
  rw [MonoidHom.range_eq_top.mpr (MulAut.conj a).surjective, top_inf_eq] at hmap
  have e : Subgroup.centralizer ({y} : Set G) ≃* Subgroup.centralizer ({y'} : Set G) :=
    ((Subgroup.centralizer ({y} : Set G)).equivMapOfInjective _ (MulAut.conj a).injective).trans
      (MulEquiv.subgroupCongr hmap)
  exact Group.isSolvable_of_isSolvable_injective (f := e.toMonoidHom) e.injective

end JTHyp

end CFSG.Walter.JT
