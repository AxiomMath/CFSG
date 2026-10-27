module

public import CFSG.Milestones.ASVolI.A3Spor.Core
public import CFSG.Quasithin.H13.NQCatT513J1
public import CFSG.Sporadic.Schreier.J1OddCore
public import CFSG.GroupTheory.SmallOrderNotSimple
import CFSG.Blueprint.NativeSporadic
public import CFSG.Quasithin.Vol2.Ch5Sec1L34FiveA7
public import CFSG.Quasithin.Vol2.Ch6Sec1Lem4SpA
public import CFSG.Walter.J1Props
public import CFSG.Walter.J1Recog
public import CFSG.Walter.W67.Statements

public section

namespace CFSG.ASVolI

open CFSG.QuasithinUnique CFSG.QuasithinUnique.Ch1.SporLat CFSG.Quasithin.A312S
  CFSG.Quasithin.E2P.SporB

theorem burnsideA315s_sylow_card56 {G : Type*} [Group G] [Finite G] (hG : Nat.card G = 56) :
    Subsingleton (Sylow 7 G) ∨ Subsingleton (Sylow 2 G) := by
  classical
  have : Fintype G := Fintype.ofFinite G
  have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hf7 : (Nat.card G).factorization 7 = 1 := by
    rw [hG]
    exact CFSG.GroupTheory.factorization_eq_of_pow_dvd (by norm_num) (by norm_num) (by norm_num)
      (by norm_num)
  have hf2 : (Nat.card G).factorization 2 = 3 := by
    rw [hG]
    exact CFSG.GroupTheory.factorization_eq_of_pow_dvd (by norm_num) (by norm_num) (by norm_num)
      (by norm_num)
  have hn7 : Nat.card (Sylow 7 G) = 1 ∨ Nat.card (Sylow 7 G) = 8 := by
    obtain ⟨hdvd, hmod⟩ := CFSG.GroupTheory.card_sylow_dvd_and_modEq (p := 7) (G := G)
      (CFSG.GroupTheory.index_sylow_eq (m := 8) hf7 (by rw [hG]; norm_num))
    have hpos : 0 < Nat.card (Sylow 7 G) := Nat.card_pos
    have hle := Nat.le_of_dvd (by norm_num) hdvd
    generalize Nat.card (Sylow 7 G) = n at hdvd hmod hpos hle ⊢
    interval_cases n <;> first | (left; rfl) | (right; rfl) | (exfalso; revert hdvd hmod; decide)
  rcases hn7 with h7 | h7
  · exact Or.inl (Nat.card_eq_one_iff_unique.1 h7).1
  right
  have : Fintype (Sylow 7 G) := Fintype.ofFinite _
  have hc7 := CFSG.GroupTheory.card_filter_orderOf_eq_prime (G := G) (p := 7) hf7
  rw [Fintype.card_eq_nat_card, h7] at hc7
  have hcard2 : ∀ P : Sylow 2 G, Nat.card (P : Subgroup G) = 8 := fun P => by
    rw [P.card_eq_multiplicity, hf2]
    norm_num
  have hcompl : ∀ P : Sylow 2 G,
      ((P : Subgroup G) : Set G).toFinset = Finset.univ.filter fun g : G => ¬ orderOf g = 7 := by
    intro P
    have hsplit := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset G))
      (fun g : G => orderOf g = 7)
    rw [hc7, Finset.card_univ, ← Nat.card_eq_fintype_card, hG] at hsplit
    apply Finset.eq_of_subset_of_card_le
    · intro g hg
      rw [Set.mem_toFinset] at hg
      rw [Finset.mem_filter]
      refine ⟨Finset.mem_univ g, fun h7' => ?_⟩
      have hdvd : orderOf g ∣ 8 := by
        rw [← hcard2 P, ← Subgroup.orderOf_mk g hg]
        exact orderOf_dvd_natCard _
      rw [h7'] at hdvd
      exact absurd hdvd (by norm_num)
    · rw [Set.toFinset_card, ← Nat.card_eq_fintype_card]
      change _ ≤ Nat.card (P : Subgroup G)
      rw [hcard2 P]
      omega
  exact ⟨fun P P' => Sylow.ext (SetLike.coe_injective (by
    rw [← Set.toFinset_inj, hcompl P, hcompl P']))⟩

theorem burnsideA315s_exists_involution_comm {G : Type*} [Group G] [Finite G]
    (hG : Nat.card G = 56) {P : Subgroup G} [P.Normal] (hP : Nat.card P = 7) :
    ∃ t b : G, orderOf t = 2 ∧ orderOf b = 7 ∧ t * b = b * t := by
  classical
  have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨b, hb⟩ := exists_prime_orderOf_dvd_card' (G := ↥P) 7 (by rw [hP])
  set C := Subgroup.centralizer ({(b : G)} : Set G) with hC
  have hPC : P ≤ C := by
    intro x hx
    rw [hC, Subgroup.mem_centralizer_singleton_iff]
    haveI : IsCyclic ↥P := isCyclic_of_prime_card hP
    have := (IsCyclic.commGroup (α := ↥P)).mul_comm ⟨x, hx⟩ b
    have := congrArg Subtype.val this
    simpa using this
  have h7C : 7 ∣ Nat.card C := hP ▸ Subgroup.card_dvd_of_le hPC
  have horb : MulAction.orbit (ConjAct G) (b : G) ⊆ (P : Set G) \ {1} := by
    rintro _ ⟨c, rfl⟩
    dsimp only
    refine ⟨?_, ?_⟩
    · rw [SetLike.mem_coe, ConjAct.smul_def]
      exact Subgroup.Normal.conj_mem inferInstance _ b.2 _
    · intro h1
      rw [Set.mem_singleton_iff, ConjAct.smul_def] at h1
      have : (b : G) = 1 := by
        have h2 := congrArg (fun y => (ConjAct.ofConjAct c)⁻¹ * y * ConjAct.ofConjAct c) h1
        simpa [mul_assoc] using h2
      have hb1 : (b : ↥P) = 1 := Subtype.ext this
      rw [hb1, orderOf_one] at hb
      exact absurd hb (by norm_num)
  have hfin : (P : Set G).Finite := Set.toFinite _
  have hncP : ((P : Set G) \ {1}).ncard = 6 := by
    rw [Set.ncard_diff_singleton_of_mem P.one_mem, ← Nat.card_coe_set_eq]
    change Nat.card ↥P - 1 = 6
    rw [hP]
  have hidx : (MulAction.stabilizer (ConjAct G) (b : G)).index ≤ 6 := by
    rw [MulAction.index_stabilizer]
    rw [← hncP]
    exact Set.ncard_le_ncard horb (hfin.diff)
  have hcardC : Nat.card C = Nat.card (MulAction.stabilizer (ConjAct G) (b : G)) :=
    Subgroup.nat_card_centralizer_nat_card_stabilizer _
  have hmul : Nat.card (MulAction.stabilizer (ConjAct G) (b : G)) *
      (MulAction.stabilizer (ConjAct G) (b : G)).index = 56 := by
    rw [Subgroup.card_mul_index, ← hG]
    exact Nat.card_congr ConjAct.toConjAct.toEquiv.symm
  have h2C : 2 ∣ Nat.card C := by
    rw [hcardC] at h7C ⊢
    generalize Nat.card (MulAction.stabilizer (ConjAct G) (b : G)) = c at h7C hmul ⊢
    generalize (MulAction.stabilizer (ConjAct G) (b : G)).index = i at hidx hmul
    interval_cases i <;> omega
  obtain ⟨t, ht⟩ := exists_prime_orderOf_dvd_card' (G := ↥C) 2 h2C
  refine ⟨t, b, by rw [Subgroup.orderOf_coe, ht], by rw [Subgroup.orderOf_coe, hb], ?_⟩
  have := Subgroup.mem_centralizer_singleton_iff.1 t.2
  exact this

theorem burnsideA315s_normalizer_of_card56 {X : Type} [Group X] [Finite X] {S B H : Subgroup X}
    (hS : Nat.card ↥S = 8) (hB : Nat.card ↥B = 7) (hSH : S ≤ H) (hBH : B ≤ H)
    (hH : Nat.card ↥H = 56) (hinv : ∀ t b : X, orderOf t = 2 → orderOf b = 7 → t * b ≠ b * t) :
    H ≤ Subgroup.normalizer (S : Set X) := by
  have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hS' : Nat.card ↥(S.subgroupOf H) = 8 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hSH).toEquiv, hS]
  have hB' : Nat.card ↥(B.subgroupOf H) = 7 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hBH).toEquiv, hB]
  rcases burnsideA315s_sylow_card56 hH with h7 | h2
  · exfalso
    have hBp : IsPGroup 7 ↥(B.subgroupOf H) := IsPGroup.of_card (n := 1) (by rw [hB', pow_one])
    have hBi : ¬ 7 ∣ (B.subgroupOf H).index := by
      have := (B.subgroupOf H).card_mul_index
      rw [hB', hH] at this
      have hi : (B.subgroupOf H).index = 8 := by omega
      rw [hi]
      norm_num
    let P : Sylow 7 ↥H := hBp.toSylow hBi
    haveI : (B.subgroupOf H).Normal := by
      have := P.normal_of_subsingleton
      exact this
    obtain ⟨t, b, ht, hb, htb⟩ := burnsideA315s_exists_involution_comm hH hB'
    apply hinv t b (by rw [Subgroup.orderOf_coe, ht]) (by rw [Subgroup.orderOf_coe, hb])
    have := congrArg Subtype.val htb
    simpa using this
  · have hSp : IsPGroup 2 ↥(S.subgroupOf H) := IsPGroup.of_card (n := 3) (by rw [hS']; norm_num)
    have hSi : ¬ 2 ∣ (S.subgroupOf H).index := by
      have := (S.subgroupOf H).card_mul_index
      rw [hS', hH] at this
      have hi : (S.subgroupOf H).index = 7 := by omega
      rw [hi]
      norm_num
    let P : Sylow 2 ↥H := hSp.toSylow hSi
    haveI : (S.subgroupOf H).Normal := by
      have := P.normal_of_subsingleton
      exact this
    exact (Subgroup.normal_subgroupOf_iff_le_normalizer hSH).1 inferInstance

theorem burnsideA315s_config_J1Grp
    {S B : Subgroup ↥CFSG.Sporadic.J1.J} (hc : burnsideA315x_Config ↥CFSG.Sporadic.J1.J S B) :
    Nat.card ↥B = 7 ∧ B ≤ Subgroup.normalizer (S : Set ↥CFSG.Sporadic.J1.J) := by
  classical
  have hS₀ : Nat.card ↥j1S = 2 ^ 3 :=
    CFSG.Quasithin.H13.NQCat.T513P.card_of_isSylowTwoOf_top j1_sylow (m := 21945)
      (by rw [CFSG.Sporadic.J1.card_J]; norm_num) (by decide)
  have hall := j1_all
  have hcard : ∀ j < (#[1, 15, 15, 15, 15, 15, 15, 7, 3, 15, 3, 3, 3, 3, 3, 3, 21] :
      Array ℕ).size, Nat.card ↥(j1Y j) =
        (#[1, 15, 15, 15, 15, 15, 15, 7, 3, 15, 3, 3, 3, 3, 3, 3, 21] : Array ℕ)[j]! *
          Nat.card ↥j1S := fun j hj => by
    rw [hS₀]
    exact j1_Y_card hj
  have hpos : 0 < Nat.card ↥j1S := Nat.card_pos
  have hΓ : Nat.card ↥CFSG.Sporadic.J1.J = 21945 * Nat.card ↥j1S := by
    rw [CFSG.Sporadic.J1.card_J, hS₀]
    norm_num
  have hidx : ∀ Z : Subgroup ↥CFSG.Sporadic.J1.J, j1S ≤ Z → ∀ m : ℕ,
      Nat.card ↥Z = m * Nat.card ↥j1S → m ∈ ({1, 3, 7, 15, 21, 21945} : Finset ℕ) := by
    intro Z hZ m hm
    have hL : ∀ j < (#[1, 15, 15, 15, 15, 15, 15, 7, 3, 15, 3, 3, 3, 3, 3, 3, 21] :
        Array ℕ).size, (#[1, 15, 15, 15, 15, 15, 15, 7, 3, 15, 3, 3, 3, 3, 3, 3, 21] :
          Array ℕ)[j]! ∈ ({1, 3, 7, 15, 21, 21945} : Finset ℕ) := by decide
    rcases CFSG.Quasithin.H13.NQCat.T513P.index_of_list hall hcard hZ hm with ⟨j, hj, rfl⟩ | h
    · exact hL j hj
    · rw [hΓ] at h
      rw [← Nat.eq_of_mul_eq_mul_right hpos h]
      decide
  have h7 : ∀ r : ℕ, r.Prime → 5 ≤ r → r ∣ Nat.card ↥B → r = 7 := by
    intro r hr hr5 hrB
    obtain ⟨g, K, -, -, -, hS₀K, -, m, hm, hrm, hpm⟩ :=
      burnsideA315s_hall_index hc j1_sylow hr (by omega) hrB
    have hmem := hidx _ hS₀K m hm
    simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
    rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
    · exact absurd (Nat.dvd_one.1 hrm) hr.one_lt.ne'
    · have := hpm 3 Nat.prime_three dvd_rfl; omega
    · exact (Nat.prime_dvd_prime_iff_eq hr (by norm_num)).1 hrm
    · have := hpm 3 Nat.prime_three (by norm_num); omega
    · have := hpm 3 Nat.prime_three (by norm_num); omega
    · have := hpm 3 Nat.prime_three (by norm_num); omega
  have hBdvd : Nat.card ↥B ∣ 21945 := by
    have h1 : Nat.card ↥B ∣ 8 * 21945 := by
      have := Subgroup.card_subgroup_dvd_card B
      rw [hΓ, hS₀] at this
      rw [show (8 : ℕ) * 21945 = 21945 * 2 ^ 3 by norm_num]
      exact this
    have hcop : Nat.Coprime (Nat.card ↥B) 8 := by
      have := Nat.Coprime.pow_right 3 (Nat.coprime_two_right.2 hc.odd)
      simpa using this
    exact hcop.dvd_of_dvd_mul_left h1
  have hB21 : Nat.card ↥B ∣ 21 := by
    have hc5 : Nat.Coprime (Nat.card ↥B) 5 :=
      (Nat.coprime_comm.1 ((Nat.Prime.coprime_iff_not_dvd (by norm_num)).2
        (fun h => by have := h7 5 (by norm_num) le_rfl h; omega)))
    have hc11 : Nat.Coprime (Nat.card ↥B) 11 :=
      (Nat.coprime_comm.1 ((Nat.Prime.coprime_iff_not_dvd (by norm_num)).2
        (fun h => by have := h7 11 (by norm_num) (by norm_num) h; omega)))
    have hc19 : Nat.Coprime (Nat.card ↥B) 19 :=
      (Nat.coprime_comm.1 ((Nat.Prime.coprime_iff_not_dvd (by norm_num)).2
        (fun h => by have := h7 19 (by norm_num) (by norm_num) h; omega)))
    have hcop : Nat.Coprime (Nat.card ↥B) (5 * 11 * 19) := (hc5.mul_right hc11).mul_right hc19
    rw [show (21945 : ℕ) = 21 * (5 * 11 * 19) by norm_num] at hBdvd
    exact hcop.dvd_of_dvd_mul_right hBdvd
  have hBcases : Nat.card ↥B = 1 ∨ Nat.card ↥B = 3 ∨ Nat.card ↥B = 7 ∨ Nat.card ↥B = 21 := by
    have : Nat.card ↥B ∈ Nat.divisors 21 := Nat.mem_divisors.2 ⟨hB21, by norm_num⟩
    have hd : Nat.divisors 21 = {1, 3, 7, 21} := by decide
    rw [hd] at this
    simpa using this
  rcases hBcases with h1 | h3 | h7' | h21
  · exact absurd (IsPGroup.of_card (p := 3) (n := 0) (by rw [h1, pow_zero])) hc.not3
  · exact absurd (IsPGroup.of_card (p := 3) (n := 1) (by rw [h3, pow_one])) hc.not3
  · refine ⟨h7', ?_⟩
    have hSc : Nat.card ↥S = 8 := by
      rw [CFSG.Quasithin.H13.NQCat.T513P.card_of_isSylowTwoOf_top hc.sylow (a := 3) (m := 21945)
        (by rw [CFSG.Sporadic.J1.card_J]; norm_num) (by decide)]
      norm_num
    obtain ⟨hSH, hHcard⟩ := hc.sup_card
    have hH : Nat.card ↥(B ⊔ S) = 56 := by rw [hHcard, h7', hSc]
    have hinv : ∀ t b : ↥CFSG.Sporadic.J1.J, orderOf t = 2 → orderOf b = 7 → t * b ≠ b * t := by
      intro t b ht hb htb
      have hcen := (CFSG.Sporadic.Schreier.ctugs_j1_involution_centralizer_odd_core_free
        ⟨CFSG.Sporadic.J1.nativeEquiv.symm⟩ t ht).1
      have hbC : b ∈ Subgroup.centralizer ({t} : Set ↥CFSG.Sporadic.J1.J) := by
        rw [Subgroup.mem_centralizer_singleton_iff]
        exact htb.symm
      have := Subgroup.orderOf_dvd_natCard _ hbC
      rw [hb, hcen] at this
      exact absurd this (by norm_num)
    exact le_sup_left.trans (burnsideA315s_normalizer_of_card56 hSc h7' le_sup_right le_sup_left
      hH hinv)
  · exfalso
    obtain ⟨z, -, hz⟩ := hc.exists_order_mul (r := 3) (s := 7) Nat.prime_three (by norm_num)
      (by norm_num) (by rw [h21]; norm_num) (by rw [h21]; norm_num)
    exact CFSG.Quasithin.H13.NQCat.T513P.j1J_no_order_21 z hz

end CFSG.ASVolI
