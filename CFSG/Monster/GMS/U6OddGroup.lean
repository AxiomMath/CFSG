module

public import Mathlib.GroupTheory.Transfer
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.SubgroupConjAction

public section

namespace CFSG.Monster.GMS.U6Odd

open Subgroup

structure U6Hyp (U : Type*) [Group U] : Prop where
  card : Nat.card U = 2 ^ 15 * 3 ^ 6 * 5 * 7 * 11
  norm5 : ∀ P : Subgroup U, Nat.card P = 5 → ∀ N : Subgroup U, N ≤ normalizer (P : Set U) →
    Odd (Nat.card N) → Nat.card N ∣ 15
  norm7 : ∀ P : Subgroup U, Nat.card P = 7 → ∀ N : Subgroup U, N ≤ normalizer (P : Set U) →
    Odd (Nat.card N) → Nat.card N ∣ 21
  norm11 : ∀ P : Subgroup U, Nat.card P = 11 → ∀ N : Subgroup U, N ≤ normalizer (P : Set U) →
    Odd (Nat.card N) → Nat.card N ∣ 55
  abelian3 : ∀ A : Subgroup U, IsPGroup 3 A → (∀ a ∈ A, ∀ b ∈ A, a * b = b * a) →
    Nat.card A < 243

section Arith

theorem arith_main : ∀ y ∈ Nat.divisors 729, ∀ z ∈ Nat.divisors 385, 3000 ≤ y * z →
    (5 ∣ y * z → ∃ k ∈ Nat.divisors 15, 5 ∣ k ∧ ((y * z) / k) % 5 = 1 ∧ k ∣ y * z) →
    (7 ∣ y * z → ∃ k ∈ Nat.divisors 21, 7 ∣ k ∧ ((y * z) / k) % 7 = 1 ∧ k ∣ y * z) →
    (11 ∣ y * z → ∃ k ∈ Nat.divisors 55, 11 ∣ k ∧ ((y * z) / k) % 11 = 1 ∧ k ∣ y * z) →
    y * z = 5103 ∨ y * z = 13365 := by
  decide +kernel

end Arith

section Centre

variable {L : Type*} [Group L] [Finite L]

omit [Finite L] in
theorem map_center_normalized (X : Subgroup L) {g : L} (hg : g ∈ normalizer (X : Set L)) :
    ∀ z ∈ (Subgroup.center X).map X.subtype,
      g * z * g⁻¹ ∈ (Subgroup.center X).map X.subtype := by
  intro z hz
  obtain ⟨c, hc, rfl⟩ := Subgroup.mem_map.1 hz
  have hc' : ∀ x : X, x * c = c * x := fun x => Subgroup.mem_center_iff.1 hc x
  have hX : ∀ x : L, x ∈ X ↔ g * x * g⁻¹ ∈ X := fun x => Subgroup.mem_normalizer_iff.1 hg x
  have hX' : ∀ x : L, x ∈ X ↔ g⁻¹ * x * g⁻¹⁻¹ ∈ X := fun x =>
    Subgroup.mem_normalizer_iff.1 ((Subgroup.inv_mem_iff _).2 hg) x
  have hcX : g * ((c : X) : L) * g⁻¹ ∈ X := (hX _).1 c.2
  refine Subgroup.mem_map.2 ⟨⟨g * ((c : X) : L) * g⁻¹, hcX⟩, ?_, rfl⟩
  rw [Subgroup.mem_center_iff]
  intro x
  have hx : g⁻¹ * (x : L) * g ∈ X := by
    have := (hX' (x : L)).1 x.2
    simpa using this
  have h1 := congrArg (fun y : X => (y : L)) (hc' ⟨g⁻¹ * (x : L) * g, hx⟩)
  simp only [Subgroup.coe_mul] at h1
  apply Subtype.ext
  simp only [Subgroup.coe_mul]
  calc (x : L) * (g * ((c : X) : L) * g⁻¹)
      = g * (g⁻¹ * (x : L) * g * ((c : X) : L)) * g⁻¹ := by group
    _ = g * (((c : X) : L) * (g⁻¹ * (x : L) * g)) * g⁻¹ := by rw [h1]
    _ = g * ((c : X) : L) * g⁻¹ * (x : L) := by group

theorem fpf_abelian (X : Subgroup L) (g : L) {q e : ℕ} [hq : Fact q.Prime]
    (hX : Nat.card X = 3 ^ e) (he : 1 ≤ e) (hg : g ∈ normalizer (X : Set L))
    (hgq : orderOf g = q) (hfix : ∀ x ∈ X, g * x = x * g → x = 1)
    (hmod : ∀ j, 1 ≤ j → j ≤ e → 3 ^ j % q = 1 → j = e) :
    ∀ a ∈ X, ∀ b ∈ X, a * b = b * a := by
  set Z : Subgroup L := (Subgroup.center X).map X.subtype with hZ
  have hZX : Z ≤ X := by
    intro z hz
    obtain ⟨c, -, rfl⟩ := Subgroup.mem_map.1 hz
    exact c.2
  have hZcard : Nat.card Z = Nat.card (Subgroup.center X) :=
    Nat.card_congr (Subgroup.equivMapOfInjective _ X.subtype X.subtype_injective).symm.toEquiv
  have h3 : IsPGroup 3 X := IsPGroup.of_card hX
  have hnt : Nontrivial X := by
    rw [← Finite.one_lt_card_iff_nontrivial, hX]
    exact Nat.one_lt_pow (by omega) (by norm_num)
  have hZnt : Nontrivial (Subgroup.center X) := h3.center_nontrivial
  have hZdvd : Nat.card Z ∣ 3 ^ e := by
    rw [hZcard, ← hX]
    exact Subgroup.card_subgroup_dvd_card _
  obtain ⟨j, hj, hZj⟩ := (Nat.dvd_prime_pow Nat.prime_three).1 hZdvd
  have hj1 : 1 ≤ j := by
    by_contra h0
    have h0' : j = 0 := by omega
    rw [h0', pow_zero] at hZj
    have hlt : 1 < Nat.card (Subgroup.center X) := Finite.one_lt_card_iff_nontrivial.2 hZnt
    omega
  have hg' : g⁻¹ ∈ normalizer (X : Set L) := (Subgroup.inv_mem_iff _).2 hg
  have hgZ : zpowers g ≤ normalizer (Z : Set L) := by
    rw [zpowers_le]
    refine Subgroup.mem_normalizer_iff.2 fun z => ⟨map_center_normalized X hg z, fun hz => ?_⟩
    have := map_center_normalized X hg' _ hz
    rwa [show g⁻¹ * (g * z * g⁻¹) * g⁻¹⁻¹ = z by group] at this
  let _ := Subgroup.conjMulDistribMulActionOfLeNormalizer (zpowers g) Z hgZ
  have hPcard : Nat.card (zpowers g) = q ^ 1 := by
    rw [Nat.card_zpowers, hgq, pow_one]
  have hPp : IsPGroup q (zpowers g) := IsPGroup.of_card hPcard
  have hmodq := hPp.card_modEq_card_fixedPoints Z
  have hfx : ∀ a : MulAction.fixedPoints (zpowers g) Z, (a : Z) = 1 := by
    intro a
    have ha := a.2 ⟨g, mem_zpowers g⟩
    have hcomm : g * ((a : Z) : L) = ((a : Z) : L) * g := by
      have h1 : g * ((a : Z) : L) * g⁻¹ = ((a : Z) : L) := congrArg (fun y : Z => (y : L)) ha
      exact mul_inv_eq_iff_eq_mul.1 h1
    exact Subtype.ext (hfix _ (hZX (a : Z).2) hcomm)
  have hfixcard : Nat.card (MulAction.fixedPoints (zpowers g) Z) = 1 := by
    rw [Nat.card_eq_one_iff_unique]
    refine ⟨⟨fun a b => Subtype.ext (by rw [hfx a, hfx b])⟩, ⟨⟨1, fun y => smul_one y⟩⟩⟩
  rw [hfixcard, hZj] at hmodq
  have hq1 : 1 < q := hq.out.one_lt
  have h3j : 3 ^ j % q = 1 := by
    have := hmodq
    unfold Nat.ModEq at this
    rwa [Nat.mod_eq_of_lt hq1] at this
  have hje : j = e := hmod j hj1 hj h3j
  have hZeq : Z = X := by
    refine Subgroup.eq_of_le_of_card_ge hZX ?_
    have : Nat.card Z = Nat.card X := by rw [hZj, hje, hX]
    exact this.ge
  intro a ha b hb
  rw [← hZeq] at ha
  obtain ⟨c, hc, rfl⟩ := Subgroup.mem_map.1 ha
  have := Subgroup.mem_center_iff.1 hc ⟨b, hb⟩
  exact (congrArg (fun y : X => (y : L)) this).symm

end Centre

section Burnside

variable {M : Type*} [Group M] [Finite M]

theorem normalizer_le_centralizer_of_coprime (P : Subgroup M) {p : ℕ} (hp : p.Prime)
    (hP : Nat.card P = p)
    (hcop : Nat.Coprime (Nat.card (normalizer ((P : Subgroup M) : Set M))) (p - 1)) :
    normalizer ((P : Subgroup M) : Set M) ≤ centralizer ((P : Subgroup M) : Set M) := by
  have : Fact p.Prime := ⟨hp⟩
  have : IsCyclic P := isCyclic_of_prime_card hP
  have key := card_dvd_of_injective _ (QuotientGroup.kerLift_injective P.normalizerMonoidHom)
  rw [normalizerMonoidHom_ker, ← index, ← relIndex] at key
  have h1 : (centralizer ((P : Subgroup M) : Set M)).relIndex
      (normalizer ((P : Subgroup M) : Set M)) ∣ p - 1 := by
    refine key.trans ?_
    rw [IsCyclic.card_mulAut, hP, Nat.totient_prime hp]
  have h2 : (centralizer ((P : Subgroup M) : Set M)).relIndex
      (normalizer ((P : Subgroup M) : Set M)) ∣
        Nat.card (normalizer ((P : Subgroup M) : Set M)) := Subgroup.relIndex_dvd_card _ _
  exact relIndex_eq_one.mp (Nat.eq_one_of_dvd_coprimes hcop h2 h1)

omit [Finite M] in
theorem normalizer_le_centralizer_of_self (P : Subgroup M) {p : ℕ} (hp : p.Prime)
    (hP : Nat.card P = p) (hN : normalizer ((P : Subgroup M) : Set M) = P) :
    normalizer ((P : Subgroup M) : Set M) ≤ centralizer ((P : Subgroup M) : Set M) := by
  have : Fact p.Prime := ⟨hp⟩
  have : IsCyclic P := isCyclic_of_prime_card hP
  rw [hN]
  have : IsMulCommutative P := inferInstance
  exact Subgroup.le_centralizer_iff_isMulCommutative.2 this

theorem exists_normal_complement {p : ℕ} [Fact p.Prime] (P : Sylow p M)
    (hP : normalizer ((P : Subgroup M) : Set M) ≤ centralizer ((P : Subgroup M) : Set M)) :
    ∃ K : Subgroup M, K.Normal ∧ Nat.card K * Nat.card P = Nat.card M := by
  have := MonoidHom.ker_transferSylow_isComplement' P hP
  exact ⟨_, MonoidHom.normal_ker _, this.card_mul_card⟩

theorem exists_generator (P : Subgroup M) {p : ℕ} (hp : p.Prime) (hP : Nat.card P = p) :
    ∃ g ∈ P, orderOf g = p ∧ P = zpowers g := by
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := P) p (by rw [hP])
  refine ⟨(x : M), x.2, by rw [Subgroup.orderOf_coe, hx], ?_⟩
  refine (Subgroup.eq_of_le_of_card_ge (zpowers_le.2 x.2) ?_).symm
  rw [Nat.card_zpowers, Subgroup.orderOf_coe, hx, hP]

omit [Finite M] in
theorem eq_one_of_commute_of_selfNormalizing {P K : Subgroup M} {g : M} (hPg : P = zpowers g)
    (hN : normalizer ((P : Subgroup M) : Set M) = P)
    (hcop : Nat.Coprime (Nat.card P) (Nat.card K)) :
    ∀ x ∈ K, g * x = x * g → x = 1 := by
  intro x hxK hx
  have hxC : x ∈ centralizer ((P : Subgroup M) : Set M) := by
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    rw [hPg] at hh
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.1 hh
    exact ((show Commute g x from hx).zpow_left i).eq
  have hxP : x ∈ P := by
    rw [← hN]
    exact Subgroup.centralizer_le_normalizer ((P : Subgroup M) : Set M) hxC
  exact Subgroup.disjoint_def.1 (Subgroup.disjoint_of_coprime_natCard hcop) hxP hxK

end Burnside

section SylowData

theorem sylow_card_eq_prime {G : Type*} [Group G] [Finite G] {p : ℕ} [hp : Fact p.Prime]
    (P : Sylow p G) (hpG : p ∣ Nat.card G) (hp2 : ¬ p ^ 2 ∣ Nat.card G) : Nat.card P = p := by
  have hPmult := P.card_eq_multiplicity
  have hPdvd : Nat.card P ∣ Nat.card G := Subgroup.card_subgroup_dvd_card _
  have hpP : p ∣ Nat.card P := P.dvd_card_of_dvd_card hpG
  rcases hPmult' : (Nat.card G).factorization p with _ | _ | e
  · rw [hPmult', pow_zero] at hPmult
    rw [hPmult] at hpP
    exact absurd (Nat.le_of_dvd one_pos hpP) (by have := hp.out.two_le; omega)
  · rw [hPmult', pow_one] at hPmult
    exact hPmult
  · exfalso
    rw [hPmult'] at hPmult
    apply hp2
    refine (pow_dvd_pow p (by omega : 2 ≤ e + 1 + 1)).trans ?_
    rw [← hPmult]
    exact hPdvd

variable {U : Type*} [Group U] [Finite U]

theorem sylow_data (M : Subgroup U) {p D : ℕ} (hp : p.Prime)
    (hnorm : ∀ P : Subgroup U, Nat.card P = p → ∀ N : Subgroup U, N ≤ normalizer (P : Set U) →
      Odd (Nat.card N) → Nat.card N ∣ D)
    (hodd : Odd (Nat.card M)) (hpM : p ∣ Nat.card M) (hp2 : ¬ p ^ 2 ∣ Nat.card M)
    (P : Sylow p M) :
    Nat.card (P : Subgroup M) = p ∧ Nat.card (normalizer ((P : Subgroup M) : Set M)) ∣ D ∧
      p ∣ Nat.card (normalizer ((P : Subgroup M) : Set M)) ∧
      Nat.card (normalizer ((P : Subgroup M) : Set M)) * Nat.card (Sylow p M) = Nat.card M ∧
      Nat.card (Sylow p M) % p = 1 := by
  have : Fact p.Prime := ⟨hp⟩
  have hPcard : Nat.card P = p := sylow_card_eq_prime P hpM hp2
  have hNcard : Nat.card (normalizer ((P : Subgroup M) : Set M)) ∣ Nat.card M :=
    Subgroup.card_subgroup_dvd_card _
  have hNodd : Odd (Nat.card (normalizer ((P : Subgroup M) : Set M))) :=
    Odd.of_dvd_nat hodd hNcard
  have hP' : Nat.card ((P : Subgroup M).map M.subtype) = p := by
    rw [Subgroup.card_map_of_injective M.subtype_injective, hPcard]
  have hN' : (normalizer ((P : Subgroup M) : Set M)).map M.subtype ≤
      normalizer (((P : Subgroup M).map M.subtype : Subgroup U) : Set U) :=
    Subgroup.le_normalizer_map M.subtype
  have hNcard' : Nat.card ((normalizer ((P : Subgroup M) : Set M)).map M.subtype) =
      Nat.card (normalizer ((P : Subgroup M) : Set M)) :=
    Subgroup.card_map_of_injective M.subtype_injective
  have hD := hnorm _ hP' _ hN' (by rw [hNcard']; exact hNodd)
  rw [hNcard'] at hD
  refine ⟨hPcard, hD, ?_, ?_, ?_⟩
  · have := Subgroup.card_dvd_of_le P.le_normalizer
    rwa [hPcard] at this
  · rw [P.card_eq_index_normalizer]
    exact Subgroup.card_mul_index _
  · have h := card_sylow_modEq_one p M
    unfold Nat.ModEq at h
    rwa [Nat.mod_eq_of_lt hp.one_lt] at h

end SylowData

section Main

variable {U : Type*} [Group U] [Finite U]

omit [Finite U] in
theorem not_abelian (hU : U6Hyp U) (M : Subgroup U) (X : Subgroup M) {e : ℕ} (he : 5 ≤ e)
    (hX : Nat.card X = 3 ^ e) (hab : ∀ a ∈ X, ∀ b ∈ X, a * b = b * a) : False := by
  have hcard : Nat.card (X.map M.subtype) = 3 ^ e := by
    rw [Subgroup.card_map_of_injective M.subtype_injective, hX]
  have hp : IsPGroup 3 (X.map M.subtype) := IsPGroup.of_card hcard
  have hlt := hU.abelian3 _ hp (by
    rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    exact congrArg (fun y : M => (y : U)) (hab a ha b hb))
  rw [hcard] at hlt
  have : 3 ^ 5 ≤ 3 ^ e := Nat.pow_le_pow_right (by norm_num) he
  omega

theorem case_seven (hU : U6Hyp U) (M : Subgroup U) (hodd : Odd (Nat.card M))
    (hn : Nat.card M = 5103) : False := by
  have hp7 : Nat.Prime 7 := by decide
  have : Fact (Nat.Prime 7) := ⟨hp7⟩
  obtain ⟨P⟩ := (inferInstance : Nonempty (Sylow 7 M))
  obtain ⟨hP, hk21, hk7, hkc, hc⟩ := sylow_data M hp7 hU.norm7 hodd (by rw [hn]; norm_num)
    (by rw [hn]; norm_num) P
  have hk : Nat.card (normalizer ((P : Subgroup M) : Set M)) = 7 := by
    generalize Nat.card (normalizer ((P : Subgroup M) : Set M)) = k at hk21 hk7 hkc
    generalize Nat.card (Sylow 7 M) = c at hkc hc
    rw [hn] at hkc
    have hle : k ≤ 21 := Nat.le_of_dvd (by norm_num) hk21
    have hk0 : 0 < k := by
      rcases Nat.eq_zero_or_pos k with h | h
      · simp [h] at hkc
      · exact h
    interval_cases k <;> omega
  have hN : normalizer ((P : Subgroup M) : Set M) = (P : Subgroup M) :=
    (Subgroup.eq_of_le_of_card_ge P.le_normalizer (by
      rw [hP]
      exact hk.le)).symm
  obtain ⟨K, hKn, hKc⟩ := exists_normal_complement P
    (normalizer_le_centralizer_of_self (P : Subgroup M) hp7 hP hN)
  have hK : Nat.card K = 3 ^ 6 := by
    rw [hP, hn] at hKc
    norm_num
    omega
  obtain ⟨g, hgP, hg7, hPg⟩ := exists_generator (P : Subgroup M) hp7 hP
  have hgK : g ∈ normalizer (K : Set M) := by
    rw [Subgroup.normalizer_eq_top_iff.2 hKn]
    exact Subgroup.mem_top g
  have hab := fpf_abelian K g (q := 7) (e := 6) hK (by norm_num) hgK hg7
    (eq_one_of_commute_of_selfNormalizing hPg hN (by rw [hP, hK]; norm_num)) (by decide)
  exact not_abelian hU M K (e := 6) (by norm_num) hK hab

theorem case_five_eleven (hU : U6Hyp U) (M : Subgroup U) (hodd : Odd (Nat.card M))
    (hn : Nat.card M = 13365) : False := by
  have hp5 : Nat.Prime 5 := by decide
  have hp11 : Nat.Prime 11 := by decide
  have : Fact (Nat.Prime 5) := ⟨hp5⟩
  have : Fact (Nat.Prime 11) := ⟨hp11⟩
  obtain ⟨P5⟩ := (inferInstance : Nonempty (Sylow 5 M))
  obtain ⟨hP5, hk15, hk5, hkc5, hc5⟩ := sylow_data M hp5 hU.norm5 hodd (by rw [hn]; norm_num)
    (by rw [hn]; norm_num) P5
  have hk5' : Nat.card (normalizer ((P5 : Subgroup M) : Set M)) = 15 := by
    generalize Nat.card (normalizer ((P5 : Subgroup M) : Set M)) = k at hk15 hk5 hkc5
    generalize Nat.card (Sylow 5 M) = c at hkc5 hc5
    rw [hn] at hkc5
    have hle : k ≤ 15 := Nat.le_of_dvd (by norm_num) hk15
    have hk0 : 0 < k := by
      rcases Nat.eq_zero_or_pos k with h | h
      · simp [h] at hkc5
      · exact h
    interval_cases k <;> omega
  obtain ⟨K5, hK5n, hK5c⟩ := exists_normal_complement P5
    (normalizer_le_centralizer_of_coprime (P5 : Subgroup M) hp5 hP5 (by
      rw [hk5']
      norm_num))
  have hK5 : Nat.card K5 = 2673 := by
    rw [hP5, hn] at hK5c
    omega
  have hK5idx : K5.index = 5 := by
    have := Subgroup.card_mul_index K5
    rw [hK5, hn] at this
    omega
  obtain ⟨Q⟩ := (inferInstance : Nonempty (Sylow 11 K5))
  have hQ : Nat.card Q = 11 :=
    sylow_card_eq_prime Q (by rw [hK5]; norm_num) (by rw [hK5]; norm_num)
  have hQM : Nat.card ((Q : Subgroup K5).map K5.subtype) = 11 := by
    rw [Subgroup.card_map_of_injective K5.subtype_injective, hQ]
  have hQ11 : IsPGroup 11 ((Q : Subgroup K5).map K5.subtype) :=
    IsPGroup.of_card (n := 1) (by simpa using hQM)
  have hQidx : ¬ 11 ∣ ((Q : Subgroup K5).map K5.subtype).index := by
    have := Subgroup.card_mul_index ((Q : Subgroup K5).map K5.subtype)
    rw [hQM, hn] at this
    omega
  let P11 : Sylow 11 M := hQ11.toSylow hQidx
  obtain ⟨hP11, hk55, hk11, hkc11, hc11⟩ := sylow_data M hp11 hU.norm11 hodd
    (by rw [hn]; norm_num) (by rw [hn]; norm_num) P11
  have hk11' : Nat.card (normalizer ((P11 : Subgroup M) : Set M)) = 55 := by
    generalize Nat.card (normalizer ((P11 : Subgroup M) : Set M)) = k at hk55 hk11 hkc11
    generalize Nat.card (Sylow 11 M) = c at hkc11 hc11
    rw [hn] at hkc11
    have hle : k ≤ 55 := Nat.le_of_dvd (by norm_num) hk55
    have hk0 : 0 < k := by
      rcases Nat.eq_zero_or_pos k with h | h
      · simp [h] at hkc11
      · exact h
    interval_cases k <;> omega
  have hNQ : normalizer ((Q : Subgroup K5) : Set K5) = Q := by
    have h1 : (normalizer ((Q : Subgroup K5) : Set K5)).map K5.subtype ≤
        normalizer ((P11 : Subgroup M) : Set M) :=
      Subgroup.le_normalizer_map K5.subtype
    have h2 : Nat.card (normalizer ((Q : Subgroup K5) : Set K5)) ∣ 55 := by
      rw [← hk11']
      have := Subgroup.card_dvd_of_le h1
      rwa [Subgroup.card_map_of_injective K5.subtype_injective] at this
    have h3 : Nat.card (normalizer ((Q : Subgroup K5) : Set K5)) ∣ 2673 := by
      rw [← hK5]
      exact Subgroup.card_subgroup_dvd_card _
    have h4 : Nat.card (normalizer ((Q : Subgroup K5) : Set K5)) ∣ 11 := by
      have := Nat.dvd_gcd h2 h3
      simpa using this
    refine (Subgroup.eq_of_le_of_card_ge Q.le_normalizer ?_).symm
    rw [hQ]
    exact Nat.le_of_dvd (by norm_num) h4
  obtain ⟨T, hTn, hTc⟩ := exists_normal_complement Q
    (normalizer_le_centralizer_of_self (Q : Subgroup K5) hp11 hQ hNQ)
  have hT : Nat.card T = 3 ^ 5 := by
    rw [hQ, hK5] at hTc
    norm_num
    omega
  obtain ⟨g, hgQ, hg11, hQg⟩ := exists_generator (Q : Subgroup K5) hp11 hQ
  have hgT : g ∈ normalizer (T : Set K5) := by
    rw [Subgroup.normalizer_eq_top_iff.2 hTn]
    exact Subgroup.mem_top g
  have hab := fpf_abelian T g (q := 11) (e := 5) hT (by norm_num) hgT hg11
    (eq_one_of_commute_of_selfNormalizing hQg hNQ (by rw [hQ, hT]; norm_num)) (by decide)
  have hTM : Nat.card (T.map K5.subtype) = 3 ^ 5 := by
    rw [Subgroup.card_map_of_injective K5.subtype_injective, hT]
  refine not_abelian hU M (T.map K5.subtype) (e := 5) le_rfl hTM ?_
  rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
  exact congrArg (fun y : K5 => (y : M)) (hab a ha b hb)

theorem U6Hyp.odd_card_lt (hU : U6Hyp U) (M : Subgroup U) (hodd : Odd (Nat.card M)) :
    Nat.card M < 3000 := by
  by_contra hge
  push Not at hge
  have hp5 : Nat.Prime 5 := by decide
  have hp7 : Nat.Prime 7 := by decide
  have hp11 : Nat.Prime 11 := by decide
  have hMdvd : Nat.card M ∣ 2 ^ 15 * (729 * 385) := by
    have := Subgroup.card_subgroup_dvd_card M
    rw [hU.card] at this
    convert this using 1
  have hcop2 : Nat.Coprime (Nat.card M) 2 :=
    Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).2 (by
      have := Nat.odd_iff.1 hodd
      omega))
  have hdvd : Nat.card M ∣ 729 * 385 := (Nat.Coprime.pow_right 15 hcop2).dvd_of_dvd_mul_left hMdvd
  obtain ⟨y, z, hy, hz, hyz⟩ := Nat.dvd_mul.1 hdvd
  have hyd : y ∈ Nat.divisors 729 := Nat.mem_divisors.2 ⟨hy, by norm_num⟩
  have hzd : z ∈ Nat.divisors 385 := Nat.mem_divisors.2 ⟨hz, by norm_num⟩
  have key : ∀ {p D : ℕ}, p.Prime → (∀ P : Subgroup U, Nat.card P = p → ∀ N : Subgroup U,
      N ≤ normalizer (P : Set U) → Odd (Nat.card N) → Nat.card N ∣ D) → p ∣ Nat.card M →
      ¬ p ^ 2 ∣ Nat.card M → D ≠ 0 →
      ∃ k ∈ Nat.divisors D, p ∣ k ∧ (Nat.card M / k) % p = 1 ∧ k ∣ Nat.card M := by
    intro p D hp hnorm hpM hp2 hD
    have : Fact p.Prime := ⟨hp⟩
    obtain ⟨P⟩ := (inferInstance : Nonempty (Sylow p M))
    obtain ⟨-, hkD, hpk, hkc, hc⟩ := sylow_data M hp hnorm hodd hpM hp2 P
    have hk0 : 0 < Nat.card (normalizer ((P : Subgroup M) : Set M)) := Nat.card_pos
    refine ⟨_, Nat.mem_divisors.2 ⟨hkD, hD⟩, hpk, ?_, ⟨_, hkc.symm⟩⟩
    rw [← hkc, Nat.mul_div_cancel_left _ hk0]
    exact hc
  have hnot : ∀ p : ℕ, p ∣ 280665 → ¬ p ^ 2 ∣ 280665 → p ∣ Nat.card M → ¬ p ^ 2 ∣ Nat.card M := by
    intro p _ hp2 _ h
    exact hp2 (h.trans (by rw [show (280665 : ℕ) = 729 * 385 by norm_num]; exact hdvd))
  have h5 : 5 ∣ y * z → ∃ k ∈ Nat.divisors 15, 5 ∣ k ∧ ((y * z) / k) % 5 = 1 ∧ k ∣ y * z := by
    intro h
    rw [hyz] at h ⊢
    exact key hp5 hU.norm5 h (hnot 5 (by norm_num) (by norm_num) h) (by norm_num)
  have h7 : 7 ∣ y * z → ∃ k ∈ Nat.divisors 21, 7 ∣ k ∧ ((y * z) / k) % 7 = 1 ∧ k ∣ y * z := by
    intro h
    rw [hyz] at h ⊢
    exact key hp7 hU.norm7 h (hnot 7 (by norm_num) (by norm_num) h) (by norm_num)
  have h11 : 11 ∣ y * z →
      ∃ k ∈ Nat.divisors 55, 11 ∣ k ∧ ((y * z) / k) % 11 = 1 ∧ k ∣ y * z := by
    intro h
    rw [hyz] at h ⊢
    exact key hp11 hU.norm11 h (hnot 11 (by norm_num) (by norm_num) h) (by norm_num)
  rcases arith_main y hyd z hzd (by rw [hyz]; exact hge) h5 h7 h11 with h | h
  · exact case_seven hU M hodd (by rw [← hyz]; exact h)
  · exact case_five_eleven hU M hodd (by rw [← hyz]; exact h)

end Main

end CFSG.Monster.GMS.U6Odd
