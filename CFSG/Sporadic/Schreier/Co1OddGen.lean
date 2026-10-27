module

public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Tactic.Simproc.Factors
public import CFSG.GroupTheory.LocalCores.PrimeSetCore
public import CFSG.FeitThompson.OddOrderTheorem
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBHeldSmallCoreMultiplicity
public import CFSG.GroupTheory.PCore.Defs

public section

namespace CFSG.Sporadic.Co1Schreier.OddGen

open scoped commutatorElement

theorem card_dvd_ncard_of_free {G α : Type*} [Group G] [MulAction G α] [Finite G] {S : Set α}
    (hfin : S.Finite) (hS : ∀ g : G, ∀ a ∈ S, g • a ∈ S)
    (hfree : ∀ g : G, ∀ a ∈ S, g • a = a → g = 1) : Nat.card G ∣ S.ncard := by
  classical
  let act : MulAction G S :=
    { smul := fun g a => ⟨g • (a : α), hS g a a.2⟩
      one_smul := fun a => Subtype.ext (one_smul G (a : α))
      mul_smul := fun g h a => Subtype.ext (mul_smul g h (a : α)) }
  have : Finite S := hfin.to_subtype
  let _ : Fintype (MulAction.orbitRel.Quotient G S) := Fintype.ofFinite _
  have hstab : ∀ a : S, MulAction.stabilizer G a = ⊥ := fun a => by
    rw [eq_bot_iff]
    intro g hg
    rw [MulAction.mem_stabilizer_iff] at hg
    exact (Subgroup.mem_bot).mpr (hfree g a a.2 (congrArg Subtype.val hg))
  have horb : ∀ a : S, Nat.card (MulAction.orbit G a) = Nat.card G := fun a => by
    rw [Nat.card_congr (MulAction.orbitEquivQuotientStabilizer G a), hstab a,
      ← Subgroup.index, Subgroup.index_bot]
  rw [← Nat.card_coe_set_eq, Nat.card_congr (MulAction.selfEquivSigmaOrbits G S),
    Nat.card_sigma]
  exact Finset.dvd_sum fun ω _ => (horb _).symm ▸ dvd_rfl

theorem card_sylow_of_card_eq_mul {G : Type*} [Group G] [Finite G] {p q r : ℕ} (hp : p.Prime)
    (hq : q.Prime) (hpq : p ≠ q) (hG : Nat.card G = p * q) (hr : r = p ∨ r = q) [Fact r.Prime]
    (P : Sylow r G) : Nat.card P = r := by
  rw [P.card_eq_multiplicity, hG, Nat.factorization_mul hp.ne_zero hq.ne_zero, Finsupp.add_apply,
    hp.factorization, hq.factorization]
  rcases hr with rfl | rfl
  · rw [Finsupp.single_eq_same, Finsupp.single_eq_of_ne hpq, add_zero, pow_one]
  · rw [Finsupp.single_eq_same, Finsupp.single_eq_of_ne hpq.symm, zero_add, pow_one]

theorem isCyclic_of_card_eq_mul {G : Type*} [Group G] [Finite G] {p q : ℕ} (hp : p.Prime)
    (hq : q.Prime) (hpq : p < q) (hdiv : ¬p ∣ q - 1) (hG : Nat.card G = p * q) : IsCyclic G := by
  have : Fact p.Prime := ⟨hp⟩
  have : Fact q.Prime := ⟨hq⟩
  have hGp : 0 < Nat.card G := Nat.card_pos
  have hidx : ∀ {r s : ℕ} [Fact r.Prime], r * s = Nat.card G → (P : Sylow r G) →
      Nat.card P = r → (P : Subgroup G).index = s := by
    intro r s _ hrs P hP
    have h := (P : Subgroup G).card_mul_index
    rw [hP, ← hrs] at h
    exact Nat.eq_of_mul_eq_mul_left (Fact.out : r.Prime).pos h
  obtain ⟨P⟩ : Nonempty (Sylow p G) := inferInstance
  obtain ⟨Q⟩ : Nonempty (Sylow q G) := inferInstance
  have hP : Nat.card P = p := card_sylow_of_card_eq_mul hp hq hpq.ne hG (.inl rfl) P
  have hQ : Nat.card Q = q := card_sylow_of_card_eq_mul hp hq hpq.ne hG (.inr rfl) Q
  have hnq : Nat.card (Sylow q G) = 1 := by
    have h1 := card_sylow_modEq_one q G
    have h2 : Nat.card (Sylow q G) ∣ p := by
      have := Q.card_dvd_index
      rwa [hidx (by rw [hG, mul_comm]) Q hQ] at this
    rcases (Nat.dvd_prime hp).mp h2 with h | h
    · exact h
    · exfalso
      rw [h, Nat.ModEq, Nat.mod_eq_of_lt hpq, Nat.one_mod_eq_one.mpr hq.one_lt.ne'] at h1
      exact hp.one_lt.ne' h1
  have hnp : Nat.card (Sylow p G) = 1 := by
    have h1 := card_sylow_modEq_one p G
    have h2 : Nat.card (Sylow p G) ∣ q := by
      have := P.card_dvd_index
      rwa [hidx hG.symm P hP] at this
    rcases (Nat.dvd_prime hq).mp h2 with h | h
    · exact h
    · exfalso
      rw [h] at h1
      exact hdiv ((Nat.modEq_iff_dvd' hq.one_lt.le).mp h1.symm)
  have : Subsingleton (Sylow p G) := (Nat.card_eq_one_iff_unique.mp hnp).1
  have : Subsingleton (Sylow q G) := (Nat.card_eq_one_iff_unique.mp hnq).1
  have hPn : (P : Subgroup G).Normal := P.normal_of_subsingleton
  have hQn : (Q : Subgroup G).Normal := Q.normal_of_subsingleton
  obtain ⟨a, ha⟩ := exists_prime_orderOf_dvd_card' p (by rw [hG]; exact dvd_mul_right p q)
  obtain ⟨b, hb⟩ := exists_prime_orderOf_dvd_card' q (by rw [hG]; exact dvd_mul_left q p)
  have haP : a ∈ (P : Subgroup G) := by
    obtain ⟨P', hP'⟩ := IsPGroup.exists_le_sylow (IsPGroup.of_card
      (show Nat.card (Subgroup.zpowers a) = p ^ 1 by rw [Nat.card_zpowers, ha, pow_one]))
    rw [Subsingleton.elim P' P] at hP'
    exact hP' (Subgroup.mem_zpowers a)
  have hbQ : b ∈ (Q : Subgroup G) := by
    obtain ⟨Q', hQ'⟩ := IsPGroup.exists_le_sylow (IsPGroup.of_card
      (show Nat.card (Subgroup.zpowers b) = q ^ 1 by rw [Nat.card_zpowers, hb, pow_one]))
    rw [Subsingleton.elim Q' Q] at hQ'
    exact hQ' (Subgroup.mem_zpowers b)
  have hcop : Nat.Coprime p q := (Nat.coprime_primes hp hq).mpr hpq.ne
  have hdisj : (P : Subgroup G) ⊓ Q = ⊥ := by
    refine disjoint_iff.mp (Subgroup.disjoint_of_coprime_natCard ?_)
    rw [hP, hQ]
    exact hcop
  have hc : a * b * a⁻¹ * b⁻¹ ∈ (P : Subgroup G) ⊓ Q := by
    refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
    · have h1 : b * a⁻¹ * b⁻¹ ∈ (P : Subgroup G) := hPn.conj_mem _ ((P : Subgroup G).inv_mem haP) b
      have := (P : Subgroup G).mul_mem haP h1
      simpa only [mul_assoc] using this
    · have h1 : a * b * a⁻¹ ∈ (Q : Subgroup G) := hQn.conj_mem _ hbQ a
      exact (Q : Subgroup G).mul_mem h1 ((Q : Subgroup G).inv_mem hbQ)
  rw [hdisj, Subgroup.mem_bot] at hc
  have hcomm : Commute a b := by
    show a * b = b * a
    calc a * b = a * b * a⁻¹ * b⁻¹ * (b * a) := by group
      _ = b * a := by rw [hc, one_mul]
  have hco : Nat.Coprime (orderOf a) (orderOf b) := by
    rw [ha, hb]
    exact hcop
  have hord : orderOf (a * b) = p * q := by
    rw [hcomm.orderOf_mul_eq_mul_orderOf_of_coprime hco, ha, hb]
  exact isCyclic_of_card_le_orderOf (a * b) (by rw [hord, hG])

theorem isCyclic_of_card_dvd_fifteen {G : Type*} [Group G] [Finite G]
    (h : Nat.card G ∣ 15) : IsCyclic G := by
  have hd : Nat.card G ∈ Nat.divisors 15 := Nat.mem_divisors.mpr ⟨h, by norm_num⟩
  have : Nat.divisors 15 = {1, 3, 5, 15} := by decide
  rw [this] at hd
  simp only [Finset.mem_insert, Finset.mem_singleton] at hd
  rcases hd with h1 | h3 | h5 | h15
  · have : Subsingleton G := (Nat.card_eq_one_iff_unique.mp h1).1
    infer_instance
  · have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    exact isCyclic_of_prime_card h3
  · have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
    exact isCyclic_of_prime_card h5
  · exact isCyclic_of_card_eq_mul Nat.prime_three Nat.prime_five (by norm_num) (by norm_num)
      (by rw [h15])

theorem isCyclic_of_card_dvd_thirtythree {G : Type*} [Group G] [Finite G]
    (h : Nat.card G ∣ 33) : IsCyclic G := by
  have hd : Nat.card G ∈ Nat.divisors 33 := Nat.mem_divisors.mpr ⟨h, by norm_num⟩
  have : Nat.divisors 33 = {1, 3, 11, 33} := by decide
  rw [this] at hd
  simp only [Finset.mem_insert, Finset.mem_singleton] at hd
  have h11p : Nat.Prime 11 := by decide
  rcases hd with h1 | h3 | h11 | h33
  · have : Subsingleton G := (Nat.card_eq_one_iff_unique.mp h1).1
    infer_instance
  · have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    exact isCyclic_of_prime_card h3
  · have : Fact (Nat.Prime 11) := ⟨h11p⟩
    exact isCyclic_of_prime_card h11
  · exact isCyclic_of_card_eq_mul Nat.prime_three h11p (by norm_num) (by norm_num)
      (by rw [h33])

theorem commute_of_cyclic {C : Type*} [Group C] {M : Subgroup C} [Finite M] [IsCyclic M]
    {s : C} (hs : ∀ m ∈ M, s * m * s⁻¹ ∈ M) {k : ℕ} (hk : s ^ k = 1)
    (harith : ∀ e < Nat.card M, e ^ k % Nat.card M = 1 % Nat.card M →
      e % Nat.card M = 1 % Nat.card M) :
    ∀ m ∈ M, s * m = m * s := by
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := M)
  have hgo : orderOf (g : C) = Nat.card M := by
    rw [Subgroup.orderOf_coe, orderOf_eq_card_of_forall_mem_zpowers hg]
  obtain ⟨i, hi⟩ := hg ⟨s * g * s⁻¹, hs g g.2⟩
  have hpos : 0 < Nat.card M := Nat.card_pos
  set e : ℕ := (i % (Nat.card M : ℤ)).toNat with he
  have hge : s * (g : C) * s⁻¹ = (g : C) ^ e := by
    have h1 : ((g ^ i : M) : C) = s * (g : C) * s⁻¹ := congrArg Subtype.val hi
    rw [← h1, Subgroup.coe_zpow, ← zpow_natCast, he, Int.toNat_of_nonneg
      (Int.emod_nonneg _ (by exact_mod_cast hpos.ne')), ← hgo, zpow_mod_orderOf]
  have hpow : ∀ j : ℕ, s ^ j * (g : C) * (s ^ j)⁻¹ = (g : C) ^ (e ^ j) := by
    intro j
    induction j with
    | zero => simp
    | succ j ih =>
      rw [pow_succ', pow_succ, mul_inv_rev, pow_mul]
      calc s * s ^ j * (g : C) * ((s ^ j)⁻¹ * s⁻¹)
          = s * (s ^ j * (g : C) * (s ^ j)⁻¹) * s⁻¹ := by group
        _ = s * (g : C) ^ (e ^ j) * s⁻¹ := by rw [ih]
        _ = (s * (g : C) * s⁻¹) ^ (e ^ j) := by rw [conj_pow]
        _ = ((g : C) ^ e) ^ (e ^ j) := by rw [hge]
        _ = ((g : C) ^ e ^ j) ^ e := by rw [← pow_mul, ← pow_mul, mul_comm]
  have hek : (g : C) ^ (e ^ k) = (g : C) := by
    have := hpow k
    rw [hk, one_mul, inv_one, mul_one] at this
    exact this.symm
  have hmod : e ^ k % Nat.card M = 1 % Nat.card M := by
    rw [← hgo]
    have := (pow_eq_pow_iff_modEq (x := (g : C))).mp (hek.trans (pow_one _).symm)
    exact this
  have he_lt : e < Nat.card M := by
    rw [he]
    have h0 : 0 ≤ i % (Nat.card M : ℤ) := Int.emod_nonneg _ (by exact_mod_cast hpos.ne')
    have h1 : i % (Nat.card M : ℤ) < Nat.card M := Int.emod_lt_of_pos _ (by exact_mod_cast hpos)
    omega
  have he1 := harith e he_lt hmod
  have hsg : s * (g : C) * s⁻¹ = g := by
    rw [hge]
    conv_rhs => rw [← pow_one (g : C)]
    refine pow_eq_pow_iff_modEq.mpr ?_
    rw [hgo]
    exact he1
  intro m hm
  obtain ⟨j, hj⟩ := hg ⟨m, hm⟩
  have hm' : m = (g : C) ^ j := (congrArg Subtype.val hj).symm.trans (by rw [Subgroup.coe_zpow])
  rw [hm']
  have : s * (g : C) ^ j * s⁻¹ = (g : C) ^ j := by rw [← conj_zpow, hsg]
  calc s * (g : C) ^ j = s * (g : C) ^ j * s⁻¹ * s := by group
    _ = (g : C) ^ j * s := by rw [this]

theorem le_ker_of_perfect {G A : Type*} [Group G] [Group A] [Group.IsSolvable A] (φ : G →* A)
    {J : Subgroup G} (hJ : ⁅J, J⁆ = J) : J ≤ φ.ker := by
  have hle : ∀ n, J ≤ derivedSeries G n := by
    intro n
    induction n with
    | zero => exact le_top
    | succ n ih =>
      rw [derivedSeries_succ, ← hJ]
      exact Subgroup.commutator_mono ih ih
  obtain ⟨n, hn⟩ := Group.IsSolvable.solvable (G := A)
  intro x hx
  have h1 : φ x ∈ derivedSeries A n :=
    map_derivedSeries_le_derivedSeries φ n (Subgroup.mem_map_of_mem φ (hle n hx))
  rw [hn, Subgroup.mem_bot] at h1
  exact h1

theorem perfect_closure_pair {G : Type*} [Group G] {x y a b c d a' b' c' d' : G}
    (hmem : ∀ g ∈ [a, b, c, d, a', b', c', d'], g ∈ Subgroup.closure ({x, y} : Set G))
    (hx : x = ⁅a, b⁆ * ⁅c, d⁆) (hy : y = ⁅a', b'⁆ * ⁅c', d'⁆) :
    ⁅Subgroup.closure ({x, y} : Set G), Subgroup.closure ({x, y} : Set G)⁆ =
      Subgroup.closure ({x, y} : Set G) := by
  have m : ∀ g ∈ [a, b, c, d, a', b', c', d'], g ∈ Subgroup.closure ({x, y} : Set G) := hmem
  refine le_antisymm (Subgroup.commutator_le.mpr fun g₁ h₁ g₂ h₂ => ?_) ?_
  · rw [commutatorElement_def]
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ h₁ h₂)
      (Subgroup.inv_mem _ h₁)) (Subgroup.inv_mem _ h₂)
  · have hxJ : x ∈ ⁅Subgroup.closure ({x, y} : Set G), Subgroup.closure ({x, y} : Set G)⁆ := by
      have h := Subgroup.mul_mem _
        (Subgroup.commutator_mem_commutator (m a (by simp)) (m b (by simp)))
        (Subgroup.commutator_mem_commutator (m c (by simp)) (m d (by simp)))
      rwa [← hx] at h
    have hyJ : y ∈ ⁅Subgroup.closure ({x, y} : Set G), Subgroup.closure ({x, y} : Set G)⁆ := by
      have h := Subgroup.mul_mem _
        (Subgroup.commutator_mem_commutator (m a' (by simp)) (m b' (by simp)))
        (Subgroup.commutator_mem_commutator (m c' (by simp)) (m d' (by simp)))
      rwa [← hy] at h
    rw [Subgroup.closure_le]
    intro g hg
    rcases hg with hg | hg
    · rw [hg]
      exact hxJ
    · rw [Set.mem_singleton_iff.mp hg]
      exact hyJ

theorem comm_inv_of_comm {G : Type*} [Group G] {c s : G} (h : c * s = s * c) :
    c⁻¹ * s = s * c⁻¹ := by
  calc c⁻¹ * s = c⁻¹ * (s * c) * c⁻¹ := by group
    _ = c⁻¹ * (c * s) * c⁻¹ := by rw [h]
    _ = s * c⁻¹ := by group

theorem conj_comm_of_comm {G : Type*} [Group G] {t q s : G} (hts : t * s = s * t)
    (hqs : q * s = s * q) : t⁻¹ * q * t⁻¹⁻¹ * s = s * (t⁻¹ * q * t⁻¹⁻¹) := by
  have hti := comm_inv_of_comm hts
  calc t⁻¹ * q * t⁻¹⁻¹ * s = t⁻¹ * q * (t * s) := by group
    _ = t⁻¹ * q * (s * t) := by rw [hts]
    _ = t⁻¹ * (q * s) * t := by group
    _ = t⁻¹ * (s * q) * t := by rw [hqs]
    _ = t⁻¹ * s * q * t := by group
    _ = s * t⁻¹ * q * t := by rw [hti]
    _ = s * (t⁻¹ * q * t⁻¹⁻¹) := by group

theorem eq_one_of_conj_eq_one {G : Type*} [Group G] {t q : G} (h : t⁻¹ * q * t⁻¹⁻¹ = 1) :
    q = 1 := by
  calc q = t * (t⁻¹ * q * t⁻¹⁻¹) * t⁻¹ := by group
    _ = 1 := by rw [h]; group

theorem eq_of_conj_eq {G : Type*} [Group G] {g q : G} (h : g * q * g⁻¹ = q) : q * g = g * q := by
  calc q * g = g * q * g⁻¹ * g := by rw [h]
    _ = g * q := by group

theorem conj_conj_inv {G : Type*} [Group G] (c h : G) : c⁻¹ * (c * h * c⁻¹) * c⁻¹⁻¹ = h := by
  group

theorem prime_dvd_4095 {p : ℕ} (hp : p.Prime) (h : p ∣ 4095) : p ∈ [3, 5, 7, 13] := by
  have h' : p ∣ 3 * (3 * (5 * (7 * 13))) := by norm_num; exact h
  have h13 : Nat.Prime 13 := by norm_num
  rcases (Nat.Prime.dvd_mul hp).mp h' with h3 | h'
  · rw [(Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).mp h3]; simp
  rcases (Nat.Prime.dvd_mul hp).mp h' with h3 | h'
  · rw [(Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).mp h3]; simp
  rcases (Nat.Prime.dvd_mul hp).mp h' with h5 | h'
  · rw [(Nat.prime_dvd_prime_iff_eq hp Nat.prime_five).mp h5]; simp
  rcases (Nat.Prime.dvd_mul hp).mp h' with h7 | h13'
  · rw [(Nat.prime_dvd_prime_iff_eq hp (by norm_num)).mp h7]; simp
  · rw [(Nat.prime_dvd_prime_iff_eq hp h13).mp h13']; simp

open CFSG.ComponentClassification.CatalogueBHeldSmallCore in
theorem solvable_mulAut_of_dvd {M : Type*} [Group M] [Finite M] [Group.IsSolvable M]
    (h : Nat.card M ∣ 4095) : Group.IsSolvable (MulAut M) := by
  have hM0 : Nat.card M ≠ 0 := Nat.card_pos.ne'
  have hle := (Nat.factorization_le_iff_dvd hM0 (by norm_num)).mpr h
  have hf : ∀ p, (4095 : ℕ).factorization p = [3, 3, 5, 7, 13].count p := by
    intro p
    rw [← Nat.primeFactorsList_count_eq, show Nat.primeFactorsList 4095 = [3, 3, 5, 7, 13] by
      norm_num]
  refine small_prime_multiplicity_solvable_automorphisms M ?_ fun p _ hp3 => ?_
  · exact (hle 3).trans (by rw [hf]; decide)
  · refine (hle p).trans ?_
    rw [hf]
    simp only [List.count_cons, List.count_nil, beq_iff_eq]
    split_ifs <;> omega

theorem centralizes_of_perfect_of_dvd {G : Type*} [Group G] [Finite G] {Q : Subgroup G}
    (hodd : Odd (Nat.card Q)) (hdvd : Nat.card Q ∣ 4095) {J : Subgroup G}
    (hJN : J ≤ Subgroup.normalizer (Q : Set G)) (hperf : ⁅J, J⁆ = J) :
    ∀ g ∈ J, ∀ q ∈ Q, q * g = g * q := by
  have hsolv : Group.IsSolvable Q := CFSG.FeitThompson.isSolvable_of_odd_natCard _ hodd
  have hAut : Group.IsSolvable (MulAut Q) := solvable_mulAut_of_dvd hdvd
  have hmap : (J.subgroupOf (Subgroup.normalizer (Q : Set G))).map
      (Subgroup.normalizer (Q : Set G)).subtype = J := by
    rw [Subgroup.subgroupOf_map_subtype, inf_of_le_left hJN]
  have hperf' : ⁅J.subgroupOf (Subgroup.normalizer (Q : Set G)),
      J.subgroupOf (Subgroup.normalizer (Q : Set G))⁆ =
      J.subgroupOf (Subgroup.normalizer (Q : Set G)) := by
    apply Subgroup.map_injective (f := (Subgroup.normalizer (Q : Set G)).subtype)
      Subtype.val_injective
    rw [Subgroup.map_commutator, hmap, hperf]
  have hker := le_ker_of_perfect Q.normalizerMonoidHom hperf'
  intro g hg q hq
  have h1 : Q.normalizerMonoidHom ⟨g, hJN hg⟩ = 1 := hker (Subgroup.mem_subgroupOf.mpr hg)
  have h2 := congrArg (fun α : MulAut Q => ((α ⟨q, hq⟩ : Q) : G)) h1
  have h3 : g * q * g⁻¹ = q := h2
  exact eq_of_conj_eq h3

theorem eq_bot_of_two_elements {K : Type*} [Group K] [Finite K]
    (hK : Nat.card K = 2 ^ 15 * 15) {e3 e3' e5 e5' : K} (h3 : e3 ^ 3 = 1) (h3' : e3' ^ 3 = 1)
    (h5 : e5 ^ 5 = 1) (h5' : e5' ^ 5 = 1) (h33 : (e3 * e3') ^ 15 ≠ 1)
    (h55 : (e5 * e5') ^ 15 ≠ 1) (N : Subgroup K) (hN : N.Normal) (hodd : Odd (Nat.card N)) :
    N = ⊥ := by
  have hNK : Nat.card N ∣ 2 ^ 15 * 15 := hK ▸ Subgroup.card_subgroup_dvd_card N
  have hN15 : Nat.card N ∣ 15 :=
    Nat.Coprime.dvd_of_dvd_mul_left (Nat.Coprime.pow_right 15 (Nat.coprime_two_right.mpr hodd))
      (by rw [mul_comm] at hNK; exact hNK)
  have hcardQ : Nat.card (K ⧸ N) * Nat.card N = 2 ^ 15 * 15 := by
    rw [← hK, ← Subgroup.card_eq_card_quotient_mul_card_subgroup]
  have key : ∀ {p : ℕ} {e : K}, p.Prime → p ∣ 15 → ¬p ^ 2 ∣ 15 → e ^ p = 1 → p ∣ Nat.card N →
      e ∈ N := by
    intro p e hp hp15 hp2 he hpN
    have hq : ¬p ∣ Nat.card (K ⧸ N) := by
      intro hpQ
      have : p ^ 2 ∣ 2 ^ 15 * 15 := by
        rw [← hcardQ, pow_two]
        exact Nat.mul_dvd_mul hpQ hpN
      have hp2' : p ≠ 2 := by
        rintro rfl
        exact absurd hp15 (by norm_num)
      have hcop : Nat.Coprime (p ^ 2) (2 ^ 15) :=
        Nat.Coprime.pow _ _ ((Nat.coprime_primes hp Nat.prime_two).mpr hp2')
      exact hp2 (hcop.dvd_of_dvd_mul_left this)
    have ho : orderOf (QuotientGroup.mk e : K ⧸ N) ∣ p := by
      apply orderOf_dvd_of_pow_eq_one
      rw [← QuotientGroup.mk_pow, he, QuotientGroup.mk_one]
    rcases (Nat.dvd_prime hp).mp ho with h1 | h1
    · rw [orderOf_eq_one_iff, QuotientGroup.eq_one_iff] at h1
      exact h1
    · exact absurd (h1 ▸ orderOf_dvd_natCard _) hq
  have hpow : ∀ n ∈ N, n ^ 15 = 1 := fun n hn => by
    have : orderOf (⟨n, hn⟩ : N) ∣ 15 := (orderOf_dvd_natCard _).trans hN15
    have h := orderOf_dvd_iff_pow_eq_one.mp this
    exact congrArg Subtype.val h
  have h3N : ¬3 ∣ Nat.card N := fun h => h33 (hpow _ (N.mul_mem
    (key Nat.prime_three (by norm_num) (by norm_num) h3 h)
    (key Nat.prime_three (by norm_num) (by norm_num) h3' h)))
  have h5N : ¬5 ∣ Nat.card N := fun h => h55 (hpow _ (N.mul_mem
    (key Nat.prime_five (by norm_num) (by norm_num) h5 h)
    (key Nat.prime_five (by norm_num) (by norm_num) h5' h)))
  have h1 : Nat.card N = 1 := by
    have hd : Nat.card N ∈ Nat.divisors 15 := Nat.mem_divisors.mpr ⟨hN15, by norm_num⟩
    have : Nat.divisors 15 = {1, 3, 5, 15} := by decide
    rw [this] at hd
    simp only [Finset.mem_insert, Finset.mem_singleton] at hd
    rcases hd with h | h | h | h
    · exact h
    · exact absurd (h ▸ dvd_rfl) h3N
    · exact absurd (h ▸ dvd_rfl) h5N
    · exact absurd (h ▸ (by norm_num : 3 ∣ 15)) h3N
  exact Subgroup.eq_bot_of_card_eq N h1

theorem fix_of_ncard_le_two {G α : Type*} [Group G] [MulAction G α] [Finite G]
    (hodd : Odd (Nat.card G)) {S : Set α} (hS : ∀ g : G, ∀ a ∈ S, g • a ∈ S)
    (hfin : S.Finite) (h2 : S.ncard ≤ 2) : ∀ g : G, ∀ a ∈ S, g • a = a := by
  intro g a ha
  have hsub : MulAction.orbit G a ⊆ S := by
    rintro _ ⟨h, rfl⟩
    exact hS h a ha
  have hle : (MulAction.orbit G a).ncard ≤ 2 := (Set.ncard_le_ncard hsub hfin).trans h2
  have hdvd : (MulAction.orbit G a).ncard ∣ Nat.card G := by
    rw [← MulAction.index_stabilizer]
    exact Subgroup.index_dvd_card _
  have hpos : 0 < (MulAction.orbit G a).ncard :=
    Set.ncard_pos (hfin.subset hsub) |>.mpr ⟨a, MulAction.mem_orbit_self a⟩
  have hodd' : Odd (MulAction.orbit G a).ncard := hodd.of_dvd_nat hdvd
  have h1 : (MulAction.orbit G a).ncard = 1 := by
    rcases hodd' with ⟨k, hk⟩
    omega
  obtain ⟨b, hb⟩ := Set.ncard_eq_one.mp h1
  have hga : g • a ∈ MulAction.orbit G a := MulAction.mem_orbit a g
  have haa : a ∈ MulAction.orbit G a := MulAction.mem_orbit_self a
  rw [hb, Set.mem_singleton_iff] at hga haa
  rw [hga, haa]

@[expose] def CentOddFreeIn {G : Type*} [Group G] (Γ : Subgroup G) (t : G) : Prop :=
  ∀ Q : Subgroup G, Q ≤ Γ → (∀ q ∈ Q, q * t = t * q) →
    (∀ c ∈ Γ, c * t = t * c → ∀ q ∈ Q, c * q * c⁻¹ ∈ Q) → Odd (Nat.card Q) → Q = ⊥

theorem centOddFreeIn_of_oddCore {K : Type*} [Group K] {t : K}
    (h : CFSG.oddCore (Subgroup.centralizer ({t} : Set K)) = ⊥) :
    CentOddFreeIn (⊤ : Subgroup K) t := by
  intro Q _ hQt hnorm hodd
  have hQC : Q ≤ Subgroup.centralizer ({t} : Set K) := fun q hq =>
    Subgroup.mem_centralizer_singleton_iff.mpr (hQt q hq)
  have hn : (Q.subgroupOf (Subgroup.centralizer ({t} : Set K))).Normal := ⟨fun n hn c => by
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    have hc : (c : K) * t = t * c := Subgroup.mem_centralizer_singleton_iff.mp c.2
    simpa only [Subgroup.coe_mul, Subgroup.coe_inv] using hnorm c trivial hc n hn⟩
  have hcard : Nat.card (Q.subgroupOf (Subgroup.centralizer ({t} : Set K))) = Nat.card Q :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hQC).toEquiv
  have hle : Q.subgroupOf (Subgroup.centralizer ({t} : Set K)) ≤
      CFSG.oddCore (Subgroup.centralizer ({t} : Set K)) := le_sSup ⟨hn, hcard ▸ hodd⟩
  rw [h, le_bot_iff, Subgroup.subgroupOf_eq_bot] at hle
  exact hle.eq_bot_of_le hQC

theorem CentOddFreeIn.map_equiv {K K' : Type*} [Group K] [Group K'] (e : K ≃* K') {t : K}
    (h : CentOddFreeIn (⊤ : Subgroup K) t) : CentOddFreeIn (⊤ : Subgroup K') (e t) := by
  intro Q _ hQt hnorm hodd
  have hmem : ∀ q, q ∈ Q.map e.symm.toMonoidHom ↔ e q ∈ Q := fun q => by
    rw [Subgroup.mem_map_equiv, MulEquiv.symm_symm]
  have h1 := h (Q.map e.symm.toMonoidHom) le_top (fun q hq => by
      rw [hmem] at hq
      apply e.injective
      rw [map_mul, map_mul]
      exact hQt _ hq)
    (fun c _ hc q hq => by
      rw [hmem] at hq ⊢
      have hc' : e c * e t = e t * e c := by rw [← map_mul, ← map_mul, hc]
      simpa only [map_mul, map_inv] using hnorm (e c) trivial hc' (e q) hq)
    (by rw [Subgroup.card_map_of_injective e.symm.injective]; exact hodd)
  exact (Subgroup.map_eq_bot_iff_of_injective Q e.symm.injective).mp h1

theorem card_map_mulAut_conj {G : Type*} [Group G] (H : Subgroup G) (g : G) :
    Nat.card (H.map (MulAut.conj g).toMonoidHom) = Nat.card H :=
  Subgroup.card_map_of_injective (MulAut.conj g).injective

theorem CentOddFreeIn.conj {K : Type*} [Group K] {t : K} (h : CentOddFreeIn (⊤ : Subgroup K) t)
    (g : K) : CentOddFreeIn (⊤ : Subgroup K) (g * t * g⁻¹) :=
  h.map_equiv (MulAut.conj g)

theorem CentOddFreeIn.of_subtype {G : Type*} [Group G] {Γ : Subgroup G} {t : G} (ht : t ∈ Γ)
    (h : CentOddFreeIn (⊤ : Subgroup Γ) ⟨t, ht⟩) : CentOddFreeIn Γ t := by
  intro Q hQΓ hQt hnorm hodd
  have h1 := h (Q.subgroupOf Γ) le_top
    (fun q hq => Subtype.ext (hQt _ (Subgroup.mem_subgroupOf.mp hq)))
    (fun c _ hc q hq => by
      rw [Subgroup.mem_subgroupOf] at hq ⊢
      simpa only [Subgroup.coe_mul, Subgroup.coe_inv] using
        hnorm c c.2 (congrArg Subtype.val hc) q hq)
    (by rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hQΓ).toEquiv]; exact hodd)
  rw [Subgroup.subgroupOf_eq_bot] at h1
  exact h1.eq_bot_of_le hQΓ

theorem CentOddFreeIn.of_equiv {G K : Type*} [Group G] [Group K] {Γ : Subgroup G} (e : K ≃* Γ)
    {t : G} (ht : t ∈ Γ) (h : CentOddFreeIn Γ t) :
    CentOddFreeIn (⊤ : Subgroup K) (e.symm ⟨t, ht⟩) := by
  intro Q _ hQt hnorm hodd
  set f : K →* G := Γ.subtype.comp e.toMonoidHom with hfdef
  have hf : Function.Injective f := Subtype.val_injective.comp e.injective
  have hft : f (e.symm ⟨t, ht⟩) = t := by
    rw [hfdef, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulEquiv.apply_symm_apply]
    rfl
  have h1 := h (Q.map f) (by
      rintro _ ⟨q, -, rfl⟩
      exact (e q).2)
    (by
      rintro _ ⟨q, hq, rfl⟩
      rw [← hft, ← map_mul, ← map_mul, hQt q hq])
    (by
      rintro c hc hct _ ⟨q, hq, rfl⟩
      have hfc : f (e.symm ⟨c, hc⟩) = c := by
        rw [hfdef, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulEquiv.apply_symm_apply]
        rfl
      have hc' : e.symm ⟨c, hc⟩ * e.symm ⟨t, ht⟩ = e.symm ⟨t, ht⟩ * e.symm ⟨c, hc⟩ := by
        apply hf
        rw [map_mul, map_mul, hfc, hft, hct]
      refine ⟨e.symm ⟨c, hc⟩ * q * (e.symm ⟨c, hc⟩)⁻¹, hnorm _ trivial hc' q hq, ?_⟩
      rw [map_mul, map_mul, map_inv, hfc])
    (by rw [Subgroup.card_map_of_injective hf]; exact hodd)
  exact (Subgroup.map_eq_bot_iff_of_injective Q hf).mp h1

theorem CentOddFreeIn.noOddNormal {K : Type*} [Group K] {t : K}
    (h : CentOddFreeIn (⊤ : Subgroup K) t) :
    ∀ R : Subgroup (Subgroup.centralizer ({t} : Set K)), R.Normal → Odd (Nat.card R) → R = ⊥ := by
  intro R hR hodd
  have h1 := h (R.map (Subgroup.centralizer ({t} : Set K)).subtype) le_top
    (by
      rintro _ ⟨r, -, rfl⟩
      exact Subgroup.mem_centralizer_singleton_iff.mp r.2)
    (by
      rintro c - hc _ ⟨r, hr, rfl⟩
      have hc' : c ∈ Subgroup.centralizer ({t} : Set K) :=
        Subgroup.mem_centralizer_singleton_iff.mpr hc
      exact ⟨⟨c, hc'⟩ * r * ⟨c, hc'⟩⁻¹, hR.conj_mem r hr ⟨c, hc'⟩, rfl⟩)
    (by rw [Subgroup.card_map_of_injective Subtype.val_injective]; exact hodd)
  exact (Subgroup.map_eq_bot_iff_of_injective R Subtype.val_injective).mp h1

theorem cores_of_noOddNormal {G : Type*} [Group G] [Finite G]
    (h : ∀ R : Subgroup G, R.Normal → Odd (Nat.card R) → R = ⊥) :
    CFSG.piCore {p : Nat.Primes | p.1 ≠ 2} G = ⊥ ∧ CFSG.pPrimeCore 2 G = ⊥ ∧
      CFSG.oddCore G = ⊥ := by
  refine ⟨?_, CFSG.pPrimeCore_eq_bot_iff.2 fun K hK hc => h K hK (Nat.coprime_two_left.1 hc),
    sSup_eq_bot.2 fun N hN => h N hN.1 hN.2⟩
  refine h _ inferInstance ?_
  rw [← Nat.not_even_iff_odd, even_iff_two_dvd]
  intro h2
  exact (CFSG.LocalCores.piCore_isPiSubgroup {p : Nat.Primes | p.1 ≠ 2} ⟨2, Nat.prime_two⟩ h2) rfl

end CFSG.Sporadic.Co1Schreier.OddGen
