module

public import CFSG.RankThree.PartTwo.Sec16.Item163StepsAltProofTools
import CFSG.LocalAnalysis.SectionRank.Ccomm.FrattiniAut
import CFSG.GroupTheory.Fitting.CharacteristicP
import CFSG.CharacterTheory.Semidihedral.Principal.CoprimeFixedPointLifting
import CFSG.RankThree.PartTwo.Sec17.Item17HeadProofDefs

public section

namespace CFSG.RankThree.PartTwo.Sec16.Step163Alt

open scoped commutatorElement

theorem mul_mul_eq_one_of_fixedPointFree {V : Type*} [CommGroup V] (u : MulAut V)
    (hu3 : u ^ 3 = 1) (hfix : ∀ v : V, u v = v → v = 1) (x : V) :
    x * u x * u (u x) = 1 := by
  apply hfix
  have h3 : u (u (u x)) = x := by
    have := congrArg (fun σ : MulAut V => σ x) hu3
    simpa [pow_succ, MulAut.mul_apply] using this
  rw [map_mul, map_mul, h3]
  rw [mul_comm (u x * u (u x)) x, mul_assoc]

theorem pow_mod_seven {M : Type*} [Monoid M] {t : M} (ht7 : t ^ 7 = 1) (n : ℕ) :
    t ^ n = t ^ (n % 7) := by
  conv_lhs => rw [← Nat.div_add_mod n 7, pow_add, pow_mul, ht7, one_pow, one_mul]

theorem mul_pow_eq_of_conj {M : Type*} [Group M] {t c : M} (htc : c * t * c⁻¹ = t ^ 2)
    (k : ℕ) : c * t ^ k = t ^ (2 * k) * c := by
  have h1 : c * t = t ^ 2 * c := by
    rw [← htc, inv_mul_cancel_right]
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, ← mul_assoc, ih, mul_assoc, h1, ← mul_assoc, ← pow_add,
      show 2 * k + 2 = 2 * (k + 1) by ring]

theorem eq_one_of_frobenius_twentyOne {V : Type*} [CommGroup V] [Finite V] (hV : IsPGroup 2 V)
    (t c : MulAut V) (ht7 : t ^ 7 = 1) (hc3 : c ^ 3 = 1) (htc : c * t * c⁻¹ = t ^ 2)
    (hfix : ∀ v : V, c v = v → v = 1) : t = 1 := by
  classical
  have hct := mul_pow_eq_of_conj htc
  have hinv : ∀ j : ℕ, (t ^ j)⁻¹ = t ^ (6 * j) := by
    intro j
    rw [inv_eq_iff_mul_eq_one, ← pow_add, show j + 6 * j = 7 * j by ring, pow_mul, ht7, one_pow]
  have hu : ∀ j : ℕ, t ^ (6 * j) * c = t ^ j * c * (t ^ j)⁻¹ := by
    intro j
    rw [hinv, mul_assoc, hct, ← mul_assoc, ← pow_add,
      pow_mod_seven ht7 (j + 2 * (6 * j)), pow_mod_seven ht7 (6 * j)]
    congr 2
    omega
  have hu3 : ∀ j : ℕ, (t ^ (6 * j) * c) ^ 3 = 1 := by
    intro j
    rw [hu, conj_pow, hc3, mul_one, mul_inv_cancel]
  have hufix : ∀ j : ℕ, ∀ v : V, (t ^ (6 * j) * c) v = v → v = 1 := by
    intro j v hv
    rw [hu] at hv
    have e : (t ^ j * c * (t ^ j)⁻¹) v = (t ^ j) (c ((t ^ j)⁻¹ v)) := rfl
    rw [e] at hv
    have h1 : c ((t ^ j)⁻¹ v) = (t ^ j)⁻¹ v := by
      calc c ((t ^ j)⁻¹ v) = (t ^ j)⁻¹ ((t ^ j) (c ((t ^ j)⁻¹ v))) :=
            (MulAut.inv_apply_self _ _ _).symm
        _ = (t ^ j)⁻¹ v := by rw [hv]
    have h2 := hfix _ h1
    calc v = (t ^ j) ((t ^ j)⁻¹ v) := (MulAut.apply_inv_self _ _ _).symm
      _ = 1 := by rw [h2, map_one]
  have hsq : ∀ j : ℕ, (t ^ (6 * j) * c) * (t ^ (6 * j) * c) = t ^ (4 * j) * c ^ 2 := by
    intro j
    rw [mul_assoc, ← mul_assoc c, hct, ← mul_assoc, ← mul_assoc, ← pow_add, mul_assoc, ← sq,
      pow_mod_seven ht7 (6 * j + 2 * (6 * j)), pow_mod_seven ht7 (4 * j)]
    congr 2
    omega
  have hnorm : ∀ (j : ℕ) (x : V), x * (t ^ (6 * j)) (c x) * (t ^ (4 * j)) (c (c x)) = 1 := by
    intro j x
    have h := mul_mul_eq_one_of_fixedPointFree _ (hu3 j) (hufix j) x
    have e1 : (t ^ (6 * j) * c) x = (t ^ (6 * j)) (c x) := rfl
    have e2 : (t ^ (6 * j) * c) ((t ^ (6 * j) * c) x) = (t ^ (4 * j)) (c (c x)) := by
      rw [← MulAut.mul_apply, hsq, MulAut.mul_apply, sq, MulAut.mul_apply]
    rwa [e2, e1] at h
  set S : V → V := fun y => ∏ i : Fin 7, (t ^ (i : ℕ)) y with hS
  have hSmul : ∀ y z : V, S (y * z) = S y * S z := by
    intro y z
    simp only [hS, map_mul, Finset.prod_mul_distrib]
  have hreindex : ∀ (m : ℕ) (hm : Function.Bijective
      (fun j : Fin 7 => (⟨(m * j.val) % 7, Nat.mod_lt _ (by norm_num)⟩ : Fin 7))) (y : V),
      ∏ j : Fin 7, (t ^ (m * (j : ℕ))) y = S y := by
    intro m hm y
    refine Fintype.prod_bijective _ hm _ _ fun j => ?_
    rw [pow_mod_seven ht7 (m * (j : ℕ))]
  have hb6 : Function.Bijective
      (fun j : Fin 7 => (⟨(6 * j.val) % 7, Nat.mod_lt _ (by norm_num)⟩ : Fin 7)) := by
    decide
  have hb4 : Function.Bijective
      (fun j : Fin 7 => (⟨(4 * j.val) % 7, Nat.mod_lt _ (by norm_num)⟩ : Fin 7)) := by
    decide
  have hb1 : Function.Bijective
      (fun j : Fin 7 => (⟨(1 * j.val) % 7, Nat.mod_lt _ (by norm_num)⟩ : Fin 7)) := by
    decide
  have hx7 : ∀ x : V, x ^ 7 = S x := by
    intro x
    have hprod : ∏ j : Fin 7, (x * (t ^ (6 * (j : ℕ))) (c x) * (t ^ (4 * (j : ℕ))) (c (c x))) =
        1 := by
      simp [hnorm]
    rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ,
      Fintype.card_fin, hreindex 6 hb6, hreindex 4 hb4] at hprod
    have hS1 : S x * S (c x) * S (c (c x)) = 1 := by
      rw [← hSmul, ← hSmul, mul_mul_eq_one_of_fixedPointFree c hc3 hfix x]
      simp [hS]
    calc x ^ 7 = x ^ 7 * S (c x) * S (c (c x)) * (S (c x) * S (c (c x)))⁻¹ := by group
      _ = S x * S (c x) * S (c (c x)) * (S (c x) * S (c (c x)))⁻¹ := by rw [hprod, hS1]
      _ = S x := by group
  have htS : ∀ y : V, t (S y) = S y := by
    intro y
    have h1 : t (S y) = ∏ i : Fin 7, (t ^ ((i : ℕ) + 1)) y := by
      simp only [hS, map_prod]
      refine Finset.prod_congr rfl fun i _ => ?_
      rw [pow_succ', MulAut.mul_apply]
    rw [h1]
    have h2 : ∏ i : Fin 7, (t ^ ((i : ℕ) + 1)) y = ∏ i : Fin 7, (t ^ (1 * (i : ℕ))) y := by
      have hb : Function.Bijective
          (fun j : Fin 7 => (⟨((j : ℕ) + 1) % 7, Nat.mod_lt _ (by norm_num)⟩ : Fin 7)) := by
        decide
      refine Fintype.prod_bijective _ hb _ _ fun j => ?_
      rw [pow_mod_seven ht7 ((j : ℕ) + 1), pow_mod_seven ht7 (1 * _)]
      simp
    rw [h2, hreindex 1 hb1]
  refine MulEquiv.ext fun x => ?_
  have h7 : (t x * x⁻¹) ^ 7 = 1 := by
    rw [mul_pow, inv_pow, ← map_pow, hx7, htS, ← hx7, mul_inv_cancel]
  obtain ⟨k, hk⟩ := hV (t x * x⁻¹)
  have ho : orderOf (t x * x⁻¹) ∣ Nat.gcd 7 (2 ^ k) :=
    Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one h7) (orderOf_dvd_of_pow_eq_one hk)
  rw [Nat.Coprime.gcd_eq_one (Nat.Coprime.pow_right k (by norm_num))] at ho
  have h1 : t x * x⁻¹ = 1 := orderOf_eq_one_iff.mp (Nat.dvd_one.mp ho)
  rw [MulAut.one_apply]
  exact mul_inv_eq_one.mp h1

theorem eq_one_of_frobenius_twentyOne' {V : Type*} [Group V] [Finite V]
    (hcomm : ∀ a b : V, a * b = b * a) (hV : IsPGroup 2 V) (t c : MulAut V) (ht7 : t ^ 7 = 1)
    (hc3 : c ^ 3 = 1) (htc : c * t * c⁻¹ = t ^ 2) (hfix : ∀ v : V, c v = v → v = 1) :
    t = 1 := by
  let _ : CommGroup V := { (inferInstance : Group V) with mul_comm := hcomm }
  exact eq_one_of_frobenius_twentyOne hV t c ht7 hc3 htc hfix

theorem eq_one_of_pow_eq_one_of_coprime {X : Type*} [Monoid X] {x : X} {m n : ℕ}
    (hmn : Nat.Coprime m n) (hm : x ^ m = 1) (hn : x ^ n = 1) : x = 1 := by
  have h := pow_gcd_eq_one.mpr ⟨hm, hn⟩
  rwa [Nat.Coprime.gcd_eq_one hmn, pow_one] at h

variable {G : Type} [Group G] [Finite G]

theorem pCoreOf_inf_centralizer_ne_bot_of_twoCycles {Y : Subgroup G} {c g : G}
    (hcN : c ∈ Subgroup.normalizer (Y : Set G)) (hc3 : c ^ 3 = 1) (hgY : g ∈ Y)
    (φ : ↥Y ⧸ CFSG.pCore 2 ↥Y ≃* alternatingGroup (Fin 7))
    (hcg : ∀ y ∈ Y, (g * y * g⁻¹)⁻¹ * (c * y * c⁻¹) ∈ CFSG.Open.pCoreOf 2 Y)
    (hσ : ((φ (QuotientGroup.mk' (CFSG.pCore 2 ↥Y) ⟨g, hgY⟩) : alternatingGroup (Fin 7)) :
      Equiv.Perm (Fin 7)).cycleType = {3, 3})
    (hF : CFSG.generalizedFitting ↥Y = CFSG.pCore 2 ↥Y) :
    CFSG.Open.pCoreOf 2 Y ⊓ Subgroup.centralizer {c} ≠ ⊥ := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hp7 : Nat.Prime 7 := by norm_num
  have : Fact (Nat.Prime 7) := ⟨hp7⟩
  set N := CFSG.pCore 2 ↥Y with hN
  set π := QuotientGroup.mk' N with hπ
  set O := CFSG.Open.pCoreOf 2 Y with hO
  set g₀ : ↥Y := ⟨g, hgY⟩ with hg₀
  set ψ7 : (↥Y ⧸ N) →* Equiv.Perm (Fin 7) :=
    (alternatingGroup (Fin 7)).subtype.comp φ.toMonoidHom with hψ7
  have hψinj : Function.Injective ψ7 := Subtype.val_injective.comp φ.injective
  have hOp : IsPGroup 2 O := CFSG.LieType.BorelTits.pCoreOf_isPGroup (r := 2) Y
  have hYO : Y ≤ Subgroup.normalizer (O : Set G) :=
    CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 Y
  have hcO : c ∈ Subgroup.normalizer (O : Set G) :=
    CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 Y hcN
  have hNp : IsPGroup 2 N := CFSG.pCore_isPGroup
  have hact : ∀ y : ↥Y, π ⟨c * y * c⁻¹, (Subgroup.mem_normalizer_iff.mp hcN y).mp y.2⟩ =
      π g₀ * π y * (π g₀)⁻¹ := by
    intro y
    rw [← map_inv, ← map_mul, ← map_mul, eq_comm, hπ, mk_eq_mk_iff]
    simpa using hcg y y.2
  obtain ⟨z, hzA, hz7, hσz⟩ :=
    CFSG.RankThree.PartTwo.KFacts.KP2.exists_orderOf_seven_of_cycleType hσ
  set zb : ↥Y ⧸ N := φ.symm ⟨z, hzA⟩ with hzb
  have hψz : ψ7 zb = z := by simp [hψ7, hzb]
  have hgz : π g₀ * zb * (π g₀)⁻¹ = zb ^ 2 := by
    apply hψinj
    rw [map_mul, map_mul, map_inv, map_pow, hψz]
    exact hσz
  have hzb7 : zb ^ 7 = 1 := by
    apply hψinj
    rw [map_pow, hψz, map_one]
    have h := pow_orderOf_eq_one z
    rwa [hz7] at h
  have hzb1 : zb ≠ 1 := by
    intro h1
    have : ψ7 zb = 1 := by rw [h1, map_one]
    rw [hψz] at this
    rw [this, orderOf_one] at hz7
    omega
  have hconjk : ∀ k : ℤ, π g₀ * zb ^ k * (π g₀)⁻¹ = (zb ^ k) ^ 2 := by
    intro k
    rw [← conj_zpow, hgz, sq, (Commute.refl zb).mul_zpow, sq]
  have hz7mem : ∀ q ∈ Subgroup.zpowers zb, q ^ 7 = 1 := by
    intro q hq
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hq
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hzb7, one_zpow]
  set P₀ : Subgroup ↥Y := (Subgroup.zpowers zb).comap π with hP₀
  set P : Subgroup G := P₀.map Y.subtype with hP
  have hPY : P ≤ Y := Subgroup.map_subtype_le _
  have hcP : Subgroup.zpowers c ≤ Subgroup.normalizer (P : Set G) := by
    rw [Subgroup.zpowers_le]
    refine Subgroup.mem_normalizer_fintype fun x hx => ?_
    obtain ⟨p, hp, rfl⟩ := hx
    refine ⟨⟨c * p * c⁻¹, (Subgroup.mem_normalizer_iff.mp hcN p).mp p.2⟩, ?_, rfl⟩
    show π ⟨c * p * c⁻¹, _⟩ ∈ Subgroup.zpowers zb
    rw [hact]
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp (Subgroup.mem_comap.mp hp)
    rw [← hk, hconjk]
    exact Subgroup.pow_mem _ (Subgroup.zpow_mem_zpowers zb k) 2
  have hP3 : ¬ 3 ∣ Nat.card P := by
    intro h3
    obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' 3 h3
    obtain ⟨p, hp, hpx⟩ := Subgroup.mem_map.mp x.2
    have hpo : orderOf p = 3 := by
      have h1 : orderOf (x : G) = 3 := by rw [Subgroup.orderOf_coe, hx]
      rw [← hpx] at h1
      rwa [Subgroup.coe_subtype, Subgroup.orderOf_coe] at h1
    have hπp : π p = 1 := by
      have h7 := hz7mem _ (Subgroup.mem_comap.mp hp)
      have h3' : (π p) ^ 3 = 1 := by rw [← map_pow, ← hpo, pow_orderOf_eq_one, map_one]
      exact eq_one_of_pow_eq_one_of_coprime (by norm_num) h7 h3'
    have hpN : p ∈ N := by rwa [hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hπp
    obtain ⟨m, hm⟩ := hNp ⟨p, hpN⟩
    have h2 : p ^ 2 ^ m = 1 := by simpa using congrArg Subtype.val hm
    have hp3 : p ^ 3 = 1 := by
      have h := pow_orderOf_eq_one p
      rwa [hpo] at h
    have hp1 : p = 1 :=
      eq_one_of_pow_eq_one_of_coprime (Nat.Coprime.pow_left m (by norm_num)) h2 hp3
    rw [hp1, orderOf_one] at hpo
    omega
  have hcp3 : IsPGroup 3 (Subgroup.zpowers c) := by
    rintro ⟨x, hx⟩
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
    refine ⟨1, Subtype.ext ?_⟩
    simp only [pow_one, Subgroup.coe_pow, Subgroup.coe_one]
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hc3, one_zpow]
  obtain ⟨T, hTP, hT7, hcT, hTcard⟩ :=
    CFSG.RankThree.PartTwo.Sec17.HeadProof.exists_invariant_sylow hcp3 hP3 hcP hp7
  have h7P : 7 ∣ Nat.card P := by
    obtain ⟨y, hy⟩ := QuotientGroup.mk'_surjective N zb
    have hyP₀ : y ∈ P₀ := Subgroup.mem_comap.mpr (by
      rw [show π y = zb from hy]
      exact Subgroup.mem_zpowers zb)
    have h1 : orderOf zb ∣ orderOf y := by
      rw [← hy]
      exact orderOf_map_dvd _ y
    have hzbo : orderOf zb = 7 := orderOf_eq_prime hzb7 hzb1
    have h2 : orderOf (y : G) ∣ Nat.card P :=
      Subgroup.orderOf_dvd_natCard P (Subgroup.mem_map_of_mem Y.subtype hyP₀)
    rw [Subgroup.orderOf_coe] at h2
    exact (hzbo ▸ h1).trans h2
  have hT1 : T ≠ ⊥ := by
    intro hbot
    rw [hbot, Subgroup.card_bot] at hTcard
    have hpos : 0 < (Nat.card P).factorization 7 :=
      hp7.factorization_pos_of_dvd Nat.card_pos.ne' h7P
    have : 7 ≤ 7 ^ (Nat.card P).factorization 7 := Nat.le_self_pow hpos.ne' 7
    omega
  obtain ⟨⟨t, htT⟩, ht1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hT1
  have ht1' : t ≠ 1 := fun h => ht1 (Subtype.ext h)
  have htP : t ∈ P := hTP htT
  have htY : t ∈ Y := hPY htP
  have hTO : ∀ x ∈ T, x ∈ O → x = 1 := by
    intro x hxT hxO
    obtain ⟨a, ha⟩ := hT7 ⟨x, hxT⟩
    obtain ⟨b, hb⟩ := hOp ⟨x, hxO⟩
    have h1 : x ^ 7 ^ a = 1 := by simpa using congrArg Subtype.val ha
    have h2 : x ^ 2 ^ b = 1 := by simpa using congrArg Subtype.val hb
    exact eq_one_of_pow_eq_one_of_coprime (Nat.Coprime.pow a b (by norm_num)) h1 h2
  obtain ⟨t₀, ht₀P, ht₀⟩ := Subgroup.mem_map.mp htP
  have ht7 : t ^ 7 = 1 := by
    have h1 : π (t₀ ^ 7) = 1 := by
      rw [map_pow]
      exact hz7mem _ (Subgroup.mem_comap.mp ht₀P)
    have h2 : t₀ ^ 7 ∈ N := by rwa [hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
    have h3 : t ^ 7 ∈ O := by
      rw [← ht₀]
      simpa using (mem_pCore_two_iff (t₀ ^ 7)).mp h2
    exact hTO _ (pow_mem htT 7) h3
  have hctc : c * t * c⁻¹ = t ^ 2 := by
    have hct : c * t * c⁻¹ ∈ T :=
      (Subgroup.mem_normalizer_iff.mp (hcT (Subgroup.mem_zpowers c)) t).mp htT
    have h1 : π ⟨c * t₀ * c⁻¹, (Subgroup.mem_normalizer_iff.mp hcN t₀).mp t₀.2⟩ =
        π (t₀ ^ 2) := by
      rw [hact, map_pow]
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp (Subgroup.mem_comap.mp ht₀P)
      rw [← hk, hconjk]
    have h2 := (mk_eq_mk_iff _ _).mp h1
    have h3 : (c * t * c⁻¹)⁻¹ * t ^ 2 = 1 := by
      refine hTO _ (T.mul_mem (T.inv_mem hct) (pow_mem htT 2)) ?_
      rw [← ht₀]
      simpa using h2
    exact inv_mul_eq_one.mp h3
  have htnc : ¬ ∀ o ∈ O, o * t = t * o := by
    intro hc
    have hmem : t₀ ∈ Subgroup.centralizer (CFSG.generalizedFitting ↥Y : Set ↥Y) := by
      rw [hF, Subgroup.mem_centralizer_iff]
      intro q hq
      apply Subtype.ext
      have hqO : (q : G) ∈ O := (mem_pCore_two_iff q).mp hq
      have ht₀' : (t₀ : G) = t := ht₀
      simp only [Subgroup.coe_mul, ht₀']
      exact hc _ hqO
    have h1 := CFSG.centralizer_generalizedFitting_le ↥Y hmem
    rw [hF] at h1
    have htO : t ∈ O := by
      rw [← ht₀]
      exact (mem_pCore_two_iff t₀).mp h1
    exact ht1' (hTO t htT htO)
  intro hbot
  have hcfix : ∀ o ∈ O, c * o * c⁻¹ = o → o = 1 := by
    intro o ho hco
    have hmem : o ∈ O ⊓ Subgroup.centralizer {c} := by
      refine Subgroup.mem_inf.mpr ⟨ho, Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩
      calc o * c = (c * o * c⁻¹) * c := by rw [hco]
        _ = c * o := by group
    rwa [hbot, Subgroup.mem_bot] at hmem
  set ρ := O.normalizerMonoidHom with hρ
  set tN : ↥(Subgroup.normalizer (O : Set G)) := ⟨t, hYO htY⟩ with htN
  set cN : ↥(Subgroup.normalizer (O : Set G)) := ⟨c, hcO⟩ with hcNdef
  have htN7 : tN ^ 7 = 1 := Subtype.ext (by simpa using ht7)
  have hcN3 : cN ^ 3 = 1 := Subtype.ext (by simpa using hc3)
  have htcN : cN * tN * cN⁻¹ = tN ^ 2 := Subtype.ext (by simpa using hctc)
  set Φ := CFSG.SectionRank.Ccomm.autQuotient (frattini ↥O) with hΦ
  have hO2 : IsPGroup 2 ↥O := hOp
  have : Fact (IsPGroup 2 ↥O) := ⟨hO2⟩
  have hVcomm : ∀ a b : ↥O ⧸ frattini ↥O, a * b = b * a := by
    intro a b
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective a
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective b
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq]
    have hcomm : ⁅y⁻¹, x⁻¹⁆ ∈ _root_.commutator ↥O :=
      Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _)
    have h1 := CFSG.commutator_le_frattini_of_isPGroup (R := ↥O) (p := 2) hcomm
    rw [commutatorElement_def, inv_inv, inv_inv] at h1
    rwa [mul_inv_rev, ← mul_assoc]
  have hVp : IsPGroup 2 (↥O ⧸ frattini ↥O) :=
    hO2.of_surjective (QuotientGroup.mk' _) (QuotientGroup.mk'_surjective _)
  have hτ7 : Φ (ρ tN) ^ 7 = 1 := by rw [← map_pow, ← map_pow, htN7, map_one, map_one]
  have hκ3 : Φ (ρ cN) ^ 3 = 1 := by rw [← map_pow, ← map_pow, hcN3, map_one, map_one]
  have hτκ : Φ (ρ cN) * Φ (ρ tN) * (Φ (ρ cN))⁻¹ = Φ (ρ tN) ^ 2 := by
    rw [← map_inv, ← map_mul, ← map_mul, ← map_inv, ← map_mul, ← map_mul, htcN, map_pow,
      map_pow]
  have hκfix : ∀ v, Φ (ρ cN) v = v → v = 1 := by
    intro v hv
    have hzO : Subgroup.zpowers c ≤ Subgroup.normalizer (O : Set G) :=
      Subgroup.zpowers_le.mpr hcO
    set α : ↥(Subgroup.zpowers c) →* MulAut ↥O :=
      ρ.comp (Subgroup.inclusion hzO) with hα
    have hαN : ∀ a : ↥(Subgroup.zpowers c), ∀ n ∈ frattini ↥O, α a n ∈ frattini ↥O := by
      intro a n hn
      have h : (frattini ↥O).map (α a).toMonoidHom = frattini ↥O :=
        Subgroup.characteristic_iff_map_eq.mp inferInstance (α a)
      exact h ▸ Subgroup.mem_map_of_mem (α a).toMonoidHom hn
    have hcop : ¬ 3 ∣ Nat.card (frattini ↥O) := by
      obtain ⟨m, hm⟩ := IsPGroup.iff_card.mp (hO2.to_subgroup (frattini ↥O))
      rw [hm]
      intro h3
      have := (Nat.prime_dvd_prime_iff_eq Nat.prime_three Nat.prime_two).mp
        (Nat.prime_three.dvd_of_dvd_pow h3)
      omega
    set gen : ↥(Subgroup.zpowers c) := ⟨c, Subgroup.mem_zpowers c⟩ with hgen
    have hgenv : CFSG.Semidihedral.Principal.CoprimeFixedPoint.quotientAction α
        (frattini ↥O) hαN gen v = v := by
      obtain ⟨r, rfl⟩ := QuotientGroup.mk_surjective v
      rw [CFSG.Semidihedral.Principal.CoprimeFixedPoint.quotientAction_mk]
      rw [CFSG.SectionRank.Ccomm.autQuotient_mk] at hv
      exact hv
    have hfixv : v ∈ {q : ↥O ⧸ frattini ↥O | ∀ a : ↥(Subgroup.zpowers c),
        CFSG.Semidihedral.Principal.CoprimeFixedPoint.quotientAction α (frattini ↥O) hαN a q =
          q} := by
      intro a
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp a.2
      have ha : a = gen ^ k := Subtype.ext (by rw [Subgroup.coe_zpow, ← hk])
      have hst : CFSG.Semidihedral.Principal.CoprimeFixedPoint.quotientAction α
          (frattini ↥O) hαN gen ∈ MulAction.stabilizer (MulAut (↥O ⧸ frattini ↥O)) v := by
        rw [MulAction.mem_stabilizer_iff, MulAut.smul_def]
        exact hgenv
      have := (MulAction.stabilizer (MulAut (↥O ⧸ frattini ↥O)) v).zpow_mem hst k
      rw [MulAction.mem_stabilizer_iff, MulAut.smul_def, ← map_zpow] at this
      rw [ha]
      exact this
    rw [CFSG.Semidihedral.Principal.coprime_fixed_point_lifting 3 hcp3 α _ hαN hcop] at hfixv
    obtain ⟨r, hrfix, hr⟩ := hfixv
    have hcr : c * (r : G) * c⁻¹ = r := by
      have h1 := congrArg Subtype.val (hrfix gen)
      rw [hα, MonoidHom.comp_apply, Subgroup.normalizerMonoidHom_apply_apply_coe] at h1
      exact h1
    have hr1 := hcfix r r.2 hcr
    rw [← hr, show r = 1 from Subtype.ext hr1, map_one]
  have hτ1 : Φ (ρ tN) = 1 :=
    eq_one_of_frobenius_twentyOne' hVcomm hVp _ _ hτ7 hκ3 hτκ hκfix
  have hkp := CFSG.SectionRank.Ccomm.isPGroup_ker_autQuotient_frattini hO2
  obtain ⟨m, hm⟩ := hkp ⟨ρ tN, hτ1⟩
  have hm' : ρ tN ^ 2 ^ m = 1 := by simpa using congrArg Subtype.val hm
  have hρ7 : ρ tN ^ 7 = 1 := by rw [← map_pow, htN7, map_one]
  have hρ1 : ρ tN = 1 :=
    eq_one_of_pow_eq_one_of_coprime (Nat.Coprime.pow_left m (by norm_num)) hm' hρ7
  apply htnc
  intro o ho
  have h1 := congrArg (fun σ : MulAut ↥O => ((σ ⟨o, ho⟩ : ↥O) : G)) hρ1
  simp only [MulAut.one_apply] at h1
  rw [hρ, Subgroup.normalizerMonoidHom_apply_apply_coe] at h1
  calc o * t = (t * o * t⁻¹) * t := by rw [show t * o * t⁻¹ = o from h1]
    _ = t * o := by group

end CFSG.RankThree.PartTwo.Sec16.Step163Alt
