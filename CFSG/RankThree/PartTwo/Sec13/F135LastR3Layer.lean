module

public import CFSG.GroupTheory.LocalCores.Layer
public import CFSG.GroupTheory.Fitting.CharacteristicP
public import CFSG.GroupTheory.ElementaryAbelianTransport
public import CFSG.RankThree.PartTwo.Sec3.Item38

public section

namespace CFSG.RankThree.PartTwo.Sec13.F135Last



open CFSG

theorem r3L1_isComponent_map_subtype {N : Type*} [Group N] (H : Subgroup N) [H.Normal]
    {K : Subgroup H} (hK : CFSG.IsComponent K) : CFSG.IsComponent (K.map H.subtype) :=
  ⟨CFSG.LocalCores.isQuasisimple_of_mulEquiv
      (Subgroup.equivMapOfInjective K H.subtype H.subtype_injective) hK.1,
    Subgroup.IsSubnormal.trans' hK.2 (Subgroup.Normal.isSubnormal (inferInstance : H.Normal))⟩

theorem r3L1_centralizer_layer_normal (N : Type*) [Group N] :
    (Subgroup.centralizer (CFSG.layer N : Set N)).Normal := by
  have hLchar : (CFSG.layer N).Characteristic := CFSG.LocalCores.layer_characteristic
  have hLn : (CFSG.layer N).Normal := by
    haveI := hLchar
    infer_instance
  refine ⟨fun x hx g => ?_⟩
  rw [Subgroup.mem_centralizer_iff] at hx ⊢
  intro l hl
  have hl' : g⁻¹ * l * g ∈ CFSG.layer N := by
    have h1 := hLn.conj_mem l hl g⁻¹
    rwa [inv_inv] at h1
  have key := hx (g⁻¹ * l * g) hl'
  calc l * (g * x * g⁻¹) = g * ((g⁻¹ * l * g) * x) * g⁻¹ := by group
    _ = g * (x * (g⁻¹ * l * g)) * g⁻¹ := by rw [key]
    _ = g * x * g⁻¹ * l := by group

theorem r3L1_no_component_of_le_centralizer {N : Type*} [Group N] (H : Subgroup N) [H.Normal]
    (hH : H ≤ Subgroup.centralizer (CFSG.layer N : Set N)) :
    ∀ K : Subgroup H, ¬ CFSG.IsComponent K := by
  intro K hK
  have hK' : CFSG.IsComponent (K.map H.subtype) := r3L1_isComponent_map_subtype H hK
  have hle : K.map H.subtype ≤ CFSG.layer N := CFSG.LocalCores.component_le_layer hK'
  have hKH : K.map H.subtype ≤ H := by
    rintro _ ⟨k, _, rfl⟩
    exact k.2
  have hcomm : ⁅K.map H.subtype, CFSG.layer N⁆ = ⊥ := by
    rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
    exact hKH.trans hH
  have hperf : ⁅K.map H.subtype, K.map H.subtype⁆ = K.map H.subtype :=
    Subgroup.isPerfect_iff.mp hK'.1.1
  have hbot : K.map H.subtype = ⊥ := by
    apply le_bot_iff.mp
    calc K.map H.subtype = ⁅K.map H.subtype, K.map H.subtype⁆ := hperf.symm
      _ ≤ ⁅K.map H.subtype, CFSG.layer N⁆ :=
          Subgroup.commutator_mono le_rfl hle
      _ = ⊥ := hcomm
  have hnt : Nontrivial (K.map H.subtype) := CFSG.LocalCores.isQuasisimple_nontrivial hK'.1
  exact ((Subgroup.nontrivial_iff_ne_bot _).mp hnt) hbot

theorem r3L1_pPrimeCore_eq_bot_of_normal {N : Type*} [Group N] [Finite N] {p : ℕ} [Fact p.Prime]
    (hcore : CFSG.pPrimeCore p N = ⊥) (H : Subgroup N) [H.Normal] :
    CFSG.pPrimeCore p H = ⊥ := by
  have hcop : Nat.Coprime p (Nat.card ((CFSG.pPrimeCore p H).map H.subtype)) := by
    rw [Subgroup.card_map_of_injective H.subtype_injective]
    exact CFSG.pPrimeCore_coprime_card
  have hle : (CFSG.pPrimeCore p H).map H.subtype ≤ CFSG.pPrimeCore p N :=
    le_sSup (s := {K : Subgroup N | K.Normal ∧ Nat.Coprime p (Nat.card K)}) ⟨inferInstance, hcop⟩
  rw [hcore, le_bot_iff] at hle
  exact (Subgroup.map_eq_bot_iff_of_injective _ H.subtype_injective).mp hle

theorem r3L1_isCharacteristicP_of_le_centralizer {N : Type*} [Group N] [Finite N] {p : ℕ}
    [Fact p.Prime] (hcore : CFSG.pPrimeCore p N = ⊥) (H : Subgroup N) [H.Normal]
    (hH : H ≤ Subgroup.centralizer (CFSG.layer N : Set N)) : CFSG.IsCharacteristicP p H := by
  have hlayer : CFSG.layer ↥H = ⊥ :=
    CFSG.LocalCores.layer_eq_bot_of_forall (r3L1_no_component_of_le_centralizer H hH)
  have hcoreH : CFSG.pPrimeCore p ↥H = ⊥ := r3L1_pPrimeCore_eq_bot_of_normal hcore H
  exact CFSG.isCharacteristicP_of_pPrimeCore_eq_bot_of_layer_eq_bot ↥H p hcoreH hlayer

theorem r3_charP_centralizer_layer {N : Type} [Group N] [Finite N] {p : ℕ} (hp : p.Prime)
    (hcore : CFSG.pPrimeCore p N = ⊥) :
    ∃ Q : Subgroup N, IsPGroup p Q ∧ (∀ g : N, g ∈ Subgroup.normalizer (Q : Set N)) ∧
      Subgroup.centralizer (CFSG.layer N : Set N) ⊓ Subgroup.centralizer (Q : Set N) ≤ Q := by
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨C, hC⟩ : ∃ C : Subgroup N, C = Subgroup.centralizer (CFSG.layer N : Set N) :=
    ⟨_, rfl⟩
  have hCle : C ≤ Subgroup.centralizer (CFSG.layer N : Set N) := hC.le
  have hCn : C.Normal := by
    rw [hC]
    exact r3L1_centralizer_layer_normal N
  have hchar : CFSG.IsCharacteristicP p C :=
    r3L1_isCharacteristicP_of_le_centralizer hcore C hCle
  have hchar' : Subgroup.centralizer (CFSG.pCore p C : Set C) ≤ CFSG.pCore p C := hchar
  have hQn : ((CFSG.pCore p C).map C.subtype).Normal := inferInstance
  rw [← hC]
  refine ⟨(CFSG.pCore p C).map C.subtype,
    (CFSG.pCore_isPGroup (p := p) (G := ↥C)).map C.subtype, ?_, ?_⟩
  · intro g
    rw [Subgroup.mem_normalizer_iff]
    intro n
    constructor
    · intro hn
      exact hQn.conj_mem n hn g
    · intro hn
      have h1 := hQn.conj_mem _ hn g⁻¹
      have e : g⁻¹ * (g * n * g⁻¹) * g⁻¹⁻¹ = n := by group
      rwa [e] at h1
  · rintro x ⟨hx1, hx2⟩
    have hy : (⟨x, hx1⟩ : C) ∈ Subgroup.centralizer (CFSG.pCore p C : Set C) := by
      rw [Subgroup.mem_centralizer_iff]
      intro z hz
      apply Subtype.ext
      have hzQ : (z : N) ∈ (CFSG.pCore p C).map C.subtype :=
        Subgroup.mem_map_of_mem C.subtype hz
      have hzx := Subgroup.mem_centralizer_iff.mp hx2 (z : N) hzQ
      simpa using hzx
    have hyP : (⟨x, hx1⟩ : C) ∈ CFSG.pCore p C := hchar' hy
    exact Subgroup.mem_map_of_mem C.subtype hyP

open scoped commutatorElement

theorem r3L2a_mem_normalizer {N : Type} [Group N] {U : Subgroup N} {x : N} (hx : x ∈ U) :
    x ∈ Subgroup.normalizer (U : Set N) := by
  rw [Subgroup.mem_set_normalizer_iff]
  intro n
  constructor
  · intro hn
    exact U.mul_mem (U.mul_mem hx hn) (U.inv_mem hx)
  · intro hn
    have h2 := U.mul_mem (U.mul_mem (U.inv_mem hx) hn) hx
    have e1 : x⁻¹ * (x * n * x⁻¹) * x = n := by group
    rw [e1] at h2
    exact h2

theorem r3L2a_decomp {N : Type} [Group N] {f : N} {Ū : Subgroup N}
    (hfŪ : f ∈ Subgroup.normalizer (Ū : Set N)) {k : N}
    (hk : k ∈ Subgroup.zpowers f ⊔ Ū) :
    ∃ e ∈ Subgroup.zpowers f, ∃ x ∈ Ū, k = e * x := by
  have hconj1 : ∀ g ∈ Subgroup.zpowers f, ∀ n ∈ Ū, g * n * g⁻¹ ∈ Ū := by
    intro g hg n hn
    have hgN : g ∈ Subgroup.normalizer (Ū : Set N) := Subgroup.zpowers_le.mpr hfŪ hg
    exact (Subgroup.mem_set_normalizer_iff.mp hgN n).mp hn
  have hconj2 : ∀ g ∈ Subgroup.zpowers f, ∀ n ∈ Ū, g⁻¹ * n * g ∈ Ū := by
    intro g hg n hn
    have h := hconj1 g⁻¹ (Subgroup.inv_mem _ hg) n hn
    rwa [inv_inv] at h
  let T : Subgroup N :=
    { carrier := {y : N | ∃ e ∈ Subgroup.zpowers f, ∃ x ∈ Ū, y = e * x}
      mul_mem' := by
        rintro a b ⟨e1, he1, x1, hx1, rfl⟩ ⟨e2, he2, x2, hx2, rfl⟩
        exact ⟨e1 * e2, Subgroup.mul_mem _ he1 he2, e2⁻¹ * x1 * e2 * x2,
          Ū.mul_mem (hconj2 e2 he2 x1 hx1) hx2, by group⟩
      one_mem' := ⟨1, Subgroup.one_mem _, 1, Ū.one_mem, by simp⟩
      inv_mem' := by
        rintro a ⟨e, he, x, hx, rfl⟩
        exact ⟨e⁻¹, Subgroup.inv_mem _ he, e * x⁻¹ * e⁻¹,
          hconj1 e he x⁻¹ (Ū.inv_mem hx), by group⟩ }
  have hle : Subgroup.zpowers f ⊔ Ū ≤ T := by
    apply sup_le
    · intro e he
      exact ⟨e, he, 1, Ū.one_mem, by simp⟩
    · intro x hx
      exact ⟨1, Subgroup.one_mem _, x, hx, by simp⟩
  have hkT : k ∈ {y : N | ∃ e ∈ Subgroup.zpowers f, ∃ x ∈ Ū, y = e * x} := hle hk
  obtain ⟨e, he, x, hx, hkex⟩ := hkT
  exact ⟨e, he, x, hx, hkex⟩

theorem r3L2a_conj_cent {N : Type} [Group N] {Q : Subgroup N} {u g : N}
    (hu : u ∈ Subgroup.normalizer (Q : Set N)) (hg : g ∈ Subgroup.centralizer (Q : Set N)) :
    u * g * u⁻¹ ∈ Subgroup.centralizer (Q : Set N) := by
  rw [Subgroup.mem_centralizer_iff] at hg ⊢
  intro q hq
  have hq' : u⁻¹ * q * u ∈ Q := by
    refine (Subgroup.mem_set_normalizer_iff.mp hu (u⁻¹ * q * u)).mpr ?_
    have e1 : u * (u⁻¹ * q * u) * u⁻¹ = q := by group
    rw [e1]
    exact hq
  have h1 := hg (u⁻¹ * q * u) hq'
  calc q * (u * g * u⁻¹) = u * ((u⁻¹ * q * u) * g) * u⁻¹ := by group
    _ = u * (g * (u⁻¹ * q * u)) * u⁻¹ := by rw [h1]
    _ = u * g * u⁻¹ * q := by group

theorem r3_faithful_prod {N : Type} [Group N] {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {f : N}
    (hf : f ^ p = 1) {Ū Q : Subgroup N} (hŪ2 : IsPGroup 2 Ū)
    (hfŪ : f ∈ Subgroup.normalizer (Ū : Set N)) (hfn : f ∉ Subgroup.centralizer (Ū : Set N))
    (hŪQ : Ū ≤ Subgroup.normalizer (Q : Set N)) (hfQ : f ∈ Subgroup.normalizer (Q : Set N))
    (hfaith : Ū ⊓ Subgroup.centralizer (Q : Set N) = ⊥) :
    (Subgroup.zpowers f ⊔ Ū) ⊓ Subgroup.centralizer (Q : Set N) = ⊥ := by
  rw [eq_bot_iff]
  rintro k ⟨hkH, hkQ⟩
  obtain ⟨e, he, x, hx, rfl⟩ := r3L2a_decomp hfŪ hkH
  rw [Subgroup.mem_bot]
  have hbot : ∀ y ∈ Ū, y ∈ Subgroup.centralizer (Q : Set N) → y = 1 := by
    intro y hy hyc
    have hmem : y ∈ Ū ⊓ Subgroup.centralizer (Q : Set N) := Subgroup.mem_inf.mpr ⟨hy, hyc⟩
    rw [hfaith, Subgroup.mem_bot] at hmem
    exact hmem
  by_cases he1 : e = 1
  · subst he1
    rw [one_mul] at hkQ ⊢
    exact hbot x hx hkQ
  exfalso
  have hen : e ∈ Subgroup.normalizer (Ū : Set N) := Subgroup.zpowers_le.mpr hfŪ he
  have hxn : x ∈ Subgroup.normalizer (Ū : Set N) := r3L2a_mem_normalizer hx
  have hgn : e * x ∈ Subgroup.normalizer (Ū : Set N) := Subgroup.mul_mem _ hen hxn
  have hcomm : ∀ u ∈ Ū, (e * x) * u = u * (e * x) := by
    intro u hu
    have hc1 : (e * x) * u * (e * x)⁻¹ ∈ Ū := (Subgroup.mem_set_normalizer_iff.mp hgn u).mp hu
    have hc2 : (e * x) * u * (e * x)⁻¹ * u⁻¹ = (e * x) * (u * (e * x)⁻¹ * u⁻¹) := by group
    have hc3 : (e * x) * (u * (e * x)⁻¹ * u⁻¹) ∈ Subgroup.centralizer (Q : Set N) :=
      Subgroup.mul_mem _ hkQ (r3L2a_conj_cent (hŪQ hu) (Subgroup.inv_mem _ hkQ))
    have hc4 := hbot _ (Ū.mul_mem hc1 (Ū.inv_mem hu)) (by rw [hc2]; exact hc3)
    exact mul_inv_eq_iff_eq_mul.mp (mul_inv_eq_one.mp hc4)
  have hR : ∀ w ∈ Ū, e * w * e⁻¹ = x⁻¹ * w * x := by
    intro w hw
    have hu : x⁻¹ * w * x ∈ Ū := Ū.mul_mem (Ū.mul_mem (Ū.inv_mem hx) hw) hx
    have h1 := hcomm _ hu
    have h2 : e * w * x = x⁻¹ * w * x * e * x := by
      calc e * w * x = e * x * (x⁻¹ * w * x) := by group
        _ = (x⁻¹ * w * x) * (e * x) := h1
        _ = x⁻¹ * w * x * e * x := by group
    have h3 : e * w = x⁻¹ * w * x * e := mul_right_cancel h2
    rw [h3, mul_inv_cancel_right]
  have hiter : ∀ j : ℕ, ∀ w ∈ Ū, e ^ j * w * (e ^ j)⁻¹ = (x ^ j)⁻¹ * w * x ^ j := by
    intro j
    induction j with
    | zero => intro w _; simp
    | succ j ih =>
      intro w hw
      have hwj : (x ^ j)⁻¹ * w * x ^ j ∈ Ū :=
        Ū.mul_mem (Ū.mul_mem (Ū.inv_mem (Ū.pow_mem hx j)) hw) (Ū.pow_mem hx j)
      calc e ^ (j + 1) * w * (e ^ (j + 1))⁻¹ = e * (e ^ j * w * (e ^ j)⁻¹) * e⁻¹ := by
            simp only [pow_succ', mul_inv_rev, mul_assoc]
        _ = e * ((x ^ j)⁻¹ * w * x ^ j) * e⁻¹ := by rw [ih w hw]
        _ = x⁻¹ * ((x ^ j)⁻¹ * w * x ^ j) * x := hR _ hwj
        _ = (x ^ (j + 1))⁻¹ * w * x ^ (j + 1) := by
            simp only [pow_succ, mul_inv_rev, mul_assoc]
  obtain ⟨s, hs⟩ := hŪ2 ⟨x, hx⟩
  have hxs : x ^ 2 ^ s = 1 := by
    have h := congrArg Subtype.val hs
    simpa using h
  have hcen_pow : e ^ 2 ^ s ∈ Subgroup.centralizer (Ū : Set N) := by
    rw [Subgroup.mem_centralizer_iff]
    intro w hw
    have h1 := hiter (2 ^ s) w hw
    rw [hxs, inv_one, one_mul, mul_one] at h1
    exact (mul_inv_eq_iff_eq_mul.mp h1).symm
  obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.mp he
  have hep : e ^ p = 1 := by
    rw [← hi, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hf, one_zpow]
  have hcop2 : Nat.Coprime (2 ^ s) p :=
    Nat.Coprime.pow_left s ((Nat.coprime_primes Nat.prime_two hp).mpr (Ne.symm hp2))
  obtain ⟨a, -, ha⟩ := Nat.exists_mul_mod_eq_one_of_coprime hcop2 hp.one_lt
  have he_eq : e = (e ^ 2 ^ s) ^ a := by
    rw [← pow_mul, pow_eq_pow_mod (2 ^ s * a) hep, ha, pow_one]
  have hmemC : e ∈ Subgroup.centralizer (Ū : Set N) := by
    have h := Subgroup.pow_mem _ hcen_pow a
    rwa [← he_eq] at h
  have hpi : ¬ ((p : ℤ) ∣ i) := by
    rintro ⟨t, rfl⟩
    apply he1
    rw [← hi, zpow_mul, zpow_natCast, hf, one_zpow]
  have hcop : IsCoprime (p : ℤ) i :=
    (_root_.Prime.coprime_iff_not_dvd (Nat.prime_iff_prime_int.mp hp)).mpr hpi
  obtain ⟨u, v, huv⟩ := hcop
  have hf_eq : f = e ^ v := by
    calc f = f ^ (u * (p : ℤ) + v * i) := by rw [huv, zpow_one]
      _ = (f ^ (p : ℤ)) ^ u * (f ^ i) ^ v := by rw [zpow_add, zpow_mul', zpow_mul']
      _ = e ^ v := by rw [zpow_natCast, hf, one_zpow, one_mul, hi]
  apply hfn
  rw [hf_eq]
  exact Subgroup.zpow_mem _ hmemC v

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo
open scoped commutatorElement

theorem r3L2_eq_bot_of_pgroup_inf {N : Type} [Group N] {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {A Q : Subgroup N} (hA : IsPGroup 2 A) (hQ : IsPGroup p Q) : A ⊓ Q = ⊥ := by
  rw [eq_bot_iff]
  rintro x ⟨hxA, hxQ⟩
  rw [Subgroup.mem_bot]
  obtain ⟨k, hk⟩ := hA ⟨x, hxA⟩
  obtain ⟨m, hm⟩ := hQ ⟨x, hxQ⟩
  have hk' : x ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
  have hm' : x ^ p ^ m = 1 := by simpa using congrArg Subtype.val hm
  have hcop : Nat.Coprime (2 ^ k) (p ^ m) :=
    Nat.Coprime.pow k m ((Nat.coprime_primes Nat.prime_two hp).mpr (Ne.symm hp2))
  have h1 : x ^ Nat.gcd (2 ^ k) (p ^ m) = 1 := pow_gcd_eq_one.mpr ⟨hk', hm'⟩
  rw [Nat.Coprime.gcd_eq_one hcop, pow_one] at h1
  exact h1

theorem r3L2_zpowers_inf_centralizer_eq_bot {N : Type} [Group N] [Finite N] {p : ℕ}
    (hp : p.Prime) {f : N} (hf : f ^ p = 1) (hf1 : f ≠ 1) {S : Subgroup N}
    (hfn : f ∉ Subgroup.centralizer (S : Set N)) :
    Subgroup.zpowers f ⊓ Subgroup.centralizer (S : Set N) = ⊥ := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hEcard : Nat.card (Subgroup.zpowers f) = p := by
    rw [Nat.card_zpowers, orderOf_eq_prime hf hf1]
  have hHle : Subgroup.zpowers f ⊓ Subgroup.centralizer (S : Set N) ≤ Subgroup.zpowers f :=
    inf_le_left
  have hdvd : Nat.card ↥(Subgroup.zpowers f ⊓ Subgroup.centralizer (S : Set N)) ∣ p := by
    have h := Subgroup.card_dvd_of_le hHle
    rwa [hEcard] at h
  rcases (Nat.dvd_prime hp).mp hdvd with h1 | hpH
  · exact Subgroup.card_eq_one.mp h1
  · exfalso
    have hEH : Subgroup.zpowers f ⊓ Subgroup.centralizer (S : Set N) = Subgroup.zpowers f :=
      Subgroup.eq_of_le_of_card_ge hHle (le_of_eq (hEcard.trans hpH.symm))
    have hfm : f ∈ Subgroup.zpowers f ⊓ Subgroup.centralizer (S : Set N) := by
      rw [hEH]
      exact Subgroup.mem_zpowers f
    exact hfn hfm.2

theorem r3_exists_not_centralizing {N : Type} [Group N] [Finite N] {p : ℕ} (hp : p.Prime)
    (hp7 : 7 ≤ p) (hlr : CFSG.Assembly.RankThreeEven.localRank p N < 3)
    (hcore : CFSG.pPrimeCore p N = ⊥) {Ū B : Subgroup N} (hŪ2 : IsPGroup 2 Ū) (hŪ1 : Ū ≠ ⊥)
    (hB : IsPGroup p B) (hBexp : ∀ x ∈ B, x ^ p = 1)
    (hBN : B ≤ Subgroup.normalizer (Ū : Set N)) (hcomm : ⁅Ū, B⁆ = Ū) :
    ¬ Ū ≤ Subgroup.centralizer (CFSG.layer N : Set N) := by
  intro hle
  obtain ⟨Q, hQp, hQnorm, hQ⟩ := r3_charP_centralizer_layer hp hcore
  have hp2 : p ≠ 2 := by omega
  have hp3 : 3 < p := by omega
  have hfaith : Ū ⊓ Subgroup.centralizer (Q : Set N) = ⊥ := by
    have hUQ : Ū ⊓ Q = ⊥ := r3L2_eq_bot_of_pgroup_inf hp hp2 hŪ2 hQp
    rw [eq_bot_iff]
    rintro x ⟨hxŪ, hxC⟩
    have hxI : x ∈ Subgroup.centralizer (CFSG.layer N : Set N) ⊓
        Subgroup.centralizer (Q : Set N) := ⟨hle hxŪ, hxC⟩
    have hx : x ∈ Ū ⊓ Q := ⟨hxŪ, hQ hxI⟩
    rw [hUQ] at hx
    exact hx
  obtain ⟨f, hfB, hfn⟩ : ∃ f ∈ B, f ∉ Subgroup.centralizer (Ū : Set N) := by
    by_contra hcon
    apply hŪ1
    have hBC : ∀ y ∈ B, y ∈ Subgroup.centralizer (Ū : Set N) := fun y hy =>
      Classical.byContradiction fun hn => hcon ⟨y, hy, hn⟩
    have h0 : ⁅Ū, B⁆ = ⊥ := by
      rw [eq_bot_iff, Subgroup.commutator_le]
      intro g₁ hg₁ g₂ hg₂
      rw [Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm]
      exact Subgroup.mem_centralizer_iff.mp (hBC g₂ hg₂) g₁ hg₁
    exact hcomm.symm.trans h0
  have hf : f ^ p = 1 := hBexp f hfB
  have hf1 : f ≠ 1 := by
    intro h1
    apply hfn
    rw [h1]
    exact Subgroup.one_mem _
  have hfN : f ∈ Subgroup.normalizer (Ū : Set N) := hBN hfB
  have hEp : CFSG.Assembly.IsElemAbelian p (Subgroup.zpowers f) :=
    CFSG.Open.isElemAbelian_zpowers hf
  have hE1 : Subgroup.zpowers f ≠ ⊥ := by
    intro h
    apply hf1
    have hfz : f ∈ Subgroup.zpowers f := Subgroup.mem_zpowers f
    rw [h, Subgroup.mem_bot] at hfz
    exact hfz
  have hES : Subgroup.zpowers f ≤ Subgroup.normalizer (Ū : Set N) :=
    Subgroup.zpowers_le.mpr hfN
  have hEf : Subgroup.zpowers f ⊓ Subgroup.centralizer (Ū : Set N) = ⊥ :=
    r3L2_zpowers_inf_centralizer_eq_bot hp hf hf1 hfn
  have hŪQ : Ū ≤ Subgroup.normalizer (Q : Set N) := by
    intro x _
    exact hQnorm x
  have hESQ : Subgroup.zpowers f ⊔ Ū ≤ Subgroup.normalizer (Q : Set N) := by
    apply sup_le
    · intro x _
      exact hQnorm x
    · exact hŪQ
  have hESf : (Subgroup.zpowers f ⊔ Ū) ⊓ Subgroup.centralizer (Q : Set N) = ⊥ :=
    r3_faithful_prod hp hp2 hf hŪ2 hfN hfn hŪQ (hQnorm f) hfaith
  have hp5 : p = 5 → 25 ≤ Nat.card (Subgroup.zpowers f) := fun h => absurd h (by omega)
  have hres : 2 < CFSG.Assembly.RankThreeEven.localRank p N :=
    CFSG.RankThree.PartTwo.Sec3.rank3II_3_8 hp hp hp3 hp3 hEp hE1 hŪ2 hQp hES hEf hESQ hESf hp5
  omega

end CFSG.RankThree.PartTwo.Sec13.F135Last
