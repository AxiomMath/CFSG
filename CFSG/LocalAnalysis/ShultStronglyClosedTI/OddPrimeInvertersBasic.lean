module

public import CFSG.GroupTheory.BurnsideNormalComplement
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar

public noncomputable section

namespace CFSG.ShultStronglyClosedTI.OddPrimeInverters

structure OddPrimeInvertersAndSplitFusion (F : Type*) [Group F] (q : ℕ) : Prop where
  exists_involution_inverts : ∀ x : F, (orderOf x).Prime → orderOf x ≠ 2 →
    ∃ s : F, orderOf s = 2 ∧ s * x * s⁻¹ = x⁻¹
  exists_conj_mem : ∀ T : Subgroup F, Nat.card T = q - 1 → ∀ p : ℕ, p.Prime → p ≠ 2 →
    p ∣ q - 1 → ∀ x : F, orderOf x = p → ∃ g : F, g * x * g⁻¹ ∈ T

variable {G : Type*} [Group G]

theorem pow_conj_of_inverts {x h : G} (hxh : h * x * h⁻¹ = x⁻¹) (n : ℕ) :
    h ^ n * x * (h ^ n)⁻¹ = x ^ ((-1 : ℤ) ^ n) := by
  induction n with
  | zero => simp
  | succ n ih =>
    calc h ^ (n + 1) * x * (h ^ (n + 1))⁻¹ = MulAut.conj h (h ^ n * x * (h ^ n)⁻¹) := by
          rw [MulAut.conj_apply]
          group
      _ = x ^ ((-1 : ℤ) ^ (n + 1)) := by
          rw [ih, map_zpow, MulAut.conj_apply, hxh, ← zpow_neg_one, ← zpow_mul, pow_succ']

theorem exists_involution_inverts_of_inverts [Finite G] {x h : G} (hxh : h * x * h⁻¹ = x⁻¹)
    (hx : x⁻¹ ≠ x) (hcent : ∀ s : G, orderOf s = 2 → s * x ≠ x * s) :
    ∃ s : G, orderOf s = 2 ∧ s * x * s⁻¹ = x⁻¹ := by
  have hpow := pow_conj_of_inverts hxh (orderOf h)
  rw [pow_orderOf_eq_one, one_mul, inv_one, mul_one] at hpow
  have heven : Even (orderOf h) := by
    by_contra hne
    rw [(Nat.not_even_iff_odd.mp hne).neg_one_pow, zpow_neg_one] at hpow
    exact hx hpow.symm
  obtain ⟨m, hm⟩ := heven
  have hpos := orderOf_pos h
  have hs : orderOf (h ^ m) = 2 := by
    refine orderOf_eq_prime ?_ (pow_ne_one_of_lt_orderOf (by omega) (by omega))
    rw [← pow_mul, mul_two, ← hm, pow_orderOf_eq_one]
  have hconj := pow_conj_of_inverts hxh m
  rcases Nat.even_or_odd m with hme | hme
  · rw [hme.neg_one_pow, zpow_one] at hconj
    exact absurd (mul_inv_eq_iff_eq_mul.mp hconj) (hcent _ hs)
  · rw [hme.neg_one_pow, zpow_neg_one] at hconj
    exact ⟨h ^ m, hs, hconj⟩

theorem not_commute_of_involution_centralizers [Finite G]
    (hcent : ∀ t : G, orderOf t = 2 → IsPGroup 2 (Subgroup.centralizer ({t} : Set G)))
    {x : G} (hx : (orderOf x).Prime) (hx2 : orderOf x ≠ 2) {s : G} (hs : orderOf s = 2) :
    s * x ≠ x * s := by
  intro hsx
  have hmem : x ∈ Subgroup.centralizer ({s} : Set G) :=
    Subgroup.mem_centralizer_singleton_iff.mpr hsx.symm
  obtain ⟨n, hn⟩ := hcent s hs ⟨x, hmem⟩
  have hdvd : orderOf x ∣ 2 ^ n := by
    rw [← Subgroup.orderOf_mk x hmem]
    exact orderOf_dvd_of_pow_eq_one hn
  obtain ⟨i, -, hi⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd
  rcases i with _ | i
  · exact hx.ne_one (by simpa using hi)
  · apply hx2
    have h2 : 2 ∣ orderOf x := by
      rw [hi]
      exact dvd_pow_self 2 (Nat.succ_ne_zero i)
    exact ((Nat.prime_dvd_prime_iff_eq Nat.prime_two hx).mp h2).symm

theorem exists_mem_normalizer_not_mem_centralizer [Finite G] (hperf : commutator G = ⊤)
    {p : ℕ} [Fact p.Prime] (P : Sylow p G) (hP : (P : Subgroup G) ≠ ⊥) :
    ∃ g ∈ Subgroup.normalizer (P : Set G), g ∉ Subgroup.centralizer (P : Set G) := by
  by_contra hcon
  push Not at hcon
  obtain ⟨K, hKn, -, hKidx, -, -, -, -, -, -, hcomm⟩ :=
    CFSG.GroupTheory.burnside_normal_complement P hcon
  have hle : commutator G ≤ K :=
    Subgroup.Normal.quotient_commutative_iff_commutator_le.mp ⟨⟨hcomm⟩⟩
  rw [hperf, top_le_iff] at hle
  rw [hle, Subgroup.index_top] at hKidx
  exact hP (Subgroup.card_eq_one.mp hKidx.symm)

theorem exists_conj_mem_of_not_dvd_index [Finite G] {p : ℕ} [Fact p.Prime] (T : Subgroup G)
    (hT : ¬ p ∣ T.index) {x : G} (hx : IsPGroup p (Subgroup.zpowers x)) :
    ∃ g : G, g * x * g⁻¹ ∈ T := by
  obtain ⟨Q⟩ : Nonempty (Sylow p T) := inferInstance
  have hQ : IsPGroup p ((Q : Subgroup T).map T.subtype) := Q.isPGroup'.map _
  have hidx : ¬ p ∣ ((Q : Subgroup T).map T.subtype).index := by
    rw [Subgroup.index_map_subtype, (Fact.out : p.Prime).dvd_mul, not_or]
    exact ⟨Q.not_dvd_index, hT⟩
  obtain ⟨P, hxP⟩ := hx.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G P (hQ.toSylow hidx)
  refine ⟨g, ?_⟩
  have hmem : g * x * g⁻¹ ∈ ((hQ.toSylow hidx : Sylow p G) : Subgroup G) := by
    rw [← hg, Sylow.coe_subgroup_smul]
    exact Subgroup.smul_mem_pointwise_smul x (MulAut.conj g) (P : Subgroup G)
      (hxP (Subgroup.mem_zpowers x))
  rw [IsPGroup.toSylow_coe] at hmem
  obtain ⟨t, -, ht⟩ := hmem
  rw [← ht]
  exact t.2

theorem exists_inverts_of_not_dvd_index [Finite G] {p : ℕ} [Fact p.Prime] (T : Subgroup G)
    (hT : ¬ p ∣ T.index) {w : G} (hw : ∀ t ∈ T, w * t * w⁻¹ = t⁻¹) {x : G}
    (hx : IsPGroup p (Subgroup.zpowers x)) : ∃ h : G, h * x * h⁻¹ = x⁻¹ := by
  obtain ⟨g, hg⟩ := exists_conj_mem_of_not_dvd_index T hT hx
  refine ⟨g⁻¹ * w * g, ?_⟩
  calc g⁻¹ * w * g * x * (g⁻¹ * w * g)⁻¹ = g⁻¹ * (w * (g * x * g⁻¹) * w⁻¹) * g := by group
    _ = x⁻¹ := by rw [hw _ hg]; group

theorem conj_eq_inv_of_lt_two {y g : G} {q : ℕ} (hq : y ^ q = y⁻¹)
    (h : ∃ i < 2, g * y * g⁻¹ = y ^ q ^ i) (hne : g * y * g⁻¹ ≠ y) : g * y * g⁻¹ = y⁻¹ := by
  obtain ⟨i, hi, hgi⟩ := h
  interval_cases i
  · exact absurd (by rw [hgi, pow_zero, pow_one]) hne
  · rw [hgi, pow_one, hq]

theorem conj_eq_inv_or_sq_conj_eq_inv_of_lt_four {y g : G} {q : ℕ} (hq : y ^ q ^ 2 = y⁻¹)
    (h : ∃ i < 4, g * y * g⁻¹ = y ^ q ^ i) (hne : g * y * g⁻¹ ≠ y) :
    g * y * g⁻¹ = y⁻¹ ∨ g ^ 2 * y * (g ^ 2)⁻¹ = y⁻¹ := by
  obtain ⟨i, hi, hgi⟩ := h
  have hsq : ∀ a : ℕ, g * y * g⁻¹ = y ^ a → g ^ 2 * y * (g ^ 2)⁻¹ = y ^ (a * a) := by
    intro a ha
    calc g ^ 2 * y * (g ^ 2)⁻¹ = g * (g * y * g⁻¹) * g⁻¹ := by
          rw [pow_two, mul_inv_rev]
          simp only [mul_assoc]
      _ = g * y ^ a * g⁻¹ := by rw [ha]
      _ = (g * y * g⁻¹) ^ a := conj_pow.symm
      _ = y ^ (a * a) := by rw [ha, ← pow_mul]
  have hq4 : y ^ q ^ 4 = y := by
    rw [show q ^ 4 = q ^ 2 * q ^ 2 by ring, pow_mul, hq, inv_pow, hq, inv_inv]
  interval_cases i
  · exact absurd (by rw [hgi, pow_zero, pow_one]) hne
  · right
    rw [hsq _ hgi, pow_one, ← pow_two, hq]
  · exact Or.inl (hgi.trans hq)
  · right
    rw [hsq _ hgi, show q ^ 3 * q ^ 3 = q ^ 4 * q ^ 2 by ring, pow_mul, hq4, hq]

theorem exists_inverts_of_frobenius [Finite G] (hperf : commutator G = ⊤) {p : ℕ} [Fact p.Prime]
    (hcyc : ∀ P : Sylow p G, IsCyclic P)
    (hfrob : ∀ y g : G, IsPGroup p (Subgroup.zpowers y) → g * y * g⁻¹ ∈ Subgroup.zpowers y →
      g * y * g⁻¹ ≠ y → g * y * g⁻¹ = y⁻¹ ∨ g ^ 2 * y * (g ^ 2)⁻¹ = y⁻¹)
    {x : G} (hx : IsPGroup p (Subgroup.zpowers x)) (hx1 : x ≠ 1) :
    ∃ h : G, h * x * h⁻¹ = x⁻¹ := by
  obtain ⟨P, hxP⟩ := hx.exists_le_sylow
  have hxP' : x ∈ (P : Subgroup G) := hxP (Subgroup.mem_zpowers x)
  obtain ⟨⟨y, hyP⟩, hy⟩ := (hcyc P).exists_generator
  have hPy : (P : Subgroup G) = Subgroup.zpowers y := by
    refine le_antisymm (fun z hz => ?_) ((Subgroup.zpowers_le).mpr hyP)
    obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp (hy ⟨z, hz⟩)
    exact Subgroup.mem_zpowers_iff.mpr ⟨n, by simpa using congrArg Subtype.val hn⟩
  have hPne : (P : Subgroup G) ≠ ⊥ := fun h => hx1 (by rwa [h, Subgroup.mem_bot] at hxP')
  obtain ⟨g, hgN, hgC⟩ := exists_mem_normalizer_not_mem_centralizer hperf P hPne
  have hgy : g * y * g⁻¹ ∈ Subgroup.zpowers y := by
    rw [← hPy]
    exact (Subgroup.mem_normalizer_iff.mp hgN y).mp hyP
  have hgy' : g * y * g⁻¹ ≠ y := by
    intro h
    apply hgC
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    have hz' : z ∈ Subgroup.zpowers y := by rw [← hPy]; exact hz
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz'
    have hcomm : Commute g y := mul_inv_eq_iff_eq_mul.mp h
    exact (hcomm.zpow_right n).eq.symm
  have hyp : IsPGroup p (Subgroup.zpowers y) := hPy ▸ P.isPGroup'
  obtain ⟨h, hh⟩ : ∃ h : G, h * y * h⁻¹ = y⁻¹ := by
    rcases hfrob y g hyp hgy hgy' with h1 | h2
    exacts [⟨g, h1⟩, ⟨g ^ 2, h2⟩]
  obtain ⟨e, rfl⟩ := Subgroup.mem_zpowers_iff.mp (hPy ▸ hxP')
  refine ⟨h, ?_⟩
  rw [← MulAut.conj_apply, map_zpow, MulAut.conj_apply, hh, inv_zpow]

theorem oddPrimeInvertersAndSplitFusion_of_data [Finite G] {q N : ℕ} (hperf : commutator G = ⊤)
    (hcyc : ∀ p [Fact p.Prime], p ≠ 2 → ∀ P : Sylow p G, IsCyclic P)
    (hcent : ∀ t : G, orderOf t = 2 → IsPGroup 2 (Subgroup.centralizer ({t} : Set G)))
    (hcard : Nat.card G = (q - 1) * N) (hcop : Nat.Coprime (q - 1) N)
    (T₀ : Subgroup G) (hT₀ : Nat.card T₀ = q - 1) (w : G) (hw : ∀ t ∈ T₀, w * t * w⁻¹ = t⁻¹)
    (hfrob : ∀ p : ℕ, p.Prime → p ≠ 2 → ¬ p ∣ q - 1 → ∀ y g : G,
      IsPGroup p (Subgroup.zpowers y) → g * y * g⁻¹ ∈ Subgroup.zpowers y → g * y * g⁻¹ ≠ y →
      g * y * g⁻¹ = y⁻¹ ∨ g ^ 2 * y * (g ^ 2)⁻¹ = y⁻¹) :
    OddPrimeInvertersAndSplitFusion G q := by
  have hindex : ∀ T : Subgroup G, Nat.card T = q - 1 → T.index = N := by
    intro T hT
    have h1 := T.card_mul_index
    rw [hT, hcard] at h1
    exact Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero fun h0 => by
      rw [h0, zero_mul] at hcard; exact Nat.card_pos.ne' hcard) h1
  have hsplit : ∀ T : Subgroup G, Nat.card T = q - 1 → ∀ p : ℕ, p.Prime → p ∣ q - 1 →
      ¬ p ∣ T.index := by
    intro T hT p hp hpq hpN
    rw [hindex T hT] at hpN
    exact hp.one_lt.ne' (Nat.eq_one_of_dvd_coprimes hcop hpq hpN)
  have hpgroup : ∀ x : G, (orderOf x).Prime → IsPGroup (orderOf x) (Subgroup.zpowers x) :=
    fun x hx => IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, pow_one])
  refine ⟨fun x hx hx2 => ?_, fun T hT p hp hp2 hpq x hx => ?_⟩
  · have : Fact (orderOf x).Prime := ⟨hx⟩
    have hxinv : x⁻¹ ≠ x := by
      intro h
      have h2 : x ^ 2 = 1 := by
        rw [pow_two]
        calc x * x = x * x⁻¹ := by rw [h]
          _ = 1 := mul_inv_cancel x
      have h3 := orderOf_dvd_of_pow_eq_one h2
      exact hx2 ((Nat.prime_dvd_prime_iff_eq hx Nat.prime_two).mp h3)
    have hx1 : x ≠ 1 := fun h => hxinv (by rw [h, inv_one])
    obtain ⟨h, hh⟩ : ∃ h : G, h * x * h⁻¹ = x⁻¹ := by
      by_cases hpq : orderOf x ∣ q - 1
      · exact exists_inverts_of_not_dvd_index T₀ (hsplit T₀ hT₀ _ hx hpq) hw (hpgroup x hx)
      · exact exists_inverts_of_frobenius hperf (hcyc _ hx2)
          (hfrob _ hx hx2 hpq) (hpgroup x hx) hx1
    exact exists_involution_inverts_of_inverts hh hxinv
      (fun s hs => not_commute_of_involution_centralizers hcent hx hx2 hs)
  · have : Fact p.Prime := ⟨hp⟩
    exact exists_conj_mem_of_not_dvd_index T (hsplit T hT p hp hpq) (hx ▸ hpgroup x (hx ▸ hp))

theorem OddPrimeInvertersAndSplitFusion.of_mulEquiv {F : Type*} [Group F] {q : ℕ}
    (h : OddPrimeInvertersAndSplitFusion G q) (e : F ≃* G) :
    OddPrimeInvertersAndSplitFusion F q := by
  have hord : ∀ x : F, orderOf (e x) = orderOf x := fun x => MulEquiv.orderOf_eq e x
  refine ⟨fun x hx hx2 => ?_, fun T hT p hp hp2 hpq x hx => ?_⟩
  · obtain ⟨s, hs, hsx⟩ := h.exists_involution_inverts (e x) (by rwa [hord]) (by rwa [hord])
    refine ⟨e.symm s, by rwa [MulEquiv.orderOf_eq], e.injective ?_⟩
    simp only [map_mul, map_inv, MulEquiv.apply_symm_apply, hsx]
  · obtain ⟨g, hg⟩ := h.exists_conj_mem (T.map e.toMonoidHom)
      (by rw [Subgroup.card_map_of_injective e.injective, hT]) p hp hp2 hpq (e x)
      (by rw [hord, hx])
    refine ⟨e.symm g, ?_⟩
    obtain ⟨t, ht, hte⟩ := Subgroup.mem_map.mp hg
    have : e.symm g * x * (e.symm g)⁻¹ = t := e.injective (by
      rw [map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply]
      exact hte.symm)
    rw [this]
    exact ht

end CFSG.ShultStronglyClosedTI.OddPrimeInverters
