module

public import CFSG.Quasithin.H13.NQBlockRadicalR2Max
public import CFSG.Quasithin.EmptyFaithfulMultiple.L3213Setup

public section

namespace CFSG.Quasithin.H13.T313

open Subgroup CFSG.Open CFSG.Quasithin
open CFSG.Quasithin.EmptyFaithfulMultiple (L3213.vOf)
open CFSG.Quasithin.SteinbergCC (normalizerFrattiniConj)

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem pow_mem_pCoreOf_of_exponent {X : Subgroup G} {p : ℕ}
    (hexp : Monoid.exponent (↥X ⧸ CFSG.pCore 2 ↥X) = p) {g : G} (hg : g ∈ X) :
    g ^ p ∈ pCoreOf 2 X := by
  have h1 : (((⟨g, hg⟩ : ↥X) ^ p : ↥X) : ↥X ⧸ CFSG.pCore 2 ↥X) = 1 := by
    rw [QuotientGroup.mk_pow, ← hexp, Monoid.pow_exponent_eq_one]
  have h2 : (⟨g, hg⟩ : ↥X) ^ p ∈ CFSG.pCore 2 ↥X := (QuotientGroup.eq_one_iff _).mp h1
  rw [pCoreOf]
  exact ⟨_, h2, rfl⟩

omit [Finite G] in
theorem relIndex_eq_of_isXi {T X : Subgroup G} (hX : IsXi T X) {p : ℕ} (hp : p.Prime)
    (hpow : ∀ x ∈ X, x ^ p ∈ pCoreOf 2 X) :
    (pCoreOf 2 X).relIndex X = p ^ 2 ∨
      ((pCoreOf 2 X).relIndex X = p ^ 3 ∧ ¬ ⁅X, X⁆ ≤ pCoreOf 2 X) := by
  obtain ⟨-, -, -, q, hq, -, hqpow, hidx, -⟩ := id hX
  suffices hqp : q = p by
    subst hqp
    exact hidx
  by_contra hne
  have hXle : X ≤ pCoreOf 2 X := fun x hx =>
    EmptyFaithfulMultiple.L3213.mem_of_pow_mem_of_pow_mem
      ((Nat.coprime_primes hq hp).mpr hne) (hqpow x hx) (hpow x hx)
  have h1 : (pCoreOf 2 X).relIndex X = 1 := Subgroup.relIndex_eq_one.mpr hXle
  have hq1 := hq.one_lt
  rcases hidx with h | ⟨h, -⟩ <;> rw [h1, eq_comm, Nat.pow_eq_one] at h <;> omega

theorem vOf_ne_bot {T X D : Subgroup G} (hX : IsXi T X) (hXD : X ≤ D)
    (hDX : D ≤ normalizer (X : Set G)) (hc : QuasithinUnique.CharTwo (D ⊔ T))
    (hXR : ¬ X ≤ centralizer (reducedAggregate (D ⊔ T) : Set G)) : L3213.vOf T X ≠ ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hXne : X ≠ ⊥ := fun h0 => hXR (by rw [h0]; exact bot_le)
  have hXDT : X ≤ D ⊔ T := hXD.trans le_sup_left
  have hDTX : D ⊔ T ≤ normalizer (X : Set G) := sup_le hDX hX.2.1
  have hsubDT : IsSubnormal X (D ⊔ T) :=
    A3.subnormal_of_normal hXDT ((normal_subgroupOf_iff_le_normalizer hXDT).mpr hDTX)
  have hsubXT : IsSubnormal X (X ⊔ T) :=
    A3.subnormal_of_normal le_sup_left ((normal_subgroupOf_iff_le_normalizer le_sup_left).mpr
      (EmptyFaithfulMultiple.L3213.sup_le_normalizer_of_isXi hX))
  have hXc : IsXClass X := ⟨hXne, hX.1, A4.charTwo_of_subnormal hsubDT hc⟩
  have h1 : ⁅omegaOneCenterOf (pCoreOf 2 (D ⊔ T)), X⁆ ≠ ⊥ := by
    intro h0
    apply hXR
    rw [commutator_eq_bot_iff_le_centralizer] at h0
    exact (le_centralizer_iff.mp h0).trans
      (centralizer_le (H13.NQBlock.reducedAggregate_le_omegaOneCenterOf (D ⊔ T)))
  exact (a4_9 hXc hsubXT).mpr ((a4_9 hXc hsubDT).mp h1)

theorem pCoreOf_sup_eq_inf_centralizer_vOf {T X : Subgroup G} (hT : quasithinIsSylowTwo T)
    (hX : IsXi T X) (hsolv : Group.IsSolvable X) (hVne : L3213.vOf T X ≠ ⊥) :
    pCoreOf 2 (X ⊔ T) = T ⊓ centralizer (L3213.vOf T X : Set G) := by
  obtain ⟨-, -, -, p, hp, hp2, hpow, -, -⟩ := id hX
  set V := L3213.vOf T X with hVdef
  have hXTV : X ⊔ T ≤ normalizer (V : Set G) :=
    EmptyFaithfulMultiple.L3213.sup_le_normalizer_vOf hX
  have hR := EmptyFaithfulMultiple.L3213.inf_centralizer_vOf_le hX hsolv hVne
  refine le_antisymm
    (le_inf ?_ (EmptyFaithfulMultiple.L3213.pCoreOf_sup_le_centralizer_vOf T X)) ?_
  · exact pCoreOf_le_of_quasithinIsSylowTwo hT (le_sup_right.trans le_normalizer)
  · rintro t ⟨ht, htV⟩
    refine EmptyFaithfulMultiple.L3213.xi_mem_pCoreOf_sup hT hX hp hp2 hpow ht
      fun x hx => hR ⟨?_, ?_⟩
    · exact X.mul_mem ((mem_normalizer_iff.mp (hX.2.1 ht) x).mp hx) (X.inv_mem hx)
    · have h1 : x * t⁻¹ * x⁻¹ ∈ centralizer (V : Set G) :=
        (mem_normalizer_iff.mp (A4.mem_normalizer_centralizer
          (hXTV (le_sup_left (b := T) hx))) t⁻¹).mp (inv_mem htV)
      have e : t * x * t⁻¹ * x⁻¹ = t * (x * t⁻¹ * x⁻¹) := by group
      rw [e]
      exact mul_mem htV h1

omit [Finite G] in
theorem le_of_isPerfect_of_dvd {N C D : Subgroup G} [Finite N] (hCN : (C.subgroupOf N).Normal)
    (hDN : D ≤ N) (hD : ⁅D, D⁆ = D)
    (h25 : ∀ q : ℕ, q.Prime → q ∣ C.relIndex N → q = 2 ∨ q = 5) : D ≤ C := by
  have := hCN
  have hsolv : Group.IsSolvable (↥N ⧸ C.subgroupOf N) :=
    CFSG.SignalizerFunctor.Helpers.two_prime_order_solvable _ 2 5 Nat.prime_two
      (by norm_num) fun q hq hqd => h25 q hq hqd
  set φ : ↥D →* ↥N ⧸ C.subgroupOf N := (QuotientGroup.mk' _).comp (inclusion hDN) with hφ
  have : Group.IsPerfect ↥D := (Subgroup.isPerfect_iff (H := D)).mpr hD
  have hrange : φ.range = ⊥ := by
    by_contra hne
    have : Nontrivial φ.range := (nontrivial_iff_ne_bot _).mpr hne
    have : Group.IsPerfect φ.range := Group.IsPerfect.range φ
    exact Group.IsPerfect.not_isSolvable φ.range inferInstance
  intro d hd
  have h1 : φ ⟨d, hd⟩ = 1 := by
    have h : φ ⟨d, hd⟩ ∈ φ.range := ⟨⟨d, hd⟩, rfl⟩
    rwa [hrange, mem_bot] at h
  exact mem_subgroupOf.mp ((QuotientGroup.eq_one_iff _).mp h1)

omit [Finite G] in
theorem normalizerFrattiniConj_eq_one_of_mem {X : Subgroup G} (d : normalizer (X : Set G))
    (hd : (d : G) ∈ sectionCentralizer X (pCoreOf 2 X)) : normalizerFrattiniConj X d = 1 :=
  H13.NQCore.normalizerFrattiniConj_eq_one_of
    ((H13.NQCore.normalizerCoreQuotConj_eq_one_iff d).mpr hd.2.2)

end CFSG.Quasithin.H13.T313
