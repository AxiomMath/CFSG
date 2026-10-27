module

public import CFSG.Quasithin.H13.NQRigidAsmSetup

public section

namespace CFSG.Quasithin.H13.NQRigid

open Subgroup CFSG.Open
open CFSG.Quasithin.SteinbergCC (normalizerFrattiniConj)
open CFSG.QuasithinUnique.Setup.Campbell (NoPQuotient)
open CFSG.ABGLocalTools (IsSylowOf)
open scoped Pointwise commutatorElement

theorem generalizedFitting_eq_pCore_of_not_quasisimple {H : Type*} [Group H] [Finite H]
    (hodd : CFSG.pPrimeCore 2 H = ⊥) {K : Subgroup H} (hK : CFSG.IsCComponent K)
    (hq : ¬ CFSG.IsQuasisimple K) : CFSG.generalizedFitting K = CFSG.pCore 2 K := by
  classical
  have hKc := CFSG.Quasithin.mem_cComp_top_iff_isCComponent.mpr hK
  obtain ⟨-, hF, -, -, -⟩ := LocDbl.Ccomm_structure_nonquasisimple_Fitting hKc hq
  rw [hF]
  apply le_antisymm
  · rw [CFSG.LocalCores.fittingSubgroup_eq_iSup_pCore]
    refine iSup_le fun r => ?_
    have hr : (r : ℕ).Prime := Nat.prime_of_mem_primeFactors r.2
    have : Fact (r : ℕ).Prime := ⟨hr⟩
    by_cases hr2 : (r : ℕ) = 2
    · have h1 : CFSG.pCore (r : ℕ) K = CFSG.pCore 2 K := by rw [hr2]
      exact h1.le
    ·
      have h1 := NQBlock.pCore_map_le_of_isSubnormal (p := (r : ℕ)) hK.2.2.1
      have h2 : CFSG.pCore (r : ℕ) H ≤ CFSG.pPrimeCore 2 H := by
        apply le_sSup
        refine ⟨CFSG.pCore_normal, ?_⟩
        obtain ⟨k, hk⟩ :=
          (CFSG.pCore_isPGroup : IsPGroup (r : ℕ) (CFSG.pCore (r : ℕ) H)).exists_card_eq
        rw [hk]
        exact Nat.Coprime.pow_right k ((Nat.coprime_primes Nat.prime_two hr).mpr (Ne.symm hr2))
      have h3 : (CFSG.pCore (r : ℕ) K).map K.subtype = ⊥ := by
        rw [eq_bot_iff, ← hodd]
        exact h1.trans h2
      rw [map_eq_bot_iff_of_injective _ K.subtype_injective] at h3
      rw [h3]
      exact bot_le
  · have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    exact CFSG.pCore_le_fitting K 2

theorem commutator_pCore_ne_bot {H : Type*} [Group H] [Finite H] {p : ℕ} [Fact p.Prime]
    (hp2 : p ≠ 2) {X P : Subgroup H} (hXA : IsPGroup p (X ⧸ CFSG.pCore 2 X))
    (hX2 : NoPQuotient 2 X) (hO2 : CFSG.pCore 2 X ≠ ⊥) (hP : IsSylowOf p P X) :
    ⁅(CFSG.pCore 2 X).map X.subtype, P⁆ ≠ ⊥ := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro hc
  set Q := (CFSG.pCore 2 X).map X.subtype with hQ
  have hPX : P ≤ X := hP.le
  have hXQP : ∀ x ∈ X, ∃ y ∈ P, y⁻¹ * x ∈ Q := by
    intro x hx
    obtain ⟨y, hyP, hyx⟩ := NQSetup.exists_mem_sylow_mk_eq hXA hP ⟨x, hx⟩
    rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply] at hyx
    refine ⟨(y : H), hyP, ⟨y⁻¹ * ⟨x, hx⟩, ?_, rfl⟩⟩
    exact QuotientGroup.eq.mp hyx
  have hQP : ∀ q ∈ Q, ∀ y ∈ P, q * y = y * q := by
    intro q hq y hy
    have h1 : ⁅q, y⁆ ∈ ⁅Q, P⁆ := commutator_mem_commutator hq hy
    rw [hc, mem_bot, commutatorElement_eq_one_iff_mul_comm] at h1
    exact h1
  set P' := P.subgroupOf X with hP'
  have hP'n : P'.Normal := by
    refine ⟨fun a ha x => ?_⟩
    rw [mem_subgroupOf] at ha ⊢
    obtain ⟨y, hyP, hyx⟩ := hXQP x x.2
    set q := y⁻¹ * (x : H) with hq
    have hxyq : (x : H) = y * q := by rw [hq]; group
    have h1 : q * (a : H) * q⁻¹ = a := by
      rw [hQP q hyx a ha]
      group
    change (x : H) * a * (x : H)⁻¹ ∈ P
    rw [hxyq, show y * q * (a : H) * (y * q)⁻¹ = y * (q * a * q⁻¹) * y⁻¹ by group, h1]
    exact mul_mem (mul_mem hyP ha) (inv_mem hyP)
  have hq2 : IsPGroup 2 (X ⧸ P') := by
    intro z
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective z
    obtain ⟨y, hyP, hyx⟩ := hXQP x x.2
    obtain ⟨⟨q', hq'⟩, hqQ, hqe⟩ := hyx
    obtain ⟨k, hk⟩ := (CFSG.pCore_isPGroup : IsPGroup 2 (CFSG.pCore 2 X)) ⟨⟨q', hq'⟩, hqQ⟩
    refine ⟨k, ?_⟩
    have hxe : x = ⟨y, hPX hyP⟩ * ⟨q', hq'⟩ := by
      apply Subtype.ext
      change (x : H) = y * q'
      have : q' = y⁻¹ * (x : H) := hqe
      rw [this]
      group
    rw [hxe, QuotientGroup.mk_mul, (QuotientGroup.eq_one_iff _).mpr (mem_subgroupOf.mpr hyP),
      one_mul, ← QuotientGroup.mk_pow]
    have h1 : (⟨q', hq'⟩ : X) ^ 2 ^ k = 1 := by
      have := congrArg Subtype.val hk
      exact this
    rw [h1, QuotientGroup.mk_one]
  have htop := hX2 P' hq2
  have hp : p.Prime := Fact.out
  apply hO2
  rw [eq_bot_iff]
  intro q hq
  have hqP : (q : H) ∈ P := by
    have : q ∈ P' := htop ▸ mem_top q
    exact this
  obtain ⟨a, ha⟩ := (CFSG.pCore_isPGroup : IsPGroup 2 (CFSG.pCore 2 X)) ⟨q, hq⟩
  have hord : orderOf (q : H) ∣ 2 ^ a := by
    rw [Subgroup.orderOf_coe]
    exact orderOf_dvd_of_pow_eq_one (by simpa using congrArg Subtype.val ha)
  have h2P : ¬ 2 ∣ Nat.card P := by
    obtain ⟨n, hn⟩ := hP.isPGroup.exists_card_eq
    rw [hn]
    intro hd
    exact hp2 ((Nat.prime_dvd_prime_iff_eq Nat.prime_two hp).mp
      (Nat.prime_two.dvd_of_dvd_pow hd)).symm
  have h1 := NQTerm.eq_one_of_orderOf_dvd_prime_pow Nat.prime_two h2P hqP hord
  exact (mem_bot).mpr (Subtype.ext h1)

theorem mul_comm_sylow_of_core_le {H : Type*} [Group H] [Finite H] {p : ℕ} [Fact p.Prime]
    {X P Q : Subgroup H} (hXA : IsPGroup p (X ⧸ CFSG.pCore 2 X)) (hP : IsSylowOf p P X)
    (hQN : Q ≤ normalizer (X : Set H)) (hOQ : (CFSG.pCore 2 X).map X.subtype ≤ Q) :
    (P : Set H) * (Q : Set H) = (Q : Set H) * (P : Set H) := by
  classical
  have hPX : P ≤ X := hP.le
  set AX := (CFSG.pCore 2 X).map X.subtype with hAX
  have hNAX : normalizer (X : Set H) ≤ normalizer (AX : Set H) :=
    LieType.BorelTits.normalizer_le_normalizer_map_of_characteristic _
  have hNA : ∀ g ∈ normalizer (X : Set H), ∀ a ∈ AX, g * a * g⁻¹ ∈ AX := fun g hg a ha =>
    (mem_normalizer_iff.mp (hNAX hg) a).mp ha
  have hXPA : ∀ x ∈ X, ∃ y ∈ P, y⁻¹ * x ∈ AX := by
    intro x hx
    obtain ⟨y, hyP, hyx⟩ := NQSetup.exists_mem_sylow_mk_eq hXA hP ⟨x, hx⟩
    rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply] at hyx
    exact ⟨(y : H), hyP, ⟨y⁻¹ * ⟨x, hx⟩, QuotientGroup.eq.mp hyx, rfl⟩⟩
  ext z
  constructor
  · rintro ⟨y, hy, q, hq, rfl⟩
    have hx : q⁻¹ * y * q⁻¹⁻¹ ∈ X := (mem_normalizer_iff.mp (hQN (inv_mem hq)) y).mp (hPX hy)
    rw [inv_inv] at hx
    obtain ⟨y', hy', hya⟩ := hXPA _ hx
    refine ⟨q * (y' * (y'⁻¹ * (q⁻¹ * y * q)) * y'⁻¹),
      mul_mem hq (hOQ (hNA y' (le_normalizer (hPX hy')) _ hya)), y', hy', by group⟩
  · rintro ⟨q, hq, y, hy, rfl⟩
    obtain ⟨y', hy', hya⟩ := hXPA _ ((mem_normalizer_iff.mp (hQN hq) y).mp (hPX hy))
    exact ⟨y', hy', y'⁻¹ * (q * y * q⁻¹) * q, mul_mem (hOQ hya) hq, by group⟩

theorem not_isCyclic_coreQuot_of_card_frattini {X : Type*} [Group X] [Finite X] {p : ℕ}
    [hp : Fact p.Prime] (hXA : IsPGroup p (X ⧸ CFSG.pCore 2 X))
    (hW : Nat.card ((X ⧸ CFSG.pCore 2 X) ⧸ frattini (X ⧸ CFSG.pCore 2 X)) = p ^ 2) :
    ¬ IsCyclic (X ⧸ CFSG.pCore 2 X) := by
  intro hc
  have hWc : IsCyclic ((X ⧸ CFSG.pCore 2 X) ⧸ frattini (X ⧸ CFSG.pCore 2 X)) :=
    isCyclic_of_surjective _ (QuotientGroup.mk'_surjective _)
  obtain ⟨-, -, hWpow, -, -⟩ := CFSG.GroupTheory.frattini_elementary_quotient hXA
  obtain ⟨w, hw⟩ := hWc.exists_generator
  have h1 : Nat.card ((X ⧸ CFSG.pCore 2 X) ⧸ frattini (X ⧸ CFSG.pCore 2 X)) ≤ p := by
    rw [← orderOf_eq_card_of_forall_mem_zpowers hw]
    exact orderOf_le_of_pow_eq_one hp.out.pos (hWpow w)
  rw [hW] at h1
  have h2 := hp.out.two_le
  nlinarith

variable {G : Type} [Group G] [Finite G]

structure RigidSingle (T L M : Subgroup G) (p : ℕ) (X : Subgroup G) (v : G)
    (K : Subgroup (centralizer ({v} : Set G))) : Prop extends RigidEscape T L M p X v K where
  normal : K.Normal
  x_le : X.subgroupOf (centralizer ({v} : Set G)) ≤ K

end CFSG.Quasithin.H13.NQRigid
