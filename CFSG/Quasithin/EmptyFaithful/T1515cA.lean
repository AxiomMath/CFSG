module

public import CFSG.FeitThompson.OddOrderTheorem
import CFSG.LocalAnalysis.QuasithinUnique.CharTwoTransport
public import CFSG.Quasithin.Background.C2Six
public import CFSG.Quasithin.Background.F1Models

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits

section OddQuotient

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem mem_pCoreOf_of_odd_quotient1515c {K : Subgroup G}
    (hK : Odd (Nat.card (↥K ⧸ CFSG.pCore 2 ↥K))) {x : G} (hx : x ∈ K) {k : ℕ}
    (hk : x ^ 2 ^ k = 1) : x ∈ pCoreOf 2 K := by
  set z : ↥K ⧸ CFSG.pCore 2 ↥K := QuotientGroup.mk (⟨x, hx⟩ : ↥K) with hz
  have hz1 : z ^ 2 ^ k = 1 := by
    rw [hz, ← QuotientGroup.mk_pow]
    have : (⟨x, hx⟩ : ↥K) ^ 2 ^ k = 1 := Subtype.ext (by simpa using hk)
    rw [this, QuotientGroup.mk_one]
  have h1 : orderOf z ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one hz1
  have h2 : orderOf z ∣ Nat.card (↥K ⧸ CFSG.pCore 2 ↥K) := orderOf_dvd_natCard z
  have hcop : Nat.Coprime (2 ^ k) (Nat.card (↥K ⧸ CFSG.pCore 2 ↥K)) :=
    Nat.Coprime.pow_left k (Nat.coprime_two_left.mpr hK)
  have h3 : orderOf z = 1 :=
    Nat.Coprime.eq_one_of_dvd (Nat.Coprime.coprime_dvd_left h1 hcop) h2
  have h4 : z = 1 := orderOf_eq_one_iff.mp h3
  have h6 : (⟨x, hx⟩ : ↥K) ∈ CFSG.pCore 2 ↥K := (QuotientGroup.eq_one_iff _).mp h4
  exact (C2Six.mem_pCore_two_iff (L := K) (y := ⟨x, hx⟩)).mp h6

omit [Finite G] in
theorem exists_pow_mem_of_mem_sup1515c {K Q : Subgroup G} (hQ : IsPGroup 2 Q)
    (hN : Q ≤ Subgroup.normalizer (K : Set G)) {x : G} (hx : x ∈ K ⊔ Q) :
    ∃ k : ℕ, x ^ 2 ^ k ∈ K := by
  have hxset : x ∈ ((K ⊔ Q : Subgroup G) : Set G) := hx
  rw [Subgroup.coe_mul_of_right_le_normalizer_left _ _ hN] at hxset
  obtain ⟨y, hy, r, hr, rfl⟩ := hxset
  obtain ⟨k, hk⟩ := hQ ⟨r, hr⟩
  refine ⟨k, ?_⟩
  set X : Subgroup G := K ⊔ Q with hX
  have hKX : K ≤ X := le_sup_left
  have hQX : Q ≤ X := le_sup_right
  have hXN : X ≤ Subgroup.normalizer (K : Set G) := sup_le Subgroup.le_normalizer hN
  have : (K.subgroupOf X).Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hKX).mpr hXN
  have hyX : y ∈ X := hKX hy
  have hrX : r ∈ X := hQX hr
  have hrk : (⟨r, hrX⟩ : ↥X) ^ 2 ^ k = 1 := by
    apply Subtype.ext
    have := congrArg Subtype.val hk
    simpa using this
  have h1 : (QuotientGroup.mk (⟨y, hyX⟩ : ↥X) : ↥X ⧸ K.subgroupOf X) = 1 :=
    (QuotientGroup.eq_one_iff _).mpr hy
  have h2 : (⟨y * r, X.mul_mem hyX hrX⟩ : ↥X) ^ 2 ^ k ∈ K.subgroupOf X := by
    rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_pow]
    have : (⟨y * r, X.mul_mem hyX hrX⟩ : ↥X) = ⟨y, hyX⟩ * ⟨r, hrX⟩ := rfl
    rw [this, QuotientGroup.mk_mul, h1, one_mul, ← QuotientGroup.mk_pow, hrk, QuotientGroup.mk_one]
  have h3 := Subgroup.mem_subgroupOf.mp h2
  simpa using h3

theorem isSylowTwoOf_sup_of_odd_quotient1515c {K Q : Subgroup G} (hQ : IsPGroup 2 Q)
    (hN : Q ≤ Subgroup.normalizer (K : Set G))
    (hK : Odd (Nat.card (↥K ⧸ CFSG.pCore 2 ↥K))) (hOQ : pCoreOf 2 K ≤ Q) :
    IsSylowTwoOf Q (K ⊔ Q) := by
  refine A4.isSylowTwoOf_iff_maximal.mpr ⟨le_sup_right, hQ, fun P hP hPp hQP => ?_⟩
  intro q hq
  have hqYR : q ∈ ((K ⊔ Q : Subgroup G) : Set G) := hP hq
  rw [Subgroup.coe_mul_of_right_le_normalizer_left _ _ hN] at hqYR
  obtain ⟨y, hy, r, hr, rfl⟩ := hqYR
  have hyP : y ∈ P := by
    have : y * r * r⁻¹ ∈ P := P.mul_mem hq (P.inv_mem (hQP hr))
    simpa using this
  have hyO : y ∈ pCoreOf 2 K := by
    obtain ⟨k, hk⟩ := hPp ⟨y, hyP⟩
    exact mem_pCoreOf_of_odd_quotient1515c hK hy (k := k) (by
      have := congrArg Subtype.val hk
      simpa using this)
  exact Q.mul_mem (hOQ hyO) hr

theorem charTwo_sup_of_odd_quotient1515c {K Q : Subgroup G} (hQ : IsPGroup 2 Q)
    (hN : Q ≤ Subgroup.normalizer (K : Set G)) (hF : CharTwo K) : CharTwo (K ⊔ Q) :=
  CFSG.QuasithinUnique.CharTwo.sup_of_le_normalizer hF hQ hN

theorem isSolvable_of_odd_quotient1515c {K : Subgroup G}
    (hK : Odd (Nat.card (↥K ⧸ CFSG.pCore 2 ↥K))) : Group.IsSolvable ↥K := by
  set N : Subgroup ↥K := CFSG.pCore 2 ↥K with hNdef
  have hN2 : IsPGroup 2 N := CFSG.pCore_isPGroup (G := ↥K) (p := 2)
  have hNn : Group.IsNilpotent ↥N := hN2.isNilpotent
  have hNs : Group.IsSolvable ↥N := inferInstance
  have hQs : Group.IsSolvable (↥K ⧸ N) := CFSG.FeitThompson.isSolvable_of_odd_natCard _ hK
  exact Group.isSolvable_of_ker_le_range N.subtype (QuotientGroup.mk' N) (by
    intro x hx
    exact ⟨⟨x, (QuotientGroup.eq_one_iff x).mp hx⟩, rfl⟩)

theorem isSolvable_sup_of_odd_quotient1515c {K Q : Subgroup G} (hQ : IsPGroup 2 Q)
    (hN : Q ≤ Subgroup.normalizer (K : Set G)) (hK : Odd (Nat.card (↥K ⧸ CFSG.pCore 2 ↥K))) :
    Group.IsSolvable ↥(K ⊔ Q) := by
  have : Group.IsSolvable ↥K := isSolvable_of_odd_quotient1515c hK
  have : Group.IsNilpotent ↥Q := hQ.isNilpotent
  have : Group.IsSolvable ↥Q := inferInstance
  exact A3.isSolvable_sup_of_le_normalizer hN

end OddQuotient

end CFSG.Quasithin
