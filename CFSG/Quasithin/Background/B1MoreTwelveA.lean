module

public import CFSG.Quasithin.Background.B1MoreTenA

public section

namespace CFSG.Quasithin

open CFSG.Open
open scoped commutatorElement

namespace B1Red

section Group

variable {Ω : Type*} [Group Ω]

theorem mem_of_two_pow_mem_of_odd {N : Subgroup Ω} {x : Ω} {j : ℕ} (hx : x ^ 2 ^ j ∈ N)
    (ho : Odd (orderOf x)) : x ∈ N := by
  have hcop : Nat.Coprime (2 ^ j) (orderOf x) :=
    Nat.Coprime.pow_left j (Nat.coprime_two_left.2 ho)
  exact (Subgroup.zpowers_le.2 hx) (A4.mem_zpowers_pow_of_coprime hcop)

theorem mul_mem_of_odd_orderOf {N : Subgroup Ω} {n a : Ω} (hn : n ∈ N)
    (ha : a ∈ Subgroup.normalizer (N : Set Ω)) {j : ℕ} (haj : a ^ 2 ^ j = 1)
    (ho : Odd (orderOf (n * a))) : n * a ∈ N := by
  obtain ⟨x', hx', h⟩ := A4.exists_pow_mul_eq hn ha (2 ^ j)
  rw [haj, mul_one] at h
  exact mem_of_two_pow_mem_of_odd (h ▸ hx') ho

theorem mem_of_odd_orderOf_of_mem_sup {N T : Subgroup Ω} (hT : IsPGroup 2 T)
    (hn : T ≤ Subgroup.normalizer (N : Set Ω)) {x : Ω} (hx : x ∈ N ⊔ T)
    (ho : Odd (orderOf x)) : x ∈ N := by
  obtain ⟨n, hnN, t, htT, rfl⟩ := (B19Aux.mem_sup_iff_of_le_normalizer hn).1 hx
  obtain ⟨j, hj⟩ := hT ⟨t, htT⟩
  exact mul_mem_of_odd_orderOf hnN (hn htT) (j := j) (congrArg Subtype.val hj) ho

theorem odd_orderOf_of_isPGroup_three {R : Subgroup Ω} (h : IsPGroup 3 R) {x : Ω} (hx : x ∈ R) :
    Odd (orderOf x) := by
  obtain ⟨i, hi⟩ := IsPGroup.iff_orderOf.1 h ⟨x, hx⟩
  rw [Subgroup.orderOf_mk] at hi
  rw [hi]
  exact Odd.pow (by decide)

theorem conj_mem_pCoreOf_prime (p : ℕ) {H : Subgroup Ω} {h q : Ω} (hh : h ∈ H)
    (hq : q ∈ pCoreOf p H) : h * q * h⁻¹ ∈ pCoreOf p H :=
  (Subgroup.mem_normalizer_iff.mp (CFSG.LieType.BorelTits.le_normalizer_pCoreOf p H hh) q).mp hq

theorem isSolvable_sup_of_isSolvable_of_le_normalizer {F A' : Subgroup Ω}
    (hn : A' ≤ Subgroup.normalizer (F : Set Ω)) [Group.IsSolvable ↥F] [Group.IsSolvable ↥A'] :
    Group.IsSolvable ↥(F ⊔ A') := by
  have hN : (F.subgroupOf (F ⊔ A')).Normal := by
    refine ⟨fun x hx g => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hx ⊢
    have := B19Aux.conj_mem_sup_of_le_normalizer hn g.2 hx
    simpa using this
  have hsolvN : Group.IsSolvable ↥(F.subgroupOf (F ⊔ A')) :=
    Group.isSolvable_of_isSolvable_injective
      (f := (Subgroup.subgroupOfEquivOfLe (le_sup_left : F ≤ F ⊔ A')).toMonoidHom)
      (Subgroup.subgroupOfEquivOfLe (le_sup_left : F ≤ F ⊔ A')).injective
  have hsolvA : Group.IsSolvable ↥(A'.subgroupOf (F ⊔ A')) :=
    Group.isSolvable_of_isSolvable_injective
      (f := (Subgroup.subgroupOfEquivOfLe (le_sup_right : A' ≤ F ⊔ A')).toMonoidHom)
      (Subgroup.subgroupOfEquivOfLe (le_sup_right : A' ≤ F ⊔ A')).injective
  have hsurj : Function.Surjective
      ((QuotientGroup.mk' (F.subgroupOf (F ⊔ A'))).comp (A'.subgroupOf (F ⊔ A')).subtype) := by
    intro q
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective q
    obtain ⟨f, hf, a, ha, hx⟩ := (B19Aux.mem_sup_iff_of_le_normalizer hn).1 x.2
    refine ⟨⟨⟨a, Subgroup.mem_sup_right ha⟩, ha⟩, ?_⟩
    show (QuotientGroup.mk (⟨a, Subgroup.mem_sup_right ha⟩ : ↥(F ⊔ A')) :
      ↥(F ⊔ A') ⧸ F.subgroupOf (F ⊔ A')) = QuotientGroup.mk x
    rw [QuotientGroup.eq, Subgroup.mem_subgroupOf]
    have h1 : (((⟨a, Subgroup.mem_sup_right ha⟩ : ↥(F ⊔ A'))⁻¹ * x : ↥(F ⊔ A')) : Ω) =
        a⁻¹ * f * a⁻¹⁻¹ := by
      show a⁻¹ * (x : Ω) = _
      rw [hx]
      group
    rw [h1]
    exact B19Aux.conj_mem_of_le_normalizer hn (A'.inv_mem ha) hf
  have hsolvQ : Group.IsSolvable (↥(F ⊔ A') ⧸ F.subgroupOf (F ⊔ A')) :=
    Group.isSolvable_of_surjective hsurj
  exact Group.isSolvable_of_ker_le_range (F.subgroupOf (F ⊔ A')).subtype
    (QuotientGroup.mk' (F.subgroupOf (F ⊔ A')))
    (by rw [QuotientGroup.ker_mk', Subgroup.range_subtype])

end Group

section K0Basic

variable {Ω : Type*} [Group Ω] {T K : Subgroup Ω}

theorem conjClosure_le_sup : conjClosure K T ≤ T ⊔ K :=
  conjClosure_le fun _ hh _ hz =>
    (T ⊔ K).mul_mem ((T ⊔ K).mul_mem (Subgroup.mem_sup_left hh) (Subgroup.mem_sup_right hz))
      ((T ⊔ K).inv_mem (Subgroup.mem_sup_left hh))

theorem le_normalizer_conjClosure_sup : T ⊔ K ≤ Subgroup.normalizer (conjClosure K T : Set Ω) :=
  sup_le (le_normalizer_conjClosure K T)
    ((le_conjClosure K T).trans Subgroup.le_normalizer)

theorem sup_le_conjClosure_sup : T ⊔ K ≤ conjClosure K T ⊔ T :=
  sup_le le_sup_right ((le_conjClosure K T).trans le_sup_left)

theorem odd_mem_conjClosure (hT : IsPGroup 2 T) {x : Ω} (hx : x ∈ T ⊔ K)
    (ho : Odd (orderOf x)) : x ∈ conjClosure K T :=
  mem_of_odd_orderOf_of_mem_sup hT (le_normalizer_conjClosure K T)
    (sup_le_conjClosure_sup hx) ho

end K0Basic

section K0

variable {Ω : Type*} [Group Ω] [Finite Ω] {T K : Subgroup Ω}

theorem le_pCoreOf_three_of_subnormal (hK : Nat.card ↥K = 3) {H : Subgroup Ω}
    (hsub : IsSubnormal K H) : K ≤ pCoreOf 3 H := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have h3 : IsPGroup 3 ↥K := IsPGroup.of_card (n := 1) (by rw [hK]; simp)
  have h1 : K ≤ pCoreOf 3 K :=
    CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 3 le_rfl Subgroup.le_normalizer h3
  exact h1.trans (A4.pCoreOf_le_of_subnormal 3 hsub)

theorem conjClosure_le_pCoreOf_three (hK : Nat.card ↥K = 3) (hsub : IsSubnormal K (T ⊔ K)) :
    conjClosure K T ≤ pCoreOf 3 (T ⊔ K) := by
  refine conjClosure_le fun h hh z hz => ?_
  exact conj_mem_pCoreOf_prime 3 (Subgroup.mem_sup_left hh)
    (le_pCoreOf_three_of_subnormal hK hsub hz)

theorem isPGroup_conjClosure (hK : Nat.card ↥K = 3) (hsub : IsSubnormal K (T ⊔ K)) :
    IsPGroup 3 ↥(conjClosure K T) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  exact (CFSG.LieType.BorelTits.pCoreOf_isPGroup 3 (T ⊔ K)).to_le
    (conjClosure_le_pCoreOf_three hK hsub)

theorem commute_conjClosure_pCoreOf (hK : Nat.card ↥K = 3) (hsub : IsSubnormal K (T ⊔ K)) :
    ∀ x ∈ conjClosure K T, ∀ q ∈ pCoreOf 2 (T ⊔ K), x * q = q * x := by
  intro x hx q hq
  have hodd : ∀ r ∈ conjClosure K T, Odd (orderOf r) := fun r hr =>
    odd_orderOf_of_isPGroup_three (isPGroup_conjClosure hK hsub) hr
  have hn : ∀ h ∈ T ⊔ K, ∀ r ∈ conjClosure K T, h * r * h⁻¹ ∈ conjClosure K T :=
    fun h hh r hr => B19Aux.conj_mem_of_le_normalizer le_normalizer_conjClosure_sup hh hr
  exact (pCoreOf_commute_of_odd_normal conjClosure_le_sup hn hodd q hq x hx).symm

theorem conjClosure_inf_pCoreOf (hK : Nat.card ↥K = 3) (hsub : IsSubnormal K (T ⊔ K)) :
    conjClosure K T ⊓ pCoreOf 2 (T ⊔ K) = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine (Subgroup.eq_bot_iff_forall _).2 fun x hx => ?_
  have hQ2 : IsPGroup 2 ↥(pCoreOf 2 (T ⊔ K)) := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 (T ⊔ K)
  obtain ⟨j, hj⟩ := hQ2 ⟨x, hx.2⟩
  exact B19Aux.eq_one_of_odd_orderOf_of_pow
    (odd_orderOf_of_isPGroup_three (isPGroup_conjClosure hK hsub) hx.1) (k := j)
    (congrArg Subtype.val hj)

theorem isSolvable_sup (hT : IsPGroup 2 T) (hK : Nat.card ↥K = 3)
    (hsub : IsSubnormal K (T ⊔ K)) : Group.IsSolvable ↥(T ⊔ K) := by
  have h3 : IsPGroup 3 ↥(conjClosure K T) := isPGroup_conjClosure hK hsub
  have : Group.IsNilpotent ↥(conjClosure K T) := h3.isNilpotent
  have : Group.IsNilpotent ↥T := hT.isNilpotent
  have hS : Group.IsSolvable ↥(conjClosure K T ⊔ T) :=
    isSolvable_sup_of_isSolvable_of_le_normalizer (le_normalizer_conjClosure K T)
  exact Group.isSolvable_of_isSolvable_injective
    (f := (Subgroup.inclusion (sup_le_conjClosure_sup : T ⊔ K ≤ conjClosure K T ⊔ T)))
    (Subgroup.inclusion_injective _)

end K0

end B1Red

end CFSG.Quasithin
