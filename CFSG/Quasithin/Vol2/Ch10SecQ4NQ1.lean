module

public import CFSG.Quasithin.Background.A3Structure37Comm
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.OffenderGroup

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecF.C10P4F

open CFSG.Open CFSG.Quasithin
open scoped commutatorElement

variable {G : Type} [Group G]

theorem eq_one_or_eq_of_mem_zpowers' {z x : G} (hz : z * z = 1) (hx : x ∈ Subgroup.zpowers z) :
    x = 1 ∨ x = z := by
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
  have h2 : z ^ (2 : ℤ) = 1 := by rw [zpow_two, hz]
  have e : z ^ k = z ^ (k % 2) := by
    conv_lhs => rw [← Int.emod_add_mul_ediv k 2]
    rw [zpow_add, zpow_mul, h2, one_zpow, mul_one]
  rcases Int.emod_two_eq_zero_or_one k with h | h
  · left; rw [e, h, zpow_zero]
  · right; rw [e, h, zpow_one]

theorem commutator_zpowers_le {A : Subgroup G} {z : G}
    (hzA : z ∈ Subgroup.normalizer (A : Set G)) : ⁅A, Subgroup.zpowers z⁆ ≤ A := by
  rw [Subgroup.commutator_le]
  intro a ha y hy
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
  have hk : z ^ k ∈ Subgroup.normalizer (A : Set G) := Subgroup.zpow_mem _ hzA k
  rw [commutatorElement_def]
  have e : a * z ^ k * a⁻¹ * (z ^ k)⁻¹ = a * (z ^ k * a⁻¹ * (z ^ k)⁻¹) := by group
  rw [e]
  exact A.mul_mem ha ((Subgroup.mem_normalizer_iff.mp hk _).mp (A.inv_mem ha))

variable [Finite G]

omit [Finite G] in
theorem commutator_zpowers_idem {A : Subgroup G} (hA : Odd (Nat.card A)) {z : G}
    (hz : z * z = 1) (hzA : z ∈ Subgroup.normalizer (A : Set G)) :
    ⁅⁅A, Subgroup.zpowers z⁆, Subgroup.zpowers z⁆ = ⁅A, Subgroup.zpowers z⁆ := by
  refine le_antisymm (Subgroup.commutator_mono (commutator_zpowers_le hzA) le_rfl) ?_
  rw [Subgroup.commutator_le]
  intro a ha y hy
  rcases eq_one_or_eq_of_mem_zpowers' hz hy with h | h
  · rw [h, commutatorElement_one_right]
    exact Subgroup.one_mem _
  rw [h]
  have hzi : z⁻¹ = z := inv_eq_of_mul_eq_one_right hz
  set g := ⁅a, z⁆ with hg
  have hgD : g ∈ ⁅A, Subgroup.zpowers z⁆ :=
    Subgroup.commutator_mem_commutator ha (Subgroup.mem_zpowers z)
  have hgA : g ∈ A := commutator_zpowers_le hzA hgD
  have hinv : z * g * z⁻¹ = g⁻¹ := by
    rw [hg, commutatorElement_def]
    calc z * (a * z * a⁻¹ * z⁻¹) * z⁻¹ = z * a * z * a⁻¹ * (z⁻¹ * z⁻¹) := by group
      _ = z * a * z * a⁻¹ := by rw [hzi, hz, mul_one]
      _ = (a * z * a⁻¹ * z⁻¹)⁻¹ := by
        rw [hzi, mul_inv_rev, mul_inv_rev, mul_inv_rev, inv_inv, hzi]
        group
  set m := orderOf g with hm
  have hmodd : Odd m := hA.of_dvd_nat (by
    have := orderOf_dvd_natCard (⟨g, hgA⟩ : ↥A)
    rwa [Subgroup.orderOf_mk] at this)
  obtain ⟨k, hk⟩ := hmodd
  have hpow : ∀ n : ℕ, z * g ^ n * z⁻¹ = (g ^ n)⁻¹ := fun n => by
    rw [← conj_pow, hinv, inv_pow]
  have e : ⁅g ^ (k + 1), z⁆ = g := by
    rw [commutatorElement_def]
    have h1 : z * (g ^ (k + 1))⁻¹ * z⁻¹ = g ^ (k + 1) := by
      rw [← inv_inj, mul_inv_rev, mul_inv_rev, inv_inv, inv_inv, ← mul_assoc, hpow]
    calc g ^ (k + 1) * z * (g ^ (k + 1))⁻¹ * z⁻¹ = g ^ (k + 1) * (z * (g ^ (k + 1))⁻¹ * z⁻¹) :=
          by group
      _ = g ^ (k + 1) * g ^ (k + 1) := by rw [h1]
      _ = g ^ m * g := by rw [← pow_add, show k + 1 + (k + 1) = m + 1 by omega, pow_succ]
      _ = g := by rw [hm, pow_orderOf_eq_one, one_mul]
  rw [← e]
  exact Subgroup.commutator_mem_commutator (Subgroup.pow_mem _ hgD _) (Subgroup.mem_zpowers z)

omit [Finite G] in
theorem exists_odd_preimage {B : Type*} [Group B] (π : G →* B) {y : G} (hy0 : 0 < orderOf y)
    (hy : Odd (orderOf (π y))) : ∃ y' ∈ Subgroup.zpowers y, Odd (orderOf y') ∧ π y' = π y := by
  obtain ⟨a, m, hm, hn⟩ := Nat.exists_eq_two_pow_mul_odd hy0.ne'
  set y1 := y ^ 2 ^ a with hy1
  have hy1o : orderOf y1 = m := by
    rw [hy1, orderOf_pow_of_dvd (pow_ne_zero a two_ne_zero) ⟨m, hn⟩, hn,
      Nat.mul_div_cancel_left m (pow_pos two_pos a)]
  have hcop : Nat.Coprime (2 ^ a) (orderOf (π y)) :=
    Nat.Coprime.pow_left a (Nat.coprime_two_left.mpr hy)
  rcases Nat.lt_or_ge 1 (orderOf (π y)) with h1 | h1
  · obtain ⟨b, -, hb⟩ := Nat.exists_mul_mod_eq_one_of_coprime hcop h1
    refine ⟨y1 ^ b, Subgroup.pow_mem _ (Subgroup.pow_mem _ (Subgroup.mem_zpowers y) _) _,
      ?_, ?_⟩
    · exact hm.of_dvd_nat (hy1o ▸ orderOf_pow_dvd b)
    · rw [map_pow, hy1, map_pow, ← pow_mul, ← pow_mod_orderOf, hb, pow_one]
  · have h1' : orderOf (π y) = 1 := by
      obtain ⟨k, hk⟩ := hy
      omega
    refine ⟨1, Subgroup.one_mem _, by rw [orderOf_one]; exact odd_one, ?_⟩
    rw [map_one, orderOf_eq_one_iff.mp h1']

omit [Finite G] in
theorem commute_of_odd_of_mem {W : Subgroup G} (hW2 : ∀ w ∈ W, w * w = 1) {x q : G}
    (hx : Odd (orderOf x)) (hxW : ∀ w ∈ W, x * w = w * x) (hxq : x * q * x⁻¹ * q⁻¹ ∈ W) :
    x * q = q * x := by
  set w := x * q * x⁻¹ * q⁻¹ with hw
  have h1 : x * q * x⁻¹ = w * q := by rw [hw]; group
  have hn : ∀ n : ℕ, x ^ n * q * (x ^ n)⁻¹ = w ^ n * q := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      have hc : x * w ^ n = w ^ n * x := (Commute.pow_right (hxW w hxq) n).eq
      calc x ^ (n + 1) * q * (x ^ (n + 1))⁻¹ = x * (x ^ n * q * (x ^ n)⁻¹) * x⁻¹ := by
            rw [pow_succ']; group
        _ = x * w ^ n * q * x⁻¹ := by rw [ih]; group
        _ = w ^ n * (x * q * x⁻¹) := by rw [hc]; group
        _ = w ^ (n + 1) * q := by rw [h1, pow_succ]; group
  have h2 := hn (orderOf x)
  rw [pow_orderOf_eq_one, one_mul, inv_one, mul_one] at h2
  have hwn : w ^ orderOf x = 1 := by
    have := congrArg (· * q⁻¹) h2
    simpa using this.symm
  obtain ⟨k, hk⟩ := hx
  have hw1 : w = 1 := by
    rw [hk, pow_succ, pow_mul, sq, hW2 w hxq, one_pow, one_mul] at hwn
    exact hwn
  rw [hw1] at h1
  calc x * q = x * q * x⁻¹ * x := by group
    _ = q * x := by rw [h1, one_mul]

theorem mem_oddCoreOf_of_central {C S : Subgroup G} (hSC : S ≤ C) (hS2 : IsPGroup 2 S)
    (hcen : ∀ s ∈ S, ∀ c ∈ C, s * c = c * s) (hodd : ¬ 2 ∣ S.relIndex C) {x : G} (hxC : x ∈ C)
    (hx : Odd (orderOf x)) : x ∈ A37.oddCoreOf C := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set N := S.subgroupOf C with hN
  have hN2 : IsPGroup 2 N := hS2.of_equiv (Subgroup.subgroupOfEquivOfLe hSC).symm
  let P : Sylow 2 ↥C := hN2.toSylow hodd
  have hP : Subgroup.normalizer ((P : Subgroup ↥C) : Set ↥C) ≤
      Subgroup.centralizer ((P : Subgroup ↥C) : Set ↥C) := by
    intro c _
    rw [Subgroup.mem_centralizer_iff]
    intro n hn
    have hn' : (n : G) ∈ S := Subgroup.mem_subgroupOf.mp hn
    exact Subtype.ext (hcen _ hn' _ c.2)
  set f := MonoidHom.transferSylow P hP
  have hxk : (⟨x, hxC⟩ : ↥C) ∈ f.ker := by
    rw [MonoidHom.mem_ker]
    have h1 : orderOf (f ⟨x, hxC⟩) ∣ orderOf x :=
      (orderOf_map_dvd f (⟨x, hxC⟩ : ↥C)).trans (Subgroup.orderOf_mk x hxC).dvd
    obtain ⟨e, he⟩ := P.isPGroup' (f ⟨x, hxC⟩)
    have h2 := orderOf_dvd_of_pow_eq_one he
    have hcop : Nat.Coprime (2 ^ e) (orderOf x) := Nat.Coprime.pow_left e
      (Nat.coprime_two_left.mpr hx)
    exact orderOf_eq_one_iff.mp (Nat.dvd_one.mp (hcop.gcd_eq_one ▸ Nat.dvd_gcd h2 h1))
  have hko : Odd (Nat.card f.ker) :=
    Nat.odd_iff.mpr (Nat.two_dvd_ne_zero.mp (MonoidHom.not_dvd_card_ker_transferSylow P hP))
  have hkO : f.ker ≤ CFSG.oddCore ↥C := le_sSup ⟨inferInstance, hko⟩
  exact ⟨_, hkO hxk, rfl⟩

omit [Finite G] in
theorem le_of_perfect_of_le_sup [Finite G] {K C P : Subgroup G} (hKp : ⁅K, K⁆ = K)
    (hP2 : IsPGroup 2 P) (hKC : K ≤ Subgroup.normalizer (C : Set G))
    (hPC : P ≤ Subgroup.normalizer (C : Set G)) (hK : K ≤ C ⊔ P) : K ≤ C := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set N := (K ⊓ C).subgroupOf K with hNdef
  have hNn : N.Normal := ⟨fun n hn g => by
    rw [hNdef, Subgroup.mem_subgroupOf] at hn ⊢
    refine ⟨K.mul_mem (K.mul_mem g.2 hn.1) (K.inv_mem g.2), ?_⟩
    exact (Subgroup.mem_normalizer_iff.mp (hKC g.2) n).mp hn.2⟩
  have h2 : IsPGroup 2 (↥K ⧸ N) := by
    intro g
    obtain ⟨k, rfl⟩ := QuotientGroup.mk_surjective g
    have hk : (k : G) ∈ ((C ⊔ P : Subgroup G) : Set G) := hK k.2
    rw [Subgroup.coe_mul_of_right_le_normalizer_left C P hPC] at hk
    obtain ⟨c, hc, p, hp, hkcp⟩ := Set.mem_mul.mp hk
    obtain ⟨e, he⟩ := hP2 ⟨p, hp⟩
    have hpe : p ^ 2 ^ e = 1 := by simpa using congrArg Subtype.val he
    have key : ∀ n : ℕ, ∃ c' ∈ C, (c * p) ^ n = c' * p ^ n := by
      intro n
      induction n with
      | zero => exact ⟨1, C.one_mem, by simp⟩
      | succ n ih =>
        obtain ⟨c', hc', e'⟩ := ih
        have hc2 : p ^ n * c * (p ^ n)⁻¹ ∈ C :=
          (Subgroup.mem_normalizer_iff.mp (hPC (P.pow_mem hp n)) c).mp hc
        refine ⟨c' * (p ^ n * c * (p ^ n)⁻¹), C.mul_mem hc' hc2, ?_⟩
        rw [pow_succ, e', pow_succ]
        group
    obtain ⟨c', hc', e'⟩ := key (2 ^ e)
    rw [hpe, mul_one] at e'
    refine ⟨e, ?_⟩
    rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff, hNdef, Subgroup.mem_subgroupOf]
    refine ⟨K.pow_mem k.2 _, ?_⟩
    rw [Subgroup.coe_pow, ← hkcp, e']
    exact hc'
  have htop := CFSG.QuasithinUnique.Setup.Offender.noPQuotient_of_perfect Nat.prime_two
    (Subgroup.isPerfect_iff.2 hKp) N h2
  intro k hk
  have : (⟨k, hk⟩ : ↥K) ∈ N := htop ▸ Subgroup.mem_top _
  exact (Subgroup.mem_subgroupOf.mp this).2

end CFSG.Quasithin.Vol2.Ch10.SecF.C10P4F
