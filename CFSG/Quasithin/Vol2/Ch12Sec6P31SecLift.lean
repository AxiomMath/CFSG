module

public import CFSG.Quasithin.Vol2.Ch12Sec6P31a

public section

namespace CFSG.Quasithin.H13.P31Sec

open CFSG.Open CFSG.Quasithin S126 S126P31

theorem exists_lift_threePower {A B : Type} [Group A] [Group B] (f : A →* B)
    (hf : Function.Surjective f) (hker : IsPGroup 2 ↥f.ker) {b : B} {k : ℕ} (hb : b ^ 3 ^ k = 1) :
    ∃ a : A, f a = b ∧ ∃ m : ℕ, a ^ 3 ^ m = 1 := by
  obtain ⟨a₀, rfl⟩ := hf b
  have hmem : a₀ ^ 3 ^ k ∈ f.ker := by
    rw [MonoidHom.mem_ker, map_pow]
    exact hb
  obtain ⟨j, hj⟩ := hker ⟨a₀ ^ 3 ^ k, hmem⟩
  have hj' : (a₀ ^ 3 ^ k) ^ 2 ^ j = 1 := by
    have := congrArg Subtype.val hj
    simpa using this
  have hco : Nat.Coprime (3 ^ k) (2 ^ j) :=
    Nat.Coprime.pow k j (by norm_num)
  obtain ⟨s, hs1, hs2⟩ := Nat.chineseRemainder hco 1 0
  refine ⟨a₀ ^ s, ?_, k, ?_⟩
  · rw [map_pow, pow_eq_pow_mod s hb, show s % 3 ^ k = 1 % 3 ^ k from hs1]
    exact (pow_eq_pow_mod 1 hb).symm.trans (pow_one _)
  · obtain ⟨t, ht⟩ : 2 ^ j ∣ s := Nat.dvd_of_mod_eq_zero hs2
    have h3 : 2 ^ j * t * 3 ^ k = 3 ^ k * 2 ^ j * t := by ring
    rw [← pow_mul, ht, h3, pow_mul, pow_mul, hj', one_pow]

section Star

variable {G : Type} [Group G] [Finite G]

theorem oThreePrimeResidual_star_le {H Y : Subgroup G} (hYH : Y ≤ H) :
    oThreePrimeResidual (S126.star H Y) ≤ S126.star H (oThreePrimeResidual Y) := by
  refine (Subgroup.closure_le _).2 ?_
  rintro x ⟨hx, k, hxk⟩
  let f : ↥(Y.subgroupOf H) →* ↥(S126.star H Y) :=
    (QuotientGroup.mk' (CFSG.pCore 2 ↥H)).subgroupMap (Y.subgroupOf H)
  have hf : Function.Surjective f := MonoidHom.subgroupMap_surjective _ _
  have hker : IsPGroup 2 ↥f.ker := by
    intro y
    have hy : (QuotientGroup.mk' (CFSG.pCore 2 ↥H)) ((y : ↥(Y.subgroupOf H)) : ↥H) = 1 :=
      congrArg Subtype.val y.2
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hy
    obtain ⟨m, hm⟩ := (CFSG.pCore_isPGroup (p := 2) (G := ↥H)) ⟨_, hy⟩
    refine ⟨m, Subtype.ext (Subtype.ext ?_)⟩
    have := congrArg (fun z : ↥(CFSG.pCore 2 ↥H) => ((z : ↥H))) hm
    simpa using this
  have hb : (⟨x, hx⟩ : ↥(S126.star H Y)) ^ 3 ^ k = 1 := Subtype.ext (by simpa using hxk)
  obtain ⟨a, haf, m, ham⟩ := exists_lift_threePower f hf hker hb
  have haY : (((a : ↥(Y.subgroupOf H)) : ↥H) : G) ∈ Y := Subgroup.mem_subgroupOf.1 a.2
  have ha3 : (((a : ↥(Y.subgroupOf H)) : ↥H) : G) ^ 3 ^ m = 1 := by
    have := congrArg (fun z : ↥(Y.subgroupOf H) => (((z : ↥(Y.subgroupOf H)) : ↥H) : G)) ham
    simpa using this
  have hxa : x = (QuotientGroup.mk ((a : ↥(Y.subgroupOf H)) : ↥H) : HStar H) := by
    have := congrArg Subtype.val haf
    exact this.symm
  rw [hxa]
  exact mk_mem_star (h := ((a : ↥(Y.subgroupOf H)) : ↥H))
    (Subgroup.subset_closure ⟨haY, m, ha3⟩)

end Star

end CFSG.Quasithin.H13.P31Sec
