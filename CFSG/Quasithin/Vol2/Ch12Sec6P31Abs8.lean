module

public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.Quasithin.Background.F8G2
public import CFSG.Quasithin.Vol2.Ch12Sec6Frame

public section

namespace CFSG.Quasithin.H13.S126P31

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.LieType.BorelTits S126 Equiv

private theorem eq_bot_of_perfect_solvable_S126P31 {Q : Type*} [Group Q] [Group.IsSolvable Q]
    {X : Subgroup Q} (h : ⁅X, X⁆ = X) : X = ⊥ := by
  have key : ∀ n, X ≤ derivedSeries Q n := by
    intro n
    induction n with
    | zero => exact le_top
    | succ n ih =>
      rw [derivedSeries_succ, ← h]
      exact Subgroup.commutator_mono ih ih
  obtain ⟨n, hn⟩ := Group.IsSolvable.solvable (G := Q)
  exact le_bot_iff.1 (hn ▸ key n)

theorem normal_oTwoRes_top {Y : Type*} [Group Y] : (oTwoRes (⊤ : Subgroup Y)).Normal := by
  have h := le_normalizer_oTwoRes (⊤ : Subgroup Y)
  exact Subgroup.normalizer_eq_top_iff.1 (top_le_iff.1 h)

theorem exists_pow_two_mem_oTwoRes_top {Y : Type*} [Group Y] [Finite Y] (y : Y) :
    ∃ k : ℕ, y ^ 2 ^ k ∈ oTwoRes (⊤ : Subgroup Y) := by
  obtain ⟨k, m, hm, hkm⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos y).ne'
  refine ⟨k, ?_⟩
  refine Subgroup.subset_closure ⟨Subgroup.mem_top _, m, hm, ?_⟩
  rw [← pow_mul, ← hkm, pow_orderOf_eq_one]

theorem le_oTwoRes_top_of_perfect {Y : Type*} [Group Y] [Finite Y] (X : Subgroup Y)
    (hX : ⁅X, X⁆ = X) : X ≤ oTwoRes (⊤ : Subgroup Y) := by
  haveI : (oTwoRes (⊤ : Subgroup Y)).Normal := normal_oTwoRes_top
  have hp : IsPGroup 2 (Y ⧸ oTwoRes (⊤ : Subgroup Y)) := by
    intro q
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective q
    obtain ⟨k, hk⟩ := exists_pow_two_mem_oTwoRes_top x
    refine ⟨k, ?_⟩
    rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]
    exact hk
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI := hp.isNilpotent
  have hbot : X.map (QuotientGroup.mk' (oTwoRes (⊤ : Subgroup Y))) = ⊥ := by
    apply eq_bot_of_perfect_solvable_S126P31
    rw [← Subgroup.map_commutator, hX]
  intro x hx
  have hmem : QuotientGroup.mk' (oTwoRes (⊤ : Subgroup Y)) x ∈
      X.map (QuotientGroup.mk' (oTwoRes (⊤ : Subgroup Y))) := Subgroup.mem_map_of_mem _ hx
  rw [hbot, Subgroup.mem_bot, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hmem
  exact hmem

theorem inf_oTwoRes_le {Y : Type*} [Group Y] [Finite Y] (X P Ts : Subgroup Y) [X.Normal]
    [P.Normal] (hXP : X ≤ P) (hidx : P.index = 4) (hXidx : X.index = 12) (hT : IsPGroup 2 Ts) :
    Ts ⊓ oTwoRes (⊤ : Subgroup Y) ≤ X := by
  have hP4 : ∀ y : Y, y ^ 2 ^ 2 ∈ P := by
    intro y
    have h1 : (QuotientGroup.mk y : Y ⧸ P) ^ Nat.card (Y ⧸ P) = 1 := pow_card_eq_one'
    rw [← Subgroup.index_eq_card, hidx, ← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff] at h1
    exact h1
  have hOP : oTwoRes (⊤ : Subgroup Y) ≤ P := by
    rw [oTwoRes_eq_oTwoUpper]
    exact oTwoUpper_le_of_pow_mem fun y _ => ⟨2, hP4 y⟩
  have hrel : (X.subgroupOf P).index = 3 := by
    have h := Subgroup.relIndex_mul_index hXP
    rw [hidx, hXidx] at h
    have e : X.relIndex P = (X.subgroupOf P).index := rfl
    omega
  rintro y ⟨hyT, hyO⟩
  have hyP : y ∈ P := hOP hyO
  obtain ⟨k, hk⟩ := hT ⟨y, hyT⟩
  have hk' : y ^ 2 ^ k = 1 := by
    have h := congrArg Subtype.val hk
    simpa using h
  obtain ⟨q, hq⟩ : ∃ q : ↥P ⧸ X.subgroupOf P, q = QuotientGroup.mk ⟨y, hyP⟩ := ⟨_, rfl⟩
  have h3 : q ^ 3 = 1 := by
    have h := pow_card_eq_one' (G := ↥P ⧸ X.subgroupOf P) (x := q)
    rwa [← Subgroup.index_eq_card, hrel] at h
  have h2 : q ^ 2 ^ k = 1 := by
    rw [hq, ← QuotientGroup.mk_pow]
    have e : (⟨y, hyP⟩ : ↥P) ^ 2 ^ k = 1 := Subtype.ext (by simpa using hk')
    rw [e, QuotientGroup.mk_one]
  have hcop2 : Nat.Coprime 3 2 := by norm_num
  have hcop : Nat.gcd 3 (2 ^ k) = 1 := Nat.Coprime.pow_right k hcop2
  have hgcd : q ^ Nat.gcd 3 (2 ^ k) = 1 := pow_gcd_eq_one.mpr ⟨h3, h2⟩
  rw [hcop, pow_one, hq, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf] at hgcd
  exact hgcd

end CFSG.Quasithin.H13.S126P31
