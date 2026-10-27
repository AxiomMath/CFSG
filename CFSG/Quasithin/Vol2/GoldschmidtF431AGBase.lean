module

public import CFSG.Quasithin.Background.F7Basic
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.ConfinedInvolution
public import CFSG.Quasithin.Background.Ordering

public section

namespace CFSG.Quasithin.H13.F431.AG

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.LieType.BorelTits
open scoped Pointwise

variable {G : Type*} [Group G]

theorem eq_of_le_of_isSylowTwoOf [Finite G] {A B X : Subgroup G} (hA : IsSylowTwoOf A X)
    (hAB : A ≤ B) (hBX : B ≤ X) (hB : IsPGroup 2 B) : A = B := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h1 := Subgroup.relIndex_mul_relIndex A B X hAB hBX
  have hA' : ¬ 2 ∣ A.relIndex X := F7.isSylowTwoOf_odd_relIndex hA
  have hodd : ¬ 2 ∣ A.relIndex B := fun hd => hA' (h1 ▸ hd.mul_right _)
  obtain ⟨n, hn⟩ := hB.index (A.subgroupOf B)
  have hn' : A.relIndex B = 2 ^ n := hn
  rcases n with _ | n
  · exact le_antisymm hAB (Subgroup.relIndex_eq_one.mp hn')
  · exact absurd (hn' ▸ dvd_pow_self 2 (Nat.succ_ne_zero n)) hodd

theorem eq_of_inf_normalizer_le [Finite G] {D Q : Subgroup G} (hQ : IsPGroup 2 Q) (hDQ : D ≤ Q)
    (h : Q ⊓ Subgroup.normalizer (D : Set G) ≤ D) : D = Q := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Group.IsNilpotent ↥Q := hQ.isNilpotent
  have hnc := Group.normalizerCondition_of_isNilpotent (G := ↥Q)
  rw [normalizerCondition_iff_only_full_group_self_normalizing] at hnc
  have hself : Subgroup.normalizer (D.subgroupOf Q : Set ↥Q) = D.subgroupOf Q := by
    refine le_antisymm (fun x hx => ?_) Subgroup.le_normalizer
    rw [Subgroup.mem_subgroupOf]
    have hxn : (x : G) ∈ Subgroup.normalizer (D : Set G) := by
      rw [Subgroup.mem_normalizer_iff] at hx ⊢
      intro y
      constructor
      · intro hy
        have := (hx ⟨y, hDQ hy⟩).mp hy
        simpa [Subgroup.mem_subgroupOf] using this
      · intro hy
        have hyQ : y ∈ Q := by
          have : (x : G)⁻¹ * (x * y * x⁻¹) * x ∈ Q :=
            Q.mul_mem (Q.mul_mem (Q.inv_mem x.2) (hDQ hy)) x.2
          simpa [mul_assoc] using this
        have := (hx ⟨y, hyQ⟩).mpr (by simpa [Subgroup.mem_subgroupOf] using hy)
        simpa [Subgroup.mem_subgroupOf] using this
    exact h ⟨x.2, hxn⟩
  have htop := hnc _ hself
  refine le_antisymm hDQ fun y hy => ?_
  have : (⟨y, hy⟩ : ↥Q) ∈ D.subgroupOf Q := by rw [htop]; trivial
  simpa [Subgroup.mem_subgroupOf] using this

theorem le_normalizer_sup {N A B : Subgroup G} (hA : N ≤ Subgroup.normalizer (A : Set G))
    (hB : N ≤ Subgroup.normalizer (B : Set G)) :
    N ≤ Subgroup.normalizer ((A ⊔ B : Subgroup G) : Set G) := by
  have key : ∀ g ∈ N, conjSub g (A ⊔ B) ≤ A ⊔ B := by
    intro g hg
    have h1 : ∀ C : Subgroup G, g ∈ Subgroup.normalizer (C : Set G) → conjSub g C ≤ C := by
      intro C hC x hx
      rw [mem_conjSub] at hx
      have e : g * (g⁻¹ * x * g) * g⁻¹ = x := by group
      have := (Subgroup.mem_normalizer_iff.mp hC (g⁻¹ * x * g)).mp hx
      rwa [e] at this
    rw [conjSub_sup]
    exact sup_le_sup (h1 A (hA hg)) (h1 B (hB hg))
  exact fun g hg => F7.mem_normalizer_of_conj_le (key g hg) (key g⁻¹ (N.inv_mem hg))

theorem exists_pow_mem_sup_pCoreOf [Finite G] {N R : Subgroup G} (hRN : R ≤ N)
    (hNR : N ≤ Subgroup.normalizer (R : Set G)) {x : G} (hx : x ∈ R ⊔ pCoreOf 2 N) :
    ∃ k : ℕ, x ^ 2 ^ k ∈ R := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hYN : pCoreOf 2 N ≤ N := pCoreOf_le 2 N
  have hYR : pCoreOf 2 N ≤ Subgroup.normalizer (R : Set G) := hYN.trans hNR
  rw [sup_comm] at hx
  have hx' : x ∈ ((pCoreOf 2 N : Set G) * (R : Set G)) := by
    rw [← Subgroup.coe_mul_of_left_le_normalizer_right _ _ hYR]
    exact hx
  obtain ⟨y, hy, r, hr, rfl⟩ := hx'
  have hyN : y ∈ N := hYN hy
  have hrN : r ∈ N := hRN hr
  obtain ⟨k, hk⟩ := pCoreOf_isPGroup 2 N ⟨y, hy⟩
  have hyk : y ^ 2 ^ k = 1 := congrArg Subtype.val hk
  have hn : (R.subgroupOf N).Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hRN).mpr hNR
  refine ⟨k, ?_⟩
  have h1 : (QuotientGroup.mk (⟨y * r, N.mul_mem hyN hrN⟩ : ↥N) : ↥N ⧸ R.subgroupOf N) =
      QuotientGroup.mk ⟨y, hyN⟩ := by
    rw [QuotientGroup.eq, Subgroup.mem_subgroupOf]
    simpa using R.inv_mem hr
  have h2 : (QuotientGroup.mk (⟨y * r, N.mul_mem hyN hrN⟩ : ↥N) : ↥N ⧸ R.subgroupOf N) ^ 2 ^ k
      = 1 := by
    rw [h1, ← QuotientGroup.mk_pow]
    have : (⟨y, hyN⟩ : ↥N) ^ 2 ^ k = 1 := Subtype.ext (by simpa using hyk)
    rw [this]
    rfl
  rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf] at h2
  exact h2

theorem pCoreOf_normalizer_le_of_isAGMember [Finite G] {T D : Subgroup G} (hT : IsPGroup 2 T)
    (hD : IsAGMember T D) : pCoreOf 2 (Subgroup.normalizer (D : Set G)) ≤ D := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hDT, hD1, hsyl, hi, hCD, hRC, hRD⟩ := hD
  set N := Subgroup.normalizer (D : Set G) with hN
  set R := oddCoreIn N with hR
  have hRN : R ≤ N := oddCoreIn_le N
  have hNR : N ≤ Subgroup.normalizer (R : Set G) := le_normalizer_oddCoreIn N
  have hYN : pCoreOf 2 N ≤ N := pCoreOf_le 2 N
  have hNY : N ≤ Subgroup.normalizer (pCoreOf 2 N : Set G) := le_normalizer_pCoreOf 2 N
  have hQN : R ⊔ pCoreOf 2 N ≤ N := sup_le hRN hYN
  have hQnorm : ((R ⊔ pCoreOf 2 N).subgroupOf N).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hQN).mpr (le_normalizer_sup hNR hNY)
  have hQ := hi (R ⊔ pCoreOf 2 N) le_sup_left hQN hQnorm fun x hx =>
    exists_pow_mem_sup_pCoreOf hRN hNR hx
  intro y hy
  have hyRD : y ∈ ((R : Set G) * (D : Set G)) := by
    rw [← Subgroup.coe_mul_of_left_le_normalizer_right _ _ hRN]
    exact hQ (Subgroup.mem_sup_right hy)
  obtain ⟨r, hr, d, hd, rfl⟩ := hyRD
  have hcomm : Commute r d := (Subgroup.mem_centralizer_iff.mp (hRC hr) d hd).symm
  obtain ⟨k, hk⟩ := pCoreOf_isPGroup 2 N ⟨r * d, hy⟩
  obtain ⟨k', hk'⟩ := hT ⟨d, hDT hd⟩
  have hyk : (r * d) ^ 2 ^ k = 1 := congrArg Subtype.val hk
  have hdk : d ^ 2 ^ k' = 1 := congrArg Subtype.val hk'
  have hdK : d ^ 2 ^ (k + k') = 1 := by
    rw [add_comm, pow_add, pow_mul, hdk, one_pow]
  have hyK : (r * d) ^ 2 ^ (k + k') = 1 := by
    rw [pow_add, pow_mul, hyk, one_pow]
  have hr1 : r ^ 2 ^ (k + k') = 1 := by
    rw [hcomm.mul_pow, hdK, mul_one] at hyK
    exact hyK
  have hodd := odd_card_oddCoreIn N
  have hord : orderOf r ∣ 2 ^ (k + k') := orderOf_dvd_of_pow_eq_one hr1
  have hord' : orderOf r ∣ Nat.card R := Subgroup.orderOf_dvd_natCard R hr
  have hcop : Nat.Coprime (2 ^ (k + k')) (Nat.card R) :=
    Nat.Coprime.pow_left _ ((Nat.coprime_two_left).mpr hodd)
  have h1 : orderOf r = 1 := Nat.eq_one_of_dvd_coprimes hcop hord hord'
  have hr' : r = 1 := orderOf_eq_one_iff.mp h1
  subst hr'
  simpa using hd

end CFSG.Quasithin.H13.F431.AG
