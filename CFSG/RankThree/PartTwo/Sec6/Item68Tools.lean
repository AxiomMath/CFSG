module

public import CFSG.RankThree.PartTwo.Sec6.Item612Fitting
import CFSG.LocalAnalysis.RankThreeEvenClassification.HallContainment

public section

namespace CFSG.RankThree.PartTwo.Sec6

open CFSG CFSG.RankThreeEvenClassification.Helpers
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G]

theorem exists_pow_mem_mul_zpowers_cube (x : G) :
    ∃ n : ℕ, x⁻¹ * x ^ n ∈ Subgroup.zpowers (x ^ 3) ∧ ∃ k : ℕ, (x ^ n) ^ (3 ^ k) = 1 := by
  obtain ⟨a, m, hm3, hn⟩ :=
    Nat.exists_eq_pow_mul_and_not_dvd (orderOf_pos x).ne' 3 (by norm_num)
  have hmm : m * m % 3 = 1 := by
    have h1 : m % 3 = 1 ∨ m % 3 = 2 := by omega
    rcases h1 with h1 | h1 <;> simp [Nat.mul_mod, h1]
  refine ⟨m * m, ?_, a, ?_⟩
  · have hq : m * m = 3 * (m * m / 3) + 1 := by omega
    rw [hq, pow_succ' x (3 * (m * m / 3)), pow_mul, inv_mul_cancel_left]
    exact Subgroup.pow_mem _ (Subgroup.mem_zpowers _) _
  · rw [← pow_mul, show m * m * 3 ^ a = orderOf x * m by rw [hn]; ring, pow_mul,
      pow_orderOf_eq_one, one_pow]

theorem mem_of_mem_sup_of_pow_eq_one {p : ℕ} [hp : Fact p.Prime] {C K : Subgroup G}
    (hKC : K ≤ Subgroup.normalizer (C : Set G)) (hK : ¬ p ∣ Nat.card K) {x : G}
    (hx : x ∈ C ⊔ K) {k : ℕ} (hxk : x ^ (p ^ k) = 1) : x ∈ C := by
  have hxN : x ∈ Subgroup.normalizer (C : Set G) := sup_le Subgroup.le_normalizer hKC hx
  have hx' : x ∈ (C : Set G) * (K : Set G) := by
    rw [← Subgroup.coe_mul_of_right_le_normalizer_left C K hKC]
    exact hx
  obtain ⟨c, hc, w, hw, rfl⟩ := hx'
  have key : ∀ n : ℕ, w ^ n * ((c * w) ^ n)⁻¹ ∈ C := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      have hconj : (c * w) ^ n * c⁻¹ * ((c * w) ^ n)⁻¹ ∈ C :=
        (Subgroup.mem_normalizer_iff.mp (Subgroup.pow_mem _ hxN n) c⁻¹).mp (C.inv_mem hc)
      have e : w ^ (n + 1) * ((c * w) ^ (n + 1))⁻¹ =
          (w ^ n * ((c * w) ^ n)⁻¹) * ((c * w) ^ n * c⁻¹ * ((c * w) ^ n)⁻¹) := by
        rw [pow_succ, pow_succ, mul_inv_rev]
        group
      rw [e]
      exact C.mul_mem ih hconj
  have hwC : w ^ (p ^ k) ∈ C := by
    have := key (p ^ k)
    rwa [hxk, inv_one, mul_one] at this
  have hcop : (orderOf w).Coprime (p ^ k) := by
    have hdvd : orderOf w ∣ Nat.card K := Subgroup.orderOf_dvd_natCard K hw
    exact Nat.Coprime.pow_right k (Nat.Coprime.symm
      ((Nat.Prime.coprime_iff_not_dvd hp.out).mpr fun h => hK (h.trans hdvd)))
  have hwz : w ∈ Subgroup.zpowers (w ^ (p ^ k)) := by
    have hle : Subgroup.zpowers (w ^ (p ^ k)) ≤ Subgroup.zpowers w :=
      Subgroup.zpowers_le.mpr (Subgroup.pow_mem _ (Subgroup.mem_zpowers w) _)
    have heq : Subgroup.zpowers (w ^ (p ^ k)) = Subgroup.zpowers w :=
      Subgroup.eq_of_le_of_card_ge hle
        (by rw [Nat.card_zpowers, Nat.card_zpowers, hcop.orderOf_pow])
    rw [heq]
    exact Subgroup.mem_zpowers w
  exact C.mul_mem hc (Subgroup.zpowers_le.mpr hwC hwz)

omit [Finite G] in
theorem exists_pow_mem_of_mem_closure_sup {p : ℕ} {H N : Subgroup G} (hNH : N ≤ H)
    (hHN : H ≤ Subgroup.normalizer (N : Set G)) {S : Set G} (hSH : S ⊆ H)
    (hSp : ∀ s ∈ S, ∃ k : ℕ, s ^ (p ^ k) = 1)
    (hSc : ∀ s ∈ S, ∀ s' ∈ S, s * s' * s⁻¹ * s'⁻¹ ∈ N) {x : G}
    (hx : x ∈ Subgroup.closure S ⊔ N) : ∃ k : ℕ, x ^ (p ^ k) ∈ N := by
  have hn : (N.subgroupOf H).Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hNH).mpr hHN
  set ρ := QuotientGroup.mk' (N.subgroupOf H) with hρ
  set T : Set (H ⧸ N.subgroupOf H) := ρ '' {y : H | (y : G) ∈ S} with hT
  have hTc : T.Pairwise Commute := by
    rintro _ ⟨y, hy, rfl⟩ _ ⟨y', hy', rfl⟩ -
    rw [Commute, SemiconjBy, ← commutatorElement_eq_one_iff_mul_comm, ← map_commutatorElement,
      hρ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf,
      commutatorElement_def]
    simpa using hSc _ hy _ hy'
  have hTp : ∀ t ∈ T, ∃ k : ℕ, t ^ (p ^ k) = 1 := by
    rintro _ ⟨y, hy, rfl⟩
    obtain ⟨k, hk⟩ := hSp _ hy
    refine ⟨k, ?_⟩
    rw [← map_pow]
    have : y ^ (p ^ k) = 1 := Subtype.ext (by simpa using hk)
    rw [this, map_one]
  have hcomm := Subgroup.isMulCommutative_closure hTc
  have hcl : ∀ z ∈ Subgroup.closure T, ∃ k : ℕ, z ^ (p ^ k) = 1 := by
    intro z hz
    induction hz using Subgroup.closure_induction with
    | mem t ht => exact hTp t ht
    | one => exact ⟨0, one_pow _⟩
    | mul y z hy hz ihy ihz =>
      obtain ⟨a, ha⟩ := ihy
      obtain ⟨b, hb⟩ := ihz
      have hc : Commute y z := congrArg Subtype.val (hcomm.is_comm.comm ⟨y, hy⟩ ⟨z, hz⟩)
      have h1 : y ^ (p ^ (a + b)) = 1 := by rw [pow_add, pow_mul, ha, one_pow]
      have h2 : z ^ (p ^ (a + b)) = 1 := by rw [pow_add, mul_comm, pow_mul, hb, one_pow]
      exact ⟨a + b, by rw [hc.mul_pow, h1, h2, one_mul]⟩
    | inv y hy ih =>
      obtain ⟨a, ha⟩ := ih
      exact ⟨a, by rw [inv_pow, ha, inv_one]⟩
  have hle : Subgroup.closure S ⊔ N ≤ ((Subgroup.closure T).comap ρ).map H.subtype := by
    refine sup_le ((Subgroup.closure_le _).mpr fun s hs => ?_) fun n hn => ?_
    · exact ⟨⟨s, hSH hs⟩, Subgroup.subset_closure ⟨⟨s, hSH hs⟩, hs, rfl⟩, rfl⟩
    · refine ⟨⟨n, hNH hn⟩, ?_, rfl⟩
      rw [SetLike.mem_coe, Subgroup.mem_comap]
      have : ρ ⟨n, hNH hn⟩ = 1 := by
        rw [hρ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
        exact hn
      rw [this]
      exact one_mem _
  obtain ⟨y, hy, rfl⟩ := hle hx
  obtain ⟨k, hk⟩ := hcl _ hy
  refine ⟨k, ?_⟩
  rw [← map_pow, hρ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff,
    Subgroup.mem_subgroupOf] at hk
  simpa using hk

@[expose] def centralizerMod (H Θ O : Subgroup G) (hHΘ : H ≤ Subgroup.normalizer (Θ : Set G))
    (hHO : H ≤ Subgroup.normalizer (O : Set G)) : Subgroup G where
  carrier := {h | h ∈ H ∧ ∀ v ∈ Θ, h * v * h⁻¹ * v⁻¹ ∈ O}
  mul_mem' := by
    rintro z₁ z₂ ⟨h₁H, h₁⟩ ⟨h₂H, h₂⟩
    refine ⟨H.mul_mem h₁H h₂H, fun y hy => ?_⟩
    have e : z₁ * z₂ * y * (z₁ * z₂)⁻¹ * y⁻¹ =
        z₁ * (z₂ * y * z₂⁻¹ * y⁻¹) * z₁⁻¹ * (z₁ * y * z₁⁻¹ * y⁻¹) := by group
    rw [e]
    exact O.mul_mem ((Subgroup.mem_normalizer_iff.mp (hHO h₁H) _).mp (h₂ y hy)) (h₁ y hy)
  one_mem' := ⟨H.one_mem, fun y _ => by simp⟩
  inv_mem' := by
    rintro z ⟨hzH, hz⟩
    refine ⟨H.inv_mem hzH, fun y hy => ?_⟩
    have hy' : z⁻¹ * y * z⁻¹⁻¹ ∈ Θ :=
      (Subgroup.mem_normalizer_iff.mp (hHΘ (H.inv_mem hzH)) y).mp hy
    have h1 := O.inv_mem (hz _ hy')
    have e : (z * (z⁻¹ * y * z⁻¹⁻¹) * z⁻¹ * (z⁻¹ * y * z⁻¹⁻¹)⁻¹)⁻¹ =
        z⁻¹ * y * z⁻¹⁻¹ * y⁻¹ := by
      group
    rwa [e] at h1

omit [Finite G] in
theorem mem_centralizerMod {H Θ O : Subgroup G} {hHΘ : H ≤ Subgroup.normalizer (Θ : Set G)}
    {hHO : H ≤ Subgroup.normalizer (O : Set G)} {z : G} :
    z ∈ centralizerMod H Θ O hHΘ hHO ↔ z ∈ H ∧ ∀ v ∈ Θ, z * v * z⁻¹ * v⁻¹ ∈ O :=
  Iff.rfl

omit [Finite G] in
theorem le_normalizer_centralizerMod {H Θ O : Subgroup G}
    (hHΘ : H ≤ Subgroup.normalizer (Θ : Set G)) (hHO : H ≤ Subgroup.normalizer (O : Set G)) :
    H ≤ Subgroup.normalizer (centralizerMod H Θ O hHΘ hHO : Set G) := by
  refine le_normalizer_of_forall_conj_mem fun h hh z hz => ?_
  obtain ⟨hzH, hzc⟩ := mem_centralizerMod.mp hz
  refine mem_centralizerMod.mpr ⟨H.mul_mem (H.mul_mem hh hzH) (H.inv_mem hh), fun v hv => ?_⟩
  have hv' : h⁻¹ * v * h⁻¹⁻¹ ∈ Θ := (Subgroup.mem_normalizer_iff.mp (hHΘ (H.inv_mem hh)) v).mp hv
  have h1 := (Subgroup.mem_normalizer_iff.mp (hHO hh) _).mp (hzc _ hv')
  have e : h * (z * (h⁻¹ * v * h⁻¹⁻¹) * z⁻¹ * (h⁻¹ * v * h⁻¹⁻¹)⁻¹) * h⁻¹ =
      h * z * h⁻¹ * v * (h * z * h⁻¹)⁻¹ * v⁻¹ := by group
  rwa [e] at h1

theorem exists_invariant_isPGroup_lift {Θ O P E S : Subgroup G}
    (hΘsol : Group.IsSolvable Θ) (hΘ3 : ¬ 3 ∣ Nat.card Θ) (hO : Odd (Nat.card O))
    (hΘP : Θ ≤ P) (hPΘ : P ≤ Subgroup.normalizer (Θ : Set G))
    (hP3 : ∀ x ∈ P, ∃ k : ℕ, x ^ (3 ^ k) ∈ Θ)
    (hE : IsPGroup 3 E) (hS : IsPGroup 2 S) (hES : E ≤ Subgroup.normalizer (S : Set G))
    (hESP : E ⊔ S ≤ Subgroup.normalizer (P : Set G))
    (hESΘ : E ⊔ S ≤ Subgroup.normalizer (Θ : Set G))
    (hPO : ∀ x ∈ P, (∃ k : ℕ, x ^ (3 ^ k) = 1) → ∀ v ∈ Θ, x * v * x⁻¹ * v⁻¹ ∈ O) :
    ∃ R : Subgroup G, IsPGroup 3 R ∧ E ⊔ S ≤ Subgroup.normalizer (R : Set G) ∧
      ∀ x ∈ P, ∃ r ∈ R, r⁻¹ * x ∈ Θ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set ES := E ⊔ S with hESdef
  set M := P ⊔ ES with hM
  have hPM : P ≤ M := le_sup_left
  have hESM : ES ≤ M := le_sup_right
  have hΘM : Θ ≤ M := hΘP.trans hPM
  have hMP : M ≤ Subgroup.normalizer (P : Set G) := sup_le Subgroup.le_normalizer hESP
  have hMΘ : M ≤ Subgroup.normalizer (Θ : Set G) := sup_le hPΘ hESΘ
  have hPsol : Group.IsSolvable P := by
    have hn : (Θ.subgroupOf P).Normal :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer hΘP).mpr hPΘ
    have hq3 : IsPGroup 3 (P ⧸ Θ.subgroupOf P) := by
      intro g
      induction g using QuotientGroup.induction_on with
      | H x =>
        obtain ⟨k, hk⟩ := hP3 x x.2
        refine ⟨k, ?_⟩
        rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
        simpa using hk
    have : Group.IsNilpotent (P ⧸ Θ.subgroupOf P) := hq3.isNilpotent
    have := hΘsol
    refine Group.isSolvable_of_ker_le_range (Subgroup.inclusion hΘP)
      (QuotientGroup.mk' (Θ.subgroupOf P)) ?_
    intro x hx
    rw [QuotientGroup.ker_mk'] at hx
    exact ⟨⟨x, Subgroup.mem_subgroupOf.mp hx⟩, rfl⟩
  have hESsol : Group.IsSolvable ES := by
    have : Group.IsNilpotent S := hS.isNilpotent
    have : Group.IsNilpotent E := hE.isNilpotent
    have h1 := isSolvable_sup_of_le_normalizer hES inferInstance inferInstance
    rwa [sup_comm] at h1
  have hMsol : Group.IsSolvable M := isSolvable_sup_of_le_normalizer hESP hPsol hESsol
  set π : Set ℕ := {2, 3} with hπ
  have h2π : 2 ∈ π := by rw [hπ]; exact Set.mem_insert 2 _
  have h3π : 3 ∈ π := by rw [hπ]; simp
  have hESπ : PrimeSetOrder π (Nat.card (ES.subgroupOf M)) := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hESM).toEquiv, hESdef, sup_comm]
    exact normalized_sup_primeSetOrder π S E hES (primeSetOrder_of_isPGroup h2π hS)
      (primeSetOrder_of_isPGroup h3π hE)
  have := hMsol
  obtain ⟨Hl, hHl, hESHl⟩ := hall_containment_of_solvable π (ES.subgroupOf M) hESπ
  set θM := Θ.subgroupOf M with hθMdef
  have hθMn : θM.Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hΘM).mpr hMΘ
  set PM := P.subgroupOf M with hPMdef
  have hPMn : PM.Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hPM).mpr hMP
  set ESM := ES.subgroupOf M with hESMdef
  have hθMPM : θM ≤ PM := fun y hy =>
    Subgroup.mem_subgroupOf.mpr (hΘP (Subgroup.mem_subgroupOf.mp hy))
  set ρ := QuotientGroup.mk' θM with hρ
  have hPMρ : IsPGroup 3 (PM.map ρ) := by
    rintro ⟨_, y, hy, rfl⟩
    obtain ⟨k, hk⟩ := hP3 _ (Subgroup.mem_subgroupOf.mp hy)
    refine ⟨k, Subtype.ext ?_⟩
    rw [SubgroupClass.coe_pow, OneMemClass.coe_one, ← map_pow, hρ, QuotientGroup.mk'_apply,
      QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
    simpa using hk
  have hsupPE : PM ⊔ ESM = ⊤ := by
    apply Subgroup.map_injective M.subtype_injective
    rw [Subgroup.map_sup, Subgroup.map_subgroupOf_eq_of_le hPM,
      Subgroup.map_subgroupOf_eq_of_le hESM, ← MonoidHom.range_eq_map, Subgroup.range_subtype]
  have hθMπ : PrimeSetOrder π θM.index := by
    have htop : PM.map ρ ⊔ ESM.map ρ = ⊤ := by
      rw [← Subgroup.map_sup, hsupPE, ← MonoidHom.range_eq_map, MonoidHom.range_eq_top]
      exact QuotientGroup.mk'_surjective θM
    have h1 : PrimeSetOrder π (Nat.card (PM.map ρ ⊔ ESM.map ρ : Subgroup (M ⧸ θM))) := by
      refine normalized_sup_primeSetOrder π _ _ ?_ ?_ ?_
      · have : (PM.map ρ).Normal := hPMn.map ρ (QuotientGroup.mk'_surjective θM)
        rw [Subgroup.normalizer_eq_top (PM.map ρ)]
        exact le_top
      · obtain ⟨j, hj⟩ := hPMρ.exists_card_eq
        rw [hj]
        exact PrimeSetOrder.prime_pow π 3 Nat.prime_three h3π j
      · exact PrimeSetOrder.of_dvd π _ _ hESπ (Subgroup.card_map_dvd ESM ρ)
    rw [htop, Subgroup.card_top] at h1
    exact h1
  have hsup : Hl ⊔ θM = ⊤ := by
    have h1 : (Hl ⊔ θM).index ∣ Hl.index := Subgroup.index_dvd_of_le le_sup_left
    have h2 : (Hl ⊔ θM).index ∣ θM.index := Subgroup.index_dvd_of_le le_sup_right
    have hcop : Nat.Coprime θM.index Hl.index := PrimeSetOrder.coprime_compl π _ _ hθMπ hHl.2
    exact Subgroup.index_eq_one.mp (Nat.eq_one_of_dvd_coprimes hcop h2 h1)
  set R0 := Hl ⊓ PM with hR0
  set N0 := Hl ⊓ θM with hN0
  have hN0R0 : N0 ≤ R0 := inf_le_inf_left Hl hθMPM
  have hR0N : R0 ≤ Subgroup.normalizer (N0 : Set M) :=
    (le_inf (inf_le_left.trans Subgroup.le_normalizer)
      (by rw [Subgroup.normalizer_eq_top θM]; exact le_top)).trans
      Subgroup.inf_normalizer_le_normalizer_inf
  have hN02 : IsPGroup 2 N0 := by
    have hπN : PrimeSetOrder π (Nat.card N0) :=
      PrimeSetOrder.of_dvd π _ _ hHl.1 (Subgroup.card_dvd_of_le inf_le_left)
    have h3N : ¬ 3 ∣ Nat.card N0 := fun h => hΘ3 (h.trans ((Subgroup.card_dvd_of_le
      inf_le_right).trans (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hΘM).toEquiv).dvd))
    refine IsPGroup.of_card (Nat.eq_prime_pow_of_unique_prime_dvd Nat.card_pos.ne' ?_)
    intro d hd hdN
    have hdπ := hπN d hd hdN
    simp only [hπ, Set.mem_insert_iff, Set.mem_singleton_iff] at hdπ
    rcases hdπ with h | h
    · exact h
    · exact absurd (h ▸ hdN) h3N
  set N0' := N0.subgroupOf R0 with hN0'
  have hN0'n : N0'.Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hN0R0).mpr hR0N
  have hq3 : IsPGroup 3 (R0 ⧸ N0') := by
    intro g
    induction g using QuotientGroup.induction_on with
    | H y =>
      have hyH : (y : M) ∈ Hl := y.2.1
      have hyP : ((y : M) : G) ∈ P := Subgroup.mem_subgroupOf.mp y.2.2
      obtain ⟨k, hk⟩ := hP3 _ hyP
      refine ⟨k, ?_⟩
      rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf,
        Subgroup.mem_inf]
      refine ⟨?_, ?_⟩
      · simpa using Hl.pow_mem hyH (3 ^ k)
      · rw [Subgroup.mem_subgroupOf]
        simpa using hk
  obtain ⟨j, hj⟩ := hq3.exists_card_eq
  obtain ⟨i, hi⟩ := hN02.exists_card_eq
  have hN0'card : Nat.card N0' = 2 ^ i := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hN0R0).toEquiv, hi]
  have hN0'2 : IsPGroup 2 N0' := IsPGroup.of_card hN0'card
  have hindex : N0'.index = 3 ^ j := hj
  have hcop : Nat.Coprime (Nat.card N0') N0'.index := by
    rw [hN0'card, hindex]
    exact Nat.Coprime.pow i j (by norm_num)
  obtain ⟨Q, hQ⟩ := Subgroup.exists_right_complement'_of_coprime hcop
  have hQcard : Nat.card Q = 3 ^ j := by rw [← hQ.symm.index_eq_card, hindex]
  have hQ3 : IsPGroup 3 Q := IsPGroup.of_card hQcard
  have hQN : ∀ q ∈ Q, ∀ s ∈ N0', q * s * q⁻¹ * s⁻¹ = 1 := by
    intro q hq s hs
    have hyN : q * s * q⁻¹ * s⁻¹ ∈ N0' := N0'.mul_mem (hN0'n.conj_mem s hs q) (N0'.inv_mem hs)
    have hqP : ((q : M) : G) ∈ P := Subgroup.mem_subgroupOf.mp q.2.2
    have hq3e : ∃ k : ℕ, ((q : M) : G) ^ (3 ^ k) = 1 := by
      obtain ⟨k, hk⟩ := hQ3 ⟨q, hq⟩
      refine ⟨k, ?_⟩
      have : q ^ (3 ^ k) = 1 := congrArg Subtype.val hk
      simpa using congrArg (fun y : R0 => ((y : M) : G)) this
    have hsΘ : ((s : M) : G) ∈ Θ :=
      Subgroup.mem_subgroupOf.mp (Subgroup.mem_subgroupOf.mp hs).2
    have hO' := hPO _ hqP hq3e _ hsΘ
    obtain ⟨m, hm⟩ := hN0'2 ⟨_, hyN⟩
    have h1 : orderOf (q * s * q⁻¹ * s⁻¹) ∣ 2 ^ m := by
      have := orderOf_dvd_of_pow_eq_one hm
      rwa [Subgroup.orderOf_mk] at this
    have h2 : orderOf (q * s * q⁻¹ * s⁻¹) ∣ Nat.card O := by
      have := Subgroup.orderOf_dvd_natCard O hO'
      rwa [show ((q : M) : G) * ((s : M) : G) * ((q : M) : G)⁻¹ * ((s : M) : G)⁻¹ =
        (((q * s * q⁻¹ * s⁻¹ : R0) : M) : G) by simp, Subgroup.orderOf_coe,
        Subgroup.orderOf_coe] at this
    exact orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes
      (Nat.Coprime.pow_left m (Nat.coprime_two_left.mpr hO)) h1 h2)
  have hdecomp : ∀ y : R0, ∃ q ∈ Q, ∃ n ∈ N0', q * n = y := by
    intro y
    have hy : y ∈ Q ⊔ N0' := by rw [sup_comm, hQ.sup_eq_top]; exact Subgroup.mem_top y
    exact Subgroup.mem_sup_of_normal_right.mp hy
  have hQ3elt : ∀ y : R0, (∃ k : ℕ, y ^ (3 ^ k) = 1) → y ∈ Q := by
    rintro y ⟨k, hk⟩
    obtain ⟨q, hq, n, hn, rfl⟩ := hdecomp y
    have hqn : Commute q n := by
      have h := hQN q hq n hn
      calc q * n = q * n * q⁻¹ * n⁻¹ * (n * q) := by group
        _ = n * q := by rw [h, one_mul]
    have hq1 : q ^ (3 ^ j) = 1 := by
      have := pow_card_eq_one' (x := (⟨q, hq⟩ : Q))
      rw [hQcard] at this
      exact congrArg Subtype.val this
    have hn1 : n ^ (3 ^ (k + j)) = 1 := by
      have h1 : (q * n) ^ (3 ^ (k + j)) = 1 := by rw [pow_add, pow_mul, hk, one_pow]
      have h2 : q ^ (3 ^ (k + j)) = 1 := by rw [pow_add, mul_comm, pow_mul, hq1, one_pow]
      rwa [hqn.mul_pow, h2, one_mul] at h1
    obtain ⟨m, hm⟩ := hN0'2 ⟨n, hn⟩
    have h1 : orderOf n ∣ 2 ^ m := by
      have := orderOf_dvd_of_pow_eq_one hm
      rwa [Subgroup.orderOf_mk] at this
    have h2 : orderOf n ∣ 3 ^ (k + j) := orderOf_dvd_of_pow_eq_one hn1
    have hn' : n = 1 := orderOf_eq_one_iff.mp
      (Nat.eq_one_of_dvd_coprimes (Nat.Coprime.pow m (k + j) (by norm_num)) h1 h2)
    rw [hn', mul_one]
    exact hq
  have hHlQ : ∀ h ∈ Hl, ∀ y : R0, y ∈ Q →
      ∃ y' : R0, y' ∈ Q ∧ (y' : M) = h * (y : M) * h⁻¹ := by
    intro h hh y hy
    have hmem : h * (y : M) * h⁻¹ ∈ R0 :=
      ⟨Hl.mul_mem (Hl.mul_mem hh y.2.1) (Hl.inv_mem hh), hPMn.conj_mem _ y.2.2 h⟩
    refine ⟨⟨_, hmem⟩, hQ3elt _ ?_, rfl⟩
    obtain ⟨k, hk⟩ := hQ3 ⟨y, hy⟩
    refine ⟨k, Subtype.ext ?_⟩
    have hy1 : (y : M) ^ (3 ^ k) = 1 := by
      have : y ^ (3 ^ k) = 1 := congrArg Subtype.val hk
      simpa using congrArg (fun z : R0 => (z : M)) this
    rw [SubgroupClass.coe_pow, OneMemClass.coe_one]
    show (h * (y : M) * h⁻¹) ^ (3 ^ k) = 1
    rw [conj_pow, hy1, mul_one, mul_inv_cancel]
  refine ⟨(Q.map R0.subtype).map M.subtype, (hQ3.map _).map _, ?_, ?_⟩
  · refine le_normalizer_of_forall_conj_mem fun a ha x hx => ?_
    obtain ⟨_, ⟨y, hy, rfl⟩, rfl⟩ := hx
    have haHl : (⟨a, hESM ha⟩ : M) ∈ Hl := hESHl (Subgroup.mem_subgroupOf.mpr ha)
    obtain ⟨y', hy', hy'eq⟩ := hHlQ _ haHl y hy
    refine ⟨(y' : M), ⟨y', hy', rfl⟩, ?_⟩
    simp only [Subgroup.coe_subtype]
    rw [hy'eq]
    simp
  · intro x hx
    set x' : M := ⟨x, hPM hx⟩ with hx'
    have hx'top : x' ∈ Hl ⊔ θM := hsup ▸ Subgroup.mem_top x'
    obtain ⟨h, hh, w, hw, hhw⟩ := Subgroup.mem_sup_of_normal_right.mp hx'top
    have hhR0 : h ∈ R0 := by
      refine ⟨hh, ?_⟩
      have : h = x' * w⁻¹ := by rw [← hhw]; group
      rw [this]
      exact PM.mul_mem (Subgroup.mem_subgroupOf.mpr hx) (PM.inv_mem (hθMPM hw))
    obtain ⟨q, hq, n, hn, hqn⟩ := hdecomp ⟨h, hhR0⟩
    refine ⟨((q : M) : G), ⟨(q : M), ⟨q, hq, rfl⟩, rfl⟩, ?_⟩
    have hnθ : ((n : M) : G) ∈ Θ :=
      Subgroup.mem_subgroupOf.mp (Subgroup.mem_subgroupOf.mp hn).2
    have hwθ : (w : G) ∈ Θ := Subgroup.mem_subgroupOf.mp hw
    have hqn' : (q : M) * (n : M) = h := congrArg Subtype.val hqn
    have e : ((q : M) : G)⁻¹ * x = ((n : M) : G) * (w : G) := by
      have h1 : (x : G) = ((q : M) : G) * ((n : M) : G) * (w : G) := by
        have := congrArg Subtype.val hhw
        rw [← hqn'] at this
        simpa [hx'] using this.symm
      rw [h1]
      group
    rw [e]
    exact Θ.mul_mem hnθ hwθ

end CFSG.RankThree.PartTwo.Sec6
