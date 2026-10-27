module

public import CFSG.Quasithin.SteinbergCDRankOneLeviOddCyclic

public section

namespace CFSG.RankThree.PartOne.KFU

open Subgroup CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.Quasithin.SteinbergCD

theorem le_of_le_sup_of_isPGroup {G : Type*} [Group G] {N T P : Subgroup G}
    (hTN : T ≤ normalizer (N : Set G)) {r : ℕ} [Fact r.Prime] (hrT : ¬ r ∣ Nat.card T)
    (hPNT : P ≤ N ⊔ T) (hP : IsPGroup r P) : P ≤ N := by
  intro e he
  have hx : e ∈ ((N ⊔ T : Subgroup G) : Set G) := hPNT he
  rw [coe_mul_of_right_le_normalizer_left N T hTN] at hx
  obtain ⟨n, hn, t, ht, rfl⟩ := hx
  obtain ⟨k, hk⟩ := hP ⟨n * t, he⟩
  have hk' : (n * t) ^ (r ^ k) = 1 := congrArg Subtype.val hk
  have key : ∀ m : ℕ, ∃ n' ∈ N, (n * t) ^ m = n' * t ^ m := by
    intro m
    induction m with
    | zero => exact ⟨1, N.one_mem, by simp⟩
    | succ m ih =>
      obtain ⟨n', hn', hm⟩ := ih
      refine ⟨n' * (t ^ m * n * (t ^ m)⁻¹), N.mul_mem hn' ?_, ?_⟩
      · exact (mem_normalizer_iff.1 (hTN (T.pow_mem ht m)) n).1 hn
      · rw [pow_succ, hm, pow_succ]
        group
  obtain ⟨n', hn', hnp⟩ := key (r ^ k)
  have htm : t ^ (r ^ k) ∈ N := by
    have h1 : n' * t ^ (r ^ k) = 1 := by rw [← hnp]; exact hk'
    rw [eq_inv_of_mul_eq_one_right h1]
    exact N.inv_mem hn'
  have hT1 : t ^ Nat.card T = 1 :=
    congrArg Subtype.val (pow_card_eq_one' (G := T) (x := (⟨t, ht⟩ : T)))
  have hcop : Nat.Coprime (r ^ k) (Nat.card T) :=
    Nat.Coprime.pow_left k ((Nat.Prime.coprime_iff_not_dvd (Fact.out : r.Prime)).2 hrT)
  obtain ⟨a, b, hab⟩ := Nat.isCoprime_iff_coprime.2 hcop
  have htN : t ∈ N := by
    have e1 : t = (t ^ (r ^ k)) ^ a * (t ^ Nat.card T) ^ b := by
      calc t = t ^ (1 : ℤ) := (zpow_one t).symm
        _ = t ^ (a * ((r ^ k : ℕ) : ℤ) + b * (Nat.card T : ℤ)) := by rw [hab]
        _ = (t ^ (r ^ k)) ^ a * (t ^ Nat.card T) ^ b := by
          rw [zpow_add, mul_comm a, mul_comm b, zpow_mul, zpow_mul, zpow_natCast, zpow_natCast]
    rw [e1, hT1, one_zpow, mul_one]
    exact N.zpow_mem htm a
  exact N.mul_mem hn htN

theorem isCyclic_of_le_sup_of_coprime {G : Type*} [Group G] {X Q R T P : Subgroup G} [Finite T]
    (hX : X ≤ Q ⊔ R ⊔ T) (hRX : R ≤ X) (hTX : T ≤ X) (hXQ : X ≤ normalizer (Q : Set G))
    (hTR : T ≤ normalizer (R : Set G)) (hQ : IsPGroup 2 Q) (hQR : Q ⊓ R = ⊥) {r : ℕ}
    [Fact r.Prime] (hr2 : r ≠ 2) (hrT : ¬ r ∣ Nat.card T)
    (hRcyc : ∀ P' : Subgroup G, P' ≤ R → IsPGroup r P' → IsCyclic P') (hPX : P ≤ X)
    (hP : IsPGroup r P) : IsCyclic P := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hTN : T ≤ normalizer ((Q ⊔ R : Subgroup G) : Set G) := fun t ht =>
    inf_normalizer_le_normalizer_sup Q R ⟨hXQ (hTX ht), hTR ht⟩
  have hPN : P ≤ Q ⊔ R := le_of_le_sup_of_isPGroup hTN hrT (hPX.trans hX) hP
  have hPQ : P ⊓ Q = ⊥ := (IsPGroup.disjoint_of_ne r 2 hr2 P Q hP hQ).eq_bot
  obtain ⟨κ, hκ⟩ := exists_injective_of_le_sup (fun x hx => hXQ (hRX hx)) hQR hPN hPQ
  have hrange : IsPGroup r κ.range := hP.of_surjective κ.rangeRestrict κ.rangeRestrict_surjective
  have hP' : IsCyclic (κ.range.map R.subtype) := hRcyc _ (by
    rintro _ ⟨x, -, rfl⟩
    exact x.2) (hrange.map R.subtype)
  have e : P ≃* κ.range.map R.subtype :=
    (MonoidHom.ofInjective hκ).trans (κ.range.equivMapOfInjective R.subtype R.subtype_injective)
  exact isCyclic_of_surjective e.symm.toMonoidHom e.symm.surjective

theorem charP_two_of_card_eq_two_pow {K : Type} [Field K] [Finite K] {f : ℕ}
    (hK : Nat.card K = 2 ^ f) : CharP K 2 := by
  have : Fintype K := Fintype.ofFinite K
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact charP_of_card_eq_prime_pow (f := f) (by rw [← Nat.card_eq_fintype_card]; exact hK)

theorem not_isCyclic_of_pow_eq_one {G : Type*} [Group G] {p : ℕ} (hp : p.Prime)
    (hc : Nat.card G = p ^ 2) (h : ∀ g : G, g ^ p = 1) : ¬ IsCyclic G := by
  intro hcyc
  have h1 : Monoid.exponent G ∣ p := Monoid.exponent_dvd_of_forall_pow_eq_one h
  rw [IsCyclic.exponent_eq_card, hc] at h1
  have h2 : p * p ≤ p * 1 := by
    simpa only [sq, mul_one] using Nat.le_of_dvd hp.pos h1
  exact absurd (Nat.le_of_mul_le_mul_left h2 hp.pos) (by have := hp.two_le; omega)

theorem isCyclic_of_le_parabolic_singleton {τ : Tag} {K : Type} [Field K] [Finite K] [CharP K 2]
    (i : Fin τ.rank) {r : ℕ} [Fact r.Prime] (hr2 : r ≠ 2)
    (hrT : ¬ r ∣ Nat.card (torusGroup τ K)) {P : Subgroup (ModGL τ K)}
    (hP : P ≤ parabolicSubgroup τ K {i}) (hPr : IsPGroup r P) : IsCyclic P := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨ρ, -, -, -, -, hrange, hker, -, -⟩ := exceptional_ordinary_rank_one_central_image τ K i
  have hset : {g | ∃ j ∈ ({i} : Set (Fin τ.rank)), ∃ c : K,
      g = xUnit τ K j c ∨ g = yUnit τ K j c} =
        Set.range (xUnit τ K i) ∪ Set.range (yUnit τ K i) := by
    ext g
    simp only [Set.mem_singleton_iff, exists_eq_left, Set.mem_ofPred_eq, Set.mem_union,
      Set.mem_range]
    constructor
    · rintro ⟨c, rfl | rfl⟩
      · exact Or.inl ⟨c, rfl⟩
      · exact Or.inr ⟨c, rfl⟩
    · rintro (⟨c, rfl⟩ | ⟨c, rfl⟩)
      · exact ⟨c, Or.inl rfl⟩
      · exact ⟨c, Or.inr rfl⟩
  obtain ⟨hQP, hQn, -, hMP, hQM, hQMP, -, -, -, -, -, -, hfin⟩ :=
    parabolic_root_radical_Levi_factors τ K {i}
  have hRJ : Subgroup.closure {g | ∃ j ∈ ({i} : Set (Fin τ.rank)), ∃ c : K,
      g = xUnit τ K j c ∨ g = yUnit τ K j c} = ρ.range := by
    rw [hset, hrange]
  have hM : parabolicLevi τ K {i} = torusGroup τ K ⊔ ρ.range := by
    rw [← hRJ]
    rfl
  have hRM : ρ.range ≤ parabolicLevi τ K {i} := hM ▸ le_sup_right
  have hTM : torusGroup τ K ≤ parabolicLevi τ K {i} := hM ▸ le_sup_left
  have hTR : torusGroup τ K ≤ normalizer (ρ.range : Set (ModGL τ K)) := by
    rw [hrange, closure_xUnit_yUnit_eq]
    exact fun h hh => inf_normalizer_le_normalizer_sup _ _
      ⟨torusGroup_le_normalizer_rootSubgroup (isRoot_single τ i) hh,
        torusGroup_le_normalizer_rootSubgroup (isRoot_neg_single τ i) hh⟩
  have hXQ : parabolicSubgroup τ K {i} ≤
      normalizer (parabolicRadical τ K {i} : Set (ModGL τ K)) :=
    (normal_subgroupOf_iff_le_normalizer hQP).1 hQn
  have hX : parabolicSubgroup τ K {i} ≤
      (parabolicRadical τ K {i} ⊔ ρ.range) ⊔ torusGroup τ K := by
    rw [← hQMP, hM]
    exact sup_le (le_sup_left.trans le_sup_left)
      (sup_le le_sup_right (le_sup_right.trans le_sup_left))
  have : Finite (ModGL τ K) := CFSG.LieType.Chevalley.finite_modGL
  refine isCyclic_of_le_sup_of_coprime hX (hRM.trans hMP) (hTM.trans hMP) hXQ hTR (hfin 2).2.1
    ?_ hr2 hrT (fun P' h hP' => isCyclic_of_le_range_of_ker_scalar ρ
      (fun g hg => by obtain ⟨l, -, hl⟩ := hker g hg; exact ⟨l, hl⟩) hr2 h hP') hP hPr
  refine eq_bot_iff.2 fun g hg => ?_
  rw [← hQM]
  exact ⟨hg.1, hRM hg.2⟩

end CFSG.RankThree.PartOne.KFU
