module

public import CFSG.RankThree.PartOne.KF.R1Final
public import CFSG.RankThree.PartOne.KF.SUSylow

public section

namespace CFSG.RankThree.PartOne

open CFSG CFSG.RankThree.PartOne.KFU CFSG.Assembly.LowTwoRank CFSG.LieType.Universal.Unitary
  CFSG.LieType.BorelTits

variable {G : Type} [Group G]

@[expose] noncomputable def suQ {K : Type} [Field K] [Finite K] [CharP K 2] {f : ℕ} (n : ℕ)
    (hK : Nat.card K = (2 ^ f) ^ 2) :
    ↥(SU (unitaryInvolution K 2 f) n) →* StatedProj (StatedSU n (2 ^ f) K) :=
  (QuotientGroup.mk' ((StatedScalars (Fin n) K).subgroupOf (StatedSU n (2 ^ f) K))).comp
    (equivStatedSU hK n).toMonoidHom

theorem isCentralPQuot_suQ {K : Type} [Field K] [Finite K] [CharP K 2] {f : ℕ} {n p : ℕ}
    (hp : p.Prime)
    (hp2 : p ≠ 2) (hn1 : 1 ≤ n) (hpq : p ∣ 2 ^ f - 1) (hf1 : 1 ≤ f)
    (hK : Nat.card K = (2 ^ f) ^ 2) : IsCentralPQuot p (suQ n hK) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let ψ₀ : SU (unitaryInvolution K 2 f) n ≃* StatedSU n (2 ^ f) K := equivStatedSU hK n
  let N : Subgroup ↥(StatedSU n (2 ^ f) K) :=
    (StatedScalars (Fin n) K).subgroupOf (StatedSU n (2 ^ f) K)
  have hker : (suQ n hK).ker =
      N.comap (ψ₀ : ↥(SU (unitaryInvolution K 2 f) n) →* ↥(StatedSU n (2 ^ f) K)) := by
    ext x
    rw [MonoidHom.mem_ker, Subgroup.mem_comap]
    exact QuotientGroup.eq_one_iff _
  refine ⟨(QuotientGroup.mk'_surjective N).comp ψ₀.surjective, ?_, ?_⟩
  · intro x hx
    rw [hker] at hx
    have hxN : ((ψ₀ x : ↥(StatedSU n (2 ^ f) K)) : GL (Fin n) K) ∈
        Subgroup.center (GL (Fin n) K) := by
      rw [← statedScalars_eq_center]
      exact Subgroup.mem_subgroupOf.mp hx
    rw [Subgroup.mem_center_iff]
    intro z
    apply ψ₀.injective
    rw [map_mul, map_mul]
    apply Subtype.ext
    exact Subgroup.mem_center_iff.mp hxN ((ψ₀ z : ↥(StatedSU n (2 ^ f) K)) : GL (Fin n) K)
  · rw [hker, Subgroup.comap_equiv_eq_map_symm,
      Subgroup.card_map_of_injective (MulEquiv.injective _),
      (CFSG.LinearGroups.unitary_scalar_kernel Nat.prime_two hK hn1).2.2]
    refine (Nat.Prime.coprime_iff_not_dvd hp).mpr fun hd => ?_
    have h1 : p ∣ 2 ^ f + 1 := hd.trans (Nat.gcd_dvd_right _ _)
    have hq2 : 2 ≤ 2 ^ f := by
      calc 2 = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf1
    exact not_dvd_add_one_of_dvd_sub_one hp hp2 (by omega) hpq h1

theorem exists_runitary_frame_of [Finite G] {n : ℕ} [NeZero n] (hn : n = 4 ∨ n = 5) (hc : D8Comb n)
    {p : ℕ} {L A₀ F : Subgroup G} (h : Table123Core p L A₀ F) {f : ℕ} (hf1 : 1 ≤ f)
    (hpq : p ∣ 2 ^ f - 1) (hmod : StatedClassicalModel (L ⧸ Subgroup.center L) .PSU n 2 f) :
    ∃ (K : Type) (_ : Field K) (_ : Finite K) (_ : CharP K 2) (hK : Nat.card K = (2 ^ f) ^ 2),
      (∃ ζ : Kˣ, IsPrimitiveRoot ζ p) ∧
      ∃ ε : ↥L →* StatedProj (StatedSU n (2 ^ f) K), IsCentralPQuot p ε ∧
        (∀ t ∈ (d8Tor p K n).subgroupOf (SU (unitaryInvolution K 2 f) n), ∃ x : F,
          ε (Subgroup.inclusion h.F_le x) = suQ n hK t) ∧
        ∀ x : F, ∃ t ∈ (d8Tor p K n).subgroupOf (SU (unitaryInvolution K 2 f) n),
          ε (Subgroup.inclusion h.F_le x) = suQ n hK t := by
  classical
  obtain ⟨-, K, hKf, hKfin, hK, ⟨e⟩⟩ := hmod
  have hp := h.prime
  have h5 := h.five_le
  have hp2 : p ≠ 2 := by omega
  have : Fact p.Prime := ⟨hp⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hchar : CharP K 2 := by
    have := Fintype.ofFinite K
    refine charP_of_card_eq_prime_pow (p := 2) (f := 2 * f) ?_
    rw [Fintype.card_eq_nat_card, hK, ← pow_mul, mul_comm]
  have hn1 : 1 ≤ n := by rcases hn with rfl | rfl <;> norm_num
  have hζ : ∃ ζ : Kˣ, IsPrimitiveRoot ζ p := by
    have hdvd : p ∣ Nat.card Kˣ := by
      rw [Nat.card_units, hK]
      have h1 : 2 ^ f - 1 ∣ (2 ^ f) ^ 2 - 1 := by
        have : (2 ^ f) ^ 2 - 1 = (2 ^ f - 1) * (2 ^ f + 1) := by
          have hq2 : 1 ≤ 2 ^ f := Nat.one_le_two_pow
          zify [Nat.one_le_pow 2 (2 ^ f) (by omega), hq2]
          ring
        rw [this]
        exact dvd_mul_right _ _
      exact hpq.trans h1
    obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' p hdvd
    refine ⟨z, ?_⟩
    have := IsPrimitiveRoot.orderOf z
    rwa [hz] at this
  have hcop : Nat.Coprime p (Nat.card (Subgroup.center ↥L)) :=
    (Nat.Prime.coprime_iff_not_dvd hp).mpr h.center_pPrime
  have hε₀ := isCentralPQuot_center e hcop
  have hq : IsCentralPQuot p (suQ n hK) := isCentralPQuot_suQ hp hp2 hn1 hpq hf1 hK
  have hTexp : ∀ t ∈ (d8Tor p K n).subgroupOf (SU (unitaryInvolution K 2 f) n), t ^ p = 1 := by
    intro t ht
    obtain ⟨v, hv⟩ := Subgroup.mem_subgroupOf.mp ht
    apply Subtype.ext
    show ((t : ↥(SU (unitaryInvolution K 2 f) n)) : GL (Fin n) K) ^ p = 1
    rw [← hv]
    show diagU (d8Vec n v) ^ p = 1
    rw [diagU_pow, d8Vec_pow_eq_one, diagU_one]
  have hTcomm : ∀ s ∈ (d8Tor p K n).subgroupOf (SU (unitaryInvolution K 2 f) n),
      ∀ t ∈ (d8Tor p K n).subgroupOf (SU (unitaryInvolution K 2 f) n), s * t = t * s := by
    intro s hs t ht
    obtain ⟨v, hv⟩ := Subgroup.mem_subgroupOf.mp hs
    obtain ⟨w, hw⟩ := Subgroup.mem_subgroupOf.mp ht
    apply Subtype.ext
    show ((s : ↥(SU (unitaryInvolution K 2 f) n)) : GL (Fin n) K) * (t : GL (Fin n) K) =
      (t : GL (Fin n) K) * (s : GL (Fin n) K)
    rw [← hv, ← hw]
    show diagU (d8Vec n v) * diagU (d8Vec n w) = diagU (d8Vec n w) * diagU (d8Vec n v)
    rw [diagU_mul, diagU_mul, mul_comm]
  obtain ⟨ε, hε, hFT₁, hFT₂⟩ := exists_toral_quot (suQ n hK) hq _ hε₀ hTexp hTcomm
    (fun X hexp _ => exists_conj_into_d8Tor_su hn hc hK hp hp2 hpq X hexp) h.F_le h.F_exp
    h.F_comm h.maximal
  exact ⟨K, hKf, hKfin, hchar, hK, hζ, ε, hε, hFT₁, hFT₂⟩

theorem exists_runitary_frame [Finite G] {n : ℕ} [NeZero n] (hn : n = 4 ∨ n = 5) (hc : D8Comb n)
    {p : ℕ} {L A₀ F : Subgroup G} (h : Table123Core p L A₀ F)
    (hmodel : ∃ f : ℕ, 1 ≤ f ∧ p ∣ 2 ^ f - 1 ∧
      StatedClassicalModel (L ⧸ Subgroup.center L) .PSU n 2 f) :
    ∃ (f : ℕ) (K : Type) (_ : Field K) (_ : Finite K) (_ : CharP K 2)
      (hK : Nat.card K = (2 ^ f) ^ 2),
      1 ≤ f ∧ p ∣ 2 ^ f - 1 ∧ (∃ ζ : Kˣ, IsPrimitiveRoot ζ p) ∧
      ∃ ε : ↥L →* StatedProj (StatedSU n (2 ^ f) K), IsCentralPQuot p ε ∧
        (∀ t ∈ (d8Tor p K n).subgroupOf (SU (unitaryInvolution K 2 f) n), ∃ x : F,
          ε (Subgroup.inclusion h.F_le x) = suQ n hK t) ∧
        ∀ x : F, ∃ t ∈ (d8Tor p K n).subgroupOf (SU (unitaryInvolution K 2 f) n),
          ε (Subgroup.inclusion h.F_le x) = suQ n hK t := by
  obtain ⟨f, hf1, hpq, hmod⟩ := hmodel
  obtain ⟨K, hKf, hKfin, hchar, hK, hζ, ε, hε, hFT₁, hFT₂⟩ :=
    exists_runitary_frame_of hn hc h hf1 hpq hmod
  exact ⟨f, K, hKf, hKfin, hchar, hK, hf1, hpq, hζ, ε, hε, hFT₁, hFT₂⟩

theorem exists_runitary_ctx [Finite G] {n : ℕ} [NeZero n] (hn : n = 4 ∨ n = 5) (hc : D8Comb n)
    (hc2 : D8Comb2 hc) {p : ℕ} {L A₀ F : Subgroup G} (h : Table123Generic p L A₀ F)
    (hmodel : ∃ f : ℕ, 1 ≤ f ∧ p ∣ 2 ^ f - 1 ∧
      StatedClassicalModel (L ⧸ Subgroup.center L) .PSU n 2 f) :
    ∃ (K : Type) (_ : Field K) (_ : Finite K), (∃ ζ : Kˣ, IsPrimitiveRoot ζ p) ∧
      Nonempty (D8Ctx p K L F) := by
  classical
  obtain ⟨f, hf1, hpq, -, K, hKf, hKfin, hK, ⟨e⟩⟩ := hmodel
  have hp := h.prime
  have h5 := h.five_le
  have hp2 : p ≠ 2 := by omega
  have : Fact p.Prime := ⟨hp⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hchar : CharP K 2 := by
    have := Fintype.ofFinite K
    refine charP_of_card_eq_prime_pow (p := 2) (f := 2 * f) ?_
    rw [Fintype.card_eq_nat_card, hK, ← pow_mul, mul_comm]
  have hn1 : 1 ≤ n := by rcases hn with rfl | rfl <;> norm_num
  have hq2 : 2 ≤ 2 ^ f := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf1
  set σ : K ≃+* K := unitaryInvolution K 2 f with hσdef
  have hσ : ∀ c : K, σ c = c ^ 2 ^ f := fun c => unitaryInvolution_apply K 2 f c
  have hζ : ∃ ζ : Kˣ, IsPrimitiveRoot ζ p := by
    have hdvd : p ∣ Nat.card Kˣ := by
      rw [Nat.card_units, hK]
      have h1 : 2 ^ f - 1 ∣ (2 ^ f) ^ 2 - 1 := by
        have : (2 ^ f) ^ 2 - 1 = (2 ^ f - 1) * (2 ^ f + 1) := by
          zify [Nat.one_le_pow 2 (2 ^ f) (by omega), (by omega : 1 ≤ 2 ^ f)]
          ring
        rw [this]
        exact dvd_mul_right _ _
      exact hpq.trans h1
    obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' p hdvd
    refine ⟨z, ?_⟩
    have := IsPrimitiveRoot.orderOf z
    rwa [hz] at this
  have hσfix : ∀ u : rootsOfUnity p K, σ ((u : Kˣ) : K) = (u : Kˣ) := by
    intro u
    have h1 : (u : Kˣ) ^ p = 1 := (mem_rootsOfUnity p _).mp u.2
    have h2 : (u : Kˣ) ^ (2 ^ f - 1) = 1 := by
      obtain ⟨k, hk⟩ := hpq
      rw [hk, pow_mul, h1, one_pow]
    rw [hσ, ← Units.val_pow_eq_pow_val]
    have : (u : Kˣ) ^ 2 ^ f = (u : Kˣ) := by
      calc (u : Kˣ) ^ 2 ^ f = (u : Kˣ) ^ (2 ^ f - 1) * (u : Kˣ) := by
            rw [← pow_succ, Nat.sub_add_cancel (by omega)]
        _ = (u : Kˣ) := by rw [h2, one_mul]
    rw [this]
  have hT : ∀ v : D8Mod p K, (diagU (d8Vec n v) : GL (Fin n) K) ∈ SU σ n :=
    fun v => d8Vec_mem_SU hn hc σ hσfix v
  have hP : ∀ τ : Equiv.Perm (Fin n), (∀ i, τ (Fin.rev i) = Fin.rev (τ i)) →
      (permGL τ : GL (Fin n) K) ∈ SU σ n := fun τ hτ => permGL_mem_SU σ τ hτ
  obtain ⟨SM⟩ := exists_d8ctx hc hc2 hp hp2 hζ (SU σ n) hT hP
  have hcop : Nat.Coprime p (Nat.card (Subgroup.center ↥L)) :=
    (Nat.Prime.coprime_iff_not_dvd hp).mpr h.center_pPrime
  have hε₀ := isCentralPQuot_center e hcop
  let ψ₀ : SU σ n ≃* StatedSU n (2 ^ f) K := equivStatedSU hK n
  let N : Subgroup ↥(StatedSU n (2 ^ f) K) :=
    (StatedScalars (Fin n) K).subgroupOf (StatedSU n (2 ^ f) K)
  let q : ↥(SU σ n) →* StatedProj (StatedSU n (2 ^ f) K) :=
    (QuotientGroup.mk' N).comp ψ₀.toMonoidHom
  have hker : q.ker = N.comap (ψ₀ : ↥(SU σ n) →* ↥(StatedSU n (2 ^ f) K)) := by
    ext x
    rw [MonoidHom.mem_ker, Subgroup.mem_comap]
    exact QuotientGroup.eq_one_iff _
  have hq : IsCentralPQuot p q := by
    refine ⟨(QuotientGroup.mk'_surjective N).comp ψ₀.surjective, ?_, ?_⟩
    · intro x hx
      rw [hker] at hx
      have hxN : ((ψ₀ x : ↥(StatedSU n (2 ^ f) K)) : GL (Fin n) K) ∈
          Subgroup.center (GL (Fin n) K) := by
        rw [← statedScalars_eq_center]
        exact Subgroup.mem_subgroupOf.mp hx
      rw [Subgroup.mem_center_iff]
      intro z
      apply ψ₀.injective
      rw [map_mul, map_mul]
      apply Subtype.ext
      exact Subgroup.mem_center_iff.mp hxN ((ψ₀ z : ↥(StatedSU n (2 ^ f) K)) :
        GL (Fin n) K)
    · rw [hker, Subgroup.comap_equiv_eq_map_symm,
        Subgroup.card_map_of_injective (MulEquiv.injective _),
        (CFSG.LinearGroups.unitary_scalar_kernel Nat.prime_two hK hn1).2.2]
      refine (Nat.Prime.coprime_iff_not_dvd hp).mpr fun hd => ?_
      have h1 : p ∣ 2 ^ f + 1 := hd.trans (Nat.gcd_dvd_right _ _)
      exact not_dvd_add_one_of_dvd_sub_one hp hp2 (by omega) hpq h1
  have hTexp : ∀ t ∈ (d8Tor p K n).subgroupOf (SU σ n), t ^ p = 1 := by
    intro t ht
    obtain ⟨v, hv⟩ := Subgroup.mem_subgroupOf.mp ht
    apply Subtype.ext
    show ((t : ↥(SU σ n)) : GL (Fin n) K) ^ p = 1
    rw [← hv]
    show diagU (d8Vec n v) ^ p = 1
    rw [diagU_pow, d8Vec_pow_eq_one, diagU_one]
  have hTcomm : ∀ s ∈ (d8Tor p K n).subgroupOf (SU σ n),
      ∀ t ∈ (d8Tor p K n).subgroupOf (SU σ n), s * t = t * s := by
    intro s hs t ht
    obtain ⟨v, hv⟩ := Subgroup.mem_subgroupOf.mp hs
    obtain ⟨w, hw⟩ := Subgroup.mem_subgroupOf.mp ht
    apply Subtype.ext
    show ((s : ↥(SU σ n)) : GL (Fin n) K) * (t : GL (Fin n) K) =
      (t : GL (Fin n) K) * (s : GL (Fin n) K)
    rw [← hv, ← hw]
    show diagU (d8Vec n v) * diagU (d8Vec n w) = diagU (d8Vec n w) * diagU (d8Vec n v)
    rw [diagU_mul, diagU_mul, mul_comm]
  obtain ⟨ε, hε, hFT₁, hFT₂⟩ := exists_toral_quot q hq _ hε₀ hTexp hTcomm
    (fun X hexp _ => exists_conj_into_d8Tor_su hn hc hK hp hp2 hpq X hexp) h.F_le h.F_exp
    h.F_comm h.maximal
  have hVexp : ∀ d : D8Mod p K, d ^ p = 1 := fun d =>
    Prod.ext (Subtype.ext ((mem_rootsOfUnity p _).mp d.1.2))
      (Subtype.ext ((mem_rootsOfUnity p _).mp d.2.2))
  exact ⟨K, hKf, hKfin, hζ, WCtx.ofCentralQuot hVexp SM q hq ε hε h.F_le h.F_exp hFT₁ hFT₂⟩

theorem kf123Row5 : KF123Row 5 := by
  intro G _ _ p L A₀ F h hmodel
  obtain ⟨K, hKf, hKfin, hζ, ⟨S⟩⟩ :=
    exists_runitary_ctx (Or.inl rfl) d8Comb_four d8Comb2_four h hmodel
  exact S.rowData (Or.inl rfl) h.prime (by have := h.five_le; omega) hζ hmodel

theorem kf123Row6 : KF123Row 6 := by
  intro G _ _ p L A₀ F h hmodel
  obtain ⟨K, hKf, hKfin, hζ, ⟨S⟩⟩ :=
    exists_runitary_ctx (Or.inr rfl) d8Comb_five d8Comb2_five h hmodel
  exact S.rowData (Or.inr (Or.inl rfl)) h.prime (by have := h.five_le; omega) hζ hmodel

theorem kf123NTRow5 : KF123NTRow 5 := by
  intro G _ _ p L A₀ F h hmodel y hyL hyF
  obtain ⟨K, hKf, hKfin, hζ, ⟨S⟩⟩ :=
    exists_runitary_ctx (Or.inl rfl) d8Comb_four d8Comb2_four h hmodel
  have hpowF : ∀ a : F, a ^ p = 1 :=
    Monoid.exponent_dvd_iff_forall_pow_eq_one.mp h.F_elem.exponent_dvd_p
  exact S.not_isAutTransvection h.prime (by have := h.five_le; omega) h.five_le hζ hpowF hyL hyF

theorem kf123NTRow6 : KF123NTRow 6 := by
  intro G _ _ p L A₀ F h hmodel y hyL hyF
  obtain ⟨K, hKf, hKfin, hζ, ⟨S⟩⟩ :=
    exists_runitary_ctx (Or.inr rfl) d8Comb_five d8Comb2_five h hmodel
  have hpowF : ∀ a : F, a ^ p = 1 :=
    Monoid.exponent_dvd_iff_forall_pow_eq_one.mp h.F_elem.exponent_dvd_p
  exact S.not_isAutTransvection h.prime (by have := h.five_le; omega) h.five_le hζ hpowF hyL hyF

end CFSG.RankThree.PartOne
