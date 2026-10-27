module

public import CFSG.RankThree.PartOne.KF.R7Final
public import CFSG.RankThree.PartOne.KF.R8Final
public import CFSG.RankThree.PartOne.KF.R12Final
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.RankThree.PartOne.KF.R10Model
public import CFSG.RankThree.PartOne.KF.SUSylow
public import CFSG.RankThree.PartOne.KF.W10Ctx

public section

namespace CFSG.RankThree.PartOne.Q1327C

open CFSG CFSG.RankThree.PartOne.KFU CFSG.RankThree.PartOne.KFQ CFSG.Assembly.LowTwoRank
  CFSG.LocalAnalysis.ComponentInitial CFSG.ClassicalGroups.UnitaryFlag
  CFSG.LieType.Universal.Unitary CFSG.LieType.BorelTits

variable {G : Type} [Group G]

theorem exists_runitary_ctx_core [Finite G] {n : ℕ} [NeZero n] (hn : n = 4 ∨ n = 5) (hc : D8Comb n)
    (hc2 : D8Comb2 hc) {p : ℕ} {L A₀ F : Subgroup G} (h : Table123Core p L A₀ F)
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

theorem exists_r7ctx_core [Finite G] {p : ℕ} {L A₀ F : Subgroup G} (h : Table123Core p L A₀ F)
    (hmodel : RowModel p L 7) :
    ∃ (K : Type) (_ : Field K) (_ : Finite K), (∃ ζ : Kˣ, IsPrimitiveRoot ζ p) ∧
      Nonempty (D8Ctx p K L F) := by
  classical
  obtain ⟨f, K, hKf, hKfin, hf1, hpq, hK, hζ, hchar, ε, hε, hFT₁, hFT₂⟩ :=
    exists_r7frame h hmodel
  have hp := h.prime
  have h5 := h.five_le
  have hp2 : p ≠ 2 := by omega
  have : Fact p.Prime := ⟨hp⟩
  have hT : ∀ v : D8Mod p K, (diagU (d8Vec 4 v) : GL (Fin 4) K) ∈ spRev K := fun v => by
    rw [d8Vec_four]
    exact diagU_dvec4_mem_spRev _ _
  have hP : ∀ τ : Equiv.Perm (Fin 4), (∀ i, τ (Fin.rev i) = Fin.rev (τ i)) →
      (permGL τ : GL (Fin 4) K) ∈ spRev K := fun τ hτ => by
    rw [mem_spRev_iff]
    simpa [conjTr] using permGL_gram (RingEquiv.refl K) τ hτ
  obtain ⟨SM⟩ := exists_d8ctx d8Comb_four d8Comb2_four hp hp2 hζ (spRev K) hT hP
  have hq : IsCentralPQuot p (spQ K) := isCentralPQuot_spQ p
  have hVexp : ∀ d : D8Mod p K, d ^ p = 1 := fun d =>
    Prod.ext (Subtype.ext ((mem_rootsOfUnity p _).mp d.1.2))
      (Subtype.ext ((mem_rootsOfUnity p _).mp d.2.2))
  exact ⟨K, hKf, hKfin, hζ, WCtx.ofCentralQuot hVexp SM (spQ K) hq ε hε h.F_le h.F_exp hFT₁ hFT₂⟩

theorem exists_r8ctx_core [Finite G] {p : ℕ} {L A₀ F : Subgroup G} (h : Table123Core p L A₀ F)
    (hmodel : RowModel p L 8) :
    ∃ (K' : Type) (_ : Field K') (_ : Finite K'), (∃ ζ : K'ˣ, IsPrimitiveRoot ζ p) ∧
      Nonempty (D8Ctx p K' L F) := by
  classical
  obtain ⟨f, K, hKf, hKfin, hchar, hf1, hpq, hK, ε, hε, hFT₁, hFT₂⟩ :=
    exists_r8frame h hmodel
  have hp := h.prime
  have h5 := h.five_le
  have hp2 : p ≠ 2 := by omega
  have : Fact p.Prime := ⟨hp⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hpq' : p ∣ Nat.card K + 1 := by rw [hK]; exact hpq
  obtain ⟨m, hmp, hm1, -⟩ := exists_root_not_mem hp hp2 hpq'
  have hζ : ∃ ζ : (Qext K)ˣ, IsPrimitiveRoot ζ p := by
    have hm0 : m ≠ 0 := by
      rintro rfl
      rw [zero_pow hp.ne_zero] at hmp
      exact zero_ne_one hmp
    refine ⟨Units.mk0 m hm0, ?_⟩
    have hu : (Units.mk0 m hm0) ^ p = 1 := Units.ext (by simpa using hmp)
    have hu1 : Units.mk0 m hm0 ≠ 1 := fun h1 => hm1 (by simpa using congrArg Units.val h1)
    rw [IsPrimitiveRoot.iff_orderOf]
    rcases (Nat.dvd_prime hp).mp (orderOf_dvd_of_pow_eq_one hu) with h1 | h1
    · exact absurd (orderOf_eq_one_iff.mp h1) hu1
    · exact h1
  obtain ⟨SM⟩ := exists_d8ctx_r8 hp hp2 hpq'
  have hq := isCentralPQuot_m8 (K := K) p
  have hVexp : ∀ d : D8Mod p (Qext K), d ^ p = 1 := fun d =>
    Prod.ext (Subtype.ext ((mem_rootsOfUnity p _).mp d.1.2))
      (Subtype.ext ((mem_rootsOfUnity p _).mp d.2.2))
  refine ⟨Qext K, inferInstance, inferInstance, hζ, ?_⟩
  exact WCtx.ofCentralQuot hVexp SM (q8 K) hq ε hε h.F_le h.F_exp hFT₁ hFT₂

theorem exists_r10ctx_core [Finite G] {p : ℕ} {L A₀ F : Subgroup G} (h : Table123Core p L A₀ F)
    (hmodel : RowModel p L 10) :
    ∃ (K' : Type) (_ : Field K') (_ : Finite K'), (∃ ζ : K'ˣ, IsPrimitiveRoot ζ p) ∧
      Nonempty (W10Ctx p K' L F) := by
  classical
  obtain ⟨f, hf1, hpq, hmod⟩ := hmodel
  obtain ⟨-, K, hKf, hKfin, hK, ⟨e⟩⟩ := hmod
  have hp := h.prime
  have h5 := h.five_le
  have hp2 : p ≠ 2 := by omega
  have : Fact p.Prime := ⟨hp⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hchar : CharP K 2 := by
    have := Fintype.ofFinite K
    exact charP_of_card_eq_prime_pow (p := 2) (f := f) (by rw [Fintype.card_eq_nat_card]; exact hK)
  have hpq' : p ∣ Nat.card K + 1 := by rw [hK]; exact hpq
  obtain ⟨m, hmp, hm1, -⟩ := exists_root_not_mem hp hp2 hpq'
  have hζ : ∃ ζ : (Qext K)ˣ, IsPrimitiveRoot ζ p := by
    have hm0 : m ≠ 0 := by
      rintro rfl
      rw [zero_pow hp.ne_zero] at hmp
      exact zero_ne_one hmp
    refine ⟨Units.mk0 m hm0, ?_⟩
    have hu : (Units.mk0 m hm0) ^ p = 1 := Units.ext (by simpa using hmp)
    have hu1 : Units.mk0 m hm0 ≠ 1 := fun h1 => hm1 (by simpa using congrArg Units.val h1)
    rw [IsPrimitiveRoot.iff_orderOf]
    rcases (Nat.dvd_prime hp).mp (orderOf_dvd_of_pow_eq_one hu) with h1 | h1
    · exact absurd (orderOf_eq_one_iff.mp h1) hu1
    · exact h1
  obtain ⟨SM⟩ := exists_w10ctx hp h5 hpq' hζ
  obtain ⟨e10⟩ := nonempty_m10Equiv (K := K)
  have hcop : Nat.Coprime p (Nat.card (Subgroup.center ↥L)) :=
    (Nat.Prime.coprime_iff_not_dvd hp).mpr h.center_pPrime
  have hε₀ := isCentralPQuot_center e hcop
  let N : Subgroup ↥(StatedSp 3 K) := (StatedScalars (Fin 3 ⊕ Fin 3) K).subgroupOf (StatedSp 3 K)
  have hN : N = ⊥ :=
    CFSG.LieType.SteinbergBR.EvenSp.statedScalars_subgroupOf_statedSp (by norm_num)
  let q : ↥(M10 K) →* StatedProj (StatedSp 3 K) := (QuotientGroup.mk' N).comp e10.toMonoidHom
  have hqbij : Function.Bijective q := by
    refine ⟨fun x y hxy => ?_, (QuotientGroup.mk'_surjective N).comp e10.surjective⟩
    have h1 : (QuotientGroup.mk' N) (e10 x) = (QuotientGroup.mk' N) (e10 y) := hxy
    rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq, hN,
      Subgroup.mem_bot, inv_mul_eq_one] at h1
    exact e10.injective h1
  have hq : IsCentralPQuot p q := SymCtx.isCentralPQuot_of_bijective q hqbij p
  have hTexp : ∀ t ∈ (emb10 : torusVec p 4 (Qext K) →*
      (QV K (Fin 3) ≃ₗ[K] QV K (Fin 3))).range.subgroupOf (M10 K), t ^ p = 1 := by
    intro t ht
    obtain ⟨v, hv⟩ := Subgroup.mem_subgroupOf.mp ht
    apply Subtype.ext
    show ((t : ↥(M10 K)) : QV K (Fin 3) ≃ₗ[K] QV K (Fin 3)) ^ p = 1
    rw [← hv]
    exact emb10_pow v
  have hTcomm : ∀ s ∈ (emb10 : torusVec p 4 (Qext K) →*
      (QV K (Fin 3) ≃ₗ[K] QV K (Fin 3))).range.subgroupOf (M10 K),
      ∀ t ∈ (emb10 : torusVec p 4 (Qext K) →*
      (QV K (Fin 3) ≃ₗ[K] QV K (Fin 3))).range.subgroupOf (M10 K), s * t = t * s := by
    intro s hs t ht
    obtain ⟨v, hv⟩ := Subgroup.mem_subgroupOf.mp hs
    obtain ⟨w, hw⟩ := Subgroup.mem_subgroupOf.mp ht
    apply Subtype.ext
    show ((s : ↥(M10 K)) : QV K (Fin 3) ≃ₗ[K] QV K (Fin 3)) *
      (t : QV K (Fin 3) ≃ₗ[K] _) = (t : QV K (Fin 3) ≃ₗ[K] _) * (s : QV K (Fin 3) ≃ₗ[K] _)
    rw [← hv, ← hw]
    exact emb10_comm v w
  obtain ⟨ε, hε, hFT₁, hFT₂⟩ := exists_toral_quot q hq _ hε₀ hTexp hTcomm
    (fun X hexp _ => exists_conj_into_T10 hp h5 hpq' X hexp) h.F_le h.F_exp h.F_comm
    h.maximal
  have hVexp : ∀ d : torusVec p 4 (Qext K), d ^ p = 1 := fun d =>
    Subtype.ext (funext fun i => d.2.1 i)
  exact ⟨Qext K, inferInstance, inferInstance, hζ,
    WCtx.ofCentralQuot hVexp SM q hq ε hε h.F_le h.F_exp hFT₁ hFT₂⟩

theorem rowData_core_one [Finite G] {p : ℕ} {L A₀ F : Subgroup G} (h : Table123Core p L A₀ F)
    (hmodel : RowModel p L 1) : RowData p L F 1 := by
  obtain ⟨K, hKf, hKfin, hζ, ⟨S⟩⟩ := exists_r1ctx h hmodel
  have hp := h.prime
  have h5 := h.five_le
  have hp2 : p ≠ 2 := by omega
  have hp3 : ¬ p ∣ 3 := fun hd => by
    have := Nat.le_of_dvd (by norm_num) hd
    omega
  exact ⟨hmodel, S.card_F (m := 2) rfl hp.pos hζ, ⟨S.weylEquiv hp hp2 hζ⟩,
    S.torusImage_eq_closure hp hp2 hζ,
    fun _ B hBF hB => S.torusIrreducible hp (by norm_num) hp3 B hBF hB,
    fun h11 => absurd h11 (by norm_num)⟩

theorem rowData_core_five [Finite G] {p : ℕ} {L A₀ F : Subgroup G} (h : Table123Core p L A₀ F)
    (hmodel : RowModel p L 5) : RowData p L F 5 := by
  obtain ⟨K, hKf, hKfin, hζ, ⟨S⟩⟩ :=
    exists_runitary_ctx_core (Or.inl rfl) d8Comb_four d8Comb2_four h hmodel
  exact S.rowData (Or.inl rfl) h.prime (by have := h.five_le; omega) hζ hmodel

theorem rowData_core_six [Finite G] {p : ℕ} {L A₀ F : Subgroup G} (h : Table123Core p L A₀ F)
    (hmodel : RowModel p L 6) : RowData p L F 6 := by
  obtain ⟨K, hKf, hKfin, hζ, ⟨S⟩⟩ :=
    exists_runitary_ctx_core (Or.inr rfl) d8Comb_five d8Comb2_five h hmodel
  exact S.rowData (Or.inr (Or.inl rfl)) h.prime (by have := h.five_le; omega) hζ hmodel

theorem rowData_core_seven [Finite G] {p : ℕ} {L A₀ F : Subgroup G} (h : Table123Core p L A₀ F)
    (hmodel : RowModel p L 7) : RowData p L F 7 := by
  obtain ⟨K, hKf, hKfin, hζ, ⟨S⟩⟩ := exists_r7ctx_core h hmodel
  exact S.rowData (Or.inr (Or.inr (Or.inl rfl))) h.prime (by have := h.five_le; omega) hζ hmodel

theorem rowData_core_eight [Finite G] {p : ℕ} {L A₀ F : Subgroup G} (h : Table123Core p L A₀ F)
    (hmodel : RowModel p L 8) : RowData p L F 8 := by
  obtain ⟨K', hKf, hKfin, hζ, ⟨S⟩⟩ := exists_r8ctx_core h hmodel
  exact S.rowData (Or.inr (Or.inr (Or.inr rfl))) h.prime (by have := h.five_le; omega) hζ hmodel

theorem rowData_core_ten [Finite G] {p : ℕ} {L A₀ F : Subgroup G} (h : Table123Core p L A₀ F)
    (hmodel : RowModel p L 10) : RowData p L F 10 := by
  obtain ⟨K', hKf, hKfin, hζ, ⟨S⟩⟩ := exists_r10ctx_core h hmodel
  exact S.rowData h.prime h.five_le hζ hmodel

theorem rowData_core_twelve [Finite G] {p : ℕ} {L A₀ F : Subgroup G} (h : Table123Core p L A₀ F)
    (hmodel : RowModel p L 12) : RowData p L F 12 := by
  obtain ⟨K, hKf, hKfin, hζ, ⟨S⟩⟩ := exists_r12ctx h hmodel
  have hp5 : p = 5 := hmodel.1
  subst hp5
  exact S.rowData hζ hmodel

end CFSG.RankThree.PartOne.Q1327C
