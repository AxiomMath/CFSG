module

public import CFSG.RankThree.PartOne.KF.R8Model
public import CFSG.RankThree.PartOne.KF.R1Final

public section

namespace CFSG.RankThree.PartOne

open CFSG CFSG.RankThree.PartOne.KFU CFSG.RankThree.PartOne.KFQ CFSG.Assembly.LowTwoRank

variable {G : Type} [Group G]

@[expose] noncomputable def q8 (K : Type) [Field K] [Finite K] [CharP K 2] :
    ↥(M8 K) →* StatedProj (StatedSL 4 K) :=
  (QuotientGroup.mk' ((StatedScalars (Fin 4) K).subgroupOf (StatedSL 4 K))).comp
    (m8Equiv (K := K)).toMonoidHom

@[expose] noncomputable def T8 (p : ℕ) (K : Type) [Field K] [Finite K] [CharP K 2] :
    Subgroup ↥(M8 K) :=
  (d8Emb : D8Mod p (Qext K) →* (QV K (Fin 2) ≃ₗ[K] QV K (Fin 2))).range.subgroupOf (M8 K)

theorem exists_r8frame_of [Finite G] {p : ℕ} {L A₀ F : Subgroup G} (h : Table123Core p L A₀ F)
    {f : ℕ} (hpq : p ∣ 2 ^ f + 1)
    (hmod : StatedClassicalModel (L ⧸ Subgroup.center L) .PSL 4 2 f) :
    ∃ (K : Type) (_ : Field K) (_ : Finite K) (_ : CharP K 2), Nat.card K = 2 ^ f ∧
      ∃ ε : ↥L →* StatedProj (StatedSL 4 K), IsCentralPQuot p ε ∧
        (∀ t ∈ T8 p K, ∃ x : F, ε (Subgroup.inclusion h.F_le x) = q8 K t) ∧
        ∀ x : F, ∃ t ∈ T8 p K, ε (Subgroup.inclusion h.F_le x) = q8 K t := by
  classical
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
  have hq := isCentralPQuot_m8 (K := K) p
  have hcop : Nat.Coprime p (Nat.card (Subgroup.center ↥L)) :=
    (Nat.Prime.coprime_iff_not_dvd hp).mpr h.center_pPrime
  have hε₀ := isCentralPQuot_center e hcop
  have hTexp : ∀ t ∈ T8 p K, t ^ p = 1 := by
    intro t ht
    obtain ⟨v, hv⟩ := Subgroup.mem_subgroupOf.mp ht
    apply Subtype.ext
    show ((t : ↥(M8 K)) : QV K (Fin 2) ≃ₗ[K] QV K (Fin 2)) ^ p = 1
    rw [← hv]
    exact d8Emb_pow v
  have hTcomm : ∀ s ∈ T8 p K, ∀ t ∈ T8 p K, s * t = t * s := by
    intro s hs t ht
    obtain ⟨v, hv⟩ := Subgroup.mem_subgroupOf.mp hs
    obtain ⟨w, hw⟩ := Subgroup.mem_subgroupOf.mp ht
    apply Subtype.ext
    show ((s : ↥(M8 K)) : QV K (Fin 2) ≃ₗ[K] QV K (Fin 2)) * (t : QV K (Fin 2) ≃ₗ[K] _) =
      (t : QV K (Fin 2) ≃ₗ[K] _) * (s : QV K (Fin 2) ≃ₗ[K] _)
    rw [← hv, ← hw]
    exact d8Emb_comm v w
  obtain ⟨ε, hε, hFT₁, hFT₂⟩ := exists_toral_quot (q8 K) hq _ hε₀ hTexp hTcomm
    (fun X hexp _ => exists_conj_into_T8 hp hp2 hpq' X hexp) h.F_le h.F_exp h.F_comm
    h.maximal
  exact ⟨K, hKf, hKfin, hchar, hK, ε, hε, hFT₁, hFT₂⟩

theorem exists_r8frame [Finite G] {p : ℕ} {L A₀ F : Subgroup G} (h : Table123Core p L A₀ F)
    (hmodel : RowModel p L 8) :
    ∃ (f : ℕ) (K : Type) (_ : Field K) (_ : Finite K) (_ : CharP K 2), 1 ≤ f ∧ p ∣ 2 ^ f + 1 ∧
      Nat.card K = 2 ^ f ∧
      ∃ ε : ↥L →* StatedProj (StatedSL 4 K), IsCentralPQuot p ε ∧
        (∀ t ∈ T8 p K, ∃ x : F, ε (Subgroup.inclusion h.F_le x) = q8 K t) ∧
        ∀ x : F, ∃ t ∈ T8 p K, ε (Subgroup.inclusion h.F_le x) = q8 K t := by
  obtain ⟨f, hf1, hpq, hmod⟩ := hmodel
  obtain ⟨K, hKf, hKfin, hchar, hK, ε, hε, hFT₁, hFT₂⟩ := exists_r8frame_of h hpq hmod
  exact ⟨f, K, hKf, hKfin, hchar, hf1, hpq, hK, ε, hε, hFT₁, hFT₂⟩

theorem exists_r8ctx [Finite G] {p : ℕ} {L A₀ F : Subgroup G} (h : Table123Generic p L A₀ F)
    (hmodel : RowModel p L 8) :
    ∃ (K' : Type) (_ : Field K') (_ : Finite K'), (∃ ζ : K'ˣ, IsPrimitiveRoot ζ p) ∧
      Nonempty (D8Ctx p K' L F) := by
  classical
  obtain ⟨f, K, hKf, hKfin, hchar, hf1, hpq, hK, ε, hε, hFT₁, hFT₂⟩ :=
    exists_r8frame h.toCore hmodel
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

theorem kf123Row8 : KF123Row 8 := by
  intro G _ _ p L A₀ F h hmodel
  obtain ⟨K', hKf, hKfin, hζ, ⟨S⟩⟩ := exists_r8ctx h hmodel
  exact S.rowData (Or.inr (Or.inr (Or.inr rfl))) h.prime (by have := h.five_le; omega) hζ hmodel

theorem kf123NTRow8 : KF123NTRow 8 := by
  intro G _ _ p L A₀ F h hmodel y hyL hyF
  obtain ⟨K', hKf, hKfin, hζ, ⟨S⟩⟩ := exists_r8ctx h hmodel
  have hpowF : ∀ a : F, a ^ p = 1 :=
    Monoid.exponent_dvd_iff_forall_pow_eq_one.mp h.F_elem.exponent_dvd_p
  exact S.not_isAutTransvection h.prime (by have := h.five_le; omega) h.five_le hζ hpowF hyL hyF

end CFSG.RankThree.PartOne
