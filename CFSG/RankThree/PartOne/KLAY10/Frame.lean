module

public import CFSG.RankThree.PartOne.KF.R1Model
public import CFSG.RankThree.PartOne.KF.RowCore
public import CFSG.RankThree.PartOne.KF.SpQuad
public import CFSG.RankThree.PartOne.KF.ToralQuot

public section

namespace CFSG.RankThree.PartOne.KLAY10

open CFSG CFSG.RankThree.PartOne CFSG.RankThree.PartOne.KFU CFSG.RankThree.PartOne.KFQ
  CFSG.Assembly.LowTwoRank

@[expose] noncomputable def T10 (p : ℕ) (K : Type) [Field K] [Finite K] [CharP K 2] :
    Subgroup ↥(M10 K) :=
  (emb10 : torusVec p 4 (Qext K) →* (QV K (Fin 3) ≃ₗ[K] QV K (Fin 3))).range.subgroupOf (M10 K)

theorem exists_r10frame {G : Type} [Group G] [Finite G] {p : ℕ} {L A₀ F : Subgroup G}
    (h : Table123Core p L A₀ F) (hmodel : RowModel p L 10) :
    ∃ (f : ℕ) (K : Type) (_ : Field K) (_ : Finite K) (_ : CharP K 2), 1 ≤ f ∧ p ∣ 2 ^ f + 1 ∧
      Nat.card K = 2 ^ f ∧
      StatedClassicalModel (L ⧸ Subgroup.center L) .PSp 3 2 f ∧
      (∃ ζ : (Qext K)ˣ, IsPrimitiveRoot ζ p) ∧
      ∃ (ε : ↥L →* StatedProj (StatedSp 3 K)) (q : ↥(M10 K) →* StatedProj (StatedSp 3 K)),
        IsCentralPQuot p ε ∧ IsCentralPQuot p q ∧ Function.Bijective q ∧
        (∀ t ∈ T10 p K, ∃ x : F, ε (Subgroup.inclusion h.F_le x) = q t) ∧
        ∀ x : F, ∃ t ∈ T10 p K, ε (Subgroup.inclusion h.F_le x) = q t := by
  classical
  obtain ⟨f, hf1, hpq, hmod⟩ := hmodel
  have hmod' := hmod
  obtain ⟨-, K, hKf, hKfin, hK, ⟨e⟩⟩ := hmod'
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
    (fun X hexp _ => exists_conj_into_T10 hp h5 hpq' X hexp) h.F_le h.F_exp h.F_comm h.maximal
  exact ⟨f, K, hKf, hKfin, hchar, hf1, hpq, hK, hmod, hζ, ε, q, hε, hq, hqbij, hFT₁, hFT₂⟩

end CFSG.RankThree.PartOne.KLAY10
