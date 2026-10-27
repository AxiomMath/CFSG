module

public import CFSG.RankThree.PartOne.KEXC.D8Class
public import CFSG.RankThree.PartOne.KEXC.ScalarAssemble
public import CFSG.RankThree.PartOne.KFOUT3.KtyRow8

public section

namespace CFSG.RankThree.PartOne.KEXC

open CFSG CFSG.RankThree.PartOne CFSG.RankThree.PartOne.KFU CFSG.RankThree.PartOne.KFOUT3
  CFSG.RankThree.PartOne.KFQ CFSG.Assembly.LowTwoRank

theorem linear4_weyl_scalar {G : Type} [Group G] [Finite G] {p : ℕ} {L A₀ F : Subgroup G}
    (h : Table123Core p L A₀ F) (hmodel : RowModel p L 8) {y : G}
    (hyL : y ∈ Subgroup.normalizer (L : Set G)) (hyF : y ∈ Subgroup.normalizer (F : Set G)) :
    ∃ h' : G, h' ∈ L ∧ h' ∈ Subgroup.normalizer (F : Set G) ∧
      ∃ k : ℤ, ∀ f ∈ F, y * f * y⁻¹ = h' * f ^ k * h'⁻¹ := by
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
  have hq2 : 2 ≤ Nat.card K := by
    have : 1 < Nat.card K := Finite.one_lt_card
    omega
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
  have hcop : Nat.Coprime p (Nat.card (Subgroup.center ↥L)) :=
    (Nat.Prime.coprime_iff_not_dvd hp).mpr h.center_pPrime
  have hε₀ := isCentralPQuot_center' (e.trans (m8Iso (K := K)).symm) hcop
  set Tsub : Subgroup ↥(M8 K) :=
    (d8Emb : D8Mod p (Qext K) →* (QV K (Fin 2) ≃ₗ[K] QV K (Fin 2))).range.subgroupOf (M8 K)
    with hTsub
  have hTexp : ∀ t ∈ Tsub, t ^ p = 1 := by
    intro t ht
    obtain ⟨v, hv⟩ := Subgroup.mem_subgroupOf.mp ht
    apply Subtype.ext
    show ((t : ↥(M8 K)) : QV K (Fin 2) ≃ₗ[K] QV K (Fin 2)) ^ p = 1
    rw [← hv]
    exact d8Emb_pow v
  have hTcomm : ∀ s ∈ Tsub, ∀ t ∈ Tsub, s * t = t * s := by
    intro s hs t ht
    obtain ⟨v, hv⟩ := Subgroup.mem_subgroupOf.mp hs
    obtain ⟨w, hw⟩ := Subgroup.mem_subgroupOf.mp ht
    apply Subtype.ext
    show ((s : ↥(M8 K)) : QV K (Fin 2) ≃ₗ[K] QV K (Fin 2)) *
      (t : QV K (Fin 2) ≃ₗ[K] _) = (t : QV K (Fin 2) ≃ₗ[K] _) * (s : QV K (Fin 2) ≃ₗ[K] _)
    rw [← hv, ← hw]
    exact d8Emb_comm v w
  obtain ⟨ε, hε, hFT₁, hFT₂⟩ := exists_toral_quot (T := Tsub) (MonoidHom.id _)
    (isCentralPQuot_id p) _ hε₀ hTexp hTcomm
    (fun X hexp _ => exists_conj_into_T8 hp hp2 hpq' X hexp) h.F_le h.F_exp h.F_comm h.maximal
  obtain ⟨SM, hSM⟩ := exists_d8ctx_r8' (K := K) hp hp2 hpq'
  have hVexp : ∀ d : D8Mod p (Qext K), d ^ p = 1 := fun d =>
    Prod.ext (Subtype.ext ((mem_rootsOfUnity p _).mp d.1.2))
      (Subtype.ext ((mem_rootsOfUnity p _).mp d.2.2))
  obtain ⟨S, hrel⟩ := wctx_ofCentralQuot' hVexp SM (MonoidHom.id _) (isCentralPQuot_id p) ε hε
    h.F_le h.F_exp hFT₁ hFT₂
  have hrel' : ∀ d, ε (Subgroup.inclusion h.F_le (S.tor d)) = KFOUT3.T8 hp hp2 hpq' d := by
    intro d
    rw [hrel d]
    exact hSM d
  have Hconj : ∀ γ : DihedralGroup 4, ∃ m : ↥(M8 K),
      ∀ v, m * KFOUT3.T8 hp hp2 hpq' v * m⁻¹ = KFOUT3.T8 hp hp2 hpq' (d8Act γ v) := by
    intro γ
    obtain ⟨g', hdet, hr⟩ := exists_realizer (p := p) hpq' γ
    exact ⟨⟨g', (mem_M8_iff _).mpr hdet⟩, fun v => Subtype.ext (hr v)⟩
  exact d8_weyl_scalar hp hp2 hζ hcop h.F_le S hε (KFOUT3.T8 hp hp2 hpq') hrel' Hconj
    (fun b hb => smallAt_of_card_le (card_centralizer_le hp hp2 hpq' hb) (small_lt_big hq2))
    (fun a ha => bigAt_diag hp hp2 hpq' ha) hyL hyF

theorem kf1215Scalar8 : KF1215Scalar 8 := by
  intro G _ _ p A c L E ctx hmodel n hn
  refine exists_scalar_of_weyl_scalar ctx hn fun y hyL hyF => ?_
  exact linear4_weyl_scalar ctx.table_core hmodel hyL hyF

end CFSG.RankThree.PartOne.KEXC
