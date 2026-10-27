module

public import CFSG.LocalAnalysis.UniquenessCase.Lie.SU3Cover
import CFSG.LocalAnalysis.UniquenessCase.Lie.Cover

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.LieType.Universal.Unitary CFSG.LieType.BorelTits CFSG.LieType.Steinberg Subgroup

@[expose] def uc22pwTorusSU3 : Prop :=
  ∀ (X : Type) [Group X] [Finite X], CFSG.Open.IsQuasisimple X → ∀ n : ℕ, 2 < n → IsSU3 X n →
    ∃ T : Subgroup X, IsCyclic T ∧ Odd (Nat.card T) ∧
      (2 ^ (2 * n) - 1) ∣ 3 * Nat.card (T.map (QuotientGroup.mk' (Subgroup.center X)))

theorem uc22pwTorusSU3_holds :
    uc22pwTorusSU3 := by
  intro X _ _ hq n hn hSU
  obtain ⟨-, hU3⟩ := hSU
  obtain ⟨-, K, hKf, hKfin, hK, ⟨e₁⟩⟩ :=
    CFSG.Blueprint.LieModel.statedClassicalModel hU3 (by decide)
  haveI : CharP K 2 := uc22pwlie_charP_two (n := 2 * n) (by rw [hK, ← pow_mul, mul_comm])
  have hn1 : 1 ≤ n := by omega
  haveI : Finite (SU (unitaryInvolution K 2 n) 3) := inferInstance
  let ρ : SU (unitaryInvolution K 2 n) 3 →* X ⧸ center X :=
    e₁.symm.toMonoidHom.comp ((QuotientGroup.mk' _).comp (equivStatedSU hK 3).toMonoidHom)
  have hρ : Function.Surjective ρ :=
    e₁.symm.surjective.comp ((QuotientGroup.mk'_surjective _).comp (equivStatedSU hK 3).surjective)
  have hρZ : ∀ s, ρ s = 1 → equivStatedSU hK 3 s ∈
      (StatedScalars (Fin 3) K).subgroupOf (StatedSU 3 (2 ^ n) K) := by
    intro s hs
    have h1 : e₁.symm (QuotientGroup.mk'
        ((StatedScalars (Fin 3) K).subgroupOf (StatedSU 3 (2 ^ n) K))
        (equivStatedSU hK 3 s)) = 1 := hs
    exact (QuotientGroup.eq_one_iff _).1 ((map_eq_one_iff _ e₁.symm.injective).1 h1)
  have hρc : ρ.ker ≤ center (SU (unitaryInvolution K 2 n) 3) := by
    intro s hs
    have hc := uc22pwsu3_scalar_mem_center _ (hρZ s hs)
    rw [Subgroup.mem_center_iff]
    intro g
    apply (equivStatedSU hK 3).injective
    rw [map_mul, map_mul]
    exact Subgroup.mem_center_iff.1 hc _
  obtain ⟨α, -, -, hαπ⟩ := uc22pwlie_exists_cover_of_closed_fin
    (fun E _ _ π hπ hc => uc22pwsu3_closed hn hK E π hπ hc) hq.1 (QuotientGroup.mk' (center X))
    (QuotientGroup.mk'_surjective _) (by rw [QuotientGroup.ker_mk']) ρ hρ hρc
  have hHc : Nat.card (uc22pwsu3H (unitaryInvolution K 2 n)) = (2 ^ n) ^ 2 - 1 :=
    card_levelTorus_three hK
  haveI : IsCyclic (uc22pwsu3H (unitaryInvolution K 2 n)) := uc22pwsu3H_cyclic
  set H := uc22pwsu3H (unitaryInvolution K 2 n) with hH
  refine ⟨H.map α, isCyclic_of_surjective (α.subgroupMap H) (α.subgroupMap_surjective H), ?_, ?_⟩
  · refine Odd.of_dvd_nat ?_ (Subgroup.card_map_dvd H α)
    rw [hHc, uc22pwsu3_sq_sub_one hn1]
    exact (uc22pwsu3_odd_two_pow_sub_one hn1).mul (uc22pwsu3_odd_two_pow_add_one hn1)
  · have hmap : (H.map α).map (QuotientGroup.mk' (center X)) = H.map ρ := by
      rw [Subgroup.map_map]
      congr 1
      ext s
      exact hαπ s
    have h1 := Subgroup.relIndex_mul_card ρ.ker H
    rw [Subgroup.relIndex_ker] at h1
    have hk : Nat.card ↥(ρ.ker ⊓ H) ∣ 3 := by
      have h2 : Nat.card ρ.ker ∣ Nat.card ((StatedScalars (Fin 3) K).subgroupOf
          (StatedSU 3 (2 ^ n) K)) := by
        rw [Nat.card_congr (MulEquiv.subgroupMap (equivStatedSU hK 3) ρ.ker).toEquiv]
        exact Subgroup.card_dvd_of_le (fun _ ⟨s, hs, hsx⟩ => hsx ▸ hρZ s hs)
      rw [(CFSG.LinearGroups.unitary_scalar_kernel Nat.prime_two hK (n := 3)
        (by norm_num)).2.2] at h2
      exact (Subgroup.card_dvd_of_le inf_le_left).trans (h2.trans (Nat.gcd_dvd_left _ _))
    obtain ⟨t, ht⟩ := hk
    rw [hmap, show 2 ^ (2 * n) - 1 = Nat.card H by rw [hHc, ← pow_mul, mul_comm]]
    refine ⟨t, ?_⟩
    calc 3 * Nat.card (H.map ρ) = (Nat.card ↥(ρ.ker ⊓ H) * t) * Nat.card (H.map ρ) := by rw [← ht]
      _ = t * (Nat.card (H.map ρ) * Nat.card ↥(ρ.ker ⊓ H)) := by ring
      _ = Nat.card H * t := by rw [h1]; ring

end CFSG.LocalAnalysis.UniquenessCase.UC22
