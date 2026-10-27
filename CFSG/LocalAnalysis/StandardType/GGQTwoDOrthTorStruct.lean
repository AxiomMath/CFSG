module

public import CFSG.LocalAnalysis.StandardType.GGQTwoDOrthTorFactor

public section

namespace CFSG.StandardType.QTwo

open CFSG.StandardType CFSG.StandardType.OrthTorus
open CFSG.RankThree.Classical2 (orthDerived)
open TauCeti.QuadraticMap

private lemma plh_ofAdd_one_pow_three (p : ℕ) [Fact p.Prime] (hp : p ∣ 3) :
    (Multiplicative.ofAdd (1 : ZMod p)) ^ 3 = 1 := by
  rw [← ofAdd_nsmul, nsmul_one]
  have h3 : ((3 : ℕ) : ZMod p) = 0 := (ZMod.natCast_eq_zero_iff 3 p).mpr hp
  rw [h3]
  rfl

theorem qtwoOrth_torStruct_std {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {Bs X : Subgroup G} (Φ : OrthFrameCore p Bs X) (hF : Nat.card Φ.F = 2) {a₀ : ℕ}
    (ha : a₀ ≤ Φ.r) : Φ.TorStruct (Φ.Δ.τ (torStd p Φ.r a₀)) := by
  let t₀ : Φ.V ≃ₗ[Φ.F] Φ.V := Φ.Δ.τ (torStd p Φ.r a₀)
  have htA : t₀ ∈ Φ.A := by
    rw [← Φ.Δ.τ_range]
    exact ⟨torStd p Φ.r a₀, rfl⟩
  have htΩ : t₀ ∈ orthDerived Φ.Q := Φ.hA htA
  have htO : t₀ ∈ orthogonalGroup Φ.Q :=
    CFSG.RankThree.Classical.orthDerived_le_orthogonalGroup Φ.Q htΩ
  have hpdvd : p ∣ 3 := by
    have h := Φ.hpq
    rwa [hF] at h
  have ht3 : t₀ ^ 3 = 1 := by
    change (Φ.Δ.τ (torStd p Φ.r a₀)) ^ 3 = 1
    have hpow : (torStd p Φ.r a₀) ^ 3 = 1 := by
      funext i
      change ((torStd p Φ.r a₀) i) ^ 3 = 1
      by_cases hi : i.val < a₀
      · simp [torStd, hi]
      · rw [show (torStd p Φ.r a₀) i = Multiplicative.ofAdd (1 : ZMod p) by
          simp [torStd, hi]]
        exact plh_ofAdd_one_pow_three p hpdvd
    rw [← map_pow, hpow, map_one]
  have h3 : (3 : Φ.F) ≠ 0 := by
    have h2 : (2 : Φ.F) = 0 := CharP.cast_eq_zero Φ.F 2
    have h31 : (3 : Φ.F) = 1 := by
      rw [show (3 : Φ.F) = 2 + 1 by norm_num, h2, zero_add]
    rw [h31]
    exact one_ne_zero
  have hQ := Φ.Δ.polarBilin_nondegenerate_of_noFixed Φ.hfix
  have htorCle : Φ.torC t₀ ≤ orthogonalGroup Φ.Q ⊓ Subgroup.centralizer {t₀} := by
    intro x hx
    rw [OrthFrameCore.torC] at hx
    exact ⟨CFSG.RankThree.Classical.orthDerived_le_orthogonalGroup Φ.Q hx.1, hx.2⟩
  refine ⟨torP₀ Φ.Q t₀, torP₁ Φ.Q t₀, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact torP₀_le Φ.Q htO ht3 h3 hQ
  · exact torP₁_le Φ.Q
  · refine (Subgroup.normal_subgroupOf_iff (torP₀_le Φ.Q htO ht3 h3 hQ)).mpr ?_
    intro h k hh hk
    exact (Subgroup.normal_subgroupOf_iff
      ((torP₀_le Φ.Q htO ht3 h3 hQ).trans htorCle)).mp
        (torP₀_normal Φ.Q htO ht3 h3 hQ) h k hh (htorCle hk)
  · refine (Subgroup.normal_subgroupOf_iff (torP₁_le Φ.Q)).mpr ?_
    intro h k hh hk
    exact (Subgroup.normal_subgroupOf_iff
      ((torP₁_le Φ.Q).trans htorCle)).mp
        (torP₁_normal Φ.Q htO ht3 h3 hQ) h k hh (htorCle hk)
  · intro a ha b hb
    exact torP_commute Φ.Q htO ht3 h3 hQ ha hb
  · intro K hK hperf
    exact perfect_le_torP Φ.Q htO ht3 h3 hQ (hK.trans htorCle) hperf
  · exact Φ.torFactor_P₀_std hF ha
  · exact Φ.torFactor_P₁_std hF ha

theorem qtwoOrth_torStruct {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {Bs X : Subgroup G} (Φ : OrthFrameCore p Bs X) (hF : Nat.card Φ.F = 2)
    {t : Φ.V ≃ₗ[Φ.F] Φ.V} (ht : t ∈ Φ.A) : Φ.TorStruct t := by
  exact Φ.torStruct_of_std hF (fun a₀ ha => qtwoOrth_torStruct_std Φ hF ha) ht

end CFSG.StandardType.QTwo

end
