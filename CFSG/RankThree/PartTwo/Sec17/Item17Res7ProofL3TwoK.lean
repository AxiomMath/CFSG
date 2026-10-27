module

public import CFSG.RankThree.PartTwo.Sec17.Item17Res7ProofL3Two
import CFSG.RankThree.PartTwo.Sec13.Item138NMod9
import CFSG.RankThree.PartTwo.Sec13.Item138ProofOmega
import CFSG.RankThree.PartTwo.Sec19.Step1915WProofLie3K
import CFSG.RankThree.PartTwo.Sec19.Step1919NarrowRank
public import CFSG.RankThree.PartTwo.Sec17.Item17Res7ProofL3Defs

public section

namespace CFSG.RankThree.PartTwo.Sec17

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec4
open CFSG.Assembly.RankThreeEven (projImage)

theorem ks17L3TwoCent : KS17L3TwoCent := by
  intro X _ _ p _ hp3 hiso h91 h98 B hB
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hp2 : p ≠ 2 := by omega
  have h9 : (Nat.card X).factorization 3 = 2 :=
    Sec13.Item138Proof.factorization_card_three_eq_two le_rfl hiso (by simp; omega)
  obtain ⟨π, K, _, hK, hq, ⟨ψ⟩⟩ := Sec13.exists_projImage_model le_rfl hiso
  have := hK.finite
  have : Finite (Matrix.ProjGenLinGroup (Fin 3) K) := by
    unfold Matrix.ProjGenLinGroup
    infer_instance
  have h9M : (Nat.card (projImage (slPi π 3 (p ^ 1) K))).factorization 3 = 2 := by
    rw [← Nat.card_congr ψ.toEquiv, h9]
  obtain ⟨τ, hτ, hτ1⟩ := exists_tau hK hq
  obtain ⟨dM, cM, hdM, hcM, hdc, hdo, hco, hcd⟩ := Sec19.Step1915WProof.exists_heisPair hK hq hτ hτ1
  set E := Subgroup.zpowers dM ⊔ Subgroup.zpowers cM with hE
  have hE9 : Nat.card E = 9 := by
    rw [hE, Sec19.Step1919NarrowRank.card_sup_zpowers_of_orderOf _ hco hcd (by
      rintro _ ⟨k, rfl⟩
      exact ((Commute.zpow_left hdc k).eq)), Nat.card_zpowers, hdo]
  set S₀ := Sylow.ofCard E (by rw [hE9, h9M]; norm_num) with hS₀
  have hB'card : Nat.card (B.map ψ.toMonoidHom) =
      3 ^ (Nat.card (projImage (slPi π 3 (p ^ 1) K))).factorization 3 := by
    rw [Subgroup.card_map_of_injective ψ.injective, hB, h9M]
    norm_num
  set S' := Sylow.ofCard (B.map ψ.toMonoidHom) hB'card with hS'
  obtain ⟨k, hk⟩ := MulAction.exists_smul_eq (projImage (slPi π 3 (p ^ 1) K)) S₀ S'
  set Φ : projImage (slPi π 3 (p ^ 1) K) ≃* X := (MulAut.conj k).trans ψ.symm with hΦ
  have hΦapp : ∀ m, Φ m = ψ.symm (k * m * k⁻¹) := fun m => rfl
  have hΦE : ∀ w ∈ E, Φ w ∈ B := by
    intro w hw
    have h1 : k * w * k⁻¹ ∈ ((k • S₀ : Sylow 3 _) : Subgroup _) := by
      rw [Sylow.coe_subgroup_smul, Subgroup.mem_smul_pointwise_iff_exists]
      exact ⟨w, hw, by simp [MulAut.smul_def, MulAut.conj_apply]⟩
    rw [hk] at h1
    obtain ⟨y, hy, hye⟩ := h1
    rw [hΦapp, ← hye]
    change ψ.symm (ψ y) ∈ B
    rw [MulEquiv.symm_apply_apply]
    exact hy
  have hΦB : ∀ b ∈ B, Φ.symm b ∈ E := by
    intro b hb
    have h1 : ψ b ∈ ((k • S₀ : Sylow 3 _) : Subgroup _) := by
      rw [hk]
      exact ⟨b, hb, rfl⟩
    rw [Sylow.coe_subgroup_smul, Subgroup.mem_smul_pointwise_iff_exists] at h1
    obtain ⟨w, hw, hwe⟩ := h1
    have : Φ w = b := by
      rw [hΦapp, ← MulAut.conj_apply, ← MulAut.smul_def, hwe, MulEquiv.symm_apply_apply]
    rw [← this, MulEquiv.symm_apply_apply]
    exact hw
  refine ⟨fun R hR2 hBR => ?_, ?_⟩
  · set R' := R.map Φ.symm.toMonoidHom with hR'
    have hR'2 : IsPGroup 2 R' := hR2.map _
    have hER' : E ≤ Subgroup.normalizer (R' : Set (projImage (slPi π 3 (p ^ 1) K))) := by
      intro e he
      refine Subgroup.mem_normalizer_fintype fun x hx => ?_
      obtain ⟨r, hr, rfl⟩ := hx
      refine ⟨Φ e * r * (Φ e)⁻¹, (Subgroup.mem_normalizer_iff.mp (hBR (hΦE e he)) r).mp hr, ?_⟩
      change Φ.symm (Φ e * r * (Φ e)⁻¹) = e * Φ.symm r * e⁻¹
      rw [map_mul, map_mul, map_inv, MulEquiv.symm_apply_apply]
    obtain ⟨b', hb'E, hb'1, hR'O⟩ := Proof17Res7.exists_le_pCoreOf_model hτ hτ1 hK hq hp2 hdM hcM
      hdc hdo hco hcd hR'2 hER'
    refine ⟨Φ b', hΦE b' hb'E, fun h => hb'1 (Φ.injective (by rw [h, map_one])), ?_⟩
    intro r hr
    have h1 : Φ.symm r ∈ CFSG.Open.pCoreOf 2 (Subgroup.centralizer {b'}) := hR'O ⟨r, hr, rfl⟩
    have h2 := Proof17Res7.map_pCoreOf_centralizer_le Φ b' ⟨_, h1, rfl⟩
    have e : Φ.toMonoidHom (Φ.symm r) = r := Φ.apply_symm_apply r
    rw [e] at h2
    exact h2
  · obtain ⟨R₀, hR₀2, hER₀, hR₀1⟩ := Proof17Res7.fourGroup_model hτ hK hp2 hdM hcM
    refine ⟨R₀.map Φ.toMonoidHom, hR₀2.map _, ?_, ?_⟩
    · intro b hb
      refine Subgroup.mem_normalizer_fintype fun x hx => ?_
      obtain ⟨r, hr, rfl⟩ := hx
      refine ⟨Φ.symm b * r * (Φ.symm b)⁻¹,
        (Subgroup.mem_normalizer_iff.mp (hER₀ (hΦB b hb)) r).mp hr, ?_⟩
      change Φ (Φ.symm b * r * (Φ.symm b)⁻¹) = b * Φ r * b⁻¹
      rw [map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply]
    · intro h
      apply hR₀1
      rw [eq_bot_iff]
      intro x hx
      have : Φ x ∈ R₀.map Φ.toMonoidHom := ⟨x, hx, rfl⟩
      rw [h, Subgroup.mem_bot] at this
      rw [Subgroup.mem_bot]
      exact Φ.injective (by rw [this, map_one])

end CFSG.RankThree.PartTwo.Sec17
