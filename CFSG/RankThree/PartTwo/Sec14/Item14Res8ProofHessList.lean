module

public import CFSG.RankThree.PartTwo.Sec14.Item14Res6ProofTypesL3
public import CFSG.RankThree.PartTwo.Sec14.Item14Res8ProofHessModel
import CFSG.RankThree.PartTwo.Sec13.Item138NMod9
import CFSG.RankThree.PartTwo.Sec13.Item138ProofOmega
import CFSG.RankThree.PartTwo.Sec19.Step1915WProofLie3K
import CFSG.RankThree.PartTwo.Sec19.Step1919NarrowRank

public section

namespace CFSG.RankThree.PartTwo.Sec14

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec4
open CFSG.RankThree.PartTwo.Sec13 (Item131)
open CFSG.Assembly.RankThreeEven (projImage)

theorem ks142L3HessList : KS142L3HessList := by
  intro X _ _ p _ hp3 hiso h91 h98 E hEe hE9 Y hY3 hEY
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
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
  obtain ⟨dM, cM, hdM, hcM, hdc, hdo, hco, hcd⟩ :=
    Sec19.Step1915WProof.exists_heisPair hK hq hτ hτ1
  set Ê := Subgroup.zpowers dM ⊔ Subgroup.zpowers cM with hÊ
  have hÊ9 : Nat.card Ê = 9 := by
    rw [hÊ, Sec19.Step1919NarrowRank.card_sup_zpowers_of_orderOf _ hco hcd (by
      rintro _ ⟨k, rfl⟩
      exact ((Commute.zpow_left hdc k).eq)), Nat.card_zpowers, hdo]
  set S₀ := Sylow.ofCard Ê (by rw [hÊ9, h9M]; norm_num) with hS₀
  have hE'card : Nat.card (E.map ψ.toMonoidHom) =
      3 ^ (Nat.card (projImage (slPi π 3 (p ^ 1) K))).factorization 3 := by
    rw [Subgroup.card_map_of_injective ψ.injective, hE9, h9M]
    norm_num
  set S' := Sylow.ofCard (E.map ψ.toMonoidHom) hE'card with hS'
  obtain ⟨k, hk⟩ := MulAction.exists_smul_eq (projImage (slPi π 3 (p ^ 1) K)) S₀ S'
  set Φ : projImage (slPi π 3 (p ^ 1) K) ≃* X := (MulAut.conj k).trans ψ.symm with hΦ
  have hΦapp : ∀ m, Φ m = ψ.symm (k * m * k⁻¹) := fun m => rfl
  have hΦE : ∀ w ∈ Ê, Φ w ∈ E := by
    intro w hw
    have h1 : k * w * k⁻¹ ∈ ((k • S₀ : Sylow 3 _) : Subgroup _) := by
      rw [Sylow.coe_subgroup_smul, Subgroup.mem_smul_pointwise_iff_exists]
      exact ⟨w, hw, by simp [MulAut.smul_def, MulAut.conj_apply]⟩
    rw [hk] at h1
    obtain ⟨y, hy, hye⟩ := h1
    rw [hΦapp, ← hye]
    change ψ.symm (ψ y) ∈ E
    rw [MulEquiv.symm_apply_apply]
    exact hy
  set Y' := Y.map Φ.symm.toMonoidHom with hY'
  have hY'3 : ¬ 3 ∣ Nat.card Y' := by
    rw [hY', Subgroup.card_map_of_injective Φ.symm.injective]
    exact hY3
  have hÊY' : Ê ≤ Subgroup.normalizer (Y' : Set (projImage (slPi π 3 (p ^ 1) K))) := by
    intro e he
    refine Subgroup.mem_normalizer_fintype fun x hx => ?_
    obtain ⟨y, hy, rfl⟩ := hx
    refine ⟨Φ e * y * (Φ e)⁻¹, (Subgroup.mem_normalizer_iff.mp (hEY (hΦE e he)) y).mp hy, ?_⟩
    change Φ.symm (Φ e * y * (Φ e)⁻¹) = e * Φ.symm y * e⁻¹
    rw [map_mul, map_mul, map_inv, MulEquiv.symm_apply_apply]
  obtain ⟨b, hbÊ, hb1, hY'b⟩ := Res8Hess.le_thetaC_model hK hp2 hτ hτ1 hq hdM hcM hdc hdo hco
    hcd hY'3 hÊY'
  refine ⟨Φ b, hΦE b hbÊ, fun h => hb1 (Φ.injective (by rw [h, map_one])), fun y hy => ?_⟩
  have h1 : Φ.symm y ∈ Res8Hess.thetaC b := hY'b ⟨y, hy, rfl⟩
  have h2 : Φ (Φ.symm y) ∈ (Res8Hess.thetaC b).map Φ.toMonoidHom := ⟨_, h1, rfl⟩
  rw [Res8Hess.thetaC_map_equiv, MulEquiv.apply_symm_apply] at h2
  exact h2

end CFSG.RankThree.PartTwo.Sec14
