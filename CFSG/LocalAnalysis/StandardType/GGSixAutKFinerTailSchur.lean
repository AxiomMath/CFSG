module

public import CFSG.LocalAnalysis.StandardType.GGSixAutKFinerOrbit

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.RootSystem
  CFSG.Assembly.LowTwoRank

section Transfer

theorem ggAKFT_pow_index_eq_one {L : Type*} [Group L] [Finite L] (hperf : commutator L = ⊤)
    (u : L ⧸ Subgroup.center L) {z : L} (hz : z ∈ Subgroup.center L) :
    z ^ ((Subgroup.zpowers u).comap (QuotientGroup.mk' (Subgroup.center L))).index = 1 := by
  classical
  set A := (Subgroup.zpowers u).comap (QuotientGroup.mk' (Subgroup.center L)) with hA
  let f : ↥A →* ↥(Subgroup.zpowers u) :=
    ((QuotientGroup.mk' (Subgroup.center L)).comp A.subtype).codRestrict _ (fun a => a.2)
  have hker : f.ker ≤ Subgroup.center A := by
    intro a ha
    rw [Subgroup.mem_center_iff]
    intro b
    have h1 : (QuotientGroup.mk' (Subgroup.center L)) (a : L) = 1 := congrArg Subtype.val ha
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
    exact Subtype.ext (Subgroup.mem_center_iff.mp h1 b)
  let : IsMulCommutative A := f.isMulCommutative_of_isCyclic_of_ker_le_center hker
  let : CommGroup A := IsMulCommutative.instCommGroup
  have key : ∀ (k : ℕ) (g₀ : L), g₀⁻¹ * z ^ k * g₀ ∈ A → g₀⁻¹ * z ^ k * g₀ = z ^ k := by
    intro k g₀ _
    have h := Subgroup.mem_center_iff.mp ((Subgroup.center L).pow_mem hz k) g₀
    rw [mul_assoc, ← h, inv_mul_cancel_left]
  have htr := MonoidHom.transfer_eq_pow (MonoidHom.id A) z key
  have h1 : MonoidHom.transfer (MonoidHom.id A) z = 1 := by
    have hzc : z ∈ commutator L := by
      rw [hperf]
      trivial
    exact Abelianization.commutator_subset_ker _ hzc
  rw [h1] at htr
  have h2 := congrArg Subtype.val htr
  simpa using h2.symm

theorem ggAKFT_index_mul_orderOf {L : Type*} [Group L] (u : L ⧸ Subgroup.center L) :
    ((Subgroup.zpowers u).comap (QuotientGroup.mk' (Subgroup.center L))).index * orderOf u =
      Nat.card (L ⧸ Subgroup.center L) := by
  rw [Subgroup.index_comap_of_surjective _ (QuotientGroup.mk'_surjective _), ← Nat.card_zpowers,
    Subgroup.index_mul_card]

end Transfer

section Schur

theorem ggAKFT_card_alternatingGroup_five : Nat.card (alternatingGroup (Fin 5)) = 60 := by
  rw [Nat.card_eq_fintype_card, card_alternatingGroup, Fintype.card_fin]
  decide

theorem ggAltFiveCentreInput_holds : GGAltFiveCentreInput := by
  intro L _ _ hL he h5
  obtain ⟨e⟩ := he
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  obtain ⟨a, ha⟩ := exists_prime_orderOf_dvd_card' (G := alternatingGroup (Fin 5)) 5
    (by rw [ggAKFT_card_alternatingGroup_five]; norm_num)
  have hu : orderOf (e.symm a) = 5 := by rw [MulEquiv.orderOf_eq, ha]
  have hidx := ggAKFT_index_mul_orderOf (e.symm a)
  rw [hu, Nat.card_congr e.toEquiv, ggAKFT_card_alternatingGroup_five] at hidx
  have hidx12 : ((Subgroup.zpowers (e.symm a)).comap
      (QuotientGroup.mk' (Subgroup.center L))).index = 12 := by omega
  obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' (G := Subgroup.center L) 5 h5
  have hpow := ggAKFT_pow_index_eq_one hL.1 (e.symm a) z.2
  rw [hidx12] at hpow
  have hdvd : orderOf (z : L) ∣ 12 := orderOf_dvd_of_pow_eq_one hpow
  rw [Subgroup.orderOf_coe, hz] at hdvd
  norm_num at hdvd

end Schur

section Consequences

theorem ggStepTwoBstarNormFiveInput_holds : GGStepTwoBstarNormFiveInput :=
  ggStepTwoBstarNormFiveInput_of_schur ggAltFiveCentreInput_holds

theorem ggStepTwoAutKFiveInput_of_field (hF : GGSixFieldFiveInput)
    (hD : GGLayerNotDFourTwoInput) : GGStepTwoAutKFiveInput :=
  ggStepTwoAutKFiveInput_of_schur ggAltFiveCentreInput_holds hF hD

end Consequences

end CFSG.StandardType
