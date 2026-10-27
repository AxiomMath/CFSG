module

public import CFSG.LocalAnalysis.WeakClosure81.GF2RepsAsch5Bridge
public import CFSG.Quasithin.Vol2.Ch11SecE3L0
public import CFSG.Quasithin.Background.E3ClosedTwo

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Open CFSG.Quasithin
open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.Quasithin.Vol2.Ch11.SecE3
open scoped commutatorElement

theorem inCalEi_one_of_surjective_almostSimple_two_kernel
    {G Γ : Type} [Group G] [Finite G] [Group Γ] [Finite Γ]
    {T A K : Subgroup G}
    (hAT : A ≤ T) (hA : IsElemAbelian 2 A)
    (hτ : tA T A ≤ T ⊓ K)
    (hSyl : IsSylowIn 2 (T ⊓ K) K)
    (π : ↥K →* Γ) (hπ : Function.Surjective π)
    (hker : IsPGroup 2 π.ker)
    {L : Subgroup Γ} (hAS : AlmostSimple L)
    (hcard : Nat.card ((A.subgroupOf K).map π) = 2) :
    InCalEi 1 T A K := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hAK : A ≤ K := (le_tA_of_isElemAbelian hAT hA).trans (hτ.trans inf_le_right)
  let A0 : Subgroup ↥K := A.subgroupOf K
  let B : Subgroup Γ := A0.map π
  let S0 : Subgroup ↥K := (T ⊓ K).subgroupOf K
  have hB : B ≠ ⊥ := by
    intro hbot
    have h1 : Nat.card B = 1 := by rw [hbot]; simp
    have h2 : Nat.card B = 2 := hcard
    omega
  have hS0 : IsSylowIn 2 S0 ⊤ := by
    have h := (E1.isSylowIn_subgroupOf_iff (p := 2) (P := T ⊓ K) (K := K) (H := K)
      inf_le_right le_rfl).mpr hSyl
    simpa [S0, Subgroup.subgroupOf_self] using h
  have hA0S0 : A0 ≤ S0 := by
    intro a ha
    exact Subgroup.mem_subgroupOf.mpr ⟨hAT (Subgroup.mem_subgroupOf.mp ha), a.2⟩
  have hks : Group.IsSolvable π.ker := E1.isSolvable_of_isPGroup_two hker
  have hR : CFSG.solvableRadical ↥K = π.ker := by
    rw [E1.solvableRadical_eq_comap π hπ hks, hAS.solvableRadical_eq_bot, MonoidHom.comap_bot]
  have hO2Q : CFSG.Open.pCore 2 ↥K = π.ker :=
    le_antisymm ((E3.pCore_two_le_solvableRadical (Q := ↥K)).trans (le_of_eq hR))
      (CFSG.LieType.BorelTits.le_pCore 2 inferInstance hker)
  have hO2Γ : CFSG.Open.pCore 2 Γ = ⊥ :=
    le_bot_iff.mp ((E3.pCore_two_le_solvableRadical (Q := Γ)).trans
      (le_of_eq hAS.solvableRadical_eq_bot))
  have hZ : E1.IsTwoClosed ((CFSG.Open.pCore 2 Γ).comap π) := by
    rw [hO2Γ, MonoidHom.comap_bot]
    exact ⟨π.ker, ⟨le_rfl, hker, by rw [Subgroup.relIndex_self]; norm_num⟩,
      by rw [Subgroup.subgroupOf_self]; infer_instance⟩
  have hkerS : π.ker ≤ S0 := by
    have h2 := B6.pCoreOf_two_le_of_isSylowTwoOf hS0
    rw [E1.pCoreOf_top_eq] at h2
    exact (le_of_eq hO2Q.symm).trans h2
  have hres : twoResidual (⊤ : Subgroup ↥K) = perfectCore (⊤ : Subgroup ↥K) :=
    E1.twoResidual_eq_perfectCore_of_surjective π hπ hS0
      (fun M hSM hM => by rw [sup_eq_left.mpr (hkerS.trans hSM)] at hM; exact hM)
      (by rw [hAS.twoResidual_eq, hAS.perfectCore_eq])
  have hETwo := E1.eTwo_of_surjective π hπ hZ hS0.isPGroup hA0S0 hres
    (hAS.eTwo (S := S0.map π) hB)
  let e : (↥K ⧸ CFSG.solvableRadical ↥K) ≃* Γ :=
    QuotientGroup.liftEquiv (CFSG.solvableRadical ↥K) hπ hR
  let L0 : Subgroup (↥K ⧸ CFSG.solvableRadical ↥K) := L.map e.symm.toMonoidHom
  have he_mk : ∀ x : ↥K,
      e (QuotientGroup.mk' (CFSG.solvableRadical ↥K) x) = π x :=
    fun x => QuotientGroup.liftEquiv_coe (N := CFSG.solvableRadical ↥K) hπ hR x
  have hcomp : e.toMonoidHom.comp (QuotientGroup.mk' (CFSG.solvableRadical ↥K)) = π :=
    MonoidHom.ext he_mk
  have hbar : (E1.barRad ↥K A0).map e.toMonoidHom = B := by
    unfold E1.barRad
    rw [Subgroup.map_map, hcomp]
  have hbar_symm : B.map e.symm.toMonoidHom = E1.barRad ↥K A0 := by
    rw [← hbar, CFSG.LocalCores.map_map_symm]
  have hcomm : L0 = ⁅L0, E1.barRad ↥K A0⁆ := by
    have h1 : (⁅L, B⁆).map e.symm.toMonoidHom = L.map e.symm.toMonoidHom := by
      rw [hAS.commutator_eq hB]
    rw [Subgroup.map_commutator, hbar_symm] at h1
    exact h1.symm
  have hL0comp : CFSG.IsComponent L0 :=
    CFSG.LocalCores.isComponent_map_mulEquiv e.symm hAS.isComponent
  have hL0n : L0.Normal := hAS.normal.map e.symm.toMonoidHom e.symm.surjective
  have hL0layer : CFSG.layer (↥K ⧸ CFSG.solvableRadical ↥K) = L0 := by
    rw [← E1.layer_map_mulEquiv e.symm, hAS.layer_eq]
  have hconj : ∀ t : ↥K ⧸ CFSG.solvableRadical ↥K,
      L0.map (MulAut.conj t).toMonoidHom = L0 := fun t =>
    Subgroup.mem_normalizer_iff_map_conj_eq.mp
      ((Subgroup.normalizer_eq_top (h := hL0n)).ge (Subgroup.mem_top t))
  have horbit : CFSG.layer (↥K ⧸ CFSG.solvableRadical ↥K) =
      ⨆ t ∈ ((tA T A).subgroupOf K).map
        (QuotientGroup.mk' (CFSG.solvableRadical ↥K)),
        L0.map (MulAut.conj t).toMonoidHom := by
    rw [hL0layer]
    exact le_antisymm (le_iSup₂_of_le 1 (Subgroup.one_mem _) (hconj 1).ge)
      (iSup₂_le fun t _ => (hconj t).le)
  have hII : ECaseII T A K := by
    obtain ⟨hRclosed, hcore, hresK, -⟩ := hETwo
    exact ⟨hRclosed, hcore, hresK, ⟨L0, hL0comp, horbit, Or.inl hcomm⟩⟩
  have hbarΓ : Nat.card (E1.barRad Γ B) = 2 := by
    have hinj : Function.Injective (QuotientGroup.mk' (CFSG.solvableRadical Γ)) := by
      rw [← MonoidHom.ker_eq_bot_iff, QuotientGroup.ker_mk']
      exact hAS.solvableRadical_eq_bot
    unfold E1.barRad
    rw [Subgroup.card_map_of_injective hinj]
    exact hcard
  have hbarQ : Nat.card (E1.barRad ↥K A0) = 2 := by
    rw [← E1.card_barRad_eq_of_surjective π hπ hks A0]
    exact hbarΓ
  let qe : (↥K ⧸ CFSG.Open.pCore 2 ↥K) ≃* (↥K ⧸ CFSG.solvableRadical ↥K) :=
    QuotientGroup.quotientMulEquivOfEq (hO2Q.trans hR.symm)
  have hbarO2 : (E1.barO2 ↥K A0).map qe.toMonoidHom = E1.barRad ↥K A0 := by
    unfold E1.barO2 E1.barRad
    rw [Subgroup.map_map]
    congr 1
  have hcardMap : Nat.card ((E1.barO2 ↥K A0).map qe.toMonoidHom) =
      Nat.card (E1.barO2 ↥K A0) :=
    Subgroup.card_map_of_injective qe.injective
  have hcardBarO2 : Nat.card (E1.barO2 ↥K A0) = 2 := by
    rw [← hcardMap, hbarO2]
    exact hbarQ
  have hrel : (pCoreOf 2 K).relIndex A = 2 := by
    rw [← card_barO2_subgroupOf_eq hAK]
    exact hcardBarO2
  have hnonmem : ¬ A ≤ pCoreOf 2 K := by
    intro hAP
    have h1 : (pCoreOf 2 K).relIndex A = 1 := Subgroup.relIndex_eq_one.mpr hAP
    omega
  have hm : E3.mQuot A (pCoreOf 2 K) ≤ 1 := by
    have hpow : 2 ^ E3.mQuot A (pCoreOf 2 K) = 2 ^ 1 := by
      rw [pow_one, ← E3.relIndex_eq_two_pow hA.isPGroup (pCoreOf 2 K)]
      exact hrel
    have h1 : E3.mQuot A (pCoreOf 2 K) = 1 :=
      Nat.pow_right_injective (le_refl 2) hpow
    omega
  exact ⟨⟨hτ, CFSG.ABGLocalTools.isSylowOf_iff.mpr hSyl, hnonmem, Or.inr hII⟩, hm⟩

end CFSG.LocalAnalysis.WeakClosure81
