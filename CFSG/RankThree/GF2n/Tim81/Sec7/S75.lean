module

public import CFSG.RankThree.GF2n.Tim81.Sec7.Stmts
import CFSG.RankThree.GF2n.Tim81.Sec7.Transport
import CFSG.RankThree.GF2n.Tim81.Sec7.Images
import CFSG.GroupTheory.InvariantSubgroup

public section

namespace CFSG.RankThree.GF2n.Tim81

open CFSG CFSG.CGT.Timmesfeld75 CFSG.RankThree.GF2n CFSG.RankThree.GF2n.Tim78
open CFSG.Timmesfeld.ARS
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {M V : Subgroup G} {n f : ℕ}

private theorem map_conjSub_mul_inv {H K : Type*} [Group H] [Group K] (f : H →* K)
    (A : Subgroup H) (x y : H) :
    (conjSub A x).map f = conjSubgroup (f x * (f y)⁻¹) ((conjSub A y).map f) := by
  change (conjSubgroup x A).map f =
    conjSubgroup (f x * (f y)⁻¹) ((conjSubgroup y A).map f)
  rw [← CFSG.GroupTheory.map_conjSubgroup f A x,
    ← CFSG.GroupTheory.map_conjSubgroup f A y]
  rw [conjSubgroup_conjSubgroup]
  congr 1
  group

theorem Sec7Hyp.exists_conj_of_sup_eq (hS : Sec7Hyp M V n f) {S : Set (Subgroup G)}
    (hSsub : S ⊆ sigmaSet M V) {D₀ : Subgroup G} (hD₀ : D₀ ∈ S)
    (hinv : ∀ y ∈ (⨆ D ∈ S, D), ∀ D ∈ S, conjSubgroup y D ∈ S)
    (hsup : (⨆ D ∈ S, D) ⊔ Pc M V = m0Of M V) :
    ∀ U ∈ sigmaSet M V, ∃ D ∈ S, ∃ p ∈ Pc M V, U = conjSubgroup p D := by
  intro U hU
  obtain ⟨Φ, -, hrange, hclass⟩ := hS.m0
  have hUimg : imgQ M U ∈ imgQ M '' sigmaSet M V := ⟨U, hU, rfl⟩
  have hDimg : imgQ M D₀ ∈ imgQ M '' sigmaSet M V := ⟨D₀, hSsub hD₀, rfl⟩
  obtain ⟨x₁, hx₁⟩ := (hclass (imgQ M U)).mp hUimg
  obtain ⟨x₀, hx₀⟩ := (hclass (imgQ M D₀)).mp hDimg
  have hrel : imgQ M U = conjSubgroup (Φ (x₁ * x₀⁻¹)) (imgQ M D₀) := by
    rw [hx₁, hx₀]
    simpa only [map_mul, map_inv] using map_conjSub_mul_inv Φ _ x₁ x₀
  have hYleM : (⨆ D ∈ S, D) ≤ M :=
    iSup₂_le fun D hD => (hS.sec5.le_M_of_mem_sigmaSet (hSsub hD)).1
  have hYimg : imgQ M (m0Of M V) = imgQ M (⨆ D ∈ S, D) := by
    rw [← hsup, Sec6Hyp.imgQ_sup_Pc hS.toSec6Hyp hYleM]
  have hz : Φ (x₁ * x₀⁻¹) ∈ imgQ M (⨆ D ∈ S, D) := by
    rw [← hYimg, ← hrange]
    exact MonoidHom.mem_range.mpr ⟨x₁ * x₀⁻¹, rfl⟩
  obtain ⟨x, hxY, hxz⟩ := mem_imgQ_iff.mp hz
  have hDmem : conjSubgroup (x : G) D₀ ∈ S := hinv (x : G) hxY D₀ hD₀
  have himg : imgQ M (conjSubgroup (x : G) D₀) =
      conjSubgroup (Φ (x₁ * x₀⁻¹)) (imgQ M D₀) := by
    rw [imgQ_conjSubgroup x D₀, hxz]
  have himgU : imgQ M U = imgQ M (conjSubgroup (x : G) D₀) := by
    rw [hrel, himg]
  have hUM : U ≤ M := (hS.sec5.le_M_of_mem_sigmaSet hU).1
  have hle : U ≤ conjSubgroup (x : G) D₀ ⊔ Pc M V :=
    hS.toSec6Hyp.le_sup_Pc_of_imgQ_le hUM (by rw [himgU])
  have hUbot : U ≠ ⊥ := by
    obtain ⟨g, hUeq, -⟩ := hU
    rw [hUeq]
    exact fun h => hS.sec5.toRootHyp.toHyp.ne_bot (conjSubgroup_eq_bot_iff.mp h)
  have hne : U ⊓ (conjSubgroup (x : G) D₀ ⊔ Pc M V) ≠ ⊥ := by
    rw [inf_eq_left.mpr hle]
    exact hUbot
  obtain ⟨p, hp, hUp⟩ :=
    hS.res.s55 M V hS.sec5 (conjSubgroup (x : G) D₀) (hSsub hDmem) U hU hne
  exact ⟨conjSubgroup (x : G) D₀, hDmem, p, hp, hUp⟩

theorem Sec6Hyp.sup_Pc_eq_of_isL2Gen (hS : Sec6Hyp M V) (h74 : Sec7.Stmt74 M V)
    {C A : Subgroup G} (hC : C ∈ sigmaSet M V) (hA : A ∈ sigmaAt C) (hVA : IsL2Gen V A) :
    (⨆ D ∈ sigmaAt V ∩ sigmaAt A, D) ⊔ Pc M V = m0Of M V := by
  obtain ⟨c, hCeq, hHc⟩ := hC
  subst hCeq
  have hHyp : Hyp M V := hS.sec5.toRootHyp.toHyp
  have hA' : A ∈ sigmaSet (conjSubgroup c M) (conjSubgroup c V) :=
    (Hyp.sigmaAt_conj hHyp c) ▸ hA
  have hV' : V ∈ sigmaSet (conjSubgroup c M) (conjSubgroup c V) :=
    (hS.sec5.mem_sigmaSet_iff_self_mem).mp ⟨c, rfl, hHc⟩
  have hVeq : V = conjSubgroup c⁻¹ (conjSubgroup c V) := by
    rw [conjSubgroup_conjSubgroup, inv_mul_cancel, conjSubgroup_one]
  obtain ⟨h1, -, h3⟩ := h74.conj hS.sec5 c V A c⁻¹ hVeq hV' hA' hVA
  rw [← h1]
  rw [show Pc M V =
        conjSubgroup c⁻¹ (Pc (conjSubgroup c M) (conjSubgroup c V)) by
      rw [Pc_conjSubgroup, conjSubgroup_conjSubgroup, inv_mul_cancel, conjSubgroup_one],
    show m0Of M V =
        conjSubgroup c⁻¹ (m0Of (conjSubgroup c M) (conjSubgroup c V)) by
      rw [m0Of_conjSubgroup c, conjSubgroup_conjSubgroup, inv_mul_cancel,
        conjSubgroup_one]]
  exact h3

theorem Sec7Hyp.mem_gammaAt_of_isL2Gen (hS : Sec7Hyp M V n f) (h74 : Sec7.Stmt74 M V)
    {C A U : Subgroup G} (hC : C ∈ sigmaSet M V) (hA : A ∈ sigmaAt C) (hVA : IsL2Gen V A)
    (hU : U ∈ sigmaSet M V) : A ∈ gammaAt U := by
  have hCω : C ∈ omegaSet V := sigmaSet_subset_omegaSet M V hC
  have hAω : A ∈ omegaSet V := sigmaAt_subset_omegaSet hCω hA
  have hVω : V ∈ omegaSet V := ⟨1, Subgroup.mem_top 1, (conjSubgroup_one V).symm⟩
  have hCV : C ∈ sigmaAt V := by
    rwa [hS.sec5.toRootHyp.toHyp.sigmaAt_eq]
  have hCA : C ∈ sigmaAt A := hS.sec5.mem_sigmaAt_symm hCω hA
  let S : Set (Subgroup G) := sigmaAt V ∩ sigmaAt A
  have hCS : C ∈ S := ⟨hCV, hCA⟩
  have hSsub : S ⊆ sigmaSet M V := by
    intro D hD
    rw [← hS.sec5.toRootHyp.toHyp.sigmaAt_eq]
    exact hD.1
  have hYle : (⨆ D ∈ S, D) ≤
      Subgroup.normalizer (V : Set G) ⊓ Subgroup.normalizer (A : Set G) := by
    refine iSup₂_le fun D hD => le_inf ?_ ?_
    · exact (hS.sec5.le_of_mem_sigmaAt hVω hD.1).1
    · exact (hS.sec5.le_of_mem_sigmaAt hAω hD.2).1
  have hinv : ∀ y ∈ (⨆ D ∈ S, D), ∀ D ∈ S, conjSubgroup y D ∈ S := by
    intro y hy D hD
    refine ⟨hS.sec5.conj_mem_sigmaAt hVω (hYle hy).1 hD.1,
      hS.sec5.conj_mem_sigmaAt hAω (hYle hy).2 hD.2⟩
  have hsup := hS.toSec6Hyp.sup_Pc_eq_of_isL2Gen h74 hC hA hVA
  obtain ⟨D, hD, p, hp, hUeq⟩ := hS.exists_conj_of_sup_eq hSsub hCS hinv hsup U hU
  have hAD : A ∈ sigmaAt D := hS.sec5.mem_sigmaAt_symm hAω hD.2
  by_cases hDU : D = U
  · have hADU : A ∈ sigmaAt U := hDU ▸ hAD
    exact hS.toSec6Hyp.sigmaAt_subset_gammaAt (sigmaSet_subset_omegaSet M V hU) hADU
  · have hDp : D ∈ sigmaAt U := by
      rw [hUeq]
      refine hS.mem_sigmaAt_conj_of_mem_Pc (hSsub hD) hp ?_
      intro h
      exact hDU (hUeq.trans h).symm
    exact ⟨D, hDp, hAD⟩

theorem Sec7Hyp.mem_gammaAt_of_mem_sigmaSet (hS : Sec7Hyp M V n f) (h74 : Sec7.Stmt74 M V)
    {A U : Subgroup G} (hA : A ∈ gammaAt V) (hU : U ∈ sigmaSet M V) : A ∈ gammaAt U := by
  obtain ⟨C, hC, hAC⟩ := hA
  have hCsig : C ∈ sigmaSet M V := by
    rwa [hS.sec5.toRootHyp.toHyp.sigmaAt_eq] at hC
  have hCω : C ∈ omegaSet V := sigmaSet_subset_omegaSet M V hCsig
  by_cases hAsig : A ∈ sigmaSet M V
  · refine ⟨V, hS.sec5.self_mem_sigmaAt hU, ?_⟩
    rwa [hS.sec5.toRootHyp.toHyp.sigmaAt_eq]
  · by_cases hAV : A = V
    · rw [hAV]
      exact hS.toSec6Hyp.sigmaAt_subset_gammaAt (sigmaSet_subset_omegaSet M V hU)
        (hS.sec5.self_mem_sigmaAt hU)
    · have hVC : V ∈ sigmaAt C := hS.sec5.self_mem_sigmaAt hCsig
      rcases hS.toSec6Hyp.commute_or_isL2Gen_at hCω hVC hAC with hcomm | hL2
      · exact absurd (by
          rw [← hS.sec5.toRootHyp.toHyp.sigmaAt_eq]
          exact hS.toSec6Hyp.mem_sigmaAt_of_commute_at hCω hVC hAC hcomm (Ne.symm hAV))
          hAsig
      · exact hS.mem_gammaAt_of_isL2Gen h74 hCsig hAC hL2 hU

theorem Sec7Hyp.gammaAt_subset_of_mem_sigmaAt (hS : Sec7Hyp M V n f) (h74 : Sec7.Stmt74 M V)
    {X U : Subgroup G} (hX : X ∈ omegaSet V) (hU : U ∈ sigmaAt X) :
    gammaAt X ⊆ gammaAt U := by
  have hVω : V ∈ omegaSet V := ⟨1, Subgroup.mem_top 1, (conjSubgroup_one V).symm⟩
  have hHyp : Hyp M V := hS.sec5.toRootHyp.toHyp
  obtain ⟨x, -, rfl⟩ := hX
  intro A hA
  have hAx : conjSubgroup x⁻¹ A ∈ gammaAt V :=
    (Hyp.mem_gammaAt_conj_iff hHyp hVω x).mp hA
  have hUx : conjSubgroup x⁻¹ U ∈ sigmaSet M V := by
    rw [← hHyp.sigmaAt_eq]
    exact (Hyp.mem_sigmaAt_conj_iff hHyp hVω x).mp hU
  have hmem : conjSubgroup x⁻¹ A ∈ gammaAt (conjSubgroup x⁻¹ U) :=
    hS.mem_gammaAt_of_mem_sigmaSet h74 hAx hUx
  have hUxω : conjSubgroup x⁻¹ U ∈ omegaSet V :=
    sigmaSet_subset_omegaSet M V hUx
  have hback : A ∈ gammaAt (conjSubgroup x (conjSubgroup x⁻¹ U)) :=
    (Hyp.mem_gammaAt_conj_iff hHyp hUxω x).mpr hmem
  have hUeq : conjSubgroup x (conjSubgroup x⁻¹ U) = U := by
    rw [conjSubgroup_conjSubgroup, mul_inv_cancel, conjSubgroup_one]
  rwa [hUeq] at hback

theorem Sec7Hyp.gammaAt_eq_of_mem_sigmaAt (hS : Sec7Hyp M V n f) (h74 : Sec7.Stmt74 M V)
    {X U : Subgroup G} (hX : X ∈ omegaSet V) (hU : U ∈ sigmaAt X) :
    gammaAt U = gammaAt X := by
  have hUω : U ∈ omegaSet V := sigmaAt_subset_omegaSet hX hU
  have hXU : X ∈ sigmaAt U := hS.sec5.mem_sigmaAt_symm hX hU
  exact le_antisymm (hS.gammaAt_subset_of_mem_sigmaAt h74 hUω hXU)
    (hS.gammaAt_subset_of_mem_sigmaAt h74 hX hU)

theorem Sec7Hyp.stmt75 (hS : Sec7Hyp M V n f) (h74 : Sec7.Stmt74 M V) : Sec7.Stmt75 V := by
  intro A hA
  obtain ⟨C, hC, hAC⟩ := hA
  have hCsig : C ∈ sigmaSet M V := by
    rwa [hS.sec5.toRootHyp.toHyp.sigmaAt_eq] at hC
  have hCω : C ∈ omegaSet V := sigmaSet_subset_omegaSet M V hCsig
  have hVω : V ∈ omegaSet V := ⟨1, Subgroup.mem_top 1, (conjSubgroup_one V).symm⟩
  calc gammaAt A = gammaAt C := hS.gammaAt_eq_of_mem_sigmaAt h74 hCω hAC
    _ = gammaAt V := hS.gammaAt_eq_of_mem_sigmaAt h74 hVω hC

end CFSG.RankThree.GF2n.Tim81
