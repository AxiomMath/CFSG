module

public import CFSG.LocalAnalysis.SeitzReduction.UnitaryPilotAlignImages
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotWeakCT

public section

namespace CFSG.SeitzReduction.UnitaryPilot

open Subgroup CFSG.LocalAnalysis.ComponentInitial CFSG.ClassicalGroups.UnitaryFlag
open CFSG.Quasithin (perfectCore)
open CFSG.SeitzReduction.F4Pilot (centralizerPerfectCore)
open CFSG.SeitzReduction.LinearPilot (blockSpecialLinear blockSpecialLinear_mono)
open scoped MatrixGroups

section Pair

variable {G : Type*} [Group G] {L : Subgroup G} {m f : ℕ} {K : Type} [Field K]
  {h : UnitaryFieldData 2 f K} {e : L ≃* unitaryPSU h (m + 1)} {t : G} {X : Subgroup G}
  {N : Finset (Fin (m + 1))}

theorem exists_theta_of_graphFieldNeighbourParam [Finite G]
    (P : GraphFieldNeighbourParam e t X N) (i j : Fin m) (hj : (j : ℕ) = i + 1)
    (hN : ({i.castSucc, i.succ} : Finset (Fin (m + 1))) ∪ {j.castSucc, j.succ} ⊆ N)
    (hNc : 2 ≤ Nᶜ.card)
    (hX : X ≤ modelToG e (unitaryBlockTorus h
      (({i.castSucc, i.succ} : Finset (Fin (m + 1))) ∪ {j.castSucc, j.succ}))) :
    ∃ θ : SL(3, K) →* G, θ.ker ≤ center SL(3, K) ∧
      (CFSG.ClassicalInvolution.WeakCT.B12 K).map θ =
        pieceCore e ({i.castSucc, i.succ} : Finset (Fin (m + 1))) ∧
      (CFSG.ClassicalInvolution.WeakCT.B23 K).map θ =
        pieceCore e ({j.castSucc, j.succ} : Finset (Fin (m + 1))) ∧
      θ.range = pieceCore e
        (({i.castSucc, i.succ} : Finset (Fin (m + 1))) ∪ {j.castSucc, j.succ}) := by
  have hm : (i : ℕ) + 1 < m := by have := j.isLt; omega
  let β : SL(3, K) →* blockSpecialLinear (K := K) N :=
    (CFSG.ClassicalInvolution.WeakCT.blockSL3 K m i hm).codRestrict (blockSpecialLinear N)
      (fun A => blockSpecialLinear_mono hN (LinearPilot.range_blockSL3_le m i j hj hm ⟨A, rfl⟩))
  have hβ : ∀ A, ((β A : blockSpecialLinear (K := K) N) : SL(m + 1, K)) =
      CFSG.ClassicalInvolution.WeakCT.blockSL3 K m i hm A := fun A => rfl
  have hβinj : Function.Injective β := fun A B hAB =>
    CFSG.ClassicalInvolution.WeakCT.blockSL3_injective m i hm (by rw [← hβ, ← hβ, hAB])
  have hmapβ : ∀ (H : Subgroup SL(3, K)) (I : Finset (Fin (m + 1))),
      H.map (CFSG.ClassicalInvolution.WeakCT.blockSL3 K m i hm) = blockSpecialLinear (K := K) I →
      H.map β = (blockSpecialLinear (K := K) I).subgroupOf (blockSpecialLinear N) := by
    intro H I hHI
    ext x
    rw [mem_map, mem_subgroupOf, ← hHI, mem_map]
    constructor
    · rintro ⟨A, hA, rfl⟩
      exact ⟨A, hA, rfl⟩
    · rintro ⟨A, hA, hAx⟩
      exact ⟨A, hA, Subtype.ext hAx⟩
  have hpiece : ∀ I : Finset (Fin (m + 1)),
      I ⊆ ({i.castSucc, i.succ} : Finset (Fin (m + 1))) ∪ {j.castSucc, j.succ} → 2 ≤ I.card →
      pieceCore e I =
        ((blockSpecialLinear (K := K) I).subgroupOf (blockSpecialLinear N)).map P.Φ :=
    fun I hIS hI2 => P.pieceCore_eq_map_of_compl (hIS.trans hN) hI2 hNc
      (hX.trans (modelToG_mono e (unitaryBlockTorus_anti h hIS)))
  refine ⟨P.Φ.comp β, ?_, ?_, ?_, ?_⟩
  · intro A hA
    have hz : β A ∈ center (blockSpecialLinear (K := K) N) := P.ker_le hA
    rw [mem_center_iff] at hz ⊢
    intro B
    apply hβinj
    rw [map_mul, map_mul, hz (β B)]
  · rw [← map_map,
      hmapβ _ _ ((CFSG.ClassicalInvolution.WeakCT.map_B12_blockSL3 (K := K) m i hm).trans
        (LinearPilot.range_blockSL2_eq m i)),
      hpiece _ Finset.subset_union_left (LinearPilot.card_nodePair i).ge]
  · have hji : (⟨(i : ℕ) + 1, hm⟩ : Fin m) = j := Fin.ext hj.symm
    have hB23 := CFSG.ClassicalInvolution.WeakCT.map_B23_blockSL3 (K := K) m i hm
    rw [hji] at hB23
    rw [← map_map, hmapβ _ _ (hB23.trans (LinearPilot.range_blockSL2_eq m j)),
      hpiece _ Finset.subset_union_right (LinearPilot.card_nodePair j).ge]
  · have hτ : (⊤ : Subgroup SL(3, K)).map (CFSG.ClassicalInvolution.WeakCT.blockSL3 K m i hm) =
        blockSpecialLinear (K := K)
          (({i.castSucc, i.succ} : Finset (Fin (m + 1))) ∪ {j.castSucc, j.succ}) := by
      rw [← MonoidHom.range_eq_map, ← LinearPilot.consecutiveBlock_three i j hj]
      exact LinearPilot.range_blockSL_eq _
    have hτ2 : 2 ≤ (({i.castSucc, i.succ} : Finset (Fin (m + 1))) ∪ {j.castSucc, j.succ}).card :=
      (LinearPilot.card_nodePair i).symm.le.trans (Finset.card_le_card Finset.subset_union_left)
    rw [MonoidHom.range_eq_map, ← map_map, hmapβ _ _ hτ, hpiece _ subset_rfl hτ2]

end Pair

section Recognition

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {m f : ℕ} {K : Type} [Field K]
  {h : UnitaryFieldData 2 f K} {e : L ≃* unitaryPSU h (m + 1)} {t : G}

theorem exists_weakCT_of_graphFieldNeighbourCover (hm : 3 ≤ m)
    (hcov : GraphFieldNeighbourCover e t 3)
    (hcomm : ∀ i j : Fin m, (i : ℕ) + 1 < j →
      pieceCore e ({i.castSucc, i.succ} : Finset (Fin (m + 1))) ≤
        centralizer (pieceCore e ({j.castSucc, j.succ} : Finset (Fin (m + 1))) : Set G))
    {G₀ : Subgroup G}
    (hG₀ : G₀ = ⨆ i : Fin m, pieceCore e ({i.castSucc, i.succ} : Finset (Fin (m + 1)))) :
    ∃ ψ : SL(m + 1, K) →* G₀, Function.Surjective ψ ∧ ψ.ker ≤ center SL(m + 1, K) ∧
      (∀ i : Fin m,
        (blockSpecialLinear (K := K) ({i.castSucc, i.succ} : Finset (Fin (m + 1)))).map ψ =
          (pieceCore e ({i.castSucc, i.succ} : Finset (Fin (m + 1)))).subgroupOf G₀) ∧
      CFSG.IsQuasisimple G₀ ∧
      CFSG.Blueprint.LieModel (G₀ ⧸ center G₀) CFSG.Assembly.LowTwoRank.StatedLieTag.PSL
        (m + 1) 2 (2 * f) := by
  have := h.finite
  have hF4 : 4 ≤ Nat.card K := four_le_card_of_unitaryFieldData h
  have hle : ∀ i : Fin m, pieceCore e ({i.castSucc, i.succ} : Finset (Fin (m + 1))) ≤ G₀ :=
    fun i => hG₀ ▸ le_iSup (fun i : Fin m =>
      pieceCore e ({i.castSucc, i.succ} : Finset (Fin (m + 1)))) i
  have hUmap : ∀ i : Fin m,
      ((pieceCore e ({i.castSucc, i.succ} : Finset (Fin (m + 1)))).subgroupOf G₀).map
        G₀.subtype = pieceCore e ({i.castSucc, i.succ} : Finset (Fin (m + 1))) := fun i => by
    rw [subgroupOf_map_subtype, inf_eq_left.mpr (hle i)]
  have hcomm' : ∀ i j : Fin m, (i : ℕ) + 1 < j →
      ∀ x ∈ (pieceCore e ({i.castSucc, i.succ} : Finset (Fin (m + 1)))).subgroupOf G₀,
      ∀ y ∈ (pieceCore e ({j.castSucc, j.succ} : Finset (Fin (m + 1)))).subgroupOf G₀,
        x * y = y * x := by
    intro i j hij x hx y hy
    have h1 := mem_centralizer_iff.1 (hcomm i j hij (mem_subgroupOf.1 hx)) (y : G)
      (mem_subgroupOf.1 hy)
    exact Subtype.ext h1.symm
  have hpair : ∀ i j : Fin m, (j : ℕ) = i + 1 →
      ∃ W, CFSG.ClassicalInvolution.WeakCT.LinearBlockStandardPair K W
        ((pieceCore e ({i.castSucc, i.succ} : Finset (Fin (m + 1)))).subgroupOf G₀)
        ((pieceCore e ({j.castSucc, j.succ} : Finset (Fin (m + 1)))).subgroupOf G₀) := by
    intro i j hj
    obtain ⟨X, N, hSN, hNc, hX, ⟨P⟩⟩ := hcov _ (LinearPilot.card_union_nodePair_adjacent_le i j hj)
    obtain ⟨θ, hθker, hθ12, hθ23, -⟩ :=
      exists_theta_of_graphFieldNeighbourParam P i j hj hSN hNc hX
    have hθG₀ : ∀ A, θ A ∈ G₀ := by
      intro A
      have hA : θ A ∈ θ.range := ⟨A, rfl⟩
      rw [MonoidHom.range_eq_map, ← CFSG.ClassicalInvolution.WeakCT.B12_sup_B23 (K := K),
        Subgroup.map_sup, hθ12, hθ23] at hA
      exact sup_le (hle i) (hle j) hA
    let θ' : SL(3, K) →* G₀ := θ.codRestrict G₀ hθG₀
    have hθθ' : G₀.subtype.comp θ' = θ := MonoidHom.ext fun _ => rfl
    have hθ' : ∀ H : Subgroup SL(3, K), (H.map θ').map G₀.subtype = H.map θ := fun H => by
      rw [map_map, hθθ']
    refine ⟨θ'.range, θ', 1, rfl, ?_, Or.inl ⟨?_, ?_⟩⟩
    · rw [MonoidHom.ker_codRestrict]
      exact hθker
    · rw [LinearPilot.map_conj_one_inv_eq]
      apply map_injective G₀.subtype_injective
      rw [hθ', hθ12, hUmap]
    · rw [LinearPilot.map_conj_one_inv_eq]
      apply map_injective G₀.subtype_injective
      rw [hθ', hθ23, hUmap]
  have hgen : ⨆ i : Fin m,
      (pieceCore e ({i.castSucc, i.succ} : Finset (Fin (m + 1)))).subgroupOf G₀ = ⊤ := by
    apply map_injective G₀.subtype_injective
    rw [Subgroup.map_iSup, ← MonoidHom.range_eq_map, range_subtype]
    simp only [hUmap]
    exact hG₀.symm
  obtain ⟨Fam, hFam⟩ := CFSG.ClassicalInvolution.WeakCT.exists_ctFamily_of_pairs hF4
    (by omega) hcomm' hpair
  have hgen' : ⨆ i, (Fam.ι i).range = ⊤ := by
    simp only [fun i => (hFam i).1]
    exact hgen
  have hnt : ∃ i, ∃ A, Fam.ι i A ≠ 1 := by
    obtain ⟨s, hs⟩ := CFSG.ClassicalInvolution.WeakCT.exists_unit_ne_one (K := K) (by omega)
    refine ⟨⟨0, by omega⟩, CFSG.ClassicalInvolution.WeakCT.torusHom K s, fun h' => hs ?_⟩
    apply CFSG.ClassicalInvolution.WeakCT.torusHom_injective
    rw [map_one]
    exact (hFam ⟨0, by omega⟩).2 (h'.trans (map_one _).symm)
  obtain ⟨ψ, hψ, hsurj, hker, hqs, -, hmodel⟩ :=
    CFSG.ClassicalInvolution.WeakCT.exists_recognition hm Nat.prime_two
      (by have := h.one_le; omega : 1 ≤ 2 * f) h.card Fam hgen' hnt
  refine ⟨ψ, hsurj, hker, fun i => ?_, hqs, hmodel⟩
  rw [← LinearPilot.range_blockSL2_eq m i, ← MonoidHom.range_comp, ← (hFam i).1]
  congr 1
  exact MonoidHom.ext fun A => hψ i A

end Recognition

end CFSG.SeitzReduction.UnitaryPilot
