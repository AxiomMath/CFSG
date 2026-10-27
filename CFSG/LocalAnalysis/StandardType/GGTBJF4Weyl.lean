module

public import CFSG.LieType.Chevalley.KernelComponentRoots
public import CFSG.LieType.Chevalley.SignKernelComponentBorel
public import CFSG.LieType.Chevalley.CLSOddE7RationalEightGroup
public import CFSG.LieType.Chevalley.E6ToralGraphInvolution
public import CFSG.LieType.Chevalley.ToralCentralizerBruhat
public import CFSG.LieType.Chevalley.TorusCoordinates

public section

namespace CFSG.StandardType

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open CFSG.LieType.Steinberg.Adjoint

private theorem ggTBJ_rootChar_mul_zpow_aux {K : Type} [Field K] {τ : Tag}
    (c : Fin τ.rank → Kˣ) (k : Fin τ.rank) (u : Fin τ.rank → ℤ) :
    rootChar (fun j => c j * c k ^ (-τ.cartan k j)) u =
      rootChar c u * c k ^ (-(∑ j, τ.cartan k j * u j)) := by
  have hprod : ∏ j, (c k ^ (-τ.cartan k j)) ^ u j =
      c k ^ (-(∑ j, τ.cartan k j * u j)) := by
    rw [Finset.prod_congr rfl fun j _ => (zpow_mul (c k) (-τ.cartan k j) (u j)).symm]
    rw [prod_zpow_eq_zpow_sum]
    congr 1
    rw [Finset.sum_congr rfl fun j _ => neg_mul (τ.cartan k j) (u j)]
    rw [Finset.sum_neg_distrib]
  simp only [rootChar]
  rw [Finset.prod_congr rfl fun j _ => mul_zpow (c j) (c k ^ (-τ.cartan k j)) (u j)]
  rw [Finset.prod_mul_distrib, hprod]

private theorem ggTBJ_conj_weylElt_rootDiagUnit_aux
    {K : Type} [Field K] {τ : Tag} (w : WeylGroup τ)
    (k : Fin τ.rank) {β : Fin τ.rank → ℤ}
    (hwk : w • (Pi.single k 1 : Fin τ.rank → ℤ) = β) (b : Fin τ.rank → Kˣ) :
    canonicalRep (coxeterSystem τ) K w * weylElt τ K k 1 *
        (canonicalRep (coxeterSystem τ) K w)⁻¹ * rootDiagUnit τ b *
        (canonicalRep (coxeterSystem τ) K w * weylElt τ K k 1 *
          (canonicalRep (coxeterSystem τ) K w)⁻¹)⁻¹ =
      rootDiagUnit τ (fun i => b i * rootChar b β ^ (-(corootPair β (Pi.single i 1)))) := by
  classical
  set nw : ModGL τ K := canonicalRep (coxeterSystem τ) K w with hnw
  set c : Fin τ.rank → Kˣ := weylTuple w⁻¹ b with hc
  set c' : Fin τ.rank → Kˣ := fun j => c j * c k ^ (-τ.cartan k j) with hc'
  have hweyl : weylTuple w c = b := by
    rw [hc, weylTuple_weylTuple, mul_inv_cancel, weylTuple_one]
  have hD : nw⁻¹ * rootDiagUnit τ b * nw = rootDiagUnit τ c := by
    have h := canonicalRep_conj_rootDiagUnit (τ := τ) w c
    rw [← hnw] at h
    rw [hweyl] at h
    rw [← h]
    group
  have hE : weylElt τ K k 1 * rootDiagUnit τ c * (weylElt τ K k 1)⁻¹ = rootDiagUnit τ c' := by
    rw [hc']
    exact weylElt_conj_rootDiagUnit c k
  have hN : nw * rootDiagUnit τ c' * nw⁻¹ = rootDiagUnit τ (weylTuple w c') := by
    have h := canonicalRep_conj_rootDiagUnit (τ := τ) w c'
    rw [← hnw] at h
    exact h
  have hmain : nw * weylElt τ K k 1 * nw⁻¹ * rootDiagUnit τ b *
      (nw * weylElt τ K k 1 * nw⁻¹)⁻¹ = rootDiagUnit τ (weylTuple w c') := by
    calc nw * weylElt τ K k 1 * nw⁻¹ * rootDiagUnit τ b *
          (nw * weylElt τ K k 1 * nw⁻¹)⁻¹
        = nw * (weylElt τ K k 1 * (nw⁻¹ * rootDiagUnit τ b * nw) *
            (weylElt τ K k 1)⁻¹) * nw⁻¹ := by group
      _ = nw * (weylElt τ K k 1 * rootDiagUnit τ c * (weylElt τ K k 1)⁻¹) * nw⁻¹ := by
            rw [hD]
      _ = nw * rootDiagUnit τ c' * nw⁻¹ := by rw [hE]
      _ = rootDiagUnit τ (weylTuple w c') := hN
  rw [hmain]
  have hB' : weylTuple w c' =
      fun i => b i * rootChar b β ^ (-(corootPair β (Pi.single i 1))) := by
    rw [hc']
    funext i
    change rootChar (fun j => c j * c k ^ (-τ.cartan k j))
        (w⁻¹ • (Pi.single i 1 : Fin τ.rank → ℤ)) =
      b i * rootChar b β ^ (-(corootPair β (Pi.single i 1)))
    rw [ggTBJ_rootChar_mul_zpow_aux]
    have h1 : rootChar c (w⁻¹ • (Pi.single i 1 : Fin τ.rank → ℤ)) = b i := by
      rw [hc, rootChar_weylTuple, inv_inv, smul_inv_smul]
      simpa using rootChar_nsmul_single b i 1
    have h2 : ∑ j, τ.cartan k j * (w⁻¹ • (Pi.single i 1 : Fin τ.rank → ℤ)) j =
        corootPair β (Pi.single i 1) := by
      have h := corootPair_smul_single (τ := τ) w k (Pi.single i 1 : Fin τ.rank → ℤ)
      rw [hwk] at h
      exact h.symm
    have h3 : c k = rootChar b β := by
      rw [hc]
      change rootChar b ((w⁻¹)⁻¹ • (Pi.single k 1 : Fin τ.rank → ℤ)) = rootChar b β
      rw [inv_inv, hwk]
    rw [h1, h2, h3]
  rw [hB']

private theorem ggTBJ_corootPair_expand_aux
    {τ : Tag}
    {β : Fin τ.rank → ℤ} (hβ : IsRoot τ β) (v : Fin τ.rank → ℤ) :
    corootPair β v = ∑ i : Fin τ.rank, v i * corootPair β (Pi.single i 1) := by
  classical
  have hv : v = ∑ i, v i • (Pi.single i 1 : Fin τ.rank → ℤ) := by
    ext j
    simp [Finset.sum_apply, Pi.single_apply]
  have hlin : iform β v = ∑ i, v i * iform β (Pi.single i 1 : Fin τ.rank → ℤ) := by
    conv_lhs => rw [hv]
    rw [iform_finset_sum_right]
    exact Finset.sum_congr rfl fun i _ => by rw [iform_smul_right]
  have hpos : iform β β ≠ 0 := (iform_self_pos_of_isRoot hβ).ne'
  apply mul_right_cancel₀ hpos
  rw [corootPair_mul hβ v, hlin]
  have hR : (∑ i : Fin τ.rank, v i * corootPair β (Pi.single i 1)) * iform β β =
      ∑ i : Fin τ.rank, v i * (2 * iform β (Pi.single i 1)) := by
    rw [Finset.sum_mul]
    exact Finset.sum_congr rfl fun i _ => by
      rw [mul_assoc, corootPair_mul hβ (Pi.single i 1)]
  rw [hR, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => by ring

theorem ggTBJ_exists_weylElt
    (τ : Tag) {K : Type} [Field K] {β : Fin τ.rank → ℤ}
    (hβ : IsRoot τ β) :
    ∃ n : ModGL τ K, n ∈ rootSpan τ K ({β, -β} : Set (Fin τ.rank → ℤ)) ∧
      ∀ b : Fin τ.rank → Kˣ, n * rootDiagUnit τ b * n⁻¹ =
        rootDiagUnit τ (fun i => b i * rootChar b β ^ (-(corootPair β (Pi.single i 1)))) := by
  classical
  obtain ⟨w, k, hwk⟩ := isRoot_iff_exists_smul_single.1 hβ
  set nw : ModGL τ K := canonicalRep (coxeterSystem τ) K w with hnw
  refine ⟨nw * weylElt τ K k 1 * nw⁻¹, ?_, ?_⟩
  · have hpos : β ∈ ({β, -β} : Set (Fin τ.rank → ℤ)) := by simp
    have hneg : -β ∈ ({β, -β} : Set (Fin τ.rank → ℤ)) := by simp
    have hx : ∀ c : K, nw * xUnit τ K k c * nw⁻¹ ∈
        rootSpan τ K ({β, -β} : Set (Fin τ.rank → ℤ)) := by
      intro c
      have h := canonicalRep_conj_mem_rootSpan_singleton w (isRoot_single τ k)
        (xUnit_mem_rootSpan_single k c)
      rw [← hnw] at h
      rw [hwk] at h
      exact rootSpan_mono (Set.singleton_subset_iff.2 hpos) h
    have hy : ∀ c : K, nw * yUnit τ K k c * nw⁻¹ ∈
        rootSpan τ K ({β, -β} : Set (Fin τ.rank → ℤ)) := by
      intro c
      have h := canonicalRep_conj_mem_rootSpan_singleton w (isRoot_neg_single τ k)
        (yUnit_mem_rootSpan_neg_single k c)
      rw [← hnw] at h
      rw [smul_neg, hwk] at h
      exact rootSpan_mono (Set.singleton_subset_iff.2 hneg) h
    have e : weylElt τ K k (1 : Kˣ) =
        xUnit τ K k (1 : Kˣ) * yUnit τ K k (-(((1 : Kˣ)⁻¹ : Kˣ) : K)) *
          xUnit τ K k (1 : Kˣ) := Units.ext rfl
    have e' : nw * weylElt τ K k (1 : Kˣ) * nw⁻¹ =
        (nw * xUnit τ K k (1 : Kˣ) * nw⁻¹) *
          (nw * yUnit τ K k (-(((1 : Kˣ)⁻¹ : Kˣ) : K)) * nw⁻¹) *
          (nw * xUnit τ K k (1 : Kˣ) * nw⁻¹) := by
      rw [e]
      group
    rw [e']
    exact mul_mem (mul_mem (hx _) (hy _)) (hx _)
  · intro b
    rw [hnw]
    exact ggTBJ_conj_weylElt_rootDiagUnit_aux w k hwk b

theorem ggTBJ_corootPair_expand
    (τ : Tag) {β : Fin τ.rank → ℤ} (hβ : IsRoot τ β)
    (v : Fin τ.rank → ℤ) :
    corootPair β v = ∑ i : Fin τ.rank, v i * corootPair β (Pi.single i 1) := by
  exact ggTBJ_corootPair_expand_aux hβ v

end CFSG.StandardType

end
