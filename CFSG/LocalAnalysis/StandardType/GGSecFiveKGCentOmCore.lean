module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveKGCentOmPattern

import CFSG.LocalAnalysis.StandardType.GGSecFiveKGCentOmLift
import CFSG.LocalAnalysis.StandardType.GGSecFiveKGCentOmTau
import CFSG.LocalAnalysis.StandardType.GGSecFiveKGCentOmTail
import CFSG.LocalAnalysis.StandardType.GGSecFiveKGCentOmFour
import CFSG.LocalAnalysis.StandardType.GGRootCentKGOTwoOmPlusAut
import CFSG.LocalAnalysis.StandardType.GGRootCentKGOTwoOmPlusAutFour
import CFSG.LocalAnalysis.StandardType.GGSixAutSteinbergTrialityModel

public section

namespace CFSG.StandardType.KGCentOm

open CFSG.LieType.Universal CFSG.LieType.Universal.Spin CFSG.StandardType.KGOm
  CFSG.StandardType.Triality

private theorem xr_mem_rootGroup {K : Type} [Field K] [CharP K 2] {δ : Fin 4 → ℤ}
    (hδ : δ ∈ rootsD4) (b : K) : xr δ b ∈ (plusDatum 4 K three_le_four).rootGroup δ := by
  obtain ⟨i, j, hij, s, t, h, hRG⟩ := exists_plusRootGroup_eq (K := K) three_le_four hδ
  rw [show (plusDatum 4 K three_le_four).rootGroup δ = _ from hRG, xr_eq_longRoot hij h b]
  exact ⟨_, rfl⟩

theorem conj_eq_self_four_of_D3 {K : Type} [Field K] [Finite K] [CharP K 2] {G : Type*}
    [Group G] {D J : Subgroup G} {ψ : Sp8 K →* G} (hψ : Function.Injective ψ)
    (hlift : ∀ d ∈ D, ∃ s ∈ ggTorus (plusDatum 4 K three_le_four),
      ∀ u, d * ψ u * d⁻¹ = ψ (s * u * s⁻¹))
    (hKC1 : ∀ β ∈ rootsD4, (plusDatum 4 K three_le_four).rootGroup β ≤
        (Subgroup.centralizer (D : Set G)).comap ψ →
      ((plusDatum 4 K three_le_four).rootGroup β).map ψ ≤ J)
    {i₀ : Fin 4} (hD3 : ∀ δ ∈ rootsD4, toStdD 4 δ i₀ = 0 →
      (plusDatum 4 K three_le_four).rootGroup δ ≤ (Subgroup.centralizer (D : Set G)).comap ψ)
    {t : G} (ht2 : ∃ m : ℕ, t ^ (2 ^ m) = 1) (htN : t ∈ Subgroup.normalizer (ψ.range : Set G))
    (htD : t ∈ Subgroup.centralizer (D : Set G)) (htJ : t ∈ Subgroup.centralizer (J : Set G)) :
    ∀ k, t * ψ k * t⁻¹ = ψ k := by
  obtain ⟨γ, c, k, ε, τ, hconj, hcA⟩ := exists_conj_tri_of_mem_normalizer hψ htN
  have hfix : ∀ δ ∈ rootsD4, toStdD 4 δ i₀ = 0 → ∀ b : K, γ * c (xr δ b) * γ⁻¹ = xr δ b :=
    fun δ hδ h0 b => eq_self_of_map_le (φ := fun k => γ * c k * γ⁻¹) hψ htJ hconj
      (hKC1 δ hδ (hD3 δ hδ h0)) (xr_mem_rootGroup hδ b)
  have hroot : ∀ {a b : Fin 4} (hab : a ≠ b), a ≠ i₀ → b ≠ i₀ → ∀ s s' : Bool,
      ∃ δ ∈ rootsD4, toStdD 4 δ i₀ = 0 ∧ (plusDatum 4 K three_le_four).rootGroup δ =
        ((plusFrame 4 K three_le_four).longRoot hab s s').range := by
    intro a b hab ha hb s s'
    obtain ⟨δ, hδ, hδs⟩ := exists_mem_rootsD_toStdD_eq 4 hab (boolSign_eq_one_or_eq_neg_one s)
      (boolSign_eq_one_or_eq_neg_one s')
    refine ⟨δ, hδ, ?_, plusRootGroup_eq three_le_four hab s s' hδs⟩
    rw [hδs, Pi.add_apply, Pi.single_eq_of_ne ha.symm, Pi.single_eq_of_ne hb.symm, add_zero]
  obtain ⟨a₁, ha₁, -⟩ := exists_ne_and_ne three_le_four i₀ i₀
  obtain ⟨a₂, ha₂, ha₂₁⟩ := exists_ne_and_ne three_le_four i₀ a₁
  obtain ⟨δ₀, hδ₀, h0, -⟩ := hroot ha₂₁.symm ha₁ ha₂ true true
  have hε : (if ε then refl0 δ₀ else δ₀) ∈ rootsD4 := by
    cases ε
    · exact hδ₀
    · exact refl0_mem_roots hδ₀
  have hτ : τ = 1 := ringEquiv_eq_one_of_conj_xr hδ₀
    (Set.MapsTo.iterate (fun _ h => tri_mem_roots h) k hε) fun b => by
      rw [← hcA δ₀ hδ₀ b]
      exact hfix δ₀ hδ₀ h0 b
  subst hτ
  have hcA1 : ∀ δ ∈ rootsD4, ∀ b : K,
      c (xr δ b) = xr ((⇑tri)^[k] (if ε then refl0 δ else δ)) b :=
    fun δ hδ b => by rw [hcA δ hδ b, RingAut.one_apply]
  obtain ⟨m, rfl⟩ := Nat.dvd_of_mod_eq_zero (mod_three_eq_zero_of_conj_xr hcA1 i₀ hfix)
  have h3 : ∀ v, (⇑tri)^[3 * m] v = v := fun v => by
    rw [Function.iterate_mul, show (⇑tri)^[3] = id from funext tri_tri_tri, Function.iterate_id,
      id_eq]
  have hST := kgcLiftSet_subset_ggTorus three_le_four hψ hlift
  have hfixIdx : ∀ a, a ≠ i₀ → KGCFixedIdx three_le_four (kgcLiftSet ψ D) a := fun a ha => by
    obtain ⟨b, hb, hba⟩ := exists_ne_and_ne three_le_four i₀ a
    refine kgcFixedIdx_of_mem_centralizer three_le_four hψ hST hba.symm fun r => ?_
    obtain ⟨δ, hδ, h0, hRG⟩ := hroot hba.symm ha hb true r
    refine hD3 δ hδ h0 ?_
    rw [hRG]
    exact ⟨_, rfl⟩
  exact conj_eq_self_of_plusSemi_one three_le_four hψ ht2 hconj
    (spinAction_plusSemi_of_conj_xr fun δ hδ b => by rw [hcA1 δ hδ b, h3]) hST
    (fun s hs => conj_eq_of_mem_kgcLiftSet_of_commute three_le_four hψ htN htD hconj hs)
    (fun hij s s' hc b => conj_longRoot_eq_of_forall_lift three_le_four hψ hlift hKC1 htJ hconj
      hij s s' hc b)
    fun ⟨_, _, hu⟩ => ha₂₁ ((hu a₂ (hfixIdx a₂ ha₂)).trans (hu a₁ (hfixIdx a₁ ha₁)).symm)

theorem conj_eq_self_four {K : Type} [Field K] [Finite K] [CharP K 2] {G : Type*} [Group G]
    {p : ℕ} (hp : p.Prime) {D J : Subgroup G} {ψ : Sp8 K →* G} (hψ : Function.Injective ψ)
    (hDp : ∀ d ∈ D, d ^ p = 1)
    (hlift : ∀ d ∈ D, ∃ s ∈ ggTorus (plusDatum 4 K three_le_four),
      ∀ u, d * ψ u * d⁻¹ = ψ (s * u * s⁻¹))
    (hKC1 : ∀ β ∈ rootsD4, (plusDatum 4 K three_le_four).rootGroup β ≤
        (Subgroup.centralizer (D : Set G)).comap ψ →
      ((plusDatum 4 K three_le_four).rootGroup β).map ψ ≤ J)
    (hKC2 : ∃ β ∈ {β | β ∈ rootsD4 ∧ (plusDatum 4 K three_le_four).rootGroup β ≤
        (Subgroup.centralizer (D : Set G)).comap ψ},
      ∃ β' ∈ {β | β ∈ rootsD4 ∧ (plusDatum 4 K three_le_four).rootGroup β ≤
        (Subgroup.centralizer (D : Set G)).comap ψ}, β + β' ∈ rootsD4)
    (hKC2' : Set.ncard (kgcTorusSet three_le_four ψ D p) ≤ p)
    {t : G} (ht2 : ∃ m : ℕ, t ^ (2 ^ m) = 1) (htN : t ∈ Subgroup.normalizer (ψ.range : Set G))
    (htD : t ∈ Subgroup.centralizer (D : Set G)) (htJ : t ∈ Subgroup.centralizer (J : Set G)) :
    ∀ k, t * ψ k * t⁻¹ = ψ k := by
  obtain ⟨j, i₀, hpat⟩ := exists_iterate_tri_le_comap hp hψ hDp hlift hKC2' hKC2
  obtain ⟨θ, hθ⟩ : ∃ θ : MulAut (Sp8 K), θ = triSpinAut ^ j := ⟨_, rfl⟩
  have hmap : ∀ δ ∈ rootsD4, ((plusDatum 4 K three_le_four).rootGroup δ).map θ.toMonoidHom =
      (plusDatum 4 K three_le_four).rootGroup ((⇑tri)^[j] δ) := fun δ hδ =>
    hθ ▸ map_rootGroup_triSpinAut_pow j hδ
  have hθinv : ∀ s, θ (((triSpinAut : MulAut (Sp8 K)) ^ (2 * j)) s) = s := fun s => by
    rw [hθ, ← MulAut.mul_apply, ← pow_add, show j + 2 * j = 3 * j by ring, pow_mul,
      triSpinAut_cube, one_pow, MulAut.one_apply]
  have key := conj_eq_self_four_of_D3 (ψ := ψ.comp θ.toMonoidHom) (hψ.comp θ.injective)
    (fun d hd => by
      obtain ⟨s, hs, hsd⟩ := hlift d hd
      refine ⟨_, triSpinAut_pow_mem_ggTorus (2 * j) hs, fun u => ?_⟩
      have e := hsd (θ u)
      rw [← hθinv s, ← map_inv θ, ← map_mul θ, ← map_mul θ] at e
      exact e)
    (fun β hβ hβC => by
      rw [← Subgroup.map_map, hmap β hβ]
      refine hKC1 _ (Set.MapsTo.iterate (fun _ h => tri_mem_roots h) j hβ) ?_
      rw [← hmap β hβ, Subgroup.map_le_iff_le_comap, Subgroup.comap_comap]
      exact hβC)
    (fun δ hδ h0 => by
      rw [← Subgroup.comap_comap, ← Subgroup.map_le_iff_le_comap, hmap δ hδ]
      exact hpat δ hδ h0)
    ht2 (by rwa [MonoidHom.range_comp, MonoidHom.range_eq_top_of_surjective _ θ.surjective,
      ← MonoidHom.range_eq_map]) htD htJ
  intro k
  have e := key (θ.symm k)
  simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulEquiv.apply_symm_apply] at e
  exact e

theorem conj_eq_self_five {n : ℕ} {K : Type} [Field K] [Finite K] [CharP K 2] (hn : 3 ≤ n)
    (hn5 : 5 ≤ n) {G : Type*} [Group G] {p : ℕ} (hp : p.Prime) {D J : Subgroup G}
    {ψ : spinGroup (quadPlus n K) →* G} (hψ : Function.Injective ψ) (hDp : ∀ d ∈ D, d ^ p = 1)
    (hlift : ∀ d ∈ D, ∃ s ∈ ggTorus (plusDatum n K hn), ∀ u, d * ψ u * d⁻¹ = ψ (s * u * s⁻¹))
    (hKC1 : ∀ β ∈ (plusDatum n K hn).roots,
      (plusDatum n K hn).rootGroup β ≤ (Subgroup.centralizer (D : Set G)).comap ψ →
        ((plusDatum n K hn).rootGroup β).map ψ ≤ J)
    (hKC2 : ∃ β ∈ {β | β ∈ (plusDatum n K hn).roots ∧ (plusDatum n K hn).rootGroup β ≤
        (Subgroup.centralizer (D : Set G)).comap ψ},
      ∃ β' ∈ {β | β ∈ (plusDatum n K hn).roots ∧ (plusDatum n K hn).rootGroup β ≤
        (Subgroup.centralizer (D : Set G)).comap ψ}, β + β' ∈ (plusDatum n K hn).roots)
    (hKC2' : Set.ncard (kgcTorusSet hn ψ D p) ≤ p)
    {t : G} (ht2 : ∃ m : ℕ, t ^ (2 ^ m) = 1) (htN : t ∈ Subgroup.normalizer (ψ.range : Set G))
    (htD : t ∈ Subgroup.centralizer (D : Set G)) (htJ : t ∈ Subgroup.centralizer (J : Set G)) :
    ∀ k, t * ψ k * t⁻¹ = ψ k := by
  obtain ⟨γ, c, ε, τ, hconj, hcA⟩ := exists_conj_plusSemi_of_mem_normalizer hn5 hψ htN
  have hR : ∀ {i j : Fin n} (hij : i ≠ j) (s s' : Bool),
      (∀ σ ∈ kgcLiftSet ψ D, ∀ b : K, σ * (plusFrame n K hn).longRoot hij s s' (.ofAdd b) * σ⁻¹ =
        (plusFrame n K hn).longRoot hij s s' (.ofAdd b)) →
      ∀ b : K, γ * c ((plusFrame n K hn).longRoot hij s s' (.ofAdd b)) * γ⁻¹ =
        (plusFrame n K hn).longRoot hij s s' (.ofAdd b) := fun hij s s' hc b =>
    conj_longRoot_eq_of_forall_lift hn hψ hlift hKC1 htJ hconj hij s s' hc b
  obtain ⟨β, ⟨hβ, hβD⟩, -⟩ := hKC2
  obtain ⟨i, j, hij, s, s', -, hRG⟩ := exists_plusRootGroup_eq (K := K) hn hβ
  have hτ : τ = 1 := ringEquiv_eq_one_of_conj_longRoot hn hcA hij s s' (hR hij s s' fun σ hσ b => by
    obtain ⟨d, hd, hds⟩ := hσ
    have hm : (plusFrame n K hn).longRoot hij s s' (.ofAdd b) ∈ (plusDatum n K hn).rootGroup β := by
      rw [show (plusDatum n K hn).rootGroup β = _ from hRG]
      exact ⟨_, rfl⟩
    refine hψ ?_
    rw [← hds, mul_inv_eq_iff_eq_mul]
    exact Subgroup.mem_centralizer_iff.mp (Subgroup.mem_comap.mp (hβD hm)) d hd)
  subst hτ
  exact conj_eq_self_of_plusSemi_one hn hψ ht2 hconj hcA (kgcLiftSet_subset_ggTorus hn hψ hlift)
    (fun s hs => conj_eq_of_mem_kgcLiftSet_of_commute hn hψ htN htD hconj hs) hR
    (not_existsUnique_fixed_index_of_ncard hn hp hψ hDp hlift hKC2')

theorem conj_eq_self_of_kgc {n : ℕ} {K : Type} [Field K] [Finite K] [CharP K 2] (hn : 3 ≤ n)
    (hn4 : 4 ≤ n) {G : Type*} [Group G] {p : ℕ} (hp : p.Prime) {D J : Subgroup G}
    {ψ : spinGroup (quadPlus n K) →* G} (hψ : Function.Injective ψ) (hDp : ∀ d ∈ D, d ^ p = 1)
    (hlift : ∀ d ∈ D, ∃ s ∈ ggTorus (plusDatum n K hn), ∀ u, d * ψ u * d⁻¹ = ψ (s * u * s⁻¹))
    (hKC1 : ∀ β ∈ (plusDatum n K hn).roots,
      (plusDatum n K hn).rootGroup β ≤ (Subgroup.centralizer (D : Set G)).comap ψ →
        ((plusDatum n K hn).rootGroup β).map ψ ≤ J)
    (hKC2 : ∃ β ∈ {β | β ∈ (plusDatum n K hn).roots ∧ (plusDatum n K hn).rootGroup β ≤
        (Subgroup.centralizer (D : Set G)).comap ψ},
      ∃ β' ∈ {β | β ∈ (plusDatum n K hn).roots ∧ (plusDatum n K hn).rootGroup β ≤
        (Subgroup.centralizer (D : Set G)).comap ψ}, β + β' ∈ (plusDatum n K hn).roots)
    (hKC2' : Set.ncard (kgcTorusSet hn ψ D p) ≤ p)
    {t : G} (ht2 : ∃ m : ℕ, t ^ (2 ^ m) = 1) (htN : t ∈ Subgroup.normalizer (ψ.range : Set G))
    (htD : t ∈ Subgroup.centralizer (D : Set G)) (htJ : t ∈ Subgroup.centralizer (J : Set G)) :
    ∀ k, t * ψ k * t⁻¹ = ψ k := by
  rcases (show n = 4 ∨ 5 ≤ n by omega) with rfl | hn5
  · exact conj_eq_self_four hp hψ hDp hlift hKC1 hKC2 hKC2' ht2 htN htD htJ
  · exact conj_eq_self_five hn hn5 hp hψ hDp hlift hKC1 hKC2 hKC2' ht2 htN htD htJ

end CFSG.StandardType.KGCentOm

end
