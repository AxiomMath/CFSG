module

public import CFSG.Quasithin.Vol2.Ch11SecO3CXe
public import CFSG.Quasithin.Vol2.Ch11SecO3CXc

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecF.O3CX

open CFSG.Quasithin Matrix
open CFSG.Quasithin.Vol2.KGNat (vec4 mat_mulVec_inv mat_inv_mulVec)
open CFSG.Quasithin.Vol2.KGNat.KA (gconj_mulVec_sp)
open CFSG.Assembly.LowTwoRank (StatedSp)
open CFSG.LieType.Universal.Symplectic.SpExtras (mat)
open CFSG.LocalAnalysis.ComponentInitial.SymplecticTorusWeyl (torusHom)
open CFSG.Quasithin.Vol2.Ch11.SecB.K7 (trv trv_mul trv_conj trv_smul)

variable {G : Type} [Group G] {V W C : Subgroup G}

theorem conjV_mul3 {a b c : G} (ha : a ∈ Subgroup.normalizer (V : Set G))
    (hb : b ∈ Subgroup.normalizer (V : Set G)) (hc : c ∈ Subgroup.normalizer (V : Set G)) :
    SecA.conjV V (a * b * c) (Subgroup.mul_mem _ (Subgroup.mul_mem _ ha hb) hc) =
      SecA.conjV V a ha * SecA.conjV V b hb * SecA.conjV V c hc := by
  rw [SecA.conjV_mul V (Subgroup.mul_mem _ ha hb) hc, SecA.conjV_mul V ha hb]

variable {K : Type} [Field K] [CharP K 2]

theorem exists_roots (ρ : StatedSp 2 K →* MulAut ↥V) (g : StatedSp 2 K)
    (hfull : ∀ c : K, ∃ w ∈ W, ∃ hw : w ∈ Subgroup.normalizer (V : Set G),
      SecA.conjV V w hw = ρ (trv (mat 2 K g *ᵥ vec4 1 0 0 0) c))
    (hC : ∀ h (hh : h ∈ Subgroup.normalizer (V : Set G)), SecA.conjV V h hh = 1 → h ∈ C)
    (hNW : ∀ h (hh : h ∈ Subgroup.normalizer (V : Set G)) (δ : StatedSp 2 K) (l : K),
      SecA.conjV V h hh = ρ δ →
        mat 2 K δ *ᵥ (mat 2 K g *ᵥ vec4 1 0 0 0) = l • (mat 2 K g *ᵥ vec4 1 0 0 0) →
        h ∈ Subgroup.normalizer (W : Set G))
    (hWC : W ≤ Subgroup.normalizer (C : Set G)) {y : G}
    (hyV : y ∈ Subgroup.normalizer (V : Set G)) (hyC : y ∈ Subgroup.normalizer (C : Set G))
    {γ : StatedSp 2 K} (hyγ : SecA.conjV V y hyV = ρ γ) {β : K} (hβ : β ≠ 0)
    (hu : mat 2 K γ⁻¹ *ᵥ (mat 2 K g *ᵥ vec4 1 0 0 0) = β • (mat 2 K g *ᵥ vec4 0 0 1 0)) :
    ∃ wf wf' : K → G, Roots W (conjSubgroup W y) C β wf wf' ∧ (∀ d, wf' d = y⁻¹ * wf d * y) ∧
      ∀ a : Kˣ, ∃ hτ : (wf a * wf' ((a : K) * β ^ 2)⁻¹ * wf a) *
          (wf 1 * wf' (1 * β ^ 2)⁻¹ * wf 1) ∈ Subgroup.normalizer (V : Set G),
        SecA.conjV V _ hτ = ρ (g * torusHom (Pi.mulSingle 0 a) * g⁻¹) := by
  set e := mat 2 K g *ᵥ vec4 1 0 0 0 with he
  set f := mat 2 K g *ᵥ vec4 0 0 1 0 with hf
  have hge : mat 2 K g⁻¹ *ᵥ e = vec4 1 0 0 0 := mat_inv_mulVec g _
  have hgf : mat 2 K g⁻¹ *ᵥ f = vec4 0 0 1 0 := mat_inv_mulVec g _
  have he' : mat 2 K g *ᵥ vec4 1 0 0 0 = e := rfl
  have hf' : mat 2 K g *ᵥ vec4 0 0 1 0 = f := rfl
  choose wf hwW hwV hwρ using hfull
  have hyV' : y⁻¹ ∈ Subgroup.normalizer (V : Set G) := Subgroup.inv_mem _ hyV
  set wf' : K → G := fun d => y⁻¹ * wf d * y with hwf'
  have hw'V : ∀ d, wf' d ∈ Subgroup.normalizer (V : Set G) := fun d =>
    Subgroup.mul_mem _ (Subgroup.mul_mem _ hyV' (hwV d)) hyV
  have hγf : mat 2 K γ *ᵥ f = β⁻¹ • e := by
    have h1 := congrArg (fun v => mat 2 K γ *ᵥ v) hu
    simp only [mat_mulVec_inv, Matrix.mulVec_smul] at h1
    rw [h1, smul_smul, inv_mul_cancel₀ hβ, one_smul]
  have hw'ρ : ∀ d, SecA.conjV V (wf' d) (hw'V d) = ρ (trv f (β ^ 2 * d)) := by
    intro d
    have h1 : γ⁻¹ * trv e d * γ = trv (mat 2 K γ⁻¹ *ᵥ e) d := by
      have := trv_conj γ⁻¹ e d
      rwa [inv_inv] at this
    rw [conjV_mul3 hyV' (hwV d) hyV, SecA.conjV_inv V hyV, hwρ d, hyγ, ← map_inv, ← map_mul,
      ← map_mul, h1, hu, trv_smul]
  have hw'W : ∀ d, wf' d ∈ conjSubgroup W y := fun d => by
    rw [mem_conjSubgroup_iff]
    have e1 : y * wf' d * y⁻¹ = wf d := by simp only [hwf']; group
    rw [e1]
    exact hwW d
  have hsV : ∀ c d, wf c * wf' d * wf c ∈ Subgroup.normalizer (V : Set G) := fun c d =>
    Subgroup.mul_mem _ (Subgroup.mul_mem _ (hwV c) (hw'V d)) (hwV c)
  have hsρ : ∀ c d, SecA.conjV V _ (hsV c d) = ρ (g * (trv (vec4 1 0 0 0) c *
      trv (vec4 0 0 1 0) (β ^ 2 * d) * trv (vec4 1 0 0 0) c) * g⁻¹) := by
    intro c d
    rw [conjV_mul3 (hwV c) (hw'V d) (hwV c), hwρ, hw'ρ, ← map_mul, ← map_mul, weyl_conj]
  have hsC : ∀ c d, wf c * wf' d * wf c ∈ Subgroup.normalizer (C : Set G) := fun c d =>
    Subgroup.mul_mem _ (Subgroup.mul_mem _ (hWC (hwW c)) (Subgroup.mul_mem _
      (Subgroup.mul_mem _ (Subgroup.inv_mem _ hyC) (hWC (hwW d))) hyC)) (hWC (hwW c))
  have hstd : ∀ c d : K, c * d * β ^ 2 = 1 → c * (β ^ 2 * d) = 1 := fun c d h => by
    rw [← h]; ring
  have hadd : ∀ c c', (wf c * wf c')⁻¹ * wf (c + c') ∈ W ⊓ C := by
    intro c c'
    have hm := Subgroup.mul_mem _ (hwV c) (hwV c')
    refine ⟨Subgroup.mul_mem _ (Subgroup.inv_mem _ (Subgroup.mul_mem _ (hwW c) (hwW c')))
      (hwW _), hC _ (Subgroup.mul_mem _ (Subgroup.inv_mem _ hm) (hwV _)) ?_⟩
    rw [SecA.conjV_mul V (Subgroup.inv_mem _ hm) (hwV _), SecA.conjV_inv V hm,
      SecA.conjV_mul V (hwV c) (hwV c'), hwρ, hwρ, hwρ, ← map_mul, ← map_inv, ← map_mul, trv_mul,
      inv_mul_cancel, map_one]
  refine ⟨wf, wf', ⟨hwW, hw'W, hadd, fun d d' => ?_, fun c d hcd a ha => ?_,
    fun c d hcd b hb => ?_⟩, fun d => rfl, fun a => ?_⟩
  ·
    have h1 := hadd d d'
    have e1 : (wf' d * wf' d')⁻¹ * wf' (d + d') = y⁻¹ * ((wf d * wf d')⁻¹ * wf (d + d')) * y := by
      simp only [hwf']; group
    rw [e1]
    refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
    · rw [mem_conjSubgroup_iff]
      have e2 : y * (y⁻¹ * ((wf d * wf d')⁻¹ * wf (d + d')) * y) * y⁻¹ =
          (wf d * wf d')⁻¹ * wf (d + d') := by group
      rw [e2]
      exact h1.1
    · have h2 := conj_mem_of_mem_normalizer (Subgroup.inv_mem _ hyC) h1.2
      rwa [inv_inv] at h2
  ·
    have hys : y * (wf c * wf' d * wf c) ∈ Subgroup.normalizer (W : Set G) := by
      refine hNW _ (Subgroup.mul_mem _ hyV (hsV c d)) (γ * (g * (trv (vec4 1 0 0 0) c *
        trv (vec4 0 0 1 0) (β ^ 2 * d) * trv (vec4 1 0 0 0) c) * g⁻¹)) (β ^ 2 * d * β⁻¹) ?_ ?_
      · rw [SecA.conjV_mul V hyV (hsV c d), hyγ, hsρ, ← map_mul]
      · rw [map_mul, ← Matrix.mulVec_mulVec, gconj_mulVec_sp, hge, weyl_std_e0 (hstd c d hcd),
          Matrix.mulVec_smul, Matrix.mulVec_smul, hf', hγf, smul_smul]
    refine Subgroup.mem_inf.mpr ⟨?_, conj_mem_of_mem_normalizer (hsC c d) ha.2⟩
    rw [mem_conjSubgroup_iff]
    have h1 := conj_mem_of_mem_normalizer hys ha.1
    have e1 : y * (wf c * wf' d * wf c) * a * (y * (wf c * wf' d * wf c))⁻¹ =
        y * ((wf c * wf' d * wf c) * a * (wf c * wf' d * wf c)⁻¹) * y⁻¹ := by group
    rwa [e1] at h1
  ·
    have hsy : (wf c * wf' d * wf c) * y⁻¹ ∈ Subgroup.normalizer (W : Set G) := by
      refine hNW _ (Subgroup.mul_mem _ (hsV c d) hyV') (g * (trv (vec4 1 0 0 0) c *
        trv (vec4 0 0 1 0) (β ^ 2 * d) * trv (vec4 1 0 0 0) c) * g⁻¹ * γ⁻¹) (β * c) ?_ ?_
      · rw [SecA.conjV_mul V (hsV c d) hyV', hsρ, SecA.conjV_inv V hyV, hyγ, ← map_inv,
          ← map_mul]
      · rw [map_mul, ← Matrix.mulVec_mulVec, hu, Matrix.mulVec_smul, gconj_mulVec_sp, hgf,
          weyl_std_f0 (hstd c d hcd), Matrix.mulVec_smul, he', smul_smul]
    refine Subgroup.mem_inf.mpr ⟨?_, conj_mem_of_mem_normalizer (hsC c d) hb.2⟩
    have h1 := conj_mem_of_mem_normalizer hsy (mem_conjSubgroup_iff.mp hb.1)
    have e1 : (wf c * wf' d * wf c) * y⁻¹ * (y * b * y⁻¹) * ((wf c * wf' d * wf c) * y⁻¹)⁻¹ =
        (wf c * wf' d * wf c) * b * (wf c * wf' d * wf c)⁻¹ := by group
    rwa [e1] at h1
  ·
    refine ⟨Subgroup.mul_mem _ (hsV _ _) (hsV _ _), ?_⟩
    have e1 : β ^ 2 * ((a : K) * β ^ 2)⁻¹ = (a : K)⁻¹ := by field_simp
    have e2 : β ^ 2 * (1 * β ^ 2)⁻¹ = 1 := by field_simp
    rw [SecA.conjV_mul V (hsV _ _) (hsV _ _), hsρ, hsρ, e1, e2, ← map_mul, ← weyl_mul_weyl_std a]
    congr 1
    group

end CFSG.Quasithin.Vol2.Ch11.SecF.O3CX
