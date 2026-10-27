module

public import CFSG.Quasithin.Vol2.Ch11SecAKA7
public import CFSG.Quasithin.Vol2.Ch11SecAKA6
public import CFSG.Quasithin.Vol2.Ch11SecQ9aCartE
public import CFSG.Quasithin.Vol2.Ch11SecQ9aS4J

public section

namespace CFSG.Quasithin.Vol2.KGNat

open CFSG.Quasithin Matrix CFSG.ClassicalInvolution.ModelFacts.OddCover
open CFSG.Assembly.LowTwoRank (StatedSp)
open CFSG.LieType.Universal.Symplectic.SpExtras (mat mat_apply)
open CFSG.QuasithinUnique.Setup.X7a (Q2)
open CFSG.Open (pCoreOf)
open CFSG.Quasithin.Vol2.Ch11.SecS.C11P9A (gammaW_pre_eq)

namespace KA

variable {K : Type} [Field K] {W : Type*} [CommGroup W] {H : Subgroup (MulAut W)}
  {Z : Subgroup W} {π : ↥(StatedSp 2 K) →* ↥H} {f : W → (Fin 2 ⊕ Fin 2 → K)}

theorem pCoreOf_gamma_eq [Finite K] [Finite W]
    (hf : IsCoord (linModelNat (StatedSp 2 K)) H Z π f) (g : StatedSp 2 K) :
    pCoreOf 2 (perfectCore (H ⊓ Ch11.SecA.stabW (hf.pre (gmapSp g (spLine K)).toAddSubgroup))) =
      (pCoreOf 2 (perfectCore (Q2 K 0))).map (psiSp π g) := by
  have : Finite (MulAut W) := Finite.of_injective _ MulEquiv.toEquiv_injective
  rw [show perfectCore (H ⊓ Ch11.SecA.stabW (hf.pre (gmapSp g (spLine K)).toAddSubgroup)) =
    Ch11.SecS.gammaW H (hf.pre (gmapSp g (spLine K)).toAddSubgroup) from rfl,
    gammaW_pre_eq hf g 0 _ flag_one_eq,
    Ch11.SecS.C11P9A.pCoreOf_map_of_injective _ (psiSp_injective hf g)]

omit [Field K] in
theorem iterate_of_intertwine {K : Type} {f : W → (Fin 2 ⊕ Fin 2 → K)}
    {T : (Fin 2 ⊕ Fin 2 → K) → (Fin 2 ⊕ Fin 2 → K)} {τ : MulAut W}
    (hT : ∀ w, T (f w) = f (τ w)) (m : ℕ) (w : W) : T^[m] (f w) = f ((τ ^ m) w) := by
  induction m with
  | zero => rfl
  | succ m ih => rw [Function.iterate_succ_apply', ih, hT, pow_succ', MulAut.mul_apply]

theorem gconj_mulVec_sp (g M : StatedSp 2 K) (y : Fin 2 ⊕ Fin 2 → K) :
    mat 2 K (g * M * g⁻¹) *ᵥ y = mat 2 K g *ᵥ (mat 2 K M *ᵥ (mat 2 K g⁻¹ *ᵥ y)) := by
  rw [map_mul, map_mul, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]

theorem act_congr (hf : IsCoord (linModelNat (StatedSp 2 K)) H Z π f) {x : MulAut W}
    (hx : x ∈ H) {u v : W} (h : f u = f v) : f (x u) = f (x v) := by
  obtain ⟨γ, hγ⟩ : ∃ γ : ↥(StatedSp 2 K), π γ = ⟨x, hx⟩ := hf.onto ⟨x, hx⟩
  have hxγ : x = ((π γ : ↥H) : MulAut W) := by rw [hγ]
  rw [hxγ, hf.act4, hf.act4, h]

theorem act_cancel (hf : IsCoord (linModelNat (StatedSp 2 K)) H Z π f) {x : MulAut W}
    (hx : x ∈ H) {u v : W} (h : f (x u) = f (x v)) : f u = f v := by
  obtain ⟨γ, hγ⟩ : ∃ γ : ↥(StatedSp 2 K), π γ = ⟨x, hx⟩ := hf.onto ⟨x, hx⟩
  have hxγ : x = ((π γ : ↥H) : MulAut W) := by rw [hγ]
  rw [hxγ, hf.act4, hf.act4] at h
  have h1 := congrArg (fun v => mat 2 K γ⁻¹ *ᵥ v) h
  simpa only [mat_inv_mulVec] using h1

variable [Finite K] [CharP K 2] [Finite W]

theorem exists_core (hK4 : ∃ s : Finset K, s.card = 4)
    (hf : IsCoord (linModelNat (StatedSp 2 K)) H Z π f) (g : StatedSp 2 K) {U : Subgroup W}
    (hU : U = hf.pre (gmapSp g (spLine K)).toAddSubgroup) (hfix : Ch11.SecA.RadicalFixes H Z U)
    (hpt : ∀ h ∈ perfectCore (H ⊓ Ch11.SecA.stabW U), ∀ u ∈ U, h u * u⁻¹ ∈ Z)
    {τ : MulAut W} (hτ2 : ∃ k : ℕ, τ ^ 2 ^ k = 1) (hτZ : τ ∈ Ch11.SecA.stabW Z)
    (hτH : ∀ h ∈ H, τ * h * τ⁻¹ ∈ H)
    (hτc : ∀ x : ↥(perfectCore (H ⊓ Ch11.SecA.stabW U)),
      ∃ y : ↥(perfectCore (H ⊓ Ch11.SecA.stabW U)),
        y ∈ CFSG.pCore 2 ↥(perfectCore (H ⊓ Ch11.SecA.stabW U)) ∧
          τ * (x : MulAut W) * τ⁻¹ = (y : MulAut W) * x) :
    ∃ N ∈ pCoreOf 2 (perfectCore (Q2 K 0)), ∀ w, f (τ w) = f (psiSp π g N w) := by
  obtain ⟨k, hk⟩ := hτ2
  have : Finite (MulAut W) := Finite.of_injective _ MulEquiv.toEquiv_injective
  have hτZ' : ∀ z ∈ Z, τ z ∈ Z := fun z hz => (Ch11.SecA.mem_stabW.mp hτZ z).mp hz
  have hτZ'' : ∀ z ∈ Z, τ⁻¹ z ∈ Z := fun z hz =>
    (Ch11.SecA.mem_stabW.mp ((Ch11.SecA.stabW Z).inv_mem hτZ) z).mp hz
  have hτR : ∀ r ∈ pCoreOf 2 (perfectCore (H ⊓ Ch11.SecA.stabW U)),
      τ * r * τ⁻¹ ∈ pCoreOf 2 (perfectCore (H ⊓ Ch11.SecA.stabW U)) := by
    rintro _ ⟨x, hx, rfl⟩
    obtain ⟨y, hy, hxy⟩ := hτc x
    have hx' : x ∈ CFSG.pCore 2 ↥(perfectCore (H ⊓ Ch11.SecA.stabW U)) := by
      exact hx
    show τ * (x : MulAut W) * τ⁻¹ ∈ _
    rw [hxy]
    exact (mem_pCoreOf_iff' _ (y * x)).mpr (mul_mem hy hx')
  have hτU := mem_stabW_of_conj hfix hpt hτZ hτR
  subst hU
  have he0 : (vec4 1 0 0 0 : Fin 2 ⊕ Fin 2 → K) ≠ 0 := fun h =>
    (one_ne_zero : (1 : K) ≠ 0) (congrFun h (.inl 0))
  obtain ⟨σ, hσ⟩ := hf.exists_semilinear (fun T hT => commutant_statedSp T hT) he0 τ hτZ'
    hτZ'' (inv_conj_mem_of_conj_mem hτH)
  obtain ⟨T, hTf, hσ⟩ : ∃ T : (Fin 2 ⊕ Fin 2 → K) →+ (Fin 2 ⊕ Fin 2 → K),
      (∀ w, T (f w) = f (τ w)) ∧ ∀ (c : K) x, T (c • x) = σ c • T x :=
    ⟨hf.autMap τ hτZ', hf.autMap_apply _ _, hσ⟩
  have hTinj : Function.Injective T := by
    intro x y hxy
    obtain ⟨a, rfl⟩ := hf.surj x
    obtain ⟨b, rfl⟩ := hf.surj y
    rw [hTf, hTf, hf.eq_iff] at hxy
    rw [hf.eq_iff]
    have := hτZ'' _ hxy
    rwa [← map_inv, ← map_mul, MulAut.inv_apply_self] at this
  have hnorm : ∀ γ : ↥(StatedSp 2 K), ∃ γ' : ↥(StatedSp 2 K), ∀ x,
      T (mat 2 K γ *ᵥ x) = mat 2 K γ' *ᵥ T x := by
    intro γ
    obtain ⟨γ', hγ'⟩ : ∃ γ' : ↥(StatedSp 2 K), π γ' = ⟨_, hτH _ (π γ).2⟩ :=
      hf.onto ⟨_, hτH _ (π γ).2⟩
    refine ⟨γ', fun x => ?_⟩
    obtain ⟨w, rfl⟩ := hf.surj x
    have e : τ (((π γ : ↥H) : MulAut W) w) = ((π γ' : ↥H) : MulAut W) (τ w) := by
      rw [hγ']
      simp [MulAut.mul_apply]
    rw [← hf.act4, hTf, hTf, e, hf.act4]
  have hσ' : ∀ (c : K) x, gconjMap g T (c • x) = σ c • gconjMap g T x := fun c x => by
    rw [gconjMap_apply, gconjMap_apply, Matrix.mulVec_smul, hσ, Matrix.mulVec_smul]
  have hL' : ∀ γ : ↥(StatedSp 2 K), ∃ γ' : ↥(StatedSp 2 K), ∀ x,
      gconjMap g T (mat 2 K γ *ᵥ x) = mat 2 K γ' *ᵥ gconjMap g T x := by
    intro γ
    obtain ⟨γ', hγ'⟩ := hnorm (g * γ * g⁻¹)
    refine ⟨g⁻¹ * γ' * g, fun x => ?_⟩
    have e : mat 2 K g *ᵥ (mat 2 K γ *ᵥ x) = mat 2 K (g * γ * g⁻¹) *ᵥ (mat 2 K g *ᵥ x) := by
      rw [gconj_mulVec_sp, mat_inv_mulVec]
    rw [gconjMap_apply, gconjMap_apply, e, hγ', map_mul, map_mul, ← Matrix.mulVec_mulVec,
      ← Matrix.mulVec_mulVec, mat_mulVec_inv]
  have hinj' : Function.Injective (gconjMap g T) := fun x y h => by
    rw [gconjMap_apply, gconjMap_apply] at h
    have h1 := congrArg (fun v => mat 2 K g *ᵥ v) h
    simp only [mat_mulVec_inv] at h1
    have h3 := congrArg (fun v => mat 2 K g⁻¹ *ᵥ v) (hTinj h1)
    simpa only [mat_inv_mulVec] using h3
  have hline' : gconjMap g T (vec4 1 0 0 0) ∈ spLine K := by
    obtain ⟨u₀, hu₀⟩ := hf.surj (mat 2 K g *ᵥ vec4 1 0 0 0)
    have hu₀U : u₀ ∈ hf.pre (gmapSp g (spLine K)).toAddSubgroup :=
      hf.mem_pre.mpr (mem_gmapSp_spLine_iff.mpr ⟨1, by rw [hu₀, one_smul]⟩)
    have h2 : f (τ u₀) ∈ gmapSp g (spLine K) := (Ch11.SecA.mem_stabW.mp hτU u₀).mp hu₀U
    rw [← hTf, hu₀, mem_gmapSp] at h2
    exact h2
  have hlevi' : ∀ M ∈ perfectCore (Q2 K 0), ∃ N ∈ pCoreOf 2 (perfectCore (Q2 K 0)), ∀ v,
      gconjMap g T (mat 2 K M *ᵥ v) = mat 2 K N *ᵥ (mat 2 K M *ᵥ gconjMap g T v) := by
    intro M hM
    have hψM : psiSp π g M ∈
        perfectCore (H ⊓ Ch11.SecA.stabW (hf.pre (gmapSp g (spLine K)).toAddSubgroup)) := by
      rw [show perfectCore (H ⊓ Ch11.SecA.stabW (hf.pre (gmapSp g (spLine K)).toAddSubgroup)) =
        Ch11.SecS.gammaW H (hf.pre (gmapSp g (spLine K)).toAddSubgroup) from rfl,
        gammaW_pre_eq hf g 0 _ flag_one_eq]
      exact ⟨M, hM, rfl⟩
    obtain ⟨y, hy, hxy⟩ := hτc ⟨_, hψM⟩
    have hyR := (mem_pCoreOf_iff' _ y).mpr hy
    rw [pCoreOf_gamma_eq hf g] at hyR
    obtain ⟨N, hN, hNy⟩ := hyR
    refine ⟨N, hN, fun v => ?_⟩
    obtain ⟨w, hw⟩ := hf.surj (mat 2 K g *ᵥ v)
    have e : τ (psiSp π g M w) = psiSp π g N (psiSp π g M (τ w)) := by
      have := congrArg (fun x : MulAut W => x (τ w)) hxy
      simp only [MulAut.mul_apply, MulAut.inv_apply_self] at this
      rw [this, ← hNy]
    have e2 := congrArg f e
    rw [← hTf, psiSp_apply, hf.act4, psiSp_apply, hf.act4, hf.act4, ← hTf, hw] at e2
    have e3 := congrArg (fun z => mat 2 K g⁻¹ *ᵥ z) e2
    simp only [gconj_mulVec_sp, mat_inv_mulVec] at e3
    rw [gconjMap_apply, gconjMap_apply]
    exact e3
  have hk' : ∀ v, (⇑(gconjMap g T))^[2 ^ k] v = v := by
    intro v
    rw [gconjMap_iterate]
    obtain ⟨w, hw⟩ := hf.surj (mat 2 K g *ᵥ v)
    rw [← hw, iterate_of_intertwine hTf, hk, MulAut.one_apply, hw, mat_inv_mulVec]
  obtain ⟨N₀, hN₀, hN₀T⟩ := exists_pCore_eq hK4 hσ' hL' hinj' hline' hlevi' hk'
  refine ⟨N₀, hN₀, fun w => ?_⟩
  rw [← hTf, psiSp_apply, hf.act4, gconj_mulVec_sp, hN₀T, gconjMap_apply, mat_mulVec_inv,
    mat_mulVec_inv]

end KA

end CFSG.Quasithin.Vol2.KGNat
