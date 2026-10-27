module

public import CFSG.Quasithin.Vol2.Ch11SecAKA17
public import CFSG.Quasithin.Vol2.Ch11SecAKA15

public section

namespace CFSG.Quasithin.Vol2.KGNat

open CFSG.Quasithin Matrix CFSG.ClassicalInvolution.ModelFacts.OddCover
open CFSG.Assembly.LowTwoRank (StatedSp)
open CFSG.LieType.Universal.Symplectic.SpExtras (mat mat_apply)
open CFSG.QuasithinUnique.Setup.X7a (Q2)
open CFSG.Open (pCoreOf)

namespace KA

variable {K : Type} [Field K] {W : Type*} [CommGroup W] {H : Subgroup (MulAut W)}
  {Z : Subgroup W} {π : ↥(StatedSp 2 K) →* ↥H} {f : W → (Fin 2 ⊕ Fin 2 → K)}

@[expose] noncomputable def tf (hf : IsCoord (linModelNat (StatedSp 2 K)) H Z π f)
    (g : StatedSp 2 K) (k : MulAut W) (x : Fin 2 ⊕ Fin 2 → K) : Fin 2 ⊕ Fin 2 → K :=
  mat 2 K g⁻¹ *ᵥ f (k (Function.surjInv hf.surj (mat 2 K g *ᵥ x)))

theorem f_congr (hf : IsCoord (linModelNat (StatedSp 2 K)) H Z π f) {k : MulAut W}
    (hk : ∀ z ∈ Z, k z ∈ Z) {u v : W} (h : f u = f v) : f (k u) = f (k v) := by
  rw [hf.eq_iff] at h ⊢
  have := hk _ h
  rwa [map_mul, map_inv] at this

theorem tf_mk (hf : IsCoord (linModelNat (StatedSp 2 K)) H Z π f) (g : StatedSp 2 K)
    {k : MulAut W} (hk : ∀ z ∈ Z, k z ∈ Z) (w : W) :
    tf hf g k (mat 2 K g⁻¹ *ᵥ f w) = mat 2 K g⁻¹ *ᵥ f (k w) := by
  rw [tf, mat_mulVec_inv]
  congr 1
  exact f_congr hf hk (Function.surjInv_eq hf.surj (f w))

theorem tf_mul (hf : IsCoord (linModelNat (StatedSp 2 K)) H Z π f) (g : StatedSp 2 K)
    {k k' : MulAut W} (hk : ∀ z ∈ Z, k z ∈ Z) (x : Fin 2 ⊕ Fin 2 → K) :
    tf hf g (k * k') x = tf hf g k (tf hf g k' x) := by
  conv_rhs => rw [show tf hf g k' x = mat 2 K g⁻¹ *ᵥ
    f (k' (Function.surjInv hf.surj (mat 2 K g *ᵥ x))) from rfl, tf_mk hf g hk]
  rfl

variable [Finite K] [CharP K 2] [Finite W]

theorem tf_shape (hK4 : ∃ s : Finset K, s.card = 4)
    (hf : IsCoord (linModelNat (StatedSp 2 K)) H Z π f) (g : StatedSp 2 K) {k : MulAut W}
    (hkZ : k ∈ Ch11.SecA.stabW Z) (hkH : ∀ h ∈ H, k * h * k⁻¹ ∈ H)
    (hkU : k ∈ Ch11.SecA.stabW (hf.pre (gmapSp g (spPlane K)).toAddSubgroup))
    (hkc : ∀ s ∈ perfectCore (H ⊓ Ch11.SecA.stabW (hf.pre (gmapSp g (spPlane K)).toAddSubgroup)),
      k * s * k⁻¹ * s⁻¹ ∈ pCoreOf 2 (perfectCore (H ⊓ Ch11.SecA.stabW
        (hf.pre (gmapSp g (spPlane K)).toAddSubgroup)))) :
    (∀ x y, tf hf g k (x + y) = tf hf g k x + tf hf g k y) ∧
      (∀ (c : K) x, tf hf g k (c • x) = c • tf hf g k x) ∧ Function.Injective (tf hf g k) ∧
      ∃ μ ν : K, μ ≠ 0 ∧ tf hf g k (vec4 1 0 0 0) = μ • vec4 1 0 0 0 ∧
        tf hf g k (vec4 0 1 0 0) = μ • vec4 0 1 0 0 ∧ tf hf g k (vec4 0 0 1 0) (.inr 0) = ν ∧
        tf hf g k (vec4 0 0 1 0) (.inr 1) = 0 ∧ tf hf g k (vec4 0 0 0 1) (.inr 0) = 0 ∧
        tf hf g k (vec4 0 0 0 1) (.inr 1) = ν := by
  have : Finite (MulAut W) := Finite.of_injective _ MulEquiv.toEquiv_injective
  have hkZ' : ∀ z ∈ Z, k z ∈ Z := fun z hz => (Ch11.SecA.mem_stabW.mp hkZ z).mp hz
  have hkZ'' : ∀ z ∈ Z, k⁻¹ z ∈ Z := fun z hz =>
    (Ch11.SecA.mem_stabW.mp ((Ch11.SecA.stabW Z).inv_mem hkZ) z).mp hz
  have he0 : (vec4 1 0 0 0 : Fin 2 ⊕ Fin 2 → K) ≠ 0 := fun h =>
    (one_ne_zero : (1 : K) ≠ 0) (congrFun h (.inl 0))
  obtain ⟨σ, hσ⟩ := hf.exists_semilinear (fun T hT => commutant_statedSp T hT) he0 k hkZ'
    hkZ'' (inv_conj_mem_of_conj_mem hkH)
  obtain ⟨T, hTf, hσ⟩ : ∃ T : (Fin 2 ⊕ Fin 2 → K) →+ (Fin 2 ⊕ Fin 2 → K),
      (∀ w, T (f w) = f (k w)) ∧ ∀ (c : K) x, T (c • x) = σ c • T x :=
    ⟨hf.autMap k hkZ', hf.autMap_apply _ _, hσ⟩
  have hT' : ∀ x, gconjMap g T x = tf hf g k x := fun x => by
    rw [gconjMap_apply, tf, ← hTf, Function.surjInv_eq hf.surj]
  have hTinj : Function.Injective T := by
    intro x y hxy
    obtain ⟨a, rfl⟩ := hf.surj x
    obtain ⟨b, rfl⟩ := hf.surj y
    rw [hTf, hTf, hf.eq_iff] at hxy
    rw [hf.eq_iff]
    have := hkZ'' _ hxy
    rwa [← map_inv, ← map_mul, MulAut.inv_apply_self] at this
  have hnorm : ∀ γ : ↥(StatedSp 2 K), ∃ γ' : ↥(StatedSp 2 K), ∀ x,
      T (mat 2 K γ *ᵥ x) = mat 2 K γ' *ᵥ T x := by
    intro γ
    obtain ⟨γ', hγ'⟩ : ∃ γ' : ↥(StatedSp 2 K), π γ' = ⟨_, hkH _ (π γ).2⟩ :=
      hf.onto ⟨_, hkH _ (π γ).2⟩
    refine ⟨γ', fun x => ?_⟩
    obtain ⟨w, rfl⟩ := hf.surj x
    have e : k (((π γ : ↥H) : MulAut W) w) = ((π γ' : ↥H) : MulAut W) (k w) := by
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
  have hplane : ∀ x ∈ spPlane K, gconjMap g T x ∈ spPlane K := by
    intro x hx
    obtain ⟨w, hw⟩ := hf.surj (mat 2 K g *ᵥ x)
    have hwU : w ∈ hf.pre (gmapSp g (spPlane K)).toAddSubgroup := by
      show f w ∈ gmapSp g (spPlane K)
      rw [hw, mem_gmapSp, mat_inv_mulVec]
      exact hx
    have h2 : f (k w) ∈ gmapSp g (spPlane K) := (Ch11.SecA.mem_stabW.mp hkU w).mp hwU
    rw [gconjMap_apply, ← hw, hTf]
    exact mem_gmapSp.mp h2
  have hlevi : ∀ M ∈ perfectCore (Q2 K 1), ∃ N ∈ pCoreOf 2 (perfectCore (Q2 K 1)), ∀ v,
      gconjMap g T (mat 2 K M *ᵥ v) = mat 2 K N *ᵥ (mat 2 K M *ᵥ gconjMap g T v) := by
    intro M hM
    have hs : psiSp π g M ∈
        perfectCore (H ⊓ Ch11.SecA.stabW (hf.pre (gmapSp g (spPlane K)).toAddSubgroup)) := by
      rw [gamma2_eq hf g]
      exact ⟨M, hM, rfl⟩
    have hc := hkc _ hs
    rw [pCoreOf_gamma2_eq hf g] at hc
    obtain ⟨N, hN, hNe⟩ := hc
    refine ⟨N, hN, fun v => ?_⟩
    obtain ⟨w, hw⟩ := hf.surj (mat 2 K g *ᵥ v)
    have h1 : psiSp π g N * psiSp π g M = k * psiSp π g M * k⁻¹ := by
      rw [hNe]
      group
    have e : k (psiSp π g M w) = psiSp π g N (psiSp π g M (k w)) := by
      have := congrArg (fun x : MulAut W => x (k w)) h1
      simp only [MulAut.mul_apply, MulAut.inv_apply_self] at this
      exact this.symm
    have e2 := congrArg f e
    rw [← hTf, psiSp_apply, hf.act4, psiSp_apply, hf.act4, hf.act4, ← hTf, hw] at e2
    have e3 := congrArg (fun z => mat 2 K g⁻¹ *ᵥ z) e2
    simp only [gconj_mulVec_sp, mat_inv_mulVec] at e3
    rw [gconjMap_apply, gconjMap_apply]
    exact e3
  obtain ⟨hσ1, μ, ν, hμ0, h0, h1, h2, h3, h4, h5⟩ :=
    shape_of_levi1 hK4 hσ' hL' hinj' hplane hlevi
  refine ⟨fun x y => by rw [← hT', ← hT', ← hT', map_add],
    fun c x => by rw [← hT', ← hT', hσ', hσ1], fun x y h => hinj' (by rwa [hT', hT']),
    μ, ν, hμ0, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [← hT']
    exact h0
  · rw [← hT']
    exact h1
  · rw [← hT']
    exact h2
  · rw [← hT']
    exact h3
  · rw [← hT']
    exact h4
  · rw [← hT']
    exact h5

end KA

end CFSG.Quasithin.Vol2.KGNat
