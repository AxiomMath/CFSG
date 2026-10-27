module

public import CFSG.LocalAnalysis.StandardType.GGHdRo7SUCoordDefs

public section

namespace CFSG.StandardType.HdRo7SU

open CFSG.StandardType.HdRo7C

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

private noncomputable def hdRo7SULinAux_iota {G : Type} [Group G] {p : ℕ} {Bs : Subgroup G} {m : ℕ}
    (τ : (Fin m → Multiplicative (ZMod p)) ≃* ↥Bs) : Additive ↥Bs ≃+ (Fin m → ZMod p) :=
  AddEquiv.mk
    (toEquiv :=
      { toFun := fun z i => Multiplicative.toAdd (τ.symm (Additive.toMul z) i)
        invFun := fun v => Additive.ofMul (τ (fun i => Multiplicative.ofAdd (v i)))
        left_inv := by
          intro z
          have h : (fun i => Multiplicative.ofAdd
              (Multiplicative.toAdd (τ.symm (Additive.toMul z) i))) = τ.symm (Additive.toMul z) := by
            funext i
            simp
          simp only [h]
          simp
        right_inv := by
          intro v
          funext i
          simp })
    (by
      intro z w
      funext i
      simp [toMul_add, Pi.mul_apply, toAdd_mul])

private lemma hdRo7SULinAux_iota_ofMul {G : Type} [Group G] {p : ℕ} {Bs : Subgroup G} {m : ℕ}
    (τ : (Fin m → Multiplicative (ZMod p)) ≃* ↥Bs)
    (f : Fin m → Multiplicative (ZMod p)) :
    hdRo7SULinAux_iota τ (Additive.ofMul (τ f)) = fun i => Multiplicative.toAdd (f i) := by
  simp [hdRo7SULinAux_iota]

private lemma hdRo7SULinAux_basisFun_eq {G : Type} [Group G] {p : ℕ} {Bs : Subgroup G} {m : ℕ}
    (τ : (Fin m → Multiplicative (ZMod p)) ≃* ↥Bs) (i : Fin m) :
    (Pi.basisFun (ZMod p) (Fin m)) i =
      hdRo7SULinAux_iota τ (Additive.ofMul (τ (Pi.mulSingle i (Multiplicative.ofAdd 1)))) := by
  rw [hdRo7SULinAux_iota_ofMul, Pi.basisFun_apply]
  funext j
  by_cases h : j = i
  · simp [Pi.single_apply, Pi.mulSingle_apply, h]
  · simp [Pi.single_apply, Pi.mulSingle_apply, h]

private lemma hdRo7SULinAux_SUOnes_eq {p : ℕ} {m : ℕ} :
    SUOnes p (Pi.basisFun (ZMod p) (Fin m)) = fun _ => (1 : ZMod p) := by
  funext k
  rw [SUOnes, Finset.sum_apply, Finset.sum_eq_single k]
  · rw [Pi.basisFun_apply, Pi.single_apply, if_pos rfl]
  · intro j _ hjk
    rw [Pi.basisFun_apply, Pi.single_apply, if_neg (Ne.symm hjk)]
  · intro hk
    exact absurd (Finset.mem_univ k) hk

private lemma hdRo7SULinAux_coord_formula {p : ℕ} {m : ℕ}
    (g : (Fin m → ZMod p) ≃ₗ[ZMod p] (Fin m → ZMod p)) (σ : Equiv.Perm (Fin m))
    (hg : ∀ i, g ((Pi.basisFun (ZMod p) (Fin m)) i) = (Pi.basisFun (ZMod p) (Fin m)) (σ i))
    (v : Fin m → ZMod p) (k : Fin m) : g v k = v (σ.symm k) := by
  have hv : v = ∑ i, v i • (Pi.basisFun (ZMod p) (Fin m)) i := by
    funext j
    rw [Finset.sum_apply, Finset.sum_eq_single j]
    · simp [Pi.basisFun_apply]
    · intro i _ hij
      simp [Pi.basisFun_apply, Pi.single_apply, Ne.symm hij]
    · intro hj
      exact absurd (Finset.mem_univ j) hj
  have hgv : g v = ∑ i, v i • g ((Pi.basisFun (ZMod p) (Fin m)) i) := by
    conv_lhs => rw [hv]
    rw [show (g : (Fin m → ZMod p) → (Fin m → ZMod p)) = ⇑g.toLinearMap from rfl]
    rw [map_sum g.toLinearMap]
    simp [map_smul]
  rw [hgv, Finset.sum_apply]
  simp only [Pi.smul_apply, smul_eq_mul, hg]
  simp only [Pi.basisFun_apply, Pi.single_apply]
  rw [Finset.sum_eq_single (σ.symm k)]
  · rw [Equiv.apply_symm_apply]
    simp
  · intro i _ hi
    have h : k ≠ σ i := by
      intro H
      exact hi (by rw [H, Equiv.symm_apply_apply])
    simp [h]
  · intro hk
    exact absurd (Finset.mem_univ (σ.symm k)) hk

theorem su_linearModel_of_coord {G : Type} [Group G] {p : ℕ} [Fact p.Prime]
    {Bs X : Subgroup G} {m : ℕ} {τ : (Fin m → Multiplicative (ZMod p)) ≃* ↥Bs}
    (hcm : SUCoordModel p Bs X m τ) {a : G} (ha : a ∈ Bs)
    (hτ : τ (fun _ => Multiplicative.ofAdd (1 : ZMod p)) = ⟨a, ha⟩) :
    ∃ (V : Type) (_ : AddCommGroup V) (_ : Module (ZMod p) V)
      (ι : Additive ↥Bs ≃+ V) (b : Module.Basis (Fin m) (ZMod p) V),
      ι (Additive.ofMul (⟨a, ha⟩ : ↥Bs)) = SUOnes p b ∧
      ∀ g, g ∈ (ggAutomizer X Bs).map (ggLin (p := p) ι) ↔ SUPerm p b g := by
  refine ⟨(Fin m → ZMod p), inferInstance, inferInstance, hdRo7SULinAux_iota τ,
    Pi.basisFun (ZMod p) (Fin m), ?_, ?_⟩
  · rw [← hτ, hdRo7SULinAux_iota_ofMul]
    simpa using hdRo7SULinAux_SUOnes_eq.symm
  · intro (g : (Fin m → ZMod p) ≃ₗ[ZMod p] (Fin m → ZMod p))
    constructor
    · rintro ⟨ψ, hψ, rfl⟩
      obtain ⟨σ, hσ⟩ := (hcm ψ).mp hψ
      refine ⟨σ, fun i => ?_⟩
      have hX : ψ (τ (Pi.mulSingle i (Multiplicative.ofAdd 1))) =
          τ (Pi.mulSingle (σ i) (Multiplicative.ofAdd 1)) := by
        have hcoe : τ.symm (ψ (τ (Pi.mulSingle i (Multiplicative.ofAdd 1)))) =
            Pi.mulSingle (σ i) (Multiplicative.ofAdd 1) := by
          funext j
          have hj := hσ (Pi.mulSingle i (Multiplicative.ofAdd 1)) (σ.symm j)
          rw [Equiv.apply_symm_apply] at hj
          apply Multiplicative.toAdd.injective
          refine hj.trans ?_
          by_cases h : j = σ i
          · have h' : σ.symm j = i := by rw [h, Equiv.symm_apply_apply]
            simp [Pi.mulSingle_apply, h, h']
          · have h' : σ.symm j ≠ i := by
              intro H
              exact h (by rw [← H, Equiv.apply_symm_apply])
            simp [Pi.mulSingle_apply, h, h']
        simpa using congrArg τ hcoe
      rw [hdRo7SULinAux_basisFun_eq τ i, ggLin_apply_ofMul, hX,
        ← hdRo7SULinAux_basisFun_eq τ (σ i)]
    · intro hg
      obtain ⟨σ, hσ⟩ := hg
      let A : Additive ↥Bs ≃+ Additive ↥Bs :=
        (hdRo7SULinAux_iota τ).trans
          ((AddEquiv.mk (toEquiv := g.toEquiv) (map_add' := fun x y => map_add g x y)).trans
            (hdRo7SULinAux_iota τ).symm)
      let ψ : MulAut ↥Bs := AddEquiv.toMultiplicative A
      have hψ_apply : ∀ x : Additive ↥Bs, Additive.ofMul (ψ (Additive.toMul x)) = A x := by
        intro x
        rfl
      have hψ_g : ggLin (p := p) (hdRo7SULinAux_iota τ) ψ = g := by
        refine LinearEquiv.ext fun v => ?_
        rw [ggLin_apply]
        show hdRo7SULinAux_iota τ
          (Additive.ofMul (ψ (Additive.toMul ((hdRo7SULinAux_iota τ).symm v)))) = g v
        rw [hψ_apply]
        simp [A]
      refine Subgroup.mem_map.mpr ⟨ψ, ?_, hψ_g⟩
      rw [hcm ψ]
      refine ⟨σ, fun f i => ?_⟩
      have h1 : hdRo7SULinAux_iota τ (Additive.ofMul (ψ (τ f))) =
          g (fun j => Multiplicative.toAdd (f j)) := by
        rw [← ggLin_apply_ofMul (p := p) (hdRo7SULinAux_iota τ) ψ (τ f), hψ_g,
          hdRo7SULinAux_iota_ofMul]
      have hcoord := hdRo7SULinAux_coord_formula g σ hσ
        (fun j => Multiplicative.toAdd (f j)) (σ i)
      rw [Equiv.symm_apply_apply] at hcoord
      exact (congrFun h1 (σ i)).trans hcoord

private theorem hdRo7SULinAux_model_of_coord {G : Type} [Group G] {p : ℕ} [Fact p.Prime]
    {Bs X : Subgroup G} {m : ℕ} {τ : (Fin m → Multiplicative (ZMod p)) ≃* ↥Bs}
    (hcm : SUCoordModel p Bs X m τ) (hp : p = 3) (hm : 7 ≤ m) (h3 : ¬ 3 ∣ m)
    {a : G} (ha : a ∈ Bs)
    (hτ : τ (fun _ => Multiplicative.ofAdd (1 : ZMod p)) = ⟨a, ha⟩) :
    SUModelAt p Bs X a := by
  obtain ⟨V, hV, hVp, ι, b, hb, hperm⟩ := su_linearModel_of_coord hcm ha hτ
  exact ⟨m, V, hV, hVp, ι, b, ha, hp, hm, h3, hb, hperm⟩

theorem su_lmodel_of_coord : SULCoordLeaf → GGLabelRigidInput → (∀ (G : Type) [Group G] [Finite G]
    (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G) (y : G) (K : Subgroup G), GGResHyp p B
    Bs x L D J y K → ∀ [Fact p.Prime], GGResRowAt ggRowSUCorank2 p J L → SUModelAt p Bs L x) := by
  intro hL hRig G _ _ p B Bs x L D J y K hH _ hrow
  obtain ⟨m, hx, τ, hp, hm, h3, hτ, hcm⟩ := hL hRig G p B Bs x L D J y K hH hrow
  exact hdRo7SULinAux_model_of_coord hcm hp hm h3 hx hτ

theorem su_kmodel_of_coord :
    SUKCoordLeaf → GGLabelRigidInput → GGLBalanceInput → (∀ (G : Type) [Group G] [Finite G] (p : ℕ)
        (B Bs : Subgroup G) (x : G) (L D J : Subgroup G) (y : G) (K : Subgroup G), GGResHyp p B Bs x
        L D J y K → ∀ [Fact p.Prime], GGResRowAt ggRowSUCorank2 p J K → SUModelAt p Bs K y) := by
  intro hK hRig hLB G _ _ p B Bs x L D J y K hH _ hrow
  obtain ⟨m, hy, τ, hp, hm, h3, hτ, hcm⟩ := hK hRig hLB G p B Bs x L D J y K hH hrow
  exact hdRo7SULinAux_model_of_coord hcm hp hm h3 hy hτ

end CFSG.StandardType.HdRo7SU
