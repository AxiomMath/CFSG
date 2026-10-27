module

public import CFSG.LocalAnalysis.StandardType.GGHdRo7CCoordDefs
public import CFSG.LocalAnalysis.StandardType.GGHdRo7CDefs

public section

namespace CFSG.StandardType.HdRo7C

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

private noncomputable def hdRo7CLinAux_single {p n : ℕ} (i : Fin (n + 1)) :
    Fin (n + 1) → Multiplicative (ZMod p) :=
  Pi.mulSingle i (Multiplicative.ofAdd (1 : ZMod p))

private noncomputable def hdRo7CLinAux_coordAdd (p : ℕ) (n : ℕ) :
    Additive (Fin (n + 1) → Multiplicative (ZMod p)) ≃+ (Fin (n + 1) → ZMod p) where
  toFun f := fun i => Multiplicative.toAdd (f i)
  invFun v := fun i => Multiplicative.ofAdd (v i)
  left_inv f := by
    funext i
    exact Equiv.symm_apply_apply Multiplicative.ofAdd (f i)
  right_inv v := by
    funext i
    exact Equiv.apply_symm_apply Multiplicative.ofAdd (v i)
  map_add' f g := by
    funext i
    exact rfl

private noncomputable def hdRo7CLinAux_iota {G : Type} [Group G] (p : ℕ) (Bs : Subgroup G)
    (n : ℕ) (τ : (Fin (n + 1) → Multiplicative (ZMod p)) ≃* ↥Bs) :
    Additive ↥Bs ≃+ (Fin (n + 1) → ZMod p) :=
  (MulEquiv.toAdditive τ.symm).trans (hdRo7CLinAux_coordAdd p n)

private theorem hdRo7CLinAux_iota_apply {G : Type} [Group G] (p : ℕ) (Bs : Subgroup G)
    (n : ℕ) (τ : (Fin (n + 1) → Multiplicative (ZMod p)) ≃* ↥Bs) (b : ↥Bs)
    (i : Fin (n + 1)) :
    hdRo7CLinAux_iota p Bs n τ (Additive.ofMul b) i = Multiplicative.toAdd (τ.symm b i) :=
  rfl

private theorem hdRo7CLinAux_iota_ofMul {G : Type} [Group G] (p : ℕ) (Bs : Subgroup G)
    (n : ℕ) (τ : (Fin (n + 1) → Multiplicative (ZMod p)) ≃* ↥Bs)
    (f : Fin (n + 1) → Multiplicative (ZMod p)) :
    hdRo7CLinAux_iota p Bs n τ (Additive.ofMul (τ f)) =
      fun i => Multiplicative.toAdd (f i) := by
  funext i
  rw [hdRo7CLinAux_iota_apply]
  simp

private theorem hdRo7CLinAux_iota_b0 {G : Type} [Group G] (p : ℕ) (Bs : Subgroup G)
    (n : ℕ) (τ : (Fin (n + 1) → Multiplicative (ZMod p)) ≃* ↥Bs) (z : G) (hz : z ∈ Bs)
    (hτ : τ (Pi.mulSingle 0 (Multiplicative.ofAdd (1 : ZMod p))) = ⟨z, hz⟩) :
    hdRo7CLinAux_iota p Bs n τ (Additive.ofMul (⟨z, hz⟩ : ↥Bs)) =
      Pi.basisFun (ZMod p) (Fin (n + 1)) 0 := by
  have hzτ : (⟨z, hz⟩ : ↥Bs) = τ (hdRo7CLinAux_single (p := p) (0 : Fin (n + 1))) := by
    rw [← hτ]
    rfl
  rw [hzτ, hdRo7CLinAux_iota_ofMul]
  funext i
  rw [Pi.basisFun_apply]
  by_cases hi : i = 0
  · subst hi
    simp [hdRo7CLinAux_single, Pi.mulSingle_apply, Pi.single_eq_same]
  · simp [hdRo7CLinAux_single, Pi.mulSingle_apply, Pi.single_eq_of_ne, hi]

private theorem hdRo7CLinAux_coord_apply {p : ℕ} [Fact p.Prime] {n : ℕ}
    (a : (Fin (n + 1) → ZMod p) ≃ₗ[ZMod p] (Fin (n + 1) → ZMod p))
    (σ : Equiv.Perm (Fin (n + 1))) (c : Fin (n + 1) → ZMod p)
    (ha : ∀ i, a (Pi.basisFun (ZMod p) (Fin (n + 1)) i) =
      c i • Pi.basisFun (ZMod p) (Fin (n + 1)) (σ i))
    (g : Fin (n + 1) → ZMod p) (i : Fin (n + 1)) :
    (a g) (σ i) = c i * g i := by
  have hg : g = ∑ j, g j • Pi.basisFun (ZMod p) (Fin (n + 1)) j := by
    conv_lhs => rw [← Module.Basis.sum_repr (Pi.basisFun (ZMod p) (Fin (n + 1))) g]
    apply Finset.sum_congr rfl
    intro j _
    rw [Pi.basisFun_repr]
  have h1 : a g = ∑ j, g j • (c j • Pi.basisFun (ZMod p) (Fin (n + 1)) (σ j)) := by
    conv_lhs => rw [hg]
    simp only [map_sum, map_smul, ha]
  rw [h1, Finset.sum_apply]
  rw [Finset.sum_eq_single i]
  · rw [Pi.smul_apply, Pi.smul_apply, Pi.basisFun_apply, Pi.single_eq_same]
    ring
  · intro j _ hj
    rw [Pi.smul_apply, Pi.smul_apply, Pi.basisFun_apply,
      Pi.single_eq_of_ne (by exact fun h => hj (σ.injective h).symm)]
    simp
  · intro h
    exact absurd (Finset.mem_univ i) h

private theorem hdRo7CLinAux_model {G : Type} [Group G] (p : ℕ) [Fact p.Prime]
    (Bs X : Subgroup G) (n : ℕ)
    (τ : (Fin (n + 1) → Multiplicative (ZMod p)) ≃* ↥Bs)
    (hcoord : C2CoordModel p Bs X n τ) :
    ∀ a, a ∈ (ggAutomizer X Bs).map (ggLin (p := p) (hdRo7CLinAux_iota p Bs n τ)) ↔
      C2SP p (Pi.basisFun (ZMod p) (Fin (n + 1))) a := by
  intro a
  constructor
  · intro ha
    obtain ⟨ψ, hψ, rfl⟩ := Subgroup.mem_map.mp ha
    obtain ⟨σ, c, hσ0, hc0, hcsign, hcoord'⟩ := (hcoord ψ).mp hψ
    refine ⟨σ, c, hσ0, hc0, hcsign, fun i => ?_⟩
    have hbi : Pi.basisFun (ZMod p) (Fin (n + 1)) i =
        hdRo7CLinAux_iota p Bs n τ (Additive.ofMul (τ (hdRo7CLinAux_single i))) := by
      rw [hdRo7CLinAux_iota_ofMul]
      funext j
      rw [Pi.basisFun_apply]
      by_cases hj : j = i
      · subst hj
        simp [hdRo7CLinAux_single, Pi.mulSingle_apply, Pi.single_eq_same]
      · simp [hdRo7CLinAux_single, Pi.mulSingle_apply, Pi.single_eq_of_ne, hj]
    rw [hbi, ggLin_apply_ofMul]
    funext k
    rw [hdRo7CLinAux_iota_apply]
    have hstep := hcoord' (hdRo7CLinAux_single i) (σ.symm k)
    rw [Equiv.apply_symm_apply] at hstep
    rw [hstep]
    have hf : Multiplicative.toAdd (hdRo7CLinAux_single i (σ.symm k)) =
        if k = σ i then (1 : ZMod p) else 0 := by
      rw [hdRo7CLinAux_single, Pi.mulSingle_apply]
      by_cases hk : σ.symm k = i
      · have hki : k = σ i := by rw [← hk, Equiv.apply_symm_apply]
        simp [hki]
      · have hki : k ≠ σ i := fun h => hk (by rw [h, Equiv.symm_apply_apply])
        simp [hk, hki]
    rw [hf, Pi.smul_apply, Pi.basisFun_apply]
    by_cases hk : k = σ i
    · subst hk
      simp
    · simp [Pi.single_eq_of_ne, hk]
  · rintro ⟨σ, c, hσ0, hc0, hcsign, ha⟩
    let ι : Additive ↥Bs ≃+ (Fin (n + 1) → ZMod p) := hdRo7CLinAux_iota p Bs n τ
    let e : Additive ↥Bs ≃+ Additive ↥Bs := ι.trans (a.toAddEquiv.trans ι.symm)
    let ψ : MulAut ↥Bs := AddEquiv.toMultiplicative e
    have hpoint : ∀ bb : ↥Bs,
        ggLin (p := p) ι ψ (ι (Additive.ofMul bb)) = a (ι (Additive.ofMul bb)) := by
      intro bb
      rw [ggLin_apply_ofMul]
      have hψbb : ψ bb = Additive.toMul (ι.symm (a (ι (Additive.ofMul bb)))) := rfl
      rw [hψbb]
      rw [show Additive.ofMul (Additive.toMul (ι.symm (a (ι (Additive.ofMul bb))))) =
          ι.symm (a (ι (Additive.ofMul bb))) from rfl, AddEquiv.apply_symm_apply]
    have hpointV : ∀ v : Fin (n + 1) → ZMod p,
        ggLin (p := p) ι ψ v = a v := by
      intro v
      have hb := hpoint (Additive.toMul (ι.symm v))
      have hbv : ι (Additive.ofMul (Additive.toMul (ι.symm v))) = v := by
        rw [show Additive.ofMul (Additive.toMul (ι.symm v)) = ι.symm v from rfl,
          AddEquiv.apply_symm_apply]
      rwa [hbv] at hb
    have hgg : ggLin (p := p) ι ψ = a := LinearEquiv.ext hpointV
    have hmem : ψ ∈ ggAutomizer X Bs := by
      refine (hcoord ψ).mpr ?_
      refine ⟨σ, c, hσ0, hc0, hcsign, fun f i => ?_⟩
      rw [← hdRo7CLinAux_iota_apply, ← ggLin_apply_ofMul (p := p) ι ψ (τ f),
        hpointV (ι (Additive.ofMul (τ f))), hdRo7CLinAux_iota_ofMul]
      exact hdRo7CLinAux_coord_apply a σ c ha (fun j => Multiplicative.toAdd (f j)) i
    exact Subgroup.mem_map.mpr ⟨ψ, hmem, hgg⟩

theorem c2_linearModel_of_coord {G : Type} [Group G] (p : ℕ) [Fact p.Prime]
    (Bs X : Subgroup G) (n : ℕ) (z : G) (hz : z ∈ Bs)
    (τ : (Fin (n + 1) → Multiplicative (ZMod p)) ≃* ↥Bs)
    (hτ : τ (Pi.mulSingle 0 (Multiplicative.ofAdd (1 : ZMod p))) = ⟨z, hz⟩)
    (hcoord : C2CoordModel p Bs X n τ) :
    ∃ (V : Type) (_ : AddCommGroup V) (_ : Module (ZMod p) V)
      (ι : Additive ↥Bs ≃+ V) (b : Module.Basis (Fin (n + 1)) (ZMod p) V),
      ι (Additive.ofMul (⟨z, hz⟩ : ↥Bs)) = b 0 ∧
        ∀ a, a ∈ (ggAutomizer X Bs).map (ggLin (p := p) ι) ↔ C2SP p b a := by
  exact ⟨Fin (n + 1) → ZMod p, inferInstance, inferInstance,
    hdRo7CLinAux_iota p Bs n τ, Pi.basisFun (ZMod p) (Fin (n + 1)),
    hdRo7CLinAux_iota_b0 p Bs n τ z hz hτ, hdRo7CLinAux_model p Bs X n τ hcoord⟩

theorem c2_lmodel_of_coord : C2LCoordLeaf → GGLabelRigidInput → C2LModelLeaf := by
  intro hleaf hRig
  intro G _ _ p B Bs x L D J y K hhyp hpFact hrow
  obtain ⟨n, hx, τ, hp3, hn5, hτx, hcoord⟩ := hleaf hRig G p B Bs x L D J y K hhyp hrow
  obtain ⟨V, hV, hVp, ι, b, hxb, hAL⟩ := c2_linearModel_of_coord p Bs L n x hx τ hτx hcoord
  exact ⟨n, V, hV, hVp, ι, b, hx, hp3, hn5, hxb, hAL⟩

theorem c2_kmodel_of_coord : C2KCoordLeaf → C2KModelLeaf := by
  intro hleaf
  intro hRig hBal
  intro G _ _ p B Bs x L D J y K hhyp hpFact hrow
  obtain ⟨n, hy, hx, τ, hp3, hn5, hτy, hcoord, c, hc⟩ :=
    hleaf hRig hBal G p B Bs x L D J y K hhyp hrow
  refine ⟨n, Fin (n + 1) → ZMod p, inferInstance, inferInstance,
    hdRo7CLinAux_iota p Bs n τ, Pi.basisFun (ZMod p) (Fin (n + 1)), hy, hx, hp3, hn5, ?_, ?_, ?_⟩
  · exact hdRo7CLinAux_iota_b0 p Bs n τ y hy hτy
  · exact hdRo7CLinAux_model p Bs K n τ hcoord
  · refine ⟨c, ?_⟩
    funext i
    have h10 : (1 : Fin (n + 1)) ≠ 0 := by
      apply Fin.ne_of_val_ne
      change (Fin.ofNat (n + 1) 1).val ≠ (Fin.ofNat (n + 1) 0).val
      rw [Fin.val_ofNat, Fin.val_ofNat]
      have h1 : 1 % (n + 1) = 1 := Nat.mod_eq_of_lt (by omega)
      have h0 : 0 % (n + 1) = 0 := Nat.zero_mod (n + 1)
      omega
    have h20 : (2 : Fin (n + 1)) ≠ 0 := by
      apply Fin.ne_of_val_ne
      change (Fin.ofNat (n + 1) 2).val ≠ (Fin.ofNat (n + 1) 0).val
      rw [Fin.val_ofNat, Fin.val_ofNat]
      have h2 : 2 % (n + 1) = 2 := Nat.mod_eq_of_lt (by omega)
      have h0 : 0 % (n + 1) = 0 := Nat.zero_mod (n + 1)
      omega
    have h21 : (2 : Fin (n + 1)) ≠ 1 := by
      apply Fin.ne_of_val_ne
      change (Fin.ofNat (n + 1) 2).val ≠ (Fin.ofNat (n + 1) 1).val
      rw [Fin.val_ofNat, Fin.val_ofNat]
      have h2 : 2 % (n + 1) = 2 := Nat.mod_eq_of_lt (by omega)
      have h1 : 1 % (n + 1) = 1 := Nat.mod_eq_of_lt (by omega)
      omega
    rw [hdRo7CLinAux_iota_apply, hc]
    rw [Pi.add_apply, Pi.add_apply, Pi.smul_apply]
    rw [Pi.basisFun_apply, Pi.basisFun_apply, Pi.basisFun_apply]
    by_cases h0 : i = 0
    · subst h0
      simp [Pi.single_eq_same, Pi.single_eq_of_ne, Ne.symm h10, Ne.symm h20]
    · by_cases h1 : i = 1
      · subst h1
        simp [Pi.single_eq_same, Pi.single_eq_of_ne, h10, Ne.symm h21]
      · by_cases h2 : i = 2
        · subst h2
          simp [Pi.single_eq_same, Pi.single_eq_of_ne, h20, h21]
        · simp [Pi.single_eq_of_ne, h0, h1, h2]

end CFSG.StandardType.HdRo7C
