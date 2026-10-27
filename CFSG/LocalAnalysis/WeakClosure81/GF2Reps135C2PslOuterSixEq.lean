module

public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2PslOuterSixEqPart1
public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2FinLinearEndField

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open Matrix
open CFSG.LieType.SpecialLinear CFSG.LieType.SpecialLinear.ExteriorModel
open CFSG.HardMathSupport.Meierfrankenfeld.PSUScalar

theorem w135c2_six_three_graph_eq {K : Type} [Field K] [Fintype K] [CharP K 2]
    (hK : Fintype.card K = 2) {W : Type} [AddCommGroup W] [Module (ZMod 2) W] [Finite W]
    (ρ : Representation (ZMod 2) (Matrix.SpecialLinearGroup (Fin 6) K) W)
    (hirr : ρ.IsIrreducible) (hne : ∃ x, ρ x ≠ 1)
    (β : W ≃+ (Set.powersetCard (Fin 6) 3 → K))
    (hβ : ∀ (g : Matrix.SpecialLinearGroup (Fin 6) K) (w : W),
      β (ρ g w) = extTwist 6 3 0 K g *ᵥ β w)
    {d : W ≃ₗ[ZMod 2] W} {B : Matrix.GeneralLinearGroup (Fin 6) K} {τ : K ≃+* K}
    (hd : ∀ (x : Matrix.SpecialLinearGroup (Fin 6) K) (w : W),
      d (ρ x w) = ρ (borelStd 6 K B τ 1 x) (d w)) (w : W) :
    β (d w) = Matrix.mulVecLin (minor (B : Matrix (Fin 6) (Fin 6) K) :
        Matrix (Set.powersetCard (Fin 6) 3) (Set.powersetCard (Fin 6) 3) K)
      (revMap (R := K) (n := 3) (m := 6) (by norm_num) (β w)) := by
  classical
  have hτ : τ = RingEquiv.refl K := c2slout6e_ringEquiv_eq_refl hK τ
  let V := Set.powersetCard (Fin 6) 3 → K
  let hn : 3 ≤ 6 := by norm_num
  set PB : Matrix (Set.powersetCard (Fin 6) 3) (Set.powersetCard (Fin 6) 3) K :=
    (minor (B : Matrix (Fin 6) (Fin 6) K) :
      Matrix (Set.powersetCard (Fin 6) 3) (Set.powersetCard (Fin 6) 3) K) with hPB
  set PBinv : Matrix (Set.powersetCard (Fin 6) 3) (Set.powersetCard (Fin 6) 3) K :=
    (minor (((B⁻¹ : Matrix.GeneralLinearGroup (Fin 6) K) : Matrix (Fin 6) (Fin 6) K)) :
      Matrix (Set.powersetCard (Fin 6) 3) (Set.powersetCard (Fin 6) 3) K) with hPBinv
  have hPP' : PB * PBinv = 1 := by
    rw [hPB, hPBinv]
    change minorMatrix 3 (B : Matrix (Fin 6) (Fin 6) K) *
      minorMatrix 3 (((B⁻¹ : Matrix.GeneralLinearGroup (Fin 6) K) :
        Matrix (Fin 6) (Fin 6) K)) = 1
    have h1 : (B : Matrix (Fin 6) (Fin 6) K) *
        ((B⁻¹ : Matrix.GeneralLinearGroup (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) = 1 := by
      rw [← Matrix.GeneralLinearGroup.coe_mul, mul_inv_cancel, Matrix.GeneralLinearGroup.coe_one]
    rw [← minorMatrix_mul, h1, minorMatrix_one]
  have hP'P : PBinv * PB = 1 := by
    rw [hPBinv, hPB]
    change minorMatrix 3 (((B⁻¹ : Matrix.GeneralLinearGroup (Fin 6) K) :
        Matrix (Fin 6) (Fin 6) K)) *
      minorMatrix 3 (B : Matrix (Fin 6) (Fin 6) K) = 1
    have h1 : ((B⁻¹ : Matrix.GeneralLinearGroup (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) *
        (B : Matrix (Fin 6) (Fin 6) K) = 1 := by
      rw [← Matrix.GeneralLinearGroup.coe_mul, inv_mul_cancel, Matrix.GeneralLinearGroup.coe_one]
    rw [← minorMatrix_mul, h1, minorMatrix_one]
  haveI hntW : Nontrivial W := by
    obtain ⟨x, hx⟩ := hne
    have hx' : ¬ ∀ y : W, ρ x y = y := by
      intro hy
      exact hx (LinearMap.ext fun y => by simpa using hy y)
    rw [not_forall] at hx'
    obtain ⟨y, hy⟩ := hx'
    exact ⟨ρ x y, y, hy⟩
  let rev : V ≃ₗ[K] V := revMap (R := K) (n := 3) (m := 6) hn
  let mulPA : V ≃+ V :=
    { toFun := fun v => PB *ᵥ v
      invFun := fun v => PBinv *ᵥ v
      left_inv := fun v => by
        show PBinv *ᵥ (PB *ᵥ v) = v
        rw [Matrix.mulVec_mulVec, hP'P, Matrix.one_mulVec]
      right_inv := fun v => by
        show PB *ᵥ (PBinv *ᵥ v) = v
        rw [Matrix.mulVec_mulVec, hPP', Matrix.one_mulVec]
      map_add' := fun a b => Matrix.mulVec_add PB a b }
  let D0a : V ≃+ V := rev.toAddEquiv.trans mulPA
  letI : Module (ZMod 2) V :=
    AddCommGroup.zmodModule (G := V) (n := 2) fun x => by
      ext s
      show (2 : ℕ) • x s = 0
      rw [two_nsmul, ← two_mul]
      have h2 : (2 : K) = 0 := CharP.cast_eq_zero K 2
      rw [h2, zero_mul]
  let D0z : V ≃ₗ[ZMod 2] V := D0a.toLinearEquiv fun c v => ZMod.map_smul (n := 2) D0a c v
  let βlin : W ≃ₗ[ZMod 2] V := β.toLinearEquiv fun c x => ZMod.map_smul (n := 2) β c x
  let D'e : W ≃ₗ[ZMod 2] W := (βlin.trans D0z).trans βlin.symm
  have hD0 : ∀ (g : Matrix.SpecialLinearGroup (Fin 6) K) (v : V),
      D0a (extTwist 6 3 0 K g *ᵥ v) =
        extTwist 6 3 0 K (borelStd 6 K B τ 1 g) *ᵥ D0a v := by
    intro g v
    change (minor (B : Matrix (Fin 6) (Fin 6) K) :
        Matrix (Set.powersetCard (Fin 6) 3) (Set.powersetCard (Fin 6) 3) K) *ᵥ
        revMap (R := K) (n := 3) (m := 6) hn (extTwist 6 3 0 K g *ᵥ v) =
      extTwist 6 3 0 K (borelStd 6 K B τ 1 g) *ᵥ
        ((minor (B : Matrix (Fin 6) (Fin 6) K) :
          Matrix (Set.powersetCard (Fin 6) 3) (Set.powersetCard (Fin 6) 3) K) *ᵥ
          revMap (R := K) (n := 3) (m := 6) hn v)
    rw [c2slout6e_extTwist_zero_eq_minor, c2slout6e_extTwist_zero_eq_minor]
    exact c2slout6e_minor_revMap_borelStd hK B τ hτ g v
  have hD' : ∀ (x : Matrix.SpecialLinearGroup (Fin 6) K) (u : W),
      D'e (ρ x u) = ρ (borelStd 6 K B τ 1 x) (D'e u) := by
    intro x u
    apply βlin.injective
    have h1 : βlin (D'e (ρ x u)) = D0z (βlin (ρ x u)) := by simp [D'e]
    rw [h1]
    have h2 : βlin (ρ x u) = extTwist 6 3 0 K x *ᵥ βlin u := by
      change β (ρ x u) = extTwist 6 3 0 K x *ᵥ β u
      exact hβ x u
    rw [h2]
    have h3 : βlin (ρ (borelStd 6 K B τ 1 x) (D'e u)) =
        extTwist 6 3 0 K (borelStd 6 K B τ 1 x) *ᵥ βlin (D'e u) := by
      change β (ρ (borelStd 6 K B τ 1 x) (D'e u)) =
        extTwist 6 3 0 K (borelStd 6 K B τ 1 x) *ᵥ β (D'e u)
      exact hβ (borelStd 6 K B τ 1 x) (D'e u)
    rw [h3]
    have h4 : βlin (D'e u) = D0z (βlin u) := by simp [D'e]
    rw [h4]
    change D0a (extTwist 6 3 0 K x *ᵥ βlin u) =
      extTwist 6 3 0 K (borelStd 6 K B τ 1 x) *ᵥ D0a (βlin u)
    exact hD0 x (βlin u)
  let c : W ≃ₗ[ZMod 2] W := d.trans D'e.symm
  have hc : ∀ (x : Matrix.SpecialLinearGroup (Fin 6) K) (u : W),
      c (ρ x u) = ρ x (c u) := by
    intro x u
    have hsym : D'e.symm (ρ (borelStd 6 K B τ 1 x) (d u)) = ρ x (D'e.symm (d u)) := by
      apply D'e.injective
      rw [D'e.apply_symm_apply, hD' x (D'e.symm (d u)), D'e.apply_symm_apply]
    show D'e.symm (d (ρ x u)) = ρ x (D'e.symm (d u))
    rw [hd x u, hsym]
  let cIM : ρ.IntertwiningMap ρ :=
    { toLinearMap := c.toLinearMap
      isIntertwining' := fun x => LinearMap.ext fun u => hc x u }
  have hcardEnd : Nat.card (Module.End (MonoidAlgebra (ZMod 2)
      (Matrix.SpecialLinearGroup (Fin 6) K)) ρ.asModule) = 2 :=
    card_endField_eq_two_of_card_eq_two hK (by norm_num : 2 ≤ 6) ρ hirr
  have hcard : Nat.card (ρ.IntertwiningMap ρ) = 2 :=
    (Nat.card_congr (Representation.IntertwiningMap.equivAlgEnd ρ).toEquiv).trans hcardEnd
  have htwo : ∀ f : ρ.IntertwiningMap ρ, f = 0 ∨ f = 1 := by
    obtain ⟨y, hy, hyu⟩ := (Nat.card_eq_two_iff' (0 : ρ.IntertwiningMap ρ)).1 hcard
    haveI : Nontrivial (ρ.IntertwiningMap ρ) := ⟨⟨y, 0, hy⟩⟩
    intro f
    by_cases hf : f = 0
    · exact Or.inl hf
    · right
      have h1y : (1 : ρ.IntertwiningMap ρ) = y := hyu 1 one_ne_zero
      exact (hyu f hf).trans h1y.symm
  have hcne : cIM ≠ 0 := by
    intro h0
    have hfun : ∀ u, c u = 0 := by
      intro u
      have hcongr := congrArg (fun f : ρ.IntertwiningMap ρ => f u) h0
      change c u = 0 at hcongr
      exact hcongr
    obtain ⟨u, hu⟩ := exists_ne (0 : W)
    have hu0 : c u = 0 := hfun u
    exact hu (c.injective (by rw [hu0, map_zero]))
  have hc1 : cIM = 1 := by
    rcases htwo cIM with h | h
    · exact absurd h hcne
    · exact h
  have hc_eq : c = 1 := by
    have hlin : c.toLinearMap = (1 : ρ.IntertwiningMap ρ).toLinearMap := by
      have hcongr := congrArg (fun f : ρ.IntertwiningMap ρ => f.toLinearMap) hc1
      simpa [cIM] using hcongr
    ext u
    have hcongr := congrArg (fun f : W →ₗ[ZMod 2] W => f u) hlin
    simpa using hcongr
  have hdD' : ∀ u, d u = D'e u := by
    intro u
    have hcu : c u = u := by rw [hc_eq]; rfl
    have hcongr := congrArg D'e hcu
    have h1 : D'e (c u) = d u := by
      change D'e (D'e.symm (d u)) = d u
      exact D'e.apply_symm_apply (d u)
    rw [h1] at hcongr
    exact hcongr
  rw [hdD' w]
  have hβD' : β (D'e w) = PB *ᵥ revMap (R := K) (n := 3) (m := 6) hn (β w) := by
    simp [D'e, D0a, D0z, rev, mulPA, βlin]
  rw [hβD']
  change PB *ᵥ revMap (R := K) (n := 3) (m := 6) hn (β w) =
    Matrix.mulVecLin (minor (B : Matrix (Fin 6) (Fin 6) K) :
      Matrix (Set.powersetCard (Fin 6) 3) (Set.powersetCard (Fin 6) 3) K)
      (revMap (R := K) (n := 3) (m := 6) (by norm_num) (β w))
  rfl

end CFSG.LocalAnalysis.WeakClosure81
