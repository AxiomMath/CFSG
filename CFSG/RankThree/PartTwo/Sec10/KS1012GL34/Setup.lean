module

public import CFSG.RankThree.PartTwo.Sec10.KS1012GL34.Defs
public import CFSG.RankThree.PartTwo.Sec10.Item1012Res3ProofGL
public import CFSG.Fischer.F4
import all CFSG.Fischer.F4

public section

namespace CFSG.RankThree.PartTwo.Sec10.KS1012GL34

open CFSG CFSG.Fischer CFSG.RankThree.PartTwo.Sec10.Item1012Res3Proof

section Cyclic

variable {V : Type*} [AddCommGroup V] [Module F4 V]

theorem exists_cyclic_basis [Finite V] (X : V →ₗ[F4] V) (W : V ≃ₗ[F4] V)
    (hX3 : ∀ v, X (X (X v)) = v) (hWX : ∀ v, W (X v) = F4.ω • X (W v))
    (hfix : Nat.card {v : V // X v = v} = 4) :
    ∃ (v₀ : V) (μ : F4), v₀ ≠ 0 ∧ μ ≠ 0 ∧ X v₀ = v₀ ∧ ∃ b : Module.Basis (Fin 3) F4 V,
      b 0 = v₀ ∧ b 1 = W v₀ ∧ b 2 = W (W v₀) ∧ W (W (W v₀)) = μ • v₀ ∧
      ∀ i, X (b i) = ![1, F4.ω * F4.ω, F4.ω] i • b i := by
  have hω3 := omega_mul_omega_mul_omega
  obtain ⟨v₀, hv₀X, hv₀⟩ : ∃ v₀ : V, X v₀ = v₀ ∧ v₀ ≠ 0 := by
    by_contra hcon
    push Not at hcon
    have hsub : Subsingleton {v : V // X v = v} :=
      ⟨fun a b => Subtype.ext (by rw [hcon a.1 a.2, hcon b.1 b.2])⟩
    have h1 : Nat.card {v : V // X v = v} ≤ 1 := Finite.card_le_one_iff_subsingleton.mpr hsub
    omega
  have hE1 : ∀ u : V, X u = u → ∃ α : F4, u = α • v₀ := by
    intro u hu
    let f : F4 → {v : V // X v = v} := fun α => ⟨α • v₀, by rw [map_smul, hv₀X]⟩
    have hf : Function.Injective f := fun α β h =>
      smul_left_injective F4 hv₀ (congrArg Subtype.val h)
    have hbij := hf.bijective_of_nat_card_le (by
      rw [hfix, Nat.card_eq_fintype_card, F4.card])
    obtain ⟨α, hα⟩ := hbij.2 ⟨u, hu⟩
    exact ⟨α, (congrArg Subtype.val hα).symm⟩
  have hXW : ∀ v, X (W v) = (F4.ω * F4.ω) • W (X v) := by
    intro v
    rw [hWX, smul_smul, hω3, one_smul]
  set v₁ := W v₀ with hv₁def
  set v₂ := W v₁ with hv₂def
  have hv₁X : X v₁ = (F4.ω * F4.ω) • v₁ := by rw [hv₁def, hXW, hv₀X]
  have hv₂X : X v₂ = F4.ω • v₂ := by
    rw [hv₂def, hXW, hv₁X, map_smul, smul_smul,
      show F4.ω * F4.ω * (F4.ω * F4.ω) = F4.ω by decide]
  have hv₁ : v₁ ≠ 0 := fun h => hv₀ (W.injective (h.trans W.map_zero.symm))
  have hv₂ : v₂ ≠ 0 := fun h => hv₁ (W.injective (h.trans W.map_zero.symm))
  have hE2 : ∀ u : V, X u = (F4.ω * F4.ω) • u → ∃ α : F4, u = α • v₁ := by
    intro u hu
    have hfix' : X (W.symm u) = W.symm u := by
      apply W.injective
      rw [hWX, W.apply_symm_apply, hu, smul_smul,
        show F4.ω * (F4.ω * F4.ω) = 1 by decide, one_smul]
    obtain ⟨α, hα⟩ := hE1 _ hfix'
    refine ⟨α, ?_⟩
    rw [hv₁def, ← map_smul, ← hα, W.apply_symm_apply]
  have hE3 : ∀ u : V, X u = F4.ω • u → ∃ α : F4, u = α • v₂ := by
    intro u hu
    have h2 : X (W.symm u) = (F4.ω * F4.ω) • W.symm u := by
      apply W.injective
      rw [hWX, W.apply_symm_apply, hu, map_smul, W.apply_symm_apply, smul_smul]
    obtain ⟨α, hα⟩ := hE2 _ h2
    refine ⟨α, ?_⟩
    rw [hv₂def, ← map_smul, ← hα, W.apply_symm_apply]
  have hfixW3 : X (W (W (W v₀))) = W (W (W v₀)) := by
    have h6 : F4.ω * F4.ω * (F4.ω * F4.ω * (F4.ω * F4.ω)) = 1 := by decide
    rw [hXW, hXW, hXW, hv₀X]
    simp only [map_smul, smul_smul, h6, one_smul]
  obtain ⟨μ, hμ⟩ := hE1 _ hfixW3
  have hμ0 : μ ≠ 0 := by
    rintro rfl
    rw [zero_smul] at hμ
    have h1 : W (W v₀) = 0 := W.injective (hμ.trans W.map_zero.symm)
    exact hv₁ (W.injective (h1.trans W.map_zero.symm))
  set μ' : Fin 3 → F4 := ![1, F4.ω * F4.ω, F4.ω] with hμ'
  set vs : Fin 3 → V := ![v₀, v₁, v₂] with hvs
  have hvsX : ∀ i, X (vs i) = μ' i • vs i := by
    intro i
    fin_cases i
    · simp [hvs, hμ', hv₀X]
    · simp [hvs, hμ', hv₁X]
    · simp [hvs, hμ', hv₂X]
  have hli : LinearIndependent F4 vs := by
    refine Module.End.eigenvectors_linearIndependent' X μ' (by decide) vs fun i => ?_
    rw [Module.End.hasEigenvector_iff, Module.End.mem_eigenspace_iff]
    refine ⟨hvsX i, ?_⟩
    fin_cases i
    · simpa [hvs] using hv₀
    · simpa [hvs] using hv₁
    · simpa [hvs] using hv₂
  have hsp : ⊤ ≤ Submodule.span F4 (Set.range vs) := by
    intro v _
    have hp₀ : X (v + X v + X (X v)) = v + X v + X (X v) := by
      simp only [map_add, hX3]
      abel
    have hp₁ : X (v + F4.ω • X v + (F4.ω * F4.ω) • X (X v)) =
        (F4.ω * F4.ω) • (v + F4.ω • X v + (F4.ω * F4.ω) • X (X v)) := by
      simp only [map_add, map_smul, hX3]
      match_scalars <;> decide
    have hp₂ : X (v + (F4.ω * F4.ω) • X v + F4.ω • X (X v)) =
        F4.ω • (v + (F4.ω * F4.ω) • X v + F4.ω • X (X v)) := by
      simp only [map_add, map_smul, hX3]
      match_scalars <;> decide
    obtain ⟨α, hα⟩ := hE1 _ hp₀
    obtain ⟨β, hβ⟩ := hE2 _ hp₁
    obtain ⟨γ, hγ⟩ := hE3 _ hp₂
    have hv : v = (v + X v + X (X v)) + (v + F4.ω • X v + (F4.ω * F4.ω) • X (X v)) +
        (v + (F4.ω * F4.ω) • X v + F4.ω • X (X v)) := by
      match_scalars <;> decide
    rw [hv, hα, hβ, hγ]
    have hmem : ∀ i, vs i ∈ Submodule.span F4 (Set.range vs) := fun i =>
      Submodule.subset_span ⟨i, rfl⟩
    refine Submodule.add_mem _ (Submodule.add_mem _ (Submodule.smul_mem _ _ (hmem 0))
      (Submodule.smul_mem _ _ (hmem 1))) (Submodule.smul_mem _ _ (hmem 2))
  refine ⟨v₀, μ, hv₀, hμ0, hv₀X, Module.Basis.mk hli hsp, ?_, ?_, ?_, ?_, ?_⟩
  · rw [Module.Basis.mk_apply]
    simp [hvs]
  · rw [Module.Basis.mk_apply]
    simp [hvs, hv₁def]
  · rw [Module.Basis.mk_apply]
    simp [hvs, hv₂def, hv₁def]
  · exact hμ
  · intro i
    rw [Module.Basis.mk_apply]
    exact hvsX i

end Cyclic

theorem exists_gl3_model (S : Type) [Group S] [Finite S] (hcomm : ∀ s t : S, s * t = t * s)
    (hexp : ∀ s : S, s ^ 2 = 1) (Y : Subgroup (MulAut S)) (z x w : MulAut S)
    (hzY : z ∈ Y) (hxY : x ∈ Y) (hwY : w ∈ Y) (hzc : ∀ y ∈ Y, y * z = z * y) (hz3 : z ^ 3 = 1)
    (hzfix : ∀ s : S, z s = s → s = 1) (hx3 : x ^ 3 = 1)
    (hxfix : Nat.card {s : S // x s = s} = 4) (hwx : w * x * w⁻¹ = x * z) :
    ∃ ρ : Y →* Matrix.GeneralLinearGroup (Fin 3) F4, Function.Injective ρ ∧
      ∃ μ : F4, μ ≠ 0 ∧
        ((ρ ⟨x, hxY⟩ : Matrix.GeneralLinearGroup (Fin 3) F4) : Matrix (Fin 3) (Fin 3) F4) = Xd ∧
        ((ρ ⟨z, hzY⟩ : Matrix.GeneralLinearGroup (Fin 3) F4) : Matrix (Fin 3) (Fin 3) F4) = Zs ∧
        ((ρ ⟨w, hwY⟩ : Matrix.GeneralLinearGroup (Fin 3) F4) : Matrix (Fin 3) (Fin 3) F4) =
          Wm μ := by
  have hzz := apply_apply_eq_mul hcomm hexp hz3 hzfix
  let _ : AddCommGroup (Additive S) :=
    { (inferInstance : AddGroup (Additive S)) with
      add_comm := fun a b => hcomm (Additive.toMul a) (Additive.toMul b) }
  let _ : Module (ZMod 2) (Additive S) := AddCommGroup.zmodModule (n := 2) (fun v => by
    change Additive.ofMul (Additive.toMul v ^ 2) = Additive.ofMul 1
    rw [hexp])
  set Z : Additive S →ₗ[ZMod 2] Additive S :=
    (MulEquiv.toAdditive z).toAddMonoidHom.toZModLinearMap 2
  have hZapp : ∀ v, Z v = Additive.ofMul (z (Additive.toMul v)) := fun v => rfl
  have hZ : ∀ v, Z (Z v) = v + Z v := fun v => by
    rw [hZapp, hZapp]
    exact hzz (Additive.toMul v)
  let _ : Module F4 (Additive S) := Module.compHom (Additive S) (f4Hom Z hZ)
  have hsmul : ∀ (r : F4) (v : Additive S), r • v = c0 r • v + c1 r • Z v := fun r v => rfl
  have hω : ∀ v : Additive S, F4.ω • v = Z v := fun v => by
    rw [hsmul, c0_omega, c1_omega, zero_smul, one_smul, zero_add]
  have hlin : ∀ y : MulAut S, y * z = z * y → ∀ (r : F4) (v : Additive S),
      (MulEquiv.toAdditive y) (r • v) = r • (MulEquiv.toAdditive y) v := by
    intro y hy r v
    have hyZ : (MulEquiv.toAdditive y) (Z v) = Z ((MulEquiv.toAdditive y) v) := by
      change Additive.ofMul (y (z (Additive.toMul v))) =
        Additive.ofMul (z (y (Additive.toMul v)))
      rw [← MulAut.mul_apply, hy, MulAut.mul_apply]
    have hE : ∀ (c : ZMod 2) (u : Additive S),
        (MulEquiv.toAdditive y) (c • u) = c • (MulEquiv.toAdditive y) u := fun c u =>
      ((MulEquiv.toAdditive y).toAddMonoidHom.toZModLinearMap 2).map_smul c u
    rw [hsmul, hsmul, map_add, hE, hE, hyZ]
  let ρ₀ : Y →* (Additive S ≃ₗ[F4] Additive S) :=
    { toFun := fun y => (MulEquiv.toAdditive (y : MulAut S)).toLinearEquiv
        (hlin y (hzc y y.2))
      map_one' := by
        ext v
        rfl
      map_mul' := fun y y' => by
        ext v
        rfl }
  have hρapp : ∀ (y : Y) (v : Additive S),
      ρ₀ y v = Additive.ofMul ((y : MulAut S) (Additive.toMul v)) := fun y v => rfl
  have hρinj : Function.Injective ρ₀ := by
    rw [injective_iff_map_eq_one]
    intro y hy
    apply Subtype.ext
    ext s
    have h := congrArg (fun f : Additive S ≃ₗ[F4] Additive S => f (Additive.ofMul s)) hy
    exact congrArg Additive.toMul h
  set X : Additive S ≃ₗ[F4] Additive S := ρ₀ ⟨x, hxY⟩ with hXdef
  set W : Additive S ≃ₗ[F4] Additive S := ρ₀ ⟨w, hwY⟩ with hWdef
  have hX3 : ∀ v, X (X (X v)) = v := by
    intro v
    rw [hXdef, hρapp, hρapp, hρapp]
    have h := congrArg (fun f : MulAut S => f (Additive.toMul v)) hx3
    have h' : x (x (x (Additive.toMul v))) = Additive.toMul v := by
      simpa [pow_succ, MulAut.mul_apply] using h
    simp only [toMul_ofMul]
    rw [h']
    rfl
  have hWX : ∀ v, W (X v) = F4.ω • X (W v) := by
    intro v
    rw [hω, hZapp, hWdef, hXdef, hρapp, hρapp, hρapp, hρapp]
    congr 1
    have hwx' : w * x = z * (x * w) := by
      have h1 : w * x = x * z * w := by
        rw [← hwx]
        group
      rw [h1, hzc x hxY]
      group
    simp only [toMul_ofMul]
    have h := congrArg (fun f : MulAut S => f (Additive.toMul v)) hwx'
    simpa [MulAut.mul_apply] using h
  have hfix : Nat.card {v : Additive S // X v = v} = 4 := by
    rw [← hxfix]
    refine Nat.card_congr
      { toFun := fun v => ⟨Additive.toMul v.1, congrArg Additive.toMul v.2⟩
        invFun := fun s => ⟨Additive.ofMul s.1, congrArg Additive.ofMul s.2⟩
        left_inv := fun v => rfl
        right_inv := fun s => rfl }
  obtain ⟨_, μ, _, hμ, _, b, hb0, hb1, hb2, hW3, hb⟩ :=
    exists_cyclic_basis (X : Additive S →ₗ[F4] Additive S) W hX3 hWX hfix
  let ψ : (Additive S ≃ₗ[F4] Additive S) ≃* Matrix.GeneralLinearGroup (Fin 3) F4 :=
    (LinearMap.GeneralLinearGroup.generalLinearEquiv F4 (Additive S)).symm.trans
      (Units.mapEquiv (LinearMap.toMatrixAlgEquiv b).toRingEquiv.toMulEquiv)
  have hψ : ∀ f : Additive S ≃ₗ[F4] Additive S,
      ((ψ f : Matrix.GeneralLinearGroup (Fin 3) F4) : Matrix (Fin 3) (Fin 3) F4) =
        LinearMap.toMatrix b b (f : Additive S →ₗ[F4] Additive S) := fun f => rfl
  refine ⟨ψ.toMonoidHom.comp ρ₀, ψ.injective.comp hρinj, μ, hμ, ?_, ?_, ?_⟩
  ·
    show ((ψ (ρ₀ ⟨x, hxY⟩) : Matrix.GeneralLinearGroup (Fin 3) F4) : Matrix (Fin 3) (Fin 3) F4) = Xd
    rw [hψ]
    rw [toMatrix_eq_diagonal b (X : Additive S →ₗ[F4] Additive S) _ hb]
    rfl
  ·
    have hzρ : ((ρ₀ ⟨z, hzY⟩ : Additive S ≃ₗ[F4] Additive S) : Additive S →ₗ[F4] Additive S) =
        F4.ω • LinearMap.id := by
      ext v
      rw [LinearMap.smul_apply, LinearMap.id_apply, LinearEquiv.coe_coe, hω v]
      exact (hρapp ⟨z, hzY⟩ v).trans (hZapp v).symm
    show ((ψ (ρ₀ ⟨z, hzY⟩) : Matrix.GeneralLinearGroup (Fin 3) F4) : Matrix (Fin 3) (Fin 3) F4) = Zs
    rw [hψ, hzρ, map_smul, LinearMap.toMatrix_id]
    rfl
  ·
    have e0 : W (b 0) = b 1 := by rw [hb0, hb1]
    have e1 : W (b 1) = b 2 := by rw [hb1, hb2]
    have e2 : W (b 2) = μ • b 0 := by rw [hb2, hb0, hW3]
    have hWmat : LinearMap.toMatrix b b (W : Additive S →ₗ[F4] Additive S) = Wm μ := by
      ext i j
      rw [LinearMap.toMatrix_apply]
      fin_cases j <;> fin_cases i <;>
        simp [Wm, e0, e1, e2, Finsupp.single_apply]
    show ((ψ (ρ₀ ⟨w, hwY⟩) : Matrix.GeneralLinearGroup (Fin 3) F4) : Matrix (Fin 3) (Fin 3) F4) =
      Wm μ
    rw [hψ]
    exact hWmat

end CFSG.RankThree.PartTwo.Sec10.KS1012GL34

end
