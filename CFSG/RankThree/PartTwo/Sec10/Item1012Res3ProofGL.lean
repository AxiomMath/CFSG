module

public import CFSG.RankThree.PartTwo.Sec10.Item1012Res2Proof
public import CFSG.Fischer.F4
import all CFSG.Fischer.F4

public section

namespace CFSG.RankThree.PartTwo.Sec10.Item1012Res3Proof

open CFSG CFSG.Fischer

@[expose] def c0 (r : F4) : ZMod 2 := ((r.code : ℕ) % 2 : ℕ)

@[expose] def c1 (r : F4) : ZMod 2 := ((r.code : ℕ) / 2 : ℕ)

theorem c0_mul : ∀ r t : F4, c0 (r * t) = c0 r * c0 t + c1 r * c1 t := by decide

theorem c1_mul : ∀ r t : F4, c1 (r * t) = c0 r * c1 t + c1 r * c0 t + c1 r * c1 t := by decide

theorem c0_add : ∀ r t : F4, c0 (r + t) = c0 r + c0 t := by decide

theorem c1_add : ∀ r t : F4, c1 (r + t) = c1 r + c1 t := by decide

theorem c0_one : c0 1 = 1 := by decide

theorem c1_one : c1 1 = 0 := by decide

theorem c0_zero : c0 0 = 0 := by decide

theorem c1_zero : c1 0 = 0 := by decide

theorem c0_omega : c0 F4.ω = 0 := by decide

theorem c1_omega : c1 F4.ω = 1 := by decide

section F4Hom

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]

@[expose] def f4Hom (Z : V →ₗ[ZMod 2] V) (hZ : ∀ v, Z (Z v) = v + Z v) :
    F4 →+* Module.End (ZMod 2) V where
  toFun r := c0 r • 1 + c1 r • Z
  map_one' := by
    rw [c0_one, c1_one, one_smul, zero_smul, add_zero]
  map_mul' r t := by
    ext v
    simp only [Module.End.mul_apply, LinearMap.add_apply, LinearMap.smul_apply,
      Module.End.one_apply, map_add, map_smul, hZ, c0_mul, c1_mul]
    module
  map_zero' := by
    rw [c0_zero, c1_zero, zero_smul, zero_smul, add_zero]
  map_add' r t := by
    ext v
    simp only [LinearMap.add_apply, LinearMap.smul_apply, Module.End.one_apply, c0_add,
      c1_add]
    module

end F4Hom

section LinearAlgebra

variable {V : Type*} [AddCommGroup V] [Module F4 V]

theorem omega_mul_omega_mul_omega : F4.ω * F4.ω * F4.ω = 1 := by decide

theorem exists_basis_eigen [Finite V] (X : V →ₗ[F4] V) (W : V ≃ₗ[F4] V)
    (hX3 : ∀ v, X (X (X v)) = v) (hWX : ∀ v, W (X v) = F4.ω • X (W v))
    (hfix : Nat.card {v : V // X v = v} = 4) :
    ∃ b : Module.Basis (Fin 3) F4 V, ∀ i, X (b i) = ![1, F4.ω * F4.ω, F4.ω] i • b i := by
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
  set μ : Fin 3 → F4 := ![1, F4.ω * F4.ω, F4.ω] with hμ
  set vs : Fin 3 → V := ![v₀, v₁, v₂] with hvs
  have hvsX : ∀ i, X (vs i) = μ i • vs i := by
    intro i
    fin_cases i
    · simp [hvs, hμ, hv₀X]
    · simp [hvs, hμ, hv₁X]
    · simp [hvs, hμ, hv₂X]
  have hli : LinearIndependent F4 vs := by
    refine Module.End.eigenvectors_linearIndependent' X μ (by decide) vs fun i => ?_
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
  refine ⟨Module.Basis.mk hli hsp, fun i => ?_⟩
  rw [Module.Basis.mk_apply]
  exact hvsX i

theorem toMatrix_eq_diagonal {ι : Type*} [Fintype ι] [DecidableEq ι] (b : Module.Basis ι F4 V)
    (f : V →ₗ[F4] V) (μ : ι → F4) (hf : ∀ i, f (b i) = μ i • b i) :
    LinearMap.toMatrix b b f = Matrix.diagonal μ := by
  ext i j
  rw [LinearMap.toMatrix_apply, hf, map_smul, b.repr_self, Finsupp.smul_single, smul_eq_mul,
    mul_one, Finsupp.single_apply, Matrix.diagonal_apply]
  by_cases hij : i = j
  · subst hij
    simp
  · simp [hij, Ne.symm hij]

theorem card_ker_det_dvd (b : Module.Basis (Fin 3) F4 V) :
    Nat.card (LinearEquiv.det : (V ≃ₗ[F4] V) →* F4ˣ).ker ∣ 60480 := by
  let σ : (LinearEquiv.det : (V ≃ₗ[F4] V) →* F4ˣ).ker →*
      Matrix.SpecialLinearGroup (Fin 3) F4 :=
    { toFun := fun f => ⟨LinearMap.toMatrix b b (f.1 : V →ₗ[F4] V), by
        rw [LinearMap.det_toMatrix, ← LinearEquiv.coe_det, (MonoidHom.mem_ker).mp f.2,
          Units.val_one]⟩
      map_one' := by
        apply Subtype.ext
        change LinearMap.toMatrix b b ((1 : V ≃ₗ[F4] V) : V →ₗ[F4] V) = 1
        exact LinearMap.toMatrix_id b
      map_mul' := fun f g => by
        apply Subtype.ext
        change LinearMap.toMatrix b b ((f.1 * g.1 : V ≃ₗ[F4] V) : V →ₗ[F4] V) =
          LinearMap.toMatrix b b (f.1 : V →ₗ[F4] V) * LinearMap.toMatrix b b (g.1 : V →ₗ[F4] V)
        rw [LinearEquiv.coe_toLinearMap_mul, LinearMap.toMatrix_mul] }
  have hσ : Function.Injective σ := by
    intro f g h
    have h' : LinearMap.toMatrix b b (f.1 : V →ₗ[F4] V) =
        LinearMap.toMatrix b b (g.1 : V →ₗ[F4] V) :=
      congrArg (fun A : Matrix.SpecialLinearGroup (Fin 3) F4 =>
        (A : Matrix (Fin 3) (Fin 3) F4)) h
    exact Subtype.ext (LinearEquiv.toLinearMap_injective ((LinearMap.toMatrix b b).injective h'))
  have h1 := Subgroup.card_dvd_of_injective σ hσ
  rw [Matrix.card_SL_field, F4.card] at h1
  simpa [Fin.prod_univ_three] using h1

end LinearAlgebra

theorem mem_of_card_dvd {Q : Type*} [Group Q] [Finite Q] (P : Subgroup Q) [P.Normal]
    (hQ : Nat.card Q ∣ 60480) (hP : Nat.card P = 60480 ∨ Nat.card P = 1080) {x : Q}
    (hx : x ^ 3 = 1) : x ∈ P := by
  have hidx : ¬ 3 ∣ P.index := by
    rintro ⟨k, hk⟩
    have h := P.card_mul_index
    rw [hk] at h
    have h3 : Nat.card P * 3 ∣ 60480 :=
      (Nat.mul_dvd_mul_left _ (dvd_mul_right 3 k)).trans (h ▸ hQ)
    rcases hP with hP | hP <;> rw [hP] at h3 <;> norm_num at h3
  have hmem := P.pow_index_mem x
  have hsplit : x ^ P.index = x ^ (P.index % 3) := by
    conv_lhs => rw [← Nat.div_add_mod P.index 3, pow_add, pow_mul, hx, one_pow, one_mul]
  rw [hsplit] at hmem
  have hmod : P.index % 3 = 1 ∨ P.index % 3 = 2 := by omega
  rcases hmod with h1 | h2
  · rwa [h1, pow_one] at hmem
  · rw [h2] at hmem
    have hx4 : x = (x ^ 2) ^ 2 := by
      rw [← pow_mul, show 2 * 2 = 3 + 1 by norm_num, pow_add, hx, one_mul, pow_one]
    rw [hx4]
    exact P.pow_mem hmem 2

theorem apply_apply_eq_mul {S : Type*} [Group S] (hcomm : ∀ s t : S, s * t = t * s)
    (hexp : ∀ s : S, s ^ 2 = 1) {z : MulAut S} (hz3 : z ^ 3 = 1)
    (hzfix : ∀ s : S, z s = s → s = 1) (s : S) : z (z s) = s * z s := by
  have hzzz : z (z (z s)) = s := by
    have h := congrArg (fun f : MulAut S => f s) hz3
    simpa [pow_succ, MulAut.mul_apply] using h
  have ht : z (s * z s * z (z s)) = s * z s * z (z s) := by
    rw [map_mul, map_mul, hzzz]
    calc z s * z (z s) * s = s * (z s * z (z s)) := hcomm _ _
      _ = s * z s * z (z s) := (mul_assoc _ _ _).symm
  have h1 := hzfix _ ht
  have hinv : ∀ u : S, u⁻¹ = u := fun u => by
    have h := hexp u
    rw [sq] at h
    exact inv_eq_of_mul_eq_one_right h
  calc z (z s) = (s * z s)⁻¹ := (eq_inv_of_mul_eq_one_right h1)
    _ = s * z s := hinv _

theorem ks1012GL34Inf_holds : KS1012GL34Inf := by
  intro S _ _ hcomm hexp Y z x w hzY hxY hwY hzc hz3 hzfix hx3 hxfix hwx hP
  have hzz := apply_apply_eq_mul hcomm hexp hz3 hzfix
  let _ : AddCommGroup (Additive S) :=
    { (inferInstance : AddGroup (Additive S)) with
      add_comm := fun a b => hcomm (Additive.toMul a) (Additive.toMul b) }
  let _ : Module (ZMod 2) (Additive S) := AddCommGroup.zmodModule (n := 2) (fun v => by
    change Additive.ofMul (Additive.toMul v ^ 2) = Additive.ofMul 1
    rw [hexp])
  set Z : Additive S →ₗ[ZMod 2] Additive S :=
    (MulEquiv.toAdditive z).toAddMonoidHom.toZModLinearMap 2 with hZdef
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
  let ρ : Y →* (Additive S ≃ₗ[F4] Additive S) :=
    { toFun := fun y => (MulEquiv.toAdditive (y : MulAut S)).toLinearEquiv
        (hlin y (hzc y y.2))
      map_one' := by
        ext v
        rfl
      map_mul' := fun y y' => by
        ext v
        rfl }
  have hρapp : ∀ (y : Y) (v : Additive S),
      ρ y v = Additive.ofMul ((y : MulAut S) (Additive.toMul v)) := fun y v => rfl
  have hρinj : Function.Injective ρ := by
    rw [injective_iff_map_eq_one]
    intro y hy
    apply Subtype.ext
    ext s
    have h := congrArg (fun f : Additive S ≃ₗ[F4] Additive S => f (Additive.ofMul s)) hy
    exact congrArg Additive.toMul h
  set X : Additive S ≃ₗ[F4] Additive S := ρ ⟨x, hxY⟩ with hXdef
  set W : Additive S ≃ₗ[F4] Additive S := ρ ⟨w, hwY⟩ with hWdef
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
  obtain ⟨b, hb⟩ := exists_basis_eigen (X : Additive S →ₗ[F4] Additive S) W hX3 hWX hfix
  set δ : Y →* F4ˣ := (LinearEquiv.det : (Additive S ≃ₗ[F4] Additive S) →* F4ˣ).comp ρ
    with hδdef
  have hxδ : (⟨x, hxY⟩ : Y) ∈ δ.ker := by
    rw [MonoidHom.mem_ker]
    apply Units.ext
    rw [hδdef, MonoidHom.comp_apply, LinearEquiv.coe_det, ← LinearMap.det_toMatrix b,
      toMatrix_eq_diagonal b _ _ hb, Matrix.det_diagonal, Fin.prod_univ_three, Units.val_one]
    decide
  set P' := perfectResidual Y with hP'def
  have hP'normal : P'.Normal :=
    Subgroup.normal_iInf_normal fun n => derivedSeries_normal Y n
  have hP'le : P' ≤ δ.ker :=
    (iInf_le (fun n => derivedSeries Y n) 1).trans
      ((derivedSeries_one Y).le.trans (Abelianization.commutator_subset_ker δ))
  have hY₁ : Nat.card δ.ker ∣ 60480 := by
    let ι : δ.ker →* (LinearEquiv.det : (Additive S ≃ₗ[F4] Additive S) →* F4ˣ).ker :=
      { toFun := fun y => ⟨ρ y.1, y.2⟩
        map_one' := by
          ext1
          exact ρ.map_one
        map_mul' := fun y y' => by
          ext1
          exact ρ.map_mul y.1 y'.1 }
    have hι : Function.Injective ι := fun y y' h =>
      Subtype.ext (hρinj (congrArg Subtype.val h))
    exact (Subgroup.card_dvd_of_injective ι hι).trans (card_ker_det_dvd b)
  have hPcard : Nat.card P' = 60480 ∨ Nat.card P' = 1080 := by
    have hc : Nat.card (inSubgroup perfectResidual Y) = Nat.card P' :=
      Subgroup.card_map_of_injective Y.subtype_injective
    rcases hP with h4 | h6
    · left
      rw [← hc]
      exact Step1012ClaimProof.card_of_isSLThreePiAt_four h4
    · right
      rw [← hc]
      exact KFacts.KS14.card_eq_of_isExtOf_alternating_six h6.isExtOf
  have hsub : Nat.card (P'.subgroupOf δ.ker) = Nat.card P' :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hP'le).toEquiv
  have : (P'.subgroupOf δ.ker).Normal := hP'normal.subgroupOf δ.ker
  have hmem := mem_of_card_dvd (P'.subgroupOf δ.ker) hY₁ (hsub ▸ hPcard)
    (x := ⟨⟨x, hxY⟩, hxδ⟩) (Subtype.ext (Subtype.ext (by simp [hx3])))
  exact ⟨⟨x, hxY⟩, Subgroup.mem_subgroupOf.mp hmem, rfl⟩

end CFSG.RankThree.PartTwo.Sec10.Item1012Res3Proof
