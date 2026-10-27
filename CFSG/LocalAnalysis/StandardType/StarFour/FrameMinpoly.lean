module

public import CFSG.LocalAnalysis.StandardType.StarFour.SemisimpleFrame

public section

namespace CFSG.StandardType.StarFour

variable {F : Type} [Field F] {V : Type} [AddCommGroup V] [Module F V]

theorem SemiFrame.adjoin_chi_eq_top {P : Type} [CommGroup P] {ρ : P →* (V ≃ₗ[F] V)}
    (fr : SemiFrame F ρ) (g : P) (hg : ∀ x : P, x ∈ Subgroup.zpowers g) (j : Fin fr.r) :
    Algebra.adjoin F {((fr.χ j g : (fr.E j)ˣ) : fr.E j)} = ⊤ := by
  classical
  have hint : IsIntegral F (((fr.χ j g : (fr.E j)ˣ) : fr.E j)) := IsIntegral.of_finite F _
  rw [eq_top_iff, ← fr.gen j]
  apply Algebra.adjoin_le
  rintro x ⟨p, rfl⟩
  obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp (hg p)
  change ((fr.χ j (g ^ n) : (fr.E j)ˣ) : fr.E j) ∈
    Algebra.adjoin F {((fr.χ j g : (fr.E j)ˣ) : fr.E j)}
  rw [map_zpow (fr.χ j) g n]
  refine zpow_induction_right (g := fr.χ j g)
    (P := fun w : (fr.E j)ˣ =>
      ((w : fr.E j)) ∈
        Algebra.adjoin F ({((fr.χ j g : (fr.E j)ˣ) : fr.E j)} : Set (fr.E j)))
    ?_ ?_ ?_ n
  · rw [Units.val_one]
    exact Subalgebra.one_mem _
  · intro w hw
    rw [Units.val_mul]
    exact Subalgebra.mul_mem _ hw (Algebra.subset_adjoin (Set.mem_singleton _))
  · intro w hw
    simpa [Units.val_mul] using
      (Subalgebra.mul_mem _ hw
        (hint.inv_mem (Algebra.subset_adjoin (Set.mem_singleton _))))

theorem SemiFrame.exists_algHom_chi {P : Type} [CommGroup P] {ρ : P →* (V ≃ₗ[F] V)}
    (fr : SemiFrame F ρ) (g : P) (hg : ∀ x : P, x ∈ Subgroup.zpowers g) (j : Fin fr.r)
    {K : Type} [Field K] [Algebra F K] (b : K)
    (hb : Polynomial.aeval b (minpoly F ((fr.χ j g : (fr.E j)ˣ) : fr.E j)) = 0) :
    ∃ ε : fr.E j →ₐ[F] K, ε ((fr.χ j g : (fr.E j)ˣ) : fr.E j) = b := by
  classical
  let a : fr.E j := ((fr.χ j g : (fr.E j)ˣ) : fr.E j)
  have hint : IsIntegral F a := IsIntegral.of_finite F a
  let μ : Polynomial F := minpoly F a
  have hμirr : Irreducible μ := minpoly.irreducible hint
  haveI : Fact (Irreducible μ) := ⟨hμirr⟩
  have hb' : Polynomial.aeval b μ = 0 := hb
  let e₀ : AdjoinRoot μ →ₐ[F] fr.E j :=
    AdjoinRoot.liftAlgHom μ (Algebra.ofId F (fr.E j)) a
      (by
        simpa [Polynomial.aeval_def] using minpoly.aeval F a)
  have hinj : Function.Injective e₀ := RingHom.injective e₀.toRingHom
  have hgen : Algebra.adjoin F ({a} : Set (fr.E j)) = ⊤ :=
    SemiFrame.adjoin_chi_eq_top fr g hg j
  have hsurj : Function.Surjective e₀ := by
    have hle : Algebra.adjoin F ({a} : Set (fr.E j)) ≤ e₀.range := by
      apply Algebra.adjoin_le
      intro x hx
      rw [Set.mem_singleton_iff] at hx
      subst hx
      exact e₀.mem_range.2 ⟨AdjoinRoot.root μ, AdjoinRoot.liftAlgHom_root _ _ _ _⟩
    have htop : e₀.range = ⊤ := le_antisymm le_top (hgen ▸ hle)
    intro y
    have hy : y ∈ e₀.range := by rw [htop]; exact Set.mem_univ y
    exact (AlgHom.mem_range e₀).mp hy
  have hbij : Function.Bijective e₀ := ⟨hinj, hsurj⟩
  let e : AdjoinRoot μ ≃ₐ[F] fr.E j := AlgEquiv.ofBijective e₀ hbij
  let ε₀ : AdjoinRoot μ →ₐ[F] K :=
    AdjoinRoot.liftAlgHom μ (Algebra.ofId F K) b
      (by simpa [Polynomial.aeval_def] using hb')
  refine ⟨ε₀.comp e.symm.toAlgHom, ?_⟩
  have hroot : e (AdjoinRoot.root μ) = a := by
    change (AlgEquiv.ofBijective e₀ hbij) (AdjoinRoot.root μ) = a
    rw [AlgEquiv.ofBijective_apply]
    exact AdjoinRoot.liftAlgHom_root _ _ _ _
  have hsymm : e.symm a = AdjoinRoot.root μ := by
    rw [← hroot, AlgEquiv.symm_apply_apply]
  show ε₀ (e.symm a) = b
  rw [hsymm]
  exact AdjoinRoot.liftAlgHom_root _ _ _ _

private noncomputable def frameBlockCopy {P : Type} [CommGroup P] {ρ : P →* (V ≃ₗ[F] V)}
    (fr : SemiFrame F ρ) {j j₂ : Fin fr.r} (c₀ : Fin (fr.m j)) (c₂ : Fin (fr.m j₂))
    (ε : fr.E j →ₐ[F] fr.E j₂) : V →ₗ[F] V :=
  let geta : V →ₗ[F] fr.E j :=
    (LinearMap.proj (R := F) (φ := fun _ : Fin (fr.m j) => fr.E j) c₀).comp
      ((LinearMap.proj (R := F) (φ := fun i : Fin fr.r => Fin (fr.m i) → fr.E i) j).comp
        fr.Φ.toLinearMap)
  fr.Φ.symm.toLinearMap.comp
    ((LinearMap.single (R := F) (φ := fun i : Fin fr.r => Fin (fr.m i) → fr.E i) j₂).comp
      ((LinearMap.single (R := F) (φ := fun _ : Fin (fr.m j₂) => fr.E j₂) c₂).comp
        (ε.toLinearMap.comp geta)))

private lemma frameBlockCopy_apply {P : Type} [CommGroup P] {ρ : P →* (V ≃ₗ[F] V)}
    (fr : SemiFrame F ρ) {j j₂ : Fin fr.r} (c₀ : Fin (fr.m j)) (c₂ : Fin (fr.m j₂))
    (ε : fr.E j →ₐ[F] fr.E j₂) (v : V) :
    frameBlockCopy fr c₀ c₂ ε v =
      fr.Φ.symm (Pi.single j₂ (Pi.single c₂ (ε (fr.Φ v j c₀)))) := rfl

private lemma frameBlockCopy_apply_ne {P : Type} [CommGroup P] {ρ : P →* (V ≃ₗ[F] V)}
    (fr : SemiFrame F ρ) {j j₂ : Fin fr.r} (hjj : j ≠ j₂) (c₀ : Fin (fr.m j))
    (c₂ : Fin (fr.m j₂)) (ε : fr.E j →ₐ[F] fr.E j₂) (v : V) :
    fr.Φ (frameBlockCopy fr c₀ c₂ ε v) j = 0 := by
  rw [frameBlockCopy_apply, LinearEquiv.apply_symm_apply, Pi.single_eq_of_ne hjj]

private lemma frameBlockCopy_idempotent {P : Type} [CommGroup P] {ρ : P →* (V ≃ₗ[F] V)}
    (fr : SemiFrame F ρ) {j j₂ : Fin fr.r} (hjj : j ≠ j₂) (c₀ : Fin (fr.m j))
    (c₂ : Fin (fr.m j₂)) (ε : fr.E j →ₐ[F] fr.E j₂) (v : V) :
    frameBlockCopy fr c₀ c₂ ε (frameBlockCopy fr c₀ c₂ ε v) = 0 := by
  rw [frameBlockCopy_apply]
  rw [frameBlockCopy_apply_ne fr hjj c₀ c₂ ε v]
  simp [Pi.single_zero]

private lemma frameBlockCopy_comm_g {P : Type} [CommGroup P] {ρ : P →* (V ≃ₗ[F] V)}
    (fr : SemiFrame F ρ) (g : P) {j j₂ : Fin fr.r} (hjj : j ≠ j₂) (c₀ : Fin (fr.m j))
    (c₂ : Fin (fr.m j₂)) (ε : fr.E j →ₐ[F] fr.E j₂)
    (hεχ : ε ((fr.χ j g : (fr.E j)ˣ) : fr.E j) =
      ((fr.χ j₂ g : (fr.E j₂)ˣ) : fr.E j₂)) (v : V) :
    frameBlockCopy fr c₀ c₂ ε (ρ g v) = ρ g (frameBlockCopy fr c₀ c₂ ε v) := by
  apply fr.Φ.injective
  funext i c
  have hL : ε (fr.Φ (ρ g v) j c₀) =
      ((fr.χ j₂ g : (fr.E j₂)ˣ) : fr.E j₂) * ε (fr.Φ v j c₀) := by
    rw [fr.act g v j, Pi.smul_apply, smul_eq_mul, map_mul, hεχ]
  rw [frameBlockCopy_apply, LinearEquiv.apply_symm_apply, hL]
  rw [fr.act g (frameBlockCopy fr c₀ c₂ ε v) i, Pi.smul_apply, frameBlockCopy_apply,
    LinearEquiv.apply_symm_apply]
  by_cases hi : i = j₂
  · subst hi
    rw [Pi.single_eq_same, Pi.single_eq_same]
    by_cases hc : c = c₂
    · subst hc
      rw [Pi.single_eq_same, Pi.single_eq_same, smul_eq_mul]
    · rw [Pi.single_eq_of_ne hc, Pi.single_eq_of_ne hc]
      simp
  · rw [Pi.single_eq_of_ne hi, Pi.single_eq_of_ne hi]
    simp

theorem SemiFrame.minpoly_ne_of_ne [Finite F] {P : Type} [CommGroup P]
    {ρ : P →* (V ≃ₗ[F] V)} (fr : SemiFrame F ρ) (g : P) (hg : ∀ x : P, x ∈ Subgroup.zpowers g)
    {j j₂ : Fin fr.r} (hj : j ≠ j₂) (hmj : 0 < fr.m j) (hmj₂ : 0 < fr.m j₂) :
    minpoly F ((fr.χ j g : (fr.E j)ˣ) : fr.E j) ≠
      minpoly F ((fr.χ j₂ g : (fr.E j₂)ˣ) : fr.E j₂) := by
  classical
  intro hμ
  let a : fr.E j := ((fr.χ j g : (fr.E j)ˣ) : fr.E j)
  let b : fr.E j₂ := ((fr.χ j₂ g : (fr.E j₂)ˣ) : fr.E j₂)
  have hμ' : minpoly F a = minpoly F b := hμ
  have hbroot : Polynomial.aeval b (minpoly F a) = 0 := by
    rw [hμ']
    exact minpoly.aeval F b
  obtain ⟨ε, hε⟩ := SemiFrame.exists_algHom_chi fr g hg j b hbroot
  have hεa : ε a = b := hε
  have hεχ : ε ((fr.χ j g : (fr.E j)ˣ) : fr.E j) =
      ((fr.χ j₂ g : (fr.E j₂)ˣ) : fr.E j₂) := hεa
  let c₀ : Fin (fr.m j) := ⟨0, hmj⟩
  let c₂ : Fin (fr.m j₂) := ⟨0, hmj₂⟩
  let T : V →ₗ[F] V := frameBlockCopy fr c₀ c₂ ε
  have hT : ∀ v : V, T v =
      fr.Φ.symm (Pi.single j₂ (Pi.single c₂ (ε (fr.Φ v j c₀)))) :=
    fun v => frameBlockCopy_apply fr c₀ c₂ ε v
  have hTi : ∀ v : V, fr.Φ (T v) j = 0 :=
    fun v => frameBlockCopy_apply_ne fr hj c₀ c₂ ε v
  have hTcomm : ∀ v : V, T (ρ g v) = ρ g (T v) :=
    fun v => frameBlockCopy_comm_g fr g hj c₀ c₂ ε hεχ v
  have hT2 : ∀ v : V, T (T v) = 0 :=
    fun v => frameBlockCopy_idempotent fr hj c₀ c₂ ε v
  have hfg : (LinearMap.id + T : V →ₗ[F] V).comp (LinearMap.id - T) = LinearMap.id := by
    ext v
    simp only [LinearMap.comp_apply, LinearMap.add_apply, LinearMap.sub_apply,
      LinearMap.id_apply]
    rw [map_sub, hT2 v, sub_zero, sub_add_cancel]
  have hgf : (LinearMap.id - T : V →ₗ[F] V).comp (LinearMap.id + T) = LinearMap.id := by
    ext v
    simp only [LinearMap.comp_apply, LinearMap.add_apply, LinearMap.sub_apply,
      LinearMap.id_apply]
    rw [map_add, hT2 v, add_zero, add_sub_cancel_right]
  let S : V ≃ₗ[F] V := LinearEquiv.ofLinearMap (LinearMap.id + T) (LinearMap.id - T) hfg hgf
  have hS : ∀ v : V, S v = v + T v := by
    intro v
    show (LinearMap.id + T : V →ₗ[F] V) v = v + T v
    rfl
  have hSg : S * ρ g = ρ g * S := by
    ext v
    rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, hS (ρ g v), hS v, map_add, hTcomm v]
  have hScomm : Commute S (ρ g) := by
    rw [commute_iff_eq]
    exact hSg
  have hSall : ∀ p : P, S * ρ p = ρ p * S := by
    intro p
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp (hg p)
    rw [map_zpow]
    exact (hScomm.zpow_right n).eq
  obtain ⟨B, hB⟩ := ((fr.comm S).mp hSall) j₂
  let v₀ : V := fr.Φ.symm (Pi.single j (Pi.single c₀ (1 : fr.E j)))
  have hv₀ : fr.Φ v₀ = Pi.single j (Pi.single c₀ (1 : fr.E j)) :=
    LinearEquiv.apply_symm_apply fr.Φ _
  have hv₀j₂ : fr.Φ v₀ j₂ = 0 := by
    rw [hv₀, Pi.single_eq_of_ne (Ne.symm hj)]
  have hzero : fr.Φ (S v₀) j₂ = 0 := by
    rw [hB v₀, hv₀j₂, map_zero]
  have hone : fr.Φ (S v₀) j₂ c₂ = 1 := by
    rw [hS v₀, map_add, Pi.add_apply, hv₀j₂, Pi.add_apply, Pi.zero_apply, zero_add]
    rw [hT v₀, LinearEquiv.apply_symm_apply, Pi.single_eq_same]
    rw [hv₀, Pi.single_eq_same, Pi.single_eq_same]
    exact map_one ε
  have hzero' : fr.Φ (S v₀) j₂ c₂ = 0 := by
    rw [hzero]
    simp
  exact one_ne_zero (hone.symm.trans hzero')

end CFSG.StandardType.StarFour
