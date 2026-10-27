module

public import CFSG.LinearAlgebra.RootGroupSL.DatumEquiv
public import CFSG.LocalAnalysis.StandardType.GGInterfaceDefs
public import CFSG.LocalAnalysis.StandardType.GGLieKnownR2CoverNC
public import CFSG.LocalAnalysis.StandardType.GGLieKnownR2SLFpf
public import CFSG.LocalAnalysis.StandardType.GGLieKnownR2SLRankOne
public import CFSG.LieType.Universal.SpecialLinearExtras

public section

namespace CFSG.StandardType.LieKnownR2.SpecialLinearNC

open CFSG.Open CFSG.LieType.Universal CFSG.LieType.RootSystem CFSG.LinearAlgebra.RootGroupSL

theorem exists_mulEquiv_rootSubgroup_eq_rootSL {F : Type} [Field F] {m : ℕ} {i j : Fin (m + 1)}
    (hij : i ≠ j) :
    ∃ (X' : Type) (_ : AddCommGroup X') (_ : Module F X') (_ : Module.Finite F X')
      (e : Matrix.SpecialLinearGroup (Fin (m + 1)) F ≃* SpecialLinearGroup F (DSpace F X')),
      (SpecialLinear.rootSubgroup m F hij).map e.toMonoidHom = rootSL F F X' ∧
        Module.finrank F X' + 2 = m + 1 := by
  classical
  let ι : F →ₗ[F] (Fin (m + 1) → F) := LinearMap.toSpanSingleton F _ (Pi.single i 1)
  let ι₁ : F →ₗ[F] (Fin (m + 1) → F) := LinearMap.toSpanSingleton F _ (Pi.single j 1)
  let π : (Fin (m + 1) → F) →ₗ[F] F := LinearMap.proj j
  let π₁ : (Fin (m + 1) → F) →ₗ[F] F := LinearMap.proj i
  have h1 : ∀ t, π (ι t) = 0 := by
    intro t
    simp [ι, π, Pi.single_apply, hij.symm]
  have h2 : ∀ t, π (ι₁ t) = t := by
    intro t
    simp [ι₁, π]
  have h3 : ∀ t, π₁ (ι t) = t := by
    intro t
    simp [ι, π₁]
  have h4 : ∀ t, π₁ (ι₁ t) = 0 := by
    intro t
    simp [ι₁, π₁, Pi.single_apply, hij]
  obtain ⟨X', _, _, _, e₀, he, -, hdim⟩ := exists_datumEquiv ι ι₁ π π₁ h1 h2 h3 h4
  have key : ∀ c : F, Matrix.SpecialLinearGroup.toLin'_equiv
      (Matrix.SpecialLinearGroup.transvection hij c) = datumElt ι π h1 c := by
    intro c
    apply SpecialLinearGroup.ext
    intro v
    change (Matrix.SpecialLinearGroup.toLin'
      (Matrix.SpecialLinearGroup.transvection hij c) : _ ≃ₗ[F] _) v = v + ι (c * π v)
    rw [Matrix.SpecialLinearGroup.toLin'_apply, Matrix.SpecialLinearGroup.transvection_coe,
      Matrix.toLin'_apply, Matrix.add_mulVec, Matrix.one_mulVec, Matrix.single_mulVec_eq]
    simp [ι, π]
  refine ⟨X', inferInstance, inferInstance, inferInstance,
    Matrix.SpecialLinearGroup.toLin'_equiv.trans e₀, ?_, ?_⟩
  · ext y
    rw [Subgroup.mem_map]
    constructor
    · rintro ⟨g, hg, rfl⟩
      obtain ⟨c, rfl⟩ := (SpecialLinear.mem_rootSubgroup hij g).1 hg
      change e₀ (Matrix.SpecialLinearGroup.toLin'_equiv _) ∈ _
      rw [key, he]
      exact rootElt_mem_rootSL c
    · intro hy
      obtain ⟨t, ht⟩ := mem_rootSL_iff.1 hy
      refine ⟨Matrix.SpecialLinearGroup.transvection hij t,
        SpecialLinear.transvection_mem_rootSubgroup hij t, ?_⟩
      change e₀ (Matrix.SpecialLinearGroup.toLin'_equiv _) = y
      rw [key, he]
      exact Subtype.ext ht.symm
  · have h5 := hdim
    rw [Module.finrank_fin_fun, Module.finrank_self] at h5
    omega

private theorem isPGroup_rootSubgroup {F : Type} [Field F] [CharP F 2] {m : ℕ}
    {i j : Fin (m + 1)} (hij : i ≠ j) : IsPGroup 2 (SpecialLinear.rootSubgroup m F hij) := by
  rintro ⟨x, hx⟩
  obtain ⟨c, rfl⟩ := (SpecialLinear.mem_rootSubgroup hij x).1 hx
  refine ⟨1, Subtype.ext ?_⟩
  change (Matrix.SpecialLinearGroup.transvection hij c) ^ 2 ^ 1 = 1
  rw [pow_one, pow_two, ← Matrix.SpecialLinearGroup.transvection_add, CharTwo.add_self_eq_zero,
    Matrix.SpecialLinearGroup.transvection_coeff_zero]

private theorem noCentral_top_map_mulEquiv {U U' : Type} [Group U] [Group U'] (e : U ≃* U')
    {R : Subgroup U} (h : GGRootNoCentralAt (⊤ : Subgroup U) R) :
    GGRootNoCentralAt (⊤ : Subgroup U') (R.map e.toMonoidHom) := by
  intro A B hRA hAB hB hNA hNB hc
  simp only [top_inf_eq] at hB hNA hNB hc
  refine ggRootNormNoCentral_map_mulEquiv e ?_ A B hRA hAB hB hNA hNB hc
  intro A' B' hRA' hAB' hB' hNA' hNB' hc'
  exact h A' B' hRA' hAB' (by simpa only [top_inf_eq] using hB')
    (by simpa only [top_inf_eq] using hNA') (by simpa only [top_inf_eq] using hNB')
    (by simpa only [top_inf_eq] using hc')

theorem ggRootNoCentralAt_specialLinear {m g : ℕ} (hm : 1 ≤ m) (hg : 1 ≤ g)
    (hexc : ¬ (m = 2 ∧ g = 1)) {X : Type} [Group X] [Finite X]
    (φ : Matrix.SpecialLinearGroup (Fin (m + 1)) (GaloisField 2 g) →* X)
    (hker : φ.ker ≤ Subgroup.center (Matrix.SpecialLinearGroup (Fin (m + 1)) (GaloisField 2 g)))
    (hodd : Odd (Nat.card φ.ker)) {β : Fin m → ℤ}
    (hβ : β ∈ roots (SpecialLinear.isFiniteType_A m) ∅)
    (u : Matrix.SpecialLinearGroup (Fin (m + 1)) (GaloisField 2 g)) :
    GGRootNoCentralAt φ.range (ggRootSub (SpecialLinear.rootDatum m (GaloisField 2 g)) φ β u) := by
  have hroot : (SpecialLinear.rootDatum m (GaloisField 2 g)).rootGroup β =
      SpecialLinear.rootSubgroup m (GaloisField 2 g) (SpecialLinear.idx_spec m hβ).1 :=
    SpecialLinear.rootGroup_eq_idx m _ hβ
  have hNC : GGRootNoCentralAt
      (⊤ : Subgroup (Matrix.SpecialLinearGroup (Fin (m + 1)) (GaloisField 2 g)))
      (SpecialLinear.rootSubgroup m (GaloisField 2 g) (SpecialLinear.idx_spec m hβ).1) := by
    rcases Nat.lt_or_ge m 2 with h1 | h2
    · obtain rfl : m = 1 := by omega
      intro A B hRA hAB hB hNA hNB hc b hb
      rw [top_inf_eq] at hB
      exact hRA (pCoreOf_normalizer_rootSubgroup_le (SpecialLinear.idx_spec 1 hβ).1 (hB hb))
    · obtain ⟨X', _, _, _, e, he, hdim⟩ := exists_mulEquiv_rootSubgroup_eq_rootSL
        (F := GaloisField 2 g) (SpecialLinear.idx_spec m hβ).1
      have hcard : Nat.card (GaloisField 2 g) = 2 ^ g := GaloisField.card 2 g (by omega)
      have h4 := ggRootNoCentralAt_top_rootSL (k := GaloisField 2 g) (X := X') (by omega) (by
        rcases Nat.lt_or_ge g 2 with hg2 | hg2
        · right
          omega
        · left
          rw [hcard]
          calc 4 = 2 ^ 2 := by norm_num
            _ ≤ 2 ^ g := Nat.pow_le_pow_right (by norm_num) hg2)
      have h5 := noCentral_top_map_mulEquiv e.symm h4
      rwa [← he, GGRootNorm.map_symm_map] at h5
  have h2g := isPGroup_rootSubgroup (F := GaloisField 2 g) (SpecialLinear.idx_spec m hβ).1
  have h3 := ggRootNoCentralAt_map_of_odd_central_ker φ hker hodd
    (h2g.map (MulAut.conj u).toMonoidHom) (noCentral_top_map_mulEquiv (MulAut.conj u) hNC)
  unfold ggRootSub
  rw [hroot]
  exact h3

end CFSG.StandardType.LieKnownR2.SpecialLinearNC
