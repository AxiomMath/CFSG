module

public import CFSG.LocalAnalysis.StandardType.GGPsiDiagInner

public section

namespace CFSG.StandardType

open CFSG.LieType.Universal CFSG.LieType.RootSystem CFSG.LieType.Steinberg

namespace PsiDiag

section CubeVariant

variable {K : Type*} [Group K] {D : UniversalRootDatum K} {k : Type*} [Field k]
  {x : (Fin D.rank → ℤ) → k → K}
  {C : (Fin D.rank → ℤ) → (Fin D.rank → ℤ) → ℕ × ℕ → ℤ}
  {O : CommOrder (CFSG.LieType.Steinberg.RootSystem.ofCartan D.isFiniteType D.divisible)}

theorem exists_prod_zpow_cartan_cube {I : Type*} [Fintype I] [DecidableEq I]
    (A B : Matrix I I ℤ) {m : ℕ} (hBA : B * A = (m : ℤ) • (1 : Matrix I I ℤ)) (a : I → kˣ) :
    ∃ s : I → kˣ, ∀ j, ∏ i, s i ^ A i j = a j ^ m := by
  refine ⟨fun i => ∏ l, a l ^ B l i, fun j => ?_⟩
  have h1 : ∀ i, (∏ l, a l ^ B l i) ^ A i j = ∏ l, a l ^ (B l i * A i j) := by
    intro i
    rw [← Finset.prod_zpow]
    refine Finset.prod_congr rfl fun l _ => ?_
    rw [← zpow_mul]
  rw [Finset.prod_congr rfl fun i _ => h1 i, Finset.prod_comm]
  have h2 : ∀ l, ∏ i, a l ^ (B l i * A i j) = a l ^ ((m : ℤ) * (1 : Matrix I I ℤ) l j) := by
    intro l
    rw [prod_zpow_eq_zpow_sum]
    congr 1
    have := congrFun (congrFun hBA l) j
    rw [Matrix.mul_apply, Matrix.smul_apply, smul_eq_mul] at this
    exact this
  rw [Finset.prod_congr rfl fun l _ => h2 l]
  rw [Finset.prod_eq_single j]
  · rw [Matrix.one_apply_eq, mul_one, zpow_natCast]
  · intro l _ hl
    rw [Matrix.one_apply_ne hl, mul_zero, zpow_zero]
  · intro hj
    exact absurd (Finset.mem_univ j) hj

theorem exists_mul_psi_mem_centralizer_cube (hE : ChevalleyExtras D k x C O) [Finite k] [CharP k 2]
    (hdiv : D.divisible = ∅) (hgen : ⨆ γ ∈ D.roots, D.rootGroup γ = ⊤)
    (hsolv : ∀ a : Fin D.rank → kˣ,
      ∃ s : Fin D.rank → kˣ, ∀ j, ∏ i, s i ^ D.cartan i j = a j ^ 3)
    {G : Type*} [Group G] (ψ : K →* G)
    (hker : ψ.ker ≤ Subgroup.center K) {d : G}
    (hpos : ∀ i, ∃ a : kˣ, ∀ c,
      d⁻¹ * ψ (x (Pi.single i 1) c) * d = ψ (x (Pi.single i 1) (((a : kˣ) : k) ^ 3 * c)))
    (hneg : ∀ i, ∃ φ : k → k, ∀ c,
      d⁻¹ * ψ (x (-Pi.single i 1) c) * d = ψ (x (-Pi.single i 1) (φ c))) :
    ∃ u : K, d * ψ u ∈ Subgroup.centralizer (ψ.range : Set G) := by
  choose a ha using hpos
  choose χ' hχ' using hneg
  obtain ⟨χ, hχdef⟩ : ∃ χ : Fin D.rank → k, ∀ i, χ i = ((a i : kˣ) : k) ^ 3 :=
    ⟨fun i => ((a i : kˣ) : k) ^ 3, fun i => rfl⟩
  have hχ : ∀ i c, d⁻¹ * ψ (x (Pi.single i 1) c) * d = ψ (x (Pi.single i 1) (χ i * c)) := by
    intro i c
    rw [hχdef]
    exact ha i c
  choose φ hφinj hφu hφl using hE.rankOne
  have hΦ : ∀ i, Function.Injective (ψ.comp (φ i)) := fun i =>
    injective_comp_of_ker_le_center (φ i) (hφinj i) ψ hker
  have hχ0 : ∀ i, χ i ≠ 0 := fun i => by
    rw [hχdef]
    exact pow_ne_zero 3 (a i).ne_zero
  let e : Fin D.rank → kˣ := fun i => Units.mk0 (χ i) (hχ0 i)
  obtain ⟨s, hs⟩ := hsolv a
  have hs' : ∀ j, ∏ i, s i ^ D.cartan i j = e j := fun j => by
    rw [hs j]
    apply Units.ext
    simp [e, hχdef]
  set T := torusProd x s with hTdef
  have hTpos : ∀ i v, T * x (Pi.single i 1) v * T⁻¹ = x (Pi.single i 1) (((e i : kˣ) : k) * v) := by
    intro i v
    rw [hTdef, torusProd_conj hE s (single_mem_roots i) v]
    simp only [coroot_single]
    rw [hs' i]
  set d' := d * ψ T with hd'
  have hconj : ∀ z, d'⁻¹ * ψ z * d' = ψ T⁻¹ * (d⁻¹ * ψ z * d) * ψ T := by
    intro z
    rw [hd', map_inv]
    group
  have hfpos : ∀ i c, d'⁻¹ * ψ (x (Pi.single i 1) c) * d' = ψ (x (Pi.single i 1) c) := by
    intro i c
    rw [hconj, hχ, ← map_mul, ← map_mul, inv_conj_of_conj (hTpos i)]
    congr 2
    show (((Units.mk0 (χ i) (hχ0 i))⁻¹ : kˣ) : k) * (χ i * c) = c
    rw [Units.val_inv_eq_inv_val, Units.val_mk0, ← mul_assoc, inv_mul_cancel₀ (hχ0 i), one_mul]
  have hfneg : ∀ i c, d'⁻¹ * ψ (x (-Pi.single i 1) c) * d' = ψ (x (-Pi.single i 1) c) := by
    intro i
    set ν : kˣ := ∏ j, s j ^ coroot D.cartan j (-Pi.single i 1) with hν
    have hTneg : ∀ v, T * x (-Pi.single i 1) v * T⁻¹ = x (-Pi.single i 1) ((ν : k) * v) :=
      fun v => torusProd_conj hE s (neg_single_mem_roots i) v
    have hl : ∀ c, d'⁻¹ * ψ (x (-Pi.single i 1) c) * d' =
        ψ (x (-Pi.single i 1) (((ν⁻¹ : kˣ) : k) * χ' i c)) := by
      intro c
      rw [hconj, hχ', ← map_mul, ← map_mul, inv_conj_of_conj hTneg]
    have he1 : ∀ c, ((ν⁻¹ : kˣ) : k) * χ' i c = c := by
      refine eq_of_conj_sl2 (ψ.comp (φ i)) (hΦ i) (d := d') (fun c => ?_) (fun c => ?_)
      · rw [MonoidHom.comp_apply, hφu]
        exact hfpos i c
      · rw [MonoidHom.comp_apply, MonoidHom.comp_apply, hφl, hφl]
        exact hl c
    intro c
    rw [hl, he1]
  have hall : ∀ γ ∈ D.roots, ∀ v, x γ v ∈ (Subgroup.centralizer ({d'} : Set G)).comap ψ := by
    rintro γ (⟨w, j, rfl⟩ | ⟨w, j, hj, -⟩) v
    · obtain ⟨ω, rfl⟩ := (coxeterMatrix D.isFiniteType).toCoxeterSystem.wordProd_surjective w
      exact fix_weylAction hE ψ hfpos hfneg ω j v
    · rw [hdiv] at hj
      exact absurd hj (Set.notMem_empty j)
  have hS : ⨆ γ ∈ D.roots, D.rootGroup γ ≤ (Subgroup.centralizer ({d'} : Set G)).comap ψ := by
    refine iSup₂_le fun γ hγ z hz => ?_
    obtain ⟨c, rfl⟩ := ((hE.param γ hγ).1 z).mp hz
    exact hall γ hγ c
  rw [hgen] at hS
  refine ⟨T, ?_⟩
  rw [Subgroup.mem_centralizer_iff]
  rintro _ ⟨z, rfl⟩
  exact Subgroup.mem_centralizer_singleton_iff.mp (Subgroup.mem_comap.mp (hS (Subgroup.mem_top z)))

end CubeVariant

end PsiDiag

end CFSG.StandardType
