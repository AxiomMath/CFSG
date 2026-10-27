module

public import Mathlib.GroupTheory.IsPerfect
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.Tactic.LinearCombination

public section

open scoped commutatorElement

namespace CFSG.RankThree.PartTwo.Sec19.TorusLayerAux

theorem cube_root_cases {K : Type*} [Field K] {μ ν : K} (hν3 : ν ^ 3 = 1) (hν1 : ν ≠ 1)
    (hμ3 : μ ^ 3 = 1) : μ = 1 ∨ μ = ν ∨ μ = ν ^ 2 := by
  have h1 : 1 + ν + ν ^ 2 = 0 := by
    have h : (ν - 1) * (1 + ν + ν ^ 2) = 0 := by linear_combination hν3
    rcases mul_eq_zero.mp h with h | h
    · exact absurd (sub_eq_zero.mp h) hν1
    · exact h
  have h2 : (μ - 1) * (μ - ν) * (μ - ν ^ 2) = 0 := by
    linear_combination hμ3 - (μ - 1) * μ * h1 + (μ - 1) * hν3
  rcases mul_eq_zero.mp h2 with h | h
  · rcases mul_eq_zero.mp h with h | h
    · exact Or.inl (sub_eq_zero.mp h)
    · exact Or.inr (Or.inl (sub_eq_zero.mp h))
  · exact Or.inr (Or.inr (sub_eq_zero.mp h))

theorem central_pow_of_scalar {H K : Type*} [Group H] [Field K]
    (φ : H →* Matrix (Fin 3) (Fin 3) K) (hφ : Function.Injective φ)
    (hcen : ∀ u : H, (∀ g : H, g * u = u * g) → ∃ μ : K, φ u = Matrix.scalar (Fin 3) μ)
    {y z : H} (hy3 : y ^ 3 = 1) (hy1 : y ≠ 1) (hyc : ∀ g : H, g * y = y * g)
    (hz3 : z ^ 3 = 1) (hzc : ∀ g : H, g * z = z * g) : ∃ k : ℕ, z = y ^ k := by
  obtain ⟨ν, hν⟩ := hcen y hyc
  obtain ⟨μ, hμ⟩ := hcen z hzc
  have hsc : Function.Injective (Matrix.scalar (Fin 3) : K →+* Matrix (Fin 3) (Fin 3) K) :=
    RingHom.injective _
  have hν3 : ν ^ 3 = 1 := by
    have h := congrArg φ hy3
    rw [map_pow, hν, map_one] at h
    apply hsc
    rw [map_pow, map_one]
    exact h
  have hμ3 : μ ^ 3 = 1 := by
    have h := congrArg φ hz3
    rw [map_pow, hμ, map_one] at h
    apply hsc
    rw [map_pow, map_one]
    exact h
  have hν1 : ν ≠ 1 := by
    intro h
    apply hy1
    apply hφ
    simp [hν, h]
  rcases cube_root_cases hν3 hν1 hμ3 with h | h | h
  · exact ⟨0, by apply hφ; simp [hμ, h]⟩
  · exact ⟨1, by apply hφ; simp [hμ, hν, h]⟩
  · exact ⟨2, by apply hφ; simp [hμ, hν, h, map_pow]⟩

theorem pow_conj_eq {G : Type*} [Group G] (g a : G) (k : ℕ) :
    (g * a * g⁻¹) ^ k = g * a ^ k * g⁻¹ :=
  (map_pow (MulAut.conj g) a k).symm

theorem zpow_conj_eq {G : Type*} [Group G] (g a : G) (k : ℤ) :
    (g * a * g⁻¹) ^ k = g * a ^ k * g⁻¹ :=
  (map_zpow (MulAut.conj g) a k).symm

theorem conj_ne_one {G : Type*} [Group G] {c y : G} (hy : y ≠ 1) : c * y * c⁻¹ ≠ 1 := by
  intro h
  apply hy
  calc y = c⁻¹ * (c * y * c⁻¹) * c := by group
    _ = c⁻¹ * 1 * c := by rw [h]
    _ = 1 := by group

theorem conj_pow_eq_one {G : Type*} [Group G] {g a : G} {k : ℕ} (h : a ^ k = 1) :
    (g * a * g⁻¹) ^ k = 1 := by
  rw [pow_conj_eq, h]
  simp

theorem mem_zpowers_of_conj {G : Type*} [Group G] {g a z : G}
    (h : g * z * g⁻¹ ∈ Subgroup.zpowers (g * a * g⁻¹)) : z ∈ Subgroup.zpowers a := by
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp h
  rw [zpow_conj_eq] at hk
  have hz : z = a ^ k := by
    calc z = g⁻¹ * (g * z * g⁻¹) * g := by group
      _ = g⁻¹ * (g * a ^ k * g⁻¹) * g := by rw [hk]
      _ = a ^ k := by group
  rw [hz]
  exact zpow_mem (Subgroup.mem_zpowers a) k

@[expose] def LayerProp {G : Type*} [Group G] (w : G) : Prop :=
  w ∈ ⁅Subgroup.centralizer ({w} : Set G), Subgroup.centralizer ({w} : Set G)⁆ ∧
    ∀ z ∈ ⁅Subgroup.centralizer ({w} : Set G), Subgroup.centralizer ({w} : Set G)⁆,
      z ^ 3 = 1 →
      (∀ d ∈ ⁅Subgroup.centralizer ({w} : Set G), Subgroup.centralizer ({w} : Set G)⁆,
        z * d = d * z) →
      z ∈ Subgroup.zpowers w

theorem conj_mem_commutator {G : Type*} [Group G] (g a z : G)
    (hz : z ∈ ⁅Subgroup.centralizer ({a} : Set G), Subgroup.centralizer ({a} : Set G)⁆) :
    g * z * g⁻¹ ∈ ⁅Subgroup.centralizer ({g * a * g⁻¹} : Set G),
      Subgroup.centralizer ({g * a * g⁻¹} : Set G)⁆ := by
  have hC : Subgroup.map (MulAut.conj g).toMonoidHom (Subgroup.centralizer ({a} : Set G)) ≤
      Subgroup.centralizer ({g * a * g⁻¹} : Set G) := by
    rintro _ ⟨c, hc, rfl⟩
    have hca : c * a = a * c := Subgroup.mem_centralizer_singleton_iff.mp hc
    rw [Subgroup.mem_centralizer_singleton_iff]
    show g * c * g⁻¹ * (g * a * g⁻¹) = g * a * g⁻¹ * (g * c * g⁻¹)
    calc g * c * g⁻¹ * (g * a * g⁻¹) = g * (c * a) * g⁻¹ := by group
      _ = g * (a * c) * g⁻¹ := by rw [hca]
      _ = g * a * g⁻¹ * (g * c * g⁻¹) := by group
  have hmap : Subgroup.map (MulAut.conj g).toMonoidHom
      ⁅Subgroup.centralizer ({a} : Set G), Subgroup.centralizer ({a} : Set G)⁆ ≤
      ⁅Subgroup.centralizer ({g * a * g⁻¹} : Set G),
        Subgroup.centralizer ({g * a * g⁻¹} : Set G)⁆ := by
    rw [Subgroup.map_commutator]
    exact Subgroup.commutator_mono hC hC
  exact hmap (Subgroup.mem_map_of_mem (MulAut.conj g).toMonoidHom hz)

theorem layerProp_of_conj {G : Type*} [Group G] (g a : G) (h : LayerProp (g * a * g⁻¹)) :
    LayerProp a := by
  unfold LayerProp at h ⊢
  obtain ⟨h1, h2⟩ := h
  have e : g⁻¹ * (g * a * g⁻¹) * g⁻¹⁻¹ = a := by group
  have back : ∀ t ∈ ⁅Subgroup.centralizer ({g * a * g⁻¹} : Set G),
      Subgroup.centralizer ({g * a * g⁻¹} : Set G)⁆,
      g⁻¹ * t * g⁻¹⁻¹ ∈ ⁅Subgroup.centralizer ({a} : Set G), Subgroup.centralizer ({a} : Set G)⁆ := by
    intro t ht
    have := conj_mem_commutator g⁻¹ (g * a * g⁻¹) t ht
    rwa [e] at this
  refine ⟨?_, ?_⟩
  · have := back _ h1
    rwa [e] at this
  · intro z hz hz3 hzc
    have hz' := conj_mem_commutator g a z hz
    have hz3' : (g * z * g⁻¹) ^ 3 = 1 := by
      rw [pow_conj_eq, hz3]
      simp
    have hzc' : ∀ d ∈ ⁅Subgroup.centralizer ({g * a * g⁻¹} : Set G),
        Subgroup.centralizer ({g * a * g⁻¹} : Set G)⁆,
        (g * z * g⁻¹) * d = d * (g * z * g⁻¹) := by
      intro d hd
      have hd' := back d hd
      have key := hzc _ hd'
      calc g * z * g⁻¹ * d = g * (z * (g⁻¹ * d * g⁻¹⁻¹)) * g⁻¹ := by group
        _ = g * ((g⁻¹ * d * g⁻¹⁻¹) * z) * g⁻¹ := by rw [key]
        _ = d * (g * z * g⁻¹) := by group
    exact mem_zpowers_of_conj (h2 _ hz' hz3' hzc')

theorem two_pow_mod_three_even (m : ℕ) : 2 ^ (2 * m) % 3 = 1 := by
  rw [pow_mul, Nat.pow_mod]
  norm_num

theorem two_pow_mod_three_odd (m : ℕ) : 2 ^ (2 * m + 1) % 3 = 2 := by
  rw [pow_succ, pow_mul, Nat.mul_mod, Nat.pow_mod]
  norm_num

theorem commutator_self_eq_of_perfect {G : Type*} [Group G] (R : Subgroup G)
    (hP : Group.IsPerfect R) : ⁅R, R⁆ = R :=
  Subgroup.isPerfect_iff.mp hP

theorem commutator_centralizer_eq {G : Type*} [Group G] (w : G) (R : Subgroup G)
    (hP : Group.IsPerfect R) (hRc : R ≤ Subgroup.centralizer ({w} : Set G))
    (hcomm : ∀ a ∈ Subgroup.centralizer ({w} : Set G), ∀ b ∈ Subgroup.centralizer ({w} : Set G),
      a * b * a⁻¹ * b⁻¹ ∈ R) :
    ⁅Subgroup.centralizer ({w} : Set G), Subgroup.centralizer ({w} : Set G)⁆ = R := by
  apply le_antisymm
  · refine Subgroup.commutator_le.2 fun a ha b hb => ?_
    rw [commutatorElement_def]
    exact hcomm a ha b hb
  · exact (commutator_self_eq_of_perfect R hP).symm.le.trans (Subgroup.commutator_mono hRc hRc)

theorem layer_of_rep {G K : Type*} [Group G] [Field K] (w : G) (R : Subgroup G)
    (hP : Group.IsPerfect R) (hwR : w ∈ R) (hRc : R ≤ Subgroup.centralizer ({w} : Set G))
    (hcomm : ∀ a ∈ Subgroup.centralizer ({w} : Set G), ∀ b ∈ Subgroup.centralizer ({w} : Set G),
      a * b * a⁻¹ * b⁻¹ ∈ R)
    (hw3 : w ^ 3 = 1) (hw1 : w ≠ 1)
    (φ : R →* Matrix (Fin 3) (Fin 3) K) (hφ : Function.Injective φ)
    (hcen : ∀ u : R, (∀ g : R, g * u = u * g) → ∃ μ : K, φ u = Matrix.scalar (Fin 3) μ) :
    LayerProp w := by
  have hD := commutator_centralizer_eq w R hP hRc hcomm
  unfold LayerProp
  refine ⟨?_, ?_⟩
  · rw [hD]
    exact hwR
  intro z hz hz3 hzc
  rw [hD] at hz hzc
  have hzc' : ∀ g : R, g * (⟨z, hz⟩ : R) = (⟨z, hz⟩ : R) * g := fun g =>
    Subtype.ext (hzc (g : G) g.2).symm
  have hy3 : (⟨w, hwR⟩ : R) ^ 3 = 1 := Subtype.ext (by simpa using hw3)
  have hy1 : (⟨w, hwR⟩ : R) ≠ 1 := fun h => hw1 (congrArg Subtype.val h)
  have hyc : ∀ g : R, g * (⟨w, hwR⟩ : R) = (⟨w, hwR⟩ : R) * g := fun g =>
    Subtype.ext (Subgroup.mem_centralizer_singleton_iff.mp (hRc g.2))
  have hz3' : (⟨z, hz⟩ : R) ^ 3 = 1 := Subtype.ext (by simpa using hz3)
  obtain ⟨k, hk⟩ := central_pow_of_scalar φ hφ hcen hy3 hy1 hyc hz3' hzc'
  have hzk : z = w ^ k := by
    have h := congrArg Subtype.val hk
    simpa using h
  rw [hzk]
  exact pow_mem (Subgroup.mem_zpowers w) k

def sl3Hom (F : Type*) [Field F] :
    Matrix.SpecialLinearGroup (Fin 3) F →* Matrix (Fin 3) (Fin 3) F where
  toFun A := (A : Matrix (Fin 3) (Fin 3) F)
  map_one' := by simp [Matrix.SpecialLinearGroup.coe_one]
  map_mul' A B := by simp [Matrix.SpecialLinearGroup.coe_mul]

theorem sl3Hom_injective (F : Type*) [Field F] : Function.Injective (sl3Hom F) := by
  intro A B h
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  exact congrFun (congrFun h i) j

theorem sl3_center_scalar {F : Type*} [Field F] {u : Matrix.SpecialLinearGroup (Fin 3) F}
    (hu : u ∈ Subgroup.center (Matrix.SpecialLinearGroup (Fin 3) F)) :
    ∃ μ : F, (u : Matrix (Fin 3) (Fin 3) F) = Matrix.scalar (Fin 3) μ := by
  obtain ⟨r, -, hr⟩ := (Matrix.SpecialLinearGroup.mem_center_iff (n := Fin 3) (R := F)).mp hu
  exact ⟨r, hr.symm⟩

theorem layer_of_SL {G : Type*} [Group G] {F : Type*} [Field F] (w : G) (R : Subgroup G)
    (hP : Group.IsPerfect R) (hwR : w ∈ R) (hRc : R ≤ Subgroup.centralizer ({w} : Set G))
    (hcomm : ∀ a ∈ Subgroup.centralizer ({w} : Set G), ∀ b ∈ Subgroup.centralizer ({w} : Set G),
      a * b * a⁻¹ * b⁻¹ ∈ R)
    (hw3 : w ^ 3 = 1) (hw1 : w ≠ 1)
    (e : R ≃* Matrix.SpecialLinearGroup (Fin 3) F) : LayerProp w := by
  let φ : R →* Matrix (Fin 3) (Fin 3) F := (sl3Hom F).comp e.toMonoidHom
  have hφ : Function.Injective φ := (sl3Hom_injective F).comp e.injective
  have hcen : ∀ u : R, (∀ g : R, g * u = u * g) → ∃ μ : F, φ u = Matrix.scalar (Fin 3) μ := by
    intro u hu
    have hmem : e u ∈ Subgroup.center (Matrix.SpecialLinearGroup (Fin 3) F) := by
      rw [Subgroup.mem_center_iff]
      intro g
      obtain ⟨g', rfl⟩ := e.surjective g
      rw [← map_mul, ← map_mul, hu g']
    exact sl3_center_scalar hmem
  exact layer_of_rep w R hP hwR hRc hcomm hw3 hw1 φ hφ hcen

theorem layer_of_SU {G : Type*} [Group G] {L : Type*} [Field L] (w : G) (R : Subgroup G)
    (hP : Group.IsPerfect R) (hwR : w ∈ R) (hRc : R ≤ Subgroup.centralizer ({w} : Set G))
    (hcomm : ∀ a ∈ Subgroup.centralizer ({w} : Set G), ∀ b ∈ Subgroup.centralizer ({w} : Set G),
      a * b * a⁻¹ * b⁻¹ ∈ R)
    (hw3 : w ^ 3 = 1) (hw1 : w ≠ 1)
    (U : Subgroup (Matrix.GeneralLinearGroup (Fin 3) L)) (e : R ≃* U)
    (hcen : ∀ X : R, X ∈ Subgroup.center R ↔
      ∃ μ : L, (((e X : U) : Matrix.GeneralLinearGroup (Fin 3) L) :
        Matrix (Fin 3) (Fin 3) L) = Matrix.scalar (Fin 3) μ) : LayerProp w := by
  let φ : R →* Matrix (Fin 3) (Fin 3) L :=
    (Units.coeHom (Matrix (Fin 3) (Fin 3) L)).comp (U.subtype.comp e.toMonoidHom)
  have hφ : Function.Injective φ := by
    intro a b hab
    apply e.injective
    apply Subtype.ext
    apply Units.ext
    exact hab
  have hcen' : ∀ u : R, (∀ g : R, g * u = u * g) → ∃ μ : L, φ u = Matrix.scalar (Fin 3) μ :=
    fun u hu => (hcen u).1 (Subgroup.mem_center_iff.mpr hu)
  exact layer_of_rep w R hP hwR hRc hcomm hw3 hw1 φ hφ hcen'

end CFSG.RankThree.PartTwo.Sec19.TorusLayerAux

end
