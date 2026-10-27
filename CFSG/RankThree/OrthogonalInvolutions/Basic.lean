module

public import TauCeti.LinearAlgebra.QuadraticForm.OrthogonalGroup.Basic
public import TauCeti.LinearAlgebra.BilinearForm.SymplecticBasis
public import CFSG.LieType.BorelTits.OrthogonalForm

public section

namespace CFSG.RankThree.OrthogonalInvolutions

open Module QuadraticMap

variable {K : Type*} [Field K] {V : Type*} [AddCommGroup V] [Module K V]

abbrev commSpace (g : V ≃ₗ[K] V) : Submodule K V :=
  LinearMap.range ((g : V →ₗ[K] V) - 1)

abbrev fixSpace (g : V ≃ₗ[K] V) : Submodule K V :=
  LinearMap.ker ((g : V →ₗ[K] V) - 1)

theorem mem_commSpace {g : V ≃ₗ[K] V} {x : V} : x ∈ commSpace g ↔ ∃ v, g v - v = x := by
  simp [commSpace]

theorem sub_mem_commSpace (g : V ≃ₗ[K] V) (v : V) : g v - v ∈ commSpace g :=
  mem_commSpace.mpr ⟨v, rfl⟩

theorem mem_fixSpace {g : V ≃ₗ[K] V} {v : V} : v ∈ fixSpace g ↔ g v = v := by
  simp [fixSpace, sub_eq_zero]

theorem finrank_commSpace_add_finrank_fixSpace [FiniteDimensional K V] (g : V ≃ₗ[K] V) :
    finrank K (commSpace g) + finrank K (fixSpace g) = finrank K V :=
  LinearMap.finrank_range_add_finrank_ker _

theorem one_le_finrank_commSpace [FiniteDimensional K V] {g : V ≃ₗ[K] V} (hg : g ≠ 1) :
    1 ≤ finrank K (commSpace g) := by
  rw [Submodule.one_le_finrank_iff]
  intro hbot
  apply hg
  ext v
  have hv : g v - v ∈ commSpace g := sub_mem_commSpace g v
  rw [hbot, Submodule.mem_bot, sub_eq_zero] at hv
  rw [hv, LinearEquiv.coe_one, id]

@[expose] def toQuadForm (Q : QuadraticForm K V) (hQ : Q.polarBilin.Nondegenerate) :
    CFSG.LieType.BorelTits.QuadForm K V where
  Q := Q
  polar :=
    { σ := RingEquiv.refl K
      β := polar Q
      add_left := polar_add_left Q
      smul_left := fun c u v => by rw [polar_smul_left, smul_eq_mul]; rfl
      add_right := polar_add_right Q
      smul_right := fun c u v => by rw [polar_smul_right, smul_eq_mul]
      refl := fun u v h => by rw [polar_comm]; exact h
      nondeg := fun u h => hQ.1 u fun v => by rw [polarBilin_apply_apply]; exact h v }
  polar_σ := rfl
  Q_smul := fun c v => by rw [QuadraticMap.map_smul, smul_eq_mul, pow_two]
  Q_add := fun u v => by
    show Q (u + v) = Q u + Q v + QuadraticMap.polar Q u v
    rw [QuadraticMap.polar]
    ring

@[simp] theorem toQuadForm_Q (Q : QuadraticForm K V) (hQ : Q.polarBilin.Nondegenerate) (v : V) :
    (toQuadForm Q hQ).Q v = Q v :=
  rfl

@[simp] theorem toQuadForm_polar_β (Q : QuadraticForm K V) (hQ : Q.polarBilin.Nondegenerate)
    (u v : V) : (toQuadForm Q hQ).polar.β u v = polar Q u v :=
  rfl

theorem toQuadForm_perp (Q : QuadraticForm K V) (hQ : Q.polarBilin.Nondegenerate)
    (W : Submodule K V) :
    (toQuadForm Q hQ).polar.perp W = LinearMap.BilinForm.orthogonal Q.polarBilin W := by
  ext v
  rw [CFSG.LieType.BorelTits.ReflForm.mem_perp, LinearMap.BilinForm.mem_orthogonal_iff]
  simp

theorem toQuadForm_Q_apply {Q : QuadraticForm K V} (hQ : Q.polarBilin.Nondegenerate)
    {g : V ≃ₗ[K] V} (hg : g ∈ TauCeti.QuadraticMap.orthogonalGroup Q) (v : V) :
    (toQuadForm Q hQ).Q ((g : V →ₗ[K] V) v) = (toQuadForm Q hQ).Q v :=
  TauCeti.QuadraticMap.map_app_of_mem_orthogonalGroup hg v

theorem map_add_eq (Q : QuadraticForm K V) (x y : V) : Q (x + y) = Q x + Q y + polar Q x y := by
  rw [polar]; ring

theorem apply_apply_of_mul_self {t : V ≃ₗ[K] V} (htt : t * t = 1) (v : V) : t (t v) = v := by
  rw [← LinearEquiv.mul_apply, htt, LinearEquiv.coe_one, id]

theorem polar_apply_eq_polar_apply {Q : QuadraticForm K V} {t : V ≃ₗ[K] V}
    (hO : t ∈ TauCeti.QuadraticMap.orthogonalGroup Q) (htt : t * t = 1) (x y : V) :
    polar Q (t x) y = polar Q x (t y) := by
  rw [← TauCeti.QuadraticMap.polar_apply_of_mem_orthogonalGroup hO x (t y),
    apply_apply_of_mul_self htt]

theorem polar_sub_eq_polar_sub {Q : QuadraticForm K V} {t : V ≃ₗ[K] V}
    (hO : t ∈ TauCeti.QuadraticMap.orthogonalGroup Q) (htt : t * t = 1) (x y : V) :
    polar Q (t x - x) y = polar Q x (t y - y) := by
  rw [QuadraticMap.polar_sub_left, QuadraticMap.polar_sub_right,
    polar_apply_eq_polar_apply hO htt]

theorem fixSpace_eq_orthogonal_commSpace {Q : QuadraticForm K V}
    (hQ : Q.polarBilin.Nondegenerate) {t : V ≃ₗ[K] V}
    (hO : t ∈ TauCeti.QuadraticMap.orthogonalGroup Q) (htt : t * t = 1) :
    fixSpace t = LinearMap.BilinForm.orthogonal Q.polarBilin (commSpace t) := by
  ext v
  rw [LinearMap.BilinForm.mem_orthogonal_iff, mem_fixSpace]
  constructor
  · intro hv x hx
    obtain ⟨u, rfl⟩ := mem_commSpace.mp hx
    rw [polarBilin_apply_apply, polar_sub_eq_polar_sub hO htt, hv, sub_self, polar_zero_right]
  · intro hv
    have h0 : t v - v = 0 := hQ.1 _ fun y => by
      rw [polarBilin_apply_apply, polar_sub_eq_polar_sub hO htt, polar_comm]
      exact hv _ (sub_mem_commSpace t y)
    exact sub_eq_zero.mp h0

@[expose] def wallForm (Q : QuadraticForm K V) (t : V ≃ₗ[K] V) : LinearMap.BilinForm K V :=
  Q.polarBilin.compl₂ ((t : V →ₗ[K] V) - 1)

theorem wallForm_apply (Q : QuadraticForm K V) (t : V ≃ₗ[K] V) (x y : V) :
    wallForm Q t x y = polar Q x (t y - y) := by
  simp [wallForm]

theorem wallForm_symm {Q : QuadraticForm K V} {t : V ≃ₗ[K] V}
    (hO : t ∈ TauCeti.QuadraticMap.orthogonalGroup Q) (htt : t * t = 1) (x y : V) :
    wallForm Q t x y = wallForm Q t y x := by
  rw [wallForm_apply, wallForm_apply, ← polar_sub_eq_polar_sub hO htt, polar_comm]

theorem wallForm_isSymm {Q : QuadraticForm K V} {t : V ≃ₗ[K] V}
    (hO : t ∈ TauCeti.QuadraticMap.orthogonalGroup Q) (htt : t * t = 1) :
    (wallForm Q t).IsSymm :=
  ⟨wallForm_symm hO htt⟩

theorem wallForm_apply_fixSpace (Q : QuadraticForm K V) {t : V ≃ₗ[K] V} (x : V) {c : V}
    (hc : c ∈ fixSpace t) : wallForm Q t x c = 0 := by
  rw [mem_fixSpace] at hc
  rw [wallForm_apply, hc, sub_self, polar_zero_right]

theorem mem_fixSpace_of_wallForm {Q : QuadraticForm K V} (hQ : Q.polarBilin.Nondegenerate)
    {t : V ≃ₗ[K] V} (hO : t ∈ TauCeti.QuadraticMap.orthogonalGroup Q) (htt : t * t = 1) {x : V}
    (hx : ∀ y, wallForm Q t x y = 0) : x ∈ fixSpace t := by
  rw [fixSpace_eq_orthogonal_commSpace hQ hO htt, LinearMap.BilinForm.mem_orthogonal_iff]
  intro n hn
  obtain ⟨u, rfl⟩ := mem_commSpace.mp hn
  rw [polarBilin_apply_apply, polar_comm, ← wallForm_apply]
  exact hx u

theorem wallForm_restrict_nondegenerate {Q : QuadraticForm K V}
    (hQ : Q.polarBilin.Nondegenerate) {t : V ≃ₗ[K] V}
    (hO : t ∈ TauCeti.QuadraticMap.orthogonalGroup Q) (htt : t * t = 1) {X : Submodule K V}
    (hX : IsCompl X (fixSpace t)) : ((wallForm Q t).restrict X).Nondegenerate := by
  have hsep : ((wallForm Q t).restrict X).SeparatingLeft := by
    intro x hx
    have hfix : (x : V) ∈ fixSpace t := mem_fixSpace_of_wallForm hQ hO htt fun v => by
      have hv : v ∈ X ⊔ fixSpace t := by rw [hX.sup_eq_top]; exact Submodule.mem_top
      obtain ⟨y, hy, c, hc, rfl⟩ := Submodule.mem_sup.mp hv
      rw [map_add, wallForm_apply_fixSpace Q _ hc, add_zero]
      exact hx ⟨y, hy⟩
    exact Subtype.ext (Submodule.disjoint_def.mp hX.disjoint _ x.2 hfix)
  exact (LinearMap.IsRefl.nondegenerate_iff_separatingLeft
    ((wallForm_isSymm hO htt).restrict X).isRefl).mpr hsep

theorem exists_mem_compl_of_mem_commSpace {t : V ≃ₗ[K] V} {X : Submodule K V}
    (hX : IsCompl X (fixSpace t)) {w : V} (hw : w ∈ commSpace t) : ∃ x ∈ X, t x - x = w := by
  obtain ⟨v, rfl⟩ := mem_commSpace.mp hw
  have hv : v ∈ X ⊔ fixSpace t := by rw [hX.sup_eq_top]; exact Submodule.mem_top
  obtain ⟨y, hy, c, hc, rfl⟩ := Submodule.mem_sup.mp hv
  rw [mem_fixSpace] at hc
  exact ⟨y, hy, by rw [map_add, hc]; abel⟩

theorem finrank_compl_eq [FiniteDimensional K V] {t : V ≃ₗ[K] V} {X : Submodule K V}
    (hX : IsCompl X (fixSpace t)) : finrank K X = finrank K (commSpace t) := by
  have h1 := Submodule.finrank_add_eq_of_isCompl hX
  have h2 := finrank_commSpace_add_finrank_fixSpace t
  omega

section CharTwo

variable [CharP K 2]

theorem polar_self_eq_zero (Q : QuadraticForm K V) (x : V) : polar Q x x = 0 := by
  rw [polar_self, two_nsmul, CharTwo.add_self_eq_zero]

variable (K) in
include K in
theorem neg_vec_eq (v : V) : -v = v := by
  rw [← one_smul K v, ← neg_smul, CharTwo.neg_eq]

variable (K) in
include K in
theorem add_self_vec (v : V) : v + v = 0 := by
  have h := neg_vec_eq K v
  rw [eq_comm, eq_neg_iff_add_eq_zero] at h
  exact h

variable (K) in
include K in
theorem sub_eq_add_vec (u v : V) : u - v = u + v := by
  rw [sub_eq_add_neg, neg_vec_eq K]

theorem commSpace_le_fixSpace {t : V ≃ₗ[K] V} (htt : t * t = 1) : commSpace t ≤ fixSpace t := by
  intro x hx
  obtain ⟨v, rfl⟩ := mem_commSpace.mp hx
  rw [mem_fixSpace, map_sub, apply_apply_of_mul_self htt, sub_eq_add_vec K, sub_eq_add_vec K,
    add_comm]

theorem polar_commSpace_eq_zero {Q : QuadraticForm K V} {t : V ≃ₗ[K] V}
    (hO : t ∈ TauCeti.QuadraticMap.orthogonalGroup Q) (htt : t * t = 1) {x y : V}
    (hx : x ∈ commSpace t) (hy : y ∈ commSpace t) : polar Q x y = 0 := by
  obtain ⟨u, rfl⟩ := mem_commSpace.mp hx
  have hy' := commSpace_le_fixSpace htt hy
  rw [mem_fixSpace] at hy'
  rw [polar_sub_eq_polar_sub hO htt, hy', sub_self, polar_zero_right]

theorem map_sub_eq_polar {Q : QuadraticForm K V} {t : V ≃ₗ[K] V}
    (hO : t ∈ TauCeti.QuadraticMap.orthogonalGroup Q) (v : V) : Q (t v - v) = polar Q (t v) v := by
  rw [sub_eq_add_vec K, map_add_eq, TauCeti.QuadraticMap.map_app_of_mem_orthogonalGroup hO v,
    CharTwo.add_self_eq_zero, zero_add]

theorem two_mul_finrank_commSpace_le [FiniteDimensional K V] {t : V ≃ₗ[K] V} (htt : t * t = 1) :
    2 * finrank K (commSpace t) ≤ finrank K V := by
  have h1 := finrank_commSpace_add_finrank_fixSpace t
  have h2 := Submodule.finrank_mono (commSpace_le_fixSpace htt)
  omega

theorem wallForm_self {Q : QuadraticForm K V} {t : V ≃ₗ[K] V}
    (hO : t ∈ TauCeti.QuadraticMap.orthogonalGroup Q) (x : V) :
    wallForm Q t x x = Q (t x - x) := by
  rw [wallForm_apply, map_sub_eq_polar hO, QuadraticMap.polar_sub_right, polar_self_eq_zero,
    sub_zero, polar_comm]

theorem wallForm_restrict_isAlt_iff {Q : QuadraticForm K V} {t : V ≃ₗ[K] V}
    (hO : t ∈ TauCeti.QuadraticMap.orthogonalGroup Q) {X : Submodule K V}
    (hX : IsCompl X (fixSpace t)) :
    ((wallForm Q t).restrict X).IsAlt ↔ ∀ x ∈ commSpace t, Q x = 0 := by
  constructor
  · intro halt w hw
    obtain ⟨x, hx, rfl⟩ := exists_mem_compl_of_mem_commSpace hX hw
    rw [← wallForm_self hO]
    exact halt ⟨x, hx⟩
  · intro hzero x
    change wallForm Q t x x = 0
    rw [wallForm_self hO]
    exact hzero _ (sub_mem_commSpace t x)

theorem even_finrank_commSpace_of_forall_eq_zero [FiniteDimensional K V]
    {Q : QuadraticForm K V} (hQ : Q.polarBilin.Nondegenerate) {t : V ≃ₗ[K] V}
    (hO : t ∈ TauCeti.QuadraticMap.orthogonalGroup Q) (htt : t * t = 1)
    (hzero : ∀ x ∈ commSpace t, Q x = 0) : Even (finrank K (commSpace t)) := by
  obtain ⟨X, hX⟩ := (fixSpace t).exists_isCompl
  have hX' : IsCompl X (fixSpace t) := hX.symm
  rw [← finrank_compl_eq hX']
  exact LinearMap.BilinForm.IsAlt.even_finrank ((wallForm_restrict_isAlt_iff hO hX').mpr hzero)
    (wallForm_restrict_nondegenerate hQ hO htt hX')

end CharTwo

end CFSG.RankThree.OrthogonalInvolutions
