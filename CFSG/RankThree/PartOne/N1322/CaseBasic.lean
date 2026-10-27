module

public import CFSG.RankThree.SubgroupLists.SchurCommutant
public import Mathlib.GroupTheory.IsPerfect
import Mathlib.Tactic.NoncommRing
public import CFSG.RankThree.PartOne.N1322.CoreDefs

public section

namespace CFSG.RankThree.PartOne.N1322

open scoped Matrix
open CFSG.RepresentationTheory

variable {K : Type*} [Field K]

theorem IsRefl.det_eq {g : GL (Fin 3) K} (hg : IsRefl g) :
    (g : Matrix (Fin 3) (Fin 3) K).det = -1 := by
  obtain ⟨r, φ, hr, hφ, hgm⟩ := hg
  have h1 : (g : Matrix (Fin 3) (Fin 3) K) =
      1 + Matrix.replicateCol Unit r * Matrix.replicateRow Unit (-φ) := by
    rw [hgm, ← Matrix.vecMulVec_eq Unit, Matrix.vecMulVec_neg, sub_eq_add_neg]
  rw [h1, Matrix.det_one_add_replicateCol_mul_replicateRow, neg_dotProduct, hφ]
  ring

theorem det_eq_one_of_perfect {H : Subgroup (GL (Fin 3) K)} [hperf : Group.IsPerfect H]
    {x : GL (Fin 3) K} (hx : x ∈ H) : (x : Matrix (Fin 3) (Fin 3) K).det = 1 := by
  let δ : H →* Kˣ := (Matrix.GeneralLinearGroup.det).comp H.subtype
  have hker : δ.ker = ⊤ := by
    rw [eq_top_iff, ← hperf.commutator_eq_top]
    exact Abelianization.commutator_subset_ker δ
  have h1 : δ ⟨x, hx⟩ = 1 := MonoidHom.mem_ker.mp (by rw [hker]; trivial)
  have h2 := congrArg Units.val h1
  simpa [δ] using h2

theorem neg_one_comm (a : GL (Fin 3) K) : (-1 : GL (Fin 3) K) * a = a * (-1) := by
  apply Units.ext
  simp

theorem neg_one_mul_neg_one : (-1 : GL (Fin 3) K) * (-1) = 1 := by
  apply Units.ext
  simp

theorem central_sq_eq_one {X : Subgroup (GL (Fin 3) K)} (hirr : IsIrreducibleMatrixRep X.subtype)
    {z : GL (Fin 3) K} (hz2 : z * z = 1) (hzc : ∀ y ∈ X, z * y = y * z) :
    z = 1 ∨ z = -1 := by
  have hz2m : (z : Matrix (Fin 3) (Fin 3) K) * z = 1 := by
    have := congrArg (fun x : GL (Fin 3) K => (x : Matrix (Fin 3) (Fin 3) K)) hz2
    simpa using this
  let W : Submodule K (Fin 3 → K) := LinearMap.ker ((z : Matrix (Fin 3) (Fin 3) K) - 1).mulVecLin
  have hW : ∀ y : X, ∀ w ∈ W, ((y : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ w ∈ W := by
    intro y w hw
    have hw' : ((z : Matrix (Fin 3) (Fin 3) K) - 1) *ᵥ w = 0 := hw
    have hc : (z : Matrix (Fin 3) (Fin 3) K) * ((y : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
        ((y : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) * z := by
      rw [← Units.val_mul, ← Units.val_mul, hzc y y.2]
    have e1 : (z : Matrix (Fin 3) (Fin 3) K) *ᵥ w = w := by
      rw [Matrix.sub_mulVec, Matrix.one_mulVec] at hw'
      exact sub_eq_zero.mp hw'
    show ((z : Matrix (Fin 3) (Fin 3) K) - 1) *ᵥ (((y : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ w) = 0
    rw [Matrix.sub_mulVec, Matrix.one_mulVec, Matrix.mulVec_mulVec, hc, ← Matrix.mulVec_mulVec, e1,
      sub_self]
  rcases hirr W hW with h | h
  · right
    apply Units.ext
    ext i j
    have h1 : ((z : Matrix (Fin 3) (Fin 3) K) + 1) *ᵥ Pi.single j 1 ∈ W := by
      show ((z : Matrix (Fin 3) (Fin 3) K) - 1) *ᵥ (((z : Matrix (Fin 3) (Fin 3) K) + 1) *ᵥ Pi.single j 1) = 0
      rw [Matrix.mulVec_mulVec]
      have : ((z : Matrix (Fin 3) (Fin 3) K) - 1) * ((z : Matrix (Fin 3) (Fin 3) K) + 1) = 0 := by
        have e : ((z : Matrix (Fin 3) (Fin 3) K) - 1) * ((z : Matrix (Fin 3) (Fin 3) K) + 1) =
            (z : Matrix (Fin 3) (Fin 3) K) * z - 1 := by noncomm_ring
        rw [e, hz2m, sub_self]
      rw [this, Matrix.zero_mulVec]
    rw [h, Submodule.mem_bot] at h1
    have h3 := congrFun h1 i
    rw [Matrix.add_mulVec, Matrix.one_mulVec, Matrix.mulVec_single_one] at h3
    simp only [Pi.add_apply, Pi.zero_apply] at h3
    simp only [Units.val_neg, Units.val_one, Matrix.neg_apply, Matrix.one_apply]
    have h4 : (z : Matrix (Fin 3) (Fin 3) K) i j + (Pi.single j (1 : K) : Fin 3 → K) i = 0 := by
      simpa using h3
    simp only [Pi.single_apply] at h4
    by_cases hij : i = j
    · subst hij; simp at h4 ⊢; linear_combination h4
    · simp [hij] at h4 ⊢
      exact h4
  · left
    apply Units.ext
    ext i j
    have h1 : Pi.single j (1 : K) ∈ W := by rw [h]; trivial
    have h2 : ((z : Matrix (Fin 3) (Fin 3) K) - 1) *ᵥ Pi.single j 1 = 0 := h1
    have h3 := congrFun h2 i
    rw [Matrix.mulVec_single_one] at h3
    simp only [Pi.zero_apply] at h3
    simp only [Units.val_one, Matrix.one_apply]
    exact sub_eq_zero.mp h3

theorem IsRefl.ne_neg_one (h4 : (4 : K) ≠ 0) {t : GL (Fin 3) K} (ht : IsRefl t) :
    (t : Matrix (Fin 3) (Fin 3) K) ≠ -1 := by
  intro h
  have h1 := ht.trace_eq
  rw [h] at h1
  simp at h1
  apply h4
  linear_combination -h1

theorem central_of_scalar {z : GL (Fin 3) K} {c : K}
    (hz : (z : Matrix (Fin 3) (Fin 3) K) = Matrix.scalar (Fin 3) c) (g : GL (Fin 3) K) :
    g * z = z * g := by
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, hz]
  exact ((Matrix.scalar_commute c (fun r' => Commute.all c r') _).symm).eq

theorem scalar_commutant_of_noncomm {p : ℕ} [Fact p.Prime]
    {H : Subgroup (GL (Fin 3) (ZMod p))} (hirr : IsIrreducibleMatrixRep H.subtype)
    (hnc : ∃ a ∈ H, ∃ b ∈ H, a * b ≠ b * a) :
    ∀ M : Matrix (Fin 3) (Fin 3) (ZMod p), (∀ g ∈ H, (g : Matrix (Fin 3) (Fin 3) (ZMod p)) * M = M * g) →
      ∃ c : ZMod p, M = Matrix.scalar (Fin 3) c := by
  rcases CFSG.RankThree.SubgroupLists.scalar_commutant_or_cyclic Nat.prime_three hirr with h | ⟨hcyc, -, -⟩
  · exact h
  · exfalso
    obtain ⟨a, ha, b, hb, hab⟩ := hnc
    obtain ⟨g, hg⟩ := hcyc.exists_generator
    obtain ⟨i, hi⟩ := hg ⟨a, ha⟩
    obtain ⟨j, hj⟩ := hg ⟨b, hb⟩
    apply hab
    have hi' : (g : GL (Fin 3) (ZMod p)) ^ i = a := congrArg Subtype.val hi
    have hj' : (g : GL (Fin 3) (ZMod p)) ^ j = b := congrArg Subtype.val hj
    rw [← hi', ← hj', ← zpow_add, ← zpow_add, add_comm]

@[expose] def actOn {G : Type*} [Group G] {X H : Subgroup G}
    (hnorm : ∀ g ∈ X, ∀ x ∈ H, g * x * g⁻¹ ∈ H) {g : G} (hg : g ∈ X) : H ≃* H where
  toFun x := ⟨g * x * g⁻¹, hnorm g hg x x.2⟩
  invFun x := ⟨g⁻¹ * x * g, by simpa using hnorm g⁻¹ (X.inv_mem hg) x x.2⟩
  left_inv x := Subtype.ext (by show g⁻¹ * (g * (x : G) * g⁻¹) * g = x; group)
  right_inv x := Subtype.ext (by show g * (g⁻¹ * (x : G) * g) * g⁻¹ = x; group)
  map_mul' x y := Subtype.ext (by
    show g * ((x : G) * (y : G)) * g⁻¹ = g * (x : G) * g⁻¹ * (g * (y : G) * g⁻¹)
    group)

end CFSG.RankThree.PartOne.N1322
