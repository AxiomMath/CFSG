module

public import CFSG.Permutation.UnitaryThreeRecognition.StdHyp
public import CFSG.Permutation.UnitaryThreeRecognition.BridgeTorus

public section

namespace CFSG.UnitaryThreeRecognition

open MulAction CFSG.BenderSuzuki.MatrixGroups CFSG.BenderSuzuki.External
open CFSG.UnitaryThreeRecognition.Model CFSG.UnitaryThreeRecognition.WeylAlg

structure CoordHyp {G Ω : Type*} [Group G] [MulAction G Ω] (Q : Subgroup G) (a b : Ω) (j : G)
    {K : Type*} [Field K] (J : HermitianForm 3 K) (φ : Q ≃* Coord J) : Prop where
  torus : ∀ t ∈ pairStab G a b, ∃ k : Kˣ, ∀ (x : Q) (hx : t * (x : G) * t⁻¹ ∈ Q),
    φ ⟨t * x * t⁻¹, hx⟩ = hermitianTorusAction J k (φ x)
  torus_surj : ∀ k : Kˣ, ∃ t ∈ pairStab G a b, ∀ (x : Q) (hx : t * (x : G) * t⁻¹ ∈ Q),
    φ ⟨t * x * t⁻¹, hx⟩ = hermitianTorusAction J k (φ x)
  center : ∀ z : Q, (z : G) ∈ centQ Q j ↔ (φ z).1.1 = 0

namespace CoordHyp

variable {G Ω : Type*} [Group G] [MulAction G Ω] {Q : Subgroup G} {a b : Ω} {j s : G}
  {p f d : ℕ} {K : Type*} [Field K] {J : HermitianForm 3 K} {φ : Q ≃* Coord J}
  (C : CoordHyp Q a b j J φ) (S : StdHyp G Q a b j s p f d)
include C S

theorem exists_coord_witnesses [Finite G] [Finite Ω] :
    ∃ z₀ w₀ : Coord J, z₀ ≠ 1 ∧ w₀.1.1 ≠ 0 := by
  obtain ⟨z, hz, hz1⟩ := S.exists_centQ_ne_one
  obtain ⟨u, hu, huZ⟩ := S.exists_mem_not_centQ
  refine ⟨φ ⟨z, (mem_centQ.mp hz).1⟩, φ ⟨u, hu⟩, ?_, ?_⟩
  · intro e
    apply hz1
    have := φ.injective (e.trans (map_one φ).symm)
    exact congrArg Subtype.val this
  · intro e
    exact huZ ((C.center ⟨u, hu⟩).mpr e)

theorem torus_param_unique [Finite G] [Finite Ω] {q : ℕ} (hconj : ∀ x : K, J.conj x = x ^ q)
    (hcop : Nat.Coprime 3 (q + 1)) {k k' : Kˣ}
    (h : ∀ x : Q, hermitianTorusAction J k (φ x) = hermitianTorusAction J k' (φ x)) : k = k' := by
  obtain ⟨z₀, w₀, hz₀, hw₀⟩ := C.exists_coord_witnesses S
  have h1 : k'⁻¹ * k = 1 := by
    apply torus_eq_one_of_forall hconj hcop _ hz₀ hw₀
    intro c
    obtain ⟨x, rfl⟩ := φ.surjective c
    rw [torus_mul_apply, h x, ← torus_mul_apply, inv_mul_cancel, torus_one_apply]
  calc k = k' * (k'⁻¹ * k) := by group
    _ = k' := by rw [h1, mul_one]

noncomputable def kOf (t : pairStab G a b) : Kˣ := Classical.choose (C.torus t t.2)

omit S in
theorem kOf_spec (t : pairStab G a b) (x : Q) (hx : (t : G) * (x : G) * (t : G)⁻¹ ∈ Q) :
    φ ⟨t * x * t⁻¹, hx⟩ = hermitianTorusAction J (C.kOf t) (φ x) :=
  Classical.choose_spec (C.torus t t.2) x hx

omit S in
theorem kOf_spec' (t : pairStab G a b) (x y : Q) (hy : (y : G) = t * x * (t : G)⁻¹) :
    φ y = hermitianTorusAction J (C.kOf t) (φ x) := by
  have hx : (t : G) * (x : G) * (t : G)⁻¹ ∈ Q := by rw [← hy]; exact y.2
  rw [← C.kOf_spec t x hx]
  congr 1
  exact Subtype.ext hy

variable [Finite G] [Finite Ω] {q : ℕ} (hconj : ∀ x : K, J.conj x = x ^ q)
  (hcop : Nat.Coprime 3 (q + 1))
include hconj hcop

theorem kOf_mul (t₁ t₂ : pairStab G a b) : C.kOf (t₁ * t₂) = C.kOf t₁ * C.kOf t₂ := by
  apply C.torus_param_unique S hconj hcop
  intro x
  let y₂ : Q := ⟨(t₂ : G) * x * (t₂ : G)⁻¹, S.root.normal t₂ t₂.2.1 x x.2⟩
  let y : Q := ⟨(t₁ : G) * y₂ * (t₁ : G)⁻¹, S.root.normal t₁ t₁.2.1 _ y₂.2⟩
  have e1 := C.kOf_spec' (t₁ * t₂) x y (by
    change (t₁ : G) * ((t₂ : G) * x * (t₂ : G)⁻¹) * (t₁ : G)⁻¹ =
      ((t₁ * t₂ : pairStab G a b) : G) * x * ((t₁ * t₂ : pairStab G a b) : G)⁻¹
    simp only [Subgroup.coe_mul, mul_inv_rev]; group)
  have e2 := C.kOf_spec' t₁ y₂ y rfl
  have e3 := C.kOf_spec' t₂ x y₂ rfl
  rw [← e1, e2, e3, ← torus_mul_apply]

@[expose] noncomputable def kOfHom : pairStab G a b →* Kˣ :=
  MonoidHom.mk' C.kOf (C.kOf_mul S hconj hcop)

theorem kOfHom_apply (t : pairStab G a b) : C.kOfHom S hconj hcop t = C.kOf t := rfl

theorem kOfHom_injective : Function.Injective (C.kOfHom S hconj hcop) := by
  rw [injective_iff_map_eq_one]
  intro t ht
  rw [kOfHom_apply] at ht
  by_contra ht1
  have ht1' : (t : G) ≠ 1 := fun e => ht1 (Subtype.ext e)
  obtain ⟨u, hu, huZ⟩ := S.exists_mem_not_centQ
  apply huZ
  apply S.mem_centQ_of_commute t.2 ht1' hu
  let y : Q := ⟨(t : G) * u * (t : G)⁻¹, S.root.normal t t.2.1 u hu⟩
  have e := C.kOf_spec' t ⟨u, hu⟩ y rfl
  rw [ht, torus_one_apply] at e
  have := congrArg Subtype.val (φ.injective e)
  change (t : G) * u * (t : G)⁻¹ = u at this
  calc (t : G) * u = (t : G) * u * (t : G)⁻¹ * t := by group
    _ = u * t := by rw [this]

theorem kOfHom_surjective : Function.Surjective (C.kOfHom S hconj hcop) := by
  intro k
  obtain ⟨t, ht, htk⟩ := C.torus_surj k
  refine ⟨⟨t, ht⟩, ?_⟩
  rw [kOfHom_apply]
  apply C.torus_param_unique S hconj hcop
  intro x
  let y : Q := ⟨t * x * t⁻¹, S.root.normal t ht.1 x x.2⟩
  rw [← C.kOf_spec' ⟨t, ht⟩ x y rfl]
  exact htk x _

@[expose] noncomputable def torusEquiv : pairStab G a b ≃* Kˣ :=
  MulEquiv.ofBijective (C.kOfHom S hconj hcop)
    ⟨C.kOfHom_injective S hconj hcop, C.kOfHom_surjective S hconj hcop⟩

theorem torusEquiv_apply (t : pairStab G a b) : C.torusEquiv S hconj hcop t = C.kOf t := rfl

end CoordHyp


end CFSG.UnitaryThreeRecognition
