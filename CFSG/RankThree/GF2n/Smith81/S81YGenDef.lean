module

public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.RankThree.GF2n.Smith81.S81NBridge
public import CFSG.RankThree.GF2n.Smith81.S81TModelDef
public import CFSG.RankThree.GF2n.Stroth80.Sec1110Core

public section

namespace CFSG.RankThree.GF2n.Smith81.RootGen

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
  CFSG.RankThree.GF2n CFSG.RankThree.GF2n.Stroth80 CFSG.RankThree.GF2n.Smith81.EGeom
  CFSG.RankThree.GF2n.Smith81.E3LBridge CFSG.RankThree.GF2n.Smith81.E3LCond
  CFSG.RankThree.GF2n.Smith81 CFSG.RankThree.GF2n.Smith81.MinuscT
open scoped commutatorElement

@[expose] def IsPurePt {K : Type} [Field K] {V : Type} [AddCommGroup V] [Module K V]
    (Γ : Subgroup (V ≃ₗ[K] V)) (p₀ p : V) : Prop :=
  ∃ g ∈ Γ, ∃ c : K, c ≠ 0 ∧ p = c • g p₀

structure MinRootFacts {K : Type} [Field K] {V : Type} [AddCommGroup V] [Module K V]
    (Γ : Subgroup (V ≃ₗ[K] V)) (p₀ : V) (IsRt : (V ≃ₗ[K] V) → Prop) : Prop where
  sq : ∀ r, IsRt r → r * r = 1
  pure_sub : ∀ r, IsRt r → ∀ p, IsPurePt Γ p₀ p → r p - p = 0 ∨ IsPurePt Γ p₀ (r p - p)
  odd_disj : ∀ r s, IsRt r → IsRt s → Odd (orderOf (r * s)) → r * s ≠ 1 →
    LinearMap.range ((r : V →ₗ[K] V) - 1) ⊓ LinearMap.range ((s : V →ₗ[K] V) - 1) = ⊥
  move : ∀ r s, IsRt r → IsRt s → ¬ (Odd (orderOf (r * s)) ∧ r * s ≠ 1) →
    ∀ p, IsPurePt Γ p₀ p → p ∈ LinearMap.range ((r : V →ₗ[K] V) - 1) →
      ∃ c ∈ Γ, c * r = r * c ∧ s (c p) = c p

variable {G : Type} [Group G]

section Acts

variable {M Q B : Subgroup G} {K : Type} [Field K] {V : Type} [AddCommGroup V] [Module K V]
  {φ : Lgen M (LB M Q B) →* (V ≃ₗ[K] V)}

@[expose] def Acts (φ : Lgen M (LB M Q B) →* (V ≃ₗ[K] V)) (x : G) (r : V ≃ₗ[K] V) : Prop :=
  ∃ hxL : x ∈ Lgen M (LB M Q B), φ ⟨x, hxL⟩ = r

theorem Acts.mul {x y : G} {r s : V ≃ₗ[K] V} (hx : Acts φ x r) (hy : Acts φ y s) :
    Acts φ (x * y) (r * s) := by
  obtain ⟨hxL, hx⟩ := hx
  obtain ⟨hyL, hy⟩ := hy
  refine ⟨(Lgen M (LB M Q B)).mul_mem hxL hyL, ?_⟩
  have : (⟨x * y, (Lgen M (LB M Q B)).mul_mem hxL hyL⟩ : Lgen M (LB M Q B)) =
      ⟨x, hxL⟩ * ⟨y, hyL⟩ := rfl
  rw [this, map_mul, hx, hy]

theorem Acts.one : Acts φ (1 : G) (1 : V ≃ₗ[K] V) :=
  ⟨(Lgen M (LB M Q B)).one_mem, by
    have : (⟨1, (Lgen M (LB M Q B)).one_mem⟩ : Lgen M (LB M Q B)) = 1 := rfl
    rw [this, map_one]⟩

theorem Acts.pow {x : G} {r : V ≃ₗ[K] V} (hx : Acts φ x r) (n : ℕ) :
    Acts φ (x ^ n) (r ^ n) := by
  induction n with
  | zero => simpa using (Acts.one : Acts φ (1 : G) (1 : V ≃ₗ[K] V))
  | succ n ih => rw [pow_succ, pow_succ]; exact ih.mul hx

theorem Acts.mem_Lgen {x : G} {r : V ≃ₗ[K] V} (hx : Acts φ x r) : x ∈ Lgen M (LB M Q B) := by
  obtain ⟨h, -⟩ := hx
  exact h

theorem Acts.phi {x : G} {r : V ≃ₗ[K] V} (hx : Acts φ x r) (hxL : x ∈ Lgen M (LB M Q B)) :
    φ ⟨x, hxL⟩ = r := by
  obtain ⟨_, h⟩ := hx
  exact h

end Acts

structure GDat (M Q Z B : Subgroup G) (K : Type) [Field K] (γ : G → K)
    (M₀ : Tim79.QuadModel Q Z K γ) {V : Type} [AddCommGroup V] [Module K V]
    (ψ : M₀.E ≃ₗ[K] V) (φ : Lgen M (LB M Q B) →* (V ≃ₗ[K] V)) (Γ : Subgroup (V ≃ₗ[K] V))
    (p₀ : V) (U₀ : Subgroup (V ≃ₗ[K] V)) (IsRt : (V ≃ₗ[K] V) → Prop) (z : G) : Prop where
  ctx : Ctx M Q Z B
  hD : GlobalModelData M Q Z γ M₀
  d : EUniData M Q Z B M₀ ψ φ Γ p₀ U₀
  hz : z ∈ Z
  hz1 : z ≠ 1
  nf : ∀ y : G, IsConj z y → y ∈ M → y ∉ Q → ∀ w ∈ Z, w ≠ 1 → ¬ IsConj y (y * w)
  fe2 : ∀ y : G, IsConj z y → y ∈ M → y ∉ Q →
    ∃ s : Lgen M (LB M Q B), (s : G) * y⁻¹ ∈ Q ∧ IsRt (φ s)
  mrf : MinRootFacts Γ p₀ IsRt
  caseII : ∀ x : G, IsConj z x → x ∈ M → x ∉ Q → ∀ r, Acts φ x r → IsRt r → CaseII Q Z x

section Basic

variable [Finite G] {M Q Z B : Subgroup G} {K : Type} [Field K]
  [Finite K] [CharP K 2] {γ : G → K} {M₀ : Tim79.QuadModel Q Z K γ} {V : Type} [AddCommGroup V]
  [Module K V] {ψ : M₀.E ≃ₗ[K] V} {φ : Lgen M (LB M Q B) →* (V ≃ₗ[K] V)}
  {Γ : Subgroup (V ≃ₗ[K] V)} {p₀ : V} {U₀ : Subgroup (V ≃ₗ[K] V)}
  {IsRt : (V ≃ₗ[K] V) → Prop} {z : G}

theorem phi_eq_of_mul_mem_Q_gen (d : EUniData M Q Z B M₀ ψ φ Γ p₀ U₀) {x : G}
    {s : Lgen M (LB M Q B)} (hsx : (s : G) * x⁻¹ ∈ Q) :
    ∃ hxL : x ∈ Lgen M (LB M Q B), φ ⟨x, hxL⟩ = φ s := by
  have hxs : x * (s : G)⁻¹ ∈ Q := by
    have := Q.inv_mem hsx
    simpa [mul_inv_rev] using this
  have hxL : x ∈ Lgen M (LB M Q B) := by
    have h1 : x * (s : G)⁻¹ ∈ Lgen M (LB M Q B) := Q_le_Lgen M Q B hxs
    have h2 := (Lgen M (LB M Q B)).mul_mem h1 s.2
    simpa using h2
  refine ⟨hxL, ?_⟩
  have h : φ (⟨x, hxL⟩ * s⁻¹) = 1 := (d.ker _).mpr (by simpa using hxs)
  rw [map_mul, map_inv, mul_inv_eq_one] at h
  exact h

theorem GDat.acts_root (Dt : GDat M Q Z B K γ M₀ ψ φ Γ p₀ U₀ IsRt z) {y : G} (hyc : IsConj z y)
    (hyM : y ∈ M) (hyQ : y ∉ Q) : ∃ r, Acts φ y r ∧ IsRt r := by
  obtain ⟨s, hsq, hs⟩ := Dt.fe2 y hyc hyM hyQ
  obtain ⟨hyL, hφy⟩ := phi_eq_of_mul_mem_Q_gen Dt.d hsq
  exact ⟨φ s, ⟨hyL, hφy⟩, hs⟩

end Basic

end CFSG.RankThree.GF2n.Smith81.RootGen
