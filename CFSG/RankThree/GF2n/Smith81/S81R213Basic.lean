module

public import CFSG.RankThree.GF2n.Smith81.S81RRoot
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge

public section

namespace CFSG.RankThree.GF2n.Smith81.E3LRoot

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
  CFSG.RankThree.GF2n CFSG.RankThree.GF2n.Stroth80 CFSG.RankThree.GF2n.Smith81.EGeom
  CFSG.RankThree.GF2n.Smith81.A5Cube CFSG.RankThree.GF2n.Smith81.E3LBridge
  CFSG.RankThree.GF2n.Smith81.E3LCond CFSG.RankThree.GF2n.Smith81
open scoped commutatorElement

variable {G : Type} [Group G]

structure E3LDat (M Q Z B : Subgroup G) (K : Type) [Field K] (γ : G → K)
    (M₀ : Tim79.QuadModel Q Z K γ) (ψ : M₀.E ≃ₗ[K] Cube K)
    (φ : Lgen M (LB M Q B) →* (Cube K ≃ₗ[K] Cube K)) (z : G) : Prop where
  ctx : Ctx M Q Z B
  hD : GlobalModelData M Q Z γ M₀
  d : EUniData M Q Z B M₀ ψ φ (Gam K) (p0 K) (U0 K)
  hz : z ∈ Z
  hz1 : z ≠ 1
  nf : ∀ y : G, IsConj z y → y ∈ M → y ∉ Q → ∀ w ∈ Z, w ≠ 1 → ¬ IsConj y (y * w)
  fe2 : ∀ y : G, IsConj z y → y ∈ M → y ∉ Q →
    ∃ s : Lgen M (LB M Q B), (s : G) * y⁻¹ ∈ Q ∧ ∃ g : GL (Fin 6) K, IsTransvec K g ∧
      φ s = rhoEquiv K g

section Basic

variable [Finite G] {M Q Z B : Subgroup G} {K : Type} [Field K]
  [Finite K] [CharP K 2] {γ : G → K} {M₀ : Tim79.QuadModel Q Z K γ} {ψ : M₀.E ≃ₗ[K] Cube K}
  {φ : Lgen M (LB M Q B) →* (Cube K ≃ₗ[K] Cube K)} {z : G}

theorem inZClass_of_isConj {z c : G} (hz : z ∈ Z) (hz1 : z ≠ 1) (h : IsConj z c) :
    InZClass Z c := by
  obtain ⟨g, hg⟩ := isConj_iff.mp h
  exact ⟨g, z, hz, hz1, hg.symm⟩

theorem isConj_of_inZClass {M Q Z : Subgroup G} (H : StrothHyp M Q Z) {z c : G} (hz : z ∈ Z)
    (hz1 : z ≠ 1) (h : InZClass Z c) : IsConj z c := by
  obtain ⟨g, u, hu, hu1, e⟩ := h
  obtain ⟨m, -, hm⟩ := Z_isConj H hz hz1 hu hu1
  exact isConj_iff.mpr ⟨g * m, by rw [e, ← hm]; group⟩

def ActsAs (φ : Lgen M (LB M Q B) →* (Cube K ≃ₗ[K] Cube K)) (x : G) (g : GL (Fin 6) K) : Prop :=
  ∃ hxL : x ∈ Lgen M (LB M Q B), φ ⟨x, hxL⟩ = rhoEquiv K g

theorem ActsAs.mul {x y : G} {g h : GL (Fin 6) K} (hx : ActsAs φ x g) (hy : ActsAs φ y h) :
    ActsAs φ (x * y) (g * h) := by
  obtain ⟨hxL, hx⟩ := hx
  obtain ⟨hyL, hy⟩ := hy
  refine ⟨(Lgen M (LB M Q B)).mul_mem hxL hyL, ?_⟩
  have : (⟨x * y, (Lgen M (LB M Q B)).mul_mem hxL hyL⟩ : Lgen M (LB M Q B)) =
      ⟨x, hxL⟩ * ⟨y, hyL⟩ := rfl
  rw [this, map_mul, hx, hy, map_mul]

theorem ActsAs.inv {x : G} {g : GL (Fin 6) K} (hx : ActsAs φ x g) : ActsAs φ x⁻¹ g⁻¹ := by
  obtain ⟨hxL, hx⟩ := hx
  refine ⟨(Lgen M (LB M Q B)).inv_mem hxL, ?_⟩
  have : (⟨x⁻¹, (Lgen M (LB M Q B)).inv_mem hxL⟩ : Lgen M (LB M Q B)) = (⟨x, hxL⟩)⁻¹ := rfl
  rw [this, map_inv, hx, map_inv]

theorem ActsAs.one : ActsAs φ (1 : G) (1 : GL (Fin 6) K) :=
  ⟨(Lgen M (LB M Q B)).one_mem, by
    have : (⟨1, (Lgen M (LB M Q B)).one_mem⟩ : Lgen M (LB M Q B)) = 1 := rfl
    rw [this, map_one, map_one]⟩

theorem ActsAs.conj {x y : G} {g h : GL (Fin 6) K} (hx : ActsAs φ x g) (hy : ActsAs φ y h) :
    ActsAs φ (y * x * y⁻¹) (h * g * h⁻¹) := (hy.mul hx).mul hy.inv

theorem ActsAs.mem_Lgen {x : G} {g : GL (Fin 6) K} (hx : ActsAs φ x g) :
    x ∈ Lgen M (LB M Q B) := by
  obtain ⟨h, -⟩ := hx
  exact h

theorem ActsAs.phi {x : G} {g : GL (Fin 6) K} (hx : ActsAs φ x g)
    (hxL : x ∈ Lgen M (LB M Q B)) : φ ⟨x, hxL⟩ = rhoEquiv K g := by
  obtain ⟨_, h⟩ := hx
  exact h

theorem E3LDat.actsAs (Dt : E3LDat M Q Z B K γ M₀ ψ φ z) {y : G} (hyc : IsConj z y) (hyM : y ∈ M)
    (hyQ : y ∉ Q) : ∃ g : GL (Fin 6) K, IsTransvec K g ∧ ActsAs φ y g := by
  obtain ⟨s, hsq, g, hg, hφs⟩ := Dt.fe2 y hyc hyM hyQ
  obtain ⟨hyL, hφy⟩ := phi_eq_of_mul_mem_Q (x := y) Dt.d hsq
  exact ⟨g, hg, hyL, by rw [hφy, hφs]⟩

end Basic

end CFSG.RankThree.GF2n.Smith81.E3LRoot
