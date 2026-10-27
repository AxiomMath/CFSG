module

public import CFSG.LocalAnalysis.StandardType.GGF4QGeFourOrb
public import CFSG.LocalAnalysis.StandardType.GGF4Rk2Core
public import CFSG.LocalAnalysis.StandardType.GGF4QGeFourRk1
import Mathlib.Tactic.Group

public noncomputable section

namespace CFSG.StandardType

open CFSG.Open CFSG.Assembly CFSG.LieType.Universal CFSG.LieType.RootSystem

theorem exists_f4_pair_rootLevi_transport
    {U : Type} [Group U] (D : UniversalRootDatum U)
    {G : Type} [Group G] [Finite G] {p : ℕ} {Bs X : Subgroup G}
    (hp : p.Prime) (hp2 : p ≠ 2) (hEl : IsElemAbelian p Bs) (hNT : GGNoTransvection p Bs)
    {A : Subgroup (MulAut ↥Bs)} (hAind : A ≤ ggInduced ⊤ Bs)
    {e : CoxeterMatrix.F₄.Group ≃* ↥A} (hpres : GGCoxeterPres p A CoxeterMatrix.F₄ e)
    (hXA : ggAutomizer X Bs ≤ A) (ψ : U →* G)
    (ε : (coxeterMatrix D.isFiniteType).Group ≃* ↥(ggAutomizer X Bs))
    (hεrefl : ∀ k, GGIsReflection p (ε ((coxeterMatrix D.isFiniteType).simple k) : MulAut ↥Bs))
    (hεlevi : ∀ w k,
      ggRankOneIn X Bs (ε (w * (coxeterMatrix D.isFiniteType).simple k * w⁻¹) : MulAut ↥Bs) =
        (ggRootLevi D (weylAction D.isFiniteType w (Pi.single k 1))).map ψ)
    (σ : Fin 3 ≃ Fin D.rank)
    (hM : ∀ k l, (coxeterMatrix D.isFiniteType) (σ k) (σ l) = CoxeterMatrix.B 3 k l)
    (ν : (coxeterMatrix D.isFiniteType).Group →* U) (hν : GGWeylLift D ν)
    (w : CoxeterMatrix.F₄.Group) (i j : Fin 4) (hij : i ≠ j)
    (hi : ((e (w * CoxeterMatrix.F₄.simple i * w⁻¹) : ↥A) : MulAut ↥Bs) ∈ ggAutomizer X Bs)
    (hj : ((e (w * CoxeterMatrix.F₄.simple j * w⁻¹) : ↥A) : MulAut ↥Bs) ∈ ggAutomizer X Bs) :
    ∃ (u : (coxeterMatrix D.isFiniteType).Group) (c d : Fin 3),
      ggRankOneIn X Bs ((e (w * CoxeterMatrix.F₄.simple i * w⁻¹) : ↥A) : MulAut ↥Bs) =
        (ggRootLevi D (Pi.single (σ c) 1)).map
          ((MulAut.conj (ψ (ν u))).toMonoidHom.comp ψ) ∧
      ggRankOneIn X Bs ((e (w * CoxeterMatrix.F₄.simple j * w⁻¹) : ↥A) : MulAut ↥Bs) =
        (ggRootLevi D (Pi.single (σ d) 1)).map
          ((MulAut.conj (ψ (ν u))).toMonoidHom.comp ψ) ∧
      (CoxeterMatrix.F₄ i j = 2 → c = 0 ∧ d = 2 ∨ c = 2 ∧ d = 0) ∧
      (CoxeterMatrix.F₄ i j = 3 → c = 0 ∧ d = 1) ∧
      (CoxeterMatrix.F₄ i j = 4 → c = 2 ∧ d = 1 ∨ c = 1 ∧ d = 2) := by
  obtain ⟨φ, hφe, ha, ha01, ha12, ha02, haX⟩ :=
    exists_f4Triple_map_of_weyl hp hp2 hEl hNT hAind hpres hXA ε hεrefl σ hM
  let a : Fin 3 → CoxeterMatrix.F₄.Group := fun k => φ ((coxeterMatrix D.isFiniteType).simple (σ k))
  obtain ⟨R, hRs⟩ := F4Model.exists_f4Rep CoxeterMatrix.F₄.toCoxeterSystem
  have hsimp : ∀ k, R.s k = CoxeterMatrix.F₄.simple k := by
    intro k
    rw [hRs k, CoxeterMatrix.toCoxeterSystem_simple]
  have hord : orderOf (R.s i * R.s j) = CoxeterMatrix.F₄ i j := by
    rw [hsimp, hsimp]
    simpa [CoxeterMatrix.toCoxeterSystem_simple] using
      CoxeterMatrix.F₄.toCoxeterSystem.orderOf_simple_mul_simple i j
  have hi' : w * R.s i * w⁻¹ ∈ Subgroup.closure (Set.range a) := by
    rw [hsimp]
    exact (haX _).mpr hi
  have hj' : w * R.s j * w⁻¹ ∈ Subgroup.closure (Set.range a) := by
    rw [hsimp]
    exact (haX _).mpr hj
  obtain ⟨v, c, d, hvc, hvd, h2, h3, h4⟩ :=
    R.pair_core (fun k => (F4Model.F4Rep.isRefl_iff hRs).2 (ha k)) ha01 ha12 ha02 hij hord hi' hj'
  let u : (coxeterMatrix D.isFiniteType).Group :=
    (v.map fun k : Fin 3 => (coxeterMatrix D.isFiniteType).simple (σ k)).prod
  have hvu : (v.map a).prod = φ u := by
    rw [show u = _ from rfl, map_list_prod, List.map_map]
    rfl
  let θ : U →* G := (MulAut.conj (ψ (ν u))).toMonoidHom.comp ψ
  have hS : ∀ (n : Fin 4) (b : Fin 3),
      w * R.s n * w⁻¹ = φ u * φ ((coxeterMatrix D.isFiniteType).simple (σ b)) * (φ u)⁻¹ →
      ggRankOneIn X Bs ((e (w * CoxeterMatrix.F₄.simple n * w⁻¹) : ↥A) : MulAut ↥Bs) =
        (ggRootLevi D (Pi.single (σ b) 1)).map θ := by
    intro n b hn
    have he : ((e (w * CoxeterMatrix.F₄.simple n * w⁻¹) : ↥A) : MulAut ↥Bs) =
        (ε (u * (coxeterMatrix D.isFiniteType).simple (σ b) * u⁻¹) : MulAut ↥Bs) := by
      rw [← hsimp n, hn, ← map_inv φ, ← map_mul φ, ← map_mul φ]
      exact hφe _
    rw [he, hεlevi u (σ b), ggRootLevi_map_conj_weylLift' D ν hν ψ u (σ b), Subgroup.map_map]
  exact ⟨u, c, d, hS i c (by rw [hvc, hvu]), hS j d (by rw [hvd, hvu]), h2, h3, h4⟩

end CFSG.StandardType
