module

public import CFSG.LocalAnalysis.StandardType.GGOrthWeakFrame
public import CFSG.LocalAnalysis.StandardType.GGOrthFrameTransport
public import CFSG.LocalAnalysis.StandardType.GGOrthFrameModel
public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyAut
public import CFSG.LocalAnalysis.StandardType.GGSecFiveRankOneConj

public section

open Module Multiplicative QuadraticMap

namespace CFSG.StandardType

namespace OrthTorus

open CFSG.RankThree.Classical2 (orthDerived)
open SpCoord NbrOrth

theorem OrthWeakFrame.finite_linearEquiv {p : ℕ} {G : Type} [Group G] {Bs X : Subgroup G}
    (Φ : OrthWeakFrame p Bs X) : Finite (Φ.V ≃ₗ[Φ.F] Φ.V) := by
  haveI : Finite Φ.V := Module.finite_of_finite Φ.F
  exact Finite.of_injective (fun e : Φ.V ≃ₗ[Φ.F] Φ.V => (e : Φ.V → Φ.V)) DFunLike.coe_injective

theorem OrthWeakFrame.exists_swap_refl {p : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G]
    {Bs X : Subgroup G} (Φ : OrthWeakFrame p Bs X) {i j : Fin Φ.r} (hij : i ≠ j) :
    ∃ a ∈ ggAutomizer X Bs, GGIsReflection p a ∧
      ggRankOneIn X Bs a = ((Φ.Δ.rankOne i j).subgroupOf (orthDerived Φ.Q)).map Φ.ψ := by
  haveI := Φ.finite_linearEquiv
  obtain ⟨w, hw, hn⟩ := Φ.swapReal i j hij
  have hgX : Φ.ψ w ∈ X := by
    have h : Φ.ψ w ∈ Φ.ψ.range := ⟨w, rfl⟩
    rwa [Φ.hrange] at h
  have ha : ∀ b : ↥Bs, ((ggConjAut Bs hn b : ↥Bs) : G) = Φ.ψ w * b * (Φ.ψ w)⁻¹ :=
    fun b => ggConjAut_apply Bs hn b
  refine ⟨ggConjAut Bs hn, ggConjAut_mem_ggAutomizer hgX hn, ?_, ?_⟩
  · exact isReflection_of_inner Φ.ψ Φ.β Φ.hinj Φ.hcompat Φ.hβA Φ.hβsurj
      (Fact.out : p.Prime).one_lt ha (fun t ht => Φ.Δ.swap_sq_comm hw t ht)
      (fun t => Φ.Δ.mem_reflFixed_iff hw t) (Φ.Δ.card_reflFixed hij)
  · have h := ggRankOneIn_eq_map_of_inner Φ.ψ Φ.β Φ.hinj Φ.hcompat Φ.hβA Φ.hβsurj ha
      (fun t => Φ.Δ.mem_reflFixed_iff hw t)
    rw [Φ.hrange] at h
    exact h

theorem OrthWeakFrame.exists_pos_refl {p : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G]
    {Bs X : Subgroup G} (Φ : OrthWeakFrame p Bs X) {i j : Fin Φ.r} (hij : i ≠ j) :
    ∃ a ∈ ggAutomizer X Bs, GGIsReflection p a ∧
      ggRankOneIn X Bs a = ((Φ.Δ.rankOnePos i j).subgroupOf (orthDerived Φ.Q)).map Φ.ψ := by
  haveI := Φ.finite_linearEquiv
  obtain ⟨ws, hws, hns⟩ := Φ.swapReal i j hij
  obtain ⟨wd, hwd, hnd⟩ := Φ.dinvReal i j hij
  have hw : ∀ f : Fin Φ.r → Multiplicative (ZMod p),
      ((wd * ws : ↥(orthDerived Φ.Q)) : Φ.V ≃ₗ[Φ.F] Φ.V) * Φ.Δ.τ f *
        ((wd * ws : ↥(orthDerived Φ.Q)) : Φ.V ≃ₗ[Φ.F] Φ.V)⁻¹ =
        Φ.Δ.τ (dinv i j (permAut (Equiv.swap i j) f)) := by
    intro f
    have h1 := hws f
    have h2 := hwd (permAut (Equiv.swap i j) f)
    rw [← h2, ← h1]
    simp only [Subgroup.coe_mul, mul_inv_rev]
    group
  have hn : Φ.ψ (wd * ws) ∈ Subgroup.normalizer (Bs : Set G) := by
    rw [map_mul]
    exact Subgroup.mul_mem _ hnd hns
  have hgX : Φ.ψ (wd * ws) ∈ X := by
    have h : Φ.ψ (wd * ws) ∈ Φ.ψ.range := ⟨wd * ws, rfl⟩
    rwa [Φ.hrange] at h
  have ha : ∀ b : ↥Bs, ((ggConjAut Bs hn b : ↥Bs) : G) =
      Φ.ψ (wd * ws) * b * (Φ.ψ (wd * ws))⁻¹ := fun b => ggConjAut_apply Bs hn b
  refine ⟨ggConjAut Bs hn, ggConjAut_mem_ggAutomizer hgX hn, ?_, ?_⟩
  · exact isReflection_of_inner Φ.ψ Φ.β Φ.hinj Φ.hcompat Φ.hβA Φ.hβsurj
      (Fact.out : p.Prime).one_lt ha (fun t ht => Φ.Δ.pos_sq_comm hij hw t ht)
      (fun t => Φ.Δ.mem_reflFixedPos_iff hij hw t) (Φ.Δ.card_reflFixedPos hij)
  · have h := ggRankOneIn_eq_map_of_inner Φ.ψ Φ.β Φ.hinj Φ.hcompat Φ.hβA Φ.hβsurj ha
      (fun t => Φ.Δ.mem_reflFixedPos_iff hij hw t)
    rw [Φ.hrange] at h
    exact h

end OrthTorus

end CFSG.StandardType

end
