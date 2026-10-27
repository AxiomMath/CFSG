module

public import CFSG.LocalAnalysis.StandardType.GGOrthWeakFrame
public import CFSG.LocalAnalysis.StandardType.GGOrthFrameTransport
public import CFSG.LocalAnalysis.StandardType.GGOrthFrameModel
public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyAut
import CFSG.LocalAnalysis.StandardType.GGOrthRk1FieldTwo
public import CFSG.LocalAnalysis.StandardType.GGSecFiveRankOneConj

public section

open Module Multiplicative QuadraticMap

namespace CFSG.StandardType

namespace OrthTorus

open CFSG.RankThree.Classical2 (orthDerived)
open SpCoord NbrOrth

structure OrthFrameCore (p : ℕ) {G : Type} [Group G] (Bs X : Subgroup G) where
  F : Type
  [instField : Field F]
  [instFinite : Finite F]
  [instChar : CharP F 2]
  V : Type
  [instAdd : AddCommGroup V]
  [instMod : Module F V]
  [instFD : FiniteDimensional F V]
  Q : QuadraticForm F V
  A : Subgroup (V ≃ₗ[F] V)
  r : ℕ
  Δ : TBJOmData Q p A r
  ψ : ↥(orthDerived Q) →* G
  β : ↥Bs →* ↥(orthDerived Q)
  hA : A ≤ orthDerived Q
  hr : 4 ≤ r
  hpq : p ∣ Nat.card F + 1
  hfix : ∀ v : V, (∀ a ∈ A, a v = v) → v = 0
  hinj : Function.Injective ψ
  hrange : ψ.range = X
  hβA : ∀ b : ↥Bs, (β b : V ≃ₗ[F] V) ∈ A
  hβsurj : ∀ a ∈ A, ∃ b : ↥Bs, (β b : V ≃ₗ[F] V) = a
  hcompat : ∀ (b : ↥Bs) (y : ↥(orthDerived Q)),
    ψ (β b * y * (β b)⁻¹) = (b : G) * ψ y * (b : G)⁻¹
  swapReal : ∀ i j : Fin r, i ≠ j → ∃ w : ↥(orthDerived Q),
    (∀ f' : Fin r → Multiplicative (ZMod p),
      (w : V ≃ₗ[F] V) * Δ.τ f' * (w : V ≃ₗ[F] V)⁻¹ = Δ.τ (permAut (Equiv.swap i j) f')) ∧
    ψ w ∈ Subgroup.normalizer (Bs : Set G)
  dinvReal : ∀ i j : Fin r, i ≠ j → ∃ w : ↥(orthDerived Q),
    (∀ f' : Fin r → Multiplicative (ZMod p),
      (w : V ≃ₗ[F] V) * Δ.τ f' * (w : V ≃ₗ[F] V)⁻¹ = Δ.τ (dinv i j f')) ∧
    ψ w ∈ Subgroup.normalizer (Bs : Set G)

attribute [instance] OrthFrameCore.instField OrthFrameCore.instFinite OrthFrameCore.instChar
  OrthFrameCore.instAdd OrthFrameCore.instMod OrthFrameCore.instFD

@[expose] def OrthFrameCore.toWeakFrame {p : ℕ} {G : Type} [Group G] {Bs X : Subgroup G}
    (Φ : OrthFrameCore p Bs X) (f : ℕ) (hcard : Nat.card Φ.F = 2 ^ f) (hf : 2 ≤ f) :
    OrthWeakFrame p Bs X where
  F := Φ.F
  V := Φ.V
  Q := Φ.Q
  A := Φ.A
  r := Φ.r
  Δ := Φ.Δ
  ψ := Φ.ψ
  β := Φ.β
  f := f
  hA := Φ.hA
  hr := Φ.hr
  hcard := hcard
  hf := hf
  hpq := Φ.hpq
  hfix := Φ.hfix
  hinj := Φ.hinj
  hrange := Φ.hrange
  hβA := Φ.hβA
  hβsurj := Φ.hβsurj
  hcompat := Φ.hcompat
  swapReal := Φ.swapReal
  dinvReal := Φ.dinvReal

theorem OrthFrameCore.finite_linearEquiv {p : ℕ} {G : Type} [Group G] {Bs X : Subgroup G}
    (Φ : OrthFrameCore p Bs X) : Finite (Φ.V ≃ₗ[Φ.F] Φ.V) := by
  haveI : Finite Φ.V := Module.finite_of_finite Φ.F
  exact Finite.of_injective (fun e : Φ.V ≃ₗ[Φ.F] Φ.V => (e : Φ.V → Φ.V)) DFunLike.coe_injective

theorem OrthFrameCore.exists_swap_refl {p : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G]
    {Bs X : Subgroup G} (Φ : OrthFrameCore p Bs X) {i j : Fin Φ.r} (hij : i ≠ j) :
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

theorem OrthFrameCore.exists_refl_card_six {p : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G]
    {Bs X : Subgroup G} (Φ : OrthFrameCore p Bs X) (hK : Nat.card Φ.F = 2) :
    ∃ a ∈ ggAutomizer X Bs, GGIsReflection p a ∧ Nat.card ↥(ggRankOneIn X Bs a) = 6 := by
  have hp3 : p = 3 := by
    have h := Φ.hpq
    rw [hK] at h
    exact (Nat.prime_dvd_prime_iff_eq (Fact.out : p.Prime) Nat.prime_three).mp h
  have hr := Φ.hr
  let i : Fin Φ.r := ⟨0, by omega⟩
  let j : Fin Φ.r := ⟨1, by omega⟩
  have hij : i ≠ j := fun h => absurd (congrArg Fin.val h) (by simp [i, j])
  obtain ⟨a, ha, hrefl, heq⟩ := Φ.exists_swap_refl hij
  refine ⟨a, ha, hrefl, ?_⟩
  have hle : Φ.Δ.rankOne i j ≤ orthDerived Φ.Q := (ggOTwoPrime_le _).trans inf_le_right
  rw [heq, Subgroup.card_map_of_injective Φ.hinj,
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv]
  exact Φ.Δ.card_rankOne_of_card_two (by omega) Φ.hA Φ.hfix hK hij

end OrthTorus

end CFSG.StandardType

end
