module

public import CFSG.RankThree.Chevalley.SteinbergCDTrialityTwelveLocalCore
public import CFSG.RankThree.PartOne.S11c.Sec66Exc
public import CFSG.RankThree.PartOne.S11d.FixedFacts
public import CFSG.LieType.Chevalley.OddExceptionalOuterTwoRank
public import CFSG.RankThree.PartOne.K128.FixCenter
public import CFSG.RankThree.PartOne.KF.ClsExcE

public section

namespace CFSG.RankThree.PartOne.TCX.Tri

open Subgroup CFSG CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.RankThree.Chevalley CFSG.RankThree.PartOne CFSG.RankThree.PartOne.Sec66T
  CFSG.RankThree.PartOne.FieldFix CFSG.RankThree.PartOne.K128
open CFSG.Assembly.LowTwoRank (StatedLieTag StatedLieAdmissible)



theorem stdForm_trialityD4
    {T : Type} [Group T] [Finite T] {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) {n f₀ : ℕ}
    (hM : LieModel T .trialityD4 n 2 (p * f₀)) {α : MulAut T} (hαp : α ^ p = 1)
    (hαinn : α ∉ innerAut T) :
    ∃ (K : Type) (_ : Field K) (_ : Finite K) (σ δ₀ : K ≃+* K)
      (φ : T ≃* graphFixedRootGroup TwistTag.D4 K σ.toRingHom),
      Nat.card K = (2 ^ (p * f₀)) ^ 3 ∧ (∀ c, σ c = c ^ 2 ^ (p * f₀)) ∧
        (∀ c, δ₀ c = c ^ 2 ^ (3 * f₀)) ∧ orderOf δ₀ = p ∧
        Subgroup.zpowers (MulAut.congr φ α) = Subgroup.zpowers (fieldActor σ δ₀) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact p.Prime := ⟨hp⟩
  have hadm := statedLieAdmissible_of_lieModel hM
  have hn0 : n = 0 := hadm.2.2
  subst hn0
  have hm1 : 1 ≤ p * f₀ := hadm.2.1
  have hch := chevalleyModel_of_lieModel (by decide) (by decide) (by decide) hM
  obtain ⟨K, hKf, hKfin, σ, hK, hσ, ⟨e⟩⟩ :=
    exists_mulEquiv_graphFixedRootGroup_card .D4 Nat.prime_two hm1 hch.2
  have hK3 : Nat.card K = (2 ^ (p * f₀)) ^ 3 := hK
  obtain ⟨hα'inn, hα'ord⟩ := congr_noninner_prime hp e hαp hαinn
  set α' : MulAut (graphFixedRootGroup TwistTag.D4 K σ.toRingHom) := MulAut.congr e α with hα'
  obtain ⟨-, hcyc, Θ, hΘ, -⟩ := triality_normal_form_data (ℓ := 2) (f := p * f₀) Nat.prime_two hm1 K
    hK3 σ hσ
  obtain ⟨hΘord, -, ⟨h, hh⟩, -⟩ := triality_noninner_large_prime_field_descent_and_local_core_trivial
    (ℓ := 2) (f := p * f₀) Nat.prime_two hm1 K hK3 σ hσ Θ hΘ hp (by omega) ⊤ le_top
    ⟨α', Subgroup.mem_top _⟩ hα'inn (by rw [Subgroup.orderOf_mk]; exact hα'ord)
  set δ := Θ α' with hδ
  have hKf2 : Nat.card K = 2 ^ (p * (3 * f₀)) := by
    rw [hK3, ← pow_mul]
    congr 1
    ring
  obtain ⟨δ₀, hδ₀, hzp⟩ := exists_canonical_generator (f := p * (3 * f₀)) (f' := 3 * f₀)
    (by nlinarith) hKf2 hΘord hp.pos rfl
  have hord₀ : orderOf δ₀ = p := by
    have h1 : Nat.card (Subgroup.zpowers δ) = p := by rw [Nat.card_zpowers, hΘord]
    rw [hzp, Nat.card_zpowers] at h1
    exact h1
  let φ : T ≃* graphFixedRootGroup TwistTag.D4 K σ.toRingHom := e.trans (MulAut.conj h)
  refine ⟨K, hKf, hKfin, σ, δ₀, φ, hK3, hσ, hδ₀, hord₀, ?_⟩
  have h2 : MulAut.congr φ α = MulAut.conj h * α' * (MulAut.conj h)⁻¹ := rfl
  rw [h2, hh]
  have h4 : ∀ ε : K ≃+* K, Subgroup.zpowers (fieldActor σ ε) =
      (Subgroup.zpowers ε).map (fieldActorHom (t := TwistTag.D4) σ) := fun ε =>
    (MonoidHom.map_zpowers (fieldActorHom (t := TwistTag.D4) σ) ε).symm
  rw [h4 δ, h4 δ₀, hzp]

end CFSG.RankThree.PartOne.TCX.Tri
