module

public import CFSG.RankThree.PartOne.FTL.Scalar
public import CFSG.RankThree.PartOne.FTL.Frattini
public import CFSG.RankThree.PartOne.S9.Sylow.GlobalEndgame

public section

namespace CFSG.RankThree.PartOne.FTL

open Subgroup CFSG CFSG.Assembly CFSG.Assembly.RankThreeEven CFSG.RankThree
  CFSG.RankThree.LocalRank CFSG.RankThree.GroupTheory CFSG.RankThree.PartOne.Sec9B
open scoped commutatorElement

theorem active_core_centralized (hTwo : TwoActionInputs) {G : Type} [Group G] [Finite G]
    {p q : ℕ} (hp : p.Prime) (hp3 : 3 < p) (he : evenRank G = 3) (hsig : p ∈ sigmaA G)
    (hq : q.Prime) (hq2 : q ≠ 2) (hqp : q ≠ p) {A R E M : Subgroup G} {d : G}
    (hAe : IsElementaryAbelian p A) (hAcard : Nat.card A = p ^ 3)
    (hAR : A ≤ normalizer (R : Set G)) (hR2 : IsPGroup 2 R) (hRA : ⁅R, A⁆ = R) (hR1 : R ≠ ⊥)
    (hBcard : Nat.card ↥(A ⊓ Subgroup.centralizer (R : Set G)) = p ^ 2)
    (hminR : ∀ U : Subgroup G, U < R → A ≤ normalizer (U : Set G) → ⁅U, A⁆ = U → U = ⊥)
    (hdB : d ∈ A ⊓ Subgroup.centralizer (R : Set G))
    (hEq : CFSG.IsQuasisimple ↥E) (hdE : d ∈ E) (hdnc : ∃ e ∈ E, d * e ≠ e * d)
    (hMq : IsPGroup q M) (hM1 : M ≠ ⊥) (hRM : R ≤ normalizer (M : Set G))
    (hAM : A ≤ normalizer (M : Set G)) (hEM : E ≤ normalizer (M : Set G))
    (hRMne : ⁅R, M⁆ ≠ ⊥) : E ≤ Subgroup.centralizer (M : Set G) := by
  have : Fact q.Prime := ⟨hq⟩
  obtain ⟨X, hXM, hX1, hXnorm, hXexp, hXcomm, hXdet⟩ := exists_critical hq hq2 hMq hM1
  have hXq : IsPGroup q X := hMq.to_le hXM
  have hRX' : R ≤ normalizer (X : Set G) := fun r hr => hXnorm r (hRM hr)
  have hAX : A ≤ normalizer (X : Set G) := fun a ha => hXnorm a (hAM ha)
  have hEX : E ≤ normalizer (X : Set G) := fun e he => hXnorm e (hEM he)
  have hRAX : R ⊔ A ≤ normalizer (X : Set G) := sup_le hRX' hAX
  have hXX : ⁅⁅X, X⁆, X⁆ = ⊥ := by
    rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
    exact (Subgroup.commutator_mono le_rfl hXM).trans (hXcomm.trans inf_le_right)
  have hRX : ⁅R, X⁆ ≠ ⊥ := by
    intro hRX0
    apply hRMne
    rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
    intro r hr
    have hrC := Subgroup.commutator_eq_bot_iff_le_centralizer.mp hRX0 hr
    have hfix : ∀ x ∈ X, r * x * r⁻¹ = x := fun x hx => by
      have h' := Subgroup.mem_centralizer_iff.mp hrC x hx
      calc r * x * r⁻¹ = x * r * r⁻¹ := by rw [← h']
        _ = x := by group
    refine Subgroup.mem_centralizer_iff.mpr fun m hm => ?_
    have := hXdet r (hRM hr) hfix
      (coprime_orderOf_of_isPGroup Nat.prime_two hq (Ne.symm hq2) hR2 hr) m hm
    calc m * r = (r * m * r⁻¹) * r := by rw [this]
      _ = r * m := by group
  have hmin : ∀ U : Subgroup G, U < R → A ≤ normalizer (U : Set G) → ⁅U, A⁆ = U →
      ⁅U, X⁆ = ⊥ := fun U hU hAU hUA => by
    rw [hminR U hU hAU hUA, Subgroup.commutator_bot_left]
  have hrank : ∀ r ∈ R, r ≠ 1 → CFSG.pRank q ↥(X ⊓ Subgroup.centralizer ({r} : Set G)) ≤ 3 :=
    fun r hr hr1 =>
      pRank_le_three_of_le_centralizer_of_two_element he.le hq hq2 hR2 hr hr1 inf_le_right
  have hscalar := scalar_of_minimal_two_action hTwo hp hp3 he hsig hq hq2 hqp hAe hAcard hAR hR2
    hRA hR1 hRAX hXq hXexp hXX hRX hBcard hmin hrank d hdB
  have hdp : d ^ p = 1 := by
    have : IsElementaryAbelian p A := hAe
    exact elemPow_eq_one_of_isElementaryAbelian (p := p) d hdB.1
  have hdX := centralizes_of_scalar_action hp hq hqp hEq hdE hdnc hEX hXq hdp hscalar
  have hdM : d ∈ Subgroup.centralizer (M : Set G) := by
    refine Subgroup.mem_centralizer_iff.mpr fun m hm => ?_
    have hcop : Nat.Coprime (orderOf d) q :=
      Nat.Coprime.coprime_dvd_left (orderOf_dvd_of_pow_eq_one hdp)
        ((Nat.coprime_primes hp hq).mpr (Ne.symm hqp))
    have := hXdet d (hAM hdB.1) hdX hcop m hm
    calc m * d = (d * m * d⁻¹) * d := by rw [this]
      _ = d * m := by group
  exact le_centralizer_of_mem_centralizer hEq hdE hdnc hEM hdM

end CFSG.RankThree.PartOne.FTL
