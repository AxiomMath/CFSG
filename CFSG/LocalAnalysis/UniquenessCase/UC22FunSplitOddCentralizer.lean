module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.FundamentalOverModel
public import CFSG.ClassicalInvolution.ModelFacts.FundCentralizerNormalizer
public import CFSG.ClassicalInvolution.AschTight.HypOmegaGenCover
public import CFSG.GroupTheory.OddOrderLift
public import CFSG.ClassicalInvolution.Asc77.AscE189Comp
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.FunHypOmega

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open Subgroup CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Asc77
open CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719
open CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17
open scoped commutatorElement


theorem mem_normalizer_of_fundamental_involution_of_odd
    {X : Type} [Group X] [Finite X] {p e : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    (hL2 : ¬ IsL2Over17 (X ⧸ center X) (p ^ e))
    {K : Subgroup X} (hK : IsFundamentalOver (p ^ e) K)
    {z : X} (hz : IsUniqueInvolution K z) {g : X}
    (hgodd : Odd (orderOf g)) (hgz : g * z = z * g) :
    g ∈ normalizer (K : Set X) := by
  obtain ⟨t, n, hfund, hadm, _, ψ, hψ, hker, R, hR, hRker, hKR⟩ :=
    exists_model_of_isFundamentalOver hp2 rfl hL2 hK
  have : Finite (modelUniv t n p e Fact.out).K :=
    CFSG.ClassicalInvolution.ModelFacts.finite_modelUniv hp2 Fact.out hfund hadm
  obtain ⟨z₀, hz₀⟩ :=
    CFSG.ClassicalInvolution.ModelFacts.exists_isUniqueInvolution_of_mem_fundamentalSubgroups
      hp2 hfund hadm hR
  have hinj : ∀ x ∈ R, ψ x = 1 → x = 1 := fun x hx h1 =>
    Subgroup.mem_bot.mp (hRker ▸ ⟨hx, h1⟩)
  have hzmap : IsUniqueInvolution (R.map ψ) (ψ z₀) :=
    isUniqueInvolution_map_of_injOn ψ hinj hz₀
  have hzeq : ψ z₀ = z := hzmap.eq (hKR ▸ hz)
  obtain ⟨g₀, hg₀, hgo⟩ := CFSG.GroupTheory.exists_odd_orderOf_preimage ψ hψ hgodd
  have hc : ⁅z₀, g₀⁆ ∈ center (modelUniv t n p e Fact.out).K := by
    apply hker
    rw [MonoidHom.mem_ker, commutatorElement_def, map_mul, map_mul, map_mul, map_inv,
      map_inv, hzeq, hg₀]
    rw [← hgz]
    group
  have hsq : Commute z₀ (g₀ * g₀) :=
    CFSG.ClassicalInvolution.commute_mul_self_of_commutator_mem_center hz₀.sq hc
  have hgp : g₀ ∈ zpowers (g₀ ^ 2) := by
    rw [mem_zpowers_pow_iff]
    exact Nat.coprime_iff_gcd_eq_one.mp ((Nat.coprime_two_right.mpr hgo).symm)
  have hgcen : g₀ ∈ centralizer ({z₀} : Set (modelUniv t n p e Fact.out).K) :=
    (Subgroup.zpowers_le.mpr (Subgroup.mem_centralizer_singleton_iff.mpr
      (by simpa [pow_two] using hsq.symm.eq))) hgp
  have hgN : g₀ ∈ normalizer (R : Set (modelUniv t n p e Fact.out).K) :=
    CFSG.ClassicalInvolution.ModelFacts.centralizer_le_normalizer_of_mem_fundamentalSubgroups
      hp2 hfund hadm hR hz₀ hgcen
  rw [hKR, ← hg₀]
  exact Subgroup.le_normalizer_map ψ (Subgroup.mem_map.mpr ⟨g₀, hgN, rfl⟩)

end CFSG.LocalAnalysis.UniquenessCase.UC22
