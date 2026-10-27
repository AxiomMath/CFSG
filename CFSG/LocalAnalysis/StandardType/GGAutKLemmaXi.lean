module

public import CFSG.LocalAnalysis.StandardType.GGSixAutKFlatKGDefs
public import CFSG.LocalAnalysis.StandardType.GGSummandStructQuotBot
public import CFSG.LocalAnalysis.StandardType.GGSixAutKFlatSeventeen
public import CFSG.SignalizerFunctorTheorem.McBride.Prelim.Generation
public import CFSG.SignalizerFunctorTheorem.McBride.Prelim.Basic
public import CFSG.SignalizerFunctorTheorem.Nonsolvable.SolComponent

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.RootSystem
  CFSG.Assembly.LowTwoRank CFSG.RankThree.PartTwo.Sec21

section LemmaXi

variable {G : Type} [Group G]

theorem normalizer_zpowers_eq_centralizer {r : G} (hr : orderOf r = 2) :
    Subgroup.normalizer (Subgroup.zpowers r : Set G) = Subgroup.centralizer {r} := by
  have hr1 : r ≠ 1 := fun h => by simp [h] at hr
  ext g
  rw [Subgroup.mem_centralizer_singleton_iff]
  constructor
  · intro hg
    have h1 : g * r * g⁻¹ ∈ Subgroup.zpowers r :=
      (Subgroup.mem_normalizer_iff.mp hg r).mp (Subgroup.mem_zpowers r)
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp h1
    have hne : g * r * g⁻¹ ≠ 1 := fun h => hr1 (by
      have : r = g⁻¹ * (g * r * g⁻¹) * g := by group
      rw [this, h]; group)
    have hk2 : r ^ k = r ^ (k % 2) := by
      have := zpow_mod_orderOf r k
      rw [hr] at this
      simpa using this.symm
    rcases Int.emod_two_eq_zero_or_one k with h0 | h0
    · exfalso
      apply hne
      rw [← hk, hk2, h0]; simp
    · have hk' : g * r * g⁻¹ = r := by rw [← hk, hk2, h0]; simp
      calc g * r = g * r * g⁻¹ * g := by group
        _ = r * g := by rw [hk']
  · intro hg n
    have hc : Commute g r := hg
    have key : ∀ c : G, Commute c r → ∀ y ∈ Subgroup.zpowers r, c * y * c⁻¹ = y := by
      intro c hc y hy
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
      have h2 : c * r ^ k = r ^ k * c := (hc.zpow_right k).eq
      rw [h2]; group
    constructor
    · intro hn
      rw [key g hc n hn]; exact hn
    · intro hn
      have h3 := key g⁻¹ hc.inv_left _ hn
      have h4 : g⁻¹ * (g * n * g⁻¹) * g⁻¹⁻¹ = n := by group
      rw [h4] at h3
      rw [h3]; exact hn

theorem ggFalse_of_Xi [Finite G] {p : ℕ} {M E₀ : Subgroup G}
    (hchar : IsCharTwoType G) (hp : p.Prime) (hp2 : p ≠ 2)
    (hfus : GGControlsStrongFusion M E₀) (hE : IsElemAbelian p E₀)
    (hE2 : p ^ 2 ≤ Nat.card E₀) {b : G} (hXi : GGOTwoXi M E₀ b) : False := by
  obtain ⟨r, hr, -, -, hrE, hOr, hnot⟩ := hXi
  have hr1 : r ≠ 1 := fun h => by simp [h] at hr
  have hrp : IsPGroup 2 (Subgroup.zpowers r) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hr]; rfl)
  set X : Subgroup G := Subgroup.centralizer {r} with hX
  have hX2 : IsTwoLocal X :=
    ⟨Subgroup.zpowers r, fun h => hr1 (Subgroup.zpowers_eq_bot.mp h), hrp,
      (normalizer_zpowers_eq_centralizer hr).symm⟩
  have hXQ := hchar X hX2
  set Q : Subgroup G := pCoreOf 2 X with hQ
  have hQX : Q ≤ X := pCoreOf_le' 2 X
  have hQp : IsPGroup 2 Q := isPGroup_pCoreOf' 2 X
  have hE0X : E₀ ≤ X := fun e he =>
    Subgroup.mem_centralizer_singleton_iff.mpr (hrE e he)
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hcop : Nat.Coprime p (Nat.card Q) := by
    obtain ⟨k, hk⟩ := hQp.exists_card_eq
    rw [hk]
    exact Nat.Coprime.pow_right _ ((Nat.coprime_primes hp Nat.prime_two).mpr hp2)
  have hnorm : E₀ ≤ Subgroup.normalizer (Q : Set G) := by
    intro e he
    rw [Subgroup.mem_normalizer_iff]
    intro q
    constructor
    · intro hq
      exact conj_mem_pCoreOf' 2 (hE0X he) hq
    · intro hq
      have h := conj_mem_pCoreOf' 2 (X.inv_mem (hE0X he)) hq
      rwa [show e⁻¹ * (e * q * e⁻¹) * e⁻¹⁻¹ = q from by group] at h
  have hgen := CFSG.SignalizerFunctorTheorem.McBride.iSup_centralizer_nonidentity hp hE hE2 hnorm
    hcop
  have hQM : Q ≤ M ⊓ X := by
    refine le_trans (le_of_eq hgen.symm) (iSup_le fun a => iSup_le fun ha => iSup_le fun ha1 => ?_)
    intro y hy
    obtain ⟨hyQ, hyC⟩ := Subgroup.mem_inf.mp hy
    exact Subgroup.mem_inf.mpr ⟨hfus.centralizer_le ha ha1 hyC, hQX hyQ⟩
  have hQle : Q ≤ pCoreOf 2 (M ⊓ X) :=
    le_pCoreOf_of_normalized 2 hQM hQp fun h hh q hq =>
      conj_mem_pCoreOf' 2 (Subgroup.mem_inf.mp hh).2 hq
  have hQr : Q ≤ Subgroup.zpowers r := hQle.trans hOr
  have hXC : X ≤ Subgroup.centralizer (Q : Set G) := by
    intro x hx q hq
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp (hQr hq)
    have hc : Commute x r := Subgroup.mem_centralizer_singleton_iff.mp hx
    exact ((hc.zpow_right k).eq).symm
  have hXle : X ≤ Q := fun x hx => hXQ (Subgroup.mem_inf.mpr ⟨hx, hXC hx⟩)
  exact hnot (hrp.to_le ((inf_le_right.trans hXle).trans hQr))

end LemmaXi

end CFSG.StandardType
