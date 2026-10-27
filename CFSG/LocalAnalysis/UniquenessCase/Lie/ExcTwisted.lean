module

public import CFSG.LocalAnalysis.UniquenessCase.UC22P20o
import CFSG.LocalAnalysis.SeitzReduction.TwistedE6PilotModel
import CFSG.LocalAnalysis.UniquenessCase.Lie.ExcE6
import CFSG.LocalAnalysis.UniquenessCase.Lie.ExcShared
import CFSG.Timmesfeld.Orders.ExceptionalTwistedBruhat
import CFSG.LieType.Chevalley.C2E6StandardFixedData
import CFSG.LieType.Chevalley.C2E6UnitaryFourImages

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.LieType.Chevalley CFSG.Blueprint.Chevalley CFSG.Timmesfeld.ExceptionalOrders Subgroup
open CFSG.Blueprint (LieModel)

section Torus


theorem uc22pwex_twisted_torus {t : TwistTag} {K : Type} [Field K] [Finite K] (σ : K →+* K)
    (hσs : Function.Surjective σ) {n : ℕ} (hσ : ∀ c, σ c = c ^ 2 ^ n) {m : ℕ}
    (hK : Nat.card K = (2 ^ n) ^ m) {p : ℕ} (hp : p.Prime) (hpn : p ∣ 2 ^ n - 1)
    (hker : ∀ c : Fin t.tag.rank → Kˣ, (∀ i, c i ^ p = 1) → torusCoordHom t.tag K c = 1 → c = 1) :
    ∃ F : Subgroup ↥(graphFixedRootGroup t K σ),
      F ≤ normalizer (((graphFixedPosUnipotent t K σ).subgroupOf (graphFixedRootGroup t K σ) :
        Subgroup ↥(graphFixedRootGroup t K σ)) : Set ↥(graphFixedRootGroup t K σ)) ∧
      IsElemAbelian p F ∧ Nat.card F = p ^ t.foldedTag.rank := by
  have hpK : p ∣ Nat.card K - 1 := by
    rw [hK]
    exact hpn.trans (Nat.sub_one_dvd_pow_sub_one (2 ^ n) m)
  obtain ⟨μ, hμc, hμp⟩ := uc22pwex_exists_mu hp hpK
  have hfix : ∀ x : μ, σ ((x : Kˣ) : K) = ((x : Kˣ) : K) := by
    intro x
    obtain ⟨k, hk⟩ := hpn
    have h1 : (((x : Kˣ) : K)) ^ p = 1 := by
      rw [← Units.val_pow_eq_pow_val, hμp x, Units.val_one]
    have h2n : 1 ≤ 2 ^ n := Nat.one_le_two_pow
    rw [hσ, show 2 ^ n = p * k + 1 by omega, pow_succ, pow_mul, h1, one_pow, one_mul]
  let ι : (Fin t.foldedTag.rank → μ) →* (Fin t.tag.rank → Kˣ) :=
    Pi.monoidHom fun i => μ.subtype.comp (Pi.evalMonoidHom (fun _ => μ) (t.orbitIndex i))
  have hι : ∀ s, ι s ∈ compatSubgroup σ := by
    intro s
    rw [mem_compatSubgroup]
    intro i
    show ((s (t.orbitIndex (t.perm i)) : μ) : Kˣ) =
      Units.map σ.toMonoidHom ((s (t.orbitIndex i) : μ) : Kˣ)
    rw [t.orbitIndex_perm]
    exact Units.ext (hfix _).symm
  let Φ0 : (Fin t.foldedTag.rank → μ) →* ModGL t.tag K :=
    (torusGroup t.tag K).subtype.comp ((torusCoordHom t.tag K).comp ι)
  have hmem : ∀ s, Φ0 s ∈ graphFixedRootTorus t K σ := by
    intro s
    rw [graphFixedRootTorus_eq_compatTorus hσs]
    exact (mem_compatTorus σ).2 ⟨ι s, hι s, rfl⟩
  let Φ : (Fin t.foldedTag.rank → μ) →* ↥(graphFixedRootGroup t K σ) :=
    Φ0.codRestrict (graphFixedRootGroup t K σ) fun s => graphFixedRootTorus_le t K σ (hmem s)
  have hinj : Function.Injective Φ := by
    rw [injective_iff_map_eq_one]
    intro s hs
    have h1 : torusCoordHom t.tag K (ι s) = 1 := by
      have := congrArg (fun x : ↥(graphFixedRootGroup t K σ) => (x : ModGL t.tag K)) hs
      exact Subtype.ext this
    have h2 := hker (ι s) (fun i => hμp (s (t.orbitIndex i))) h1
    funext a
    obtain ⟨i, rfl⟩ := t.exists_orbitIndex_eq a
    exact Subtype.ext (congrFun h2 i)
  have hA : Nat.card (Fin t.foldedTag.rank → μ) = p ^ t.foldedTag.rank := by
    rw [Nat.card_pi]
    simp [hμc]
  obtain ⟨hE, hc⟩ := uc22pwex_elemAbelian_range Φ hinj (fun a b => mul_comm a b)
    (fun a => funext fun i => Subtype.ext (hμp (a i))) hA
  refine ⟨Φ.range, ?_, hE, hc⟩
  rintro _ ⟨s, rfl⟩
  refine uc22pwex_mem_normalizer_subgroupOf ?_
  exact graphFixedRootTorus_le_normalizer_graphFixedPosUnipotent (hmem s)

end Torus

section D4Kernel


theorem uc22pwex_d4_torusCoordHom_ker {K : Type} [Field K] {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {t : Fin Tag.D4.rank → Kˣ} (ht : ∀ i, t i ^ p = 1) (h : torusCoordHom Tag.D4 K t = 1) :
    t = 1 :=
  uc22pwex_torusCoordHom_ker_pTorsion (τ := Tag.D4)
    (B := (!![2, 1, 2, 1; 1, 2, 2, 1; 2, 2, 4, 2; 1, 1, 2, 2] :
      Matrix (Fin Tag.D4.rank) (Fin Tag.D4.rank) ℤ)) (m := 2) (by decide +kernel)
    ((Nat.coprime_primes Nat.prime_two hp).2 (Ne.symm hp2)) ht h

end D4Kernel

section Witness


theorem uc22pwex_twE6_borelWit {G : Type} [Group G] [Finite G] {n : ℕ}
    (hG : LieModel G .twistedE6 0 2 n) {p : ℕ} (hp : p.Prime) (hpn : p ∣ 2 ^ n - 1) (hp3 : p ≠ 3) :
    uc22p20oBorelWit G p 4 := by
  obtain ⟨-, K, _, _, σ, hK, hσ, ⟨e⟩⟩ :=
    CFSG.SeitzReduction.TwistedE6Pilot.exists_mulEquiv_graphFixedRootGroup_of_lieModel hG
  haveI : CharP K 2 := uc22pwex_charP_two (m := n * 2) (by rw [hK, ← pow_mul])
  have hσs : Function.Surjective σ := Finite.surjective_of_injective σ.injective
  obtain ⟨F, hN, hE, hc⟩ := uc22pwex_twisted_torus (t := .E6) σ hσs hσ (m := 2) hK hp hpn
    (fun c hc h => uc22pwex_e6_torusCoordHom_ker hp hp3 hc h)
  exact uc22pwex_borelWit_of_equiv e _
    (isPGroup_graphFixedPosUnipotent_subgroupOf 2 (t := .E6) (K := K) (σ := σ))
    (not_dvd_index_graphFixedPosUnipotent 2 hσs) F hN hE hc

theorem uc22pwex_d4_borelWit {G : Type} [Group G] [Finite G] {n : ℕ}
    (hG : LieModel G .trialityD4 0 2 n) {p : ℕ} (hp : p.Prime) (hpn : p ∣ 2 ^ n - 1) :
    uc22p20oBorelWit G p 2 := by
  have hn1 : 1 ≤ n := by
    obtain ⟨⟨-, hn1, -⟩, -⟩ := hG.chevalleyExceptionalModel (by decide)
    exact hn1
  have hp2 : p ≠ 2 := by
    rintro rfl
    have h2 : 2 ∣ 2 ^ n := dvd_pow_self 2 (by omega)
    have h3 : 1 ≤ 2 ^ n := Nat.one_le_two_pow
    omega
  obtain ⟨K, _, _, σ, hK, hσ, ⟨e⟩⟩ :=
    CFSG.RankThree.PartTwo.Sec4.exists_mulEquiv_graphFixedRootGroup_D4
      (hG.chevalleyExceptionalModel (by decide))
  haveI : CharP K 2 := uc22pwex_charP_two (m := n * 3) (by rw [hK, ← pow_mul])
  have hσs : Function.Surjective σ := Finite.surjective_of_injective σ.injective
  obtain ⟨F, hN, hE, hc⟩ :=
    uc22pwex_twisted_torus (t := .D4) σ.toRingHom hσs hσ (m := 3) hK hp hpn
      (fun c hc h => uc22pwex_d4_torusCoordHom_ker hp hp2 hc h)
  exact uc22pwex_borelWit_of_equiv e _
    (isPGroup_graphFixedPosUnipotent_subgroupOf 2 (t := .D4) (K := K) (σ := σ.toRingHom))
    (not_dvd_index_graphFixedPosUnipotent 2 hσs) F hN hE hc

end Witness

end CFSG.LocalAnalysis.UniquenessCase.UC22
