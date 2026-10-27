module

public import CFSG.LocalAnalysis.UniquenessCase.UC22P20o
import CFSG.LocalAnalysis.SeitzReduction.TwistedE6PilotModel
import CFSG.LocalAnalysis.UniquenessCase.Lie.ExcShared
import CFSG.Timmesfeld.Orders.ExceptionalTorus
import CFSG.Timmesfeld.Orders.ExceptionalTwistedBruhat
import CFSG.LieType.Chevalley.C2E6StandardFixedData
import CFSG.LieType.Chevalley.C2E6UnitaryFourImages

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.LieType.Chevalley CFSG.Blueprint.Chevalley CFSG.Timmesfeld.ExceptionalOrders Subgroup
open CFSG.Blueprint (LieModel)

theorem uc22pwex_prod_zpow_orbitIndex {t : TwistTag} {G : Type*} [CommGroup G]
    (s : Fin t.foldedTag.rank → G) (e : Fin t.tag.rank → ℤ) :
    ∏ i, s (t.orbitIndex i) ^ e i = ∏ a, s a ^ ∑ i with t.orbitIndex i = a, e i := by
  rw [← Finset.prod_fiberwise Finset.univ t.orbitIndex]
  refine Finset.prod_congr rfl fun a _ => ?_
  rw [← prod_zpow_eq_zpow_sum]
  refine Finset.prod_congr rfl fun i hi => ?_
  rw [(Finset.mem_filter.1 hi).2]

section Kernel


theorem uc22pwex_orbit_torusCoordHom_ker {t : TwistTag} {K : Type} [Field K]
    {s : Fin t.foldedTag.rank → Kˣ} (h : torusCoordHom t.tag K (fun i => s (t.orbitIndex i)) = 1) :
    s = 1 := by
  have hrel : ∀ j, ∏ i, s (t.orbitIndex i) ^ t.tag.cartan i j = 1 := fun j =>
    congrFun ((torusCoordHom_eq_one_iff _).1 h) j
  cases t with
  | E6 =>
    refine eq_one_of_prod_zpow_eq_one (t := s)
      (A := fun a j => ∑ i with TwistTag.E6.orbitIndex i = a,
        Tag.E6.cartan i ((![0, 2, 3, 1] : Fin 4 → Fin 6) j))
      (B := !![2, 3, 4, 2; 3, 6, 8, 4; 2, 4, 6, 3; 1, 2, 3, 2]) (by decide +kernel) fun j => ?_
    exact (uc22pwex_prod_zpow_orbitIndex s _).symm.trans (hrel _)
  | D4 =>
    refine eq_one_of_prod_zpow_eq_one (t := s)
      (A := fun a j => ∑ i with TwistTag.D4.orbitIndex i = a,
        Tag.D4.cartan i ((![0, 2] : Fin 2 → Fin 4) j))
      (B := !![2, 3; 1, 2]) (by decide +kernel) fun j => ?_
    exact (uc22pwex_prod_zpow_orbitIndex s _).symm.trans (hrel _)

end Kernel

section Torus


theorem uc22pwex_twisted_torus_orbit {t : TwistTag} {K : Type} [Field K] [Finite K] (σ : K →+* K)
    (hσs : Function.Surjective σ) {n : ℕ} (hσ : ∀ c, σ c = c ^ 2 ^ n) {m : ℕ}
    (hK : Nat.card K = (2 ^ n) ^ m) {p : ℕ} (hp : p.Prime) (hpn : p ∣ 2 ^ n - 1) :
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
    have h2 := uc22pwex_orbit_torusCoordHom_ker (s := fun a => ((s a : μ) : Kˣ)) h1
    funext a
    exact Subtype.ext (congrFun h2 a)
  have hA : Nat.card (Fin t.foldedTag.rank → μ) = p ^ t.foldedTag.rank := by
    rw [Nat.card_pi]
    simp [hμc]
  obtain ⟨hE, hc⟩ := uc22pwex_elemAbelian_range Φ hinj (fun a b => mul_comm a b)
    (fun a => funext fun i => Subtype.ext (hμp (a i))) hA
  refine ⟨Φ.range, ?_, hE, hc⟩
  rintro _ ⟨s, rfl⟩
  refine uc22pwex_mem_normalizer_subgroupOf ?_
  exact graphFixedRootTorus_le_normalizer_graphFixedPosUnipotent (hmem s)

theorem uc22pwex_twE6_borelWit_orbit {G : Type} [Group G] [Finite G] {n : ℕ}
    (hG : LieModel G .twistedE6 0 2 n) {p : ℕ} (hp : p.Prime) (hpn : p ∣ 2 ^ n - 1) :
    uc22p20oBorelWit G p 4 := by
  obtain ⟨-, K, _, _, σ, hK, hσ, ⟨e⟩⟩ :=
    CFSG.SeitzReduction.TwistedE6Pilot.exists_mulEquiv_graphFixedRootGroup_of_lieModel hG
  have : CharP K 2 := uc22pwex_charP_two (m := n * 2) (by rw [hK, ← pow_mul])
  have hσs : Function.Surjective σ := Finite.surjective_of_injective σ.injective
  obtain ⟨F, hN, hE, hc⟩ := uc22pwex_twisted_torus_orbit (t := .E6) σ hσs hσ (m := 2) hK hp hpn
  exact uc22pwex_borelWit_of_equiv e _
    (isPGroup_graphFixedPosUnipotent_subgroupOf 2 (t := .E6) (K := K) (σ := σ))
    (not_dvd_index_graphFixedPosUnipotent 2 hσs) F hN hE hc

end Torus

end CFSG.LocalAnalysis.UniquenessCase.UC22
