module

public import CFSG.LocalAnalysis.StandardType.GGTorusGenSLPSL
public import CFSG.LocalAnalysis.StandardType.GGCoverSLTransfer
public import CFSG.LocalAnalysis.StandardType.GGCoverSLModel
public import CFSG.LocalAnalysis.StandardType.GGCoverSLSemilin
public import CFSG.LocalAnalysis.StandardType.GGCoverSLDiag

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly TableB Matrix CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.LinearFlag

theorem ggCoverPTableB_PSL
    {d p : ℕ} {K : Type} [Field K] [Finite K] [CharP K 2] (hp : p.Prime)
    (hpK : p ∣ Nat.card K - 1) (hd : 4 ≤ d) :
    GGCoverPTableB p (projectiveSL d K) (Set.range (conjAut d K)) := by
  intro M _ _ L' E θ hE hpos a ha
  classical
  have hsec : TypeA.SLHasSections d K := slHasSections_of_four_le hp hpK hd
  have hL : GGTorusLift p (d - 2) (projectiveSL d K) :=
    TypeA.ggTorusLift_sub_two (d := d) hp hpK (by omega) hsec
  have hr : p ^ (d - 2) ≤ Nat.card (ggGamma L' hE).range :=
    TableBBridge.pow_le_card_range_of_torusLift (L' := L') (E := E) hpos hp hL
  obtain ⟨φ, hφs, hφk, hdiag⟩ := exists_model_of_position_PSL_gamma hp hpK hd hpos hr
  have hp2 : p ≠ 2 := LinUnitL.prime_ne_two_of_dvd_card_sub_one (K := K) hpK
  obtain ⟨g, σ, m, hσ, hact⟩ := exists_semilin_through_model_SL (by omega) hp hp2 hφs hφk ha
  obtain ⟨ρ, hρ⟩ := exists_rho_commute_diag_SL hp (by omega) hφs hφk hσ hact
  refine ⟨ρ, fun e => ?_⟩
  obtain ⟨t, ht⟩ := hdiag e
  have hep : ggLAut L' θ ⟨e, hE e.2⟩ ^ p = 1 := by
    rw [← map_pow]
    have hnorm : (⟨e, hE e.2⟩ : Subgroup.normalizer (L' : Set M)) ^ p = 1 :=
      Subtype.ext (by simpa using hpos.2.1.2 e e.2)
    rw [hnorm, map_one]
  exact hρ _ hep ⟨t, ht⟩

theorem largeEvenLabelAll_coverP_typeA
    {p : ℕ} (hp : p.Prime) {lab : LargeEvenLabel} (hlab : LargeEvenInLambda2 lab)
    (htag : lab.tag = .A) (hl : 3 ≤ lab.rank) (hpn : p ∣ 2 ^ lab.n - 1) :
    LargeEvenLabelAll lab fun R _ I _ => GGCoverPTableB p R I := by
  obtain ⟨t, l, n⟩ := lab
  dsimp only at htag hl hpn ⊢
  subst htag
  intro Q hQ
  dsimp only [LargeEvenRawDatum] at hQ ⊢
  obtain ⟨K, hfield, hfinite, hK, hQ'⟩ := hQ
  refine ⟨K, hfield, hfinite, hK, hQ', ?_⟩
  haveI : Fintype K := Fintype.ofFinite K
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : CharP K 2 :=
    charP_of_card_eq_prime_pow (R := K) (p := 2) (f := n)
      (by rw [← Nat.card_eq_fintype_card]; exact hK)
  have hd : 4 ≤ l + 1 := by omega
  have hpK : p ∣ Nat.card K - 1 := by rw [hK]; exact hpn
  refine ggCoverPTableB_of_mulEquiv (R' := projectiveSL (l + 1) K)
    (I' := Set.range (conjAut (l + 1) K)) (TypeA.recipeEquiv (l + 1) K) ?_ ?_
  · intro φ hφ
    exact TypeA.congr_recipeEquiv_mem hφ
  · exact ggCoverPTableB_PSL (K := K) hp hpK hd

end CFSG.StandardType
