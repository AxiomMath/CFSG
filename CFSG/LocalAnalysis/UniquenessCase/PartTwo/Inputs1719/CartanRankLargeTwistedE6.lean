module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.CartanCoverTools
public import CFSG.LocalAnalysis.UniquenessCase.Lie.FoldedTorus
public import CFSG.LocalAnalysis.SeitzReduction.TwistedE6PilotModel
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.StatementsC
public import CFSG.RankThree.CentralCover.SteinbergBNReflectionNormalizers

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719

open CFSG.Open
open CFSG.Blueprint (LieModel)
open CFSG.Blueprint.Chevalley
open CFSG.LieType.Chevalley
open CFSG.RankThree.CentralCover
open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.QuasithinUnique (IsSylowTwoOf)
open TauCeti.Subgroup (normalizerQuotient)

theorem twistedE6_exists_fixed_prime_order {L : Type} [Field L] [Finite L] {f r : ℕ}
    (hr : r.Prime) (hrdvd : r ∣ 2 ^ f - 1) (hK : Nat.card L = (2 ^ f) ^ 2)
    (σ : L →+* L) (hσ : ∀ c, σ c = c ^ 2 ^ f) :
    ∃ ζ : Lˣ, orderOf ζ = r ∧ ζ ^ r = 1 ∧ Units.map σ.toMonoidHom ζ = ζ := by
  haveI : Fact r.Prime := ⟨hr⟩
  have hdvdUnits : r ∣ Nat.card Lˣ := by
    rw [Nat.card_units, hK]
    exact hrdvd.trans (Nat.sub_one_dvd_pow_sub_one (2 ^ f) 2)
  obtain ⟨ζ, hζo⟩ := exists_prime_orderOf_dvd_card' r hdvdUnits
  have hζ : ζ ^ r = 1 := by
    rw [← hζo]
    exact pow_orderOf_eq_one ζ
  have hσζ : Units.map σ.toMonoidHom ζ = ζ := by
    apply Units.ext
    rw [Units.coe_map]
    change σ ((ζ : L)) = ((ζ : L))
    rw [hσ, ← Units.val_pow_eq_pow_val]
    congr 1
    obtain ⟨k, hk⟩ := hrdvd
    have h2 : 2 ^ f = r * k + 1 := by
      have hpos : 0 < 2 ^ f := pow_pos (by norm_num) f
      omega
    rw [h2, pow_add, pow_mul, hζ, one_pow, one_mul, pow_one]
  exact ⟨ζ, hζo, hζ, hσζ⟩

section Certificates


theorem cartanRankLarge_twistedE6_of_model {K : Type} [Group K] [Finite K] {f : ℕ}
    {L : Type} [Field L] [Finite L] (σ : L →+* L) (hσ : ∀ c, σ c = c ^ 2 ^ f)
    (hK : Nat.card L = (2 ^ f) ^ 2)
    (e₀ : (K ⧸ Subgroup.center K) ≃* graphFixedRootGroup TwistTag.E6 L σ)
    (hq : 2 < 2 ^ f)
    (S : Subgroup K) (hS : IsSylowTwoOf S ⊤) :
    ∃ r : ℕ, r.Prime ∧ r ≠ 2 ∧ r ∣ 2 ^ f - 1 ∧
      3 < CFSG.Open.pRank r (⊤ : Subgroup (normalizerQuotient S)) := by
  classical
  haveI : CharP L 2 := uc22pwex_charP_two (m := f * 2) (by rw [hK, ← pow_mul])
  have hσs : Function.Surjective σ := Finite.surjective_of_injective σ.injective
  let φ : K →* ↥(graphFixedRootGroup TwistTag.E6 L σ) :=
    e₀.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center K))
  have hφ : Function.Surjective φ :=
    e₀.surjective.comp (QuotientGroup.mk'_surjective (Subgroup.center K))
  have hker_eq : φ.ker = Subgroup.center K := by
    rw [MonoidHom.ker_comp_of_injective _ _ e₀.injective, QuotientGroup.ker_mk']
  have hker : φ.ker ≤ Subgroup.center K := le_of_eq hker_eq
  have hf2 : 2 ≤ f := by
    by_contra hf
    interval_cases f <;> norm_num at hq
  obtain ⟨r, hr, hr2, -, hrdvd⟩ :=
    CFSG.RankThree.PartOne.KFU.exists_odd_prime_dvd_two_pow_sub_one_ne_five hf2
  haveI : NeZero r := ⟨hr.ne_zero⟩
  obtain ⟨ζ, hζo, hζ, hσζ⟩ := twistedE6_exists_fixed_prime_order hr hrdvd hK σ hσ
  let D : Subgroup ↥(graphFixedRootGroup TwistTag.E6 L σ) :=
    (foldedTorusHom TwistTag.E6 σ ζ hζ hσζ).range
  have hinj : Function.Injective (foldedTorusHom TwistTag.E6 σ ζ hζ hσζ) :=
    foldedTorusHom_injective TwistTag.E6 σ hζo hζ hσζ
      (fun s hs h => e6_foldedTorus_kernel hs h)
  have hDr : ∀ x ∈ D, x ^ r = 1 := by
    rintro _ ⟨v, rfl⟩
    rw [← map_pow, pow_eq_one_of_zmod, map_one]
  obtain ⟨hDab, hDcard⟩ := uc22pwex_elemAbelian_range (foldedTorusHom TwistTag.E6 σ ζ hζ hσζ)
    hinj (fun a b => mul_comm a b) (fun a => pow_eq_one_of_zmod a)
    (card_multiplicative_fin_zmod 4)
  have hDU : D ≤ Subgroup.normalizer (((graphFixedPosUnipotent TwistTag.E6 L σ).subgroupOf
      (graphFixedRootGroup TwistTag.E6 L σ) : Subgroup ↥(graphFixedRootGroup TwistTag.E6 L σ)) :
        Set ↥(graphFixedRootGroup TwistTag.E6 L σ)) :=
    foldedTorusHom_range_le_normalizer TwistTag.E6 σ ζ hζ hσζ
  have hDc : ∀ x ∈ D.comap φ, ∀ y ∈ D.comap φ, x * y = y * x :=
    reflection_comap_comm hφ hker hr hr2 (foldedTorusHom TwistTag.E6 σ ζ hζ hσζ)
      (e6FoldedFunctional r) (e6FoldedFunctional_single r)
      (fun a => ⟨orbitN TwistTag.E6 L σ a 1,
        orbitN_mem_graphFixedRootGroup (t := TwistTag.E6) σ a 1⟩)
      (fun a v => e6_foldedTorusWeyl_conj hζ hσζ a v)
  let U : Subgroup ↥(graphFixedRootGroup TwistTag.E6 L σ) :=
    (graphFixedPosUnipotent TwistTag.E6 L σ).subgroupOf (graphFixedRootGroup TwistTag.E6 L σ)
  have hU : IsSylowTwoOf U ⊤ := by
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    refine ⟨le_top, isPGroup_graphFixedPosUnipotent_subgroupOf 2, ?_⟩
    rw [CFSG.QuasithinUnique.index_subgroupOf_top]
    exact not_dvd_index_graphFixedPosUnipotent 2 hσs
  have h := le_pRank_normalizerQuotient_of_comap_comm hφ hker hr hr2 hDr hDc
    (k := 4) (by rw [hDcard]) hU hDU S hS
  exact ⟨r, hr, hr2, hrdvd, by omega⟩

theorem k_CartanRankLarge_twistedE6 :
    ∀ (K : Type) [Group K] [Finite K] (f : ℕ),
      CFSG.Open.StatedLieAdmissible .twistedE6 0 2 f → 2 < 2 ^ f →
      CFSG.Blueprint.LieModel (K ⧸ Subgroup.center K) .twistedE6 0 2 f →
      CFSG.Open.IsQuasisimple K → Odd (Nat.card (Subgroup.center K)) →
      ∀ S : Subgroup K, CFSG.QuasithinUnique.IsSylowTwoOf S ⊤ →
        4 ≤ CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17.CS17LieRank .twistedE6 0 →
          ∃ r : ℕ, r.Prime ∧ r ≠ 2 ∧ r ∣ 2 ^ f - 1 ∧
            3 < CFSG.Open.pRank r (⊤ : Subgroup (TauCeti.Subgroup.normalizerQuotient S)) := by
  intro K _ _ f _ hq hL _ _ S hS _
  obtain ⟨-, L, hFld, hFin, σ, hK, hσ, ⟨e₀⟩⟩ :=
    CFSG.SeitzReduction.TwistedE6Pilot.exists_mulEquiv_graphFixedRootGroup_of_lieModel hL
  letI := hFld
  letI := hFin
  exact cartanRankLarge_twistedE6_of_model σ hσ hK e₀ hq S hS

end Certificates

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719
