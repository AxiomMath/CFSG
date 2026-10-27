module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightS1Star
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightS1OmegaCScal
public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenThreeS
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.TwelveShort
public import CFSG.LocalAnalysis.UniquenessCase.UC22DataExt

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {G : Type} [Group G] [Finite G]

theorem s16e_omc_centralizer_embeds_units_mBar (D : Data G) (hx : DataExt D)
    (h4 : 3 < CFSG.Open.evenRank G) (h61 : UC6.R6_1 D) (h127 : R127 D) (h1217 : R1217 D)
    {V₀ V L : Subgroup G} (hV : IsElemAbelian 2 V) (hset : Setting16 D V₀ V L)
    (hL : barSub V₀ V hV L ≠ ⊥) (hconc : Conc4_136 D V₀ V hV L)
    (h : Case162_7 D V₀ V hV L) :
    ∃ (K : Type) (_ : Field K) (_ : Finite K), Nat.card K = 4 ∧
      ∃ f : ↥(Subgroup.centralizer
          ((lBar V₀ V hV L).subgroupOf (Mbar D.M V₀ V hV) : Set ↥(Mbar D.M V₀ V hV))) →*
          Kˣ, Function.Injective f := by
  obtain ⟨ρ, -, hρL⟩ := s16e_star_equiv D h1217 hset.hyp151 hV
  have hW := s15_Three_wStar_eq_top D h1217 hset.hyp151 hV hL h.2.2
  have hnat : NatOmegaPlus (lStar D.M V₀ V hV L) (⊤ : Subgroup (vStar D.M V₀ V hV L)) ⊥ 4 2 := by
    rw [← hW]
    exact h.2.1
  obtain ⟨K, hKf, hKfin, hK4, f, hf⟩ := s16e_omc_centralizer_embeds_units hnat
  refine ⟨K, hKf, hKfin, hK4, ?_⟩
  have hleS : lStar D.M V₀ V hV L ≤ Mbar D.M (v1Sub D.M V₀ V hV L) V hV :=
    barSub_mono _ V hV hset.hyp151.le
  let φ : ↥(Subgroup.centralizer
        ((lBar V₀ V hV L).subgroupOf (Mbar D.M V₀ V hV) : Set ↥(Mbar D.M V₀ V hV))) →*
      ↥(Subgroup.centralizer (lStar D.M V₀ V hV L : Set (MulAut (vStar D.M V₀ V hV L)))) :=
    MonoidHom.codRestrict
      ((Mbar D.M (v1Sub D.M V₀ V hV L) V hV).subtype.comp
        (ρ.toMonoidHom.comp (Subgroup.centralizer
          ((lBar V₀ V hV L).subgroupOf (Mbar D.M V₀ V hV) :
            Set ↥(Mbar D.M V₀ V hV))).subtype)) _ (by
      intro c
      rw [Subgroup.mem_centralizer_iff]
      intro l hl
      have hmem : (⟨l, hleS hl⟩ : ↥(Mbar D.M (v1Sub D.M V₀ V hV L) V hV)) ∈
          (lStar D.M V₀ V hV L).subgroupOf (Mbar D.M (v1Sub D.M V₀ V hV L) V hV) :=
        Subgroup.mem_subgroupOf.2 hl
      rw [← hρL] at hmem
      obtain ⟨n, hn, hnl⟩ := Subgroup.mem_map.1 hmem
      have hcomm : n * (c : ↥(Mbar D.M V₀ V hV)) = (c : ↥(Mbar D.M V₀ V hV)) * n :=
        Subgroup.mem_centralizer_iff.1 c.2 n hn
      have h1 : ρ (n * (c : ↥(Mbar D.M V₀ V hV))) = ρ ((c : ↥(Mbar D.M V₀ V hV)) * n) := by
        rw [hcomm]
      rw [map_mul, map_mul] at h1
      have h2 := congrArg Subtype.val h1
      have hnl' : ((ρ n : ↥(Mbar D.M (v1Sub D.M V₀ V hV L) V hV)) :
          MulAut (vStar D.M V₀ V hV L)) = l := congrArg Subtype.val hnl
      rw [Subgroup.coe_mul, Subgroup.coe_mul, hnl'] at h2
      exact h2)
  have hφ : Function.Injective φ := by
    intro c c' hcc'
    have h1 := congrArg Subtype.val hcc'
    exact Subtype.ext (ρ.injective (Subtype.ext h1))
  exact ⟨f.comp φ, hf.comp hφ⟩

theorem s16e_omc_nilpotent_equiv_zmod_three {C : Type} [Group C] [Finite C] [Nontrivial C]
    {K : Type} [Field K] [Finite K] (hK : Nat.card K = 4) (f : C →* Kˣ)
    (hf : Function.Injective f) :
    Group.IsNilpotent C ∧ Nonempty (C ≃* Multiplicative (ZMod 3)) := by
  classical
  haveI := Fintype.ofFinite K
  have hunits : Nat.card Kˣ = 3 := by
    rw [Nat.card_eq_fintype_card, Fintype.card_units, ← Nat.card_eq_fintype_card, hK]
  have hdvd : Nat.card C ∣ 3 := hunits ▸ Subgroup.card_dvd_of_injective f hf
  have hne : Nat.card C ≠ 1 := by
    intro h
    have := (Nat.card_eq_one_iff_unique.1 h).1
    exact not_subsingleton C this
  have h3 : Nat.card C = 3 := by
    rcases (Nat.dvd_prime Nat.prime_three).1 hdvd with h | h
    · exact absurd h hne
    · exact h
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hcard' : Nat.card (Multiplicative (ZMod 3)) = 3 := by
    simp [Nat.card_eq_fintype_card]
  have e : C ≃* Multiplicative (ZMod 3) := mulEquivOfPrimeCardEq h3 hcard'
  refine ⟨?_, ⟨e⟩⟩
  have hp : IsPGroup 3 C := IsPGroup.of_card (n := 1) (by simpa using h3)
  exact hp.isNilpotent

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
