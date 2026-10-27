module

public import CFSG.LocalAnalysis.UniquenessCase.UCFront07
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC6CommAux1
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Fourteen4Aux
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.ShapeDisjoint
public import CFSG.LocalAnalysis.PreuniquenessRankFour.Helpers
public import CFSG.LocalAnalysis.UniquenessCase.UCFront09
public import CFSG.Quasithin.Background.B6Sections
import CFSG.Adapters.LieModelSimple

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {G : Type} [Group G] [Finite G]

theorem derInf_isPerfect (P : Subgroup G) : ⁅F07.DerInf P, F07.DerInf P⁆ = F07.DerInf P := by
  change ⁅(CFSG.perfectResidual ↥P).map P.subtype, (CFSG.perfectResidual ↥P).map P.subtype⁆ =
    (CFSG.perfectResidual ↥P).map P.subtype
  exact Subgroup.isPerfect_iff.mp
    (CFSG.SignalizerFunctorTheorem.Nonsolvable.isPerfect_perfectResidual_map P)

theorem opp3_eq_self_of_isL2 {X : Subgroup G} {m : ℕ} (hperf : ⁅X, X⁆ = X)
    (hL2 : IsL2 (Bar2 X) m) : Opp 3 X = X := by
  haveI hsimple : IsSimpleGroup (Bar2 X) :=
    CFSG.Blueprint.LieModel.isSimpleGroup_of_mem_classicalTags (by decide) hL2
  exact s16c6_opp3_eq_self hperf hsimple (three_dvd_card_of_isL2 hL2)

theorem exists_card_eq_three_of_isL2 {X : Subgroup G} {m : ℕ} (hL2 : IsL2 (Bar2 X) m) :
    ∃ D₃ : Subgroup G, D₃ ≤ X ∧ Nat.card D₃ = 3 := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have h3bar : 3 ∣ Nat.card (Bar2 X) := three_dvd_card_of_isL2 hL2
  have h3X : 3 ∣ Nat.card ↥X :=
    h3bar.trans (Subgroup.card_quotient_dvd_card (CFSG.pCore 2 ↥X))
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := ↥X) 3 h3X
  refine ⟨(Subgroup.zpowers x).map X.subtype, Subgroup.map_subtype_le (Subgroup.zpowers x), ?_⟩
  rw [Subgroup.card_map_of_injective X.subtype_injective, Nat.card_zpowers, hx]

theorem eq_of_normal_of_isL2 {X B D₃ : Subgroup G} {m : ℕ} (hperf : ⁅X, X⁆ = X)
    (hL2 : IsL2 (Bar2 X) m) (hBX : B ≤ X) (hXB : X ≤ normalizer (B : Set G)) (hD₃B : D₃ ≤ B)
    (hD₃ : Nat.card D₃ = 3) : B = X := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI hXperf : Group.IsPerfect ↥X := Subgroup.isPerfect_iff.mpr hperf
  haveI h2core : IsPGroup 2 ↥(CFSG.pCore 2 ↥X) := CFSG.pCore_isPGroup
  haveI hsimple : IsSimpleGroup (Bar2 X) :=
    CFSG.Blueprint.LieModel.isSimpleGroup_of_mem_classicalTags (by decide) hL2
  haveI hBn : (B.subgroupOf X).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hBX).mpr hXB
  let π : ↥X →* Bar2 X := QuotientGroup.mk' (CFSG.pCore 2 ↥X)
  have hmap_ne : (B.subgroupOf X).map π ≠ ⊥ := by
    obtain ⟨d, hd⟩ := exists_prime_orderOf_dvd_card' (G := ↥D₃) 3 (by rw [hD₃])
    let x' : ↥X := ⟨(d : G), hBX (hD₃B d.2)⟩
    have hx'3 : orderOf x' = 3 := by
      rw [← Subgroup.orderOf_coe (a := x')]
      have hdG : orderOf (d : G) = 3 := by rw [Subgroup.orderOf_coe]; exact hd
      exact hdG
    have hxne : π x' ≠ 1 := by
      intro h1
      have hxker : x' ∈ π.ker := (MonoidHom.mem_ker).mpr h1
      rw [show π.ker = CFSG.pCore 2 ↥X from QuotientGroup.ker_mk' _] at hxker
      have h3dvd : 3 ∣ Nat.card (CFSG.pCore 2 ↥X) := by
        have h := Subgroup.orderOf_dvd_natCard (CFSG.pCore 2 ↥X) hxker
        rwa [hx'3] at h
      obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp (CFSG.pCore_isPGroup (p := 2) (G := ↥X))
      rw [hk] at h3dvd
      exact (by norm_num : ¬ (3 : ℕ) ∣ 2) (Nat.prime_three.dvd_of_dvd_pow h3dvd)
    intro hbot
    have hmem : π x' ∈ (B.subgroupOf X).map π :=
      Subgroup.mem_map_of_mem π (Subgroup.mem_subgroupOf.mpr (hD₃B d.2))
    rw [hbot, Subgroup.mem_bot] at hmem
    exact hxne hmem
  have hmap_top : (B.subgroupOf X).map π = ⊤ := by
    haveI : ((B.subgroupOf X).map π).Normal := hBn.map π (QuotientGroup.mk'_surjective _)
    exact (Subgroup.Normal.eq_bot_or_eq_top _).resolve_left hmap_ne
  have htop : (B.subgroupOf X) ⊔ (CFSG.pCore 2 ↥X) = ⊤ := by
    have h := Subgroup.comap_map_eq π (B.subgroupOf X)
    rw [hmap_top, Subgroup.comap_top, QuotientGroup.ker_mk'] at h
    exact h.symm
  have hBtop : B.subgroupOf X = ⊤ := by
    haveI hsub : Subsingleton (↥X ⧸ B.subgroupOf X) := by
      haveI : Group.IsPerfect (↥X ⧸ B.subgroupOf X) := Group.IsPerfect.instQuotientSubgroup
      have h2group : IsPGroup 2 (↥X ⧸ B.subgroupOf X) := by
        let f : ↥(CFSG.pCore 2 ↥X) →* (↥X ⧸ B.subgroupOf X) :=
          (QuotientGroup.mk' (B.subgroupOf X)).comp (CFSG.pCore 2 ↥X).subtype
        have hf : Function.Surjective f := by
          intro z
          obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective (B.subgroupOf X) z
          have hx : x ∈ (B.subgroupOf X) ⊔ (CFSG.pCore 2 ↥X) := by
            rw [htop]; exact Subgroup.mem_top x
          obtain ⟨y, hy, o, ho, hxy⟩ := (Subgroup.mem_sup_of_normal_left.mp hx)
          refine ⟨⟨o, ho⟩, ?_⟩
          show QuotientGroup.mk' (B.subgroupOf X) (o : ↥X) =
            QuotientGroup.mk' (B.subgroupOf X) x
          have hy1 : (QuotientGroup.mk' (B.subgroupOf X)) y = 1 :=
            (QuotientGroup.eq_one_iff (N := B.subgroupOf X) y).mpr hy
          rw [← hxy, map_mul, hy1, one_mul]
        exact h2core.of_surjective f hf
      exact s16c6_subsingleton_of_isPerfect_of_isPGroup h2group inferInstance
    rw [Subgroup.eq_top_iff']
    intro z
    rw [← QuotientGroup.eq_one_iff (N := B.subgroupOf X) z]
    exact Subsingleton.elim _ _
  rw [← Subgroup.map_subgroupOf_eq_of_le (H := B) (K := X) hBX, hBtop, Subgroup.map_top,
    Subgroup.range_subtype]

theorem ne_top_of_hyp97 (D : Data G) {Y H D₃ S : Subgroup G} (hyp : F09.Hyp97 D Y H D₃ S) :
    H ≠ ⊤ := by
  haveI := D.standing.simple
  obtain ⟨⟨-, ⟨-, hHM, -⟩, -, -⟩, -, ⟨-, hF⟩, -⟩ := hyp
  have hHne : H ≠ ⊥ := fun h => hHM (h ▸ bot_le)
  obtain ⟨N, hN, hHN⟩ := PartTwo.exists_isMaxTwoLocal_ge_of_fstar (G := G) hF hHne
  intro hHtop
  exact CFSG.PreuniquenessRankFour.Helpers.twoLocal_ne_top D.standing.nonab hN.1
    (top_le_iff.mp (hHtop ▸ hHN))

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
