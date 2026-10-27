module

public import Certificates.Certificate113
public import Certificates.Certificate114
public import Certificates.Certificate117
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenDefs
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC1677ThreeDefs

import CFSG.LocalAnalysis.UniquenessCase.PartTwo.ExceptionalComponentCover
import CFSG.LocalAnalysis.UniquenessCase.UC22P20p
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC165ExclDirect
import CFSG.Quasithin.H13.A5W1622q
import CFSG.LieType.Steinberg.CentralExt.SL2CentrallyClosed
import CFSG.LocalAnalysis.SectionRank.EvenCover.Symplectic
import CFSG.LocalAnalysis.SectionRank.EvenCover.Orthogonal
import CFSG.LocalAnalysis.SectionRank.EvenCover.Unitary
import CFSG.RankThree.PartTwo.Sec19.Census194.RonanC194SU
import CFSG.RankThree.PartTwo.Sec19.Census194.RonanC194OmegaTorus
import CFSG.RankThree.GF2n.Stroth80.GriessOrthSmall
import CFSG.GroupTheory.WeirSylow.CrossRankForms
import CFSG.ClassicalGroups.Symplectic.ComponentCartanRank
import CFSG.LieType.Universal.SpinOmega.Center
import CFSG.LocalAnalysis.StandardType.GGTableBNbrInnerUnitaryHypCentral
import CFSG.GroupTheory.LocalCores.Components
import CFSG.LocalAnalysis.AGLEmbedding.RankTools
import CFSG.LocalAnalysis.AGLEmbedding.OneSmallGEVNormalThreeDiag
import CFSG.LocalAnalysis.RankThreeCoreUniqueness.Helpers
import CFSG.LocalAnalysis.SectionRank.PRank
import CFSG.LocalAnalysis.SectionRank.SubgroupRank
import CFSG.ClassicalGroups.Unitary.Finite
import CFSG.LocalAnalysis.SectionRank.ClassicalOdd.Basic
import CFSG.RankThree.PartTwo.Sec11.Item116R1Comp
import CFSG.Quasithin.Background.F918V5GComp
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightRowCtx
public import CFSG.LocalAnalysis.UniquenessCase.UC22P21a
public import CFSG.LocalAnalysis.UniquenessCase.UC22P2214a
public import CFSG.LocalAnalysis.UniquenessCase.UC22P2214b
public import CFSG.Quasithin.Background.G10Local
public import CFSG.Sporadic.Schreier.J4SCommGenBase1
import CFSG.ClassicalGroups.Symplectic.DiagonalTorusRank
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSeven3Close16CoverR119
import CFSG.Quasithin.Background.C134L32Corr
import CFSG.Quasithin.H13.A5W1622g
import CFSG.Quasithin.H13.A5W1622i
import CFSG.Quasithin.H13.A5W1622k
import CFSG.Quasithin.H13.A5W1622p
import CFSG.SignalizerFunctorTheorem.NonLocal.Cross
import CFSG.SignalizerFunctorTheorem.NonLocal.SpData

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open scoped commutatorElement Pointwise

private theorem exists_iso_barImage_of_model
    {G : Type} [Group G] [Finite G] {D : Data G} {V₀ V : Subgroup G} {hV : IsElemAbelian 2 V}
    {H : Subgroup (MulAut (Vtil V₀ V hV))} (hHne : H ≠ ⊥)
    {K : Subgroup G} (hK : K ∈ calC D.M) (hbar : barSub V₀ V hV K = H)
    (h125 : Hyp125 D V₀ V)
    {ψ : Bar2 D.M →* MulAut (Vtil V₀ V hV)}
    (hψ : ∀ m : D.M, ψ (QuotientGroup.mk m) =
      actTil V₀ V hV ⟨m, le_stabTil h125.pairFacts.le_normalizer
        h125.pairFacts.le_normalizer₀ m.2⟩)
    {Y : Type} [Group Y] (eH : ↥H ≃* Y)
    (hspl : ∀ (E : Type) [Group E] [Finite E] (π : E →* Y),
      Function.Surjective π → π.ker ≤ Subgroup.center E → Odd (Nat.card π.ker) →
      ∃ σ : Y →* E, ∀ y, π (σ y) = y) :
    Nonempty (↥(UC22.barImage D.M K) ≃* Y) := by
  classical
  let C : Subgroup (Bar2 D.M) := UC22.barImage D.M K
  have hCcomp : CFSG.IsComponent C := UC22.uc22p22l_barImage_isComponent hK
  have hCmap : C.map ψ = H := barImage_map_eq_of_mem_calC h125 hK hbar ψ hψ
  let f : ↥C →* ↥H := (MulEquiv.subgroupCongr hCmap).toMonoidHom.comp (ψ.subgroupMap C)
  have hf : Function.Surjective f :=
    (MulEquiv.subgroupCongr hCmap).surjective.comp (ψ.subgroupMap_surjective C)
  have hHnt : Nontrivial ↥H := (Subgroup.nontrivial_iff_ne_bot H).mpr hHne
  have hkerf : f.ker ≤ Subgroup.center ↥C :=
    CFSG.Quasithin.H13.A5.ker_le_center_of_isQuasisimple hCcomp.1 f hf hHnt
  obtain ⟨eBK⟩ := UC22.uc22p22l_barImage_equiv (L := D.M) hK
  have hoddC : Odd (Nat.card (Subgroup.center ↥C)) := by
    rw [← Nat.card_congr (Subgroup.centerCongr eBK).toEquiv]
    exact UC22.uc22p20p_odd_center_bar2 ↥K
  have hoddKer : Odd (Nat.card f.ker) :=
    Odd.of_dvd_nat hoddC (Subgroup.card_dvd_of_le hkerf)
  let π : ↥C →* Y := eH.toMonoidHom.comp f
  have hπ : Function.Surjective π := eH.surjective.comp hf
  have hkerπ_eq : π.ker = f.ker := by
    rw [show π = eH.toMonoidHom.comp f from rfl,
      MonoidHom.ker_comp_of_injective f eH.toMonoidHom eH.injective]
  have hkerπ : π.ker ≤ Subgroup.center ↥C := by
    rw [hkerπ_eq]
    exact hkerf
  have hoddπ : Odd (Nat.card π.ker) := by
    rw [hkerπ_eq]
    exact hoddKer
  obtain ⟨σ, hσ⟩ := hspl ↥C π hπ hkerπ hoddπ
  let : Group.IsPerfect ↥C := hCcomp.1.1
  have hbot : π.ker = ⊥ :=
    CFSG.LieType.Steinberg.CentralExt.SL2Closed.ker_eq_bot_of_section π hkerπ σ hσ
  have hinj : Function.Injective π := (MonoidHom.ker_eq_bot_iff π).1 hbot
  exact ⟨MulEquiv.ofBijective π ⟨hinj, hπ⟩⟩

private theorem false_of_component_model_rank_four
    {G : Type} [Group G] [Finite G] {D : Data G} {V₀ V L : Subgroup G} {hV : IsElemAbelian 2 V}
    (c : S168e3Ctx D V₀ V L hV)
    (hcomp : IsComponentOf (lBar V₀ V hV L) (Mbar D.M V₀ V hV))
    {p : ℕ} {Y : Type} [Group Y] [Finite Y]
    (eH : ↥(lBar V₀ V hV L) ≃* Y)
    (hspl : ∀ (E : Type) [Group E] [Finite E] (π : E →* Y),
      Function.Surjective π → π.ker ≤ Subgroup.center E → Odd (Nat.card π.ker) →
      ∃ σ : Y →* E, ∀ y, π (σ y) = y)
    (hp : p.Prime) (hp2 : p ≠ 2)
    (hYrank : 4 ≤ CFSG.Open.pRank p (⊤ : Subgroup Y)) : False := by
  classical
  obtain ⟨K, hKcal, hKbar⟩ :=
    exists_calC_cover_of_component c.setting.hyp16.hyp125 c.std.h127 c.std.h119 hcomp
  obtain ⟨ψ, hψ⟩ := exists_barLift_of_hyp125 c.setting.hyp16.hyp125
  obtain ⟨eC⟩ := exists_iso_barImage_of_model (H := lBar V₀ V hV L) c.ne hKcal hKbar
    c.setting.hyp16.hyp125 hψ eH hspl
  have hCrank : 4 ≤ CFSG.Open.pRank p (UC22.barImage D.M K) := by
    rw [CFSG.SectionRank.pRank_eq_pRank_top_subgroup (p := p) (UC22.barImage D.M K)]
    rw [CFSG.SectionRank.pRank_top_eq_of_mulEquiv (p := p) hp.one_lt eC]
    exact hYrank
  have hle : CFSG.Open.pRank p (UC22.barImage D.M K) ≤ CFSG.Open.pRank p D.M := by
    refine (CFSG.SectionRank.pRank_mono (p := p) hp.one_lt le_top).trans ?_
    have htop : CFSG.AGLEmbedding.barM D.M D.M = ⊤ :=
      CFSG.AGLEmbedding.barM_self_eq_top D.M
    rw [← htop]
    exact (CFSG.AGLEmbedding.pRank_barM_eq hp hp2 D.M D.M le_rfl).le
  have hbound : CFSG.Open.pRank p D.M ≤ CFSG.Open.evenRank G :=
    CFSG.RankThreeCoreUniqueness.Helpers.local_pRank_le_evenRank p hp hp2 D.M D.maxLocal.1
  have h3 : CFSG.Open.evenRank G = 3 := c.std.h3
  omega

private theorem s15_eq_one_of_component_model_rank_two
    {G : Type} [Group G] [Finite G] {D : Data G} {V₀ V L : Subgroup G} {hV : IsElemAbelian 2 V}
    (c : S168e3Ctx D V₀ V L hV)
    (hcomp : IsComponentOf (lBar V₀ V hV L) (Mbar D.M V₀ V hV))
    {p : ℕ} {Y : Type} [Group Y] [Finite Y]
    (eH : ↥(lBar V₀ V hV L) ≃* Y)
    (hYcenter : Subgroup.center Y = ⊥)
    (hspl : ∀ (E : Type) [Group E] [Finite E] (π : E →* Y),
      Function.Surjective π → π.ker ≤ Subgroup.center E → Odd (Nat.card π.ker) →
      ∃ σ : Y →* E, ∀ y, π (σ y) = y)
    (hp : p.Prime) (hp2 : p ≠ 2)
    (hYrank : 2 ≤ CFSG.Open.pRank p (⊤ : Subgroup Y)) :
    s15 D.M V₀ V hV L = 1 := by
  classical
  by_contra hsne
  have hs1 : 1 ≤ s15 D.M V₀ V hV L := Om8Excl.one_le_s15 D.M V₀ V hV L
  have hs2 : 2 ≤ s15 D.M V₀ V hV L := by omega
  let S : Set (Subgroup (MulAut (Vtil V₀ V hV))) :=
    {X | ∃ φ ∈ Mbar D.M V₀ V hV,
      X = (barSub V₀ V hV L).map (MulAut.conj φ).toMonoidHom}
  have hS : 1 < S.ncard := by
    simpa only [S, s15] using (show 1 < s15 D.M V₀ V hV L by omega)
  obtain ⟨X, hXmem, hXne⟩ := Set.exists_ne_of_one_lt_ncard hS (barSub V₀ V hV L)
  obtain ⟨φ, hφM, hXeq⟩ := hXmem
  have hcompX : CFSG.Open.IsComponentOf X (Mbar D.M V₀ V hV) := by
    rw [hXeq]
    exact CFSG.Quasithin.F918V5G.isComponentOf_map_conj hcomp hφM
  have hconjEquiv : ↥(lBar V₀ V hV L) ≃*
      ↥((lBar V₀ V hV L).map (MulAut.conj φ).toMonoidHom) :=
    Subgroup.equivMapOfInjective (lBar V₀ V hV L) (MulAut.conj φ).toMonoidHom
      (MulAut.conj φ).injective
  have eHc : ↥X ≃* Y := by
    rw [hXeq]
    exact hconjEquiv.symm.trans eH
  have hXnebot : X ≠ ⊥ := by
    intro hbot
    rw [hXeq] at hbot
    exact c.ne ((Subgroup.map_eq_bot_iff_of_injective _
      (MulAut.conj φ).injective).1 hbot)
  obtain ⟨K, hKcal, hKbar⟩ :=
    exists_calC_cover_of_component c.setting.hyp16.hyp125 c.std.h127 c.std.h119 hcomp
  obtain ⟨K', hK'cal, hK'bar⟩ :=
    exists_calC_cover_of_component c.setting.hyp16.hyp125 c.std.h127 c.std.h119 hcompX
  obtain ⟨ψ, hψ⟩ := exists_barLift_of_hyp125 c.setting.hyp16.hyp125
  let C : Subgroup (Bar2 D.M) := UC22.barImage D.M K
  let C' : Subgroup (Bar2 D.M) := UC22.barImage D.M K'
  obtain ⟨eC⟩ := exists_iso_barImage_of_model (H := lBar V₀ V hV L) c.ne hKcal hKbar
    c.setting.hyp16.hyp125 hψ eH hspl
  obtain ⟨eC'⟩ := exists_iso_barImage_of_model (H := X) hXnebot hK'cal hK'bar
    c.setting.hyp16.hyp125 hψ eHc hspl
  have hCcomp : CFSG.IsComponent C := UC22.uc22p22l_barImage_isComponent hKcal
  have hC'comp : CFSG.IsComponent C' := UC22.uc22p22l_barImage_isComponent hK'cal
  have hCne : C ≠ C' := by
    intro heq
    have himageC : C.map ψ = lBar V₀ V hV L :=
      barImage_map_eq_of_mem_calC c.setting.hyp16.hyp125 hKcal hKbar ψ hψ
    have himageC' : C'.map ψ = X :=
      barImage_map_eq_of_mem_calC c.setting.hyp16.hyp125 hK'cal hK'bar ψ hψ
    have hmap : C.map ψ = C'.map ψ := congrArg (fun E => E.map ψ) heq
    rw [himageC, himageC'] at hmap
    exact hXne hmap.symm
  have hCrank : 2 ≤ CFSG.Open.pRank p C := by
    rw [CFSG.SectionRank.pRank_eq_pRank_top_subgroup (p := p) C]
    rw [CFSG.SectionRank.pRank_top_eq_of_mulEquiv (p := p) hp.one_lt eC]
    exact hYrank
  have hC'rank : 2 ≤ CFSG.Open.pRank p C' := by
    rw [CFSG.SectionRank.pRank_eq_pRank_top_subgroup (p := p) C']
    rw [CFSG.SectionRank.pRank_top_eq_of_mulEquiv (p := p) hp.one_lt eC']
    exact hYrank
  have hcommC : C ≤ Subgroup.centralizer (C' : Set (Bar2 D.M)) :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.mp
      ((CFSG.LocalCores.distinct_components_commute hCcomp hC'comp).resolve_left hCne)
  have hcenterC : Subgroup.center ↥C = ⊥ := by
    rw [← Subgroup.map_center_eq eC.symm, hYcenter, Subgroup.map_bot]
  have hinf_bot : C ⊓ C' = ⊥ :=
    CFSG.RankThree.PartTwo.Sec11.compJ3_inf_eq_bot hCcomp hC'comp hCne hcenterC
  have hcop : Nat.Coprime p (Nat.card ↥(C ⊓ C')) := by
    rw [hinf_bot, Subgroup.card_bot]
    exact Nat.coprime_one_right p
  have hcommute : ∀ x ∈ C, ∀ y ∈ C', x * y = y * x := by
    intro x hx y hy
    exact (Subgroup.mem_centralizer_iff.mp (hcommC hx) y hy).symm
  have hadd := CFSG.AGLEmbedding.pRank_add_le_pRank_sup_of_coprime
    (q := p) hp hcommute hcop
  have hsup : 2 + 2 ≤ CFSG.Open.pRank p (C ⊔ C') :=
    (add_le_add hCrank hC'rank).trans hadd
  have htop : CFSG.Open.pRank p (C ⊔ C') ≤
      CFSG.Open.pRank p (⊤ : Subgroup (Bar2 D.M)) :=
    CFSG.SectionRank.pRank_mono (p := p) hp.one_lt le_top
  have hbar : 2 + 2 ≤ CFSG.Open.pRank p (⊤ : Subgroup (Bar2 D.M)) := hsup.trans htop
  have hM : 2 + 2 ≤ CFSG.Open.pRank p D.M := by
    have htop : CFSG.AGLEmbedding.barM D.M D.M = ⊤ :=
      CFSG.AGLEmbedding.barM_self_eq_top D.M
    rw [← htop] at hbar
    exact hbar.trans (le_of_eq (CFSG.AGLEmbedding.pRank_barM_eq hp hp2 D.M D.M le_rfl))
  have hbound : CFSG.Open.pRank p D.M ≤ CFSG.Open.evenRank G :=
    CFSG.RankThreeCoreUniqueness.Helpers.local_pRank_le_evenRank p hp hp2 D.M D.maxLocal.1
  have h3 : CFSG.Open.evenRank G = 3 := c.std.h3
  omega

theorem s15_eq_one_of_sp_component_field_four_eight
    {G : Type} [Group G] [Finite G] {D : Data G}
    {V₀ V L : Subgroup G} {hV : IsElemAbelian 2 V}
    (c : S168e3Ctx D V₀ V L hV)
    (hcomp : IsComponentOf (lBar V₀ V hV L) (Mbar D.M V₀ V hV))
    {n a : ℕ} (ha : a = 2 ∨ a = 3) (hn : 4 ≤ n)
    (hSp : IsSpn ↥(lBar V₀ V hV L) n a) :
    s15 D.M V₀ V hV L = 1 := by
  classical
  obtain ⟨hEven, K, hKf, hKfin, hKcard, ⟨eH⟩⟩ := hSp
  let : Field K := hKf
  let : Finite K := hKfin
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : CharP K 2 :=
    CFSG.SectionRank.ClassicalOdd.charP_of_card (p := 2) (f := a) hKcard
  have h2n := Nat.two_mul_div_two_of_even hEven
  have hr : 2 ≤ n / 2 := by omega
  have hYcenter : Subgroup.center ↥(StatedSp (n / 2) K) = ⊥ :=
    CFSG.ClassicalGroups.Symplectic.center_statedSp_eq_bot_of_charP_two
      (m := n / 2) (F := K) (by omega)
  have hspl : ∀ (E : Type) [Group E] [Finite E] (π : E →* ↥(StatedSp (n / 2) K)),
      Function.Surjective π → π.ker ≤ Subgroup.center E → Odd (Nat.card π.ker) →
      ∃ σ : ↥(StatedSp (n / 2) K) →* E, ∀ x, π (σ x) = x := by
    intro E _ _ π hπ hker hodd
    obtain ⟨σ, hσ, -⟩ :=
      CFSG.SectionRank.EvenCover.even_symplectic_central_odd_extension_splitting
        (K := K) (n / 2) hπ hker hodd
    exact ⟨σ, hσ⟩
  rcases ha with rfl | rfl
  · have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    have hpK : 3 ∣ Nat.card K ^ 2 - 1 := by rw [hKcard]; norm_num
    have hrank := CFSG.GroupTheory.WeirSylow.pRank_top_statedSp_eq_of_dvd
      (p := 3) (by norm_num) hpK (n / 2)
    have hYrank : 2 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup ↥(StatedSp (n / 2) K)) := by
      rw [hrank]
      exact hr
    exact s15_eq_one_of_component_model_rank_two c hcomp eH hYcenter hspl
      Nat.prime_three (by norm_num) hYrank
  · have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
    have hpK : 7 ∣ Nat.card K ^ 2 - 1 := by rw [hKcard]; norm_num
    have hrank := CFSG.GroupTheory.WeirSylow.pRank_top_statedSp_eq_of_dvd
      (p := 7) (by norm_num) hpK (n / 2)
    have hYrank : 2 ≤ CFSG.Open.pRank 7 (⊤ : Subgroup ↥(StatedSp (n / 2) K)) := by
      rw [hrank]
      exact hr
    exact s15_eq_one_of_component_model_rank_two c hcomp eH hYcenter hspl
      (by norm_num : Nat.Prime 7) (by norm_num) hYrank

theorem s168e3_false_of_sp_component_field_four_eight_ge_eight
    {G : Type} [Group G] [Finite G] {D : Data G}
    {V₀ V L : Subgroup G} {hV : IsElemAbelian 2 V}
    (c : S168e3Ctx D V₀ V L hV)
    (hcomp : IsComponentOf (lBar V₀ V hV L) (Mbar D.M V₀ V hV))
    {n a : ℕ} (ha : a = 2 ∨ a = 3) (hn : 8 ≤ n)
    (hSp : IsSpn ↥(lBar V₀ V hV L) n a) :
    False := by
  classical
  obtain ⟨hEven, K, hKf, hKfin, hKcard, ⟨eH⟩⟩ := hSp
  let : Field K := hKf
  let : Finite K := hKfin
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : CharP K 2 :=
    CFSG.SectionRank.ClassicalOdd.charP_of_card (p := 2) (f := a) hKcard
  have h2n := Nat.two_mul_div_two_of_even hEven
  have hr : 4 ≤ n / 2 := by omega
  have hspl : ∀ (E : Type) [Group E] [Finite E] (π : E →* ↥(StatedSp (n / 2) K)),
      Function.Surjective π → π.ker ≤ Subgroup.center E → Odd (Nat.card π.ker) →
      ∃ σ : ↥(StatedSp (n / 2) K) →* E, ∀ x, π (σ x) = x := by
    intro E _ _ π hπ hker hodd
    obtain ⟨σ, hσ, -⟩ :=
      CFSG.SectionRank.EvenCover.even_symplectic_central_odd_extension_splitting
        (K := K) (n / 2) hπ hker hodd
    exact ⟨σ, hσ⟩
  rcases ha with rfl | rfl
  · have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    have hpK : 3 ∣ Nat.card K ^ 2 - 1 := by rw [hKcard]; norm_num
    have hrank := CFSG.GroupTheory.WeirSylow.pRank_top_statedSp_eq_of_dvd
      (p := 3) (by norm_num) hpK (n / 2)
    have hYrank : 4 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup ↥(StatedSp (n / 2) K)) := by
      rw [hrank]
      exact hr
    exact false_of_component_model_rank_four c hcomp eH hspl
      Nat.prime_three (by norm_num) hYrank
  · have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
    have hpK : 7 ∣ Nat.card K ^ 2 - 1 := by rw [hKcard]; norm_num
    have hrank := CFSG.GroupTheory.WeirSylow.pRank_top_statedSp_eq_of_dvd
      (p := 7) (by norm_num) hpK (n / 2)
    have hYrank : 4 ≤ CFSG.Open.pRank 7 (⊤ : Subgroup ↥(StatedSp (n / 2) K)) := by
      rw [hrank]
      exact hr
    exact false_of_component_model_rank_four c hcomp eH hspl
      (by norm_num : Nat.Prime 7) (by norm_num) hYrank

private theorem statedScalars_quadPlus_bot {K : Type} [Field K] [CharP K 2]
    {r : ℕ} (hr : 1 ≤ r) :
    (StatedScalars (Fin r ⊕ Fin r) K).subgroupOf
      (StatedOmega (StatedQuadPlus r K)) = ⊥ :=
  CFSG.SectionRank.EvenCover.statedScalars_subgroupOf_statedOmega_eq_bot
    (Q := CFSG.LieType.Universal.Spin.quadPlus r K)
    (Q₀ := StatedQuadPlus r K)
    (CFSG.LieType.Universal.Spin.coe_quadPlus r K)
    (CFSG.LieType.Universal.Spin.exists_map_ne_zero_of_hypPair _
      (CFSG.ClassicalGroups.Orthogonal.plusPair K (⟨0, by omega⟩ : Fin r)))

private noncomputable def statedProj_statedOmega_quadPlus_mulEquiv
    {K : Type} [Field K] [CharP K 2] {r : ℕ} (hr : 1 ≤ r) :
    StatedProj (StatedOmega (StatedQuadPlus r K)) ≃*
      ↥(StatedOmega (StatedQuadPlus r K)) :=
  (QuotientGroup.quotientMulEquivOfEq (statedScalars_quadPlus_bot (K := K) hr)).trans
    QuotientGroup.quotientBot

theorem s15_eq_one_of_omegaPlus_component_field_four_eight
    {G : Type} [Group G] [Finite G] {D : Data G}
    {V₀ V L : Subgroup G} {hV : IsElemAbelian 2 V}
    (c : S168e3Ctx D V₀ V L hV)
    (hcomp : IsComponentOf (lBar V₀ V hV L) (Mbar D.M V₀ V hV))
    {n a : ℕ} (ha : a = 2 ∨ a = 3) (hn : 6 ≤ n)
    (hOm : IsOmegaPlus ↥(lBar V₀ V hV L) n a) :
    s15 D.M V₀ V hV L = 1 := by
  classical
  obtain ⟨hEven, K, hKf, hKfin, hKcard, ⟨eHproj⟩⟩ := hOm
  let : Field K := hKf
  let : Finite K := hKfin
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : CharP K 2 :=
    CFSG.SectionRank.ClassicalOdd.charP_of_card (p := 2) (f := a) hKcard
  have h2n := Nat.two_mul_div_two_of_even hEven
  have h3r : 3 ≤ n / 2 := by omega
  let eProj := statedProj_statedOmega_quadPlus_mulEquiv (K := K) (r := n / 2) (by omega)
  have eH : ↥(lBar V₀ V hV L) ≃* ↥(StatedOmega (StatedQuadPlus (n / 2) K)) :=
    eHproj.trans eProj
  have hYcenter : Subgroup.center ↥(StatedOmega (StatedQuadPlus (n / 2) K)) = ⊥ := by
    rw [CFSG.LieType.Universal.Spin.center_statedOmega_quadPlus (n := n / 2) (K := K) h3r,
      statedScalars_quadPlus_bot (K := K) (r := n / 2) (by omega)]
  have hspl : ∀ (E : Type) [Group E] [Finite E]
      (π : E →* ↥(StatedOmega (StatedQuadPlus (n / 2) K))),
      Function.Surjective π → π.ker ≤ Subgroup.center E → Odd (Nat.card π.ker) →
      ∃ σ : ↥(StatedOmega (StatedQuadPlus (n / 2) K)) →* E, ∀ x, π (σ x) = x := by
    intro E _ _ π hπ hker hodd
    obtain ⟨σ, hσ, -⟩ :=
      CFSG.SectionRank.EvenCover.even_split_orthogonal_central_odd_extension_splitting
        (n := n / 2) h3r hπ hker hodd
    exact ⟨σ, hσ⟩
  rcases ha with rfl | rfl
  · have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    have hKunits : 3 ∣ Nat.card Kˣ := by rw [Nat.card_units, hKcard]; norm_num
    have hrankProj : n / 2 ≤ CFSG.Open.pRank 3
        (⊤ : Subgroup (StatedProj (StatedOmega (StatedQuadPlus (n / 2) K)))) :=
      CFSG.RankThree.PartTwo.Sec19.Census194.RonanC194.OmegaEven.le_pRank_omegaPlus_torus
        (K := K) (r := 3) (n := n / 2) Nat.prime_three (by norm_num) hKunits
    have hYrank : 2 ≤ CFSG.Open.pRank 3
        (⊤ : Subgroup ↥(StatedOmega (StatedQuadPlus (n / 2) K))) := by
      rw [← CFSG.SectionRank.pRank_top_eq_of_mulEquiv (p := 3) (by norm_num) eProj]
      exact (by omega : 2 ≤ n / 2).trans hrankProj
    exact s15_eq_one_of_component_model_rank_two c hcomp eH hYcenter hspl
      Nat.prime_three (by norm_num) hYrank
  · have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
    have hKunits : 7 ∣ Nat.card Kˣ := by rw [Nat.card_units, hKcard]; norm_num
    have hrankProj : n / 2 ≤ CFSG.Open.pRank 7
        (⊤ : Subgroup (StatedProj (StatedOmega (StatedQuadPlus (n / 2) K)))) :=
      CFSG.RankThree.PartTwo.Sec19.Census194.RonanC194.OmegaEven.le_pRank_omegaPlus_torus
        (K := K) (r := 7) (n := n / 2) (by norm_num) (by norm_num) hKunits
    have hYrank : 2 ≤ CFSG.Open.pRank 7
        (⊤ : Subgroup ↥(StatedOmega (StatedQuadPlus (n / 2) K))) := by
      rw [← CFSG.SectionRank.pRank_top_eq_of_mulEquiv (p := 7) (by norm_num) eProj]
      exact (by omega : 2 ≤ n / 2).trans hrankProj
    exact s15_eq_one_of_component_model_rank_two c hcomp eH hYcenter hspl
      (by norm_num : Nat.Prime 7) (by norm_num) hYrank

theorem s168e3_false_of_omegaPlus_component_field_four_eight_ge_eight
    {G : Type} [Group G] [Finite G] {D : Data G}
    {V₀ V L : Subgroup G} {hV : IsElemAbelian 2 V}
    (c : S168e3Ctx D V₀ V L hV)
    (hcomp : IsComponentOf (lBar V₀ V hV L) (Mbar D.M V₀ V hV))
    {n a : ℕ} (ha : a = 2 ∨ a = 3) (hn : 8 ≤ n)
    (hOm : IsOmegaPlus ↥(lBar V₀ V hV L) n a) :
    False := by
  classical
  obtain ⟨hEven, K, hKf, hKfin, hKcard, ⟨eHproj⟩⟩ := hOm
  let : Field K := hKf
  let : Finite K := hKfin
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : CharP K 2 :=
    CFSG.SectionRank.ClassicalOdd.charP_of_card (p := 2) (f := a) hKcard
  have h2n := Nat.two_mul_div_two_of_even hEven
  have h3r : 3 ≤ n / 2 := by omega
  have h4r : 4 ≤ n / 2 := by omega
  let eProj := statedProj_statedOmega_quadPlus_mulEquiv (K := K) (r := n / 2) (by omega)
  have eH : ↥(lBar V₀ V hV L) ≃* ↥(StatedOmega (StatedQuadPlus (n / 2) K)) :=
    eHproj.trans eProj
  have hspl : ∀ (E : Type) [Group E] [Finite E]
      (π : E →* ↥(StatedOmega (StatedQuadPlus (n / 2) K))),
      Function.Surjective π → π.ker ≤ Subgroup.center E → Odd (Nat.card π.ker) →
      ∃ σ : ↥(StatedOmega (StatedQuadPlus (n / 2) K)) →* E, ∀ x, π (σ x) = x := by
    intro E _ _ π hπ hker hodd
    obtain ⟨σ, hσ, -⟩ :=
      CFSG.SectionRank.EvenCover.even_split_orthogonal_central_odd_extension_splitting
        (n := n / 2) h3r hπ hker hodd
    exact ⟨σ, hσ⟩
  rcases ha with rfl | rfl
  · have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    have hKunits : 3 ∣ Nat.card Kˣ := by rw [Nat.card_units, hKcard]; norm_num
    have hrankProj : n / 2 ≤ CFSG.Open.pRank 3
        (⊤ : Subgroup (StatedProj (StatedOmega (StatedQuadPlus (n / 2) K)))) :=
      CFSG.RankThree.PartTwo.Sec19.Census194.RonanC194.OmegaEven.le_pRank_omegaPlus_torus
        (K := K) (r := 3) (n := n / 2) Nat.prime_three (by norm_num) hKunits
    have hYrank : 4 ≤ CFSG.Open.pRank 3
        (⊤ : Subgroup ↥(StatedOmega (StatedQuadPlus (n / 2) K))) := by
      rw [← CFSG.SectionRank.pRank_top_eq_of_mulEquiv (p := 3) (by norm_num) eProj]
      exact h4r.trans hrankProj
    exact false_of_component_model_rank_four c hcomp eH hspl
      Nat.prime_three (by norm_num) hYrank
  · have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
    have hKunits : 7 ∣ Nat.card Kˣ := by rw [Nat.card_units, hKcard]; norm_num
    have hrankProj : n / 2 ≤ CFSG.Open.pRank 7
        (⊤ : Subgroup (StatedProj (StatedOmega (StatedQuadPlus (n / 2) K)))) :=
      CFSG.RankThree.PartTwo.Sec19.Census194.RonanC194.OmegaEven.le_pRank_omegaPlus_torus
        (K := K) (r := 7) (n := n / 2) (by norm_num) (by norm_num) hKunits
    have hYrank : 4 ≤ CFSG.Open.pRank 7
        (⊤ : Subgroup ↥(StatedOmega (StatedQuadPlus (n / 2) K))) := by
      rw [← CFSG.SectionRank.pRank_top_eq_of_mulEquiv (p := 7) (by norm_num) eProj]
      exact h4r.trans hrankProj
    exact false_of_component_model_rank_four c hcomp eH hspl
      (by norm_num : Nat.Prime 7) (by norm_num) hYrank

private theorem statedScalars_quadMinus_bot {K : Type} [Field K] [CharP K 2]
    {r : ℕ} (hr : 2 ≤ r) {b c : K} :
    (StatedScalars (Fin (r - 1) ⊕ Fin (r - 1) ⊕ Fin 2) K).subgroupOf
      (StatedOmega (StatedQuadMinus r K b c)) = ⊥ :=
  CFSG.SectionRank.EvenCover.statedScalars_subgroupOf_statedOmega_eq_bot
    (Q := CFSG.LieType.Universal.Spin.quadMinus r K b c)
    (Q₀ := StatedQuadMinus r K b c)
    (CFSG.LieType.Universal.Spin.coe_quadMinus r K b c)
    (CFSG.LieType.Universal.Spin.exists_map_ne_zero_of_hypPair _
      (CFSG.ClassicalGroups.Orthogonal.minusPair K b c (⟨0, by omega⟩ : Fin (r - 1))))

private noncomputable def statedProj_statedOmega_quadMinus_mulEquiv
    {K : Type} [Field K] [CharP K 2] {r : ℕ} (hr : 2 ≤ r) {b c : K} :
    StatedProj (StatedOmega (StatedQuadMinus r K b c)) ≃*
      ↥(StatedOmega (StatedQuadMinus r K b c)) :=
  (QuotientGroup.quotientMulEquivOfEq
    (statedScalars_quadMinus_bot (K := K) (b := b) (c := c) hr)).trans
    QuotientGroup.quotientBot

theorem s15_eq_one_of_omegaMinus_component_field_four_eight
    {G : Type} [Group G] [Finite G] {D : Data G}
    {V₀ V L : Subgroup G} {hV : IsElemAbelian 2 V}
    (hc : S168e3Ctx D V₀ V L hV)
    (hcomp : IsComponentOf (lBar V₀ V hV L) (Mbar D.M V₀ V hV))
    {n a : ℕ} (ha : a = 2 ∨ a = 3) (hn : 6 ≤ n)
    (hOm : IsOmegaMinus ↥(lBar V₀ V hV L) n a) :
    s15 D.M V₀ V hV L = 1 := by
  classical
  obtain ⟨hEven, K, hKf, hKfin, b, c, hKcard, hirr, ⟨eHproj⟩⟩ := hOm
  let : Field K := hKf
  let : Finite K := hKfin
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : CharP K 2 :=
    CFSG.SectionRank.ClassicalOdd.charP_of_card (p := 2) (f := a) hKcard
  have h2n := Nat.two_mul_div_two_of_even hEven
  rcases ha with rfl | rfl
  ·
    have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    have hKunits : 3 ∣ Nat.card Kˣ := by rw [Nat.card_units, hKcard]; norm_num
    by_cases h6 : n = 6
    ·
      subst n
      have h62 : (6 : ℕ) / 2 = 3 := by norm_num
      have eHproj3 : ↥(lBar V₀ V hV L) ≃*
          StatedProj (StatedOmega (StatedQuadMinus 3 K b c)) := by
        simpa only [h62] using eHproj
      let eProj3 := statedProj_statedOmega_quadMinus_mulEquiv
        (K := K) (r := 3) (b := b) (c := c) (by norm_num)
      obtain ⟨F, hFf, hFfin, hFcard, ⟨eSU⟩⟩ :=
        CFSG.RankThree.GF2n.Stroth80.exists_statedOmega_quadMinus_three_mulEquiv
          (K := K) (b := b) (c := c) (f := 2) hKcard hirr
      let : Field F := hFf
      let : Finite F := hFfin
      have : CharP F 2 :=
        CFSG.ClassicalGroups.Unitary.charP_of_card_sq (p := 2) (f := 2) hFcard
      have eModel : StatedProj (StatedOmega (StatedQuadMinus 3 K b c)) ≃*
          ↥(StatedSU 4 (2 ^ 2) F) := eProj3.trans eSU
      have eH : ↥(lBar V₀ V hV L) ≃* ↥(StatedSU 4 (2 ^ 2) F) := eHproj3.trans eModel
      have hYcenter : Subgroup.center ↥(StatedSU 4 (2 ^ 2) F) = ⊥ := by
        have hle := CFSG.StandardType.center_statedSU_le_scalars
          (F := F) (n := 2) (d := 4) hFcard (by norm_num)
        have hbot := CFSG.SectionRank.EvenCover.statedScalars_subgroupOf_statedSU_four_eq_bot
          (K := F) (q := 2 ^ 2)
        exact eq_bot_iff.mpr (hbot ▸ hle)
      have hrankProj : 3 - 1 ≤ CFSG.Open.pRank 3
          (⊤ : Subgroup (StatedProj (StatedOmega (StatedQuadMinus 3 K b c)))) :=
        CFSG.RankThree.PartTwo.Sec19.Census194.RonanC194.OmegaEven.le_pRank_omegaMinus_torus
          (K := K) (r := 3) (n := 3) Nat.prime_three (by norm_num) hKunits b c
      have hYrank : 2 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup ↥(StatedSU 4 (2 ^ 2) F)) := by
        rw [← CFSG.SectionRank.pRank_top_eq_of_mulEquiv (p := 3) (by norm_num) eModel]
        exact (by norm_num : 2 ≤ 3 - 1).trans hrankProj
      have hspl : ∀ (E : Type) [Group E] [Finite E]
          (π : E →* ↥(StatedSU 4 (2 ^ 2) F)),
          Function.Surjective π → π.ker ≤ Subgroup.center E → Odd (Nat.card π.ker) →
          ∃ σ : ↥(StatedSU 4 (2 ^ 2) F) →* E, ∀ x, π (σ x) = x := by
        intro E _ _ π hπ hker hodd
        obtain ⟨σ, hσ, -⟩ :=
          CFSG.RankThree.PartTwo.Sec19.Census194.RonanC194.evenSU_central_odd_extension_splitting_stated
            (K := F) (f := 2) (n := 4) hFcard (by norm_num) (by norm_num) hπ hker hodd
        exact ⟨σ, hσ⟩
      exact s15_eq_one_of_component_model_rank_two hc hcomp eH hYcenter hspl
        Nat.prime_three (by norm_num) hYrank
    ·
      have h8 : 8 ≤ n := by
        by_contra h
        have : n = 6 := by omega
        exact h6 this
      have h4r : 4 ≤ n / 2 := by omega
      let eProj := statedProj_statedOmega_quadMinus_mulEquiv
        (K := K) (r := n / 2) (b := b) (c := c) (by omega)
      have eH : ↥(lBar V₀ V hV L) ≃*
          ↥(StatedOmega (StatedQuadMinus (n / 2) K b c)) := eHproj.trans eProj
      have hYcenter : Subgroup.center ↥(StatedOmega (StatedQuadMinus (n / 2) K b c)) = ⊥ := by
        rw [CFSG.LieType.Universal.Spin.center_statedOmega_quadMinus (n := n / 2) (K := K)
          (b := b) (c := c) h4r hirr,
          statedScalars_quadMinus_bot (K := K) (r := n / 2) (b := b) (c := c) (by omega)]
      have hrankProj : n / 2 - 1 ≤ CFSG.Open.pRank 3
          (⊤ : Subgroup (StatedProj (StatedOmega (StatedQuadMinus (n / 2) K b c)))) :=
        CFSG.RankThree.PartTwo.Sec19.Census194.RonanC194.OmegaEven.le_pRank_omegaMinus_torus
          (K := K) (r := 3) (n := n / 2) Nat.prime_three (by norm_num) hKunits b c
      have hYrank : 2 ≤ CFSG.Open.pRank 3
          (⊤ : Subgroup ↥(StatedOmega (StatedQuadMinus (n / 2) K b c))) := by
        rw [← CFSG.SectionRank.pRank_top_eq_of_mulEquiv (p := 3) (by norm_num) eProj]
        exact (by omega : 2 ≤ n / 2 - 1).trans hrankProj
      have hspl : ∀ (E : Type) [Group E] [Finite E]
          (π : E →* ↥(StatedOmega (StatedQuadMinus (n / 2) K b c))),
          Function.Surjective π → π.ker ≤ Subgroup.center E → Odd (Nat.card π.ker) →
          ∃ σ : ↥(StatedOmega (StatedQuadMinus (n / 2) K b c)) →* E, ∀ x, π (σ x) = x := by
        intro E _ _ π hπ hker hodd
        obtain ⟨σ, hσ, -⟩ :=
          CFSG.SectionRank.EvenCover.even_nonsplit_orthogonal_central_odd_extension_splitting
            (n := n / 2) h4r hirr hπ hker hodd
        exact ⟨σ, hσ⟩
      exact s15_eq_one_of_component_model_rank_two hc hcomp eH hYcenter hspl
        Nat.prime_three (by norm_num) hYrank
  ·
    have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
    have hKunits : 7 ∣ Nat.card Kˣ := by rw [Nat.card_units, hKcard]; norm_num
    by_cases h6 : n = 6
    · subst n
      have h62 : (6 : ℕ) / 2 = 3 := by norm_num
      have eHproj3 : ↥(lBar V₀ V hV L) ≃*
          StatedProj (StatedOmega (StatedQuadMinus 3 K b c)) := by
        simpa only [h62] using eHproj
      let eProj3 := statedProj_statedOmega_quadMinus_mulEquiv
        (K := K) (r := 3) (b := b) (c := c) (by norm_num)
      obtain ⟨F, hFf, hFfin, hFcard, ⟨eSU⟩⟩ :=
        CFSG.RankThree.GF2n.Stroth80.exists_statedOmega_quadMinus_three_mulEquiv
          (K := K) (b := b) (c := c) (f := 3) hKcard hirr
      let : Field F := hFf
      let : Finite F := hFfin
      have : CharP F 2 :=
        CFSG.ClassicalGroups.Unitary.charP_of_card_sq (p := 2) (f := 3) hFcard
      have eModel : StatedProj (StatedOmega (StatedQuadMinus 3 K b c)) ≃*
          ↥(StatedSU 4 (2 ^ 3) F) := eProj3.trans eSU
      have eH : ↥(lBar V₀ V hV L) ≃* ↥(StatedSU 4 (2 ^ 3) F) := eHproj3.trans eModel
      have hYcenter : Subgroup.center ↥(StatedSU 4 (2 ^ 3) F) = ⊥ := by
        have hle := CFSG.StandardType.center_statedSU_le_scalars
          (F := F) (n := 3) (d := 4) hFcard (by norm_num)
        have hbot := CFSG.SectionRank.EvenCover.statedScalars_subgroupOf_statedSU_four_eq_bot
          (K := F) (q := 2 ^ 3)
        exact eq_bot_iff.mpr (hbot ▸ hle)
      have hrankProj : 3 - 1 ≤ CFSG.Open.pRank 7
          (⊤ : Subgroup (StatedProj (StatedOmega (StatedQuadMinus 3 K b c)))) :=
        CFSG.RankThree.PartTwo.Sec19.Census194.RonanC194.OmegaEven.le_pRank_omegaMinus_torus
          (K := K) (r := 7) (n := 3) (by norm_num) (by norm_num) hKunits b c
      have hYrank : 2 ≤ CFSG.Open.pRank 7 (⊤ : Subgroup ↥(StatedSU 4 (2 ^ 3) F)) := by
        rw [← CFSG.SectionRank.pRank_top_eq_of_mulEquiv (p := 7) (by norm_num) eModel]
        exact (by norm_num : 2 ≤ 3 - 1).trans hrankProj
      have hspl : ∀ (E : Type) [Group E] [Finite E]
          (π : E →* ↥(StatedSU 4 (2 ^ 3) F)),
          Function.Surjective π → π.ker ≤ Subgroup.center E → Odd (Nat.card π.ker) →
          ∃ σ : ↥(StatedSU 4 (2 ^ 3) F) →* E, ∀ x, π (σ x) = x := by
        intro E _ _ π hπ hker hodd
        obtain ⟨σ, hσ, -⟩ :=
          CFSG.RankThree.PartTwo.Sec19.Census194.RonanC194.evenSU_central_odd_extension_splitting_stated
            (K := F) (f := 3) (n := 4) hFcard (by norm_num) (by norm_num) hπ hker hodd
        exact ⟨σ, hσ⟩
      exact s15_eq_one_of_component_model_rank_two hc hcomp eH hYcenter hspl
        (by norm_num : Nat.Prime 7) (by norm_num) hYrank
    · have h8 : 8 ≤ n := by
        by_contra h
        have : n = 6 := by omega
        exact h6 this
      have h4r : 4 ≤ n / 2 := by omega
      let eProj := statedProj_statedOmega_quadMinus_mulEquiv
        (K := K) (r := n / 2) (b := b) (c := c) (by omega)
      have eH : ↥(lBar V₀ V hV L) ≃*
          ↥(StatedOmega (StatedQuadMinus (n / 2) K b c)) := eHproj.trans eProj
      have hYcenter : Subgroup.center ↥(StatedOmega (StatedQuadMinus (n / 2) K b c)) = ⊥ := by
        rw [CFSG.LieType.Universal.Spin.center_statedOmega_quadMinus (n := n / 2) (K := K)
          (b := b) (c := c) h4r hirr,
          statedScalars_quadMinus_bot (K := K) (r := n / 2) (b := b) (c := c) (by omega)]
      have hrankProj : n / 2 - 1 ≤ CFSG.Open.pRank 7
          (⊤ : Subgroup (StatedProj (StatedOmega (StatedQuadMinus (n / 2) K b c)))) :=
        CFSG.RankThree.PartTwo.Sec19.Census194.RonanC194.OmegaEven.le_pRank_omegaMinus_torus
          (K := K) (r := 7) (n := n / 2) (by norm_num) (by norm_num) hKunits b c
      have hYrank : 2 ≤ CFSG.Open.pRank 7
          (⊤ : Subgroup ↥(StatedOmega (StatedQuadMinus (n / 2) K b c))) := by
        rw [← CFSG.SectionRank.pRank_top_eq_of_mulEquiv (p := 7) (by norm_num) eProj]
        exact (by omega : 2 ≤ n / 2 - 1).trans hrankProj
      have hspl : ∀ (E : Type) [Group E] [Finite E]
          (π : E →* ↥(StatedOmega (StatedQuadMinus (n / 2) K b c))),
          Function.Surjective π → π.ker ≤ Subgroup.center E → Odd (Nat.card π.ker) →
          ∃ σ : ↥(StatedOmega (StatedQuadMinus (n / 2) K b c)) →* E, ∀ x, π (σ x) = x := by
        intro E _ _ π hπ hker hodd
        obtain ⟨σ, hσ, -⟩ :=
          CFSG.SectionRank.EvenCover.even_nonsplit_orthogonal_central_odd_extension_splitting
            (n := n / 2) h4r hirr hπ hker hodd
        exact ⟨σ, hσ⟩
      exact s15_eq_one_of_component_model_rank_two hc hcomp eH hYcenter hspl
        (by norm_num : Nat.Prime 7) (by norm_num) hYrank

theorem s168e3_false_of_omegaMinus_component_field_four_eight_ge_ten
    {G : Type} [Group G] [Finite G] {D : Data G}
    {V₀ V L : Subgroup G} {hV : IsElemAbelian 2 V}
    (hc : S168e3Ctx D V₀ V L hV)
    (hcomp : IsComponentOf (lBar V₀ V hV L) (Mbar D.M V₀ V hV))
    {n a : ℕ} (ha : a = 2 ∨ a = 3) (hn : 10 ≤ n)
    (hOm : IsOmegaMinus ↥(lBar V₀ V hV L) n a) :
    False := by
  classical
  obtain ⟨hEven, K, hKf, hKfin, b, c, hKcard, hirr, ⟨eHproj⟩⟩ := hOm
  let : Field K := hKf
  let : Finite K := hKfin
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : CharP K 2 :=
    CFSG.SectionRank.ClassicalOdd.charP_of_card (p := 2) (f := a) hKcard
  have h2n := Nat.two_mul_div_two_of_even hEven
  have h4r : 4 ≤ n / 2 := by omega
  let eProj := statedProj_statedOmega_quadMinus_mulEquiv
    (K := K) (r := n / 2) (b := b) (c := c) (by omega)
  have eH : ↥(lBar V₀ V hV L) ≃*
      ↥(StatedOmega (StatedQuadMinus (n / 2) K b c)) := eHproj.trans eProj
  have hspl : ∀ (E : Type) [Group E] [Finite E]
      (π : E →* ↥(StatedOmega (StatedQuadMinus (n / 2) K b c))),
      Function.Surjective π → π.ker ≤ Subgroup.center E → Odd (Nat.card π.ker) →
      ∃ σ : ↥(StatedOmega (StatedQuadMinus (n / 2) K b c)) →* E, ∀ x, π (σ x) = x := by
    intro E _ _ π hπ hker hodd
    obtain ⟨σ, hσ, -⟩ :=
      CFSG.SectionRank.EvenCover.even_nonsplit_orthogonal_central_odd_extension_splitting
        (n := n / 2) h4r hirr hπ hker hodd
    exact ⟨σ, hσ⟩
  rcases ha with rfl | rfl
  · have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    have hKunits : 3 ∣ Nat.card Kˣ := by rw [Nat.card_units, hKcard]; norm_num
    have hrankProj : n / 2 - 1 ≤ CFSG.Open.pRank 3
        (⊤ : Subgroup (StatedProj (StatedOmega (StatedQuadMinus (n / 2) K b c)))) :=
      CFSG.RankThree.PartTwo.Sec19.Census194.RonanC194.OmegaEven.le_pRank_omegaMinus_torus
        (K := K) (r := 3) (n := n / 2) Nat.prime_three (by norm_num) hKunits b c
    have hYrank : 4 ≤ CFSG.Open.pRank 3
        (⊤ : Subgroup ↥(StatedOmega (StatedQuadMinus (n / 2) K b c))) := by
      rw [← CFSG.SectionRank.pRank_top_eq_of_mulEquiv (p := 3) (by norm_num) eProj]
      exact (by omega : 4 ≤ n / 2 - 1).trans hrankProj
    exact false_of_component_model_rank_four hc hcomp eH hspl
      Nat.prime_three (by norm_num) hYrank
  · have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
    have hKunits : 7 ∣ Nat.card Kˣ := by rw [Nat.card_units, hKcard]; norm_num
    have hrankProj : n / 2 - 1 ≤ CFSG.Open.pRank 7
        (⊤ : Subgroup (StatedProj (StatedOmega (StatedQuadMinus (n / 2) K b c)))) :=
      CFSG.RankThree.PartTwo.Sec19.Census194.RonanC194.OmegaEven.le_pRank_omegaMinus_torus
        (K := K) (r := 7) (n := n / 2) (by norm_num) (by norm_num) hKunits b c
    have hYrank : 4 ≤ CFSG.Open.pRank 7
        (⊤ : Subgroup ↥(StatedOmega (StatedQuadMinus (n / 2) K b c))) := by
      rw [← CFSG.SectionRank.pRank_top_eq_of_mulEquiv (p := 7) (by norm_num) eProj]
      exact (by omega : 4 ≤ n / 2 - 1).trans hrankProj
    exact false_of_component_model_rank_four hc hcomp eH hspl
      (by norm_num : Nat.Prime 7) (by norm_num) hYrank

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
