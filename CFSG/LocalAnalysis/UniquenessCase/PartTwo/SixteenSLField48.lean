module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC1677ThreeDefs
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.ExceptionalComponentCover
import CFSG.Quasithin.H13.A5W1622q
import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanCoverThreeRank
import CFSG.LocalAnalysis.AGLEmbedding.RankTools
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC165ExclDirect
public import CFSG.Quasithin.Background.F918V5GComp

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G] {D : Data G} {V₀ V L : Subgroup G}
  {hV : IsElemAbelian 2 V}

private theorem s16sl_exists_actual_cover
    (c : S168e3Ctx D V₀ V L hV)
    {H : Subgroup (MulAut (Vtil V₀ V hV))}
    (hcomp : IsComponentOf H (Mbar D.M V₀ V hV))
    (hHne : H ≠ ⊥)
    (ψ : Bar2 D.M →* MulAut (Vtil V₀ V hV))
    (hψ : ∀ m : D.M, ψ (QuotientGroup.mk m) =
      actTil V₀ V hV ⟨m, le_stabTil c.setting.hyp16.hyp125.pairFacts.le_normalizer
        c.setting.hyp16.hyp125.pairFacts.le_normalizer₀ m.2⟩) :
    ∃ C : Subgroup (Bar2 D.M), CFSG.IsComponent C ∧ C.map ψ = H ∧
      ∃ f : ↥C →* ↥H, Function.Surjective f ∧ f.ker ≤ Subgroup.center ↥C := by
  classical
  obtain ⟨K, hK, hbarK⟩ :=
    exists_calC_cover_of_component c.setting.hyp16.hyp125 c.std.h127 c.std.h119 hcomp
  let C : Subgroup (Bar2 D.M) := UC22.barImage D.M K
  have hCcomp : CFSG.IsComponent C := UC22.uc22p22l_barImage_isComponent hK
  have hCmap : C.map ψ = H := by
    simpa [C] using
      barImage_map_eq_of_mem_calC c.setting.hyp16.hyp125 hK hbarK ψ hψ
  let f : ↥C →* ↥H :=
    (MulEquiv.subgroupCongr hCmap).toMonoidHom.comp (ψ.subgroupMap C)
  have hf : Function.Surjective f :=
    (MulEquiv.subgroupCongr hCmap).surjective.comp (ψ.subgroupMap_surjective C)
  have hP : Nontrivial ↥H := (Subgroup.nontrivial_iff_ne_bot H).2 hHne
  have hfker : f.ker ≤ Subgroup.center ↥C :=
    CFSG.Quasithin.H13.A5.ker_le_center_of_isQuasisimple hCcomp.1 f hf hP
  exact ⟨C, hCcomp, hCmap, f, hf, hfker⟩

private theorem s16sl_equiv_of_stated
    {C H : Type} [Group C] [Group H] [Group.IsPerfect C]
    (f : C →* H) (hf : Function.Surjective f) (hfker : f.ker ≤ Subgroup.center C)
    {n : ℕ} (hn : 4 ≤ n)
    {K : Type} [Field K] [Finite K]
    (eH : H ≃* ↥(StatedSL n K))
    (h2 : Nat.card K ≠ 2) (h3 : Nat.card K ≠ 3) :
    Nonempty (C ≃* Matrix.SpecialLinearGroup (Fin n) K) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have hm : 2 ≤ m := by omega
  have h4 : ¬(m = 2 ∧ Nat.card K = 4) := by omega
  have h3' : ¬(m = 3 ∧ Nat.card K = 3) := by
    rintro ⟨-, hc⟩
    exact h3 hc
  have hsep : CFSG.LieType.Steinberg.CentralExt.SLClosed.Separating m K :=
    CFSG.LieType.Steinberg.CentralExt.SLClosed.separating_of_card
      (m := m) (F := K) hm h2 h4 h3'
  let π : C →* Matrix.SpecialLinearGroup (Fin (m + 1)) K :=
    (CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL (m + 1) K).symm.toMonoidHom.comp
      (eH.toMonoidHom.comp f)
  have hπ : Function.Surjective π :=
    (CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL (m + 1) K).symm.surjective.comp
      (eH.surjective.comp hf)
  have hπker : π.ker ≤ Subgroup.center C := by
    have h1 : π.ker = (eH.toMonoidHom.comp f).ker :=
      MonoidHom.ker_comp_of_injective (eH.toMonoidHom.comp f)
        (CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL (m + 1) K).symm.toMonoidHom
        (CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL (m + 1) K).symm.injective
    have h2' : (eH.toMonoidHom.comp f).ker = f.ker :=
      MonoidHom.ker_comp_of_injective f eH.toMonoidHom eH.injective
    rw [h1, h2']
    exact hfker
  obtain ⟨σ, hσ⟩ :=
    CFSG.LieType.Steinberg.CentralExt.SLClosed.sl_exists_section_of_separating
      (m := m) (F := K) (π := π) hm hsep hπ hπker
  have hkerbot : π.ker = ⊥ :=
    CFSG.LieType.Steinberg.CentralExt.SL2Closed.ker_eq_bot_of_section π hπker σ hσ
  exact ⟨MulEquiv.ofBijective π ⟨(MonoidHom.ker_eq_bot_iff π).1 hkerbot, hπ⟩⟩

private theorem s16sl_card_four_or_eight {K : Type} [Finite K] {a : ℕ}
    (ha : a = 2 ∨ a = 3) (hK : Nat.card K = 2 ^ a) :
    Nat.card K = 4 ∨ Nat.card K = 8 := by
  rcases ha with rfl | rfl
  · left
    norm_num at hK
    exact hK
  · right
    norm_num at hK
    exact hK

private theorem s16sl_center_eq_bot_of_card
    {C : Type} [Group C] {K : Type} [Field K] [Finite K]
    (e : C ≃* Matrix.SpecialLinearGroup (Fin 4) K)
    (hcard : Nat.card K = 4 ∨ Nat.card K = 8) :
    Subgroup.center C = ⊥ := by
  have hcenter : Nat.card (Subgroup.center (Matrix.SpecialLinearGroup (Fin 4) K)) = 1 := by
    rw [CFSG.OrderReductions.LinearOrders.card_specialLinear_center K 4 (by norm_num)]
    rcases hcard with h | h <;> rw [h] <;> norm_num
  have hcenterC : Nat.card (Subgroup.center C) = 1 := by
    have h := Nat.card_congr (Subgroup.centerCongr e).toEquiv
    rwa [hcenter] at h
  exact (Subgroup.card_eq_one).1 hcenterC

private theorem s16sl_two_le_pRank_of_SL4
    {C : Type} [Group C] [Finite C] {K : Type} [Field K] [Finite K] [CharP K 2]
    {p : ℕ} (hp : p.Prime) (hpK : p ∣ Nat.card Kˣ)
    (e : C ≃* Matrix.SpecialLinearGroup (Fin 4) K) :
    2 ≤ CFSG.Open.pRank p (⊤ : Subgroup C) := by
  have hkerSL : e.symm.toMonoidHom.ker ≤
      Subgroup.center (Matrix.SpecialLinearGroup (Fin 4) K) := by
    have hker : e.symm.toMonoidHom.ker = ⊥ :=
      (MonoidHom.ker_eq_bot_iff e.symm.toMonoidHom).2 e.symm.injective
    rw [hker]
    exact bot_le
  have hloc : 2 ≤ CFSG.Assembly.RankThreeEven.localRank p C :=
    CFSG.RankThree.PartOne.KFU.le_localRank_of_surjective_torus
      (K := K) (r := p) (m := 2) (n := 4) hp hpK (by norm_num) (by norm_num)
      (Or.inl (by norm_num)) (ρ := e.symm.toMonoidHom) (hρ := e.symm.surjective)
      (hker := hkerSL)
  have h := CFSG.AGLEmbedding.KFactProofs.CoverFive.localRank_le_pRank (G := C) hp
  exact hloc.trans h

private theorem s16sl_four_le_pRank_of_SLn
    {C : Type} [Group C] [Finite C] {K : Type} [Field K] [Finite K] [CharP K 2]
    {n p : ℕ} (e : C ≃* Matrix.SpecialLinearGroup (Fin n) K)
    (hp : p.Prime) (hpK : p ∣ Nat.card Kˣ)
    (hn : 5 ≤ n) (hcen : 5 < n ∨ ¬ p ∣ n) :
    4 ≤ CFSG.Open.pRank p (⊤ : Subgroup C) := by
  have hkerSL : e.symm.toMonoidHom.ker ≤
      Subgroup.center (Matrix.SpecialLinearGroup (Fin n) K) := by
    have hker : e.symm.toMonoidHom.ker = ⊥ :=
      (MonoidHom.ker_eq_bot_iff e.symm.toMonoidHom).2 e.symm.injective
    rw [hker]
    exact bot_le
  have hloc : 4 ≤ CFSG.Assembly.RankThreeEven.localRank p C :=
    CFSG.RankThree.PartOne.KFU.le_localRank_of_surjective_torus
      (K := K) (r := p) (m := 4) (n := n) hp hpK (by omega) (by omega) hcen
      (ρ := e.symm.toMonoidHom) (hρ := e.symm.surjective) (hker := hkerSL)
  have h := CFSG.AGLEmbedding.KFactProofs.CoverFive.localRank_le_pRank (G := C) hp
  exact hloc.trans h

private theorem s16sl_false_of_four_le_pRank
    (c : S168e3Ctx D V₀ V L hV) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (h : 4 ≤ CFSG.Open.pRank p (⊤ : Subgroup (Bar2 D.M))) : False := by
  have hbarM : CFSG.AGLEmbedding.barM D.M D.M = ⊤ := by
    rw [CFSG.AGLEmbedding.barM, Subgroup.subgroupOf_self]
    exact Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective _)
  have hM : 4 ≤ CFSG.Open.pRank p D.M := by
    have hquot : CFSG.Open.pRank p (⊤ : Subgroup (Bar2 D.M)) =
        CFSG.Open.pRank p D.M := by
      have hbar := CFSG.AGLEmbedding.pRank_barM_eq (G := G) hp hp2 D.M D.M le_rfl
      rwa [hbarM] at hbar
    rwa [hquot] at h
  have hle : CFSG.Open.pRank p D.M ≤ CFSG.Open.evenRank G :=
    CFSG.RankThreeCoreUniqueness.Helpers.local_pRank_le_evenRank p hp hp2 D.M D.maxLocal.1
  rw [c.std.h3] at hle
  omega

private theorem s16sl_false_of_sl_four_component
    (c : S168e3Ctx D V₀ V L hV)
    (hcomp : IsComponentOf (lBar V₀ V hV L) (Mbar D.M V₀ V hV))
    {a : ℕ} (ha : a = 2 ∨ a = 3)
    (hSL : IsSLn ↥(lBar V₀ V hV L) 4 a)
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hpd : p ∣ 2 ^ a - 1)
    (hs : s15 D.M V₀ V hV L ≠ 1) : False := by
  classical
  let H : Subgroup (MulAut (Vtil V₀ V hV)) := lBar V₀ V hV L
  have hcompH : IsComponentOf H (Mbar D.M V₀ V hV) := hcomp
  have hHne : H ≠ ⊥ := c.ne
  obtain ⟨ψ, hψ⟩ := exists_barLift_of_hyp125 c.setting.hyp16.hyp125
  obtain ⟨C, hCcomp, hCmap, f, hf, hfker⟩ :=
    s16sl_exists_actual_cover c hcompH hHne ψ hψ
  have : Group.IsPerfect ↥C := hCcomp.1.1
  obtain ⟨K, hKf, hKfin, hKcard, ⟨eH⟩⟩ := hSL
  let : Field K := hKf
  let : Finite K := hKfin
  have hcard48 : Nat.card K = 4 ∨ Nat.card K = 8 :=
    s16sl_card_four_or_eight ha hKcard
  have hcard2 : Nat.card K ≠ 2 := by rcases hcard48 with h | h <;> omega
  have hcard3 : Nat.card K ≠ 3 := by rcases hcard48 with h | h <;> omega
  obtain ⟨eC⟩ := s16sl_equiv_of_stated f hf hfker (by norm_num) eH hcard2 hcard3
  have hcenterC : Subgroup.center ↥C = ⊥ :=
    s16sl_center_eq_bot_of_card eC hcard48
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : CharP K 2 := CFSG.SectionRank.ClassicalOdd.charP_of_card (p := 2) (f := a) hKcard
  have hKunits : p ∣ Nat.card Kˣ := by
    rw [Nat.card_units K, hKcard]
    exact hpd
  have hCrankTop : 2 ≤ CFSG.Open.pRank p (⊤ : Subgroup ↥C) :=
    s16sl_two_le_pRank_of_SL4 (K := K) hp hKunits eC
  have hCrank : 2 ≤ CFSG.Open.pRank p C := by
    rw [CFSG.SectionRank.pRank_eq_pRank_top_subgroup (p := p) C]
    exact hCrankTop
  have hs15 : s15 D.M V₀ V hV L =
      (conjSet (lBar V₀ V hV L) (Mbar D.M V₀ V hV)).ncard := rfl
  have hS : 1 < (conjSet (lBar V₀ V hV L) (Mbar D.M V₀ V hV)).ncard := by
    have hs1 : 1 ≤ s15 D.M V₀ V hV L := Om8Excl.one_le_s15 D.M V₀ V hV L
    rw [← hs15]
    omega
  obtain ⟨H', hH'mem, hH'ne⟩ :=
    Set.exists_ne_of_one_lt_ncard hS (lBar V₀ V hV L)
  obtain ⟨φ, hφM, hH'eq⟩ := hH'mem
  have hcompH' : IsComponentOf H' (Mbar D.M V₀ V hV) := by
    rw [hH'eq]
    exact CFSG.Quasithin.F918V5G.isComponentOf_map_conj hcompH hφM
  have hH'bot : H' ≠ ⊥ := by
    rw [hH'eq]
    intro hbot
    exact hHne ((Subgroup.map_eq_bot_iff_of_injective H
      (MulAut.conj φ).injective).1 hbot)
  obtain ⟨C', hC'comp, hC'map, f', hf', hf'ker⟩ :=
    s16sl_exists_actual_cover c hcompH' hH'bot ψ hψ
  have : Group.IsPerfect ↥C' := hC'comp.1.1
  have eH' : ↥H' ≃* ↥(StatedSL 4 K) := by
    rw [hH'eq]
    exact (H.equivMapOfInjective (MulAut.conj φ).toMonoidHom
      (MulAut.conj φ).injective).symm.trans eH
  obtain ⟨eC'⟩ := s16sl_equiv_of_stated f' hf' hf'ker (by norm_num) eH' hcard2 hcard3
  have hC'rankTop : 2 ≤ CFSG.Open.pRank p (⊤ : Subgroup ↥C') :=
    s16sl_two_le_pRank_of_SL4 (K := K) hp hKunits eC'
  have hC'rank : 2 ≤ CFSG.Open.pRank p C' := by
    rw [CFSG.SectionRank.pRank_eq_pRank_top_subgroup (p := p) C']
    exact hC'rankTop
  have hCne : C ≠ C' := by
    intro heq
    have hmap : C.map ψ = C'.map ψ := congrArg (fun X => X.map ψ) heq
    rw [hCmap, hC'map] at hmap
    exact hH'ne hmap.symm
  have hcommC : C ≤ Subgroup.centralizer (C' : Set (Bar2 D.M)) :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.mp
      ((CFSG.LocalCores.distinct_components_commute hCcomp hC'comp).resolve_left hCne)
  have hcommute : ∀ x ∈ C, ∀ y ∈ C', x * y = y * x := by
    intro x hx y hy
    exact (Subgroup.mem_centralizer_iff.mp (hcommC hx) y hy).symm
  have hinf : C ⊓ C' = ⊥ :=
    CFSG.RankThree.PartTwo.Sec11.compJ3_inf_eq_bot hCcomp hC'comp hCne
      (by simpa using hcenterC)
  have hcop : Nat.Coprime p (Nat.card ↥(C ⊓ C')) := by
    rw [hinf, Subgroup.card_bot]
    simp
  have hadd := CFSG.AGLEmbedding.pRank_add_le_pRank_sup_of_coprime
    (q := p) hp hcommute hcop
  have hsup : 4 ≤ CFSG.Open.pRank p (C ⊔ C') := by
    have h2 : 2 + 2 ≤ CFSG.Open.pRank p (C ⊔ C') :=
      (add_le_add hCrank hC'rank).trans hadd
    simpa using h2
  have hbar : 4 ≤ CFSG.Open.pRank p (⊤ : Subgroup (Bar2 D.M)) :=
    hsup.trans (CFSG.SectionRank.pRank_mono (p := p) hp.one_lt le_top)
  exact s16sl_false_of_four_le_pRank c hp hp2 hbar

private theorem s16sl_false_of_sl_ge_five_component
    (c : S168e3Ctx D V₀ V L hV)
    (hcomp : IsComponentOf (lBar V₀ V hV L) (Mbar D.M V₀ V hV))
    {n a : ℕ} (ha : a = 2 ∨ a = 3) (hn : 5 ≤ n)
    (hSL : IsSLn ↥(lBar V₀ V hV L) n a)
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hpd : p ∣ 2 ^ a - 1)
    (hcen : 5 < n ∨ ¬ p ∣ n) : False := by
  classical
  let H : Subgroup (MulAut (Vtil V₀ V hV)) := lBar V₀ V hV L
  have hcompH : IsComponentOf H (Mbar D.M V₀ V hV) := hcomp
  have hHne : H ≠ ⊥ := c.ne
  obtain ⟨ψ, hψ⟩ := exists_barLift_of_hyp125 c.setting.hyp16.hyp125
  obtain ⟨C, hCcomp, - , f, hf, hfker⟩ :=
    s16sl_exists_actual_cover c hcompH hHne ψ hψ
  have : Group.IsPerfect ↥C := hCcomp.1.1
  obtain ⟨K, hKf, hKfin, hKcard, ⟨eH⟩⟩ := hSL
  let : Field K := hKf
  let : Finite K := hKfin
  have hcard48 : Nat.card K = 4 ∨ Nat.card K = 8 :=
    s16sl_card_four_or_eight ha hKcard
  have hcard2 : Nat.card K ≠ 2 := by rcases hcard48 with h | h <;> omega
  have hcard3 : Nat.card K ≠ 3 := by rcases hcard48 with h | h <;> omega
  obtain ⟨eC⟩ := s16sl_equiv_of_stated f hf hfker (by omega) eH hcard2 hcard3
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : CharP K 2 := CFSG.SectionRank.ClassicalOdd.charP_of_card (p := 2) (f := a) hKcard
  have hKunits : p ∣ Nat.card Kˣ := by
    rw [Nat.card_units K, hKcard]
    exact hpd
  have hCrankTop : 4 ≤ CFSG.Open.pRank p (⊤ : Subgroup ↥C) :=
    s16sl_four_le_pRank_of_SLn (K := K) eC hp hKunits hn hcen
  have hCrank : 4 ≤ CFSG.Open.pRank p C := by
    rw [CFSG.SectionRank.pRank_eq_pRank_top_subgroup (p := p) C]
    exact hCrankTop
  have hbar : 4 ≤ CFSG.Open.pRank p (⊤ : Subgroup (Bar2 D.M)) :=
    hCrank.trans (CFSG.SectionRank.pRank_mono (p := p) hp.one_lt le_top)
  exact s16sl_false_of_four_le_pRank c hp hp2 hbar

theorem s168e3_false_of_sl_component_field_four_eight_ge_five
    (c : S168e3Ctx D V₀ V L hV)
    (hcomp : IsComponentOf (lBar V₀ V hV L) (Mbar D.M V₀ V hV))
    {n a : ℕ} (ha : a = 2 ∨ a = 3) (hn : 5 ≤ n)
    (hSL : IsSLn ↥(lBar V₀ V hV L) n a) : False := by
  rcases ha with rfl | rfl
  · refine s16sl_false_of_sl_ge_five_component c hcomp (Or.inl rfl) hn hSL
      (p := 3) (by norm_num) (by norm_num) (by norm_num) ?_
    by_cases h5 : 5 < n
    · exact Or.inl h5
    · right
      have hn5 : n = 5 := by omega
      rw [hn5]
      norm_num
  · refine s16sl_false_of_sl_ge_five_component c hcomp (Or.inr rfl) hn hSL
      (p := 7) (by norm_num) (by norm_num) (by norm_num) ?_
    by_cases h5 : 5 < n
    · exact Or.inl h5
    · right
      have hn5 : n = 5 := by omega
      rw [hn5]
      norm_num

theorem s15_eq_one_of_sl_four_component_field_four_eight
    (c : S168e3Ctx D V₀ V L hV)
    (hcomp : IsComponentOf (lBar V₀ V hV L) (Mbar D.M V₀ V hV))
    {a : ℕ} (ha : a = 2 ∨ a = 3)
    (hSL : IsSLn ↥(lBar V₀ V hV L) 4 a) :
    s15 D.M V₀ V hV L = 1 := by
  by_contra hs
  rcases ha with rfl | rfl
  · exact s16sl_false_of_sl_four_component c hcomp (Or.inl rfl) hSL
      (p := 3) (by norm_num) (by norm_num) (by norm_num) hs
  · exact s16sl_false_of_sl_four_component c hcomp (Or.inr rfl) hSL
      (p := 7) (by norm_num) (by norm_num) (by norm_num) hs

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
