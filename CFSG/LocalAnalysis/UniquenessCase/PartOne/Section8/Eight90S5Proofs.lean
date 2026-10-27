module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight90S5
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight90S123
import CFSG.Quasithin.EmptyFaithful.S146zMListCl
import CFSG.GH74.Generic.S1.SymLift
import CFSG.GroupTheory.ChiefSectionPGroup
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight90Sz5Holds
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.SuzukiCrossCharReduction
import CFSG.GroupTheory.CoprimeActionSupport.NormalSubgroupSylowJoin
import CFSG.GH74.GLS.Stage4.Q9.SylowEnd
import CFSG.GroupTheory.ABGLocalTools.SylowNormalizerGrows
public import CFSG.CGT.PushingUpLit.Transport
public import CFSG.GroupTheory.ABGLocalTools.PStabilityModule
public import CFSG.GroupTheory.Commutator.ThreeSubgroupsModNormal
public import CFSG.GroupTheory.PerfectActionCritical
public import CFSG.LieType.SteinbergBRMulEquivCores
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.EvenBN.GMSK.SzFacts
public import CFSG.LocalAnalysis.SeitzReduction.EPilotPosition
public import CFSG.Quasithin.EmptyFaithful.S1422Basic
public import CFSG.RankThree.PartTwo.Sec3.TwoThreeStructure
public import CFSG.SignalizerFunctorTheorem.Nonsolvable.SolComponent.Radical

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8

section R90D3

open Subgroup CFSG.Open CFSG.LocalAnalysis.UniquenessCase CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.Blueprint (LieModel)

private theorem r90d3_three_dvd {S : Type} [Group S] {Q : Prop}
    (h : (∃ p : ℕ, p.Prime ∧ p ≠ 2 ∧ (LieModel S .PSL 2 p 1 ∨ LieModel S .PSL 3 p 1)) ∨
      IsAlt S 6 ∨ IsAlt S 7 ∨
      ((∃ p : ℕ, p.Prime ∧ p ≠ 2 ∧ (LieModel S .PSp 2 p 1 ∨ LieModel S .PSL 2 p 2)) ∧ Q)) :
    3 ∣ Nat.card S := by
  have alt : ∀ n : ℕ, 5 ≤ n → n ≤ 8 → Nonempty (S ≃* alternatingGroup (Fin n)) →
      3 ∣ Nat.card S := by
    intro n h5 h8 ⟨e⟩
    have : Nontrivial (Fin n) :=
      ⟨⟨0, by omega⟩, ⟨1, by omega⟩, fun h => by simpa using congrArg Fin.val h⟩
    rw [Nat.card_congr e.toEquiv, nat_card_alternatingGroup, Nat.card_fin]
    interval_cases n <;> decide
  rcases h with ⟨p, -, -, h | h⟩ | h | h | ⟨⟨p, -, -, h | h⟩, -⟩
  · exact CFSG.Quasithin.three_dvd_card_psl_model (h.statedClassicalModel (by decide))
  · exact CFSG.Quasithin.three_dvd_card_psl_model (h.statedClassicalModel (by decide))
  · exact alt 6 (by norm_num) (by norm_num) h
  · exact alt 7 (by norm_num) (by norm_num) h
  · exact CFSG.Quasithin.three_dvd_card_psp_model (h.statedClassicalModel (by decide))
  · exact CFSG.Quasithin.three_dvd_card_psl_model (h.statedClassicalModel (by decide))

private theorem r90d3_equiv_quotient {G L : Type} [Group G] [Finite G] [Group L] [Finite L]
    [Nontrivial (G ⧸ CFSG.solvableRadical G)]
    (f : L →* G ⧸ CFSG.solvableRadical G) (hf : Function.Surjective f)
    (hS : IsSimpleGroup (L ⧸ CFSG.pCore 2 L)) :
    Nonempty ((L ⧸ CFSG.pCore 2 L) ≃* (G ⧸ CFSG.solvableRadical G)) := by
  have h2 : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hP : (CFSG.pCore 2 L).map f ≤ CFSG.solvableRadical (G ⧸ CFSG.solvableRadical G) := by
    refine CFSG.SignalizerFunctorTheorem.Nonsolvable.le_solvableRadical
      (Subgroup.Normal.map inferInstance f hf) ?_
    have hp : IsPGroup 2 ((CFSG.pCore 2 L).map f) :=
      (CFSG.pCore_isPGroup (p := 2) (G := L)).map f
    have : Group.IsNilpotent ((CFSG.pCore 2 L).map f) := hp.isNilpotent
    infer_instance
  rw [CFSG.SignalizerFunctorTheorem.Nonsolvable.solvableRadical_quotient, le_bot_iff,
    Subgroup.map_eq_bot_iff] at hP
  let g : L ⧸ CFSG.pCore 2 L →* G ⧸ CFSG.solvableRadical G := QuotientGroup.lift _ f hP
  have hg : Function.Surjective g := by
    intro s
    obtain ⟨l, rfl⟩ := hf s
    exact ⟨QuotientGroup.mk l, rfl⟩
  have hker : g.ker = ⊥ := by
    rcases hS.eq_bot_or_eq_top_of_normal g.ker with h | h
    · exact h
    · exfalso
      obtain ⟨a, b, hab⟩ :=
        (inferInstance : Nontrivial (G ⧸ CFSG.solvableRadical G)).exists_pair_ne
      obtain ⟨a', rfl⟩ := hg a
      obtain ⟨b', rfl⟩ := hg b
      apply hab
      have h1 : g a' = 1 := by rw [← MonoidHom.mem_ker, h]; trivial
      have h2 : g b' = 1 := by rw [← MonoidHom.mem_ker, h]; trivial
      rw [h1, h2]
  exact ⟨MulEquiv.ofBijective g ⟨(MonoidHom.ker_eq_bot_iff g).1 hker, hg⟩⟩

private theorem r90d3_radical_le_center {G : Type} [Group G] [Finite G] [Group.IsPerfect G]
    (hS : IsSimpleGroup (G ⧸ CFSG.solvableRadical G))
    (hc : ¬ centralizer ((CFSG.solvableRadical G : Subgroup G) : Set G) ≤
      CFSG.solvableRadical G) :
    CFSG.solvableRadical G ≤ center G := by
  set R : Subgroup G := CFSG.solvableRadical G with hR
  have hRs : Group.IsSolvable R :=
    CFSG.SignalizerFunctorTheorem.Nonsolvable.isSolvable_solvableRadical
  set C : Subgroup G := centralizer (R : Set G) with hC
  have hCn : C.Normal := inferInstance
  have hmap : C.map (QuotientGroup.mk' R) = ⊤ := by
    have : (C.map (QuotientGroup.mk' R)).Normal :=
      Subgroup.Normal.map inferInstance _ (QuotientGroup.mk'_surjective R)
    rcases hS.eq_bot_or_eq_top_of_normal (C.map (QuotientGroup.mk' R)) with h | h
    · exfalso
      apply hc
      intro c hcC
      have hmem : QuotientGroup.mk' R c ∈ C.map (QuotientGroup.mk' R) :=
        Subgroup.mem_map_of_mem _ hcC
      rw [h, Subgroup.mem_bot, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hmem
      exact hmem
    · exact h
  have hsurj : Function.Surjective ((QuotientGroup.mk' C).comp R.subtype) := by
    intro q
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective q
    have hg : QuotientGroup.mk' R g ∈ C.map (QuotientGroup.mk' R) := by rw [hmap]; trivial
    obtain ⟨c, hcC, hcg⟩ := Subgroup.mem_map.mp hg
    rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq] at hcg
    refine ⟨⟨c⁻¹ * g, hcg⟩, ?_⟩
    simp only [MonoidHom.comp_apply, Subgroup.coe_subtype, QuotientGroup.mk'_apply]
    rw [QuotientGroup.eq]
    simpa [mul_assoc] using hCn.conj_mem' c hcC g
  have : Group.IsSolvable (G ⧸ C) := Group.isSolvable_of_surjective hsurj
  have hCtop : C = ⊤ := by
    by_contra hne
    rw [Subgroup.eq_top_iff'] at hne
    obtain ⟨g, hg⟩ := not_forall.mp hne
    have : Nontrivial (G ⧸ C) :=
      ⟨⟨QuotientGroup.mk g, 1, fun h => hg ((QuotientGroup.eq_one_iff g).1 h)⟩⟩
    exact Group.IsPerfect.not_isSolvable (G ⧸ C) inferInstance
  intro r hr
  refine Subgroup.mem_center_iff.mpr fun g => ?_
  have hgC : g ∈ C := hCtop ▸ Subgroup.mem_top g
  exact (Subgroup.mem_centralizer_iff.mp hgC r hr).symm

private theorem r90d3_pCoreOf_radical {D : Type} [Group D] [Finite D] :
    pCoreOf 2 (CFSG.solvableRadical (D ⧸ CFSG.pCore 2 D)) = ⊥ := by
  have h2 : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set R : Subgroup (D ⧸ CFSG.pCore 2 D) := CFSG.solvableRadical (D ⧸ CFSG.pCore 2 D) with hR
  have hNR : normalizer (R : Set (D ⧸ CFSG.pCore 2 D)) = ⊤ :=
    Subgroup.normalizer_eq_top_iff.mpr inferInstance
  have hn : (pCoreOf 2 R).Normal := by
    refine Subgroup.normalizer_eq_top_iff.mp (top_le_iff.mp ?_)
    rw [← hNR]
    exact CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 R
  have hle : pCoreOf 2 R ≤ CFSG.pCore 2 (D ⧸ CFSG.pCore 2 D) :=
    CFSG.LieType.BorelTits.le_pCore 2 hn (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 R)
  rw [CFSG.ABGLocalTools.pCore_quotient_pCore_eq_bot] at hle
  exact le_bot_iff.mp hle

private theorem r90d3_card_pCore_not_dvd {D : Type} [Group D] [Finite D] {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) : ¬ p ∣ Nat.card (CFSG.pCore 2 D) := by
  have h2 : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨k, hk⟩ := (IsPGroup.iff_card).mp (CFSG.pCore_isPGroup (p := 2) (G := D))
  rw [hk]
  intro h
  exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp (hp.dvd_of_dvd_pow h))

private theorem r90d3_rank_radical {D : Type} [Group D] [Finite D]
    (hrank : ∀ p : ℕ, p.Prime → p ≠ 2 → CFSG.Open.pRank p (⊤ : Subgroup D) ≤ 3) :
    ∀ p : ℕ, p.Prime → p ≠ 2 →
      CFSG.Open.pRank p (CFSG.solvableRadical (D ⧸ CFSG.pCore 2 D)) ≤ 3 := by
  intro p hp hp2
  have : Fact p.Prime := ⟨hp⟩
  calc CFSG.Open.pRank p (CFSG.solvableRadical (D ⧸ CFSG.pCore 2 D))
      ≤ CFSG.Open.pRank p (⊤ : Subgroup (D ⧸ CFSG.pCore 2 D)) :=
        CFSG.SectionRank.pRank_mono hp.one_lt le_top
    _ = CFSG.Open.pRank p (⊤ : Subgroup D) :=
        CFSG.SectionRank.pRank_quotient_eq _ (r90d3_card_pCore_not_dvd hp hp2)
    _ ≤ 3 := hrank p hp hp2

private theorem r90d3_map_le_radical {D : Type} [Group D] [Finite D] (U : Subgroup D) [U.Normal]
    (hU : Odd (Nat.card U)) :
    U.map (QuotientGroup.mk' (CFSG.pCore 2 D)) ≤ CFSG.solvableRadical (D ⧸ CFSG.pCore 2 D) := by
  have : Group.IsSolvable U := CFSG.FeitThompson.isSolvable_of_odd_natCard U hU
  refine CFSG.SignalizerFunctorTheorem.Nonsolvable.le_solvableRadical
    (Subgroup.Normal.map inferInstance _ (QuotientGroup.mk'_surjective _)) ?_
  exact Group.isSolvable_of_surjective
    ((QuotientGroup.mk' (CFSG.pCore 2 D)).subgroupMap_surjective U)

private theorem r90d3_nontrivial {D L : Type} [Group D] [Finite D] [Group L] [Finite L]
    (ι : L →* D) (hι : Function.Injective ι) (hS : IsSimpleGroup (L ⧸ CFSG.pCore 2 L))
    (hnc : ∃ a b : L ⧸ CFSG.pCore 2 L, a * b ≠ b * a) :
    Nontrivial ((D ⧸ CFSG.pCore 2 D) ⧸ CFSG.solvableRadical (D ⧸ CFSG.pCore 2 D)) := by
  have h2 : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_contra hnt
  have hsub := not_nontrivial_iff_subsingleton.mp hnt
  have hRtop : CFSG.solvableRadical (D ⧸ CFSG.pCore 2 D) = ⊤ := by
    rw [Subgroup.eq_top_iff']
    intro g
    exact (QuotientGroup.eq_one_iff g).1 (Subsingleton.elim _ _)
  have hRs := CFSG.SignalizerFunctorTheorem.Nonsolvable.isSolvable_solvableRadical
    (G := D ⧸ CFSG.pCore 2 D)
  rw [hRtop] at hRs
  have hGs : Group.IsSolvable (D ⧸ CFSG.pCore 2 D) :=
    Group.isSolvable_of_surjective (f := (Subgroup.topEquiv : (⊤ : Subgroup (D ⧸ CFSG.pCore 2 D)) ≃*
      (D ⧸ CFSG.pCore 2 D)).toMonoidHom) Subgroup.topEquiv.surjective
  have : Group.IsSolvable (CFSG.pCore 2 D) := by
    have : Group.IsNilpotent (CFSG.pCore 2 D) := (CFSG.pCore_isPGroup (p := 2) (G := D)).isNilpotent
    infer_instance
  have : Group.IsSolvable D := Group.isSolvable_of_subgroup_quotient (CFSG.pCore 2 D)
  have : Group.IsSolvable L := Group.isSolvable_of_isSolvable_injective hι
  have := hS
  exact hnc.elim fun a hb => hb.elim fun b hab =>
    hab (IsSimpleGroup.comm_iff_isSolvable.mpr inferInstance a b)

private theorem r90d3_core (hK : UCK.K318) {D L : Type} [Group D] [Finite D] [Group L] [Finite L]
    (hKD : CFSG.Open.IsKGroup D)
    (hrank : ∀ p : ℕ, p.Prime → p ≠ 2 → CFSG.Open.pRank p (⊤ : Subgroup D) ≤ 3)
    [Group.IsPerfect D] (ι : L →* D) (hι : Function.Injective ι) {n : ℕ}
    (hSz : IsSz (L ⧸ CFSG.pCore 2 L) n) (U : Subgroup D) [U.Normal] (hU : Odd (Nat.card U))
    (hLU : ι.range ⊔ U = ⊤) : U ≤ center D := by
  have h2 : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hSimple : IsSimpleGroup (L ⧸ CFSG.pCore 2 L) :=
    CFSG.LocalAnalysis.EvenBN.GMSK.isSimpleGroup_of_lieModel_twistedB2 hSz
  have hnc := CFSG.LocalAnalysis.EvenBN.GMSK.exists_mul_ne_of_lieModel_twistedB2 hSz
  have hKG : CFSG.Open.IsKGroup (D ⧸ CFSG.pCore 2 D) := hKD.quotient _
  have := r90d3_nontrivial ι hι hSimple hnc
  let f : L →* (D ⧸ CFSG.pCore 2 D) ⧸ CFSG.solvableRadical (D ⧸ CFSG.pCore 2 D) :=
    (QuotientGroup.mk' _).comp ((QuotientGroup.mk' (CFSG.pCore 2 D)).comp ι)
  have hf : Function.Surjective f := by
    intro s
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective s
    obtain ⟨d, rfl⟩ := QuotientGroup.mk_surjective g
    have hd : d ∈ ι.range ⊔ U := by rw [hLU]; trivial
    obtain ⟨y, ⟨l, rfl⟩, z, hz, rfl⟩ := Subgroup.mem_sup_of_normal_right.mp hd
    refine ⟨l, ?_⟩
    have hzR : (QuotientGroup.mk z : D ⧸ CFSG.pCore 2 D) ∈
        CFSG.solvableRadical (D ⧸ CFSG.pCore 2 D) :=
      r90d3_map_le_radical U hU (Subgroup.mem_map_of_mem (QuotientGroup.mk' _) hz)
    have hz1 : ((QuotientGroup.mk z : D ⧸ CFSG.pCore 2 D) :
        (D ⧸ CFSG.pCore 2 D) ⧸ CFSG.solvableRadical (D ⧸ CFSG.pCore 2 D)) = 1 :=
      (QuotientGroup.eq_one_iff _).mpr hzR
    simp only [f, MonoidHom.comp_apply, QuotientGroup.mk'_apply]
    rw [QuotientGroup.mk_mul, QuotientGroup.mk_mul, hz1, mul_one]
  obtain ⟨e⟩ := r90d3_equiv_quotient f hf hSimple
  have hSsimple : IsSimpleGroup
      ((D ⧸ CFSG.pCore 2 D) ⧸ CFSG.solvableRadical (D ⧸ CFSG.pCore 2 D)) := by
    have := hSimple
    exact e.symm.isSimpleGroup
  have h3 : ¬ 3 ∣ Nat.card
      ((D ⧸ CFSG.pCore 2 D) ⧸ CFSG.solvableRadical (D ⧸ CFSG.pCore 2 D)) := by
    rw [← Nat.card_congr e.toEquiv]
    exact CFSG.LocalAnalysis.EvenBN.GMSK.not_three_dvd_card_of_lieModel_twistedB2 hSz
  have hc : ¬ centralizer ((CFSG.solvableRadical (D ⧸ CFSG.pCore 2 D) :
      Subgroup (D ⧸ CFSG.pCore 2 D)) : Set (D ⧸ CFSG.pCore 2 D)) ≤
      CFSG.solvableRadical (D ⧸ CFSG.pCore 2 D) := fun hc =>
    h3 (r90d3_three_dvd (hK _ hKG (Group.isPerfect_def.mp inferInstance) r90d3_pCoreOf_radical
      hSsimple (r90d3_rank_radical hrank) hc).1)
  have hcen := r90d3_radical_le_center hSsimple hc
  intro u hu
  refine Subgroup.mem_center_iff.mpr fun d => ?_
  have hmk := hcen (r90d3_map_le_radical U hU (Subgroup.mem_map_of_mem (QuotientGroup.mk' _) hu))
  have hcomm := Subgroup.mem_center_iff.mp hmk (QuotientGroup.mk d)
  have hx : (d * u)⁻¹ * (u * d) ∈ CFSG.pCore 2 D := by
    rw [← QuotientGroup.eq, QuotientGroup.mk_mul, QuotientGroup.mk_mul]
    exact hcomm
  have hxU : (d * u)⁻¹ * (u * d) ∈ U := by
    have : (d * u)⁻¹ * (u * d) = u⁻¹ * (d⁻¹ * u * d) := by group
    rw [this]
    exact U.mul_mem (U.inv_mem hu) (Subgroup.Normal.conj_mem' inferInstance u hu d)
  obtain ⟨k, hk⟩ := (IsPGroup.iff_card).mp (CFSG.pCore_isPGroup (p := 2) (G := D))
  have hdisj : Disjoint U (CFSG.pCore 2 D) :=
    Subgroup.disjoint_of_coprime_natCard (by
      rw [hk]; exact Nat.Coprime.pow_right k (Nat.coprime_two_right.mpr hU))
  have hx1 : (d * u)⁻¹ * (u * d) = 1 := by
    have := hdisj.le_bot ⟨hxU, hx⟩
    simpa using this
  exact inv_mul_eq_one.mp hx1

private theorem r90d3_sup_eq_top {X : Type} [Group X] {O Ls D : Subgroup X} [O.Normal]
    (hLD : Ls ≤ D) (hDH : D ≤ O ⊔ Ls) :
    (Subgroup.inclusion hLD).range ⊔ O.subgroupOf D = ⊤ := by
  rw [eq_top_iff, sup_comm]
  intro d _
  obtain ⟨o, ho, l, hl, hol⟩ := (Subgroup.mem_sup_of_normal_left (s := O) (t := Ls)).mp (hDH d.2)
  have hoD : o ∈ D := by
    have : o = (d : X) * l⁻¹ := by rw [← hol]; group
    rw [this]
    exact D.mul_mem d.2 (D.inv_mem (hLD hl))
  have hd : d = ⟨o, hoD⟩ * Subgroup.inclusion hLD ⟨l, hl⟩ := Subtype.ext (by simp [hol])
  rw [hd]
  exact Subgroup.mul_mem_sup (Subgroup.mem_subgroupOf.mpr ho) ⟨⟨l, hl⟩, rfl⟩

private theorem r90d3_odd_subgroupOf {X : Type} [Group X] [Finite X] {O : Subgroup X}
    (hO : Odd (Nat.card O)) (D : Subgroup X) : Odd (Nat.card (O.subgroupOf D)) := by
  let f : O.subgroupOf D →* O :=
    ((D.subtype).comp (O.subgroupOf D).subtype).codRestrict O fun x => x.2
  have hf : Function.Injective f := by
    intro a b hab
    have h1 : ((f a : O) : X) = ((f b : O) : X) := congrArg Subtype.val hab
    exact Subtype.ext (Subtype.ext h1)
  exact hO.of_dvd_nat (Subgroup.card_dvd_of_injective f hf)

theorem r890_lemma5d3 : Lemma5d3_890 := by
  intro hK X _ _ Ls n hKX hrank _ _ hperf hSz
  set O : Subgroup X := CFSG.oddCore X with hO
  set H : Subgroup X := O ⊔ Ls with hH
  set D : Subgroup X := CFSG.RankThreeCoreUniqueness.Helpers.perfectResidualOf H with hD
  have hLD : Ls ≤ D := CFSG.GH74.Generic.S1.le_perfectResidualOf le_sup_right hperf
  have hDH : D ≤ H := Subgroup.map_subtype_le _
  have hDnorm : H ≤ normalizer (D : Set X) :=
    Subgroup.le_normalizer.trans
      (CFSG.RankThreeCoreUniqueness.Helpers.perfectResidualOf_normalizer_contains H)
  have : Group.IsPerfect D :=
    CFSG.RankThreeCoreUniqueness.Helpers.finite_perfectResidualOf_isPerfect H
  have hrk : ∀ p : ℕ, p.Prime → p ≠ 2 → CFSG.Open.pRank p (⊤ : Subgroup D) ≤ 3 := by
    intro p hp hp2
    calc CFSG.Open.pRank p (⊤ : Subgroup D) = CFSG.Open.pRank p D :=
          (CFSG.SectionRank.pRank_eq_pRank_top_subgroup D).symm
      _ ≤ CFSG.Open.pRank p (⊤ : Subgroup X) := CFSG.SectionRank.pRank_mono hp.one_lt le_top
      _ ≤ 3 := hrank p hp hp2
  have hcenter : O.subgroupOf D ≤ center D :=
    r90d3_core hK (hKX.subgroup D) hrk (Subgroup.inclusion hLD) (Subgroup.inclusion_injective hLD)
      hSz (O.subgroupOf D) (r90d3_odd_subgroupOf (CFSG.ABGLocalTools.odd_card_oddCore (H := X)) D)
      (r90d3_sup_eq_top hLD hDH)
  have hcomm : ⁅O, Ls⁆ ≤ centralizer (Ls : Set X) := by
    rw [Subgroup.commutator_le]
    intro o ho l hl
    show o * l * o⁻¹ * l⁻¹ ∈ centralizer (Ls : Set X)
    have hoH : o ∈ H := Subgroup.mem_sup_left ho
    have hc1 : o * l * o⁻¹ * l⁻¹ ∈ D := by
      have h1 : o * l * o⁻¹ ∈ D := (Subgroup.mem_normalizer_iff.mp (hDnorm hoH) l).mp (hLD hl)
      exact D.mul_mem h1 (D.inv_mem (hLD hl))
    have hc2 : o * l * o⁻¹ * l⁻¹ ∈ O := by
      have : o * l * o⁻¹ * l⁻¹ = o * (l * o⁻¹ * l⁻¹) := by group
      rw [this]
      exact O.mul_mem ho (Subgroup.Normal.conj_mem inferInstance o⁻¹ (O.inv_mem ho) l)
    have hcen := hcenter
      (Subgroup.mem_subgroupOf.mpr hc2 : (⟨o * l * o⁻¹ * l⁻¹, hc1⟩ : D) ∈ O.subgroupOf D)
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    exact congrArg Subtype.val (Subgroup.mem_center_iff.mp hcen ⟨y, hLD hy⟩)
  rw [Subgroup.commutator_comm]
  exact r890_commutator_eq_bot_of_perfect hperf hcomm

end R90D3

section R90E1

open Subgroup CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase
open scoped commutatorElement IsMulCommutative

open Module in
private theorem r90e1_three_fix {F V : Type*} [Field F] [AddCommGroup V] [Module F V]
    [FiniteDimensional F V] (h2 : (2 : F) ≠ 0) (a b : V →ₗ[F] V) (ha : a * a = 1)
    (hb : b * b = 1) (hab : a * b = b * a) :
    finrank F V ≤ finrank F (LinearMap.ker (a - 1)) + finrank F (LinearMap.ker (b - 1)) +
      finrank F (LinearMap.ker (a * b - 1)) := by
  have hax : ∀ v, a (a v) = v := fun v => by
    simpa using congrArg (fun f : V →ₗ[F] V => f v) ha
  have hbx : ∀ v, b (b v) = v := fun v => by
    simpa using congrArg (fun f : V →ₗ[F] V => f v) hb
  have habx : ∀ v, a (b v) = b (a v) := fun v => by
    simpa using congrArg (fun f : V →ₗ[F] V => f v) hab
  have hc : (2 : F)⁻¹ * 2 = 1 := inv_mul_cancel₀ h2
  have hcov : (⊤ : Submodule F V) ≤
      LinearMap.ker (a - 1) ⊔ LinearMap.ker (b - 1) ⊔ LinearMap.ker (a * b - 1) := by
    intro w _
    set c : F := (2 : F)⁻¹ with hcdef
    set u : V := c • (w - a w) with hu
    have hau : a u = -u := by
      rw [hu, map_smul, map_sub, hax, ← smul_neg]
      congr 1
      abel
    have hbu : a (b u) = -b u := by
      rw [habx, hau, map_neg]
    have h1 : c • (w + a w) ∈ LinearMap.ker (a - 1) := by
      rw [LinearMap.mem_ker, LinearMap.sub_apply, map_smul, map_add, hax]
      simp [add_comm]
    have h2' : c • (u + b u) ∈ LinearMap.ker (b - 1) := by
      rw [LinearMap.mem_ker, LinearMap.sub_apply, map_smul, map_add, hbx]
      simp [add_comm]
    have h3 : c • (u - b u) ∈ LinearMap.ker (a * b - 1) := by
      rw [LinearMap.mem_ker, LinearMap.sub_apply, Module.End.mul_apply, map_smul, map_sub, hbx,
        map_smul, map_sub, hau, hbu, Module.End.one_apply]
      simp only [smul_sub, smul_neg]
      abel
    have e1 : c • (u + b u) + c • (u - b u) = u := by
      rw [← smul_add]
      have : u + b u + (u - b u) = (2 : F) • u := by rw [two_smul]; abel
      rw [this, smul_smul, hc, one_smul]
    have e2 : c • (w + a w) + u = w := by
      rw [hu, ← smul_add]
      have : w + a w + (w - a w) = (2 : F) • w := by rw [two_smul]; abel
      rw [this, smul_smul, hc, one_smul]
    have hsum : w = (c • (w + a w) + c • (u + b u)) + c • (u - b u) := by
      rw [add_assoc, e1, e2]
    rw [hsum]
    exact Submodule.add_mem_sup (Submodule.add_mem_sup h1 h2') h3
  calc finrank F V = finrank F (⊤ : Submodule F V) := (finrank_top F V).symm
    _ ≤ finrank F (LinearMap.ker (a - 1) ⊔ LinearMap.ker (b - 1) ⊔
          LinearMap.ker (a * b - 1) : Submodule F V) := Submodule.finrank_mono hcov
    _ ≤ finrank F (LinearMap.ker (a - 1) ⊔ LinearMap.ker (b - 1) : Submodule F V) +
          finrank F (LinearMap.ker (a * b - 1)) := Submodule.finrank_add_le_finrank_add_finrank _ _
    _ ≤ (finrank F (LinearMap.ker (a - 1)) + finrank F (LinearMap.ker (b - 1))) +
          finrank F (LinearMap.ker (a * b - 1)) := by
        gcongr
        exact Submodule.finrank_add_le_finrank_add_finrank _ _

private theorem r90e1_eight {X : Type} [Group X] [Finite X] {n : ℕ} (hn : 3 ≤ n)
    (h : IsSz X n) :
    ∃ E : Subgroup X, IsMulCommutative E ∧ (∀ x ∈ E, x ^ 2 = 1) ∧ Nat.card E = 8 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hB := CFSG.LocalAnalysis.EvenBN.GMSK.fusionBenderBorel_of_lieModel_twistedB2 h
  obtain ⟨Q⟩ := (inferInstance : Nonempty (Sylow 2 X))
  obtain ⟨-, -, hsq, hZ, -⟩ := hB Q
  set Z := Subgroup.center (Q : Subgroup X)
  obtain ⟨E, hE⟩ := Sylow.exists_subgroup_card_pow_prime (G := Z) 2 (n := 3)
    (by rw [hZ]; exact pow_dvd_pow 2 hn)
  set f : Z →* X := (Q : Subgroup X).subtype.comp Z.subtype
  have hf : Function.Injective f :=
    (Q : Subgroup X).subtype_injective.comp Z.subtype_injective
  refine ⟨E.map f, ⟨⟨fun a b => ?_⟩⟩, ?_, ?_⟩
  · obtain ⟨x, hx, hxa⟩ := Subgroup.mem_map.mp a.2
    obtain ⟨y, hy, hyb⟩ := Subgroup.mem_map.mp b.2
    apply Subtype.ext
    change (a : X) * b = b * a
    rw [← hxa, ← hyb, ← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (Subgroup.mem_center_iff.mp y.2 (x : Q))
  · rintro _ ⟨x, hx, rfl⟩
    rw [← map_pow]
    have : x ^ 2 = 1 := Subtype.ext (hsq x x.2)
    rw [this, map_one]
  · rw [Subgroup.card_map_of_injective hf, hE]
    norm_num

private theorem r90e1_pair {R : Type} [Group R] [Finite R] (h : 2 ≤ twoRank R) :
    ∃ a b : R, orderOf a = 2 ∧ orderOf b = 2 ∧ a ≠ b ∧ Commute a b := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨E, -, ⟨hcomm, hsq⟩, hcard⟩ :=
    CFSG.SectionRank.exists_pRank (G := R) (p := 2) (by norm_num) ⊤
  have h' : 2 ≤ CFSG.Open.pRank 2 (⊤ : Subgroup R) := h
  have h4 : 4 ≤ Nat.card E := by
    rw [hcard]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ CFSG.Open.pRank 2 (⊤ : Subgroup R) := Nat.pow_le_pow_right (by norm_num) h'
  obtain ⟨a, haE, ha1⟩ : ∃ a ∈ E, a ≠ 1 := by
    by_contra hno
    push Not at hno
    have : E = ⊥ := eq_bot_iff.mpr fun a ha => Subgroup.mem_bot.mpr (hno a ha)
    rw [this, Subgroup.card_bot] at h4
    omega
  have hao : orderOf a = 2 := orderOf_eq_prime (hsq a haE) ha1
  obtain ⟨b, hbE, hbn⟩ : ∃ b ∈ E, b ∉ Subgroup.zpowers a := by
    by_contra hno
    push Not at hno
    have hle : E ≤ Subgroup.zpowers a := fun b hb => hno b hb
    have := Subgroup.card_le_of_le hle
    rw [Nat.card_zpowers, hao] at this
    omega
  have hb1 : b ≠ 1 := fun h1 => hbn (h1 ▸ Subgroup.one_mem _)
  refine ⟨a, b, hao, orderOf_eq_prime (hsq b hbE) hb1,
    fun hab => hbn (hab ▸ Subgroup.mem_zpowers a), ?_⟩
  exact congrArg Subtype.val (hcomm.is_comm.comm ⟨a, haE⟩ ⟨b, hbE⟩)

private theorem r90e1_two_gen_quat (m : ℕ) [NeZero m] :
    ∃ x y : QuaternionGroup m, ∀ g : QuaternionGroup m,
      g ∈ Subgroup.closure ({x, y} : Set (QuaternionGroup m)) := by
  refine ⟨QuaternionGroup.a 1, QuaternionGroup.xa 0, fun g => ?_⟩
  have ha : ∀ i : ZMod (2 * m), QuaternionGroup.a i ∈
      Subgroup.closure ({QuaternionGroup.a 1, QuaternionGroup.xa 0} :
        Set (QuaternionGroup m)) := by
    intro i
    obtain ⟨k, rfl⟩ := ZMod.natCast_zmod_surjective i
    rw [← QuaternionGroup.a_one_pow]
    exact pow_mem (Subgroup.subset_closure (by simp)) k
  cases g with
  | a i => exact ha i
  | xa i =>
    have : QuaternionGroup.xa i = QuaternionGroup.xa 0 * QuaternionGroup.a i := by
      rw [QuaternionGroup.xa_mul_a, zero_add]
    rw [this]
    exact mul_mem (Subgroup.subset_closure (by simp)) (ha i)

private theorem r90e1_two_gen_cyclic {R : Type} [Group R] [IsCyclic R] :
    ∃ x y : R, ∀ r : R, r ∈ Subgroup.closure ({x, y} : Set R) := by
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := R)
  refine ⟨g, g, fun r => ?_⟩
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp (hg r)
  exact zpow_mem (Subgroup.subset_closure (by simp)) k

private theorem r90e1_two_gen_map {R E : Type} [Group R] [Group E] (f : R →* E)
    (hf : Function.Surjective f)
    (h : ∃ x y : R, ∀ r : R, r ∈ Subgroup.closure ({x, y} : Set R)) :
    ∃ u v : E, ∀ e : E, e ∈ Subgroup.closure ({u, v} : Set E) := by
  obtain ⟨x, y, hxy⟩ := h
  refine ⟨f x, f y, fun e => ?_⟩
  obtain ⟨r, rfl⟩ := hf e
  have := Subgroup.mem_map_of_mem f (hxy r)
  rwa [MonoidHom.map_closure, Set.image_pair] at this

private theorem r90e1_not_two_gen {E : Type} [Group E] [Finite E]
    (hcomm : ∀ a b : E, a * b = b * a) (hsq : ∀ a : E, a ^ 2 = 1) (hcard : Nat.card E = 8) :
    ¬ ∃ u v : E, ∀ e : E, e ∈ Subgroup.closure ({u, v} : Set E) := by
  rintro ⟨u, v, huv⟩
  have hu : u ^ 2 = 1 := hsq u
  have hv : v ^ 2 = 1 := hsq v
  have e1 : u * u = 1 := by rw [← pow_two]; exact hu
  have e2 : v * v = 1 := by rw [← pow_two]; exact hv
  have e3 : v * u = u * v := hcomm v u
  have e4 : u * (u * v) = v := by rw [← mul_assoc, e1, one_mul]
  have e6 : v * (u * v) = u := by rw [← mul_assoc, e3, mul_assoc, e2, mul_one]
  have e7 : u * v * u = v := by rw [mul_assoc, e3, e4]
  have e8 : u * v * v = u := by rw [mul_assoc, e2, mul_one]
  have e9 : u * v * (u * v) = 1 := by rw [mul_assoc, e6, e1]
  have hsub' : ∀ g ∈ Subgroup.closure ({u, v} : Set E), g = 1 ∨ g = u ∨ g = v ∨ g = u * v := by
    intro g hg
    refine Subgroup.closure_induction (p := fun g _ => g = 1 ∨ g = u ∨ g = v ∨ g = u * v)
      ?_ ?_ ?_ ?_ hg
    · rintro x (rfl | rfl)
      · exact Or.inr (Or.inl rfl)
      · exact Or.inr (Or.inr (Or.inl rfl))
    · exact Or.inl rfl
    · intro x y _ _ hx hy
      rcases hx with rfl | rfl | rfl | rfl <;> rcases hy with rfl | rfl | rfl | rfl <;>
        simp [e1, e2, e3, e4, e6, e7, e8, e9]
    · intro x _ hx
      rcases hx with rfl | rfl | rfl | rfl
      · simp
      · exact Or.inr (Or.inl (by rw [inv_eq_of_mul_eq_one_right e1]))
      · exact Or.inr (Or.inr (Or.inl (by rw [inv_eq_of_mul_eq_one_right e2])))
      · exact Or.inr (Or.inr (Or.inr (by rw [inv_eq_of_mul_eq_one_right e9])))
  have hsub : (Set.univ : Set E) ⊆ ({1, u, v, u * v} : Set E) := fun e _ => hsub' e (huv e)
  have h4 : Nat.card E ≤ 4 := by
    rw [← Set.ncard_univ]
    refine (Set.ncard_le_ncard hsub (Set.toFinite _)).trans ?_
    refine (Set.ncard_insert_le _ _).trans ?_
    refine Nat.succ_le_succ ((Set.ncard_insert_le _ _).trans (Nat.succ_le_succ ?_))
    refine (Set.ncard_insert_le _ _).trans ?_
    simp
  omega

private theorem r90e1_klein {Kt : Type} [Group Kt] [Finite Kt] {n : ℕ} (hn : 3 ≤ n)
    (hSz : IsSz (Kt ⧸ CFSG.pCore 2 Kt) n) :
    ∃ a b : Kt, orderOf a = 2 ∧ orderOf b = 2 ∧ a ≠ b ∧ Commute a b := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨E, hEc, hEs, hE8⟩ := r90e1_eight hn hSz
  set U : Subgroup Kt := CFSG.pCore 2 Kt with hU
  set π : Kt →* Kt ⧸ U := QuotientGroup.mk' U with hπ
  set R : Subgroup Kt := E.comap π with hR
  have hRp : IsPGroup 2 R := by
    intro g
    have hg2 : ((g : Kt) ^ 2) ∈ U := by
      rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_pow]
      exact hEs _ g.2
    obtain ⟨k, hk⟩ := (CFSG.pCore_isPGroup (p := 2) (G := Kt)) ⟨(g : Kt) ^ 2, hg2⟩
    refine ⟨k + 1, Subtype.ext ?_⟩
    have := congrArg Subtype.val hk
    simp only [Subgroup.coe_pow, Subgroup.coe_one] at this
    rw [pow_succ', pow_mul]
    simpa using this
  by_contra hno
  push Not at hno
  have hrank : CFSG.Open.twoRank R ≤ 1 := by
    by_contra h
    push Not at h
    obtain ⟨a, b, ha, hb, hab, hc⟩ := r90e1_pair (R := R) h
    exact hno (a : Kt) (b : Kt) (by rw [Subgroup.orderOf_coe]; exact ha)
      (by rw [Subgroup.orderOf_coe]; exact hb) (fun h => hab (Subtype.ext h))
      (hc.map R.subtype)
  let f : ↥R →* ↥E := (π.comp R.subtype).codRestrict E (fun r => r.2)
  have hf : Function.Surjective f := by
    intro e
    obtain ⟨x, hx⟩ := QuotientGroup.mk'_surjective U (e : Kt ⧸ U)
    refine ⟨⟨x, ?_⟩, Subtype.ext hx⟩
    change π x ∈ E
    rw [hπ, hx]
    exact e.2
  have hgen : ∃ x y : ↥R, ∀ r : ↥R, r ∈ Subgroup.closure ({x, y} : Set ↥R) := by
    rcases CFSG.TwoRankLowerBound.Helpers.rank_one_two_group_cyclic_or_quaternion ↥R hRp
      hrank with hcyc | ⟨e, -, ⟨iso⟩⟩
    · exact r90e1_two_gen_cyclic
    · exact r90e1_two_gen_map iso.symm.toMonoidHom iso.symm.surjective (r90e1_two_gen_quat _)
  exact r90e1_not_two_gen (fun a b => hEc.is_comm.comm a b)
    (fun a => Subtype.ext (hEs a a.2)) hE8 (r90e1_two_gen_map f hf hgen)

private theorem r90e1_preimage {Kt Γ : Type} [Group Kt] [Finite Kt] [Group Γ] [Group.IsPerfect Γ]
    (hsimple : IsSimpleGroup (Kt ⧸ CFSG.pCore 2 Kt)) (ρ' : Kt →* Γ)
    (hρ's : Function.Surjective ρ') (hnt : ρ' ≠ 1) :
    ((CFSG.pCore 2 Kt).map ρ').comap ρ' = CFSG.pCore 2 Kt := by
  classical
  have : Finite Γ := Finite.of_surjective _ hρ's
  set U : Subgroup Kt := CFSG.pCore 2 Kt with hU
  set N : Subgroup Γ := U.map ρ' with hN
  set W : Subgroup Kt := N.comap ρ' with hW
  have hUW : U ≤ W := fun u hu => Subgroup.mem_map_of_mem ρ' hu
  have hWn : W.Normal := Subgroup.Normal.comap (Subgroup.Normal.map inferInstance ρ' hρ's) ρ'
  have hnorm : (W.map (QuotientGroup.mk' U)).Normal :=
    Subgroup.Normal.map hWn _ (QuotientGroup.mk'_surjective U)
  rcases hsimple.eq_bot_or_eq_top_of_normal (W.map (QuotientGroup.mk' U)) with h | h
  · refine le_antisymm ?_ hUW
    have := (Subgroup.map_eq_bot_iff _).mp h
    rwa [QuotientGroup.ker_mk'] at this
  · exfalso
    have htop : W = ⊤ := by
      rw [eq_top_iff]
      intro x _
      have hx : QuotientGroup.mk' U x ∈ W.map (QuotientGroup.mk' U) := by
        rw [h]; trivial
      obtain ⟨m, hm, hmx⟩ := Subgroup.mem_map.mp hx
      have hmU : m⁻¹ * x ∈ U := QuotientGroup.eq.mp hmx
      have hxm : x = m * (m⁻¹ * x) := by group
      rw [hxm]
      exact W.mul_mem hm (hUW hmU)
    have hall : ∀ γ : Γ, γ ∈ N := by
      intro γ
      obtain ⟨k, rfl⟩ := hρ's γ
      have hk : k ∈ W := htop ▸ Subgroup.mem_top k
      exact hk
    have hpg : IsPGroup 2 Γ := by
      intro γ
      obtain ⟨u, hu, rfl⟩ := Subgroup.mem_map.mp (hall γ)
      obtain ⟨j, hj⟩ := (CFSG.pCore_isPGroup (p := 2) (G := Kt)) ⟨u, hu⟩
      refine ⟨j, ?_⟩
      rw [← map_pow]
      have : u ^ 2 ^ j = 1 := congrArg Subtype.val hj
      rw [this, map_one]
    have hnil : Group.IsNilpotent Γ := hpg.isNilpotent
    have hsub : Subsingleton Γ := by
      by_contra hns
      have : Nontrivial Γ := not_subsingleton_iff_nontrivial.mp hns
      exact Group.IsPerfect.not_isNilpotent Γ hnil
    apply hnt
    exact MonoidHom.ext fun k => Subsingleton.elim _ _

private theorem r90e1_image_sz {p : ℕ} [Fact p.Prime]
    {Kt : Type} [Group Kt] [Finite Kt] [Group.IsPerfect Kt] {n : ℕ}
    (hSz : IsSz (Kt ⧸ CFSG.pCore 2 Kt) n)
    {V : Type} [AddCommGroup V] [Module (ZMod p) V]
    (ρ : Kt →* (V ≃ₗ[ZMod p] V)) (hρ : ρ ≠ 1) :
    ∃ (Γ : Subgroup (V ≃ₗ[ZMod p] V)) (N : Subgroup ↥Γ) (_ : N.Normal), IsSz (↥Γ ⧸ N) n := by
  classical
  set U : Subgroup Kt := CFSG.pCore 2 Kt with hU
  set Γ : Subgroup (V ≃ₗ[ZMod p] V) := ρ.range with hΓ
  set ρ' : Kt →* Γ := ρ.rangeRestrict with hρ'
  have hρ's : Function.Surjective ρ' := ρ.rangeRestrict_surjective
  have hfin : Finite Γ := Finite.of_surjective _ hρ's
  have hperf : Group.IsPerfect Γ := Group.IsPerfect.range ρ
  set N : Subgroup Γ := U.map ρ' with hN
  have hNn : N.Normal := Subgroup.Normal.map inferInstance ρ' hρ's
  set φ : Kt →* Γ ⧸ N := (QuotientGroup.mk' N).comp ρ' with hφ
  have hφs : Function.Surjective φ := (QuotientGroup.mk'_surjective N).comp hρ's
  have hsimple : IsSimpleGroup (Kt ⧸ U) :=
    CFSG.LocalAnalysis.EvenBN.GMSK.isSimpleGroup_of_lieModel_twistedB2 hSz
  have hρ'1 : ρ' ≠ 1 := by
    intro h
    apply hρ
    refine MonoidHom.ext fun k => ?_
    exact congrArg Subtype.val (congrArg (fun f : Kt →* Γ => f k) h)
  have hker : φ.ker = U := by
    have h := r90e1_preimage hsimple ρ' hρ's hρ'1
    ext k
    have h1 : k ∈ N.comap ρ' ↔ k ∈ U := SetLike.ext_iff.mp h k
    rw [← h1, Subgroup.mem_comap, MonoidHom.mem_ker]
    exact QuotientGroup.eq_one_iff (ρ' k)
  let e : (Kt ⧸ U) ≃* (Γ ⧸ N) :=
    (QuotientGroup.quotientMulEquivOfEq hker.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective φ hφs)
  exact ⟨Γ, N, hNn, CFSG.Blueprint.LieModel.of_mulEquiv e hSz⟩

private theorem r90e1_abel_card {G : Type} [Group G] [Finite G] {p : ℕ} [hp : Fact p.Prime]
    {X C : Subgroup G} (hCX : C ≤ X) (hXp : IsPGroup p X) (hXexp : ∀ x ∈ X, x ^ p = 1)
    (hXcl : ⁅⁅X, X⁆, X⁆ = ⊥) (hrk : CFSG.pRank p ↥C ≤ 3) :
    Nat.card (↥C ⧸ commutator ↥C) ≤ p ^ 4 := by
  have hCp : IsPGroup p ↥C := hXp.to_le hCX
  have hexp : ∀ x : ↥C, x ^ p = 1 := fun x => Subtype.ext (hXexp x (hCX x.2))
  have hcl : commutator ↥C ≤ Subgroup.center ↥C := by
    refine Subgroup.commutator_le.mpr fun a _ b _ => ?_
    rw [Subgroup.mem_center_iff]
    intro z
    apply Subtype.ext
    have h1 : ⁅⁅(a : G), (b : G)⁆, (z : G)⁆ = 1 := by
      have : ⁅⁅(a : G), (b : G)⁆, (z : G)⁆ ∈ ⁅⁅X, X⁆, X⁆ :=
        Subgroup.commutator_mem_commutator (Subgroup.commutator_mem_commutator (hCX a.2) (hCX b.2))
          (hCX z.2)
      rw [hXcl] at this
      exact Subgroup.mem_bot.mp this
    have h2 := commutatorElement_eq_one_iff_mul_comm.mp h1
    simpa [commutatorElement_def, mul_assoc] using h2.symm
  have h4 := (CFSG.RankThree.PartTwo.class_two_small_rank_order_bounds hCp hexp hcl).2.2 hrk
  obtain ⟨k, hk⟩ := (hCp.to_quotient (commutator ↥C)).exists_card_eq
  have := (CFSG.RankThree.PartTwo.quotient_commutator_rank hp.out hexp hk).2
  rw [hk]
  exact Nat.pow_le_pow_right hp.out.pos (this ▸ h4)

private theorem r90e1_not_two_dvd {G : Type} [Group G] [Finite G] {p : ℕ} [hp : Fact p.Prime]
    (hp2 : p ≠ 2) {X : Subgroup G} (hXp : IsPGroup p X) (Y' : Subgroup ↥X) :
    ¬ 2 ∣ Nat.card Y' := by
  intro hdvd
  obtain ⟨m, hm⟩ := hXp.exists_card_eq
  have h1 : Nat.card Y' ∣ p ^ m := hm ▸ Subgroup.card_subgroup_dvd_card Y'
  have h2' : 2 ∣ p := Nat.prime_two.dvd_of_dvd_pow (hdvd.trans h1)
  exact hp2 ((Nat.prime_dvd_prime_iff_eq Nat.prime_two hp.out).mp h2').symm

private theorem r90e1_zpowers_fix {G M : Type} [Group G] [Group M] (t : G)
    (ψ : ↥(Subgroup.zpowers t) →* MulAut M) {q : M}
    (h : ψ ⟨t, Subgroup.mem_zpowers t⟩ q = q) (a : ↥(Subgroup.zpowers t)) : ψ a q = q := by
  let S : Subgroup ↥(Subgroup.zpowers t) := (MulAction.stabilizer (MulAut M) q).comap ψ
  have htS : (⟨t, Subgroup.mem_zpowers t⟩ : ↥(Subgroup.zpowers t)) ∈ S := by
    rw [Subgroup.mem_comap, MulAction.mem_stabilizer_iff, MulAut.smul_def]
    exact h
  have hzS : Subgroup.zpowers (⟨t, Subgroup.mem_zpowers t⟩ : ↥(Subgroup.zpowers t)) ≤ S :=
    Subgroup.zpowers_le.mpr htS
  have haz : a ∈ Subgroup.zpowers (⟨t, Subgroup.mem_zpowers t⟩ : ↥(Subgroup.zpowers t)) := by
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp a.2
    exact Subgroup.mem_zpowers_iff.mpr ⟨k, Subtype.ext (by simpa using hk)⟩
  have := hzS haz
  rwa [Subgroup.mem_comap, MulAction.mem_stabilizer_iff, MulAut.smul_def] at this

private theorem r90e1_fix_lift {G : Type} [Group G] [Finite G] {p : ℕ} [hp : Fact p.Prime]
    (hp2 : p ≠ 2) {X Y K : Subgroup G} (hXp : IsPGroup p X) (hKX : K ≤ normalizer (X : Set G))
    (hKY : K ≤ normalizer (Y : Set G)) [(Y.subgroupOf X).Normal]
    [CFSG.IsElementaryAbelian p (↥X ⧸ Y.subgroupOf X)] {t : G} (htK : t ∈ K) (ht : orderOf t = 2) :
    ∀ v ∈ LinearMap.ker ((CFSG.ABGLocalTools.chiefRep (p := p) hKX hKY ⟨t, htK⟩ :
      LinearMap.GeneralLinearGroup (ZMod p) _).val - 1),
    ∃ c : ↥X, (c : G) ∈ Subgroup.centralizer ((Subgroup.zpowers t : Subgroup G) : Set G) ∧
      Additive.ofMul (c : ↥X ⧸ Y.subgroupOf X) = v := by
  classical
  have h2 : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set Y' : Subgroup ↥X := Y.subgroupOf X with hY'
  set T : Subgroup G := Subgroup.zpowers t with hT
  have hTK : T ≤ K := Subgroup.zpowers_le.mpr htK
  have hTX : T ≤ normalizer (X : Set G) := hTK.trans hKX
  have hTY : T ≤ normalizer (Y : Set G) := hTK.trans hKY
  have hT2 : IsPGroup 2 ↥T :=
    IsPGroup.of_card (n := 1) (by rw [hT, Nat.card_zpowers, ht, pow_one])
  let α : ↥T →* MulAut ↥X := CFSG.ABGLocalTools.chiefConj hTX
  have hα : ∀ (a : ↥T) (x : ↥X), ((α a x : ↥X) : G) = (a : G) * x * (a : G)⁻¹ :=
    fun a x => CFSG.ABGLocalTools.chiefConj_apply_coe hTX a x
  have hαY : ∀ a : ↥T, ∀ n ∈ Y', α a n ∈ Y' := by
    intro a n hn
    rw [hY', Subgroup.mem_subgroupOf] at hn ⊢
    rw [hα]
    exact (Subgroup.mem_normalizer_iff.mp (hTY a.2) n).mp hn
  have hcop : ¬ 2 ∣ Nat.card Y' := r90e1_not_two_dvd hp2 hXp Y'
  have hlift := CFSG.Semidihedral.Principal.coprime_fixed_point_lifting 2 hT2 α Y' hαY hcop
  intro v hv
  obtain ⟨w, rfl⟩ := CFSG.ABGLocalTools.exists_ofMul_mk v
  have hfixw : ((CFSG.ABGLocalTools.chiefConj hKX ⟨t, htK⟩ w : ↥X) : ↥X ⧸ Y') =
      (w : ↥X ⧸ Y') := by
    have h1 := LinearMap.mem_ker.mp hv
    rw [LinearMap.sub_apply, Module.End.one_apply, sub_eq_zero,
      CFSG.ABGLocalTools.chiefRep_apply_mk] at h1
    exact congrArg Additive.toMul h1
  set q : ↥X ⧸ Y' := (w : ↥X ⧸ Y') with hq
  have ht0 : CFSG.Semidihedral.Principal.CoprimeFixedPoint.quotientAction α Y' hαY
      ⟨t, Subgroup.mem_zpowers t⟩ q = q := by
    rw [hq, CFSG.Semidihedral.Principal.CoprimeFixedPoint.quotientAction_mk]
    have : (α ⟨t, Subgroup.mem_zpowers t⟩ w : ↥X) =
        CFSG.ABGLocalTools.chiefConj hKX ⟨t, htK⟩ w :=
      Subtype.ext (by rw [hα, CFSG.ABGLocalTools.chiefConj_apply_coe])
    rw [this]
    exact hfixw
  have hall : ∀ a : ↥T, CFSG.Semidihedral.Principal.CoprimeFixedPoint.quotientAction α Y' hαY
      a q = q := r90e1_zpowers_fix t _ ht0
  have hmem : q ∈ {q : ↥X ⧸ Y' | ∀ a : ↥T,
      CFSG.Semidihedral.Principal.CoprimeFixedPoint.quotientAction α Y' hαY a q = q} := hall
  rw [hlift] at hmem
  obtain ⟨c, hc, hcq⟩ := hmem
  refine ⟨c, ?_, congrArg Additive.ofMul hcq⟩
  rw [Subgroup.mem_centralizer_iff]
  intro s hs
  have h3 : (s : G) * c * (s : G)⁻¹ = c := by
    have := congrArg Subtype.val (hc ⟨s, hs⟩)
    rwa [hα] at this
  calc s * (c : G) = (s * c * s⁻¹) * s := by group
    _ = c * s := by rw [h3]

private theorem r90e1_fix_count {G : Type} [Group G] [Finite G] {p : ℕ} [hp : Fact p.Prime]
    {X Y T : Subgroup G} (hXp : IsPGroup p X) (hXexp : ∀ x ∈ X, x ^ p = 1)
    (hXcl : ⁅⁅X, X⁆, X⁆ = ⊥) [(Y.subgroupOf X).Normal]
    [CFSG.IsElementaryAbelian p (↥X ⧸ Y.subgroupOf X)]
    (hrank : CFSG.Open.pRank p (normalizer (T : Set G)) ≤ 3)
    (F : Submodule (ZMod p) (Additive (↥X ⧸ Y.subgroupOf X)))
    (key : ∀ v ∈ F, ∃ c : ↥X, (c : G) ∈ Subgroup.centralizer (T : Set G) ∧
      Additive.ofMul (c : ↥X ⧸ Y.subgroupOf X) = v) :
    Module.finrank (ZMod p) F ≤ 4 := by
  classical
  set Y' : Subgroup ↥X := Y.subgroupOf X with hY'
  set C : Subgroup G := X ⊓ Subgroup.centralizer (T : Set G) with hC
  have hCX : C ≤ X := inf_le_left
  have hCN : C ≤ normalizer (T : Set G) :=
    inf_le_right.trans (Subgroup.centralizer_le_normalizer (T : Set G))
  have hrk : CFSG.pRank p ↥C ≤ 3 := by
    rw [CFSG.SectionRank.pRank_eq_open_pRank_top]
    calc CFSG.Open.pRank p (⊤ : Subgroup ↥C)
        ≤ CFSG.Open.pRank p ((⊤ : Subgroup ↥C).map C.subtype) :=
          CFSG.SectionRank.pRank_le_map hp.out.one_lt C.subtype C.subtype_injective ⊤
      _ ≤ CFSG.Open.pRank p (normalizer (T : Set G)) := by
          refine CFSG.SectionRank.pRank_mono hp.out.one_lt ?_
          rw [Subgroup.map_top, Subgroup.range_subtype]
          exact hCN
      _ ≤ 3 := hrank
  have hbound := r90e1_abel_card hCX hXp hXexp hXcl hrk
  let h : ↥C →* ↥X ⧸ Y' := (QuotientGroup.mk' Y').comp (Subgroup.inclusion hCX)
  have hker : commutator ↥C ≤ h.ker := by
    refine Subgroup.commutator_le.mpr fun a _ b _ => ?_
    rw [MonoidHom.mem_ker, map_commutatorElement]
    exact commutatorElement_eq_one_iff_mul_comm.mpr (mul_comm' _ _)
  let q : ↥C ⧸ commutator ↥C →* ↥X ⧸ Y' := QuotientGroup.lift (commutator ↥C) h hker
  have hmemq : ∀ v : F, Additive.toMul (v : Additive (↥X ⧸ Y')) ∈ Set.range q := by
    intro v
    obtain ⟨c, hcC, hcv⟩ := key v v.2
    have hcC' : (c : G) ∈ C := Subgroup.mem_inf.mpr ⟨c.2, hcC⟩
    refine ⟨((⟨c, hcC'⟩ : ↥C) : ↥C ⧸ commutator ↥C), ?_⟩
    have h1 : q ((⟨c, hcC'⟩ : ↥C) : ↥C ⧸ commutator ↥C) = (c : ↥X ⧸ Y') := rfl
    rw [h1, ← hcv]
    rfl
  have hinj : Function.Injective
      (Set.codRestrict (fun v : F => Additive.toMul (v : Additive (↥X ⧸ Y'))) (Set.range q)
        hmemq) := by
    rw [Set.injective_codRestrict]
    intro v w hvw
    exact Subtype.ext (Additive.toMul.injective hvw)
  have hF4 : Nat.card F ≤ p ^ 4 :=
    (Nat.card_le_card_of_injective _ hinj).trans ((Finite.card_range_le q).trans hbound)
  have hfin : Module.Finite (ZMod p) F := inferInstance
  have hcard : Nat.card F = p ^ Module.finrank (ZMod p) F := by
    rw [Module.natCard_eq_pow_finrank (K := ZMod p), Nat.card_zmod]
  rw [hcard] at hF4
  exact (Nat.pow_le_pow_iff_right hp.out.one_lt).mp hF4

private theorem r90e1_fix {G : Type} [Group G] [Finite G] {p : ℕ} [hp : Fact p.Prime]
    (hp2 : p ≠ 2) {X Y K : Subgroup G} (hXp : IsPGroup p X) (hXexp : ∀ x ∈ X, x ^ p = 1)
    (hXcl : ⁅⁅X, X⁆, X⁆ = ⊥) (hKX : K ≤ normalizer (X : Set G))
    (hKY : K ≤ normalizer (Y : Set G)) [(Y.subgroupOf X).Normal]
    [CFSG.IsElementaryAbelian p (↥X ⧸ Y.subgroupOf X)] {t : G} (htK : t ∈ K) (ht : orderOf t = 2)
    (hrank : CFSG.Open.pRank p (normalizer ((Subgroup.zpowers t : Subgroup G) : Set G)) ≤ 3) :
    Module.finrank (ZMod p)
      (LinearMap.ker ((CFSG.ABGLocalTools.chiefRep (p := p) hKX hKY ⟨t, htK⟩ :
        LinearMap.GeneralLinearGroup (ZMod p) _).val - 1)) ≤ 4 :=
  r90e1_fix_count hXp hXexp hXcl hrank _ (r90e1_fix_lift hp2 hXp hKX hKY htK ht)

private theorem r90e1_normalizes_map {G : Type} [Group G] {A H : Subgroup G}
    (hH : H ≤ normalizer (A : Set G)) (D : Subgroup ↥A) [hD : D.Characteristic] :
    H ≤ normalizer ((D.map A.subtype : Subgroup G) : Set G) := by
  rw [Subgroup.le_normalizer_iff]
  rintro h hh _ ⟨d, hd, rfl⟩
  let α : MulAut ↥A := CFSG.ABGLocalTools.chiefConj hH ⟨h, hh⟩
  have hα : ((α d : ↥A) : G) = h * (d : G) * h⁻¹ :=
    CFSG.ABGLocalTools.chiefConj_apply_coe hH ⟨h, hh⟩ d
  have hmem : α d ∈ D := by
    have h1 := Subgroup.mem_map_of_mem α.toMonoidHom hd
    rwa [Subgroup.characteristic_iff_map_eq.mp hD α] at h1
  exact ⟨α d, hmem, hα⟩

private theorem r90e1_prime {G : Type} [Group G] [Finite G] {K H A : Subgroup G}
    (hKK : ⁅K, K⁆ = K) (hKH : K ≤ H) (hHA : H ≤ normalizer (A : Set G))
    (hodd : Odd (Nat.card ↥A)) (hne : ⁅K, A⁆ ≠ ⊥) :
    ∃ p : ℕ, p.Prime ∧ p ≠ 2 ∧ ⁅K, (CFSG.pCore p ↥A).map A.subtype⁆ ≠ ⊥ := by
  have hsolv : Group.IsSolvable ↥A := CFSG.FeitThompson.isSolvable_of_odd_natCard _ hodd
  by_contra hcon
  push Not at hcon
  set F : Subgroup G := CFSG.fittingSubgroupOf A with hF
  have hFcent : F ≤ centralizer (K : Set G) := by
    change (CFSG.fittingSubgroup ↥A).map A.subtype ≤ _
    rw [CFSG.fitting_eq_sup_pCore, Subgroup.map_iSup]
    refine iSup_le fun q => ?_
    have hq : q.1.1.Prime := Nat.prime_of_mem_primeFactors q.1.2
    have hq2 : q.1.1 ≠ 2 := by
      intro h2
      have := Nat.dvd_of_mem_primeFactors q.1.2
      rw [h2] at this
      exact (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr this)
    exact Subgroup.le_centralizer_iff.mp
      (Subgroup.commutator_eq_bot_iff_le_centralizer.mp (hcon _ hq hq2))
  have hKF : K ≤ centralizer (F : Set G) := Subgroup.le_centralizer_iff.mp hFcent
  have hFnorm : A ≤ normalizer (F : Set G) := by
    rw [Subgroup.le_normalizer_iff]
    rintro b hb _ ⟨f, hf, rfl⟩
    exact ⟨⟨b, hb⟩ * f * ⟨b, hb⟩⁻¹, (CFSG.fittingSubgroup_normal).conj_mem f hf ⟨b, hb⟩, rfl⟩
  have hAK : ⁅A, K⁆ ≤ F := by
    refine Subgroup.commutator_le.mpr fun b hb a ha => ?_
    have h1 : b * a * b⁻¹ ∈ centralizer (F : Set G) :=
      CFSG.GroupTheory.conj_mem_centralizer_of_le_normalizer hFnorm hKF b hb a ha
    have h2 : ⁅b, a⁆ ∈ centralizer (F : Set G) := by
      have : ⁅b, a⁆ = (b * a * b⁻¹) * a⁻¹ := by rw [commutatorElement_def]
      rw [this]
      exact (centralizer (F : Set G)).mul_mem h1 ((centralizer (F : Set G)).inv_mem (hKF ha))
    have h3 : ⁅b, a⁆ ∈ A := by
      have : ⁅b, a⁆ = b * (a * b⁻¹ * a⁻¹) := by rw [commutatorElement_def]; group
      rw [this]
      exact A.mul_mem hb
        ((Subgroup.mem_normalizer_iff.mp (hHA (hKH ha)) b⁻¹).mp (A.inv_mem hb))
    exact CFSG.GorensteinWalter.fact_1_2_centralizer_fitting_le_fitting A hsolv ⟨h3, h2⟩
  exact hne (CFSG.GroupTheory.commutator_eq_bot_of_commutator_le_of_centralizer
    (A := K) (V := A) (V₀ := F) (by rw [Subgroup.commutator_comm]; exact hAK) hKF hKK)

private theorem r90e1_critical {G : Type} [Group G] [Finite G] {K H Q : Subgroup G} {p : ℕ}
    [Fact p.Prime] (hp2 : p ≠ 2) (hKK : ⁅K, K⁆ = K) (hKH : K ≤ H)
    (hHQ : H ≤ normalizer (Q : Set G)) (hQp : IsPGroup p Q) (hne : ⁅K, Q⁆ ≠ ⊥) :
    ∃ D : Subgroup G, D ≤ Q ∧ IsPGroup p D ∧ (∀ x ∈ D, x ^ p = 1) ∧ ⁅⁅D, D⁆, D⁆ = ⊥ ∧
      H ≤ normalizer (D : Set G) ∧ ⁅K, D⁆ ≠ ⊥ := by
  have hQ1 : Q ≠ ⊥ := fun h => hne (by rw [h, Subgroup.commutator_bot_right])
  have : Nontrivial ↥Q := (Subgroup.nontrivial_iff_ne_bot Q).2 hQ1
  obtain ⟨D, hDchar, -, hDcomm, hDexp, hDfix⟩ :=
    CFSG.SectionRank.Ccomm.odd_critical_exponent_subgroup (p := p) hp2 hQp
  refine ⟨D.map Q.subtype, Subgroup.map_subtype_le D, (hQp.to_subgroup D).map Q.subtype, ?_, ?_,
    r90e1_normalizes_map hHQ D, ?_⟩
  · rintro y ⟨d, hd, rfl⟩
    simpa [Subgroup.coe_pow] using congrArg Subtype.val (hDexp d hd)
  · have hDD : ⁅D, D⁆ ≤ D ⊓ Subgroup.centralizer (D : Set ↥Q) :=
      (Subgroup.commutator_mono le_rfl le_top).trans hDcomm
    have hcent : ⁅D, D⁆ ≤ Subgroup.centralizer (D : Set ↥Q) := hDD.trans inf_le_right
    have hbot : ⁅⁅D, D⁆, D⁆ = ⊥ := Subgroup.commutator_eq_bot_iff_le_centralizer.mpr hcent
    have hmap : (⁅⁅D, D⁆, D⁆ : Subgroup ↥Q).map Q.subtype =
        ⁅⁅D.map Q.subtype, D.map Q.subtype⁆, D.map Q.subtype⁆ := by
      rw [Subgroup.map_commutator, Subgroup.map_commutator]
    rw [← hmap, hbot, Subgroup.map_bot]
  · intro hbot
    apply hne
    have hKQ : K ≤ normalizer (Q : Set G) := hKH.trans hHQ
    let φ : ↥K →* MulAut ↥Q := CFSG.ABGLocalTools.chiefConj hKQ
    have hcent : K ≤ centralizer ((D.map Q.subtype : Subgroup G) : Set G) :=
      Subgroup.commutator_eq_bot_iff_le_centralizer.mp hbot
    have hperf : ⁅(⊤ : Subgroup ↥K), (⊤ : Subgroup ↥K)⁆ = ⊤ := by
      apply Subgroup.map_injective K.subtype_injective
      rw [Subgroup.map_commutator, Subgroup.map_top, Subgroup.range_subtype, hKK]
    have hle : (⊤ : Subgroup ↥K).map φ ≤ fixingSubgroup (MulAut ↥Q) (D : Set ↥Q) := by
      rintro _ ⟨k, -, rfl⟩
      rw [mem_fixingSubgroup_iff]
      intro d hd
      apply Subtype.ext
      rw [MulAut.smul_def]
      change ((CFSG.ABGLocalTools.chiefConj hKQ k d : ↥Q) : G) = (d : G)
      rw [CFSG.ABGLocalTools.chiefConj_apply_coe]
      have hc := Subgroup.mem_centralizer_iff.mp (hcent k.2) (d : G) ⟨d, hd, rfl⟩
      calc (k : G) * d * (k : G)⁻¹ = ((d : G) * k) * (k : G)⁻¹ := by rw [← hc]
        _ = d := by group
    have hbot' := CFSG.GroupTheory.map_eq_bot_of_isPerfect_of_le_fixingSubgroup φ D hDfix hperf hle
    refine Subgroup.commutator_eq_bot_iff_le_centralizer.mpr fun k hk => ?_
    rw [Subgroup.mem_centralizer_iff]
    intro q hq
    have h1 : φ ⟨k, hk⟩ = 1 :=
      Subgroup.mem_bot.mp (hbot' ▸ Subgroup.mem_map_of_mem φ (Subgroup.mem_top _))
    have h2 := congrArg (fun f : MulAut ↥Q => ((f ⟨q, hq⟩ : ↥Q) : G)) h1
    simp only [MulAut.one_apply] at h2
    change ((CFSG.ABGLocalTools.chiefConj hKQ ⟨k, hk⟩ ⟨q, hq⟩ : ↥Q) : G) = q at h2
    rw [CFSG.ABGLocalTools.chiefConj_apply_coe] at h2
    calc q * k = (k * q * k⁻¹) * k := by rw [h2]
      _ = k * q := by group

private theorem r90e1_section_normal {G : Type} [Group G] {X Y : Subgroup G} (hYX : Y ≤ X)
    (hc : ⁅X, X⁆ ≤ Y) : (Y.subgroupOf X).Normal := by
  rw [Subgroup.normal_subgroupOf_iff_le_normalizer hYX,
    Subgroup.le_normalizer_iff_commutator_le_left]
  exact (Subgroup.commutator_mono hYX le_rfl).trans hc

private theorem r90e1_section_elem {G : Type} [Group G] {p : ℕ} {X Y : Subgroup G}
    [(Y.subgroupOf X).Normal] (hc : ⁅X, X⁆ ≤ Y) (hexp : ∀ x ∈ X, x ^ p = 1) :
    CFSG.IsElementaryAbelian p (↥X ⧸ Y.subgroupOf X) where
  is_comm := ⟨fun x y => by
    induction x using QuotientGroup.induction_on with
    | H a =>
    induction y using QuotientGroup.induction_on with
    | H b =>
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq, Subgroup.mem_subgroupOf]
    have : (((a * b)⁻¹ * (b * a) : X) : G) = ⁅(b : G)⁻¹, (a : G)⁻¹⁆ := by
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, commutatorElement_def]
      group
    rw [this]
    exact hc (Subgroup.commutator_mem_commutator (inv_mem b.2) (inv_mem a.2))⟩
  exponent_dvd_p := by
    apply Monoid.exponent_dvd_of_forall_pow_eq_one
    intro x
    induction x using QuotientGroup.induction_on with
    | H a =>
    rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf,
      Subgroup.coe_pow, hexp _ a.2]
    exact Y.one_mem

private theorem r90e1_reduce {G : Type} [Group G] [Finite G] {K H : Subgroup G}
    (hKK : ⁅K, K⁆ = K) (hKH : K ≤ H) (hne : ⁅K, oddCore890 H⁆ ≠ ⊥) :
    ∃ (p : ℕ) (_ : p.Prime) (X Y : Subgroup G), p ≠ 2 ∧ IsPGroup p X ∧ (∀ x ∈ X, x ^ p = 1) ∧
      ⁅⁅X, X⁆, X⁆ = ⊥ ∧ Y ≤ X ∧ ⁅X, X⁆ ≤ Y ∧ K ≤ normalizer (X : Set G) ∧
      K ≤ normalizer (Y : Set G) ∧ ¬ ⁅X, K⁆ ≤ Y := by
  set A : Subgroup G := oddCore890 H with hA
  have hAH : A ≤ H := Subgroup.map_subtype_le _
  have hHA : H ≤ normalizer (A : Set G) := by
    rw [Subgroup.le_normalizer_iff]
    rintro h hh _ ⟨d, hd, rfl⟩
    exact ⟨⟨h, hh⟩ * d * ⟨h, hh⟩⁻¹, (CFSG.oddCore_normal ↥H).conj_mem d hd ⟨h, hh⟩, rfl⟩
  have hAodd : Odd (Nat.card ↥A) := by
    rw [hA, oddCore890, Subgroup.card_map_of_injective H.subtype_injective]
    exact CFSG.ABGLocalTools.odd_card_oddCore
  obtain ⟨p, hp, hp2, hpne⟩ := r90e1_prime hKK hKH hHA hAodd hne
  have : Fact p.Prime := ⟨hp⟩
  set Q : Subgroup G := (CFSG.pCore p ↥A).map A.subtype with hQ
  have hQp : IsPGroup p Q := (CFSG.pCore_isPGroup (p := p) (G := ↥A)).map A.subtype
  have hHQ : H ≤ normalizer (Q : Set G) := r90e1_normalizes_map hHA (CFSG.pCore p ↥A)
  have hQH : Q ≤ H := (Subgroup.map_subtype_le _).trans hAH
  obtain ⟨D, hDQ, hDp, hDexp, hDcl, hHD, hKD⟩ := r90e1_critical hp2 hKK hKH hHQ hQp hpne
  have hDH : D ≤ H := hDQ.trans hQH
  have hHbot : H ≤ normalizer ((⊥ : Subgroup G) : Set G) := fun h _ =>
    Subgroup.mem_normalizer_iff.mpr fun x => by simp [Subgroup.mem_bot, mul_inv_eq_one]
  obtain ⟨X, Y, -, hYX, hXD, hHX, hHY, -, hXDY, hXK⟩ :=
    CFSG.GroupTheory.exists_section_of_not_commutator_le (G := G) (p := p) (H := H) (L := K)
      (Q := D) (P := D) (V := ⊥) hKH hDH bot_le le_rfl hDp hHD hHD hHbot hKK
      (fun h => hKD (by rw [Subgroup.commutator_comm]; exact le_bot_iff.mp h))
  refine ⟨p, hp, X, Y, hp2, hDp.to_le hXD, fun x hx => hDexp x (hXD hx), ?_, hYX, ?_,
    hKH.trans hHX, hKH.trans hHY, hXK⟩
  · exact le_bot_iff.mp (hDcl ▸ Subgroup.commutator_mono
      (Subgroup.commutator_mono hXD hXD) hXD)
  · exact (Subgroup.commutator_mono le_rfl hXD).trans hXDY

private theorem r90e1_dim_le {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) {Kt V : Type} [Group Kt]
    [AddCommGroup V] [Module (ZMod p) V] [FiniteDimensional (ZMod p) V]
    (ρ : Kt →* LinearMap.GeneralLinearGroup (ZMod p) V)
    (hfix : ∀ t : Kt, orderOf t = 2 →
      Module.finrank (ZMod p) (LinearMap.ker ((ρ t).val - 1)) ≤ 4)
    {a b : Kt} (ha : orderOf a = 2) (hb : orderOf b = 2) (hab : a ≠ b) (hcomm : Commute a b) :
    Module.finrank (ZMod p) V ≤ 12 := by
  have h2 : (2 : ZMod p) ≠ 0 := by
    intro h
    have h' : ((2 : ℕ) : ZMod p) = 0 := by exact_mod_cast h
    rw [ZMod.natCast_eq_zero_iff] at h'
    exact hp2 ((Nat.prime_dvd_prime_iff_eq (Fact.out : p.Prime) Nat.prime_two).mp h')
  have h2f : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have ha2 : a ^ 2 = 1 := ha ▸ pow_orderOf_eq_one a
  have hb2 : b ^ 2 = 1 := hb ▸ pow_orderOf_eq_one b
  have hab2 : orderOf (a * b) = 2 := by
    refine orderOf_eq_prime ?_ ?_
    · rw [hcomm.mul_pow, ha2, hb2, one_mul]
    · intro h
      have hb' : b = a⁻¹ := eq_inv_of_mul_eq_one_right h
      have hai : a⁻¹ = a := inv_eq_of_mul_eq_one_right (by rw [← pow_two]; exact ha2)
      exact hab (hb'.trans hai).symm
  have hrel := r90e1_three_fix h2 (ρ a).val (ρ b).val
    (by rw [← Units.val_mul, ← map_mul, ← pow_two, ha2, map_one, Units.val_one])
    (by rw [← Units.val_mul, ← map_mul, ← pow_two, hb2, map_one, Units.val_one])
    (by rw [← Units.val_mul, ← Units.val_mul, ← map_mul, ← map_mul, hcomm.eq])
  have h3 : (ρ a).val * (ρ b).val = (ρ (a * b)).val := by rw [map_mul, Units.val_mul]
  rw [h3] at hrel
  have := hfix a ha
  have := hfix b hb
  have := hfix (a * b) hab2
  omega

private theorem r90e1_section {G : Type} [Group G] [Finite G] {K X Y : Subgroup G} {p n : ℕ}
    [Fact p.Prime] (hp2 : p ≠ 2) (hKK : ⁅K, K⁆ = K) (hn : 3 ≤ n) (hSz : IsSz (Bar2 K) n)
    (hrank : ∀ T : Subgroup G, T ≤ K → T ≠ ⊥ → IsPGroup 2 T →
      CFSG.Open.pRank p (normalizer (T : Set G)) ≤ 3)
    (hXp : IsPGroup p X) (hXexp : ∀ x ∈ X, x ^ p = 1) (hXcl : ⁅⁅X, X⁆, X⁆ = ⊥)
    (hKX : K ≤ normalizer (X : Set G)) (hKY : K ≤ normalizer (Y : Set G)) (hXK : ¬ ⁅X, K⁆ ≤ Y)
    [(Y.subgroupOf X).Normal] [CFSG.IsElementaryAbelian p (↥X ⧸ Y.subgroupOf X)] :
    Module.finrank (ZMod p) (Additive (↥X ⧸ Y.subgroupOf X)) ≤ 12 ∧
      ∃ (Γ : Subgroup (Additive (↥X ⧸ Y.subgroupOf X) ≃ₗ[ZMod p]
          Additive (↥X ⧸ Y.subgroupOf X))) (N : Subgroup ↥Γ) (_ : N.Normal),
          IsSz (↥Γ ⧸ N) n := by
  have hperf : Group.IsPerfect ↥K := Subgroup.isPerfect_iff.mpr hKK
  let ρ := CFSG.ABGLocalTools.chiefRep (p := p) hKX hKY
  have hρ1 : ρ ≠ 1 := by
    intro h
    apply hXK
    refine Subgroup.commutator_le.mpr fun x hx k hk => ?_
    exact (CFSG.ABGLocalTools.chiefRep_eq_one_iff (p := p) hKX hKY ⟨k, hk⟩).mp
      (by simp [ρ, h]) x hx
  let e := LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod p)
    (Additive (↥X ⧸ Y.subgroupOf X))
  have hfix : ∀ t : ↥K, orderOf t = 2 →
      Module.finrank (ZMod p) (LinearMap.ker ((ρ t).val - 1)) ≤ 4 := by
    intro t ht
    have ht' : orderOf (t : G) = 2 := by rw [Subgroup.orderOf_coe]; exact ht
    have hT1 : (Subgroup.zpowers (t : G)) ≠ ⊥ := by
      intro h
      have h1 : (t : G) = 1 :=
        Subgroup.mem_bot.mp (h ▸ Subgroup.mem_zpowers (t : G))
      rw [h1, orderOf_one] at ht'
      omega
    have hT2 : IsPGroup 2 (Subgroup.zpowers (t : G)) :=
      IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, ht', pow_one])
    exact r90e1_fix hp2 hXp hXexp hXcl hKX hKY t.2 ht'
      (hrank _ (Subgroup.zpowers_le.mpr t.2) hT1 hT2)
  obtain ⟨a, b, ha, hb, hab, hcomm⟩ := r90e1_klein hn hSz
  refine ⟨r90e1_dim_le hp2 ρ hfix ha hb hab hcomm, r90e1_image_sz hSz (e.toMonoidHom.comp ρ) ?_⟩
  intro h
  apply hρ1
  refine MonoidHom.ext fun k => e.injective ?_
  exact congrArg (fun f => f k) h

theorem r890_lemma5e1_holds : Lemma5e1_890 := by
  intro G _ _ K n hKK _ hn _ hSz hrank H hKH
  by_contra hne
  obtain ⟨p, hp, X, Y, hp2, hXp, hXexp, hXcl, hYX, hXXY, hKX, hKY, hXK⟩ :=
    r90e1_reduce hKK hKH hne
  have : Fact p.Prime := ⟨hp⟩
  rcases eq_or_ne n 3 with rfl | hn3
  · apply hXK
    rw [Sz5.sz5e1_strongCentralization hp2 G K hKK hSz (hrank p hp hp2) X hXp hXexp hXcl hKX]
    exact bot_le
  · have hnorm : (Y.subgroupOf X).Normal := r90e1_section_normal hYX hXXY
    have hel : CFSG.IsElementaryAbelian p (↥X ⧸ Y.subgroupOf X) :=
      r90e1_section_elem hXXY hXexp
    obtain ⟨h12, Γ, N, hN, hSz'⟩ :=
      r90e1_section hp2 hKK hn hSz (hrank p hp hp2) hXp hXexp hXcl hKX hKY hXK
    have h14 := fourteen_le_finrank_of_suzuki_quotient_of_ne_three
      (Sz5.ringChar_zmod_ne_two hp2) Γ N hn hSz' hn3
    omega

end R90E1

section R90Y12

open Subgroup CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase
open CFSG.ABGLocalTools (IsSylowOf)

private theorem r90y12_le_of_pGroup {G : Type} [Group G] [Finite G] {M L P U : Subgroup G}
    (hP : IsSylowOf 3 P M) (hPL : P ≤ L) (hLM : M ≤ normalizer (L : Set G)) (hUM : U ≤ M)
    (hU : IsPGroup 3 U) : U ≤ L := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hU' : IsPGroup 3 (U.subgroupOf M) := hU.comap_subtype
  obtain ⟨S, hUS⟩ := hU'.exists_le_sylow
  have hS : IsSylowOf 3 ((S : Subgroup M).map M.subtype) M := ⟨S, rfl⟩
  obtain ⟨k, hkM, hk⟩ := hP.exists_mem_conj hS
  intro u hu
  have hu' : u ∈ (S : Subgroup M).map M.subtype :=
    ⟨⟨u, hUM hu⟩, hUS (Subgroup.mem_subgroupOf.mpr hu), rfl⟩
  have hL : k⁻¹ * u * k ∈ L := hPL ((hk u).mp hu')
  have := (Subgroup.mem_normalizer_iff.mp (hLM hkM) (k⁻¹ * u * k)).mp hL
  have e : k * (k⁻¹ * u * k) * k⁻¹ = u := by group
  rwa [e] at this

private theorem r90y12_card_map {H X : Type} [Group H] [Group X] (f : H →* X) (V : Subgroup H)
    (hd : Disjoint V f.ker) : Nat.card (V.map f) = Nat.card V := by
  have hinj : Function.Injective (f.comp V.subtype) := by
    rw [injective_iff_map_eq_one]
    intro x hx
    exact Subtype.ext (Subgroup.disjoint_def.mp hd x.2 hx)
  have hrange : (f.comp V.subtype).range = V.map f := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
  rw [← hrange]
  exact (Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv).symm

private theorem r90y12_card_dvd {X : Type} [Group X] [Finite X] {p : ℕ} [Fact p.Prime]
    (C U : Subgroup X) (hUC : U ≤ C) (hU : IsPGroup p U) :
    Nat.card U ∣ p ^ (Nat.card C).factorization p := by
  have hU' : IsPGroup p (U.subgroupOf C) := hU.comap_subtype
  obtain ⟨S, hUS⟩ := hU'.exists_le_sylow
  have h1 : Nat.card (U.subgroupOf C) ∣ Nat.card S := Subgroup.card_dvd_of_le hUS
  rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hUC).toEquiv, Sylow.card_eq_multiplicity]
    at h1

private theorem r90y12_bound {G : Type} [Group G] [Finite G] {M L P Y U : Subgroup G}
    (hP : IsSylowOf 3 P M) (hPL : P ≤ L) (hLM : M ≤ normalizer (L : Set G))
    (hC : (Nat.card (centralizer (barImg_890 L Y : Set (Bar2 L)))).factorization 3 = 2)
    (hUM : U ≤ M) (hUY : U ≤ centralizer (Y : Set G)) (hU : IsPGroup 3 U) :
    Nat.card U ∣ 3 ^ 2 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hUL : U ≤ L := r90y12_le_of_pGroup hP hPL hLM hUM hU
  have hVp : IsPGroup 3 (U.subgroupOf L) := hU.comap_subtype
  have hd : Disjoint (U.subgroupOf L) (QuotientGroup.mk' (CFSG.pCore 2 ↥L)).ker := by
    rw [QuotientGroup.ker_mk']
    exact IsPGroup.disjoint_of_ne 3 2 (by norm_num) _ _ hVp
      (CFSG.pCore_isPGroup (p := 2) (G := ↥L))
  have hcard : Nat.card ((U.subgroupOf L).map (QuotientGroup.mk' (CFSG.pCore 2 ↥L))) =
      Nat.card U := by
    rw [r90y12_card_map _ _ hd, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hUL).toEquiv]
  have hle : (U.subgroupOf L).map (QuotientGroup.mk' (CFSG.pCore 2 ↥L)) ≤
      centralizer (barImg_890 L Y : Set (Bar2 L)) := by
    rintro _ ⟨v, hv, rfl⟩
    rw [Subgroup.mem_centralizer_iff]
    rintro _ ⟨w, hw, rfl⟩
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext ((Subgroup.mem_centralizer_iff.mp (hUY hv)) (w : G) hw)
  have h := r90y12_card_dvd _ _ hle (hVp.map (QuotientGroup.mk' (CFSG.pCore 2 ↥L)))
  rwa [hcard, hC] at h

private theorem r90y12_card_sup {G : Type} [Group G] [Finite G] {Y Z : Subgroup G}
    (hY : Nat.card Y = 3) (hZ : Nat.card Z = 3) (hne : Y ≠ Z)
    (hN : Y ≤ normalizer (Z : Set G)) : Nat.card (Y ⊔ Z : Subgroup G) = 3 ^ 2 := by
  have h1 := CFSG.GroupTheory.CoprimeActionSupport.NormalSubgroupSylowJoin.card_sup_mul_card_inf hN
  have h2 : Nat.card (Y ⊓ Z : Subgroup G) = 1 := by
    have hd : Nat.card (Y ⊓ Z : Subgroup G) ∣ 3 := hY ▸ Subgroup.card_dvd_of_le inf_le_left
    rcases (Nat.dvd_prime Nat.prime_three).mp hd with h | h
    · exact h
    · exfalso
      apply hne
      have e1 : Y ⊓ Z = Y := Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [h, hY])
      have e2 : Y ⊓ Z = Z := Subgroup.eq_of_le_of_card_ge inf_le_right (by rw [h, hZ])
      rw [← e1, e2]
  rw [h2, hY, hZ, mul_one] at h1
  rw [h1]
  norm_num

private theorem r90y12_sylow {G : Type} [Group G] [Finite G] (K E : Subgroup G) (hEK : E ≤ K)
    (hE : Nat.card E = 3 ^ 2)
    (hbound : ∀ U : Subgroup G, U ≤ K → IsPGroup 3 U → Nat.card U ∣ 3 ^ 2) :
    IsSylowOf 3 E K := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨S, hS⟩ := CFSG.ABGLocalTools.exists_isSylowOf 3 K
  have h1 : 3 ^ (Nat.card K).factorization 3 ∣ 3 ^ 2 := hS.card_eq ▸ hbound S hS.le hS.isPGroup
  have h2 : (Nat.card K).factorization 3 ≤ 2 := (Nat.pow_dvd_pow_iff_le_right (by norm_num)).mp h1
  have h3 : 3 ^ 2 ∣ Nat.card K := hE ▸ Subgroup.card_dvd_of_le hEK
  have h4 : 2 ≤ (Nat.card K).factorization 3 :=
    (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_three Nat.card_pos.ne').mp h3
  refine CFSG.ABGLocalTools.isSylowOf_of_card hEK ?_
  rw [hE, le_antisymm h2 h4]

private theorem r90y12_final {G : Type} [Group G] [Finite G] (Y E : Subgroup G)
    (hY : Nat.card Y = 3) (hE : Nat.card E = 3 ^ 2)
    (hS : IsSylowOf 3 E (centralizer (Y : Set G))) :
    (Nat.card (normalizer (Y : Set G))).factorization 3 = 2 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : IsCyclic Y := isCyclic_of_prime_card hY
  have hv : (Nat.card (centralizer (Y : Set G))).factorization 3 = 2 := by
    have h := hS.card_eq
    rw [hE] at h
    exact (Nat.pow_right_injective (by norm_num) h).symm
  have hdvd := CFSG.GH74.GLS.Stage4.Q9.relIndex_centralizer_normalizer_dvd_totient Y
  rw [hY, Nat.totient_prime Nat.prime_three] at hdvd
  have hCN : centralizer (Y : Set G) ≤ normalizer (Y : Set G) :=
    Subgroup.centralizer_le_normalizer (Y : Set G)
  have hmul := Subgroup.relIndex_mul_card (H := centralizer (Y : Set G))
    (K := normalizer (Y : Set G))
  rw [inf_eq_left.mpr hCN] at hmul
  have hN0 : Nat.card (normalizer (Y : Set G)) ≠ 0 := Nat.card_pos.ne'
  rw [← hmul] at hN0 ⊢
  rw [Nat.factorization_mul (left_ne_zero_of_mul hN0) (right_ne_zero_of_mul hN0),
    Finsupp.add_apply, hv, Nat.factorization_eq_zero_of_not_dvd, zero_add]
  intro h3
  have := Nat.dvd_trans h3 hdvd
  omega

private theorem r90y12_Z_comm {G : Type} [Group G] (Q : Subgroup G) {z : G} (hz : z ∈ ZOf Q)
    {q : G} (hq : q ∈ Q) : q * z = z * q :=
  (Subgroup.mem_centralizer_iff.mp hz.2) q hq

theorem r890_y12
    (hJ3 : J2OrderThree_890) (hY3B : Y3B_890) : Y12_890 := by
  intro G _ _ D L P J Y n cfg hYZ h885 h886 _ h888 h889
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hC := hY3B hJ3 G D L P J Y n cfg hYZ h885 h886 h889
  have hS := cfg.set880
  have hPL : P ≤ L := h889 L P hS
  have hPM : P ≤ D.M := hS.sylow.le
  have hZP : ZOf (P ⊓ L) ≤ P := inf_le_left.trans inf_le_left
  have hZcomm : ∀ y ∈ Y, ∀ z ∈ ZOf (P ⊓ L), y * z = z * y := fun y hy z hz =>
    r90y12_Z_comm _ hz ⟨cfg.le_P hy, hPL (cfg.le_P hy)⟩
  have hYZc : Y ≤ centralizer (ZOf (P ⊓ L) : Set G) := fun y hy =>
    Subgroup.mem_centralizer_iff.mpr fun z hz => (hZcomm y hy z hz).symm
  have hEcard : Nat.card (Y ⊔ ZOf (P ⊓ L) : Subgroup G) = 3 ^ 2 :=
    r90y12_card_sup cfg.card_Y (h886 L P hS).1 cfg.ne_Z
      (hYZc.trans (Subgroup.centralizer_le_normalizer _))
  have hEM : Y ⊔ ZOf (P ⊓ L) ≤ D.M := sup_le (cfg.le_P.trans hPM) (hZP.trans hPM)
  have hNE : normalizer ((Y ⊔ ZOf (P ⊓ L) : Subgroup G) : Set G) ≤ D.M :=
    CFSG.LocalAnalysis.RankThreeUC.normalizer_le_of_mem_uniqueSet D.maxLocal
      (CFSG.LocalAnalysis.RankThreeUC.mem_uniqueSet_of_le (h888 L P hS) le_sup_right hEM)
  have : IsCyclic Y := isCyclic_of_prime_card cfg.card_Y
  have hEC : Y ⊔ ZOf (P ⊓ L) ≤ centralizer (Y : Set G) :=
    sup_le (Subgroup.le_centralizer_iff_isMulCommutative.mpr inferInstance) fun z hz =>
      Subgroup.mem_centralizer_iff.mpr fun y hy => hZcomm y hy z hz
  have hbound : ∀ U : Subgroup G, U ≤ D.M ⊓ centralizer (Y : Set G) → IsPGroup 3 U →
      Nat.card U ∣ 3 ^ 2 := fun U hU hUp =>
    r90y12_bound hS.sylow hPL cfg.normal_L hC (hU.trans inf_le_left) (hU.trans inf_le_right) hUp
  have hSyl : IsSylowOf 3 (Y ⊔ ZOf (P ⊓ L)) (D.M ⊓ centralizer (Y : Set G)) :=
    r90y12_sylow _ _ (le_inf hEM hEC) hEcard hbound
  exact r90y12_final Y _ cfg.card_Y hEcard
    (CFSG.ABGLocalTools.isSylowOf_of_normalizer_inf_le hSyl (inf_le_left.trans hNE))

end R90Y12

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8
