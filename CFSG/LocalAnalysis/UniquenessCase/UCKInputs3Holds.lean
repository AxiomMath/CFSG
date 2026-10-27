module

public import CFSG.LocalAnalysis.UniquenessCase.UC6K591Defs
public import CFSG.LocalAnalysis.UniquenessCase.UCKInputs3
public import CFSG.LocalAnalysis.AGLEmbedding.CatalogSchreier
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.SchurRankHolds
public import CFSG.LocalAnalysis.RankThreeTheoremC.OutCyclicThree

import CFSG.RankThree.PartOne.S11d.OutCentral

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UCK

open CFSG.Open Subgroup
open CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.SchurRank
  (schurMultiplierRankFact_holds)

section KSch


theorem kSch_holds : KSch := by
  intro J _ _ hs hK
  by_cases hnab : ∃ a b : J, a * b ≠ b * a
  · have hcat : CFSG.Open.IsCatalogGroup J :=
      hK.isCatalogGroup_of_surjective ⊤ hnab (Subgroup.subtype ⊤) (fun x => ⟨⟨x, trivial⟩, rfl⟩)
    exact CFSG.AGLEmbedding.kFactCatalogSchreier_holds J hs hnab hcat
  · push Not at hnab
    have hcyc : IsCyclic J := by
      by_cases h1 : ∀ g : J, g = 1
      · exact ⟨⟨1, fun g => ⟨0, by simp [h1 g]⟩⟩⟩
      · push Not at h1
        obtain ⟨g, hg⟩ := h1
        have hn : (Subgroup.zpowers g).Normal :=
          ⟨fun n hn h => by rwa [hnab h n, mul_inv_cancel_right]⟩
        rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.zpowers g) with h | h
        · exact absurd (Subgroup.zpowers_eq_bot.1 h) hg
        · exact ⟨⟨g, fun x => Subgroup.mem_zpowers_iff.1 (h ▸ Subgroup.mem_top x)⟩⟩
    haveI : Group.IsSolvable (MulAut J) :=
      Group.isSolvable_of_isSolvable_injective (f := (IsCyclic.mulAutMulEquiv J).toMonoidHom)
        (IsCyclic.mulAutMulEquiv J).injective
    change Group.IsSolvable (MulAut J ⧸ (MulAut.conj : J →* MulAut J).range)
    infer_instance

end KSch

section KMult


private theorem exists_not_comm_quotient_center {J : Type} [Group J]
    (hq : CFSG.Open.IsQuasisimple J) : ∃ a b : J ⧸ Subgroup.center J, a * b ≠ b * a := by
  obtain ⟨hperf, hsimple⟩ := hq
  by_contra hab
  push Not at hab
  have hcomm : ∀ a b : J, a * b * a⁻¹ * b⁻¹ ∈ Subgroup.center J := by
    intro a b
    rw [← QuotientGroup.eq_one_iff]
    simp only [QuotientGroup.mk_mul, QuotientGroup.mk_inv]
    rw [hab (a : J ⧸ Subgroup.center J) b]
    group
  have hle : commutator J ≤ Subgroup.center J := by
    rw [commutator_def, Subgroup.commutator_le]
    intro a _ b _
    rw [commutatorElement_def]
    exact hcomm a b
  rw [hperf, top_le_iff] at hle
  have hall : ∀ q : J ⧸ Subgroup.center J, q = 1 := by
    intro q
    induction q using QuotientGroup.induction_on with
    | H x => exact (QuotientGroup.eq_one_iff x).2 (hle ▸ Subgroup.mem_top x)
  have := hsimple
  obtain ⟨a, b, hab'⟩ := exists_pair_ne (J ⧸ Subgroup.center J)
  exact hab' ((hall a).trans (hall b).symm)

theorem kMult_holds : KMult := by
  intro J _ _ hq hK p hp hp5 hpz h3
  by_contra hne
  haveI : Fact p.Prime := ⟨hp⟩
  have hdvd : p ∣ Nat.card (Subgroup.center J) :=
    (hpz.card_eq_or_dvd).resolve_left fun h => hne (Subgroup.eq_bot_of_card_eq _ h)
  haveI : IsSimpleGroup (J ⧸ Subgroup.center J) := hq.2
  have hnab := exists_not_comm_quotient_center hq
  have hcat : CFSG.Open.IsCatalogGroup (J ⧸ Subgroup.center J) :=
    hK.isCatalogGroup_of_surjective ⊤ hnab (Subgroup.subtype ⊤) (fun x => ⟨⟨x, trivial⟩, rfl⟩)
  have h4 := schurMultiplierRankFact_holds p hp hp5 J hq hcat hdvd
  omega

end KMult

section K631


theorem k631_holds : K631 := by
  intro Y _ _ hY r hr hr2 N hNn hsN hnc hC hrk B hB hBN
  haveI := hNn
  haveI := hsN
  haveI : Fact r.Prime := ⟨hr⟩
  have hnab : ∃ a b : ↥N, a * b ≠ b * a := by
    by_contra h
    push Not at h
    exact hnc ⟨⟨fun a b => h a b⟩⟩
  have hcat : CFSG.Open.IsCatalogGroup ↥N :=
    hY.isCatalogGroup_of_surjective N hnab (MonoidHom.id ↥N) Function.surjective_id
  have hrk' : CFSG.Open.pRank r (⊤ : Subgroup ↥N) ≤ 1 := by
    have h := CFSG.SectionRank.pRank_le_map hr.one_lt N.subtype N.subtype_injective ⊤
    rw [Subgroup.map_top, Subgroup.range_subtype] at h
    omega
  obtain ⟨T⟩ : Nonempty (Sylow r ↥N) := inferInstance
  have hTcyc : IsCyclic ↥(T : Subgroup ↥N) := by
    have hLX : (T : Subgroup ↥N).map N.subtype ≤ N := by
      rintro _ ⟨x, -, rfl⟩
      exact x.2
    have hr' : CFSG.pRank r ↥N ≤ 1 := by
      rw [CFSG.SectionRank.pRank_eq_open_pRank_top r ↥N]
      exact hrk'
    have hcycX : IsCyclic ((T : Subgroup ↥N).map N.subtype) :=
      CFSG.RankThree.PartOne.isCyclic_of_pRank_le_one hr hr2 hLX (T.isPGroup'.map N.subtype) hr'
    exact (Subgroup.equivMapOfInjective (T : Subgroup ↥N) N.subtype
      N.subtype_injective).isCyclic.mpr hcycX
  have hOut := CFSG.LocalAnalysis.RankThreeTheoremC.kFactOutCyclic_holds ↥N hsN hnab hcat r hr hr2
    T hTcyc
  let ψY : Y →* CFSG.ComponentClassification.OuterAutomorphisms.Outer ↥N :=
    (QuotientGroup.mk' (CFSG.ComponentClassification.OuterAutomorphisms.inner ↥N)).comp
      (MulAut.conjNormal : Y →* MulAut ↥N)
  have hinj : Function.Injective (ψY.comp B.subtype) := by
    rw [injective_iff_map_eq_one]
    intro b hb
    have hmem : (MulAut.conjNormal (b : Y) : MulAut ↥N) ∈
        CFSG.ComponentClassification.OuterAutomorphisms.inner ↥N :=
      (QuotientGroup.eq_one_iff _).1 hb
    obtain ⟨n, hn⟩ := hmem
    have hcent : ((n : Y)⁻¹ * (b : Y)) ∈ Subgroup.centralizer (N : Set Y) := by
      rw [Subgroup.mem_centralizer_iff]
      intro x hx
      have h1 := congrArg (fun e : MulAut ↥N => ((e ⟨x, hx⟩ : ↥N) : Y)) hn
      simp only [MulAut.conj_apply, MulAut.conjNormal_apply, Subgroup.coe_mul,
        Subgroup.coe_inv] at h1
      calc x * ((n : Y)⁻¹ * (b : Y)) = (n : Y)⁻¹ * ((n : Y) * x * (n : Y)⁻¹) * (b : Y) := by group
        _ = (n : Y)⁻¹ * ((b : Y) * x * (b : Y)⁻¹) * (b : Y) := by rw [h1]
        _ = ((n : Y)⁻¹ * (b : Y)) * x := by group
    rw [hC, Subgroup.mem_bot] at hcent
    have hbn : (b : Y) = (n : Y) := by
      have := congrArg (fun z => (n : Y) * z) hcent
      simpa using this
    have hbB : (b : Y) ∈ B ⊓ N := ⟨b.2, hbn ▸ n.2⟩
    rw [hBN, Subgroup.mem_bot] at hbB
    exact Subtype.ext hbB
  obtain ⟨k, hk⟩ := (IsPGroup.iff_card).1 (CFSG.Open.IsElemAbelian.isPGroup hB)
  have hE : CFSG.Open.IsElemAbelian r (B.map ψY) := CFSG.SectionRank.isElemAbelian_map hB ψY
  have hrange : (ψY.comp B.subtype).range = B.map ψY := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
  have hcard : Nat.card (B.map ψY) = r ^ k := by
    rw [← hrange, ← hk]
    exact (Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv).symm
  have hkle : k ≤ CFSG.Open.pRank r
      (⊤ : Subgroup (CFSG.ComponentClassification.OuterAutomorphisms.Outer ↥N)) :=
    CFSG.SectionRank.le_pRank hr.one_lt le_top hE hcard
  calc Nat.card B = r ^ k := hk
    _ ≤ r ^ 1 := Nat.pow_le_pow_right hr.pos (hkle.trans hOut)
    _ = r := pow_one r

end K631

end CFSG.LocalAnalysis.UniquenessCase.UCK
