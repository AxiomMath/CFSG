module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight56U14CoverDefs
import CFSG.GroupTheory.SylowIntersectionControl.Basic
import CFSG.HardMathSupport.Solomon.Proving.GLBCoreNormalizer
import CFSG.LocalAnalysis.AGLEmbedding.Norton.OrdinaryProofs.SylowTransport

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8

open CFSG.Open Subgroup

private theorem covfacts_gamma_dvd_card {H : Type} [Group H] [Finite H] {p : ℕ} [Fact p.Prime]
    {A : Subgroup H} (hA : IsPGroup p A) (hne : A ≠ ⊥) : p ∣ Nat.card A := by
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hA
  rcases n with _ | n
  · exact absurd (Subgroup.eq_bot_of_card_eq A (by simpa using hn)) hne
  · rw [hn]
    exact dvd_pow_self p n.succ_ne_zero

private theorem covfacts_gamma_one_le_pRank {H : Type} [Group H] [Finite H] {p : ℕ} [Fact p.Prime]
    {A : Subgroup H} (hA : IsPGroup p A) (hne : A ≠ ⊥) : 1 ≤ CFSG.Open.pRank p A := by
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' p (covfacts_gamma_dvd_card hA hne)
  have hE : Nat.card (Subgroup.zpowers (x : H)) = p := by
    rw [Nat.card_zpowers, Subgroup.orderOf_coe, hx]
  exact CFSG.SectionRank.le_pRank (Fact.out : p.Prime).one_lt (Subgroup.zpowers_le.mpr x.2)
    (CFSG.GroupTheory.isElemAbelian_of_card_prime hE) (k := 1) (by simpa using hE)

private theorem covfacts_gamma_normalizer_le {H : Type} [Group H] [Finite H] {p : ℕ} [Fact p.Prime]
    {U A : Subgroup H} (hU : IsPGroup p U) (hAU : A ≤ U) (hne : A ≠ ⊥) :
    Subgroup.normalizer (A : Set H) ≤ GLBCore p 1 U :=
  CFSG.HardMathSupport.Solomon.Proving.normalizer_le_glbCore hAU
    (covfacts_gamma_one_le_pRank (hU.to_le hAU) hne)

private theorem covfacts_gamma_le_core {H : Type} [Group H] [Finite H] {p : ℕ} [Fact p.Prime]
    {U : Subgroup H} (hU : IsPGroup p U) (hne : U ≠ ⊥) : U ≤ GLBCore p 1 U :=
  Subgroup.le_normalizer.trans (covfacts_gamma_normalizer_le hU le_rfl hne)

private theorem covfacts_gamma_mem_map_conj {H : Type} [Group H] (P : Subgroup H) (g x : H) :
    x ∈ P.map (MulAut.conj g).toMonoidHom ↔ g⁻¹ * x * g ∈ P :=
  Subgroup.mem_map_equiv

private theorem covfacts_gamma_map_conj_of_mem {H : Type} [Group H] {K : Subgroup H} {k : H}
    (hk : k ∈ K) : K.map (MulAut.conj k).toMonoidHom = K := by
  ext x
  rw [covfacts_gamma_mem_map_conj]
  constructor
  · intro h
    have e : k * (k⁻¹ * x * k) * k⁻¹ = x := by group
    simpa only [e] using K.mul_mem (K.mul_mem hk h) (K.inv_mem hk)
  · intro h
    exact K.mul_mem (K.mul_mem (K.inv_mem hk) h) hk

private theorem covfacts_gamma_exists_sylow_ge {H : Type} [Group H] [Finite H] {p : ℕ}
    [Fact p.Prime] {K A : Subgroup H} (hA : IsPGroup p A) (hAK : A ≤ K) :
    ∃ T, CFSG.ABGLocalTools.IsSylowOf p T K ∧ A ≤ T := by
  obtain ⟨Q, hQ⟩ := (hA.comap_subtype (K := K)).exists_le_sylow
  exact ⟨(Q : Subgroup K).map K.subtype, ⟨Q, rfl⟩, fun a ha =>
    ⟨⟨a, hAK ha⟩, hQ (Subgroup.mem_comap.mpr ha), rfl⟩⟩

private theorem covfacts_gamma_core_eq {H : Type} [Group H] [Finite H] {p : ℕ} [Fact p.Prime]
    {U T : Subgroup H} (hU : CFSG.ABGLocalTools.IsSylowOf p U ⊤) (hne : U ≠ ⊥)
    (hT : CFSG.ABGLocalTools.IsSylowOf p T (GLBCore p 1 U)) :
    GLBCore p 1 T = GLBCore p 1 U := by
  have hUΓ : CFSG.ABGLocalTools.IsSylowOf p U (GLBCore p 1 U) :=
    hU.of_le (covfacts_gamma_le_core hU.isPGroup hne) le_top
  obtain ⟨k, hk, hconj⟩ := hUΓ.exists_mem_conj hT
  have hTeq : T = U.map (MulAut.conj k).toMonoidHom := by
    ext x
    rw [covfacts_gamma_mem_map_conj]
    exact hconj x
  rw [hTeq, CFSG.AGLEmbedding.Norton.OrdinaryProofs.GLBCore_map_conj,
    covfacts_gamma_map_conj_of_mem hk]

private theorem covfacts_gamma_normalizer_le_core {H : Type} [Group H] [Finite H] {p : ℕ}
    [Fact p.Prime] {U A : Subgroup H} (hU : CFSG.ABGLocalTools.IsSylowOf p U ⊤) (hUne : U ≠ ⊥)
    (hA : IsPGroup p A) (hAΓ : A ≤ GLBCore p 1 U) (hne : A ≠ ⊥) :
    Subgroup.normalizer (A : Set H) ≤ GLBCore p 1 U := by
  obtain ⟨T, hT, hAT⟩ := covfacts_gamma_exists_sylow_ge hA hAΓ
  rw [← covfacts_gamma_core_eq hU hUne hT]
  exact covfacts_gamma_normalizer_le hT.isPGroup hAT hne

private theorem covfacts_gamma_eq_of_normalizer_le {H : Type} [Group H] [Finite H] {p : ℕ}
    [Fact p.Prime] {A T D : Subgroup H} (hA : CFSG.ABGLocalTools.IsSylowOf p A D)
    (hT : IsPGroup p T) (hAT : A ≤ T) (hN : Subgroup.normalizer (A : Set H) ≤ D) : A = T := by
  by_contra hne
  let Q : Subgroup T := A.subgroupOf T
  have hQlt : Q < ⊤ := by
    refine lt_top_iff_ne_top.mpr fun hQtop => hne (le_antisymm hAT fun x hxT => ?_)
    have hxQ : (⟨x, hxT⟩ : T) ∈ Q := by
      rw [hQtop]
      exact Subgroup.mem_top _
    exact hxQ
  have : Group.IsNilpotent T := hT.isNilpotent
  obtain ⟨y, hyN, hyQ⟩ := SetLike.exists_of_lt (Group.normalizerCondition_of_isNilpotent Q hQlt)
  let B : Subgroup H := (Subgroup.normalizer (Q : Set T)).map T.subtype
  have hBN : B ≤ Subgroup.normalizer (A : Set H) := by
    rintro _ ⟨w, hw, rfl⟩
    have hw' : w ∈ (Subgroup.normalizer (A : Set H)).subgroupOf T := by
      rw [Subgroup.subgroupOf_normalizer_eq hAT]
      exact hw
    exact Subgroup.mem_subgroupOf.mp hw'
  have hAB : A ≤ B := fun a ha => ⟨⟨a, hAT ha⟩, Subgroup.le_normalizer ha, rfl⟩
  have hBp : IsPGroup p B := hT.to_le (Subgroup.map_subtype_le _)
  have hyB : (y : H) ∈ B := ⟨y, hyN, rfl⟩
  rw [hA.eq_of_le hAB (hBN.trans hN) hBp] at hyB
  exact hyQ hyB

private theorem covfacts_gamma_isSylowOf_of_normalizer_le {H : Type} [Group H] [Finite H] {p : ℕ}
    [Fact p.Prime] {A D K : Subgroup H} (hA : CFSG.ABGLocalTools.IsSylowOf p A D) (hDK : D ≤ K)
    (hN : Subgroup.normalizer (A : Set H) ≤ D) : CFSG.ABGLocalTools.IsSylowOf p A K := by
  obtain ⟨T, hT, hAT⟩ := covfacts_gamma_exists_sylow_ge hA.isPGroup (hA.le.trans hDK)
  rwa [covfacts_gamma_eq_of_normalizer_le hA hT.isPGroup hAT hN]

private theorem covfacts_gamma_ne_bot {H : Type} [Group H] [Finite H] {p : ℕ} [Fact p.Prime]
    {A D : Subgroup H} (hA : CFSG.ABGLocalTools.IsSylowOf p A D) (hdvd : p ∣ Nat.card D) :
    A ≠ ⊥ := by
  intro h
  have hpos := Nat.Prime.factorization_pos_of_dvd (Fact.out : p.Prime) Nat.card_pos.ne' hdvd
  have hlt := Nat.one_lt_pow hpos.ne' (Fact.out : p.Prime).one_lt
  have hcard := hA.card_eq
  rw [h, Subgroup.card_bot] at hcard
  omega

private theorem covfacts_gamma_core_eq_of_dvd {H : Type} [Group H] [Finite H] {p : ℕ} [Fact p.Prime]
    {U V : Subgroup H} (hU : CFSG.ABGLocalTools.IsSylowOf p U ⊤) (hUne : U ≠ ⊥)
    (hV : CFSG.ABGLocalTools.IsSylowOf p V ⊤) (hVne : V ≠ ⊥)
    (hdvd : p ∣ Nat.card (GLBCore p 1 U ⊓ GLBCore p 1 V : Subgroup H)) :
    GLBCore p 1 U = GLBCore p 1 V := by
  obtain ⟨A, hA⟩ := CFSG.ABGLocalTools.exists_isSylowOf p (GLBCore p 1 U ⊓ GLBCore p 1 V)
  have hne := covfacts_gamma_ne_bot hA hdvd
  have hN : Subgroup.normalizer (A : Set H) ≤ GLBCore p 1 U ⊓ GLBCore p 1 V :=
    le_inf
      (covfacts_gamma_normalizer_le_core hU hUne hA.isPGroup (hA.le.trans inf_le_left) hne)
      (covfacts_gamma_normalizer_le_core hV hVne hA.isPGroup (hA.le.trans inf_le_right) hne)
  rw [← covfacts_gamma_core_eq hU hUne
      (covfacts_gamma_isSylowOf_of_normalizer_le hA inf_le_left hN),
    covfacts_gamma_core_eq hV hVne
      (covfacts_gamma_isSylowOf_of_normalizer_le hA inf_le_right hN)]

private theorem covfacts_gamma_mem_normalizer_of_conj {H : Type} [Group H] {S : Subgroup H}
    {g k : H} (h : ∀ x, x ∈ S.map (MulAut.conj g).toMonoidHom ↔ k⁻¹ * x * k ∈ S) :
    g⁻¹ * k ∈ Subgroup.normalizer (S : Set H) := by
  rw [Subgroup.mem_normalizer_iff]
  intro y
  have hy := (covfacts_gamma_mem_map_conj S g (k * y * k⁻¹)).symm.trans (h (k * y * k⁻¹))
  have e1 : k⁻¹ * (k * y * k⁻¹) * k = y := by group
  have e2 : g⁻¹ * (k * y * k⁻¹) * g = g⁻¹ * k * y * (g⁻¹ * k)⁻¹ := by group
  rw [e1, e2] at hy
  exact hy.symm

private theorem covfacts_gamma_mem_core {H : Type} [Group H] [Finite H] {p : ℕ} [Fact p.Prime]
    {S : Subgroup H} (hS : CFSG.ABGLocalTools.IsSylowOf p S ⊤) (hSne : S ≠ ⊥) {g : H}
    (hdvd : p ∣ Nat.card
      (GLBCore p 1 S ⊓ GLBCore p 1 (S.map (MulAut.conj g).toMonoidHom) : Subgroup H)) :
    g ∈ GLBCore p 1 S := by
  have hV : CFSG.ABGLocalTools.IsSylowOf p (S.map (MulAut.conj g).toMonoidHom) ⊤ := by
    have h := CFSG.GroupTheory.isSylowOf_map_conj hS g
    rwa [Subgroup.map_top_of_surjective (MulAut.conj g).toMonoidHom
      (MulAut.conj g).surjective] at h
  have hVne : S.map (MulAut.conj g).toMonoidHom ≠ ⊥ := fun h =>
    hSne ((Subgroup.map_eq_bot_iff_of_injective S
      (f := (MulAut.conj g).toMonoidHom) (MulAut.conj g).injective).mp h)
  have heq := covfacts_gamma_core_eq_of_dvd hS hSne hV hVne hdvd
  have hSΓ := hS.of_le (covfacts_gamma_le_core hS.isPGroup hSne) le_top
  have hVΓ : CFSG.ABGLocalTools.IsSylowOf p (S.map (MulAut.conj g).toMonoidHom)
      (GLBCore p 1 S) := by
    rw [heq]
    exact hV.of_le (covfacts_gamma_le_core hV.isPGroup hVne) le_top
  obtain ⟨k, hk, hconj⟩ := hSΓ.exists_mem_conj hVΓ
  have hw := covfacts_gamma_normalizer_le hS.isPGroup le_rfl hSne
    (covfacts_gamma_mem_normalizer_of_conj hconj)
  have hg := (GLBCore p 1 S).mul_mem hk ((GLBCore p 1 S).inv_mem hw)
  have e : k * (g⁻¹ * k)⁻¹ = g := by group
  rwa [e] at hg

theorem kFactGammaStrong : KFactGammaStrong := by
  intro H _ _ p hp S hS hSne hΓ
  have : Fact p.Prime := ⟨hp⟩
  have hle : S ≤ GLBCore p 1 S := covfacts_gamma_le_core hS.isPGroup hSne
  unfold CFSG.RankThree.PartOne.IsStronglyPEmbedded
  refine ⟨hΓ, (covfacts_gamma_dvd_card hS.isPGroup hSne).trans (Subgroup.card_dvd_of_le hle), ?_⟩
  intro g hg hdvd
  refine hg (covfacts_gamma_mem_core hS hSne ?_)
  rw [CFSG.AGLEmbedding.Norton.OrdinaryProofs.GLBCore_map_conj]
  exact hdvd

open CFSG.Blueprint (LieModel)

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8
