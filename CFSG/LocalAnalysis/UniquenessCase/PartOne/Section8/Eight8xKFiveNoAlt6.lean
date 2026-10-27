module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight8xKLeaves
import CFSG.Adapters.LieModelL3U3Sylow
import CFSG.ClassicalInvolution.Q3.TL4MF163Psl
import CFSG.GroupTheory.ThreeTranspositions.IndexEnd
import CFSG.LargeExtraspecial.S45QSix
import CFSG.LocalAnalysis.AGLEmbedding.LinTwoBorelSolvable
import CFSG.LocalAnalysis.ComponentClassification.HarrisLitLift
import CFSG.LocalAnalysis.EvenBN.GMSK.SzFacts
import CFSG.LocalAnalysis.EvenSporadicStandard.McLStd.McL
import CFSG.LocalAnalysis.OddStandard.Seitz77Sec27StructAux
import CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.GroupMcL
import CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.GroupTits
import CFSG.LocalAnalysis.SeitzReduction.LinearPilotCatEvenOuterPSL
import CFSG.LocalAnalysis.SeitzReduction.RankOneSuzukiRegularStab
import CFSG.LocalAnalysis.StandardType.GGSporKOrd7Suzuki
import CFSG.LocalAnalysis.UniquenessCase.UC6K36SporGe4
import CFSG.LocalAnalysis.UniquenessCase.UC6K620ExcFi22
import CFSG.LocalAnalysis.UniquenessCase.UC6TitsAut
import CFSG.Quasithin.Vol2.Ch8Sec2L827F
import CFSG.RankThree.PartTwo.Sec21.Hering214KGen
import CFSG.SignalizerFunctorTheorem.McBride.Prelim.KGroup

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8

section

open CFSG.Blueprint (LieModel)
open CFSG.RankThree.PartOne (IsStronglyPEmbedded)
open CFSG.GH74.GLS.Stage2.Signalizer.Odd87 (IsSection)
open CFSG.AGLEmbedding CFSG.PSL2Table

private theorem nonempty_mulEquiv_psl2GF_of_lieModel {K : Type} [Group K] {p n : ℕ} [Fact p.Prime]
    (h : LieModel K .PSL 2 p n) : Nonempty (K ≃* PSL2GF p n) := by
  obtain ⟨hp, h4, F, _, _, hF, ⟨e⟩⟩ := CFSG.ClassicalInvolution.Q3.TL4.MF163.psl2_of_lieModel h
  have hn : n ≠ 0 := by rintro rfl; simp at h4
  have hG : Nat.card (GaloisField p n) = p ^ n := GaloisField.card p n hn
  obtain ⟨e'⟩ := CFSG.RankThree.PartOne.CTP.nonempty_psl2_equiv_of_card_eq
    (k₁ := F) (k₂ := GaloisField p n) (hF.trans hG.symm)
  exact ⟨e.trans e'⟩

private theorem isSolvable_normalizer_sylow_psl2GF (p n : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) (hn : 1 ≤ n)
    (T : Sylow p (PSL2GF p n)) :
    Group.IsSolvable (Subgroup.normalizer ((T : Subgroup (PSL2GF p n)) : Set (PSL2GF p n))) := by
  have hF : ringChar (GaloisField p n) ≠ 2 := by rw [ringChar.eq (GaloisField p n) p]; exact hp2
  obtain ⟨U, hU⟩ := exists_sylow_eq_unipotent_psl2GF hp2 hn
  obtain ⟨g, rfl⟩ := MulAction.exists_smul_eq (PSL2GF p n) U T
  have hgU : ((g • U : Sylow p (PSL2GF p n)) : Subgroup (PSL2GF p n)) =
      (unipotent (GaloisField p n)).map (MulAut.conj g).toMonoidHom := by
    ext x
    rw [Sylow.coe_subgroup_smul, Subgroup.mem_smul_pointwise_iff_exists, Subgroup.mem_map, hU]
    rfl
  rw [hgU, ← Subgroup.map_equiv_normalizer_eq, normalizer_unipotent_eq_borel hF]
  exact CFSG.SignalizerFunctorTheorem.McBride.isSolvable_map_mulEquiv _ isSolvable_borel_psl2

private theorem not_isSection_alt6_of_stronglyEmbedded_psl2GF (p n : ℕ) [Fact p.Prime] (hp2 : p ≠ 2)
    (hn : 1 ≤ n) {H : Subgroup (PSL2GF p n)} (hH : IsStronglyPEmbedded p H) :
    ¬ IsSection (alternatingGroup (Fin 6)) ↥H := by
  intro hsec
  obtain ⟨T, hTH⟩ :=
    CFSG.GroupTheory.ThreeTranspositions.exists_sylow_le_of_isStronglyPEmbedded Fact.out hH
  have hpG : p ∣ Nat.card (PSL2GF p n) := hH.2.1.trans (Subgroup.card_subgroup_dvd_card H)
  have hT1 : (T : Subgroup (PSL2GF p n)) ≠ ⊥ := T.ne_bot_of_dvd_card hpG
  have hNH : Subgroup.normalizer ((T : Subgroup (PSL2GF p n)) : Set (PSL2GF p n)) ≤ H :=
    hH.normalizer_le hT1 T.isPGroup' hTH
  have hco := psl2GF_borelCoatom p n hp2 hn T
  have hEq : Subgroup.normalizer ((T : Subgroup (PSL2GF p n)) : Set (PSL2GF p n)) = H := by
    by_contra hne
    exact hH.1 (hco.2 H (lt_of_le_of_ne hNH hne))
  have hsol : Group.IsSolvable ↥H := hEq ▸ isSolvable_normalizer_sylow_psl2GF p n hp2 hn T
  exact CFSG.Quasithin.H13.not_isSolvable_alt6_827 (hsec.isSolvable hsol)

private theorem noA6_psl2 {K : Type} [Group K] {n : ℕ} (h : LieModel K .PSL 2 5 n) (H : Subgroup K)
    (hH : IsStronglyPEmbedded 5 H) : ¬ IsSection (alternatingGroup (Fin 6)) ↥H := by
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  obtain ⟨-, h4, -⟩ := CFSG.ClassicalInvolution.Q3.TL4.MF163.psl2_of_lieModel h
  have hn : 1 ≤ n := by
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp at h4
    · exact hn
  obtain ⟨e⟩ := nonempty_mulEquiv_psl2GF_of_lieModel h
  have hH' := CFSG.LocalAnalysis.UniquenessCase.UCK.isStronglyPEmbedded_map_mulEquiv e hH
  intro hsec
  have e' : ↥H ≃* ↥(H.map e.toMonoidHom) := H.equivMapOfInjective e.toMonoidHom e.injective
  exact not_isSection_alt6_of_stronglyEmbedded_psl2GF 5 n (by norm_num) hn hH'
    (hsec.of_equiv e'.symm)

end

section

open CFSG.RankThree.PartOne (IsStronglyPEmbedded)
open CFSG.GH74.GLS.Stage2.Signalizer.Odd87 (IsSection)

private theorem isStronglyPEmbedded_inf_normal {Y : Type} [Group Y] [Finite Y] {p : ℕ} [Fact p.Prime]
    {S K : Subgroup Y} (hS : IsStronglyPEmbedded p S) (hK : K.Normal) (hpK : p ∣ Nat.card K) :
    IsStronglyPEmbedded p ((K ⊓ S).subgroupOf K) := by
  refine ⟨?_, ?_, ?_⟩
  · intro htop
    rw [Subgroup.subgroupOf_eq_top] at htop
    exact hS.not_dvd_card_of_normal_le (le_inf_iff.mp htop).2 hpK
  · obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := ↥K) p hpK
    have hxo : orderOf (x : Y) = p := by rw [Subgroup.orderOf_coe]; exact hx
    have hzp : IsPGroup p (Subgroup.zpowers (x : Y)) :=
      IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hxo, pow_one])
    obtain ⟨Q, hQ⟩ := hzp.exists_le_sylow
    obtain ⟨T, hTS⟩ :=
      CFSG.GroupTheory.ThreeTranspositions.exists_sylow_le_of_isStronglyPEmbedded Fact.out hS
    obtain ⟨g, hg⟩ := MulAction.exists_smul_eq Y Q T
    have hyT : MulAut.conj g (x : Y) ∈ (T : Subgroup Y) := by
      rw [← hg, Sylow.coe_subgroup_smul]
      exact Subgroup.smul_mem_pointwise_smul _ _ _ (hQ (Subgroup.mem_zpowers _))
    have hyK : MulAut.conj g (x : Y) ∈ K := by
      rw [MulAut.conj_apply]; exact hK.conj_mem _ x.2 g
    have hyo : orderOf (MulAut.conj g (x : Y)) = p := by
      rw [MulEquiv.orderOf_eq]; exact hxo
    have h1 : p ∣ Nat.card ↥(K ⊓ S) :=
      hyo ▸ Subgroup.orderOf_dvd_natCard (K ⊓ S) ⟨hyK, hTS hyT⟩
    rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (inf_le_left : K ⊓ S ≤ K)).toEquiv]
  · intro g hg
    have hgS : (g : Y) ∉ S := fun h => hg (Subgroup.mem_subgroupOf.mpr ⟨g.2, h⟩)
    have hint := hS.2.2 (g : Y) hgS
    intro hdvd
    apply hint
    set H' := (K ⊓ S).subgroupOf K
    set A := H' ⊓ H'.map (MulAut.conj g).toMonoidHom
    have hle : A.map K.subtype ≤ S ⊓ S.map (MulAut.conj (g : Y)).toMonoidHom := by
      rintro z ⟨a, ⟨ha1, b, hb, rfl⟩, rfl⟩
      refine ⟨(Subgroup.mem_subgroupOf.mp ha1).2, (b : Y), (Subgroup.mem_subgroupOf.mp hb).2, ?_⟩
      simp [MulAut.conj_apply]
    have hcard : Nat.card A = Nat.card (A.map K.subtype) :=
      (Subgroup.card_map_of_injective K.subtype_injective).symm
    exact hdvd.trans (hcard ▸ Subgroup.card_dvd_of_le hle)

private theorem isSection_inf_of_solvable {Y : Type} [Group Y] {S K : Subgroup Y} (hK : K.Normal)
    (hsol : Group.IsSolvable (↥S ⧸ (K.subgroupOf S)))
    (h : IsSection (alternatingGroup (Fin 6)) ↥S) :
    IsSection (alternatingGroup (Fin 6)) ↥((K ⊓ S).subgroupOf K) := by
  have := CFSG.LargeExtraspecial.S45Q.isSimpleGroup_alternatingGroup_six
  have : (K.subgroupOf S).Normal := Subgroup.normal_subgroupOf
  rcases h.dichotomy (K.subgroupOf S) with h1 | h2
  · have e1 : ↥(K.subgroupOf S) ≃* ↥(K ⊓ S) :=
      ((K.subgroupOf S).equivMapOfInjective S.subtype S.subtype_injective).trans
        (MulEquiv.subgroupCongr (Subgroup.subgroupOf_map_subtype K S))
    have e2 : ↥((K ⊓ S).subgroupOf K) ≃* ↥(K ⊓ S) :=
      Subgroup.subgroupOfEquivOfLe (inf_le_left : K ⊓ S ≤ K)
    exact h1.of_equiv (e2.trans e1.symm)
  · exact absurd (h2.isSolvable hsol) CFSG.Quasithin.H13.not_isSolvable_alt6_827

open CFSG.Open in
private theorem centralizer_eq_bot_of_genFittingFStar_le {Y : Type} [Group Y] [Finite Y]
    {N : Subgroup Y} (hN : genFittingFStar Y ≤ N) (hZ : Subgroup.center ↥N = ⊥) :
    Subgroup.centralizer (N : Set Y) = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  have hxN : x ∈ N :=
    hN (CFSG.Adapters.generalized_fitting_self_centralizing Y (Subgroup.centralizer_le hN hx))
  have hxZ : (⟨x, hxN⟩ : ↥N) ∈ Subgroup.center ↥N := by
    rw [Subgroup.mem_center_iff]
    intro y
    exact Subtype.ext (Subgroup.mem_centralizer_iff.mp hx y y.2)
  rw [hZ, Subgroup.mem_bot] at hxZ
  exact (Subgroup.mem_bot).mpr (congrArg Subtype.val hxZ)

private theorem isSolvable_quotient_subgroupOf {Y : Type} [Group Y] {S K : Subgroup Y} [K.Normal]
    (hsol : Group.IsSolvable (Y ⧸ K)) : Group.IsSolvable (↥S ⧸ K.subgroupOf S) := by
  let f : ↥S ⧸ K.subgroupOf S →* Y ⧸ K :=
    QuotientGroup.map (K.subgroupOf S) K S.subtype (fun x hx => hx)
  have hf : Function.Injective f := by
    intro a b hab
    induction a using QuotientGroup.induction_on with
    | H a =>
      induction b using QuotientGroup.induction_on with
      | H b =>
        simp only [f] at hab
        rw [QuotientGroup.eq]
        have h1 : ((a : Y))⁻¹ * b ∈ K := QuotientGroup.eq.mp hab
        simpa [Subgroup.mem_subgroupOf] using h1
  exact Group.isSolvable_of_isSolvable_injective hf

private def NoA6InStronglyFiveEmbedded (K : Type) [Group K] : Prop :=
  ∀ H : Subgroup K, IsStronglyPEmbedded 5 H → ¬ IsSection (alternatingGroup (Fin 6)) ↥H

private theorem not_isSection_alt6_of_normal {Y : Type} [Group Y] [Finite Y] {S K : Subgroup Y}
    (hS : IsStronglyPEmbedded 5 S) (hK : K.Normal) (h5 : 5 ∣ Nat.card K)
    (hsol : Group.IsSolvable (Y ⧸ K)) (hKA : NoA6InStronglyFiveEmbedded ↥K) :
    ¬ IsSection (alternatingGroup (Fin 6)) ↥S := by
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  intro h
  exact hKA _ (isStronglyPEmbedded_inf_normal hS hK h5)
    (isSection_inf_of_solvable hK (isSolvable_quotient_subgroupOf hsol) h)

end

section

open Subgroup
open CFSG.Blueprint (LieModel)
open CFSG.LocalAnalysis.UniquenessCase.UC22.F07 (IsAutSz)
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)

private theorem commutator_le_inner {S : Type} [Group S] (hc : ∀ a b : Outer S, a * b = b * a) :
    commutator (MulAut S) ≤ CFSG.ComponentClassification.OuterAutomorphisms.inner S := by
  rw [_root_.commutator_def, Subgroup.commutator_le]
  intro a _ b _
  rw [← QuotientGroup.eq_one_iff, commutatorElement_def, QuotientGroup.mk_mul,
    QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv, QuotientGroup.mk_inv,
    hc (a : Outer S) b]
  group

private theorem inner_le_commutator {S : Type} [Group S] (hS : commutator S = ⊤) :
    CFSG.ComponentClassification.OuterAutomorphisms.inner S ≤ commutator (MulAut S) := by
  rintro _ ⟨s, rfl⟩
  have hs : s ∈ commutator S := hS ▸ Subgroup.mem_top s
  have h1 := Subgroup.mem_map_of_mem (MulAut.conj : S →* MulAut S) hs
  rw [_root_.commutator_def, Subgroup.map_commutator] at h1
  rw [_root_.commutator_def]
  exact Subgroup.commutator_mono le_top le_top h1

private theorem conj_injective {S : Type} [Group S] (hZ : center S = ⊥) :
    Function.Injective (MulAut.conj : S →* MulAut S) := by
  rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
  intro x hx
  rw [← hZ, Subgroup.mem_center_iff]
  intro y
  have hy := DFunLike.congr_fun (MonoidHom.mem_ker.mp hx) y
  simp only [MulAut.conj_apply, MulAut.one_apply] at hy
  calc y * x = x * y * x⁻¹ * x := by rw [hy]
    _ = x * y := by group

private theorem eq_one_of_commute_conj {S : Type} [Group S] (hZ : center S = ⊥) {α : MulAut S}
    (h : ∀ s : S, α * MulAut.conj s = MulAut.conj s * α) : α = 1 := by
  ext s
  rw [MulAut.one_apply]
  have h2 : MulAut.conj (α s) = MulAut.conj s := by
    have h3 : MulAut.conj (α s) = α * MulAut.conj s * α⁻¹ := by
      ext y
      simp [MulAut.conj_apply, MulAut.mul_apply]
    rw [h3, h s, mul_inv_cancel_right]
  exact conj_injective hZ h2

private theorem comm_of_card_dvd_prime {G : Type} [Group G] {p : ℕ} (hp : p.Prime)
    (h : Nat.card G ∣ p) (a b : G) : a * b = b * a := by
  have hne : Nat.card G ≠ 0 := fun h0 => hp.ne_zero (Nat.eq_zero_of_zero_dvd (h0 ▸ h))
  have : Finite G := Nat.finite_of_card_ne_zero hne
  rcases (Nat.dvd_prime hp).mp h with h1 | h1
  · have : Subsingleton G := (Nat.card_eq_one_iff_unique.mp h1).1
    exact Subsingleton.elim _ _
  · have : Fact p.Prime := ⟨hp⟩
    have : IsCyclic G := isCyclic_of_prime_card h1
    have : IsMulCommutative G := IsCyclic.commutative
    exact (IsMulCommutative.is_comm (M := G)).comm a b

private theorem not_three_dvd_card_of_isAutSz
    {Y : Type} [Group Y] [Finite Y] {N : Subgroup Y}
    (hNn : N.Normal) (hC : centralizer (N : Set Y) = ⊥) (h : IsAutSz ↥N 5) :
    ¬ 3 ∣ Nat.card Y := by
  obtain ⟨S, _, hS, ⟨e⟩⟩ := h
  have hS' : LieModel S .twistedB2 0 2 5 := hS
  have : IsSimpleGroup S := CFSG.LocalAnalysis.EvenBN.GMSK.isSimpleGroup_of_lieModel_twistedB2 hS'
  obtain ⟨a, b, hab⟩ := CFSG.LocalAnalysis.EvenBN.GMSK.exists_mul_ne_of_lieModel_twistedB2 hS'
  have hZ : center S = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (center S) with h | h
    · exact h
    · exact absurd (Subgroup.mem_center_iff.mp (h ▸ Subgroup.mem_top a) b).symm hab
  have hP : commutator S = ⊤ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (commutator S) with h | h
    · rw [_root_.commutator_def, Subgroup.commutator_eq_bot_iff_le_centralizer] at h
      exact absurd (Subgroup.mem_centralizer_iff.mp (h (Subgroup.mem_top b)) a
        (Subgroup.mem_top a)) hab
    · exact h
  have hcomm : commutator (MulAut S) = CFSG.ComponentClassification.OuterAutomorphisms.inner S :=
    le_antisymm (commutator_le_inner (comm_of_card_dvd_prime Nat.prime_five
      (CFSG.SeitzReduction.RankOne.card_outer_dvd_of_lieModel_twistedB2 hS')))
      (inner_le_commutator hP)
  let ψ : MulAut S →* Y := N.subtype.comp e.symm.toMonoidHom
  have hψ : Function.Injective ψ := Subtype.val_injective.comp e.symm.injective
  have hNψ : ψ.range = N := by
    ext y
    constructor
    · rintro ⟨α, rfl⟩
      exact (e.symm α).2
    · intro hy
      exact ⟨e ⟨y, hy⟩, by simp [ψ]⟩
  let φ : S →* Y := ψ.comp MulAut.conj
  have hφ : Function.Injective φ := hψ.comp (conj_injective hZ)
  have hK : ⁅N, N⁆ = φ.range := by
    rw [← hNψ, MonoidHom.range_eq_map, ← Subgroup.map_commutator, ← _root_.commutator_def, hcomm,
      MonoidHom.range_comp]
    rfl
  have : (⁅N, N⁆ : Subgroup Y).Normal := Subgroup.commutator_normal N N
  let eK : ↥(⁅N, N⁆ : Subgroup Y) ≃* S :=
    (MulEquiv.subgroupCongr hK).trans (MonoidHom.ofInjective hφ).symm
  have hNK : N ⊓ centralizer ((⁅N, N⁆ : Subgroup Y) : Set Y) = ⊥ := by
    rw [eq_bot_iff]
    rintro y ⟨hyN, hyC⟩
    rw [Subgroup.mem_bot]
    have hy : y = ψ (e ⟨y, hyN⟩) := by simp [ψ]
    have hα : e ⟨y, hyN⟩ = 1 := by
      apply eq_one_of_commute_conj hZ
      intro s
      apply hψ
      have hmem : φ s ∈ (⁅N, N⁆ : Subgroup Y) := hK ▸ ⟨s, rfl⟩
      have := Subgroup.mem_centralizer_iff.mp hyC _ hmem
      rw [hy] at this
      simpa [map_mul, φ] using this.symm
    rw [hy, hα, map_one]
  have hCK : centralizer ((⁅N, N⁆ : Subgroup Y) : Set Y) = ⊥ := by
    have hCn : (centralizer ((⁅N, N⁆ : Subgroup Y) : Set Y)).Normal := inferInstance
    have hdis : Disjoint (centralizer ((⁅N, N⁆ : Subgroup Y) : Set Y)) N := by
      rw [disjoint_iff, inf_comm, hNK]
    rw [eq_bot_iff, ← hC]
    intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    exact (Subgroup.commute_of_normal_of_disjoint _ _ hCn hNn hdis x y hx hy).symm
  have hY : Nat.card Y ∣ 5 * Nat.card S := by
    have h1 := CFSG.OddStandard.Seitz77.card_dvd_mulAut hCK
    rw [Nat.card_congr (MulAut.congr eK).toEquiv] at h1
    exact h1.trans (CFSG.StandardType.SporadicShape.ord7_card_mulAut_dvd_twistedB2 hS')
  intro h3
  rcases (Nat.Prime.dvd_mul Nat.prime_three).mp (h3.trans hY) with h | h
  · norm_num at h
  · exact CFSG.LocalAnalysis.EvenBN.GMSK.not_three_dvd_card_of_lieModel_twistedB2 hS' h

private theorem isSolvable_quotient_of_centralizer_eq_bot {Y : Type} [Group Y] {K : Subgroup Y} [K.Normal]
    (hC : centralizer (K : Set Y) = ⊥) (hOut : Group.IsSolvable (Outer ↥K)) :
    Group.IsSolvable (Y ⧸ K) := by
  let φ : Y →* Outer ↥K :=
    (QuotientGroup.mk' (CFSG.ComponentClassification.OuterAutomorphisms.inner ↥K)).comp
      MulAut.conjNormal
  have hle : K ≤ φ.ker := by
    intro k hk
    rw [MonoidHom.mem_ker]
    change (QuotientGroup.mk (MulAut.conjNormal k) : Outer ↥K) = 1
    rw [QuotientGroup.eq_one_iff]
    refine ⟨⟨k, hk⟩, ?_⟩
    ext m
    simp [MulAut.conjNormal_apply, MulAut.conj_apply]
  have hinj : Function.Injective (QuotientGroup.lift K φ hle) := by
    intro a b hab
    induction a using QuotientGroup.induction_on with
    | H a =>
      induction b using QuotientGroup.induction_on with
      | H b =>
        rw [QuotientGroup.lift_mk, QuotientGroup.lift_mk] at hab
        have h1 : φ (a⁻¹ * b) = 1 := by rw [map_mul, map_inv, hab, inv_mul_cancel]
        rw [← MonoidHom.mem_ker] at h1
        change (QuotientGroup.mk (MulAut.conjNormal (a⁻¹ * b)) : Outer ↥K) = 1 at h1
        obtain ⟨k, hk⟩ := (QuotientGroup.eq_one_iff _).mp h1
        have hz : (k : Y)⁻¹ * (a⁻¹ * b) ∈ centralizer (K : Set Y) := by
          rw [Subgroup.mem_centralizer_iff]
          intro m hm
          have h2 : (k : Y) * m * (k : Y)⁻¹ = (a⁻¹ * b) * m * (a⁻¹ * b)⁻¹ := by
            have := congrArg (fun α : MulAut ↥K => ((α ⟨m, hm⟩ : ↥K) : Y)) hk
            simp only [MulAut.conjNormal_apply, MulAut.conj_apply] at this
            rw [← this]
            simp
          calc m * ((k : Y)⁻¹ * (a⁻¹ * b))
              = (k : Y)⁻¹ * ((k : Y) * m * (k : Y)⁻¹) * (a⁻¹ * b) := by group
            _ = (k : Y)⁻¹ * ((a⁻¹ * b) * m * (a⁻¹ * b)⁻¹) * (a⁻¹ * b) := by rw [h2]
            _ = (k : Y)⁻¹ * (a⁻¹ * b) * m := by group
        rw [hC, Subgroup.mem_bot, inv_mul_eq_one] at hz
        rw [QuotientGroup.eq, ← hz]
        exact k.2
  exact Group.isSolvable_of_isSolvable_injective hinj

end

private instance : Fact (Nat.Prime 5) := ⟨by norm_num⟩

section

open Equiv
open Subgroup
open CFSG.RankThree.PartOne (IsStronglyPEmbedded)
open CFSG.GH74.GLS.Stage2.Signalizer.Odd87 (IsSection)
open CFSG.LocalAnalysis.UniquenessCase.UC22 (IsAlt)

private theorem NoA6InStronglyFiveEmbedded.of_mulEquiv {K K' : Type} [Group K] [Group K'] (e : K ≃* K')
    (h : NoA6InStronglyFiveEmbedded K') : NoA6InStronglyFiveEmbedded K := fun H hH hS =>
  h (H.map e.toMonoidHom)
    (CFSG.LocalAnalysis.UniquenessCase.UCK.isStronglyPEmbedded_map_mulEquiv e hH)
    (hS.of_equiv (H.equivMapOfInjective _ e.injective).symm)

private abbrev A5 := ↥(alternatingGroup (Fin 5))

private abbrev A10 := ↥(alternatingGroup (Fin 5 ⊕ Fin 5))

private theorem card_alt (α : Type) [Fintype α] [DecidableEq α] [Nontrivial α] :
    2 * Nat.card (alternatingGroup α) = (Nat.card α).factorial := by
  rw [two_mul_nat_card_alternatingGroup, Nat.card_perm]

private theorem card_A5 : Nat.card (alternatingGroup (Fin 5)) = 60 := by
  have h := card_alt (Fin 5)
  rw [Nat.card_eq_fintype_card (α := Fin 5), Fintype.card_fin] at h
  have : (5 : ℕ).factorial = 120 := rfl
  omega

private theorem card_A10 : Nat.card (alternatingGroup (Fin 5 ⊕ Fin 5)) = 1814400 := by
  have h := card_alt (Fin 5 ⊕ Fin 5)
  rw [Nat.card_eq_fintype_card (α := Fin 5 ⊕ Fin 5), Fintype.card_sum, Fintype.card_fin] at h
  have : (5 + 5 : ℕ).factorial = 3628800 := rfl
  omega

private theorem card_A6 : Nat.card (alternatingGroup (Fin 6)) = 360 := by
  have h := card_alt (Fin 6)
  rw [Nat.card_eq_fintype_card (α := Fin 6), Fintype.card_fin] at h
  have : (6 : ℕ).factorial = 720 := rfl
  omega

private def ι : A5 × A5 →* A10 where
  toFun ab := ⟨Perm.sumCongr ab.1.1 ab.2.1, by
    rw [Perm.mem_alternatingGroup, Perm.sign_sumCongr, Perm.mem_alternatingGroup.mp ab.1.2,
      Perm.mem_alternatingGroup.mp ab.2.2, mul_one]⟩
  map_one' := Subtype.ext (by simp)
  map_mul' a b := Subtype.ext (Perm.sumCongr_mul _ _ _ _).symm

private theorem ι_injective : Function.Injective ι := by
  intro a b h
  have h' := congrArg Subtype.val h
  refine Prod.ext (Subtype.ext (Equiv.ext fun x => ?_)) (Subtype.ext (Equiv.ext fun x => ?_))
  · have := congrArg (fun σ : Perm (Fin 5 ⊕ Fin 5) => σ (Sum.inl x)) h'
    simpa [ι] using this
  · have := congrArg (fun σ : Perm (Fin 5 ⊕ Fin 5) => σ (Sum.inr x)) h'
    simpa [ι] using this

private def c5 : A5 := ⟨finRotate 5, by rw [Perm.mem_alternatingGroup]; decide⟩

private theorem c5_pow : c5 ^ 5 = 1 := Subtype.ext (by rw [Subgroup.coe_pow]; decide)

private theorem c5_ne : c5 ≠ 1 := fun h => by
  have := congrArg Subtype.val h
  revert this
  decide

private theorem orderOf_c5 : orderOf c5 = 5 := orderOf_eq_prime c5_pow c5_ne

private def x₀ : A10 := ι (c5, 1)

private def y₀ : A10 := ι (1, c5)

private def P₀ : Subgroup A10 := ((zpowers c5).prod (zpowers c5)).map ι

private theorem card_P₀ : Nat.card P₀ = 25 := by
  rw [P₀, Subgroup.card_map_of_injective ι_injective,
    Nat.card_congr (Subgroup.prodEquiv (zpowers c5) (zpowers c5)).toEquiv, Nat.card_prod,
    Nat.card_zpowers, orderOf_c5]

private theorem isPGroup_P₀ : IsPGroup 5 P₀ := IsPGroup.of_card (n := 2) (by rw [card_P₀]; norm_num)

private theorem x₀_mem : x₀ ∈ P₀ := ⟨(c5, 1), ⟨mem_zpowers c5, one_mem _⟩, rfl⟩

private theorem y₀_mem : y₀ ∈ P₀ := ⟨(1, c5), ⟨one_mem _, mem_zpowers c5⟩, rfl⟩

private theorem mem_normalizer_zpowers_of_commute {G : Type} [Group G] {g z : G} (h : g * z = z * g) :
    g ∈ normalizer (zpowers z : Set G) := by
  have hc : Commute g z := h
  rw [Subgroup.mem_normalizer_iff]
  intro w
  constructor
  · intro hw
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hw
    rw [(hc.zpow_right k).eq, mul_inv_cancel_right]
    exact zpow_mem (mem_zpowers z) k
  · intro hw
    obtain ⟨k, hk⟩ := mem_zpowers_iff.mp hw
    have : w = z ^ k := by
      calc w = g⁻¹ * (g * w * g⁻¹) * g := by group
        _ = g⁻¹ * (z ^ k * g) := by rw [← hk, mul_assoc]
        _ = z ^ k := by rw [← (hc.zpow_right k).eq, inv_mul_cancel_left]
    rw [this]
    exact zpow_mem (mem_zpowers z) k

private theorem ne_bot_zpowers {G : Type} [Group G] {z : G} (h : z ≠ 1) : zpowers z ≠ ⊥ := by
  rwa [Ne, Subgroup.zpowers_eq_bot]

private theorem x₀_ne : x₀ ≠ 1 := fun h =>
  c5_ne (congrArg Prod.fst (ι_injective (h.trans (map_one ι).symm)))

private theorem y₀_ne : y₀ ≠ 1 := fun h =>
  c5_ne (congrArg Prod.snd (ι_injective (h.trans (map_one ι).symm)))

private theorem noA6_of_le {H : Subgroup A10} (hH : IsStronglyPEmbedded 5 H) (hP : P₀ ≤ H) :
    ¬ IsSection (alternatingGroup (Fin 6)) ↥H := by
  have hNx := hH.normalizer_le (ne_bot_zpowers x₀_ne)
    (isPGroup_P₀.to_le (zpowers_le.mpr x₀_mem)) ((zpowers_le.mpr x₀_mem).trans hP)
  have hNy := hH.normalizer_le (ne_bot_zpowers y₀_ne)
    (isPGroup_P₀.to_le (zpowers_le.mpr y₀_mem)) ((zpowers_le.mpr y₀_mem).trans hP)
  have hE : ι.range ≤ H := by
    rintro _ ⟨⟨a, b⟩, rfl⟩
    have hab : ((a, b) : A5 × A5) = (a, 1) * (1, b) := by simp
    rw [hab, map_mul]
    refine mul_mem (hNy (mem_normalizer_zpowers_of_commute ?_))
      (hNx (mem_normalizer_zpowers_of_commute ?_))
    · rw [y₀, ← map_mul, ← map_mul]
      congr 1
    · rw [x₀, ← map_mul, ← map_mul]
      congr 1
  have hcardE : Nat.card ι.range = 3600 := by
    rw [← Nat.card_congr (MonoidHom.ofInjective ι_injective).toEquiv, Nat.card_prod, card_A5]
  have hidx := hH.index_modEq_card isPGroup_P₀ hP
  rw [card_P₀] at hidx
  have hne : H.index ≠ 1 := fun h1 => hH.1 (Subgroup.index_eq_one.mp h1)
  have hmul := H.index_mul_card
  rw [card_A10] at hmul
  obtain ⟨k, hk⟩ := (Subgroup.card_dvd_of_le hE).trans (dvd_refl _) |>.trans
    (dvd_refl (Nat.card H)) |> fun h => (hcardE ▸ h : 3600 ∣ Nat.card H)
  rw [hk] at hmul
  have hd : H.index * k = 504 := by nlinarith
  have hmod : H.index % 25 = 1 := hidx
  have hcardH : Nat.card H = 14400 := by
    obtain ⟨j, hj⟩ : ∃ j, H.index = 25 * j + 1 := ⟨H.index / 25, by omega⟩
    have hj20 : j ≤ 20 := by
      have : H.index ≤ 504 := Nat.le_of_dvd (by norm_num) ⟨k, hd.symm⟩
      omega
    rw [hj] at hd hne
    rw [hk]
    interval_cases j <;> omega
  let E : Subgroup ↥H := ι.range.subgroupOf H
  have hcardE' : Nat.card E = 3600 := by
    rw [← hcardE]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hE).toEquiv
  have hEidx : Nat.card (↥H ⧸ E) = 4 := by
    have := E.index_mul_card
    rw [hcardE', hcardH] at this
    change E.index = 4
    omega
  let ρ := MulAction.toPermHom ↥H (↥H ⧸ E)
  have hκ : ρ.ker ≤ E := by
    intro h hh
    have h1 : h • (QuotientGroup.mk 1 : ↥H ⧸ E) = QuotientGroup.mk 1 :=
      congrArg (fun σ : Perm (↥H ⧸ E) => σ (QuotientGroup.mk 1)) (MonoidHom.mem_ker.mp hh)
    rw [MulAction.Quotient.smul_mk, smul_eq_mul, mul_one, QuotientGroup.eq, mul_one, inv_mem_iff] at h1
    exact h1
  have := CFSG.LargeExtraspecial.S45Q.isSimpleGroup_alternatingGroup_six
  intro hS
  rcases hS.dichotomy ρ.ker with h1 | h2
  ·
    have h3 : IsSection (alternatingGroup (Fin 6)) (A5 × A5) :=
      (h1.of_le_le hκ).of_equiv
        ((MonoidHom.ofInjective ι_injective).trans (Subgroup.subgroupOfEquivOfLe hE).symm)
    have hsurj : Function.Surjective (MonoidHom.fst A5 A5) := Prod.fst_surjective
    rcases h3.dichotomy (MonoidHom.fst A5 A5).ker with h4 | h4
    · have hc := Subgroup.card_eq_card_quotient_mul_card_subgroup (MonoidHom.fst A5 A5).ker
      rw [Nat.card_prod, card_A5, Nat.card_congr
        (QuotientGroup.quotientKerEquivOfSurjective _ hsurj).toEquiv, card_A5] at hc
      have := h4.card_dvd
      rw [card_A6] at this
      have := Nat.le_of_dvd (by omega) this
      omega
    · have := h4.card_dvd
      rw [card_A6, Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective _ hsurj).toEquiv,
        card_A5] at this
      exact absurd this (by norm_num)
  ·
    have hle : Nat.card (↥H ⧸ ρ.ker) ≤ 24 := by
      rw [Nat.card_congr (QuotientGroup.quotientKerEquivRange ρ).toEquiv]
      calc Nat.card ρ.range ≤ Nat.card (Perm (↥H ⧸ E)) := Subgroup.card_le_card_group _
        _ = 24 := by rw [Nat.card_perm, hEidx]; rfl
    have := h2.card_dvd
    rw [card_A6] at this
    have := Nat.le_of_dvd (Nat.card_pos) this
    omega

private theorem noA6_A10 : NoA6InStronglyFiveEmbedded A10 := by
  intro H hH hS
  obtain ⟨P, hPs, hPH⟩ := hH.exists_isSylowOf_le
  let S : Sylow 5 A10 := hPs.2.1.toSylow (by simpa [Subgroup.relIndex_top_right] using hPs.2.2)
  have hidx0 : ¬ 5 ∣ P₀.index := by
    have := P₀.index_mul_card
    rw [card_P₀, card_A10] at this
    omega
  let S₀ : Sylow 5 A10 := isPGroup_P₀.toSylow hidx0
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq A10 S S₀
  have hP₀ : P₀ = P.map (MulAut.conj g).toMonoidHom := by
    have h1 : ((g • S : Sylow 5 A10) : Subgroup A10) = (S₀ : Subgroup A10) := by rw [hg]
    rw [Sylow.coe_subgroup_smul, Subgroup.pointwise_smul_def] at h1
    exact h1.symm
  refine noA6_of_le (H := H.map (MulAut.conj g).toMonoidHom)
    (CFSG.LocalAnalysis.UniquenessCase.UCK.isStronglyPEmbedded_map_mulEquiv _ hH)
    (hP₀ ▸ Subgroup.map_mono hPH)
    (hS.of_equiv (H.equivMapOfInjective _ (MulAut.conj g).injective).symm)

private theorem noA6_alt10 {K : Type} [Group K] (h : IsAlt K 10) : NoA6InStronglyFiveEmbedded K := by
  obtain ⟨e⟩ := h
  exact noA6_A10.of_mulEquiv (e.trans (Equiv.altCongrHom (finSumFinEquiv (m := 5) (n := 5)).symm))

end

section

open Subgroup
open CFSG.Blueprint (LieModel)
open CFSG.RankThree.PartOne (IsStronglyPEmbedded)
open CFSG.GH74.GLS.Stage2.Signalizer.Odd87 (IsSection)

private theorem noA6_of_card_sylow {K : Type} [Group K] [Finite K]
    (hn : ∀ T : Sylow 5 K, Nat.card (Sylow 5 K) = Nat.card T + 1) :
    NoA6InStronglyFiveEmbedded K := by
  intro H hH hS
  obtain ⟨P, hPs, hPH⟩ := hH.exists_isSylowOf_le
  let T : Sylow 5 K := hPs.2.1.toSylow (by simpa [Subgroup.relIndex_top_right] using hPs.2.2)
  have hTP : (T : Subgroup K) = P := IsPGroup.toSylow_coe _ _
  have h5K : 5 ∣ Nat.card K := (hH.2.1).trans (Subgroup.card_subgroup_dvd_card H)
  have hTne : (T : Subgroup K) ≠ ⊥ := T.ne_bot_of_dvd_card h5K
  have hTp : IsPGroup 5 (T : Subgroup K) := T.isPGroup'
  have hTH : (T : Subgroup K) ≤ H := hTP ▸ hPH
  let N := normalizer ((T : Subgroup K) : Set K)
  have hNH : N ≤ H := hH.normalizer_le hTne hTp hTH
  have hNidx : N.index = Nat.card T + 1 :=
    ((hn T).symm.trans (Sylow.card_eq_index_normalizer T)).symm
  have hdvd : H.index ∣ Nat.card T + 1 := hNidx ▸ Subgroup.index_dvd_of_le hNH
  have hmod := hH.index_modEq_card hTp hTH
  have hne : H.index ≠ 1 := fun h1 => hH.1 (Subgroup.index_eq_one.mp h1)
  have hT5 : 5 ≤ Nat.card T := by
    obtain ⟨k, hk⟩ := (IsPGroup.iff_card).mp hTp
    have hk0 : k ≠ 0 := by
      rintro rfl
      exact hTne (Subgroup.eq_bot_of_card_eq _ (by simpa using hk))
    rw [hk]
    exact le_trans (by norm_num) (Nat.pow_le_pow_right (by norm_num) (Nat.one_le_iff_ne_zero.mpr hk0))
  have hHidx : H.index = Nat.card T + 1 := by
    have hpos : 0 < H.index := Nat.pos_of_ne_zero (Subgroup.index_ne_zero_of_finite)
    have hle : H.index ≤ Nat.card T + 1 := Nat.le_of_dvd (by omega) hdvd
    have hm : H.index % Nat.card T = 1 := by
      have := hmod
      unfold Nat.ModEq at this
      rw [this, Nat.mod_eq_of_lt (by omega)]
    rcases Nat.lt_or_ge H.index (Nat.card T) with hlt | hge
    · rw [Nat.mod_eq_of_lt hlt] at hm
      exact absurd hm hne
    · rcases Nat.eq_or_lt_of_le hle with h | h
      · exact h
      · have : H.index = Nat.card T := by omega
        rw [this, Nat.mod_self] at hm
        omega
  have hHN : H = N := by
    symm
    apply Subgroup.eq_of_le_of_card_ge hNH
    have h1 := N.index_mul_card
    have h2 := H.index_mul_card
    rw [hNidx] at h1
    rw [hHidx] at h2
    have := h1.trans h2.symm
    exact (Nat.eq_of_mul_eq_mul_left (by omega) this).ge
  subst hHN
  have := CFSG.LargeExtraspecial.S45Q.isSimpleGroup_alternatingGroup_six
  have : ((T : Subgroup K).subgroupOf N).Normal := Subgroup.normal_in_normalizer
  rcases hS.dichotomy ((T : Subgroup K).subgroupOf N) with h1 | h2
  ·
    have hd := h1.card_dvd
    rw [card_A6] at hd
    have hp : IsPGroup 5 ((T : Subgroup K).subgroupOf N) :=
      hTp.comap_of_injective N.subtype Subtype.val_injective
    obtain ⟨k, hk⟩ := (IsPGroup.iff_card).mp hp
    rw [hk] at hd
    have h2 : 2 ∣ 5 ^ k := (by norm_num : 2 ∣ 360).trans hd
    exact absurd (Nat.Prime.dvd_of_dvd_pow Nat.prime_two h2) (by norm_num)
  ·
    have hd := h2.card_dvd
    rw [card_A6] at hd
    have hrel : ((T : Subgroup K).subgroupOf N).index ∣ (T : Subgroup K).index :=
      Subgroup.relIndex_dvd_index_of_le Subgroup.le_normalizer
    have h5 : 5 ∣ (T : Subgroup K).index :=
      ((by norm_num : 5 ∣ 360).trans hd).trans hrel
    exact T.not_dvd_index h5

private theorem noA6_psu3 {K : Type} [Group K] {n : ℕ} (h : LieModel K .PSU 3 5 n) :
    NoA6InStronglyFiveEmbedded K := by
  have hS := h.statedClassicalModel_of_ne_zero (by norm_num)
  obtain ⟨-, hf, hq, F, _, _, J, hJ, hF, hfix, ⟨e⟩⟩ :=
    CFSG.AGLEmbedding.UnitaryModel.exists_equiv_psu hS
  have : Finite K := CFSG.LieType.Simplicity.finite_of_statedClassicalModel hS
  have : Finite (CFSG.BenderSuzuki.MatrixGroups.ProjectiveSpecialUnitaryMatrixGroup J) :=
    Finite.of_equiv K e.toEquiv
  exact (noA6_of_card_sylow fun T =>
    CFSG.LocalAnalysis.UniquenessCase.UCK.K38B.card_sylow_psu J hJ hf hq hF hfix T).of_mulEquiv e

end

section

open Subgroup
open CFSG.Blueprint (LieModel)
open CFSG.RankThree.PartOne (IsStronglyPEmbedded)
open CFSG.GH74.GLS.Stage2.Signalizer.Odd87 (IsSection)
open CFSG.LocalAnalysis.UniquenessCase.UC22 (IsSpor)
open CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor
  (NormalizerMaximal IsTitsType IsMcLType tits_maximal mcl_maximal)

private theorem not_isSection_normalizer {K : Type} [Group K] [Finite K] (T : Sylow 5 K) :
    ¬ IsSection (alternatingGroup (Fin 6)) ↥(normalizer ((T : Subgroup K) : Set K)) := by
  intro hS
  have := CFSG.LargeExtraspecial.S45Q.isSimpleGroup_alternatingGroup_six
  let N := normalizer ((T : Subgroup K) : Set K)
  have : ((T : Subgroup K).subgroupOf N).Normal := Subgroup.normal_in_normalizer
  rcases hS.dichotomy ((T : Subgroup K).subgroupOf N) with h1 | h2
  · have hd := h1.card_dvd
    rw [card_A6] at hd
    have hp : IsPGroup 5 ((T : Subgroup K).subgroupOf N) :=
      T.isPGroup'.comap_of_injective N.subtype Subtype.val_injective
    obtain ⟨k, hk⟩ := (IsPGroup.iff_card).mp hp
    rw [hk] at hd
    have h2 : 2 ∣ 5 ^ k := (by norm_num : 2 ∣ 360).trans hd
    exact absurd (Nat.Prime.dvd_of_dvd_pow Nat.prime_two h2) (by norm_num)
  · have hd := h2.card_dvd
    rw [card_A6] at hd
    have hrel : ((T : Subgroup K).subgroupOf N).index ∣ (T : Subgroup K).index :=
      Subgroup.relIndex_dvd_index_of_le Subgroup.le_normalizer
    exact T.not_dvd_index (((by norm_num : 5 ∣ 360).trans hd).trans hrel)

private theorem noA6_of_normalizerMaximal {K : Type} [Group K] [Finite K] (hM : NormalizerMaximal 5 K) :
    NoA6InStronglyFiveEmbedded K := by
  intro H hH hS
  obtain ⟨P, hPs, hPH⟩ := hH.exists_isSylowOf_le
  let T : Sylow 5 K := hPs.2.1.toSylow (by simpa [Subgroup.relIndex_top_right] using hPs.2.2)
  have hTP : (T : Subgroup K) = P := IsPGroup.toSylow_coe _ _
  have h5K : 5 ∣ Nat.card K := (hH.2.1).trans (Subgroup.card_subgroup_dvd_card H)
  have hNH : normalizer ((T : Subgroup K) : Set K) ≤ H :=
    hH.normalizer_le (T.ne_bot_of_dvd_card h5K) T.isPGroup' (hTP ▸ hPH)
  rcases hM T H hNH with h | h
  · subst h
    exact not_isSection_normalizer T hS
  · exact hH.1 h

private theorem noA6_tits
    {K : Type} [Group K] (h : LieModel K .Tits 0 2 1) :
    NoA6InStronglyFiveEmbedded K := by
  have : Finite K := CFSG.LieType.Simplicity.finite_of_native_lieModel h
  exact noA6_of_normalizerMaximal
    (tits_maximal K ⟨rfl, CFSG.LocalAnalysis.UniquenessCase.UC6.TitsAut.isoLie_of_lieModel h⟩)

private theorem noA6_mcl
    {K : Type} [Group K] (h : IsSpor K .McL) : NoA6InStronglyFiveEmbedded K := by
  obtain ⟨e⟩ := h
  have hcard := CFSG.EvenSporadicStandard.McLStd.card_eq_of_isSporadic_mcl ⟨e⟩
  have : Finite K := Nat.finite_of_card_ne_zero (by rw [hcard]; norm_num)
  obtain ⟨eC⟩ := CFSG.Sporadic.Bridge.McL.nonempty_mulEquiv
  exact noA6_of_normalizerMaximal (mcl_maximal K ⟨rfl, ⟨e.trans eC⟩⟩)

end

section

open Subgroup
open CFSG.Blueprint (LieModel)
open CFSG.RankThree.PartOne (IsStronglyPEmbedded)
open CFSG.GH74.GLS.Stage2.Signalizer.Odd87 (IsSection)
open CFSG.LocalAnalysis.UniquenessCase.UC22 (IsSpor IsAlt)
open CFSG.LocalAnalysis.UniquenessCase.UC22.F07 (IsAutSz)
open CFSG.ComponentClassification.OuterAutomorphisms (Outer equivalence center_map_equiv)

private theorem center_eq_bot_of_noncomm {G : Type} [Group G] [IsSimpleGroup G] {a b : G}
    (hab : a * b ≠ b * a) : center G = ⊥ := by
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (center G) with h | h
  · exact h
  · exact absurd (Subgroup.mem_center_iff.mp (h ▸ Subgroup.mem_top a) b).symm hab

private theorem center_eq_bot_of_mulEquiv {G H : Type} [Group G] [Group H] (e : G ≃* H)
    (h : center H = ⊥) : center G = ⊥ := by
  have := center_map_equiv e
  rw [h] at this
  exact (Subgroup.map_eq_bot_iff_of_injective _ e.injective).mp this

private theorem isSolvable_of_two_group {G : Type} [Group G] [Finite G]
    (h : ∀ p : ℕ, p.Prime → p ∣ Nat.card G → p = 2) : Group.IsSolvable G := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hc := Nat.eq_prime_pow_of_unique_prime_dvd (Nat.card_pos (α := G)).ne'
    (fun {d} hd hdvd => h d hd hdvd)
  have := (IsPGroup.of_card hc).isNilpotent
  infer_instance

private theorem center_eq_bot_of_isAutSz {X : Type} [Group X] (h : IsAutSz X 5) : center X = ⊥ := by
  obtain ⟨S, _, hS, ⟨e⟩⟩ := h
  have hS' : LieModel S .twistedB2 0 2 5 := hS
  have := CFSG.LocalAnalysis.EvenBN.GMSK.isSimpleGroup_of_lieModel_twistedB2 hS'
  obtain ⟨a, b, hab⟩ := CFSG.LocalAnalysis.EvenBN.GMSK.exists_mul_ne_of_lieModel_twistedB2 hS'
  have hZ := center_eq_bot_of_noncomm hab
  refine center_eq_bot_of_mulEquiv e ?_
  rw [eq_bot_iff]
  intro α hα
  rw [Subgroup.mem_bot]
  exact eq_one_of_commute_conj hZ fun s =>
    (Subgroup.mem_center_iff.mp hα (MulAut.conj s)).symm

private theorem not_isSection_of_socle {Y : Type} [Group Y] [Finite Y] {N S : Subgroup Y}
    (hNn : N.Normal) (hF : CFSG.Open.genFittingFStar Y ≤ N) (hZ : center ↥N = ⊥)
    (hOut : Group.IsSolvable (Outer ↥N)) (hA : NoA6InStronglyFiveEmbedded ↥N) (hS : IsStronglyPEmbedded 5 S) :
    ¬ IsSection (alternatingGroup (Fin 6)) ↥S := by
  intro h
  have := hNn
  have hC := centralizer_eq_bot_of_genFittingFStar_le hF hZ
  have hsol := isSolvable_quotient_of_centralizer_eq_bot hC hOut
  have h' := isSection_inf_of_solvable hNn (isSolvable_quotient_subgroupOf hsol) h
  have h5 : 5 ∣ Nat.card N := by
    have hd := h'.card_dvd
    rw [card_A6] at hd
    exact ((by norm_num : 5 ∣ 360).trans hd).trans (Subgroup.card_subgroup_dvd_card _)
  exact not_isSection_alt6_of_normal hS hNn h5 hsol hA h

private theorem good_psl2 {K : Type} [Group K] {n : ℕ} (h : LieModel K .PSL 2 5 n) :
    center K = ⊥ ∧ Group.IsSolvable (Outer K) ∧ NoA6InStronglyFiveEmbedded K := by
  have := CFSG.ComponentClassification.HarrisLit.isSimpleGroup_of_lieModel_psl2 h
  obtain ⟨a, b, hab⟩ := CFSG.ComponentClassification.HarrisLit.nonabelian_of_lieModel_psl2 h
  exact ⟨center_eq_bot_of_noncomm hab,
    CFSG.ComponentClassification.CatalogueSchreierAssembly.classical_model_outer_solvable
      (h.statedClassicalModel_of_ne_zero (by norm_num)),
    fun H hH => noA6_psl2 h H hH⟩

private theorem good_psu3 {K : Type} [Group K] [Finite K] {n : ℕ} (h : LieModel K .PSU 3 5 n) :
    center K = ⊥ ∧ Group.IsSolvable (Outer K) ∧ NoA6InStronglyFiveEmbedded K := by
  have := CFSG.SeitzReduction.LinearPilot.isSimpleGroup_of_lieModel_PSU h
  refine ⟨CFSG.RankThree.PartTwo.Sec21.Hering214.center_eq_bot_of_simple_of_not_prime
      inferInstance ?_,
    CFSG.ComponentClassification.CatalogueSchreierAssembly.classical_model_outer_solvable
      (h.statedClassicalModel_of_ne_zero (by norm_num)),
    noA6_psu3 h⟩
  intro hp
  have h1 := h.factorization_card_psu3
  have hf : 1 ≤ n := h.admissible.2.1
  rw [hp.factorization, Finsupp.single_apply] at h1
  split_ifs at h1 <;> omega

private theorem good_tits
    {K : Type} [Group K] [Finite K] (h : LieModel K .Tits 0 2 1) :
    center K = ⊥ ∧ Group.IsSolvable (Outer K) ∧ NoA6InStronglyFiveEmbedded K := by
  obtain ⟨hs, a, b, hab⟩ := CFSG.LocalAnalysis.UniquenessCase.UC6.TitsAut.simple_of_lieModel h
  have := hs
  obtain ⟨hv, ⟨e⟩⟩ := CFSG.LocalAnalysis.UniquenessCase.UC6.TitsAut.isoLie_of_lieModel h
  have : Finite (MulAut K) := Finite.of_injective _ (DFunLike.coe_injective (F := MulAut K))
  refine ⟨center_eq_bot_of_noncomm hab, isSolvable_of_two_group fun p hp hd => ?_,
    noA6_tits h⟩
  by_contra hp2
  exact CFSG.AGLEmbedding.not_dvd_card_outer_tits hv e hp hp2 hd

private theorem good_mcl
    {K : Type} [Group K] (h : IsSpor K .McL) :
    center K = ⊥ ∧ Group.IsSolvable (Outer K) ∧ NoA6InStronglyFiveEmbedded K := by
  obtain ⟨e⟩ := h
  have : Finite CFSG.Blueprint.NativeSporadic.McL :=
    Nat.finite_of_card_ne_zero (by rw [CFSG.Sporadic.McL.card_McL]; norm_num)
  have hZ : center CFSG.Blueprint.NativeSporadic.McL = ⊥ :=
    CFSG.RankThree.PartTwo.Sec21.Hering214.center_eq_bot_of_simple_of_not_prime
      CFSG.Sporadic.McL.isSimpleGroup_McL (by rw [CFSG.Sporadic.McL.card_McL]; norm_num)
  refine ⟨center_eq_bot_of_mulEquiv e hZ, ?_, noA6_mcl ⟨e⟩⟩
  have h2 : Nat.card (Outer K) = 2 :=
    (Nat.card_congr (equivalence e).toEquiv).trans CFSG.Sporadic.Recognition.McLAS.card_outer_mcl
  have : Finite (Outer K) := Nat.finite_of_card_ne_zero (by omega)
  exact isSolvable_of_two_group fun p hp hd => by
    rw [h2] at hd
    exact (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp hd

private theorem good_alt10 {K : Type} [Group K] (h : IsAlt K 10) :
    center K = ⊥ ∧ Group.IsSolvable (Outer K) ∧ NoA6InStronglyFiveEmbedded K := by
  obtain ⟨e⟩ := h
  refine ⟨center_eq_bot_of_mulEquiv e (alternatingGroup.center_eq_bot
    (by rw [Nat.card_eq_fintype_card, Fintype.card_fin]; omega)), ?_, noA6_alt10 ⟨e⟩⟩
  have h4 : Nat.card (Outer K) ∣ 4 := by
    rw [Nat.card_congr (equivalence e).toEquiv]
    exact CFSG.AGLEmbedding.card_outer_alternatingGroup_dvd_four 10 (by norm_num)
  have : Finite (Outer K) := Nat.finite_of_card_ne_zero (fun h0 => by rw [h0] at h4; norm_num at h4)
  exact isSolvable_of_two_group fun p hp hd =>
    (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp
      (hp.dvd_of_dvd_pow (hd.trans h4 : p ∣ 2 ^ 2))

theorem fiveEmbeddedNoAlt6 :
    FiveEmbeddedNoAlt6 := by
  intro Y _ _ N S hNn hF hcase hS _ ⟨A, V, hV, ⟨e⟩⟩
  have := hV
  have hsec : IsSection (alternatingGroup (Fin 6)) ↥S :=
    ⟨A, e.toMonoidHom.comp (QuotientGroup.mk' V), e.surjective.comp (QuotientGroup.mk'_surjective V)⟩
  have key : center ↥N = ⊥ ∧ Group.IsSolvable (Outer ↥N) ∧ NoA6InStronglyFiveEmbedded ↥N → False :=
    fun ⟨hZ, hO, hA⟩ => not_isSection_of_socle hNn hF hZ hO hA hS hsec
  rcases hcase with ⟨n, h⟩ | ⟨n, h⟩ | h | h | h | h
  · exact key (good_psl2 h)
  · exact key (good_psu3 h)
  ·
    have hC := centralizer_eq_bot_of_genFittingFStar_le hF (center_eq_bot_of_isAutSz h)
    apply not_three_dvd_card_of_isAutSz hNn hC h
    have hd := hsec.card_dvd
    rw [card_A6] at hd
    exact ((by norm_num : 3 ∣ 360).trans hd).trans (Subgroup.card_subgroup_dvd_card S)
  · exact key (good_tits h)
  · exact key (good_mcl h)
  · exact key (good_alt10 h)

end

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8
