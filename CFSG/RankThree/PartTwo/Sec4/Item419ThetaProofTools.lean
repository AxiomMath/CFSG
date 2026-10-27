module

public import CFSG.RankThree.PartTwo.Sec8.Item84PairProofTheta419
public import CFSG.RankThree.PartTwo.Sec21.Item211ProofQuot
import CFSG.RankThree.PartOne.S10.EmbeddingTransport
import CFSG.RankThree.PartTwo.Sec19.Step1914Tri
import CFSG.RankThree.PartTwo.Sec13.Item13Models
import CFSG.RankThree.PartTwo.KFacts.KS14Orders
import CFSG.Sporadic.Schreier.TitsOuter
import CFSG.LocalAnalysis.SignalizerFunctor.InvariantSylowAmbient
import CFSG.LocalAnalysis.RankThreeEvenClassification.CoprimeCentralizer
public import CFSG.LieType.Simplicity.ReeLargeModel
import CFSG.Sporadic.Schreier.J4SSylowBase

public section

namespace CFSG.RankThree.PartTwo.Sec4.Item419ThetaProof

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.Assembly.RankThreeEven (projSU projSp)
open CFSG.Blueprint
open Sec21 Sec21.Item211Proof
open CFSG.RankThreeEvenClassification.Helpers (centralizer_map_eq_of_pGroup_prime_complement_kernel)

theorem not_isSolvable_of_isPerfect {Y : Type} [Group Y] [Nontrivial Y]
    (hY : Group.IsPerfect Y) : ¬ Group.IsSolvable Y := by
  intro hs
  obtain ⟨n, hn⟩ := hs.solvable
  rw [hY.derivedSeries_eq_top] at hn
  exact top_ne_bot hn

theorem card_projSU_three_two_one : Nat.card (projSU 3 2 1) = 72 := by
  have h := KFacts.KS14.card_projSU_three_mul_gcd 2 1 le_rfl
  norm_num at h
  omega

section Types


theorem isSimpleGroup_of_isType419Theta {Y : Type} [Group Y] (h : IsType419Theta Y)
    (hY : Group.IsPerfect Y) : IsSimpleGroup Y := by
  rcases h with ⟨n, hG2⟩ | hU | ⟨n, hF4⟩ | hT | ⟨n, hn, ⟨e⟩⟩ | hA | ⟨m, hm, ⟨e⟩⟩
  · exact (CFSG.LieType.Simplicity.fam_g2_simplicity Y 2 n hG2).2
  · obtain ⟨e⟩ := hU
    have := Sec19.Step1914TriProof.isSimpleGroup_projSU_three_of_ne_two 3 1 le_rfl (by norm_num)
    exact e.isSimpleGroup
  · exact (CFSG.LieType.Simplicity.fam_2f4_simplicity Y 2 n hF4).2
  · obtain ⟨e⟩ := CFSG.Sporadic.Schreier.Tits.titsModelEquiv Y 2 1 hT
    have := CFSG.Sporadic.Schreier.Tits.titsD_simple
    exact e.isSimpleGroup
  · have h4 : 4 ≤ Nat.card (GaloisField 2 n) := by
      rw [GaloisField.card 2 n (by omega)]
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
    have := CFSG.ClassicalGroups.Symplectic.isSimpleGroup_statedProj_statedSp
      (GaloisField 2 n) 2 (by norm_num) (Or.inl (Or.inr h4))
    exact (e.trans (Sec4.projSpEquivStatedProj 2 _)).isSimpleGroup
  · obtain ⟨e⟩ := hA
    have := alternatingGroup.isSimpleGroup (α := Fin 6) (by rw [Nat.card_fin]; norm_num)
    exact e.isSimpleGroup
  · obtain ⟨k, rfl⟩ := hm
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · exfalso
      have hcard : Nat.card Y = 72 := by
        rw [Nat.card_congr e.toEquiv]
        exact card_projSU_three_two_one
      have : Finite Y := Nat.finite_of_card_ne_zero (by omega)
      have : Nontrivial Y := Finite.one_lt_card_iff_nontrivial.mp (by omega)
      have hs : Group.IsSolvable (projSU 3 2 1) := Sec13.isSolvable_projSU_two
      exact not_isSolvable_of_isPerfect hY
        (Group.isSolvable_of_isSolvable_injective (f := (e.toMonoidHom : Y →* projSU 3 2 1))
          e.injective)
    · have hq : 2 ^ (2 * k + 1) ≠ 2 := by
        intro h2
        have h3 : 2 ^ (2 * k + 1) ≥ 2 ^ 3 := Nat.pow_le_pow_right (by norm_num) (by omega)
        omega
      have := Sec19.Step1914TriProof.isSimpleGroup_projSU_three_of_ne_two 2 (2 * k + 1)
        (by omega) hq
      exact e.isSimpleGroup

theorem isQuasisimple_of_isType419Theta {Y : Type} [Group Y] (h : IsType419Theta Y)
    (hY : Group.IsPerfect Y) : IsQuasisimple Y := by
  have hs := isSimpleGroup_of_isType419Theta h hY
  refine (CFSG.LocalCores.isQuasisimple_of_isSimpleGroup ?_).1
  by_contra hab
  push Not at hab
  have hcomm : commutator Y = ⊥ := by
    rw [commutator_def, eq_bot_iff, Subgroup.commutator_le]
    intro x _ y _
    rw [commutatorElement_def, hab x y, mul_inv_cancel_right, mul_inv_cancel, Subgroup.mem_bot]
  have htop : commutator Y = ⊤ := hY.commutator_eq_top
  obtain ⟨x, y, hxy⟩ := exists_pair_ne Y
  apply hxy
  have hx : x ∈ (⊥ : Subgroup Y) := hcomm ▸ htop ▸ Subgroup.mem_top x
  have hy : y ∈ (⊥ : Subgroup Y) := hcomm ▸ htop ▸ Subgroup.mem_top y
  rw [Subgroup.mem_bot] at hx hy
  rw [hx, hy]

end Types

theorem isType419Theta_of_mulEquiv {Y Z : Type} [Group Y] [Group Z] (e : Y ≃* Z)
    (h : IsType419Theta Z) : IsType419Theta Y := by
  rcases h with ⟨n, hG2⟩ | hU | ⟨n, hF4⟩ | hT | ⟨n, hn, ⟨f⟩⟩ | hA | ⟨m, hm, ⟨f⟩⟩
  · exact Or.inl ⟨n, CFSG.SectionRank.chevalleyExceptionalModel_of_mulEquiv e hG2⟩
  · obtain ⟨f⟩ := hU
    exact Or.inr (Or.inl ⟨e.trans f⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨n, CFSG.SectionRank.reeTitsModel_of_mulEquiv e hF4⟩))
  · exact Or.inr (Or.inr (Or.inr (Or.inl (CFSG.SectionRank.reeTitsModel_of_mulEquiv e hT))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨n, hn, ⟨e.trans f⟩⟩))))
  · obtain ⟨f⟩ := hA
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨e.trans f⟩)))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨m, hm, ⟨e.trans f⟩⟩)))))

variable {G : Type} [Group G] [Finite G] {L A : Subgroup G}

theorem isSolvable_theta (H : Type) [Group H] [Finite H] :
    Group.IsSolvable (aschbacherSolvableCore 3 H) :=
  (solvable_prime_complement_core_characterization Nat.prime_three).1

theorem nonempty_kOne_equiv_thetaImage (hL : L.IsSubnormal) (hAp : IsPGroup 3 A)
    (hAL : A ≤ Subgroup.normalizer (L : Set G)) {K : Subgroup G} (hKL : K ≤ L) :
    Nonempty (↥((K.subgroupOf (L ⊔ A)).map (piX L A)) ≃* ↥(thetaImage K)) := by
  have hKLA : K ≤ L ⊔ A := hKL.trans le_sup_left
  set f₁ : K →* G ⧸ aschbacherSolvableCore 3 G :=
    (QuotientGroup.mk' (aschbacherSolvableCore 3 G)).comp K.subtype with hf₁
  set f₂ : K →* QuotX L A := (piX L A).comp (Subgroup.inclusion hKLA) with hf₂
  have hθ := inSubgroup_theta_sup hAp hAL
  have hint := solvable_prime_complement_core_subnormal_intersection Nat.prime_three hL
  have hker : f₂.ker = f₁.ker := by
    ext k
    rw [MonoidHom.mem_ker, MonoidHom.mem_ker, hf₁, hf₂, MonoidHom.comp_apply,
      MonoidHom.comp_apply, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply,
      QuotientGroup.eq_one_iff, QuotientGroup.eq_one_iff]
    constructor
    · intro h
      have h1 : (k : G) ∈ inSubgroup (aschbacherSolvableCore 3) (L ⊔ A) := ⟨_, h, rfl⟩
      rw [hθ, hint] at h1
      exact h1.2
    · intro h
      have h1 : (k : G) ∈ inSubgroup (aschbacherSolvableCore 3) (L ⊔ A) := by
        rw [hθ, hint]
        exact ⟨hKL k.2, h⟩
      obtain ⟨y, hy, hyk⟩ := h1
      have : y = Subgroup.inclusion hKLA k := Subtype.ext hyk
      rwa [← this]
  have hr₁ : f₁.range = thetaImage K := by
    rw [hf₁, MonoidHom.range_comp, Subgroup.range_subtype]
    rfl
  have hr₂ : f₂.range = (K.subgroupOf (L ⊔ A)).map (piX L A) := by
    rw [hf₂, MonoidHom.range_comp, Subgroup.inclusion_range]
  exact ⟨(MulEquiv.subgroupCongr hr₂).symm.trans
    ((QuotientGroup.quotientKerEquivRange f₂).symm.trans
      ((QuotientGroup.quotientMulEquivOfEq hker).trans
        ((QuotientGroup.quotientKerEquivRange f₁).trans (MulEquiv.subgroupCongr hr₁))))⟩

theorem map_mem_thetaComponentsIn_quotient {H : Type} [Group H] [Finite H] (N : Subgroup H)
    [N.Normal] (hNs : Group.IsSolvable N) (hN3 : ¬ 3 ∣ Nat.card N) {M K : Subgroup H}
    (hK : K ∈ thetaComponentsIn M) :
    K.map (QuotientGroup.mk' N) ∈ thetaComponentsIn (M.map (QuotientGroup.mk' N)) := by
  obtain ⟨hKM, hK'⟩ := mem_thetaComponentsIn_iff.mp hK
  set π := QuotientGroup.mk' N with hπ
  let f : M →* M.map π := π.subgroupMap M
  have hf : Function.Surjective f := π.subgroupMap_surjective M
  let ι : f.ker →* N := (M.subtype.comp f.ker.subtype).codRestrict N fun x =>
    (QuotientGroup.eq_one_iff _).mp (congrArg Subtype.val x.2)
  have hι : Function.Injective ι := fun x y hxy =>
    Subtype.ext (Subtype.ext (congrArg (fun z : N => (z : H)) hxy))
  have hks : Group.IsSolvable f.ker := Group.isSolvable_of_isSolvable_injective hι
  have hkp : ¬ 3 ∣ Nat.card f.ker := fun h => hN3 (h.trans (Subgroup.card_dvd_of_injective ι hι))
  have hmem := CFSG.RankThree.PartOne.EmbeddingTransport.map_mem_thetaComponents_of_surjective
    Nat.prime_three f hf hks hkp hK'
  refine mem_thetaComponentsIn_iff.mpr ⟨Subgroup.map_mono hKM, ?_⟩
  convert hmem using 1
  ext z
  rw [Subgroup.mem_subgroupOf]
  constructor
  · rintro ⟨k, hk, hkz⟩
    exact ⟨⟨k, hKM hk⟩, Subgroup.mem_subgroupOf.mpr hk, Subtype.ext hkz⟩
  · rintro ⟨m, hm, rfl⟩
    exact ⟨m, Subgroup.mem_subgroupOf.mp hm, rfl⟩

theorem map_inf_centralizer_eq (hAp : IsPGroup 3 A) (hAL : A ≤ Subgroup.normalizer (L : Set G))
    {a : G} (ha : a ∈ A) :
    ((L ⊓ Subgroup.centralizer ({a} : Set G)).subgroupOf (L ⊔ A)).map (piX L A) =
      lOne L A ⊓ Subgroup.centralizer
        ({piX L A ⟨a, Subgroup.mem_sup_right ha⟩} : Set (QuotX L A)) := by
  set a' : ↥(L ⊔ A) := ⟨a, Subgroup.mem_sup_right ha⟩ with ha'
  have hpg : IsPGroup 3 (Subgroup.zpowers a') :=
    (isPGroup_subgroupOf (L := L) hAp).to_le
      (Subgroup.zpowers_le.mpr (Subgroup.mem_subgroupOf.mpr ha))
  have hker : ¬ 3 ∣ Nat.card (piX L A).ker := by
    rw [QuotientGroup.ker_mk']
    exact three_not_dvd_card_aschbacherSolvableCore
  have hC : (Subgroup.centralizer ({a'} : Set ↥(L ⊔ A))).map (piX L A) =
      Subgroup.centralizer ({piX L A a'} : Set (QuotX L A)) := by
    have h := centralizer_map_eq_of_pGroup_prime_complement_kernel 3 Nat.prime_three (piX L A)
      (QuotientGroup.mk'_surjective _) hker _ hpg
    rwa [← CFSG.RankThree.GroupTheory.SteinbergBY.centralizer_singleton_eq_centralizer_zpowers,
      MonoidHom.map_zpowers,
      ← CFSG.RankThree.GroupTheory.SteinbergBY.centralizer_singleton_eq_centralizer_zpowers] at h
  have hθ := theta_le_subgroupOf hAp hAL
  apply le_antisymm
  · rintro _ ⟨m, hm, rfl⟩
    have hm' : (m : G) ∈ L ⊓ Subgroup.centralizer ({a} : Set G) := Subgroup.mem_subgroupOf.mp hm
    refine ⟨⟨m, Subgroup.mem_subgroupOf.mpr hm'.1, rfl⟩, ?_⟩
    rw [← hC]
    refine ⟨m, ?_, rfl⟩
    rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff]
    exact Subtype.ext (Subgroup.mem_centralizer_singleton_iff.mp hm'.2)
  · rintro x ⟨⟨l, hl, rfl⟩, hx⟩
    rw [← hC] at hx
    obtain ⟨y, hy, hyx⟩ := hx
    have hly : l⁻¹ * y ∈ aschbacherSolvableCore 3 ↥(L ⊔ A) := by
      rw [← QuotientGroup.eq]
      exact hyx.symm
    have hyL : y ∈ L.subgroupOf (L ⊔ A) := by
      have h1 := (L.subgroupOf (L ⊔ A)).mul_mem hl (hθ hly)
      rwa [mul_inv_cancel_left] at h1
    refine ⟨y, Subgroup.mem_subgroupOf.mpr ⟨Subgroup.mem_subgroupOf.mp hyL, ?_⟩, hyx⟩
    rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff] at hy
    change (y : G) ∈ Subgroup.centralizer ({a} : Set G)
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact congrArg Subtype.val hy

section Component


theorem isComponent_kOne (hL : L ∈ thetaComponents 3 G) (hAp : IsPGroup 3 A)
    (hAL : A ≤ Subgroup.normalizer (L : Set G)) {a : G} (ha : a ∈ A) {K : Subgroup G}
    (hK : K ∈ thetaComponentsIn (L ⊓ Subgroup.centralizer ({a} : Set G)))
    (htype : IsType419Theta ↥(thetaImage K)) :
    (K.subgroupOf (L ⊔ A)).map (piX L A) ≤ lOne L A ⊓ Subgroup.centralizer
        ({piX L A ⟨a, Subgroup.mem_sup_right ha⟩} : Set (QuotX L A)) ∧
      IsComponent (((K.subgroupOf (L ⊔ A)).map (piX L A)).subgroupOf
        (lOne L A ⊓ Subgroup.centralizer
          ({piX L A ⟨a, Subgroup.mem_sup_right ha⟩} : Set (QuotX L A)))) ∧
      IsType419Theta ↥((K.subgroupOf (L ⊔ A)).map (piX L A)) ∧
      Nonempty (↥((K.subgroupOf (L ⊔ A)).map (piX L A)) ≃* ↥(thetaImage K)) := by
  have hKL : K ≤ L := (le_of_mem_thetaComponentsIn hK).trans inf_le_left
  have hmap : ((L ⊓ Subgroup.centralizer ({a} : Set G)).subgroupOf (L ⊔ A)).map
      (L ⊔ A).subtype = L ⊓ Subgroup.centralizer ({a} : Set G) :=
    Subgroup.map_subgroupOf_eq_of_le (inf_le_left.trans le_sup_left)
  have hK₀ := Sec8.Item87Proof.subgroupOf_mem_thetaComponentsIn hmap hK
  have hK₁ := map_mem_thetaComponentsIn_quotient (aschbacherSolvableCore 3 ↥(L ⊔ A))
    (isSolvable_theta _) three_not_dvd_card_aschbacherSolvableCore hK₀
  rw [map_inf_centralizer_eq hAp hAL ha] at hK₁
  obtain ⟨hle, hK₁'⟩ := mem_thetaComponentsIn_iff.mp hK₁
  obtain ⟨eK⟩ := nonempty_kOne_equiv_thetaImage hL.2.1 hAp hAL hKL
  have e₀ := Subgroup.subgroupOfEquivOfLe hle
  have hperf : Group.IsPerfect ↥((K.subgroupOf (L ⊔ A)).map (piX L A)) := by
    have := hK₁'.1
    exact Group.IsPerfect.ofSurjective (f := e₀.toMonoidHom) e₀.surjective
  have htype₁ := isType419Theta_of_mulEquiv eK htype
  have hq := isQuasisimple_of_isType419Theta htype₁ hperf
  exact ⟨hle, ⟨CFSG.LocalCores.isQuasisimple_of_mulEquiv e₀.symm hq, hK₁'.2.1⟩, htype₁, ⟨eK⟩⟩

end Component

theorem card_le_of_mem_partTwoF_quotX (hF : ∀ A₀ ∈ partTwoF G, Nat.card A₀ ≤ 3 ^ 4) :
    ∀ A₀ ∈ partTwoF (QuotX L A), Nat.card A₀ ≤ 3 ^ 4 := by
  rintro A₀ ⟨hA₀e, -, E₀, ⟨hE₀e, hE₀card, T, hT1, hT2, hE₀T⟩, hE₀A₀⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨E'', -, hE''map, hE''card, hE''e⟩ := exists_lift_of_le (L := L) (A := A) (T := ⊥)
    IsPGroup.of_bot hE₀e (by rw [Subgroup.map_bot]; exact bot_le)
  have hE''p : IsPGroup 3 E'' := fun x => ⟨1, Subtype.ext (by simpa using hE''e.2 x x.2)⟩
  obtain ⟨S, hE''S, -, hScard, hSe⟩ :=
    exists_lift_of_le hE''p hA₀e (by rw [hE''map]; exact hE₀A₀)
  set N := aschbacherSolvableCore 3 ↥(L ⊔ A) with hN
  set D : Subgroup ↥(L ⊔ A) := T.comap (piX L A) with hD
  have hDcard : Nat.card D = Nat.card N * Nat.card T :=
    QuotientGroup.card_preimage_mk N (T : Set (QuotX L A))
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hT2
  have hk0 : k ≠ 0 := by
    rintro rfl
    rw [pow_zero] at hk
    exact hT1 (Subgroup.card_eq_one.mp hk)
  have hcop : Nat.Coprime 3 (Nat.card D) := by
    rw [hDcard, hk]
    exact Nat.Coprime.mul_right
      ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr
        three_not_dvd_card_aschbacherSolvableCore)
      (Nat.Coprime.pow_right k (by norm_num))
  have h2 : 2 ∣ Nat.card D := by
    rw [hDcard, hk]
    exact Dvd.dvd.mul_left (dvd_pow_self 2 hk0) _
  have hE''D : E'' ≤ Subgroup.normalizer (D : Set ↥(L ⊔ A)) := by
    intro x hx
    have hxE : piX L A x ∈ E₀ := by
      rw [← hE''map]
      exact ⟨x, hx, rfl⟩
    exact Subgroup.le_normalizer_comap (piX L A) (hE₀T hxE)
  obtain ⟨Q, hQN, hQ1⟩ :=
    CFSG.SignalizerFunctor.Helpers.normalized_subgroup_invariant_sylow_nontrivial
      3 2 Nat.prime_three Nat.prime_two E'' D hE''p hE''D hcop h2
  set U₁ : Subgroup G := ((Q : Subgroup D).map D.subtype).map (L ⊔ A).subtype with hU₁
  have hE₂ : E''.map (L ⊔ A).subtype ∈ partTwoE G := by
    refine ⟨isElemAbelian_map_subtype hE''e, ?_, U₁, ?_, ?_, ?_⟩
    · rw [Subgroup.card_map_of_injective (L ⊔ A).subtype_injective, hE''card, hE₀card]
    · intro h0
      apply hQ1
      rwa [hU₁, Subgroup.map_eq_bot_iff_of_injective _ (L ⊔ A).subtype_injective] at h0
    · exact (Q.isPGroup'.map D.subtype).map (L ⊔ A).subtype
    · exact (Subgroup.map_mono hQN).trans (Subgroup.le_normalizer_map _)
  obtain ⟨B, hSB, hBmax⟩ := Finite.exists_le_maximal
    (p := fun B : Subgroup G => CFSG.Assembly.IsElemAbelian 3 B) (isElemAbelian_map_subtype hSe)
  have hBF : B ∈ partTwoF G :=
    ⟨hBmax.prop, fun B' hB' hBB' => le_antisymm (hBmax.2 hB' hBB') hBB', _, hE₂,
      (Subgroup.map_mono hE''S).trans hSB⟩
  calc Nat.card A₀ = Nat.card S := hScard.symm
    _ = Nat.card (S.map (L ⊔ A).subtype) :=
        (Subgroup.card_map_of_injective (L ⊔ A).subtype_injective).symm
    _ ≤ Nat.card B := Subgroup.card_le_of_le hSB
    _ ≤ 3 ^ 4 := hF B hBF

end CFSG.RankThree.PartTwo.Sec4.Item419ThetaProof
