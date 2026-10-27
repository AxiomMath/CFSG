module

import CFSG.RankThree.PartTwo.Sec15.Sylow155R1T114
import CFSG.RankThree.PartTwo.Sec15.Sylow155TwinB
import CFSG.RankThree.PartTwo.Sec13.Item13ResProofE9
import CFSG.RankThree.PartTwo.Sec3.ThompsonFamilyG
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.RankThreeCoreUniqueness.CoprimeQuotientRank
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.RankThree.PartTwo.KFacts.KS14MultCore
public import CFSG.RankThree.PartTwo.Sec15.Item153ClaimsTools
public import CFSG.RankThree.PartTwo.Sec15.Item155R2ProofCases
public import CFSG.Sporadic.Mathieu.M22

public section

namespace CFSG.RankThree.PartTwo.Sec15.Sylow155R1

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.LocalRank CFSG.GH74.GLS
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem le_normalizer_of_faithful {A : Subgroup G} {c : G} {L : Subgroup G}
    (h : Sec14Std G A c L) {S : Set G} {M X F : Subgroup G}
    (hM : M ∈ CFSG.maximalTwoLocalsContaining S) (hXM : X ∈ thetaComponentsIn M)
    (hFX : F ≤ X) (hFe : ∀ f ∈ F, f ^ 3 = 1) (hFc : ∀ f ∈ F, ∀ f' ∈ F, f * f' = f' * f)
    (hF9 : Nat.card F = 9)
    (hFf : ∀ f ∈ F,
      (∀ x ∈ X, f * x * f⁻¹ * x⁻¹ ∈ (aschbacherSolvableCore 3 ↥M).map M.subtype) → f = 1) :
    M ≤ Subgroup.normalizer (X : Set G) := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  intro m hm
  by_contra hmX
  obtain ⟨hXM', hY'⟩ := mem_thetaComponentsIn_iff.mp hXM
  set Y' := X.subgroupOf M with hY'def
  set θ := aschbacherSolvableCore 3 ↥M with hθ
  set π := QuotientGroup.mk' θ with hπ
  set g : ↥M := ⟨m, hm⟩ with hg
  set κ := (MulAut.conj g).toMonoidHom with hκ
  have hYY' : Y'.map M.subtype = X := by
    rw [hY'def, Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hXM']
  have hYc : Y'.map κ ∈ thetaComponents 3 ↥M :=
    map_mulEquiv_mem_thetaComponents Nat.prime_three (MulAut.conj g) hY'
  have hne : Y' ≠ Y'.map κ := by
    intro he
    apply hmX
    have h1 : (Y'.map M.subtype).map (MulAut.conj m : G →* G) = (Y'.map κ).map M.subtype := by
      rw [Subgroup.map_map, Subgroup.map_map]
      congr 1
    rw [← he, hYY'] at h1
    exact Subgroup.mem_normalizer_iff_map_conj_eq.mpr h1
  have cc := commutator_le_of_mem_thetaComponents hY' hYc hne
  have hπθ : ∀ t : ↥M, t ∈ θ → π t = 1 := fun t ht => by
    rw [← QuotientGroup.ker_mk' θ] at ht
    exact ht
  have hθπ : ∀ t : ↥M, π t = 1 → t ∈ θ := fun t ht => by
    rw [← QuotientGroup.ker_mk' θ]
    exact ht
  have hYY : ∀ y ∈ Y', ∀ y' ∈ Y'.map κ, π y * π y' = π y' * π y := by
    intro y hy y' hy'
    have h1 : π ⁅y, y'⁆ = 1 := hπθ _ (cc (Subgroup.commutator_mem_commutator hy hy'))
    rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm] at h1
    exact h1
  have hFM : F ≤ M := hFX.trans hXM'
  set F₁ := F.subgroupOf M with hF₁
  have hFY : F₁ ≤ Y' := fun f hf =>
    Subgroup.mem_subgroupOf.mpr (hFX (Subgroup.mem_subgroupOf.mp hf))
  set Fs := F₁.map π with hFs
  set F's := (F₁.map κ).map π with hF's
  have hcomm : ∀ a ∈ Fs, ∀ b ∈ F's, a * b = b * a := by
    rintro _ ⟨f, hf, rfl⟩ _ ⟨_, ⟨f', hf', rfl⟩, rfl⟩
    exact hYY f (hFY hf) _ (Subgroup.mem_map_of_mem κ (hFY hf'))
  have hinf : Fs ⊓ F's = ⊥ := by
    rw [eq_bot_iff]
    rintro _ ⟨⟨f, hf, rfl⟩, ⟨_, ⟨f', hf', rfl⟩, hff'⟩⟩
    rw [Subgroup.mem_bot]
    have hf1 : (f : G) = 1 := by
      refine hFf _ (Subgroup.mem_subgroupOf.mp hf) fun x hx => ?_
      have hxM := hXM' hx
      have h3 := hYY ⟨x, hxM⟩ (Subgroup.mem_subgroupOf.mpr hx) _
        (Subgroup.mem_map_of_mem κ (hFY hf'))
      rw [hff'] at h3
      have h2 : π (f * ⟨x, hxM⟩ * f⁻¹ * (⟨x, hxM⟩ : ↥M)⁻¹) = 1 := by
        rw [map_mul, map_mul, map_mul, map_inv, map_inv, ← h3]
        group
      exact Subgroup.mem_map.mpr ⟨_, hθπ _ h2, rfl⟩
    rw [show f = 1 from Subtype.ext hf1, map_one]
  have hker : Nat.Coprime 3 (Nat.card π.ker) := by
    rw [hπ, QuotientGroup.ker_mk']
    obtain ⟨-, -, hθ3, -⟩ :=
      solvable_prime_complement_core_characterization (H := ↥M) Nat.prime_three
    exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr hθ3
  have hcardmap : ∀ T : Subgroup ↥M, IsPGroup 3 T → Nat.card (T.map π) = Nat.card T :=
    fun T hT => by
      obtain ⟨e⟩ := CFSG.RankThreeCoreUniqueness.Helpers.coprime_kernel_pGroup_equiv_image 3
        Nat.prime_three π hker T hT
      exact (Nat.card_congr e.toEquiv).symm
  have hF3 : IsPGroup 3 F₁ := fun f =>
    ⟨1, Subtype.ext (Subtype.ext (by simpa using hFe _ (Subgroup.mem_subgroupOf.mp f.2)))⟩
  have hF₁card : Nat.card F₁ = 9 := by
    rw [hF₁, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hFM).toEquiv, hF9]
  have hFscard : Nat.card Fs = 9 := by rw [hFs, hcardmap _ hF3, hF₁card]
  have hF'scard : Nat.card F's = 9 := by
    rw [hF's, hcardmap _ (hF3.map κ),
      Subgroup.card_map_of_injective (f := κ) (MulAut.conj g).injective, hF₁card]
  have hVcard : Nat.card ↥(Fs ⊔ F's) = 81 := by
    have h1 := Sec3.card_sup_mul_card_inf_of_commute hcomm
    rw [hinf, Subgroup.card_bot, mul_one, hFscard, hF'scard] at h1
    omega
  have hFF : ∀ a ∈ Fs, ∀ b ∈ Fs, a * b = b * a := by
    rintro _ ⟨f, hf, rfl⟩ _ ⟨f', hf', rfl⟩
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (hFc _ (Subgroup.mem_subgroupOf.mp hf) _ (Subgroup.mem_subgroupOf.mp hf'))
  have hF'F' : ∀ a ∈ F's, ∀ b ∈ F's, a * b = b * a := by
    rintro _ ⟨_, ⟨f, hf, rfl⟩, rfl⟩ _ ⟨_, ⟨f', hf', rfl⟩, rfl⟩
    have h' : f * f' = f' * f :=
      Subtype.ext (hFc _ (Subgroup.mem_subgroupOf.mp hf) _ (Subgroup.mem_subgroupOf.mp hf'))
    rw [← map_mul π, ← map_mul π, ← map_mul κ, ← map_mul κ, h']
  have hVcl : Fs ⊔ F's = Subgroup.closure ((Fs : Set (↥M ⧸ θ)) ∪ (F's : Set (↥M ⧸ θ))) := by
    rw [Subgroup.closure_union, Subgroup.closure_eq, Subgroup.closure_eq]
  have hVcomm : ∀ a ∈ Fs ⊔ F's, ∀ b ∈ Fs ⊔ F's, a * b = b * a := by
    have hT : ∀ a ∈ ((Fs : Set (↥M ⧸ θ)) ∪ (F's : Set (↥M ⧸ θ))),
        ∀ b ∈ ((Fs : Set (↥M ⧸ θ)) ∪ (F's : Set (↥M ⧸ θ))), a * b = b * a := by
      intro a ha b hb
      rcases ha with ha | ha <;> rcases hb with hb | hb
      · exact hFF a ha b hb
      · exact hcomm a ha b hb
      · exact (hcomm b hb a ha).symm
      · exact hF'F' a ha b hb
    intro a ha b hb
    rw [hVcl] at ha hb
    exact KFacts.KS14.commute_of_mem_closure hT ha hb
  have hVe : ∀ v ∈ Fs ⊔ F's, v ^ 3 = 1 := by
    intro v hv
    rw [hVcl] at hv
    induction hv using Subgroup.closure_induction with
    | mem a ha =>
      rcases ha with ⟨f, hf, rfl⟩ | ⟨_, ⟨f, hf, rfl⟩, rfl⟩
      · rw [← map_pow, show f ^ 3 = 1 from
          Subtype.ext (by simpa using hFe _ (Subgroup.mem_subgroupOf.mp hf)), map_one]
      · rw [← map_pow, ← map_pow, show f ^ 3 = 1 from
          Subtype.ext (by simpa using hFe _ (Subgroup.mem_subgroupOf.mp hf)), map_one, map_one]
    | one => exact one_pow 3
    | mul a b ha hb iha ihb =>
      rw [(show Commute a b from hVcomm a (hVcl ▸ ha) b (hVcl ▸ hb)).mul_pow 3, iha, ihb,
        one_mul]
    | inv a ha iha => rw [inv_pow, iha, inv_one]
  have hEc : IsMulCommutative ↥(Fs ⊔ F's) :=
    ⟨⟨fun a b => Subtype.ext (hVcomm _ a.2 _ b.2)⟩⟩
  exact Sylow155T.false_of_card_eighty_one h hM hEc hVe hVcard

theorem exists_faithful_e9 {M L : Subgroup G} (hLM : L ≤ M)
    (hZ : Subgroup.center (↥L ⧸ aschbacherSolvableCore 3 ↥L) = ⊥)
    (hE9 : ∃ E : Subgroup (↥L ⧸ aschbacherSolvableCore 3 ↥L), (∀ e ∈ E, e ^ 3 = 1) ∧
      Nat.card E = 9) :
    ∃ F : Subgroup G, F ≤ L ∧ (∀ f ∈ F, f ^ 3 = 1) ∧ (∀ f ∈ F, ∀ f' ∈ F, f * f' = f' * f) ∧
      Nat.card F = 9 ∧
      ∀ f ∈ F, (∀ l ∈ L, f * l * f⁻¹ * l⁻¹ ∈ (aschbacherSolvableCore 3 ↥M).map M.subtype) →
        f = 1 := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨E, hEe, hE9⟩ := hE9
  set θL := aschbacherSolvableCore 3 ↥L with hθL
  set πL := QuotientGroup.mk' θL with hπL
  obtain ⟨-, -, hθL3, hθLmax, -⟩ :=
    solvable_prime_complement_core_characterization (H := ↥L) Nat.prime_three
  obtain ⟨hθMsol, hθMchar, hθM3, -⟩ :=
    solvable_prime_complement_core_characterization (H := ↥M) Nat.prime_three
  have hker : Nat.Coprime 3 (Nat.card πL.ker) := by
    rw [hπL, QuotientGroup.ker_mk']
    exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr hθL3
  have hE3 : IsPGroup 3 E := fun e => ⟨1, Subtype.ext (by simpa using hEe e e.2)⟩
  obtain ⟨R, -, ⟨eR⟩⟩ := CFSG.RankThreeCoreUniqueness.Helpers.coprime_kernel_lifts_pSubgroup 3
    Nat.prime_three πL (QuotientGroup.mk'_surjective θL) hker E hE3
  have hEc : IsMulCommutative E :=
    IsPGroup.isMulCommutative_of_card_eq_prime_sq (p := 3) (by rw [hE9]; norm_num)
  have hRcomm : ∀ a b : R, a * b = b * a := fun a b => eR.injective (by
    rw [map_mul, map_mul]
    exact hEc.is_comm.comm _ _)
  have hRe : ∀ a : R, a ^ 3 = 1 := fun a => eR.injective (by
    rw [map_pow, map_one]
    exact Subtype.ext (by simpa using hEe _ (eR a).2))
  set N : Subgroup ↥L := (aschbacherSolvableCore 3 ↥M).comap (Subgroup.inclusion hLM) with hN
  have hNn : N.Normal := by
    haveI : (aschbacherSolvableCore 3 ↥M).Characteristic := hθMchar
    exact Subgroup.Normal.comap inferInstance _
  have hinj : Function.Injective
      ((Subgroup.inclusion hLM).subgroupComap (aschbacherSolvableCore 3 ↥M)) := by
    intro a b hab
    have h1 : Subgroup.inclusion hLM (a : ↥L) = Subgroup.inclusion hLM (b : ↥L) :=
      congrArg Subtype.val hab
    exact Subtype.ext (Subgroup.inclusion_injective hLM h1)
  have hNsol : Group.IsSolvable N := by
    haveI := hθMsol
    exact Group.isSolvable_of_isSolvable_injective hinj
  have hN3 : ¬ 3 ∣ Nat.card N := fun h3 =>
    hθM3 (h3.trans (Subgroup.card_dvd_of_injective _ hinj))
  have hNθ : N ≤ θL := hθLmax N hNn hNsol hN3
  refine ⟨R.map L.subtype, Subgroup.map_subtype_le R, ?_, ?_, ?_, ?_⟩
  · rintro _ ⟨r, hr, rfl⟩
    have h1 : r ^ 3 = 1 := by simpa using congrArg Subtype.val (hRe ⟨r, hr⟩)
    rw [← map_pow, h1, map_one]
  · rintro _ ⟨r, hr, rfl⟩ _ ⟨r', hr', rfl⟩
    have h1 : r * r' = r' * r := by
      simpa using congrArg Subtype.val (hRcomm ⟨r, hr⟩ ⟨r', hr'⟩)
    rw [← map_mul, ← map_mul, h1]
  · rw [Subgroup.card_map_of_injective L.subtype_injective, Nat.card_congr eR.toEquiv, hE9]
  · rintro _ ⟨r, hr, rfl⟩ hf
    have hcommN : ∀ l : ↥L, ⁅r, l⁆ ∈ N := by
      intro l
      obtain ⟨t, ht, hteq⟩ := Subgroup.mem_map.mp (hf l l.2)
      have hteq' : (t : G) = (r : G) * l * (r : G)⁻¹ * (l : G)⁻¹ := hteq
      have h1 : Subgroup.inclusion hLM ⁅r, l⁆ = t := by
        apply Subtype.ext
        rw [hteq']
        simp [commutatorElement_def]
      rw [hN, Subgroup.mem_comap, h1]
      exact ht
    have hcen : πL r ∈ Subgroup.center (↥L ⧸ θL) := by
      rw [Subgroup.mem_center_iff]
      intro q
      obtain ⟨l, rfl⟩ := QuotientGroup.mk'_surjective θL q
      have h1 : πL ⁅r, l⁆ = 1 := by
        have h2 := hNθ (hcommN l)
        rw [← QuotientGroup.ker_mk' θL] at h2
        exact h2
      rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm] at h1
      exact h1.symm
    rw [hZ, Subgroup.mem_bot] at hcen
    have hrθ : r ∈ θL := by
      rw [← QuotientGroup.ker_mk' θL]
      exact hcen
    have h3 : r ^ 3 = 1 := by simpa using congrArg Subtype.val (hRe ⟨r, hr⟩)
    rw [eq_one_of_mem_of_pow_three hθL3 hrθ h3, map_one]

theorem le_normalizer_x_of_le {A : Subgroup G} {c : G} {L : Subgroup G} (h : Sec14Std G A c L)
    {X K Y M T P : Subgroup G} (hC : Ctx155 A X K Y M T) (hE : End155N A X K Y M T P)
    (hLX : L ≤ X) (hZ : Subgroup.center (↥L ⧸ aschbacherSolvableCore 3 ↥L) = ⊥)
    (hE9 : ∃ E : Subgroup (↥L ⧸ aschbacherSolvableCore 3 ↥L), (∀ e ∈ E, e ^ 3 = 1) ∧
      Nat.card E = 9) :
    M ≤ Subgroup.normalizer (X : Set G) := by
  have hXM := (mem_thetaComponentsIn_iff.mp hE.mem_x).1
  obtain ⟨F, hFL, hFe, hFc, hF9, hFf⟩ := exists_faithful_e9 (hLX.trans hXM) hZ hE9
  exact le_normalizer_of_faithful h hC.mem_m hE.mem_x (hFL.trans hLX) hFe hFc hF9
    fun f hf hx => hFf f hf fun l hl => hx l (hLX hl)

theorem eq_normalizer_x_of_le_of_center {A : Subgroup G} {c : G} {L : Subgroup G}
    (h : Sec14Std G A c L) (h149 : Item149 A (lB A)) {X K Y M T P : Subgroup G}
    (hC : Ctx155 A X K Y M T) (hE : End155N A X K Y M T P)
    (hIX : delta A (lB A) M ≤ Subgroup.normalizer (X : Set G)) (hLX : L ≤ X)
    (hZ : Subgroup.center (↥L ⧸ aschbacherSolvableCore 3 ↥L) = ⊥)
    (hE9 : ∃ E : Subgroup (↥L ⧸ aschbacherSolvableCore 3 ↥L), (∀ e ∈ E, e ^ 3 = 1) ∧
      Nat.card E = 9) :
    M = Subgroup.normalizer (X : Set G) ∧
      M = Subgroup.normalizer (CFSG.Open.pCoreOf 2 X : Set G) :=
  eq_normalizer_x_of_le h h149 hC hIX (le_normalizer_x_of_le h hC hE hLX hZ hE9)

theorem center_eq_bot_and_e9_of_mulEquiv {Q R : Type*} [Group Q] [Group R] (e : Q ≃* R)
    (hZ : Subgroup.center R = ⊥)
    (hE : ∃ E : Subgroup R, Monoid.exponent E ∣ 3 ∧ Nat.card E = 9) :
    Subgroup.center Q = ⊥ ∧ ∃ E : Subgroup Q, (∀ x ∈ E, x ^ 3 = 1) ∧ Nat.card E = 9 := by
  refine ⟨?_, ?_⟩
  · rw [eq_bot_iff]
    intro z hz
    rw [Subgroup.mem_bot]
    have h1 : e z ∈ Subgroup.center R := by
      rw [Subgroup.mem_center_iff] at hz ⊢
      intro r
      obtain ⟨q, rfl⟩ := e.surjective r
      rw [← map_mul, ← map_mul, hz q]
    rw [hZ, Subgroup.mem_bot] at h1
    exact e.injective (h1.trans (map_one e).symm)
  · obtain ⟨E, hEe, hE9⟩ := hE
    refine ⟨E.map e.symm.toMonoidHom, ?_, ?_⟩
    · rintro _ ⟨y, hy, rfl⟩
      have h1 : (⟨y, hy⟩ : E) ^ 3 = 1 := Monoid.exponent_dvd_iff_forall_pow_eq_one.mp hEe _
      have h2 : y ^ 3 = 1 := by simpa using congrArg Subtype.val h1
      rw [← map_pow, h2, map_one]
    · rw [Subgroup.card_map_of_injective (f := e.symm.toMonoidHom) e.symm.injective, hE9]

theorem center_eq_bot_and_e9_of_a7 {Q : Type*} [Group Q] (e : Q ≃* alternatingGroup (Fin 7)) :
    Subgroup.center Q = ⊥ ∧ ∃ E : Subgroup Q, (∀ x ∈ E, x ^ 3 = 1) ∧ Nat.card E = 9 :=
  center_eq_bot_and_e9_of_mulEquiv e (alternatingGroup.center_eq_bot (by simp))
    ResProof.exists_e9_alt7

theorem center_eq_bot_and_e9_of_m22
    {Q : Type*} [Group Q] (e : Q ≃* CFSG.Blueprint.NativeSporadic.M22) :
    Subgroup.center Q = ⊥ ∧ ∃ E : Subgroup Q, (∀ x ∈ E, x ^ 3 = 1) ∧ Nat.card E = 9 := by
  obtain ⟨-, -, hs⟩ := CFSG.Sporadic.Mathieu.fam_m22_simplicity
  refine center_eq_bot_and_e9_of_mulEquiv e ?_ ResProof.exists_e9_m22
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal
      (Subgroup.center CFSG.Blueprint.NativeSporadic.M22) with h | h
  · exact h
  · exfalso
    haveI : IsMulCommutative CFSG.Blueprint.NativeSporadic.M22 :=
      ⟨⟨fun a b => (Subgroup.mem_center_iff.mp (h ▸ Subgroup.mem_top b : b ∈ _) a)⟩⟩
    have hp := Group.is_simple_iff_prime_card.mp hs
    rw [CFSG.Sporadic.Mathieu.card_M22] at hp
    norm_num at hp

end CFSG.RankThree.PartTwo.Sec15.Sylow155R1
