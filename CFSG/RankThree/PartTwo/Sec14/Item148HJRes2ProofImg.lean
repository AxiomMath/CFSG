module

import CFSG.RankThree.PartTwo.Sec14.Item148StepCases
import CFSG.RankThree.PartTwo.Sec14.Item148HJProofLB
import CFSG.RankThree.PartTwo.Sec14.Concrete
import CFSG.RankThree.PartTwo.Sec13.Item13Basic
public import CFSG.CGT.PushingUpLit.Transport
public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.LocalAnalysis.SeitzReduction.EPilotPosition
public import CFSG.LocalAnalysis.SignalizerFunctor.AmbientCommutators
public import CFSG.RankThree.GroupTheory.SteinbergCEThetaQuotientAction
public import CFSG.RankThree.PartTwo.Sec14.Item148MainProofHJ
public import CFSG.RankThree.PartTwo.Sec14.Item148MainProofLift
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

namespace CFSG.RankThree.PartTwo.Sec14

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.LocalRank CFSG.GH74.GLS

variable {G : Type} [Group G] [Finite G]

namespace HJRes2

open Main148

section Quot

variable {A Y : Subgroup G} [(ker148 A Y).Normal]

omit [Finite G] in
theorem img148_commutator_eq {X X' : Subgroup G} (hX : X ≤ Y ⊔ A) (hX' : X' ≤ Y ⊔ A) :
    img148 A Y ⁅X, X'⁆ = ⁅img148 A Y X, img148 A Y X'⁆ := by
  unfold img148
  have key : ⁅X, X'⁆.subgroupOf (Y ⊔ A) =
      ⁅X.subgroupOf (Y ⊔ A), X'.subgroupOf (Y ⊔ A)⁆ := by
    have h1 : ⁅X, X'⁆ = (⁅X.subgroupOf (Y ⊔ A), X'.subgroupOf (Y ⊔ A)⁆).map (Y ⊔ A).subtype := by
      rw [Subgroup.map_commutator, Subgroup.map_subgroupOf_eq_of_le hX,
        Subgroup.map_subgroupOf_eq_of_le hX']
    rw [h1]
    exact Subgroup.comap_map_eq_self_of_injective (Y ⊔ A).subtype_injective _
  rw [key, Subgroup.map_commutator]

omit [Finite G] in
theorem img148_deltaZero_le_of {LB : Subgroup G → Subgroup G}
    {T : Subgroup (↥(Y ⊔ A) ⧸ ker148 A Y)}
    (h : ∀ Q ∈ collectionIn (scriptQZero A LB) Y, img148 A Y Q ≤ T) :
    img148 A Y (deltaZero A LB Y) ≤ T := by
  set T' : Subgroup G := (T.comap (QuotientGroup.mk' (ker148 A Y))).map (Y ⊔ A).subtype
    with hT'
  have hle : deltaZero A LB Y ≤ T' := by
    refine sSup_le fun Q hQ => ?_
    intro g hg
    have hgM : g ∈ Y ⊔ A := Subgroup.mem_sup_left (hQ.2 hg)
    exact ⟨⟨g, hgM⟩, h Q hQ (mem_img148_iff.mpr ⟨g, hgM, hg, rfl⟩), rfl⟩
  intro x hx
  obtain ⟨g, hgM, hgD, rfl⟩ := mem_img148_iff.mp hx
  obtain ⟨m, hm, hmg⟩ := hle hgD
  have : m = ⟨g, hgM⟩ := Subtype.ext hmg
  rw [← this]
  exact hm

theorem deltaZero_eq_sup_of_le_centralizer (hAY : A ≤ Subgroup.normalizer (Y : Set G))
    (hA3 : IsPGroup 3 A) (hAab : ∀ a ∈ A, ∀ a' ∈ A, a * a' = a' * a) {e : G} (he : e ∈ A)
    (he3 : e ^ 3 = 1) {LB : Subgroup G → Subgroup G}
    (hX : img148 A Y (deltaZero A LB Y) ≤ Subgroup.centralizer {alpha148 A Y e he}) :
    deltaZero A LB Y = pPrimeCoreOf 3 (deltaZero A LB Y) ⊔
      deltaZero A LB (Y ⊓ Subgroup.centralizer ({e} : Set G)) := by
  refine deltaZero_eq_sup_of_img148_le (K := deltaZero A LB (Y ⊓ Subgroup.centralizer {e})) ?_
    le_rfl inf_le_left
  refine img148_deltaZero_le_of fun Q hQ => ?_
  obtain ⟨hQ0, hQY⟩ := hQ
  have hQM : Q ≤ Y ⊔ A := hQY.trans le_sup_left
  obtain ⟨hQπ, hAQ, -⟩ := mem_scriptQ_iff.mp hQ0.1
  have hQ3 : ¬ 3 ∣ Nat.card Q := (isPiSubgroup_piCompl_iff Nat.prime_three Q).mp hQπ
  have hQα : img148 A Y Q ≤ Subgroup.centralizer {alpha148 A Y e he} :=
    (img148_mono (le_deltaZero hQ0 hQY)).trans hX
  set Qe := Q ⊓ Subgroup.centralizer ({e} : Set G) with hQe
  have hAe : A ≤ Subgroup.centralizer ({e} : Set G) := fun a ha =>
    Subgroup.mem_centralizer_singleton_iff.mpr (hAab e he a ha).symm
  have hAQe : A ≤ Subgroup.normalizer (Qe : Set G) :=
    Late.le_normalizer_inf hAQ (hAe.trans Subgroup.le_normalizer)
  have heqα : img148 A Y Q = img148 A Y Qe := by
    rw [← img148_inf_centralizer_alpha148 hAY hQM hAQ he he3, inf_eq_left.mpr hQα]
  set R := ⁅Qe, A⁆ with hR
  have hRQe : R ≤ Qe := by
    rw [Subgroup.commutator_le]
    intro x hx a ha
    rw [commutatorElement_def]
    have h1 : a * x⁻¹ * a⁻¹ ∈ Qe :=
      (Subgroup.mem_normalizer_iff.mp (hAQe ha) x⁻¹).mp (Qe.inv_mem hx)
    have e : x * a * x⁻¹ * a⁻¹ = x * (a * x⁻¹ * a⁻¹) := by group
    rw [e]
    exact Qe.mul_mem hx h1
  have hAR : A ≤ Subgroup.normalizer (R : Set G) := Subgroup.normalizer_commutator_ge_right Qe A
  have hRQ : R ∈ scriptQ A LB := mem_scriptQ_of_le hQ0.1 (hRQe.trans inf_le_left) hAR
  have hcop : Nat.Coprime 3 (Nat.card Qe) :=
    (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr fun h3 =>
      hQ3 (h3.trans (Subgroup.card_dvd_of_le inf_le_left))
  have hRR : R = ⁅R, A⁆ :=
    (CFSG.SignalizerFunctor.Helpers.coprime_normalized_commutator_idempotent 3 Nat.prime_three A
      Qe hA3 hAQe hcop).symm
  have hRY : R ≤ Y ⊓ Subgroup.centralizer ({e} : Set G) :=
    hRQe.trans (inf_le_inf_right _ hQY)
  have hRΔ : R ≤ deltaZero A LB (Y ⊓ Subgroup.centralizer ({e} : Set G)) :=
    le_deltaZero ⟨hRQ, hRR⟩ hRY
  have hQeM : Qe ≤ Y ⊔ A := inf_le_left.trans hQM
  calc img148 A Y Q = img148 A Y ⁅Q, A⁆ := by rw [← hQ0.2]
    _ = ⁅img148 A Y Q, img148 A Y A⁆ := img148_commutator_eq hQM le_sup_right
    _ = ⁅img148 A Y Qe, img148 A Y A⁆ := by rw [heqα]
    _ = img148 A Y R := (img148_commutator_eq hQeM le_sup_right).symm
    _ ≤ img148 A Y (deltaZero A LB (Y ⊓ Subgroup.centralizer {e})) := img148_mono hRΔ

omit [Finite G] in
theorem le_centralizer_of_mem_sectionCentralizer {J : Subgroup G} {a : G} (ha : a ∈ A)
    (hac : a ∈ Late.sectionCentralizer A J (pPrimeCoreOf 3 Y)) :
    img148 A Y J ≤ Subgroup.centralizer {alpha148 A Y a ha} := by
  intro x hx
  obtain ⟨j, hjM, hjJ, rfl⟩ := mem_img148_iff.mp hx
  rw [Subgroup.mem_centralizer_singleton_iff]
  have h1 := hac.2 j hjJ
  have haM : a ∈ Y ⊔ A := Subgroup.mem_sup_right ha
  have hmem : a * j * a⁻¹ * j⁻¹ ∈ Y ⊔ A :=
    (Y ⊔ A).mul_mem ((Y ⊔ A).mul_mem ((Y ⊔ A).mul_mem haM hjM) ((Y ⊔ A).inv_mem haM))
      ((Y ⊔ A).inv_mem hjM)
  have h2 := (mk'_ker148_eq_one_iff (A := A) (Y := Y) (g := ⟨_, hmem⟩)).mpr h1
  have h3 : alpha148 A Y a ha * QuotientGroup.mk' (ker148 A Y) ⟨j, hjM⟩ *
      (alpha148 A Y a ha)⁻¹ * (QuotientGroup.mk' (ker148 A Y) ⟨j, hjM⟩)⁻¹ = 1 := by
    rw [alpha148_eq_mk', ← map_inv, ← map_inv, ← map_mul, ← map_mul, ← map_mul]
    exact h2
  rw [mul_inv_eq_one, mul_inv_eq_iff_eq_mul] at h3
  exact h3.symm

theorem le_centralizer_of_theta {Yd J : Subgroup G} (hYdM : Yd ≤ Y ⊔ A)
    (heq : img148 A Y Yd = img148 A Y J)
    (hJθ : aschbacherSolvableCore 3 ↥(img148 A Y J) = ⊥) {a : G} (ha : a ∈ A)
    (hac : ∀ y ∈ Yd, a * y * a⁻¹ * y⁻¹ ∈ inSubgroup (aschbacherSolvableCore 3) Yd) :
    img148 A Y J ≤ Subgroup.centralizer {alpha148 A Y a ha} := by
  set Θ := inSubgroup (aschbacherSolvableCore 3) Yd with hΘ
  obtain ⟨hθs, -, hθ3, -⟩ :=
    solvable_prime_complement_core_characterization (H := ↥Yd) Nat.prime_three
  have hΘYd : Θ ≤ Yd := Subgroup.map_subtype_le _
  set T := img148 A Y Θ with hT
  have hTJ : T ≤ img148 A Y J := heq ▸ img148_mono hΘYd
  have hYdΘ : Yd ≤ Subgroup.normalizer (Θ : Set G) :=
    Subgroup.le_normalizer.trans
      (CFSG.LieType.BorelTits.normalizer_le_normalizer_map_of_characteristic _)
  have hTn : img148 A Y J ≤ Subgroup.normalizer (T : Set (↥(Y ⊔ A) ⧸ ker148 A Y)) :=
    heq ▸ img148_le_normalizer hYdΘ
  have hΘs : Group.IsSolvable Θ :=
    Group.isSolvable_of_surjective (Yd.subtype.subgroupMap_surjective _)
  have hTs : Group.IsSolvable T := by
    let f : ↥(Θ.subgroupOf (Y ⊔ A)) →* ↥Θ :=
      MonoidHom.codRestrict ((Y ⊔ A).subtype.comp (Θ.subgroupOf (Y ⊔ A)).subtype) Θ
        fun x => Subgroup.mem_subgroupOf.mp x.2
    have hf : Function.Injective f := fun x y hxy => by
      have h1 : ((f x : ↥Θ) : G) = ((f y : ↥Θ) : G) := congrArg Subtype.val hxy
      exact Subtype.ext (Subtype.ext h1)
    have : Group.IsSolvable ↥(Θ.subgroupOf (Y ⊔ A)) :=
      Group.isSolvable_of_isSolvable_injective (f := f) hf
    exact Group.isSolvable_of_surjective
      ((QuotientGroup.mk' (ker148 A Y)).subgroupMap_surjective (Θ.subgroupOf (Y ⊔ A)))
  have hT3 : ¬ 3 ∣ Nat.card T := by
    intro h3
    apply hθ3
    refine h3.trans ((Subgroup.card_map_dvd _ _).trans ?_)
    have hle : Θ.subgroupOf (Y ⊔ A) ≤ (⊤ : Subgroup ↥(Y ⊔ A)) := le_top
    rw [← Subgroup.card_map_of_injective (Y ⊔ A).subtype_injective,
      Subgroup.subgroupOf_map_subtype, inf_of_le_left (hΘYd.trans hYdM), hΘ, inSubgroup,
      Subgroup.card_map_of_injective Yd.subtype_injective]
  have hT1 : T = ⊥ := by
    have hTn' : (T.subgroupOf (img148 A Y J)).Normal :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer hTJ).mpr hTn
    have hTs' : Group.IsSolvable ↥(T.subgroupOf (img148 A Y J)) := by
      have e := Subgroup.subgroupOfEquivOfLe hTJ
      exact Group.isSolvable_of_surjective (f := e.symm.toMonoidHom) e.symm.surjective
    have hT3' : ¬ 3 ∣ Nat.card ↥(T.subgroupOf (img148 A Y J)) := by
      rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hTJ).toEquiv]
    have hle := (solvable_prime_complement_core_characterization
      (H := ↥(img148 A Y J)) Nat.prime_three).2.2.2.1 _ hTn' hTs' hT3'
    rw [hJθ, le_bot_iff] at hle
    rw [eq_bot_iff]
    intro t ht
    have : (⟨t, hTJ ht⟩ : ↥(img148 A Y J)) ∈ T.subgroupOf (img148 A Y J) := ht
    rw [hle] at this
    exact congrArg Subtype.val (Subgroup.mem_bot.mp this)
  intro x hx
  rw [← heq] at hx
  obtain ⟨y, hyM, hyYd, rfl⟩ := mem_img148_iff.mp hx
  rw [Subgroup.mem_centralizer_singleton_iff]
  have haM : a ∈ Y ⊔ A := Subgroup.mem_sup_right ha
  have hmem : a * y * a⁻¹ * y⁻¹ ∈ Y ⊔ A :=
    (Y ⊔ A).mul_mem ((Y ⊔ A).mul_mem ((Y ⊔ A).mul_mem haM hyM) ((Y ⊔ A).inv_mem haM))
      ((Y ⊔ A).inv_mem hyM)
  have h1 : QuotientGroup.mk' (ker148 A Y) (⟨_, hmem⟩ : ↥(Y ⊔ A)) ∈ T :=
    mem_img148_iff.mpr ⟨_, hmem, hac y hyYd, rfl⟩
  rw [hT1, Subgroup.mem_bot] at h1
  have h3 : alpha148 A Y a ha * QuotientGroup.mk' (ker148 A Y) ⟨y, hyM⟩ *
      (alpha148 A Y a ha)⁻¹ * (QuotientGroup.mk' (ker148 A Y) ⟨y, hyM⟩)⁻¹ = 1 := by
    rw [alpha148_eq_mk', ← map_inv, ← map_inv, ← map_mul, ← map_mul, ← map_mul]
    exact h1
  rw [mul_inv_eq_one, mul_inv_eq_iff_eq_mul] at h3
  exact h3.symm

end Quot

section Cases

variable {A Y : Subgroup G} [(ker148 A Y).Normal]

theorem deltaZero_eq_sup_normalizer_of_le_centralizer {c : G} {L : Subgroup G}
    (h : Sec14Std G A c L) (hY : Y ∈ scriptY A) {b : G} (hb : b ∈ A)
    (hXb : img148 A Y (deltaZero A (lB A) Y) ≤ Subgroup.centralizer {alpha148 A Y b hb}) :
    deltaZero A (lB A) Y = pPrimeCoreOf 3 (deltaZero A (lB A) Y) ⊔
      deltaZero A (lB A) (Y ⊓ Subgroup.normalizer (Subgroup.zpowers b : Set G)) := by
  have hA : Late.IsE27 A := h.isE27
  have hA3 : IsPGroup 3 A := IsPGroup.of_card (n := 3) (by rw [hA.2]; norm_num)
  have hAab : ∀ a ∈ A, ∀ a' ∈ A, a * a' = a' * a := fun a ha a' ha' =>
    h.toSec13Data.commute ha ha'
  have h1 := deltaZero_eq_sup_of_le_centralizer hY.2 hA3 hAab hb (hA.1.2 b hb) hXb
  have hCN : Y ⊓ Subgroup.centralizer ({b} : Set G) ≤
      Y ⊓ Subgroup.normalizer (Subgroup.zpowers b : Set G) := by
    refine inf_le_inf_left _ (le_trans (fun x hx => ?_) (Subgroup.centralizer_le_normalizer _))
    rw [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]
    exact hx
  refine le_antisymm (h1.le.trans (sup_le_sup_left (deltaZero_mono148 hCN) _))
    (sup_le (pPrimeCoreOf_le 3 _) (deltaZero_mono148 inf_le_left))

theorem case148Two_of_le_centralizer_point {c : G} {L : Subgroup G} (h : Sec14Std G A c L)
    (hY : Y ∈ scriptY A) {a : G} (ha : a ∈ A) (haΩ : Subgroup.zpowers a ∈ omegaA A)
    {La : Subgroup G} (hLa : La ∈ lA A a)
    (hLa2 : Nonempty (↥La ⧸ aschbacherSolvableCore 3 ↥La ≃* CFSG.Blueprint.NativeSporadic.J2))
    (hXa : img148 A Y (deltaZero A (lB A) Y) ≤ Subgroup.centralizer {alpha148 A Y a ha})
    (hX2 : Nonempty (↥(img148 A Y (deltaZero A (lB A) Y)) ≃* CFSG.Blueprint.NativeSporadic.J2)) :
    Case148Two A (lB A) Y := by
  refine ⟨a, haΩ, deltaZero_eq_sup_normalizer_of_le_centralizer h hY ha hXa, La, hLa, ?_⟩
  obtain ⟨φ⟩ := hX2
  obtain ⟨ψ⟩ := hLa2
  exact Or.inl ⟨φ.trans ψ.symm⟩

theorem case148Two_of_img148_eq_point {c : G} {L : Subgroup G} (h : Sec14Std G A c L)
    (hY : Y ∈ scriptY A) {a : G} (ha : a ∈ A) (haΩ : Subgroup.zpowers a ∈ omegaA A)
    {La : Subgroup G} (hLa : La ∈ lA A a)
    (hLa2 : Nonempty (↥La ⧸ aschbacherSolvableCore 3 ↥La ≃* CFSG.Blueprint.NativeSporadic.J2))
    {J : Subgroup G} (hXJ : img148 A Y (deltaZero A (lB A) Y) = img148 A Y J)
    (hJa : img148 A Y J ≤ Subgroup.centralizer {alpha148 A Y a ha})
    (hJ2 : Nonempty (↥(img148 A Y J) ≃* CFSG.Blueprint.NativeSporadic.J2)) :
    Case148Two A (lB A) Y :=
  case148Two_of_le_centralizer_point h hY ha haΩ hLa hLa2 (hXJ ▸ hJa) (hXJ ▸ hJ2)

theorem case148Three_of_le_centralizer {c₀ : G} {L₀ : Subgroup G} (h : Sec14Std G A c₀ L₀)
    (hY : Y ∈ scriptY A) {c : G} (hcΩ : Subgroup.zpowers c ∈ omegaA A) {L : Subgroup G}
    (hL : L ∈ lA A c)
    (hL2 : Nonempty (↥L ⧸ aschbacherSolvableCore 3 ↥L ≃* CFSG.Blueprint.NativeSporadic.J2))
    {d : G} (hd : d ∈ A) (hd1 : d ≠ 1) (hd3 : IsThreeCentralIn L d)
    (hXd : img148 A Y (deltaZero A (lB A) Y) ≤ Subgroup.centralizer {alpha148 A Y d hd})
    (htype : Sec4.IsTripleCover ↥(img148 A Y (deltaZero A (lB A) Y))
        CFSG.Blueprint.NativeSporadic.ON ∨
      IsCentralProductA6Covers ↥(img148 A Y (deltaZero A (lB A) Y)) ∨
      IsA6CoverTimesA5 ↥(img148 A Y (deltaZero A (lB A) Y)) ∨
      Nonempty (↥(img148 A Y (deltaZero A (lB A) Y)) ≃*
        alternatingGroup (Fin 5) × alternatingGroup (Fin 5)) ∨
      Nonempty (↥(img148 A Y (deltaZero A (lB A) Y)) ≃* alternatingGroup (Fin 7)) ∨
      (∃ _ : Fact (Nat.Prime 7), Nonempty (↥(img148 A Y (deltaZero A (lB A) Y)) ≃*
        CFSG.Assembly.RankThreeEven.projSL 3 (GaloisField 7 1)))) :
    Case148Three A (lB A) Y := by
  have hA : Late.IsE27 A := h.isE27
  have hA3 : IsPGroup 3 A := IsPGroup.of_card (n := 3) (by rw [hA.2]; norm_num)
  have hAab : ∀ a ∈ A, ∀ a' ∈ A, a * a' = a' * a := fun a ha a' ha' =>
    h.toSec13Data.commute ha ha'
  exact ⟨c, d, L, hcΩ, hL, hL2, hd, hd1, hd3,
    deltaZero_eq_sup_of_le_centralizer hY.2 hA3 hAab hd (hA.1.2 d hd) hXd, htype⟩


theorem case148Two_of_le_centralizer_b {c : G} {L : Subgroup G} (h : Sec14Std G A c L)
    (hY : Y ∈ scriptY A) {B : Subgroup G} (hB : IsHyperplane A B) {b d : G} {Lb : Subgroup G}
    (hc : IsLBConfig A B b d Lb)
    (hXb : ∀ hb : b ∈ A,
      img148 A Y (deltaZero A (lB A) Y) ≤ Subgroup.centralizer {alpha148 A Y b hb})
    (htype : Sec4.IsTripleCover ↥(img148 A Y (deltaZero A (lB A) Y)) (alternatingGroup (Fin 6)) ∨
      Nonempty (↥(img148 A Y (deltaZero A (lB A) Y)) ≃* alternatingGroup (Fin 5)) ∨
      Nonempty (↥(img148 A Y (deltaZero A (lB A) Y)) ≃* CFSG.Blueprint.NativeSporadic.J2)) :
    Case148Two A (lB A) Y := by
  have hA : Late.IsE27 A := h.isE27
  obtain ⟨hbB, -, -, -, -⟩ := lbConfig_points hB hA.2 hc
  have hb : b ∈ A := hB.1 hbB
  have hJ2 := Item148HJ.j2_of_isLBConfig hc
  have hLb : Lb ∈ lA A b := hc.2.2.1 ▸ Set.mem_singleton Lb
  refine ⟨b, hc.2.1, deltaZero_eq_sup_normalizer_of_le_centralizer h hY hb (hXb hb), Lb, hLb, ?_⟩
  rcases htype with hA6 | hA5 | hXJ2
  · exact Or.inr (Or.inr (Or.inr ⟨hJ2, Or.inl hA6⟩))
  · exact Or.inr (Or.inr (Or.inr ⟨hJ2, Or.inr hA5⟩))
  · obtain ⟨φ⟩ := hXJ2
    obtain ⟨ψ⟩ := hJ2
    exact Or.inl ⟨φ.trans ψ.symm⟩

theorem case148Two_of_img148_eq_b {c : G} {L : Subgroup G} (h : Sec14Std G A c L)
    (hY : Y ∈ scriptY A) {B : Subgroup G} (hB : IsHyperplane A B) {b d : G} {Lb : Subgroup G}
    (hc : IsLBConfig A B b d Lb) {J : Subgroup G}
    (hXJ : img148 A Y (deltaZero A (lB A) Y) = img148 A Y J)
    (hJb : ∀ hb : b ∈ A, img148 A Y J ≤ Subgroup.centralizer {alpha148 A Y b hb})
    (htype : Sec4.IsTripleCover ↥(img148 A Y J) (alternatingGroup (Fin 6)) ∨
      Nonempty (↥(img148 A Y J) ≃* alternatingGroup (Fin 5)) ∨
      Nonempty (↥(img148 A Y J) ≃* CFSG.Blueprint.NativeSporadic.J2)) :
    Case148Two A (lB A) Y :=
  case148Two_of_le_centralizer_b h hY hB hc (fun hb => hXJ ▸ hJb hb) (hXJ ▸ htype)

theorem case148Three_of_img148_eq_d {c : G} {L : Subgroup G} (h : Sec14Std G A c L)
    (hY : Y ∈ scriptY A) {B : Subgroup G} (hB : IsHyperplane A B) {b d : G} {Lb : Subgroup G}
    (hc : IsLBConfig A B b d Lb) {J : Subgroup G}
    (hXJ : img148 A Y (deltaZero A (lB A) Y) = img148 A Y J)
    (hJd : ∀ hd : d ∈ A, img148 A Y J ≤ Subgroup.centralizer {alpha148 A Y d hd})
    (hON : Sec4.IsTripleCover ↥(img148 A Y J) CFSG.Blueprint.NativeSporadic.ON) :
    Case148Three A (lB A) Y := by
  have hA : Late.IsE27 A := h.isE27
  obtain ⟨-, hdB, -, hd1, -⟩ := lbConfig_points hB hA.2 hc
  have hd : d ∈ A := hB.1 hdB
  have hLb : Lb ∈ lA A b := hc.2.2.1 ▸ Set.mem_singleton Lb
  exact case148Three_of_le_centralizer h hY hc.2.1 hLb (Item148HJ.j2_of_isLBConfig hc) hd hd1
    hc.2.2.2.2 (hXJ ▸ hJd hd) (Or.inl (hXJ ▸ hON))

end Cases

end HJRes2

end CFSG.RankThree.PartTwo.Sec14
