module

public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps136Defs
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs12d
public import CFSG.LocalAnalysis.WeakClosure81.SixFourteenOmega4UniqueAbstract
import CFSG.Quasithin.Background.B5Models
import CFSG.Quasithin.Vol2.Ch4Sec2Thm4213J4KXQS
import CFSG.Quasithin.Background.B1More13A
import CFSG.Quasithin.Background.B1More13Defs
import CFSG.Quasithin.Background.B1MoreEleven
import CFSG.Quasithin.Background.B5Basic
import CFSG.Quasithin.Background.B5CompA
import CFSG.Quasithin.Background.B5CompB
import CFSG.Quasithin.Vol2.Ch4Sec2Thm4213J4Defs

public section

namespace CFSG.LocalAnalysis.WeakClosure81.GF2Reps136

open CFSG.Quasithin CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.Blueprint (LieModel)
open scoped commutatorElement Pointwise Matrix

variable {W : Type} [CommGroup W] [Finite W]

abbrev Sect (U Z : Subgroup W) : Type := CFSG.Quasithin.Sec U Z

@[expose] def resAut (U : Subgroup W) (g : MulAut W) (hU : ∀ u ∈ U, g u ∈ U) : ↥U ≃* ↥U where
  toFun u := ⟨g u, hU u u.2⟩
  invFun u := ⟨(g⁻¹ : MulAut W) u, inv_mem_of_forall_mem g hU u u.2⟩
  left_inv u := Subtype.ext (by simp)
  right_inv u := Subtype.ext (by simp)
  map_mul' u v := Subtype.ext (map_mul g (u : W) (v : W))

@[expose] def secAut (U Z : Subgroup W) (g : MulAut W) (hU : ∀ u ∈ U, g u ∈ U)
    (hZ : ∀ z ∈ Z, g z ∈ Z) : MulAut (Sect U Z) :=
  QuotientGroup.congr (Z.subgroupOf U) (Z.subgroupOf U) (resAut U g hU) (by
    apply le_antisymm
    · rintro _ ⟨z, hz, rfl⟩
      exact hZ _ hz
    · intro z hz
      refine ⟨⟨(g⁻¹ : MulAut W) z, inv_mem_of_forall_mem g hU z z.2⟩, ?_, ?_⟩
      · exact inv_mem_of_forall_mem g hZ z hz
      · exact Subtype.ext (by simp [resAut]))

theorem secAut_mk (U Z : Subgroup W) (g : MulAut W) (hU : ∀ u ∈ U, g u ∈ U)
    (hZ : ∀ z ∈ Z, g z ∈ Z) (u : ↥U) :
    secAut U Z g hU hZ (QuotientGroup.mk u) = QuotientGroup.mk ⟨g u, hU u u.2⟩ := rfl

abbrev secSub (U Z : Subgroup W) (A : Subgroup (MulAut W)) : Subgroup (MulAut (Sect U Z)) :=
  CFSG.Quasithin.autSec A U Z

@[expose] def StabPair (A : Subgroup (MulAut W)) (U Z : Subgroup W) : Prop :=
  ∀ a ∈ A, (∀ u ∈ U, a u ∈ U) ∧ ∀ z ∈ Z, a z ∈ Z

@[expose] def FaithOn (A : Subgroup (MulAut W)) (U Z : Subgroup W) : Prop :=
  ∀ a ∈ A, (∀ u ∈ U, a u * u⁻¹ ∈ Z) → a = 1

private theorem w1369_mem_stabSub_of_forall_mem {U : Subgroup W} {g : MulAut W}
    (h : ∀ u ∈ U, g u ∈ U) : g ∈ stabSub U :=
  mem_stabSub_of_invariant h (inv_mem_of_forall_mem g h)

private theorem w1369_stabPair_le_stabSub_left {A : Subgroup (MulAut W)} {U Z : Subgroup W}
    (hA : StabPair A U Z) : A ≤ stabSub U :=
  fun a ha => w1369_mem_stabSub_of_forall_mem (hA a ha).1

private theorem w1369_stabPair_le_stabSub_right {A : Subgroup (MulAut W)} {U Z : Subgroup W}
    (hA : StabPair A U Z) : A ≤ stabSub Z :=
  fun a ha => w1369_mem_stabSub_of_forall_mem (hA a ha).2

private theorem w1369_secHom_eq_secAut {A : Subgroup (MulAut W)} {U Z : Subgroup W}
    (hAU : A ≤ stabSub U) (hAZ : A ≤ stabSub Z) (a : ↥A)
    (hU : ∀ u ∈ U, (a : MulAut W) u ∈ U) (hZ : ∀ z ∈ Z, (a : MulAut W) z ∈ Z) :
    B5.secHom A hAU hAZ a = secAut U Z a hU hZ := by
  ext x
  induction x using QuotientGroup.induction_on with
  | H u =>
      rw [B5.secHom_mk, secAut_mk]

private theorem w1369_secAut_mem {A : Subgroup (MulAut W)} {U Z : Subgroup W}
    (hA : StabPair A U Z) {a : MulAut W} (ha : a ∈ A) :
    secAut U Z a (hA a ha).1 (hA a ha).2 ∈ secSub U Z A := by
  have hAU : A ≤ stabSub U := w1369_stabPair_le_stabSub_left hA
  have hAZ : A ≤ stabSub Z := w1369_stabPair_le_stabSub_right hA
  change secAut U Z a (hA a ha).1 (hA a ha).2 ∈ autSec A U Z
  rw [← B5.range_secHom A hAU hAZ]
  exact ⟨⟨a, ha⟩, w1369_secHom_eq_secAut hAU hAZ ⟨a, ha⟩ (hA a ha).1 (hA a ha).2⟩

private def w1369_secIm (U Z : Subgroup W) (M : Subgroup W) : Subgroup (Sect U Z) :=
  (M.subgroupOf U).map (QuotientGroup.mk' (Z.subgroupOf U))

private def w1369_secPre (U Z : Subgroup W) (N : Subgroup (Sect U Z)) : Subgroup W :=
  (N.comap (QuotientGroup.mk' (Z.subgroupOf U))).map U.subtype

private theorem w1369_secIm_sup {U Z : Subgroup W} {A B : Subgroup W} (hA : A ≤ U)
    (hB : B ≤ U) : w1369_secIm U Z (A ⊔ B) = w1369_secIm U Z A ⊔ w1369_secIm U Z B := by
  unfold w1369_secIm
  rw [Subgroup.subgroupOf_sup hA hB, Subgroup.map_sup]

private theorem w1369_secIm_C (U Z : Subgroup W) : w1369_secIm U Z Z = ⊥ := by
  unfold w1369_secIm
  rw [Subgroup.map_eq_bot_iff]
  exact (QuotientGroup.ker_mk' (Z.subgroupOf U)).ge

private theorem w1369_secIm_top (U Z : Subgroup W) : w1369_secIm U Z U = ⊤ := by
  unfold w1369_secIm
  rw [Subgroup.subgroupOf_self,
    Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective _)]

private theorem w1369_secPre_bot {U Z : Subgroup W} (hZU : Z ≤ U) :
    w1369_secPre U Z ⊥ = Z := by
  unfold w1369_secPre
  rw [MonoidHom.comap_bot, QuotientGroup.ker_mk']
  exact Subgroup.map_subgroupOf_eq_of_le hZU

private theorem w1369_secPre_im {U Z M : Subgroup W} (hZ : Z ≤ M) (hM : M ≤ U) :
    w1369_secPre U Z (w1369_secIm U Z M) = M := by
  unfold w1369_secPre w1369_secIm
  rw [Subgroup.comap_map_eq, QuotientGroup.ker_mk']
  have hsup : M.subgroupOf U ⊔ Z.subgroupOf U = M.subgroupOf U :=
    sup_eq_left.mpr (Subgroup.comap_mono hZ)
  rw [hsup]
  exact Subgroup.map_subgroupOf_eq_of_le hM

private theorem w1369_secIm_pre (U Z : Subgroup W) (N : Subgroup (Sect U Z)) :
    w1369_secIm U Z (w1369_secPre U Z N) = N := by
  unfold w1369_secIm w1369_secPre
  have h1 : ((N.comap (QuotientGroup.mk' (Z.subgroupOf U))).map U.subtype).subgroupOf U =
      N.comap (QuotientGroup.mk' (Z.subgroupOf U)) := by
    rw [← Subgroup.comap_subtype]
    exact Subgroup.comap_map_eq_self_of_injective U.subtype_injective _
  rw [h1]
  exact Subgroup.map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective _) N

private theorem w1369_secPre_le {U Z : Subgroup W} (hZU : Z ≤ U)
    (N : Subgroup (Sect U Z)) : Z ≤ w1369_secPre U Z N := by
  intro c hc
  unfold w1369_secPre
  rw [Subgroup.mem_map]
  refine ⟨⟨c, hZU hc⟩, ?_, rfl⟩
  rw [Subgroup.mem_comap]
  have h1 : (QuotientGroup.mk' (Z.subgroupOf U)) ⟨c, hZU hc⟩ = 1 := by
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    exact Subgroup.mem_subgroupOf.mpr hc
  rw [h1]
  exact N.one_mem

private theorem w1369_secIm_card {U Z M : Subgroup W} (hZM : Z ≤ M) (hMU : M ≤ U) :
    Nat.card (w1369_secIm U Z M) = Nat.card (Sect M Z) := by
  let φ : ↥M →* Sect U Z := (QuotientGroup.mk' (Z.subgroupOf U)).comp (Subgroup.inclusion hMU)
  have hker : φ.ker = Z.subgroupOf M := by
    ext m
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    show (QuotientGroup.mk' (Z.subgroupOf U)) (Subgroup.inclusion hMU m) = 1 ↔ (m : W) ∈ Z
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
    rfl
  have hrange : φ.range = w1369_secIm U Z M := by
    ext x
    rw [MonoidHom.mem_range]
    unfold w1369_secIm
    rw [Subgroup.mem_map]
    constructor
    · rintro ⟨m, rfl⟩
      exact ⟨Subgroup.inclusion hMU m, Subgroup.mem_subgroupOf.mpr m.2, rfl⟩
    · rintro ⟨u, hu, rfl⟩
      refine ⟨⟨(u : W), Subgroup.mem_subgroupOf.mp hu⟩, ?_⟩
      rfl
  have hmem : ∀ m : ↥M, φ m ∈ w1369_secIm U Z M := fun m => by
    rw [← hrange]
    exact MonoidHom.mem_range.mpr ⟨m, rfl⟩
  let φ' : ↥M →* ↥(w1369_secIm U Z M) := φ.codRestrict (w1369_secIm U Z M) hmem
  have hker' : φ'.ker = Z.subgroupOf M := by
    rw [← hker]
    ext m
    rw [MonoidHom.mem_ker, MonoidHom.mem_ker]
    exact Subtype.ext_iff
  have hsurj : Function.Surjective φ' := fun y => by
    have hy : y.1 ∈ φ.range := by rw [hrange]; exact y.2
    obtain ⟨m, hm⟩ := MonoidHom.mem_range.mp hy
    exact ⟨m, Subtype.ext hm⟩
  have e : Sect M Z ≃* ↥(w1369_secIm U Z M) :=
    (QuotientGroup.quotientMulEquivOfEq hker').symm.trans
      (QuotientGroup.quotientKerEquivOfSurjective φ' hsurj)
  exact (Nat.card_congr e.toEquiv).symm

private theorem w1369_secStable_im {U Z : Subgroup W} {A : Subgroup (MulAut W)}
    (hA : StabPair A U Z) {M : Subgroup W} (hAM : StableUnder A M) :
    StableUnder (secSub U Z A) (w1369_secIm U Z M) := by
  intro γ hγ x hx
  rw [w1369_secIm, Subgroup.mem_map] at hx ⊢
  obtain ⟨m, hm, rfl⟩ := hx
  obtain ⟨g, hg, hgq⟩ := (CFSG.Quasithin.mem_autQuot).mp hγ
  obtain ⟨h, hh, heq⟩ := mem_autSub.mp hg
  rw [← hgq, QuotientGroup.mk'_apply, quotHom_mk, heq.symm]
  refine Subgroup.mem_map.mpr ⟨resHom U h m, ?_, rfl⟩
  rw [Subgroup.mem_subgroupOf, resHom_apply]
  exact hAM h hh (m : W) (Subgroup.mem_subgroupOf.mp hm)

private theorem w1369_secStable_pre {U Z : Subgroup W} {A : Subgroup (MulAut W)}
    (hA : StabPair A U Z) {N : Subgroup (Sect U Z)} (hN : StableUnder (secSub U Z A) N) :
    StableUnder A (w1369_secPre U Z N) := by
  intro a ha x hx
  rw [w1369_secPre, Subgroup.mem_map] at hx ⊢
  obtain ⟨u, hu, rfl⟩ := hx
  have huN : QuotientGroup.mk u ∈ N := Subgroup.mem_comap.mp hu
  have hmem := hN (secAut U Z a (hA a ha).1 (hA a ha).2) (w1369_secAut_mem hA ha)
    (QuotientGroup.mk u) huN
  rw [secAut_mk] at hmem
  exact ⟨⟨a (u : W), (hA a ha).1 u u.2⟩, hmem, rfl⟩

private theorem w1369_bot_lt_top_sec {U Z : Subgroup W} (hZU : Z < U) :
    (⊥ : Subgroup (Sect U Z)) < ⊤ := by
  rw [bot_lt_iff_ne_bot]
  intro hbot
  obtain ⟨u, huU, huZ⟩ := IsConcreteLE.exists_of_lt hZU
  have h1 : (QuotientGroup.mk ⟨u, huU⟩ : Sect U Z) ∈ (⊥ : Subgroup (Sect U Z)) := by
    rw [← hbot]; exact Subgroup.mem_top _
  rw [Subgroup.mem_bot, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf] at h1
  exact huZ h1

private theorem w1369_commutator_subgroupOf {X A B : Subgroup (MulAut W)} (hA : A ≤ X)
    (hB : B ≤ X) : ⁅A.subgroupOf X, B.subgroupOf X⁆ = (⁅A, B⁆).subgroupOf X := by
  apply Subgroup.map_injective (f := X.subtype) X.subtype_injective
  rw [Subgroup.map_commutator, Subgroup.subgroupOf_map_subtype, Subgroup.subgroupOf_map_subtype,
    Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hA, inf_eq_left.mpr hB,
    inf_eq_left.mpr (Subgroup.commutator_le_of_le hA hB)]

private theorem w1369_secSub_eq_map {A B : Subgroup (MulAut W)} {U Z : Subgroup W}
    (hAU : A ≤ stabSub U) (hAZ : A ≤ stabSub Z) (hBA : B ≤ A) :
    secSub U Z B = (B.subgroupOf A).map (B5.secHom A hAU hAZ) :=
  (B5.map_secHom_eq_autSec A hAU hAZ hBA).symm

theorem sect_exp_two (hw2 : ∀ w : W, w ^ 2 = 1) (U Z : Subgroup W) :
    ∀ x : Sect U Z, x ^ 2 = 1 := by
  intro x
  induction x using QuotientGroup.induction_on with
  | H u =>
      change (QuotientGroup.mk' (Z.subgroupOf U) u) ^ 2 = 1
      rw [← map_pow (QuotientGroup.mk' (Z.subgroupOf U)) u 2]
      have h1 : u ^ 2 = 1 := Subtype.ext (by simpa using hw2 (u : W))
      rw [h1, map_one]

theorem secSub_irr {A : Subgroup (MulAut W)} {U Z : Subgroup W} (hA : StabPair A U Z)
    (hZU : Z < U) : IsIrrOn (secSub U Z A) ⊤ ⊥ ↔ IsIrrOn A U Z := by
  have hU : StableUnder A U := fun a ha => (hA a ha).1
  have hZ : StableUnder A Z := fun a ha => (hA a ha).2
  constructor
  · intro h
    refine ⟨hZU, hU, hZ, fun J hJ hZJ hJU => ?_⟩
    have hJ' : StableUnder (secSub U Z A) (w1369_secIm U Z J) := w1369_secStable_im hA hJ
    rcases h.2.2.2 (w1369_secIm U Z J) hJ' bot_le le_top with hbot | htop
    · left
      have h1 := congrArg (w1369_secPre U Z) hbot
      rw [w1369_secPre_im hZJ hJU, w1369_secPre_bot hZU.le] at h1
      exact h1
    · right
      have h1 := congrArg (w1369_secPre U Z) htop
      rw [w1369_secPre_im hZJ hJU] at h1
      have h2 : w1369_secPre U Z ⊤ = U := by
        rw [← w1369_secIm_top U Z, w1369_secPre_im hZU.le le_rfl]
      rw [h2] at h1
      exact h1
  · intro h
    refine ⟨w1369_bot_lt_top_sec hZU, fun _ _ _ _ => Subgroup.mem_top _,
      fun _ _ _ hx => ?_, fun J' hJ' _ _ => ?_⟩
    · rw [Subgroup.mem_bot.mp hx, map_one]
      exact Subgroup.mem_bot.mpr rfl
    · have hJ : StableUnder A (w1369_secPre U Z J') := w1369_secStable_pre hA hJ'
      have hZJ : Z ≤ w1369_secPre U Z J' := w1369_secPre_le hZU.le J'
      have hJU : w1369_secPre U Z J' ≤ U := Subgroup.map_subtype_le _
      rcases h.2.2.2 _ hJ hZJ hJU with hJZ | hJU'
      · left
        rw [← w1369_secIm_pre U Z J', hJZ, w1369_secIm_C]
      · right
        rw [← w1369_secIm_pre U Z J', hJU', w1369_secIm_top]

private def w1369_commHomSub {U : Subgroup W} (t : MulAut W) (hU : ∀ u ∈ U, t u ∈ U) :
    ↥U →* ↥U :=
  ((commHom t).comp U.subtype).codRestrict U fun u => U.mul_mem (hU u u.2) (U.inv_mem u.2)

private theorem w1369_commHom_secAut_apply {U Z : Subgroup W} {t : MulAut W}
    (hU : ∀ u ∈ U, t u ∈ U) (hZ : ∀ z ∈ Z, t z ∈ Z) (u : ↥U) :
    commHom (secAut U Z t hU hZ) (QuotientGroup.mk u) =
      QuotientGroup.mk (w1369_commHomSub t hU u) := by
  rw [commHom_apply, secAut_mk]
  change QuotientGroup.mk' (Z.subgroupOf U) ⟨t u, hU u u.2⟩ *
      (QuotientGroup.mk' (Z.subgroupOf U) u)⁻¹ =
    QuotientGroup.mk' (Z.subgroupOf U) (w1369_commHomSub t hU u)
  rw [← map_inv, ← map_mul]
  congr 1

private theorem w1369_commHom_secAut_range {U Z : Subgroup W} {t : MulAut W}
    (hU : ∀ u ∈ U, t u ∈ U) (hZ : ∀ z ∈ Z, t z ∈ Z) :
    (commHom (secAut U Z t hU hZ)).range =
      ((U.map (commHom t)).subgroupOf U).map (QuotientGroup.mk' (Z.subgroupOf U)) := by
  ext y
  constructor
  · intro hy
    obtain ⟨x, rfl⟩ := MonoidHom.mem_range.mp hy
    obtain ⟨u, rfl⟩ := QuotientGroup.mk_surjective x
    refine Subgroup.mem_map.mpr ⟨w1369_commHomSub t hU u, ?_, ?_⟩
    · exact Subgroup.mem_subgroupOf.mpr ⟨u, u.2, rfl⟩
    · exact (w1369_commHom_secAut_apply hU hZ u).symm
  · rintro ⟨w, hw, rfl⟩
    rw [MonoidHom.mem_range]
    have hw' : (w : W) ∈ U.map (commHom t) := Subgroup.mem_subgroupOf.mp hw
    obtain ⟨u, hu, huw⟩ := Subgroup.mem_map.mp hw'
    refine ⟨QuotientGroup.mk ⟨u, hu⟩, ?_⟩
    rw [w1369_commHom_secAut_apply hU hZ ⟨u, hu⟩]
    congr 1
    exact Subtype.ext huw

theorem rk_secAut_comm {U Z : Subgroup W} (hZU : Z ≤ U) {t : MulAut W}
    (hU : ∀ u ∈ U, t u ∈ U) (hZ : ∀ z ∈ Z, t z ∈ Z) :
    rk ↥(commSub ⊤ (Subgroup.zpowers (secAut U Z t hU hZ))) =
      E3.mQuot (commSub U (Subgroup.zpowers t) ⊔ Z) Z := by
  let M := commSub U (Subgroup.zpowers t)
  have hMU : M ≤ U := commSub_le_of_invariant fun x hx u hu =>
    (Subgroup.zpowers_le.2 (w1369_mem_stabSub_of_forall_mem hU) hx u).2 hu
  have hM : M = U.map (commHom t) :=
    commSub_zpowers_eq_map fun x hx u hu =>
      (Subgroup.zpowers_le.2 (w1369_mem_stabSub_of_forall_mem hU) hx u).2 hu
  have hcomm : commSub ⊤ (Subgroup.zpowers (secAut U Z t hU hZ)) = w1369_secIm U Z M := by
    rw [commSub_zpowers_eq_map (g := secAut U Z t hU hZ) (W := ⊤) (fun _ _ _ _ => trivial),
      ← MonoidHom.range_eq_map, w1369_commHom_secAut_range hU hZ, hM]
    rfl
  have hMsup : w1369_secIm U Z M = w1369_secIm U Z (M ⊔ Z) := by
    rw [w1369_secIm_sup hMU hZU, w1369_secIm_C, sup_bot_eq]
  calc rk ↥(commSub ⊤ (Subgroup.zpowers (secAut U Z t hU hZ)))
      = rk ↥(w1369_secIm U Z M) := by rw [hcomm]
    _ = padicValNat 2 (Nat.card (w1369_secIm U Z M)) := rfl
    _ = padicValNat 2 (Nat.card (w1369_secIm U Z (M ⊔ Z))) := by rw [hMsup]
    _ = padicValNat 2 (Nat.card (Sect (M ⊔ Z) Z)) := by
          rw [w1369_secIm_card le_sup_right (sup_le hMU hZU)]
    _ = padicValNat 2 (Z.relIndex (M ⊔ Z)) := rfl
    _ = E3.mQuot (M ⊔ Z) Z := rfl

theorem secSub_map_conj {A : Subgroup (MulAut W)} {U Z : Subgroup W} (hA : StabPair A U Z)
    {t : MulAut W} (hU : ∀ u ∈ U, t u ∈ U) (hZ : ∀ z ∈ Z, t z ∈ Z) :
    (secSub U Z A).map (MulAut.conj (secAut U Z t hU hZ)).toMonoidHom =
      secSub U Z (A.map (MulAut.conj t).toMonoidHom) := by
  change (autSec A U Z).map (MulAut.conj (secAut U Z t hU hZ)).toMonoidHom =
    autSec (A.map (MulAut.conj t).toMonoidHom) U Z
  have hAU : A ≤ stabSub U := w1369_stabPair_le_stabSub_left hA
  have hAZ : A ≤ stabSub Z := w1369_stabPair_le_stabSub_right hA
  have htU : t ∈ stabSub U := w1369_mem_stabSub_of_forall_mem hU
  have htZ : t ∈ stabSub Z := w1369_mem_stabSub_of_forall_mem hZ
  have hXU : A ⊔ Subgroup.zpowers t ≤ stabSub U := sup_le hAU (Subgroup.zpowers_le.2 htU)
  have hXZ : A ⊔ Subgroup.zpowers t ≤ stabSub Z := sup_le hAZ (Subgroup.zpowers_le.2 htZ)
  have hAtX : A ≤ A ⊔ Subgroup.zpowers t := le_sup_left
  have htX : t ∈ A ⊔ Subgroup.zpowers t := Subgroup.mem_sup_right (Subgroup.mem_zpowers t)
  have hAt'X : A.map (MulAut.conj t).toMonoidHom ≤ A ⊔ Subgroup.zpowers t := by
    rintro _ ⟨a, ha, rfl⟩
    exact (A ⊔ Subgroup.zpowers t).mul_mem
      ((A ⊔ Subgroup.zpowers t).mul_mem htX (hAtX ha))
      ((A ⊔ Subgroup.zpowers t).inv_mem htX)
  have h1 := B5.map_secHom_eq_autSec (A ⊔ Subgroup.zpowers t) hXU hXZ hAtX
  have h2 := B5.map_secHom_eq_autSec (A ⊔ Subgroup.zpowers t) hXU hXZ hAt'X
  rw [← h1, ← h2, Subgroup.map_map]
  have hconj : ((MulAut.conj (secAut U Z t hU hZ)).toMonoidHom.comp
        (B5.secHom (A ⊔ Subgroup.zpowers t) hXU hXZ)) =
      ((B5.secHom (A ⊔ Subgroup.zpowers t) hXU hXZ).comp
        (MulAut.conj (⟨t, htX⟩ : ↥(A ⊔ Subgroup.zpowers t))).toMonoidHom) := by
    apply MonoidHom.ext
    intro x
    show MulAut.conj (secAut U Z t hU hZ) (B5.secHom (A ⊔ Subgroup.zpowers t) hXU hXZ x) =
      B5.secHom (A ⊔ Subgroup.zpowers t) hXU hXZ
        (MulAut.conj (⟨t, htX⟩ : ↥(A ⊔ Subgroup.zpowers t)) x)
    rw [MulAut.conj_apply, ← w1369_secHom_eq_secAut hXU hXZ ⟨t, htX⟩ hU hZ,
      ← map_mul, ← map_inv, ← map_mul]
    congr 1
  rw [hconj, ← Subgroup.map_map]
  congr 1
  change MulAut.conj (⟨t, htX⟩ : ↥(A ⊔ Subgroup.zpowers t)) •
      (A.subgroupOf (A ⊔ Subgroup.zpowers t)) =
    (MulAut.conj t • A).subgroupOf (A ⊔ Subgroup.zpowers t)
  exact Subgroup.conj_smul_subgroupOf hAtX ⟨t, htX⟩

theorem secSub_commutator {A B : Subgroup (MulAut W)} {U Z : Subgroup W} (hA : StabPair A U Z)
    (hB : StabPair B U Z) : ⁅secSub U Z A, secSub U Z B⁆ = secSub U Z ⁅A, B⁆ := by
  have hAU : A ≤ stabSub U := w1369_stabPair_le_stabSub_left hA
  have hAZ : A ≤ stabSub Z := w1369_stabPair_le_stabSub_right hA
  have hBU : B ≤ stabSub U := w1369_stabPair_le_stabSub_left hB
  have hBZ : B ≤ stabSub Z := w1369_stabPair_le_stabSub_right hB
  have hABU : A ⊔ B ≤ stabSub U := sup_le hAU hBU
  have hABZ : A ⊔ B ≤ stabSub Z := sup_le hAZ hBZ
  have hABX : ⁅A, B⁆ ≤ A ⊔ B := Subgroup.commutator_le_of_le le_sup_left le_sup_right
  rw [w1369_secSub_eq_map hABU hABZ le_sup_left,
    w1369_secSub_eq_map hABU hABZ le_sup_right,
    w1369_secSub_eq_map hABU hABZ hABX,
    ← Subgroup.map_commutator, w1369_commutator_subgroupOf le_sup_left le_sup_right]

theorem secSub_zpowers {U Z : Subgroup W} {t : MulAut W} (hU : ∀ u ∈ U, t u ∈ U)
    (hZ : ∀ z ∈ Z, t z ∈ Z) :
    secSub U Z (Subgroup.zpowers t) = Subgroup.zpowers (secAut U Z t hU hZ) := by
  change autSec (Subgroup.zpowers t) U Z = Subgroup.zpowers (secAut U Z t hU hZ)
  have htU : t ∈ stabSub U := w1369_mem_stabSub_of_forall_mem hU
  have htZ : t ∈ stabSub Z := w1369_mem_stabSub_of_forall_mem hZ
  have htop : (⊤ : Subgroup ↥(Subgroup.zpowers t)) =
      Subgroup.zpowers (⟨t, Subgroup.mem_zpowers t⟩ : ↥(Subgroup.zpowers t)) := by
    refine le_antisymm ?_ le_top
    intro x _
    obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp x.2
    exact Subgroup.mem_zpowers_iff.mpr ⟨n, Subtype.ext (by simpa using hn)⟩
  rw [← B5.range_secHom (Subgroup.zpowers t) (Subgroup.zpowers_le.2 htU)
      (Subgroup.zpowers_le.2 htZ), MonoidHom.range_eq_map, htop, MonoidHom.map_zpowers]
  rfl

theorem secSub_sup {A B : Subgroup (MulAut W)} {U Z : Subgroup W} (hA : StabPair A U Z)
    (hB : StabPair B U Z) : secSub U Z (A ⊔ B) = secSub U Z A ⊔ secSub U Z B := by
  have hAU : A ≤ stabSub U := w1369_stabPair_le_stabSub_left hA
  have hAZ : A ≤ stabSub Z := w1369_stabPair_le_stabSub_right hA
  have hBU : B ≤ stabSub U := w1369_stabPair_le_stabSub_left hB
  have hBZ : B ≤ stabSub Z := w1369_stabPair_le_stabSub_right hB
  have hABU : A ⊔ B ≤ stabSub U := sup_le hAU hBU
  have hABZ : A ⊔ B ≤ stabSub Z := sup_le hAZ hBZ
  rw [w1369_secSub_eq_map hABU hABZ le_rfl,
    Subgroup.subgroupOf_sup le_sup_left le_sup_right, Subgroup.map_sup,
    w1369_secSub_eq_map hABU hABZ le_sup_left,
    w1369_secSub_eq_map hABU hABZ le_sup_right]

theorem isQuasisimple_secSub {L : Subgroup (MulAut W)} {U Z : Subgroup W} (hL : StabPair L U Z)
    (hq : IsQuasisimple ↥L) (hnt : ¬ ∀ l ∈ L, ∀ u ∈ U, l u * u⁻¹ ∈ Z) :
    IsQuasisimple ↥(secSub U Z L) := by
  have hLU : L ≤ stabSub U := w1369_stabPair_le_stabSub_left hL
  have hLZ : L ≤ stabSub Z := w1369_stabPair_le_stabSub_right hL
  have hker_ne : (B5.secHom L hLU hLZ).ker ≠ ⊤ := by
    intro htop
    apply hnt
    intro l hl u hu
    have hmem : (⟨l, hl⟩ : ↥L) ∈ (B5.secHom L hLU hLZ).ker := by rw [htop]; trivial
    rw [B5.mem_ker_secHom] at hmem
    exact hmem.2 u hu
  have hker_le : (B5.secHom L hLU hLZ).ker ≤ Subgroup.center ↥L := by
    rcases CFSG.Quasithin.H13.Ch4.J4KX.normal_le_center_or_top hq
      (B5.secHom L hLU hLZ).ker with h | h
    · exact h
    · exact absurd h hker_ne
  have hq' : IsQuasisimple (↥L ⧸ (B5.secHom L hLU hLZ).ker) :=
    CFSG.Quasithin.H13.Ch4.J4KX.isQuasisimple_quot_of_le_center hq _ hker_le
  have e : (↥L ⧸ (B5.secHom L hLU hLZ).ker) ≃* ↥(secSub U Z L) :=
    (QuotientGroup.quotientKerEquivRange (B5.secHom L hLU hLZ)).trans
      (MulEquiv.subgroupCongr (B5.range_secHom L hLU hLZ))
  exact hq'.of_mulEquiv e.symm

theorem mulEquiv_secSub {A : Subgroup (MulAut W)} {U Z : Subgroup W} (hA : StabPair A U Z)
    (hf : FaithOn A U Z) : Nonempty (↥A ≃* ↥(secSub U Z A)) := by
  have hAU : A ≤ stabSub U := w1369_stabPair_le_stabSub_left hA
  have hAZ : A ≤ stabSub Z := w1369_stabPair_le_stabSub_right hA
  have hfaith : A ⊓ centSec U Z = ⊥ := by
    rw [eq_bot_iff]
    intro a ha
    rw [Subgroup.mem_inf, mem_centSec] at ha
    rw [Subgroup.mem_bot]
    exact hf a ha.1 ha.2.2
  exact ⟨B5.secEquiv A hAU hAZ hfaith⟩

theorem realizes_secSub_iff (D : FFModel) {A : Subgroup (MulAut W)} {U Z : Subgroup W}
    (hA : StabPair A U Z) (hZU : Z ≤ U) (hf : FaithOn A U Z) :
    D.Realizes (secSub U Z A) ⊤ ⊥ ↔ D.Realizes A U Z := by
  have hAU : A ≤ stabSub U := w1369_stabPair_le_stabSub_left hA
  have hAZ : A ≤ stabSub Z := w1369_stabPair_le_stabSub_right hA
  have hfaith : A ⊓ centSec U Z = ⊥ := by
    rw [eq_bot_iff]
    intro a ha
    rw [Subgroup.mem_inf, mem_centSec] at ha
    rw [Subgroup.mem_bot]
    exact hf a ha.1 ha.2.2
  refine ⟨fun h => B5.realizes_of_autSec hZU hAU hAZ hfaith h, fun h => ?_⟩
  obtain ⟨π, hπsurj, -, hker, -, -, hsec, hker', β, hβsurj, hβker, hβeq⟩ := h
  let e : ↥A ≃* ↥(secSub U Z A) := B5.secEquiv A hAU hAZ hfaith
  let π' : D.Gam →* ↥(secSub U Z A) := e.toMonoidHom.comp π
  have hlift : Z.subgroupOf U ≤ β.ker := by
    intro x hx
    rw [MonoidHom.mem_ker, hβker]
    exact Subgroup.mem_subgroupOf.mp hx
  let β₀ : Sect U Z →* ↥D.sec ⧸ D.ker.subgroupOf D.sec :=
    QuotientGroup.lift (Z.subgroupOf U) β hlift
  have hβ₀ : ∀ u : ↥U, β₀ (QuotientGroup.mk u) = β u := fun _ => rfl
  let β' : ↥(⊤ : Subgroup (Sect U Z)) →* ↥D.sec ⧸ D.ker.subgroupOf D.sec :=
    β₀.comp (Subgroup.topEquiv (G := Sect U Z)).toMonoidHom
  have hβ' : ∀ u : ↥U, β' ⟨QuotientGroup.mk u, trivial⟩ = β u := fun u => hβ₀ u
  have hβ'surj : Function.Surjective β' := by
    intro y
    obtain ⟨u, hu⟩ := hβsurj y
    exact ⟨⟨QuotientGroup.mk u, trivial⟩, by rw [hβ' u, hu]⟩
  refine ⟨π', e.surjective.comp hπsurj, le_top, hker, fun _ _ _ => Subgroup.mem_top _,
    fun _ _ hx => ?_, hsec, hker', β', hβ'surj, ?_, ?_⟩
  · rw [Subgroup.mem_bot.mp hx, map_one]
    exact Subgroup.mem_bot.mpr rfl
  · intro u
    obtain ⟨u₀, hu₀⟩ := QuotientGroup.mk_surjective (u : Sect U Z)
    have hu_eq : u = ⟨QuotientGroup.mk u₀, trivial⟩ := Subtype.ext hu₀.symm
    rw [hu_eq, hβ' u₀, hβker u₀, Subgroup.mem_bot, QuotientGroup.eq_one_iff,
      Subgroup.mem_subgroupOf]
  · intro γ u m hu hm hum
    obtain ⟨u₀, hu₀⟩ := QuotientGroup.mk_surjective (u : Sect U Z)
    have hu_eq : u = ⟨QuotientGroup.mk u₀, trivial⟩ := Subtype.ext hu₀.symm
    have hβu : β u₀ = QuotientGroup.mk m := by
      have h1 := hum
      rw [hu_eq, hβ' u₀] at h1
      exact h1
    set w : ↥U := ⟨((π γ : ↥A) : MulAut W) u₀, (hAU (π γ).2 u₀).2 u₀.2⟩
    have hπ' : ((π' γ : ↥(secSub U Z A)) : MulAut (Sect U Z)) (QuotientGroup.mk u₀) =
        QuotientGroup.mk w := by
      change ((B5.secEquiv A hAU hAZ hfaith (π γ) : ↥(secSub U Z A)) :
        MulAut (Sect U Z)) (QuotientGroup.mk u₀) = QuotientGroup.mk w
      rw [B5.secEquiv_apply, B5.secHom_mk]
    have hkey := hβeq γ u₀ m w.2 hm hβu
    rw [hu_eq]
    have harg : (⟨((π' γ : ↥(secSub U Z A)) : MulAut (Sect U Z))
        (QuotientGroup.mk u₀), hu⟩ : ↥(⊤ : Subgroup (Sect U Z))) = ⟨QuotientGroup.mk w, trivial⟩ :=
      Subtype.ext hπ'
    rw [harg]
    exact (hβ' w).trans hkey

end CFSG.LocalAnalysis.WeakClosure81.GF2Reps136
