module

public import CFSG.RankThree.PartTwo.Sec14.Wales1411WL3Tori
public import CFSG.RankThree.PartTwo.Sec14.Wales1411WPoint
import CFSG.RankThree.PartTwo.Sec14.Wales1411WL3Ext
import CFSG.RankThree.PartTwo.Sec13.Item13Sporadic
import CFSG.RankThree.PartTwo.Sec12.Item128Bar
import CFSG.RankThree.PartTwo.Sec14.Item1413Res6ProofL3

public section

namespace CFSG.RankThree.PartTwo.Sec14

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
  CFSG.RankThree.PartTwo.Sec13 CFSG.RankThree.PartTwo.Sec15 CFSG.RankThree.PartTwo.Late
  CFSG.GH74.GLS
open scoped commutatorElement

namespace Wales1411W

variable {G : Type} [Group G] [Finite G]

section Transport

variable {X X' : Type} [Group X] [Group X']

theorem isElemAbelian_map (φ : X ≃* X') {E : Subgroup X} (hE : CFSG.Assembly.IsElemAbelian 3 E) :
    CFSG.Assembly.IsElemAbelian 3 (E.map φ.toMonoidHom) := by
  refine ⟨⟨⟨fun u v => ?_⟩⟩, fun x hx => ?_⟩
  · obtain ⟨u', hu', hu⟩ := u.2
    obtain ⟨v', hv', hv⟩ := v.2
    apply Subtype.ext
    change (u : X') * v = v * u
    rw [← hu, ← hv, ← map_mul, ← map_mul]
    exact congrArg φ (congrArg Subtype.val (hE.1.is_comm.comm ⟨u', hu'⟩ ⟨v', hv'⟩))
  · obtain ⟨y, hy, rfl⟩ := hx
    change φ y ^ 3 = 1
    rw [← map_pow, hE.2 y hy, map_one]

theorem trans_map (φ : X ≃* X') {E : Subgroup X}
    (htr : ∀ y₀ ∈ E, y₀ ≠ 1 → ∀ y₁ ∈ E, y₁ ≠ 1 →
      ∃ w ∈ Subgroup.normalizer (E : Set X), w * y₀ * w⁻¹ = y₁) :
    ∀ y₀ ∈ E.map φ.toMonoidHom, y₀ ≠ 1 → ∀ y₁ ∈ E.map φ.toMonoidHom, y₁ ≠ 1 →
      ∃ w ∈ Subgroup.normalizer ((E.map φ.toMonoidHom : Subgroup X') : Set X'),
        w * y₀ * w⁻¹ = y₁ := by
  rintro _ ⟨z₀, hz₀, rfl⟩ h₀ _ ⟨z₁, hz₁, rfl⟩ h₁
  have h₀' : z₀ ≠ 1 := fun h => h₀ (by simp [h])
  have h₁' : z₁ ≠ 1 := fun h => h₁ (by simp [h])
  obtain ⟨w, hw, hwz⟩ := htr z₀ hz₀ h₀' z₁ hz₁ h₁'
  refine ⟨φ w, ?_, ?_⟩
  · rw [← Subgroup.map_equiv_normalizer_eq]
    exact Subgroup.mem_map_of_mem _ hw
  · simp only [MulEquiv.coe_toMonoidHom]
    rw [← map_inv, ← map_mul, ← map_mul, hwz]

theorem isoLThreePi_of_mulEquiv (φ : X ≃* X') {p e : ℕ} [Fact p.Prime]
    (h : Sec4.IsoLThreePi X p e) :
    Sec4.IsoLThreePi X' p e := by
  rcases h with ⟨h3, ⟨ψ⟩⟩ | ⟨h3, ⟨ψ⟩⟩
  · exact Or.inl ⟨h3, ⟨φ.symm.trans ψ⟩⟩
  · exact Or.inr ⟨h3, ⟨φ.symm.trans ψ⟩⟩

end Transport

theorem frame142_of_pt142 {A L : Subgroup G} {c : G} (P : Proof1413Res5.Pt142 A c L)
    (h142 : Item142 A (lB A) c L P.std.toSec13Data.isElemAbelian.1 P.std.toSec13Data.mem_A) :
    Frame142 A c where
  isE27 := P.std.isE27
  mem_A := P.std.toSec13Data.mem_A
  k_le_centralizer := P.k_le_centralizer
  zpow_eq_one_of_mem := fun _ h => P.zpow_eq_one_of_mem Sec13.sporadicModels131 h
  mem_scriptQ := fun Z hZK hAZ hZ3 => mem_scriptQ_of_invariant _ _ h142
    ⟨hZK.trans (delta_le _), (isPiSubgroup_piCompl_iff Nat.prime_three Z).mpr hZ3, hAZ⟩

section Lalpha

variable {A L : Subgroup G} {c : G} [(ker142 A (lB A) c).Normal]

theorem l_le_kA_pt (P : Proof1413Res5.Pt142 A c L) : L ≤ kA142 A (lB A) c :=
  P.l_le.trans le_sup_left

theorem ker_toKα_pt (P : Proof1413Res5.Pt142 A c L) :
    (Res5Types.toKα (l_le_kA_pt P)).ker = aschbacherSolvableCore 3 ↥L := by
  ext l
  rw [MonoidHom.mem_ker, Res5Types.toKα, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
    QuotientGroup.eq_one_iff, ker142, Subgroup.mem_subgroupOf]
  change (l : G) ∈ pPrimeCoreOf 3 (k142 A (lB A) c) ⊔ Subgroup.zpowers c ↔ _
  constructor
  · intro hl
    have h := P.mem_theta_of_mem Sec13.sporadicModels131 hl l.2
    obtain ⟨l', hl', hll'⟩ := h
    have : l' = l := Subtype.ext hll'
    rwa [← this]
  · intro hl
    exact Subgroup.mem_sup_left (P.theta_le ⟨l, hl, rfl⟩)

@[expose] noncomputable def lbarEquivPt (P : Proof1413Res5.Pt142 A c L) :
    (↥L ⧸ aschbacherSolvableCore 3 ↥L) ≃* ↥(img142 A (lB A) c L) :=
  (QuotientGroup.quotientMulEquivOfEq (ker_toKα_pt P)).symm.trans
    ((QuotientGroup.quotientKerEquivRange (Res5Types.toKα (l_le_kA_pt P))).trans
      (MulEquiv.subgroupCongr (Res5Types.range_toKα (l_le_kA_pt P))))

theorem img_l_normal_pt (P : Proof1413Res5.Pt142 A c L) : (img142 A (lB A) c L).Normal := by
  have hKA : kA142 A (lB A) c ≤ Subgroup.normalizer (L : Set G) :=
    sup_le P.k_le_normalizer P.std.toSec13Data.le_normalizer
  have h := (Subgroup.normal_subgroupOf_iff_le_normalizer (l_le_kA_pt P)).mpr hKA
  exact h.map _ (QuotientGroup.mk'_surjective _)

theorem img_A_pt (P : Proof1413Res5.Pt142 A c L) (hAc : A = Subgroup.zpowers c ⊔ (A ⊓ L)) :
    img142 A (lB A) c A = img142 A (lB A) c (A ⊓ L) := by
  have hcA := P.std.toSec13Data.mem_A
  have hZ : Subgroup.zpowers c ≤ kA142 A (lB A) c :=
    (Subgroup.zpowers_le.mpr hcA).trans le_sup_right
  have hAL : A ⊓ L ≤ kA142 A (lB A) c := inf_le_left.trans le_sup_right
  have h : img142 A (lB A) c A = img142 A (lB A) c (Subgroup.zpowers c ⊔ (A ⊓ L)) :=
    congrArg (fun X => img142 A (lB A) c X) hAc
  rw [h, img142, img142, Subgroup.subgroupOf_sup hZ hAL, Subgroup.map_sup]
  have hbot : ((Subgroup.zpowers c).subgroupOf (kA142 A (lB A) c)).map
      (QuotientGroup.mk' (ker142 A (lB A) c)) = ⊥ := by
    rw [Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk']
    intro x hx
    rw [ker142, Subgroup.mem_subgroupOf]
    exact Subgroup.mem_sup_right (Subgroup.mem_subgroupOf.mp hx)
  rw [hbot, bot_sup_eq]

theorem map_lbarEquivPt (P : Proof1413Res5.Pt142 A c L)
    (hAc : A = Subgroup.zpowers c ⊔ (A ⊓ L)) :
    ((A.subgroupOf L).map (QuotientGroup.mk' (aschbacherSolvableCore 3 ↥L))).map
        (lbarEquivPt P).toMonoidHom =
      (img142 A (lB A) c A).subgroupOf (img142 A (lB A) c L) := by
  ext z
  rw [Subgroup.mem_map, Subgroup.mem_subgroupOf, img_A_pt P hAc]
  constructor
  · rintro ⟨_, ⟨l, hl, rfl⟩, rfl⟩
    refine ⟨Subgroup.inclusion (l_le_kA_pt P) l, Subgroup.mem_subgroupOf.mpr
      ⟨Subgroup.mem_subgroupOf.mp hl, l.2⟩, rfl⟩
  · intro hz
    obtain ⟨x, hx, hxz⟩ := hz
    have hxAL : ((x : ↥(kA142 A (lB A) c)) : G) ∈ A ⊓ L := Subgroup.mem_subgroupOf.mp hx
    refine ⟨QuotientGroup.mk' _ ⟨(x : G), hxAL.2⟩,
      ⟨⟨(x : G), hxAL.2⟩, Subgroup.mem_subgroupOf.mpr hxAL.1, rfl⟩, ?_⟩
    apply Subtype.ext
    rw [← hxz]
    rfl

end Lalpha

open Proof1413Res5 in
theorem isConjIn_of_l3odd_point (h131 : Item131) (h142 : Item142AllS14) (hbot : Item145BotS14)
    (hKL : KL3HessTori) {A L : Subgroup G} {c : G} (hR : Sec15R G A c L) {a : G}
    (ha : Subgroup.zpowers a ∈ omegaA A) {La : Subgroup G} (hLa : La ∈ lA A a)
    (hPGL : ¬ Sec8.IsZ3PGLThreePi (lBarA a La A)) {p e : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    (he : 1 ≤ e) (hiso : Sec4.IsoLThreePi (↥La ⧸ aschbacherSolvableCore 3 ↥La) p e)
    {Y : Subgroup G} (hY : Y ∈ scriptY A)
    (hIH : ∀ Y' ∈ scriptY A, Nat.card Y' < Nat.card Y →
      TransOn A (lB A) (Subgroup.normalizer (A : Set G)) Y')
    (hYa : Y ≤ Subgroup.centralizer ({a} : Set G))
    {S T : Subgroup G} (hS : S ∈ scriptQPiStar A (lB A) Y (piOf 2))
    (hT : T ∈ scriptQPiStar A (lB A) Y (piOf 2)) :
    IsConjIn (Subgroup.normalizer (A : Set G) ⊓ Y) S T := by
  by_cases hYST : S ⊔ T = Y
  swap
  · exact isConjIn_of_sup_ne hY hIH hS hT hYST
  have h' : Sec14Std G A a La := Proof1413.sec14Std_at hR.toSec14Std ha hLa
  have hD := h'.toSec13Data
  have := ker142_normal (LB := lB A) hD.isElemAbelian.1 hD.mem_A
  obtain ⟨haL, h9, hAa, hQ⟩ :=
    Proof1413Res6.l3_point_facts h131 hD ⟨p, e, ‹_›, he, hiso⟩ hPGL
  obtain ⟨hEe, hE9, htr⟩ := Proof1413Res6.hess_of_l3_point hD haL h9 hAa hQ
  have hXW : xA A ≤ Subgroup.normalizer (A : Set G) :=
    (pPrimeCoreOf_le 3 _).trans (Subgroup.centralizer_le_normalizer _)
  set H := Subgroup.normalizer (Subgroup.zpowers a : Set G) with hH
  obtain ⟨Q₀, hQ₀⟩ := maxInvariantPiSubgroups_nonempty H A (piCompl 3)
  obtain ⟨hQ₀q, hQ₀b⟩ := h142 G A a La h' Q₀ hQ₀
  rcases hQ₀b with ⟨-, hQK, -, -⟩ | ⟨hK, -⟩
  ·
    have hKq : k142 A (lB A) a ∈ scriptQ A (lB A) := by
      rw [← hQK]
      exact hQ₀q.1
    have hCH : Subgroup.centralizer ({a} : Set G) ≤ H :=
      centralizer_singleton_le_normalizer_zpowers a
    have hSY : S ≤ Y := hS.prop.1.2
    have hTY : T ≤ Y := hT.prop.1.2
    have hZY : k142 A (lB A) a ⊓ Y ∈ scriptQ A (lB A) :=
      mem_scriptQ_of_le hKq inf_le_left (le_normalizer_inf hKq.1.2.2 hY.2)
    exact (isConjIn_of_le_mem_scriptQ h'.isE27 (hbot G A a La h') hZY inf_le_right hS hT
      (le_inf (le_delta hS.prop.1.1 ((hSY.trans hYa).trans hCH)) hSY)
      (le_inf (le_delta hT.prop.1.1 ((hTY.trans hYa).trans hCH)) hTY)).mono
      (inf_le_inf_right Y hXW)
  · have P : Pt142 A a La := ⟨h', hK⟩
    have f := frame142_of_pt142 P (h142 G A a La h')
    have hLn := img_l_normal_pt P
    have hAL : img142 A (lB A) a A ≤ img142 A (lB A) a La := by
      rw [img_A_pt P hAa]
      exact Res5Types.img_inf_le
    set φ := lbarEquivPt P with hφ
    have hmap := map_lbarEquivPt P hAa
    have hET : ETrans2 (↥(kA142 A (lB A) a) ⧸ ker142 A (lB A) a) (img142 A (lB A) a A) := by
      refine etrans2_of_normal_l3 hKL (img142 A (lB A) a La) (img142 A (lB A) a A) hAL hp2 he
        (isoLThreePi_of_mulEquiv φ hiso) ?_ ?_ ?_
      · rw [← hmap]
        exact isElemAbelian_map φ hEe
      · rw [← hmap, Subgroup.card_map_of_injective φ.injective]
        exact hE9
      · rw [← hmap]
        exact trans_map φ htr
    exact f.isConjIn_of_etrans2 (hbot G A a La h') hET hY.2 hYa hS hT hYST.symm

end Wales1411W

open Wales1411W in
theorem claim1411NonsolvWPointL3FieldOmegaR_of_tori
    (h131 : Item131)
    (h142 : Item142AllS14) (hbot : Item145BotS14) (h422 : Sec4.Item4_22) (h45 : Sec4.Item4_5)
    (hKL : KL3HessTori) : Claim1411NonsolvWPointL3FieldOmegaR := by
  intro G _ _ A c L hR Y hYΔ hY hs h3 hBc hIH S hS T hT hD hbig hres a haA ha1 haS haT ha hpt
  have hYa := hres a haA ha1 haS haT
  have hD13 := hR.toSec14Std.toSec13Data
  have hAa : A ≤ Subgroup.centralizer ({a} : Set G) := fun x hx =>
    Subgroup.mem_centralizer_singleton_iff.mpr (hD13.commute hx haA)
  obtain ⟨La₀, hLa₀⟩ := Sec12.exists_mem_lA422 h422 h45 hD13.toPartTwoStanding
    hD13.mem_partTwoF hD13.card_eq ha
  have hLa := Sec12.mem_lA_of_mem_lA422 hAa hLa₀
  set La := La₀ with hLaDef
  obtain ⟨hPGL, ⟨p, e, hp, he, hiso⟩, h2, -⟩ := hpt La hLa
  have hp2 : p ≠ 2 := by
    rintro rfl
    exact h2 ⟨hp, e, he, hiso⟩
  exact isConjIn_of_l3odd_point h131 h142 hbot hKL hR ha hLa hPGL hp2 he hiso hY hIH hYa hS hT

end CFSG.RankThree.PartTwo.Sec14
