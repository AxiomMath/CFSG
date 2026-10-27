module

public import CFSG.RankThree.PartTwo.Sec15.Item15Res6ProofTools
public import CFSG.RankThree.PartTwo.Sec15.Y4CoreProofUse
import CFSG.RankThree.PartTwo.Sec14.Item143Proof
import CFSG.RankThree.PartTwo.Sec14.Concl142HJPoint
import CFSG.RankThree.PartTwo.KFacts.KS14HJBasic
import CFSG.RankThree.PartTwo.KFacts.KS14PGL
import CFSG.RankThree.PartTwo.Sec4.Sporadic.Item415
public import CFSG.RankThree.PartTwo.Sec14.Item148Steps

public section

namespace CFSG.RankThree.PartTwo.Sec15

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.LocalRank CFSG.GH74.GLS
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem false_of_case148Seven {A : Subgroup G} {LB : Subgroup G → Subgroup G}
    (hAab : IsMulCommutative A) {Y : Subgroup G} (hY : Y ∈ scriptY4 A LB)
    (hYΔ : Y = deltaZero A LB Y)
    (h7 : letI := ker148_normal hY.1.2; Case148Seven A LB Y) : False := by
  let := ker148_normal hY.1.2
  have hq := Proof1515.isQuasisimple_quot_pPrimeCore hY
  obtain ⟨e0⟩ : Nonempty (↥(img148 A Y (deltaZero A LB Y)) ≃* ↥Y ⧸ CFSG.pPrimeCore 3 ↥Y) := by
    rw [← hYΔ]
    exact nonempty_img148_equiv hY.1.2
  have hqX : IsQuasisimple ↥(img148 A Y (deltaZero A LB Y)) :=
    CFSG.LocalCores.isQuasisimple_of_surjective hq e0.symm.toMonoidHom e0.symm.surjective
      (by rw [(MonoidHom.ker_eq_bot_iff _).mpr e0.symm.injective]; exact bot_le)
  obtain ⟨-, -, L₁, L₂, J₁, J₂, p₁, f₁, -, p₂, f₂, -, -, -, -, -, -, -, hJ₁, hJ₂, hsup, hinf,
    hcomm, -, -, -, -, hZ₁, hZ₂, -, -⟩ := h7
  set X := img148 A Y (deltaZero A LB Y) with hX
  have hJ₁le : img148 A Y J₁ ≤ X := hsup ▸ le_sup_left
  have hJ₂le : img148 A Y J₂ ≤ X := hsup ▸ le_sup_right
  have hC₁ : img148 A Y J₂ ≤ Subgroup.centralizer (img148 A Y J₁ : Set _) := by
    rw [← Subgroup.commutator_eq_bot_iff_le_centralizer, Subgroup.commutator_comm]
    exact hcomm
  have hC₂ : img148 A Y J₁ ≤ Subgroup.centralizer (img148 A Y J₂ : Set _) :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcomm
  have hN₁ : ((img148 A Y J₁).subgroupOf X).Normal := by
    refine (Subgroup.normal_subgroupOf_iff_le_normalizer hJ₁le).mpr ?_
    rw [← hsup]
    exact sup_le Subgroup.le_normalizer (hC₁.trans (Subgroup.centralizer_le_normalizer _))
  have hN₂ : ((img148 A Y J₂).subgroupOf X).Normal := by
    refine (Subgroup.normal_subgroupOf_iff_le_normalizer hJ₂le).mpr ?_
    rw [← hsup]
    exact sup_le (hC₂.trans (Subgroup.centralizer_le_normalizer _)) Subgroup.le_normalizer
  have hsup' : (img148 A Y J₁).subgroupOf X ⊔ (img148 A Y J₂).subgroupOf X = ⊤ := by
    rw [← Subgroup.subgroupOf_sup hJ₁le hJ₂le, hsup, Subgroup.subgroupOf_self]
  have hinf' : (img148 A Y J₁).subgroupOf X ⊓ (img148 A Y J₂).subgroupOf X = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    have h1 : (x : ↥(Y ⊔ A) ⧸ ker148 A Y) ∈ img148 A Y J₁ ⊓ img148 A Y J₂ := ⟨hx.1, hx.2⟩
    rw [hinf] at h1
    exact (Subgroup.mem_bot).mpr (Subtype.ext ((Subgroup.mem_bot).mp h1))
  have hbot : img148 A Y J₁ = ⊥ ∨ img148 A Y J₂ = ⊥ := by
    rcases eq_bot_or_eq_bot_of_isQuasisimple hqX hN₁ hN₂ hsup' hinf' with h | h
    · left
      rw [Subgroup.subgroupOf_eq_bot] at h
      exact disjoint_self.mp (h.mono_right hJ₁le)
    · right
      rw [Subgroup.subgroupOf_eq_bot] at h
      exact disjoint_self.mp (h.mono_right hJ₂le)
  have hAle : A ≤ Y ⊔ A := le_sup_right
  have key : ∀ J : Subgroup G, J ≤ Y → img148 A Y J = ⊥ →
      ∀ p f : ℕ, IsZ3PGLThreeAt ↥(img148 A Y (J ⊔ A)) p f → False := by
    intro J hJY hJ p f hZ
    rw [img148_sup (hJY.trans le_sup_left) hAle, hJ, bot_sup_eq] at hZ
    obtain ⟨a, b, hab⟩ := KFacts.KS14.ks15Z3PGLNonabelian _ p f hZ
    exact hab (img148_comm hAab a b)
  rcases hbot with h | h
  · exact key J₁ (hJ₁.trans inf_le_right) h p₁ f₁ hZ₁
  · exact key J₂ (hJ₂.trans inf_le_right) h p₂ f₂ hZ₂


section Certificates


@[expose] noncomputable def Step159FiveR : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
    Ctx159 G A c L → ∀ w : G, IsW159 A L w →
      ∀ (J : Subgroup G) (hJ : J ∈ scriptY0 A (lB A)), w ∈ Subgroup.normalizer (J : Set G) →
        (letI := ker148_normal hJ.1.1.2; Case148Five A (lB A) J) → False

end Certificates


theorem false_of_mem_actTriv {A L : Subgroup G} {c : G} (ctx : Ctx159 G A c L) {w : G}
    (hw : IsW159 A L w) (hLB : ∀ B : Subgroup G, IsHyperplane A B → lB A B = ⊥)
    {J : Subgroup G} (hJ : J ∈ scriptY4 A (lB A)) (hwJ : w ∈ Subgroup.normalizer (J : Set G))
    {a : G} (haΩ : Subgroup.zpowers a ∈ omegaA A)
    (haT : a ∈ Proof15Res6.actTriv J (pPrimeCoreOf 3 J)) : False := by
  have h := ctx.toSec15R
  have hA := h.isElemAbelian
  have hA27 := h.card_eq
  obtain ⟨haA, ha3, -⟩ := zpowers_mem_omegaA_iff.mp haΩ
  have ha1 : a ≠ 1 := by
    rintro rfl
    rw [Subgroup.zpowers_one_eq_bot, Subgroup.card_bot] at ha3
    exact absurd ha3 (by norm_num)
  have hord : orderOf a = 3 := by rw [← Nat.card_zpowers]; exact ha3
  have hJ3 : 3 ∣ Nat.card J :=
    (Proof1515.three_dvd_card_of_mem_scriptY4 hJ).trans (Subgroup.card_quotient_dvd_card _)
  have hN3 : ¬ 3 ∣ Nat.card (pPrimeCoreOf 3 J) :=
    (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp (coprime_card_pPrimeCoreOf 3 J)
  have hwN : w ∈ Subgroup.normalizer (pPrimeCoreOf 3 J : Set G) :=
    normalizer_le_normalizer_pPrimeCoreOf 3 J hwJ
  have hwaT := Proof15Res6.conj_mem_actTriv hwJ hwN haT
  have hwaA : w * a * w⁻¹ ∈ A := (Subgroup.mem_normalizer_iff.mp hw.1 a).mp haA
  have hmem := Proof15Res6.mem_zpowers_of_mem_actTriv hA hA27 hLB hJ.2.2.1
    (le_normalizer_pPrimeCoreOf 3 J) hN3 hJ3 haA hwaA ha1 haT hwaT
  obtain ⟨k, hwk⟩ := hw.2.1
  have hcomm : w * a = a * w := Proof159Res2.commute_of_conj_mem_zpowers hord hwk hmem
  have hle : Subgroup.zpowers a ≤ A ⊓ Subgroup.centralizer ({w} : Set G) := by
    rw [Subgroup.zpowers_le]
    exact ⟨haA, Subgroup.mem_centralizer_singleton_iff.mpr hcomm.symm⟩
  rw [hw.inf_centralizer_eq h.toSec13Data.card_eq ctx.card_inf] at hle
  exact ctx.not_le_inf haΩ hle

theorem false_of_ctx159_y0 (h134 : Item134) (h48 : Sec4.Item4_8) (h148 : Item148R)
    (h5 : Step159FiveR) {A L : Subgroup G} {c : G} (ctx : Ctx159 G A c L) {w : G}
    (hw : IsW159 A L w) {J : Subgroup G} (hJ : J ∈ scriptY0 A (lB A))
    (hwJ : w ∈ Subgroup.normalizer (J : Set G)) : False := by
  have h := ctx.toSec15R
  have h14 := h.toSec14Std
  have hNHJ : ¬ AllPointsHJ A :=
    Proof15Res6.not_allPointsHJ_of_isEmpty h14 (Proof15Res6.isEmpty_j2_of_types ctx.types)
  have hLB : ∀ B : Subgroup G, IsHyperplane A B → lB A B = ⊥ :=
    fun B hB => lB_eq_bot_of_not_allPointsHJ' h134 h48 h14 hNHJ hB
  have hJ4 := hJ.1
  have hJY : J ∈ scriptY A := hJ4.1
  have hAJ : A ≤ Subgroup.normalizer (J : Set G) := hJY.2
  have hJΔ0 : J = deltaZero A (lB A) J :=
    eq_deltaZero_of_eq_delta' h134 CFSG.Sporadic.J2.isSimpleGroup_J2 h48
      Sec4.Sporadic.rank3II_4_15 (KFacts.KS14.center_nativeJ2_eq_bot Sec4.Sporadic.rank3II_4_15)
      h14 hAJ hJ4.2.1 hJ4.2.2.1
  have hJ3 : 3 ∣ Nat.card J :=
    (Proof1515.three_dvd_card_of_mem_scriptY4 hJ4).trans (Subgroup.card_quotient_dvd_card _)
  have hHJ : ∀ (c' : G) (L' : Subgroup G), Subgroup.zpowers c' ∈ omegaA A → L' ∈ lA A c' →
      Nonempty (↥L' ⧸ aschbacherSolvableCore 3 ↥L' ≃* CFSG.Blueprint.NativeSporadic.J2) →
        False := fun c' L' hc' hL' hJ2 =>
    hNHJ (allPointsHJ_of_j2 h134 h48 { h14 with zpowers_mem_omegaA := hc', mem_lA := hL' } hJ2)
  let := ker148_normal hAJ
  have hcases := ((item148_iff A (lB A)).mp (h148 G A c L h) J hJY).2
  rcases hcases with h1 | h2 | h3 | h4 | h5' | h6 | h7
  ·
    have h1' : deltaZero A (lB A) J ≤ pPrimeCoreOf 3 J := h1
    have hle : J ≤ pPrimeCoreOf 3 J := hJΔ0.le.trans h1'
    have hN3 : ¬ 3 ∣ Nat.card (pPrimeCoreOf 3 J) :=
      (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp (coprime_card_pPrimeCoreOf 3 J)
    exact hN3 (hJ3.trans (Subgroup.card_dvd_of_le hle))
  ·
    obtain ⟨c', hc'Ω, hdec, -⟩ := h2
    rw [← hJΔ0] at hdec
    obtain ⟨hc'A, hc'3, -⟩ := zpowers_mem_omegaA_iff.mp hc'Ω
    have hord : orderOf c' = 3 := by rw [← Nat.card_zpowers]; exact hc'3
    exact false_of_mem_actTriv ctx hw hLB hJ4 hwJ hc'Ω
      (Proof15Res6.mem_actTriv_of_eq_sup hc'A hord hAJ hdec)
  ·
    obtain ⟨c', -, L', hc', hL', hJ2, -⟩ := h3
    exact hHJ c' L' hc' hL' hJ2
  ·
    obtain ⟨-, -, hW⟩ := h4
    have h9 : 9 ∣ Nat.card (wStar A) := by
      rw [← ctx.card_oThree]
      exact Subgroup.card_dvd_of_le (Subgroup.map_subtype_le _)
    rcases hW with ⟨⟨φ⟩⟩ | ⟨⟨φ⟩⟩
    · rw [Nat.card_congr φ.toEquiv, Nat.card_eq_fintype_card, Fintype.card_perm,
        Fintype.card_fin] at h9
      exact absurd h9 (by decide)
    · rw [Nat.card_congr φ.toEquiv, Nat.card_prod, Nat.card_eq_fintype_card (α := Equiv.Perm _),
        Fintype.card_perm, Fintype.card_fin, Nat.card_eq_fintype_card (α := Multiplicative _),
        Fintype.card_multiplicative, ZMod.card] at h9
      exact absurd h9 (by decide)
  ·
    exact h5 G A c L ctx w hw J hJ hwJ h5'
  ·
    obtain ⟨-, ⟨c', L', hc', hL', hJ2⟩, -⟩ := h6
    exact hHJ c' L' hc' hL' hJ2
  ·
    exact false_of_case148Seven h.isElemAbelian.1 hJ4 hJΔ0 h7

theorem step159ClaimKY0_of (h134 : Item134) (h48 : Sec4.Item4_8) (h148 : Item148R)
    (h5 : Step159FiveR) : Step159ClaimKY0 := by
  intro G _ _ A c L ctx w hw J hJ hwJ
  exact (false_of_ctx159_y0 h134 h48 h148 h5 ctx hw hJ hwJ).elim

end CFSG.RankThree.PartTwo.Sec15
