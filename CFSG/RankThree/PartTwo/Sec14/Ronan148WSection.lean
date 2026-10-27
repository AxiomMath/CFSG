module

public import CFSG.RankThree.PartTwo.Sec14.Ronan148WOmega
import CFSG.RankThree.PartTwo.Sec14.Ronan148WKey
import CFSG.RankThree.PartTwo.Sec14.Ronan148WOrder
import CFSG.RankThree.PartTwo.Sec14.Ronan148WComm
import CFSG.RankThree.PartTwo.Sec14.Item1411HJ

public section

namespace CFSG.RankThree.PartTwo.Sec14.Ronan148W

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.LocalRank CFSG.GH74.GLS CFSG.RankThree.PartTwo.Sec14
  CFSG.RankThree.PartTwo.Sec14.Main148 CFSG.AGLEmbeddingD2.Wilson.MaximalityAmbient.Step148M24
  CFSG.Blueprint

variable {G : Type} [Group G] [Finite G]

theorem exists_lift_pow_three {A Y : Subgroup G} [(ker148 A Y).Normal] {U : Subgroup G}
    (hUM : U ≤ Y ⊔ A) {x : ↥(Y ⊔ A) ⧸ ker148 A Y} (hx : x ∈ img148 A Y U) (hx3 : x ^ 3 = 1) :
    ∃ (u : G) (hu : u ∈ Y ⊔ A), u ∈ U ∧ u ^ 3 = 1 ∧
      QuotientGroup.mk' (ker148 A Y) ⟨u, hu⟩ = x := by
  obtain ⟨j, hjM, hjU, rfl⟩ := mem_img148_iff.mp hx
  obtain ⟨m, k, hm, hv⟩ := exists_pow_three_part148 (y := j)
  have hvU : j ^ m ∈ U := U.pow_mem hjU m
  have hvM : j ^ m ∈ Y ⊔ A := hUM hvU
  have hαv : QuotientGroup.mk' (ker148 A Y) ⟨j ^ m, hvM⟩ =
      QuotientGroup.mk' (ker148 A Y) ⟨j, hjM⟩ := by
    have e1 : QuotientGroup.mk' (ker148 A Y) ⟨j ^ m, hvM⟩ =
        QuotientGroup.mk' (ker148 A Y) ⟨j, hjM⟩ ^ m := by
      rw [← map_pow]
      rfl
    rw [e1, ← Nat.div_add_mod m 3, hm, pow_add, pow_mul, hx3, one_pow, one_mul, pow_one]
  have hv3 : (j ^ m) ^ 3 = 1 := by
    have hv3M : (j ^ m) ^ 3 ∈ Y ⊔ A := (Y ⊔ A).pow_mem hvM 3
    have h1 : (j ^ m) ^ 3 ∈ pPrimeCoreOf 3 Y := by
      have : QuotientGroup.mk' (ker148 A Y) ⟨(j ^ m) ^ 3, hv3M⟩ = 1 := by
        rw [show (⟨(j ^ m) ^ 3, hv3M⟩ : ↥(Y ⊔ A)) = ⟨j ^ m, hvM⟩ ^ 3 from rfl, map_pow, hαv,
          hx3]
      exact mk'_ker148_eq_one_iff.mp this
    refine eq_one_of_pow_three_pow_eq_one148 (coprime_card_pPrimeCoreOf 3 Y) h1 (k := k) ?_
    rw [← pow_mul, show 3 * 3 ^ k = 3 ^ k * 3 by ring, pow_mul, hv, one_pow]
  exact ⟨j ^ m, hvM, hvU, hv3, hαv⟩



theorem sec13HJPointSection_of_omega (hΩ : Sec13HJPointOmega) : Sec13HJPointSection := by
  intro G _ _ A c L hStd Y hY hs ih B hB hnot YB hYB htype hΔ b d Lb hc hle J hJ hYBJ hAJ Yd hYd
    hYBYd hYdJ hAYd hA6 hθ hW hdc hYB6 hdYB hb hM a haB ha1 ha3 haC La hLa eLa P hPle hAP hPperf
    himgP
  exfalso
  have hker : (ker148 A Y).Normal := ker148_normal hY.2
  obtain ⟨hΩa, -⟩ := hΩ G A c L hStd Y hY hs ih B hB hnot YB hYB htype hΔ b d Lb hc hle J hJ
    hYBJ hAJ Yd hYd hYBYd hYdJ hAYd hA6 hθ hW hdc hYB6 hdYB hb hM a haB ha1 ha3 haC
  obtain ⟨e⟩ := hM
  have hS' : Sec14Std G A a La := { hStd with zpowers_mem_omegaA := hΩa, mem_lA := hLa }
  have hJY : J ≤ Y := le_of_mem_thetaComponentsIn hJ
  have hJM : J ≤ Y ⊔ A := hJY.trans le_sup_left
  have hPJ : P ≤ J := hPle.trans inf_le_left
  have hPC : P ≤ Subgroup.centralizer ({a} : Set G) := hPle.trans inf_le_right
  have hPM : P ≤ Y ⊔ A := hPJ.trans hJM
  have hLaC : La ≤ Subgroup.centralizer ({a} : Set G) :=
    le_centralizer_of_mem_thetaComponentsAt hLa.1
  have hAeq : A = Subgroup.zpowers a ⊔ (A ⊓ La) := (j2_point_facts hS'.toSec13Data eLa).2.2
  have hLaA : La ⊔ A = La ⊔ Subgroup.zpowers a := by
    refine le_antisymm (sup_le le_sup_left ?_) (sup_le le_sup_left ?_)
    · conv_lhs => rw [hAeq]
      exact sup_le le_sup_right (inf_le_right.trans le_sup_left)
    · exact (Subgroup.zpowers_le.mpr haC.1).trans le_sup_right
  set Q0 : Subgroup G := P ⊓ (La ⊔ A) with hQ0
  have hQ0M : Q0 ≤ Y ⊔ A := inf_le_left.trans hPM
  have hQ0img : img148 A Y Q0 = img148 A Y J := by
    refine le_antisymm (himgP ▸ img148_mono inf_le_left) ?_
    have hdA : d ∈ A := hB.1 (lbConfig_points hB hStd.isE27.2 hc).2.1
    have hd1 : d ≠ 1 := (lbConfig_points hB hStd.isE27.2 hc).2.2.2.1
    have hdJα : alpha148 A Y d hdA ∈ img148 A Y J :=
      mem_img148_iff.mpr ⟨d, Subgroup.mem_sup_right hdA, hYdJ (hYBYd hdYB), rfl⟩
    have hd1α : alpha148 A Y d hdA ≠ 1 := alpha148_ne_one hdA hd1 (hStd.isE27.1.2 d hdA)
    haveI : IsSimpleGroup NativeSporadic.M24 := (CFSG.Sporadic.Mathieu.fam_m24_simplicity).2.2
    haveI : IsSimpleGroup ↥(img148 A Y J) := MulEquiv.isSimpleGroup e
    have htop : (img148 A Y Q0).subgroupOf (img148 A Y J) = ⊤ := by
      refine eq_top_of_forall_pow_three_mem (z := ⟨alpha148 A Y d hdA, hdJα⟩) ?_ ?_ ?_
      · intro h1
        exact hd1α (congrArg Subtype.val h1)
      · apply Subtype.ext
        rw [Subgroup.coe_pow, Subgroup.coe_one]
        exact alpha148_pow_three hStd.isE27.1.2 hdA
      · intro x hx3
        rw [Subgroup.mem_subgroupOf]
        have hx3' : (x : ↥(Y ⊔ A) ⧸ ker148 A Y) ^ 3 = 1 := by
          simpa using congrArg Subtype.val hx3
        obtain ⟨u, huM, huP, hu3, hux⟩ :=
          exists_lift_pow_three hPM (by rw [himgP]; exact x.2) hx3'
        have huLA : u ∈ La ⊔ A := mem_sup_of_pow_three_eq_one hS' eLa (hPC huP) hu3
        rw [← hux]
        exact mem_img148_iff.mpr ⟨u, huM, ⟨huP, huLA⟩, rfl⟩
    intro y hy
    have : (⟨y, hy⟩ : ↥(img148 A Y J)) ∈ (img148 A Y Q0).subgroupOf (img148 A Y J) := by
      rw [htop]
      exact Subgroup.mem_top _
    exact Subgroup.mem_subgroupOf.mp this
  set R : Subgroup G := ⁅Q0, Q0⁆ with hR
  have hRLa : R ≤ La := by
    have h1 : R ≤ ⁅La ⊔ A, La ⊔ A⁆ := Subgroup.commutator_mono inf_le_right inf_le_right
    rw [hLaA] at h1
    exact h1.trans (commutator_sup_zpowers_le La fun l hl =>
      Subgroup.mem_centralizer_singleton_iff.mp (hLaC hl))
  have hRQ : R ≤ Q0 := Subgroup.commutator_le.mpr fun g hg h hh => by
    rw [commutatorElement_def]
    exact Q0.mul_mem (Q0.mul_mem (Q0.mul_mem hg hh) (Q0.inv_mem hg)) (Q0.inv_mem hh)
  have hRP : R ≤ P := hRQ.trans inf_le_left
  have h3J : 3 ∣ Nat.card J :=
    (three_dvd_card_of_ydType148 (d := d) (Or.inr (Or.inl hA6))).trans
      (Subgroup.card_dvd_of_le hYdJ)
  have hperfJ : Group.IsPerfect ↥(img148 A Y J) :=
    (img148_isQuasisimple (A := A) (Y := Y) hJ h3J).1.1
  have hRimg : img148 A Y R = img148 A Y J := by
    have h1 : img148 A Y R = ⁅img148 A Y Q0, img148 A Y Q0⁆ :=
      map_commutator_subgroupOf hQ0M (QuotientGroup.mk' (ker148 A Y))
    rw [h1, hQ0img]
    have h2 : (⁅(⊤ : Subgroup ↥(img148 A Y J)), ⊤⁆ : Subgroup ↥(img148 A Y J)) = ⊤ :=
      Group.isPerfect_def.1 hperfJ
    have h3 := congrArg (Subgroup.map (img148 A Y J).subtype) h2
    rw [Subgroup.map_commutator, ← MonoidHom.range_eq_map, Subgroup.range_subtype] at h3
    exact h3
  exact false_of_le_sup_theta hJY e hLa.1 eLa (hRP.trans hPJ) (hRP.trans hPC)
    (hRLa.trans le_sup_left) hRimg

theorem sec13HJPointSection_of (h134 : Item134) (h48 : Sec4.Item4_8) : Sec13HJPointSection :=
  sec13HJPointSection_of_omega (sec13HJPointOmega_of h134 h48)

end CFSG.RankThree.PartTwo.Sec14.Ronan148W
