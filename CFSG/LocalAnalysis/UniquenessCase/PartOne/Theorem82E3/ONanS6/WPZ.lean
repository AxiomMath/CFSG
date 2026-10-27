module

public import CFSG.LieType.BorelTits.Basic
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.Context
public import CFSG.RankThree.PartTwo.Sec6.Item612Basic
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.ONanS6.WS6

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.ONan
section
open CFSG.Open
open CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo.Sec4
open CFSG.RankThree.PartOne (IsStronglyPEmbedded)
open CFSG.LocalAnalysis.UniquenessCase.UC22 (Data IsSpor IsAlt)
open CFSG.ASVolI.ChIJK (IsWeaklyClosedIn)
open CFSG.Blueprint (LieModel)
open scoped commutatorElement Pointwise
variable {G : Type} [Group G] [Finite G]
variable {D : Data G}
variable (c : Ctx82E3 D) {P A : Subgroup G} {a : G}

theorem autThetaQuot_eq_bot_of_forall {Z J : Subgroup G}
    (h : ∀ z ∈ Z, ∀ hz : z ∈ Subgroup.normalizer (J : Set G),
      thetaQuotMulAut J (J.normalizerMonoidHom ⟨z, hz⟩) = 1) :
    autThetaQuot Z J = ⊥ := by
  rw [Subgroup.eq_bot_iff_forall]
  intro τ hτ
  obtain ⟨z, hzN, hzZ, rfl⟩ := mem_autThetaQuot_iff.mp hτ
  exact h z hzZ hzN

theorem card_autThetaQuot_eq_one_of_forall {Z J : Subgroup G}
    (h : ∀ z ∈ Z, ∀ hz : z ∈ Subgroup.normalizer (J : Set G),
      thetaQuotMulAut J (J.normalizerMonoidHom ⟨z, hz⟩) = 1) :
    Nat.card (autThetaQuot Z J) = 1 := by
  rw [autThetaQuot_eq_bot_of_forall h, Subgroup.card_bot]

theorem stronglyEmbedded_seven (c : Ctx82E3 D) (h7 : D.sig = {7}) : IsStronglyPEmbedded 7 D.M := by
  have hnot : ¬ (D.sig2 ∪ D.sig3).Nonempty := fun hne =>
    Ctx82E3.not_isSolvable c (Std82E3.solvable_of (D := D) c.toStd82E3 hne)
  have h7sig : 7 ∈ D.sig := by rw [h7]; exact Set.mem_singleton 7
  have hmem : 7 ∈ D.sig1 := by
    rw [D.sig_sub, Set.mem_union, Set.mem_union] at h7sig
    rcases h7sig with (h | h) | h
    · exact h
    · exact absurd ⟨7, Set.mem_union_left _ h⟩ hnot
    · exact absurd ⟨7, Set.mem_union_right _ h⟩ hnot
  exact Std82E3.sig1_sp (D := D) c.toStd82E3 7 hmem

theorem centralizer_le_M_of_orderOf_seven (c : Ctx82E3 D) (h7 : D.sig = {7}) {y : G}
    (hyM : y ∈ D.M) (hy7 : orderOf y = 7) :
    Subgroup.centralizer ({y} : Set G) ≤ D.M := by
  obtain ⟨-, -, hmain⟩ := stronglyEmbedded_seven (D := D) c h7
  intro g hg
  by_contra hgM
  have hconj : (MulEquiv.toMonoidHom (MulAut.conj g)) y = y := by
    show g * y * g⁻¹ = y
    rw [Subgroup.mem_centralizer_singleton_iff.mp hg]
    group
  have hmem : y ∈ D.M ⊓ D.M.map ((MulAut.conj g).toMonoidHom) := by
    refine ⟨hyM, ?_⟩
    have h := Subgroup.mem_map_of_mem ((MulAut.conj g).toMonoidHom) hyM
    rwa [hconj] at h
  have hdvd : 7 ∣ Nat.card ↥(D.M ⊓ D.M.map ((MulAut.conj g).toMonoidHom)) := by
    rw [← hy7]
    exact (D.M ⊓ D.M.map ((MulAut.conj g).toMonoidHom)).orderOf_dvd_natCard hmem
  exact hmain g hgM hdvd

theorem normalizer_le_M_of_seven (c : Ctx82E3 D) (h7 : D.sig = {7}) {R : Subgroup G}
    (hRM : R ≤ D.M) (hR : IsPGroup 7 R) (hRne : R ≠ ⊥) :
    Subgroup.normalizer (R : Set G) ≤ D.M := by
  obtain ⟨-, -, hmain⟩ := stronglyEmbedded_seven (D := D) c h7
  intro g hg
  by_contra hgM
  have hRmap : R.map ((MulAut.conj g).toMonoidHom) = R :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp hg
  have hle : R ≤ D.M ⊓ D.M.map ((MulAut.conj g).toMonoidHom) := by
    intro r hr
    refine ⟨hRM hr, ?_⟩
    have hr' : r ∈ R.map (MulEquiv.toMonoidHom (MulAut.conj g)) := by
      rw [hRmap]; exact hr
    obtain ⟨s, hsR, hfs⟩ := Subgroup.mem_map.mp hr'
    rw [← hfs]
    exact Subgroup.mem_map_of_mem (MulEquiv.toMonoidHom (MulAut.conj g)) (hRM hsR)
  have hdvd : 7 ∣ Nat.card R := by
    obtain ⟨r, hrR, hr1⟩ : ∃ r ∈ R, r ≠ 1 := by
      by_contra h
      push Not at h
      exact hRne ((Subgroup.eq_bot_iff_forall (H := R)).mpr h)
    haveI : Fact (Nat.Prime 7) := ⟨Nat.prime_seven⟩
    have h7' : 7 ∣ orderOf (⟨r, hrR⟩ : ↥R) :=
      hR.dvd_orderOf (g := (⟨r, hrR⟩ : ↥R)) (by simpa using hr1)
    exact h7'.trans (orderOf_dvd_natCard (⟨r, hrR⟩ : ↥R))
  exact hmain g hgM (hdvd.trans (Subgroup.card_dvd_of_le hle))

theorem eq_inf_sup_theta_of_seven (c : Ctx82E3 D) (h7 : D.sig = {7})
    {J : Subgroup G} {y : G} (hyM : y ∈ D.M) (hy7 : orderOf y = 7)
    (hyC : y ∈ thetaQuotCentralizer J) :
    J = (J ⊓ D.M) ⊔ theta3 J := by
  classical
  haveI : Fact (Nat.Prime 7) := ⟨Nat.prime_seven⟩
  have hy1 : y ≠ 1 := by rintro rfl; rw [orderOf_one] at hy7; norm_num at hy7
  have hyN : y ∈ Subgroup.normalizer (J : Set G) :=
    CFSG.RankThree.PartTwo.Sec6.thetaQuotCentralizer_le_normalizer J hyC
  have hTJ : theta3 J ≤ J := CFSG.RankThree.PartTwo.Sec6.theta_le J
  have hyT : y ∈ Subgroup.normalizer (theta3 J : Set G) :=
    CFSG.RankThree.PartTwo.Sec6.normalizer_le_normalizer_theta J hyN
  have hcomm : ⁅J, Subgroup.zpowers y⁆ ≤ theta3 J :=
    (CFSG.RankThree.PartTwo.Sec6.commutator_le_theta_iff
      (Subgroup.zpowers_le.mpr hyN)).mpr (Subgroup.zpowers_le.mpr hyC)
  set T : Subgroup G := theta3 J with hT
  set X : Subgroup G := T ⊔ Subgroup.zpowers y with hX
  have hTX : T ≤ X := by rw [hX]; exact le_sup_left
  have hyX : y ∈ X := by rw [hX]; exact Subgroup.mem_sup_right (Subgroup.mem_zpowers y)
  have hXmul : (↑X : Set G) = (Subgroup.zpowers y : Set G) * (T : Set G) := by
    rw [hX, sup_comm]
    exact Subgroup.coe_mul_of_left_le_normalizer_right (Subgroup.zpowers y) T
      (Subgroup.zpowers_le.mpr hyT)
  have hconj : ∀ j ∈ J, ∀ x ∈ X, j * x * j⁻¹ ∈ X := by
    intro j hj x hx
    have hx' : x ∈ (Subgroup.zpowers y : Set G) * (T : Set G) := by
      rw [← hXmul]; exact hx
    obtain ⟨w, hw, t, ht, rfl⟩ := Set.mem_mul.mp hx'
    have hjy : j * y * j⁻¹ ∈ X := by
      have hc : ⁅j, y⁆ ∈ T :=
        hcomm (Subgroup.commutator_mem_commutator hj (Subgroup.mem_zpowers y))
      have heq : j * y * j⁻¹ = ⁅j, y⁆ * y := by
        rw [commutatorElement_def]; group
      rw [heq]
      exact X.mul_mem (hTX hc) hyX
    have hw' : j * w * j⁻¹ ∈ X := by
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hw
      have hpow : j * y ^ k * j⁻¹ = (j * y * j⁻¹) ^ k := by
        rw [← MulAut.conj_apply, map_zpow, MulAut.conj_apply]
      rw [hpow]
      exact X.zpow_mem hjy k
    have ht' : j * t * j⁻¹ ∈ T :=
      (Subgroup.mem_normalizer_iff.mp
        (CFSG.RankThree.PartTwo.Sec6.le_normalizer_theta J hj) t).mp ht
    rw [show j * (w * t) * j⁻¹ = (j * w * j⁻¹) * (j * t * j⁻¹) from by group]
    exact X.mul_mem hw' (hTX ht')
  have hJN : J ≤ Subgroup.normalizer (X : Set G) := by
    intro j hj
    rw [Subgroup.mem_normalizer_iff]
    intro x
    exact ⟨fun hx => hconj j hj x hx, fun hx => by
      have h := hconj j⁻¹ (J.inv_mem hj) (j * x * j⁻¹) hx
      have he : j⁻¹ * (j * x * j⁻¹) * j⁻¹⁻¹ = x := by group
      rwa [he] at h⟩
  have hordX : orderOf (⟨y, hyX⟩ : ↥X) = 7 := by
    rw [← Subgroup.orderOf_coe (⟨y, hyX⟩ : ↥X)]
    exact hy7
  obtain ⟨P, hyP⟩ := (IsPGroup.of_card (p := 7) (n := 1) (by
    rw [Nat.card_zpowers, hordX]; norm_num) :
      IsPGroup 7 (Subgroup.zpowers (⟨y, hyX⟩ : ↥X))).exists_le_sylow
  set R' : Subgroup G := (P : Subgroup ↥X).map X.subtype with hR'
  have hR'7 : IsPGroup 7 R' := P.isPGroup'.map X.subtype
  have hyR' : y ∈ R' := by
    have hyPX : (⟨y, hyX⟩ : ↥X) ∈ (P : Subgroup ↥X) := hyP (Subgroup.mem_zpowers _)
    rw [hR']
    exact Subgroup.mem_map_of_mem X.subtype hyPX
  have hR'ne : R' ≠ ⊥ := by
    intro hbot
    rw [hbot] at hyR'
    exact hy1 (by simpa using hyR')
  let ZR : Subgroup G := (Subgroup.center ↥R').map R'.subtype
  have hcenter7 : IsPGroup 7 (Subgroup.center ↥R') :=
    hR'7.of_injective (Subgroup.center ↥R').subtype (Subgroup.subtype_injective _)
  have hZR7 : IsPGroup 7 ZR := hcenter7.map R'.subtype
  have hZR_C : ZR ≤ Subgroup.centralizer ({y} : Set G) := by
    intro z hz
    obtain ⟨z', hz', rfl⟩ := Subgroup.mem_map.mp hz
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hcz := Subgroup.mem_center_iff.mp hz' (⟨y, hyR'⟩ : ↥R')
    exact (congrArg Subtype.val hcz).symm
  have hZR_M : ZR ≤ D.M :=
    hZR_C.trans (centralizer_le_M_of_orderOf_seven c h7 hyM hy7)
  have hZRne : ZR ≠ ⊥ := by
    haveI : Nontrivial ↥R' := (Subgroup.nontrivial_iff_ne_bot R').mpr hR'ne
    intro hbot
    have hc : Subgroup.center ↥R' = ⊥ := by
      have h1 : Subgroup.comap R'.subtype ZR = Subgroup.center ↥R' := by
        show Subgroup.comap R'.subtype ((Subgroup.center ↥R').map R'.subtype) = _
        exact Subgroup.comap_map_eq_self_of_injective (H := Subgroup.center ↥R')
          R'.subtype_injective
      rw [← h1, hbot]
      simp
    exact (ne_of_gt hR'7.bot_lt_center) hc
  have hNZR : Subgroup.normalizer (ZR : Set G) ≤ D.M :=
    normalizer_le_M_of_seven c h7 hZR_M hZR7 hZRne
  have hR'_M : R' ≤ D.M :=
    (Subgroup.le_normalizer.trans
      (CFSG.LieType.BorelTits.normalizer_le_normalizer_map_of_characteristic
        (Subgroup.center ↥R'))).trans hNZR
  have hNR'_M : Subgroup.normalizer (R' : Set G) ≤ D.M :=
    normalizer_le_M_of_seven c h7 hR'_M hR'7 hR'ne
  have hmain : J ≤ (J ⊓ D.M) ⊔ T := by
    intro g hg
    obtain ⟨x, hxX, hx'⟩ :=
      CFSG.RankThree.PartTwo.Sec6.exists_inv_mul_mem_normalizer_sylow P (hJN (J.inv_mem hg))
    have hnM : x⁻¹ * g⁻¹ ∈ D.M := by
      apply hNR'_M
      simpa [R'] using hx'
    have hxX' : x ∈ (Subgroup.zpowers y : Set G) * (T : Set G) := by
      rw [← hXmul]; exact hxX
    obtain ⟨w, hw, t, ht, hxwt⟩ := Set.mem_mul.mp hxX'
    have hwT : w ∈ Subgroup.normalizer (T : Set G) := Subgroup.zpowers_le.mpr hyT hw
    have ht''T : w * t⁻¹ * w⁻¹ ∈ T :=
      (Subgroup.mem_normalizer_iff.mp hwT t⁻¹).mp (T.inv_mem ht)
    have hwR' : w ∈ R' := Subgroup.zpowers_le.mpr hyR' hw
    have hmM : (x⁻¹ * g⁻¹)⁻¹ * w⁻¹ ∈ D.M :=
      D.M.mul_mem (D.M.inv_mem hnM) (hR'_M (R'.inv_mem hwR'))
    have hgeq : g = ((x⁻¹ * g⁻¹)⁻¹ * w⁻¹) * (w * t⁻¹ * w⁻¹) := by
      rw [← hxwt]
      group
    have hmJ : (x⁻¹ * g⁻¹)⁻¹ * w⁻¹ ∈ J := by
      have h2 : g * (w * t⁻¹ * w⁻¹)⁻¹ ∈ J :=
        J.mul_mem hg (J.inv_mem (hTJ ht''T))
      have h3 : g * (w * t⁻¹ * w⁻¹)⁻¹ = (x⁻¹ * g⁻¹)⁻¹ * w⁻¹ := by
        rw [← hxwt]
        group
      rwa [h3] at h2
    rw [hgeq]
    exact ((J ⊓ D.M) ⊔ T).mul_mem
      (Subgroup.mem_sup_left ⟨hmJ, hmM⟩) (Subgroup.mem_sup_right ht''T)
  refine le_antisymm hmain ?_
  rw [hT]
  exact sup_le inf_le_left hTJ

end
end CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.ONan
