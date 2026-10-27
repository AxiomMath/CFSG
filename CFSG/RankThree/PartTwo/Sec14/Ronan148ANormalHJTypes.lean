module

public import CFSG.RankThree.PartTwo.Sec14.Ronan148AHJPoint
import CFSG.RankThree.PartTwo.Sec14.Ronan148WSection
import CFSG.RankThree.PartTwo.Sec14.Ronan148WOrder
import CFSG.RankThree.PartTwo.Sec14.Item148MainProofHyp
public import CFSG.RankThree.PartTwo.Sec14.Ronan148ANormalLeaves

public section

namespace CFSG.RankThree.PartTwo.Sec14.Ronan148A

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.LocalRank CFSG.GH74.GLS Main148 HJRes148

variable {G : Type} [Group G] [Finite G]

section Certificates


@[expose] def Step148NormalHJA5 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
    Sec14Std G A c L → ∀ (Y : Subgroup G) (hY : Y ∈ scriptY A), ¬ Group.IsSolvable ↥Y →
    Ind148 A (lB A) Y → (letI := ker148_normal hY.2; Item148Cases A (lB A) Y) →
    ¬ Case148One A (lB A) Y → ∀ B : Subgroup G, IsHyperplane A B → ¬ YBOne A (lB A) Y B →
    ∀ YB ∈ thetaComponentsIn (Y ⊓ Subgroup.centralizer (B : Set G)),
      (Sec4.IsTripleCover (↥YB ⧸ aschbacherSolvableCore 3 ↥YB) (alternatingGroup (Fin 6)) ∨
        Nonempty (↥YB ⧸ aschbacherSolvableCore 3 ↥YB ≃* alternatingGroup (Fin 5))) →
      deltaZero A (lB A) (Y ⊓ Subgroup.centralizer (B : Set G)) ≤
        pPrimeCoreOf 3 (Y ⊓ Subgroup.centralizer (B : Set G)) ⊔ YB →
      ∀ (b d : G) (Lb : Subgroup G), IsLBConfig A B b d Lb →
      YB ≤ pPrimeCoreOf 3 (Subgroup.centralizer (B : Set G)) ⊔ lB A B →
      letI := ker148_normal hY.2
      ∀ J ∈ thetaComponentsIn Y, YB ≤ J → A ≤ Subgroup.normalizer (J : Set G) →
      ∀ Yd ∈ thetaComponentsIn (Y ⊓ Subgroup.centralizer ({d} : Set G)), YB ≤ Yd → Yd ≤ J →
        A ≤ Subgroup.normalizer (Yd : Set G) →
        YdType148 d Yd → d ∈ Late.sectionCentralizer A J (pPrimeCoreOf 3 Y) →
        img148 A Y Yd = img148 A Y J →
        Nonempty (↥Yd ⧸ aschbacherSolvableCore 3 ↥Yd ≃* ↥(img148 A Y J)) →
        Nonempty (↥(img148 A Y J) ≃* alternatingGroup (Fin 5)) →
        (((deltaZero A (lB A) Y).subgroupOf Y).map
          (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥Y))).Normal

@[expose] def Step148NormalHJA6 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
    Sec14Std G A c L → ∀ (Y : Subgroup G) (hY : Y ∈ scriptY A), ¬ Group.IsSolvable ↥Y →
    Ind148 A (lB A) Y → (letI := ker148_normal hY.2; Item148Cases A (lB A) Y) →
    ¬ Case148One A (lB A) Y → ∀ B : Subgroup G, IsHyperplane A B → ¬ YBOne A (lB A) Y B →
    ∀ YB ∈ thetaComponentsIn (Y ⊓ Subgroup.centralizer (B : Set G)),
      (Sec4.IsTripleCover (↥YB ⧸ aschbacherSolvableCore 3 ↥YB) (alternatingGroup (Fin 6)) ∨
        Nonempty (↥YB ⧸ aschbacherSolvableCore 3 ↥YB ≃* alternatingGroup (Fin 5))) →
      deltaZero A (lB A) (Y ⊓ Subgroup.centralizer (B : Set G)) ≤
        pPrimeCoreOf 3 (Y ⊓ Subgroup.centralizer (B : Set G)) ⊔ YB →
      ∀ (b d : G) (Lb : Subgroup G), IsLBConfig A B b d Lb →
      YB ≤ pPrimeCoreOf 3 (Subgroup.centralizer (B : Set G)) ⊔ lB A B →
      letI := ker148_normal hY.2
      ∀ J ∈ thetaComponentsIn Y, YB ≤ J → A ≤ Subgroup.normalizer (J : Set G) →
      ∀ Yd ∈ thetaComponentsIn (Y ⊓ Subgroup.centralizer ({d} : Set G)), YB ≤ Yd → Yd ≤ J →
        A ≤ Subgroup.normalizer (Yd : Set G) →
        YdType148 d Yd → d ∈ Late.sectionCentralizer A J (pPrimeCoreOf 3 Y) →
        img148 A Y Yd = img148 A Y J →
        Nonempty (↥Yd ⧸ aschbacherSolvableCore 3 ↥Yd ≃* ↥(img148 A Y J)) →
        Sec4.IsTripleCover ↥(img148 A Y J) (alternatingGroup (Fin 6)) →
        (((deltaZero A (lB A) Y).subgroupOf Y).map
          (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥Y))).Normal

@[expose] def Step148NormalHJON : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
    Sec14Std G A c L → ∀ (Y : Subgroup G) (hY : Y ∈ scriptY A), ¬ Group.IsSolvable ↥Y →
    Ind148 A (lB A) Y → (letI := ker148_normal hY.2; Item148Cases A (lB A) Y) →
    ¬ Case148One A (lB A) Y → ∀ B : Subgroup G, IsHyperplane A B → ¬ YBOne A (lB A) Y B →
    ∀ YB ∈ thetaComponentsIn (Y ⊓ Subgroup.centralizer (B : Set G)),
      (Sec4.IsTripleCover (↥YB ⧸ aschbacherSolvableCore 3 ↥YB) (alternatingGroup (Fin 6)) ∨
        Nonempty (↥YB ⧸ aschbacherSolvableCore 3 ↥YB ≃* alternatingGroup (Fin 5))) →
      deltaZero A (lB A) (Y ⊓ Subgroup.centralizer (B : Set G)) ≤
        pPrimeCoreOf 3 (Y ⊓ Subgroup.centralizer (B : Set G)) ⊔ YB →
      ∀ (b d : G) (Lb : Subgroup G), IsLBConfig A B b d Lb →
      YB ≤ pPrimeCoreOf 3 (Subgroup.centralizer (B : Set G)) ⊔ lB A B →
      letI := ker148_normal hY.2
      ∀ J ∈ thetaComponentsIn Y, YB ≤ J → A ≤ Subgroup.normalizer (J : Set G) →
      ∀ Yd ∈ thetaComponentsIn (Y ⊓ Subgroup.centralizer ({d} : Set G)), YB ≤ Yd → Yd ≤ J →
        A ≤ Subgroup.normalizer (Yd : Set G) →
        YdType148 d Yd → d ∈ Late.sectionCentralizer A J (pPrimeCoreOf 3 Y) →
        img148 A Y Yd = img148 A Y J →
        Nonempty (↥Yd ⧸ aschbacherSolvableCore 3 ↥Yd ≃* ↥(img148 A Y J)) →
        Sec4.IsTripleCover ↥(img148 A Y J) CFSG.Blueprint.NativeSporadic.ON → d ∈ Yd →
        (((deltaZero A (lB A) Y).subgroupOf Y).map
          (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥Y))).Normal

theorem jalpha_type_outer148 (hKF : KF148HJA6Outer) (h41 : Sec4.Item4_1LargePrime)
    {A L : Subgroup G} {c : G} (h : Sec14Std G A c L) {Y : Subgroup G} (hY : Y ∈ scriptY A)
    (hs : ¬ Group.IsSolvable ↥Y) {d : G} (hd : d ∈ A) (hd1 : d ≠ 1)
    (hW : Subgroup.normalizer (A : Set G) ≤ Subgroup.normalizer (Subgroup.zpowers d : Set G))
    {Yd J : Subgroup G} (hYd : Yd ∈ thetaComponentsIn (Y ⊓ Subgroup.centralizer ({d} : Set G)))
    (hAYd : A ≤ Subgroup.normalizer (Yd : Set G))
    (hA6 : Sec4.IsTripleCover (↥Yd ⧸ aschbacherSolvableCore 3 ↥Yd) (alternatingGroup (Fin 6)))
    (hθ : ⁅inSubgroup (aschbacherSolvableCore 3) Yd, Yd⁆ ≤ pPrimeCoreOf 3 Y)
    (hJ : J ∈ thetaComponentsIn Y) (hYdJ : Yd ≤ J) (hAJ : A ≤ Subgroup.normalizer (J : Set G))
    (h3J : 3 ∣ Nat.card J) (hdc : d ∉ Late.sectionCentralizer A J (pPrimeCoreOf 3 Y)) :
    letI := ker148_normal hY.2
    Nonempty (↥(img148 A Y J) ≃* CFSG.Blueprint.NativeSporadic.J2) ∨
      Nonempty (↥(img148 A Y J) ≃* CFSG.Blueprint.NativeSporadic.M24) ∨
      Sec4.IsTripleCover ↥(img148 A Y J) CFSG.Blueprint.NativeSporadic.ON := by
  let := ker148_normal hY.2
  have hA : Late.IsE27 A := h.isE27
  have hA3 : ∀ a ∈ A, a ^ 3 = 1 := hA.1.2
  have hd3 : d ^ 3 = 1 := hA3 d hd
  have hJY : J ≤ Y := le_of_mem_thetaComponentsIn hJ
  have hJM : J ≤ Y ⊔ A := hJY.trans le_sup_left
  have h3Yd : 3 ∣ Nat.card Yd := three_dvd_card_of_ydType148 (d := d) (Or.inr (Or.inl hA6))
  obtain ⟨hKle, hKsub, hKp, hKθ, ⟨η⟩⟩ := ydAlpha_facts hY.2 hd hd3 hYd hJ hYdJ hAJ h3Yd hθ
  have : Group.IsPerfect ↥(img148 A Y Yd) := hKp
  have hA6α : Sec4.IsTripleCover (↥(img148 A Y Yd) ⧸ aschbacherSolvableCore 3 ↥(img148 A Y Yd))
      (alternatingGroup (Fin 6)) := KFacts.KS14.isTripleCover_congr η hA6
  have hKq : IsQuasisimple ↥(img148 A Y Yd) := by
    set θ := aschbacherSolvableCore 3 ↥(img148 A Y Yd)
    have hθn : θ.Normal := Subgroup.normal_of_le_center hKθ
    obtain ⟨hZ3, ⟨eT⟩⟩ := hA6α
    have hTp : Group.IsPerfect (↥(img148 A Y Yd) ⧸ θ) :=
      Group.IsPerfect.ofSurjective (QuotientGroup.mk'_surjective θ)
    have hA6s : IsSimpleGroup (alternatingGroup (Fin 6)) :=
      alternatingGroup.isSimpleGroup (by simp)
    have hTs : IsSimpleGroup ((↥(img148 A Y Yd) ⧸ θ) ⧸ Subgroup.center (↥(img148 A Y Yd) ⧸ θ)) :=
      eT.isSimpleGroup
    have hnc : ∃ a b : (↥(img148 A Y Yd) ⧸ θ) ⧸ Subgroup.center (↥(img148 A Y Yd) ⧸ θ),
        a * b ≠ b * a := by
      refine ⟨eT.symm ⟨Equiv.swap 0 1 * Equiv.swap 1 2,
          Equiv.Perm.mem_alternatingGroup.mpr (by decide)⟩,
        eT.symm ⟨Equiv.swap 1 2 * Equiv.swap 2 3,
          Equiv.Perm.mem_alternatingGroup.mpr (by decide)⟩, fun h0 => ?_⟩
      have h1 := congrArg (fun z => ((eT z : alternatingGroup (Fin 6)) : Equiv.Perm (Fin 6))) h0
      simp only [map_mul, MulEquiv.apply_symm_apply, Subgroup.coe_mul] at h1
      revert h1
      decide
    exact (CFSG.LocalCores.isQuasisimple_iff_of_surjective hKp (QuotientGroup.mk' θ)
      (QuotientGroup.mk'_surjective θ) (by rwa [QuotientGroup.ker_mk'])).mpr ⟨hTp, hTs, hnc⟩
  obtain ⟨hJq, hJθ⟩ := img148_isQuasisimple (A := A) (Y := Y) hJ h3J
  obtain ⟨hC4, hCE⟩ := hyp429In148_of h41 G A c L h Y hY hs J hJ hAJ h3J
  have hCeq : img148 A Y (J ⊔ A) = img148 A Y J ⊔ img148 A Y A := img148_sup hJM le_sup_right
  have hAαJα : img148 A Y A ≤ Subgroup.normalizer (img148 A Y J : Set (↥(Y ⊔ A) ⧸ ker148 A Y)) :=
    img148_le_normalizer hAJ
  have hAα3 : ∀ a ∈ img148 A Y A, a ^ 3 = 1 := (img148_isE27 hA).1.2
  have hCθ : aschbacherSolvableCore 3 ↥(img148 A Y (J ⊔ A)) = ⊥ := by
    rw [hCeq]
    exact aschbacherSolvableCore_sup_eq_bot hAαJα hAα3 hJθ
  have hLn : img148 A Y (J ⊔ A) ≤
      Subgroup.normalizer (img148 A Y J : Set (↥(Y ⊔ A) ⧸ ker148 A Y)) := by
    rw [hCeq]
    exact sup_le Subgroup.le_normalizer hAαJα
  have hA3' : IsPGroup 3 A := IsPGroup.of_card (n := 3) (by rw [hA.2]; norm_num)
  have hWα : ∀ g ∈ img148 A Y (J ⊔ A),
      g ∈ Subgroup.normalizer (img148 A Y A : Set (↥(Y ⊔ A) ⧸ ker148 A Y)) →
      g ∈ Subgroup.normalizer
        (Subgroup.zpowers (alpha148 A Y d hd) : Set (↥(Y ⊔ A) ⧸ ker148 A Y)) :=
    fun g _ hg => mem_normalizer_alpha_of hA3' hd hW hg
  have hnc : ¬ img148 A Y J ≤ Subgroup.centralizer {alpha148 A Y d hd} := fun hJc =>
    hdc (mem_sectionCentralizer_of_le_centralizer hJM hd hJc)
  exact hKF _ (img148 A Y (J ⊔ A)) hC4 hCθ hCE (img148 A Y A) (img148 A Y J) (img148 A Y Yd)
    (alpha148 A Y d hd) (img148_isE27 hA) hCeq.symm (alpha148_mem_img148 hd)
    (alpha148_ne_one hd hd1 hd3) hWα hJq hLn hnc hKle hKsub hKq (img148_le_normalizer hAYd)
    hA6α

theorem false_of_m24_outer148
    (h134 : Item134) (h48 : Sec4.Item4_8) {A L : Subgroup G} {c : G} (hS : Sec14Std G A c L)
    {Y : Subgroup G} (hY : Y ∈ scriptY A) (hs : ¬ Group.IsSolvable ↥Y) (ih : Ind148 A (lB A) Y)
    {B : Subgroup G} (hB : IsHyperplane A B) (hnot : ¬ YBOne A (lB A) Y B) {YB : Subgroup G}
    (hYB : YB ∈ thetaComponentsIn (Y ⊓ Subgroup.centralizer (B : Set G)))
    (htype : Sec4.IsTripleCover (↥YB ⧸ aschbacherSolvableCore 3 ↥YB) (alternatingGroup (Fin 6)) ∨
      Nonempty (↥YB ⧸ aschbacherSolvableCore 3 ↥YB ≃* alternatingGroup (Fin 5)))
    (hΔ : deltaZero A (lB A) (Y ⊓ Subgroup.centralizer (B : Set G)) ≤
      pPrimeCoreOf 3 (Y ⊓ Subgroup.centralizer (B : Set G)) ⊔ YB)
    {b d : G} {Lb : Subgroup G} (hc : IsLBConfig A B b d Lb)
    (hle : YB ≤ pPrimeCoreOf 3 (Subgroup.centralizer (B : Set G)) ⊔ lB A B)
    {J : Subgroup G} (hJ : J ∈ thetaComponentsIn Y) (hYBJ : YB ≤ J)
    (hAJ : A ≤ Subgroup.normalizer (J : Set G)) {Yd : Subgroup G}
    (hYd : Yd ∈ thetaComponentsIn (Y ⊓ Subgroup.centralizer ({d} : Set G))) (hYBYd : YB ≤ Yd)
    (hYdJ : Yd ≤ J) (hAYd : A ≤ Subgroup.normalizer (Yd : Set G))
    (hA6 : Sec4.IsTripleCover (↥Yd ⧸ aschbacherSolvableCore 3 ↥Yd) (alternatingGroup (Fin 6)))
    (hθ : ⁅inSubgroup (aschbacherSolvableCore 3) Yd, Yd⁆ ≤ pPrimeCoreOf 3 Y)
    (hW : Subgroup.normalizer (A : Set G) ≤ Subgroup.normalizer (Subgroup.zpowers d : Set G))
    (hdc : d ∉ Late.sectionCentralizer A J (pPrimeCoreOf 3 Y)) :
    letI := ker148_normal hY.2
    Nonempty (↥(img148 A Y J) ≃* CFSG.Blueprint.NativeSporadic.M24) → False := by
  intro hM
  let := ker148_normal hY.2
  obtain ⟨hYB6, hdYB, hbc⟩ := HJRes2.outer_facts hS hB hc hYB htype hle hYd hYBYd hAYd hA6
  have hA : Late.IsE27 A := hS.isE27
  have hA3 : ∀ a ∈ A, a ^ 3 = 1 := hA.1.2
  obtain ⟨hbB, hdB, -, hd1, -⟩ := lbConfig_points hB hA.2 hc
  have hdA : d ∈ A := hB.1 hdB
  have hdYd : d ∈ Yd := hYBYd hdYB
  have hJY : J ≤ Y := le_of_mem_thetaComponentsIn hJ
  have hAY : A ≤ Subgroup.normalizer (Y : Set G) := hY.2
  obtain ⟨e⟩ := hM
  obtain ⟨n, haC⟩ :=
    CFSG.AGLEmbeddingD2.Wilson.MaximalityAmbient.Step148M24.exists_sectionCentralizer_of_m24
      hS.mem_partTwoF hAY hJ hAJ hdA hd1 hYd hYdJ hAYd hdYd hA6 hθ hbc e
  set a := b * (d ^ n)⁻¹ with ha
  have haB : a ∈ B := B.mul_mem hbB (B.inv_mem (B.pow_mem hdB n))
  have haA : a ∈ A := hB.1 haB
  have ha3 : a ^ 3 = 1 := hA3 a haA
  have ha1 : a ≠ 1 := by
    intro h1
    have hbd : b = d ^ n := by
      calc b = (b * (d ^ n)⁻¹) * d ^ n := by group
        _ = d ^ n := by rw [← ha, h1, one_mul]
    have hBle : B ≤ Subgroup.zpowers d := by
      rw [hc.1, Subgroup.closure_le]
      rintro z (rfl | hz)
      · rw [hbd]
        exact Subgroup.pow_mem _ (Subgroup.mem_zpowers d) n
      · rw [Set.mem_singleton_iff.mp hz]
        exact Subgroup.mem_zpowers d
    have hz3 : Nat.card (Subgroup.zpowers d) ≤ 3 := by
      rw [Nat.card_zpowers]
      exact Nat.le_of_dvd (by norm_num) (orderOf_dvd_of_pow_eq_one (hA3 d hdA))
    have h9 : 3 * Nat.card B = 27 := by rw [← hB.2, hA.2]
    have := Subgroup.card_le_of_le hBle
    omega
  obtain ⟨-, La, hLa, eLa⟩ := Ronan148W.sec13HJPointOmega_of h134 h48 G A c L hS Y hY hs ih B hB
    hnot YB hYB htype hΔ b d Lb hc hle J hJ hYBJ hAJ Yd hYd hYBYd hYdJ hAYd hA6 hθ hW hdc hYB6
    hdYB hbc ⟨e⟩ a haB ha1 ha3 haC
  have hcomm : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hA.1.1.is_comm.comm (⟨x, hx⟩ : ↥A) ⟨y, hy⟩)
  set Cja : Subgroup G := J ⊓ Subgroup.centralizer ({a} : Set G) with hCja
  have hCjaYA : Cja ≤ Y ⊔ A := (inf_le_left.trans hJY).trans le_sup_left
  have himg1 : img148 A Y Cja = img148 A Y J :=
    CFSG.AGLEmbeddingD2.Wilson.MaximalityAmbient.Step148M24.img148_inf_centralizer_eq hAY hAJ hJY
      ha3 haC
  have h3J : 3 ∣ Nat.card J :=
    (three_dvd_card_of_ydType148 (d := d) (Or.inr (Or.inl hA6))).trans
      (Subgroup.card_dvd_of_le hYdJ)
  have hperfC : Group.IsPerfect ↥(img148 A Y Cja) := by
    rw [himg1]
    exact (img148_isQuasisimple (A := A) (Y := Y) hJ h3J).1.1
  set P : Subgroup G := inSubgroup perfectResidual Cja with hPdef
  have himgP : img148 A Y P = img148 A Y J :=
    (CFSG.AGLEmbeddingD2.Wilson.MaximalityAmbient.Step148M24.img148_perfectResidual_eq hCjaYA
      hperfC).trans himg1
  have hPle : P ≤ J ⊓ Subgroup.centralizer ({a} : Set G) := Subgroup.map_subtype_le _
  have hACja : A ≤ Subgroup.normalizer (Cja : Set G) := by
    intro x hx
    rw [Subgroup.mem_normalizer_iff]
    intro h
    simp only [hCja, SetLike.mem_coe, Subgroup.mem_inf, Subgroup.mem_centralizer_singleton_iff]
    exact and_congr (Subgroup.mem_normalizer_iff.mp (hAJ hx) h)
      (Iff.symm (CFSG.AGLEmbeddingD2.Wilson.MaximalityAmbient.Step148M24.conj_mul_comm_iff
        (hcomm x hx a haA)))
  have hAP : A ≤ Subgroup.normalizer (P : Set G) :=
    CFSG.AGLEmbeddingD2.Wilson.MaximalityAmbient.Step148M24.le_normalizer_inSubgroup_perfectResidual
      hACja
  have hPperf : Group.IsPerfect ↥P := by
    have hperf := (perfect_residual_characterization (G := ↥Cja)).2.2.1
    exact Group.IsPerfect.map Cja.subtype
  have hPsub := Ronan148W.sec13HJPointSection_of h134 h48 G A c L hS Y hY hs ih B hB hnot YB hYB
    htype hΔ b d Lb hc hle J hJ hYBJ hAJ Yd hYd hYBYd hYdJ hAYd hA6 hθ hW hdc hYB6 hdYB hbc ⟨e⟩
    a haB ha1 ha3 haC La hLa eLa P hPle hAP hPperf himgP
  exact Ronan148W.false_of_le_sup_theta hJY e hLa.1 eLa (hPle.trans inf_le_left)
    (hPle.trans inf_le_right) hPsub himgP

theorem false_of_on_outer148
    {A L : Subgroup G} {c : G} (hS : Sec14Std G A c L) {Y : Subgroup G} (hY : Y ∈ scriptY A)
    {B : Subgroup G} (hB : IsHyperplane A B) {YB : Subgroup G}
    (hYB : YB ∈ thetaComponentsIn (Y ⊓ Subgroup.centralizer (B : Set G)))
    (htype : Sec4.IsTripleCover (↥YB ⧸ aschbacherSolvableCore 3 ↥YB) (alternatingGroup (Fin 6)) ∨
      Nonempty (↥YB ⧸ aschbacherSolvableCore 3 ↥YB ≃* alternatingGroup (Fin 5)))
    {b d : G} {Lb : Subgroup G} (hc : IsLBConfig A B b d Lb)
    (hle : YB ≤ pPrimeCoreOf 3 (Subgroup.centralizer (B : Set G)) ⊔ lB A B)
    {J : Subgroup G} (hJ : J ∈ thetaComponentsIn Y) (hAJ : A ≤ Subgroup.normalizer (J : Set G))
    {Yd : Subgroup G} (hYd : Yd ∈ thetaComponentsIn (Y ⊓ Subgroup.centralizer ({d} : Set G)))
    (hYBYd : YB ≤ Yd) (hYdJ : Yd ≤ J) (hAYd : A ≤ Subgroup.normalizer (Yd : Set G))
    (hA6 : Sec4.IsTripleCover (↥Yd ⧸ aschbacherSolvableCore 3 ↥Yd) (alternatingGroup (Fin 6)))
    (hθ : ⁅inSubgroup (aschbacherSolvableCore 3) Yd, Yd⁆ ≤ pPrimeCoreOf 3 Y)
    (hdc : d ∉ Late.sectionCentralizer A J (pPrimeCoreOf 3 Y)) :
    letI := ker148_normal hY.2
    Sec4.IsTripleCover ↥(img148 A Y J) CFSG.Blueprint.NativeSporadic.ON → False := by
  intro hON
  let := ker148_normal hY.2
  have hA : Late.IsE27 A := hS.isE27
  obtain ⟨-, hdB, -, -, -⟩ := lbConfig_points hB hA.2 hc
  have hd : d ∈ A := hB.1 hdB
  have hd3 : d ^ 3 = 1 := hA.1.2 d hd
  obtain ⟨-, hdYB, -⟩ := HJRes2.outer_facts hS hB hc hYB htype hle hYd hYBYd hAYd hA6
  have hdYd : d ∈ Yd := hYBYd hdYB
  have hJM : J ≤ Y ⊔ A := (le_of_mem_thetaComponentsIn hJ).trans le_sup_left
  have h3Yd : 3 ∣ Nat.card Yd := three_dvd_card_of_ydType148 (d := d) (Or.inr (Or.inl hA6))
  have h3J : 3 ∣ Nat.card J := h3Yd.trans (Subgroup.card_dvd_of_le hYdJ)
  obtain ⟨hJq, -⟩ := img148_isQuasisimple (A := A) (Y := Y) hJ h3J
  obtain ⟨hKle, -, hKp, -, -⟩ := ydAlpha_facts hY.2 hd hd3 hYd hJ hYdJ hAJ h3Yd hθ
  have hdα : alpha148 A Y d hd ∈ img148 A Y Yd :=
    mem_img148_iff.mpr ⟨d, Subgroup.mem_sup_right hd, hdYd, rfl⟩
  set X := img148 A Y J with hX
  set g : ↥X := ⟨alpha148 A Y d hd, (hKle hdα).1⟩ with hg
  set K := (img148 A Y Yd).subgroupOf X with hK
  have hKX : img148 A Y Yd ≤ X := hKle.trans inf_le_left
  refine HJRes2.not_mem_of_isPerfect_of_isTripleCover hJq.1 hON (g := g) ?_ ?_ (K := K) ?_ ?_ ?_
  · apply Subtype.ext
    rw [Subgroup.coe_pow, hg, ← alpha148_pow hd 3]
    simp only [hd3, Subgroup.coe_one]
    rw [alpha148_eq_mk']
    exact (QuotientGroup.eq_one_iff _).mpr (Subgroup.one_mem _)
  · intro hgc
    apply hdc
    refine mem_sectionCentralizer_of_le_centralizer hJM hd fun x hx => ?_
    rw [Subgroup.mem_centralizer_singleton_iff]
    have := Subgroup.mem_center_iff.mp hgc ⟨x, hx⟩
    exact congrArg Subtype.val this
  · have e : ↥K ≃* ↥(img148 A Y Yd) := Subgroup.subgroupOfEquivOfLe hKX
    exact Group.IsPerfect.ofSurjective (f := e.symm.toMonoidHom) e.symm.surjective
  · intro k hk
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hk' : (k : ↥(Y ⊔ A) ⧸ ker148 A Y) ∈ Subgroup.centralizer {alpha148 A Y d hd} :=
      (hKle (Subgroup.mem_subgroupOf.mp hk)).2
    exact Subtype.ext (Subgroup.mem_centralizer_singleton_iff.mp hk')
  · exact Subgroup.mem_subgroupOf.mpr hdα

theorem step148NormalHJ_of_types
    (h45 : Sec4.Item4_5) (h48 : Sec4.Item4_8) (h134 : Item134) (h427 : Sec4.Item4_27)
    (hGW : Sec6.GWLBalanceStatement) (h41 : Sec4.Item4_1LargePrime) (hTYd : Step148HJTypeYd)
    (hKF : KF148HJA6Outer) (hHJ : Step148NormalHJHJ) (hA5 : Step148NormalHJA5)
    (hA6 : Step148NormalHJA6) (hON : Step148NormalHJON) : Step148NormalHJ := by
  intro G _ _ A c L hS Y hY hs ih hcases h1 B hB hnot YB hYB htype hΔ b d Lb hc hle
  let := ker148_normal hY.2
  have hA : Late.IsE27 A := hS.isE27
  obtain ⟨-, hdB, -, hd1, -⟩ := lbConfig_points hB hA.2 hc
  have hdA : d ∈ A := hB.1 hdB
  obtain ⟨Yd₀, -, hYBYd₀, -, J, hJ, hYdJ₀, hAJ⟩ := exists_yd_j148 h45 h48 hS hY hB hYB hc
  have hYBJ : YB ≤ J := hYBYd₀.trans hYdJ₀
  obtain ⟨Yd, hYd, hYBYd, hYdJ, hAYd, hYdt, h3J, hcase⟩ :=
    jalpha_config h45 h48 h134 h427 hGW h41 hTYd hS hY hs ih hB hnot hYB htype hΔ hc hle hJ hYBJ
      hAJ
  rcases hcase with ⟨hdc, heq, ⟨η⟩⟩ | ⟨hdc, hA6Yd, hθ, hW⟩
  ·
    rcases hYdt with hY5 | hY6 | ⟨hdYd, hYON⟩
    · obtain ⟨χ⟩ := hY5
      exact hA5 G A c L hS Y hY hs ih hcases h1 B hB hnot YB hYB htype hΔ b d Lb hc hle J hJ hYBJ
        hAJ Yd hYd hYBYd hYdJ hAYd (Or.inl ⟨χ⟩) hdc heq ⟨η⟩ ⟨η.symm.trans χ⟩
    · exact hA6 G A c L hS Y hY hs ih hcases h1 B hB hnot YB hYB htype hΔ b d Lb hc hle J hJ hYBJ
        hAJ Yd hYd hYBYd hYdJ hAYd (Or.inr (Or.inl hY6)) hdc heq ⟨η⟩
        (KFacts.KS14.isTripleCover_congr η hY6)
    · exact hON G A c L hS Y hY hs ih hcases h1 B hB hnot YB hYB htype hΔ b d Lb hc hle J hJ hYBJ
        hAJ Yd hYd hYBYd hYdJ hAYd (Or.inr (Or.inr ⟨hdYd, hYON⟩)) hdc heq ⟨η⟩
        (KFacts.KS14.isTripleCover_congr η hYON) hdYd
  ·
    rcases jalpha_type_outer148 hKF h41 hS hY hs hdA hd1 hW hYd hAYd hA6Yd hθ hJ hYdJ hAJ h3J
      hdc with hJ2 | hM | hJON
    · exact hHJ G A c L hS Y hY hs ih hcases h1 B hB hnot YB hYB htype hΔ b d Lb hc hle J hJ hYBJ
        hAJ Yd hYd hYBYd hYdJ hAYd hA6Yd hθ hW hdc hJ2
    · exact (false_of_m24_outer148 h134 h48 hS hY hs ih hB hnot hYB htype hΔ hc hle hJ hYBJ hAJ
        hYd hYBYd hYdJ hAYd hA6Yd hθ hW hdc hM).elim
    · exact (false_of_on_outer148 hS hY hB hYB htype hc hle hJ hAJ hYd hYBYd hYdJ hAYd hA6Yd hθ
        hdc hJON).elim

theorem step148NormalHJ_of_leaves
    (h142 : Concl142S14) (h45 : Sec4.Item4_5) (h48 : Sec4.Item4_8) (h134 : Item134)
    (h427 : Sec4.Item4_27) (hGW : Sec6.GWLBalanceStatement) (h41 : Sec4.Item4_1LargePrime)
    (hTYd : Step148HJTypeYd) (hKF : KF148HJA6Outer) (hP1 : Step148HJCentPoint1)
    (hA5 : Step148NormalHJA5) (hA6 : Step148NormalHJA6) (hON : Step148NormalHJON) :
    Step148NormalHJ :=
  step148NormalHJ_of_types h45 h48 h134 h427 hGW h41 hTYd hKF
    (step148NormalHJHJ_of_point1 h142 h134 h48 hP1) hA5 hA6 hON

theorem step148NormalHJA5_of_normalHJ (hN : Step148NormalHJ) : Step148NormalHJA5 :=
  fun G _ _ A c L hS Y hY hs ih hcases h1 B hB hnot YB hYB htype hΔ b d Lb hc hle _ _ _ _ _ _ _ _
    _ _ _ _ _ _ => hN G A c L hS Y hY hs ih hcases h1 B hB hnot YB hYB htype hΔ b d Lb hc hle

theorem step148NormalHJA6_of_normalHJ (hN : Step148NormalHJ) : Step148NormalHJA6 :=
  fun G _ _ A c L hS Y hY hs ih hcases h1 B hB hnot YB hYB htype hΔ b d Lb hc hle _ _ _ _ _ _ _ _
    _ _ _ _ _ _ => hN G A c L hS Y hY hs ih hcases h1 B hB hnot YB hYB htype hΔ b d Lb hc hle

theorem step148NormalHJON_of_normalHJ (hN : Step148NormalHJ) : Step148NormalHJON :=
  fun G _ _ A c L hS Y hY hs ih hcases h1 B hB hnot YB hYB htype hΔ b d Lb hc hle _ _ _ _ _ _ _ _
    _ _ _ _ _ _ _ => hN G A c L hS Y hY hs ih hcases h1 B hB hnot YB hYB htype hΔ b d Lb hc hle

end Certificates

end CFSG.RankThree.PartTwo.Sec14.Ronan148A
