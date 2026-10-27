module

public import CFSG.RankThree.PartTwo.Sec14.Ronan148ANormalHJ
import CFSG.RankThree.PartTwo.Sec14.Ronan148WOmega134
public import CFSG.RankThree.PartTwo.Sec14.Item148StepOne

public section

namespace CFSG.RankThree.PartTwo.Sec14.Ronan148A

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.LocalRank CFSG.GH74.GLS Ronan148M Main148
  Ronan148J

variable {G : Type} [Group G] [Finite G]

theorem exists_sectionCentralizer_of_j2
    {A Y J Yd : Subgroup G} [(ker148 A Y).Normal] (hAF : A ∈ partTwoF G)
    (hAY : A ≤ Subgroup.normalizer (Y : Set G)) (hJ : J ∈ thetaComponentsIn Y)
    (hAJ : A ≤ Subgroup.normalizer (J : Set G)) {d : G} (hd : d ∈ A)
    (hYd : Yd ∈ thetaComponentsIn (Y ⊓ Subgroup.centralizer ({d} : Set G))) (hYdJ : Yd ≤ J)
    (hdYd : d ∈ Yd)
    (hA6 : Sec4.IsTripleCover (↥Yd ⧸ aschbacherSolvableCore 3 ↥Yd) (alternatingGroup (Fin 6)))
    (hθ : ⁅inSubgroup (aschbacherSolvableCore 3) Yd, Yd⁆ ≤ pPrimeCoreOf 3 Y)
    (hdc : d ∉ Late.sectionCentralizer A J (pPrimeCoreOf 3 Y)) {b : G}
    (hb : b ∈ Late.sectionCentralizer A Yd (inSubgroup (aschbacherSolvableCore 3) Yd))
    (φ : ↥(img148 A Y J) ≃* CFSG.Blueprint.NativeSporadic.J2) :
    ∃ n : ℕ, b * (d ^ n)⁻¹ ∈ Late.sectionCentralizer A J (pPrimeCoreOf 3 Y) := by
  have hA3 : ∀ a ∈ A, a ^ 3 = 1 := hAF.1.2
  have hJY : J ≤ Y := le_of_mem_thetaComponentsIn hJ
  have hJM : J ≤ Y ⊔ A := hJY.trans le_sup_left
  have hYdM : Yd ≤ Y ⊔ A := hYdJ.trans hJM
  have hbA : b ∈ A := hb.1
  have hd3 : d ^ 3 = 1 := hA3 d hd
  set dα := alpha148 A Y d hd with hdαdef
  have hdα3 : dα ^ 3 = 1 := alpha148_pow_three hA3 hd
  have hdα1 : dα ≠ 1 := by
    intro h
    apply hdc
    refine HJRes148.mem_sectionCentralizer_of_le_centralizer hJM hd fun x _ => ?_
    rw [Subgroup.mem_centralizer_singleton_iff, ← hdαdef, h, one_mul, mul_one]
  obtain ⟨hYdeq, -, -, hYdZ, hYdθ⟩ :=
    img148_yd_facts_of_j2 hAY hd hd3 hYd hJ hYdJ hAJ hA6 hθ φ hdYd hdα1 hdα3
  have hdαYd : dα ∈ img148 A Y Yd :=
    mem_img148_iff.mpr ⟨d, Subgroup.mem_sup_right hd, hdYd, rfl⟩
  set β := alpha148 A Y b hbA with hβ
  have hbYd : img148 A Y Yd ≤ Subgroup.centralizer {β} :=
    HJRes2.le_centralizer_of_theta hYdM rfl hYdθ hbA hb.2
  have hβJ : β ∈ Subgroup.normalizer (img148 A Y J : Set (↥(Y ⊔ A) ⧸ ker148 A Y)) :=
    img148_le_normalizer hAJ (alpha148_mem_img148 hbA)
  obtain ⟨u, huJ, hu⟩ := exists_inner_of_j2 φ hβJ (alpha148_pow_three hA3 hbA)
  have huc : ∀ y ∈ img148 A Y Yd, u * y = y * u := by
    intro y hy
    have h1 := hu y (img148_mono hYdJ hy)
    have h2 : β * y * β⁻¹ = y := by
      rw [← Subgroup.mem_centralizer_singleton_iff.mp (hbYd hy), mul_inv_cancel_right]
    rw [h2] at h1
    calc u * y = u * y * u⁻¹ * u := by group
      _ = y * u := by rw [← h1]
  have huYd : u ∈ img148 A Y Yd := by
    rw [hYdeq]
    exact ⟨huJ, Subgroup.mem_centralizer_singleton_iff.mpr (huc dα hdαYd)⟩
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp (hYdZ u huYd huc)
  have hord : orderOf dα = 3 := orderOf_eq_prime hdα3 hdα1
  set n : ℕ := (k % 3).toNat with hn
  have hun : dα ^ n = u := by
    have h3 : dα ^ (k % (orderOf dα : ℤ)) = dα ^ k := zpow_mod_orderOf dα k
    rw [hord] at h3
    rw [← hk, ← h3, ← zpow_natCast]
    congr 1
    exact Int.toNat_of_nonneg (Int.emod_nonneg _ (by norm_num))
  have huA : d ^ n ∈ A := A.pow_mem hd n
  have hu' : alpha148 A Y (d ^ n) huA = u := by
    rw [alpha148_pow hd n, ← hdαdef, hun]
  refine ⟨n, A.mul_mem hbA (A.inv_mem huA), fun g hg => ?_⟩
  have hgM : g ∈ Y ⊔ A := hJM hg
  set gb := QuotientGroup.mk' (ker148 A Y) (⟨g, hgM⟩ : ↥(Y ⊔ A)) with hgbdef
  have hgb : gb ∈ img148 A Y J := mem_img148_iff.mpr ⟨g, hgM, hg, rfl⟩
  have hmem : (b * (d ^ n)⁻¹) * g * (b * (d ^ n)⁻¹)⁻¹ * g⁻¹ ∈ Y ⊔ A :=
    (Y ⊔ A).mul_mem ((Y ⊔ A).mul_mem ((Y ⊔ A).mul_mem (Subgroup.mem_sup_right
      (A.mul_mem hbA (A.inv_mem huA))) hgM) ((Y ⊔ A).inv_mem (Subgroup.mem_sup_right
      (A.mul_mem hbA (A.inv_mem huA))))) ((Y ⊔ A).inv_mem hgM)
  refine (mk'_ker148_eq_one_iff (g := ⟨_, hmem⟩)).mp ?_
  have e1 : QuotientGroup.mk' (ker148 A Y) (⟨_, hmem⟩ : ↥(Y ⊔ A)) =
      (β * u⁻¹) * gb * (β * u⁻¹)⁻¹ * gb⁻¹ := by
    rw [← hu', ← alpha148_inv huA, hβ, ← alpha148_mul hbA (A.inv_mem huA), alpha148_eq_mk']
    rw [← map_inv, ← map_mul, ← map_inv, ← map_mul, ← map_mul]
    rfl
  have hug : u⁻¹ * gb * u ∈ img148 A Y J :=
    (img148 A Y J).mul_mem ((img148 A Y J).mul_mem ((img148 A Y J).inv_mem huJ) hgb) huJ
  rw [e1]
  calc (β * u⁻¹) * gb * (β * u⁻¹)⁻¹ * gb⁻¹
      = β * (u⁻¹ * gb * u) * β⁻¹ * gb⁻¹ := by group
    _ = u * (u⁻¹ * gb * u) * u⁻¹ * gb⁻¹ := by rw [hu _ hug]
    _ = 1 := by group

section Certificates

@[expose] def Step148HJCentPoint1 : Prop :=
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
        Sec4.IsTripleCover (↥Yd ⧸ aschbacherSolvableCore 3 ↥Yd) (alternatingGroup (Fin 6)) →
        ⁅inSubgroup (aschbacherSolvableCore 3) Yd, Yd⁆ ≤ pPrimeCoreOf 3 Y →
        Subgroup.normalizer (A : Set G) ≤ Subgroup.normalizer (Subgroup.zpowers d : Set G) →
        d ∉ Late.sectionCentralizer A J (pPrimeCoreOf 3 Y) →
        Nonempty (↥(img148 A Y J) ≃* CFSG.Blueprint.NativeSporadic.J2) →
        omegaA A = {Subgroup.zpowers b} →
        b ∈ Late.sectionCentralizer A J (pPrimeCoreOf 3 Y)

theorem mem_sectionCentralizer_of_zpowers_eq {A Y J : Subgroup G} [(ker148 A Y).Normal]
    (hJM : J ≤ Y ⊔ A) {a b : G} (haA : a ∈ A) (hbA : b ∈ A)
    (hab : Subgroup.zpowers a = Subgroup.zpowers b)
    (hac : a ∈ Late.sectionCentralizer A J (pPrimeCoreOf 3 Y)) :
    b ∈ Late.sectionCentralizer A J (pPrimeCoreOf 3 Y) := by
  have haJ := HJRes2.le_centralizer_of_mem_sectionCentralizer (A := A) (Y := Y) haA hac
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp (hab ▸ Subgroup.mem_zpowers b : b ∈
    Subgroup.zpowers a)
  refine HJRes148.mem_sectionCentralizer_of_le_centralizer hJM hbA fun x hx => ?_
  have hxa := Subgroup.mem_centralizer_singleton_iff.mp (haJ hx)
  rw [Subgroup.mem_centralizer_singleton_iff]
  have hb : alpha148 A Y b hbA = alpha148 A Y a haA ^ k := by
    rw [alpha148_eq_mk', alpha148_eq_mk', ← map_zpow]
    congr 1
    exact Subtype.ext (by simp [hk])
  rw [hb]
  exact (Commute.zpow_right (show Commute x (alpha148 A Y a haA) from hxa) k).eq

theorem step148HJCentPoint_of
    (h134 : Item134)
    (h48 : Sec4.Item4_8) (hP1 : Step148HJCentPoint1) : Step148HJCentPoint := by
  intro G _ _ A c L hS Y hY hs ih hcases h1 B hB hnot YB hYB htype hΔ b d Lb hc hle J hJ hYBJ hAJ
    Yd hYd hYBYd hYdJ hAYd hA6 hθ hW hdc hJ2 hbJ
  let := ker148_normal hY.2
  obtain ⟨-, hdYB, hbc⟩ := HJRes2.outer_facts hS hB hc hYB htype hle hYd hYBYd hAYd hA6
  have hA : Late.IsE27 A := hS.isE27
  obtain ⟨-, hdB, -, -, -⟩ := lbConfig_points hB hA.2 hc
  have hdA : d ∈ A := hB.1 hdB
  obtain ⟨φ⟩ := hJ2
  rcases Ronan148W.omega_cases_of_lbConfig h134 h48 hS hB hc with hΩ | ⟨hΩ, -⟩
  · exact absurd (hP1 G A c L hS Y hY hs ih hcases h1 B hB hnot YB hYB htype hΔ b d Lb hc hle J
      hJ hYBJ hAJ Yd hYd hYBYd hYdJ hAYd hA6 hθ hW hdc ⟨φ⟩ hΩ) hbJ
  · obtain ⟨n, hn⟩ := exists_sectionCentralizer_of_j2 hS.mem_partTwoF hY.2 hJ hAJ hdA hYd hYdJ
      (hYBYd hdYB) hA6 hθ hdc hbc φ
    exact ⟨_, hn.1, hΩ _ (Subgroup.inv_mem _ (Subgroup.pow_mem _ (Subgroup.mem_zpowers d) n)), hn⟩

theorem step148NormalHJHJ_of_point1
    (h142 : Concl142S14)
    (h134 : Item134) (h48 : Sec4.Item4_8) (hP1 : Step148HJCentPoint1) : Step148NormalHJHJ :=
  step148NormalHJHJ_of_point h142 h134 h48 (step148HJCentPoint_of h134 h48 hP1)

end Certificates

end CFSG.RankThree.PartTwo.Sec14.Ronan148A
