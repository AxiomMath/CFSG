module

public import CFSG.RankThree.PartTwo.Sec14.Ronan148WM24Act
import CFSG.RankThree.PartTwo.Sec14.Ronan148WGroup
import CFSG.RankThree.PartTwo.Sec15.Item152ResProofW
import CFSG.RankThree.PartTwo.Sec13.Item137Tools
import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.MaximalityAmbient.Step148M24
public import CFSG.RankThree.PartTwo.Sec14.Concrete
public import CFSG.RankThree.PartTwo.Sec14.Item148StepQuot

public section

namespace CFSG.RankThree.PartTwo.Sec14.Ronan148W

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.LocalRank CFSG.GH74.GLS CFSG.RankThree.PartTwo.Sec14
  CFSG.RankThree.PartTwo.Sec14.Main148 CFSG.Blueprint

variable {G : Type} [Group G] [Finite G]


theorem zpowers_eq_of_omegaA_eq_singleton {A L : Subgroup G} {c : G} (hS : Sec14Std G A c L)
    {Y : Subgroup G} (hAY : A ≤ Subgroup.normalizer (Y : Set G)) [(ker148 A Y).Normal]
    {B : Subgroup G} (hB : IsHyperplane A B) {b d : G} {Lb : Subgroup G}
    (hc : IsLBConfig A B b d Lb)
    {J : Subgroup G} (hJ : J ∈ thetaComponentsIn Y) (hAJ : A ≤ Subgroup.normalizer (J : Set G))
    {Yd : Subgroup G} (hYd : Yd ∈ thetaComponentsIn (Y ⊓ Subgroup.centralizer ({d} : Set G)))
    (hYdJ : Yd ≤ J)
    (hA6 : Sec4.IsTripleCover (↥Yd ⧸ aschbacherSolvableCore 3 ↥Yd) (alternatingGroup (Fin 6)))
    (hθ : ⁅inSubgroup (aschbacherSolvableCore 3) Yd, Yd⁆ ≤ pPrimeCoreOf 3 Y)
    (hdc : d ∉ Late.sectionCentralizer A J (pPrimeCoreOf 3 Y)) (hdYd : d ∈ Yd)
    (e : ↥(img148 A Y J) ≃* NativeSporadic.M24)
    (hΩ1 : omegaA A = {Subgroup.zpowers b}) {a : G} (haB : a ∈ B) (ha1 : a ≠ 1)
    (haC : a ∈ Late.sectionCentralizer A J (pPrimeCoreOf 3 Y)) :
    Subgroup.zpowers a = Subgroup.zpowers b := by
  have hA : Late.IsE27 A := hS.isE27
  have hA3 : ∀ x ∈ A, x ^ 3 = 1 := hA.1.2
  obtain ⟨hbB, hdB, hb1, hd1, -⟩ := lbConfig_points hB hA.2 hc
  have hdA : d ∈ A := hB.1 hdB
  have hbA : b ∈ A := hB.1 hbB
  have haA : a ∈ A := hB.1 haB
  have hAN : A ≤ Subgroup.normalizer (pPrimeCoreOf 3 Y : Set G) :=
    hAY.trans (normalizer_le_normalizer_pPrimeCoreOf 3 Y)
  have hWb : Subgroup.normalizer (A : Set G) ≤
      Subgroup.normalizer (Subgroup.zpowers b : Set G) := by
    have hbΩ : Subgroup.zpowers b ∈ omegaA A := by
      rw [hΩ1]
      exact Set.mem_singleton _
    intro w hw
    have h2 : (Subgroup.zpowers b).map (MulAut.conj w).toMonoidHom ∈ omegaA A :=
      (map_conj_mem_omegaA_iff hw).mpr hbΩ
    rw [hΩ1, Set.mem_singleton_iff] at h2
    exact Subgroup.mem_normalizer_iff_map_conj_eq.mpr h2
  have haS : a ∈ sectionCentralizerSubgroup148 A J (pPrimeCoreOf 3 Y) hAJ hAN := haC
  have hda : d ∉ Subgroup.zpowers a := fun h => hdc ((Subgroup.zpowers_le.mpr haS) h)
  have had : a ∉ Subgroup.zpowers d := Sec15.Proof152ResW.not_mem_zpowers_symm hA ha1 hdA hda
  have hB9 : Nat.card B = 9 := by
    have h27 : Nat.card A = 27 := hA.2
    have h9 : 3 * Nat.card B = 27 := by rw [← hB.2, h27]
    omega
  have hBad : Subgroup.zpowers a ⊔ Subgroup.zpowers d = B :=
    Subgroup.eq_of_le_of_card_ge
      (sup_le (Subgroup.zpowers_le.mpr haB) (Subgroup.zpowers_le.mpr hdB))
      (by rw [hB9, Sec15.Proof152ResW.card_sup_eq_nine hA haA ha1 hdA hd1 hda])
  have hd3 : Nat.card (Subgroup.zpowers d) = 3 :=
    Sec13.card_zpowers_of_pow_three (hA3 d hdA) hd1
  have hb3 : Nat.card (Subgroup.zpowers b) = 3 := Sec13.card_zpowers_of_pow_three (hA3 b hbA) hb1
  have hbd : Subgroup.zpowers b ≠ Subgroup.zpowers d := by
    intro h
    have hBle : B ≤ Subgroup.zpowers d := by
      rw [hc.1, Subgroup.closure_le]
      intro z hz
      rcases hz with rfl | hz
      · exact h ▸ Subgroup.mem_zpowers z
      · rw [Set.mem_singleton_iff] at hz
        rw [hz]
        exact Subgroup.mem_zpowers d
    have := Subgroup.card_le_of_le hBle
    rw [hB9, hd3] at this
    omega
  obtain ⟨f, hf, hbf⟩ := Sec15.Proof152ResW.exists_eq_zpowers_mul hA haA hdA hd1 had
    (hBad ▸ Subgroup.zpowers_le.mpr hbB) hb3 hbd
  obtain ⟨n, rfl⟩ : ∃ n : ℕ, d ^ n = f := (mem_powers_iff_mem_zpowers).mpr hf
  have hfA : d ^ n ∈ A := A.pow_mem hdA n
  have hafA : a * d ^ n ∈ A := A.mul_mem haA hfA
  have hWaf : Subgroup.normalizer (A : Set G) ≤
      Subgroup.normalizer (Subgroup.zpowers (a * d ^ n) : Set G) := hbf ▸ hWb
  have hAE := img148_isE27 (Y := Y) hA
  have hAab : ∀ x ∈ img148 A Y A, ∀ y ∈ img148 A Y A, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hAE.1.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  have hA3' : ∀ x ∈ img148 A Y A, x ^ 3 = 1 := hAE.1.2
  have hF3 : ∀ w : ↥(Y ⊔ A) ⧸ ker148 A Y,
      w ∈ Subgroup.centralizer (img148 A Y A : Set (↥(Y ⊔ A) ⧸ ker148 A Y)) → w ^ 3 = 1 →
        w ∈ img148 A Y A := fun w hw hw3 => mem_img148_of_commute hS.mem_partTwoF hAY hw hw3
  have hAJα : img148 A Y A ≤
      Subgroup.normalizer (img148 A Y J : Set (↥(Y ⊔ A) ⧸ ker148 A Y)) :=
    img148_le_normalizer hAJ
  have hdJα : alpha148 A Y d hdA ∈ img148 A Y J :=
    mem_img148_iff.mpr ⟨d, Subgroup.mem_sup_right hdA, hYdJ hdYd, rfl⟩
  have hd1α : alpha148 A Y d hdA ≠ 1 := alpha148_ne_one hdA hd1 (hA3 d hdA)
  obtain ⟨h1080, hPle⟩ := HJRes148.card_img148_yd_of_a6 hAY hdA (hA3 d hdA) hYd hJ hYdJ hAJ hA6 hθ
  have hdC : 1080 ≤ Nat.card (Subgroup.centralizer
      ({(⟨alpha148 A Y d hdA, hdJα⟩ : ↥(img148 A Y J))} : Set ↥(img148 A Y J))) := by
    have hPJ : img148 A Y Yd ≤ img148 A Y J := hPle.trans inf_le_left
    have hP'le : (img148 A Y Yd).subgroupOf (img148 A Y J) ≤
        Subgroup.centralizer {(⟨alpha148 A Y d hdA, hdJα⟩ : ↥(img148 A Y J))} := by
      intro x hx
      rw [Subgroup.mem_centralizer_singleton_iff]
      apply Subtype.ext
      exact Subgroup.mem_centralizer_singleton_iff.1 (hPle (Subgroup.mem_subgroupOf.1 hx)).2
    have hcard : Nat.card ((img148 A Y Yd).subgroupOf (img148 A Y J)) =
        Nat.card (img148 A Y Yd) :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hPJ).toEquiv
    calc 1080 ≤ Nat.card (img148 A Y Yd) := h1080
      _ = Nat.card ((img148 A Y Yd).subgroupOf (img148 A Y J)) := hcard.symm
      _ ≤ _ := Subgroup.card_le_of_le hP'le
  have haJα : alpha148 A Y a haA ∈
      Subgroup.centralizer (img148 A Y J : Set (↥(Y ⊔ A) ⧸ ker148 A Y)) := by
    rw [Subgroup.mem_centralizer_iff]
    intro g hg
    obtain ⟨j, hjM, hjJ, rfl⟩ := mem_img148_iff.mp hg
    exact (CFSG.AGLEmbeddingD2.Wilson.MaximalityAmbient.Step148M24.mk_comm_of_commutator_mem
      (A := A) (Y := Y)
      (Subgroup.mem_sup_right haA) hjM (haC.2 j hjJ)).symm
  have ha1α : alpha148 A Y a haA ≠ 1 := alpha148_ne_one haA ha1 (hA3 a haA)
  obtain ⟨y, hyJ, hyN, hyd⟩ := exists_inv_mem_normalizer_of_m24 hAab hA3' hAE.2 hF3 hAJα e
    (alpha148_mem_img148 hdA) hdJα hd1α hdC (alpha148_mem_img148 haA) haJα ha1α
  have hAp : IsPGroup 3 A := IsPGroup.of_card (n := 3) (by rw [hA.2]; norm_num)
  have hyu := HJRes148.mem_normalizer_alpha_of hAp hafA hWaf hyN
  have hya : y * alpha148 A Y a haA * y⁻¹ = alpha148 A Y a haA := by
    have h1 : y * alpha148 A Y a haA = alpha148 A Y a haA * y :=
      (Subgroup.mem_centralizer_iff.mp haJα y hyJ)
    calc y * alpha148 A Y a haA * y⁻¹ = alpha148 A Y a haA * y * y⁻¹ := by rw [h1]
      _ = alpha148 A Y a haA := by group
  have hu : alpha148 A Y (a * d ^ n) hafA = alpha148 A Y a haA * alpha148 A Y d hdA ^ n := by
    rw [alpha148_mul haA hfA, alpha148_pow hdA n]
  have hmem : y * (alpha148 A Y a haA * alpha148 A Y d hdA ^ (n : ℤ)) * y⁻¹ ∈
      Subgroup.zpowers (alpha148 A Y a haA * alpha148 A Y d hdA ^ (n : ℤ)) := by
    rw [zpow_natCast, ← hu]
    exact (Subgroup.mem_normalizer_iff.mp hyu _).mp (Subgroup.mem_zpowers _)
  have had' : alpha148 A Y a haA ∉ Subgroup.zpowers (alpha148 A Y d hdA) := by
    intro h
    obtain ⟨k, hk⟩ : ∃ k : ℕ, alpha148 A Y d hdA ^ k = alpha148 A Y a haA :=
      (mem_powers_iff_mem_zpowers).mpr h
    rw [← alpha148_pow hdA k] at hk
    have hak : d ^ k = a := alpha148_injective hA3 (A.pow_mem hdA k) haA hk
    exact had (hak ▸ Subgroup.pow_mem _ (Subgroup.mem_zpowers d) k)
  have hdn := zpow_eq_one_of_conj_mem (hAab _ (alpha148_mem_img148 haA) _
    (alpha148_mem_img148 hdA)) (hA3' _ (alpha148_mem_img148 haA))
    (hA3' _ (alpha148_mem_img148 hdA)) had' hya hyd hmem
  rw [zpow_natCast, ← alpha148_pow hdA n] at hdn
  have h1 : alpha148 A Y (1 : G) A.one_mem = 1 := by
    rw [alpha148_eq_mk']
    exact map_one _
  have hdn1 : d ^ n = 1 := alpha148_injective hA3 (A.pow_mem hdA n) A.one_mem (hdn.trans h1.symm)
  rw [hbf, hdn1, mul_one]

end CFSG.RankThree.PartTwo.Sec14.Ronan148W
