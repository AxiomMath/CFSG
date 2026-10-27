module

public import CFSG.RankThree.PartTwo.Sec14.Ronan148WA5Normal
import CFSG.RankThree.PartTwo.Sec14.Item147
import CFSG.RankThree.PartTwo.Sec14.Item148HJRes2ProofInner
import CFSG.RankThree.PartTwo.Sec14.Ronan148JHJRank
import CFSG.RankThree.PartTwo.Sec14.Ronan148VDelta
import CFSG.RankThree.PartTwo.Sec15.Gagen155W315PImg
public import CFSG.RankThree.PartTwo.Sec13.Item13Basic
public import CFSG.RankThree.PartTwo.Sec14.Item148StepQuot
public import CFSG.RankThree.PartTwo.Sec14.Std

public section

namespace CFSG.RankThree.PartTwo.Sec15.Sylow155NO

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.LocalRank CFSG.GH74.GLS

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
private theorem relIndex_sup_eq {H N : Subgroup G} (hHN : H ≤ Subgroup.normalizer (N : Set G)) :
    N.relIndex (H ⊔ N) = N.relIndex H := by
  have h1 := Subgroup.normal_subgroupOf_of_le_normalizer hHN
  have h2 := Subgroup.normal_subgroupOf_sup_of_le_normalizer hHN
  exact (Nat.card_congr (QuotientGroup.quotientInfEquivProdNormalizerQuotient H N hHN).toEquiv).symm

omit [Finite G] in
private theorem le_pPrimeCoreOf_of_img148_eq_bot {A M X : Subgroup G} [(ker148 A M).Normal]
    (hXM : X ≤ M) (h : img148 A M X = ⊥) : X ≤ pPrimeCoreOf 3 M := by
  intro g hg
  have hgM : g ∈ M ⊔ A := Subgroup.mem_sup_left (hXM hg)
  have : QuotientGroup.mk' (ker148 A M) ⟨g, hgM⟩ ∈ img148 A M X :=
    mem_img148_iff.mpr ⟨g, hgM, hg, rfl⟩
  rw [h, Subgroup.mem_bot, mk'_ker148_eq_one_iff] at this
  exact this

theorem inf_le_pPrimeCoreOf {A M H N : Subgroup G} [(ker148 A M).Normal] (hHM : H ≤ M)
    (hH : Ronan148W.NoNormal3 ↥(img148 A M H)) (hHN : H ≤ Subgroup.normalizer (N : Set G))
    (hN3 : ¬ 3 ∣ Nat.card N) : H ⊓ N ≤ pPrimeCoreOf 3 M := by
  have hDH : H ⊓ N ≤ H := inf_le_left
  have hDM : H ⊓ N ≤ M := hDH.trans hHM
  have hmono : img148 A M (H ⊓ N) ≤ img148 A M H := img148_mono hDH
  have hHD : H ≤ Subgroup.normalizer ((H ⊓ N : Subgroup G) : Set G) :=
    (le_inf Subgroup.le_normalizer hHN).trans Subgroup.inf_normalizer_le_normalizer_inf
  have hnorm : img148 A M H ≤
      Subgroup.normalizer (img148 A M (H ⊓ N) : Set (↥(M ⊔ A) ⧸ ker148 A M)) :=
    img148_le_normalizer hHD
  have hnormal : ((img148 A M (H ⊓ N)).subgroupOf (img148 A M H)).Normal :=
    Subgroup.normal_subgroupOf_of_le_normalizer hnorm
  have hcard : Nat.card ((img148 A M (H ⊓ N)).subgroupOf (img148 A M H)) =
      Nat.card (img148 A M (H ⊓ N)) :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hmono).toEquiv
  have hdiv : Nat.card (img148 A M (H ⊓ N)) ∣ Nat.card ↥(H ⊓ N) := by
    rw [Proof155P.card_img148_eq_index hDM]
    exact Subgroup.index_dvd_card _
  have h3' : ¬ 3 ∣ Nat.card (img148 A M (H ⊓ N)) := fun h3 =>
    hN3 ((h3.trans hdiv).trans (Subgroup.card_dvd_of_le inf_le_right))
  have hbot : (img148 A M (H ⊓ N)).subgroupOf (img148 A M H) = ⊥ :=
    hH _ hnormal (by rwa [hcard])
  have himg : img148 A M (H ⊓ N) = ⊥ := by
    have hdisj : Disjoint (img148 A M (H ⊓ N)) (img148 A M H) :=
      Subgroup.subgroupOf_eq_bot.mp hbot
    exact disjoint_self.mp (hdisj.mono_right hmono)
  exact le_pPrimeCoreOf_of_img148_eq_bot hDM himg

theorem card_img148_dvd_index {A M H Y N : Subgroup G} [(ker148 A M).Normal] (hHM : H ≤ M)
    (hHY : H ≤ Y) (hNY : N ≤ Y) (hYN : Y ≤ Subgroup.normalizer (N : Set G))
    (hHN : H ⊓ N ≤ pPrimeCoreOf 3 M) : Nat.card (img148 A M H) ∣ (N.subgroupOf Y).index := by
  rw [Proof155P.card_img148_eq_index hHM]
  have h1 : (pPrimeCoreOf 3 M).relIndex H ∣ (H ⊓ N).relIndex H :=
    Subgroup.relIndex_dvd_of_le_left H hHN
  rw [Subgroup.inf_relIndex_left] at h1
  have h2 : N.relIndex H = N.relIndex (H ⊔ N) := (relIndex_sup_eq (hHY.trans hYN)).symm
  have h3 : N.relIndex (H ⊔ N) ∣ N.relIndex Y :=
    Dvd.intro _ (Subgroup.relIndex_mul_relIndex N (H ⊔ N) Y le_sup_right (sup_le hHY hNY))
  exact h1.trans (h2 ▸ h3)

private theorem sup_theta_le {O X : Subgroup G} (hXO : X ≤ Subgroup.normalizer (O : Set G))
    (hO3 : Nat.Coprime 3 (Nat.card O)) :
    O ⊔ inSubgroup (aschbacherSolvableCore 3) X ≤ pPrimeCoreOf 3 (O ⊔ X) := by
  have hθXX : inSubgroup (aschbacherSolvableCore 3) X ≤ X := Subgroup.map_subtype_le _
  have hXθ : X ≤ Subgroup.normalizer
      ((inSubgroup (aschbacherSolvableCore 3) X : Subgroup G) : Set G) :=
    Ronan148V.le_normalizer_theta X
  refine le_pPrimeCoreOf (sup_le_sup_left hθXX O) ?_ ?_
  · refine sup_le (le_sup_left.trans Subgroup.le_normalizer) ?_
    exact (le_inf hXO hXθ).trans (Subgroup.inf_normalizer_le_normalizer_sup _ _)
  · have hθ3 : Nat.Coprime 3 (Nat.card (inSubgroup (aschbacherSolvableCore 3) X : Subgroup G)) :=
      (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr (Ronan148V.not_dvd_card_theta X)
    have hd := card_sup_dvd_card_mul (H := inSubgroup (aschbacherSolvableCore 3) X) (K := O)
      (hθXX.trans hXO)
    rw [sup_comm] at hd
    exact Nat.Coprime.coprime_dvd_right hd (Nat.Coprime.mul_right hθ3 hO3)

private theorem sup_eq_sup_pPrimeCoreOf {O X : Subgroup G}
    (hXO : X ≤ Subgroup.normalizer (O : Set G)) (hO3 : Nat.Coprime 3 (Nat.card O)) :
    O ⊔ X = pPrimeCoreOf 3 (O ⊔ X) ⊔ X :=
  le_antisymm (sup_le_sup_right (le_sup_left.trans (sup_theta_le hXO hO3)) X)
    (sup_le (pPrimeCoreOf_le 3 _) le_sup_right)

private theorem index_dvd_card_theta_quot {Y X : Subgroup G} (hY : Y = pPrimeCoreOf 3 Y ⊔ X)
    (hθX : inSubgroup (aschbacherSolvableCore 3) X ≤ pPrimeCoreOf 3 Y) :
    ((pPrimeCoreOf 3 Y).subgroupOf Y).index ∣ Nat.card (↥X ⧸ aschbacherSolvableCore 3 ↥X) := by
  have hXY : X ≤ Y := le_sup_right.trans hY.ge
  have hYN : Y ≤ Subgroup.normalizer (pPrimeCoreOf 3 Y : Set G) := le_normalizer_pPrimeCoreOf 3 Y
  have h1 : (pPrimeCoreOf 3 Y).relIndex Y = (pPrimeCoreOf 3 Y).relIndex X := by
    have := relIndex_sup_eq (H := X) (N := pPrimeCoreOf 3 Y) (hXY.trans hYN)
    rwa [sup_comm, ← hY] at this
  have h2 : (pPrimeCoreOf 3 Y).relIndex X ∣
      (inSubgroup (aschbacherSolvableCore 3) X).relIndex X :=
    Subgroup.relIndex_dvd_of_le_left X hθX
  have h3 : (inSubgroup (aschbacherSolvableCore 3) X).subgroupOf X =
      aschbacherSolvableCore 3 ↥X :=
    Subgroup.comap_map_eq_self_of_injective X.subtype_injective _
  have h4 : (inSubgroup (aschbacherSolvableCore 3) X).relIndex X =
      Nat.card (↥X ⧸ aschbacherSolvableCore 3 ↥X) := by
    rw [Subgroup.relIndex, h3]
    exact Subgroup.index_eq_card _
  rw [h4, ← h1] at h2
  exact h2

private theorem index_dvd_card_range {Y J : Subgroup G} {Q : Type*} [Group Q] (φ : ↥J →* Q)
    (hY : Y = pPrimeCoreOf 3 Y ⊔ J) (hker : ¬ 3 ∣ Nat.card (φ.ker.map J.subtype)) :
    ((pPrimeCoreOf 3 Y).subgroupOf Y).index ∣ Nat.card φ.range := by
  have hJY : J ≤ Y := le_sup_right.trans hY.ge
  have hYN : Y ≤ Subgroup.normalizer (pPrimeCoreOf 3 Y : Set G) := le_normalizer_pPrimeCoreOf 3 Y
  have hK'J : φ.ker.map J.subtype ≤ J := Subgroup.map_subtype_le _
  have hsub : (φ.ker.map J.subtype).subgroupOf J = φ.ker :=
    Subgroup.comap_map_eq_self_of_injective J.subtype_injective _
  have hnorm : J ≤ Subgroup.normalizer ((φ.ker.map J.subtype : Subgroup G) : Set G) := by
    have : ((φ.ker.map J.subtype).subgroupOf J).Normal := by
      rw [hsub]
      infer_instance
    exact (Subgroup.normal_subgroupOf_iff_le_normalizer hK'J).mp this
  have hK'θ : φ.ker.map J.subtype ≤ pPrimeCoreOf 3 Y := by
    have hle : φ.ker.map J.subtype ⊔ pPrimeCoreOf 3 Y ≤ Y :=
      sup_le (hK'J.trans hJY) (pPrimeCoreOf_le 3 Y)
    have hN : Y ≤ Subgroup.normalizer
        ((φ.ker.map J.subtype ⊔ pPrimeCoreOf 3 Y : Subgroup G) : Set G) := by
      refine hY.le.trans (sup_le (le_sup_right.trans Subgroup.le_normalizer) ?_)
      exact (le_inf hnorm (hJY.trans hYN)).trans (Subgroup.inf_normalizer_le_normalizer_sup _ _)
    have hcop : Nat.Coprime 3 (Nat.card ↥(φ.ker.map J.subtype ⊔ pPrimeCoreOf 3 Y)) := by
      have hd := card_sup_dvd_card_mul (H := φ.ker.map J.subtype) (K := pPrimeCoreOf 3 Y)
        (hK'J.trans (hJY.trans hYN))
      exact Nat.Coprime.coprime_dvd_right hd (Nat.Coprime.mul_right
        ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr hker)
        (coprime_card_pPrimeCoreOf 3 Y))
    exact le_sup_left.trans (le_pPrimeCoreOf hle hN hcop)
  have h1 : (pPrimeCoreOf 3 Y).relIndex Y = (pPrimeCoreOf 3 Y).relIndex J := by
    have := relIndex_sup_eq (H := J) (N := pPrimeCoreOf 3 Y) (hJY.trans hYN)
    rwa [sup_comm, ← hY] at this
  have h2 : (pPrimeCoreOf 3 Y).relIndex J ∣ (φ.ker.map J.subtype).relIndex J :=
    Subgroup.relIndex_dvd_of_le_left J hK'θ
  have h3 : (φ.ker.map J.subtype).relIndex J = Nat.card φ.range := by
    rw [Subgroup.relIndex, hsub, Subgroup.index_ker]
  rw [h3, ← h1] at h2
  exact h2

private theorem index_dvd_1080
    {A L : Subgroup G} {c : G} (hS : Sec14Std G A c L) {B Y X : Subgroup G}
    (hB : IsHyperplane A B) (hY : Y = pPrimeCoreOf 3 Y ⊔ X)
    (hθX : inSubgroup (aschbacherSolvableCore 3) X ≤ pPrimeCoreOf 3 Y)
    (hXeq : X = lB A B ⊔ inSubgroup (aschbacherSolvableCore 3) X) :
    ((pPrimeCoreOf 3 Y).subgroupOf Y).index ∣ 1080 := by
  have hJX : lB A B ≤ X := le_sup_left.trans hXeq.ge
  have hXY : X ≤ Y := le_sup_right.trans hY.ge
  have hYJ : Y = pPrimeCoreOf 3 Y ⊔ lB A B := by
    refine le_antisymm ?_ (sup_le (pPrimeCoreOf_le 3 Y) (hJX.trans hXY))
    refine hY.le.trans (sup_le le_sup_left ?_)
    calc X = lB A B ⊔ inSubgroup (aschbacherSolvableCore 3) X := hXeq
      _ ≤ pPrimeCoreOf 3 Y ⊔ lB A B := sup_le le_sup_right (hθX.trans le_sup_left)
  by_cases hex : ∃ b d Lb, IsLBConfig A B b d Lb
  · obtain ⟨b, d, Lb, hc⟩ := hex
    have hJres := Item148HJ.lB_eq_residual hS hB hc
    obtain ⟨hdL, -, -, -, -, h6, -⟩ := Item148HJ.resProj_facts hS hB hc
    rw [hJres] at hYJ
    have hrange : Nat.card (Item148HJ.resProj Lb d).range = 1080 :=
      HJRes2.card_of_isTripleCover_six h6
    have hker : ¬ 3 ∣ Nat.card ((Item148HJ.resProj Lb d).ker.map
        (inSubgroup perfectResidual (Lb ⊓ Subgroup.centralizer ({d} : Set G))).subtype) := by
      have hle : (Item148HJ.resProj Lb d).ker.map
          (inSubgroup perfectResidual (Lb ⊓ Subgroup.centralizer ({d} : Set G))).subtype ≤
            inSubgroup (aschbacherSolvableCore 3) Lb := by
        rintro _ ⟨k, hk, rfl⟩
        exact (Item148HJ.mem_ker_resProj k).mp hk
      exact fun h3 => Ronan148V.not_dvd_card_theta Lb (h3.trans (Subgroup.card_dvd_of_le hle))
    have := index_dvd_card_range (Item148HJ.resProj Lb d) hYJ hker
    rwa [hrange] at this
  · push Not at hex
    rw [lB_eq_bot hex, sup_bot_eq] at hYJ
    have h1 : ((pPrimeCoreOf 3 Y).subgroupOf Y).index = 1 :=
      Subgroup.relIndex_eq_one.mpr hYJ.le
    rw [h1]
    exact one_dvd _

theorem isCentralProductA6Covers_of_five_sq_dvd
    {A L : Subgroup G} {c : G} (hS : Sec14Std G A c L) {e : G} (heA : e ∈ A) (he1 : e ≠ 1)
    (heΩ : Subgroup.zpowers e ∉ omegaA A) {b d : G} (hbΩ : Subgroup.zpowers b ∈ omegaA A)
    {X : Subgroup G}
    (hcase : (X ∈ thetaComponentsAt 3 e ∧
          X = lB A (Subgroup.closure {e, b}) ⊔ inSubgroup (aschbacherSolvableCore 3) X ∧
          Subgroup.zpowers e ≠ Subgroup.zpowers d) ∨
        (Subgroup.zpowers e = Subgroup.zpowers d ∧
          (∃ 𝒳 : Set (Subgroup G), 𝒳 ⊆ thetaComponentsAt 3 e ∧ 𝒳.Nonempty ∧ X = sSup 𝒳) ∧
          (Sec4.IsTripleCover (↥X ⧸ aschbacherSolvableCore 3 ↥X)
              CFSG.Blueprint.NativeSporadic.ON ∨
            Sec4.IsTripleCover (↥X ⧸ aschbacherSolvableCore 3 ↥X)
              (alternatingGroup (Fin 6)) ∨
            IsCentralProductA6Covers (↥X ⧸ aschbacherSolvableCore 3 ↥X))))
    (h25 : 25 ∣ ((pPrimeCoreOf 3
        (pPrimeCoreOf 3 (Subgroup.centralizer ({e} : Set G)) ⊔ X)).subgroupOf
          (pPrimeCoreOf 3 (Subgroup.centralizer ({e} : Set G)) ⊔ X)).index) :
    (∃ 𝒳 : Set (Subgroup G), 𝒳 ⊆ thetaComponentsAt 3 e ∧ 𝒳.Nonempty ∧ X = sSup 𝒳) ∧
      IsCentralProductA6Covers (↥X ⧸ aschbacherSolvableCore 3 ↥X) := by
  have hO3 : Nat.Coprime 3 (Nat.card (pPrimeCoreOf 3 (Subgroup.centralizer ({e} : Set G)))) :=
    coprime_card_pPrimeCoreOf 3 _
  have hXC : X ≤ Subgroup.centralizer ({e} : Set G) := by
    rcases hcase with ⟨hXc, -, -⟩ | ⟨-, ⟨𝒳, h𝒳, -, rfl⟩, -⟩
    · exact le_centralizer_of_mem_thetaComponentsAt hXc
    · exact sSup_le fun K hK => le_centralizer_of_mem_thetaComponentsAt (h𝒳 hK)
  have hXO : X ≤ Subgroup.normalizer
      ((pPrimeCoreOf 3 (Subgroup.centralizer ({e} : Set G)) : Subgroup G) : Set G) :=
    hXC.trans (le_normalizer_pPrimeCoreOf 3 _)
  have hYX := sup_eq_sup_pPrimeCoreOf hXO hO3
  have hθX := le_sup_right.trans (sup_theta_le hXO hO3)
  have h25X : 25 ∣ Nat.card (↥X ⧸ aschbacherSolvableCore 3 ↥X) :=
    h25.trans (index_dvd_card_theta_quot hYX hθX)
  rcases hcase with ⟨-, hXeq, -⟩ | ⟨-, h𝒳, htype⟩
  · exfalso
    have hbA : b ∈ A := (zpowers_mem_omegaA_iff.mp hbΩ).1
    have hbe : b ∉ Subgroup.zpowers e := by
      intro hb
      have hb3 := (zpowers_mem_omegaA_iff.mp hbΩ).2.1
      have he3 : e ^ 3 = 1 := hS.toSec13Data.isElemAbelian.2 e heA
      have hecard : Nat.card (Subgroup.zpowers e) = 3 := by
        rw [Nat.card_zpowers]
        exact orderOf_eq_prime he3 he1
      have heq : Subgroup.zpowers b = Subgroup.zpowers e :=
        Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hb) (by rw [hecard, hb3])
      exact heΩ (heq ▸ hbΩ)
    have hB : IsHyperplane A (Subgroup.closure ({e, b} : Set G)) := by
      have hAab := hS.toSec13Data.isElemAbelian.1
      have hcomm : e * b = b * e :=
        congrArg Subtype.val (hAab.is_comm.comm ⟨e, heA⟩ ⟨b, hbA⟩)
      have h9 := Ronan148J.card_zpowers_sup_zpowers_eq_nine hcomm
        (hS.toSec13Data.isElemAbelian.2 e heA) he1 (hS.toSec13Data.isElemAbelian.2 b hbA) hbe
      have hBeq : Subgroup.closure ({e, b} : Set G) =
          Subgroup.zpowers e ⊔ Subgroup.zpowers b := by
        rw [Subgroup.zpowers_eq_closure, Subgroup.zpowers_eq_closure, ← Subgroup.closure_union]
        rfl
      refine ⟨?_, ?_⟩
      · rw [hBeq]
        exact sup_le (Subgroup.zpowers_le.mpr heA) (Subgroup.zpowers_le.mpr hbA)
      · rw [hBeq, h9, hS.isE27.2]
    have h1080 := index_dvd_1080 hS hB hYX hθX hXeq
    have h := h25.trans h1080
    norm_num at h
  · refine ⟨h𝒳, ?_⟩
    rcases htype with hON | hA6 | hcp
    · exfalso
      rw [HJRes2.card_of_isTripleCover_ON hON] at h25X
      norm_num at h25X
    · exfalso
      rw [HJRes2.card_of_isTripleCover_six hA6] at h25X
      norm_num at h25X
    · exact hcp

end CFSG.RankThree.PartTwo.Sec15.Sylow155NO
