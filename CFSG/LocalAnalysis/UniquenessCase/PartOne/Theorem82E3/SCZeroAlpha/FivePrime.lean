module

public import CFSG.RankThree.LocalRank.SolvablePrimeComplementCore
public import CFSG.RankThree.PartTwo.KFacts.KS44OutSz
import CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.P622KDEven
import CFSG.Quasithin.Vol2.Ch5Sec1L34Lem516
import CFSG.RankThree.PartTwo.Sec11.Item116R1CompThree
import CFSG.GroupTheory.ABGLocalTools.PStabilitySignalizer
import CFSG.RankThree.PartTwo.KFacts.KP7Suzuki
import CFSG.GroupTheory.ElementaryAbelianTransport
import CFSG.LocalAnalysis.SignalizerFunctor.CentralizerImages
import CFSG.Monster.B.TwoA.Base.ElemAut

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.SCZeroAlpha

open CFSG Subgroup
open CFSG.RankThree.LocalRank
open CFSG.RankThree.PartTwo.KFacts (KPSz)

private noncomputable def conjAct {Y : Type} [Group Y] {J B : Subgroup Y}
    (hBJ : B ≤ normalizer (J : Set Y)) : B →* MulAut ↥J :=
  (Subgroup.normalizerMonoidHom (H := J)).comp (Subgroup.inclusion hBJ)

private theorem conjAct_apply {Y : Type} [Group Y] {J B : Subgroup Y}
    (hBJ : B ≤ normalizer (J : Set Y)) (b : B) (x : ↥J) :
    ((conjAct hBJ b) x : Y) = (b : Y) * (x : Y) * (b : Y)⁻¹ := by
  rw [conjAct, MonoidHom.comp_apply, Subgroup.normalizerMonoidHom_apply_apply_coe,
    Subgroup.coe_inclusion]

private theorem inf_centralizer_eq_self_of_conjAct_eq_one {Y : Type} [Group Y] {J B : Subgroup Y}
    (hBJ : B ≤ normalizer (J : Set Y)) (hbot : ∀ b : B, conjAct hBJ b = 1) :
    J ⊓ centralizer (B : Set Y) = J := by
  have hle : J ≤ centralizer (B : Set Y) := by
    intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro b hb
    have h1 : conjAct hBJ ⟨b, hb⟩ ⟨x, hx⟩ = ⟨x, hx⟩ := by rw [hbot ⟨b, hb⟩, MulAut.one_apply]
    have hc : (b : Y) * (x : Y) * (b : Y)⁻¹ = (x : Y) := by
      simpa only [conjAct_apply] using congrArg (fun z : ↥J => (z : Y)) h1
    exact mul_inv_eq_iff_eq_mul.mp hc
  exact le_antisymm inf_le_left (le_inf le_rfl hle)

private theorem exists_orderOf_eq_three_of_card_range_eq_three {A X : Type*} [Group A] [Group X]
    [Finite X] (φ : A →* MulAut X) (h3 : Nat.card φ.range = 3) :
    ∃ (α : MulAut X) (b₀ : A), orderOf α = 3 ∧ Subgroup.zpowers α = φ.range ∧ φ b₀ = α := by
  have hne : ∃ b : A, φ b ≠ 1 := by
    by_contra h
    push Not at h
    have hbot : φ.range = ⊥ := by
      rw [eq_bot_iff]
      rintro _ ⟨b, rfl⟩
      exact Subgroup.mem_bot.mpr (h b)
    rw [hbot, Subgroup.card_bot] at h3
    exact absurd h3 (by norm_num)
  obtain ⟨b₀, hb₀⟩ := hne
  have hdvd : orderOf (φ b₀) ∣ 3 := by
    rw [← h3, ← Nat.card_zpowers]
    exact Subgroup.card_dvd_of_le (Subgroup.zpowers_le.mpr ⟨b₀, rfl⟩)
  have hα3 : orderOf (φ b₀) = 3 := by
    rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h | h
    · exact absurd (orderOf_eq_one_iff.mp h) hb₀
    · exact h
  refine ⟨φ b₀, b₀, hα3, ?_, rfl⟩
  refine Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr ⟨b₀, rfl⟩) ?_
  rw [h3, Nat.card_zpowers, hα3]

private theorem inf_centralizer_eq_map_eqLocus {Y : Type} [Group Y] {J B : Subgroup Y}
    (hBJ : B ≤ normalizer (J : Set Y)) {α : MulAut ↥J}
    (hgen : ∀ b : B, ∃ n : ℤ, conjAct hBJ b = α ^ n) (hb₀ : ∃ b₀ : B, conjAct hBJ b₀ = α) :
    J ⊓ centralizer (B : Set Y) =
      (MonoidHom.eqLocus α.toMonoidHom (MonoidHom.id ↥J)).map J.subtype := by
  obtain ⟨b₀, hb₀⟩ := hb₀
  ext x
  constructor
  · rintro ⟨hxJ, hxC⟩
    refine Subgroup.mem_map.mpr ⟨⟨x, hxJ⟩, ?_, rfl⟩
    show α ⟨x, hxJ⟩ = ⟨x, hxJ⟩
    have hc := Subgroup.mem_centralizer_iff.mp hxC b₀ b₀.2
    apply Subtype.ext
    rw [← hb₀, conjAct_apply]
    exact mul_inv_eq_iff_eq_mul.mpr hc
  · rintro ⟨y, hy, rfl⟩
    refine ⟨y.2, ?_⟩
    change ∀ h ∈ (B : Set Y), h * (y : Y) = (y : Y) * h
    intro b hb
    have hy' : α y = y := hy
    obtain ⟨n, hn⟩ := hgen ⟨b, hb⟩
    have hyf : y ∈ MulAction.fixedBy ↥J α := hy'
    have hfix : conjAct hBJ ⟨b, hb⟩ y = y := by
      rw [hn]
      exact MulAction.mem_fixedBy_zpow hyf n
    have hc : (b : Y) * (y : Y) * (b : Y)⁻¹ = (y : Y) := by
      simpa only [conjAct_apply] using congrArg (fun z : ↥J => (z : Y)) hfix
    exact mul_inv_eq_iff_eq_mul.mp hc

theorem five_dvd_card_inf_centralizer_of_isSimpleGroup
    (hSz : KPSz) {Y : Type} [Group Y] [Finite Y] {J : Subgroup Y}
    [IsSimpleGroup J] (hnab : ∃ a b : J, a * b ≠ b * a) (hcat : CFSG.Open.IsCatalogGroup J)
    (hJ3 : ¬ 3 ∣ Nat.card J) {B : Subgroup Y} (hB : CFSG.Open.IsElemAbelian 3 B)
    (hBJ : B ≤ normalizer (J : Set Y)) :
    5 ∣ Nat.card ↥(J ⊓ centralizer (B : Set Y)) := by
  classical
  obtain ⟨f, hf⟩ := hSz J hnab hcat hJ3
  have hpow : ∀ x ∈ (conjAct hBJ).range, x ^ 3 = 1 := by
    rintro _ ⟨b, rfl⟩
    have hb3 : b ^ 3 = 1 := Subtype.ext (by simpa using hB.2 b b.2)
    rw [← map_pow, hb3, map_one]
  have hdvd : Nat.card (conjAct hBJ).range ∣ 3 :=
    CFSG.RankThree.PartTwo.KFacts.KP7.card_dvd_three_of_pow_three hf hpow
  rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h1 | h3
  · have hbot : ∀ b : B, conjAct hBJ b = 1 := by
      intro b
      have hmem : conjAct hBJ b ∈ (conjAct hBJ).range := ⟨b, rfl⟩
      rwa [Subgroup.card_eq_one.mp h1, Subgroup.mem_bot] at hmem
    rw [inf_centralizer_eq_self_of_conjAct_eq_one hBJ hbot]
    exact (CFSG.Quasithin.H13.five_dvd_card_of_suzukiModel hf).1
  · obtain ⟨α, b₀, hα3, hzp, hb₀⟩ := exists_orderOf_eq_three_of_card_range_eq_three _ h3
    have hgen : ∀ b : B, ∃ n : ℤ, conjAct hBJ b = α ^ n := by
      intro b
      have hmem : conjAct hBJ b ∈ Subgroup.zpowers α := by
        rw [hzp]
        exact ⟨b, rfl⟩
      obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp hmem
      exact ⟨n, hn.symm⟩
    rw [inf_centralizer_eq_map_eqLocus hBJ hgen ⟨b₀, hb₀⟩, Subgroup.card_map_of_injective
      (K := MonoidHom.eqLocus α.toMonoidHom (MonoidHom.id ↥J)) J.subtype_injective]
    exact CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.five_dvd_card_fixed hf hJ3 α hα3

private theorem isSimpleGroup_and_exists_noncomm_of_isComponent {Z : Type} [Group Z] [Finite Z]
    {J : Subgroup Z} (hθ : aschbacherSolvableCore 3 Z = ⊥) (hJ : CFSG.IsComponent J)
    (h3 : ¬ 3 ∣ Nat.card J) :
    IsSimpleGroup ↥J ∧ ∃ a b : ↥J, a * b ≠ b * a := by
  have hZ : Subgroup.center J = ⊥ :=
    CFSG.RankThree.PartTwo.Sec11.component_center_bot_of_prime_three hθ hJ h3
  have hs : IsSimpleGroup ↥J := by
    have hss : IsSimpleGroup (↥J ⧸ Subgroup.center ↥J) := hJ.1.2.1
    exact
      ((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot).symm.isSimpleGroup
  refine ⟨hs, ?_⟩
  by_contra h
  push Not at h
  have hcomm : IsMulCommutative ↥J := ⟨⟨h⟩⟩
  have hperf : Group.IsPerfect ↥J := hJ.1.1
  exact Group.IsPerfect.not_isSolvable ↥J inferInstance

theorem five_dvd_card_centralizer_of_component
    (hSz : KPSz) {X : Type} [Group X] [Finite X]
    (hK : CFSG.Open.IsKGroup X) {J : Subgroup (X ⧸ aschbacherSolvableCore 3 X)}
    (hJ : CFSG.IsComponent J) (hJ3 : ¬ 3 ∣ Nat.card J) {B : Subgroup X}
    (hB : CFSG.Open.IsElemAbelian 3 B)
    (hBJ : B.map (QuotientGroup.mk' (aschbacherSolvableCore 3 X)) ≤
      normalizer (J : Set (X ⧸ aschbacherSolvableCore 3 X))) :
    5 ∣ Nat.card (centralizer (B : Set X)) := by
  classical
  let θ := aschbacherSolvableCore 3 X
  let ρ : X →* (X ⧸ θ) := QuotientGroup.mk' θ
  have hsurj : Function.Surjective ρ := QuotientGroup.mk'_surjective θ
  have hfin : Finite (X ⧸ θ) := Finite.of_surjective ρ hsurj
  have hθ : aschbacherSolvableCore 3 (X ⧸ θ) = ⊥ :=
    (CFSG.RankThree.theta_quotient_core_and_ranks (G := X)).1
  obtain ⟨hsimple, hnab⟩ := isSimpleGroup_and_exists_noncomm_of_isComponent hθ hJ hJ3
  have hcat : CFSG.Open.IsCatalogGroup ↥J :=
    CFSG.Open.IsKGroup.isCatalogGroup_of_surjective (hK.quotient θ) J hnab
      (MonoidHom.id ↥J) Function.surjective_id
  have h5 : 5 ∣ Nat.card ↥(J ⊓ centralizer ((B.map ρ) : Set (X ⧸ θ))) :=
    five_dvd_card_inf_centralizer_of_isSimpleGroup hSz hnab hcat hJ3 (hB.map ρ) hBJ
  have hJtmap : (J.comap ρ).map ρ = J := Subgroup.map_comap_eq_self_of_surjective hsurj J
  have h3t : ¬ 3 ∣ Nat.card ↥(J.comap ρ) := by
    rw [CFSG.ABGLocalTools.card_comap_mk' θ J]
    intro h
    rcases Nat.prime_three.dvd_mul.mp h with h' | h'
    · exact CFSG.RankThree.three_not_dvd_card_aschbacherSolvableCore (G := X) h'
    · exact hJ3 h'
  have hBnorm : B ≤ Subgroup.normalizer (J.comap ρ : Set X) := by
    rw [← Subgroup.comap_normalizer_eq_of_surjective J hsurj]
    exact Subgroup.map_le_iff_le_comap.mp hBJ
  have hmap : ((J.comap ρ) ⊓ Subgroup.centralizer (B : Set X)).map ρ =
      J ⊓ Subgroup.centralizer ((B.map ρ) : Set (X ⧸ θ)) := by
    have h := CFSG.SignalizerFunctor.Helpers.coprime_centralizer_image_elementary 3
      Nat.prime_three ρ B (J.comap ρ) hB hBnorm (Nat.prime_three.coprime_iff_not_dvd.mpr h3t)
    simpa only [hJtmap] using h
  have h5map : 5 ∣ Nat.card ↥(((J.comap ρ) ⊓ Subgroup.centralizer (B : Set X)).map ρ) := by
    rw [hmap]
    exact h5
  have hdvd1 : Nat.card ↥(((J.comap ρ) ⊓ Subgroup.centralizer (B : Set X)).map ρ) ∣
      Nat.card ↥((J.comap ρ) ⊓ Subgroup.centralizer (B : Set X)) :=
    Subgroup.card_map_dvd _ ρ
  exact h5map.trans (hdvd1.trans (Subgroup.card_dvd_of_le inf_le_right))

theorem three_dvd_card_component_of_five
    (hSz : KPSz) {G : Type} [Group G] [Finite G]
    {C B M : Subgroup G} (hBC : B ≤ C) (hB : CFSG.Open.IsElemAbelian 3 B)
    (hCM : centralizer (B : Set G) ≤ M) (hC : CFSG.Open.IsKGroup C)
    (hnorm : ∀ J : Subgroup (C ⧸ aschbacherSolvableCore 3 C), CFSG.IsComponent J →
      ¬ 3 ∣ Nat.card J →
      (B.subgroupOf C).map (QuotientGroup.mk' (aschbacherSolvableCore 3 C)) ≤
        normalizer (J : Set (C ⧸ aschbacherSolvableCore 3 C)))
    (hdelta : ¬ 5 ∣ Nat.card ↥(M ⊓ centralizer (B : Set G))) :
    ∀ J : Subgroup (C ⧸ aschbacherSolvableCore 3 C), CFSG.IsComponent J → 3 ∣ Nat.card J := by
  intro J hJ
  by_contra hJ3
  have hB' : CFSG.Open.IsElemAbelian 3 (B.subgroupOf C) := hB.subgroupOf C
  have h5 : 5 ∣ Nat.card ↥(centralizer ((B.subgroupOf C) : Set ↥C)) :=
    five_dvd_card_centralizer_of_component hSz hC hJ hJ3 hB' (hnorm J hJ hJ3)
  have hle : (Subgroup.centralizer ((B.subgroupOf C) : Set ↥C)).map C.subtype ≤
      M ⊓ centralizer (B : Set G) := by
    intro x hx
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hx
    have hy' := Subgroup.mem_centralizer_iff.mp hy
    refine Subgroup.mem_inf.mpr ⟨hCM ?_, ?_⟩
    · rw [Subgroup.mem_centralizer_iff]
      intro b hb
      have hcomm := hy' ⟨b, hBC hb⟩ (Subgroup.mem_subgroupOf.mpr hb)
      exact congrArg (fun z : ↥C => (z : G)) hcomm
    · rw [Subgroup.mem_centralizer_iff]
      intro b hb
      have hcomm := hy' ⟨b, hBC hb⟩ (Subgroup.mem_subgroupOf.mpr hb)
      exact congrArg (fun z : ↥C => (z : G)) hcomm
  have hdvd : 5 ∣ Nat.card ↥(M ⊓ centralizer (B : Set G)) := by
    have h5' : 5 ∣ Nat.card ↥((Subgroup.centralizer
        ((B.subgroupOf C) : Set ↥C)).map C.subtype) := by
      rwa [Subgroup.card_map_of_injective C.subtype_injective]
    exact h5'.trans (Subgroup.card_dvd_of_le hle)
  exact hdelta hdvd

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.SCZeroAlpha
