module

public import CFSG.RankThree.PartTwo.Sec15.Sylow155B2S
public import CFSG.RankThree.PartTwo.Sec14.Ronan148QDefs
import CFSG.RankThree.PartTwo.Sec15.Sylow155NOType
import CFSG.RankThree.PartTwo.Sec15.Sylow155NOStep0
import CFSG.RankThree.PartTwo.Sec15.Sylow155NOStep1
import CFSG.RankThree.PartTwo.Sec15.Sylow155NOStep2
import CFSG.RankThree.PartTwo.Sec15.Sylow155NOCP
import CFSG.RankThree.PartTwo.Sec15.Sylow155NOT
import CFSG.RankThree.PartTwo.Sec15.Sylow155NOQ
import CFSG.RankThree.PartTwo.Sec15.Item1523Res3ProofRead
import CFSG.RankThree.PartTwo.Sec15.Read148PerfProof
import CFSG.RankThree.PartTwo.Sec15.Sylow155Twin
import CFSG.RankThree.PartTwo.Sec15.Item15Res11ProofTools
import CFSG.RankThree.PartTwo.Sec15.Gagen155W315PImg
import CFSG.RankThree.PartTwo.Sec14.Item147
import CFSG.RankThree.PartTwo.Sec14.Item148MainProofKType
import CFSG.RankThree.PartTwo.KFacts.KS14Orders

public section

namespace CFSG.RankThree.PartTwo.Sec15.Sylow155NO

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.LocalRank CFSG.GH74.GLS

variable {G : Type} [Group G] [Finite G]

private theorem not_le_of_a5 {A M W : Subgroup G} [(ker148 A M).Normal] (hWM : W ≤ M)
    (hφ : Nonempty (↥(img148 A M W) ≃* alternatingGroup (Fin 5))) :
    ¬ W ≤ pPrimeCoreOf 3 M := by
  intro hle
  obtain ⟨φ⟩ := hφ
  have h1 : Nat.card ↥(img148 A M W) = 1 := by
    rw [Proof155P.card_img148_eq_index hWM, Subgroup.subgroupOf_eq_top.mpr hle,
      Subgroup.index_top]
  have h2 := Nat.card_congr φ.toEquiv
  rw [h1, KFacts.KS14.card_alternatingGroup_five_seven_ten.1] at h2
  omega

private theorem three_dvd_card_of_noNormal3 {T : Type*} [Group T] [Finite T]
    (hN : Ronan148W.NoNormal3 T) (h25 : 25 ∣ Nat.card T) : 3 ∣ Nat.card T := by
  by_contra h3
  have htop := hN ⊤ inferInstance (by rwa [Subgroup.card_top])
  have h1 : Nat.card T = 1 := by
    have h := Subgroup.card_top (G := T)
    rw [htop, Subgroup.card_bot] at h
    exact h.symm
  rw [h1] at h25
  exact absurd (Nat.le_of_dvd one_pos h25) (by norm_num)

private theorem inner_of_quot {A M C Y H : Subgroup G} (hA : A ∈ partTwoF G) (hAC : A ≤ C)
    (hAab : IsMulCommutative A) (hA3 : ∀ a ∈ A, a ^ 3 = 1) (hA27 : Nat.card A = 27)
    (hYC : Y ≤ C) (hCY : C ≤ Subgroup.normalizer (Y : Set G))
    [((pPrimeCoreOf 3 Y).subgroupOf C).Normal]
    {J₁ J₂ : Subgroup (↥C ⧸ (pPrimeCoreOf 3 Y).subgroupOf C)}
    (hJsup : J₁ ⊔ J₂ = (Y.subgroupOf C).map (QuotientGroup.mk' _)) (hJ : ⁅J₁, J₂⁆ = ⊥)
    (h3 : Nat.card ↥(J₁ ⊓ J₂) = 3)
    (hT₁ : Sec4.IsTripleCover ↥J₁ (alternatingGroup (Fin 6)))
    (hT₂ : Sec4.IsTripleCover ↥J₂ (alternatingGroup (Fin 6)))
    (hHC : H ≤ C) (hHY : H ≤ Y) (hHθ : H ⊓ pPrimeCoreOf 3 Y ≤ pPrimeCoreOf 3 M)
    {d : G} (hdC : d ∈ C) (hdA : d ∈ Subgroup.centralizer (A : Set G)) :
    ∀ (T : Subgroup G) (f : ↥T →* alternatingGroup (Fin 5)), T ≤ H →
      Function.Surjective f → f.ker = (T ⊓ pPrimeCoreOf 3 M).subgroupOf T →
      (∀ x ∈ T, d * x * d⁻¹ ∈ T) →
      ∃ t ∈ T, ∀ x ∈ T, (d * x * d⁻¹) * (t * x * t⁻¹)⁻¹ ∈ pPrimeCoreOf 3 M := by
  intro T₀ f₀ hT₀ hf₀ hker₀ hdT₀
  set θ := pPrimeCoreOf 3 Y with hθ
  set π := QuotientGroup.mk' (θ.subgroupOf C) with hπ
  have hT₀C : T₀ ≤ C := hT₀.trans hHC
  have hθ3 : Nat.Coprime 3 (Nat.card θ) := coprime_card_pPrimeCoreOf 3 Y
  have hAθ : A ⊓ θ = ⊥ := Subgroup.inf_eq_bot_of_coprime (by
    rw [hA27]
    simpa using Nat.Coprime.pow_left 3 hθ3)
  have hinj : Function.Injective (π.comp (A.subgroupOf C).subtype) := by
    rw [injective_iff_map_eq_one]
    intro a ha
    have h1 : (a : ↥C) ∈ θ.subgroupOf C := by
      rw [← QuotientGroup.eq_one_iff]
      exact ha
    have h2 : ((a : ↥C) : G) ∈ A ⊓ θ :=
      Subgroup.mem_inf.mpr ⟨Subgroup.mem_subgroupOf.mp a.2, Subgroup.mem_subgroupOf.mp h1⟩
    rw [hAθ, Subgroup.mem_bot] at h2
    exact Subtype.ext (Subtype.ext h2)
  have hĀ27 : Nat.card ↥((A.subgroupOf C).map π) = 27 := by
    have e1 : (π.comp (A.subgroupOf C).subtype).range = (A.subgroupOf C).map π := by
      rw [MonoidHom.range_comp, Subgroup.range_subtype]
    rw [← e1, ← Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAC).toEquiv, hA27]
  have hĀc : ∀ a ∈ (A.subgroupOf C).map π, ∀ b ∈ (A.subgroupOf C).map π, a * b = b * a := by
    rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    have h1 : (a : G) * b = b * a := congrArg Subtype.val (hAab.is_comm.comm
      ⟨(a : G), Subgroup.mem_subgroupOf.mp ha⟩ ⟨(b : G), Subgroup.mem_subgroupOf.mp hb⟩)
    rw [← map_mul, ← map_mul, show a * b = b * a from Subtype.ext h1]
  have hĀ3 : ∀ a ∈ (A.subgroupOf C).map π, a ^ 3 = 1 := by
    rintro _ ⟨a, ha, rfl⟩
    have h1 : a ^ 3 = 1 := Subtype.ext (by simpa using hA3 _ (Subgroup.mem_subgroupOf.mp ha))
    rw [← map_pow, h1, map_one]
  have hĀC : ∀ q ∈ Subgroup.centralizer (((A.subgroupOf C).map π : Subgroup _) :
      Set (↥C ⧸ θ.subgroupOf C)), q ^ 3 = 1 → q ∈ (A.subgroupOf C).map π := by
    intro q hq hq3
    have hθC3 : ¬ 3 ∣ Nat.card ↥(θ.subgroupOf C) := by
      rw [Nat.card_congr
        (Subgroup.subgroupOfEquivOfLe ((pPrimeCoreOf_le 3 Y).trans hYC)).toEquiv]
      exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp hθ3
    exact Sylow155T.mem_map_of_mem_centralizer hA hAC hθC3 hq hq3
  have hnorm : ∀ g : ↥C, (g : G) ∈ Subgroup.normalizer (Y : Set G) →
      g ∈ Subgroup.normalizer ((Y.subgroupOf C : Subgroup ↥C) : Set ↥C) := by
    intro g hg
    rw [Subgroup.mem_normalizer_iff]
    intro y
    have h1 := Subgroup.mem_normalizer_iff.mp hg (y : G)
    simpa [Subgroup.mem_subgroupOf] using h1
  have hĀY : (A.subgroupOf C).map π ≤
      Subgroup.normalizer ((J₁ ⊔ J₂ : Subgroup _) : Set (↥C ⧸ θ.subgroupOf C)) := by
    rw [hJsup]
    refine (Subgroup.map_mono fun a ha => hnorm a ?_).trans (Subgroup.le_normalizer_map π)
    exact hCY (hAC (Subgroup.mem_subgroupOf.mp ha))
  set T : Subgroup ↥C := T₀.subgroupOf C with hT
  set K : Subgroup ↥C := (T₀ ⊓ pPrimeCoreOf 3 M).subgroupOf C with hK
  have hKT : K ≤ T := fun x hx =>
    Subgroup.mem_subgroupOf.mpr (Subgroup.mem_inf.mp (Subgroup.mem_subgroupOf.mp hx)).1
  have hK3 : ¬ 3 ∣ Nat.card K := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (inf_le_left.trans hT₀C)).toEquiv]
    intro h3'
    exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp (coprime_card_pPrimeCoreOf 3 M)
      (h3'.trans (Subgroup.card_dvd_of_le inf_le_right))
  let f : ↥T →* alternatingGroup (Fin 5) :=
    f₀.comp (Subgroup.subgroupOfEquivOfLe hT₀C).toMonoidHom
  have hf : Function.Surjective f := hf₀.comp (Subgroup.subgroupOfEquivOfLe hT₀C).surjective
  have hker : f.ker = K.subgroupOf T := by
    ext x
    rw [MonoidHom.mem_ker]
    change f₀ (Subgroup.subgroupOfEquivOfLe hT₀C x) = 1 ↔ _
    rw [← MonoidHom.mem_ker, hker₀]
    exact Iff.rfl
  have hTπ : T ⊓ π.ker ≤ K := by
    intro x hx
    obtain ⟨hxT, hxπ⟩ := Subgroup.mem_inf.mp hx
    have hxN : x ∈ θ.subgroupOf C := by
      rw [← QuotientGroup.eq_one_iff]
      exact MonoidHom.mem_ker.mp hxπ
    refine Subgroup.mem_subgroupOf.mpr (Subgroup.mem_inf.mpr ⟨Subgroup.mem_subgroupOf.mp hxT, ?_⟩)
    exact hHθ (Subgroup.mem_inf.mpr
      ⟨hT₀ (Subgroup.mem_subgroupOf.mp hxT), Subgroup.mem_subgroupOf.mp hxN⟩)
  have hTJ : T.map π ≤ J₁ ⊔ J₂ := by
    rw [hJsup]
    exact Subgroup.map_mono fun x hx =>
      Subgroup.mem_subgroupOf.mpr (hHY (hT₀ (Subgroup.mem_subgroupOf.mp hx)))
  have hδT : ∀ x ∈ T, (⟨d, hdC⟩ : ↥C) * x * (⟨d, hdC⟩ : ↥C)⁻¹ ∈ T := fun x hx =>
    Subgroup.mem_subgroupOf.mpr (hdT₀ _ (Subgroup.mem_subgroupOf.mp hx))
  have hδY : π ⟨d, hdC⟩ ∈
      Subgroup.normalizer ((J₁ ⊔ J₂ : Subgroup _) : Set (↥C ⧸ θ.subgroupOf C)) := by
    rw [hJsup]
    exact Subgroup.le_normalizer_map π ⟨⟨d, hdC⟩, hnorm _ (hCY hdC), rfl⟩
  have hδĀ : ∀ a ∈ (A.subgroupOf C).map π, a * π ⟨d, hdC⟩ = π ⟨d, hdC⟩ * a := by
    rintro _ ⟨a, ha, rfl⟩
    have h1 : (a : G) * d = d * a :=
      Subgroup.mem_centralizer_iff.mp hdA _ (Subgroup.mem_subgroupOf.mp ha)
    rw [← map_mul, ← map_mul, show a * ⟨d, hdC⟩ = ⟨d, hdC⟩ * a from Subtype.ext h1]
  obtain ⟨t, htT, ht⟩ := exists_inner_of_elemAbelian π hĀc hĀ3 hĀ27 hĀC hĀY hJ h3 hT₁ hT₂
    hKT hK3 f hf hker hTπ hTJ hδT hδY hδĀ
  refine ⟨(t : G), Subgroup.mem_subgroupOf.mp htT, fun x hx => ?_⟩
  exact (Subgroup.mem_inf.mp
    (Subgroup.mem_subgroupOf.mp (ht ⟨x, hT₀C hx⟩ (Subgroup.mem_subgroupOf.mpr hx)))).2

theorem innerOn_of_a5
    {A L : Subgroup G} {c : G} (h : Sec14Std G A c L) (h134 : Item134) (h48 : Sec4.Item4_8)
    (h143 : Ronan148Q.Item143Q A (lB A)) (h148 : Item148 A (lB A))
    {X Y M P : Subgroup G} (hf : Proof155Wx.Facts155W A X Y M P) (hX : X ∈ thetaComponentsIn M)
    [(ker148 A M).Normal] (hIX : delta A (lB A) M ≤ Subgroup.normalizer (X : Set G))
    (hφ : Nonempty (↥(img148 A M (w155 A M X)) ≃* alternatingGroup (Fin 5))) :
    Sylow155B2.InnerOn A M X := by
  intro d hd
  obtain ⟨hdD, hdM⟩ := Subgroup.mem_inf.mp hd
  have hAab : IsMulCommutative A := h.toSec13Data.isElemAbelian.1
  obtain ⟨c', e, L', hc'Ω, hL', hJ, heA, he1, hec, hdec, htype⟩ :=
    case148Three_of_not_le h h148 hf hX (not_le_of_a5 (Sylow155B2.w155_le_m A M X) hφ)
  have h' : Sec14Std G A c' L' := { h with zpowers_mem_omegaA := hc'Ω, mem_lA := hL' }
  have heΩ : Subgroup.zpowers e ∉ omegaA A :=
    Proof1523Res3.zpowers_not_mem_omegaA_of_j2 h134 h48 h' hJ heA he1 hec
  obtain ⟨h25, hpr, hN3⟩ := typeFacts_of_prod148 htype
  set C := Subgroup.centralizer ({e} : Set G) with hCdef
  set H := deltaZero A (lB A) (M ⊓ C) with hHdef
  have himgH : img148 A M H = img148 A M (deltaZero A (lB A) M) := img148_deltaZero_eq hdec hN3
  have hHM : H ≤ M := (deltaZero_le _).trans inf_le_left
  have hHC : H ≤ C := (deltaZero_le _).trans inf_le_right
  have hperf : Group.IsPerfect ↥(img148 A M H) := by
    rw [himgH]
    exact Read148Perf.isPerfect_img148 h h148 hf.mem_m2.1
  have hpr' : ∀ p : ℕ, p.Prime → p ∣ Nat.card ↥(img148 A M H) → p = 2 ∨ p = 3 ∨ p = 5 := by
    rw [himgH]
    exact hpr
  have h3H : 3 ∣ Nat.card H := by
    have h3 : 3 ∣ Nat.card ↥(img148 A M H) := by
      rw [himgH]
      exact three_dvd_card_of_noNormal3 hN3 h25
    exact h3.trans (Main148.card_img148_dvd (hHM.trans le_sup_left))
  have hHΔ : H ≤ delta A (lB A) C := (deltaZero_le_delta _).trans (delta_mono inf_le_right)
  obtain ⟨b, _, _, hbΩ, -, -, -, -, -, -, X', hΔ, hinv, hcase⟩ :=
    desc143_of_three_dvd h143 heA he1 heΩ hHΔ h3H
  obtain ⟨hHY, hind⟩ := le_normalizer_of_desc heA hΔ hinv hHΔ
  set Yₑ := pPrimeCoreOf 3 C ⊔ X' with hYdef
  have himgH' : img148 A M (H ⊓ Yₑ) = img148 A M (deltaZero A (lB A) M) :=
    (img148_inf_eq hHM hperf hpr' hHY hind).trans himgH
  have hH'M : H ⊓ Yₑ ≤ M := inf_le_left.trans hHM
  have hθ3 : ¬ 3 ∣ Nat.card (pPrimeCoreOf 3 Yₑ) :=
    (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp (coprime_card_pPrimeCoreOf 3 _)
  have hH'θ : H ⊓ Yₑ ⊓ pPrimeCoreOf 3 Yₑ ≤ pPrimeCoreOf 3 M :=
    inf_le_pPrimeCoreOf hH'M (by rw [himgH']; exact hN3)
      (inf_le_right.trans (le_normalizer_pPrimeCoreOf 3 Yₑ)) hθ3
  have h25' : 25 ∣ ((pPrimeCoreOf 3 Yₑ).subgroupOf Yₑ).index := by
    have h1 : 25 ∣ Nat.card ↥(img148 A M (H ⊓ Yₑ)) := by
      rw [himgH']
      exact h25
    exact h1.trans (card_img148_dvd_index hH'M inf_le_right (pPrimeCoreOf_le 3 Yₑ)
      (le_normalizer_pPrimeCoreOf 3 Yₑ) hH'θ)
  obtain ⟨-, hcp⟩ := isCentralProductA6Covers_of_five_sq_dvd h heA he1 heΩ hbΩ hcase h25'
  have hCY : C ≤ Subgroup.normalizer (Yₑ : Set G) := centralizer_le_normalizer_of_cp hinv hcp
  have hX'C : X' ≤ C := by
    have h1 : delta A (lB A) C ≤ C := delta_le C
    rw [hΔ] at h1
    exact le_sup_right.trans h1
  have hYC : Yₑ ≤ C := sup_le (pPrimeCoreOf_le 3 C) hX'C
  have hθX' : inSubgroup (aschbacherSolvableCore 3) X' ≤ pPrimeCoreOf 3 C :=
    Proof15Res11.theta_le_pPrimeCoreOf hX'C hCY
  haveI : ((pPrimeCoreOf 3 Yₑ).subgroupOf C).Normal :=
    Subgroup.normal_subgroupOf_of_le_normalizer
      (hCY.trans (normalizer_le_normalizer_pPrimeCoreOf 3 Yₑ))
  obtain ⟨J₁, J₂, hJsup, hJc, hJ3, hJ₁, hJ₂⟩ :=
    exists_cp_quot hX'C (pPrimeCoreOf_le 3 C) hθX'
      ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp (coprime_card_pPrimeCoreOf 3 C))
      (le_normalizer_pPrimeCoreOf 3 C) hcp
  have hdA : d ∈ Subgroup.centralizer (A : Set G) := pPrimeCoreOf_le 3 _ hdD
  have hdC : d ∈ C := Subgroup.centralizer_le (Set.singleton_subset_iff.mpr heA) hdA
  have hAC : A ≤ C := (Subgroup.le_centralizer_iff_isMulCommutative.mpr hAab).trans
    (Subgroup.centralizer_le (Set.singleton_subset_iff.mpr heA))
  have hinner := inner_of_quot h.mem_partTwoF hAC hAab h.toSec13Data.isElemAbelian.2
    h.isE27.2 hYC hCY hJsup hJc hJ3 hJ₁ hJ₂ (inf_le_left.trans hHC) inf_le_right hH'θ hdC hdA
  have hdW : d ∈ Subgroup.normalizer (w155 A M X : Set G) :=
    (Subgroup.mem_inf.mp (Sylow155B2.delta_le_nWK hIX
      (le_delta (pPrimeCoreOf_centralizer_inf_mem_scriptQ hAab
        (hf.le_am.trans Subgroup.le_normalizer)) inf_le_right hd))).1
  have hdH : d ∈ Subgroup.normalizer ((H ⊓ Yₑ : Subgroup G) : Set G) := by
    refine Subgroup.inf_normalizer_le_normalizer_inf (Subgroup.mem_inf.mpr ⟨?_, hCY hdC⟩)
    exact mem_normalizer_deltaZero (isNaturalFamily_lB A)
      (Subgroup.centralizer_le_normalizer _ hdA)
      (Subgroup.le_normalizer (Subgroup.mem_inf.mpr ⟨hdM, hdC⟩))
  have hWH : img148 A M (w155 A M X) ≤ img148 A M (H ⊓ Yₑ) := by
    rw [himgH']
    exact img148_mono (hf.w_le_i0.trans hf.i0_le_deltaZero)
  exact exists_inner_of_forall (Sylow155B2.w155_le_m A M X) hH'M hφ hWH hdM hdW hdH hinner

end CFSG.RankThree.PartTwo.Sec15.Sylow155NO
