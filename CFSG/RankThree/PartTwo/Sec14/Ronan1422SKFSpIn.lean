module

public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.ClassicalGroups.Symplectic.Simple
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.Coordinator.KF148Sig.Reduction
public import CFSG.Models.PGLOrders
public import CFSG.RankThree.LocalRank.SolvablePrimeComplementCore
public import CFSG.RankThree.PartTwo.KFacts.K71Sp4
public import CFSG.RankThree.PartTwo.KFacts.K72Centralizer
public import CFSG.RankThree.PartTwo.Sec4.Item47Bridges
public import CFSG.RankThree.PartTwo.Sec6.BThreeCensusSp4Main
public import CFSG.RankThree.PartTwo.Sec8.Item812Res10ProofSp48
public import CFSG.Foundations
public import CFSG.LinearAlgebra.LinearGroups.ProjectiveSimple
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.Coordinator.KF148Sig.Transport
public import CFSG.LocalAnalysis.ComponentInitial.LinearInvolutionFixedField
public import CFSG.RankThree.PartTwo.KFacts.AutKindsUnique
public import CFSG.RankThree.PartTwo.NotationBlocks
public import CFSG.RankThree.PartTwo.Sec4.Item47Diag
public import CFSG.RankThree.PartTwo.Sec4.Item47Statement
public import CFSG.RankThree.PartTwo.Sec4.Item47Witness
public import CFSG.RankThree.PartTwo.Sec4.LThreePiItem411
public import CFSG.RankThree.PartTwo.Sec4.ProjSLEquiv
public import Certificates.Certificate3029
public import Certificates.Certificate3086
public import Certificates.Certificate3139

public section

namespace CFSG.RankThree.PartTwo.Sec14.Ronan1422S

open CFSG.Assembly.RankThreeEven (projSp)
open CFSG.Assembly.LowTwoRank (StatedProj StatedSp)
open CFSG.RankThree.LocalRank (aschbacherSolvableCore)

theorem sp48_card_of_iso {Y : Type} [Group Y] {J : Subgroup Y}
    (e : ↥J ≃* projSp 2 (GaloisField 2 3)) : Nat.card J = 1056706560 := by
  rw [Nat.card_congr e.toEquiv, CFSG.PGLModel.card_projSp_two_eight]

theorem sp48_card_inf {Y : Type} [Group Y] [Finite Y] {J P : Subgroup Y}
    (hJ' : Nat.card J = 1056706560) (hY : Nat.card Y = 3 * Nat.card J)
    (hP : Nat.card P = 243) : Nat.card (P ⊓ J : Subgroup Y) = 81 := by
  have hJpos : 0 < Nat.card J := by rw [hJ']; norm_num
  have hidx : J.index = 3 := by
    have h := Subgroup.card_mul_index (H := J)
    rw [hY] at h
    exact Nat.eq_of_mul_eq_mul_left hJpos (h.trans (mul_comm _ _))
  have hne : J.relIndex ⊤ ≠ 0 := by
    rw [Subgroup.relIndex_top_right, hidx]
    norm_num
  have hrel : J.relIndex P ≤ 3 := by
    have h1 : J.relIndex P ≤ J.relIndex ⊤ := Subgroup.relIndex_le_of_le_right le_top hne
    rwa [Subgroup.relIndex_top_right, hidx] at h1
  have hprod : J.relIndex P * Nat.card (P ⊓ J : Subgroup Y) = 243 := by
    have h := Subgroup.relIndex_mul_card J P
    rw [inf_comm J P, hP] at h
    exact h
  have hlow : 81 ≤ Nat.card (P ⊓ J : Subgroup Y) := by
    by_contra hc
    have h4 : J.relIndex P * Nat.card (P ⊓ J : Subgroup Y) ≤ 3 * 80 :=
      Nat.mul_le_mul hrel (by omega)
    rw [hprod] at h4
    norm_num at h4
  have hdvd : Nat.card (P ⊓ J : Subgroup Y) ∣ 81 := by
    have h1 : Nat.card (P ⊓ J : Subgroup Y) ∣ Nat.card P :=
      Subgroup.card_dvd_of_le inf_le_left
    have h2 : Nat.card (P ⊓ J : Subgroup Y) ∣ Nat.card J :=
      Subgroup.card_dvd_of_le inf_le_right
    rw [hP] at h1
    rw [hJ'] at h2
    have h3 := Nat.dvd_gcd h1 h2
    norm_num at h3
    exact h3
  have hup := Nat.le_of_dvd (by norm_num) hdvd
  omega

theorem sp48_theta_eq_bot {Y : Type} [Group Y] [Finite Y] {J : Subgroup Y}
    (eJ : ↥J ≃* projSp 2 (GaloisField 2 3))
    (hCJ : Subgroup.centralizer (J : Set Y) = ⊥) (hJ' : Nat.card J = 1056706560) :
    aschbacherSolvableCore 3 J = ⊥ := by
  have h8 : Nat.card (GaloisField 2 3) = 8 := by
    rw [GaloisField.card 2 3 (by norm_num)]
    norm_num
  have hs : IsSimpleGroup (StatedProj (StatedSp 2 (GaloisField 2 3))) :=
    CFSG.ClassicalGroups.Symplectic.isSimpleGroup_statedProj_statedSp (GaloisField 2 3) 2
      (by norm_num) (Or.inl (Or.inr (by rw [h8]; norm_num)))
  haveI := hs
  haveI : IsSimpleGroup ↥J :=
    (eJ.trans (CFSG.RankThree.PartTwo.Sec4.projSpEquivStatedProj 2
      (GaloisField 2 3))).isSimpleGroup
  have hna : ∃ a b : ↥J, a * b ≠ b * a := by
    by_contra hcon
    have hcomm : ∀ a b : ↥J, a * b = b * a := fun a b => by
      by_contra h
      exact hcon ⟨a, b, h⟩
    have hbot : ∀ j : ↥J, (j : Y) = 1 := by
      intro j
      have hj : (j : Y) ∈ Subgroup.centralizer (J : Set Y) := by
        rw [Subgroup.mem_centralizer_iff]
        intro h hh
        exact congrArg Subtype.val (hcomm ⟨h, hh⟩ j)
      rw [hCJ, Subgroup.mem_bot] at hj
      exact hj
    have h1 : Nat.card ↥J = 1 :=
      Nat.card_eq_one_iff_unique.mpr ⟨⟨fun a b => Subtype.ext ((hbot a).trans (hbot b).symm)⟩,
        ⟨1⟩⟩
    omega
  open CFSG.AGLEmbeddingD2.Wilson.Coordinator.KF148Sig in
  exact aschbacherSolvableCore_eq_bot_of_isSimpleGroup hna

theorem sp48_inducesOuterTheta {Y : Type} [Group Y] [Finite Y] {J : Subgroup Y}
    (hθ : aschbacherSolvableCore 3 J = ⊥) (hCJ : Subgroup.centralizer (J : Set Y) = ⊥)
    {f : Y} (hfJ : f ∉ J) (hf : f ∈ Subgroup.normalizer (J : Set Y)) :
    Sec4.InducesOuterTheta f J := by
  unfold Sec4.InducesOuterTheta
  refine ⟨hf, fun hmem => ?_⟩
  obtain ⟨q, hq⟩ := MonoidHom.mem_range.mp hmem
  obtain ⟨j, rfl⟩ := QuotientGroup.mk_surjective q
  have key : ∀ x : ↥J, (j : Y) * x * (j : Y)⁻¹ = f * x * f⁻¹ := by
    intro x
    have h2 := congrArg (fun g : MulAut (↥J ⧸ aschbacherSolvableCore 3 J) =>
      g (QuotientGroup.mk x)) hq
    have h5 : ((j * x * j⁻¹ : ↥J) : ↥J ⧸ aschbacherSolvableCore 3 J) =
        (j : ↥J ⧸ aschbacherSolvableCore 3 J) * (x : ↥J ⧸ aschbacherSolvableCore 3 J) *
          (j : ↥J ⧸ aschbacherSolvableCore 3 J)⁻¹ := by
      simp only [QuotientGroup.mk_mul, QuotientGroup.mk_inv]
    simp only [MulAut.conj_apply, Sec4.thetaQuotMulAut_mk] at h2
    rw [← h5] at h2
    have h3 := QuotientGroup.eq.mp h2
    rw [hθ, Subgroup.mem_bot, inv_mul_eq_one] at h3
    exact congrArg Subtype.val h3
  have hcent : (j : Y)⁻¹ * f ∈ Subgroup.centralizer (J : Set Y) := by
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    have hk : (j : Y) * h * (j : Y)⁻¹ = f * h * f⁻¹ := key ⟨h, hh⟩
    calc h * ((j : Y)⁻¹ * f) = (j : Y)⁻¹ * ((j : Y) * h * (j : Y)⁻¹) * f := by group
      _ = (j : Y)⁻¹ * (f * h * f⁻¹) * f := by rw [hk]
      _ = (j : Y)⁻¹ * f * h := by group
  rw [hCJ, Subgroup.mem_bot, inv_mul_eq_one] at hcent
  exact hfJ (by rw [← hcent]; exact j.2)

theorem sp48_nonempty_mulEquiv {Y : Type} [Group Y] {J N : Subgroup Y}
    (eJ : ↥J ≃* projSp 2 (GaloisField 2 3)) (hNJ : N ≤ J) (hN : Nat.card N = 81) :
    Nonempty (↥N ≃* Multiplicative (ZMod 9 × ZMod 9)) := by
  have hM : Nat.card (N.subgroupOf J) = 81 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hNJ).toEquiv, hN]
  have hS : Nat.card ((N.subgroupOf J).map eJ.toMonoidHom) = 81 := by
    rw [Subgroup.card_map_of_injective (f := eJ.toMonoidHom) eJ.injective, hM]
  obtain ⟨eS⟩ := Sec8.kFSp48SylowThree_holds ((N.subgroupOf J).map eJ.toMonoidHom) hS
  exact ⟨(Subgroup.subgroupOfEquivOfLe hNJ).symm.trans
    (((N.subgroupOf J).equivMapOfInjective eJ.toMonoidHom eJ.injective).trans eS)⟩

theorem sp48_pow_nine_mult : ∀ g : Multiplicative (ZMod 9 × ZMod 9), g ^ 9 = 1 := by
  decide

theorem sp48_card_three_mult :
    Nat.card {g : Multiplicative (ZMod 9 × ZMod 9) // g ^ 3 = 1} = 9 := by
  rw [Nat.card_eq_fintype_card]
  decide

theorem sp48_mem_of_three_torsion {H : Subgroup (Multiplicative (ZMod 9 × ZMod 9))}
    (hH : ∀ h ∈ H, h ^ 3 = 1) (hcard : Nat.card H = 9) :
    ∀ g : Multiplicative (ZMod 9 × ZMod 9), g ^ 3 = 1 → g ∈ H := by
  let Ω : Subgroup (Multiplicative (ZMod 9 × ZMod 9)) :=
    MonoidHom.ker (powMonoidHom 3 : Multiplicative (ZMod 9 × ZMod 9) →*
      Multiplicative (ZMod 9 × ZMod 9))
  have hΩ : Nat.card Ω = 9 :=
    (Nat.card_congr (Equiv.subtypeEquivRight fun g => Iff.rfl)).trans sp48_card_three_mult
  have heq : H = Ω := Subgroup.eq_of_le_of_card_ge (fun h hh => hH h hh) (by omega)
  intro g hg
  rw [heq]
  exact hg

theorem sp48_card_centralizer_le {Y : Type} [Group Y] [Finite Y] {J P : Subgroup Y}
    (hJn : J.Normal) (eJ : ↥J ≃* projSp 2 (GaloisField 2 3))
    (hCJ : Subgroup.centralizer (J : Set Y) = ⊥)
    (hθ : aschbacherSolvableCore 3 J = ⊥) (hN81 : Nat.card (P ⊓ J : Subgroup Y) = 81)
    {E : Subgroup Y} (hE : CFSG.Assembly.IsElemAbelian 3 E) {f : Y} (hfE : f ∈ E)
    (hfJ : f ∉ J) :
    Nat.card (Subgroup.centralizer ({f} : Set Y) ⊓ (P ⊓ J) : Subgroup Y) ≤ 9 := by
  have hfn : f ∈ Subgroup.normalizer (J : Set Y) := by
    rw [Subgroup.normalizer_eq_top]
    exact Subgroup.mem_top f
  have hout := sp48_inducesOuterTheta hθ hCJ hfJ hfn
  have ha3 : f ^ 3 = 1 := hE.2 f hfE
  have e : ↥J ⧸ aschbacherSolvableCore 3 J ≃* StatedProj (StatedSp 2 (GaloisField 2 3)) :=
    (QuotientGroup.quotientMulEquivOfEq hθ).trans
      (QuotientGroup.quotientBot.trans
        (eJ.trans (CFSG.RankThree.PartTwo.Sec4.projSpEquivStatedProj 2 (GaloisField 2 3))))
  obtain ⟨-, σ, -, hσ, ⟨ι⟩⟩ := KFacts.exists_barCentralizer_mulEquiv_sp4 ha3 hout e
  have h8 : Nat.card (GaloisField 2 3) = 8 := by
    rw [GaloisField.card 2 3 (by norm_num)]
    norm_num
  have hk : Nat.card (CFSG.GH74.GLS.IVK.fixedField σ) = 2 := by
    have h3 : Nat.card (CFSG.GH74.GLS.IVK.fixedField σ) ^ 3 = 2 ^ 3 := by
      rw [hσ, h8]
      norm_num
    exact Nat.pow_left_injective (by norm_num) h3
  have hbar : Nat.card (Sec8.barCentralizer (Subgroup.zpowers f) J) = 720 := by
    rw [Nat.card_congr ι.toEquiv]
    exact Sec6.BThreeCensus.card_statedSp_two_of_card_two hk
  set C : Subgroup Y := Subgroup.centralizer ({f} : Set Y) ⊓ (P ⊓ J) with hCdef
  have hCN : C ≤ P ⊓ J := inf_le_right
  have hCJ' : C ≤ J := hCN.trans inf_le_right
  have hmem : ∀ c : ↥C, (QuotientGroup.mk (Subgroup.inclusion hCJ' c) :
      ↥J ⧸ aschbacherSolvableCore 3 J) ∈ Sec8.barCentralizer (Subgroup.zpowers f) J := by
    intro c
    have hcf : (c : Y) * f = f * (c : Y) :=
      Subgroup.mem_centralizer_singleton_iff.mp (Subgroup.mem_inf.mp c.2).1
    rw [KFacts.mem_barCentralizer_zpowers_iff hfn, Sec4.thetaQuotMulAut_mk]
    congr 1
    apply Subtype.ext
    show f * (c : Y) * f⁻¹ = (c : Y)
    rw [← hcf]
    group
  let ψ : ↥C →* (↥J ⧸ aschbacherSolvableCore 3 J) :=
    (QuotientGroup.mk' (aschbacherSolvableCore 3 J)).comp (Subgroup.inclusion hCJ')
  have hψ : Function.Injective ψ := by
    intro a b hab
    have hab' : (QuotientGroup.mk (Subgroup.inclusion hCJ' a) :
        ↥J ⧸ aschbacherSolvableCore 3 J) = QuotientGroup.mk (Subgroup.inclusion hCJ' b) := hab
    have h := QuotientGroup.eq.mp hab'
    rw [hθ, Subgroup.mem_bot, inv_mul_eq_one] at h
    have h2 : (a : Y) = (b : Y) := congrArg (fun x : ↥J => (x : Y)) h
    exact Subtype.ext h2
  have hrange : Nat.card ψ.range = Nat.card C :=
    (Nat.card_congr (MonoidHom.ofInjective hψ).toEquiv).symm
  have hle : ψ.range ≤ Sec8.barCentralizer (Subgroup.zpowers f) J := by
    intro y hy
    obtain ⟨c, rfl⟩ := MonoidHom.mem_range.mp hy
    exact hmem c
  have hdvd720 : Nat.card C ∣ 720 := by
    rw [← hrange, ← hbar]
    exact Subgroup.card_dvd_of_le hle
  have hdvd81 : Nat.card C ∣ 81 := by
    rw [← hN81]
    exact Subgroup.card_dvd_of_le hCN
  have h9 := Nat.dvd_gcd hdvd720 hdvd81
  norm_num at h9
  exact Nat.le_of_dvd (by norm_num) h9

theorem sp48_sylow_inputs {Y : Type} [Group Y] [Finite Y] {J : Subgroup Y} (hJn : J.Normal)
    (hJ : Nonempty (↥J ≃* projSp 2 (GaloisField 2 3)))
    (hCJ : Subgroup.centralizer (J : Set Y) = ⊥) (hY : Nat.card Y = 3 * Nat.card J)
    {E : Subgroup Y} (hE : CFSG.Assembly.IsElemAbelian 3 E) (hE27 : Nat.card E = 27)
    (hEJ : Nat.card (E ⊓ J : Subgroup Y) = 9)
    {P : Subgroup Y} (hP3 : IsPGroup 3 P) (hEP : E ≤ P) (hP : Nat.card P = 243) :
    Nat.card (P ⊓ J : Subgroup Y) = 81 ∧
    (∀ x ∈ P ⊓ J, ∀ y ∈ P ⊓ J, x * y = y * x) ∧
    (∀ x ∈ P ⊓ J, x ^ 9 = 1) ∧
    (∀ x ∈ P ⊓ J, x ^ 3 = 1 → x ∈ E) ∧
    (∀ f ∈ E, f ∉ J → ∀ x ∈ P ⊓ J, f * x = x * f → x ∈ E) := by
  obtain ⟨eJ⟩ := hJ
  have hJ' : Nat.card J = 1056706560 := sp48_card_of_iso eJ
  have hN81 : Nat.card (P ⊓ J : Subgroup Y) = 81 := sp48_card_inf hJ' hY hP
  have hθ : aschbacherSolvableCore 3 J = ⊥ := sp48_theta_eq_bot eJ hCJ hJ'
  obtain ⟨φ⟩ := sp48_nonempty_mulEquiv eJ (inf_le_right : P ⊓ J ≤ J) hN81
  refine ⟨hN81, ?_, ?_, ?_, ?_⟩
  · intro x hx y hy
    have h1 : φ ⟨x, hx⟩ * φ ⟨y, hy⟩ = φ ⟨y, hy⟩ * φ ⟨x, hx⟩ := mul_comm _ _
    rw [← map_mul, ← map_mul] at h1
    exact congrArg Subtype.val (φ.injective h1)
  · intro x hx
    have h1 : (⟨x, hx⟩ : ↥(P ⊓ J)) ^ 9 = 1 := by
      apply φ.injective
      rw [map_pow, sp48_pow_nine_mult (φ ⟨x, hx⟩), map_one]
    exact congrArg Subtype.val h1
  · intro x hx hx3
    have hEJP : E ⊓ J ≤ P ⊓ J := fun y hy =>
      Subgroup.mem_inf.mpr ⟨hEP (Subgroup.mem_inf.mp hy).1, (Subgroup.mem_inf.mp hy).2⟩
    have hK : Nat.card ((E ⊓ J).subgroupOf (P ⊓ J)) = 9 := by
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hEJP).toEquiv, hEJ]
    have hH : ∀ h ∈ ((E ⊓ J).subgroupOf (P ⊓ J)).map φ.toMonoidHom, h ^ 3 = 1 := by
      intro h hh
      obtain ⟨a, ha, rfl⟩ := Subgroup.mem_map.mp hh
      have haE : (a : Y) ∈ E := (Subgroup.mem_inf.mp (Subgroup.mem_subgroupOf.mp ha)).1
      have ha3 : a ^ 3 = 1 := Subtype.ext (by simpa using hE.2 _ haE)
      rw [← map_pow, ha3, map_one]
    have hHc : Nat.card (((E ⊓ J).subgroupOf (P ⊓ J)).map φ.toMonoidHom) = 9 := by
      rw [Subgroup.card_map_of_injective (f := φ.toMonoidHom) φ.injective, hK]
    have hx3' : (⟨x, hx⟩ : ↥(P ⊓ J)) ^ 3 = 1 := Subtype.ext (by simpa using hx3)
    obtain ⟨a, ha, hax⟩ := Subgroup.mem_map.mp
      (sp48_mem_of_three_torsion hH hHc (φ ⟨x, hx⟩) (by rw [← map_pow, hx3', map_one]))
    have hax' : a = ⟨x, hx⟩ := φ.injective hax
    rw [hax'] at ha
    exact (Subgroup.mem_inf.mp (Subgroup.mem_subgroupOf.mp ha)).1
  · intro f hfE hfJ x hx hfx
    have hle9 := sp48_card_centralizer_le hJn eJ hCJ hθ hN81 hE hfE hfJ
    have hBC : E ⊓ J ≤ Subgroup.centralizer ({f} : Set Y) ⊓ (P ⊓ J) := by
      intro b hb
      obtain ⟨hbE, hbJ⟩ := Subgroup.mem_inf.mp hb
      refine Subgroup.mem_inf.mpr ⟨Subgroup.mem_centralizer_singleton_iff.mpr ?_,
        Subgroup.mem_inf.mpr ⟨hEP hbE, hbJ⟩⟩
      exact congrArg Subtype.val (hE.1.is_comm.comm (⟨b, hbE⟩ : ↥E) ⟨f, hfE⟩)
    have heq : E ⊓ J = Subgroup.centralizer ({f} : Set Y) ⊓ (P ⊓ J) :=
      Subgroup.eq_of_le_of_card_ge hBC (by rw [hEJ]; exact hle9)
    have hxC : x ∈ Subgroup.centralizer ({f} : Set Y) ⊓ (P ⊓ J) :=
      Subgroup.mem_inf.mpr ⟨Subgroup.mem_centralizer_singleton_iff.mpr hfx.symm, hx⟩
    rw [← heq] at hxC
    exact (Subgroup.mem_inf.mp hxC).1

end CFSG.RankThree.PartTwo.Sec14.Ronan1422S
