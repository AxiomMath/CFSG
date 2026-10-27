module

public import CFSG.Quasithin.Vol2.Ch12Sec6KGCompLie2BigG2
public import CFSG.Quasithin.Vol2.Ch12Sec6KGCompAlt
public import CFSG.Quasithin.Vol2.Ch12Sec6KGCompOdd
public import CFSG.LocalAnalysis.EvenBN.G2.LocalU
public import CFSG.LocalAnalysis.EvenSmallLie.GTwoFour.Centralizers
public import CFSG.LocalAnalysis.ComponentInitial.CLSFourGroupLinearThreeFour
public import CFSG.LinearAlgebra.SL2MinimalFaithfulMatrix
public import CFSG.RankThree.PartOne.K1214.Basic
import CFSG.Timmesfeld.Orders.Exceptional
public import CFSG.LocalAnalysis.EvenBN.Common.CommutatorFixed
public import CFSG.Quasithin.Vol2.Ch12Sec6KGComp

public section

namespace CFSG.Quasithin.H13.S126C

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Quasithin.H13.L32A.C.SkPf
open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.LocalAnalysis.ComponentInitial CFSG.ComponentClassification.UnbalancedCatalog

theorem exists_E9_g24 {K : Type}
    [Field K] [Finite K] (hK : Nat.card K = 4) :
    ∃ E : Subgroup (adjointGroup Tag.G2 K), IsElemAbelian 3 E ∧ Nat.card E = 9 := by
  have hinj : Function.Injective (g2Torus K) := fun a b hab =>
    rootDiagUnit_injective (congrArg Subtype.val hab)
  refine ⟨(g2Torus K).range, ⟨⟨⟨fun a b => ?_⟩⟩, ?_⟩, ?_⟩
  · obtain ⟨x, hx⟩ := a.2
    obtain ⟨y, hy⟩ := b.2
    apply Subtype.ext
    rw [Subgroup.coe_mul, Subgroup.coe_mul, ← hx, ← hy, ← map_mul, ← map_mul, mul_comm x y]
  · rintro _ ⟨x, rfl⟩
    rw [← map_pow, show x ^ 3 = 1 from funext fun i =>
      LinearThreeFourOuter.units_pow_three hK (x i), map_one]
  · rw [← Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv, Nat.card_fun,
      LinearThreeFourOuter.card_units_eq_three hK, Nat.card_eq_fintype_card, Fintype.card_fin]
    rfl


section G24

variable {K : Type} [Field K] [Finite K]

theorem not_nine_dvd_card_centralizer_g2c (hK : Nat.card K = 4) :
    ¬ 9 ∣ Nat.card (adjointGroup Tag.G2 K ⊓
      Subgroup.centralizer {pinnedX Tag.G2 K g2c 1} : Subgroup (ModGL Tag.G2 K)) := by
  have : CharP K 2 := LinearFieldFour.charP_two_of_card_eq_four hK
  have := finite_modGL (τ := Tag.G2) (K := K)
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨-, -, hQ2, hC, -, hRN, hQR, ⟨ρ, -, -, hρr, hρi⟩, -⟩ :=
    even_G2_highest_long_root_centralizer K
  rw [hC]
  intro h9
  have e1 := CFSG.RankThree.PartOne.K1214.card_sup_mul_card_inf_of_le_normalizer hRN
  rw [hQR, Subgroup.card_bot, mul_one] at e1
  have hR : Nat.card (g2RankOne K g2ir) = 60 := by
    rw [← hρr, ← Nat.card_congr (MonoidHom.ofInjective hρi).toEquiv,
      CFSG.SL2MinimalFaithful.card_specialLinearGroup_fin_two, hK]
    norm_num
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hQ2
  rw [e1, hR, hk] at h9
  have hcop : Nat.Coprime 9 (2 ^ k) := Nat.Coprime.pow_right _ (by norm_num)
  have := hcop.dvd_of_dvd_mul_left h9
  omega

theorem false_of_commute_g2c (hK : Nat.card K = 4) {c : K} (hc : c ≠ 0)
    {E : Subgroup (adjointGroup Tag.G2 K)} (hE : Nat.card E = 9)
    (hcomm : ∀ e ∈ E, (e : ModGL Tag.G2 K) * pinnedX Tag.G2 K g2c c =
      pinnedX Tag.G2 K g2c c * e) : False := by
  have : CharP K 2 := LinearFieldFour.charP_two_of_card_eq_four hK
  have := finite_modGL (τ := Tag.G2) (K := K)
  obtain ⟨j, hjJ, hjx⟩ :=
    CFSG.LocalAnalysis.EvenBN.G2.Model.exists_J₃_scalar (K := K) (Units.mk0 c hc)
  have hjA : j ∈ adjointGroup Tag.G2 K :=
    CFSG.LocalAnalysis.EvenBN.G2.Model.torusFix_le_adjointGroup K g2r hjJ
  have hj1 : j * pinnedX Tag.G2 K g2c 1 * j⁻¹ = pinnedX Tag.G2 K g2c c := by
    rw [hjx, Units.val_mk0, mul_one]
  let E₁ : Subgroup (ModGL Tag.G2 K) :=
    (E.map (adjointGroup Tag.G2 K).subtype).map (MulAut.conj j⁻¹).toMonoidHom
  have hE₁ : Nat.card E₁ = 9 := by
    rw [Subgroup.card_map_of_injective (MulAut.conj j⁻¹).injective,
      Subgroup.card_map_of_injective (adjointGroup Tag.G2 K).subtype_injective, hE]
  have hle : E₁ ≤ adjointGroup Tag.G2 K ⊓ Subgroup.centralizer {pinnedX Tag.G2 K g2c 1} := by
    rintro _ ⟨_, ⟨e, he, rfl⟩, rfl⟩
    refine ⟨?_, Subgroup.mem_centralizer_iff.mpr fun y hy => ?_⟩
    · change j⁻¹ * (e : ModGL Tag.G2 K) * j⁻¹⁻¹ ∈ adjointGroup Tag.G2 K
      exact mul_mem (mul_mem (inv_mem hjA) e.2) (inv_mem (inv_mem hjA))
    · rw [Set.mem_singleton_iff] at hy
      subst hy
      change pinnedX Tag.G2 K g2c 1 * (j⁻¹ * (e : ModGL Tag.G2 K) * j⁻¹⁻¹) =
        j⁻¹ * (e : ModGL Tag.G2 K) * j⁻¹⁻¹ * pinnedX Tag.G2 K g2c 1
      have h1 := hcomm e he
      rw [← hj1] at h1
      calc pinnedX Tag.G2 K g2c 1 * (j⁻¹ * (e : ModGL Tag.G2 K) * j⁻¹⁻¹) =
          j⁻¹ * ((j * pinnedX Tag.G2 K g2c 1 * j⁻¹) * e) * j := by group
        _ = j⁻¹ * (e * (j * pinnedX Tag.G2 K g2c 1 * j⁻¹)) * j := by rw [h1]
        _ = j⁻¹ * (e : ModGL Tag.G2 K) * j⁻¹⁻¹ * pinnedX Tag.G2 K g2c 1 := by group
  exact not_nine_dvd_card_centralizer_g2c hK (hE₁ ▸ Subgroup.card_dvd_of_le hle)

theorem false_of_autConf_g24 (hK : Nat.card K = 4) (h34 : ¬ IsPSL 3 2 2 (adjointGroup Tag.G2 K))
    {ν : MulAut (adjointGroup Tag.G2 K)} {Lb Pb : Subgroup (MulAut (adjointGroup Tag.G2 K))}
    (h : AutConf (adjointGroup Tag.G2 K) ν Lb Pb) (hP : Nat.card Pb = 9) : False := by
  have : CharP K 2 := LinearFieldFour.charP_two_of_card_eq_four hK
  have := finite_modGL (τ := Tag.G2) (K := K)
  have hU := isSylowTwoOf_g2U (K := K)
  obtain ⟨S, hS, hSν⟩ := h.sylow
  obtain ⟨g, hg⟩ := exists_map_conj_eq hS hU
  have h' := h.map (MulAut.conj g)
  have hfix : ∀ u ∈ (posUnipotent Tag.G2 K).subgroupOf (adjointGroup Tag.G2 K),
      MulAut.congr (MulAut.conj g) ν u = u := by
    intro u hu
    rw [← hg] at hu
    obtain ⟨s, hs, rfl⟩ := hu
    change MulAut.conj g (ν ((MulAut.conj g).symm (MulAut.conj g s))) = MulAut.conj g s
    rw [MulEquiv.symm_apply_apply, hSν s hs]
  obtain ⟨z, hzU, hzc, hν'⟩ := exists_eq_conj_of_fix (n4At_g2 hK.ge) h34 cbAt_g2
    ⟨1, by simpa using h'.sq⟩ hfix
  have hz1 : z ≠ 1 := by
    rintro rfl
    exact h'.ne_one (by rw [hν', map_one])
  have hzU' : (z : ModGL Tag.G2 K) ∈ CFSG.LocalAnalysis.EvenBN.G2.Model.U K := by
    rw [← CFSG.LocalAnalysis.EvenBN.G2.Model.S_inf_centralizer_S]
    refine ⟨hzU, Subgroup.mem_centralizer_iff.mpr fun x hx => ?_⟩
    have := hzc ⟨x, posUnipotent_le_adjointGroup hx⟩ (by rw [Subgroup.mem_subgroupOf]; exact hx)
    exact (congrArg Subtype.val this).symm
  obtain ⟨c, hc⟩ := mem_rootSubgroup.mp hzU'
  have hc0 : c ≠ 0 := by
    rintro rfl
    apply hz1
    apply Subtype.ext
    rw [← hc, pinnedX_zero]
    rfl
  set Pb' := Pb.map (MulAut.congr (MulAut.conj g)).toMonoidHom
  have hcj := conj_injective_of_center_eq_bot (center_adjointGroup_eq_bot (τ := Tag.G2) (K := K))
  have hPin : Pb' ≤ (MulAut.conj : adjointGroup Tag.G2 K →* MulAut _).range := fun p hp => by
    have h3 : p ^ 3 = 1 := h'.elem.2 p hp
    have hp4 : p = p * p * (p * p) := by
      calc p = p ^ 3 * p := by rw [h3, one_mul]
        _ = p * p * (p * p) := by simp only [pow_succ, pow_zero, one_mul, mul_assoc]
    rw [hp4]
    exact mul_mem (CFSG.EvenSmallLie.GTwoFour.mul_self_mem_inner hK p)
      (CFSG.EvenSmallLie.GTwoFour.mul_self_mem_inner hK p)
  have hcard : Nat.card (Pb'.comap (MulAut.conj : adjointGroup Tag.G2 K →* MulAut _)) = 9 := by
    rw [← Subgroup.card_map_of_injective hcj, Subgroup.map_comap_eq_self hPin,
      Subgroup.card_map_of_injective (MulAut.congr (MulAut.conj g)).injective, hP]
  refine false_of_commute_g2c hK hc0 hcard fun e he => ?_
  have h1 : MulAut.conj e * MulAut.conj z = MulAut.conj z * MulAut.conj e := by
    rw [← hν']
    exact h'.comm _ (h'.le he)
  have h2 : e * z = z * e := hcj (by rw [map_mul, map_mul, h1])
  rw [hc]
  exact congrArg Subtype.val h2

end G24

theorem not_g24 {Q : Type} [Group Q] {K L P T : Subgroup Q} {v : Q}
    (hQ : Vol2Native.SQTKHypCat Q) (h : Conf12626 K L P T v) :
    ¬ ChevalleyExceptionalModel ↥K .G2 2 2 := fun hM => by
  have := hQ.finite
  have hcard : Nat.card ↥K = CFSG.Open.ordG2 (2 ^ 2) :=
    CFSG.Timmesfeld.card_chevalleyExceptionalModel_two hM
  obtain ⟨-, F, _, _, hF, ⟨e⟩⟩ := hM
  have hF4 : Nat.card F = 4 := by rw [hF]; norm_num
  let e' : ↥K ≃* adjointGroup Tag.G2 F :=
    e.trans ((QuotientGroup.quotientMulEquivOfEq center_adjointGroup_eq_bot).trans
      QuotientGroup.quotientBot)
  have h34 : ¬ IsPSL 3 2 2 (adjointGroup Tag.G2 F) := fun h34 => by
    have h1 := card_of_isPSL34 h34
    rw [← Nat.card_congr e'.toEquiv, hcard] at h1
    revert h1
    unfold CFSG.Open.ordG2
    norm_num
  obtain ⟨E, hE, hE9⟩ := exists_E9_g24 hF4
  exact false_of_autConf_g24 hF4 h34 (h.autConf.map e') (h.card_map_rhoP_eq_nine hQ e'
    (fun z hz => by rwa [center_adjointGroup_eq_bot, Subgroup.mem_bot] at hz) hE hE9)

end CFSG.Quasithin.H13.S126C
