module

public import CFSG.RankThree.PartTwo.Sec12.Item125Act
import CFSG.RankThree.PartTwo.Sec19.Step1914Tri
import CFSG.Models.PGLSimple
import CFSG.RankThree.PartTwo.KFacts.L34Sections
public import CFSG.LocalAnalysis.ComponentInitial.LinearFlagElation
public import CFSG.RankThree.PartTwo.KFacts.AutKinds
import CFSG.Sporadic.Schreier.J4SSylowBase

public section

namespace CFSG.RankThree.PartTwo.Sec18

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.Assembly.RankThreeEven (projSL)
open CFSG.LocalAnalysis.ComponentInitial.LinearFlag (projectiveSL)
open CFSG.RankThree.PartTwo.KFacts.L34

namespace SylowFive

section AutLThreeFour

variable {F : Type*} [Field F]

private theorem false_of_pow_conj_mul_betaAut {σ : F ≃+* F} (hF : Nat.card F = 4)
    (hσ : ∀ a, σ a = a ^ 2) {e : projectiveSL 3 F} (he : e ∈ eZero F) {m : ℕ}
    (h : (MulAut.conj e * betaAut σ) ^ 3 ^ m = 1) : False := by
  have hββ : betaAut σ * betaAut σ = 1 := betaAut_mul_self hF hσ
  have hcomm : Commute (MulAut.conj e) (betaAut σ) := by
    have h1 : betaAut σ * MulAut.conj e * (betaAut σ)⁻¹ = MulAut.conj e := by
      rw [KFacts.mul_mulAutConj_mul_inv, betaAut_fixed hF hσ he]
    exact (mul_inv_eq_iff_eq_mul.mp h1).symm
  have hodd : ∀ n : ℕ, betaAut σ ^ 3 ^ n = betaAut σ := by
    intro n
    induction n with
    | zero => simp
    | succ n ih => rw [pow_succ, pow_mul, ih, pow_three', hββ, one_mul]
  rw [hcomm.mul_pow, ← map_pow, hodd] at h
  have hβq : betaAut σ = MulAut.conj ((e ^ 3 ^ m)⁻¹) := by
    rw [map_inv]
    exact eq_inv_of_mul_eq_one_right h
  have hq : (e ^ 3 ^ m)⁻¹ ∈ eZero F := (eZero F).inv_mem ((eZero F).pow_mem he _)
  have h3 : betaAut σ ^ 3 = 1 := by
    rw [hβq, ← map_pow, pow_three_of_mem_eZero hF hq, map_one]
  rw [pow_three', hββ, one_mul] at h3
  exact betaAut_ne_one hF h3

private theorem exists_mulEquiv_forall_mem_iff {X : Type*} [Group X] (hF : Nat.card F = 4)
    (ψ : X ≃* projectiveSL 3 F) {Eb : Subgroup X} (hEb : Nat.card Eb = 9) :
    ∃ ψ' : X ≃* projectiveSL 3 F, ∀ x, x ∈ Eb ↔ ψ' x ∈ eZero F := by
  have hE9 : Nat.card (Eb.map ψ.toMonoidHom) = 9 := by
    rw [Subgroup.card_map_of_injective ψ.injective, hEb]
  obtain ⟨g, hg⟩ := exists_eq_map_conj_eZero hF hE9
  refine ⟨ψ.trans (MulAut.conj g).symm, fun x => ?_⟩
  have h1 : x ∈ Eb ↔ ψ x ∈ Eb.map ψ.toMonoidHom := by
    rw [Subgroup.mem_map_equiv, ψ.symm_apply_apply]
  rw [h1, hg, Subgroup.mem_map_equiv]
  rfl

theorem exists_mem_conj_eq_of_fixes {X : Type*} [Group X] (hF : Nat.card F = 4)
    (ψ : X ≃* projectiveSL 3 F) {Eb : Subgroup X} (hEb : Nat.card Eb = 9) {ρ : MulAut X}
    (hρ : ∀ x ∈ Eb, ρ x = x) {m : ℕ} (hρm : ρ ^ 3 ^ m = 1) :
    ∃ x ∈ Eb, ρ = MulAut.conj x := by
  have := CFSG.LocalAnalysis.ComponentInitial.LinearFieldFour.finite_of_card_eq_four hF
  have := CFSG.LocalAnalysis.ComponentInitial.LinearFieldFour.charP_two_of_card_eq_four hF
  obtain ⟨ψ, hψ⟩ := exists_mulEquiv_forall_mem_iff hF ψ hEb
  set σ : F ≃+* F := frobeniusEquiv F 2
  have hσ : ∀ a, σ a = a ^ 2 := fun a => frobeniusEquiv_apply F 2 a
  set α : MulAut (projectiveSL 3 F) := MulAut.congr ψ ρ with hα
  have hαapp : ∀ z, α (ψ z) = ψ (ρ z) := fun z => by simp [hα, MulAut.congr_apply]
  have hfix : ∀ y ∈ eZero F, α y = y := by
    intro y hy
    obtain ⟨z, rfl⟩ := ψ.surjective y
    rw [hαapp, hρ z ((hψ z).mpr hy)]
  obtain ⟨e, he, h | h⟩ := (forall_fixes_eZero_iff hF hσ α).mp hfix
  · refine ⟨ψ.symm e, (hψ _).mpr (by simpa using he), ?_⟩
    ext z
    apply ψ.injective
    rw [← hαapp, h, MulAut.conj_apply, MulAut.conj_apply, map_mul, map_mul, map_inv,
      ψ.apply_symm_apply]
  · exfalso
    have hαm : α ^ 3 ^ m = 1 := by rw [hα, ← map_pow, hρm, map_one]
    rw [h] at hαm
    exact false_of_pow_conj_mul_betaAut hF hσ he hαm

end AutLThreeFour

variable {G : Type} [Group G] [Finite G]

theorem exists_mem_thetaQuotCentralizer_of_commute {L E : Subgroup G} (hLp : ⁅L, L⁆ = L)
    (eL : L ⧸ CFSG.pCore 2 L ≃* projSL 3 (GaloisField 2 2)) (hEL : E ≤ L)
    (hE9 : Nat.card E = 9) (hE3 : IsPGroup 3 E) {t : G}
    (htN : t ∈ Subgroup.normalizer (L : Set G)) (htE : ∀ e ∈ E, t * e = e * t) {k : ℕ}
    (htk : t ^ 3 ^ k = 1) :
    ∃ e ∈ E, t * e⁻¹ ∈ Sec4.thetaQuotCentralizer L := by
  have : IsSimpleGroup (projSL 3 (GaloisField 2 2)) :=
    CFSG.PGLModel.isSimpleGroup_projSL_of_two_le _ (by norm_num) (Or.inl (by norm_num))
      (Or.inl (by norm_num))
  have : IsSimpleGroup (L ⧸ CFSG.pCore 2 L) := eL.isSimpleGroup
  have : Group.IsPerfect L := Subgroup.isPerfect_iff.mpr hLp
  have : Group.IsPerfect (L ⧸ CFSG.pCore 2 L) := inferInstance
  have hθeq : aschbacherSolvableCore 3 L = CFSG.pCore 2 L :=
    Sec19.Step1914TriProof.theta_eq_pCore_two_of_isSimpleGroup
  set θ := aschbacherSolvableCore 3 L
  let ψ : L ⧸ θ ≃* projectiveSL 3 (GaloisField 2 2) :=
    ((QuotientGroup.quotientMulEquivOfEq hθeq).trans eL).trans
      (projSLEquivProjectiveSL 3 (GaloisField 2 2))
  set ρ : MulAut (L ⧸ θ) := Sec12.thetaBarAct L ⟨t, htN⟩ with hρ
  set E' : Subgroup L := E.subgroupOf L
  set Eb : Subgroup (L ⧸ θ) := E'.map (QuotientGroup.mk' θ)
  have hE'card : Nat.card E' = 9 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hEL).toEquiv, hE9]
  have hEb9 : Nat.card Eb = 9 := by
    have h1 := Sec19.Step1914TriProof.card_map_mul_card_ker_subgroupOf (QuotientGroup.mk' θ) E'
    have h2 : (QuotientGroup.mk' θ).ker.subgroupOf E' = ⊥ := by
      rw [Subgroup.eq_bot_iff_forall]
      intro x hx
      rw [Subgroup.mem_subgroupOf, MonoidHom.mem_ker, QuotientGroup.mk'_apply,
        QuotientGroup.eq_one_iff] at hx
      obtain ⟨j, hj⟩ := hE3 ⟨((x : L) : G), Subgroup.mem_subgroupOf.mp x.2⟩
      have h3 : (x : L) ^ 3 ^ j = 1 := by
        apply Subtype.ext
        simpa using congrArg Subtype.val hj
      exact Subtype.ext (Sec19.Step1914TriProof.eq_one_of_mem_theta' hx h3)
    rw [h2, Subgroup.card_bot, mul_one, hE'card] at h1
    exact h1
  have hfix : ∀ x ∈ Eb, ρ x = x := by
    rintro _ ⟨e', he', rfl⟩
    have he'E : (e' : G) ∈ E := Subgroup.mem_subgroupOf.mp he'
    have h1 : L.normalizerMonoidHom ⟨t, htN⟩ e' = e' :=
      Subtype.ext (by rw [Sec4.normalizerMonoidHom_apply_coe, htE _ he'E, mul_inv_cancel_right])
    rw [hρ, Sec12.thetaBarAct_mk, h1]
  have hρk : ρ ^ 3 ^ k = 1 := by
    have h1 : (⟨t, htN⟩ : Subgroup.normalizer (L : Set G)) ^ 3 ^ k = 1 :=
      Subtype.ext (by simpa using htk)
    rw [hρ, ← map_pow, h1, map_one]
  obtain ⟨x, hxEb, hx⟩ :=
    exists_mem_conj_eq_of_fixes card_galoisField_two_two ψ hEb9 hfix hρk
  obtain ⟨e', he', rfl⟩ := hxEb
  have he'E : (e' : G) ∈ E := Subgroup.mem_subgroupOf.mp he'
  have hen : (e' : G) ∈ Subgroup.normalizer (L : Set G) := Subgroup.le_normalizer e'.2
  have htn : t * (e' : G)⁻¹ ∈ Subgroup.normalizer (L : Set G) :=
    (Subgroup.normalizer _).mul_mem htN ((Subgroup.normalizer _).inv_mem hen)
  refine ⟨e', he'E, (Sec12.mem_thetaQuotCentralizer_iff_thetaBarAct htn).mpr ?_⟩
  have h1 : (⟨t * (e' : G)⁻¹, htn⟩ : Subgroup.normalizer (L : Set G)) =
      ⟨t, htN⟩ * ⟨(e' : G), hen⟩⁻¹ := Subtype.ext rfl
  rw [h1, map_mul, map_inv, ← hρ, hx, Sec12.thetaBarAct_of_mem e'.2, mul_inv_cancel]

end SylowFive

end CFSG.RankThree.PartTwo.Sec18
