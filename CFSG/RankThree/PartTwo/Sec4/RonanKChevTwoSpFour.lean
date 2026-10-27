module

public import CFSG.RankThree.PartTwo.Sec4.RonanKChevTwoBasic
public import CFSG.RankThree.PartTwo.KFacts.K71InnerSp4
import CFSG.RankThree.PartTwo.KFacts.K71Sp48Graph
import CFSG.RankThree.SteinbergR3ECASymplecticPrimeSubfield
import CFSG.ClassicalInvolution.SL2Facts

public section

namespace CFSG.RankThree.PartTwo.Sec4.RonanKChevTwo

open CFSG CFSG.RankThree.PartTwo.Sec4.Item462AltProof
open CFSG.Assembly.RankThreeEven (projSp)

namespace SpFour

open CFSG.RankThree.PartTwo
open CFSG.Assembly.LowTwoRank (StatedSp StatedProj)
open CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag (proj)
open CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher (conjAut fieldAut)
open scoped MatrixGroups

section General

theorem center_eq_bot_of_mulEquiv {A B : Type*} [Group A] [Group B] (e : A ≃* B)
    (hB : Subgroup.center B = ⊥) : Subgroup.center A = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  have hex : e x ∈ Subgroup.center B := by
    rw [Subgroup.mem_center_iff]
    intro y
    obtain ⟨z, rfl⟩ := e.surjective y
    rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.mp hx z]
  rw [hB, Subgroup.mem_bot] at hex
  exact Subgroup.mem_bot.mpr (e.injective (hex.trans (map_one e).symm))

theorem eq_bot_of_isPGroup_two {X : Type*} [Group X] {U : Subgroup X} (hU : IsPGroup 2 U)
    (hinv : ∀ u ∈ U, u ^ 2 = 1 → u = 1) : U = ⊥ := by
  rw [eq_bot_iff]
  intro u hu
  rw [Subgroup.mem_bot]
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.mp hU) ⟨u, hu⟩
  rw [Subgroup.orderOf_mk] at hk
  rcases k with _ | k
  · rw [pow_zero] at hk
    exact orderOf_eq_one_iff.mp hk
  · exfalso
    have hc2 : (u ^ (2 ^ k)) ^ 2 = 1 := by
      rw [← pow_mul, ← pow_succ, ← hk, pow_orderOf_eq_one]
    have hdvd : orderOf u ∣ 2 ^ k :=
      orderOf_dvd_of_pow_eq_one (hinv _ (U.pow_mem hu _) hc2)
    rw [hk] at hdvd
    have h1 := Nat.le_of_dvd (by positivity) hdvd
    have h2 : 2 ^ k < 2 ^ (k + 1) := Nat.pow_lt_pow_right (by norm_num) (by omega)
    omega

theorem isQuasisimple_sl2 {F : Type} [Field F] [Finite F] (h4 : 4 ≤ Nat.card F) :
    IsQuasisimple SL(2, F) := by
  have hp : Group.IsPerfect SL(2, F) := CFSG.ClassicalInvolution.sl2_isPerfect h4
  have hs : IsSimpleGroup (SL(2, F) ⧸ Subgroup.center SL(2, F)) :=
    Matrix.ProjectiveSpecialLinearGroup.rank_two_simple h4
  refine ⟨hp, hs, ?_⟩
  by_contra h
  push Not at h
  have : IsMulCommutative (SL(2, F) ⧸ Subgroup.center SL(2, F)) := ⟨⟨h⟩⟩
  have : Group.IsPerfect (SL(2, F) ⧸ Subgroup.center SL(2, F)) :=
    Group.IsPerfect.ofSurjective (QuotientGroup.mk'_surjective _)
  exact Group.IsPerfect.not_isMulCommutative _ ‹_›

theorem not_isPerfect_perm_six : ¬ Group.IsPerfect (Equiv.Perm (Fin 6)) := by
  intro hp
  have hle : commutator (Equiv.Perm (Fin 6)) ≤ (Equiv.Perm.sign : Equiv.Perm (Fin 6) →* ℤˣ).ker :=
    Abelianization.commutator_subset_ker _
  have hmem : Equiv.swap (0 : Fin 6) 1 ∈ commutator (Equiv.Perm (Fin 6)) := by
    rw [hp.1]
    exact Subgroup.mem_top _
  have h1 := MonoidHom.mem_ker.mp (hle hmem)
  rw [Equiv.Perm.sign_swap (by decide)] at h1
  exact absurd h1 (by decide)

theorem card_eq_one_of_normal_perm_six (M : Subgroup (Equiv.Perm (Fin 6))) [M.Normal]
    (h3 : ¬ 3 ∣ Nat.card M) : Nat.card M = 1 := by
  by_contra hne
  have hnt : Nontrivial M := Finite.one_lt_card_iff_nontrivial.mp (by
    have := Nat.card_pos (α := M)
    omega)
  have hle : alternatingGroup (Fin 6) ≤ M :=
    Equiv.Perm.alternatingGroup_le_of_normal
      (by rw [Nat.card_eq_fintype_card, Fintype.card_fin]; norm_num) hnt
  have hdvd : Nat.card (alternatingGroup (Fin 6)) ∣ Nat.card M := Subgroup.card_dvd_of_le hle
  have hA : Nat.card (alternatingGroup (Fin 6)) = 360 := by
    rw [nat_card_alternatingGroup, Nat.card_eq_fintype_card, Fintype.card_fin]
    norm_num [Nat.factorial]
  rw [hA] at hdvd
  exact h3 ((by norm_num : 3 ∣ 360).trans hdvd)

theorem false_of_fixed_perm_six {X : Type*} [Group X] {β : MulAut X}
    (h : PullDatum β) (C : Subgroup X) (hC : ∀ x, x ∈ C ↔ β x = x)
    (e : C ≃* Equiv.Perm (Fin 6)) : False := by
  obtain ⟨R, U, hfix, hnorm, -, h3, hUR, -, hUnc⟩ := h
  have hRC : R ≤ C := fun r hr => (hC r).mpr (hfix r hr)
  have hN : (R.subgroupOf C).Normal := ⟨fun n hn g => by
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    exact hnorm g ((hC g).mp g.2) n hn⟩
  haveI : ((R.subgroupOf C).map e.toMonoidHom).Normal := hN.map _ e.surjective
  have hcard : Nat.card ((R.subgroupOf C).map e.toMonoidHom) = Nat.card R := by
    rw [Subgroup.card_map_of_injective e.injective]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hRC).toEquiv
  have h1 := card_eq_one_of_normal_perm_six _ (by rwa [hcard])
  rw [hcard] at h1
  have hR : R = ⊥ := Subgroup.card_eq_one.mp h1
  have hU : U = ⊥ := le_bot_iff.mp (hR ▸ hUR)
  apply hUnc
  rw [hU]
  infer_instance

end General

section Proj

variable {F : Type} [Field F] [CharP F 2]

noncomputable def projEquiv : StatedSp 2 F ≃* StatedProj (StatedSp 2 F) :=
  MulEquiv.ofBijective (proj 2 F) ⟨KFacts.proj_injective_of_charTwo,
    CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher.proj_surjective⟩

theorem center_statedProj_eq_bot : Subgroup.center (StatedProj (StatedSp 2 F)) = ⊥ :=
  center_eq_bot_of_mulEquiv projEquiv.symm KFacts.center_statedSp_eq_bot

theorem three_ne_zero_of_charTwo : (3 : F) ≠ 0 := by
  have h31 : (3 : F) = 1 := by
    have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
    linear_combination h2
  rw [h31]
  exact one_ne_zero

end Proj

section Inner

variable {F : Type} [Field F] [CharP F 2]

theorem eq_one_of_commute_ordThreeMat_of_mul_self {B : Matrix (Fin 2) (Fin 2) F}
    (hB : B * KFacts.ordThreeMat F = KFacts.ordThreeMat F * B) (hB2 : B * B = 1) : B = 1 := by
  have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
  have e00 := congrFun (congrFun hB 0) 0
  have e01 := congrFun (congrFun hB 0) 1
  have s00 := congrFun (congrFun hB2 0) 0
  have s01 := congrFun (congrFun hB2 0) 1
  simp [KFacts.ordThreeMat, Matrix.mul_apply, Fin.sum_univ_two] at e00 e01 s00 s01
  have hb : B 0 1 = 0 := by
    have hsq : B 0 1 ^ 2 = 0 := by
      linear_combination (-1 : F) * s01 - B 0 1 * e01 + B 0 0 * B 0 1 * h2
    exact pow_eq_zero_iff two_ne_zero |>.mp hsq
  have ha : B 0 0 = 1 := by
    have hsq : (B 0 0 - 1) ^ 2 = 0 := by
      linear_combination s00 - B 1 0 * hb - B 0 0 * h2 + h2
    have := pow_eq_zero_iff two_ne_zero |>.mp hsq
    linear_combination this
  have hc : B 1 0 = 0 := by linear_combination -e00 - hb
  have hd : B 1 1 = 1 := by linear_combination -e01 + ha - hb
  rw [Matrix.eta_fin_two B, ha, hb, hc, hd, Matrix.one_fin_two]

theorem eq_one_of_mem_centralizer_sp4T {u : StatedSp 2 F}
    (hu : u ∈ Subgroup.centralizer {KFacts.sp4T F}) (hu2 : u ^ 2 = 1)
    (hcomm : u * KFacts.sp4T' F = KFacts.sp4T' F * u) : u = 1 := by
  have h3 : (3 : F) ≠ 0 := three_ne_zero_of_charTwo
  set x : Subgroup.centralizer {KFacts.sp4T F} := ⟨u, hu⟩
  have hx2 : x * x = 1 := Subtype.ext (by
    change u * u = 1
    rw [← pow_two, hu2])
  have hB := KFacts.block0_mul_ordThreeMat h3 (KFacts.mul_planeBlock_eq_of_mem_centralizer hu)
  have hB2 : KFacts.block0 (((u : StatedSp 2 F) : GL (Fin 2 ⊕ Fin 2) F) :
        Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) *
      KFacts.block0 (((u : StatedSp 2 F) : GL (Fin 2 ⊕ Fin 2) F) :
        Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) = 1 := by
    have h := congrArg (KFacts.block0Hom F h3) hx2
    rwa [map_mul, map_one, KFacts.block0Hom_apply] at h
  obtain ⟨B₁, rfl⟩ := KFacts.mem_range_planeSp_one h3 hu
    (eq_one_of_commute_ordThreeMat_of_mul_self hB hB2)
  have hc : B₁ * KFacts.ordThreeSL F = KFacts.ordThreeSL F * B₁ := by
    apply KFacts.planeSp_injective 1
    rw [map_mul, map_mul]
    exact hcomm
  have hc' : (B₁ : Matrix (Fin 2) (Fin 2) F) * KFacts.ordThreeMat F =
      KFacts.ordThreeMat F * B₁ := by
    have h := congrArg (fun A : SL(2, F) => (A : Matrix (Fin 2) (Fin 2) F)) hc
    simpa [KFacts.coe_ordThreeSL] using h
  have hsq : (B₁ : Matrix (Fin 2) (Fin 2) F) * B₁ = 1 := by
    have h1 : B₁ ^ 2 = 1 := KFacts.planeSp_injective 1 (by rw [map_pow, hu2, map_one])
    have h := congrArg (fun A : SL(2, F) => (A : Matrix (Fin 2) (Fin 2) F)) h1
    simpa [pow_two] using h
  have hB₁ : B₁ = 1 := Subtype.ext (eq_one_of_commute_ordThreeMat_of_mul_self hc' hsq)
  rw [hB₁, map_one]

variable [Finite F]

theorem not_pullDatum_conj_sp4T (hF : 4 ≤ Nat.card F) :
    ¬ PullDatum (MulAut.conj (KFacts.sp4T F)) := by
  rintro ⟨R, U, hfix, hnorm, hsol, -, hUR, hU2, hUnc⟩
  have h3 : (3 : F) ≠ 0 := three_ne_zero_of_charTwo
  have hRC : ∀ r ∈ R, r ∈ Subgroup.centralizer {KFacts.sp4T F} := by
    intro r hr
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact ((conj_apply_eq_iff _ _).mp (hfix r hr)).symm
  set T := (KFacts.planeSp (F := F) 1).range
  have hTt : ∀ s ∈ T, MulAut.conj (KFacts.sp4T F) s = s := by
    rintro _ ⟨B, rfl⟩
    rw [conj_apply_eq_iff]
    exact KFacts.planeSp_commute _ _
  have hTC : ∀ s ∈ T, s ∈ Subgroup.centralizer {KFacts.sp4T F} := by
    intro s hs
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact ((conj_apply_eq_iff _ _).mp (hTt s hs)).symm
  have hTq : IsQuasisimple T :=
    CFSG.LocalCores.isQuasisimple_of_mulEquiv
      (MonoidHom.ofInjective (KFacts.planeSp_injective (F := F) 1)) (isQuasisimple_sl2 hF)
  have hTR : ∀ r ∈ R, ∀ s ∈ T, r * s * r⁻¹ ∈ T := by
    intro r hr s hs
    have hrC := hRC r hr
    have hsC := hTC s hs
    have hm : r * s * r⁻¹ ∈ Subgroup.centralizer {KFacts.sp4T F} :=
      mul_mem (mul_mem hrC hsC) (inv_mem hrC)
    refine KFacts.mem_range_planeSp_one h3 hm ?_
    have hs1 : KFacts.block0Hom F h3 ⟨s, hsC⟩ = 1 := by
      obtain ⟨B, rfl⟩ := hs
      rw [KFacts.block0Hom_apply, KFacts.coe_planeSp]
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [KFacts.block0, KFacts.planeBlock, CFSG.LieType.SteinbergBR.EvenSp.planeMat]
    have key : KFacts.block0Hom F h3 (⟨r, hrC⟩ * ⟨s, hsC⟩ * ⟨r, hrC⟩⁻¹) = 1 := by
      rw [map_mul, map_mul, hs1, mul_one, ← map_mul, mul_inv_cancel, map_one]
    rw [KFacts.block0Hom_apply] at key
    exact key
  have hcomm := commute_of_quasisimple hsol hTq (fun s hs r hr => hnorm s (hTt s hs) r hr) hTR
  have hinv : ∀ u ∈ U, u ^ 2 = 1 → u = 1 := fun u hu hu2 =>
    eq_one_of_mem_centralizer_sp4T (hRC u (hUR hu)) hu2
      (hcomm u (hUR hu) _ ⟨KFacts.ordThreeSL F, rfl⟩)
  apply hUnc
  rw [eq_bot_of_isPGroup_two hU2 hinv]
  infer_instance

end Inner

section Outer

variable {F : Type} [Field F] [Finite F] [CharP F 2]

theorem not_pullDatum_fieldAut (σ : F ≃+* F) : ¬ PullDatum (fieldAut 2 F σ) := by
  intro h
  set k := CFSG.GH74.GLS.IVK.fixedField σ
  have hC : ∀ y, y ∈ ((proj 2 F).comp (KFacts.spIncl σ)).range ↔ fieldAut 2 F σ y = y :=
    KFacts.mem_range_proj_spIncl_iff σ
  let e : StatedSp 2 k ≃* ((proj 2 F).comp (KFacts.spIncl σ)).range :=
    MonoidHom.ofInjective (KFacts.proj_spIncl_injective σ)
  by_cases hk : 4 ≤ Nat.card k
  · have hCq : IsQuasisimple ((proj 2 F).comp (KFacts.spIncl σ)).range :=
      CFSG.LocalCores.isQuasisimple_of_mulEquiv e
        (CFSG.LieType.Universal.Symplectic.isQuasisimple 2 k (by norm_num) (Or.inl (Or.inr hk)))
    have hZ : Subgroup.center ((proj 2 F).comp (KFacts.spIncl σ)).range = ⊥ :=
      center_eq_bot_of_mulEquiv e.symm KFacts.center_statedSp_eq_bot
    refine h.false_of_quasisimple_fixed _ hC hCq ?_
    rw [hZ, Subgroup.card_bot]
    exact odd_one
  · haveI : Fintype k := Fintype.ofFinite k
    have hk2 : Fintype.card k = 2 := by
      obtain ⟨m, -, hm⟩ := FiniteField.card k 2
      rw [← Nat.card_eq_fintype_card] at hm
      rw [← Nat.card_eq_fintype_card, hm]
      rw [hm] at hk
      have hm1 : 1 ≤ (m : ℕ) := m.pos
      rcases Nat.lt_or_ge (m : ℕ) 2 with hlt | hge
      · obtain hm' : (m : ℕ) = 1 := by omega
        rw [hm', pow_one]
      · exact absurd (le_trans (by norm_num) (Nat.pow_le_pow_right (by norm_num) hge)) hk
    obtain ⟨ω⟩ := CFSG.RankThree.CASymplecticSubfield.nonempty_statedSp_two_mulEquiv_perm hk2
    exact false_of_fixed_perm_six h _ hC (e.symm.trans ω)

end Outer

section Assembly

variable {F : Type} [Field F] [Finite F] [CharP F 2]

theorem not_pullDatum_sp4 (hF : 4 ≤ Nat.card F) (α : MulAut (StatedProj (StatedSp 2 F)))
    (hα : orderOf α = 3) : ¬ PullDatum α := by
  intro h
  have hα3 : α ^ 3 = 1 := by
    rw [← hα]
    exact pow_orderOf_eq_one α
  by_cases hD : α ∈ (conjAut 2 F).range
  · obtain ⟨A, hA⟩ := hD
    have hin : α ∈ (MulAut.conj : StatedProj (StatedSp 2 F) →* _).range := by
      rw [← hA]
      exact KFacts.conjAut_mem_inner_of_charTwo A
    obtain ⟨y, rfl, hy3, hy1⟩ := exists_conj_of_isInnerAut
      (conj_injective_of_center_eq_bot center_statedProj_eq_bot) hα hin
    have h1 := h.congr (projEquiv (F := F)).symm
    rw [KFacts.congr_mulAutConj] at h1
    have hx3 : (projEquiv (F := F)).symm y ^ 3 = 1 := by rw [← map_pow, hy3, map_one]
    have hx1 : (projEquiv (F := F)).symm y ≠ 1 := by
      rw [Ne, map_eq_one_iff _ (MulEquiv.injective _)]
      exact hy1
    obtain ⟨φ, hφ⟩ := KFacts.exists_mulAut_apply_sp4T_eq hx3 hx1
    have h2 := h1.conj φ⁻¹
    rw [mul_conj_mul_inv, ← hφ, MulAut.inv_apply_self] at h2
    exact not_pullDatum_conj_sp4T hF h2
  · obtain ⟨σ, -, H, rfl⟩ := KFacts.sp4_even_order_three_field_descent α hα3 hD
    have h2 := h.conj (conjAut 2 F H)⁻¹
    have heq : (conjAut 2 F H)⁻¹ * (conjAut 2 F H * fieldAut 2 F σ * (conjAut 2 F H)⁻¹) *
        (conjAut 2 F H)⁻¹⁻¹ = fieldAut 2 F σ := by group
    rw [heq] at h2
    exact not_pullDatum_fieldAut σ h2

end Assembly

theorem false_of_isQuasisimple_projSp_two_one {X : Type*} [Group X] (hX : IsQuasisimple X)
    (e : X ≃* projSp 2 (GaloisField 2 1)) : False := by
  have : Fintype (GaloisField 2 1) := Fintype.ofFinite _
  obtain ⟨ω⟩ := CFSG.RankThree.CASymplecticSubfield.nonempty_statedSp_two_mulEquiv_perm
    (k := GaloisField 2 1)
    (by rw [← Nat.card_eq_fintype_card, GaloisField.card 2 1 one_ne_zero, pow_one])
  let θ : X ≃* Equiv.Perm (Fin 6) :=
    ((e.trans (CFSG.PGLModel.projSpEquivStatedProj 2 (GaloisField 2 1))).trans
      projEquiv.symm).trans ω
  have := hX.1
  exact not_isPerfect_perm_six (Group.IsPerfect.ofSurjective (f := θ.toMonoidHom) θ.surjective)

end SpFour

theorem kChevTwo_projSp_two (n : ℕ) (hn : Odd n) :
    ∀ (X : Type) [Group X] [Finite X], IsQuasisimple X →
      Nonempty (X ≃* projSp 2 (GaloisField 2 n)) → ∀ β : MulAut X, orderOf β = 3 →
        ¬ InnThetaNoncyclic β := by
  intro X _ _ hX ⟨e⟩ β hβ
  have hn0 : n ≠ 0 := by
    rintro rfl
    exact Nat.not_odd_zero hn
  rcases Nat.lt_or_ge n 2 with hn1 | hn2
  · obtain rfl : n = 1 := by omega
    exact (SpFour.false_of_isQuasisimple_projSp_two_one hX e).elim
  · have hF : Nat.card (GaloisField 2 n) = 2 ^ n := GaloisField.card 2 n hn0
    have hF4 : 4 ≤ Nat.card (GaloisField 2 n) := by
      rw [hF]
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn2
    let e' := e.trans (CFSG.PGLModel.projSpEquivStatedProj 2 (GaloisField 2 n))
    exact not_innThetaNoncyclic_of_mulEquiv e'
      (SpFour.center_eq_bot_of_mulEquiv e' SpFour.center_statedProj_eq_bot)
      (SpFour.not_pullDatum_sp4 hF4) β hβ

end CFSG.RankThree.PartTwo.Sec4.RonanKChevTwo

end
