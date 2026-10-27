module

public import CFSG.LocalAnalysis.SteinbergCDEvenOrderFourTools
public import CFSG.LocalAnalysis.ComponentClassification.OutcomeLocalPSLTwoSections
public import CFSG.LocalAnalysis.ComponentInitial.LinearCoverModel
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.PerfectOddCoverUnitary
public import CFSG.LocalAnalysis.SteinbergSFSingleCommRootStandardClosure
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.CardSupOfDisjointNormalizer
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter1section1.proposition_4_c
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Proposition82

public section

namespace CFSG.LocalAnalysis.SymplecticFourStandard

namespace PrincipalLayers

open Subgroup
open CFSG.Assembly.LowTwoRank (StatedProj StatedSL StatedScalars statedSL_eq_range_toGL
  projectiveSpecialLinearGroupEquivStatedProj)
open scoped MatrixGroups

section General

variable {X : Type*} [Group X]

@[expose] noncomputable def restrictTo {X' : Type*} [Group X'] (f : X →* X') {Y : Subgroup X}
    {D : Subgroup X'} (h : Y.map f = D) : ↥Y →* ↥D :=
  (f.comp Y.subtype).codRestrict D fun y => h ▸ mem_map_of_mem f y.2

variable {X' : Type*} [Group X'] {f : X →* X'} {Y : Subgroup X} {D : Subgroup X'}

theorem coe_restrictTo (h : Y.map f = D) (y : Y) : (restrictTo f h y : X') = f y :=
  rfl

theorem restrictTo_surjective (h : Y.map f = D) : Function.Surjective (restrictTo f h) := by
  rintro ⟨d, hd⟩
  rw [← h] at hd
  obtain ⟨y, hy, rfl⟩ := hd
  exact ⟨⟨y, hy⟩, rfl⟩

theorem mem_ker_restrictTo (h : Y.map f = D) {y : Y} :
    y ∈ (restrictTo f h).ker ↔ f y = 1 := by
  rw [MonoidHom.mem_ker, Subtype.ext_iff]
  rfl

theorem card_mul_relIndex {H K : Subgroup X} (hHK : H ≤ K) :
    Nat.card H * H.relIndex K = Nat.card K := by
  rw [relIndex, ← Nat.card_congr (subgroupOfEquivOfLe hHK).toEquiv, card_mul_index]

theorem exists_sylow_sup_zpowers [Finite X] {Y V : Subgroup X} {t : X}
    (hV : ∃ R : Sylow 2 ↥Y, (R : Subgroup ↥Y).map Y.subtype = V)
    (htY : t ∈ normalizer (Y : Set X)) (htV : t ∈ normalizer (V : Set X)) (ht : orderOf t = 2)
    (htn : t ∉ Y) :
    ∃ R : Sylow 2 ↥(Y ⊔ zpowers t),
      (R : Subgroup ↥(Y ⊔ zpowers t)).map (Y ⊔ zpowers t).subtype = V ⊔ zpowers t := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hVY, hV2, hidx⟩ := RootStandard.exists_sylow_map_iff.mp hV
  rw [RootStandard.exists_sylow_map_iff]
  have hdisj : ∀ {N : Subgroup X}, N ≤ Y → Disjoint N (zpowers t) := by
    intro N hN
    rw [disjoint_iff, eq_bot_iff]
    intro x hx
    obtain ⟨hxN, hxt⟩ := mem_inf.mp hx
    obtain ⟨m, rfl⟩ := mem_zpowers_iff.mp hxt
    have ht2 : t * t = 1 := by rw [← sq, ← ht, pow_orderOf_eq_one]
    rcases RootAxisTwoCore.zpow_eq_one_or_eq ht2 m with h1 | h1
    · rw [h1]
      exact one_mem _
    · rw [h1] at hxN
      exact absurd (hN hxN) htn
  have hcY := CFSG.GorensteinWalter.card_sup_eq_mul_of_disjoint_of_le_normalizer Y (zpowers t)
    (zpowers_le.mpr htY) (hdisj le_rfl)
  have hcV := CFSG.GorensteinWalter.card_sup_eq_mul_of_disjoint_of_le_normalizer V (zpowers t)
    (zpowers_le.mpr htV) (hdisj hVY)
  have hct : Nat.card (zpowers t) = 2 := by rw [Nat.card_zpowers, ht]
  rw [hct] at hcY hcV
  obtain ⟨a, ha⟩ := hV2.exists_card_eq
  refine ⟨sup_le_sup_right hVY _, IsPGroup.of_card (n := a + 1) (by rw [hcV, ha, pow_succ]), ?_⟩
  have h1 := card_mul_relIndex hVY
  have h2 := card_mul_relIndex (sup_le_sup_right hVY (zpowers t))
  rw [hcV, hcY, ← h1] at h2
  have h3 : Nat.card V * 2 * (V ⊔ zpowers t).relIndex (Y ⊔ zpowers t) =
      Nat.card V * 2 * V.relIndex Y := by rw [h2]; ring
  have hpos : 0 < Nat.card V * 2 := Nat.mul_pos Nat.card_pos (by norm_num)
  rwa [Nat.eq_of_mul_eq_mul_left hpos h3]

end General

section SLTwo

variable {F : Type*} [Field F] [CharP F 2]

theorem sl2_mul_self_eq_one {x : SL(2, F)} {k : ℕ} (hx : x ^ 2 ^ k = 1) : x * x = 1 := by
  have hdvd : orderOf x ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one hx
  obtain ⟨j, -, hjx⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd
  by_cases h2 : j ≤ 1
  · rw [← pow_two, ← orderOf_dvd_iff_pow_eq_one, hjx]
    exact pow_dvd_pow 2 (by omega)
  · exfalso
    have hd : 2 ^ (j - 2) ∣ orderOf x := by
      rw [hjx]
      exact pow_dvd_pow 2 (by omega)
    have h4 : orderOf (x ^ 2 ^ (j - 2)) = 4 := by
      rw [orderOf_pow_of_dvd (pow_ne_zero _ two_ne_zero) hd, hjx,
        Nat.pow_div (by omega) (by norm_num), show j - (j - 2) = 2 by omega]
    exact SteinbergCD.SL_two_orderOf_ne_four CharTwo.two_eq_zero _ h4

end SLTwo

section OddLinearTwo

theorem le_or_mul_self_eq_one {P : Type*} [Group P] {C : Subgroup P}
    (hC : ∀ x ∈ C, ∀ y ∈ C, x * y = y * x) (hidx : C.index = 2) {τ : P} (hτC : τ ∉ C)
    (hτ : τ * τ = 1) (hinv : ∀ c ∈ C, τ * c * τ⁻¹ = c⁻¹) {A : Subgroup P}
    (hA : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x) :
    A ≤ C ∨ ∀ x ∈ A, x * x = 1 := by
  by_cases h : A ≤ C
  · exact Or.inl h
  right
  obtain ⟨x, hxA, hxC⟩ := IsConcreteLE.not_le_iff_exists.mp h
  have hmem : ∀ y, y ∉ C → τ⁻¹ * y ∈ C := fun y hy => by
    rw [mul_mem_iff_of_index_two hidx]
    exact ⟨fun h1 => absurd (inv_mem_iff.mp h1) hτC, fun h1 => absurd h1 hy⟩
  have hout : ∀ y, y ∉ C → y * y = 1 := by
    intro y hy
    have hc := hmem y hy
    calc y * y = (τ * (τ⁻¹ * y) * τ⁻¹) * (τ * τ) * (τ⁻¹ * y) := by group
      _ = 1 := by rw [hinv _ hc, hτ, mul_one, inv_mul_cancel]
  intro y hy
  by_cases hyC : y ∈ C
  · have hc := hmem x hxC
    have h1 : x * y * x⁻¹ = y⁻¹ := by
      calc x * y * x⁻¹ = τ * ((τ⁻¹ * x) * y * (τ⁻¹ * x)⁻¹) * τ⁻¹ := by group
        _ = τ * y * τ⁻¹ := by rw [hC _ hc y hyC]; group
        _ = y⁻¹ := hinv y hyC
    rw [hA x hxA y hy, mul_inv_cancel_right] at h1
    calc y * y = y * y⁻¹ := by rw [← h1]
      _ = 1 := mul_inv_cancel y
  · exact hout y hyC

variable {k : Type} [Field k] [Finite k]

theorem false_of_odd_psl_two (hq : Odd (Nat.card k)) {D : Type*} [Group D]
    (η : D ≃* StatedProj (StatedSL 2 k)) {A E : Subgroup D} (hA : IsPGroup 2 A)
    (hAc : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x) {w : D} (hwA : w ∈ A) (hw : w * w ≠ 1)
    (hEA : E ≤ A) (hE : ∀ x ∈ E, x * x = 1) (hE4 : 4 ≤ Nat.card E) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨-, hSyl, -⟩ :=
    CFSG.ComponentClassification.OutcomeLocal.odd_projective_linear_two_elementary_two_sections hq
  set A' := A.map η.toMonoidHom
  obtain ⟨P, hP⟩ := (hA.map η.toMonoidHom).exists_le_sylow
  obtain ⟨C, hCcyc, -, hidx, τ, hτC, hτ, hinv⟩ := hSyl P
  have hCc : ∀ x ∈ C, ∀ y ∈ C, x * y = y * x := fun x hx y hy => by
    let := hCcyc.commGroup
    exact congrArg Subtype.val (mul_comm (⟨x, hx⟩ : C) ⟨y, hy⟩)
  have hτ2 : τ * τ = 1 := by
    have := pow_orderOf_eq_one τ
    rwa [hτ, sq] at this
  have hAc' : ∀ x ∈ A'.subgroupOf P, ∀ y ∈ A'.subgroupOf P, x * y = y * x := by
    intro x hx y hy
    obtain ⟨a, ha, hax⟩ := mem_map.mp (mem_subgroupOf.mp hx)
    obtain ⟨b, hb, hby⟩ := mem_map.mp (mem_subgroupOf.mp hy)
    apply Subtype.ext
    rw [coe_mul, coe_mul, ← hax, ← hby, ← map_mul, ← map_mul, hAc a ha b hb]
  rcases le_or_mul_self_eq_one hCc hidx hτC hτ2 hinv hAc' with hle | hsq
  · have hEP : E.map η.toMonoidHom ≤ P := (map_mono hEA).trans hP
    set E'' := (E.map η.toMonoidHom).subgroupOf P
    have hE''C : E'' ≤ C := fun x hx =>
      hle (mem_subgroupOf.mpr (map_mono hEA (mem_subgroupOf.mp hx)))
    have : IsCyclic C := hCcyc
    have : IsCyclic E'' := Subgroup.isCyclic_of_le hE''C
    have h2 := CFSG.ComponentClassification.OutcomeLocal.card_le_two_of_isCyclic_of_sq_eq_one
      (Z := E'') fun z => by
        obtain ⟨e, he, hez⟩ := mem_map.mp (mem_subgroupOf.mp z.2)
        apply Subtype.ext
        apply Subtype.ext
        change (((z : ↥P) : StatedProj (StatedSL 2 k))) ^ 2 = 1
        rw [← hez, pow_two, ← map_mul, hE e he, map_one]
    have hcard : Nat.card E'' = Nat.card E := by
      rw [Nat.card_congr (subgroupOfEquivOfLe hEP).toEquiv, card_map_of_injective η.injective]
    omega
  · have h1 := hsq ⟨η w, hP (mem_map_of_mem _ hwA)⟩ (mem_subgroupOf.mpr (mem_map_of_mem _ hwA))
    apply hw
    apply η.injective
    rw [map_mul, map_one]
    exact congrArg Subtype.val h1

end OddLinearTwo

section Models

open CFSG.LocalAnalysis.ComponentInitial

@[expose] noncomputable def statedProjEquivProjectiveSL (d : ℕ) (F : Type) [Field F] :
    StatedProj (StatedSL d F) ≃* LinearFlag.projectiveSL d F :=
  (projectiveSpecialLinearGroupEquivStatedProj d F).symm.trans
    (LinearCover.projectiveSpecialLinearEquivProjectiveSL d F)

@[expose] noncomputable def statedProjSLTwoEquiv (F : Type) [Field F] [CharP F 2] :
    StatedProj (StatedSL 2 F) ≃* SL(2, F) :=
  (statedProjEquivProjectiveSL 2 F).trans (LinearCover.projectiveSLTwoEquivSL F)

theorem charP_two_of_card {F : Type*} [Field F] [Finite F] {m : ℕ} (h : Nat.card F = 2 ^ m) :
    CharP F 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have := Fintype.ofFinite F
  exact charP_of_card_eq_prime_pow (f := m) (by rw [← Nat.card_eq_fintype_card]; exact h)

theorem scalars_statedSL_three {F : Type} [Field F] [Finite F] :
    IsCyclic ((StatedScalars (Fin 3) F).subgroupOf (StatedSL 3 F)) ∧
      Nat.card ((StatedScalars (Fin 3) F).subgroupOf (StatedSL 3 F)) ∣
        Nat.gcd 3 (Nat.card F - 1) := by
  refine CFSG.ShultStronglyClosedTI.PerfectOddCover.isCyclic_card_dvd_of_scalar _
    (fun z hz => ?_) (fun z hz => ?_)
  · rw [mem_subgroupOf, StatedScalars, ← Matrix.GeneralLinearGroup.center_eq_range_scalar] at hz
    exact hz
  · obtain ⟨c, hc⟩ := (mem_subgroupOf.mp hz : (z : GL (Fin 3) F) ∈ StatedScalars (Fin 3) F)
    obtain ⟨A, hA⟩ := (statedSL_eq_range_toGL 3 F).le z.2
    have hdet : (c : F) ^ 3 = 1 := by
      have h1 := A.2
      have h2 : (A : Matrix (Fin 3) (Fin 3) F) = Matrix.scalar (Fin 3) (c : F) := by
        rw [← Matrix.GeneralLinearGroup.coe_scalar, hc, ← hA]
        rfl
      rw [h2, Matrix.scalar_apply, Matrix.det_diagonal, Finset.prod_const, Finset.card_univ,
        Fintype.card_fin] at h1
      exact h1
    have hq : (c : F) ^ (Nat.card F - 1) = 1 := by
      have := Fintype.ofFinite F
      rw [Nat.card_eq_fintype_card]
      exact FiniteField.pow_card_sub_one_eq_one _ c.ne_zero
    have hg : (c : F) ^ Nat.gcd 3 (Nat.card F - 1) = 1 := pow_gcd_eq_one.2 ⟨hdet, hq⟩
    apply Subtype.ext
    rw [SubgroupClass.coe_pow, ← hc, ← map_pow, OneMemClass.coe_one]
    have hcu : c ^ Nat.gcd 3 (Nat.card F - 1) = 1 := Units.ext (by
      rw [Units.val_pow_eq_pow_val, hg, Units.val_one])
    rw [hcu, map_one]

end Models

end PrincipalLayers

end CFSG.LocalAnalysis.SymplecticFourStandard
