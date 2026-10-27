module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveBCoordBCornerModel
import CFSG.LocalAnalysis.StandardType.GGSpTwoPlaneTorusPair
import CFSG.LocalAnalysis.StandardType.GGBstarLemmaC
import CFSG.LocalAnalysis.StandardType.GGSignedCoordRefl
import CFSG.LocalAnalysis.StandardType.GGStdSubSmallSpTwoDelta
import CFSG.LocalAnalysis.StandardType.GGSecFiveBProperRootPerm
import CFSG.LocalAnalysis.StandardType.GGTableBUnitDvdLabel
import Mathlib.LinearAlgebra.BilinearForm.Orthogonal
import Mathlib.LinearAlgebra.Matrix.BilinearForm
import CFSG.ClassicalGroups.Symplectic.StandardForm
import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.GLVecAction

public section

namespace CFSG.StandardType

open CFSG.Assembly TwoThree Matrix
open SpCoord Multiplicative

open scoped Matrix

variable {G : Type} [Group G] [Finite G]

private def sympFixed {r : ℕ} (U : Subgroup (CFSG.Open.StatedSp r (ZMod 2))) :
    Submodule (ZMod 2) (Fin r ⊕ Fin r → ZMod 2) where
  carrier := {v | ∀ u ∈ U,
    ((u : CFSG.Open.StatedSp r (ZMod 2)) : GL (Fin r ⊕ Fin r) (ZMod 2)) *ᵥ v = v}
  zero_mem' := by
    intro u _
    rw [Matrix.mulVec_zero]
  add_mem' := by
    intro v w hv hw u hu
    rw [Matrix.mulVec_add, hv u hu, hw u hu]
  smul_mem' := by
    intro c v hv u hu
    rw [Matrix.mulVec_smul, hv u hu]

private noncomputable def sympRadical {r : ℕ} (U : Subgroup (CFSG.Open.StatedSp r (ZMod 2))) :
    Submodule (ZMod 2) (Fin r ⊕ Fin r → ZMod 2) :=
  (CFSG.ClassicalGroups.Symplectic.spForm r (ZMod 2)).orthogonal (sympFixed U)

private lemma spForm_mulVec {r : ℕ} {A : GL (Fin r ⊕ Fin r) (ZMod 2)}
    (hA : A ∈ CFSG.Open.StatedSp r (ZMod 2)) (u v : Fin r ⊕ Fin r → ZMod 2) :
    CFSG.ClassicalGroups.Symplectic.spForm r (ZMod 2) (A *ᵥ u) (A *ᵥ v) =
      CFSG.ClassicalGroups.Symplectic.spForm r (ZMod 2) u v :=
  (CFSG.ClassicalGroups.Symplectic.mem_statedSp_iff_forall A).mp hA u v

@[instance_reducible]
private instance instGlMulAction (r : ℕ) :
    MulAction (GL (Fin r ⊕ Fin r) (ZMod 2)) (Fin r ⊕ Fin r → ZMod 2) :=
  CFSG.EvenSporadicStandard.Induction.AutBound.glVecAction

@[instance_reducible]
private instance instStatedSpMulAction (r : ℕ) :
    MulAction (CFSG.Open.StatedSp r (ZMod 2)) (Fin r ⊕ Fin r → ZMod 2) :=
  MulAction.compHom _ (Subgroup.subtype (CFSG.Open.StatedSp r (ZMod 2)))

@[instance_reducible]
private instance instSubgroupMulAction {r : ℕ}
    (U : Subgroup (CFSG.Open.StatedSp r (ZMod 2))) :
    MulAction ↥U (Fin r ⊕ Fin r → ZMod 2) :=
  MulAction.compHom _ U.subtype

private lemma statedSp_smul_eq_mulVec {r : ℕ} (g : CFSG.Open.StatedSp r (ZMod 2))
    (v : Fin r ⊕ Fin r → ZMod 2) :
    g • v = ((g : GL (Fin r ⊕ Fin r) (ZMod 2)) :
      Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) (ZMod 2)) *ᵥ v := rfl

private lemma subgroup_smul_eq_mulVec {r : ℕ} {U : Subgroup (CFSG.Open.StatedSp r (ZMod 2))}
    (u : ↥U) (v : Fin r ⊕ Fin r → ZMod 2) :
    u • v = ((u : CFSG.Open.StatedSp r (ZMod 2)) :
      GL (Fin r ⊕ Fin r) (ZMod 2)) *ᵥ v := rfl

private lemma sympFixed_invariant {r : ℕ} {U Y : Subgroup (CFSG.Open.StatedSp r (ZMod 2))}
    (hYU : ∀ y ∈ Y, ∀ u ∈ U, y * u * y⁻¹ ∈ U) :
    ∀ y ∈ Y, ∀ c ∈ sympFixed U,
      ((y : CFSG.Open.StatedSp r (ZMod 2)) : GL (Fin r ⊕ Fin r) (ZMod 2)) *ᵥ c ∈ sympFixed U := by
  intro y hy c hc u hu
  rw [← statedSp_smul_eq_mulVec u, ← statedSp_smul_eq_mulVec y]
  have hmul : u • (y • c) = (u * y) • c := (mul_smul u y c).symm
  rw [hmul, show u * y = y * (y⁻¹ * u * y) by group]
  rw [show (y * (y⁻¹ * u * y)) • c = y • ((y⁻¹ * u * y) • c) from
    mul_smul y (y⁻¹ * u * y) c]
  have hyu : y⁻¹ * u * y ∈ U := by
    simpa using hYU y⁻¹ (Subgroup.inv_mem Y hy) u hu
  congr 1
  rw [statedSp_smul_eq_mulVec]
  exact hc (y⁻¹ * u * y) hyu

private lemma sympRadical_invariant {r : ℕ} {U Y : Subgroup (CFSG.Open.StatedSp r (ZMod 2))}
    (hYU : ∀ y ∈ Y, ∀ u ∈ U, y * u * y⁻¹ ∈ U) :
    ∀ y ∈ Y, ∀ x ∈ sympRadical U,
      ((y : CFSG.Open.StatedSp r (ZMod 2)) : GL (Fin r ⊕ Fin r) (ZMod 2)) *ᵥ x ∈ sympRadical U := by
  intro y hy x hx
  rw [sympRadical, LinearMap.BilinForm.mem_orthogonal_iff] at hx ⊢
  intro c hc
  have hci : ((y⁻¹ : CFSG.Open.StatedSp r (ZMod 2)) :
      GL (Fin r ⊕ Fin r) (ZMod 2)) *ᵥ c ∈ sympFixed U :=
    sympFixed_invariant hYU y⁻¹ (Subgroup.inv_mem Y hy) c hc
  have hx' : CFSG.ClassicalGroups.Symplectic.spForm r (ZMod 2)
      (((y⁻¹ : CFSG.Open.StatedSp r (ZMod 2)) :
        GL (Fin r ⊕ Fin r) (ZMod 2)) *ᵥ c) x = 0 := hx _ hci
  rw [← hx']
  have hgl : ((y⁻¹ : CFSG.Open.StatedSp r (ZMod 2)) :
      GL (Fin r ⊕ Fin r) (ZMod 2)) *
      ((y : CFSG.Open.StatedSp r (ZMod 2)) :
        GL (Fin r ⊕ Fin r) (ZMod 2)) = 1 := by
    rw [← Subgroup.coe_mul, inv_mul_cancel, Subgroup.coe_one]
  have hAx : (((y⁻¹ : CFSG.Open.StatedSp r (ZMod 2)) :
        GL (Fin r ⊕ Fin r) (ZMod 2)) :
        Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) (ZMod 2)) *ᵥ
      ((((y : CFSG.Open.StatedSp r (ZMod 2)) :
        GL (Fin r ⊕ Fin r) (ZMod 2)) :
        Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) (ZMod 2)) *ᵥ x) = x := by
    rw [Matrix.mulVec_mulVec, ← Units.val_mul, hgl, Units.val_one, Matrix.one_mulVec]
  have hinv := spForm_mulVec (A := ((y⁻¹ : CFSG.Open.StatedSp r (ZMod 2)) :
    GL (Fin r ⊕ Fin r) (ZMod 2))) (y⁻¹).2 c
    (((y : CFSG.Open.StatedSp r (ZMod 2)) :
      GL (Fin r ⊕ Fin r) (ZMod 2)) *ᵥ x)
  rw [hAx] at hinv
  exact hinv.symm

private lemma sympFixed_ne_top {r : ℕ} {U : Subgroup (CFSG.Open.StatedSp r (ZMod 2))}
    (hU : U ≠ ⊥) : sympFixed U ≠ ⊤ := by
  intro htop
  apply hU
  rw [Subgroup.eq_bot_iff_forall]
  intro u hu
  have hfix : ∀ v : Fin r ⊕ Fin r → ZMod 2,
      ((u : CFSG.Open.StatedSp r (ZMod 2)) : GL (Fin r ⊕ Fin r) (ZMod 2)) *ᵥ v = v := by
    intro v
    exact (show v ∈ sympFixed U from htop ▸ Submodule.mem_top) u hu
  apply Subtype.ext
  apply Units.ext
  apply Matrix.ext_of_mulVec_single
  intro i
  rw [hfix]
  exact (Matrix.one_mulVec _).symm

private lemma sympRadical_ne_bot {r : ℕ} {U : Subgroup (CFSG.Open.StatedSp r (ZMod 2))}
    (hU : U ≠ ⊥) : sympRadical U ≠ ⊥ := by
  intro hbot
  have hdim := LinearMap.BilinForm.finrank_orthogonal (B :=
    CFSG.ClassicalGroups.Symplectic.spForm r (ZMod 2))
    (CFSG.ClassicalGroups.Symplectic.spForm_nondegenerate (m := r) (K := ZMod 2)) (sympFixed U)
  have h0 : Module.finrank (ZMod 2) ↥((CFSG.ClassicalGroups.Symplectic.spForm r
      (ZMod 2)).orthogonal (sympFixed U)) = 0 := by
    change Module.finrank (ZMod 2) ↥(sympRadical U) = 0
    rw [hbot]
    simp
  rw [h0] at hdim
  have hle : Module.finrank (ZMod 2) (Fin r ⊕ Fin r → ZMod 2) ≤
      Module.finrank (ZMod 2) ↥(sympFixed U) := by omega
  exact sympFixed_ne_top hU (Submodule.eq_top_of_finrank_eq
    (le_antisymm (Submodule.finrank_le _) hle))

private lemma two_dvd_card_sympRadical {r : ℕ} {U : Subgroup (CFSG.Open.StatedSp r (ZMod 2))}
    (hU : U ≠ ⊥) : 2 ∣ Nat.card ↥(sympRadical U) := by
  have hnt : Nontrivial ↥(sympRadical U) :=
    Submodule.nontrivial_iff_ne_bot.mpr (sympRadical_ne_bot hU)
  have h2 : 2 ≤ Nat.card ↥(sympRadical U) :=
    Finite.one_lt_card_iff_nontrivial.mpr hnt
  have hcard : Nat.card ↥(sympRadical U) =
      2 ^ Module.finrank (ZMod 2) ↥(sympRadical U) := by
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2)]
    simp
  rw [hcard]
  refine dvd_pow_self 2 ?_
  rintro h0
  rw [h0, pow_zero] at hcard
  omega

private def sympRadicalSubMulAction {r : ℕ} (U : Subgroup (CFSG.Open.StatedSp r (ZMod 2))) :
    SubMulAction ↥U (Fin r ⊕ Fin r → ZMod 2) where
  carrier := (sympRadical U : Set (Fin r ⊕ Fin r → ZMod 2))
  smul_mem' := by
    intro u x hx
    exact sympRadical_invariant (Y := U) (fun y hy u hu =>
      U.mul_mem (U.mul_mem hy hu) (U.inv_mem hy)) u.1 u.2 x hx

@[instance_reducible]
private instance instSympRadicalSubMulActionMulAction {r : ℕ}
    (U : Subgroup (CFSG.Open.StatedSp r (ZMod 2))) :
    MulAction ↥U ↥(sympRadicalSubMulAction U) :=
  SubMulAction.SMulMemClass.toMulAction (sympRadicalSubMulAction U)

private lemma exists_fixed_mem_sympRadical {r : ℕ} {U : Subgroup (CFSG.Open.StatedSp r (ZMod 2))}
    (hU : U ≠ ⊥) (hU2 : IsPGroup 2 U) :
    ∃ x ∈ sympRadical U, x ≠ 0 ∧ ∀ u ∈ U,
      ((u : CFSG.Open.StatedSp r (ZMod 2)) : GL (Fin r ⊕ Fin r) (ZMod 2)) *ᵥ x = x := by
  have hpdvd : 2 ∣ Nat.card ↥(sympRadicalSubMulAction U) := two_dvd_card_sympRadical hU
  have hfix0 : (⟨0, (sympRadical U).zero_mem⟩ : ↥(sympRadicalSubMulAction U)) ∈
      MulAction.fixedPoints ↥U ↥(sympRadicalSubMulAction U) := by
    rw [MulAction.mem_fixedPoints]
    intro u
    apply Subtype.ext
    change ((u : ↥U) • (0 : Fin r ⊕ Fin r → ZMod 2)) = 0
    rw [subgroup_smul_eq_mulVec]
    simp
  obtain ⟨b, hbfix, hb0⟩ :=
    hU2.exists_fixed_point_of_prime_dvd_card_of_fixed_point
      (α := ↥(sympRadicalSubMulAction U)) hpdvd hfix0
  refine ⟨(b : Fin r ⊕ Fin r → ZMod 2), b.2, ?_, ?_⟩
  · intro hb
    exact hb0 (Subtype.ext (by simpa using hb.symm))
  · intro u hu
    have h := congrArg (Subtype.val) (hbfix ⟨u, hu⟩)
    change ((⟨u, hu⟩ : ↥U) • (b : Fin r ⊕ Fin r → ZMod 2)) = (b : Fin r ⊕ Fin r → ZMod 2) at h
    rw [subgroup_smul_eq_mulVec] at h
    exact h

private lemma sympFixed_inf_sympRadical_isotropic {r : ℕ}
    {U : Subgroup (CFSG.Open.StatedSp r (ZMod 2))} :
    ∀ u ∈ sympFixed U ⊓ sympRadical U, ∀ v ∈ sympFixed U ⊓ sympRadical U,
      u ⬝ᵥ ((Matrix.fromBlocks 0 1 (-1) 0 :
        Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) (ZMod 2)) *ᵥ v) = 0 := by
  intro u hu v hv
  rw [sympRadical] at hv
  have hvX : CFSG.ClassicalGroups.Symplectic.spForm r (ZMod 2) u v = 0 :=
    (LinearMap.BilinForm.mem_orthogonal_iff.mp hv.2) u hu.1
  rw [CFSG.ClassicalGroups.Symplectic.spForm_apply] at hvX
  simpa [CFSG.ClassicalGroups.Symplectic.spJ] using hvX

private theorem exists_isotropicSubmodule_of_twoSub {r : ℕ}
    (U : Subgroup (CFSG.Open.StatedSp r (ZMod 2))) (hU : U ≠ ⊥) (hU2 : IsPGroup 2 U)
    (Y : Subgroup (CFSG.Open.StatedSp r (ZMod 2)))
    (hYU : ∀ y ∈ Y, ∀ u ∈ U, y * u * y⁻¹ ∈ U) :
    ∃ W : Submodule (ZMod 2) (Fin r ⊕ Fin r → ZMod 2), W ≠ ⊥ ∧
      (∀ u ∈ W, ∀ v ∈ W,
        u ⬝ᵥ ((Matrix.fromBlocks 0 1 (-1) 0 :
          Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) (ZMod 2)) *ᵥ v) = 0) ∧
      (∀ y ∈ Y, ∀ w ∈ W,
        ((y : GL (Fin r ⊕ Fin r) (ZMod 2)) :
          Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) (ZMod 2)) *ᵥ w ∈ W) := by
  obtain ⟨x, hxX, hx0, hxfix⟩ := exists_fixed_mem_sympRadical hU hU2
  refine ⟨sympFixed U ⊓ sympRadical U, ?_, sympFixed_inf_sympRadical_isotropic, ?_⟩
  · intro hbot
    have hxW : x ∈ sympFixed U ⊓ sympRadical U :=
      ⟨fun u hu => hxfix u hu, hxX⟩
    rw [hbot, Submodule.mem_bot] at hxW
    exact hx0 hxW
  · intro y hy w hw
    exact ⟨sympFixed_invariant hYU y hy w hw.1, sympRadical_invariant hYU y hy w hw.2⟩

private theorem exists_twoSub_of_symplectic {G : Type} [Group G] [Finite G]
    {B Bs L : Subgroup G} {n : ℕ} {x : G} {D J : Subgroup G}
    (hC : GGConfig 3 B Bs x L D J) {K : Type} [Field K] [Finite K]
    {I : Set (MulAut (LargeEvenProj (LargeEvenSpGroup K (n - 1))))}
    {θ : L ⧸ Subgroup.center L ≃* LargeEvenProj (LargeEvenSpGroup K (n - 1))}
    (hn : 5 ≤ n) (hK : Nat.card K = 2) (hL : commutator L = ⊤)
    (hBN : Bs ≤ Subgroup.normalizer (L : Set G))
    (h3 : ∀ b ∈ Bs, ∃ φ ∈ I,
      LargeEvenInduces θ (fun l l' => (l' : G) = b⁻¹ * l * b) φ)
    (hne : B ≠ Bs) :
    ∃ U : Subgroup G, U ≤ L ∧ U ≠ ⊥ ∧ IsPGroup 2 U ∧
      B ≤ Subgroup.normalizer (U : Set G) := by
  have hchar : CharP K 2 :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic
      (k := 1) Nat.prime_two (by norm_num) (by simpa using hK)
  have hlift : GGTorusLift 3 (n - 2) (LargeEvenProj (LargeEvenSpGroup K (n - 1))) := by
    have h := @TwoThree.ggTorusLift_sp_two K _ _ hchar (n - 2) hK
    rw [show n - 2 + 1 = n - 1 by omega] at h
    exact h
  have hnc : ∃ S : Subgroup G, S ≤ L ∧ IsPGroup 3 S ∧ ¬ IsCyclic S :=
    UnitTB.exists_noncyclic_of_torusLift Nat.prime_three (by omega) hL θ hlift
  have hBBs : B ≤ Bs := hC.2.1.1
  have h3B : ∀ b ∈ B, ∃ φ ∈ I,
      LargeEvenInduces θ (fun l l' => (l' : G) = b⁻¹ * l * b) φ :=
    fun b hb => h3 b (hBBs hb)
  have hOD : GGOutdiagOdd 3 (LargeEvenProj (LargeEvenSpGroup K (n - 1))) I :=
    @SpTwo.ggOutdiagOdd_spTwo K _ _ hchar (n - 1) hK (by omega) I
  exact hC.innLocal_of_ne hnc hL θ (hBBs.trans hBN) h3B hOD hne

private theorem exists_twoSub_of_marking {G : Type} [Group G] [Finite G]
    {B Bs L : Subgroup G} {n : ℕ} {x : G} {D J : Subgroup G}
    (hC : GGConfig 3 B Bs x L D J)
    (hM : GGInnerDiagOnLabel (fun _ lab => (lab.tag = .B ∨ lab.tag = .C) ∧
      lab.rank = n - 1 ∧ lab.n = 1) 3 Bs L) (hn : 5 ≤ n) (hne : B ≠ Bs) :
    ∃ U : Subgroup G, U ≤ L ∧ U ≠ ⊥ ∧ IsPGroup 2 U ∧
      B ≤ Subgroup.normalizer (U : Set G) := by
  obtain ⟨hL, lab, hlab, hraw⟩ := hM
  obtain ⟨R₀, _, I₀, F₀, hQ₀⟩ := largeEvenRawDatum_exists hraw
  obtain ⟨-, -, -, hS, -, -⟩ := hQ₀
  obtain ⟨t, r, nn⟩ := lab
  obtain ⟨htag, hr, hnn⟩ := hS
  subst hr
  subst hnn
  rcases htag with rfl | rfl <;> dsimp only [LargeEvenRawDatum] at hraw
  all_goals
    obtain ⟨K, i1, i2, hK, hQ⟩ := hraw
    obtain ⟨-, -, θ, -, hBN, h3⟩ := hQ
    exact exists_twoSub_of_symplectic hC hn (by simpa using hK) hL hBN h3 hne

private theorem exists_P_of_model {G : Type} [Group G] [Finite G]
    {B Bs L U : Subgroup G} {n : ℕ}
    (φ : CFSG.Open.StatedSp (n - 1) (ZMod 2) →* G)
    (ρ : ↥Bs →* CFSG.Open.StatedSp (n - 1) (ZMod 2))
    (hφ : Function.Injective φ) (hφL : φ.range = L)
    (hρ : ∀ (b : ↥Bs) (g : CFSG.Open.StatedSp (n - 1) (ZMod 2)),
      φ (ρ b * g * (ρ b)⁻¹) = (b : G) * φ g * (b : G)⁻¹)
    (hρT : ρ.range = (spPlaneTorus (K := ZMod 2) (r := n - 1)).range)
    (hUL : U ≤ L) (hU : U ≠ ⊥) (hU2 : IsPGroup 2 U)
    (hBU : B ≤ Subgroup.normalizer (U : Set G)) :
    ∃ P : CFSG.Open.StatedSp (n - 1) (ZMod 2), P * P = 1 ∧
      (∀ t ∈ (spPlaneTorus (K := ZMod 2) (r := n - 1)).range,
        P * t * P⁻¹ ∈ (spPlaneTorus (K := ZMod 2) (r := n - 1)).range) ∧
      (∀ y ∈ (B.subgroupOf Bs).map ρ, P * y = y * P) ∧
      ∃ t ∈ (spPlaneTorus (K := ZMod 2) (r := n - 1)).range, P * t ≠ t * P := by
  let U' : Subgroup (CFSG.Open.StatedSp (n - 1) (ZMod 2)) := U.comap φ
  let Y : Subgroup (CFSG.Open.StatedSp (n - 1) (ZMod 2)) := (B.subgroupOf Bs).map ρ
  have hYle : Y ≤ (spPlaneTorus (K := ZMod 2) (r := n - 1)).range :=
    (Subgroup.map_le_range _ _).trans (le_of_eq hρT)
  have hmap : Subgroup.map φ U' = U := by
    change Subgroup.map φ (U.comap φ) = U
    rw [Subgroup.map_comap_eq, hφL, inf_eq_right.mpr hUL]
  have hU'ne : U' ≠ ⊥ := by
    intro hbot
    apply hU
    have h1 := hmap
    rw [hbot, Subgroup.map_bot] at h1
    exact h1.symm
  have hU'2 : IsPGroup 2 U' := hU2.comap_of_injective φ hφ
  have hYU : ∀ y ∈ Y, ∀ u ∈ U', y * u * y⁻¹ ∈ U' := by
    intro y hy u hu
    obtain ⟨b, hb, rfl⟩ := Subgroup.mem_map.mp hy
    rw [Subgroup.mem_comap] at hu ⊢
    rw [hρ b u]
    exact (Subgroup.mem_normalizer_iff.mp (hBU (Subgroup.mem_subgroupOf.mp hb)) (φ u)).mp hu
  obtain ⟨W, hWne, hWiso, hWY⟩ := exists_isotropicSubmodule_of_twoSub U' hU'ne hU'2 Y hYU
  exact exists_involution_of_isotropic (K := ZMod 2) (r := n - 1) (by simp) hYle hWne hWiso hWY

private lemma spPlaneTorus_pow_three {r : ℕ} {x : CFSG.Open.StatedSp r (ZMod 2)}
    (hx : x ∈ (spPlaneTorus (K := ZMod 2) (r := r)).range) : x ^ 3 = 1 := by
  obtain ⟨f, rfl⟩ := MonoidHom.mem_range.mp hx
  have h3 : ∀ z : Multiplicative (ZMod 3), z ^ 3 = 1 := by decide
  rw [← map_pow, show f ^ 3 = 1 by funext i; exact h3 (f i), map_one]

private lemma spPlaneTorus_comm {r : ℕ} {x y : CFSG.Open.StatedSp r (ZMod 2)}
    (hx : x ∈ (spPlaneTorus (K := ZMod 2) (r := r)).range)
    (hy : y ∈ (spPlaneTorus (K := ZMod 2) (r := r)).range) : x * y = y * x := by
  obtain ⟨f, rfl⟩ := MonoidHom.mem_range.mp hx
  obtain ⟨g, rfl⟩ := MonoidHom.mem_range.mp hy
  rw [← map_mul, ← map_mul, mul_comm]

private lemma phi_conj_centralizer {G : Type} [Group G] [Finite G]
    {Bs : Subgroup G} {n : ℕ}
    (φ : CFSG.Open.StatedSp (n - 1) (ZMod 2) →* G)
    (ρ : ↥Bs →* CFSG.Open.StatedSp (n - 1) (ZMod 2))
    (hρ : ∀ (b : ↥Bs) (g : CFSG.Open.StatedSp (n - 1) (ZMod 2)),
      φ (ρ b * g * (ρ b)⁻¹) = (b : G) * φ g * (b : G)⁻¹)
    (T : Subgroup (CFSG.Open.StatedSp (n - 1) (ZMod 2))) (hρT : ρ.range = T)
    (hTcomm : ∀ x ∈ T, ∀ y ∈ T, x * y = y * x)
    {P : CFSG.Open.StatedSp (n - 1) (ZMod 2)}
    (hPN : ∀ t ∈ T, P * t * P⁻¹ ∈ T) {b : ↥Bs} :
    φ ((P * ρ b * P⁻¹) * (ρ b)⁻¹) ∈ Subgroup.centralizer (Bs : Set G) := by
  let t : CFSG.Open.StatedSp (n - 1) (ZMod 2) := (P * ρ b * P⁻¹) * (ρ b)⁻¹
  change φ t ∈ Subgroup.centralizer (Bs : Set G)
  have hρb : ρ b ∈ T := le_of_eq hρT (MonoidHom.mem_range.mpr ⟨b, rfl⟩)
  have h1T : P * ρ b * P⁻¹ ∈ T := hPN _ hρb
  have htT : t ∈ T := Subgroup.mul_mem T h1T (Subgroup.inv_mem T hρb)
  refine Subgroup.mem_centralizer_iff.mpr ?_
  intro b2 hb2
  have hρ2 : ρ ⟨b2, hb2⟩ ∈ T := le_of_eq hρT (MonoidHom.mem_range.mpr ⟨⟨b2, hb2⟩, rfl⟩)
  have hcomm : ρ ⟨b2, hb2⟩ * t * (ρ ⟨b2, hb2⟩)⁻¹ = t := by
    rw [hTcomm (ρ ⟨b2, hb2⟩) hρ2 t htT, mul_assoc, mul_inv_cancel, mul_one]
  have h := hρ ⟨b2, hb2⟩ t
  rw [hcomm] at h
  calc b2 * φ t = (b2 * φ t * b2⁻¹) * b2 := by
        rw [mul_assoc, inv_mul_cancel, mul_one]
    _ = φ t * b2 := by rw [← h]

private lemma phi_conj_mem_bstar {G : Type} [Group G] [Finite G]
    {Bs : Subgroup G} {n : ℕ}
    (φ : CFSG.Open.StatedSp (n - 1) (ZMod 2) →* G)
    (ρ : ↥Bs →* CFSG.Open.StatedSp (n - 1) (ZMod 2))
    (hρ : ∀ (b : ↥Bs) (g : CFSG.Open.StatedSp (n - 1) (ZMod 2)),
      φ (ρ b * g * (ρ b)⁻¹) = (b : G) * φ g * (b : G)⁻¹)
    (T : Subgroup (CFSG.Open.StatedSp (n - 1) (ZMod 2))) (hρT : ρ.range = T)
    (hTcomm : ∀ x ∈ T, ∀ y ∈ T, x * y = y * x)
    (hT3 : ∀ x ∈ T, x ^ 3 = 1)
    (hSC : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ 3 = 1 → g ∈ Bs)
    {P : CFSG.Open.StatedSp (n - 1) (ZMod 2)}
    (hPN : ∀ t ∈ T, P * t * P⁻¹ ∈ T) {b : ↥Bs} :
    φ ((P * ρ b * P⁻¹) * (ρ b)⁻¹) ∈ Bs := by
  let t : CFSG.Open.StatedSp (n - 1) (ZMod 2) := (P * ρ b * P⁻¹) * (ρ b)⁻¹
  have hρb : ρ b ∈ T := le_of_eq hρT (MonoidHom.mem_range.mpr ⟨b, rfl⟩)
  have h1T : P * ρ b * P⁻¹ ∈ T := hPN _ hρb
  have htT : t ∈ T := Subgroup.mul_mem T h1T (Subgroup.inv_mem T hρb)
  have hcen : φ t ∈ Subgroup.centralizer (Bs : Set G) :=
    phi_conj_centralizer φ ρ hρ T hρT hTcomm hPN (b := b)
  have h3 : (φ t) ^ 3 = 1 := by
    calc (φ t) ^ 3 = φ (t ^ 3) := (map_pow φ t 3).symm
      _ = φ 1 := by rw [hT3 t htT]
      _ = 1 := map_one φ
  exact hSC _ hcen h3

private lemma phi_P_split {G : Type} [Group G] [Finite G] {Bs : Subgroup G} {n : ℕ}
    (φ : CFSG.Open.StatedSp (n - 1) (ZMod 2) →* G)
    (ρ : ↥Bs →* CFSG.Open.StatedSp (n - 1) (ZMod 2))
    (hρ : ∀ (b : ↥Bs) (g : CFSG.Open.StatedSp (n - 1) (ZMod 2)),
      φ (ρ b * g * (ρ b)⁻¹) = (b : G) * φ g * (b : G)⁻¹)
    {P : CFSG.Open.StatedSp (n - 1) (ZMod 2)} (hP2 : P * P = 1) (b : ↥Bs) :
    (b : G) * φ P * (b : G)⁻¹ = φ P * φ ((P * ρ b * P⁻¹) * (ρ b)⁻¹) := by
  have hPinv : P⁻¹ = P := inv_eq_of_mul_eq_one_right hP2
  have h := hρ b P
  have ht : ρ b * P * (ρ b)⁻¹ = P * ((P * ρ b * P⁻¹) * (ρ b)⁻¹) := by
    rw [hPinv, show P * ((P * ρ b * P) * (ρ b)⁻¹) = (P * P) * ρ b * P * (ρ b)⁻¹ by group]
    rw [hP2, one_mul]
  rw [ht, map_mul] at h
  exact h.symm

private lemma phi_P_conj {G : Type} [Group G] [Finite G] {Bs : Subgroup G} {n : ℕ}
    (φ : CFSG.Open.StatedSp (n - 1) (ZMod 2) →* G)
    (ρ : ↥Bs →* CFSG.Open.StatedSp (n - 1) (ZMod 2))
    (hρ : ∀ (b : ↥Bs) (g : CFSG.Open.StatedSp (n - 1) (ZMod 2)),
      φ (ρ b * g * (ρ b)⁻¹) = (b : G) * φ g * (b : G)⁻¹)
    {P : CFSG.Open.StatedSp (n - 1) (ZMod 2)} (hP2 : P * P = 1) (b : ↥Bs) :
    φ P * (b : G) * (φ P)⁻¹ = φ ((P * ρ b * P⁻¹) * (ρ b)⁻¹) * (b : G) := by
  have hsplit := phi_P_split φ ρ hρ hP2 b
  have hg2' : φ P * φ P = 1 := by rw [← map_mul, hP2, map_one]
  have hbg : (b : G) * φ P = φ P * φ ((P * ρ b * P⁻¹) * (ρ b)⁻¹) * (b : G) := by
    calc (b : G) * φ P = ((b : G) * φ P * (b : G)⁻¹) * (b : G) := by group
      _ = (φ P * φ ((P * ρ b * P⁻¹) * (ρ b)⁻¹)) * (b : G) := by rw [hsplit]
  calc φ P * (b : G) * (φ P)⁻¹ = φ P * (b : G) * φ P := by
        rw [show (φ P)⁻¹ = φ P from inv_eq_of_mul_eq_one_right hg2']
    _ = φ P * ((b : G) * φ P) := by group
    _ = φ P * (φ P * φ ((P * ρ b * P⁻¹) * (ρ b)⁻¹) * (b : G)) := by rw [hbg]
    _ = (φ P * φ P) * φ ((P * ρ b * P⁻¹) * (ρ b)⁻¹) * (b : G) := by group
    _ = φ ((P * ρ b * P⁻¹) * (ρ b)⁻¹) * (b : G) := by rw [hg2', one_mul]

private lemma phi_P_normalizer_of_model {G : Type} [Group G] [Finite G] {Bs : Subgroup G} {n : ℕ}
    (φ : CFSG.Open.StatedSp (n - 1) (ZMod 2) →* G)
    (ρ : ↥Bs →* CFSG.Open.StatedSp (n - 1) (ZMod 2))
    (hρ : ∀ (b : ↥Bs) (g : CFSG.Open.StatedSp (n - 1) (ZMod 2)),
      φ (ρ b * g * (ρ b)⁻¹) = (b : G) * φ g * (b : G)⁻¹)
    (T : Subgroup (CFSG.Open.StatedSp (n - 1) (ZMod 2))) (hρT : ρ.range = T)
    (hTcomm : ∀ x ∈ T, ∀ y ∈ T, x * y = y * x)
    (hT3 : ∀ x ∈ T, x ^ 3 = 1)
    (hSC : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ 3 = 1 → g ∈ Bs)
    {P : CFSG.Open.StatedSp (n - 1) (ZMod 2)}
    (hP2 : P * P = 1) (hPN : ∀ t ∈ T, P * t * P⁻¹ ∈ T) :
    φ P ∈ Subgroup.normalizer (Bs : Set G) := by
  have hg2' : φ P * φ P = 1 := by rw [← map_mul, hP2, map_one]
  have hforward : ∀ c : G, c ∈ Bs → φ P * c * (φ P)⁻¹ ∈ Bs := by
    intro c hc
    have hmem := phi_conj_mem_bstar φ ρ hρ T hρT hTcomm hT3 hSC hPN (b := ⟨c, hc⟩)
    rw [phi_P_conj φ ρ hρ hP2 ⟨c, hc⟩]
    exact Subgroup.mul_mem _ hmem hc
  rw [Subgroup.mem_normalizer_iff]
  intro c
  constructor
  · exact hforward c
  · intro hc
    have h1 : φ P * (φ P * c * (φ P)⁻¹) * (φ P)⁻¹ ∈ Bs := hforward _ hc
    have h2 : φ P * (φ P * c * (φ P)⁻¹) * (φ P)⁻¹ = c := by
      rw [show (φ P)⁻¹ = φ P from inv_eq_of_mul_eq_one_right hg2']
      calc φ P * (φ P * c * φ P) * φ P = (φ P * φ P) * c * (φ P * φ P) := by group
        _ = c := by rw [hg2']; simp
    rwa [h2] at h1

private lemma phi_P_centralizes_B_of_model {G : Type} [Group G] [Finite G]
    {B Bs : Subgroup G} {n : ℕ}
    (φ : CFSG.Open.StatedSp (n - 1) (ZMod 2) →* G)
    (ρ : ↥Bs →* CFSG.Open.StatedSp (n - 1) (ZMod 2))
    (hρ : ∀ (b : ↥Bs) (g : CFSG.Open.StatedSp (n - 1) (ZMod 2)),
      φ (ρ b * g * (ρ b)⁻¹) = (b : G) * φ g * (b : G)⁻¹)
    {P : CFSG.Open.StatedSp (n - 1) (ZMod 2)} (hP2 : P * P = 1)
    (hPY : ∀ y ∈ (B.subgroupOf Bs).map ρ, P * y = y * P) :
    ∀ b : ↥Bs, (b : G) ∈ B → φ P * (b : G) * (φ P)⁻¹ = (b : G) := by
  intro b hb
  have hsplit := phi_P_split φ ρ hρ hP2 b
  have hg2' : φ P * φ P = 1 := by rw [← map_mul, hP2, map_one]
  have hbY : ρ b ∈ (B.subgroupOf Bs).map ρ :=
    Subgroup.mem_map_of_mem ρ (Subgroup.mem_subgroupOf.mpr hb)
  have hcomm : P * ρ b = ρ b * P := hPY (ρ b) hbY
  have ht1 : (P * ρ b * P⁻¹) * (ρ b)⁻¹ = 1 := by
    have hP : P * ρ b * P⁻¹ = ρ b := by
      calc P * ρ b * P⁻¹ = (ρ b * P) * P⁻¹ := by rw [hcomm]
        _ = ρ b := by group
    rw [hP]
    group
  have hbP : (b : G) * φ P * (b : G)⁻¹ = φ P := by
    rw [hsplit, ht1, map_one, mul_one]
  have hbg : (b : G) * φ P = φ P * (b : G) := by
    calc (b : G) * φ P = ((b : G) * φ P * (b : G)⁻¹) * (b : G) := by group
      _ = φ P * (b : G) := by rw [hbP]
  calc φ P * (b : G) * (φ P)⁻¹ = φ P * (b : G) * φ P := by
        rw [show (φ P)⁻¹ = φ P from inv_eq_of_mul_eq_one_right hg2']
    _ = φ P * ((b : G) * φ P) := by group
    _ = φ P * (φ P * (b : G)) := by rw [hbg]
    _ = (b : G) := by rw [← mul_assoc, hg2', one_mul]

private lemma phi_P_moves_of_model {G : Type} [Group G] [Finite G] {Bs : Subgroup G} {n : ℕ}
    (φ : CFSG.Open.StatedSp (n - 1) (ZMod 2) →* G) (hφ : Function.Injective φ)
    (ρ : ↥Bs →* CFSG.Open.StatedSp (n - 1) (ZMod 2))
    (hρ : ∀ (b : ↥Bs) (g : CFSG.Open.StatedSp (n - 1) (ZMod 2)),
      φ (ρ b * g * (ρ b)⁻¹) = (b : G) * φ g * (b : G)⁻¹)
    (T : Subgroup (CFSG.Open.StatedSp (n - 1) (ZMod 2))) (hρT : ρ.range = T)
    {P : CFSG.Open.StatedSp (n - 1) (ZMod 2)}
    (hPt : ∃ t ∈ T, P * t ≠ t * P) :
    ∃ b : ↥Bs, φ P * (b : G) * (φ P)⁻¹ ≠ (b : G) := by
  obtain ⟨t, htT, htne⟩ := hPt
  have htρ : t ∈ ρ.range := by rw [hρT]; exact htT
  obtain ⟨b, hb⟩ := MonoidHom.mem_range.mp htρ
  refine ⟨b, ?_⟩
  intro hfix
  have hbg : φ P * (b : G) = (b : G) * φ P := by
    calc φ P * (b : G) = (φ P * (b : G) * (φ P)⁻¹) * φ P := by group
      _ = (b : G) * φ P := by rw [hfix]
  have hbP : (b : G) * φ P * (b : G)⁻¹ = φ P := by
    calc (b : G) * φ P * (b : G)⁻¹ = (φ P * (b : G)) * (b : G)⁻¹ := by rw [hbg]
      _ = φ P := by group
  have h1 : (b : G) * φ P * (b : G)⁻¹ = φ (t * P * t⁻¹) := by
    rw [← hρ b P, hb]
  have h2 : φ (t * P * t⁻¹) = φ P := by
    calc φ (t * P * t⁻¹) = (b : G) * φ P * (b : G)⁻¹ := h1.symm
      _ = φ P := hbP
  have h3 : t * P * t⁻¹ = P := hφ h2
  have hcomm : P * t = t * P := by
    calc P * t = (t * P * t⁻¹) * t := by rw [h3]
      _ = t * P := by group
  exact htne hcomm

private theorem exists_g_of_model {G : Type} [Group G] [Finite G]
    {B Bs L : Subgroup G} {n : ℕ}
    (φ : CFSG.Open.StatedSp (n - 1) (ZMod 2) →* G)
    (ρ : ↥Bs →* CFSG.Open.StatedSp (n - 1) (ZMod 2))
    (hφ : Function.Injective φ) (hφL : φ.range = L)
    (hρ : ∀ (b : ↥Bs) (g : CFSG.Open.StatedSp (n - 1) (ZMod 2)),
      φ (ρ b * g * (ρ b)⁻¹) = (b : G) * φ g * (b : G)⁻¹)
    (T : Subgroup (CFSG.Open.StatedSp (n - 1) (ZMod 2))) (hρT : ρ.range = T)
    (hTcomm : ∀ x ∈ T, ∀ y ∈ T, x * y = y * x)
    (hT3 : ∀ x ∈ T, x ^ 3 = 1)
    (hSC : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ 3 = 1 → g ∈ Bs)
    {P : CFSG.Open.StatedSp (n - 1) (ZMod 2)}
    (hP2 : P * P = 1) (hPN : ∀ t ∈ T, P * t * P⁻¹ ∈ T)
    (hPY : ∀ y ∈ (B.subgroupOf Bs).map ρ, P * y = y * P)
    (hPt : ∃ t ∈ T, P * t ≠ t * P) :
    ∃ g : G, g ∈ L ∧ g ^ 2 = 1 ∧ g ∈ Subgroup.normalizer (Bs : Set G) ∧
      (∀ b : ↥Bs, (b : G) ∈ B → g * b * g⁻¹ = b) ∧
      (∃ b : ↥Bs, g * b * g⁻¹ ≠ b) := by
  refine ⟨φ P, ?_, ?_, ?_, ?_, ?_⟩
  · rw [← hφL]
    exact MonoidHom.mem_range.mpr ⟨P, rfl⟩
  · rw [pow_two]
    exact show φ P * φ P = 1 from by rw [← map_mul, hP2, map_one]
  · exact phi_P_normalizer_of_model φ ρ hρ T hρT hTcomm hT3 hSC hP2 hPN
  · exact phi_P_centralizes_B_of_model φ ρ hρ hP2 hPY
  · exact phi_P_moves_of_model φ hφ ρ hρ T hρT hPt

theorem GGConfig.exists_corner_involution
    {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} (hC : GGConfig 3 B Bs x L D J) {n : ℕ} (hn : 5 ≤ n)
    (eta : ↥Bs ≃* (Fin n → Multiplicative (ZMod 3))) {i0 : Fin n}
    (hb : (ggAutomizer L Bs).map (MulAut.congr eta).toMonoidHom = bCoordinateBlock n 3 i0)
    (hM : GGInnerDiagOnLabel (fun _ lab => (lab.tag = .B ∨ lab.tag = .C) ∧ lab.rank = n - 1 ∧
      lab.n = 1) 3 Bs L) (hne : B ≠ Bs) :
    ∃ g : G, g ∈ L ∧ g ∈ Subgroup.normalizer (Bs : Set G) ∧
      (∀ b : ↥Bs, (b : G) ∈ B → g * b * g⁻¹ = b) ∧ ∃ b : ↥Bs, g * b * g⁻¹ ≠ b := by
  obtain ⟨φ, ρ, hφ, hφL, hρ, hρT, hρB⟩ := exists_spPlaneTorus_model hC hn eta hb hM
  obtain ⟨U, hUL, hU, hU2, hBU⟩ := exists_twoSub_of_marking hC hM hn hne
  obtain ⟨P, hP2, hPN, hPY, hPt⟩ :=
    exists_P_of_model φ ρ hφ hφL hρ hρT hUL hU hU2 hBU
  obtain ⟨g, hgL, hg2, hgN, hgfix, hgmoves⟩ :=
    exists_g_of_model φ ρ hφ hφL hρ _ hρT
      (fun x hx y hy => spPlaneTorus_comm hx hy)
      (fun x hx => spPlaneTorus_pow_three hx)
      hC.2.1.2.2.2 hP2 hPN hPY hPt
  exact ⟨g, hgL, hgN, hgfix, hgmoves⟩

private lemma congr_apply_eta {G : Type} [Group G] {n : ℕ} {Bs : Subgroup G}
    (eta : ↥Bs ≃* (Fin n → Multiplicative (ZMod 3))) (τ : MulAut ↥Bs) (b : ↥Bs) :
    MulAut.congr eta τ (eta b) = eta (τ b) := by
  rw [MulAut.congr_apply]
  simp

private lemma card_fix_congr {G : Type} [Group G] {n : ℕ} {Bs : Subgroup G}
    (eta : ↥Bs ≃* (Fin n → Multiplicative (ZMod 3))) (τ : MulAut ↥Bs) :
    Nat.card {f : Fin n → Multiplicative (ZMod 3) // MulAut.congr eta τ f = f} =
      Nat.card {b : ↥Bs // τ b = b} := by
  let e : {b : ↥Bs // τ b = b} ≃
      {f : Fin n → Multiplicative (ZMod 3) // MulAut.congr eta τ f = f} :=
    { toFun := fun x => ⟨eta x.1, by rw [congr_apply_eta eta τ x.1, x.2]⟩
      invFun := fun x => ⟨eta.symm x.1, by
        apply eta.injective
        rw [← congr_apply_eta eta τ (eta.symm x.1)]
        simpa using x.2⟩
      left_inv := fun x => Subtype.ext (by simp)
      right_inv := fun x => Subtype.ext (by simp) }
  exact Nat.card_congr e.symm

private lemma sgnAut_eq_self_iff {n : ℕ} (hp : Nat.Prime 3) (hp2 : 3 ≠ 2)
    {f : Fin n → Multiplicative (ZMod 3)} {i : Fin n} :
    sgnAut (p := 3) i f = f ↔ f i = 1 := by
  constructor
  · intro h
    have h' := congrArg (fun v : Fin n → Multiplicative (ZMod 3) => toAdd (v i)) h
    rw [sgnAut_apply, Function.update_self, toAdd_inv] at h'
    have h'' : toAdd (f i) = -toAdd (f i) := h'.symm
    have h3 := coord_eq_zero_of_eq_neg hp hp2 h''
    exact Multiplicative.toAdd.injective (by rw [h3]; rfl)
  · intro h
    funext j
    by_cases hj : j = i
    · subst hj
      rw [sgnAut_apply, Function.update_self, h, inv_one]
    · rw [sgnAut_apply, Function.update_of_ne hj]

private lemma permAut_swap_eq_self_iff {n : ℕ} {a b : Fin n} (hab : a ≠ b)
    (f : Fin n → Multiplicative (ZMod 3)) :
    permAut (Equiv.swap a b) f = f ↔ f a = f b := by
  constructor
  · intro h
    have h' := congrArg (fun g : Fin n → Multiplicative (ZMod 3) => g a) h
    rw [permAut_apply] at h'
    change f (Equiv.swap a b a) = f a at h'
    rw [Equiv.swap_apply_left] at h'
    exact h'.symm
  · intro h
    funext k
    rw [permAut_apply]
    change f (Equiv.swap a b k) = f k
    by_cases hka : k = a
    · subst hka
      rw [Equiv.swap_apply_left]
      exact h.symm
    · by_cases hkb : k = b
      · subst hkb
        rw [Equiv.swap_apply_right]
        exact h
      · rw [Equiv.swap_apply_of_ne_of_ne hka hkb]

private lemma negTrans_eq_self_iff {n : ℕ} {a b : Fin n} (hab : a ≠ b)
    (f : Fin n → Multiplicative (ZMod 3)) :
    ((sgnAut a * permAut (Equiv.swap a b) * (sgnAut a)⁻¹ :
      MulAut (Fin n → Multiplicative (ZMod 3))) f = f) ↔ f a = (f b)⁻¹ := by
  constructor
  · intro h
    have h' := congrArg (fun g : Fin n → Multiplicative (ZMod 3) => g a) h
    rw [negTrans_apply a b hab f a] at h'
    rw [if_pos rfl] at h'
    exact h'.symm
  · intro h
    funext k
    rw [negTrans_apply a b hab f k]
    by_cases hka : k = a
    · rw [if_pos hka]
      rw [hka]
      exact h.symm
    · by_cases hkb : k = b
      · rw [if_neg hka, if_pos hkb]
        rw [h, inv_inv]
        exact congrArg f hkb.symm
      · rw [if_neg hka, if_neg hkb]

private lemma axis_fixed_of_mem_bCoordinateBlock {n : ℕ} (hp : Nat.Prime 3) (hp2 : 3 ≠ 2)
    {i0 : Fin n} {u : MulAut (Fin n → Multiplicative (ZMod 3))}
    (hu : u ∈ bCoordinateBlock n 3 i0) :
    u (Pi.mulSingle i0 (ofAdd (1 : ZMod 3))) = Pi.mulSingle i0 (ofAdd (1 : ZMod 3)) := by
  have hRHS : ∀ k, k ≠ i0 →
      (Pi.mulSingle i0 (ofAdd (1 : ZMod 3)) : Fin n → Multiplicative (ZMod 3)) k = 1 := by
    intro k hk
    rw [Pi.mulSingle_eq_of_ne hk]
  exact (forall_bCoordinateBlock_fix_iff hp hp2 i0 _).mpr hRHS u hu

private lemma permAut_swap_axis_ne {n : ℕ} {i0 j : Fin n} (hij : i0 ≠ j) :
    permAut (Equiv.swap i0 j) (Pi.mulSingle i0 (ofAdd (1 : ZMod 3))) ≠
      Pi.mulSingle i0 (ofAdd (1 : ZMod 3)) := by
  intro h
  have h' := congrArg (fun f : Fin n → Multiplicative (ZMod 3) => f j) h
  rw [permAut_apply] at h'
  change (Pi.mulSingle i0 (ofAdd 1) : Fin n → Multiplicative (ZMod 3))
    (Equiv.swap i0 j j) = ((Pi.mulSingle i0 (ofAdd 1) : Fin n → Multiplicative (ZMod 3))) j at h'
  rw [Equiv.swap_apply_right] at h'
  rw [Pi.mulSingle_eq_same, Pi.mulSingle_eq_of_ne (Ne.symm hij)] at h'
  have h1 : (1 : ZMod 3) = 0 := ofAdd_eq_one.mp h'
  exact one_ne_zero h1

private lemma negTrans_axis_ne {n : ℕ} {i0 j : Fin n} (hij : i0 ≠ j) :
    ((sgnAut i0 * permAut (Equiv.swap i0 j) * (sgnAut i0)⁻¹ :
      MulAut (Fin n → Multiplicative (ZMod 3)))
      (Pi.mulSingle i0 (ofAdd (1 : ZMod 3)))) ≠
        Pi.mulSingle i0 (ofAdd (1 : ZMod 3)) := by
  intro h
  have h' := congrArg (fun f : Fin n → Multiplicative (ZMod 3) => f i0) h
  rw [negTrans_apply i0 j hij] at h'
  rw [if_pos rfl] at h'
  rw [Pi.mulSingle_eq_of_ne (Ne.symm hij), Pi.mulSingle_eq_same] at h'
  have h1 : (1 : ZMod 3) = 0 := ofAdd_eq_one.mp h'.symm
  exact one_ne_zero h1

private theorem exists_tau_of_model {G : Type} [Group G] [Finite G]
    {B Bs L : Subgroup G}
    (g : G) (hgL : g ∈ L) (hg2 : g ^ 2 = 1)
    (hgN : g ∈ Subgroup.normalizer (Bs : Set G))
    (hgfix : ∀ b : ↥Bs, (b : G) ∈ B → g * b * g⁻¹ = b)
    (hgmoves : ∃ b : ↥Bs, g * b * g⁻¹ ≠ b)
    (hne : B ≠ Bs) (hBBs : B ≤ Bs) (hBs : IsElemAbelian 3 Bs)
    (hcard : Nat.card Bs ≤ 3 * Nat.card B) :
    ∃ τ : MulAut ↥Bs, τ ∈ ggAutomizer L Bs ∧ τ ^ 2 = 1 ∧ τ ≠ 1 ∧
      GGIsReflection 3 τ ∧ ∀ b : ↥Bs, ((b : G) ∈ B ↔ τ b = b) := by
  let τ : MulAut ↥Bs := Bs.normalizerMonoidHom ⟨g, hgN⟩
  have hτcoe : ∀ b : ↥Bs, ((τ b : ↥Bs) : G) = g * (b : G) * g⁻¹ := fun b =>
    Subgroup.normalizerMonoidHom_apply_apply_coe Bs ⟨g, hgN⟩ b
  have hτind : τ ∈ ggInduced L Bs := ⟨g, hgL, hgN, hτcoe⟩
  have hτL : τ ∈ ggAutomizer L Bs := Subgroup.subset_closure hτind
  have hg2' : (⟨g, hgN⟩ : ↥(Subgroup.normalizer (Bs : Set G))) ^ 2 = 1 := by
    apply Subtype.ext
    simpa using hg2
  have hτ2 : τ ^ 2 = 1 := by
    change (Bs.normalizerMonoidHom ⟨g, hgN⟩) ^ 2 = 1
    rw [← map_pow, hg2', map_one]
  have hfix : ∀ b : ↥Bs, (b : G) ∈ B → τ b = b := by
    intro b hb
    apply Subtype.ext
    rw [hτcoe b]
    exact hgfix b hb
  have hτ1 : τ ≠ 1 := by
    intro h
    obtain ⟨b, hbne⟩ := hgmoves
    apply hbne
    have hbτ : τ b = b := by rw [h]; rfl
    rw [← hτcoe b]
    exact congrArg (fun x : ↥Bs => (x : G)) hbτ
  have hp : Nat.Prime 3 := by norm_num
  have hiff := fix_iff_mem_of_le_of_ne_one hp hBBs hBs hcard hne hτ1 hfix
  have href := isReflection_of_fix_iff_mem hp hBBs hBs hcard hne hτ2 hiff
  exact ⟨τ, hτL, hτ2, hτ1, href, hiff⟩

private lemma exists_coord_sgnAut_of_mem_block {G : Type} [Group G] [Finite G]
    {B Bs : Subgroup G} {n : ℕ}
    (eta : ↥Bs ≃* (Fin n → Multiplicative (ZMod 3))) {i0 : Fin n}
    {i : Fin n} {τ : MulAut ↥Bs} {u : MulAut (Fin n → Multiplicative (ZMod 3))}
    (hu : u ∈ bCoordinateBlock n 3 i0)
    (hi : u = sgnAut i)
    (hiff : ∀ b : ↥Bs, ((b : G) ∈ B ↔ τ b = b))
    (hcongr : u = MulAut.congr eta τ) :
    i ≠ i0 ∧ ∀ b : ↥Bs, ((b : G) ∈ B ↔ eta b i = 1) := by
  have hp : Nat.Prime 3 := by norm_num
  have hp2 : 3 ≠ 2 := by norm_num
  have hii0 : i ≠ i0 := by
    intro hii0
    have hmem : sgnAut i ∈ bCoordinateBlock n 3 i := by
      rw [← hi]
      have hu' : u ∈ bCoordinateBlock n 3 i := by
        rw [hii0]
        exact hu
      exact hu'
    exact sgnAut_not_mem_bCoordinateBlock hp hp2 i hmem
  refine ⟨hii0, fun b => ?_⟩
  rw [hiff b, show τ b = b ↔ u (eta b) = eta b from ?_]
  · rw [hi, sgnAut_eq_self_iff hp hp2]
  · rw [hcongr]
    change τ b = b ↔ MulAut.congr eta τ (eta b) = eta b
    rw [congr_apply_eta]
    exact eta.injective.eq_iff.symm

private lemma exists_coord_permAut_of_mem_block {G : Type} [Group G] [Finite G]
    {B Bs : Subgroup G} {n : ℕ}
    (eta : ↥Bs ≃* (Fin n → Multiplicative (ZMod 3))) {i0 : Fin n}
    {a b : Fin n} {τ : MulAut ↥Bs} {u : MulAut (Fin n → Multiplicative (ZMod 3))}
    (hu : u ∈ bCoordinateBlock n 3 i0)
    (hab : a ≠ b)
    (hi : u = permAut (Equiv.swap a b))
    (hiff : ∀ c : ↥Bs, ((c : G) ∈ B ↔ τ c = c))
    (hcongr : u = MulAut.congr eta τ) :
    a ≠ i0 ∧ b ≠ i0 ∧ ∀ c : ↥Bs, ((c : G) ∈ B ↔ eta c a = eta c b) := by
  have hp : Nat.Prime 3 := by norm_num
  have hp2 : 3 ≠ 2 := by norm_num
  have hai0 : a ≠ i0 := by
    intro hai0
    have hmem : u ∈ bCoordinateBlock n 3 i0 := hu
    rw [hi] at hmem
    rw [hai0] at hmem
    have hfix := axis_fixed_of_mem_bCoordinateBlock hp hp2 hmem
    have hne : i0 ≠ b := by rw [← hai0]; exact hab
    exact permAut_swap_axis_ne hne hfix
  have hbi0 : b ≠ i0 := by
    intro hbi0
    have hmem : u ∈ bCoordinateBlock n 3 i0 := hu
    rw [hi] at hmem
    rw [hbi0] at hmem
    have hfix := axis_fixed_of_mem_bCoordinateBlock hp hp2 hmem
    rw [Equiv.swap_comm] at hfix
    have hne : i0 ≠ a := by rw [← hbi0]; exact Ne.symm hab
    exact permAut_swap_axis_ne hne hfix
  refine ⟨hai0, hbi0, fun c => ?_⟩
  rw [hiff c, show τ c = c ↔ u (eta c) = eta c from ?_]
  · rw [hi, permAut_swap_eq_self_iff hab]
  · rw [hcongr]
    change τ c = c ↔ MulAut.congr eta τ (eta c) = eta c
    rw [congr_apply_eta]
    exact eta.injective.eq_iff.symm

private lemma exists_coord_negTrans_of_mem_block {G : Type} [Group G] [Finite G]
    {B Bs : Subgroup G} {n : ℕ}
    (eta : ↥Bs ≃* (Fin n → Multiplicative (ZMod 3))) {i0 : Fin n}
    {a b : Fin n} {τ : MulAut ↥Bs} {u : MulAut (Fin n → Multiplicative (ZMod 3))}
    (hu : u ∈ bCoordinateBlock n 3 i0)
    (hab : a ≠ b)
    (hi : u = sgnAut a * permAut (Equiv.swap a b) * (sgnAut a)⁻¹)
    (hiff : ∀ c : ↥Bs, ((c : G) ∈ B ↔ τ c = c))
    (hcongr : u = MulAut.congr eta τ) :
    a ≠ i0 ∧ b ≠ i0 ∧ ∀ c : ↥Bs, ((c : G) ∈ B ↔ eta c a = (eta c b)⁻¹) := by
  have hp : Nat.Prime 3 := by norm_num
  have hp2 : 3 ≠ 2 := by norm_num
  have hai0 : a ≠ i0 := by
    intro hai0
    have hmem : u ∈ bCoordinateBlock n 3 i0 := hu
    rw [hi] at hmem
    rw [hai0] at hmem
    have hfix := axis_fixed_of_mem_bCoordinateBlock hp hp2 hmem
    have hne : i0 ≠ b := by rw [← hai0]; exact hab
    exact negTrans_axis_ne hne hfix
  have hbi0 : b ≠ i0 := by
    intro hbi0
    have hmem : u ∈ bCoordinateBlock n 3 i0 := hu
    rw [hi] at hmem
    rw [hbi0] at hmem
    have hfix := axis_fixed_of_mem_bCoordinateBlock hp hp2 hmem
    have ha_i0 : a ≠ i0 := by rw [← hbi0]; exact hab
    have h' := congrArg (fun f : Fin n → Multiplicative (ZMod 3) => f i0) hfix
    rw [negTrans_apply a i0 ha_i0] at h'
    rw [if_neg (Ne.symm ha_i0), if_pos rfl] at h'
    rw [Pi.mulSingle_eq_of_ne ha_i0, Pi.mulSingle_eq_same] at h'
    have h1 : (1 : ZMod 3) = 0 := ofAdd_eq_one.mp h'.symm
    exact one_ne_zero h1
  refine ⟨hai0, hbi0, fun c => ?_⟩
  rw [hiff c, show τ c = c ↔ u (eta c) = eta c from ?_]
  · rw [hi, negTrans_eq_self_iff hab]
  · rw [hcongr]
    change τ c = c ↔ MulAut.congr eta τ (eta c) = eta c
    rw [congr_apply_eta]
    exact eta.injective.eq_iff.symm

private theorem exists_coord_of_reflection {G : Type} [Group G] [Finite G]
    {B Bs L : Subgroup G} {n : ℕ}
    (eta : ↥Bs ≃* (Fin n → Multiplicative (ZMod 3))) {i0 : Fin n}
    (hb : (ggAutomizer L Bs).map (MulAut.congr eta).toMonoidHom = bCoordinateBlock n 3 i0)
    {τ : MulAut ↥Bs} (hτL : τ ∈ ggAutomizer L Bs) (hτ2 : τ ^ 2 = 1)
    (href : GGIsReflection 3 τ) (hiff : ∀ b : ↥Bs, ((b : G) ∈ B ↔ τ b = b)) :
    (∃ i, i ≠ i0 ∧ ∀ b : ↥Bs, ((b : G) ∈ B ↔ eta b i = 1)) ∨
      ∃ i j, i ≠ j ∧ i ≠ i0 ∧ j ≠ i0 ∧
        ((∀ b : ↥Bs, ((b : G) ∈ B ↔ eta b i = eta b j)) ∨
          ∀ b : ↥Bs, ((b : G) ∈ B ↔ eta b i = (eta b j)⁻¹)) := by
  let u : MulAut (Fin n → Multiplicative (ZMod 3)) := MulAut.congr eta τ
  have hu : u ∈ bCoordinateBlock n 3 i0 := by
    rw [← hb]
    exact Subgroup.mem_map_of_mem _ hτL
  have huSigned : u ∈ bSignedFull n 3 := bCoordinateBlock_le_bSignedFull i0 hu
  have hu2 : u ^ 2 = 1 := by
    rw [show u = MulAut.congr eta τ from rfl, ← map_pow, hτ2, map_one]
  have hfixu : Nat.card {f // u f = f} * 3 = Nat.card (Fin n → Multiplicative (ZMod 3)) := by
    rw [show Nat.card {f // u f = f} = Nat.card {b : ↥Bs // τ b = b} from
      card_fix_congr eta τ, href.2]
    exact Nat.card_congr eta.toEquiv
  have hp : Nat.Prime 3 := by norm_num
  have hp2 : 3 ≠ 2 := by norm_num
  have hcongr : u = MulAut.congr eta τ := by rfl
  have hcases :
      (∃ i, u = sgnAut i) ∨ ∃ a b, a ≠ b ∧
        (u = permAut (Equiv.swap a b) ∨
          u = sgnAut a * permAut (Equiv.swap a b) * (sgnAut a)⁻¹) :=
    eq_sgnAut_or_swap_of_isRefl (p := 3) hp hp2 huSigned hu2 hfixu
  rcases hcases with ⟨i, hi⟩ | ⟨a, b, hab, h⟩
  · obtain ⟨hii0, hiffi⟩ := exists_coord_sgnAut_of_mem_block eta hu hi hiff hcongr
    exact Or.inl ⟨i, hii0, hiffi⟩
  · rcases h with hperm | hneg
    · obtain ⟨hai0, hbi0, hiffab⟩ :=
        exists_coord_permAut_of_mem_block eta hu hab hperm hiff hcongr
      exact Or.inr ⟨a, b, hab, hai0, hbi0, Or.inl hiffab⟩
    · obtain ⟨hai0, hbi0, hiffab⟩ :=
        exists_coord_negTrans_of_mem_block eta hu hab hneg hiff hcongr
      exact Or.inr ⟨a, b, hab, hai0, hbi0, Or.inr hiffab⟩

theorem ggSecFiveBCoordB_corner_hyperplane_of_model {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} (hC : GGConfig 3 B Bs x L D J) {n : ℕ} (hn : 5 ≤ n)
    (eta : ↥Bs ≃* (Fin n → Multiplicative (ZMod 3))) {i0 : Fin n}
    (hb : (ggAutomizer L Bs).map (MulAut.congr eta).toMonoidHom = bCoordinateBlock n 3 i0)
    (hM : GGInnerDiagOnLabel (fun _ lab => (lab.tag = .B ∨ lab.tag = .C) ∧ lab.rank = n - 1 ∧
      lab.n = 1) 3 Bs L) (hne : B ≠ Bs)
    (φ : CFSG.Open.StatedSp (n - 1) (ZMod 2) →* G)
    (ρ : ↥Bs →* CFSG.Open.StatedSp (n - 1) (ZMod 2)) (hφ : Function.Injective φ)
    (hφL : φ.range = L)
    (hρ : ∀ (b : ↥Bs) (g : CFSG.Open.StatedSp (n - 1) (ZMod 2)),
      φ (ρ b * g * (ρ b)⁻¹) = (b : G) * φ g * (b : G)⁻¹)
    (hρT : ρ.range = (spPlaneTorus (K := ZMod 2) (r := n - 1)).range) :
    (∃ i, i ≠ i0 ∧ ∀ b : ↥Bs, ((b : G) ∈ B ↔ eta b i = 1)) ∨
      ∃ i j, i ≠ j ∧ i ≠ i0 ∧ j ≠ i0 ∧
        ((∀ b : ↥Bs, ((b : G) ∈ B ↔ eta b i = eta b j)) ∨
          ∀ b : ↥Bs, ((b : G) ∈ B ↔ eta b i = (eta b j)⁻¹)) := by
  obtain ⟨U, hUL, hU, hU2, hBU⟩ := exists_twoSub_of_marking hC hM hn hne
  obtain ⟨P, hP2, hPN, hPY, hPt⟩ :=
    exists_P_of_model φ ρ hφ hφL hρ hρT hUL hU hU2 hBU
  obtain ⟨g, hgL, hg2, hgN, hgfix, hgmoves⟩ :=
    exists_g_of_model φ ρ hφ hφL hρ _ hρT
      (fun x hx y hy => spPlaneTorus_comm hx hy)
      (fun x hx => spPlaneTorus_pow_three hx)
      hC.2.1.2.2.2 hP2 hPN hPY hPt
  obtain ⟨τ, hτL, hτ2, -, href, hiff⟩ :=
    exists_tau_of_model g hgL hg2 hgN hgfix hgmoves hne hC.2.1.1 hC.2.1.2.1 hC.2.1.2.2.1
  exact exists_coord_of_reflection eta hb hτL hτ2 href hiff

theorem ggSecFiveBCoordB_corner_hyperplane
    {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} (hC : GGConfig 3 B Bs x L D J) {n : ℕ} (hn : 5 ≤ n)
    (eta : ↥Bs ≃* (Fin n → Multiplicative (ZMod 3))) {i0 : Fin n}
    (hb : (ggAutomizer L Bs).map (MulAut.congr eta).toMonoidHom = bCoordinateBlock n 3 i0)
    (hM : GGInnerDiagOnLabel (fun _ lab => (lab.tag = .B ∨ lab.tag = .C) ∧ lab.rank = n - 1 ∧
      lab.n = 1) 3 Bs L) (hne : B ≠ Bs) :
    (∃ i, i ≠ i0 ∧ ∀ b : ↥Bs, ((b : G) ∈ B ↔ eta b i = 1)) ∨
      ∃ i j, i ≠ j ∧ i ≠ i0 ∧ j ≠ i0 ∧
        ((∀ b : ↥Bs, ((b : G) ∈ B ↔ eta b i = eta b j)) ∨
          ∀ b : ↥Bs, ((b : G) ∈ B ↔ eta b i = (eta b j)⁻¹)) := by
  obtain ⟨φ, ρ, hφ, hφL, hρ, hρT, -⟩ := exists_spPlaneTorus_model hC hn eta hb hM
  exact ggSecFiveBCoordB_corner_hyperplane_of_model hC hn eta hb hM hne φ ρ hφ hφL hρ hρT

end CFSG.StandardType
