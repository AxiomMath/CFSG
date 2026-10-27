module

public import CFSG.RankThree.GF2n.Stroth80.Sec7Levi
public import CFSG.RankThree.GF2n.Stroth80.Sl2Commuting
public import CFSG.RankThree.GF2n.Stroth80.Sec79OmegaFixed
public import CFSG.ClassicalGroups.Orthogonal.StatedOmegaTransport
public import Mathlib.Algebra.Group.End
public import CFSG.CGT.Timmesfeld75.Forms
public import CFSG.HardMathSupport.Cooperstein.Coordinator.FFInputs
public import CFSG.LocalAnalysis.AGLEmbedding.D1GlobalU
public import CFSG.LocalAnalysis.AGLEmbedding.Reduction
public import CFSG.LocalAnalysis.AGLEmbedding.TwoCoreObstruction
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBDerivedNormalSectionBound
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointActionModels
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointDataModelWitness
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalSemilinearDataCompatibility
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProper
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProperGroups
public import CFSG.LocalAnalysis.ComponentClassification.DisjointSolvableKernels
public import CFSG.LocalAnalysis.ComponentClassification.LayerMultiplication
public import CFSG.LocalAnalysis.ComponentClassification.MinimalBCenter
public import CFSG.LocalAnalysis.ComponentClassification.OrdinaryComponentJoins
public import CFSG.LocalAnalysis.ComponentClassification.TwoLayer
public import CFSG.LocalAnalysis.ComponentClassification.UniversalOrbitBlock
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalReflectionSplitting
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherEvenOrthogonalModel
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Vol2NativeBasic
public import CFSG.LocalAnalysis.SectionRank.Sporadic.MathieuLocalBase
public import CFSG.Monster.Code.Weights
public import CFSG.Quasithin.Background.A1bGroups
public import CFSG.Quasithin.Background.A1cModuleCoprime
public import CFSG.Quasithin.Background.A3Components
public import CFSG.Quasithin.Background.A3Structure312Facts
public import CFSG.Quasithin.Background.B4Statement
public import CFSG.Quasithin.Background.B6
public import CFSG.Quasithin.Background.B6Example
public import CFSG.Quasithin.Background.B6Offenders
public import CFSG.Quasithin.Background.C1GNBlockLemmas
public import CFSG.Quasithin.Background.C1GNInputs
public import CFSG.Quasithin.Background.C1GNNotation
public import CFSG.Quasithin.Background.C1PackNat
public import CFSG.Quasithin.Background.C1PackSolvBasic
public import CFSG.Quasithin.Background.E2SolvTwo
public import CFSG.Quasithin.Background.F1Amalgam
public import CFSG.Quasithin.Background.F2Equiv
public import CFSG.Quasithin.Vol2.Ch1Local
public import CFSG.RankThree.Asc83Table.PermTables
public import CFSG.RankThree.GF2n.Stroth80.Anisotropic
public import CFSG.RankThree.GF2n.Stroth80.FrobClause
public import CFSG.RankThree.GF2n.Stroth80.GlobalModel
public import CFSG.RankThree.GF2n.Stroth80.Sec39Rt
public import CFSG.RankThree.GF2n.Stroth80.Sec3Stmt
public import CFSG.RankThree.GF2n.Stroth80.Sec5NatBridge
public import CFSG.RankThree.GF2n.SupIndepDecomp
public import CFSG.RankThree.GF2n.Tim79CentC
public import CFSG.RankThree.GF2n.Tim79CentL
public import CFSG.RankThree.GF2n.Tim79Mod
public import CFSG.Sporadic.J4Base
public import CFSG.Sporadic.Schreier.M11
public import CFSG.Sporadic.Schreier.M22
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter1section1.proposition_4_c
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Proposition82
public import Certificates.Certificate8026Base
public import TauCeti.LinearAlgebra.QuadraticForm.OrthogonalBasis

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG.ClassicalGroups.F2Fixed CFSG.ClassicalGroups.Orthogonal CFSG.LieType.Universal.Spin
  CFSG.Open QuadraticMap
open scoped Matrix MatrixGroups

section Gen

variable {Γ : Type*} [Group Γ] {Y : Type*} [AddCommGroup Y] [DistribMulAction Γ Y]

theorem smul_mem_fixedSub_of_conj {L : Subgroup Γ} (g : Γ) (hg : ∀ h ∈ L, g⁻¹ * h * g ∈ L)
    {a : Y} (ha : a ∈ fixedSub Y (L : Set Γ)) : g • a ∈ fixedSub Y (L : Set Γ) := by
  intro h hh
  calc h • g • a = (g * (g⁻¹ * h * g)) • a := by
        rw [← mul_smul]
        congr 1
        group
    _ = g • ((g⁻¹ * h * g) • a) := mul_smul _ _ _
    _ = g • a := by rw [ha _ (hg h hh)]

theorem isotropic_of_range_comm (β : Y →+ Y →+ ZMod 2)
    (hinv : ∀ (g : Γ) a b, β (g • a) (g • b) = β a b) {L : Subgroup Γ} {x : Γ} (hx : x ∈ L)
    (hrange : (comm Y x).range = fixedSub Y (L : Set Γ)) :
    ∀ a ∈ fixedSub Y (L : Set Γ), ∀ b ∈ fixedSub Y (L : Set Γ), β a b = 0 := by
  intro a ha b hb
  rw [← hrange] at hb
  obtain ⟨c, rfl⟩ := hb
  rw [comm_apply, map_sub]
  have h1 : β a (x • c) = β a c := by
    have := hinv x⁻¹ a (x • c)
    rw [inv_smul_smul, ha x⁻¹ (L.inv_mem hx)] at this
    exact this.symm
  rw [h1]
  exact sub_self _

end Gen

section Levi

variable {K : Type} [Field K] [Finite K] [CharP K 2] {V : Type} [AddCommGroup V] [Module K V]
  {Q : QuadraticForm K V} {Y : Type} [AddCommGroup Y] [DistribMulAction (Gom Q) Y]

theorem conj_mem_Lom_of_fix (g : Gom Q) {u : V} (hg : g.app u = u) {h : Gom Q}
    (hh : h ∈ Lom Q u) : g⁻¹ * h * g ∈ Lom Q u := by
  have := (mem_Lom_app_iff g u h).mp (by rw [hg]; exact hh)
  exact this

theorem polar_eichlerG_ne_zero' {u w v : V} (hu : Q u = 0) (hw : polar Q u w = 0)
    (hQw : Q w ≠ 0) (hv : polar Q v u ≠ 0) : polar Q v ((eichlerG Q u w).app v) ≠ 0 := by
  show polar Q v (eichler Q u w v) ≠ 0
  rw [polar_apply_eichler_self hu hw v, CharTwo.two_eq_zero, zero_mul, zero_sub]
  exact neg_ne_zero.mpr (mul_ne_zero hQw (pow_ne_zero 2 hv))

theorem levi_trivial_false {H : Type} [Group H] {u u' : V} (hu : Q u = 0)
    (huu' : polar Q u' u ≠ 0)
    (hdec : IsCompl (fixedSub Y (Lom Q u : Set (Gom Q))) (fixedSub Y (Lom Q u' : Set (Gom Q))))
    (h2 : ∀ a : Y, a + a = 0)
    (β : Y →+ Y →+ ZMod 2) (hinv : ∀ (g : Gom Q) a b, β (g • a) (g • b) = β a b)
    (hnd : ∀ a, (∀ b, β a b = 0) → a = 0)
    (hY₁ : fixedSub Y (Lom Q u : Set (Gom Q)) ≠ ⊥)
    (hc2 : ∀ x ∈ Lom Q u, x.NonA2 → (comm Y x).range = fixedSub Y (Lom Q u : Set (Gom Q)))
    (hiso₂ : ∀ a ∈ fixedSub Y (Lom Q u' : Set (Gom Q)),
      ∀ b ∈ fixedSub Y (Lom Q u' : Set (Gom Q)), β a b = 0)
    (s : H →* Gom Q) (hs : ∀ g, (s g).app u = u) (hs' : ∀ g, (s g).app u' = u')
    (hw : ∃ (g : H) (w : V), polar Q u w = 0 ∧ Q ((s g).app w + w) ≠ 0)
    (htriv : ∀ g, ∀ a ∈ fixedSub Y (Lom Q u : Set (Gom Q)), s g • a = a) : False := by
  classical
  obtain ⟨g₀, w₀, hw₀, hQw⟩ := hw
  have hall : ∀ g (a : Y), s g • a = a := by
    intro g a
    have hmem : a ∈ fixedSub Y (Lom Q u : Set (Gom Q)) ⊔ fixedSub Y (Lom Q u' : Set (Gom Q)) := by
      rw [hdec.sup_eq_top]
      trivial
    obtain ⟨a₁, ha₁, a₂, ha₂, rfl⟩ := AddSubgroup.mem_sup.mp hmem
    have hd : s g • a₂ + a₂ = 0 := by
      apply hnd
      intro b
      have hbmem : b ∈ fixedSub Y (Lom Q u : Set (Gom Q)) ⊔
          fixedSub Y (Lom Q u' : Set (Gom Q)) := by
        rw [hdec.sup_eq_top]
        trivial
      obtain ⟨b₁, hb₁, b₂, hb₂, rfl⟩ := AddSubgroup.mem_sup.mp hbmem
      have hdY₂ : s g • a₂ + a₂ ∈ fixedSub Y (Lom Q u' : Set (Gom Q)) :=
        AddSubgroup.add_mem _ (smul_mem_fixedSub_of_conj (s g)
          (fun h hh => conj_mem_Lom_of_fix (s g) (hs' g) hh) ha₂) ha₂
      have e1 : β (s g • a₂ + a₂) b₂ = 0 := hiso₂ _ hdY₂ _ hb₂
      have e2 : β (s g • a₂ + a₂) b₁ = 0 := by
        have h3 : β (s g • a₂) b₁ = β a₂ b₁ := by
          have := hinv (s g)⁻¹ (s g • a₂) b₁
          rw [inv_smul_smul, ← map_inv, htriv g⁻¹ b₁ hb₁] at this
          exact this.symm
        rw [map_add, AddMonoidHom.add_apply, h3]
        exact CharTwo.add_self_eq_zero _
      rw [map_add, e1, e2]
      exact add_zero _
    have : s g • a₂ = a₂ := add_right_cancel (hd.trans (h2 a₂).symm)
    rw [smul_add, htriv g a₁ ha₁, this]
  set σ₀ : Gom Q := s g₀ with hσ₀
  have hw₁ : polar Q u (σ₀.app w₀) = 0 := by
    have := Gom.polar_app σ₀ u w₀
    rwa [hs g₀, hw₀] at this
  set y₀ : Gom Q := eichlerG Q u w₀ with hy₀
  set y₁ : Gom Q := eichlerG Q u (σ₀.app w₀) with hy₁
  have hconj : σ₀ * y₀ * σ₀⁻¹ = y₁ := by
    rw [hy₀, eichlerG_conj, hs g₀]
  have hy₂ : y₁ * y₀ = eichlerG Q u (σ₀.app w₀ + w₀) := eichlerG_mul hw₁ hw₀
  have hw₂ : polar Q u (σ₀.app w₀ + w₀) = 0 := by
    rw [polar_add_right, hw₁, hw₀, add_zero]
  have hy₂L : y₁ * y₀ ∈ Lom Q u := by
    rw [hy₂]
    exact eichlerG_mem_Lom hw₂
  have hy₂n : (y₁ * y₀).NonA2 := by
    rw [hy₂]
    exact ⟨u', polar_eichlerG_ne_zero' hu hw₂ hQw huu'⟩
  have hrange := hc2 _ hy₂L hy₂n
  have hact : ∀ a : Y, (y₁ * y₀) • a = a := by
    intro a
    have h1 : ∀ x : Y, y₁ • x = y₀ • x := by
      intro x
      rw [← hconj, mul_smul, mul_smul]
      have h2' : σ₀⁻¹ • x = x := by
        have := hall g₀⁻¹ x
        rwa [map_inv] at this
      rw [h2', hall g₀]
    rw [mul_smul, h1, ← mul_smul, hy₀, eichlerG_mul_self hw₀, one_smul]
  apply hY₁
  rw [← hrange, eq_bot_iff]
  rintro _ ⟨c, rfl⟩
  rw [comm_apply, hact c, sub_self]
  exact zero_mem _

end Levi

section Main

variable {K : Type} [Field K] [Finite K] [CharP K 2]

local notation "Qp" => quadPlus 3 K

theorem leviE0_quad : quadPlus 3 K (Pi.single (Sum.inl 0) 1 : Fin 3 ⊕ Fin 3 → K) = 0 := by
  rw [show ⇑(quadPlus 3 K) = StatedQuadPlus 3 K from coe_quadPlus 3 K]
  simp [StatedQuadPlus, CFSG.MatrixModel.plusQuadCore, Fin.sum_univ_three]

theorem leviE0'_quad : quadPlus 3 K (Pi.single (Sum.inr 0) 1 : Fin 3 ⊕ Fin 3 → K) = 0 := by
  rw [show ⇑(quadPlus 3 K) = StatedQuadPlus 3 K from coe_quadPlus 3 K]
  simp [StatedQuadPlus, CFSG.MatrixModel.plusQuadCore, Fin.sum_univ_three]

theorem leviE0_polar : polar (quadPlus 3 K) (Pi.single (Sum.inl 0) 1 : Fin 3 ⊕ Fin 3 → K)
    (Pi.single (Sum.inr 0) 1) = 1 := by
  rw [show ⇑(quadPlus 3 K) = StatedQuadPlus 3 K from coe_quadPlus 3 K]
  simp [QuadraticMap.polar, StatedQuadPlus, CFSG.MatrixModel.plusQuadCore, Fin.sum_univ_three,
    Pi.single_apply]

theorem leviE0_ne : (Pi.single (Sum.inl 0) 1 : Fin 3 ⊕ Fin 3 → K) ≠ 0 := by
  intro h
  have := congrFun h (Sum.inl 0)
  simp at this

theorem leviE0'_ne : (Pi.single (Sum.inr 0) 1 : Fin 3 ⊕ Fin 3 → K) ≠ 0 := by
  intro h
  have := congrFun h (Sum.inr 0)
  simp at this

theorem noInvariantForm_gom (hK : 4 ≤ Nat.card K)
    (Y : Type) [AddCommGroup Y] [Finite Y] [DistribMulAction (Gom (quadPlus 3 K)) Y]
    (h2 : ∀ a : Y, a + a = 0)
    (hdec : IsCompl
      (fixedSub Y (Lom (quadPlus 3 K) (Pi.single (Sum.inl 0) 1) : Set (Gom (quadPlus 3 K))))
      (fixedSub Y (Lom (quadPlus 3 K) (Pi.single (Sum.inr 0) 1) : Set (Gom (quadPlus 3 K)))))
    (hcard : Nat.card Y = Nat.card K ^ 4) (β : Y →+ Y →+ ZMod 2)
    (hinv : ∀ (g : Gom (quadPlus 3 K)) a b, β (g • a) (g • b) = β a b)
    (hnd : ∀ a : Y, (∀ b : Y, β a b = 0) → a = 0) : False := by
  classical
  set u : Fin 3 ⊕ Fin 3 → K := Pi.single (Sum.inl 0) 1 with hudef
  set u' : Fin 3 ⊕ Fin 3 → K := Pi.single (Sum.inr 0) 1 with hu'def
  have hu : Qp u = 0 := leviE0_quad
  have hu' : Qp u' = 0 := leviE0'_quad
  have huu' : polar Qp u u' ≠ 0 := by
    rw [hudef, hu'def, leviE0_polar]
    exact one_ne_zero
  have huu'' : polar Qp u' u ≠ 0 := by rwa [polar_comm]
  have hQ : (polarBilin Qp).Nondegenerate := nondegenerate_polarBilin_quadPlus 3 K
  have h4 : 4 ≤ Module.finrank K (Fin 3 ⊕ Fin 3 → K) := by
    rw [Module.finrank_fintype_fun_eq_card]
    simp [Fintype.card_sum]
  have hcard12 := card_fixedSub_Lom_eq (M := Y) hQ h4 hu hu' huu'
  obtain ⟨w₁, hw₁, hQw₁⟩ := exists_nonsingular_perp hQ h4 (leviE0_ne (K := K))
  obtain ⟨w₂, hw₂, hQw₂⟩ := exists_nonsingular_perp hQ h4 (leviE0'_ne (K := K))
  have hx₁L : eichlerG Qp u w₁ ∈ Lom Qp u := eichlerG_mem_Lom hw₁
  have hx₂L : eichlerG Qp u' w₂ ∈ Lom Qp u' := eichlerG_mem_Lom hw₂
  have hx₁n : (eichlerG Qp u w₁).NonA2 := ⟨u', polar_eichlerG_ne_zero' hu hw₁ hQw₁ huu''⟩
  have hx₂n : (eichlerG Qp u' w₂).NonA2 := ⟨u, polar_eichlerG_ne_zero' hu' hw₂ hQw₂ huu'⟩
  have key₂ := stroth_2_1_ii_omega_fixed_of_card hQ h2 hu hu' huu' hdec hcard12 hx₂L hx₂n
  have key₁ := stroth_2_1_ii_omega_fixed_of_card hQ h2 hu' hu huu'' hdec.symm hcard12.symm hx₁L
    hx₁n
  have hc2₂ : ∀ x ∈ Lom Qp u', x.NonA2 → (comm Y x).range = fixedSub Y (Lom Qp u' : Set (Gom Qp)) :=
    fun x hx hn => (stroth_2_1_ii_omega_fixed_of_card hQ h2 hu hu' huu' hdec hcard12 hx hn).2.1
  have hc2₁ : ∀ x ∈ Lom Qp u, x.NonA2 → (comm Y x).range = fixedSub Y (Lom Qp u : Set (Gom Qp)) :=
    fun x hx hn => (stroth_2_1_ii_omega_fixed_of_card hQ h2 hu' hu huu'' hdec.symm hcard12.symm
      hx hn).2.1
  have hY₁card : Nat.card (fixedSub Y (Lom Qp u : Set (Gom Qp))) = Nat.card K ^ 2 := by
    have h := key₁.2.2
    rw [hcard] at h
    have h' : (Nat.card K ^ 2) ^ 2 = Nat.card (fixedSub Y (Lom Qp u : Set (Gom Qp))) ^ 2 := by
      rw [← pow_mul, h]
    exact ((Nat.pow_left_injective (by norm_num : (2 : ℕ) ≠ 0)) h').symm
  have hiso₂ := isotropic_of_range_comm β hinv hx₂L (hc2₂ _ hx₂L hx₂n)
  have hY₁ : fixedSub Y (Lom Qp u : Set (Gom Qp)) ≠ ⊥ := by
    intro h
    have h1 : Nat.card (fixedSub Y (Lom Qp u : Set (Gom Qp))) = 1 := by
      rw [h]
      exact Nat.card_unique
    rw [hY₁card] at h1
    have : 1 < Nat.card K ^ 2 := by nlinarith
    omega
  obtain ⟨σ, τ, hσΩ, hτΩ, hστ, hσfix, hτfix, hσw, hτw⟩ := exists_levi_pair hK
  set E := ElemMatrixIso.plus (K := K) (m := 3) le_rfl with hE
  let σ' : SL(2, K) →* Gom Qp :=
    E.equiv.toMonoidHom.comp (σ.codRestrict (StatedOmega (StatedQuadPlus 3 K)) hσΩ)
  let τ' : SL(2, K) →* Gom Qp :=
    E.equiv.toMonoidHom.comp (τ.codRestrict (StatedOmega (StatedQuadPlus 3 K)) hτΩ)
  have hσ'app : ∀ g v, (σ' g).app v = (σ g : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) K) *ᵥ v :=
    fun g v => E.app ⟨σ g, hσΩ g⟩ v
  have hτ'app : ∀ g v, (τ' g).app v = (τ g : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) K) *ᵥ v :=
    fun g v => E.app ⟨τ g, hτΩ g⟩ v
  have hσ'u : ∀ g, (σ' g).app u = u := fun g => by rw [hσ'app]; exact (hσfix g).1
  have hσ'u' : ∀ g, (σ' g).app u' = u' := fun g => by rw [hσ'app]; exact (hσfix g).2
  have hτ'u : ∀ g, (τ' g).app u = u := fun g => by rw [hτ'app]; exact (hτfix g).1
  have hτ'u' : ∀ g, (τ' g).app u' = u' := fun g => by rw [hτ'app]; exact (hτfix g).2
  have hcomm' : ∀ g h, σ' g * τ' h = τ' h * σ' g := by
    intro g h
    show E.equiv ⟨σ g, hσΩ g⟩ * E.equiv ⟨τ h, hτΩ h⟩ = E.equiv ⟨τ h, hτΩ h⟩ * E.equiv ⟨σ g, hσΩ g⟩
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (hστ g h)
  let ρ₁ : SL(2, K) →* AddMonoid.End Y := (DistribMulAction.toAddMonoidEnd (Gom Qp) Y).comp σ'
  let ρ₂ : SL(2, K) →* AddMonoid.End Y := (DistribMulAction.toAddMonoidEnd (Gom Qp) Y).comp τ'
  have hρ₁ : ∀ g a, ρ₁ g a = σ' g • a := fun g a => rfl
  have hρ₂ : ∀ g a, ρ₂ g a = τ' g • a := fun g a => rfl
  have hcommρ : ∀ g h a, ρ₁ g (ρ₂ h a) = ρ₂ h (ρ₁ g a) := by
    intro g h a
    rw [hρ₁, hρ₂, hρ₂, hρ₁, ← mul_smul, ← mul_smul, hcomm']
  have hinvσ : ∀ g, ∀ a ∈ fixedSub Y (Lom Qp u : Set (Gom Qp)), ρ₁ g a ∈
      fixedSub Y (Lom Qp u : Set (Gom Qp)) := fun g a ha =>
    smul_mem_fixedSub_of_conj (σ' g) (fun h hh => conj_mem_Lom_of_fix (σ' g) (hσ'u g) hh) ha
  have hinvτ : ∀ g, ∀ a ∈ fixedSub Y (Lom Qp u : Set (Gom Qp)), ρ₂ g a ∈
      fixedSub Y (Lom Qp u : Set (Gom Qp)) := fun g a ha =>
    smul_mem_fixedSub_of_conj (τ' g) (fun h hh => conj_mem_Lom_of_fix (τ' g) (hτ'u g) hh) ha
  rcases sl2_commuting_trivial hK ρ₁ ρ₂ hcommρ (fixedSub Y (Lom Qp u : Set (Gom Qp)))
      (fun a _ => h2 a) hY₁card hinvσ hinvτ with h | h
  · exact levi_trivial_false hu huu'' hdec h2 β hinv hnd hY₁ hc2₁ hiso₂ σ' hσ'u hσ'u'
      (by
        obtain ⟨g, w, hw, hQ'⟩ := hσw
        exact ⟨g, w, hw, by rw [hσ'app]; exact hQ'⟩)
      (fun g a ha => h g a ha)
  · exact levi_trivial_false hu huu'' hdec h2 β hinv hnd hY₁ hc2₁ hiso₂ τ' hτ'u hτ'u'
      (by
        obtain ⟨g, w, hw, hQ'⟩ := hτw
        exact ⟨g, w, hw, by rw [hτ'app]; exact hQ'⟩)
      (fun g a ha => h g a ha)

end Main

end CFSG.RankThree.GF2n.Stroth80
