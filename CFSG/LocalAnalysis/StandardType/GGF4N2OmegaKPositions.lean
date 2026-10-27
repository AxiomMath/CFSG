module

public import CFSG.LocalAnalysis.StandardType.GGF4N2OmegaK
public import CFSG.LocalAnalysis.StandardType.GGF4N2JPositions
public import CFSG.GroupTheory.SupCommute
public import CFSG.LocalAnalysis.StandardType.GGTBJOmFrame
public import CFSG.LocalAnalysis.StandardType.GGTBJOmCompFixed
public import CFSG.RankThree.PartOne.KFR4.Frame
public import CFSG.LocalAnalysis.StandardType.GGTBJFrameBs
public import CFSG.LocalAnalysis.StandardType.GGTBJOmTorusAut
public import CFSG.LocalAnalysis.StandardType.GGSecFiveRestGen

public section

namespace CFSG.StandardType

open CFSG.Open CFSG.Assembly CFSG.LieType.Universal CFSG.LieType.Universal.Spin
  CFSG.RankThree.Classical2 CFSG.ClassicalGroups.Orthogonal
open Module Multiplicative
open Polynomial CFSG.RankThree.PartOne.KCPrimary CFSG.RankThree.PartOne.KCOrthogonal
  CFSG.GroupTheory.WeirSylow

theorem ggF4N2OmegaK_J_native_positions
    {G : Type} [Group G] [Finite G] {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    {y : G} {K : Subgroup G}
    {Rd Ra : Prop} (hR : GGSecFiveRestGen 5 B Bs x L D J Rd Ra)
    (hNbr : GGNbr 5 B x D J y K)
    (hL : GGCentralImage .POmegaMinus 4 2 L)
    (hK : GGCentralImage .POmegaMinus 4 2 K) :
    let F := GaloisField 2 2
    let V := (Fin 3 ⊕ Fin 3 ⊕ Fin 2 → F)
    let Q := quadMinus 4 F (minusCoeffs 2 2).1 (minusCoeffs 2 2).2
    ∃ a : K, (a : G) ∈ D ∧ orderOf a = 5 ∧
      D = Subgroup.zpowers y ⊔ Subgroup.zpowers (a : G) ∧
      (∀ k : K, x * (k : G) * x⁻¹ = ((a * k * a⁻¹ : K) : G)) ∧
      ∃ θ : K ≃* ProjOrthDerived Q,
        (J.subgroupOf K).map θ.toMonoidHom =
          LargeEvenLayer (Subgroup.centralizer ({θ a} : Set (ProjOrthDerived Q))) ∧
      ∃ (u : ↥(orthDerived Q)) (_hu : OddOrderIsometry Q 5 (u : V ≃ₗ[F] V)),
        QuotientGroup.mk u = θ a ∧
        ((∃ h ∈ primaryFactors (u : V ≃ₗ[F] V).toLinearMap, h ≠ Polynomial.X - 1 ∧
            primaryMultiplicity (u : V ≃ₗ[F] V).toLinearMap h = 3 ∧
            CFSG.IsQuasisimple ↥(specialBlock Q (u : V ≃ₗ[F] V) h) ∧
            (J.subgroupOf K).map θ.toMonoidHom = componentImage Q (u : V ≃ₗ[F] V) h) ∨
          (finrank F (fixedSpace (u : V ≃ₗ[F] V)) = 6 ∧
            IsPlusType (Q.comp (fixedSpace (u : V ≃ₗ[F] V)).subtype) ∧
            (J.subgroupOf K).map θ.toMonoidHom = fixedComponentImage Q (u : V ≃ₗ[F] V))) := by
  classical
  dsimp only
  let F := GaloisField 2 2
  let b : F := (minusCoeffs 2 2).1
  let c : F := (minusCoeffs 2 2).2
  let Q := quadMinus 4 F b c
  obtain ⟨a, haD, haO, hspan, hJC, hpoint⟩ := ggF4N2OmegaK_J_singleton_component hR hNbr hL hK
  obtain ⟨eK⟩ := ggN2OrthDerived_model_of_centralImage hK
  have hbc : ∀ s : F, s ^ 2 + b * s + c ≠ 0 := minusCoeffs_irr 2 2
  obtain ⟨hQ, hT⟩ := regular_quadMinus (by norm_num : 4 ≤ 4) hbc
  have hsc := OrthRestOdd.scalars_subgroupOf_orthDerived_eq_bot Q hQ
  let ep : ProjOrthDerived Q ≃* orthDerived Q :=
    (QuotientGroup.quotientMulEquivOfEq hsc).trans QuotientGroup.quotientBot
  let θ : K ≃* ProjOrthDerived Q := eK.trans ep.symm
  have hJK := ggF4N2J_le_omega_neighbor hR hNbr hL hK
  let eJ : J ≃* (J.subgroupOf K).map θ.toMonoidHom :=
    (Subgroup.subgroupOfEquivOfLe hJK).symm.trans
      ((J.subgroupOf K).equivMapOfInjective θ.toMonoidHom θ.injective)
  let eJQ := QuotientGroup.congr _ _ eJ (Subgroup.map_center_eq eJ)
  have hJ' := CFSG.LocalAnalysis.ComponentInitial.isComponentOf_map_of_injective
    hJC θ.toMonoidHom θ.injective
  rw [CFSG.LocalAnalysis.ComponentInitial.map_centralizer_singleton_mulEquiv] at hJ'
  have hm := CFSG.GroupTheory.WeirSylow.not_isPlusType_quadMinus (by norm_num : 1 ≤ 4) hbc
  have ha5 : (θ a) ^ 5 = 1 := by rw [← map_pow, ← haO, pow_orderOf_eq_one a, map_one]
  have ha1 : θ a ≠ 1 := by
    intro h
    have h1 : a = 1 := θ.injective (h.trans (map_one θ).symm)
    rw [h1, orderOf_one] at haO
    norm_num at haO
  have hF : Nat.card F = 4 := by simpa using GaloisField.card 2 2 (by norm_num)
  have hdim : finrank F (Fin 3 ⊕ Fin 3 ⊕ Fin 2 → F) = 8 := by simp
  obtain ⟨u, hu, hua, hpos⟩ := N2Orthogonal.component_cases_of_not_sl2 hQ hT hF hdim hm
    (θ a) ha5 ha1 ((J.subgroupOf K).map θ.toMonoidHom)
    (isComponentOf_iff_open.mp hJ')
    (fun F' _ _ hF' => ⟨fun ε => (ggF4N2J_not_psl24 hF' hR hL).false (eJQ.trans ε)⟩)
    (fun F' _ _ hF' => ⟨fun ε =>
      (ggF4N2J_not_psl2_of_card_sixteen hF' hR hL).false (eJQ.trans ε)⟩)
  have hu1 : (u : (Fin 3 ⊕ Fin 3 ⊕ Fin 2 → F) ≃ₗ[F]
      (Fin 3 ⊕ Fin 3 ⊕ Fin 2 → F)) ≠ 1 := by
    intro heq
    have hueq : u = 1 := Subtype.ext heq
    apply ha1
    rw [← hua, hueq, QuotientGroup.mk_one]
  have hpi : CFSG.RankThree.PartOne.piOrth Q u = θ a := hua
  have hJpi : CFSG.Open.IsComponentOf ((J.subgroupOf K).map θ.toMonoidHom)
      (Subgroup.centralizer ({CFSG.RankThree.PartOne.piOrth Q u} : Set (ProjOrthDerived Q))) := by
    rw [hpi]
    exact isComponentOf_iff_open.mp hJ'
  have hLayer := N2Orthogonal.largeEvenLayer_eq_of_component_position hQ hT hF hdim hm
    u hu hu1 ((J.subgroupOf K).map θ.toMonoidHom) hJpi hpos
  rw [hpi] at hLayer
  exact ⟨a, haD, haO, hspan, hpoint, θ, hLayer.symm, u, hu, hua, hpos⟩

theorem ggF4N2OmegaK_J_layer
    {G : Type} [Group G] [Finite G] {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    {y : G} {K : Subgroup G}
    {Rd Ra : Prop} (hR : GGSecFiveRestGen 5 B Bs x L D J Rd Ra)
    (hNbr : GGNbr 5 B x D J y K)
    (hL : GGCentralImage .POmegaMinus 4 2 L)
    (hK : GGCentralImage .POmegaMinus 4 2 K) :
    LargeEvenLayer (K ⊓ Subgroup.centralizer ({x} : Set G)) = J := by
  obtain ⟨a, -, -, -, hpoint, θ, hJlayer, -⟩ :=
    ggF4N2OmegaK_J_native_positions hR hNbr hL hK
  have hJKlayer : J.subgroupOf K =
      LargeEvenLayer (Subgroup.centralizer ({a} : Set K)) := by
    apply Subgroup.map_injective (f := θ.toMonoidHom) θ.injective
    rw [← largeEvenLayer_map_of_injective _ θ.injective,
      CFSG.LocalAnalysis.ComponentInitial.map_centralizer_singleton_mulEquiv]
    exact hJlayer
  have hcent : (K ⊓ Subgroup.centralizer ({x} : Set G)).subgroupOf K =
      Subgroup.centralizer ({a} : Set K) := by
    ext k
    change (k : G) ∈ K ⊓ Subgroup.centralizer ({x} : Set G) ↔
      k ∈ Subgroup.centralizer ({a} : Set K)
    rw [Subgroup.mem_inf, Subgroup.mem_centralizer_singleton_iff,
      Subgroup.mem_centralizer_singleton_iff, and_iff_right k.2]
    constructor
    · intro hk
      apply Subtype.ext
      have hfix : x * (k : G) * x⁻¹ = (k : G) := by rw [← hk]; group
      exact ((mul_inv_eq_iff_eq_mul.mp ((hpoint k).symm.trans hfix))).symm
    · intro hk
      have hafix : a * k * a⁻¹ = k := by rw [← hk]; group
      have hfix := (hpoint k).trans (congrArg Subtype.val hafix)
      exact (mul_inv_eq_iff_eq_mul.mp hfix).symm
  have hCmap : (Subgroup.centralizer ({a} : Set K)).map K.subtype =
      K ⊓ Subgroup.centralizer ({x} : Set G) := by
    rw [← hcent]
    exact Subgroup.map_subgroupOf_eq_of_le inf_le_left
  calc
    LargeEvenLayer (K ⊓ Subgroup.centralizer ({x} : Set G)) =
        LargeEvenLayer ((Subgroup.centralizer ({a} : Set K)).map K.subtype) := by rw [hCmap]
    _ = (LargeEvenLayer (Subgroup.centralizer ({a} : Set K))).map K.subtype :=
      largeEvenLayer_map_of_injective _ K.subtype_injective _
    _ = (J.subgroupOf K).map K.subtype := by rw [← hJKlayer]
    _ = J := Subgroup.map_subgroupOf_eq_of_le (ggF4N2J_le_omega_neighbor hR hNbr hL hK)

end CFSG.StandardType
