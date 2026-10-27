module

public import CFSG.LieType.AlgebraicGroups.RationalInnerDiagonal
public import CFSG.LieType.Chevalley.CLSOddToralOrdinaryComponentRootFactor
public import CFSG.LocalAnalysis.SteinbergBMOddResidualTools
import CFSG.LocalAnalysis.SteinbergBMEvenG2FixedNoNormalSL2

public noncomputable section

namespace CFSG.LocalAnalysis.SteinbergBM

open Subgroup CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.AlgebraicGroups
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

theorem exists_mulEquiv_toralCentralizer_of_innerDiagonal
    {τ : Tag} {F : Type} [Field F]
    [Finite F] (hτ : τ = .G2 ∨ τ = .F4 ∨ τ = .E6 ∨ τ = .E8) (hF : Odd (Nat.card F))
    {α : MulAut (adjointGroup τ F)} {g : adjointGroup τ F} {a : Fin τ.rank → Fˣ}
    (hαg : ∀ h : adjointGroup τ F, (α h : ModGL τ F) =
      (g : ModGL τ F) * rootDiagUnit τ a * h * (rootDiagUnit τ a)⁻¹ * (g : ModGL τ F)⁻¹)
    (hα : α ^ 2 = 1) :
    ∃ b : Fin τ.rank → Fˣ, (∀ i, b i = 1 ∨ b i = -1) ∧
      Nonempty (↥(α.toMonoidHom.eqLocus (MonoidHom.id (adjointGroup τ F))) ≃*
        ↥(toralCentralizer τ F b)) := by
  classical
  have : Fintype F := Fintype.ofFinite F
  set L := AlgebraicClosure F
  set ι := algebraMap F L with hι
  set p := ringChar F with hp_def
  have hpF : CharP F p := ringChar.charP F
  obtain ⟨n, hp, hcard⟩ := FiniteField.card F p
  have : Fact p.Prime := ⟨hp⟩
  have : CharP L p := charP_of_injective_algebraMap (algebraMap F L).injective p
  set Fr := iterateFrobenius L p n with hFr_def
  have hFr : ∀ c, Fr c = c ^ Nat.card F := fun c => by
    rw [hFr_def, iterateFrobenius_def, Nat.card_eq_fintype_card, hcard]
  have hFrι : ∀ c : F, Fr (ι c) = ι c := fun c => by
    rw [hFr, ← map_pow, Nat.card_eq_fintype_card, FiniteField.pow_card]
  set bL : Fin τ.rank → Lˣ := fun i => Units.map ι.toMonoidHom (a i) with hbL
  set x := baseChangeGL ι (g : ModGL τ F) * rootDiagUnit τ bL with hx_def
  obtain ⟨hinj, hHG, hfaith, -⟩ :=
    exceptional_Lang_finite_root_centralizer_faithfulness τ F hF L ι
  have hgG : baseChangeGL ι (g : ModGL τ F) ∈ adjointGroup τ L := hHG ⟨g, g.2, rfl⟩
  have hxG : x ∈ adjointGroup τ L :=
    mul_mem hgG (exceptional_Lang_adjoint_diagonal_lift τ L bL).1
  have hdb : baseChangeGL ι (rootDiagUnit τ a) = rootDiagUnit τ bL :=
    baseChangeGL_rootDiagUnit ι a
  have hxconj : ∀ h : adjointGroup τ F,
      x * baseChangeGL ι (h : ModGL τ F) * x⁻¹ = baseChangeGL ι (α h : ModGL τ F) := by
    intro h
    rw [hαg h, map_mul, map_mul, map_mul, map_mul, map_inv, map_inv, hdb, hx_def]
    group
  obtain ⟨-, hHR, -, -⟩ := exceptional_Lang_Frobenius_fixed_derived_root_group τ F hF L Fr hFr
  have hgR := hHR ⟨g, g.2, rfl⟩
  have hFd : Units.map (entrywiseHom Fr) (rootDiagUnit τ bL) = rootDiagUnit τ bL := by
    refine Units.ext ?_
    change entrywise Fr (rootDiag bL) = rootDiag bL
    rw [entrywise_rootDiag]
    congr 1
    funext i
    ext
    exact hFrι _
  have hxR : x ∈ adjointGroup τ L ⊓ (Units.map (entrywiseHom Fr)).eqLocus (MonoidHom.id _) := by
    refine Subgroup.mem_inf.2 ⟨hxG, ?_⟩
    change Units.map (entrywiseHom Fr) x = x
    rw [hx_def, map_mul, hFd]
    congr 1
    exact (Subgroup.mem_inf.1 hgR).2
  have hα2 : ∀ h, α (α h) = h := fun h => by
    have := congrArg (fun φ : MulAut (adjointGroup τ F) => φ h) hα
    simpa [sq] using this
  have hx2 : x ^ 2 = 1 := by
    refine hfaith _ (pow_mem hxG 2) fun y hy => ?_
    obtain ⟨h, hh, rfl⟩ := hy
    have h1 := hxconj ⟨h, hh⟩
    have h2 := hxconj (α ⟨h, hh⟩)
    rw [hα2] at h2
    change x * baseChangeGL ι h * x⁻¹ = _ at h1
    change _ = baseChangeGL ι h at h2
    rw [sq]
    calc x * x * baseChangeGL ι h =
        (x * (x * baseChangeGL ι h * x⁻¹) * x⁻¹) * (x * x) := by group
      _ = baseChangeGL ι h * (x * x) := by rw [h1, h2]
  obtain ⟨h, -, a', ha', -, -, hCh, -⟩ :=
    G2_F4_E6_E8_rational_inner_diagonal_involution_fixed_p_components τ F L hτ hF Fr hFr hxR hx2
  let φ : adjointGroup τ F →* ModGL τ L := (baseChangeGL ι).comp (adjointGroup τ F).subtype
  have hφ : Function.Injective φ := hinj.comp Subtype.val_injective
  have hmap : (α.toMonoidHom.eqLocus (MonoidHom.id (adjointGroup τ F))).map φ =
      (adjointGroup τ F).map (baseChangeGL ι) ⊓ Subgroup.centralizer {x} := by
    ext y
    simp only [Subgroup.mem_map, Subgroup.mem_inf, Subgroup.mem_centralizer_singleton_iff]
    constructor
    · rintro ⟨c, hc, rfl⟩
      refine ⟨⟨c, c.2, rfl⟩, ?_⟩
      have h1 := hxconj c
      have hc' : α c = c := hc
      rw [hc'] at h1
      change baseChangeGL ι (c : ModGL τ F) * x = x * baseChangeGL ι (c : ModGL τ F)
      calc baseChangeGL ι (c : ModGL τ F) * x =
          (x * baseChangeGL ι (c : ModGL τ F) * x⁻¹) * x := by rw [h1]
        _ = x * baseChangeGL ι (c : ModGL τ F) := by group
    · rintro ⟨⟨c, hc, rfl⟩, hcx⟩
      refine ⟨⟨c, hc⟩, ?_, rfl⟩
      have h1 := hxconj ⟨c, hc⟩
      have h2 : x * baseChangeGL ι c * x⁻¹ = baseChangeGL ι c := by
        rw [← hcx]
        group
      rw [h2] at h1
      exact Subtype.ext (hinj h1.symm)
  let e : ↥(α.toMonoidHom.eqLocus (MonoidHom.id (adjointGroup τ F))) ≃*
      ↥((adjointGroup τ F).map (baseChangeGL ι) ⊓ Subgroup.centralizer {x}) :=
    (Subgroup.equivMapOfInjective _ φ hφ).trans (MulEquiv.subgroupCongr hmap)
  let e1 : ↥((adjointGroup τ F).map (baseChangeGL ι) ⊓ Subgroup.centralizer {x}) ≃*
      ↥((adjointGroup τ F).map (baseChangeGL ι) ⊓ Subgroup.centralizer {rootDiagUnit τ a'}) :=
    ((MulAut.conj h).subgroupMap _).trans (MulEquiv.subgroupCongr hCh)
  set b : Fin τ.rank → Fˣ := fun i => if a' i = 1 then 1 else -1 with hb_def
  have hb : ∀ i, b i = 1 ∨ b i = -1 := fun i => by
    by_cases h1 : a' i = 1 <;> simp [hb_def, h1]
  have hab : (fun i => Units.map (algebraMap F L).toMonoidHom (b i)) = a' := by
    funext i
    by_cases h1 : a' i = 1
    · simp [hb_def, h1]
    · have h2 : a' i = -1 := (ha' i).resolve_left h1
      rw [h2]
      simp only [hb_def, h1, ↓reduceIte]
      exact Units.ext (by simp)
  have hXK := map_baseChangeGL_toralCentralizer (algebraMap F L) b
  rw [hab] at hXK
  let e2 : ↥(toralCentralizer τ F b) ≃*
      ↥((adjointGroup τ F).map (baseChangeGL ι) ⊓ Subgroup.centralizer {rootDiagUnit τ a'}) :=
    (Subgroup.equivMapOfInjective _ _ (baseChangeGL_injective (algebraMap F L))).trans
      (MulEquiv.subgroupCongr hXK)
  exact ⟨b, hb, ⟨e.trans (e1.trans e2.symm)⟩⟩

theorem exists_injective_SL2_of_normal_simple_toralCentralizer
    {τ : Tag} {F : Type} [Field F]
    [Finite F] (hF : ringChar F ≠ 2) (b : Fin τ.rank → Fˣ) (hb : ∀ i, b i = 1 ∨ b i = -1)
    (S : Subgroup (toralCentralizer τ F b)) (hSn : S.Normal) (hSs : IsSimpleGroup S)
    (hSnab : ∃ x y : S, x * y ≠ y * x) : ∃ φ : SL2 F →* S, Function.Injective φ := by
  classical
  have : Fintype F := Fintype.ofFinite F
  have : CharP F (ringChar F) := ringChar.charP F
  obtain ⟨n, hr, -⟩ := FiniteField.card F (ringChar F)
  obtain ⟨Ψ, -, hroots, -⟩ :=
    odd_toral_ordinary_component_root_factor_and_prime_divisor (ringChar F) hr hF F τ b hb
      (maskChar (signTupleBits b)) (rootCharKernel_eq_kernelRoots hF hb).symm _
      (isComponentOf_map_of_normal_simple S hSn hSs hSnab)
  obtain ⟨⟨β, hβ⟩, rfl⟩ := Quotient.exists_rep Ψ
  have hΨ := isRootComponent_componentRoots (χ := maskChar (signTupleBits b)) ⟦⟨β, hβ⟩⟧
  have hβΨ : β ∈ componentRoots (maskChar (signTupleBits b)) ⟦⟨β, hβ⟩⟧ := ⟨hβ, rfl⟩
  have hQ : rootSubgroup τ F β ⊔ rootSubgroup τ F (-β) ≤ S.map (toralCentralizer τ F b).subtype :=
    sup_le (hroots β hβΨ) (hroots (-β) (hΨ.neg_mem β hβΨ))
  obtain ⟨-, ⟨e⟩, -⟩ := odd_arbitrary_root_pair_SL2_p_components τ F hF (hΨ.isRoot β hβΨ)
  let eS := S.equivMapOfInjective _ (toralCentralizer τ F b).subtype_injective
  exact ⟨eS.symm.toMonoidHom.comp ((Subgroup.inclusion hQ).comp e.toMonoidHom),
    eS.symm.injective.comp ((Subgroup.inclusion_injective hQ).comp e.injective)⟩

theorem odd_residual_inner_diagonal_fixed_normal_simple_contains_SL2
    {τ : Tag} {F : Type}
    [Field F] [Finite F] (hτ : τ = .G2 ∨ τ = .F4 ∨ τ = .E6 ∨ τ = .E8) (hF : Odd (Nat.card F))
    {α : MulAut (adjointGroup τ F)} {g : adjointGroup τ F} {a : Fin τ.rank → Fˣ}
    (hαg : ∀ h : adjointGroup τ F, (α h : ModGL τ F) =
      (g : ModGL τ F) * rootDiagUnit τ a * h * (rootDiagUnit τ a)⁻¹ * (g : ModGL τ F)⁻¹)
    (hα : α ^ 2 = 1) (S : Subgroup (α.toMonoidHom.eqLocus (MonoidHom.id (adjointGroup τ F))))
    (hSn : S.Normal) (hSs : IsSimpleGroup S) (hSnab : ∃ x y : S, x * y ≠ y * x) :
    ∃ φ : SL2 F →* S, Function.Injective φ := by
  have : Fintype F := Fintype.ofFinite F
  have hF2 : ringChar F ≠ 2 := fun h => by
    have := FiniteField.even_card_iff_char_two.1 h
    rw [← Nat.card_eq_fintype_card] at this
    exact (Nat.not_even_iff_odd.2 hF) (Nat.even_iff.2 this)
  obtain ⟨b, hb, ⟨e⟩⟩ := exists_mulEquiv_toralCentralizer_of_innerDiagonal hτ hF hαg hα
  obtain ⟨S', hS'n, hS's, hS'nab, ⟨eS⟩⟩ := exists_normal_simple_of_mulEquiv e S hSn hSs hSnab
  obtain ⟨φ, hφ⟩ :=
    exists_injective_SL2_of_normal_simple_toralCentralizer hF2 b hb S' hS'n hS's hS'nab
  exact ⟨eS.symm.toMonoidHom.comp φ, eS.symm.injective.comp hφ⟩

theorem odd_inner_diagonal_fixed_no_normal_even_SL2
    {τ : Tag}
    (hτ : τ = .F4 ∨ τ = .E6 ∨ τ = .E8) {F : Type} [Field F] [Finite F] (hF : Odd (Nat.card F))
    {α : MulAut (adjointGroup τ F)} {g : adjointGroup τ F} {a : Fin τ.rank → Fˣ}
    (hαg : ∀ h : adjointGroup τ F, (α h : ModGL τ F) =
      (g : ModGL τ F) * rootDiagUnit τ a * h * (rootDiagUnit τ a)⁻¹ * (g : ModGL τ F)⁻¹)
    (hα : α ^ 2 = 1) (_hα1 : α ≠ 1)
    (S : Subgroup (α.toMonoidHom.eqLocus (MonoidHom.id (adjointGroup τ F)))) (hSn : S.Normal)
    (hSs : IsSimpleGroup S) (hSnab : ∃ x y : S, x * y ≠ y * x)
    (K : Type) [Field K] [CharP K 2] (eS : S ≃* Matrix.SpecialLinearGroup (Fin 2) K) : False := by
  have : Fintype F := Fintype.ofFinite F
  have hF2 : ringChar F ≠ 2 := fun h => by
    have := FiniteField.even_card_iff_char_two.1 h
    rw [← Nat.card_eq_fintype_card] at this
    exact (Nat.not_even_iff_odd.2 hF) (Nat.even_iff.2 this)
  have hτ' : τ = .G2 ∨ τ = .F4 ∨ τ = .E6 ∨ τ = .E8 := Or.inr hτ
  obtain ⟨φ, hφ⟩ :=
    odd_residual_inner_diagonal_fixed_normal_simple_contains_SL2 hτ' hF hαg hα S hSn hSs hSnab
  exact false_of_injective_SL2_of_mulEquiv hF2 φ hφ eS

end CFSG.LocalAnalysis.SteinbergBM
