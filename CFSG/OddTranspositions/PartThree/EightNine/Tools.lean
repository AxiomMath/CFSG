module

public import CFSG.OddTranspositions.PartThree.Statements
public import CFSG.OddTranspositions.FaithfulBlocks
import CFSG.OddTranspositions.SixSevenLocalStep
import CFSG.OddTranspositions.SixTenPetersen
import CFSG.OddTranspositions.PartThree.SixThreeGlobal
import CFSG.LocalAnalysis.ComponentClassification.SolvableRadical
import CFSG.LocalAnalysis.WeakClosure81.FiveNineTwo
import CFSG.Assembly.QuasithinDefs
import CFSG.CGT.Timmesfeld75.Cfg214Gen
import CFSG.CGT.Timmesfeld75.L2Real
import CFSG.Foundations
import CFSG.GroupTheory.ABGLocalTools.Basic
import CFSG.GroupTheory.CardSupInf
import CFSG.GroupTheory.QuasisimpleCommutingProductBound
import CFSG.LargeExtraspecial.S9TIXC
import CFSG.LocalAnalysis.ComponentClassification.FixedCentralPreimage
import CFSG.LocalAnalysis.ComponentClassification.InvolutionDiagonal
import CFSG.LocalAnalysis.ComponentClassification.OddKernelNormalizers
import CFSG.LocalAnalysis.ComponentClassification.TwoLayer
import CFSG.LocalAnalysis.ShultStronglyClosedTI.InvolutionCountingOrderFormula
import CFSG.LocalAnalysis.WeakClosure81.FiveDefs
import CFSG.LocalAnalysis.WeakClosure81.SevenThree
import CFSG.OddTranspositions.BlockAction2
import CFSG.OddTranspositions.CommutatorSize
import CFSG.OddTranspositions.WidthOne
import CFSG.Quasithin.Background.Basic
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.IV.theorem_5_4
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Proposition82Orbit
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Section11Lemma115Torus

public section

namespace CFSG.OddTranspositions.PartThree

open CFSG.Timmesfeld CFSG.Timmesfeld.Bridge CFSG.Timmesfeld.Bridge.Asc72
open CFSG.Timmesfeld.Connectivity CFSG.OddTranspositions.QZ

variable {G : Type} [Group G] [Finite G] {D : Set G}

omit [Finite G] in
theorem conj_mul_mem_map_pCore {H : Subgroup G} {x : H} (hx : x ∈ CFSG.pCore 2 H) {b : G}
    (hbH : b ∈ H) (hb2 : b * b = 1) :
    (x : G) * b * (x : G)⁻¹ * b ∈ (CFSG.pCore 2 H).map H.subtype := by
  set b' : H := ⟨b, hbH⟩ with hb'
  have hmem : x * (b' * x⁻¹ * b'⁻¹) ∈ CFSG.pCore 2 H :=
    Subgroup.mul_mem _ hx
      ((CFSG.pCore_normal (p := 2) (G := H)).conj_mem _ (Subgroup.inv_mem _ hx) b')
  refine ⟨_, hmem, ?_⟩
  have hbinv : b⁻¹ = b := inv_eq_of_mul_eq_one_right hb2
  simp only [Subgroup.coe_subtype, Subgroup.coe_mul, Subgroup.coe_inv, hb', hbinv]
  group

theorem isSolvable_closure_of_mul_mem_map_pCore {H : Subgroup G} {a b c : G} (hbH : b ∈ H)
    (hcH : c ∈ H) (hb2 : b * b = 1) (hc2 : c * c = 1)
    (hab : a * b ∈ (CFSG.pCore 2 H).map H.subtype) :
    Group.IsSolvable (Subgroup.closure ({a, c, b} : Set G)) := by
  obtain ⟨q, hq, hqab⟩ := hab
  set b' : H := ⟨b, hbH⟩ with hb'
  set c' : H := ⟨c, hcH⟩ with hc'
  have hb'2 : b' * b' = 1 := Subtype.ext hb2
  have hc'2 : c' * c' = 1 := Subtype.ext hc2
  have : Group.IsSolvable (CFSG.pCore 2 H) :=
    @IsNilpotent.to_isSolvable _ _ (CFSG.pCore_isPGroup (p := 2) (G := H)).isNilpotent
  have : Group.IsSolvable (Subgroup.zpowers b' ⊔ Subgroup.zpowers c' : Subgroup H) :=
    CFSG.LocalAnalysis.WeakClosure81.isSolvable_sup_zpowers_of_mul_self_eq_one hb'2 hc'2
  set K : Subgroup H := CFSG.pCore 2 H ⊔ (Subgroup.zpowers b' ⊔ Subgroup.zpowers c') with hK
  have hKs : Group.IsSolvable K := CFSG.ComponentClassification.SolvableRadical.solvable_sup _ _
  have hKG : Group.IsSolvable (K.map H.subtype) :=
    @Group.isSolvable_of_isSolvable_injective _ _ _ _
      (Subgroup.equivMapOfInjective K H.subtype H.subtype_injective).symm.toMonoidHom
      (MulEquiv.injective _) hKs
  have hbK : b' ∈ K := Subgroup.mem_sup_right (Subgroup.mem_sup_left (Subgroup.mem_zpowers b'))
  have hcK : c' ∈ K := Subgroup.mem_sup_right (Subgroup.mem_sup_right (Subgroup.mem_zpowers c'))
  have hle : Subgroup.closure ({a, c, b} : Set G) ≤ K.map H.subtype := by
    rw [Subgroup.closure_le]
    rintro y (rfl | rfl | rfl)
    · refine ⟨q * b', Subgroup.mul_mem _ (Subgroup.mem_sup_left hq) hbK, ?_⟩
      simp only [Subgroup.coe_subtype, Subgroup.coe_mul] at hqab ⊢
      rw [hqab, hb', mul_assoc, hb2, mul_one]
    · exact ⟨c', hcK, rfl⟩
    · exact ⟨b', hbK, rfl⟩
  exact @Group.isSolvable_of_isSolvable_injective _ _ _ _ (Subgroup.inclusion hle)
    (Subgroup.inclusion_injective hle) hKG

omit [Finite G] in
private theorem isSolvable_closure_conj_inv (g : G) {a b c : G}
    (hX : Group.IsSolvable (Subgroup.closure ({g * a * g⁻¹, c, g * b * g⁻¹} : Set G))) :
    Group.IsSolvable (Subgroup.closure ({a, b, g⁻¹ * c * g} : Set G)) := by
  set X := Subgroup.closure ({g * a * g⁻¹, c, g * b * g⁻¹} : Set G)
  set f : G →* G := (MulAut.conj g⁻¹).toMonoidHom with hf
  have hXf : Group.IsSolvable (X.map f) :=
    @Group.isSolvable_of_isSolvable_injective _ _ _ _
      (Subgroup.equivMapOfInjective X f (MulAut.conj g⁻¹).injective).symm.toMonoidHom
      (MulEquiv.injective _) hX
  have hfapp : ∀ y : G, f y = g⁻¹ * y * g := fun y => by
    rw [hf, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
  have hle : Subgroup.closure ({a, b, g⁻¹ * c * g} : Set G) ≤ X.map f := by
    rw [Subgroup.closure_le]
    rintro y (rfl | rfl | rfl)
    · exact ⟨g * y * g⁻¹, Subgroup.subset_closure (by simp), by rw [hfapp]; group⟩
    · exact ⟨g * y * g⁻¹, Subgroup.subset_closure (by simp), by rw [hfapp]; group⟩
    · exact ⟨c, Subgroup.subset_closure (by simp), by rw [hfapp]⟩
  exact @Group.isSolvable_of_isSolvable_injective _ _ _ _ (Subgroup.inclusion hle)
    (Subgroup.inclusion_injective hle) hXf

theorem conj_mul_mem_of_mem_blockClass_of_isSolvable (hC : HypothesisC D) {β γ : Set G}
    (hβ : β ∈ blockClass hC.alpha) (hγ : γ ∈ Aalpha D β) {a b c : G} (ha : a ∈ β) (hb : b ∈ β)
    (hab : Commute a b) (hne : a ≠ b) (hc : c ∈ γ)
    (hX : Group.IsSolvable (Subgroup.closure ({a, c, b} : Set G))) :
    (a * b) * c * (a * b)⁻¹ ∈ γ := by
  classical
  have hN := hC.setup.normal
  have hD := hC.setup.oddT
  obtain ⟨g, rfl⟩ := mem_blockClass_iff.mp hβ
  obtain ⟨a₀, ha₀, rfl⟩ := ha
  obtain ⟨b₀, hb₀, rfl⟩ := hb
  set c₀ := g⁻¹ * c * g with hc₀
  set γ₀ := (fun x => g⁻¹ * x * g) '' γ with hγ₀
  have hγ₀A : γ₀ ∈ Aalpha D hC.alpha := by
    have h := Aalpha.conj hN hγ g⁻¹
    rw [image_conj_inv_image_conj] at h
    simpa only [inv_inv] using h
  have hc₀γ₀ : c₀ ∈ γ₀ := ⟨c, hc, rfl⟩
  have hab₀ : Commute a₀ b₀ := by
    have h : (MulAut.conj g) (a₀ * b₀) = (MulAut.conj g) (b₀ * a₀) := by
      simp only [map_mul, MulAut.conj_apply]
      calc g * a₀ * g⁻¹ * (g * b₀ * g⁻¹) = g * b₀ * g⁻¹ * (g * a₀ * g⁻¹) := hab.eq
        _ = _ := rfl
    exact (MulAut.conj g).injective h
  have hne₀ : a₀ ≠ b₀ := fun h => hne (by rw [h])
  have hX₀ : Group.IsSolvable (Subgroup.closure ({a₀, b₀, c₀} : Set G)) :=
    isSolvable_closure_conj_inv g hX
  have haX : a₀ ∈ Subgroup.closure ({a₀, b₀, c₀} : Set G) := Subgroup.subset_closure (by simp)
  have hbX : b₀ ∈ Subgroup.closure ({a₀, b₀, c₀} : Set G) := Subgroup.subset_closure (by simp)
  have hcX : c₀ ∈ Subgroup.closure ({a₀, b₀, c₀} : Set G) := Subgroup.subset_closure (by simp)
  have htri : IsTriangle D a₀ c₀ b₀ :=
    isTriangle_of_mem_Aalpha hD hN hC.isBlock_alpha hγ₀A ha₀ hb₀ hab₀ hne₀ hc₀γ₀
  have h4 : orderOf (a₀ * b₀ * c₀) = 4 :=
    orderOf_mul_eq_four_of_solvable_subgroup hD hN hX₀ haX hcX hbX htri
  have hno : ∀ x ∈ D, x ∈ Subgroup.closure {a₀, c₀} → IsTriangle D a₀ x b₀ →
      ¬ IsThirdKind a₀ x b₀ := by
    intro x _ hx htri'
    have hxX : x ∈ Subgroup.closure ({a₀, b₀, c₀} : Set G) := by
      refine Subgroup.closure_mono ?_ hx
      intro z hz
      rcases hz with rfl | rfl
      · simp
      · simp
    exact not_isThirdKind_of_solvable_subgroup hD hN hX₀ haX hxX hbX htri'
  have key := conj_mul_mem_of_mem_Aalpha hC hγ₀A ha₀ hb₀ hab₀ hne₀ hc₀γ₀ h4 hno
  have hγ := image_conj_image_conj_inv g γ
  simp only [inv_inv] at hγ
  rw [← hγ]
  refine ⟨_, key, ?_⟩
  simp only [hc₀]
  group

private theorem exists_mem_Halpha_conj_eq (hC : HypothesisC D) {β : Set G}
    (hβ : β ∈ Dalpha D hC.alpha) {δ : Set G} (hδ : δ ∈ Dalpha D β) :
    ∃ h ∈ Halpha D β, (fun y => h * y * h⁻¹) '' hC.alpha = δ := by
  classical
  have hN := hC.setup.normal
  have hblock := hC.isBlock_alpha
  obtain ⟨g, hg⟩ := mem_blockClass_iff.mp hβ.1
  have hαβ : hC.alpha ∈ Dalpha D β := Dalpha_symm hβ hblock.subset
  have hback : ∀ S ∈ Dalpha D β, (fun x => g⁻¹ * x * g) '' S ∈ Dalpha D hC.alpha := by
    intro S hS
    have h := Dalpha.conj hN hS g⁻¹
    rw [hg, image_conj_inv_image_conj] at h
    simpa only [inv_inv] using h
  obtain ⟨y₁, hy₁⟩ := nonempty_of_mem_blockClass hblock.nonempty (hback _ hαβ).1
  obtain ⟨y₂, hy₂⟩ := nonempty_of_mem_blockClass hblock.nonempty (hback _ hδ).1
  obtain ⟨h, hh, hhy⟩ := hC.Halpha_transitive y₁ ⟨_, hback _ hαβ, hy₁⟩ y₂ ⟨_, hback _ hδ, hy₂⟩
  have hblk : (fun y => h * y * h⁻¹) '' ((fun x => g⁻¹ * x * g) '' hC.alpha) =
      (fun x => g⁻¹ * x * g) '' δ :=
    eq_of_mem_of_mem_blockClass hblock (conj_image_mem_blockClass (hback _ hαβ).1 h)
      (hback _ hδ).1 ⟨h * y₁ * h⁻¹, ⟨y₁, hy₁, rfl⟩, hhy ▸ hy₂⟩
  refine ⟨g * h * g⁻¹, ?_, ?_⟩
  · have hle : (Halpha D hC.alpha).map (MulAut.conj g).toMonoidHom ≤ Halpha D β := by
      rw [Halpha, MonoidHom.map_closure, Halpha, Subgroup.closure_le]
      rintro _ ⟨z, hz, rfl⟩
      have h1 := DalphaStar.conj hN hz g
      rw [← hg] at h1
      exact Subgroup.subset_closure (by simpa [MulAut.conj_apply] using h1)
    exact hle ⟨h, hh, by simp [MulAut.conj_apply]⟩
  · have hcomp : (fun y => g * h * g⁻¹ * y * (g * h * g⁻¹)⁻¹) '' hC.alpha =
        (fun x => g * x * g⁻¹) '' ((fun y => h * y * h⁻¹) ''
          ((fun x => g⁻¹ * x * g) '' hC.alpha)) := by
      rw [Set.image_image, Set.image_image]
      congr 1
      funext y
      group
    have hδ' := image_conj_image_conj_inv g δ
    simp only [inv_inv] at hδ'
    rw [hcomp, hblk, hδ']

theorem actsTriviallyOnBlocks_of_perp_of_theorem8_7 (h87 : Theorem8_7) (hC : HypothesisC D)
    (hrad : ∀ N : Subgroup G, N.Normal → Group.IsSolvable N → N = ⊥) (hO4 : ¬ O4PairData G D)
    {β : Set G} (hβ : β ∈ Dalpha D hC.alpha) {t : G}
    (ht : ∀ y ∈ DalphaStar D β, Commute t y)
    (htβ : (fun y => t * y * t⁻¹) '' β = β)
    (hperp : ∀ γ ∈ perp D hC.alpha, (fun y => t * y * t⁻¹) '' γ = γ) :
    ActsTriviallyOnBlocks hC.alpha t := by
  classical
  have hN := hC.setup.normal
  have hblock := hC.isBlock_alpha
  have hfixD : ∀ δ ∈ Dalpha D β, (fun y => t * y * t⁻¹) '' δ = δ := by
    intro δ hδ
    have hpt : ∀ y ∈ δ, t * y * t⁻¹ = y := fun y hy => by
      rw [(ht y ⟨δ, hδ, hy⟩).eq, mul_inv_cancel_right]
    calc (fun y => t * y * t⁻¹) '' δ = (fun y => y) '' δ := Set.image_congr hpt
      _ = δ := Set.image_id' δ
  have hHβ : ∀ h ∈ Halpha D β, Commute t h := by
    intro h hh
    have hle : Halpha D β ≤ Subgroup.centralizer ({t} : Set G) := by
      rw [Halpha, Subgroup.closure_le]
      intro y hy
      exact Subgroup.mem_centralizer_singleton_iff.mpr (ht y hy).symm.eq
    exact (Subgroup.mem_centralizer_singleton_iff.mp (hle hh)).symm
  have hfixperp : ∀ δ ∈ Dalpha D β, ∀ ε ∈ perp D δ, (fun y => t * y * t⁻¹) '' ε = ε := by
    intro δ hδ ε hε
    obtain ⟨h, hh, rfl⟩ := exists_mem_Halpha_conj_eq hC hβ hδ
    have hth : Commute t h := hHβ h hh
    rw [← perp_conj_image hN h] at hε
    obtain ⟨ε', hε', rfl⟩ := hε
    have hswap : (fun y => t * y * t⁻¹) '' ((fun y => h * y * h⁻¹) '' ε') =
        (fun y => h * y * h⁻¹) '' ((fun y => t * y * t⁻¹) '' ε') := by
      rw [Set.image_image, Set.image_image]
      congr 1
      funext y
      show t * (h * y * h⁻¹) * t⁻¹ = h * (t * y * t⁻¹) * h⁻¹
      rw [show t * (h * y * h⁻¹) * t⁻¹ = (t * h) * y * (t * h)⁻¹ by group, hth.eq]
      group
    rw [hswap, hperp ε' hε']
  intro ε hε
  rcases h87 G D hC hrad hO4 β hβ.1 ε hε with rfl | hεD | ⟨δ, hδβ, hδε⟩
  · exact htβ
  · exact hfixD ε hεD
  · exact hfixperp δ hδβ ε (mem_perp_iff.mpr
      (Or.inl (Dalpha_symm hδε (subset_of_mem_blockClass hN hblock hε))))

end CFSG.OddTranspositions.PartThree

end
