module

public import CFSG.LocalAnalysis.StandardType.GGSixBstarOrthFrameD4Frame
public import CFSG.LocalAnalysis.StandardType.GGSixBstarOrthFrameD4Class
public import CFSG.LocalAnalysis.StandardType.GGSixBstarNoOffenderOmega
public import CFSG.LocalAnalysis.StandardType.GGFieldCaseTableBIrred

public section

namespace CFSG.StandardType

namespace OrthD4

open Multiplicative CFSG.StandardType.Triality CFSG.StandardType.D4Rank

section Glue

variable {K : Type} [Field K] [Finite K] [CharP K 2] {G : Type} [Group G] {U : Type} [Group U]

theorem map_ofAdd_pow_three {H : Type} [Group H] (ι₁ : Multiplicative (Fin 4 → ZMod 3) →* H)
    (x : Fin 4 → ZMod 3) : ι₁ (ofAdd x) ^ 3 = 1 := by
  rw [← map_pow, ← ofAdd_nsmul]
  have h : (3 • x : Fin 4 → ZMod 3) = 0 := by
    funext i
    rw [Pi.smul_apply, nsmul_eq_mul, ZMod.natCast_self, zero_mul, Pi.zero_apply]
  rw [h, ofAdd_zero, map_one]

theorem exists_orthFrame_of_spinModel {Bs : Subgroup G} (hBs : CFSG.Assembly.IsElemAbelian 3 Bs)
    (hSC : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ 3 = 1 → g ∈ Bs)
    (h81 : 3 ^ 4 ≤ Nat.card Bs) (ψ : U →* G) (hψ : Function.Injective ψ) (π : U →* Om8 K)
    (hπ : Function.Bijective π) (hC : Subgroup.centralizer (ψ.range : Set G) = ⊥)
    (hdiag : ∀ b ∈ Bs, ∃ g ∈ ψ.range, b * g ∈ Subgroup.centralizer (ψ.range : Set G)) :
    ∃ ι : Multiplicative (Fin 4 → ZMod 3) →* G, Function.Injective ι ∧ ι.range = Bs ∧
      ∀ g ∈ Subgroup.normalizer (ψ.range : Set G), g ∈ Subgroup.normalizer (Bs : Set G) →
        ∀ s s' : Fin 4 → ZMod 3, g⁻¹ * ι (ofAdd s) * g = ι (ofAdd s') →
          ∑ i, s' i ^ 2 = ∑ i, s i ^ 2 := by
  classical
  set πe := MulEquiv.ofBijective π hπ with hπe
  set φ : Om8 K →* G := ψ.comp πe.symm.toMonoidHom with hφ
  have hφinj : Function.Injective φ := hψ.comp πe.symm.injective
  have hφrange : φ.range = ψ.range := by
    ext y
    constructor
    · rintro ⟨X, rfl⟩
      exact ⟨_, rfl⟩
    · rintro ⟨u, rfl⟩
      exact ⟨πe u, by simp [hφ]⟩
  have hBφ : Bs ≤ φ.range := by
    intro b hb
    obtain ⟨g, hg, hbg⟩ := hdiag b hb
    rw [hC, Subgroup.mem_bot] at hbg
    rw [hφrange, eq_inv_of_mul_eq_one_left hbg]
    exact ψ.range.inv_mem hg
  obtain ⟨ι₁, hinj, hrange, hcls⟩ := exists_orthFrame hBs hSC h81 φ hφinj hBφ
  refine ⟨φ.comp ι₁, hinj, hrange, fun g hgN hgB s s' hss' => ?_⟩
  have hgN' : g ∈ Subgroup.normalizer (φ.range : Set G) := by rw [hφrange]; exact hgN
  have hmem : ∀ X : Om8 K, ∃ Y : Om8 K, φ Y = g⁻¹ * φ X * g := by
    intro X
    obtain ⟨Y, hY⟩ := NoOffOm.inv_mul_mul_mem hgN' (MonoidHom.mem_range.mpr ⟨X, rfl⟩)
    exact ⟨Y, hY⟩
  choose α₀ hα₀ using hmem
  have hα₀mul : ∀ X Y, α₀ (X * Y) = α₀ X * α₀ Y := fun X Y => hφinj (by
    rw [hα₀, map_mul, map_mul, hα₀, hα₀]
    group)
  have hα₀inj : Function.Injective α₀ := fun X Y hXY => hφinj (by
    have h1 := hα₀ X
    rw [hXY, hα₀] at h1
    calc φ X = g * (g⁻¹ * φ X * g) * g⁻¹ := by group
      _ = g * (g⁻¹ * φ Y * g) * g⁻¹ := by rw [h1]
      _ = φ Y := by group)
  set α : MulAut (Om8 K) :=
    MulEquiv.ofBijective (MonoidHom.mk' α₀ hα₀mul)
      (Finite.injective_iff_bijective.mp hα₀inj) with hαdef
  have hα : ∀ X, φ (α X) = g⁻¹ * φ X * g := fun X => hα₀ X
  have hF : ∀ x : Fin 4 → ZMod 3, ∃ y : Fin 4 → ZMod 3, ι₁ (ofAdd y) = α (ι₁ (ofAdd x)) := by
    intro x
    have h1 : φ (α (ι₁ (ofAdd x))) ∈ Bs := by
      rw [hα]
      refine NoOffOm.inv_mul_mul_mem hgB ?_
      rw [← hrange]
      exact MonoidHom.mem_range.mpr ⟨ofAdd x, rfl⟩
    rw [← hrange] at h1
    obtain ⟨y, hy⟩ := h1
    exact ⟨toAdd y, hφinj hy⟩
  choose F hFα using hF
  have hFinj : ∀ {x y : Fin 4 → ZMod 3}, ι₁ (ofAdd x) = ι₁ (ofAdd y) → x = y := fun h =>
    ofAdd.injective (hinj (congrArg φ h))
  have hFadd : ∀ x y, F (x + y) = F x + F y := by
    intro x y
    apply hFinj
    rw [ofAdd_add, map_mul, hFα, hFα, ofAdd_add, map_mul, map_mul, hFα]
  have hFQ : ∀ x, ∑ i, F x i ^ 2 = 1 ↔ ∑ i, x i ^ 2 = 1 := by
    intro x
    rw [← hcls, ← hcls, hFα, aut_zero_six_iff α (map_ofAdd_pow_three ι₁ x)]
  have hs' : s' = F s := by
    apply hFinj
    apply hφinj
    rw [hFα, hα]
    exact hss'.symm
  rw [hs']
  exact sum_sq_map_eq F hFadd hFQ s

end Glue

end OrthD4

section Tags

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.RootSystem
  CFSG.Assembly.LowTwoRank CFSG.LieType.Universal.Spin

theorem ggSixBstarOrthFrameOn_D4Three : GGSixBstarOrthFrameOn GGPOmegaPlusD4Three := by
  intro G _ _ p B Bs x L D J t n f ψ hP
  obtain ⟨rfl, rfl, rfl⟩ := hP
  revert ψ
  rw [ggU_POmegaPlus_eq (by norm_num : 3 ≤ 4)]
  intro ψ hctx hC
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hrange, hker⟩ := hctx.2.2.2.2.1
  have hψinj : Function.Injective ψ := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff,
      ← RootCentOmega.center_spinGroup_quadPlus_eq_bot_charTwo (by norm_num : 3 ≤ 4)]
    exact hker
  have hCψ : Subgroup.centralizer (ψ.range : Set G) = ⊥ := by
    rw [hrange]
    exact hC
  have hcfg : GGConfig 3 B Bs x L D J := ⟨hctx.1, hctx.2.1, hctx.2.2.1⟩
  obtain ⟨-, hBs, -, -, h81⟩ := hcfg.tableB_facts
  obtain ⟨ι, hinj, hιr, hQ⟩ := OrthD4.exists_orthFrame_of_spinModel hBs hctx.2.1.2.2.2 h81 ψ
    hψinj (AutOm.spinModelPlus (by norm_num : 3 ≤ 4))
    ⟨AutOm.spinModelPlus_injective _, AutOm.spinModelPlus_surjective _⟩ hCψ
    (fun b hb => PsiDiag.SpinP.exists_mem_centralizer (by norm_num) ψ hker
      (hctx.2.2.2.2.2.2.1.2 b hb))
  refine ⟨ι, hinj, hιr, fun g hgM hgB _ s s' h => hQ g ?_ hgB s s' h⟩
  rw [hrange]
  exact hgM

theorem ggSixBstarNoOffenderOn_D4Three : GGSixBstarNoOffenderOn GGPOmegaPlusD4Three :=
  ggNoOffender_of_orthFrameOn ggSixBstarOrthFrameOn_D4Three

theorem ggSixBstarNoOffenderAt_POmegaPlus : GGSixBstarNoOffenderAt .POmegaPlus :=
  ggSixBstarNoOffenderAt_POmegaPlus_of_d4OrthFrame ggSixBstarOrthFrameOn_D4Three

theorem ggSixBstarNoOffenderRestOm_of_rest (hpNs : GGSixBstarNoOffenderOn GGPSpNonsplit)
    (hF4 : GGSixBstarNoOffenderAt .F4) (hE6 : GGSixBstarNoOffenderAt .E6)
    (hE7 : GGSixBstarNoOffenderAt .E7) (hE8 : GGSixBstarNoOffenderAt .E8)
    (hTwE6 : GGSixBstarNoOffenderAt .twistedE6) : GGSixBstarNoOffenderRestOm :=
  ⟨hpNs, ggSixBstarOrthFrameOn_D4Three, hF4, hE6, hE7, hE8, hTwE6⟩

end Tags

end CFSG.StandardType
