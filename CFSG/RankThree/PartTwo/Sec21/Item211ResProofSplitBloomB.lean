module

public import CFSG.RankThree.PartTwo.Sec21.Item211ResProofSplitNine
public import CFSG.RankThree.PartTwo.Toolkit.Split
import CFSG.RankThree.SubgroupLists.DicksonGL2
public import CFSG.Assembly.QuasithinDefs
public import CFSG.Foundations
public import CFSG.GroupTheory.BaerSuzuki
public import CFSG.GroupTheory.HallHigmanPiCore
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProper
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProperGroups
public import CFSG.LocalAnalysis.SectionRank.PRank
public import CFSG.LocalAnalysis.SectionRank.SQT
public import CFSG.RankThree.PartTwo.NotationBlocks
public import CFSG.RankThree.PartTwo.Sec7.ThreeTranspositions

public section

namespace CFSG.RankThree.PartTwo.Sec21.Item2130SplitProof

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo
open scoped Matrix

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

local notation "SL33" => Matrix.SpecialLinearGroup (Fin 3) (ZMod 3)

theorem slAB_cube : Toolkit.slA ^ 3 = 1 ∧ Toolkit.slB ^ 3 = 1 := by
  decide

theorem slAB_fix : ∀ v : Fin 3 → ZMod 3,
    ((Toolkit.slA : SL33) : Matrix (Fin 3) (Fin 3) (ZMod 3)) *ᵥ v = v →
      ((Toolkit.slB : SL33) : Matrix (Fin 3) (Fin 3) (ZMod 3)) *ᵥ v = v → v = 0 := by
  decide +kernel

variable {G : Type} [Group G] {A B N : Subgroup G}

@[expose] def bSub (B : Subgroup G) (g : Multiplicative (Fin 4 → ZMod 3) ≃* A) :
    Submodule (ZMod 3) (Fin 4 → ZMod 3) :=
  AddSubgroup.toZModSubmodule 3
    { carrier := {d | ((g (Multiplicative.ofAdd d) : A) : G) ∈ B}
      add_mem' := by
        intro d e hd he
        simp only [Set.mem_ofPred_eq, ofAdd_add, map_mul, Subgroup.coe_mul] at hd he ⊢
        exact B.mul_mem hd he
      zero_mem' := by
        simp only [Set.mem_ofPred_eq, ofAdd_zero, map_one, Subgroup.coe_one]
        exact B.one_mem
      neg_mem' := by
        intro d hd
        simp only [Set.mem_ofPred_eq, ofAdd_neg, map_inv, Subgroup.coe_inv] at hd ⊢
        exact B.inv_mem hd }

theorem mem_bSub {B : Subgroup G} (g : Multiplicative (Fin 4 → ZMod 3) ≃* A)
    (d : Fin 4 → ZMod 3) : d ∈ bSub B g ↔ ((g (Multiplicative.ofAdd d) : A) : G) ∈ B := by
  rw [bSub, AddSubgroup.mem_toZModSubmodule]
  rfl

theorem trivQ_of_conj_eq {r s : G} (hrs : ∀ a ∈ A, r * a * r⁻¹ = s * a * s⁻¹)
    (hs : TrivQ A B s) : TrivQ A B r := fun a ha => by
  rw [hrs a ha]
  exact hs a ha

theorem SplitHyp.concl_of_statedSL [Finite G] (h : SplitHyp A B N)
    (f : Multiplicative (Fin 3 → ZMod 3) ≃* B)
    (hfB : ∀ w ∈ N, (∀ b ∈ B, w * b * w⁻¹ = b) → ∀ a ∈ A, w * a * w⁻¹ = a)
    (hA81 : Nat.card A = 3 ^ 4)
    (hSL : CFSG.Assembly.LowTwoRank.StatedSL 3 (ZMod 3) ≤ M1 N f) : SplitConcl A B N := by
  obtain ⟨g⟩ := Sec12.exists_coords h.elem hA81
  have hlift : ∀ y : SL33, ∃ n, ∃ hn : n ∈ N,
      matB f (h.nb hn) = Matrix.SpecialLinearGroup.toGL y := by
    intro y
    refine h.exists_of_mem_M1 f (hSL ?_)
    rw [CFSG.RankThree.SubgroupLists.mem_statedSL_iff,
      Matrix.SpecialLinearGroup.coe_GL_coe_matrix]
    exact y.2
  choose L hLN hLm using hlift
  have hsame : ∀ {r s : G} (hr : r ∈ N) (hs : s ∈ N), matB f (h.nb hr) = matB f (h.nb hs) →
      ∀ a ∈ A, r * a * r⁻¹ = s * a * s⁻¹ := fun hr hs he => h.conj_eq_of_matB_eq f hfB hr hs he
  have hLmul : ∀ y₁ y₂ : SL33, ∀ a ∈ A, L (y₁ * y₂) * a * (L (y₁ * y₂))⁻¹ =
      (L y₁ * L y₂) * a * (L y₁ * L y₂)⁻¹ := by
    intro y₁ y₂
    refine hsame (hLN _) (N.mul_mem (hLN y₁) (hLN y₂)) ?_
    rw [hLm, map_mul,
      show h.nb (N.mul_mem (hLN y₁) (hLN y₂)) = h.nb (hLN y₁) * h.nb (hLN y₂) from rfl,
      map_mul, hLm, hLm]
  let σ : SL33 →* MulAut A := MonoidHom.mk'
    (fun y => A.normalizerMonoidHom ⟨L y, h.normA (hLN y)⟩) (by
      intro y₁ y₂
      rw [← map_mul]
      refine MulEquiv.ext fun a => Subtype.ext ?_
      exact hLmul y₁ y₂ a a.2)
  have hσ : ∀ y (a : A), ((σ y a : A) : G) = L y * a * (L y)⁻¹ := fun y a => rfl
  let ρ : Representation (ZMod 3) SL33 (Fin 4 → ZMod 3) :=
    LinearEquiv.automorphismGroup.toLinearMapMonoidHom.comp ((Sec12.coordHom g).comp σ)
  have hρ : ∀ y d, ((g (Multiplicative.ofAdd (ρ y d)) : A) : G) =
      L y * (g (Multiplicative.ofAdd d) : G) * (L y)⁻¹ := by
    intro y d
    change ((g (Multiplicative.ofAdd (Sec12.coordHom g (σ y) d)) : A) : G) = _
    rw [Sec12.coordHom_apply, ofAdd_toAdd, MulEquiv.apply_symm_apply, hσ]
  set W := bSub B g with hW
  have hWinv : Toolkit.IsYSubmodule ρ W := by
    intro y w hw
    rw [mem_bSub] at hw ⊢
    rw [hρ]
    exact h.conjB (hLN y) hw
  let Fa : (Fin 3 → ZMod 3) →+ (Fin 4 → ZMod 3) :=
    { toFun := fun x => Multiplicative.toAdd (g.symm ⟨eltB f x, h.le (eltB_mem f x)⟩)
      map_zero' := by
        have : (⟨eltB f 0, h.le (eltB_mem f 0)⟩ : A) = 1 := Subtype.ext (eltB_zero f)
        rw [this, map_one, toAdd_one]
      map_add' := by
        intro x y
        have : (⟨eltB f (x + y), h.le (eltB_mem f (x + y))⟩ : A) =
            ⟨eltB f x, h.le (eltB_mem f x)⟩ * ⟨eltB f y, h.le (eltB_mem f y)⟩ :=
          Subtype.ext (by simp [eltB])
        rw [this, map_mul, toAdd_mul] }
  let F : (Fin 3 → ZMod 3) →ₗ[ZMod 3] (Fin 4 → ZMod 3) := Fa.toZModLinearMap 3
  have hFg : ∀ x, ((g (Multiplicative.ofAdd (F x)) : A) : G) = eltB f x := by
    intro x
    change ((g (Multiplicative.ofAdd (Multiplicative.toAdd
      (g.symm ⟨eltB f x, h.le (eltB_mem f x)⟩))) : A) : G) = _
    rw [ofAdd_toAdd, MulEquiv.apply_symm_apply]
  have hFinj : Function.Injective F := by
    intro x y hxy
    apply eltB_injective f
    rw [← hFg x, ← hFg y, hxy]
  have hFrange : LinearMap.range F = W := by
    ext d
    rw [mem_bSub]
    constructor
    · rintro ⟨x, rfl⟩
      rw [hFg]
      exact eltB_mem f x
    · intro hd
      obtain ⟨x, hx⟩ := exists_eltB f hd
      refine ⟨x, ?_⟩
      have h1 : ((g (Multiplicative.ofAdd (F x)) : A) : G) = (g (Multiplicative.ofAdd d) : G) := by
        rw [hFg, hx]
      exact Multiplicative.ofAdd.injective (g.injective (Subtype.ext h1))
  have hiso : Toolkit.SubmoduleIso ρ W (Toolkit.natRepVia (MulEquiv.refl SL33).toMonoidHom) := by
    refine ⟨F, hFinj, hFrange, fun y x => ?_⟩
    rw [Toolkit.natRepVia_apply]
    apply Multiplicative.ofAdd.injective
    apply g.injective
    apply Subtype.ext
    rw [hρ, hFg, hFg, ← eltB_matB f (h.nb (hLN y)) x, hLm]
    rfl
  have hrank : Module.finrank (ZMod 3) ((Fin 4 → ZMod 3) ⧸ W) = 1 := by
    have h1 := Submodule.finrank_quotient_add_finrank W
    rw [← hFrange, LinearMap.finrank_range_of_inj hFinj, Module.finrank_fin_fun,
      Module.finrank_fin_fun] at h1
    rw [← hFrange]
    omega
  have hK : ∀ y : SL33, TrivQ A B (L y) := by
    let K : Subgroup SL33 :=
      { carrier := {y | TrivQ A B (L y)}
        mul_mem' := by
          intro y₁ y₂ h₁ h₂
          exact trivQ_of_conj_eq (hLmul y₁ y₂) (h.trivQ_mul (hLN y₂) h₁ h₂)
        one_mem' := by
          refine trivQ_of_conj_eq (s := 1) (hsame (hLN 1) N.one_mem ?_) (fun a ha => by simp)
          rw [hLm, map_one, show h.nb N.one_mem = 1 from rfl, map_one]
        inv_mem' := by
          intro y hy
          refine trivQ_of_conj_eq (hsame (hLN y⁻¹) (N.inv_mem (hLN y)) ?_)
            (h.trivQ_inv (hLN y) hy)
          rw [hLm, map_inv, show h.nb (N.inv_mem (hLN y)) = (h.nb (hLN y))⁻¹ from rfl, map_inv,
            hLm] }
    have hA : Toolkit.slA ∈ K := h.trivQ_of_matB_pow f hfB (hLN _) (j := 1) (by
      rw [hLm, ← map_pow, slAB_cube.1, map_one])
    have hB : Toolkit.slB ∈ K := h.trivQ_of_matB_pow f hfB (hLN _) (j := 1) (by
      rw [hLm, ← map_pow, slAB_cube.2, map_one])
    have hle : Subgroup.closure {y | y ∈ [Toolkit.slA, Toolkit.slB]} ≤ K := by
      rw [Subgroup.closure_le]
      intro y hy
      simp only [List.mem_cons, List.not_mem_nil, or_false, Set.mem_ofPred_eq] at hy
      rcases hy with rfl | rfl
      · exact hA
      · exact hB
    rw [Toolkit.closure_slA_slB] at hle
    intro y
    exact hle (Subgroup.mem_top y)
  have htriv : ∀ (y : SL33) (d : Fin 4 → ZMod 3), ρ y d - d ∈ W := by
    intro y d
    rw [mem_bSub, sub_eq_add_neg, ofAdd_add, ofAdd_neg, map_mul, map_inv, Subgroup.coe_mul,
      Subgroup.coe_inv, hρ]
    exact hK y _ (g (Multiplicative.ofAdd d)).2
  obtain ⟨W', hW'inv, hWW'⟩ := Toolkit.sl33Splitting SL33 (MulEquiv.refl SL33)
    (Fin 4 → ZMod 3) ρ W hWinv (Or.inl ⟨Or.inl hiso, hrank, htriv⟩)
  have hW'0 : W' ≠ ⊥ := by
    intro h0
    rw [h0] at hWW'
    have hWt : W = ⊤ := by
      have := hWW'.sup_eq_top
      rwa [sup_bot_eq] at this
    have h1 : Module.finrank (ZMod 3) ((Fin 4 → ZMod 3) ⧸ W) = 0 := by
      rw [hWt]
      exact Module.finrank_zero_of_subsingleton
    omega
  obtain ⟨d, hdW', hd0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hW'0
  have hfixd : ∀ y : SL33, ρ y d = d := by
    intro y
    have h1 : ρ y d - d ∈ W ⊓ W' := ⟨htriv y d, W'.sub_mem (hW'inv y d hdW') hdW'⟩
    rw [hWW'.inf_eq_bot, Submodule.mem_bot, sub_eq_zero] at h1
    exact h1
  set c : G := (g (Multiplicative.ofAdd d) : G) with hc
  have hcA : c ∈ A := (g (Multiplicative.ofAdd d)).2
  have hcB : c ∉ B := by
    intro hcB
    have h1 : d ∈ W ⊓ W' := ⟨(mem_bSub g d).mpr hcB, hdW'⟩
    rw [hWW'.inf_eq_bot, Submodule.mem_bot] at h1
    exact hd0 h1
  refine h.concl_of_matSet f (CFSG.Assembly.LowTwoRank.StatedSL 3 (ZMod 3) : Set _) ?_ ?_ hcA hcB
    ?_
  · intro m hm y hy
    rw [SetLike.mem_coe, CFSG.RankThree.SubgroupLists.mem_statedSL_iff] at hy ⊢
    rw [Units.val_mul, Units.val_mul, Matrix.det_mul, Matrix.det_mul, hy, mul_one,
      ← Matrix.det_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.det_one]
  · intro v hv
    have hmem : ∀ y : SL33, matB f (h.nb (hLN y)) ∈
        (CFSG.Assembly.LowTwoRank.StatedSL 3 (ZMod 3) : Set (GL (Fin 3) (ZMod 3))) := by
      intro y
      rw [hLm, SetLike.mem_coe, CFSG.RankThree.SubgroupLists.mem_statedSL_iff,
        Matrix.SpecialLinearGroup.coe_GL_coe_matrix]
      exact y.2
    have h1 := hv _ (hLN Toolkit.slA) (hmem _)
    have h2 := hv _ (hLN Toolkit.slB) (hmem _)
    rw [hLm, Matrix.SpecialLinearGroup.coe_GL_coe_matrix] at h1 h2
    exact slAB_fix v h1 h2
  · intro r hr hrY
    rw [SetLike.mem_coe, CFSG.RankThree.SubgroupLists.mem_statedSL_iff] at hrY
    set y : SL33 := ⟨(matB f (h.nb hr) : Matrix (Fin 3) (Fin 3) (ZMod 3)), hrY⟩ with hy
    have he : matB f (h.nb hr) = matB f (h.nb (hLN y)) := by
      rw [hLm]
      exact Units.ext rfl
    rw [hsame hr (hLN y) he c hcA, hc, ← hρ, hfixd]

end CFSG.RankThree.PartTwo.Sec21.Item2130SplitProof
