module

public import CFSG.LocalAnalysis.StandardType.ZS.DimThree.Transport
import CFSG.LocalAnalysis.StandardType.ZS.DimThree.HessInv
import CFSG.LocalAnalysis.StandardType.ZS.DimThree.HessLines

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.StandardType.ZS.DimThree

open Matrix Subgroup CFSG.RankThree.PartOne CFSG.RepresentationTheory
open CFSG.RankThree.PartOne.LIT (autGL)
open CFSG.RankThree.SubgroupLists (translate)

variable {p : ℕ} [Fact p.Prime] {U : Type} [AddCommGroup U] [Module (ZMod p) U]

private lemma mul_eq_smul_mul_inv_zh {x g : GL (Fin 3) (ZMod p)} {d : ZMod p}
    (hd : ((g * x * g⁻¹ * x : GL (Fin 3) (ZMod p)) : Matrix (Fin 3) (Fin 3) (ZMod p)) =
      Matrix.scalar (Fin 3) d) :
    (x : Matrix (Fin 3) (Fin 3) (ZMod p)) * (g : Matrix (Fin 3) (Fin 3) (ZMod p)) =
      d • ((g : Matrix (Fin 3) (Fin 3) (ZMod p)) *
        ((x⁻¹ : GL (Fin 3) (ZMod p)) : Matrix (Fin 3) (Fin 3) (ZMod p))) := by
  set s : GL (Fin 3) (ZMod p) := g * x * g⁻¹ * x with hs
  have hmat : (s : Matrix (Fin 3) (Fin 3) (ZMod p)) = d • 1 := by
    simpa only [Matrix.scalar_apply, Matrix.smul_one_eq_diagonal] using hd
  have hcentral : ∀ y : GL (Fin 3) (ZMod p), s * y = y * s := by
    intro y
    apply Units.ext
    show (s : Matrix (Fin 3) (Fin 3) (ZMod p)) * (y : Matrix (Fin 3) (Fin 3) (ZMod p)) =
      (y : Matrix (Fin 3) (Fin 3) (ZMod p)) * (s : Matrix (Fin 3) (Fin 3) (ZMod p))
    rw [hmat, Matrix.smul_mul, Matrix.one_mul, Matrix.mul_smul, Matrix.mul_one]
  have hgs : g * x * g⁻¹ = s * x⁻¹ := by
    rw [hs]
    group
  have h1 : x * g * x * g⁻¹ = s := by
    calc x * g * x * g⁻¹ = x * (g * x * g⁻¹) := by group
      _ = x * (s * x⁻¹) := by rw [hgs]
      _ = s := by rw [← mul_assoc, (hcentral x).symm, mul_assoc, mul_inv_cancel, mul_one]
  have h2 : x * g = s * g * x⁻¹ := by
    calc x * g = (x * g * x) * x⁻¹ := by group
      _ = ((x * g * x * g⁻¹) * g) * x⁻¹ := by group
      _ = (s * g) * x⁻¹ := by rw [h1]
  calc (x : Matrix (Fin 3) (Fin 3) (ZMod p)) * (g : Matrix (Fin 3) (Fin 3) (ZMod p))
      = ((x * g : GL (Fin 3) (ZMod p)) : Matrix (Fin 3) (Fin 3) (ZMod p)) := by
          rw [Units.val_mul]
    _ = ((s * g * x⁻¹ : GL (Fin 3) (ZMod p)) : Matrix (Fin 3) (Fin 3) (ZMod p)) := by rw [h2]
    _ = (s : Matrix (Fin 3) (Fin 3) (ZMod p)) * (g : Matrix (Fin 3) (Fin 3) (ZMod p)) *
        ((x⁻¹ : GL (Fin 3) (ZMod p)) : Matrix (Fin 3) (Fin 3) (ZMod p)) := by
          simp only [Units.val_mul]
    _ = (d • (1 : Matrix (Fin 3) (Fin 3) (ZMod p))) *
        (g : Matrix (Fin 3) (Fin 3) (ZMod p)) *
        ((x⁻¹ : GL (Fin 3) (ZMod p)) : Matrix (Fin 3) (Fin 3) (ZMod p)) := by rw [hmat]
    _ = d • ((g : Matrix (Fin 3) (Fin 3) (ZMod p)) *
        ((x⁻¹ : GL (Fin 3) (ZMod p)) : Matrix (Fin 3) (Fin 3) (ZMod p))) := by
        rw [Matrix.smul_mul, Matrix.one_mul, Matrix.smul_mul]

private lemma inv_mulVec_eq_inv_smul_zh {x : GL (Fin 3) (ZMod p)} {v : Fin 3 → ZMod p}
    {μ : ZMod p} (hv : (x : Matrix (Fin 3) (Fin 3) (ZMod p)) *ᵥ v = μ • v) :
    ((x⁻¹ : GL (Fin 3) (ZMod p)) : Matrix (Fin 3) (Fin 3) (ZMod p)) *ᵥ v = μ⁻¹ • v := by
  have hcancel : ((x⁻¹ : GL (Fin 3) (ZMod p)) : Matrix (Fin 3) (Fin 3) (ZMod p)) *ᵥ
      ((x : GL (Fin 3) (ZMod p)) : Matrix (Fin 3) (Fin 3) (ZMod p)) *ᵥ v = v := by
    rw [Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one,
      Matrix.one_mulVec]
  have h1 : v = μ • (((x⁻¹ : GL (Fin 3) (ZMod p)) :
      Matrix (Fin 3) (Fin 3) (ZMod p)) *ᵥ v) := by
    conv_lhs => rw [← hcancel]
    rw [hv, Matrix.mulVec_smul]
  rcases eq_or_ne μ 0 with rfl | hμ
  · have hv0 : v = 0 := by rw [h1, zero_smul]
    rw [hv0]
    simp
  · have h2 : μ⁻¹ • v = ((x⁻¹ : GL (Fin 3) (ZMod p)) :
        Matrix (Fin 3) (Fin 3) (ZMod p)) *ᵥ v := by
      conv_lhs => rw [h1]
      rw [inv_smul_smul₀ hμ]
    exact h2.symm

private lemma translate_eigenspace_le_of_conj_mul_eq_scalar_zh {x g : GL (Fin 3) (ZMod p)}
    {d : ZMod p}
    (hd : ((g * x * g⁻¹ * x : GL (Fin 3) (ZMod p)) : Matrix (Fin 3) (Fin 3) (ZMod p)) =
      Matrix.scalar (Fin 3) d) (μ : ZMod p) :
    translate g (Module.End.eigenspace (Matrix.toLin' (x : Matrix (Fin 3) (Fin 3) (ZMod p))) μ) ≤
      Module.End.eigenspace (Matrix.toLin' (x : Matrix (Fin 3) (Fin 3) (ZMod p))) (d * μ⁻¹) := by
  intro u hu
  rw [CFSG.RankThree.SubgroupLists.mem_translate] at hu
  obtain ⟨v, hv, rfl⟩ := hu
  rw [Module.End.mem_eigenspace_iff] at hv ⊢
  rw [Matrix.toLin'_apply] at hv ⊢
  have hxg := mul_eq_smul_mul_inv_zh hd
  have hxinv := inv_mulVec_eq_inv_smul_zh hv
  calc (x : Matrix (Fin 3) (Fin 3) (ZMod p)) *ᵥ
      ((g : Matrix (Fin 3) (Fin 3) (ZMod p)) *ᵥ v)
      = ((x : Matrix (Fin 3) (Fin 3) (ZMod p)) * (g : Matrix (Fin 3) (Fin 3) (ZMod p))) *ᵥ v := by
          rw [Matrix.mulVec_mulVec]
    _ = (d • ((g : Matrix (Fin 3) (Fin 3) (ZMod p)) *
          ((x⁻¹ : GL (Fin 3) (ZMod p)) : Matrix (Fin 3) (Fin 3) (ZMod p)))) *ᵥ v := by
          rw [hxg]
    _ = d • (((g : Matrix (Fin 3) (Fin 3) (ZMod p)) *
          ((x⁻¹ : GL (Fin 3) (ZMod p)) : Matrix (Fin 3) (Fin 3) (ZMod p))) *ᵥ v) := by
          rw [Matrix.smul_mulVec]
    _ = d • ((g : Matrix (Fin 3) (Fin 3) (ZMod p)) *ᵥ
          (((x⁻¹ : GL (Fin 3) (ZMod p)) : Matrix (Fin 3) (Fin 3) (ZMod p)) *ᵥ v)) := by
          rw [Matrix.mulVec_mulVec]
    _ = d • ((g : Matrix (Fin 3) (Fin 3) (ZMod p)) *ᵥ (μ⁻¹ • v)) := by rw [hxinv]
    _ = d • (μ⁻¹ • ((g : Matrix (Fin 3) (Fin 3) (ZMod p)) *ᵥ v)) := by
          rw [Matrix.mulVec_smul]
    _ = (d * μ⁻¹) • ((g : Matrix (Fin 3) (Fin 3) (ZMod p)) *ᵥ v) := by rw [smul_smul]

private lemma exists_eq_of_translate_le_zh {x g : GL (Fin 3) (ZMod p)} {μ : Fin 3 → ZMod p}
    (h1 : ∀ i, Module.finrank (ZMod p)
      (Module.End.eigenspace (Matrix.toLin' (x : Matrix (Fin 3) (Fin 3) (ZMod p))) (μ i)) = 1)
    (hL : DirectSum.IsInternal (fun i =>
      Module.End.eigenspace (Matrix.toLin' (x : Matrix (Fin 3) (Fin 3) (ZMod p))) (μ i)))
    {i : Fin 3} {ν : ZMod p}
    (hle : translate g
        (Module.End.eigenspace (Matrix.toLin' (x : Matrix (Fin 3) (Fin 3) (ZMod p))) (μ i)) ≤
      Module.End.eigenspace (Matrix.toLin' (x : Matrix (Fin 3) (Fin 3) (ZMod p))) ν) :
    ∃ j, translate g
        (Module.End.eigenspace (Matrix.toLin' (x : Matrix (Fin 3) (Fin 3) (ZMod p))) (μ i)) =
      Module.End.eigenspace (Matrix.toLin' (x : Matrix (Fin 3) (Fin 3) (ZMod p))) (μ j) := by
  have hfin : Module.finrank (ZMod p) (translate g
      (Module.End.eigenspace (Matrix.toLin' (x : Matrix (Fin 3) (Fin 3) (ZMod p))) (μ i))) = 1 := by
    rw [CFSG.RankThree.SubgroupLists.finrank_translate, h1 i]
  have hne : translate g
      (Module.End.eigenspace (Matrix.toLin' (x : Matrix (Fin 3) (Fin 3) (ZMod p))) (μ i)) ≠ ⊥ := by
    intro hb
    have h0 : Module.finrank (ZMod p) (translate g
        (Module.End.eigenspace (Matrix.toLin' (x : Matrix (Fin 3) (Fin 3) (ZMod p)))
          (μ i))) = 0 := by
      rw [hb, finrank_bot]
    exact one_ne_zero (hfin.symm.trans h0)
  by_contra hcon
  have hcon' : ∀ j, translate g
      (Module.End.eigenspace (Matrix.toLin' (x : Matrix (Fin 3) (Fin 3) (ZMod p))) (μ i)) ≠
        Module.End.eigenspace (Matrix.toLin' (x : Matrix (Fin 3) (Fin 3) (ZMod p))) (μ j) :=
    fun j heq => hcon ⟨j, heq⟩
  have hν : ∀ j, ν ≠ μ j := by
    intro j hjeq
    apply hcon' j
    subst hjeq
    exact Submodule.eq_of_le_of_finrank_eq hle (hfin.trans (h1 j).symm)
  have hmem : ν ∉ Set.range μ := by
    rintro ⟨j, hj⟩
    exact hν j hj.symm
  have hdisj := (Module.End.eigenspaces_iSupIndep
    (Matrix.toLin' (x : Matrix (Fin 3) (Fin 3) (ZMod p)))).disjoint_biSup
    (x := ν) (y := Set.range μ) hmem
  rw [iSup_range] at hdisj
  have hbot : Module.End.eigenspace
      (Matrix.toLin' (x : Matrix (Fin 3) (Fin 3) (ZMod p))) ν = ⊥ := by
    rwa [hL.submodule_iSup_eq_top, disjoint_top] at hdisj
  exact hne (le_bot_iff.mp (hbot ▸ hle))

private lemma translate_closure_zh {L : Fin 3 → Submodule (ZMod p) (Fin 3 → ZMod p)}
    {S : Set (GL (Fin 3) (ZMod p))} (hS2 : ∀ t ∈ S, t * t = 1)
    (hSL : ∀ t ∈ S, ∀ i, ∃ j, translate t (L i) = L j) :
    ∀ g ∈ Subgroup.closure S, ∀ i, ∃ j, translate g (L i) = L j := by
  intro g hg
  refine Subgroup.closure_induction'' (p :=
    fun g _ => ∀ i, ∃ j, translate g (L i) = L j) (fun t ht => hSL t ht) (fun t ht => ?_)
    ?_ ?_ hg
  · rw [inv_eq_of_mul_eq_one_right (hS2 t ht)]
    exact hSL t ht
  · intro i
    exact ⟨i, CFSG.RankThree.SubgroupLists.translate_one (L i)⟩
  · intro x y _ _ hpx hpy i
    obtain ⟨j, hj⟩ := hpy i
    obtain ⟨k, hk⟩ := hpx j
    exact ⟨k, by rw [CFSG.RankThree.SubgroupLists.translate_mul, hj, hk]⟩

theorem isImprimitiveOnV_of_extraspecial (hp : p ≠ 2) (e : U ≃ₗ[ZMod p] (Fin 3 → ZMod p))
    {A : Subgroup (U ≃ₗ[ZMod p] U)} (hR : ReflGen p A) {H : Subgroup (GL (Fin 3) (ZMod p))}
    (hn : ∀ g ∈ A.map (autGL e).toMonoidHom, ∀ x ∈ H, g * x * g⁻¹ ∈ H)
    (hirr : IsIrreducibleMatrixRep H.subtype) (h27 : Nat.card H = 27)
    (hE : IsExtraspecialPGroup 3 H) (_hp3 : p % 3 = 1) :
    CFSG.Quasithin.SimsG4.IsImprimitiveOnV A := by
  obtain ⟨x, hx3, hxZ⟩ := exists_pow_three_eq_one_not_mem_center h27 hE
  obtain ⟨y, hxy⟩ : ∃ y : H, x * y ≠ y * x := by
    by_contra h
    push Not at h
    exact hxZ (mem_center_iff.mpr fun y => (h y).symm)
  obtain ⟨c, hc1, hc3, hyx⟩ := exists_inv_conj_eq_smul_of_extraspecial hirr hE x.2 y.2
    (fun h => hxy (Subtype.ext h))
  obtain ⟨l, h1, hL⟩ := exists_eigenlines_of_inv_conj_eq_smul hc1 hc3
    (by simpa using congrArg Subtype.val hx3) hyx
  refine isImprimitiveOnV_of_lines e hL h1 fun g hg => ?_
  rw [map_autGL_eq_closure hp e hR] at hg
  refine translate_closure_zh (fun t ht => ht.2.sq) (fun t ht i => ?_) g hg
  obtain ⟨d, hd⟩ := exists_scalar_conj_mul_of_extraspecial hp hirr h27 hE ht.2 (hn t ht.1) x.2
  exact exists_eq_of_translate_le_zh h1 hL
    (translate_eigenspace_le_of_conj_mul_eq_scalar_zh hd _)

end CFSG.StandardType.ZS.DimThree
