module

public import CFSG.LocalAnalysis.StandardType.GGQTwoDRMFiveLin
public import CFSG.LocalAnalysis.StandardType.GGSimplyLacedWeyl

import CFSG.LocalAnalysis.StandardType.ZS.ClassReflOrder
import CFSG.LocalAnalysis.StandardType.ZS.ClassReflClosure
import CFSG.LocalAnalysis.StandardType.ZS.DimThree.OrthRefl
import CFSG.LocalAnalysis.StandardType.ZS.Adapter
import CFSG.LocalAnalysis.StandardType.GGFLWReflForm

public section

namespace CFSG.StandardType.QTwo

open CFSG.StandardType

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

noncomputable section

private lemma norm_eq_of_isRefl_of_neg {n : ℕ} {Q : QuadraticForm (ZMod 3) (DVec n)}
    {r : DVec n ≃ₗ[ZMod 3] DVec n} (hR : ZS.IsRefl 3 r)
    {a b : DVec n} (ha : a ≠ 0) (hb : b ≠ 0)
    (hra : r a = -a) (hrb : r b = -b) :
    Q a = Q b := by
  obtain ⟨c₀, β, hc₀, hβ, hr⟩ := ggFLW_isRefl_form (p := 3) (by norm_num) hR
  have h2 : (2 : ZMod 3) * 2 = 1 := by decide
  have h1a : (2 : ZMod 3) • a = β a • c₀ := by
    have h := hr a
    rw [hra] at h
    calc (2 : ZMod 3) • a = a + a := by rw [two_smul]
      _ = a - (-a) := by rw [sub_neg_eq_add]
      _ = a - (a - β a • c₀) := by rw [h]
      _ = β a • c₀ := by abel
  have h2a : a = (2 * β a) • c₀ := by
    calc a = (1 : ZMod 3) • a := (one_smul _ _).symm
      _ = ((2 * 2 : ZMod 3)) • a := by simp [h2]
      _ = (2 : ZMod 3) • ((2 : ZMod 3) • a) := by module
      _ = (2 : ZMod 3) • (β a • c₀) := by rw [h1a]
      _ = (2 * β a) • c₀ := by rw [← smul_smul]
  have h1b : (2 : ZMod 3) • b = β b • c₀ := by
    have h := hr b
    rw [hrb] at h
    calc (2 : ZMod 3) • b = b + b := by rw [two_smul]
      _ = b - (-b) := by rw [sub_neg_eq_add]
      _ = b - (b - β b • c₀) := by rw [h]
      _ = β b • c₀ := by abel
  have h2b : b = (2 * β b) • c₀ := by
    calc b = (1 : ZMod 3) • b := (one_smul _ _).symm
      _ = ((2 * 2 : ZMod 3)) • b := by simp [h2]
      _ = (2 : ZMod 3) • ((2 : ZMod 3) • b) := by module
      _ = (2 : ZMod 3) • (β b • c₀) := by rw [h1b]
      _ = (2 * β b) • c₀ := by rw [← smul_smul]
  have hsq : ∀ x : ZMod 3, x ≠ 0 → x * x = 1 := by decide
  have h_a_ne : 2 * β a ≠ 0 := by
    intro h0
    rw [h0, zero_smul] at h2a
    exact ha h2a
  have h_b_ne : 2 * β b ≠ 0 := by
    intro h0
    rw [h0, zero_smul] at h2b
    exact hb h2b
  rw [h2a, h2b, QuadraticMap.map_smul, QuadraticMap.map_smul]
  rw [hsq _ h_a_ne, hsq _ h_b_ne]

theorem le_dNormTwo_of_weylOfType {n : ℕ} {ι : Type} {M : CoxeterMatrix ι}
    (hM : GGSimplyLacedConnected M) {W : Subgroup (DVec n ≃ₗ[ZMod 3] DVec n)}
    (hiso : ∀ g ∈ W, ∀ v w, dDot n (g v) (g w) = dDot n v w)
    (f : M.Group ≃* ↥W) (hf : ∀ i, GGLinRefl (f (M.simple i) : DVec n ≃ₗ[ZMod 3] DVec n))
    {t : DVec n ≃ₗ[ZMod 3] DVec n} (ht : t ∈ W) (htr : GGLinRefl t) {c : DVec n}
    (hc : t c = -c) (hcn : dDot n c c = 2) :
    (∀ i, (f (M.simple i) : DVec n ≃ₗ[ZMod 3] DVec n) ∈ ZS.ClassRefl 3 (dQuadTwo n) 1) ∧
      W ≤ dNormTwo n := by
  let Q := dQuadTwo n
  have hQ : (QuadraticMap.polarBilin Q).Nondegenerate := dQuadTwo_polar_nondegenerate n
  have hiso_Q : ∀ g ∈ W, ZS.IsIsom 3 Q g := by
    intro g hg v
    rw [dQuadTwo_eq_two_dDot, dQuadTwo_eq_two_dDot, hiso g hg v v]
  have h_refl_s : ∀ i, ZS.IsRefl 3 (f (M.simple i) : DVec n ≃ₗ[ZMod 3] DVec n) := fun i =>
    (ZS.isRefl_iff_ggLinRefl _).mpr (hf i)
  have h_refl_t : ZS.IsRefl 3 t := (ZS.isRefl_iff_ggLinRefl _).mpr htr
  have hc_ne : c ≠ 0 := by
    intro h0
    rw [h0] at hcn
    simp at hcn
    exact (by decide : (0 : ZMod 3) ≠ 2) hcn
  have hcQ : Q c = 1 := by
    rw [dQuadTwo_eq_two_dDot, hcn]
    decide
  have h_t_class : t ∈ ZS.ClassRefl 3 Q 1 := ⟨h_refl_t, hiso_Q t ht, c, hcQ, hc⟩
  have hι : Nonempty ι := by
    by_contra h
    have hbot : Subgroup.closure (Set.range M.simple) = ⊥ := by
      rw [Subgroup.closure_eq_bot_iff]
      rintro _ ⟨i, _⟩
      exact absurd ⟨i⟩ h
    have htop : Subgroup.closure (Set.range M.simple) = ⊤ :=
      PresentedGroup.closure_range_of M.relationsSet
    have hWbot : W = ⊥ := by
      rw [Subgroup.eq_bot_iff_forall]
      intro g hg
      obtain ⟨w, hw⟩ := f.surjective ⟨g, hg⟩
      have hw1 : w = 1 := by
        have : w ∈ (⊥ : Subgroup M.Group) := by
          rw [← htop.symm.trans hbot]
          exact Subgroup.mem_top w
        simpa using this
      have hw_val : (f w : DVec n ≃ₗ[ZMod 3] DVec n) = g := by
        have := congrArg (fun x : ↥W => (x : DVec n ≃ₗ[ZMod 3] DVec n)) hw
        simpa using this
      rw [← hw_val, hw1, map_one]
      rfl
    have htbot : t = 1 := by
      have : t ∈ (⊥ : Subgroup (DVec n ≃ₗ[ZMod 3] DVec n)) := by rw [← hWbot]; exact ht
      simpa using this
    have hc_eq : c = -c := by
      rw [← hc, htbot]
      simp
    have h2c : (2 : ZMod 3) • c = 0 := by
      rw [two_smul]
      exact add_eq_zero_iff_eq_neg.mpr hc_eq
    have h2 : (2 : ZMod 3) ≠ 0 := by decide
    exact hc_ne ((smul_eq_zero.mp h2c).resolve_left h2)
  let i₀ := Classical.choice hι
  obtain ⟨a₀, ha₀, hra₀⟩ :=
    ZS.DimThree.exists_root_of_isRefl_isIsom (by norm_num) hQ (h_refl_s i₀)
      (hiso_Q (f (M.simple i₀)) (f (M.simple i₀)).2)
  let κ := Q a₀
  have hκ : κ ≠ 0 := ha₀
  have h_s_i₀_class : (f (M.simple i₀) : DVec n ≃ₗ[ZMod 3] DVec n) ∈ ZS.ClassRefl 3 Q κ :=
    ⟨h_refl_s i₀, hiso_Q (f (M.simple i₀)) (f (M.simple i₀)).2, a₀, rfl, hra₀⟩
  have h_class_i : ∀ i, (f (M.simple i) : DVec n ≃ₗ[ZMod 3] DVec n) ∈ ZS.ClassRefl 3 Q κ := by
    intro i
    obtain ⟨w, hw⟩ := ggSimplyLaced_simple_conj hM i₀ i
    have h_eq :
        (f (M.simple i) : DVec n ≃ₗ[ZMod 3] DVec n) =
          (f w : DVec n ≃ₗ[ZMod 3] DVec n) *
            (f (M.simple i₀) : DVec n ≃ₗ[ZMod 3] DVec n) *
              (f w : DVec n ≃ₗ[ZMod 3] DVec n)⁻¹ := by
      rw [hw]
      simp [map_mul, map_inv]
    rw [h_eq]
    exact ZS.conj_mem_classRefl (hiso_Q (f w) (f w).2) h_s_i₀_class
  have hW_le_κ : W ≤ Subgroup.closure (ZS.ClassRefl 3 Q κ) := by
    intro g hg
    obtain ⟨w, hw⟩ := f.surjective ⟨g, hg⟩
    have hw' : w ∈ Subgroup.closure (Set.range M.simple) := by
      rw [← CoxeterMatrix.toCoxeterSystem_simple]
      rw [M.toCoxeterSystem.subgroup_closure_range_simple]
      exact Subgroup.mem_top w
    have key : ∀ u ∈ Subgroup.closure (Set.range M.simple),
        (f u : DVec n ≃ₗ[ZMod 3] DVec n) ∈
          Subgroup.closure (ZS.ClassRefl 3 Q κ) := by
      intro u hu
      induction hu using Subgroup.closure_induction with
      | mem x hx =>
        obtain ⟨i, rfl⟩ := hx
        exact Subgroup.subset_closure (h_class_i i)
      | one => simp
      | mul x y hx hy hx' hy' =>
        simpa [map_mul] using Subgroup.mul_mem _ hx' hy'
      | inv x hx hx' => simpa [map_inv] using Subgroup.inv_mem _ hx'
    have hw'' := key w hw'
    rw [hw] at hw''
    simpa using hw''
  have hκ_eq : κ = 1 := by
    have h_t_class_κ : t ∈ ZS.ClassRefl 3 Q κ :=
      ZS.mem_classRefl_of_isRefl_mem_closure (by norm_num) hQ hκ (hW_le_κ ht) h_refl_t
    obtain ⟨a, hQa, hta⟩ := h_t_class_κ.2.2
    obtain ⟨b, hQb, htb⟩ := h_t_class.2.2
    have ha : a ≠ 0 := by
      intro h0
      rw [h0, QuadraticMap.map_zero] at hQa
      exact hκ hQa.symm
    have hb : b ≠ 0 := by
      intro h0
      rw [h0, QuadraticMap.map_zero] at hQb
      exact (by decide : (1 : ZMod 3) ≠ 0) hQb.symm
    have h_norm := norm_eq_of_isRefl_of_neg (Q := Q) h_refl_t ha hb hta htb
    rw [hQa, hQb] at h_norm
    exact h_norm
  constructor
  · intro i
    rw [hκ_eq] at h_class_i
    simpa [Q] using h_class_i i
  · rw [hκ_eq] at hW_le_κ
    simpa [dNormTwo, Q] using hW_le_κ

end

end CFSG.StandardType.QTwo

end
