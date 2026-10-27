module

public import Mathlib.LinearAlgebra.Eigenspace.Basic
public import Mathlib.LinearAlgebra.Dimension.Finite
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic

public section

namespace CFSG.StandardType.SpFrame

open Module

variable {k V : Type*} [Field k] [AddCommGroup V] [Module k V]

@[expose] def IsRefl (g : Module.End k V) : Prop :=
  g * g = 1 ∧ finrank k (Module.End.eigenspace g (-1)) = 1

theorem IsRefl.exists_neg {g : Module.End k V} (hg : IsRefl g) :
    ∃ b : V, b ≠ 0 ∧ g b = -b := by
  have hpos : 0 < finrank k (Module.End.eigenspace g (-1)) := by rw [hg.2]; norm_num
  haveI : Module.Finite k (Module.End.eigenspace g (-1)) := Module.finite_of_finrank_pos hpos
  obtain ⟨b, hb⟩ := (Module.finrank_pos_iff_exists_ne_zero (R := k)).mp hpos
  refine ⟨(b : V), ?_, ?_⟩
  · intro hb0
    exact hb (Subtype.ext hb0)
  · have hmem : (b : V) ∈ Module.End.eigenspace g (-1) := b.2
    rw [Module.End.mem_eigenspace_iff] at hmem
    rw [hmem, neg_one_smul]

theorem IsRefl.eigenspace_neg_eq_span {g : Module.End k V} (hg : IsRefl g) {b : V} (hb : b ≠ 0)
    (hgb : g b = -b) : Module.End.eigenspace g (-1) = k ∙ b := by
  have hb_mem : b ∈ Module.End.eigenspace g (-1) := by
    rw [Module.End.mem_eigenspace_iff, hgb, neg_one_smul]
  have hle : k ∙ b ≤ Module.End.eigenspace g (-1) :=
    (Submodule.span_singleton_le_iff_mem b _).mpr hb_mem
  have hpos : 0 < finrank k (Module.End.eigenspace g (-1)) := by rw [hg.2]; norm_num
  haveI : Module.Finite k (Module.End.eigenspace g (-1)) := Module.finite_of_finrank_pos hpos
  exact (Submodule.eq_of_le_of_finrank_eq hle (by
    rw [finrank_span_singleton hb, hg.2])).symm

theorem IsRefl.conj {g : Module.End k V} (hg : IsRefl g) {u u' : Module.End k V}
    (h1 : u * u' = 1) (h2 : u' * u = 1) : IsRefl (u * g * u') := by
  have hu'u : ∀ v, u' (u v) = v := fun v => by
    rw [← Module.End.mul_apply u' u v, h2, Module.End.one_apply]
  have huu' : ∀ v, u (u' v) = v := fun v => by
    rw [← Module.End.mul_apply u u' v, h1, Module.End.one_apply]
  have hgg : ∀ v, g (g v) = v := fun v => by
    rw [← Module.End.mul_apply g g v, hg.1, Module.End.one_apply]
  have hsq : (u * g * u') * (u * g * u') = 1 := by
    ext v
    simp only [Module.End.mul_apply, Module.End.one_apply]
    rw [hu'u, hgg, huu']
  have hmap : Module.End.eigenspace (u * g * u') (-1)
      = (Module.End.eigenspace g (-1)).map u := by
    apply le_antisymm
    · intro v hv
      rw [Module.End.mem_eigenspace_iff] at hv
      refine Submodule.mem_map.mpr ⟨u' v, ?_, huu' v⟩
      rw [Module.End.mem_eigenspace_iff]
      have huv : u (g (u' v)) = (-1 : k) • v := by
        simpa only [Module.End.mul_apply] using hv
      calc g (u' v) = u' (u (g (u' v))) := (hu'u (g (u' v))).symm
        _ = u' ((-1 : k) • v) := by rw [huv]
        _ = (-1 : k) • u' v := map_smul u' (-1) v
    · intro v hv
      obtain ⟨w, hw, rfl⟩ := Submodule.mem_map.mp hv
      have hw' : g w = (-1 : k) • w := Module.End.mem_eigenspace_iff.mp hw
      rw [Module.End.mem_eigenspace_iff]
      calc (u * g * u') (u w) = u (g (u' (u w))) := by
              simp only [Module.End.mul_apply]
        _ = u (g w) := by rw [hu'u]
        _ = u ((-1 : k) • w) := by rw [hw']
        _ = (-1 : k) • u w := map_smul u (-1) w
  have hu_inj : Function.Injective u := by
    intro a b hab
    have h : (u' * u) a = (u' * u) b := by
      rw [Module.End.mul_apply, Module.End.mul_apply, hab]
    rwa [h2, Module.End.one_apply, Module.End.one_apply] at h
  refine ⟨hsq, ?_⟩
  rw [hmap, ← (Submodule.equivMapOfInjective u hu_inj (Module.End.eigenspace g (-1))).finrank_eq,
    hg.2]

theorem IsRefl.apply_eq_self_of_commute (h2 : (2 : k) ≠ 0) {g h : Module.End k V}
    (hg : IsRefl g) (hh : IsRefl h) (hcomm : g * h = h * g) (hne : g ≠ h) {b : V}
    (hb : h b = -b) : g b = b := by
  by_cases hb0 : b = 0
  · subst hb0
    simp
  have hg_inv : ∀ v, g (g v) = v := fun v => by
    rw [← Module.End.mul_apply g g v, hg.1, Module.End.one_apply]
  have hh_inv : ∀ v, h (h v) = v := fun v => by
    rw [← Module.End.mul_apply h h v, hh.1, Module.End.one_apply]
  have hcomm_apply : ∀ v, h (g v) = g (h v) := fun v => by
    rw [← Module.End.mul_apply h g v, ← hcomm, Module.End.mul_apply g h v]
  have hgb_mem : g b ∈ Module.End.eigenspace h (-1) := by
    rw [Module.End.mem_eigenspace_iff]
    rw [hcomm_apply b, hb, map_neg, neg_one_smul]
  have hspan_h : Module.End.eigenspace h (-1) = k ∙ b := hh.eigenspace_neg_eq_span hb0 hb
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp (by rw [← hspan_h]; exact hgb_mem)
  have hcc : c * c = 1 := by
    have hc2 : (c * c) • b = b := by
      calc (c * c) • b = c • (c • b) := by rw [mul_smul]
        _ = c • (g b) := by rw [hc]
        _ = g (c • b) := (map_smul g c b).symm
        _ = g (g b) := by rw [hc]
        _ = b := hg_inv b
    have hsub : (c * c - 1) • b = 0 := by
      rw [sub_smul, one_smul, hc2, sub_self]
    exact sub_eq_zero.mp ((smul_eq_zero.mp hsub).resolve_right hb0)
  rcases mul_self_eq_one_iff.mp hcc with hc1 | hcneg
  · rw [← hc, hc1, one_smul]
  · exfalso
    have hgb_neg : g b = -b := by rw [← hc, hcneg, neg_one_smul]
    have hspan_g : Module.End.eigenspace g (-1) = k ∙ b := hg.eigenspace_neg_eq_span hb0 hgb_neg
    have hgv_sub_mem : ∀ v, g v - v ∈ k ∙ b := by
      intro v
      rw [← hspan_g, Module.End.mem_eigenspace_iff, map_sub, hg_inv v, neg_one_smul, neg_sub]
    have hhv_sub_mem : ∀ v, h v - v ∈ k ∙ b := by
      intro v
      rw [← hspan_h, Module.End.mem_eigenspace_iff, map_sub, hh_inv v, neg_one_smul, neg_sub]
    have hPv_sub_mem : ∀ v, (g * h) v - v ∈ k ∙ b := by
      intro v
      have h1' := hgv_sub_mem (h v)
      have h2' := hhv_sub_mem v
      have heq : g (h v) - v = (g (h v) - h v) + (h v - v) := by abel
      rw [Module.End.mul_apply, heq]
      exact Submodule.add_mem _ h1' h2'
    have hPb : (g * h) b = b := by
      rw [Module.End.mul_apply, hb, map_neg, hgb_neg, neg_neg]
    have hPsmul : ∀ (c' : k), (g * h) (c' • b) = c' • b := by
      intro c'
      rw [map_smul, hPb]
    have hPw : ∀ v, (g * h) ((g * h) v - v) = (g * h) v - v := by
      intro v
      obtain ⟨d, hd⟩ := Submodule.mem_span_singleton.mp (hPv_sub_mem v)
      rw [← hd, hPsmul d]
    have hPP : (g * h) * (g * h) = 1 := by
      calc (g * h) * (g * h) = g * (h * (g * h)) := by rw [mul_assoc]
        _ = g * ((h * g) * h) := by rw [mul_assoc h g h]
        _ = g * ((g * h) * h) := by rw [← hcomm]
        _ = g * (g * (h * h)) := by rw [mul_assoc g h h]
        _ = g * (g * 1) := by rw [hh.1]
        _ = g * g := by rw [mul_one]
        _ = 1 := hg.1
    have hPid : ∀ v, (g * h) ((g * h) v) = v := fun v => by
      rw [← Module.End.mul_apply (g * h) (g * h) v, hPP, Module.End.one_apply]
    have h2w : ∀ v, (g * h) v - v = 0 := by
      intro v
      have hkey : v = v + (2 : k) • ((g * h) v - v) := by
        calc v = (g * h) ((g * h) v) := (hPid v).symm
          _ = (g * h) (v + ((g * h) v - v)) := by
                rw [show v + ((g * h) v - v) = (g * h) v by abel]
          _ = (g * h) v + (g * h) ((g * h) v - v) := by rw [map_add]
          _ = (v + ((g * h) v - v)) + ((g * h) v - v) := by
                rw [hPw v]
                congr 1
                abel
          _ = v + (2 : k) • ((g * h) v - v) := by rw [two_smul]; abel
      have h2w0 : (2 : k) • ((g * h) v - v) = 0 := by
        have hcongr := congrArg (fun x => x - v) hkey
        simpa using hcongr.symm
      exact (smul_eq_zero.mp h2w0).resolve_left h2
    have hP_eq_one : g * h = 1 := by
      ext v
      rw [Module.End.one_apply]
      exact sub_eq_zero.mp (h2w v)
    have hgh : g = h := by
      calc g = g * 1 := (mul_one g).symm
        _ = g * (h * h) := by rw [hh.1]
        _ = (g * h) * h := (mul_assoc g h h).symm
        _ = 1 * h := by rw [hP_eq_one]
        _ = h := one_mul h
    exact hne hgh

theorem isCompl_eigenspace_one_neg_one (h2 : (2 : k) ≠ 0) {g : Module.End k V} (hg : g * g = 1) :
    IsCompl (Module.End.eigenspace g 1) (Module.End.eigenspace g (-1)) := by
  have hg_inv : ∀ v, g (g v) = v := fun v => by
    rw [← Module.End.mul_apply g g v, hg, Module.End.one_apply]
  apply IsCompl.of_eq
  · rw [Submodule.eq_bot_iff]
    intro v hv
    rw [Submodule.mem_inf] at hv
    obtain ⟨hv1, hv2⟩ := hv
    rw [Module.End.mem_eigenspace_iff] at hv1 hv2
    rw [one_smul] at hv1
    rw [neg_one_smul] at hv2
    have hvv : v = -v := hv1.symm.trans hv2
    have hzero : v + v = 0 := eq_neg_iff_add_eq_zero.mp hvv
    have h2v : (2 : k) • v = 0 := by rw [two_smul, hzero]
    exact (smul_eq_zero.mp h2v).resolve_left h2
  · rw [Submodule.eq_top_iff']
    intro v
    rw [Submodule.mem_sup]
    refine ⟨(1 / 2 : k) • (v + g v), ?_, (1 / 2 : k) • (v - g v), ?_, ?_⟩
    · rw [Module.End.mem_eigenspace_iff, map_smul, map_add, hg_inv v, one_smul, add_comm]
    · rw [Module.End.mem_eigenspace_iff, map_smul, map_sub, hg_inv v, neg_one_smul, ← smul_neg,
        neg_sub]
    · rw [← smul_add]
      rw [show v + g v + (v - g v) = (2 : k) • v by rw [two_smul]; abel]
      rw [smul_smul, div_mul_cancel₀ (1 : k) h2, one_smul]

theorem IsRefl.of_finrank_eigenspace_one [FiniteDimensional k V] (h2 : (2 : k) ≠ 0)
    {g : Module.End k V} (hg : g * g = 1)
    (hfix : finrank k (Module.End.eigenspace g 1) + 1 = finrank k V) : IsRefl g := by
  have hcompl : IsCompl (Module.End.eigenspace g 1) (Module.End.eigenspace g (-1)) :=
    isCompl_eigenspace_one_neg_one h2 hg
  have hsum := Submodule.finrank_add_eq_of_isCompl hcompl
  refine ⟨hg, ?_⟩
  have : finrank k (Module.End.eigenspace g 1) + finrank k (Module.End.eigenspace g (-1))
      = finrank k (Module.End.eigenspace g 1) + 1 := by rw [hsum, hfix]
  exact Nat.add_left_cancel this

end CFSG.StandardType.SpFrame
