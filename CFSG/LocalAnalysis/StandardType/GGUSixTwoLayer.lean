module

public import CFSG.LocalAnalysis.StandardType.GGUSixTwoDescent
public import CFSG.LocalAnalysis.StandardType.GGTableBSymplecticCover
import CFSG.RankThree.PartOne.S15K.CentralCover
import CFSG.LieType.Steinberg.CentralExt.PerfectCover
import CFSG.LocalAnalysis.RankThreeEvenClassification.ComponentCore

public section

namespace CFSG.StandardType.USixTwo

open CFSG.Assembly CFSG.StandardType CFSG.StandardType.TableBSymp CFSG.StandardType.Line63.H5
open scoped commutatorElement

section Fix

variable {L' Lb : Type} [Group L'] [Group Lb] {π : L' →* Lb} {a : MulAut L'} {ab : MulAut Lb}

theorem map_fix_le (hc : ∀ l, ab (π l) = π (a l)) : (ggFix a).map π ≤ ggFix ab := by
  rintro _ ⟨x, hx, rfl⟩
  rw [mem_ggFix, hc, mem_ggFix.mp hx]

theorem fix_le_comap (hc : ∀ l, ab (π l) = π (a l)) : ggFix a ≤ (ggFix ab).comap π := by
  intro x hx
  rw [Subgroup.mem_comap, mem_ggFix, hc, mem_ggFix.mp hx]

theorem apply_mul_inv_mem_ker (hc : ∀ l, ab (π l) = π (a l)) {x : L'} (hx : π x ∈ ggFix ab) :
    a x * x⁻¹ ∈ π.ker := by
  rw [MonoidHom.mem_ker, map_mul, map_inv, ← hc, mem_ggFix.mp hx, mul_inv_cancel]

theorem fix_normal_comap (hker : π.ker ≤ Subgroup.center L') (hc : ∀ l, ab (π l) = π (a l)) :
    ((ggFix a).subgroupOf ((ggFix ab).comap π)).Normal := by
  rw [Subgroup.normal_subgroupOf_iff (fix_le_comap hc)]
  intro c g hc' hg
  have hgx : π g ∈ ggFix ab := hg
  set w := a g * g⁻¹ with hw
  have hwc : w ∈ Subgroup.center L' := hker (apply_mul_inv_mem_ker hc hgx)
  have hag : a g = w * g := by rw [hw]; group
  have h := Subgroup.mem_center_iff.mp hwc (g * c * g⁻¹)
  show a (g * c * g⁻¹) = g * c * g⁻¹
  rw [map_mul, map_mul, map_inv, hag, mem_ggFix.mp hc']
  calc w * g * c * (w * g)⁻¹ = w * (g * c * g⁻¹) * w⁻¹ := by group
    _ = (g * c * g⁻¹ * w) * w⁻¹ := by rw [h]
    _ = g * c * g⁻¹ := by group

theorem isComponentOf_map_fix (hπ : Function.Surjective π) (hker : π.ker ≤ Subgroup.center L')
    (hc : ∀ l, ab (π l) = π (a l)) {K' : Subgroup L'} (h : IsComponentOf K' (ggFix a)) :
    IsComponentOf (K'.map π) (ggFix ab) := by
  have hKne : ¬ K' ≤ π.ker := fun hle => not_le_center_of_isQuasisimple h.2.2 (hle.trans hker)
  have hq := (isComponentOf_map_of_not_le_ker π h hKne).2.2
  have hsub : IsSubnormal K' ((ggFix ab).comap π) :=
    h.2.1.trans (IsSubnormal.step (fix_le_comap hc) (fix_normal_comap hker hc)
      (IsSubnormal.refl _))
  have h2 := hsub.map π
  rw [Subgroup.map_comap_eq_self_of_surjective hπ] at h2
  exact ⟨(Subgroup.map_mono h.1).trans (map_fix_le hc), h2, hq⟩

theorem commutator_le_fix (hker : π.ker ≤ Subgroup.center L') {Y : Subgroup L'} {a' : MulAut L'}
    (h : ∀ y ∈ Y, a' y * y⁻¹ ∈ π.ker) : ⁅Y, Y⁆ ≤ ggFix a' := by
  refine Subgroup.commutator_le.mpr fun y₁ hy₁ y₂ hy₂ => ?_
  have hw₁ := hker (h y₁ hy₁)
  have hw₂ := hker (h y₂ hy₂)
  have e₁ : a' y₁ = (a' y₁ * y₁⁻¹) * y₁ := by group
  have e₂ : a' y₂ = (a' y₂ * y₂⁻¹) * y₂ := by group
  rw [mem_ggFix, map_commutatorElement, e₁, e₂]
  exact CFSG.LieType.Steinberg.commutatorElement_mul_mul_of_mem_center hw₁ hw₂ y₁ y₂

theorem fix_of_perfect (hker : π.ker ≤ Subgroup.center L') {X : Subgroup L'} (hX : ⁅X, X⁆ = X)
    {a' : MulAut L'} (h : ∀ x ∈ X, a' x * x⁻¹ ∈ π.ker) : ∀ x ∈ X, a' x = x := by
  have hle : ⁅X, X⁆ ≤ ggFix a' := commutator_le_fix hker h
  rw [hX] at hle
  exact fun x hx => hle hx

theorem isComponentOf_lift_fix (hπ : Function.Surjective π) (hker : π.ker ≤ Subgroup.center L')
    (hc : ∀ l, ab (π l) = π (a l)) {Kb : Subgroup Lb} (h : IsComponentOf Kb (ggFix ab)) :
    IsComponentOf ⁅Kb.comap π, Kb.comap π⁆ (ggFix a) ∧
      (⁅Kb.comap π, Kb.comap π⁆).map π = Kb := by
  set Y := Kb.comap π with hY
  have hKbq : CFSG.IsQuasisimple Kb := (isQuasisimple_iff _).mp h.2.2
  have hperf : ⁅Kb, Kb⁆ = Kb := Subgroup.isPerfect_iff.1 hKbq.1
  have hDq : CFSG.IsQuasisimple ↥⁅Y, Y⁆ :=
    CFSG.RankThree.PartOne.S15K.isQuasisimple_commutator_comap hπ hker hKbq
  have hmap : (⁅Y, Y⁆).map π = Kb := CFSG.RankThree.PartOne.S15K.map_commutator_comap hπ hperf
  have hDfix : ⁅Y, Y⁆ ≤ ggFix a :=
    commutator_le_fix hker fun y hy => apply_mul_inv_mem_ker hc (h.1 hy)
  have hDP : ⁅Y, Y⁆ ≤ Y ⊓ ggFix a := le_inf (Subgroup.commutator_le_self Y) hDfix
  have hsubn : IsSubnormal (Y ⊓ ggFix a) (ggFix a) :=
    (h.2.1.comap π).inf_of_le (fix_le_comap hc)
  have hDn : ((⁅Y, Y⁆).subgroupOf (Y ⊓ ggFix a)).Normal := by
    rw [Subgroup.normal_subgroupOf_iff hDP]
    intro d k hd hk
    have hle : (⁅Y, Y⁆).map (MulAut.conj k).toMonoidHom ≤ ⁅Y, Y⁆ := by
      rw [Subgroup.map_commutator]
      have hYk : Y.map (MulAut.conj k).toMonoidHom ≤ Y := by
        rintro _ ⟨y, hy, rfl⟩
        exact Y.mul_mem (Y.mul_mem hk.1 hy) (Y.inv_mem hk.1)
      exact Subgroup.commutator_mono hYk hYk
    exact hle ⟨d, hd, by simp [MulAut.conj_apply]⟩
  exact ⟨⟨hDfix, IsSubnormal.step hDP hDn hsubn, (isQuasisimple_iff _).mpr hDq⟩, hmap⟩

theorem layer_map_eq (hπ : Function.Surjective π) (hker : π.ker ≤ Subgroup.center L')
    (hc : ∀ l, ab (π l) = π (a l)) :
    (LargeEvenLayer (ggFix a)).map π = LargeEvenLayer (ggFix ab) := by
  apply le_antisymm
  · rw [Subgroup.map_le_iff_le_comap]
    refine sSup_le fun K' hK' => ?_
    rw [← Subgroup.map_le_iff_le_comap]
    exact le_sSup (isComponentOf_map_fix hπ hker hc hK')
  · refine sSup_le fun Kb hKb => ?_
    obtain ⟨hK, hmap⟩ := isComponentOf_lift_fix hπ hker hc hKb
    rw [← hmap]
    exact Subgroup.map_mono (le_sSup hK)

theorem layer_eq_commutator_comap (hπ : Function.Surjective π) (hker : π.ker ≤ Subgroup.center L')
    (hc : ∀ l, ab (π l) = π (a l))
    (hE : IsComponentOf (LargeEvenLayer (ggFix ab)) (ggFix ab)) :
    LargeEvenLayer (ggFix a) = ⁅(LargeEvenLayer (ggFix ab)).comap π,
      (LargeEvenLayer (ggFix ab)).comap π⁆ ∧
      IsComponentOf (LargeEvenLayer (ggFix a)) (ggFix a) := by
  obtain ⟨hK, -⟩ := isComponentOf_lift_fix hπ hker hc hE
  have hle : LargeEvenLayer (ggFix a) ≤ ⁅(LargeEvenLayer (ggFix ab)).comap π,
      (LargeEvenLayer (ggFix ab)).comap π⁆ := by
    refine sSup_le fun K' hK' => ?_
    have hK'q : CFSG.IsQuasisimple K' := (isQuasisimple_iff _).mp hK'.2.2
    have hK'perf : ⁅K', K'⁆ = K' := Subgroup.isPerfect_iff.1 hK'q.1
    have hK'Y : K' ≤ (LargeEvenLayer (ggFix ab)).comap π := by
      rw [← Subgroup.map_le_iff_le_comap]
      exact le_sSup (isComponentOf_map_fix hπ hker hc hK')
    rw [← hK'perf]
    exact Subgroup.commutator_mono hK'Y hK'Y
  have heq : LargeEvenLayer (ggFix a) = ⁅(LargeEvenLayer (ggFix ab)).comap π,
      (LargeEvenLayer (ggFix ab)).comap π⁆ := le_antisymm hle (le_sSup hK)
  exact ⟨heq, heq ▸ hK⟩

theorem isComponentOf_layer_down (hπ : Function.Surjective π) (hker : π.ker ≤ Subgroup.center L')
    (hc : ∀ l, ab (π l) = π (a l))
    (h : IsComponentOf (LargeEvenLayer (ggFix a)) (ggFix a)) :
    IsComponentOf (LargeEvenLayer (ggFix ab)) (ggFix ab) := by
  rw [← layer_map_eq hπ hker hc]
  exact isComponentOf_map_fix hπ hker hc h

theorem layer_perfect {G : Type} [Group G] (X : Subgroup G) :
    ⁅LargeEvenLayer X, LargeEvenLayer X⁆ = LargeEvenLayer X := by
  refine le_antisymm (Subgroup.commutator_le.mpr fun x hx y hy => ?_) (sSup_le fun K hK => ?_)
  · exact (LargeEvenLayer X).mul_mem ((LargeEvenLayer X).mul_mem
      ((LargeEvenLayer X).mul_mem hx hy) ((LargeEvenLayer X).inv_mem hx))
      ((LargeEvenLayer X).inv_mem hy)
  · have hq : CFSG.IsQuasisimple K := (isQuasisimple_iff _).mp hK.2.2
    have hperf : ⁅K, K⁆ = K := Subgroup.isPerfect_iff.1 hq.1
    rw [← hperf]
    exact Subgroup.commutator_mono (le_sSup hK) (le_sSup hK)

theorem fix_layer_iff (hπ : Function.Surjective π) (hker : π.ker ≤ Subgroup.center L')
    (hc : ∀ l, ab (π l) = π (a l)) {a' : MulAut L'} {ab' : MulAut Lb}
    (hc' : ∀ l, ab' (π l) = π (a' l)) :
    (∀ j ∈ LargeEvenLayer (ggFix a), a' j = j) ↔
      ∀ jb ∈ LargeEvenLayer (ggFix ab), ab' jb = jb := by
  have hmap := layer_map_eq hπ hker hc
  constructor
  · intro h jb hjb
    rw [← hmap] at hjb
    obtain ⟨j, hj, rfl⟩ := hjb
    rw [hc', h j hj]
  · intro h j hj
    refine fix_of_perfect hker (layer_perfect _) (fun x hx => ?_) j hj
    have hxb : π x ∈ LargeEvenLayer (ggFix ab) := by
      rw [← hmap]
      exact ⟨x, hx, rfl⟩
    rw [MonoidHom.mem_ker, map_mul, map_inv, ← hc', h (π x) hxb, mul_inv_cancel]

end Fix

section Invariant

variable {L' : Type} [Group L'] {a a' : MulAut L'}

theorem layer_invariant (hcomm : a * a' = a' * a) :
    ∀ e ∈ LargeEvenLayer (ggFix a), a' e ∈ LargeEvenLayer (ggFix a) := by
  have hC : (ggFix a).map a'.toMonoidHom = ggFix a := by
    apply le_antisymm
    · rintro _ ⟨x, hx, rfl⟩
      show a (a' x) = a' x
      have := congrArg (fun f : MulAut L' => f x) hcomm
      simp only [MulAut.mul_apply] at this
      rw [this, mem_ggFix.mp hx]
    · intro y hy
      refine ⟨a'⁻¹ y, ?_, by simp⟩
      show a (a'⁻¹ y) = a'⁻¹ y
      have h2 := congrArg (fun f : MulAut L' => f (a'⁻¹ y)) hcomm
      simp only [MulAut.mul_apply, MulAut.apply_inv_self] at h2
      have h3 : a' (a (a'⁻¹ y)) = a' (a'⁻¹ y) := by
        rw [← h2, MulAut.apply_inv_self, mem_ggFix.mp hy]
      exact a'.injective (by rw [h3, MulAut.apply_inv_self])
  have hle : (LargeEvenLayer (ggFix a)).map a'.toMonoidHom ≤ LargeEvenLayer (ggFix a) := by
    rw [Subgroup.map_le_iff_le_comap]
    refine sSup_le fun K hK => ?_
    rw [← Subgroup.map_le_iff_le_comap]
    have h := isComponentOf_map_of_injective a'.toMonoidHom a'.injective hK
    rw [hC] at h
    exact le_sSup h
  exact fun e he => hle ⟨e, he, rfl⟩

end Invariant


end CFSG.StandardType.USixTwo

end
