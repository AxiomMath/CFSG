module

public import CFSG.Permutation.FiveTransitive.FreeTwoGroupOddCyclic
public import CFSG.Permutation.FiveTransitive.FixedComplementSign
public import CFSG.Permutation.FiveTransitive.ThreeSwapTwoGroup

public section

namespace CFSG

namespace FiveTransitive.FreeThreeSwapObstruction

open MulAction FixedNormalizerAction

theorem not_free
    {G X : Type*} [Group G] [Finite G] [Fintype X] [DecidableEq X] [MulAction G X]
    (Q : Subgroup G) [Fintype (Fixed (X := X) Q)] [DecidableEq (Fixed (X := X) Q)]
    (B : Subgroup (Normalizer Q)) (hB : IsPGroup 2 B)
    (e : Fin 6 ↪ Fixed (X := X) Q)
    (himage : B.map (toPermHom (Normalizer Q) (Fixed (X := X) Q)) =
      ThreeSwapTwoGroup.subgroup e)
    (heven : ∀ b : B, Equiv.Perm.sign (toPerm b.val.val : Equiv.Perm X) = 1)
    (hfree : ∀ (b : B) (z : NormalizerFixedComplement.Domain (X := X) Q),
      b • z = z → b = 1) : False := by
  classical
  let _ := Fintype.ofFinite (NormalizerFixedComplement.Domain (X := X) Q)
  let f := toPermHom (Normalizer Q) (Fixed (X := X) Q)
  have hmem (i j : Fin 6) (hij : Equiv.swap (e i) (e j) ∈ ThreeSwapTwoGroup.subgroup e) :
      ∃ b : B, f b.val = Equiv.swap (e i) (e j) := by
    rw [← himage] at hij
    obtain ⟨b, hb, he⟩ := hij
    exact ⟨⟨b, hb⟩, he⟩
  obtain ⟨b, hb⟩ := hmem 0 1 (Subgroup.subset_closure (by simp))
  obtain ⟨c, hc⟩ := hmem 2 3 (Subgroup.subset_closure (by simp))
  have hbodd : (toPerm b.val : Equiv.Perm (Fixed (X := X) Q)).sign = -1 := by
    change (f b.val).sign = -1
    rw [hb]
    exact Equiv.Perm.sign_swap (e.injective.ne (by decide))
  have hodd := FixedComplementSign.complement_odd Q b.val (heven b) (by
    convert hbodd using 1
    congr 2 <;> exact Subsingleton.elim _ _)
  obtain ⟨hgen, _⟩ := FreeTwoGroupOddCyclic.generates hB hfree b hodd
  have hcb : c ∈ Subgroup.zpowers b := by rw [hgen]; trivial
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hcb
  have hperm : Equiv.swap (e 0) (e 1) ^ k = Equiv.swap (e 2) (e 3) := by
    have h := congrArg (f.comp B.subtype) hk
    simpa only [map_zpow, MonoidHom.comp_apply, Subgroup.subtype_apply, hb, hc] using h
  have hfix : (Equiv.swap (e 0) (e 1)) (e 2) = e 2 := by
    apply Equiv.swap_apply_of_ne_of_ne <;> exact e.injective.ne (by decide)
  have heq := Equiv.Perm.zpow_apply_eq_self_of_apply_eq_self hfix k
  rw [hperm, Equiv.swap_apply_left] at heq
  exact (e.injective.ne (by decide : (3 : Fin 6) ≠ 2)) heq

end FiveTransitive.FreeThreeSwapObstruction

end CFSG
