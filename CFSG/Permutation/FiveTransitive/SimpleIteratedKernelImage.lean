module

public import CFSG.Permutation.FiveTransitive.SimpleGoursat

public section

namespace CFSG

namespace FiveTransitive.SimpleIteratedKernelImage

theorem le_kernel_image
    {L A B : Type} [Group L] [Group A] [Group B] [Finite L] [Finite A] [Finite B]
    (f : L →* A) (g : L →* B) (T : Subgroup A) [IsSimpleGroup T]
    (hT : T ≤ f.range) (hnot : ¬ Nat.card T ∣ Nat.card B) :
    T ≤ (f.comp g.ker.subtype).range := by
  intro t ht
  obtain ⟨l,hf,hg⟩ := SimpleGoursat.exists_lift_with_aux_eq_one_of_not_dvd
    L A B f g T hT (fun h => hnot (h.trans (Subgroup.card_subgroup_dvd_card g.range))) t ht
  exact ⟨⟨l,hg⟩,hf⟩

theorem le_kernel_image_of_two_aux
    {L A B C D : Type} [Group L] [Group A] [Group B] [Group C] [Group D]
    [Finite L] [Finite A] [Finite B] [Finite C] [Finite D]
    (f : L →* A) (g : L →* B) (u : B →* C) (v : B →* D)
    (T : Subgroup A) [IsSimpleGroup T] (hT : T ≤ f.range)
    (hC : ¬ Nat.card T ∣ Nat.card C) (hD : ¬ Nat.card T ∣ Nat.card D)
    (hJ : ¬ Nat.card T ∣ Nat.card ↥(u.ker ⊓ v.ker)) :
    T ≤ (f.comp g.ker.subtype).range := by
  let K := (u.comp g).ker
  let fK : K →* A := f.comp K.subtype
  let vK : K →* D := (v.comp g).comp K.subtype
  have hTK : T ≤ fK.range := le_kernel_image f (u.comp g) T hT hC
  let R := vK.ker
  let fR : R →* A := fK.comp R.subtype
  have hTR : T ≤ fR.range := le_kernel_image fK vK T hTK hD
  let J := u.ker ⊓ v.ker
  let gR : R →* B := (g.comp K.subtype).comp R.subtype
  have hmem : ∀ r : R, gR r ∈ J := by
    intro r
    exact ⟨r.val.property,r.property⟩
  let j : R →* J := gR.codRestrict J hmem
  have hTJ : T ≤ (fR.comp j.ker.subtype).range := le_kernel_image fR j T hTR hJ
  intro t ht
  obtain ⟨r,hr⟩ := hTJ ht
  have hg : g r.val.val.val = 1 := congrArg Subtype.val r.property
  exact ⟨⟨r.val.val.val,hg⟩,hr⟩

end FiveTransitive.SimpleIteratedKernelImage

end CFSG
