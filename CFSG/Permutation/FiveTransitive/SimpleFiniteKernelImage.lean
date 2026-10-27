module

public import CFSG.Permutation.FiveTransitive.SimpleIteratedKernelImage
public import Mathlib.Tactic.Basify
public import Std.Tactic.BVDecide.Normalize.Prop

public section

namespace CFSG

namespace FiveTransitive.SimpleFiniteKernelImage

private theorem le_kernel_image_finset
    {L A ι : Type} [Group L] [Group A] [Finite L] [Finite A]
    (B : ι → Type) [∀ i, Group (B i)] [∀ i, Finite (B i)]
    (f : L →* A) (g : ∀ i, L →* B i)
    (T : Subgroup A) [IsSimpleGroup T] (hT : T ≤ f.range)
    (hnot : ∀ i, ¬ Nat.card T ∣ Nat.card (B i)) (s : Finset ι) :
    ∀ t ∈ T, ∃ l : L, f l = t ∧ ∀ i ∈ s, g i l = 1 := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      intro t ht
      obtain ⟨l,hl⟩ := hT ht
      exact ⟨l,hl,by simp⟩
  | @insert i s hi ih =>
      let K : Subgroup L := ⨅ j ∈ s, (g j).ker
      let fK : K →* A := f.comp K.subtype
      let gK : K →* B i := (g i).comp K.subtype
      have hTK : T ≤ fK.range := by
        intro t ht
        obtain ⟨l,hl,hls⟩ := ih t ht
        have hlK : l ∈ K := by simpa only [K,Subgroup.mem_iInf,MonoidHom.mem_ker] using hls
        exact ⟨⟨l,hlK⟩,hl⟩
      have hTi := SimpleIteratedKernelImage.le_kernel_image fK gK T hTK (hnot i)
      intro t ht
      obtain ⟨l,hl⟩ := hTi ht
      refine ⟨l.val.val,hl,?_⟩
      intro j hj
      rcases Finset.mem_insert.mp hj with rfl | hj
      · exact l.property
      · have hls : ∀ k ∈ s, g k l.val.val = 1 := by
          simpa only [K,Subgroup.mem_iInf,MonoidHom.mem_ker] using l.val.property
        exact hls j hj

theorem eq_bot_of_jointly_faithful
    {L A ι : Type} [Group L] [Group A] [Finite L] [Finite A] [Fintype ι]
    (B : ι → Type) [∀ i, Group (B i)] [∀ i, Finite (B i)]
    (f : L →* A) (g : ∀ i, L →* B i)
    (T : Subgroup A) [IsSimpleGroup T] (hT : T ≤ f.range)
    (hnot : ∀ i, ¬ Nat.card T ∣ Nat.card (B i))
    (hfaithful : ∀ l : L, (∀ i, g i l = 1) → l = 1) : T = ⊥ := by
  classical
  rw [Subgroup.eq_bot_iff_forall]
  intro t ht
  obtain ⟨l,hl,hls⟩ := le_kernel_image_finset B f g T hT hnot Finset.univ t ht
  have he : l = 1 := hfaithful l (fun i => hls i (Finset.mem_univ i))
  rw [he,map_one] at hl
  exact hl.symm

end FiveTransitive.SimpleFiniteKernelImage

end CFSG
