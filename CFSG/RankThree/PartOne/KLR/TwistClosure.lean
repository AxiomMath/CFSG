module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.RankThree.PartOne.KLR.Embedding

public section

namespace CFSG.RankThree.PartOne.KLR

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Ree
  CFSG.RankThree.PartOne.KE CFSG.RankThree.Chevalley

variable {L : Type} [Field L] {a : ℕ} (F : MulAut (adjointGroup ReeTag.F4.tag L))

@[expose] noncomputable def twistMap (n g : ModGL ReeTag.F4.tag L) : ModGL ReeTag.F4.tag L :=
  n * Fext F g * n⁻¹

variable {F}

theorem twistMap_mul (n : ModGL ReeTag.F4.tag L) {g h : ModGL ReeTag.F4.tag L}
    (hg : g ∈ adjointGroup ReeTag.F4.tag L) (hh : h ∈ adjointGroup ReeTag.F4.tag L) :
    twistMap F n (g * h) = twistMap F n g * twistMap F n h := by
  unfold twistMap
  rw [Fext_mul F hg hh]
  group

theorem twistMap_one (n : ModGL ReeTag.F4.tag L) : twistMap F n 1 = 1 := by
  unfold twistMap
  rw [Fext_one]
  group

theorem twistMap_inv (n : ModGL ReeTag.F4.tag L) {g : ModGL ReeTag.F4.tag L}
    (hg : g ∈ adjointGroup ReeTag.F4.tag L) : twistMap F n g⁻¹ = (twistMap F n g)⁻¹ := by
  unfold twistMap
  rw [Fext_inv F hg]
  group

theorem twistMap_mem_adjoint {n g : ModGL ReeTag.F4.tag L}
    (hn : n ∈ adjointGroup ReeTag.F4.tag L) (hg : g ∈ adjointGroup ReeTag.F4.tag L) :
    twistMap F n g ∈ adjointGroup ReeTag.F4.tag L :=
  mul_mem (mul_mem hn (Fext_mem F hg)) (inv_mem hn)

theorem twistMap_mem_of_closure {n : ModGL ReeTag.F4.tag L} {s : Set (ModGL ReeTag.F4.tag L)}
    (hs : s ⊆ adjointGroup ReeTag.F4.tag L) {T : Subgroup (ModGL ReeTag.F4.tag L)}
    (h : ∀ g ∈ s, twistMap F n g ∈ T) {g : ModGL ReeTag.F4.tag L}
    (hg : g ∈ Subgroup.closure s) : twistMap F n g ∈ T ∧ g ∈ adjointGroup ReeTag.F4.tag L := by
  induction hg using Subgroup.closure_induction with
  | mem x hx => exact ⟨h x hx, hs hx⟩
  | one => exact ⟨by rw [twistMap_one]; exact one_mem _, one_mem _⟩
  | mul x y _ _ hx hy =>
    refine ⟨?_, mul_mem hx.2 hy.2⟩
    rw [twistMap_mul n hx.2 hy.2]
    exact mul_mem hx.1 hy.1
  | inv x _ hx =>
    refine ⟨?_, inv_mem hx.2⟩
    rw [twistMap_inv n hx.2]
    exact inv_mem hx.1

theorem twistMap_mem_rootSubgroup {n : ModGL ReeTag.F4.tag L} (γ : Fin ReeTag.F4.tag.rank → ℤ)
    {T : Subgroup (ModGL ReeTag.F4.tag L)}
    (h : ∀ c : L, twistMap F n (pinnedX ReeTag.F4.tag L γ c) ∈ T) {g : ModGL ReeTag.F4.tag L}
    (hg : g ∈ rootSubgroup ReeTag.F4.tag L γ) : twistMap F n g ∈ T :=
  (twistMap_mem_of_closure (s := Set.range (pinnedX ReeTag.F4.tag L γ))
    (fun _ ⟨c, hc⟩ => hc ▸ pinnedX_mem_adjointGroup γ c) (fun _ ⟨c, hc⟩ => hc ▸ h c) hg).1

end CFSG.RankThree.PartOne.KLR
