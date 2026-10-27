module

public import CFSG.LocalAnalysis.StandardType.GGTorsionDefs

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

section TorsionQuot

theorem ggTorsion_dvd_proper {X : Type} [Group X] (hX : commutator X = ⊤)
    {R : Type} [Group R] (θ : X ⧸ Subgroup.center X ≃* R) {δ : MulAut X} (hδ : δ ≠ 1)
    {J : Subgroup X} (hJ : J ≤ ggAutFixedSubgroup δ) :
    ∃ H : Subgroup R, H ≠ ⊤ ∧ Nat.card (↥J ⧸ Subgroup.center ↥J) ∣ Nat.card H := by
  set π : X →* R := (θ : X ⧸ Subgroup.center X →* R).comp
    (QuotientGroup.mk' (Subgroup.center X)) with hπdef
  have hπ : ∀ x : X, π x = θ (x : X ⧸ Subgroup.center X) := by
    intro x
    rw [hπdef]
    rfl
  set H : Subgroup R := J.map π with hHdef
  set N : Subgroup ↥J := (Subgroup.center X).subgroupOf J with hNdef
  set f : ↥J →* R := π.comp J.subtype with hfdef
  have hf : ∀ x : ↥J, f x = π (x : X) := by
    intro x
    rw [hfdef]
    rfl
  have hHne : H ≠ ⊤ := by
    intro hH
    apply hδ
    apply ggInducedAut_injective_of_perfect hX θ
    have hAut : ggInducedAut θ δ = 1 := by
      ext r
      have hr : r ∈ H := by rw [hH]; exact Subgroup.mem_top r
      rw [hHdef, Subgroup.mem_map] at hr
      obtain ⟨j, hj, hjπ⟩ := hr
      rw [← hjπ, hπ j, ggInducedAut_apply, (mem_ggAutFixedSubgroup δ j).mp (hJ hj),
        MulAut.one_apply]
    rw [hAut, map_one]
  have hNcenter : N ≤ Subgroup.center ↥J := by
    intro x hx
    rw [hNdef, Subgroup.mem_subgroupOf] at hx
    rw [Subgroup.mem_center_iff]
    intro y
    apply Subtype.ext
    change (y : X) * (x : X) = (x : X) * (y : X)
    exact (Subgroup.mem_center_iff.mp hx) (y : X)
  have hfker : f.ker = N := by
    ext x
    rw [MonoidHom.mem_ker, hf, hπ, hNdef, Subgroup.mem_subgroupOf]
    constructor
    · intro h
      exact (QuotientGroup.eq_one_iff (x : X)).mp ((θ.map_eq_one_iff).mp h)
    · intro h
      exact (θ.map_eq_one_iff).mpr ((QuotientGroup.eq_one_iff (x : X)).mpr h)
  have hfrange : f.range = H := by
    ext r
    rw [MonoidHom.mem_range, hHdef, Subgroup.mem_map]
    constructor
    · rintro ⟨x, hx⟩
      exact ⟨(x : X), x.2, by rw [← hf x]; exact hx⟩
    · rintro ⟨x, hx, hxr⟩
      exact ⟨⟨x, hx⟩, by rw [hf]; exact hxr⟩
  have hcardN : Nat.card (↥J ⧸ N) = Nat.card H := by
    have h := Nat.card_congr (QuotientGroup.quotientKerEquivRange f).toEquiv
    rw [hfker, hfrange] at h
    exact h
  refine ⟨H, hHne, ?_⟩
  have hdiv : (Subgroup.center ↥J).index ∣ N.index := Subgroup.index_dvd_of_le hNcenter
  calc Nat.card (↥J ⧸ Subgroup.center ↥J) = (Subgroup.center ↥J).index := rfl
    _ ∣ N.index := hdiv
    _ = Nat.card H := hcardN

end TorsionQuot

end CFSG.StandardType
