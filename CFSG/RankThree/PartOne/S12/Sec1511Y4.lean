module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.GroupTheory.ABGLocalTools.Basic
public import CFSG.RankThree.PartOne.CTP.StrongPGlue
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixIII.Basic

public section

namespace CFSG.RankThree.PartOne

open CFSG CFSG.ABGLocalTools StrongP

namespace Sec1511

theorem not_five_dvd_card_of_isPGroup_two {H : Type*} [Group H] [Finite H] (hH : IsPGroup 2 H) :
    ¬ 5 ∣ Nat.card H := by
  obtain ⟨k, hk⟩ := hH.exists_card_eq
  rw [hk]
  intro hdvd
  have h5 : Nat.Prime 5 := by norm_num
  have h2 : 5 ∣ 2 := h5.dvd_of_dvd_pow hdvd
  omega

section GLevel

variable {G : Type} [Group G] [Finite G]

theorem mem_normalizer_of_conj_le {R : Subgroup G} {m : G} (h : ∀ r ∈ R, m * r * m⁻¹ ∈ R) :
    m ∈ Subgroup.normalizer (R : Set G) := by
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  have hle : R.map (MulAut.conj m).toMonoidHom ≤ R := by
    rintro _ ⟨r, hr, rfl⟩
    exact h r hr
  exact Subgroup.eq_of_le_of_card_ge hle
    (by rw [Subgroup.card_map_of_injective (MulAut.conj m).injective])

theorem map_eq_of_forall_iff {X : Type*} [Group X] {S : Subgroup X} {σ : MulAut X}
    (h : ∀ x, x ∈ S ↔ σ x ∈ S) : S.map σ.toMonoidHom = S := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact (h x).1 hx
  · intro hy
    refine ⟨σ.symm y, ?_, by simp⟩
    exact (h _).2 (by simpa using hy)

end GLevel

end Sec1511

end CFSG.RankThree.PartOne
