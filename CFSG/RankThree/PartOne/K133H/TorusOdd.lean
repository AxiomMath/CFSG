module

public import CFSG.RankThree.PartOne.K133H.TorusImage
public import CFSG.RankThree.PartOne.S13K.KF133One

public section

namespace CFSG.RankThree.PartOne.K133H

open CFSG.RankThree.PartOne CFSG.RankThree.PartOne.S13K

theorem exists_injective_hom_torusImage {G Q : Type} [Group G] [Group Q] (ι : Q →* G)
    (hι : Function.Injective ι) {E : Subgroup Q} {V Y : Subgroup G} (hV : E.map ι = V)
    (hY : ∀ x, ι x ∈ Y) :
    ∃ Φ : MulAut E →* MulAut V, Function.Injective Φ ∧
      ∀ α ∈ torusImage E ⊤, Φ α ∈ torusImage V Y := by
  subst hV
  let e : E ≃* E.map ι := Subgroup.equivMapOfInjective E ι hι
  refine ⟨(MulAut.congr e).toMonoidHom, (MulAut.congr e).injective, fun α hα => ?_⟩
  obtain ⟨x, hx, -, rfl⟩ := mem_torusImage_iff.1 hα
  refine mem_torusImage_iff.2 ⟨ι x, Subgroup.le_normalizer_map ι (Subgroup.mem_map_of_mem ι hx),
    hY x, ?_⟩
  ext e'
  obtain ⟨e₀, rfl⟩ := e.surjective e'
  show ι x * ((e e₀ : E.map ι) : G) * (ι x)⁻¹ =
    ((e (E.normalizerMonoidHom ⟨x, hx⟩ (e.symm (e e₀))) : E.map ι) : G)
  rw [e.symm_apply_apply]
  simp [e, Subgroup.coe_equivMapOfInjective_apply]

theorem eq_one_or_three_of_injective {G Q : Type} [Group G] [Group Q] (ι : Q →* G)
    (hι : Function.Injective ι) {E : Subgroup Q} {V Y : Subgroup G} (hV : E.map ι = V)
    (hY : ∀ x, ι x ∈ Y)
    (h : ∀ β ∈ torusImage V Y, Odd (orderOf β) → orderOf β = 1 ∨ orderOf β = 3) :
    ∀ α ∈ torusImage E ⊤, Odd (orderOf α) → orderOf α = 1 ∨ orderOf α = 3 := by
  obtain ⟨Φ, hΦ, hmem⟩ := exists_injective_hom_torusImage ι hι hV hY
  intro α hα hodd
  have := h (Φ α) (hmem α hα) (by rwa [orderOf_injective Φ hΦ α])
  rwa [orderOf_injective Φ hΦ α] at this

theorem oddOrderOneOrThree_torusImage_of_injective {G Q : Type} [Group G] [Group Q]
    (ι : Q →* G) (hι : Function.Injective ι) {E : Subgroup Q} {V Y : Subgroup G}
    (hV : E.map ι = V) (hY : ∀ x, ι x ∈ Y)
    (h : ∀ β ∈ torusImage V Y, Odd (orderOf β) → orderOf β = 1 ∨ orderOf β = 3) :
    OddOrderOneOrThree ↥(torusImage E ⊤) := by
  intro x hx
  have h' := eq_one_or_three_of_injective ι hι hV hY h (x : MulAut E) x.2
    (by rwa [Subgroup.orderOf_coe])
  rwa [Subgroup.orderOf_coe] at h'

end CFSG.RankThree.PartOne.K133H
