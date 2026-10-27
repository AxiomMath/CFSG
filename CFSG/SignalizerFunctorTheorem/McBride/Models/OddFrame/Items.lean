module

public import CFSG.SignalizerFunctorTheorem.McBride.Models.Frame
public import CFSG.SignalizerFunctorTheorem.McBride.Models.AutItems
import CFSG.SignalizerFunctorTheorem.McBride.Models.FrameItems
import CFSG.SignalizerFunctorTheorem.McBride.Models.Conj

public section

open CFSG.Open
open scoped Pointwise

namespace CFSG.SignalizerFunctorTheorem.McBride

namespace OddFrame

variable {X : Type*} [Group X]

theorem mem_normalizer_of_forall_conj_mem [Finite X] {M : Subgroup X} {x : X}
    (hx : ∀ m ∈ M, x * m * x⁻¹ ∈ M) : x ∈ Subgroup.normalizer (M : Set X) := by
  rw [Subgroup.mem_normalizer_iff]
  intro h
  refine ⟨fun hh => hx h hh, fun hh => ?_⟩
  let φ : M → M := fun m => ⟨x * m * x⁻¹, hx m m.2⟩
  have hinj : Function.Injective φ := fun a b hab => by
    apply Subtype.ext
    have : x * (a : X) * x⁻¹ = x * (b : X) * x⁻¹ := congrArg Subtype.val hab
    simpa using this
  obtain ⟨m, hm⟩ := (Finite.injective_iff_surjective.mp hinj) ⟨x * h * x⁻¹, hh⟩
  have hmh : (m : X) = h := by
    have : x * (m : X) * x⁻¹ = x * h * x⁻¹ := congrArg Subtype.val hm
    simpa using this
  exact hmh ▸ m.2

theorem normalizer_eq_of_isCoatom (hs : IsSimpleGroup X) {M : Subgroup X} (hM : IsCoatom M)
    (hbot : M ≠ ⊥) : Subgroup.normalizer (M : Set X) = M := by
  by_contra hne
  have hlt : M < Subgroup.normalizer (M : Set X) :=
    lt_of_le_of_ne Subgroup.le_normalizer (Ne.symm hne)
  have hnorm : M.Normal := Subgroup.normalizer_eq_top_iff.mp (hM.2 _ hlt)
  rcases hs.eq_bot_or_eq_top_of_normal M with h | h
  · exact hbot h
  · exact hM.1 h

end OddFrame

variable {p ℓ : ℕ} {X : Type*} [Group X]

theorem Frame.isCoatom_fixedNormalizer [Finite X] {f : MulAut X} (h : Frame p ℓ f) :
    IsCoatom (fixedNormalizer f) := by
  refine ⟨h.fixedNormalizer_ne_top, fun b hb => ?_⟩
  by_contra hbtop
  exact not_le_of_gt hb (h.overgroup b ((fixed_le_fixedNormalizer f).trans hb.le) hbtop)

theorem Frame.fixedNormalizer_ne_bot {f : MulAut X} (h : Frame p ℓ f) :
    fixedNormalizer f ≠ ⊥ := fun h0 =>
  h.C0_ne_bot (le_bot_iff.mp (h0 ▸ Subgroup.le_normalizer))

theorem ItemG.of_inner [Finite X] {f : MulAut X} (h : Frame p ℓ f)
    (hin : ∀ g : MulAut X, Nat.Coprime p (orderOf g) → ∃ x : X, g = MulAut.conj x) :
    ItemG p f := by
  intro g hg hM _
  obtain ⟨x, rfl⟩ := hin g hg
  refine ⟨x, ?_, rfl⟩
  have hxN : x ∈ Subgroup.normalizer (fixedNormalizer f : Set X) :=
    OddFrame.mem_normalizer_of_forall_conj_mem fun m hm => by
      simpa [MulAut.conj_apply] using hM m hm
  rwa [OddFrame.normalizer_eq_of_isCoatom h.simple h.isCoatom_fixedNormalizer
    h.fixedNormalizer_ne_bot] at hxN

theorem ItemC.of_inner [Finite X] {f : MulAut X} (hp : p.Prime)
    (hin : ∀ g : MulAut X, Nat.Coprime p (orderOf g) → ∃ x : X, g = MulAut.conj x)
    (hcent : ∀ x : X, (∀ y ∈ signalizerFixedSubgroup f, x * y = y * x) → x = 1) :
    ItemC p f := by
  refine isPGroup_of_forall_coprime_orderOf_eq_one hp fun g hgcop => ?_
  have hgcop' : Nat.Coprime p (orderOf (g : MulAut X)) := by rwa [Subgroup.orderOf_coe]
  obtain ⟨x, hx⟩ := hin _ hgcop'
  have hx1 : x = 1 := by
    refine hcent x fun y hy => ?_
    have h1 := (mem_fixingSubgroup_iff (MulAut X)).mp g.2 y hy
    rw [hx, MulAut.smul_def, MulAut.conj_apply] at h1
    calc x * y = x * y * x⁻¹ * x := by group
      _ = y * x := by rw [h1]
  apply Subtype.ext
  rw [hx, hx1, map_one]
  rfl

theorem Frame.card_fixedNormalizer_dvd [Finite X] {f : MulAut X} (h : Frame p ℓ f) :
    Nat.card (fixedNormalizer f) ∣
      Nat.card (Subgroup.centralizer (fixedFitting f : Set X)) *
        Nat.card (signalizerFixedSubgroup f) := by
  have hZM := FrameItems.centralizer_le_fixedNormalizer f
  have hnorm := FrameItems.centralizer_subgroupOf_normal f
  let π : fixedNormalizer f →* fixedNormalizer f ⧸
      (Subgroup.centralizer (fixedFitting f : Set X)).subgroupOf (fixedNormalizer f) :=
    QuotientGroup.mk' _
  let ι : signalizerFixedSubgroup f →* fixedNormalizer f :=
    Subgroup.inclusion (fixed_le_fixedNormalizer f)
  have hsurj : Function.Surjective (π.comp ι) := by
    intro q
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective q
    obtain ⟨z, hz, c, hc, hxc⟩ := h.normalizer_le x x.2
    refine ⟨⟨c, hc⟩, ?_⟩
    show QuotientGroup.mk (ι ⟨c, hc⟩) = QuotientGroup.mk x
    rw [QuotientGroup.eq, Subgroup.mem_subgroupOf]
    have hc' : c⁻¹ ∈ fixedNormalizer f := Subgroup.inv_mem _ (fixed_le_fixedNormalizer f hc)
    have := FrameItems.conj_mem_centralizer hc' hz
    simpa [ι, hxc, mul_assoc] using this
  let Z' := (Subgroup.centralizer (fixedFitting f : Set X)).subgroupOf (fixedNormalizer f)
  have hidx : Z'.index ∣ Nat.card (signalizerFixedSubgroup f) := by
    rw [Subgroup.index_eq_card]
    exact Subgroup.card_dvd_of_surjective hsurj
  have hcard : Nat.card Z' = Nat.card (Subgroup.centralizer (fixedFitting f : Set X)) :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hZM).toEquiv
  rw [← Z'.card_mul_index, hcard]
  exact Nat.mul_dvd_mul_left _ hidx

end CFSG.SignalizerFunctorTheorem.McBride
