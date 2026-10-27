module

public import CFSG.SignalizerFunctorTheorem.McBride.Functor.ClassHypB
public import CFSG.LocalAnalysis.SignalizerFunctor.CentralizerImages
import CFSG.GroupTheory.ElementaryAbelianTransport

public section

open CFSG.Open

universe u

namespace CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.AChief

variable {Γ : Type u} [Group Γ]

theorem isElemAbelian_subgroupOf {p : ℕ} {E : Subgroup Γ} (hE : IsElemAbelian p E)
    (H : Subgroup Γ) : IsElemAbelian p (E.subgroupOf H) := CFSG.Open.IsElemAbelian.subgroupOf hE H

theorem subgroupOf_le_normalizer {E Y H : Subgroup Γ} (h : E ≤ Subgroup.normalizer (Y : Set Γ)) :
    E.subgroupOf H ≤ Subgroup.normalizer ((Y.subgroupOf H : Subgroup H) : Set H) := by
  intro e he
  rw [Subgroup.mem_normalizer_iff]
  intro y
  have h1 := Subgroup.mem_normalizer_iff.mp (h (Subgroup.mem_subgroupOf.mp he)) (y : Γ)
  simpa only [SetLike.mem_coe, Subgroup.mem_subgroupOf, Subgroup.coe_mul, Subgroup.coe_inv]
    using h1

theorem card_subgroupOf {X H : Subgroup Γ} (h : X ≤ H) :
    Nat.card (X.subgroupOf H) = Nat.card X :=
  Nat.card_congr (Subgroup.subgroupOfEquivOfLe h).toEquiv

theorem hypB_subgroupOf [Finite Γ] {p : ℕ} {Y H : Subgroup Γ} (hYH : Y ≤ H)
    (hY : signalizerMcBrideHypothesisB p Y) :
    signalizerMcBrideHypothesisB p (Y.subgroupOf H) := by
  have h := (signalizerMcBrideHypothesisB_map_iff (p := p) H.subtype H.subtype_injective
    (X := Y.subgroupOf H)).mpr
  rw [Subgroup.map_subgroupOf_eq_of_le hYH] at h
  exact h hY

theorem subgroupOf_inf_centralizer {E Y H : Subgroup Γ} (hEH : E ≤ H) :
    (Y ⊓ Subgroup.centralizer (E : Set Γ)).subgroupOf H =
      Y.subgroupOf H ⊓ Subgroup.centralizer ((E.subgroupOf H : Subgroup H) : Set H) := by
  ext x
  simp only [Subgroup.mem_subgroupOf, Subgroup.mem_inf, Subgroup.mem_centralizer_iff,
    SetLike.mem_coe]
  refine and_congr_right fun _ => ⟨fun h e he => Subtype.ext (h _ he), fun h e he => ?_⟩
  exact congrArg Subtype.val (h ⟨e, hEH he⟩ he)

abbrev nrm (N : Subgroup Γ) : Subgroup Γ := Subgroup.normalizer (N : Set Γ)

abbrev QG (N : Subgroup Γ) : Type u := ↥(nrm N) ⧸ N.subgroupOf (nrm N)

@[expose] def qmap (N : Subgroup Γ) : ↥(nrm N) →* QG N :=
  QuotientGroup.mk' (N.subgroupOf (nrm N))

@[expose] def qimg (N X : Subgroup Γ) : Subgroup (QG N) :=
  (X.subgroupOf (nrm N)).map (qmap N)

theorem mem_qimg_iff (N X : Subgroup Γ) (x : QG N) :
    x ∈ qimg N X ↔ ∃ y : ↥(nrm N), (y : Γ) ∈ X ∧ qmap N y = x := by
  simp [qimg, Subgroup.mem_map, Subgroup.mem_subgroupOf]

variable {p : ℕ} {N E Y : Subgroup Γ}

theorem card_qimg_mul_card (hNY : N ≤ Y) (hY : Y ≤ nrm N) :
    Nat.card (qimg N Y) * Nat.card N = Nat.card Y := by
  have hN : N.subgroupOf (nrm N) ≤ Y.subgroupOf (nrm N) := fun x hx => hNY hx
  have h := card_map_mk'_mul_card (G := ↥(nrm N)) (N := N.subgroupOf (nrm N))
    (X := Y.subgroupOf (nrm N)) hN
  rwa [card_subgroupOf (Subgroup.le_normalizer (H := N)), card_subgroupOf hY] at h

theorem isElemAbelian_qimg (hE : IsElemAbelian p E) : IsElemAbelian p (qimg N E) := by
  obtain ⟨hc, hx⟩ := isElemAbelian_subgroupOf hE (nrm N)
  refine ⟨⟨⟨?_⟩⟩, ?_⟩
  · rintro ⟨_, a, ha, rfl⟩ ⟨_, b, hb, rfl⟩
    have h := mul_comm' (⟨a, ha⟩ : E.subgroupOf (nrm N)) ⟨b, hb⟩
    exact Subtype.ext (by simpa using congrArg (fun z : E.subgroupOf (nrm N) => qmap N z) h)
  · rintro _ ⟨a, ha, rfl⟩
    rw [← map_pow, hx a ha, map_one]

theorem qimg_le_normalizer (hEY : E ≤ Subgroup.normalizer (Y : Set Γ)) :
    qimg N E ≤ Subgroup.normalizer ((qimg N Y : Subgroup (QG N)) : Set (QG N)) :=
  CFSG.SignalizerFunctor.Helpers.normalizer_image_le (qmap N) _ _
    (subgroupOf_le_normalizer hEY)

theorem hypB_qimg [Finite Γ] (hYN : Y ≤ nrm N) (hY : signalizerMcBrideHypothesisB p Y) :
    signalizerMcBrideHypothesisB p (qimg N Y) := by
  obtain ⟨hp, hcop, h⟩ := signalizerMcBrideHypothesisB_iff.mp (hypB_subgroupOf hYN hY)
  exact signalizerMcBrideHypothesisB_iff.mpr ⟨hp, hcop.coprime_dvd_right
    (Subgroup.card_map_dvd _ _), fun S _ _ _ hS hnc =>
      h S (isSectionOf_of_isSectionOf_map _ _ hS) hnc⟩

theorem qimg_inf_centralizer (hp : p.Prime) (hE : IsElemAbelian p E)
    (hEY : E ≤ Subgroup.normalizer (Y : Set Γ)) (hEN : E ≤ nrm N) (hYN : Y ≤ nrm N)
    (hcop : Nat.Coprime p (Nat.card Y)) :
    qimg N (Y ⊓ Subgroup.centralizer (E : Set Γ)) =
      qimg N Y ⊓ Subgroup.centralizer ((qimg N E : Subgroup (QG N)) : Set (QG N)) := by
  have h := CFSG.SignalizerFunctor.Helpers.coprime_centralizer_image_elementary p hp (qmap N)
    (E.subgroupOf (nrm N)) (Y.subgroupOf (nrm N)) (isElemAbelian_subgroupOf hE _)
    (subgroupOf_le_normalizer hEY) (by rwa [card_subgroupOf hYN])
  rw [← subgroupOf_inf_centralizer hEN] at h
  exact h

theorem exists_surjective_fixed (hp : p.Prime) (hE : IsElemAbelian p E)
    (hEY : E ≤ Subgroup.normalizer (Y : Set Γ)) (hEN : E ≤ nrm N) (hYN : Y ≤ nrm N)
    (hcop : Nat.Coprime p (Nat.card Y)) :
    ∃ π : ↥(Y ⊓ Subgroup.centralizer (E : Set Γ)) →*
        ↥(qimg N Y ⊓ Subgroup.centralizer ((qimg N E : Subgroup (QG N)) : Set (QG N))),
      Function.Surjective π := by
  have himg := qimg_inf_centralizer hp hE hEY hEN hYN hcop
  have hle : Y ⊓ Subgroup.centralizer (E : Set Γ) ≤ nrm N := inf_le_left.trans hYN
  let π₀ : ↥(Y ⊓ Subgroup.centralizer (E : Set Γ)) →* QG N :=
    (qmap N).comp (Subgroup.inclusion hle)
  have hmem : ∀ x, π₀ x ∈ qimg N Y ⊓ Subgroup.centralizer
      ((qimg N E : Subgroup (QG N)) : Set (QG N)) := by
    intro x
    rw [← himg, mem_qimg_iff]
    exact ⟨Subgroup.inclusion hle x, x.2, rfl⟩
  refine ⟨π₀.codRestrict _ hmem, ?_⟩
  rintro ⟨z, hz⟩
  rw [← himg, mem_qimg_iff] at hz
  obtain ⟨y, hy, rfl⟩ := hz
  exact ⟨⟨(y : Γ), hy⟩, Subtype.ext rfl⟩

theorem isSolvable_of_qimg (hNY : N ≤ Y) (hYN : Y ≤ nrm N) (hN : Group.IsSolvable N)
    (hq : Group.IsSolvable (qimg N Y)) : Group.IsSolvable Y := by
  let g₀ : ↥Y →* QG N := (qmap N).comp (Subgroup.inclusion hYN)
  have hmem : ∀ y, g₀ y ∈ qimg N Y := fun y => (mem_qimg_iff N Y _).mpr
    ⟨Subgroup.inclusion hYN y, y.2, rfl⟩
  let g : ↥Y →* ↥(qimg N Y) := g₀.codRestrict _ hmem
  refine Group.isSolvable_of_ker_le_range (Subgroup.inclusion hNY) g ?_
  intro y hy
  have h1 : qmap N (Subgroup.inclusion hYN y) = 1 := congrArg Subtype.val hy
  have h2 : (Subgroup.inclusion hYN y : ↥(nrm N)) ∈ N.subgroupOf (nrm N) :=
    (QuotientGroup.eq_one_iff _).mp h1
  exact ⟨⟨(y : Γ), Subgroup.mem_subgroupOf.mp h2⟩, Subtype.ext rfl⟩

theorem isSectionOf_normal_or_qimg (hNY : N ≤ Y) (hYN : Y ≤ nrm N) {S : Type*} [Group S]
    [IsSimpleGroup S] (hS : IsSectionOf S ↥Y) :
    IsSectionOf S ↥N ∨ IsSectionOf S ↥(qimg N Y) := by
  have hN : N.subgroupOf (nrm N) ≤ Y.subgroupOf (nrm N) := fun x hx => hNY hx
  have hS' : IsSectionOf S ↥(Y.subgroupOf (nrm N)) :=
    hS.trans (IsSectionOf.of_mulEquiv (Subgroup.subgroupOfEquivOfLe hYN))
  rcases isSectionOf_normal_or_quotient (G := ↥(nrm N)) (N := N.subgroupOf (nrm N))
    (X := Y.subgroupOf (nrm N)) hN hS' with h | h
  · exact Or.inl (h.trans (IsSectionOf.of_mulEquiv
      (Subgroup.subgroupOfEquivOfLe (Subgroup.le_normalizer (H := N))).symm))
  · exact Or.inr h

end CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.AChief
