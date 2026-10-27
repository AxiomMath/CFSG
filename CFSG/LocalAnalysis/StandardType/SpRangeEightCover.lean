module

public import CFSG.LocalAnalysis.StandardType.SpCentralizerEightCover
public import CFSG.LocalAnalysis.StandardType.AlternatingEightCoverElements
public import CFSG.Assembly.Subnormal

public section

namespace CFSG.StandardType

namespace SpFixed

open CFSG.Open (StatedSp)

theorem IsAlternatingEightCover.of_mulEquiv {J J' : Type*} [Group J] [Group J'] (e : J ≃* J')
    (h : IsAlternatingEightCover J) : IsAlternatingEightCover J' := by
  obtain ⟨hperf, ⟨eA⟩, hZ⟩ := h
  refine ⟨?_, ⟨?_, ?_⟩⟩
  · have hmap : (commutator J).map e.toMonoidHom = commutator J' := by
      rw [_root_.commutator_def, Subgroup.map_commutator,
        Subgroup.map_top_of_surjective _ e.surjective]
      rfl
    rw [← hmap, hperf, Subgroup.map_top_of_surjective _ e.surjective]
  · exact ⟨(QuotientGroup.congr (Subgroup.center J) (Subgroup.center J') e
        (Subgroup.map_center_eq e)).symm.trans eA⟩
  · exact hZ.of_equiv (Subgroup.centerCongr e)

section Pullback

variable {G H : Type*} [Group G] [Group H] {ψ : G →* H}

theorem card_comap_eq_of_le_range (hψ : Function.Injective ψ) {D : Subgroup H} (hD : D ≤ ψ.range) :
    Nat.card (D.comap ψ) = Nat.card D := by
  have hmap : (D.comap ψ).map ψ = D := by
    rw [Subgroup.map_comap_eq, inf_eq_right.2 hD]
  calc Nat.card (D.comap ψ)
      = Nat.card ((D.comap ψ).map ψ) :=
        Nat.card_congr (Subgroup.equivMapOfInjective (D.comap ψ) ψ hψ).toEquiv
    _ = Nat.card D := by rw [hmap]

theorem comap_range_inf_centralizer (hψ : Function.Injective ψ) {D : Subgroup H}
    (hD : D ≤ ψ.range) :
    (ψ.range ⊓ Subgroup.centralizer (D : Set H)).comap ψ =
      Subgroup.centralizer ((D.comap ψ : Subgroup G) : Set G) := by
  ext x
  rw [Subgroup.mem_comap, Subgroup.mem_inf, Subgroup.mem_centralizer_iff,
    Subgroup.mem_centralizer_iff]
  constructor
  · rintro ⟨-, hx⟩ y hy
    exact hψ (by rw [map_mul, map_mul, hx (ψ y) hy])
  · rintro hx
    refine ⟨⟨x, rfl⟩, ?_⟩
    intro h hh
    obtain ⟨y, rfl⟩ := hD hh
    have hy : y ∈ D.comap ψ := by rwa [Subgroup.mem_comap]
    simpa only [map_mul] using congrArg ψ (hx y hy)

noncomputable def mulEquivComapOfLeRange (hψ : Function.Injective ψ) {J : Subgroup H}
    (hJ : J ≤ ψ.range) : ↥(J.comap ψ) ≃* ↥J :=
  (Subgroup.equivMapOfInjective (J.comap ψ) ψ hψ).trans
    (MulEquiv.subgroupCongr (by rw [Subgroup.map_comap_eq, inf_eq_right.2 hJ]))

end Pullback

variable {F : Type} [Field F] [Finite F] [CharP F 2] {n : ℕ} {G : Type} [Group G] [Finite G]

theorem false_of_isSubnormal_range_inf_centralizer_eightCover
    (hn : n ≤ 4 ∨ (n = 5 ∧ 3 ∣ Nat.card F + 1)) (ψ : StatedSp n F →* G)
    (hψ : Function.Injective ψ) {D J : Subgroup G} (hD : D ≤ ψ.range) (hDc : Nat.card D = 9)
    (hcomm : ∀ a ∈ D, ∀ b ∈ D, a * b = b * a) (hexp : ∀ a ∈ D, a ^ 3 = 1)
    (hJ : CFSG.Assembly.IsSubnormal J (ψ.range ⊓ Subgroup.centralizer (D : Set G)))
    (hA : IsAlternatingEightCover ↥J) : False := by
  have hJr : J ≤ ψ.range := hJ.le.trans inf_le_left
  refine false_of_isSubnormal_centralizer_eightCover hn (D.comap ψ)
    ((card_comap_eq_of_le_range hψ hD).trans hDc) ?_ ?_ ?_
    (IsAlternatingEightCover.of_mulEquiv (mulEquivComapOfLeRange hψ hJr).symm hA)
  · intro a ha b hb
    exact hψ (by rw [map_mul, map_mul]; exact hcomm _ ha _ hb)
  · intro a ha
    exact hψ (by rw [map_pow, map_one]; exact hexp _ ha)
  · rw [← comap_range_inf_centralizer hψ hD]
    exact hJ.comap ψ

end SpFixed

end CFSG.StandardType
