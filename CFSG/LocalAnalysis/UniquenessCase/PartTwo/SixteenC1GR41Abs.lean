module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenDefsB

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

theorem s16c1G_isSym_congr {X Y : Type} [Group X] [Group Y] (e : X ≃* Y) {n : ℕ}
    (h : IsSym X n) : IsSym Y n := by
  obtain ⟨e'⟩ := h
  exact ⟨e.symm.trans e'⟩

theorem s16c1G_isSym_of_faithful {X : Type} [Group X] [Finite X] {Y : Type} [Fintype Y]
    [DecidableEq Y] {n : ℕ} (hY : Fintype.card Y = n) (ρ : X →* Equiv.Perm Y)
    (hinj : Function.Injective ρ) (hcard : Nat.card X = n.factorial) : IsSym X n := by
  let e : Y ≃ Fin n := Fintype.equivFinOfCardEq hY
  let ρ' : X →* Equiv.Perm (Fin n) := e.permCongrHom.toMonoidHom.comp ρ
  have hinj' : Function.Injective ρ' := e.permCongrHom.injective.comp hinj
  have hcard' : Nat.card (Equiv.Perm (Fin n)) ≤ Nat.card X := by
    rw [Nat.card_perm, Nat.card_eq_fintype_card, Fintype.card_fin, hcard]
  exact ⟨MulEquiv.ofBijective ρ' ⟨hinj', (hinj'.bijective_of_nat_card_le hcard').2⟩⟩

theorem s16c1G_isE16A5_congr {X Y : Type} [Group X] [Group Y] (e : X ≃* Y)
    (h : IsE16A5 X) : IsE16A5 Y := by
  obtain ⟨N, hN, hel, ⟨hQ⟩⟩ := h
  haveI : (N.map e.toMonoidHom).Normal := hN.map e.toMonoidHom e.surjective
  refine ⟨N.map e.toMonoidHom, inferInstance, ?_, ?_⟩
  · obtain ⟨φ⟩ := hel
    exact ⟨(N.equivMapOfInjective e.toMonoidHom e.injective).symm.trans φ⟩
  · exact ⟨(QuotientGroup.congr N (N.map e.toMonoidHom) e rfl).symm.trans hQ⟩

theorem s16c1G_isE16A5_of_hom {X : Type} [Group X] [Finite X] {Y : Type} [Fintype Y]
    [DecidableEq Y] (hY : Fintype.card Y = 5) (ρ : X →* Equiv.Perm Y)
    (hker : IsElemAbelianOfRank 2 4 ↥ρ.ker) (hcard : Nat.card X = 960) : IsE16A5 X := by
  classical
  have hk16 : Nat.card ρ.ker = 16 := by
    obtain ⟨φ⟩ := hker
    rw [Nat.card_congr φ.toEquiv,
      Nat.card_congr (Multiplicative.toAdd : Multiplicative (Fin 4 → ZMod 2) ≃ _)]
    simp [Nat.card_eq_fintype_card]
  have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup ρ.ker
  have h2 : Nat.card (X ⧸ ρ.ker) = Nat.card ρ.range :=
    Nat.card_congr (QuotientGroup.quotientKerEquivRange ρ).toEquiv
  rw [hcard, hk16, h2] at h1
  have hr : Nat.card ρ.range = 60 := by omega
  have hperm : Nat.card (Equiv.Perm Y) = 120 := by
    rw [Nat.card_perm, Nat.card_eq_fintype_card, hY]
    decide
  have hidx : ρ.range.index = 2 := by
    have h3 := Subgroup.index_mul_card ρ.range
    rw [hr, hperm] at h3
    omega
  have hrange : ρ.range = alternatingGroup Y :=
    Equiv.Perm.eq_alternatingGroup_of_index_eq_two hidx
  refine ⟨ρ.ker, ρ.normal_ker, hker, ?_⟩
  exact ⟨((QuotientGroup.quotientKerEquivRange ρ).trans (MulEquiv.subgroupCongr hrange)).trans
    (Equiv.altCongrHom (Fintype.equivFinOfCardEq hY))⟩

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
