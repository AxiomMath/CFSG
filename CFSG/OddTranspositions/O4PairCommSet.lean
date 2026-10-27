module

public import CFSG.OddTranspositions.O4PairTenAbstract
public import CFSG.OddTranspositions.O4CloseReduction

public section

namespace CFSG.OddTranspositions.QZ

open CFSG.Timmesfeld.Bridge

variable {G : Type} [Group G] {D : Set G}

private theorem y_ne_base (i : Fin 10) : y i ≠ SemidirectProduct.inr frob25 := by
  intro h
  have hc := y_commuting_others i
  have hall : Nat.card {j : Fin 10 // j ≠ i ∧ Commute (y i) (y j)} =
      Nat.card {j : Fin 10 // j ≠ i} :=
    Nat.card_congr (Equiv.subtypeEquivRight fun j =>
      ⟨fun h' => h'.1, fun h' => ⟨h', by rw [h]; exact (y_commute_base j).symm⟩⟩)
  rw [hall, Nat.card_eq_fintype_card] at hc
  fin_cases i <;> revert hc <;> decide

theorem commSet_class65_eq :
    commSet class65 (SemidirectProduct.inr frob25) = Set.range y := by
  ext x
  constructor
  · rintro ⟨h1, h2, h3⟩
    have hx : x ∈ insert (SemidirectProduct.inr frob25) (Set.range y) := by
      rw [← commuting_class65_eq]
      exact ⟨h1, h2⟩
    rcases hx with hx | hx
    · exact absurd hx h3
    · exact hx
  · rintro ⟨i, rfl⟩
    exact ⟨y_mem_class65 i, y_commute_base i, y_ne_base i⟩

theorem exists_mulEquiv_of_mem (hO4 : O4PairData G D) {d : G} (hd : d ∈ D) :
    ∃ φ : G ≃* PSigmaL225, φ '' D = class65 ∧ φ d = SemidirectProduct.inr frob25 := by
  obtain ⟨e, he⟩ := hO4
  have hed : e d ∈ class65 := he ▸ ⟨d, hd, rfl⟩
  obtain ⟨k, hk⟩ := isConj_iff.mp hed
  set φ : G ≃* PSigmaL225 := e.trans (MulAut.conj k⁻¹) with hφ
  have hφapp : ∀ x : G, φ x = k⁻¹ * e x * k := fun x => by
    rw [hφ, MulEquiv.trans_apply, MulAut.conj_apply, inv_inv]
  refine ⟨φ, ?_, by rw [hφapp, ← hk]; group⟩
  ext x
  constructor
  · rintro ⟨z, hz, rfl⟩
    have hez : e z ∈ class65 := he ▸ ⟨z, hz, rfl⟩
    rw [hφapp]
    exact hez.trans (isConj_iff.mpr ⟨k⁻¹, by group⟩)
  · intro hx
    have hx' : k * x * k⁻¹ ∈ class65 := hx.trans (isConj_iff.mpr ⟨k, rfl⟩)
    rw [← he] at hx'
    obtain ⟨z, hz, hzx⟩ := hx'
    refine ⟨z, hz, ?_⟩
    rw [hφapp, hzx]
    group

theorem image_commSet_eq_range_y {φ : G ≃* PSigmaL225} (hφD : φ '' D = class65) {d : G}
    (hφd : φ d = SemidirectProduct.inr frob25) : φ '' commSet D d = Set.range y := by
  rw [← commSet_class65_eq]
  ext x
  constructor
  · rintro ⟨z, ⟨hzD, hzc, hzne⟩, rfl⟩
    refine ⟨hφD ▸ ⟨z, hzD, rfl⟩, ?_, ?_⟩
    · rw [← hφd]
      exact hzc.map φ
    · rw [← hφd]
      exact fun h => hzne (φ.injective h)
  · rintro ⟨hx, hxc, hxne⟩
    rw [← hφD] at hx
    obtain ⟨z, hzD, rfl⟩ := hx
    refine ⟨z, ⟨hzD, ?_, fun h => hxne (by rw [h, hφd])⟩, rfl⟩
    rw [← hφd] at hxc
    have := hxc.map φ.symm
    simpa using this

theorem ncard_commSet_of_o4PairData (hO4 : O4PairData G D) {d : G} (hd : d ∈ D) :
    (commSet D d).ncard = 10 := by
  obtain ⟨φ, hφD, hφd⟩ := exists_mulEquiv_of_mem hO4 hd
  rw [← Set.ncard_image_of_injective _ φ.injective, image_commSet_eq_range_y hφD hφd,
    Set.ncard_range_of_injective y_injective, Nat.card_fin]

end CFSG.OddTranspositions.QZ
