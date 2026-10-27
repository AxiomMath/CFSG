module

public import CFSG.Quasithin.Background.A3StructureDefs
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitLift
public import CFSG.Sporadic.J1

public section

namespace CFSG.Quasithin

private theorem isPGroup_two_of_comm_sq {X : Type} [Group X] (E : Subgroup X)
    (hc : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a) (hsq : ∀ a ∈ E, a ^ 2 = 1) : IsPGroup 2 E := by
  have : IsMulCommutative E := ⟨⟨fun a b => Subtype.ext (hc a a.2 b b.2)⟩⟩
  have : IsElementaryAbelian 2 E :=
    ⟨Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr fun a => Subtype.ext (by simpa using hsq a a.2)⟩
  exact IsElementaryAbelian.isPGroup 2 E

private theorem card_le_four_of_dihedral_sq {m : ℕ} [NeZero m]
    (E : Subgroup (DihedralGroup (2 * m))) (hE : ∀ x ∈ E, x * x = 1) : Nat.card E ≤ 4 := by
  classical
  have hr : ∀ j : ZMod (2 * m), DihedralGroup.r j ∈ E → j = 0 ∨ j = (m : ZMod (2 * m)) := by
    intro j hj
    have h := hE _ hj
    rw [DihedralGroup.r_mul_r, DihedralGroup.one_def, DihedralGroup.r.injEq, ← two_mul] at h
    exact (CFSG.GroupTheory.two_mul_eq_zero_iff_zmod j).mp h
  have hle : ∀ F : Finset (DihedralGroup (2 * m)), (∀ x ∈ E, x ∈ F) → Nat.card E ≤ F.card := by
    intro F hF
    have h1 := Nat.card_le_card_of_injective (fun x : E => (⟨x, hF x x.2⟩ : F))
      fun a b hab => Subtype.ext (by simpa using hab)
    rwa [Nat.card_eq_finsetCard] at h1
  by_cases hs : ∃ i, DihedralGroup.sr i ∈ E
  · obtain ⟨i, hi⟩ := hs
    refine (hle {DihedralGroup.r 0, DihedralGroup.r (m : ZMod (2 * m)), DihedralGroup.sr i,
      DihedralGroup.sr (i + (m : ZMod (2 * m)))} fun x hx => ?_).trans Finset.card_le_four
    cases x with
    | r j => rcases hr j hx with rfl | rfl <;> simp
    | sr j =>
      rcases hr (j - i) (by rw [← DihedralGroup.sr_mul_sr]; exact E.mul_mem hi hx) with h | h
      · rw [sub_eq_zero.mp h]
        simp
      · rw [sub_eq_iff_eq_add.mp h, add_comm]
        simp
  · push Not at hs
    refine (hle {DihedralGroup.r 0, DihedralGroup.r (m : ZMod (2 * m))} fun x hx => ?_).trans
      (Finset.card_le_two.trans (by norm_num))
    cases x with
    | r j => rcases hr j hx with rfl | rfl <;> simp
    | sr j => exact absurd hx (hs j)

theorem card_le_eight_of_isSporadic_J1 {X : Type} [Group X]
    (h : IsSporadic .J1 X)
    (E : Subgroup X) (hc : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a) (hsq : ∀ a ∈ E, a ^ 2 = 1) :
    Nat.card E ≤ 8 := by
  obtain ⟨e⟩ := h
  have hcard : Nat.card X = 175560 := by
    rw [Nat.card_congr e.toEquiv]
    exact CFSG.Sporadic.J1.card_J1
  have : Finite X := Nat.finite_of_card_ne_zero (by rw [hcard]; norm_num)
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp (isPGroup_two_of_comm_sq E hc hsq)
  have hdvd : Nat.card E ∣ Nat.card X := Subgroup.card_subgroup_dvd_card E
  rw [hk, hcard] at hdvd
  have hk3 : k ≤ 3 := by
    by_contra hk3
    have h4 : 2 ^ 4 ∣ 2 ^ k := pow_dvd_pow 2 (by omega)
    have := h4.trans hdvd
    norm_num at this
  rw [hk]
  calc 2 ^ k ≤ 2 ^ 3 := Nat.pow_le_pow_right (by norm_num) hk3
    _ = 8 := by norm_num

theorem card_le_four_of_isPSL_two {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {X : Type} [Group X]
    (h : IsPSL 2 p 1 X) (E : Subgroup X) (hc : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a)
    (hsq : ∀ a ∈ E, a ^ 2 = 1) : Nat.card E ≤ 4 := by
  obtain ⟨-, -, -, F, _, _, hF, ⟨e⟩⟩ :=
    CFSG.ComponentClassification.HarrisLit.exists_psl2_of_lieModel
      (Or.inl ⟨by decide, h⟩ : CFSG.Blueprint.LieModel X .PSL 2 p 1)
  have : Finite X := Finite.of_equiv _ e.symm.toEquiv
  have hD := CFSG.ComponentClassification.HarrisLit.hasDihedralSylowTwo_of_mulEquiv e
    (CFSG.GorensteinWalter.psl2_odd_hasDihedralSylowTwo_model F
      ⟨p, 1, hp, hp.odd_of_ne_two hp2, le_rfl, hF⟩)
  obtain ⟨S, hES⟩ := (isPGroup_two_of_comm_sq E hc hsq).exists_le_sylow
  obtain ⟨m, hm, ⟨eS⟩⟩ := hD S
  obtain ⟨k, hk⟩ : ∃ k, 2 ^ m = 2 * k := ⟨2 ^ (m - 1), by rw [← pow_succ', Nat.sub_add_cancel hm]⟩
  have : NeZero k := ⟨by rintro rfl; simp at hk⟩
  rw [hk] at eS
  have hE' : ∀ x ∈ (E.subgroupOf (S : Subgroup X)).map eS.toMonoidHom, x * x = 1 := by
    rintro _ ⟨b, hb, rfl⟩
    rw [← map_mul]
    have : b * b = 1 := Subtype.ext (by simpa [pow_two] using hsq b.1 hb)
    simp [this]
  have hcard : Nat.card ((E.subgroupOf (S : Subgroup X)).map eS.toMonoidHom) = Nat.card E := by
    rw [Subgroup.card_map_of_injective eS.injective]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hES).toEquiv
  rw [← hcard]
  exact card_le_four_of_dihedral_sq _ hE'

end CFSG.Quasithin
