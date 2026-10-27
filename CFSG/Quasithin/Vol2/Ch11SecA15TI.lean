module

public import CFSG.Quasithin.Vol2.Ch11SecA15Three
public import CFSG.Quasithin.Vol2.Ch11SecA15M

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecA

open CFSG.Open CFSG.Blueprint CFSG.Quasithin.H13 CFSG.QuasithinUnique

variable {G : Type} [Group G] [Finite G] {T L I : Subgroup G} {n : ℕ}

theorem conj_le_L (h1104 : Stmt11_0_4) (h1102 : Stmt11_0_2) (h : Hyp11 G T L I n)
    (hk : KindSL3 L (fsuV T I) n ∨ KindSp4 L (fsuV T I) n) (hVM : fsuV T I = VM T L I) {y : G}
    (hy : L.map (MulAut.conj y).toMonoidHom ≤ Subgroup.normalizer (L : Set G)) :
    L.map (MulAut.conj y).toMonoidHom ≤ L := by
  obtain ⟨h1, h2⟩ := h1104 G T L I n h
  rcases hk with hk | hk
  · by_cases hn3 : 3 ≤ n
    · obtain ⟨p, hp, hpd, hp3⟩ := exists_prime_gt_three_dvd hn3
      exact conj_le_of_oPrimeResidualOf_eq (h1 p hp (Or.inr ⟨hk, hpd, hp3⟩)) hy
    · have hn2 : n = 2 := by have := h.one_lt; omega
      exact conj_le_of_order_three
        (fun x hx hx3 => h2 hk (by rw [hn2]; exact even_two) x hx hx3 (Or.inr (Or.inr hVM)))
        (eq_closure_order_three h1102 h hk hn2) hy
  · exact conj_le_of_oPrimeResidualOf_eq
      (h1 3 Nat.prime_three (Or.inl ⟨Or.inl hk, three_dvd_two_pow_two_mul_sub_one n⟩)) hy

omit [Finite G] in
theorem mem_normalizer_of_map_conj_le [Finite G] {L : Subgroup G} {y : G}
    (hy : L.map (MulAut.conj y).toMonoidHom ≤ L) : y ∈ Subgroup.normalizer (L : Set G) := by
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  apply Subgroup.eq_of_le_of_card_ge hy
  rw [Subgroup.card_map_of_injective (MulAut.conj y).injective]

theorem mem_normalizer_of_inf_ne_bot (h4213 : TmpL6_4_2_13) (h1104 : Stmt11_0_4)
    (hG2 : FactG2DerivedOrder) (h331 : Stmt3_3_1) (h1102 : Stmt11_0_2) (h : Hyp11 G T L I n)
    (hk : KindSL3 L (fsuV T I) n ∨ KindSp4 L (fsuV T I) n) (hVM : fsuV T I = VM T L I)
    {C : Subgroup G} (hC2 : IsPGroup 2 C) (hCL : C ≤ Subgroup.centralizer (L : Set G)) {y : G}
    (hW : C ⊓ C.map (MulAut.conj y).toMonoidHom ≠ ⊥) :
    y ∈ Subgroup.normalizer (L : Set G) := by
  set W := C ⊓ C.map (MulAut.conj y).toMonoidHom with hWdef
  have hW2 : IsPGroup 2 W := hC2.to_le inf_le_left
  have hLW : L ≤ Subgroup.normalizer (W : Set G) :=
    (Subgroup.le_centralizer_iff.mp hCL).trans
      ((Subgroup.centralizer_le fun x hx => (inf_le_left : W ≤ C) hx).trans
        (Subgroup.centralizer_le_normalizer _))
  have hLyW : L.map (MulAut.conj y).toMonoidHom ≤ Subgroup.normalizer (W : Set G) := by
    refine le_trans ?_ (Subgroup.centralizer_le_normalizer _)
    rintro _ ⟨x, hx, rfl⟩
    rw [Subgroup.mem_centralizer_iff]
    rintro _ ⟨-, ⟨c, hc, rfl⟩⟩
    have hxc : c * x = x * c := (Subgroup.mem_centralizer_iff.mp (hCL hc) x hx).symm
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    calc y * c * y⁻¹ * (y * x * y⁻¹) = y * (c * x) * y⁻¹ := by group
      _ = y * (x * c) * y⁻¹ := by rw [hxc]
      _ = y * x * y⁻¹ * (y * c * y⁻¹) := by group
  have hUM := isUniqueM_L' h4213 hG2 h331 h1102 h
  obtain ⟨M', hM', hle⟩ := exists_maxTwoLocal_ge (⟨W, hW, hW2, rfl⟩ : IsTwoLocal _)
  have hM := hUM.2 M' ⟨hM', hLW.trans hle⟩
  exact mem_normalizer_of_map_conj_le
    (conj_le_L h1104 h1102 h hk hVM (hM ▸ (hLyW.trans hle)))

end CFSG.Quasithin.Vol2.Ch11.SecA
