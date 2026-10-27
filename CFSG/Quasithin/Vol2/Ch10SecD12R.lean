module

public import CFSG.Quasithin.Vol2.Ch10SecD12Q

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecD

open CFSG.Open CFSG.Blueprint CFSG.Quasithin.H13 CFSG.QuasithinUnique CFSG.Quasithin.E3
open scoped IsMulCommutative

variable {G : Type} [Group G] [Finite G] {T L I : Subgroup G}

theorem data_of_bound (h : Hyp10 G T L I) {m a0 r0 : ℕ}
    (hcard : Nat.card ↥(fsuUL T L I) =
      2 ^ m * Nat.card ↥(fsuUL T L I ⊓ Subgroup.centralizer (fsuL0 T L : Set G)))
    (hc : Nat.card ↥(fsuUL T L I ⊓ Subgroup.centralizer (fsuL0 T L : Set G)) < 2 ^ m)
    (hr : ∀ E : Subgroup G, E ≤ fsuM T L ⊓ Subgroup.normalizer (fsuUL T L I : Set G) →
      IsElemAbelian 2 E → mQuot E (E ⊓ Subgroup.centralizer (fsuUL T L I : Set G)) ≤ r0)
    (hrm : r0 < m)
    (ha : ∀ E : Subgroup G, E ≤ fsuM T L ⊓ Subgroup.normalizer (fsuUL T L I : Set G) →
      IsElemAbelian 2 E → ¬ E ≤ Subgroup.centralizer (fsuUL T L I : Set G) → ∀ q : ℕ,
      (∀ B : Subgroup G, B ≤ E → mQuot E B < q →
        fsuUL T L I ⊓ Subgroup.centralizer (B : Set G) =
          fsuUL T L I ⊓ Subgroup.centralizer (E : Set G)) → q ≤ a0) :
    Data10212 T L I m a0 r0 := by
  have hm : mQuot (fsuUL T L I) (fsuUL T L I ⊓ Subgroup.centralizer (fsuL0 T L : Set G)) = m := by
    have h1 := card_eq_two_pow_mul (V := fsuUL T L I)
      ((SecA.isPGroup_fsuVM h).to_le V1_le_V) (inf_le_left :
        fsuUL T L I ⊓ Subgroup.centralizer (fsuL0 T L : Set G) ≤ fsuUL T L I)
    have hpos : 0 < Nat.card ↥(fsuUL T L I ⊓ Subgroup.centralizer (fsuL0 T L : Set G)) :=
      Nat.card_pos
    rw [hcard] at h1
    exact Nat.pow_right_injective (le_refl 2) (Nat.eq_of_mul_eq_mul_right hpos h1).symm
  exact ⟨hm.ge, hr, ha, fix_of_card h hm.ge hc, hrm⟩

theorem card_of_realizes_nat {V : Type*} [CommGroup V] {ι : Type} [Fintype ι] [DecidableEq ι]
    {K : Type} [Field K] [Finite K] {Γ : Subgroup (Matrix.GeneralLinearGroup ι K)}
    {H : Subgroup (MulAut V)} {U Z : Subgroup V} (h : (FFModel.nat Γ).Realizes H U Z) :
    Nat.card U = Nat.card K ^ Fintype.card ι * Nat.card Z := by
  obtain ⟨π, hπ⟩ := h
  have hZU : Z ≤ U := hπ.2.1
  obtain ⟨β, hβs, hβk, -⟩ := FFModel.RealizesVia.coord rfl rfl hπ
  have h1 := B1More.card_map_mul_card_inf_ker (⊤ : Subgroup ↥U) β
  rw [Subgroup.map_top, MonoidHom.range_eq_top.mpr hβs, top_inf_eq, Subgroup.card_top,
    Subgroup.card_top] at h1
  have h2 : Nat.card (FFModel.nat Γ).Amb = Nat.card K ^ Fintype.card ι := by
    show Nat.card (ι → K) = _
    rw [Nat.card_fun, Nat.card_eq_fintype_card (α := ι)]
  have h3 : Nat.card β.ker = Nat.card Z :=
    Nat.card_congr ⟨fun u => ⟨u.1.1, (hβk u.1).1 u.2⟩, fun z => ⟨⟨z.1, hZU z.2⟩, (hβk _).2 z.2⟩,
      fun _ => rfl, fun _ => rfl⟩
  rw [← h2, ← h3, h1]

omit [Finite G] in
theorem card_inf_eq_one (hc : fsuCVM T L I = ⊥) :
    Nat.card ↥(fsuUL T L I ⊓ Subgroup.centralizer (fsuL0 T L : Set G)) = 1 := by
  rw [Subgroup.card_eq_one, eq_bot_iff, ← hc]
  exact fun x hx => ⟨V1_le_V hx.1, hx.2⟩

theorem data_one (hF : Fact12L2) (h37 : Vol2Native.A37ForSQTKCat)
    (h38 : Vol2Native.A38ForSQTKCat) (hI16 : ASInputs.AS_I_1_6) (h : Hyp10 G T L I) {n : ℕ}
    (h1 : Case10_1_1One T L I n) : Data10212 T L I (2 * n) n n := by
  obtain ⟨hn, -, hcomm, hnat⟩ := h1
  have hfix := fixV_autOn_V1 h37 h38 h
  have hcV : Nat.card ↥(cV1 T L I) =
      Nat.card ↥(fsuUL T L I ⊓ Subgroup.centralizer (fsuL0 T L : Set G)) := by
    rw [cV1, card_subgroupOf_eq, inf_comm]
  have hcard : Nat.card ↥(fsuUL T L I) = 2 ^ (2 * n) *
      Nat.card ↥(fsuUL T L I ⊓ Subgroup.centralizer (fsuL0 T L : Set G)) := by
    obtain ⟨K, _, _, hK, hreal⟩ := hnat
    have := card_of_realizes_nat hreal
    rw [Subgroup.card_top, hK, Fintype.card_fin, hcV, ← pow_mul, mul_comm n 2] at this
    exact this
  rw [← hfix] at hnat
  have hle := (hI16 (↥(fsuUL T L I)) (SecC.sq_eq_one_fsuUL h) (autOn L (fsuUL T L I)) n).1
    (SecC.commV_autOn_fsuUL h) (Or.inr (Or.inr (Or.inl ⟨n, hn, rfl, hnat⟩)))
  rw [hfix, hcV] at hle
  have hb := hF _ (SecC.sq_eq_one_fsuUL h) _ n hn (SecC.commV_autOn_fsuUL h) hnat
  have hr := rank_le_of_bound h37 h38 h hb
  have hlt : 2 ^ n < 2 ^ (2 * n) := Nat.pow_lt_pow_right (by norm_num) (by omega)
  exact data_of_bound h hcard (by omega) hr (by omega) (a_le_of_rank_le hr)

theorem data_two (hF : Fact12A5) (h37 : Vol2Native.A37ForSQTKCat)
    (h38 : Vol2Native.A38ForSQTKCat) (h : Hyp10 G T L I) (h2 : Case10_1_1Two T L I)
    (hc : fsuCVM T L I = ⊥) : Data10212 T L I 4 1 2 := by
  obtain ⟨-, hcomm, halt⟩ := h2
  have hfix : fixV (autOn L (fsuUL T L I)) = ⊥ := by
    rw [fixV_autOn_V1 h37 h38 h, cV1_eq_bot hc]
  obtain ⟨hcard, hb, ha⟩ := hF _ (SecC.sq_eq_one_fsuUL h) _ (SecC.commV_autOn_fsuUL h) hfix halt
  have hr := rank_le_of_bound h37 h38 h hb
  refine data_of_bound h (by rw [hcard, card_inf_eq_one hc, mul_one])
    (by rw [card_inf_eq_one hc]; norm_num)
    hr (by norm_num) (a_le_of_bound h37 h38 h ha)

theorem data_four (hF : Fact12O4) (h37 : Vol2Native.A37ForSQTKCat)
    (h38 : Vol2Native.A38ForSQTKCat) (h : Hyp10 G T L I) {n : ℕ} (h4 : Case10_1_1Four T L I n)
    (hc : fsuCVM T L I = ⊥) : Data10212 T L I (4 * n) (2 * n) (2 * n) := by
  obtain ⟨hn, -, hcomm, hort⟩ := h4
  have hfix : fixV (autOn L (fsuUL T L I)) = ⊥ := by
    rw [fixV_autOn_V1 h37 h38 h, cV1_eq_bot hc]
  obtain ⟨hcard, hb⟩ := hF _ (SecC.sq_eq_one_fsuUL h) _ n hn (SecC.commV_autOn_fsuUL h) hfix hort
  have hr := rank_le_of_bound h37 h38 h hb
  have h1 : 1 < 2 ^ (4 * n) := Nat.one_lt_pow (by omega) (by norm_num)
  exact data_of_bound h (by rw [hcard, card_inf_eq_one hc, mul_one])
    (by rw [card_inf_eq_one hc]; exact h1) hr (by omega) (a_le_of_rank_le hr)

theorem data_seven (hF : Fact12Sz) (h37 : Vol2Native.A37ForSQTKCat)
    (h38 : Vol2Native.A38ForSQTKCat) (h : Hyp10 G T L I) (h7 : Case10_1_1Seven T L I)
    (hc : fsuCVM T L I = ⊥) : ∃ n : ℕ, 3 ≤ n ∧ Data10212 T L I (4 * n) n n := by
  obtain ⟨n, -, hcomm, hsz⟩ := h7
  have hfix : fixV (autOn L (fsuUL T L I)) = ⊥ := by
    rw [fixV_autOn_V1 h37 h38 h, cV1_eq_bot hc]
  have hb := hF _ (SecC.sq_eq_one_fsuUL h) _ n (SecC.commV_autOn_fsuUL h) hfix hsz
  obtain ⟨a, ha, rfl, K, _, _, hK, hreal⟩ := hsz
  have hcard : Nat.card ↥(fsuUL T L I) = 2 ^ (4 * (2 * a + 1)) := by
    have := card_of_realizes_nat hreal
    rw [Subgroup.card_top, hK, Fintype.card_fin, Subgroup.card_bot, mul_one, ← pow_mul,
      mul_comm (2 * a + 1) 4] at this
    exact this
  have hr := rank_le_of_bound h37 h38 h hb
  have h1 : 1 < 2 ^ (4 * (2 * a + 1)) := Nat.one_lt_pow (by omega) (by norm_num)
  exact ⟨2 * a + 1, by omega, data_of_bound h (by rw [hcard, card_inf_eq_one hc, mul_one])
    (by rw [card_inf_eq_one hc]; exact h1) hr (by omega) (a_le_of_rank_le hr)⟩

end CFSG.Quasithin.Vol2.Ch10.SecD
