module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.LieType.CurtisTits.Recognition

public section

namespace CFSG.Quasithin

open CFSG.Assembly.LowTwoRank
open scoped commutatorElement

private theorem commutatorElement_mul_mem_center {G : Type*} [Group G] (a b : G) {z w : G}
    (hz : z ∈ Subgroup.center G) (hw : w ∈ Subgroup.center G) : ⁅a * z, b * w⁆ = ⁅a, b⁆ := by
  have hz' := Subgroup.mem_center_iff.mp hz
  have hw' := Subgroup.mem_center_iff.mp hw
  rw [commutatorElement_def, commutatorElement_def]
  calc a * z * (b * w) * (a * z)⁻¹ * (b * w)⁻¹
      = a * (b * w * z) * z⁻¹ * a⁻¹ * (b * w)⁻¹ := by rw [hz' (b * w)]; group
    _ = a * b * (w * a⁻¹) * w⁻¹ * b⁻¹ := by group
    _ = a * b * (a⁻¹ * w) * w⁻¹ * b⁻¹ := by rw [hw' a⁻¹]
    _ = a * b * a⁻¹ * b⁻¹ := by group

private theorem finite_of_isPerfect_of_finiteIndex_center (Λ : Type*) [Group Λ]
    [Group.IsPerfect Λ] [(Subgroup.center Λ).FiniteIndex] : Finite Λ := by
  have hsub : commutatorSet Λ ⊆ Set.range fun p : (Λ ⧸ Subgroup.center Λ) ×
      (Λ ⧸ Subgroup.center Λ) => ⁅p.1.out, p.2.out⁆ := by
    rintro _ ⟨a, b, rfl⟩
    obtain ⟨z, hz⟩ := QuotientGroup.mk_out_eq_mul (Subgroup.center Λ) a
    obtain ⟨w, hw⟩ := QuotientGroup.mk_out_eq_mul (Subgroup.center Λ) b
    refine ⟨(QuotientGroup.mk a, QuotientGroup.mk b), ?_⟩
    change ⁅(QuotientGroup.mk a : Λ ⧸ Subgroup.center Λ).out,
      (QuotientGroup.mk b : Λ ⧸ Subgroup.center Λ).out⁆ = ⁅a, b⁆
    rw [hz, hw]
    exact commutatorElement_mul_mem_center a b z.2 w.2
  have : Finite (commutatorSet Λ) := ((Set.finite_range _).subset hsub).to_subtype
  have hfin : Finite (commutator Λ) := inferInstance
  rw [Group.IsPerfect.commutator_eq_top] at hfin
  exact Finite.of_equiv _ Subgroup.topEquiv.toEquiv

private theorem exists_apply_ne_one_of_surjective {Λ M : Type*} [Group Λ] [Group M]
    [Nontrivial M] {φ : Λ →* M} (hφ : Function.Surjective φ) : ∃ k, φ k ≠ 1 := by
  obtain ⟨x, hx⟩ := exists_ne (1 : M)
  obtain ⟨k, rfl⟩ := hφ x
  exact ⟨k, hx⟩

private theorem card_le_card_center_mul_of_cover {G H Λ : Type*} [Group G] [Group H] [Group Λ]
    [Finite G] [Nontrivial G] [Nontrivial H] (hΛ : CFSG.IsQuasisimple Λ) {f : Λ →* G}
    {g : Λ →* H} (hf : Function.Surjective f) (hg : Function.Surjective g) :
    Nat.card G ≤ Nat.card (Subgroup.center G) * Nat.card H := by
  have hkf := CFSG.LieType.CurtisTits.ker_le_center_of_isQuasisimple hΛ
    (exists_apply_ne_one_of_surjective hf)
  have hkg := CFSG.LieType.CurtisTits.ker_le_center_of_isQuasisimple hΛ
    (exists_apply_ne_one_of_surjective hg)
  have hidx : (Subgroup.center Λ).index = ((Subgroup.center Λ).map f).index := by
    rw [← Subgroup.index_comap_of_surjective _ hf, Subgroup.comap_map_eq_self hkf]
  have hGZ : (Subgroup.center G).index ≤ (Subgroup.center Λ).index := by
    rw [hidx]
    exact Nat.le_of_dvd (Nat.pos_of_ne_zero (Subgroup.index_ne_zero_of_finite (H := _)))
      (Subgroup.index_dvd_of_le (Subgroup.map_center_le_center hf))
  have : (Subgroup.center Λ).FiniteIndex :=
    ⟨by rw [hidx]; exact Subgroup.index_ne_zero_of_finite (H := _)⟩
  have : Group.IsPerfect Λ := hΛ.1
  have := finite_of_isPerfect_of_finiteIndex_center Λ
  have hΛH : (Subgroup.center Λ).index ≤ Nat.card H := by
    have h1 : g.ker.index = Nat.card H := by
      rw [Subgroup.index_ker, MonoidHom.range_eq_top.mpr hg, Subgroup.card_top]
    rw [← h1]
    exact Nat.le_of_dvd (Nat.pos_of_ne_zero (Subgroup.index_ne_zero_of_finite (H := _)))
      (Subgroup.index_dvd_of_le hkg)
  calc Nat.card G = Nat.card (Subgroup.center G) * (Subgroup.center G).index :=
        (Subgroup.card_mul_index _).symm
    _ ≤ Nat.card (Subgroup.center G) * Nat.card H := Nat.mul_le_mul_left _ (hGZ.trans hΛH)

private theorem nontrivial_specialLinearGroup {n : Type*} [Fintype n] [DecidableEq n] {i j : n}
    (hij : i ≠ j) (F : Type*) [Field F] : Nontrivial (Matrix.SpecialLinearGroup n F) := by
  refine ⟨⟨⟨Matrix.transvection i j (1 : F), Matrix.det_transvection_of_ne i j hij 1⟩, 1,
    fun h => ?_⟩⟩
  have := congrArg (fun A : Matrix.SpecialLinearGroup n F => (A : Matrix n n F) i j) h
  simp [Matrix.transvection, Matrix.one_apply_ne hij] at this

private theorem card_center_specialLinearGroup_le {d : ℕ} (hd : 1 ≤ d) (F : Type*) [Field F] :
    Nat.card (Subgroup.center (Matrix.SpecialLinearGroup (Fin d) F)) ≤ d := by
  have : NeZero (max (Fintype.card (Fin d)) 1) := NeZero.of_pos (lt_max_of_lt_right one_pos)
  rw [Nat.card_congr Matrix.SpecialLinearGroup.center_equiv_rootsOfUnity.toEquiv]
  calc _ ≤ max (Fintype.card (Fin d)) 1 := card_rootsOfUnity _ _
    _ = d := by rw [Fintype.card_fin]; exact max_eq_left hd

private theorem card_statedSL_mul {n : ℕ} [NeZero n] (F : Type) [Field F] [Finite F] :
    Nat.card ↥(StatedSL n F) * (Nat.card F - 1) =
      ∏ i : Fin n, (Nat.card F ^ n - Nat.card F ^ (i : ℕ)) := by
  have := Fintype.ofFinite F
  rw [← Nat.card_congr (specialLinearGroupEquivStatedSL n F).toEquiv, ← Nat.card_units F,
    Matrix.card_SL_mul_card_units, Matrix.card_GL_field, Nat.card_eq_fintype_card]

private theorem three_mul_pow_four_lt_prod (q : ℕ) (hq : 2 ≤ q) :
    3 * q ^ 4 * (q - 1) < ∏ i : Fin 3, (q ^ 3 - q ^ (i : ℕ)) := by
  obtain ⟨s, rfl⟩ := Nat.exists_eq_add_of_le hq
  rw [Fin.prod_univ_three]
  simp only [Fin.val_zero, Fin.val_one, Fin.val_two, pow_zero, pow_one]
  have h0 : (2 + s) ^ 3 - 1 = s ^ 3 + 6 * s ^ 2 + 12 * s + 7 := Nat.sub_eq_of_eq_add (by ring)
  have h1 : (2 + s) ^ 3 - (2 + s) = s ^ 3 + 6 * s ^ 2 + 11 * s + 6 :=
    Nat.sub_eq_of_eq_add (by ring)
  have h2 : (2 + s) ^ 3 - (2 + s) ^ 2 = s ^ 3 + 5 * s ^ 2 + 8 * s + 4 :=
    Nat.sub_eq_of_eq_add (by ring)
  have h3 : 2 + s - 1 = s + 1 := by omega
  rw [h0, h1, h2, h3]
  have key : (s ^ 3 + 6 * s ^ 2 + 12 * s + 7) * (s ^ 3 + 6 * s ^ 2 + 11 * s + 6) *
      (s ^ 3 + 5 * s ^ 2 + 8 * s + 4) = 3 * (2 + s) ^ 4 * (s + 1) +
      (2 + s) ^ 3 * (s + 1) * (s ^ 5 + 10 * s ^ 4 + 39 * s ^ 3 + 73 * s ^ 2 + 61 * s + 15) := by
    ring
  rw [key]
  exact Nat.lt_add_of_pos_right (by positivity)

theorem d35Two_card_ge {Y : Type} [CommGroup Y] {d : ℕ} (hd : 3 ≤ d) {F : Type} [Field F] [Finite F]
    {K K' : Subgroup (MulAut Y)} (π : ↥(StatedSL d F) →* ↥K) (hπ : Function.Surjective π)
    (hπi : Function.Injective π) (hq' : CFSG.IsQuasisimple ↥K')
    (hcover : ∃ (Λ : Type) (_ : Group Λ) (f : Λ →* ↥K) (g : Λ →* ↥K'),
      CFSG.IsQuasisimple Λ ∧ Function.Surjective f ∧ Function.Surjective g) :
    Nat.card ↥(StatedSL d F) ≤ d * Nat.card ↥K' := by
  obtain ⟨Λ, _, f, g, hΛ, hf, hg⟩ := hcover
  let e₀ : ↥(StatedSL d F) ≃* ↥K := MulEquiv.ofBijective π ⟨hπi, hπ⟩
  let e : Matrix.SpecialLinearGroup (Fin d) F ≃* ↥K :=
    (specialLinearGroupEquivStatedSL d F).trans e₀
  have hij : (⟨0, by omega⟩ : Fin d) ≠ ⟨1, by omega⟩ := by simp
  have : Nontrivial (Matrix.SpecialLinearGroup (Fin d) F) := nontrivial_specialLinearGroup hij F
  have : Finite ↥K := Finite.of_equiv _ e.toEquiv
  have : Nontrivial ↥K := e.symm.toEquiv.nontrivial
  have : IsSimpleGroup (↥K' ⧸ Subgroup.center ↥K') := hq'.2.1
  have : Nontrivial ↥K' := (QuotientGroup.mk'_surjective (Subgroup.center ↥K')).nontrivial
  have hZ : Nat.card (Subgroup.center ↥K) ≤ d := by
    rw [← Nat.card_congr (Subgroup.centerCongr e).toEquiv]
    exact card_center_specialLinearGroup_le (by omega) F
  calc Nat.card ↥(StatedSL d F) = Nat.card ↥K := Nat.card_congr e₀.toEquiv
    _ ≤ Nat.card (Subgroup.center ↥K) * Nat.card ↥K' :=
        card_le_card_center_mul_of_cover hΛ hf hg
    _ ≤ d * Nat.card ↥K' := Nat.mul_le_mul_right _ hZ

theorem card_stated_gt {d m : ℕ} {F : Type} [Field F] [Finite F]
    (h : (d = 3 ∧ m = 4) ∨ (Nat.card F = 2 ∧ (d = 4 ∨ d = 5) ∧
      ∃ k : ℕ, 1 ≤ k ∧ k ≤ d - 1 ∧ m = k * k)) :
    d * Nat.card F ^ m < Nat.card ↥(StatedSL d F) := by
  rcases h with ⟨rfl, rfl⟩ | ⟨hq, hd, k, -, hkd, rfl⟩
  · have hq : 2 ≤ Nat.card F := Finite.one_lt_card
    refine lt_of_mul_lt_mul_right (a := Nat.card F - 1) ?_ (Nat.zero_le _)
    rw [card_statedSL_mul (n := 3) F]
    exact three_mul_pow_four_lt_prod _ hq
  · have hkk : k * k ≤ (d - 1) * (d - 1) := Nat.mul_le_mul hkd hkd
    rw [hq]
    rcases hd with rfl | rfl
    · have h4 : Nat.card ↥(StatedSL 4 F) = 20160 := by
        have h := card_statedSL_mul (n := 4) F
        rw [hq, Fin.prod_univ_eq_prod_range (fun i => 2 ^ 4 - 2 ^ i) 4] at h
        simpa [Finset.prod_range_succ] using h
      rw [h4]
      calc 4 * 2 ^ (k * k) ≤ 4 * 2 ^ 9 :=
            Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by norm_num) (by simpa using hkk))
        _ < 20160 := by norm_num
    · have h5 : Nat.card ↥(StatedSL 5 F) = 9999360 := by
        have h := card_statedSL_mul (n := 5) F
        rw [hq, Fin.prod_univ_eq_prod_range (fun i => 2 ^ 5 - 2 ^ i) 5] at h
        simpa [Finset.prod_range_succ] using h
      rw [h5]
      calc 5 * 2 ^ (k * k) ≤ 5 * 2 ^ 16 :=
            Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by norm_num) (by simpa using hkk))
        _ < 9999360 := by norm_num

end CFSG.Quasithin
