module

public import CFSG.Quasithin.Vol2.Ch8InputsB
public import CFSG.Quasithin.Vol2.Ch7Setup
public import CFSG.Quasithin.Background.HL3WrNPrime
public import CFSG.Quasithin.Background.HL3WrMParam
public import CFSG.Quasithin.Background.E6Hyp
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.ReducedImage
public import CFSG.Quasithin.Background.B3Four2

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Quasithin.H CFSG.Quasithin.H.L3Wr
open scoped IsMulCommutative Matrix

section Sylow

variable {G : Type} [Group G] [Finite G]

theorem card_autOn_inf_of_sylow {T H V : Subgroup G} (hT : IsSylowIn 2 T ⊤)
    (hTH : T ≤ Subgroup.normalizer (H : Set G)) (hTV : T ≤ Subgroup.normalizer (V : Set G)) :
    Nat.card ↥(autOn (T ⊓ H) V) = 2 ^ (Nat.card ↥(autOn H V)).factorization 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set N₀ := H ⊓ Subgroup.normalizer (V : Set G) with hN₀
  have hTN₀ : T ≤ Subgroup.normalizer (N₀ : Set G) := by
    intro t ht
    rw [Subgroup.mem_normalizer_iff]
    intro x
    have htV : t ∈ Subgroup.normalizer (V : Set G) := hTV ht
    constructor
    · rintro ⟨hxH, hxV⟩
      exact ⟨(Subgroup.mem_normalizer_iff.mp (hTH ht) x).mp hxH,
        Subgroup.mul_mem _ (Subgroup.mul_mem _ htV hxV) (Subgroup.inv_mem _ htV)⟩
    · rintro ⟨hxH, hxV⟩
      refine ⟨(Subgroup.mem_normalizer_iff.mp (hTH ht) x).mpr hxH, ?_⟩
      have := Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.inv_mem _ htV) hxV) htV
      simpa [mul_assoc] using this
  have hTY : IsSylowIn 2 T (N₀ ⊔ T) := E6.isSylowIn_of_le hT le_sup_right le_top
  have hnorm : (N₀.subgroupOf (N₀ ⊔ T)).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_left).mpr
      (sup_le Subgroup.le_normalizer hTN₀)
  have hsyl : IsSylowIn 2 (T ⊓ N₀) N₀ := hTY.inf_normal le_sup_left hnorm
  let f : ↥N₀ →* MulAut ↥V := (conjAct V).comp (Subgroup.inclusion inf_le_right)
  have hrange : f.range = autOn H V := by
    ext φ
    constructor
    · rintro ⟨⟨g, hgH, hgV⟩, rfl⟩
      exact ⟨⟨g, hgV⟩, hgH, rfl⟩
    · rintro ⟨⟨g, hgV⟩, hgH, rfl⟩
      exact ⟨⟨g, hgH, hgV⟩, rfl⟩
  have himage : ((T ⊓ N₀).subgroupOf N₀).map f = autOn (T ⊓ H) V := by
    ext φ
    constructor
    · rintro ⟨⟨g, hgH, hgV⟩, ⟨hgT, -⟩, rfl⟩
      exact ⟨⟨g, hgV⟩, ⟨hgT, hgH⟩, rfl⟩
    · rintro ⟨⟨g, hgV⟩, ⟨hgT, hgH⟩, rfl⟩
      exact ⟨⟨g, hgH, hgV⟩, ⟨hgT, hgH, hgV⟩, rfl⟩
  let Q : Sylow 2 ↥f.range := hsyl.toSylow.mapSurjective f.rangeRestrict_surjective
  have hQ := Sylow.card_eq_multiplicity Q
  have hQc : (Q : Subgroup ↥f.range).map f.range.subtype = autOn (T ⊓ H) V := by
    rw [Sylow.coe_mapSurjective, IsSylowIn.coe_toSylow, Subgroup.map_map,
      MonoidHom.subtype_comp_rangeRestrict, himage]
  rw [← hQc, Subgroup.card_map_of_injective (Subgroup.subtype_injective _), hQ, hrange]

end Sylow

@[expose] noncomputable def l3wrSylU : Subgroup (MulAut WMod) := (U3.prod U3).map rho

theorem l3wrSylU_le_img : l3wrSylU ≤ img := Subgroup.map_le_range _ _

theorem card_l3wrSylU : Nat.card ↥l3wrSylU = 2 ^ 6 := by
  rw [l3wrSylU, Subgroup.card_map_of_injective rho_injective, card_prod_subgroup, card_U3]
  norm_num

theorem l3wr_tr01_mem_U3 : tr 0 1 (by decide) ∈ U3 := by
  refine ⟨?_, ?_⟩
  · change mat (tr 0 1 _) *ᵥ e0 = e0
    rw [mulVec_e0_iff, mat_tr]
    decide
  · change e2 ᵥ* mat (tr 0 1 _) = e2
    rw [e2_vecMul_iff, mat_tr]
    decide

theorem l3wr_tr02_mem_U3 : tr 0 2 (by decide) ∈ U3 := by
  refine ⟨?_, ?_⟩
  · change mat (tr 0 2 _) *ᵥ e0 = e0
    rw [mulVec_e0_iff, mat_tr]
    decide
  · change e2 ᵥ* mat (tr 0 2 _) = e2
    rw [e2_vecMul_iff, mat_tr]
    decide

theorem card_fixV_l3wrSylU_le : Nat.card ↥(fixV l3wrSylU) ≤ 2 := by
  classical
  have key : ∀ X ∈ fixV l3wrSylU, X = 1 ∨ X = Multiplicative.ofAdd (Matrix.single 0 0 1) := by
    intro X hX
    have hfix : ∀ g : ↥SL32 × ↥SL32, g ∈ U3.prod U3 →
        mat g.1 * Multiplicative.toAdd X * (mat g.2)ᵀ = Multiplicative.toAdd X := fun g hg => by
      rw [← toAdd_rho]
      exact congrArg Multiplicative.toAdd (hX _ ⟨g, hg, rfl⟩)
    have h1 := hfix (tr 0 1 (by decide), 1) ⟨l3wr_tr01_mem_U3, U3.one_mem⟩
    have h2 := hfix (tr 0 2 (by decide), 1) ⟨l3wr_tr02_mem_U3, U3.one_mem⟩
    have h3 := hfix (1, tr 0 1 (by decide)) ⟨U3.one_mem, l3wr_tr01_mem_U3⟩
    have h4 := hfix (1, tr 0 2 (by decide)) ⟨U3.one_mem, l3wr_tr02_mem_U3⟩
    simp only [mat_tr, mat_one, Matrix.transpose_one, Matrix.mul_one, Matrix.one_mul] at h1 h2 h3 h4
    have hY := eq_smul_E00 h1 h2 h3 h4
    have hc : Multiplicative.toAdd X 0 0 = 0 ∨ Multiplicative.toAdd X 0 0 = 1 := by
      generalize Multiplicative.toAdd X 0 0 = c
      fin_cases c
      · exact Or.inl rfl
      · exact Or.inr rfl
    rcases hc with hc | hc
    · left
      apply Multiplicative.toAdd.injective
      rw [hY, hc, Matrix.single_zero]
      rfl
    · right
      apply Multiplicative.toAdd.injective
      rw [hY, hc]
      rfl
  have h1 : Nat.card ↥(fixV l3wrSylU) ≤
      Nat.card ({1, Multiplicative.ofAdd (Matrix.single 0 0 1)} : Finset WMod) := by
    refine Nat.card_le_card_of_injective (fun w => ⟨w.1, ?_⟩) ?_
    · rcases key w.1 w.2 with h | h <;> simp [h]
    · intro w w' h
      have h' := congrArg Subtype.val h
      exact Subtype.ext h'
  refine h1.trans ?_
  rw [Nat.card_eq_fintype_card, Fintype.card_coe]
  exact Finset.card_le_two

theorem card_fixV_cj {W : Type*} [CommGroup W] (g : MulAut W) (X : Subgroup (MulAut W)) :
    Nat.card ↥(fixV (B3.cj g X)) = Nat.card ↥(fixV X) := by
  refine Nat.card_congr
    { toFun := fun w => ⟨g⁻¹ w.1, fun x hx => ?_⟩
      invFun := fun w => ⟨g w.1, fun x hx => ?_⟩
      left_inv := fun w => Subtype.ext (MulAut.apply_inv_self _ _ _)
      right_inv := fun w => Subtype.ext (MulAut.inv_apply_self _ _ _) }
  · have h := w.2 (g * x * g⁻¹) ⟨x, hx, rfl⟩
    rw [MulAut.mul_apply, MulAut.mul_apply] at h
    calc x (g⁻¹ w.1) = g⁻¹ (g (x (g⁻¹ w.1))) := (MulAut.inv_apply_self _ _ _).symm
      _ = g⁻¹ w.1 := by rw [h]
  · obtain ⟨y, hy, rfl⟩ := hx
    change g (y (g⁻¹ (g w.1))) = g w.1
    rw [MulAut.inv_apply_self, w.2 y hy]

theorem card_fixV_le_two_of_img {S A : Subgroup (MulAut WMod)} (hSle : S ≤ img)
    (hScard : Nat.card ↥S = 2 ^ 6) (hSA : S ≤ A) : Nat.card ↥(fixV A) ≤ 2 := by
  have hidx : ¬ 2 ∣ (S.subgroupOf img).index := by
    have h1 := (S.subgroupOf img).card_mul_index
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hSle).toEquiv, hScard, card_img] at h1
    have h2 : (S.subgroupOf img).index = 441 := by omega
    rw [h2]
    decide
  obtain ⟨g, -, hg⟩ := B3.exists_conj_le_sylow_sub hSle (IsPGroup.of_card hScard) hidx
    l3wrSylU_le_img (IsPGroup.of_card card_l3wrSylU)
  have h1 : fixV A ≤ fixV (B3.cj g l3wrSylU) := fun w hw x hx => hw x (hSA (hg hx))
  exact (Subgroup.card_le_of_le h1).trans
    ((card_fixV_cj g l3wrSylU).trans_le card_fixV_l3wrSylU_le)

theorem input8_3_z : Input8_3_z := by
  intro G _ _ T L I h702 _ hV hrow
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hfsu := h702.fsu
  obtain ⟨-, hreal⟩ := hrow
  obtain ⟨e, he⟩ := exists_model hreal
  have hT := isSylowIn_top_of_fsu hfsu
  have hTL₀ : T ≤ Subgroup.normalizer (fsuL0 T L : Set G) := le_normalizer_conjClosure L T
  have hTV : T ≤ Subgroup.normalizer (fsuV T I : Set G) := le_normalizer_conjClosure I T
  have hmono : ∀ {H K : Subgroup G}, H ≤ K → autOn H (fsuV T I) ≤ autOn K (fsuV T I) :=
    fun hHK => Subgroup.map_mono fun x hx => hHK hx
  have hB : Nat.card ↥(autOn (fsuL0 T L) (fsuV T I)) = 2 ^ 6 * 441 := by
    have h1 := card_map_congrHom e (autOn (fsuL0 T L) (fsuV T I))
    rw [he] at h1
    exact h1.symm.trans card_img
  have hfac : (2 ^ 6 * 441 : ℕ).factorization 2 = 6 := by
    rw [Nat.factorization_mul (by norm_num) (by norm_num), Finsupp.add_apply,
      Nat.Prime.factorization_pow Nat.prime_two, Finsupp.single_eq_same,
      Nat.factorization_eq_zero_of_not_dvd (by norm_num), add_zero]
  have hS := card_autOn_inf_of_sylow hT hTL₀ hTV
  rw [hB, hfac] at hS
  have hle : Nat.card ↥(fixV (autOn T (fsuV T I))) ≤ 2 := by
    have h1 := card_fixV_le_two_of_img
      (S := (autOn (T ⊓ fsuL0 T L) (fsuV T I)).map (congrHom e))
      (A := (autOn T (fsuV T I)).map (congrHom e)) (he ▸ Subgroup.map_mono (hmono inf_le_right))
      ((card_map_congrHom e _).trans hS) (Subgroup.map_mono (hmono inf_le_left))
    have h2 := fixV_map_congrHom e (autOn T (fsuV T I))
    have h3 : Nat.card ↥(fixV ((autOn T (fsuV T I)).map (congrHom e))) =
        Nat.card ↥(fixV (autOn T (fsuV T I))) := by
      rw [h2]
      exact Subgroup.card_map_of_injective e.injective
    exact h3 ▸ h1
  have hA2 : IsPGroup 2 ↥(autOn T (fsuV T I)) :=
    (hfsu.sylow.1.of_equiv (Subgroup.subgroupOfEquivOfLe hTV).symm).map _
  have hmod := hA2.card_modEq_card_fixedPoints ↥(fsuV T I)
  have hVcard : Nat.card ↥(fsuV T I) = 2 ^ 9 := by rw [Nat.card_congr e.toEquiv, card_WMod]
  have hfixeq : Nat.card ↑(MulAction.fixedPoints ↥(autOn T (fsuV T I)) ↥(fsuV T I)) =
      Nat.card ↥(fixV (autOn T (fsuV T I))) :=
    Nat.card_congr (Equiv.subtypeEquivRight fun v =>
      ⟨fun h x hx => h ⟨x, hx⟩, fun h a => h a.1 a.2⟩)
  rw [hVcard, hfixeq] at hmod
  have hpos : 0 < Nat.card ↥(fixV (autOn T (fsuV T I))) := Nat.card_pos
  have hfix2 : Nat.card ↥(fixV (autOn T (fsuV T I))) = 2 := by
    have := Nat.ModEq.symm hmod
    unfold Nat.ModEq at this
    omega
  have hCeq : fsuV T I ⊓ Subgroup.centralizer (T : Set G) =
      (fixV (autOn T (fsuV T I))).map (fsuV T I).subtype := by
    ext x
    constructor
    · rintro ⟨hxV, hxC⟩
      refine ⟨⟨x, hxV⟩, ?_, rfl⟩
      rintro _ ⟨⟨t, htN⟩, htT, rfl⟩
      apply Subtype.ext
      rw [CFSG.QuasithinUnique.Setup.coe_conjAct_apply]
      change t * x * t⁻¹ = x
      rw [Subgroup.mem_centralizer_iff.mp hxC t htT, mul_inv_cancel_right]
    · rintro ⟨⟨x, hxV⟩, hfix, rfl⟩
      refine ⟨hxV, Subgroup.mem_centralizer_iff.mpr fun t ht => ?_⟩
      have h1 := hfix (conjAct (fsuV T I) ⟨t, hTV ht⟩) ⟨⟨t, hTV ht⟩, ht, rfl⟩
      have h2 := congrArg Subtype.val h1
      rw [CFSG.QuasithinUnique.Setup.coe_conjAct_apply] at h2
      change t * x * t⁻¹ = x at h2
      calc t * x = t * x * t⁻¹ * t := by group
        _ = x * t := by rw [h2]
  have hCcard : Nat.card ↥(fsuV T I ⊓ Subgroup.centralizer (T : Set G)) = 2 := by
    rw [hCeq, Subgroup.card_map_of_injective (Subgroup.subtype_injective _), hfix2]
  obtain ⟨z, hzC, hz1⟩ : ∃ z ∈ fsuV T I ⊓ Subgroup.centralizer (T : Set G), z ≠ 1 := by
    by_contra h
    push Not at h
    have hbot : fsuV T I ⊓ Subgroup.centralizer (T : Set G) = ⊥ :=
      (Subgroup.eq_bot_iff_forall _).mpr h
    rw [hbot, Subgroup.card_bot] at hCcard
    omega
  have hz2 : orderOf z = 2 := by
    have h1 := Subgroup.orderOf_dvd_natCard _ hzC
    rw [hCcard] at h1
    rcases (Nat.dvd_prime Nat.prime_two).mp h1 with h | h
    · exact absurd (orderOf_eq_one_iff.mp h) hz1
    · exact h
  refine ⟨z, hz2, ?_⟩
  symm
  apply Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hzC)
  rw [hCcard, Nat.card_zpowers, hz2]

end CFSG.Quasithin.H13
