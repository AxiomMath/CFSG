module

public import CFSG.Quasithin.Vol2.Ch10SecCBasic
public import CFSG.Quasithin.Vol2.Ch10StatementsInputsAS2
public import CFSG.Quasithin.Vol2.Ch10SecBInner3
public import CFSG.Quasithin.Background.B4L3Two
public import CFSG.Quasithin.Vol2.Ch1Residual
public import CFSG.Quasithin.Background.C2Nine
public import CFSG.Quasithin.Vol2.Ch10StatementsE

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecC

open CFSG.Open CFSG.Quasithin.H13
open scoped IsMulCommutative commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem card_SL_two_ne {K : Type} [Field K] [Finite K] {n : ℕ} (hn : 1 < n)
    (hK : Nat.card K = 2 ^ n) : Nat.card (Matrix.SpecialLinearGroup (Fin 2) K) ≠ 168 := by
  have := Fintype.ofFinite K
  rw [Matrix.card_SL_field, Fin.prod_univ_two]
  rw [Nat.card_eq_fintype_card] at hK
  rw [hK]
  simp only [Fin.val_zero, pow_zero, Fin.val_one, pow_one]
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
  have hq : 4 ≤ 2 ^ (m + 2) := by
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ (m + 2) := Nat.pow_le_pow_right (by norm_num) (by omega)
  set q := 2 ^ (m + 2) with hqdef
  have hsq : q ^ 2 - q = q * (q - 1) := by
    rw [Nat.mul_sub_one, pow_two]
  have hpos : 0 < q - 1 := by omega
  rw [hsq, ← mul_assoc, Nat.mul_div_cancel _ hpos]
  rcases Nat.eq_zero_or_pos m with hm | hm
  · subst hm
    norm_num [hqdef]
  · have hq8 : 8 ≤ q := by
      calc 8 = 2 ^ 3 := by norm_num
        _ ≤ 2 ^ (m + 2) := Nat.pow_le_pow_right (by norm_num) (by omega)
    have h1 : 63 ≤ q ^ 2 - 1 := by
      have : 64 ≤ q ^ 2 := by nlinarith
      omega
    intro h
    have : 63 * 8 ≤ (q ^ 2 - 1) * q := Nat.mul_le_mul h1 hq8
    omega

theorem fsuUL_inf_le_fsuCVM {T L I : Subgroup G} (h37 : QuasithinUnique.Vol2Native.A37ForSQTKCat)
    (h38 : QuasithinUnique.Vol2Native.A38ForSQTKCat) (hyp : Hyp10 G T L I)
    (h1011 : Stmt10_1_1) :
    fsuUL T L I ⊓ Subgroup.centralizer (L : Set G) ≤ fsuCVM T L I := by
  obtain ⟨t, ht, htn⟩ := Set.not_subset.mp hyp.not_normal
  obtain ⟨-, -, hdec, -⟩ := h1011 G T L I hyp
  obtain ⟨-, hV1, -, -⟩ := hdec t ht htn
  have hV1V : fsuUL T L I ≤ fsuVM T L I :=
    commutator_le_left_of_le_normalizer
      ((SecA.le_fsuL0 T L).trans (SecA.fsuL0_le_normalizer_fsuVM T L I))
  rintro x ⟨hx, hxL⟩
  refine ⟨hV1V hx, ?_⟩
  rw [SecA.fsuL0_eq_sup h37 h38 hyp ht htn]
  exact mem_centralizer_sup hxL (hV1 hx)

theorem case3_of {T L I : Subgroup G} (hyp : Hyp10 G T L I) (h1012 : Stmt10_1_2) (hL : LBarL32 L)
    (hcv : fsuCVM T L I ≠ ⊥) : Case10_1_1Three T L I := by
  have h4 := (h1012 G T L I hyp).2.2.2.2.2.2.1
  by_contra h3
  have hc1 : ∃ n, Case10_1_1One T L I n := by
    by_contra hc1
    exact hcv (h4 fun h => h.elim hc1 h3)
  obtain ⟨n, hn1, ⟨K, _, _, hK, ⟨e⟩⟩, -⟩ := hc1
  obtain ⟨f⟩ := hL
  have hcard := Nat.card_congr (e.symm.trans f).toEquiv
  rw [card_SL_three_two] at hcard
  exact card_SL_two_ne hn1 hK hcard

theorem commutator_fsuUL_eq {T L I : Subgroup G} (hyp : Hyp10 G T L I) :
    ⁅fsuUL T L I, L⁆ = fsuUL T L I :=
  commutator_commutator_eq_of_opResidual (SecA.isElemAbelian_fsuVM hyp)
    ((SecA.le_fsuL0 T L).trans (SecA.fsuL0_le_normalizer_fsuVM T L I))
    (C2Nine.opResidual_eq_of_perfect hyp.fsu.faithful.1.2.1.2.1)

omit [Finite G] in
theorem le_normalizer_fsuUL (T L I : Subgroup G) :
    L ≤ Subgroup.normalizer (fsuUL T L I : Set G) :=
  SecA.le_normalizer_commutator ((SecA.le_fsuL0 T L).trans (SecA.fsuL0_le_normalizer_fsuVM T L I))
    Subgroup.le_normalizer

omit [Finite G] in
theorem conjAct_mem_autOn {T L I : Subgroup G} {l : G} (hl : l ∈ L) :
    conjAct (fsuUL T L I) ⟨l, le_normalizer_fsuUL T L I hl⟩ ∈ autOn L (fsuUL T L I) :=
  ⟨⟨l, le_normalizer_fsuUL T L I hl⟩, hl, rfl⟩

theorem fixV_autOn_fsuUL {T L I : Subgroup G} (h37 : QuasithinUnique.Vol2Native.A37ForSQTKCat)
    (h38 : QuasithinUnique.Vol2Native.A38ForSQTKCat) (hyp : Hyp10 G T L I)
    (h1011 : Stmt10_1_1) [IsMulCommutative ↥(fsuUL T L I)] :
    fixV (autOn L (fsuUL T L I)) = cV1 T L I := by
  obtain ⟨t, ht, htn⟩ := Set.not_subset.mp hyp.not_normal
  obtain ⟨-, -, hdec, -⟩ := h1011 G T L I hyp
  obtain ⟨-, hV1, -, -⟩ := hdec t ht htn
  ext v
  rw [mem_fixV, cV1, Subgroup.mem_subgroupOf]
  constructor
  · intro hv
    have hvL : (v : G) ∈ Subgroup.centralizer (L : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro l hl
      have h1 := congrArg Subtype.val (hv _ (conjAct_mem_autOn (T := T) (I := I) hl))
      change l * (v : G) * l⁻¹ = v at h1
      calc l * (v : G) = l * v * l⁻¹ * l := by group
        _ = v * l := by rw [h1]
    rw [SecA.fsuL0_eq_sup h37 h38 hyp ht htn]
    exact mem_centralizer_sup hvL (hV1 v.2)
  · intro hv g hg
    obtain ⟨x, hxL, rfl⟩ := SecB.mem_autOn_iff.mp hg
    apply Subtype.ext
    change (x : G) * v * (x : G)⁻¹ = v
    have hc := Subgroup.mem_centralizer_iff.mp hv x (SecA.le_fsuL0 T L hxL)
    rw [hc]
    group

theorem commV_autOn_fsuUL {T L I : Subgroup G} (hyp : Hyp10 G T L I)
    [IsMulCommutative ↥(fsuUL T L I)] : commV (autOn L (fsuUL T L I)) = ⊤ := by
  rw [eq_top_iff]
  rintro ⟨v, hv⟩ -
  rw [← commutator_fsuUL_eq hyp] at hv
  have hle : ⁅fsuUL T L I, L⁆ ≤ (commV (autOn L (fsuUL T L I))).map (fsuUL T L I).subtype := by
    rw [Subgroup.commutator_le]
    intro w hw l hl
    set g := conjAct (fsuUL T L I) ⟨l, le_normalizer_fsuUL T L I hl⟩
    let w' : ↥(fsuUL T L I) := ⟨w, hw⟩
    refine ⟨g w'⁻¹ * w'⁻¹⁻¹,
      Subgroup.subset_closure ⟨g, conjAct_mem_autOn hl, w'⁻¹, rfl⟩, ?_⟩
    have hcomm : ((g w'⁻¹ : ↥(fsuUL T L I)) : G) * w = w * (g w'⁻¹ : ↥(fsuUL T L I)) :=
      congrArg Subtype.val (mul_comm (g w'⁻¹) w')
    change ((g w'⁻¹ : ↥(fsuUL T L I)) : G) * w⁻¹⁻¹ = ⁅w, l⁆
    rw [inv_inv, hcomm, commutatorElement_def]
    change w * (l * w⁻¹ * l⁻¹) = w * l * w⁻¹ * l⁻¹
    group
  obtain ⟨u, hu, rfl⟩ := hle hv
  exact hu

section Coord

variable {T L I : Subgroup G} [IsMulCommutative ↥(fsuUL T L I)]

omit [Finite G] in
theorem sup_cV1_eq_top (D : L3Data (autOn L (fsuUL T L I)) ⊤ (cV1 T L I))
    {S : Subgroup ↥(fsuUL T L I)} (hS : ∀ g ∈ autOn L (fsuUL T L I), ∀ s ∈ S, g s ∈ S)
    (hSc : ¬ S ≤ cV1 T L I) : S ⊔ cV1 T L I = ⊤ := by
  obtain ⟨s, hs, hsc⟩ := Set.not_subset.mp hSc
  have hβs : D.β ⟨s, Subgroup.mem_top _⟩ ≠ 1 := fun h => hsc ((D.ker_β _).mp h)
  rw [eq_top_iff]
  intro v _
  by_cases hv : D.β ⟨v, Subgroup.mem_top _⟩ = 1
  · exact Subgroup.mem_sup_right ((D.ker_β _).mp hv)
  · obtain ⟨γ, hγ⟩ := L3.act_trans (Multiplicative.toAdd (D.β ⟨s, Subgroup.mem_top _⟩))
      (Multiplicative.toAdd (D.β ⟨v, Subgroup.mem_top _⟩)) (fun h => hβs (by simpa using h))
      (fun h => hv (by simpa using h))
    have hgs : ((D.π γ : ↥(autOn L (fsuUL T L I))) : MulAut ↥(fsuUL T L I)) s ∈ S :=
      hS _ (D.π γ).2 s hs
    have he := D.equi γ ⟨s, Subgroup.mem_top _⟩ (Subgroup.mem_top _)
    rw [hγ] at he
    simp only [ofAdd_toAdd] at he
    have hker : v⁻¹ * ((D.π γ : ↥(autOn L (fsuUL T L I))) : MulAut ↥(fsuUL T L I)) s ∈
        cV1 T L I := by
      have := (D.ker_β ⟨v⁻¹ * ((D.π γ : ↥(autOn L (fsuUL T L I))) : MulAut ↥(fsuUL T L I)) s,
        Subgroup.mem_top _⟩).mp
      apply this
      have hmul : (⟨v⁻¹ * ((D.π γ : ↥(autOn L (fsuUL T L I))) : MulAut ↥(fsuUL T L I)) s,
          Subgroup.mem_top _⟩ : ↥(⊤ : Subgroup ↥(fsuUL T L I))) =
          (⟨v, Subgroup.mem_top _⟩ : ↥(⊤ : Subgroup ↥(fsuUL T L I)))⁻¹ *
            ⟨_, Subgroup.mem_top _⟩ := rfl
      rw [hmul, map_mul, map_inv, he]
      exact inv_mul_cancel _
    have : v = ((D.π γ : ↥(autOn L (fsuUL T L I))) : MulAut ↥(fsuUL T L I)) s *
        (v⁻¹ * ((D.π γ : ↥(autOn L (fsuUL T L I))) : MulAut ↥(fsuUL T L I)) s)⁻¹ := by group
    rw [this]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hgs)
      (Subgroup.inv_mem _ (Subgroup.mem_sup_right hker))

theorem commV_le_of_sup_eq_top (h37 : QuasithinUnique.Vol2Native.A37ForSQTKCat)
    (h38 : QuasithinUnique.Vol2Native.A38ForSQTKCat) (hyp : Hyp10 G T L I) (h1011 : Stmt10_1_1)
    {S : Subgroup ↥(fsuUL T L I)} (hS : ∀ g ∈ autOn L (fsuUL T L I), ∀ s ∈ S, g s ∈ S)
    (hsup : S ⊔ cV1 T L I = ⊤) : commV (autOn L (fsuUL T L I)) ≤ S := by
  rw [commV, Subgroup.closure_le]
  rintro _ ⟨g, hg, v, rfl⟩
  have hv : v ∈ S ⊔ cV1 T L I := hsup ▸ Subgroup.mem_top v
  obtain ⟨a, ha, c, hc, rfl⟩ := Subgroup.mem_sup.mp hv
  have hgc : g c = c := by
    have hfix := fixV_autOn_fsuUL h37 h38 hyp h1011 (T := T) (L := L) (I := I)
    rw [← hfix] at hc
    exact hc g hg
  rw [map_mul, hgc, mul_inv_rev, mul_assoc, mul_inv_cancel_left]
  exact S.mul_mem (hS g hg a ha) (S.inv_mem ha)

theorem isIndecompModule_fsuUL (h37 : QuasithinUnique.Vol2Native.A37ForSQTKCat)
    (h38 : QuasithinUnique.Vol2Native.A38ForSQTKCat) (hyp : Hyp10 G T L I) (h1011 : Stmt10_1_1)
    (D : L3Data (autOn L (fsuUL T L I)) ⊤ (cV1 T L I)) :
    IsIndecompModule (autOn L (fsuUL T L I)) := by
  intro X Y hX hY hXY hXYt
  have hcomm := commV_autOn_fsuUL (T := T) (L := L) (I := I) hyp
  by_cases hXc : X ≤ cV1 T L I
  · by_cases hYc : Y ≤ cV1 T L I
    · exfalso
      have htop : cV1 T L I = ⊤ := top_le_iff.mp (hXYt ▸ sup_le hXc hYc)
      have hcard := D.card_U
      rw [htop] at hcard
      have hpos : 0 < Nat.card (⊤ : Subgroup ↥(fsuUL T L I)) := Nat.card_pos
      omega
    · left
      have hYt : ⊤ ≤ Y := hcomm ▸ commV_le_of_sup_eq_top h37 h38 hyp h1011 hY
        (sup_cV1_eq_top D hY hYc)
      rw [eq_bot_iff, ← hXY]
      exact fun x hx => ⟨hx, hYt (Subgroup.mem_top _)⟩
  · right
    have hXt : ⊤ ≤ X := hcomm ▸ commV_le_of_sup_eq_top h37 h38 hyp h1011 hX
      (sup_cV1_eq_top D hX hXc)
    rw [eq_bot_iff, ← hXY]
    exact fun y hy => ⟨hXt (Subgroup.mem_top _), hy⟩

omit [IsMulCommutative ↥(fsuUL T L I)] in
theorem sq_eq_one_fsuUL (hyp : Hyp10 G T L I) (v : ↥(fsuUL T L I)) : v ^ 2 = 1 := by
  have hV1V : fsuUL T L I ≤ fsuVM T L I :=
    commutator_le_left_of_le_normalizer
      ((SecA.le_fsuL0 T L).trans (SecA.fsuL0_le_normalizer_fsuVM T L I))
  exact Subtype.ext ((SecA.isElemAbelian_fsuVM hyp).2 v (hV1V v.2))

theorem card_fsuUL (h37 : QuasithinUnique.Vol2Native.A37ForSQTKCat)
    (h38 : QuasithinUnique.Vol2Native.A38ForSQTKCat) (hyp : Hyp10 G T L I) (h1011 : Stmt10_1_1)
    (h484 : ASInputs.AS_B_4_8_four) (D : L3Data (autOn L (fsuUL T L I)) ⊤ (cV1 T L I))
    (hnat : BinaryNaturalSL (autOn L (fsuUL T L I)) ⊤ (cV1 T L I) 3 1)
    (hne : cV1 T L I ≠ ⊥) : Nat.card ↥(fsuUL T L I) = 16 ∧ Nat.card ↥(cV1 T L I) = 2 := by
  have hiso : Nonempty (↥(autOn L (fsuUL T L I)) ≃* Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)) :=
    ⟨(MulEquiv.ofBijective D.π ⟨D.π_injective, D.π_surj⟩).symm⟩
  have hind := isIndecompModule_fsuUL h37 h38 hyp h1011 D
  have hfix := fixV_autOn_fsuUL h37 h38 hyp h1011 (T := T) (L := L) (I := I)
  have h := h484 ↥(fsuUL T L I) (sq_eq_one_fsuUL hyp) (autOn L (fsuUL T L I)) hiso
    (fun A B hA hB hAB hABt => hind A B hA hB hAB hABt)
    ⟨cV1 T L I, ⊤, le_top, hfix.symm.le, le_top, hnat⟩
  have hU := D.card_U
  rw [Subgroup.card_top] at hU
  have h2 : 2 ≤ Nat.card ↥(cV1 T L I) := by
    have h1 : 1 < Nat.card ↥(cV1 T L I) := by
      rw [Subgroup.one_lt_card_iff_ne_bot]
      exact hne
    omega
  rcases h with h8 | h16
  · omega
  · exact ⟨h16, by omega⟩

theorem offHyp_fsuUL (h37 : QuasithinUnique.Vol2Native.A37ForSQTKCat)
    (h38 : QuasithinUnique.Vol2Native.A38ForSQTKCat) (hyp : Hyp10 G T L I) (h1011 : Stmt10_1_1)
    (h484 : ASInputs.AS_B_4_8_four) (D : L3Data (autOn L (fsuUL T L I)) ⊤ (cV1 T L I))
    (hnat : BinaryNaturalSL (autOn L (fsuUL T L I)) ⊤ (cV1 T L I) 3 1)
    (hne : cV1 T L I ≠ ⊥) : OffHyp (autOn L (fsuUL T L I)) :=
  offHyp_two D (sq_eq_one_fsuUL hyp) (card_fsuUL h37 h38 hyp h1011 h484 D hnat hne).1 rfl
    (fixV_autOn_fsuUL h37 h38 hyp h1011).symm (isIndecompModule_fsuUL h37 h38 hyp h1011 D)

theorem fixV_sylow_fsuUL (h37 : QuasithinUnique.Vol2Native.A37ForSQTKCat)
    (h38 : QuasithinUnique.Vol2Native.A38ForSQTKCat) (hyp : Hyp10 G T L I) (h1011 : Stmt10_1_1)
    (h484 : ASInputs.AS_B_4_8_four) (D : L3Data (autOn L (fsuUL T L I)) ⊤ (cV1 T L I))
    (hnat : BinaryNaturalSL (autOn L (fsuUL T L I)) ⊤ (cV1 T L I) 3 1)
    (hne : cV1 T L I ≠ ⊥) {S : Subgroup (MulAut ↥(fsuUL T L I))}
    (hS : QuasithinUnique.IsSylowTwoOf S (autOn L (fsuUL T L I))) : fixV S = cV1 T L I := by
  have hfix := fixV_autOn_fsuUL h37 h38 hyp h1011 (T := T) (L := L) (I := I)
  have hnat' : BinaryNaturalSL (autOn L (fsuUL T L I)) ⊤ (fixV (autOn L (fsuUL T L I))) 3 1 := by
    rw [hfix]
    exact hnat
  rw [← hfix]
  exact (B4_8_2 (sq_eq_one_fsuUL hyp) (card_fsuUL h37 h38 hyp h1011 h484 D hnat hne).1 hnat'
    (isIndecompModule_fsuUL h37 h38 hyp h1011 D)).2.2.1 S hS

end Coord

end CFSG.Quasithin.Vol2.Ch10.SecC
