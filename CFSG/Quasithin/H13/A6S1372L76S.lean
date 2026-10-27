module

public import CFSG.Quasithin.H13.A6S1372L76R
public import CFSG.Quasithin.H13.A6S1372L76Q

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.Quasithin.H13.A6

open Equiv CFSG.Open CFSG.Quasithin Matrix

namespace A6L76S

@[expose] def w8 (j : Fin 8) : Perm (Fin 8) :=
  if j = 7 then 1 else
    swap 7 j * swap (if (j : ℕ) ≤ 1 then 2 else 0) (if (j : ℕ) ≤ 1 then 3 else 1)

theorem w8_facts : ∀ j : Fin 8, w8 j 7 = j ∧ Perm.sign (w8 j) = 1 := by
  decide +kernel

theorem exists_mem_A8 (j : Fin 8) : ∃ g : alternatingGroup (Fin 8), (g : Perm (Fin 8)) 7 = j :=
  ⟨⟨w8 j, Perm.mem_alternatingGroup.2 (w8_facts j).2⟩, (w8_facts j).1⟩

theorem card_stab7 :
    Nat.card (MulAction.stabilizer (alternatingGroup (Fin 8)) (7 : Fin 8)) = 2520 := by
  have h1 := MulAction.index_stabilizer (alternatingGroup (Fin 8)) (7 : Fin 8)
  have horb : MulAction.orbit (alternatingGroup (Fin 8)) (7 : Fin 8) = Set.univ := by
    ext j
    simp only [Set.mem_univ, iff_true]
    obtain ⟨g, hg⟩ := exists_mem_A8 j
    exact ⟨g, hg⟩
  rw [horb, Set.ncard_univ, Nat.card_eq_fintype_card, Fintype.card_fin] at h1
  have h2 := (MulAction.stabilizer (alternatingGroup (Fin 8)) (7 : Fin 8)).index_mul_card
  rw [h1, nat_card_alternatingGroup, Nat.card_fin] at h2
  have h3 : Nat.factorial 8 / 2 = 20160 := by decide
  omega

theorem exists_mem_of_card64 {Y : Subgroup (alternatingGroup (Fin 8))} (hY : Nat.card Y = 64)
    (j : Fin 8) : ∃ y ∈ Y, (y : Perm (Fin 8)) 7 = j := by
  classical
  set S := MulAction.stabilizer ↥Y (7 : Fin 8) with hS
  have hdvd1 : Nat.card S ∣ 2520 := by
    rw [← card_stab7]
    have hle : S.map Y.subtype ≤ MulAction.stabilizer (alternatingGroup (Fin 8)) (7 : Fin 8) := by
      rintro _ ⟨s, hs, rfl⟩
      exact hs
    have := Subgroup.card_dvd_of_le hle
    rwa [Subgroup.card_map_of_injective Y.subtype_injective] at this
  have hdvd2 : Nat.card S ∣ 64 := hY ▸ Subgroup.card_subgroup_dvd_card S
  have h8 : Nat.card S ∣ 8 := by
    have := Nat.dvd_gcd hdvd1 hdvd2
    rwa [show Nat.gcd 2520 64 = 8 by norm_num] at this
  have hS8 : Nat.card S ≤ 8 := Nat.le_of_dvd (by norm_num) h8
  have hidx := S.index_mul_card
  rw [hY] at hidx
  have horb := MulAction.index_stabilizer (↥Y) (7 : Fin 8)
  rw [← hS] at horb
  have hle8 : (MulAction.orbit ↥Y (7 : Fin 8)).ncard ≤ 8 := by
    calc (MulAction.orbit ↥Y (7 : Fin 8)).ncard ≤ (Set.univ : Set (Fin 8)).ncard :=
          Set.ncard_le_ncard (Set.subset_univ _)
      _ = 8 := by rw [Set.ncard_univ, Nat.card_eq_fintype_card, Fintype.card_fin]
  have hfull : (MulAction.orbit ↥Y (7 : Fin 8)).ncard = 8 := by
    rw [← horb] at hle8 ⊢
    have hpos : 0 < Nat.card S := Nat.card_pos
    nlinarith
  have huniv : MulAction.orbit ↥Y (7 : Fin 8) = Set.univ := by
    apply Set.eq_of_subset_of_ncard_le (Set.subset_univ _)
    rw [Set.ncard_univ, Nat.card_eq_fintype_card, Fintype.card_fin, hfull]
  have hj : j ∈ MulAction.orbit ↥Y (7 : Fin 8) := huniv ▸ Set.mem_univ j
  obtain ⟨y, hy⟩ := hj
  exact ⟨y, y.2, hy⟩

theorem exists_common_fix {σ τ : Perm (Fin 8)} (hσ : σ ^ 3 = 1) (hτ : τ ^ 3 = 1)
    (hστ : σ * τ = τ * σ) : ∃ j, σ j = j ∧ τ j = j := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have h1 := Equiv.Perm.card_compl_support_modEq (p := 3) (n := 1) (σ := σ)
    (by rw [pow_one]; exact hσ)
  have hp : ∀ x, σ (τ x) = τ x ↔ σ x = x := by
    intro x
    constructor
    · intro h
      apply τ.injective
      rw [← Perm.mul_apply, ← hστ, Perm.mul_apply, h]
    · intro h
      rw [← Perm.mul_apply, hστ, Perm.mul_apply, h]
  let τ' : Perm {x // σ x = x} := τ.subtypePerm hp
  have hτ' : τ' ^ (3 ^ 1) = 1 := by
    rw [pow_one, Equiv.Perm.subtypePerm_pow]
    ext x
    simp [hτ]
  have h2 := Equiv.Perm.card_compl_support_modEq hτ'
  have e : Fintype.card {x // σ x = x} = (σ.supportᶜ).card := by
    rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_finsetCard]
    apply Nat.card_congr
    exact
      { toFun := fun v => ⟨v.1, by
          rw [Finset.mem_compl, Equiv.Perm.mem_support, not_not]
          exact v.2⟩
        invFun := fun w => ⟨w.1, by
          have h := w.2
          rw [Finset.mem_compl, Equiv.Perm.mem_support, not_not] at h
          exact h⟩
        left_inv := fun v => rfl
        right_inv := fun w => rfl }
  rw [e] at h2
  have h3 : (τ'.supportᶜ).card ≡ 2 [MOD 3] := by
    have h4 := h2.trans h1
    rw [Fintype.card_fin] at h4
    exact h4
  have hne : (τ'.supportᶜ).Nonempty := by
    rw [← Finset.card_pos]
    by_contra h0
    push Not at h0
    rw [Nat.le_zero.1 h0] at h3
    exact absurd h3 (by decide)
  obtain ⟨⟨j, hj⟩, hj'⟩ := hne
  rw [Finset.mem_compl, Equiv.Perm.mem_support, not_not] at hj'
  exact ⟨j, hj, congrArg Subtype.val hj'⟩

theorem altLift7_inj : Function.Injective altLift7 := fun _ _ hab =>
  Subtype.ext (Equiv.Perm.viaEmbeddingHom_injective (Fin.castSuccEmb : Fin 7 ↪ Fin 8)
    (congrArg Subtype.val hab))

theorem exists_altLift7 {g : alternatingGroup (Fin 8)} (hg : (g : Perm (Fin 8)) 7 = 7) :
    ∃ x, altLift7 x = g := by
  have hle : altLift7.range ≤ MulAction.stabilizer (alternatingGroup (Fin 8)) (7 : Fin 8) := by
    rintro _ ⟨x, rfl⟩
    rw [MulAction.mem_stabilizer_iff]
    exact A6L76R.altLift7_last' x
  have hcard : Nat.card (MulAction.stabilizer (alternatingGroup (Fin 8)) (7 : Fin 8)) ≤
      Nat.card altLift7.range := by
    rw [card_stab7, MonoidHom.range_eq_map, Subgroup.card_map_of_injective altLift7_inj,
      Subgroup.card_top, nat_card_alternatingGroup, Nat.card_eq_fintype_card, Fintype.card_fin]
    decide
  have heq := Subgroup.eq_of_le_of_card_ge hle hcard
  have hgm : g ∈ MulAction.stabilizer (alternatingGroup (Fin 8)) (7 : Fin 8) := by
    rw [MulAction.mem_stabilizer_iff]
    exact hg
  rw [← heq] at hgm
  exact hgm

theorem e9_of_altLift7 {x y : alternatingGroup (Fin 7)}
    (h : A6L76B.E9Pair (altLift7 x) (altLift7 y)) :
    A6L76B.E9Pair x y := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := h
  refine ⟨altLift7_inj (by rw [map_mul, map_mul, h1]),
    altLift7_inj (by rw [map_pow, h2, map_one]), altLift7_inj (by rw [map_pow, h3, map_one]),
    fun e => h4 (by rw [e, map_one]), fun e => h5 (by rw [e, map_one]),
    fun e => h6 (by rw [e]), fun e => h7 (by rw [e, map_mul])⟩

@[expose] def StabL (a b : Fin 4 → ZMod 2) (N : Matrix (Fin 4) (Fin 4) (ZMod 2)) : Prop :=
  ∀ z, A6L76Q.In3v a b z → A6L76Q.In3v a b (N *ᵥ z)

theorem stabL_mul {a b : Fin 4 → ZMod 2} {N N' : Matrix (Fin 4) (Fin 4) (ZMod 2)}
    (h : StabL a b N) (h' : StabL a b N') : StabL a b (N * N') := fun z hz => by
  rw [← Matrix.mulVec_mulVec]
  exact h _ (h' z hz)

@[expose] noncomputable def lineStab (a b : Fin 4 → ZMod 2) : Subgroup (GL (Fin 4) (ZMod 2)) where
  carrier := {g | StabL a b (g : Matrix (Fin 4) (Fin 4) (ZMod 2))}
  one_mem' := fun z hz => by
    show A6L76Q.In3v a b (((1 : GL (Fin 4) (ZMod 2)) : Matrix (Fin 4) (Fin 4) (ZMod 2)) *ᵥ z)
    rwa [Units.val_one, Matrix.one_mulVec]
  mul_mem' := fun {g h} hg hh => by
    show StabL a b ((g * h : GL (Fin 4) (ZMod 2)) : Matrix (Fin 4) (Fin 4) (ZMod 2))
    rw [Units.val_mul]
    exact stabL_mul hg hh
  inv_mem' := fun {g} hg => by
    have hpow : ∀ k : ℕ,
        StabL a b ((g ^ k : GL (Fin 4) (ZMod 2)) : Matrix (Fin 4) (Fin 4) (ZMod 2)) := by
      intro k
      induction k with
      | zero => intro z hz; rwa [pow_zero, Units.val_one, Matrix.one_mulVec]
      | succ k ih =>
        rw [pow_succ, Units.val_mul]
        exact stabL_mul ih hg
    have hinv : g⁻¹ = g ^ (orderOf g - 1) := by
      apply inv_eq_of_mul_eq_one_right
      rw [← pow_succ', Nat.sub_add_cancel (orderOf_pos g), pow_orderOf_eq_one]
    show StabL a b ((g⁻¹ : GL (Fin 4) (ZMod 2)) : Matrix (Fin 4) (Fin 4) (ZMod 2))
    rw [hinv]
    exact hpow _

@[expose] def cols (a b : Fin 4 → ZMod 2) (p q : Fin 4) : Matrix (Fin 4) (Fin 4) (ZMod 2) :=
  Matrix.of fun i j => (![a, b, Pi.single p 1, Pi.single q 1] : Fin 4 → Fin 4 → ZMod 2) j i

@[expose] def InjOK (M : Matrix (Fin 4) (Fin 4) (ZMod 2)) : Prop := ∀ v, M *ᵥ v = 0 → v = 0

instance (M : Matrix (Fin 4) (Fin 4) (ZMod 2)) : Decidable (InjOK M) := by
  unfold InjOK; infer_instance

@[expose] def pick (a b : Fin 4 → ZMod 2) : Fin 4 × Fin 4 :=
  if InjOK (cols a b 0 1) then (0, 1) else if InjOK (cols a b 0 2) then (0, 2) else
  if InjOK (cols a b 0 3) then (0, 3) else if InjOK (cols a b 1 2) then (1, 2) else
  if InjOK (cols a b 1 3) then (1, 3) else (2, 3)

@[expose] def compl (a b : Fin 4 → ZMod 2) : Matrix (Fin 4) (Fin 4) (ZMod 2) :=
  cols a b (pick a b).1 (pick a b).2

@[expose] def ComplOK (a b : Fin 4 → ZMod 2) : Prop := a ≠ 0 → b ≠ 0 → a ≠ b → InjOK (compl a b)

instance (a b : Fin 4 → ZMod 2) : Decidable (ComplOK a b) := by
  unfold ComplOK; infer_instance

theorem compl_ok : ∀ a b : Fin 4 → ZMod 2, ComplOK a b := by
  decide +kernel

theorem compl_e0 (a b : Fin 4 → ZMod 2) : compl a b *ᵥ Pi.single 0 1 = a := by
  funext i
  simp [compl, cols, Matrix.mulVec_single]

theorem compl_e1 (a b : Fin 4 → ZMod 2) : compl a b *ᵥ Pi.single 1 1 = b := by
  funext i
  simp [compl, cols, Matrix.mulVec_single]

theorem isUnit_compl {a b : Fin 4 → ZMod 2} (ha : a ≠ 0) (hb : b ≠ 0) (hab : a ≠ b) :
    IsUnit (compl a b) := by
  rw [← Matrix.mulVec_injective_iff_isUnit]
  intro v w h
  have h1 : compl a b *ᵥ (v - w) = 0 := by rw [Matrix.mulVec_sub, h, sub_self]
  exact sub_eq_zero.1 (compl_ok a b ha hb hab _ h1)

theorem std_line : (∀ z : Fin 4 → ZMod 2, A6L76Q.In3v (Pi.single 0 1) (Pi.single 1 1) z →
      A6L76Q.InL z ∧ z ≠ 0) ∧
    ∀ w : Fin 4 → ZMod 2, A6L76Q.InL w → w ≠ 0 →
      A6L76Q.In3v (Pi.single 0 1) (Pi.single 1 1) w := by
  decide

theorem stabL_std {g : GL (Fin 4) (ZMod 2)}
    (hg : A6L76Q.BUT (g : Matrix (Fin 4) (Fin 4) (ZMod 2))) :
    StabL (Pi.single 0 1) (Pi.single 1 1) (g : Matrix (Fin 4) (Fin 4) (ZMod 2)) := by
  intro z hz
  obtain ⟨hL, h0⟩ := std_line.1 z hz
  refine std_line.2 _ (A6L76Q.BUT_mulVec hg hL) fun h => h0 ?_
  have := congrArg (((g⁻¹ : GL (Fin 4) (ZMod 2)) : Matrix (Fin 4) (Fin 4) (ZMod 2)) *ᵥ ·) h
  simp only [Matrix.mulVec_mulVec, Matrix.mulVec_zero] at this
  rwa [← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mulVec] at this

theorem stabL_conj {a b : Fin 4 → ZMod 2} (M : GL (Fin 4) (ZMod 2))
    (hM : (M : Matrix (Fin 4) (Fin 4) (ZMod 2)) = compl a b) {g : GL (Fin 4) (ZMod 2)}
    (hg : StabL (Pi.single 0 1) (Pi.single 1 1) (g : Matrix (Fin 4) (Fin 4) (ZMod 2))) :
    M * g * M⁻¹ ∈ lineStab a b := by
  intro z hz
  have hMi : ∀ x, ((M⁻¹ : GL (Fin 4) (ZMod 2)) : Matrix (Fin 4) (Fin 4) (ZMod 2)) *ᵥ
      ((M : Matrix (Fin 4) (Fin 4) (ZMod 2)) *ᵥ x) = x := fun x => by
    rw [Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mulVec]
  have h1 : A6L76Q.In3v (Pi.single 0 1) (Pi.single 1 1)
      (((M⁻¹ : GL (Fin 4) (ZMod 2)) : Matrix (Fin 4) (Fin 4) (ZMod 2)) *ᵥ z) := by
    have := A6L76Q.in3v_mulVec (((M⁻¹ : GL (Fin 4) (ZMod 2)) : Matrix (Fin 4) (Fin 4) (ZMod 2)))
      (show A6L76Q.In3v ((M : Matrix (Fin 4) (Fin 4) (ZMod 2)) *ᵥ Pi.single 0 1)
        ((M : Matrix (Fin 4) (Fin 4) (ZMod 2)) *ᵥ Pi.single 1 1) z by
          rwa [hM, compl_e0, compl_e1])
    rwa [hMi, hMi] at this
  have h2 := A6L76Q.in3v_mulVec (M : Matrix (Fin 4) (Fin 4) (ZMod 2)) (hg _ h1)
  rw [hM, compl_e0, compl_e1] at h2
  show A6L76Q.In3v a b
    (((M * g * M⁻¹ : GL (Fin 4) (ZMod 2)) : Matrix (Fin 4) (Fin 4) (ZMod 2)) *ᵥ z)
  rw [Units.val_mul, Units.val_mul, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hM]
  exact h2

theorem exists_e9_lineStab (α : ↥(alternatingGroup (Fin 8)) ≃* GL (Fin 4) (ZMod 2))
    {a b : Fin 4 → ZMod 2} (ha : a ≠ 0) (hb : b ≠ 0) (hab : a ≠ b) :
    ∃ x y : alternatingGroup (Fin 7), A6L76B.E9Pair x y ∧ α (altLift7 x) ∈ lineStab a b ∧
      α (altLift7 y) ∈ lineStab a b := by
  set M : GL (Fin 4) (ZMod 2) := (isUnit_compl ha hb hab).unit with hMdef
  have hM : (M : Matrix (Fin 4) (Fin 4) (ZMod 2)) = compl a b := rfl
  set U := CFSG.LocalAnalysis.ComponentInitial.LinearFlag.unitriangular 4 (ZMod 2) with hU
  set Y : Subgroup (alternatingGroup (Fin 8)) :=
    ((U.map Matrix.SpecialLinearGroup.toGL).map (MulAut.conj M).toMonoidHom).map
      α.symm.toMonoidHom with hY
  have hYcard : Nat.card Y = 64 := by
    rw [hY, Subgroup.card_map_of_injective α.symm.injective,
      Subgroup.card_map_of_injective (MulAut.conj M).injective,
      Subgroup.card_map_of_injective Matrix.SpecialLinearGroup.toGL_injective, hU,
      CFSG.LocalAnalysis.ComponentInitial.LinearFlag.card_unitriangular, Nat.card_zmod]
    norm_num
  have hYst : ∀ y ∈ Y, α y ∈ lineStab a b := by
    rintro _ ⟨_, ⟨_, ⟨u, hu, rfl⟩, rfl⟩, rfl⟩
    show α (α.symm ((MulAut.conj M) (Matrix.SpecialLinearGroup.toGL u))) ∈ lineStab a b
    rw [MulEquiv.apply_symm_apply, MulAut.conj_apply]
    refine stabL_conj (g := Matrix.SpecialLinearGroup.toGL u) M hM (stabL_std ?_)
    obtain ⟨h1, -⟩ := (CFSG.LocalAnalysis.ComponentInitial.LinearFlag.mem_unitriangular).1 hu
    exact ⟨h1 2 0 (by decide), h1 2 1 (by decide), h1 3 0 (by decide), h1 3 1 (by decide)⟩
  have hE0 := A6L76M.e9_rot (F := ZMod 2) (n := 4) rfl (p := 0) (q := 1) (r := 2) (s := 3)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  have hE1 := ((hE0.map (CFSG.Assembly.LowTwoRank.StatedSL 4 (ZMod 2)).subtype
    (CFSG.Assembly.LowTwoRank.StatedSL 4 (ZMod 2)).subtype_injective).map
      (MulAut.conj M).toMonoidHom (MulAut.conj M).injective).map α.symm.toMonoidHom
        α.symm.injective
  set a₀ := α.symm ((MulAut.conj M).toMonoidHom ((CFSG.Assembly.LowTwoRank.StatedSL 4
    (ZMod 2)).subtype (A6L76M.slOf (A6L76M.rot (0 : Fin 4) 1 : Matrix (Fin 4) (Fin 4) (ZMod 2))
      (A6L76M.det_rot (by decide))))) with ha₀
  set b₀ := α.symm ((MulAut.conj M).toMonoidHom ((CFSG.Assembly.LowTwoRank.StatedSL 4
    (ZMod 2)).subtype (A6L76M.slOf (A6L76M.rot (2 : Fin 4) 3 : Matrix (Fin 4) (Fin 4) (ZMod 2))
      (A6L76M.det_rot (by decide))))) with hb₀
  have hE : A6L76B.E9Pair a₀ b₀ := hE1
  obtain ⟨hr1, hr2⟩ := A6L76Q.BUT_rot
  have hst0 : α a₀ ∈ lineStab a b := by
    rw [ha₀, MulEquiv.apply_symm_apply]
    exact stabL_conj M hM (stabL_std hr1)
  have hst1 : α b₀ ∈ lineStab a b := by
    rw [hb₀, MulEquiv.apply_symm_apply]
    exact stabL_conj M hM (stabL_std hr2)
  have hp3 : ∀ g : alternatingGroup (Fin 8), g ^ 3 = 1 → (g : Perm (Fin 8)) ^ 3 = 1 :=
    fun g h => by rw [← Subgroup.coe_pow, h]; rfl
  obtain ⟨j, hj0, hj1⟩ := exists_common_fix (hp3 _ hE.2.1) (hp3 _ hE.2.2.1)
    (congrArg Subtype.val hE.1)
  obtain ⟨y, hyY, hy7⟩ := exists_mem_of_card64 hYcard j
  have hE2 := hE.map (MulAut.conj y⁻¹).toMonoidHom (MulAut.conj y⁻¹).injective
  have hfix : ∀ g : alternatingGroup (Fin 8), (g : Perm (Fin 8)) j = j →
      (((MulAut.conj y⁻¹).toMonoidHom g : alternatingGroup (Fin 8)) : Perm (Fin 8)) 7 = 7 := by
    intro g hg
    show ((y⁻¹ * g * y⁻¹⁻¹ : alternatingGroup (Fin 8)) : Perm (Fin 8)) 7 = 7
    rw [inv_inv, Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, Perm.mul_apply,
      Perm.mul_apply, hy7, hg, Perm.inv_eq_iff_eq, hy7]
  obtain ⟨x₇, hx₇⟩ := exists_altLift7 (hfix _ hj0)
  obtain ⟨y₇, hy₇⟩ := exists_altLift7 (hfix _ hj1)
  have hst : ∀ g : alternatingGroup (Fin 8), α g ∈ lineStab a b →
      α ((MulAut.conj y⁻¹).toMonoidHom g) ∈ lineStab a b := by
    intro g hg
    show α (y⁻¹ * g * y⁻¹⁻¹) ∈ lineStab a b
    rw [inv_inv, map_mul, map_mul, map_inv]
    exact (lineStab a b).mul_mem ((lineStab a b).mul_mem ((lineStab a b).inv_mem (hYst y hyY))
      hg) (hYst y hyY)
  refine ⟨x₇, y₇, e9_of_altLift7 (by rw [hx₇, hy₇]; exact hE2), ?_, ?_⟩
  · rw [hx₇]; exact hst _ hst0
  · rw [hy₇]; exact hst _ hst1

@[expose] def x0 : Perm (Fin 7) := swap 0 1 * swap 1 2 * (swap 3 4 * swap 4 5)

@[expose] def c012 : Perm (Fin 7) := swap 0 1 * swap 1 2

@[expose] def c345 : Perm (Fin 7) := swap 3 4 * swap 4 5

@[expose] def s7 : Perm (Fin 7) := swap 0 3 * swap 1 4 * swap 2 5

@[expose] def cent18 (i j : Fin 3) (b : Bool) : Perm (Fin 7) :=
  (if b then s7 else 1) * c012 ^ (i : ℕ) * c345 ^ (j : ℕ)

@[expose] def cmk (p q : Fin 7) : Fin 7 → Fin 7 := ![p, x0 p, x0 (x0 p), q, x0 q, x0 (x0 q), 6]

@[expose] def CentOK (p q : Fin 7) : Prop :=
  Function.Injective (cmk p q) → ∃ i j b, ∀ x, cent18 i j b x = cmk p q x

instance (p q : Fin 7) : Decidable (CentOK p q) := by
  unfold CentOK; infer_instance

theorem cent_ok : ∀ p q : Fin 7, CentOK p q := by
  decide +kernel

@[expose] def Cent18OK (i j : Fin 3) (b : Bool) : Prop :=
  Perm.sign (cent18 i j b) = 1 → cent18 i j b ^ 8 = 1 → cent18 i j b = 1

instance (i j : Fin 3) (b : Bool) : Decidable (Cent18OK i j b) := by
  unfold Cent18OK; infer_instance

theorem cent18_ok : ∀ i j b, Cent18OK i j b := by
  decide +kernel

theorem x0_fix : ∀ i : Fin 7, x0 i = i → i = 6 := by decide

theorem x0_vals : x0 0 = 1 ∧ x0 1 = 2 ∧ x0 3 = 4 ∧ x0 4 = 5 := by decide

theorem eq_cmk {σ : Perm (Fin 7)} (h : σ * x0 = x0 * σ) (i : Fin 7) :
    σ i = cmk (σ 0) (σ 3) i := by
  have hc : ∀ k, σ (x0 k) = x0 (σ k) := fun k => by
    rw [← Perm.mul_apply, h, Perm.mul_apply]
  obtain ⟨h0, h1, h3, h4⟩ := x0_vals
  have h6 : σ 6 = 6 := x0_fix _ (by rw [← hc, show x0 6 = 6 by decide])
  fin_cases i
  · rfl
  · show σ 1 = x0 (σ 0); rw [← hc, h0]
  · show σ 2 = x0 (x0 (σ 0)); rw [← hc, ← hc, h0, h1]
  · rfl
  · show σ 4 = x0 (σ 3); rw [← hc, h3]
  · show σ 5 = x0 (x0 (σ 3)); rw [← hc, ← hc, h3, h4]
  · exact h6

theorem eq_one_of_comm_x0 {σ : Perm (Fin 7)} (h : σ * x0 = x0 * σ) (hs : Perm.sign σ = 1)
    (h8 : σ ^ 8 = 1) : σ = 1 := by
  have hinj : Function.Injective (cmk (σ 0) (σ 3)) := by
    intro i j hij
    rw [← eq_cmk h, ← eq_cmk h] at hij
    exact σ.injective hij
  obtain ⟨i, j, b, hτσ⟩ := cent_ok (σ 0) (σ 3) hinj
  have e : cent18 i j b = σ := Equiv.ext fun x => (hτσ x).trans (eq_cmk h x).symm
  rw [← e] at hs h8 ⊢
  exact cent18_ok i j b hs h8

theorem x0_cycleType : x0.cycleType = {3, 3} := by
  have h1 : c012.IsThreeCycle := card_support_eq_three_iff.1 (by decide +kernel)
  have h2 : c345.IsThreeCycle := card_support_eq_three_iff.1 (by decide +kernel)
  have hd : Perm.Disjoint c012 c345 := by
    intro i
    revert i
    decide
  show (c012 * c345).cycleType = {3, 3}
  rw [hd.cycleType_mul, show c012.cycleType = {3} from h1, show c345.cycleType = {3} from h2]
  decide

theorem isThreeCycle_or_conj {x : Perm (Fin 7)} (h3 : x ^ 3 = 1) (h1 : x ≠ 1) :
    x.IsThreeCycle ∨ IsConj x x0 := by
  have hmem : ∀ n ∈ x.cycleType, n = 3 := by
    intro n hn
    have hd : n ∣ 3 := (Perm.dvd_of_mem_cycleType hn).trans (orderOf_dvd_of_pow_eq_one h3)
    have h2 := Perm.two_le_of_mem_cycleType hn
    rcases (Nat.dvd_prime Nat.prime_three).1 hd with h | h <;> omega
  have hrep : x.cycleType = Multiset.replicate (Multiset.card x.cycleType) 3 :=
    Multiset.eq_replicate.2 ⟨rfl, hmem⟩
  have hsum : Multiset.card x.cycleType * 3 ≤ 7 := by
    have h := Perm.sum_cycleType_le x
    rw [hrep, Multiset.sum_replicate, smul_eq_mul, Fintype.card_fin] at h
    exact h
  have hne : Multiset.card x.cycleType ≠ 0 := by
    intro h
    apply h1
    rw [← Perm.cycleType_eq_zero, Multiset.card_eq_zero.1 h]
  have hk : Multiset.card x.cycleType = 1 ∨ Multiset.card x.cycleType = 2 := by omega
  rcases hk with hk | hk
  · left
    show x.cycleType = {3}
    rw [hrep, hk]
    decide
  · right
    rw [Perm.isConj_iff_cycleType_eq, hrep, hk, x0_cycleType]
    decide

theorem eq_one_of_comm_order_three {x σ : Perm (Fin 7)} (h3 : x ^ 3 = 1) (h1 : x ≠ 1)
    (hx : ¬ x.IsThreeCycle) (hσx : σ * x = x * σ) (hs : Perm.sign σ = 1) (h8 : σ ^ 8 = 1) :
    σ = 1 := by
  obtain ⟨c, hc⟩ := isConj_iff.1 ((isThreeCycle_or_conj h3 h1).resolve_left hx)
  have h' : (c * σ * c⁻¹) * x0 = x0 * (c * σ * c⁻¹) := by
    rw [← hc]
    calc c * σ * c⁻¹ * (c * x * c⁻¹) = c * (σ * x) * c⁻¹ := by group
      _ = c * (x * σ) * c⁻¹ := by rw [hσx]
      _ = c * x * c⁻¹ * (c * σ * c⁻¹) := by group
  have hs' : Perm.sign (c * σ * c⁻¹) = 1 := by
    rw [Perm.sign_mul, Perm.sign_mul, Perm.sign_inv, hs, mul_one, Int.units_mul_self]
  have h8' : (c * σ * c⁻¹) ^ 8 = 1 := by rw [conj_pow, h8, mul_one, mul_inv_cancel]
  have := eq_one_of_comm_x0 h' hs' h8'
  have e : σ = c⁻¹ * (c * σ * c⁻¹) * c := by group
  rw [e, this, mul_one, inv_mul_cancel]

theorem fpf_of_isThreeCycle (α : ↥(alternatingGroup (Fin 8)) ≃* GL (Fin 4) (ZMod 2))
    {c : alternatingGroup (Fin 7)} (hc : (c : Perm (Fin 7)).IsThreeCycle) (v : Fin 4 → ZMod 2)
    (hv : ((α (altLift7 c) : GL (Fin 4) (ZMod 2)) : Matrix (Fin 4) (Fin 4) (ZMod 2)) *ᵥ v = v) :
    v = 0 := by
  have ht : ((B45Alt7.gen7 false : alternatingGroup (Fin 7)) : Perm (Fin 7)).IsThreeCycle :=
    card_support_eq_three_iff.1 (by decide +kernel)
  obtain ⟨g, hg⟩ := isConj_iff.1 (alternatingGroup.isThreeCycle_isConj (by simp) hc ht)
  set N : GL (Fin 4) (ZMod 2) := α (altLift7 g) with hN
  have e : α (altLift7 (B45Alt7.gen7 false)) = N * α (altLift7 c) * N⁻¹ := by
    rw [← hg, map_mul, map_mul, map_inv, map_mul, map_mul, map_inv]
  rw [A6L76R.altLift7_gen7] at e
  have hw : ((α A6L76O.t8 : GL (Fin 4) (ZMod 2)) : Matrix (Fin 4) (Fin 4) (ZMod 2)) *ᵥ
      ((N : Matrix (Fin 4) (Fin 4) (ZMod 2)) *ᵥ v) =
        (N : Matrix (Fin 4) (Fin 4) (ZMod 2)) *ᵥ v := by
    rw [e, Units.val_mul, Units.val_mul, Matrix.mulVec_mulVec, Matrix.mul_assoc,
      Matrix.mul_assoc, ← Units.val_mul N⁻¹ N, inv_mul_cancel, Units.val_one, Matrix.mul_one,
      ← Matrix.mulVec_mulVec, hv]
  have h0 := A6L76R.fpf_t8 α _ hw
  have := congrArg (((N⁻¹ : GL (Fin 4) (ZMod 2)) : Matrix (Fin 4) (Fin 4) (ZMod 2)) *ᵥ ·) h0
  simp only [Matrix.mulVec_mulVec, Matrix.mulVec_zero] at this
  rwa [← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mulVec] at this

end A6L76S

end CFSG.Quasithin.H13.A6
