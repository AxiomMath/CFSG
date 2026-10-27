module

public import CFSG.Quasithin.Background.SmithD37Row
public import CFSG.Quasithin.Background.SmithD37Fix
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixIII.Basic

public section

namespace CFSG.Quasithin.SmithD37

open scoped Matrix

section Mat

variable {F : Type} [Field F] {d : ℕ}

private def rowsIn (Y : Submodule F (Fin d → F)) : AddSubgroup (Matrix (Fin d) (Fin d) F) where
  carrier := {X | ∀ i, X i ∈ Y}
  zero_mem' := fun _ => Y.zero_mem
  add_mem' := fun hX hX' i => Y.add_mem (hX i) (hX' i)
  neg_mem' := fun hX i => Y.neg_mem (hX i)

private theorem mul_mem_rowsIn {Y : Submodule F (Fin d → F)} (g : Matrix (Fin d) (Fin d) F)
    {X : Matrix (Fin d) (Fin d) F} (hX : X ∈ rowsIn Y) : g * X ∈ rowsIn Y := by
  intro i
  have : (g * X) i = ∑ j, g i j • X j := by
    ext k
    simp [Matrix.mul_apply, Finset.sum_apply]
  rw [this]
  exact Y.sum_mem fun j _ => Y.smul_mem _ (hX j)

private theorem vecMulVec_single_row (i : Fin d) (y : Fin d → F) :
    Matrix.vecMulVec (Pi.single i 1) y i = y := by
  ext k
  simp [Matrix.vecMulVec_apply]

private theorem sum_vecMulVec_single (X : Matrix (Fin d) (Fin d) F) :
    ∑ i, Matrix.vecMulVec (Pi.single i 1) (X i) = X := by
  ext a b
  simp [Matrix.sum_apply, Matrix.vecMulVec_apply, Pi.single_apply]

private def colHom (j : Fin d) : Matrix (Fin d) (Fin d) F →+ (Fin d → F) where
  toFun X i := X i j
  map_zero' := rfl
  map_add' _ _ := rfl

private theorem colHom_apply (j : Fin d) (X : Matrix (Fin d) (Fin d) F) (i : Fin d) :
    colHom j X i = X i j :=
  rfl

private theorem colHom_mul (j : Fin d) (g X : Matrix (Fin d) (Fin d) F) :
    colHom j (g * X) = g *ᵥ colHom j X :=
  rfl

private def rowSpace (T : AddSubgroup (Matrix (Fin d) (Fin d) F)) : Submodule F (Fin d → F) where
  carrier := {y | ∀ x, Matrix.vecMulVec x y ∈ T}
  add_mem' := by
    intro y y' hy hy' x
    rw [Matrix.vecMulVec_add]
    exact T.add_mem (hy x) (hy' x)
  zero_mem' := by
    intro x
    rw [Matrix.vecMulVec_zero]
    exact T.zero_mem
  smul_mem' := by
    intro c y hy x
    rw [Matrix.vecMulVec_smul, ← Matrix.smul_vecMulVec]
    exact hy _

variable {ι : Type} (ρ : ι → Matrix (Fin d) (Fin d) F)

private def IsLInv (T : AddSubgroup (Matrix (Fin d) (Fin d) F)) : Prop :=
  ∀ l, ∀ X ∈ T, ρ l * X ∈ T

private theorem exists_vecMulVec_of_minimal
    (hirr : ∀ S : AddSubgroup (Fin d → F), (∀ l, ∀ v ∈ S, ρ l *ᵥ v ∈ S) → S = ⊥ ∨ S = ⊤)
    (hend : ∀ φ : (Fin d → F) →+ (Fin d → F), (∀ l v, φ (ρ l *ᵥ v) = ρ l *ᵥ φ v) →
      ∃ c : F, ∀ v, φ v = c • v)
    {T : AddSubgroup (Matrix (Fin d) (Fin d) F)} (hT : IsLInv ρ T) (hT0 : T ≠ ⊥)
    (hmin : ∀ T' ≤ T, IsLInv ρ T' → T' = ⊥ ∨ T' = T) :
    ∃ c : Fin d → F, c ≠ 0 ∧ ∀ x, Matrix.vecMulVec x c ∈ T := by
  obtain ⟨X, hXT, hX0⟩ := T.bot_or_exists_ne_zero.resolve_left hT0
  obtain ⟨i, j, hij⟩ : ∃ i j, X i j ≠ 0 := by
    by_contra! h
    exact hX0 (Matrix.ext h)
  have hXj : colHom j X ≠ 0 := fun h => hij (congrFun h i)
  have hI : T.map (colHom j) = ⊤ := by
    refine (hirr _ ?_).resolve_left ?_
    · rintro l _ ⟨Z, hZ, rfl⟩
      exact ⟨ρ l * Z, hT l Z hZ, colHom_mul j _ _⟩
    · intro h
      have : colHom j X ∈ T.map (colHom j) := AddSubgroup.mem_map_of_mem _ hXT
      rw [h, AddSubgroup.mem_bot] at this
      exact hXj this
  have hK : T ⊓ (colHom j).ker = ⊥ := by
    refine (hmin _ inf_le_left ?_).resolve_right ?_
    · intro l Z hZ
      rw [AddSubgroup.mem_inf, AddMonoidHom.mem_ker] at hZ ⊢
      refine ⟨hT l Z hZ.1, ?_⟩
      rw [colHom_mul, hZ.2, Matrix.mulVec_zero]
    · intro h
      have : X ∈ T ⊓ (colHom j).ker := by
        rw [h]
        exact hXT
      exact hXj (AddMonoidHom.mem_ker.mp this.2)
  let e : T →+ (Fin d → F) := (colHom j).comp T.subtype
  have he : Function.Bijective e := by
    constructor
    · rw [injective_iff_map_eq_zero]
      intro Z hZ
      have : (Z : Matrix (Fin d) (Fin d) F) ∈ T ⊓ (colHom j).ker := ⟨Z.2, hZ⟩
      rw [hK, AddSubgroup.mem_bot] at this
      exact Subtype.ext this
    · intro v
      obtain ⟨Z, hZ, rfl⟩ : v ∈ T.map (colHom j) := hI ▸ AddSubgroup.mem_top v
      exact ⟨⟨Z, hZ⟩, rfl⟩
  let E := AddEquiv.ofBijective e he
  have hEj : ∀ v, colHom j (E.symm v : Matrix (Fin d) (Fin d) F) = v := fun v =>
    E.apply_symm_apply v
  have hE : ∀ l v, (E.symm (ρ l *ᵥ v) : Matrix (Fin d) (Fin d) F) =
      ρ l * (E.symm v : Matrix (Fin d) (Fin d) F) := by
    intro l v
    have h1 : E ⟨ρ l * (E.symm v : Matrix (Fin d) (Fin d) F), hT l _ (E.symm v).2⟩ =
        ρ l *ᵥ v := by
      change colHom j (ρ l * (E.symm v : Matrix (Fin d) (Fin d) F)) = _
      rw [colHom_mul, hEj]
    rw [← h1, E.symm_apply_apply]
  have hφ : ∀ k, ∃ c : F, ∀ v, colHom k (E.symm v : Matrix (Fin d) (Fin d) F) = c • v := by
    intro k
    refine hend ((colHom k).comp (T.subtype.comp E.symm.toAddMonoidHom)) fun l v => ?_
    change colHom k (E.symm (ρ l *ᵥ v) : Matrix (Fin d) (Fin d) F) =
      ρ l *ᵥ colHom k (E.symm v : Matrix (Fin d) (Fin d) F)
    rw [hE, colHom_mul]
  choose c hc using hφ
  have hEc : ∀ x, (E.symm x : Matrix (Fin d) (Fin d) F) = Matrix.vecMulVec x c := by
    intro x
    ext a b
    have := congrFun (hc b x) a
    rw [colHom_apply] at this
    rw [this, Matrix.vecMulVec_apply, Pi.smul_apply, smul_eq_mul, mul_comm]
  refine ⟨c, ?_, fun x => hEc x ▸ (E.symm x).2⟩
  rintro rfl
  apply hXj
  rw [← hEj (colHom j X), hEc, Matrix.vecMulVec_zero, map_zero]

private theorem exists_eq_rowsIn [Finite F]
    (hirr : ∀ S : AddSubgroup (Fin d → F), (∀ l, ∀ v ∈ S, ρ l *ᵥ v ∈ S) → S = ⊥ ∨ S = ⊤)
    (hend : ∀ φ : (Fin d → F) →+ (Fin d → F), (∀ l v, φ (ρ l *ᵥ v) = ρ l *ᵥ φ v) →
      ∃ c : F, ∀ v, φ v = c • v)
    {T : AddSubgroup (Matrix (Fin d) (Fin d) F)} (hT : IsLInv ρ T) :
    ∃ Y : Submodule F (Fin d → F), T = rowsIn Y := by
  classical
  have hYT : rowsIn (rowSpace T) ≤ T := by
    intro X hX
    rw [← sum_vecMulVec_single X]
    exact T.sum_mem fun i _ => hX i _
  obtain ⟨Yc, hYc⟩ := Submodule.exists_isCompl (rowSpace T)
  have h0 : T ⊓ rowsIn Yc = ⊥ := by
    by_contra hne
    obtain ⟨T', ⟨hT'0, hT'le, hT'inv⟩, hmin⟩ := wellFounded_lt.has_min
      {T' | T' ≠ ⊥ ∧ T' ≤ T ⊓ rowsIn Yc ∧ IsLInv ρ T'}
      ⟨_, hne, le_rfl, fun l X hX => ⟨hT l X hX.1, mul_mem_rowsIn _ hX.2⟩⟩
    obtain ⟨c, hc0, hc⟩ := exists_vecMulVec_of_minimal ρ hirr hend hT'inv hT'0
      fun T'' hle hinv => by
        by_contra! h
        exact hmin T'' ⟨h.1, hle.trans hT'le, hinv⟩ (lt_of_le_of_ne hle h.2)
    obtain ⟨i, -⟩ := Function.ne_iff.mp hc0
    have hcY : c ∈ rowSpace T := fun x => (hT'le (hc x)).1
    have hcYc : c ∈ Yc := by
      have := (hT'le (hc (Pi.single i 1))).2 i
      rwa [vecMulVec_single_row] at this
    have := Submodule.mem_inf.mpr ⟨hcY, hcYc⟩
    rw [hYc.inf_eq_bot, Submodule.mem_bot] at this
    exact hc0 this
  refine ⟨rowSpace T, le_antisymm (fun X hX => ?_) hYT⟩
  have hdec : ∀ a, ∃ y ∈ rowSpace T, ∃ z ∈ Yc, y + z = X a := fun a =>
    Submodule.mem_sup.mp (hYc.sup_eq_top ▸ Submodule.mem_top)
  obtain ⟨A, B, hA, hB, hAB⟩ : ∃ A B : Matrix (Fin d) (Fin d) F, A ∈ rowsIn (rowSpace T) ∧
      B ∈ rowsIn Yc ∧ A + B = X := by
    choose A hA B hB hAB using hdec
    exact ⟨A, B, hA, hB, funext hAB⟩
  have hBT : B ∈ T ⊓ rowsIn Yc := by
    refine ⟨?_, hB⟩
    rw [eq_sub_of_add_eq' hAB]
    exact T.sub_mem hX (hYT hA)
  rw [h0, AddSubgroup.mem_bot] at hBT
  rw [← hAB, hBT, add_zero]
  exact hA

end Mat

section Model

variable {U : Type} [CommGroup U] {L₁ L₂ : Subgroup (MulAut U)} {F : Type} [Field F] {d : ℕ}

private def rowSubEquiv (Mm : MatModel L₁ L₂ F d) (Y : Submodule F (Fin d → F)) :
    ↥(rowSub Mm Y) ≃ (Fin d → ↥Y) where
  toFun u i := ⟨Multiplicative.toAdd (Mm.β u) i, u.2 i⟩
  invFun f := ⟨Mm.β.symm (Multiplicative.ofAdd fun i => (f i : Fin d → F)), fun i => by
    rw [MulEquiv.apply_symm_apply]
    exact (f i).2⟩
  left_inv u := by
    ext1
    simp
  right_inv f := by
    ext i : 2
    simp only [MulEquiv.apply_symm_apply]
    rfl

theorem card_rowSub (Mm : MatModel L₁ L₂ F d) (Y : Submodule F (Fin d → F)) :
    Nat.card ↥(rowSub Mm Y) = Nat.card F ^ (d * Module.finrank F Y) := by
  rw [Nat.card_congr (rowSubEquiv Mm Y), Nat.card_fun, Module.natCard_eq_pow_finrank (K := F),
    Nat.card_fin, ← pow_mul, mul_comm]

theorem rowSub_le_rowSub_iff (Mm : MatModel L₁ L₂ F d) (hd : 0 < d)
    {Y Y' : Submodule F (Fin d → F)} : rowSub Mm Y ≤ rowSub Mm Y' ↔ Y ≤ Y' := by
  refine ⟨fun h y hy => ?_, rowSub_mono Mm⟩
  have := h (rank1_mem_rowSub Mm (Pi.single ⟨0, hd⟩ 1) hy) ⟨0, hd⟩
  rwa [β_rank1, toAdd_ofAdd, vecMulVec_single_row] at this

private def matSub (Mm : MatModel L₁ L₂ F d) (S : Subgroup U) :
    AddSubgroup (Matrix (Fin d) (Fin d) F) where
  carrier := {X | Mm.β.symm (Multiplicative.ofAdd X) ∈ S}
  zero_mem' := by simp [S.one_mem]
  add_mem' := by
    intro X X' hX hX'
    simpa [ofAdd_add] using S.mul_mem hX hX'
  neg_mem' := by
    intro X hX
    simpa [ofAdd_neg] using S.inv_mem hX

theorem exists_eq_rowSub [Fintype F] (Mm : MatModel L₁ L₂ F d) {S : Subgroup U}
    (hS : IsInvBy L₁ S) : ∃ Y, S = rowSub Mm Y := by
  have hT : IsLInv (fun l : ↥L₁ =>
      ((Mm.R₁ l : Matrix.GeneralLinearGroup (Fin d) F) : Matrix (Fin d) (Fin d) F))
      (matSub Mm S) := by
    intro l X hX
    have : Mm.β.symm (Multiplicative.ofAdd
        (((Mm.R₁ l : Matrix.GeneralLinearGroup (Fin d) F) : Matrix (Fin d) (Fin d) F) * X)) =
        (l : MulAut U) (Mm.β.symm (Multiplicative.ofAdd X)) := by
      apply Mm.β.injective
      rw [Mm.act₁, MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply, toAdd_ofAdd]
    change Mm.β.symm _ ∈ S
    rw [this]
    exact hS _ l.2 _ hX
  obtain ⟨Y, hY⟩ := exists_eq_rowsIn _ Mm.irr₁ Mm.end₁ hT
  refine ⟨Y, ?_⟩
  ext u
  have : u ∈ S ↔ Multiplicative.toAdd (Mm.β u) ∈ matSub Mm S := by
    change _ ↔ Mm.β.symm (Multiplicative.ofAdd (Multiplicative.toAdd (Mm.β u))) ∈ S
    rw [ofAdd_toAdd, MulEquiv.symm_apply_apply]
  rw [this, hY]
  rfl

end Model

section Act

variable {U : Type} [CommGroup U] {L₁ L₂ : Subgroup (MulAut U)} {F : Type} [Field F] {d : ℕ}

open scoped Pointwise

private theorem card_smul (a : MulAut U) (T : Subgroup U) : Nat.card ↥(a • T) = Nat.card ↥T := by
  rw [Subgroup.pointwise_smul_def]
  exact Subgroup.card_map_of_injective (MulAction.injective a)

private theorem isInvBy_smul_rowSub (Mm : MatModel L₁ L₂ F d) {a : MulAut U}
    (ha : ∀ l ∈ L₁, a⁻¹ * l * a ∈ L₁) (Y₁ : Submodule F (Fin d → F)) :
    IsInvBy L₁ (a • rowSub Mm Y₁) := by
  intro l hl x hx
  obtain ⟨t, ht, rfl⟩ := (Subgroup.mem_smul_pointwise_iff_exists _ _ _).mp hx
  have : l (a • t) = a • (a⁻¹ * l * a) t := by
    simp [MulAut.smul_def, MulAut.mul_apply]
  rw [this]
  exact Subgroup.smul_mem_pointwise_smul _ _ _ (rowSub_inv₁ Mm Y₁ ⟨_, ha l hl⟩ ht)

end Act

section Count

variable {F : Type} [Field F]

private theorem pos_of_ne_bot {d : ℕ} {Y : Submodule F (Fin d → F)} (hY : Y ≠ ⊥) : 0 < d := by
  obtain ⟨y, -, hy⟩ := (Submodule.ne_bot_iff Y).mp hY
  obtain ⟨i, -⟩ := Function.ne_iff.mp hy
  exact i.pos

private theorem finrank_comap_subtype {V : Type} [AddCommGroup V] [Module F V]
    {Y Y₁ : Submodule F V} (h : Y₁ ≤ Y) :
    Module.finrank F (Y₁.comap Y.subtype) = Module.finrank F Y₁ := by
  rw [← Submodule.finrank_map_subtype_eq, Submodule.map_comap_subtype, inf_eq_right.mpr h]

private theorem card_le_finrank {V : Type} [AddCommGroup V] [Module F V] (Y : Submodule F V)
    (k : ℕ) : Nat.card {Y₁ : Submodule F V // Y₁ ≤ Y ∧ Module.finrank F Y₁ = k} =
      Nat.card {W : Submodule F Y // Module.finrank F W = k} :=
  Nat.card_congr
    { toFun := fun Y₁ => ⟨Y₁.1.comap Y.subtype, (finrank_comap_subtype Y₁.2.1).trans Y₁.2.2⟩
      invFun := fun W => ⟨W.1.map Y.subtype, Submodule.map_subtype_le _ _,
        (Submodule.finrank_map_subtype_eq _ _).trans W.2⟩
      left_inv := fun Y₁ => Subtype.ext <| by
        simp only [Submodule.map_comap_subtype, inf_eq_right.mpr Y₁.2.1]
      right_inv := fun W => Subtype.ext <|
        Submodule.comap_map_eq_of_injective Y.injective_subtype _ }

private theorem card_lines [Finite F] (V : Type) [AddCommGroup V] [Module F V] :
    Nat.card {W : Submodule F V // Module.finrank F W = 1} =
      ∑ i ∈ Finset.range (Module.finrank F V), Nat.card F ^ i := by
  rw [← Nat.card_congr (Projectivization.equivSubmodule F V)]
  exact Projectivization.card_of_finrank F V rfl

private theorem card_hyperplanes [Finite F] (V : Type) [AddCommGroup V] [Module F V]
    [FiniteDimensional F V] :
    Nat.card {W : Submodule F V // Module.finrank F W + 1 = Module.finrank F V} =
      ∑ i ∈ Finset.range (Module.finrank F V), Nat.card F ^ i := by
  let e : Submodule F V ≃ Submodule F (Module.Dual F V) :=
    (Subspace.orderIsoFiniteDimensional (K := F) (V := V)).toEquiv.trans OrderDual.ofDual
  rw [Nat.card_congr (e.subtypeEquiv
      (q := fun H : Submodule F (Module.Dual F V) => Module.finrank F H = 1) fun W => ?_),
    card_lines, Subspace.dual_finrank_eq]
  have := Subspace.finrank_add_finrank_dualAnnihilator_eq W
  change _ ↔ Module.finrank F W.dualAnnihilator = 1
  omega

private theorem odd_geom_sum {q : ℕ} (hq : Even q) {n : ℕ} (hn : 0 < n) :
    Odd (∑ i ∈ Finset.range n, q ^ i) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  rw [Finset.sum_range_succ', pow_zero]
  exact Even.add_one (Finset.even_sum _ fun i _ => Nat.even_pow.mpr ⟨hq, i.succ_ne_zero⟩)

private theorem even_card [Fintype F] [CharP F 2] : Even (Nat.card F) := by
  rw [even_iff_two_dvd, Nat.card_eq_fintype_card, ← CharP.cast_eq_zero_iff F 2]
  exact FiniteField.cast_card_eq_zero F

end Count

section Fix

variable {U : Type} [CommGroup U] [Finite U] {L₁ L₂ : Subgroup (MulAut U)}
  {F : Type} [Field F] [Fintype F] {d : ℕ}

open scoped Pointwise

private theorem exists_inv_of_odd (Mm : MatModel L₁ L₂ F d) (hd : 0 < d)
    {P : Subgroup (MulAut U)} (hP : IsPGroup 2 ↥P) (hPN : ∀ a ∈ P, ∀ l ∈ L₁, a * l * a⁻¹ ∈ L₁)
    {Y : Submodule F (Fin d → F)} (hY : IsInvBy P (rowSub Mm Y)) {k : ℕ}
    (hodd : Odd (Nat.card {Y₁ : Submodule F (Fin d → F) // Y₁ ≤ Y ∧ Module.finrank F Y₁ = k})) :
    ∃ Y₁ ≤ Y, Module.finrank F Y₁ = k ∧ IsInvBy P (rowSub Mm Y₁) := by
  classical
  let φ : {Y₁ : Submodule F (Fin d → F) // Y₁ ≤ Y ∧ Module.finrank F Y₁ = k} → Subgroup U :=
    fun Y₁ => rowSub Mm Y₁.1
  have hφ : Function.Injective φ := fun Y₁ Y₂ h => Subtype.ext (le_antisymm
    ((rowSub_le_rowSub_iff Mm hd).mp h.le) ((rowSub_le_rowSub_iff Mm hd).mp h.ge))
  have hq : 2 ≤ Nat.card F := Finite.one_lt_card
  have hstab : ∀ a : ↥P, ∀ Y₁, ∃ Y₂, φ Y₂ = (a : MulAut U) • φ Y₁ := by
    intro a Y₁
    have ha : ∀ l ∈ L₁, (a : MulAut U)⁻¹ * l * a ∈ L₁ := fun l hl => by
      simpa using hPN _ (P.inv_mem a.2) l hl
    obtain ⟨Y₂, hY₂⟩ := exists_eq_rowSub Mm (isInvBy_smul_rowSub Mm ha Y₁.1)
    have hle : Y₂ ≤ Y := by
      rw [← rowSub_le_rowSub_iff Mm hd, ← hY₂]
      intro x hx
      obtain ⟨t, ht, rfl⟩ := (Subgroup.mem_smul_pointwise_iff_exists _ _ _).mp hx
      exact hY _ a.2 _ (rowSub_mono Mm Y₁.2.1 ht)
    have hk : Module.finrank F Y₂ = k := by
      have h1 := card_smul (a : MulAut U) (rowSub Mm Y₁.1)
      rw [hY₂, card_rowSub, card_rowSub, Y₁.2.2] at h1
      exact Nat.eq_of_mul_eq_mul_left hd (Nat.pow_right_injective hq h1)
    exact ⟨⟨Y₂, hle, hk⟩, hY₂.symm⟩
  let A : SubMulAction ↥P (Subgroup U) :=
    { carrier := Set.range φ
      smul_mem' := by
        rintro a _ ⟨Y₁, rfl⟩
        exact hstab a Y₁ }
  have hA : Nat.card A =
      Nat.card {Y₁ : Submodule F (Fin d → F) // Y₁ ≤ Y ∧ Module.finrank F Y₁ = k} :=
    Nat.card_range_of_injective hφ
  have hmod := hP.card_modEq_card_fixedPoints A
  obtain ⟨⟨_, Y₁, rfl⟩, hfix⟩ : ∃ x : A, x ∈ MulAction.fixedPoints ↥P A := by
    by_contra! h
    have h0 : Nat.card (MulAction.fixedPoints ↥P A) = 0 :=
      Nat.card_eq_zero.mpr (Or.inl ⟨fun x => h x.1 x.2⟩)
    have h1 := Nat.odd_iff.mp hodd
    rw [Nat.ModEq, h0, hA] at hmod
    omega
  refine ⟨Y₁.1, Y₁.2.1, Y₁.2.2, fun a ha u hu => ?_⟩
  have h := congrArg Subtype.val (hfix ⟨a, ha⟩)
  rw [SubMulAction.val_smul] at h
  change a • φ Y₁ = φ Y₁ at h
  have := Subgroup.smul_mem_pointwise_smul u a (φ Y₁) hu
  rw [h] at this
  exact this

theorem exists_line_inv [CharP F 2] (Mm : MatModel L₁ L₂ F d) {P : Subgroup (MulAut U)}
    (hP : IsPGroup 2 ↥P) (hPN : ∀ a ∈ P, ∀ l ∈ L₁, a * l * a⁻¹ ∈ L₁)
    {Y : Submodule F (Fin d → F)} (hY : IsInvBy P (rowSub Mm Y)) (hY0 : Y ≠ ⊥) :
    ∃ y ∈ Y, y ≠ 0 ∧ IsInvBy P (rowSub Mm (Submodule.span F {y})) := by
  have hn : 0 < Module.finrank F Y :=
    Nat.pos_of_ne_zero fun h => hY0 (Submodule.finrank_eq_zero.mp h)
  obtain ⟨Y₁, hY₁, h1, hinv⟩ := exists_inv_of_odd Mm (pos_of_ne_bot hY0) hP hPN hY (k := 1)
    (by rw [card_le_finrank, card_lines]; exact odd_geom_sum even_card hn)
  obtain ⟨y, hy0, rfl⟩ : ∃ y : Fin d → F, y ≠ 0 ∧ Submodule.span F {y} = Y₁ :=
    ⟨_, Projectivization.rep_nonzero _,
      by rw [← Projectivization.submodule_eq, Projectivization.submodule_mk'' _ h1]⟩
  exact ⟨y, hY₁ (Submodule.mem_span_singleton_self y), hy0, hinv⟩

theorem exists_hyperplane_inv [CharP F 2] (Mm : MatModel L₁ L₂ F d) {P : Subgroup (MulAut U)}
    (hP : IsPGroup 2 ↥P) (hPN : ∀ a ∈ P, ∀ l ∈ L₁, a * l * a⁻¹ ∈ L₁)
    {Y : Submodule F (Fin d → F)} (hY : IsInvBy P (rowSub Mm Y)) (hY0 : Y ≠ ⊥) :
    ∃ Y' ≤ Y, Module.finrank F Y' + 1 = Module.finrank F Y ∧ IsInvBy P (rowSub Mm Y') := by
  have hn : 0 < Module.finrank F Y :=
    Nat.pos_of_ne_zero fun h => hY0 (Submodule.finrank_eq_zero.mp h)
  have hc : Nat.card {W : Submodule F Y // Module.finrank F W = Module.finrank F Y - 1} =
      Nat.card {W : Submodule F Y // Module.finrank F W + 1 = Module.finrank F Y} :=
    Nat.card_congr (Equiv.subtypeEquivRight fun W => by omega)
  obtain ⟨Y', hY', h1, hinv⟩ := exists_inv_of_odd Mm (pos_of_ne_bot hY0) hP hPN hY
    (k := Module.finrank F Y - 1)
    (by rw [card_le_finrank, hc, card_hyperplanes]; exact odd_geom_sum even_card hn)
  exact ⟨Y', hY', by omega, hinv⟩

end Fix

end CFSG.Quasithin.SmithD37
