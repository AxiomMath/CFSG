module

public import CFSG.RankThree.PartTwo.Sec21.Item233Res3ProofInner
public import CFSG.RankThree.PartTwo.Sec21.Item233InnerDiagonal
public import CFSG.RankThree.PartTwo.Sec21.Item233TablesMatrix
public import CFSG.RankThree.PartOne.KC.CommonEigenbasis
public import CFSG.RankThree.PartTwo.Sec21.Item23Tools

public section

namespace CFSG.RankThree.PartTwo.Sec21.Item233Res3Proof

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open Matrix
open CFSG.Assembly (IsElemAbelian)
open CFSG.RankThree.PartTwo.Sec21.InnerDiagonal (F4 SL34 inndiag mem_inndiag_of_pow card_F4
  card_units_F4 slConjugation_toGL_eq)
open CFSG.ComponentClassification.CatalogueBHigherLinearAction (slConjugation slConjugation_matrix)
open CFSG.RankThree.PartTwo.Sec21.Tables (IsBlockDiag isBlockDiag_of_commute reindexSL
  coe_reindexSL)

namespace SL34Lines

section Model

variable (ω : F4ˣ)

@[expose] noncomputable def dω : Fin 3 → F4ˣ := ![1, ω, ω⁻¹]

@[expose] noncomputable def dω' : Fin 3 → F4ˣ := ![1, ω⁻¹, ω]

@[expose] noncomputable def x0 : SL34 :=
  ⟨diagonal fun i => (dω ω i : F4), by
    simp [det_diagonal, Fin.prod_univ_three, dω]⟩

@[expose] noncomputable def x0' : SL34 :=
  ⟨diagonal fun i => (dω' ω i : F4), by
    simp [det_diagonal, Fin.prod_univ_three, dω']⟩

theorem coe_x0 : ((x0 ω : SL34) : Matrix (Fin 3) (Fin 3) F4) = diagonal fun i => (dω ω i : F4) :=
  rfl

theorem x0_inv : (x0 ω)⁻¹ = x0' ω := by
  apply inv_eq_of_mul_eq_one_right
  apply Subtype.ext
  change (diagonal fun i => (dω ω i : F4)) * (diagonal fun i => (dω' ω i : F4)) = 1
  rw [diagonal_mul_diagonal, ← diagonal_one]
  congr 1
  funext i
  fin_cases i <;> simp [dω, dω']

variable {ω}

theorem ω_ne_inv (hω3 : ω ^ 3 = 1) (hω1 : ω ≠ 1) : ω ≠ ω⁻¹ := by
  intro h
  apply hω1
  have h2 : ω * ω = 1 := by
    calc ω * ω = ω * ω⁻¹ := by rw [← h]
      _ = 1 := mul_inv_cancel ω
  calc ω = ω ^ 3 * (ω * ω)⁻¹ := by group
    _ = 1 := by rw [hω3, h2, inv_one, one_mul]

theorem dω_injective (hω3 : ω ^ 3 = 1) (hω1 : ω ≠ 1) :
    Function.Injective fun i => (dω ω i : F4) := by
  have h1 : (1 : F4) ≠ ω := fun h => hω1 (Units.ext h.symm)
  have h2 : (1 : F4) ≠ ((ω⁻¹ : F4ˣ) : F4) := by
    intro h
    apply hω1
    have : ω⁻¹ = 1 := Units.ext h.symm
    rw [inv_eq_one] at this
    exact this
  have h3 : (ω : F4) ≠ ((ω⁻¹ : F4ˣ) : F4) := fun h => ω_ne_inv hω3 hω1 (Units.ext h)
  intro i j hij
  fin_cases i <;> fin_cases j <;> simp_all [dω]

theorem offDiag_eq_zero_of_commute (hω3 : ω ^ 3 = 1) (hω1 : ω ≠ 1)
    {M : Matrix (Fin 3) (Fin 3) F4} (h : M * (x0 ω : Matrix (Fin 3) (Fin 3) F4) =
      (x0 ω : Matrix (Fin 3) (Fin 3) F4) * M) :
    ∀ i j, i ≠ j → M i j = 0 := by
  rw [coe_x0] at h
  have hb : IsBlockDiag (fun i => (dω ω i : F4)) M := isBlockDiag_of_commute h
  intro i j hij
  exact hb i j fun e => hij (dω_injective hω3 hω1 e)

theorem pattern_of (hω3 : ω ^ 3 = 1) (hω1 : ω ≠ 1) {W : Matrix (Fin 3) (Fin 3) F4}
    (h : W * (x0 ω : Matrix (Fin 3) (Fin 3) F4) = (x0' ω : Matrix (Fin 3) (Fin 3) F4) * W) :
    W 0 1 = 0 ∧ W 0 2 = 0 ∧ W 1 0 = 0 ∧ W 1 1 = 0 ∧ W 2 0 = 0 ∧ W 2 2 = 0 := by
  have h1 : (1 : F4) ≠ ω := fun h => hω1 (Units.ext h.symm)
  have h2 : (1 : F4) ≠ ((ω⁻¹ : F4ˣ) : F4) := by
    intro h
    apply hω1
    have : ω⁻¹ = 1 := Units.ext h.symm
    rw [inv_eq_one] at this
    exact this
  have h3 : (ω : F4) ≠ ((ω⁻¹ : F4ˣ) : F4) := fun h => ω_ne_inv hω3 hω1 (Units.ext h)
  have key : ∀ i j, (dω ω j : F4) ≠ (dω' ω i : F4) → W i j = 0 := by
    intro i j hij
    have e := congrFun (congrFun h i) j
    change (W * diagonal fun i => (dω ω i : F4)) i j =
      ((diagonal fun i => (dω' ω i : F4)) * W) i j at e
    rw [mul_diagonal, diagonal_mul] at e
    have e' : ((dω ω j : F4) - (dω' ω i : F4)) * W i j = 0 := by linear_combination e
    rcases mul_eq_zero.mp e' with h0 | h0
    · exact absurd (sub_eq_zero.mp h0) hij
    · exact h0
  exact ⟨key 0 1 h1.symm, key 0 2 h2.symm, key 1 0 h2, key 1 1 h3, key 2 0 h1, key 2 2 h3.symm⟩

theorem commute_of_pattern {W g : Matrix (Fin 3) (Fin 3) F4}
    (hW : W 0 1 = 0 ∧ W 0 2 = 0 ∧ W 1 0 = 0 ∧ W 1 1 = 0 ∧ W 2 0 = 0 ∧ W 2 2 = 0)
    (hg : ∀ i j, i ≠ j → g i j = 0) (h12 : g 1 1 = g 2 2) : W * g = g * W := by
  obtain ⟨h01, h02, h10, h11, h20, h22⟩ := hW
  have g01 := hg 0 1 (by decide)
  have g02 := hg 0 2 (by decide)
  have g10 := hg 1 0 (by decide)
  have g12 := hg 1 2 (by decide)
  have g20 := hg 2 0 (by decide)
  have g21 := hg 2 1 (by decide)
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_three, h01, h02, h10, h11, h20, h22, g01, g02, g10,
      g12, g20, g21, h12, mul_comm]

end Model

section Root

@[expose] noncomputable def tvM (t : F4) : Matrix (Fin 3) (Fin 3) F4 :=
  !![1, 0, 0; 0, 1, t; 0, 0, 1]

theorem tvM_mul (s t : F4) : tvM s * tvM t = tvM (s + t) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [tvM, Matrix.mul_apply, Fin.sum_univ_three, add_comm]

theorem tvM_zero : tvM 0 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

@[expose] noncomputable def tv : Multiplicative F4 →* SL34 where
  toFun t := ⟨tvM (Multiplicative.toAdd t), by simp [tvM, Matrix.det_fin_three]⟩
  map_one' := Subtype.ext tvM_zero
  map_mul' s t := Subtype.ext (by
    change tvM (Multiplicative.toAdd (s * t)) = tvM (Multiplicative.toAdd s) *
      tvM (Multiplicative.toAdd t)
    rw [tvM_mul, toAdd_mul])

theorem coe_tv (t : F4) :
    ((tv (Multiplicative.ofAdd t) : SL34) : Matrix (Fin 3) (Fin 3) F4) = tvM t := rfl

theorem tv_injective : Function.Injective tv := by
  intro s t h
  have h' := congrFun (congrFun (congrArg (fun g : SL34 => (g : Matrix (Fin 3) (Fin 3) F4)) h) 1) 2
  change tvM (Multiplicative.toAdd s) 1 2 = tvM (Multiplicative.toAdd t) 1 2 at h'
  simp only [tvM] at h'
  simpa using h'

@[expose] noncomputable def V0 : Subgroup SL34 := tv.range

theorem card_V0 : Nat.card V0 = 4 := by
  rw [V0, ← Nat.card_congr (MonoidHom.ofInjective tv_injective).toEquiv,
    Nat.card_congr Multiplicative.toAdd, card_F4]

theorem isElemAbelian_V0 : IsElemAbelian 2 V0 := by
  refine ⟨⟨⟨?_⟩⟩, ?_⟩
  · rintro ⟨_, s, rfl⟩ ⟨_, t, rfl⟩
    apply Subtype.ext
    change tv s * tv t = tv t * tv s
    rw [← map_mul, ← map_mul, mul_comm]
  · rintro _ ⟨t, rfl⟩
    rw [← map_pow, sq]
    have : t * t = 1 := by
      apply Multiplicative.toAdd.injective
      rw [toAdd_mul, toAdd_one]
      exact CharTwo.add_self_eq_zero _
    rw [this, map_one]

theorem slConjugation_tv {g : GL (Fin 3) F4}
    (hg : ∀ i j, i ≠ j → (g : Matrix (Fin 3) (Fin 3) F4) i j = 0) (t : F4) :
    slConjugation 3 F4 g (tv (Multiplicative.ofAdd t)) =
      tv (Multiplicative.ofAdd ((g : Matrix (Fin 3) (Fin 3) F4) 1 1 * t *
        ((g⁻¹ : GL (Fin 3) F4) : Matrix (Fin 3) (Fin 3) F4) 2 2)) := by
  set h := ((g⁻¹ : GL (Fin 3) F4) : Matrix (Fin 3) (Fin 3) F4) with hh
  have hgh : (g : Matrix (Fin 3) (Fin 3) F4) * h = 1 := by
    rw [hh, ← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hhg : h * (g : Matrix (Fin 3) (Fin 3) F4) = 1 := by
    rw [hh, ← Units.val_mul, inv_mul_cancel, Units.val_one]
  have hgii : ∀ i, (g : Matrix (Fin 3) (Fin 3) F4) i i * h i i = 1 := by
    intro i
    have e := congrFun (congrFun hgh i) i
    rw [Matrix.mul_apply, Finset.sum_eq_single i (fun k _ hk => by rw [hg i k (Ne.symm hk),
      zero_mul]) (by simp), Matrix.one_apply_eq] at e
    exact e
  have hgi0 : ∀ i, (g : Matrix (Fin 3) (Fin 3) F4) i i ≠ 0 := fun i h0 => by
    have := hgii i
    rw [h0, zero_mul] at this
    exact zero_ne_one this
  have hh0 : ∀ i j, i ≠ j → h i j = 0 := by
    intro i j hij
    have e := congrFun (congrFun hhg i) j
    rw [Matrix.mul_apply, Finset.sum_eq_single j (fun k _ hk => by rw [hg k j hk, mul_zero])
      (by simp), Matrix.one_apply_ne hij] at e
    exact (mul_eq_zero.mp e).resolve_right (hgi0 j)
  apply Subtype.ext
  rw [slConjugation_matrix, coe_tv, coe_tv]
  change (g : Matrix (Fin 3) (Fin 3) F4) * tvM t * h = _
  have g01 := hg 0 1 (by decide)
  have g02 := hg 0 2 (by decide)
  have g10 := hg 1 0 (by decide)
  have g12 := hg 1 2 (by decide)
  have g20 := hg 2 0 (by decide)
  have g21 := hg 2 1 (by decide)
  have h01 := hh0 0 1 (by decide)
  have h02 := hh0 0 2 (by decide)
  have h10 := hh0 1 0 (by decide)
  have h12 := hh0 1 2 (by decide)
  have h20 := hh0 2 0 (by decide)
  have h21 := hh0 2 1 (by decide)
  have e0 := hgii 0
  have e1 := hgii 1
  have e2 := hgii 2
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [tvM, Matrix.mul_apply, Fin.sum_univ_three, g01, g02, g10, g12, g20, g21, h01, h02, h10,
      h12, h20, h21, e0, e1, e2]

end Root

section Normal

variable {Z : Type*} [Group Z]

theorem exists_equiv_x0 (e : Z ≃* SL34) {u : Z} (hu3 : u ^ 3 = 1)
    (hu : u ∉ Subgroup.center Z) {ω : F4ˣ} (hω3 : ω ^ 3 = 1) (hω1 : ω ≠ 1) :
    ∃ e' : Z ≃* SL34, e' u = x0 ω := by
  classical
  have hωo : orderOf ω = 3 := orderOf_eq_prime hω3 hω1
  have hζ : IsPrimitiveRoot (ω : F4) 3 := by
    rw [IsPrimitiveRoot.coe_units_iff, ← hωo]
    exact IsPrimitiveRoot.orderOf ω
  set x := e u with hx
  have hx3 : x ^ 3 = 1 := by rw [hx, ← map_pow, hu3, map_one]
  have hxc : x ∉ Subgroup.center SL34 := by
    intro h
    apply hu
    rw [Subgroup.mem_center_iff] at h ⊢
    intro z
    apply e.injective
    rw [map_mul, map_mul]
    exact h (e z)
  have hcomm : ∀ y ∈ Subgroup.zpowers x, ∀ z ∈ Subgroup.zpowers x, y * z = z * y := by
    rintro _ ⟨i, rfl⟩ _ ⟨j, rfl⟩
    exact ((Commute.refl x).zpow_zpow i j).eq
  have hpow : ∀ y ∈ Subgroup.zpowers x, y ^ 3 = 1 := by
    rintro _ ⟨i, rfl⟩
    rw [← zpow_natCast, ← _root_.zpow_mul, mul_comm, _root_.zpow_mul, zpow_natCast, hx3,
      _root_.one_zpow]
  obtain ⟨P, hP⟩ := CFSG.RankThree.PartOne.exists_conj_diagonal_of_commuting_pow_eq_one hζ
    (Subgroup.zpowers x) hcomm hpow
  set x1 := slConjugation 3 F4 P x with hx1
  have hD : (x1 : Matrix (Fin 3) (Fin 3) F4) = (P : Matrix (Fin 3) (Fin 3) F4) *
      (x : Matrix (Fin 3) (Fin 3) F4) * ((P⁻¹ : GL (Fin 3) F4) : Matrix (Fin 3) (Fin 3) F4) :=
    slConjugation_matrix 3 F4 P x
  have hoff : ∀ i j, i ≠ j → (x1 : Matrix (Fin 3) (Fin 3) F4) i j = 0 := by
    intro i j hij
    rw [hD]
    exact hP x (Subgroup.mem_zpowers x) i j hij
  set d : Fin 3 → F4 := fun i => (x1 : Matrix (Fin 3) (Fin 3) F4) i i with hd
  have hdiag : (x1 : Matrix (Fin 3) (Fin 3) F4) = diagonal d := by
    ext i j
    by_cases hij : i = j
    · subst hij
      rw [diagonal_apply_eq]
    · rw [hoff i j hij, diagonal_apply_ne _ hij]
  have hdet : d 0 * d 1 * d 2 = 1 := by
    have h := x1.2
    rw [hdiag, det_diagonal, Fin.prod_univ_three] at h
    exact h
  have hd3 : ∀ i, d i ^ 3 = 1 := by
    have hx13 : x1 ^ 3 = 1 := by rw [hx1, ← map_pow, hx3, map_one]
    have h := congrArg (fun y : SL34 => (y : Matrix (Fin 3) (Fin 3) F4)) hx13
    simp only [Matrix.SpecialLinearGroup.coe_pow, Matrix.SpecialLinearGroup.coe_one, hdiag,
      diagonal_pow] at h
    intro i
    have := congrFun (congrFun h i) i
    rwa [diagonal_apply_eq, Matrix.one_apply_eq] at this
  have hd0 : ∀ i, d i ≠ 0 := by
    intro i h0
    have := hd3 i
    rw [h0] at this
    norm_num at this
  have hne : ¬ (d 0 = d 1 ∧ d 1 = d 2) := by
    rintro ⟨h01, h12⟩
    apply hxc
    have hx1c : x1 ∈ Subgroup.center SL34 := by
      rw [Subgroup.mem_center_iff]
      intro y
      apply Subtype.ext
      rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, hdiag]
      have hds : diagonal d = d 0 • (1 : Matrix (Fin 3) (Fin 3) F4) := by
        ext i j
        by_cases hij : i = j
        · subst hij
          fin_cases i <;> simp [h01, h12]
        · rw [diagonal_apply_ne _ hij, Matrix.smul_apply, Matrix.one_apply_ne hij, smul_zero]
      rw [hds, Matrix.mul_smul, Matrix.smul_mul, mul_one, one_mul]
    rw [Subgroup.mem_center_iff] at hx1c ⊢
    intro y
    have h := hx1c (slConjugation 3 F4 P y)
    rw [hx1, ← map_mul, ← map_mul] at h
    exact (slConjugation 3 F4 P).injective h
  have hcube : ∀ a b : F4, a ^ 3 = 1 → a * a * b = 1 → b = a := by
    intro a b ha hab
    have ha0 : a ≠ 0 := by
      intro h
      rw [h] at ha
      norm_num at ha
    calc b = a ^ 3 * b := by rw [ha, one_mul]
      _ = a * (a * a * b) := by ring
      _ = a := by rw [hab, mul_one]
  have h01 : d 0 ≠ d 1 := by
    intro h
    apply hne
    have h2 : d 2 = d 0 := hcube _ _ (hd3 0) (by rw [← hdet, h])
    exact ⟨h, by rw [← h, h2]⟩
  have h02 : d 0 ≠ d 2 := by
    intro h
    apply hne
    have h1 : d 1 = d 0 := hcube _ _ (hd3 0) (by rw [← hdet, ← h]; ring)
    exact ⟨h1.symm, by rw [h1, h]⟩
  have h12 : d 1 ≠ d 2 := by
    intro h
    apply hne
    have h0 : d 0 = d 1 := hcube _ _ (hd3 1) (by rw [← hdet, ← h]; ring)
    exact ⟨h0, h⟩
  have hinj : Function.Injective d := by
    intro i j hij
    by_contra hne'
    have key : ∀ i j : Fin 3, i ≠ j → d i ≠ d j := by
      intro i j hij'
      fin_cases i <;> fin_cases j
      all_goals first
        | exact absurd rfl hij'
        | exact h01
        | exact h01.symm
        | exact h02
        | exact h02.symm
        | exact h12
        | exact h12.symm
    exact key i j hne' hij
  have : Fintype F4ˣ := Fintype.ofFinite _
  set dU : Fin 3 → F4ˣ := fun i => Units.mk0 (d i) (hd0 i) with hdU
  have hdUinj : Function.Injective dU := fun i j h => hinj (congrArg Units.val h)
  have hcardU : Fintype.card (Fin 3) = Fintype.card F4ˣ := by
    rw [Fintype.card_fin, Fintype.card_eq_nat_card, card_units_F4]
  have hdUb : Function.Bijective dU := (Fintype.bijective_iff_injective_and_card dU).mpr
    ⟨hdUinj, hcardU⟩
  have htUinj : Function.Injective (dω ω) := fun i j h =>
    dω_injective hω3 hω1 (congrArg Units.val h)
  have htUb : Function.Bijective (dω ω) := (Fintype.bijective_iff_injective_and_card _).mpr
    ⟨htUinj, hcardU⟩
  set σ : Equiv.Perm (Fin 3) := (Equiv.ofBijective _ htUb).trans (Equiv.ofBijective _ hdUb).symm
    with hσ
  have hσd : ∀ i, d (σ i) = (dω ω i : F4) := by
    intro i
    have h : dU (σ i) = dω ω i :=
      Equiv.ofBijective_apply_symm_apply dU hdUb (dω ω i)
    exact congrArg Units.val h
  refine ⟨(e.trans (slConjugation 3 F4 P)).trans (reindexSL σ), ?_⟩
  apply Subtype.ext
  change ((reindexSL σ x1 : SL34) : Matrix (Fin 3) (Fin 3) F4) = _
  rw [coe_reindexSL, hdiag, submatrix_diagonal_equiv, coe_x0]
  congr 1
  funext i
  exact hσd i

end Normal

end SL34Lines

open SL34Lines

variable {G : Type} [Group G]

theorem exists_fourGroup_SL34 [Finite G] {A Z : Subgroup G} (hAe : IsElemAbelian 3 A)
    (hAN : A ≤ Subgroup.normalizer (Z : Set G)) (eZ : Z ≃* SL34)
    {ρ : MulAut A} (hρZ : ρ ∈ starOf A Z) (hρ : IsReflectionOn ρ) :
    ∃ V ∈ fourGroups A, A ⊓ Subgroup.centralizer (V : Set G) ≤ fixedInG A ρ := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hAc : ∀ a b : A, a * b = b * a := hAe.1.is_comm.comm
  have hA3 : ∀ a : A, a ^ 3 = 1 := fun a => Subtype.ext (by simpa using hAe.2 a a.2)
  obtain ⟨⟨w, hwN⟩, hwZ, hρw⟩ := hρZ
  have hwZ' : w ∈ Z := Subgroup.mem_subgroupOf.mp hwZ
  have hρapp : ∀ a : A, ((ρ a : A) : G) = w * a * w⁻¹ := fun a => by rw [← hρw]; rfl
  have hρ2 := apply_apply_of_orderOf_eq_two hρ.1
  have hc3 : Nat.card (commOf ρ) = 3 := hρ.2
  have : Nontrivial (commOf ρ) := Finite.one_lt_card_iff_nontrivial.mp (by rw [hc3]; norm_num)
  obtain ⟨u0, hu0⟩ := exists_ne (1 : commOf ρ)
  have hu0' : (u0 : A) ≠ 1 := fun h => hu0 (Subtype.ext h)
  have hu0Z : ((u0 : A) : G) ∈ Z := by
    have hmem : (u0 : A) ∈ (commHom hAc ρ).range := (range_commHom hAc ρ).symm ▸ u0.2
    obtain ⟨a, ha⟩ := hmem
    rw [← ha, commHom_apply, Subgroup.coe_mul, Subgroup.coe_inv, hρapp]
    have haN : (a : G)⁻¹ ∈ Subgroup.normalizer (Z : Set G) := Subgroup.inv_mem _ (hAN a.2)
    have h1 : (a : G)⁻¹ * w * ((a : G)⁻¹)⁻¹ ∈ Z :=
      (Subgroup.mem_normalizer_iff.mp haN w).mp hwZ'
    have e : (a : G)⁻¹ * (w * a * w⁻¹) = ((a : G)⁻¹ * w * ((a : G)⁻¹)⁻¹) * w⁻¹ := by group
    rw [e]
    exact Z.mul_mem h1 (Z.inv_mem hwZ')
  set u : Z := ⟨((u0 : A) : G), hu0Z⟩ with hu
  have hρu : ρ (u0 : A) = (u0 : A)⁻¹ := inv_of_mem_commOf hAc hρ2 u0.2
  have hu3 : u ^ 3 = 1 := Subtype.ext (by simpa using hAe.2 _ (u0 : A).2)
  have hcommC : ∀ y : A, y ∈ commOf ρ → (y : G) ∈ Subgroup.centralizer (Z : Set G) → y = 1 := by
    intro y hy hyC
    have hfix : ρ y = y := by
      apply Subtype.ext
      rw [hρapp, Subgroup.mem_centralizer_iff.mp hyC w hwZ', mul_inv_cancel_right]
    have hinv : ρ y = y⁻¹ := inv_of_mem_commOf hAc hρ2 hy
    have hy2 : y * y = 1 := by
      calc y * y = y * ρ y := by rw [hfix]
        _ = 1 := by rw [hinv, mul_inv_cancel]
    calc y = y ^ 3 * (y * y)⁻¹ := by group
      _ = 1 := by rw [hA3, hy2, inv_one, one_mul]
  have hucen : u ∉ Subgroup.center Z := by
    intro h
    apply hu0'
    refine hcommC _ u0.2 (Subgroup.mem_centralizer_iff.mpr fun z hz => ?_)
    exact congrArg Subtype.val (Subgroup.mem_center_iff.mp h ⟨z, hz⟩)
  obtain ⟨ω, hωo⟩ := exists_prime_orderOf_dvd_card' (G := F4ˣ) 3 (by rw [card_units_F4])
  have hω3 : ω ^ 3 = 1 := by rw [← hωo]; exact pow_orderOf_eq_one ω
  have hω1 : ω ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at hωo
    norm_num at hωo
  obtain ⟨e, he⟩ := exists_equiv_x0 eZ hu3 hucen hω3 hω1
  set τ : Subgroup.normalizer (Z : Set G) →* MulAut SL34 :=
    (MulAut.congr e).toMonoidHom.comp Z.normalizerMonoidHom with hτ
  have hτapp : ∀ (b : Subgroup.normalizer (Z : Set G)) (z : Z),
      τ b (e z) = e (Z.normalizerMonoidHom b z) := by
    intro b z
    simp [hτ, MulAut.congr_apply]
  have hτker : ∀ b : Subgroup.normalizer (Z : Set G), τ b = 1 →
      (b : G) ∈ Subgroup.centralizer (Z : Set G) := by
    intro b hb
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    have h1 := congrArg (fun φ : MulAut SL34 => φ (e ⟨z, hz⟩)) hb
    simp only [hτapp, MulAut.one_apply] at h1
    have h2 : ((Z.normalizerMonoidHom b ⟨z, hz⟩ : Z) : G) = z :=
      congrArg Subtype.val (e.injective h1)
    change (b : G) * z * (b : G)⁻¹ = z at h2
    calc z * b = (b : G) * z * (b : G)⁻¹ * b := by rw [h2]
      _ = b * z := by group
  set W : SL34 := e ⟨w, hwZ'⟩ with hW
  have hτw : τ ⟨w, Subgroup.le_normalizer hwZ'⟩ = MulAut.conj W := by
    ext y
    obtain ⟨z, rfl⟩ := e.surjective y
    rw [hτapp, MulAut.conj_apply, hW, ← map_inv, ← map_mul, ← map_mul]
    rfl
  have hWx : W * x0 ω * W⁻¹ = x0' ω := by
    rw [← x0_inv, ← he, hW, ← map_inv, ← map_mul, ← map_mul, ← map_inv]
    congr 1
    apply Subtype.ext
    change w * ((u0 : A) : G) * w⁻¹ = (((u0 : A) : G))⁻¹
    rw [← hρapp, hρu, Subgroup.coe_inv]
  have hWx' : W * x0 ω = x0' ω * W := by
    rw [← hWx]
    group
  have hWpat := pattern_of hω3 hω1 (W := (W : Matrix (Fin 3) (Fin 3) F4)) (by
    have h := congrArg (fun y : SL34 => (y : Matrix (Fin 3) (Fin 3) F4)) hWx'
    simpa only [Matrix.SpecialLinearGroup.coe_mul] using h)
  have hdiag : ∀ a (ha : a ∈ A), ∃ g : GL (Fin 3) F4, τ ⟨a, hAN ha⟩ = slConjugation 3 F4 g ∧
      ∀ i j, i ≠ j → (g : Matrix (Fin 3) (Fin 3) F4) i j = 0 := by
    intro a ha
    have h3 : τ ⟨a, hAN ha⟩ ^ 3 ^ 1 = 1 := by
      rw [pow_one, ← map_pow]
      have : (⟨a, hAN ha⟩ : Subgroup.normalizer (Z : Set G)) ^ 3 = 1 :=
        Subtype.ext (by simpa using hAe.2 a ha)
      rw [this, map_one]
    obtain ⟨g, hg⟩ := mem_inndiag_of_pow _ ⟨1, h3⟩
    refine ⟨g, hg.symm, ?_⟩
    have hfix : τ ⟨a, hAN ha⟩ (x0 ω) = x0 ω := by
      rw [← he, hτapp]
      congr 1
      apply Subtype.ext
      change a * ((u0 : A) : G) * a⁻¹ = ((u0 : A) : G)
      have hcom : a * ((u0 : A) : G) = ((u0 : A) : G) * a :=
        congrArg Subtype.val (hAc ⟨a, ha⟩ (u0 : A))
      rw [hcom, mul_inv_cancel_right]
    rw [← hg] at hfix
    have hm := congrArg (fun y : SL34 => (y : Matrix (Fin 3) (Fin 3) F4)) hfix
    simp only [slConjugation_matrix] at hm
    apply offDiag_eq_zero_of_commute hω3 hω1
    calc (g : Matrix (Fin 3) (Fin 3) F4) * (x0 ω : Matrix (Fin 3) (Fin 3) F4)
        = (g : Matrix (Fin 3) (Fin 3) F4) * (x0 ω : Matrix (Fin 3) (Fin 3) F4) *
            (((g⁻¹ : GL (Fin 3) F4) : Matrix (Fin 3) (Fin 3) F4) *
              (g : Matrix (Fin 3) (Fin 3) F4)) := by
          rw [Units.inv_mul, mul_one]
      _ = _ := by rw [← mul_assoc, hm]
  set V : Subgroup G := (V0.map e.symm.toMonoidHom).map Z.subtype with hVdef
  have hVmem : ∀ t : F4, ((e.symm (tv (Multiplicative.ofAdd t)) : Z) : G) ∈ V :=
    fun t => ⟨_, ⟨_, ⟨Multiplicative.ofAdd t, rfl⟩, rfl⟩, rfl⟩
  have hVinj : Function.Injective (Z.subtype.comp e.symm.toMonoidHom) :=
    Z.subtype_injective.comp e.symm.injective
  have hVeq : V = V0.map (Z.subtype.comp e.symm.toMonoidHom) := by
    rw [hVdef, Subgroup.map_map]
  have hV4 : Nat.card V = 4 := by
    rw [hVeq, Subgroup.card_map_of_injective hVinj, card_V0]
  have hVe : IsElemAbelian 2 V := by
    rw [hVeq]
    exact CFSG.RankThree.PartTwo.Sec21.isElemAbelian_map isElemAbelian_V0 _
  have hconjV : ∀ a (ha : a ∈ A) (g : GL (Fin 3) F4), τ ⟨a, hAN ha⟩ = slConjugation 3 F4 g →
      (∀ i j, i ≠ j → (g : Matrix (Fin 3) (Fin 3) F4) i j = 0) → ∀ t : F4,
      a * ((e.symm (tv (Multiplicative.ofAdd t)) : Z) : G) * a⁻¹ =
        ((e.symm (tv (Multiplicative.ofAdd ((g : Matrix (Fin 3) (Fin 3) F4) 1 1 * t *
          ((g⁻¹ : GL (Fin 3) F4) : Matrix (Fin 3) (Fin 3) F4) 2 2))) : Z) : G) := by
    intro a ha g hg hgd t
    have h1 : e (Z.normalizerMonoidHom ⟨a, hAN ha⟩ (e.symm (tv (Multiplicative.ofAdd t)))) =
        tv (Multiplicative.ofAdd ((g : Matrix (Fin 3) (Fin 3) F4) 1 1 * t *
          ((g⁻¹ : GL (Fin 3) F4) : Matrix (Fin 3) (Fin 3) F4) 2 2)) := by
      rw [← hτapp, MulEquiv.apply_symm_apply, hg, slConjugation_tv hgd]
    have h2 := congrArg (fun z : Z => (z : G)) ((MulEquiv.symm_apply_eq e).mpr h1.symm)
    exact h2.symm
  have hVA : A ≤ Subgroup.normalizer (V : Set G) := by
    intro a ha
    obtain ⟨g, hg, hgd⟩ := hdiag a ha
    apply mem_normalizer_of_forall_conj_mem
    rintro _ ⟨_, ⟨_, ⟨t, rfl⟩, rfl⟩, rfl⟩
    have h := hconjV a ha g hg hgd (Multiplicative.toAdd t)
    simp only [ofAdd_toAdd] at h
    change a * ((e.symm (tv t) : Z) : G) * a⁻¹ ∈ V
    rw [h]
    exact hVmem _
  refine ⟨V, mem_fourGroups_iff.mpr ⟨hVA, hVe, hV4⟩, ?_⟩
  rintro a ⟨ha, haV⟩
  obtain ⟨g, hg, hgd⟩ := hdiag a ha
  have hgii : ∀ i, (g : Matrix (Fin 3) (Fin 3) F4) i i *
      ((g⁻¹ : GL (Fin 3) F4) : Matrix (Fin 3) (Fin 3) F4) i i = 1 := by
    intro i
    have e1 : (g : Matrix (Fin 3) (Fin 3) F4) * ((g⁻¹ : GL (Fin 3) F4) : Matrix _ _ F4) = 1 :=
      Units.mul_inv g
    have e2 := congrFun (congrFun e1 i) i
    rw [Matrix.mul_apply, Finset.sum_eq_single i (fun k _ hk => by rw [hgd i k (Ne.symm hk),
      zero_mul]) (by simp), Matrix.one_apply_eq] at e2
    exact e2
  have h12 : (g : Matrix (Fin 3) (Fin 3) F4) 1 1 = (g : Matrix (Fin 3) (Fin 3) F4) 2 2 := by
    have hv1 := hVmem 1
    have hc : a * ((e.symm (tv (Multiplicative.ofAdd 1)) : Z) : G) * a⁻¹ =
        ((e.symm (tv (Multiplicative.ofAdd 1)) : Z) : G) := by
      rw [← Subgroup.mem_centralizer_iff.mp haV _ hv1, mul_inv_cancel_right]
    rw [hconjV a ha g hg hgd 1] at hc
    have hc' := e.symm.injective (Subtype.ext hc)
    have hc'' := congrArg Multiplicative.toAdd (tv_injective hc')
    simp only [toAdd_ofAdd, mul_one] at hc''
    have h22 := hgii 2
    have hne : ((g⁻¹ : GL (Fin 3) F4) : Matrix (Fin 3) (Fin 3) F4) 2 2 ≠ 0 := by
      intro h0
      rw [h0, mul_zero] at h22
      exact zero_ne_one h22
    exact mul_right_cancel₀ hne (hc''.trans h22.symm)
  have hWg : SpecialLinearGroup.toGL W * g = g * SpecialLinearGroup.toGL W :=
    Units.ext (commute_of_pattern hWpat hgd h12)
  have hτwa : τ (⟨w, Subgroup.le_normalizer hwZ'⟩ * ⟨a, hAN ha⟩ *
      (⟨w, Subgroup.le_normalizer hwZ'⟩)⁻¹) = τ ⟨a, hAN ha⟩ := by
    rw [map_mul, map_mul, map_inv, hτw, hg, ← slConjugation_toGL_eq, ← map_mul, ← map_inv,
      ← map_mul, hWg, mul_inv_cancel_right]
  have hker : τ (⟨w, Subgroup.le_normalizer hwZ'⟩ * ⟨a, hAN ha⟩ *
      (⟨w, Subgroup.le_normalizer hwZ'⟩)⁻¹ * (⟨a, hAN ha⟩)⁻¹) = 1 := by
    rw [map_mul _ _ (⟨a, hAN ha⟩ : Subgroup.normalizer (Z : Set G))⁻¹, hτwa, map_inv,
      mul_inv_cancel]
  have hC := hτker _ hker
  set y : A := ρ ⟨a, ha⟩ * (⟨a, ha⟩ : A)⁻¹ with hy
  have hycomm : y ∈ commOf ρ := by
    have h1 := mem_commOf ρ (⟨a, ha⟩ : A)
    rwa [hAc] at h1
  have hyC : (y : G) ∈ Subgroup.centralizer (Z : Set G) := by
    rw [hy, Subgroup.coe_mul, hρapp, Subgroup.coe_inv]
    exact hC
  have hy1 := hcommC y hycomm hyC
  have hfix : ρ ⟨a, ha⟩ = ⟨a, ha⟩ := by
    rw [hy, mul_inv_eq_one] at hy1
    exact hy1
  exact ⟨⟨a, ha⟩, (mem_fixedSubgroupOf ρ _).mpr hfix, rfl⟩

end CFSG.RankThree.PartTwo.Sec21.Item233Res3Proof
