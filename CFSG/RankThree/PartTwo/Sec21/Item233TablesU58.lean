module

public import CFSG.RankThree.PartTwo.Sec21.Item233TablesL44
public import CFSG.RankThree.PartTwo.Sec21.Item233TablesUnitary
public import CFSG.RankThree.PartTwo.KFacts.KS21SylowU58
import CFSG.RankThree.SubgroupLists.UnitaryThreeFamily
import CFSG.LieType.Universal.Unitary.Clause0

public noncomputable section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  CFSG.Semidihedral.CyclicPairFrattini.zmodAddCommGroup

namespace CFSG.RankThree.PartTwo.Sec21.TablesU58

open Matrix CFSG.RankThree.PartTwo.KFacts.KS21 CFSG.RankThree.PartTwo.KFacts.KS21.U58
open CFSG.RankThree.PartTwo.Sec21.Tables
open CFSG.RankThree.PartTwo.Sec21.TablesL44 (zpowers_sq map_top_mulEquiv)
open CFSG.Assembly (IsElemAbelian)
open CFSG.Assembly.LowTwoRank
open scoped MatrixGroups

abbrev mU (g : SUI) : Matrix (Fin 5) (Fin 5) K := ((g : GL (Fin 5) K) : Matrix (Fin 5) (Fin 5) K)

theorem mU_mul (g h : SUI) : mU (g * h) = mU g * mU h := rfl

theorem mU_one : mU 1 = 1 := rfl

theorem mU_injective : Function.Injective mU := fun _ _ h => Subtype.ext (Units.ext h)

theorem mU_mul_inv (g : SUI) : mU g * mU g⁻¹ = 1 := by rw [← mU_mul, mul_inv_cancel, mU_one]

theorem mU_inv_mul (g : SUI) : mU g⁻¹ * mU g = 1 := by rw [← mU_mul, inv_mul_cancel, mU_one]

theorem mem_SUI_iff (A : GL (Fin 5) K) : A ∈ SUI ↔ (A : Matrix (Fin 5) (Fin 5) K).det = 1 ∧
    ((A : Matrix (Fin 5) (Fin 5) K).map (iterateFrobenius K 2 3))ᵀ *
      (A : Matrix (Fin 5) (Fin 5) K) = 1 :=
  mem_statedSU_iff' 3 card_K (by norm_num) A

@[expose] def ζ : Kˣ := exists_zeta.choose

theorem orderOf_ζ : orderOf ζ = 9 := exists_zeta.choose_spec

theorem ζ_pow_nine : ζ ^ 9 = 1 := by
  rw [← orderOf_ζ]
  exact pow_orderOf_eq_one ζ

@[expose] def eζ (a : ZMod 9) : K := ((ζ ^ a.val : Kˣ) : K)

theorem eζ_add (a b : ZMod 9) : eζ (a + b) = eζ a * eζ b := by
  rw [eζ, eζ, eζ, ZMod.val_add, ← pow_eq_pow_mod _ ζ_pow_nine, pow_add, Units.val_mul]

theorem eζ_zero : eζ 0 = 1 := by simp [eζ]

theorem eζ_injective : Function.Injective eζ := by
  intro a b h
  have h' : ζ ^ a.val = ζ ^ b.val := Units.ext h
  have := pow_inj_mod.mp h'
  rw [orderOf_ζ, Nat.mod_eq_of_lt (ZMod.val_lt a), Nat.mod_eq_of_lt (ZMod.val_lt b)] at this
  exact ZMod.val_injective 9 this

theorem eζ_unitary (a : ZMod 9) : iterateFrobenius K 2 3 (eζ a) * eζ a = 1 := by
  rw [iterateFrobenius_def, eζ, ← Units.val_pow_eq_pow_val, ← Units.val_mul, ← pow_succ,
    show 2 ^ 3 + 1 = 9 from rfl, ← pow_mul, mul_comm a.val 9, pow_mul, ζ_pow_nine, one_pow,
    Units.val_one]

@[expose] def dgU (x : Fin 5 → ZMod 9) : Matrix (Fin 5) (Fin 5) K := diagonal fun i => eζ (x i)

theorem dgU_add (x y : Fin 5 → ZMod 9) : dgU (x + y) = dgU x * dgU y := by
  rw [dgU, dgU, dgU, diagonal_mul_diagonal]
  congr 1
  funext i
  exact eζ_add _ _

theorem dgU_zero : dgU 0 = 1 := by
  rw [dgU]
  simp [eζ_zero]

theorem det_dgU {x : Fin 5 → ZMod 9} (hx : ∑ i, x i = 0) : (dgU x).det = 1 := by
  rw [dgU, det_diagonal]
  have h : ∀ s : Finset (Fin 5), ∏ i ∈ s, eζ (x i) = eζ (∑ i ∈ s, x i) := by
    intro s
    induction s using Finset.induction_on with
    | empty => simp [eζ_zero]
    | insert a s ha ih => rw [Finset.prod_insert ha, Finset.sum_insert ha, ih, eζ_add]
  rw [h, hx, eζ_zero]

theorem unitary_dgU (x : Fin 5 → ZMod 9) :
    ((dgU x).map (iterateFrobenius K 2 3))ᵀ * dgU x = 1 := by
  rw [dgU, diagonal_map (map_zero _), diagonal_transpose, diagonal_mul_diagonal, ← diagonal_one]
  congr 1
  funext i
  exact eζ_unitary _

@[expose] def ext9 (u : Fin 4 → ZMod 9) : Fin 5 → ZMod 9 :=
  ![u 0, u 1, u 2, u 3, -(u 0 + u 1 + u 2 + u 3)]

@[expose] def ext3 (v : Fin 4 → ZMod 3) : Fin 5 → ZMod 3 :=
  ![v 0, v 1, v 2, v 3, -(v 0 + v 1 + v 2 + v 3)]

theorem sum_ext9 (u : Fin 4 → ZMod 9) : ∑ i, ext9 u i = 0 := by
  rw [Fin.sum_univ_five]
  change u 0 + u 1 + u 2 + u 3 + -(u 0 + u 1 + u 2 + u 3) = 0
  exact add_neg_cancel _

theorem sum_ext3 (v : Fin 4 → ZMod 3) : ∑ i, ext3 v i = 0 := by
  rw [Fin.sum_univ_five]
  change v 0 + v 1 + v 2 + v 3 + -(v 0 + v 1 + v 2 + v 3) = 0
  exact add_neg_cancel _

theorem ext9_add (u v : Fin 4 → ZMod 9) : ext9 (u + v) = ext9 u + ext9 v := by
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · change -((u 0 + v 0) + (u 1 + v 1) + (u 2 + v 2) + (u 3 + v 3)) =
      -(u 0 + u 1 + u 2 + u 3) + -(v 0 + v 1 + v 2 + v 3)
    rw [← neg_add]
    congr 1
    abel

theorem ext9_zero : ext9 0 = 0 := by
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · change -((0 : ZMod 9) + 0 + 0 + 0) = 0
    rw [add_zero, add_zero, add_zero, neg_zero]

theorem ext9_injective : Function.Injective ext9 := by
  intro u v h
  funext i
  fin_cases i
  · exact congrFun h 0
  · exact congrFun h 1
  · exact congrFun h 2
  · exact congrFun h 3

@[expose] def τGL (u : Fin 4 → ZMod 9) : GL (Fin 5) K :=
  ⟨dgU (ext9 u), dgU (ext9 (-u)),
    by rw [← dgU_add, ← ext9_add, add_neg_cancel, ext9_zero, dgU_zero],
    by rw [← dgU_add, ← ext9_add, neg_add_cancel, ext9_zero, dgU_zero]⟩

theorem τGL_mem (u : Fin 4 → ZMod 9) : τGL u ∈ SUI :=
  (mem_SUI_iff _).mpr ⟨det_dgU (sum_ext9 u), unitary_dgU _⟩

@[expose] def τ : Multiplicative (Fin 4 → ZMod 9) →* SUI where
  toFun u := ⟨τGL (Multiplicative.toAdd u), τGL_mem _⟩
  map_one' := Subtype.ext (Units.ext (by
    change dgU (ext9 0) = 1
    rw [ext9_zero, dgU_zero]))
  map_mul' u v := Subtype.ext (Units.ext (by
    change dgU (ext9 (Multiplicative.toAdd u + Multiplicative.toAdd v)) =
      dgU (ext9 (Multiplicative.toAdd u)) * dgU (ext9 (Multiplicative.toAdd v))
    rw [ext9_add, dgU_add]))

theorem mU_τ (u : Fin 4 → ZMod 9) : mU (τ (Multiplicative.ofAdd u)) = dgU (ext9 u) := rfl

theorem τ_injective : Function.Injective τ := by
  intro u v h
  have h' := congrArg mU h
  change dgU (ext9 (Multiplicative.toAdd u)) = dgU (ext9 (Multiplicative.toAdd v)) at h'
  apply Multiplicative.toAdd.injective
  apply ext9_injective
  funext i
  have := congrFun₂ h' i i
  simp only [dgU, diagonal_apply_eq] at this
  exact eζ_injective this

@[expose] def ι3 (a : ZMod 3) : ZMod 9 := 3 * (a.val : ZMod 9)

theorem ι3_add : ∀ a b : ZMod 3, ι3 (a + b) = ι3 a + ι3 b := by decide

theorem ι3_neg : ∀ a : ZMod 3, ι3 (-a) = -ι3 a := by decide

theorem ι3_zero : ι3 0 = 0 := by decide

theorem ι3_injective : Function.Injective ι3 := by decide

@[expose] def ι3v : (Fin 4 → ZMod 3) →+ (Fin 4 → ZMod 9) where
  toFun v i := ι3 (v i)
  map_zero' := funext fun _ => ι3_zero
  map_add' v w := funext fun i => ι3_add (v i) (w i)

theorem ι3v_injective : Function.Injective ι3v := fun _ _ h =>
  funext fun i => ι3_injective (congrFun h i)

theorem ext9_ι3v (v : Fin 4 → ZMod 3) : ext9 (ι3v v) = fun i => ι3 (ext3 v i) := by
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · change -(ι3 (v 0) + ι3 (v 1) + ι3 (v 2) + ι3 (v 3)) = ι3 (-(v 0 + v 1 + v 2 + v 3))
    rw [ι3_neg, ι3_add, ι3_add, ι3_add]

@[expose] def δ : Multiplicative (Fin 4 → ZMod 3) →* SUI :=
  τ.comp (AddMonoidHom.toMultiplicative ι3v)

theorem δ_apply (v : Fin 4 → ZMod 3) :
    δ (Multiplicative.ofAdd v) = τ (Multiplicative.ofAdd (ι3v v)) := rfl

theorem δ_injective : Function.Injective δ :=
  τ_injective.comp (fun _ _ h => Multiplicative.toAdd.injective
    (ι3v_injective (Multiplicative.ofAdd.injective h)))

@[expose] def A0 : Subgroup SUI := δ.range

theorem isElemAbelian_A0 : IsElemAbelian 3 A0 := by
  refine ⟨⟨⟨?_⟩⟩, ?_⟩
  · rintro ⟨_, v, rfl⟩ ⟨_, w, rfl⟩
    apply Subtype.ext
    change δ v * δ w = δ w * δ v
    rw [← map_mul, ← map_mul, mul_comm v w]
  · rintro _ ⟨v, rfl⟩
    rw [← map_pow]
    have : v ^ 3 = 1 := by
      apply Multiplicative.toAdd.injective
      funext i
      simp only [toAdd_pow, toAdd_one, Pi.smul_apply, Pi.zero_apply, nsmul_eq_mul]
      rw [show ((3 : ℕ) : ZMod 3) = 0 from rfl, zero_mul]
    rw [this, map_one]

theorem card_A0 : Nat.card A0 = 3 ^ 4 := by
  rw [A0, ← Nat.card_congr (MonoidHom.ofInjective δ_injective).toEquiv, Nat.card_eq_fintype_card,
    Fintype.card_multiplicative, Fintype.card_fun, ZMod.card, Fintype.card_fin]

theorem exists_map_conj_eq_A0 {A' : Subgroup SUI} (hA' : IsElemAbelian 3 A')
    (hcard : Nat.card A' = 3 ^ 4) : ∃ x : SUI, A'.map (MulAut.conj x).toMonoidHom = A0 := by
  obtain ⟨T, hTe, hfuse⟩ := hasFusionTarget_SUI
  obtain ⟨y, hy⟩ := hfuse A0 isElemAbelian_A0
  obtain ⟨z, hz⟩ := hfuse A' hA'
  have hT81 : Nat.card T ≤ 3 ^ 4 := maxEA_SUI.1 T hTe
  have hc : ∀ (X : Subgroup SUI) (u : SUI),
      Nat.card (X.map (MulAut.conj u).toMonoidHom) = Nat.card X :=
    fun X u => Subgroup.card_map_of_injective (MulAut.conj u).injective
  have hyT : A0.map (MulAut.conj y).toMonoidHom = T :=
    Subgroup.eq_of_le_of_card_ge hy (by rw [hc, card_A0]; exact hT81)
  have hzT : A'.map (MulAut.conj z).toMonoidHom = T :=
    Subgroup.eq_of_le_of_card_ge hz (by rw [hc, hcard]; exact hT81)
  refine ⟨y⁻¹ * z, ?_⟩
  rw [← map_conj_map_conj, hzT, ← hyT, map_conj_map_conj, inv_mul_cancel]
  ext g
  simp

theorem reindexGL_mem_SUI (σ : Equiv.Perm (Fin 5)) {g : GL (Fin 5) K} (hg : g ∈ SUI) :
    reindexGL σ g ∈ SUI := by
  rw [mem_SUI_iff] at hg ⊢
  rw [coe_reindexGL, det_submatrix_equiv_self]
  refine ⟨hg.1, ?_⟩
  rw [← submatrix_map, transpose_submatrix, submatrix_mul_equiv, hg.2, submatrix_one_equiv]

@[expose] def reindexSU (σ : Equiv.Perm (Fin 5)) : SUI ≃* SUI where
  toFun g := ⟨reindexGL σ g, reindexGL_mem_SUI σ g.2⟩
  invFun g := ⟨reindexGL σ.symm g, reindexGL_mem_SUI σ.symm g.2⟩
  left_inv g := Subtype.ext (Units.ext (by
    change ((mU g).submatrix σ σ).submatrix σ.symm σ.symm = mU g
    ext x y
    simp))
  right_inv g := Subtype.ext (Units.ext (by
    change ((mU g).submatrix σ.symm σ.symm).submatrix σ σ = mU g
    ext x y
    simp))
  map_mul' g h := Subtype.ext (map_mul (reindexGL σ) (g : GL (Fin 5) K) h)

theorem mU_reindexSU (σ : Equiv.Perm (Fin 5)) (g : SUI) :
    mU (reindexSU σ g) = (mU g).submatrix σ σ := rfl

@[expose] def res3 (y : Fin 5 → ZMod 3) : Fin 4 → ZMod 3 := ![y 0, y 1, y 2, y 3]

theorem ext3_res3 {y : Fin 5 → ZMod 3} (hy : ∑ i, y i = 0) : ext3 (res3 y) = y := by
  rw [Fin.sum_univ_five] at hy
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · change -(y 0 + y 1 + y 2 + y 3) = y 4
    rw [neg_eq_iff_add_eq_zero]
    exact hy

theorem res3_ext3 (v : Fin 4 → ZMod 3) : res3 (ext3 v) = v := by
  funext i
  fin_cases i <;> rfl

theorem reindexSU_δ (σ : Equiv.Perm (Fin 5)) (v : Fin 4 → ZMod 3) :
    reindexSU σ (δ (Multiplicative.ofAdd v)) = δ (Multiplicative.ofAdd (res3 (ext3 v ∘ σ))) := by
  apply mU_injective
  have hsum : ∑ i, (ext3 v ∘ σ) i = 0 := by
    change ∑ i, ext3 v (σ i) = 0
    rw [Equiv.sum_comp σ (ext3 v)]
    exact sum_ext3 v
  rw [mU_reindexSU, δ_apply, δ_apply, mU_τ, mU_τ, ext9_ι3v, ext9_ι3v, ext3_res3 hsum, dgU, dgU,
    submatrix_diagonal_equiv]
  rfl

theorem map_reindexSU_A0 (σ : Equiv.Perm (Fin 5)) : A0.map (reindexSU σ).toMonoidHom = A0 := by
  apply Subgroup.eq_of_le_of_card_ge
  · rintro _ ⟨_, ⟨v, rfl⟩, rfl⟩
    exact ⟨_, (reindexSU_δ σ (Multiplicative.toAdd v)).symm⟩
  · rw [Subgroup.card_map_of_injective (reindexSU σ).injective]

@[expose] def std : Fin 4 → (Fin 4 → ZMod 3) :=
  ![![1, 2, 0, 0], ![1, 1, 1, 0], ![1, 1, 2, 2], ![1, 1, 1, 1]]

@[expose] def mkPerm (f g : Fin 5 → Fin 5) (h₁ : ∀ x, g (f x) = x) (h₂ : ∀ x, f (g x) = x) :
    Equiv.Perm (Fin 5) :=
  ⟨f, g, h₁, h₂⟩

@[expose] def perms : List (Equiv.Perm (Fin 5)) :=
  [mkPerm ![0, 1, 2, 3, 4] ![0, 1, 2, 3, 4] (by decide) (by decide),
    mkPerm ![0, 2, 3, 4, 1] ![0, 4, 1, 2, 3] (by decide) (by decide),
    mkPerm ![0, 3, 1, 4, 2] ![0, 2, 4, 1, 3] (by decide) (by decide),
    mkPerm ![0, 4, 1, 2, 3] ![0, 2, 3, 4, 1] (by decide) (by decide),
    mkPerm ![1, 2, 3, 4, 0] ![4, 0, 1, 2, 3] (by decide) (by decide),
    mkPerm ![1, 3, 4, 0, 2] ![3, 0, 4, 1, 2] (by decide) (by decide),
    mkPerm ![1, 4, 2, 0, 3] ![3, 0, 2, 4, 1] (by decide) (by decide),
    mkPerm ![2, 3, 4, 0, 1] ![3, 4, 0, 1, 2] (by decide) (by decide),
    mkPerm ![2, 4, 0, 1, 3] ![2, 3, 0, 4, 1] (by decide) (by decide),
    mkPerm ![3, 4, 0, 1, 2] ![2, 3, 4, 0, 1] (by decide) (by decide),
    mkPerm ![0, 2, 1, 3, 4] ![0, 2, 1, 3, 4] (by decide) (by decide),
    mkPerm ![0, 3, 1, 2, 4] ![0, 2, 3, 1, 4] (by decide) (by decide),
    mkPerm ![0, 3, 2, 4, 1] ![0, 4, 2, 1, 3] (by decide) (by decide),
    mkPerm ![1, 3, 2, 4, 0] ![4, 0, 2, 1, 3] (by decide) (by decide),
    mkPerm ![1, 4, 2, 3, 0] ![4, 0, 2, 3, 1] (by decide) (by decide)]

theorem exists_perm_std : ∀ v : Fin 4 → ZMod 3, v ≠ 0 → ∃ σ ∈ perms, ∃ i : Fin 4,
    ext3 v ∘ σ = ext3 (std i) ∨ ext3 v ∘ σ = ext3 (2 • std i) := by
  decide

theorem δ_pow_three (v : Fin 4 → ZMod 3) : δ (Multiplicative.ofAdd v) ^ 3 = 1 := by
  rw [← map_pow]
  have : (Multiplicative.ofAdd v) ^ 3 = 1 := by
    apply Multiplicative.toAdd.injective
    funext i
    simp only [toAdd_pow, toAdd_ofAdd, toAdd_one, Pi.smul_apply, Pi.zero_apply, nsmul_eq_mul]
    rw [show ((3 : ℕ) : ZMod 3) = 0 from rfl, zero_mul]
  rw [this, map_one]

theorem δ_two_smul (v : Fin 4 → ZMod 3) :
    δ (Multiplicative.ofAdd (2 • v)) = δ (Multiplicative.ofAdd v) ^ 2 := by
  rw [← map_pow]
  rfl

theorem orderThreeAt_of_std (h : ∀ i : Fin 4,
    OrderThreeAt (⊤ : Subgroup SUI) A0 (Subgroup.zpowers (δ (Multiplicative.ofAdd (std i))))) :
    ∀ B : Subgroup SUI, B ≤ A0 → Nat.card B = 3 → OrderThreeAt (⊤ : Subgroup SUI) A0 B := by
  intro B hBA hB3
  have hB1 : B ≠ ⊥ := by
    intro hb
    rw [hb, Subgroup.card_bot] at hB3
    omega
  obtain ⟨⟨b, hbB⟩, hb'⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hB1
  have hb1 : b ≠ 1 := fun e => hb' (Subtype.ext e)
  obtain ⟨v, rfl⟩ := hBA hbB
  have hv : Multiplicative.toAdd v ≠ 0 := by
    intro h0
    apply hb1
    have : v = 1 := Multiplicative.toAdd.injective h0
    rw [this, map_one]
  obtain ⟨σ, -, i, hσ⟩ := exists_perm_std _ hv
  have hBb := eq_zpowers_of_card_three hB3 hbB hb1
  set φ := reindexSU σ
  have hmapB : B.map φ.toMonoidHom = Subgroup.zpowers (δ (Multiplicative.ofAdd (std i))) := by
    rw [hBb, MonoidHom.map_zpowers]
    change Subgroup.zpowers (reindexSU σ (δ v)) = _
    rw [show v = Multiplicative.ofAdd (Multiplicative.toAdd v) from rfl, reindexSU_δ]
    rcases hσ with hσ | hσ
    · rw [hσ, res3_ext3]
    · rw [hσ, res3_ext3, δ_two_smul, zpowers_sq (δ_pow_three _)]
  have hA : A0.map φ.symm.toMonoidHom = A0 := by
    have h1 := congrArg (Subgroup.map φ.symm.toMonoidHom) (map_reindexSU_A0 σ)
    rwa [Subgroup.map_map, show φ.symm.toMonoidHom.comp φ.toMonoidHom = MonoidHom.id SUI from by
      ext; simp, Subgroup.map_id, eq_comm] at h1
  have hB : (B.map φ.toMonoidHom).map φ.symm.toMonoidHom = B := by
    rw [Subgroup.map_map, show φ.symm.toMonoidHom.comp φ.toMonoidHom = MonoidHom.id SUI from by
      ext; simp, Subgroup.map_id]
  have := (h i).map φ.symm
  rwa [map_top_mulEquiv, hA, ← hmapB, hB] at this

theorem isBlockDiag_of_mem_centralizer {u : Fin 4 → ZMod 9} {g : SUI}
    (hg : g ∈ Subgroup.centralizer ({τ (Multiplicative.ofAdd u)} : Set SUI)) :
    IsBlockDiag (ext9 u) (mU g) := by
  rw [Subgroup.mem_centralizer_singleton_iff] at hg
  have h := congrArg mU hg
  rw [mU_mul, mU_mul, mU_τ, dgU] at h
  exact IsBlockDiag.of_comp (t := ext9 u) eζ_injective (isBlockDiag_of_commute h)

theorem mem_centralizer_of_isBlockDiag {u : Fin 4 → ZMod 9} {g : SUI}
    (hg : IsBlockDiag (ext9 u) (mU g)) :
    g ∈ Subgroup.centralizer ({τ (Multiplicative.ofAdd u)} : Set SUI) := by
  rw [Subgroup.mem_centralizer_singleton_iff]
  apply mU_injective
  rw [mU_mul, mU_mul, mU_τ, dgU]
  exact commute_of_isBlockDiag (hg.comp eζ)

theorem mem_centralizer_of_constant {u w : Fin 4 → ZMod 9}
    (hw : ∀ i j, ext9 u i = ext9 u j → ext9 w i = ext9 w j) :
    τ (Multiplicative.ofAdd w) ∈ Subgroup.centralizer
      (Subgroup.centralizer ({τ (Multiplicative.ofAdd u)} : Set SUI) : Set SUI) := by
  rw [Subgroup.mem_centralizer_iff]
  intro g hg
  apply mU_injective
  rw [mU_mul, mU_mul, mU_τ, dgU]
  exact commute_diagonal_of_isBlockDiag (s := fun i => eζ (ext9 w i))
    (fun i j h => by rw [hw i j h]) (isBlockDiag_of_mem_centralizer hg)

theorem isIdOutside_τ {c : Set (Fin 5)} {w : Fin 4 → ZMod 9} (hw : ∀ i, i ∉ c → ext9 w i = 0) :
    IsIdOutside c (mU (τ (Multiplicative.ofAdd w))) := by
  rw [mU_τ, dgU]
  exact isIdOutside_diagonal fun i hi => by rw [hw i hi, eζ_zero]

theorem layerCent_top_zpowers (b : SUI) :
    layerCent (⊤ : Subgroup SUI) (Subgroup.zpowers b) =
      inSubgroup CFSG.layer (Subgroup.centralizer ({b} : Set SUI)) := by
  rw [layerCent, top_inf_eq, Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]

theorem layerCent_le_centralizer_τ (u : Fin 4 → ZMod 9) :
    layerCent (⊤ : Subgroup SUI) (Subgroup.zpowers (τ (Multiplicative.ofAdd u))) ≤
      Subgroup.centralizer ({τ (Multiplicative.ofAdd u)} : Set SUI) := by
  rw [layerCent_top_zpowers]
  exact Subgroup.map_subtype_le _

@[expose] def idOutsideSU (c : Set (Fin 5)) : Subgroup SUI where
  carrier := {x | IsIdOutside c (mU x)}
  mul_mem' {x y} hx hy := by
    change IsIdOutside c (mU (x * y))
    rw [mU_mul]
    exact hx.mul hy
  one_mem' := fun _ _ _ => rfl
  inv_mem' {x} hx := hx.of_mul_eq_one (mU_mul_inv x) (mU_inv_mul x)

theorem centralizer_le_normalizer_idOutsideSU {u : Fin 4 → ZMod 9} {c : Set (Fin 5)}
    (hc : ∀ i j, ext9 u i = ext9 u j → (i ∈ c ↔ j ∈ c)) :
    Subgroup.centralizer ({τ (Multiplicative.ofAdd u)} : Set SUI) ≤
      Subgroup.normalizer (idOutsideSU c : Set SUI) := by
  set C := Subgroup.centralizer ({τ (Multiplicative.ofAdd u)} : Set SUI)
  have key : ∀ g ∈ C, ∀ s ∈ idOutsideSU c, g * s * g⁻¹ ∈ idOutsideSU c := by
    intro g hg s hs
    change IsIdOutside c (mU (g * s * g⁻¹))
    rw [mU_mul, mU_mul]
    exact IsIdOutside.conj_of_union hc (isBlockDiag_of_mem_centralizer hg)
      (isBlockDiag_of_mem_centralizer (C.inv_mem hg)) (mU_mul_inv g) hs
  intro g hg
  rw [Subgroup.mem_normalizer_iff]
  intro s
  refine ⟨key g hg s, fun h => ?_⟩
  have := key g⁻¹ (C.inv_mem hg) _ h
  simpa [mul_assoc] using this

theorem isQuasisimple_SL2_F8 : CFSG.IsQuasisimple
    (SpecialLinearGroup (Fin 2) (CFSG.LieType.Steinberg.fixedSubfield K 2 3)) := by
  set F := CFSG.LieType.Steinberg.fixedSubfield K 2 3
  have : CharP F 2 := (RingHom.charP_iff_charP F.subtype 2).mpr inferInstance
  have := Fintype.ofFinite F
  have h4 : ∃ s : Finset F, s.card = 4 := by
    have hle : 4 ≤ (Finset.univ : Finset F).card := by
      rw [Finset.card_univ, ← Nat.card_eq_fintype_card,
        CFSG.LieType.Steinberg.card_fixedSubfield card_K]
      norm_num
    obtain ⟨s, -, hs⟩ := Finset.exists_subset_card_eq hle
    exact ⟨s, hs⟩
  obtain ⟨-, hsimple, -⟩ :=
    CFSG.LinearGroups.linear_projective_simple (K := F) (n := 2) le_rfl (Or.inr h4)
  refine isQuasisimple_of_isSimpleGroup
    (CFSG.Walter.psl2MulEquivSL2OfCharTwo (K := F)).symm.isSimpleGroup ?_
  refine ⟨⟨!![1, 1; 0, 1], by simp [det_fin_two]⟩, ⟨!![1, 0; 1, 1], by simp [det_fin_two]⟩, ?_⟩
  intro h
  have h' := congrArg (fun x : SpecialLinearGroup (Fin 2) F => (x : Matrix (Fin 2) (Fin 2) F) 0 0) h
  change (!![1, 1; 0, 1] * !![1, 0; 1, 1] : Matrix (Fin 2) (Fin 2) F) 0 0 =
    (!![1, 0; 1, 1] * !![1, 1; 0, 1] : Matrix (Fin 2) (Fin 2) F) 0 0 at h'
  simp [Matrix.mul_apply, Fin.sum_univ_two] at h'

theorem isQuasisimple_SU {k : ℕ} (hk : 2 ≤ k) : CFSG.IsQuasisimple (StatedSU k (2 ^ 3) K) := by
  rcases (show k = 2 ∨ 3 ≤ k by omega) with rfl | hk3
  · obtain ⟨e⟩ := CFSG.RankThree.SubgroupLists.nonempty_sl2_mulEquiv_statedSU_two (r := 2)
      (f := 3) card_K
    exact CFSG.LocalCores.isQuasisimple_of_mulEquiv e isQuasisimple_SL2_F8
  · refine (CFSG.LieType.Universal.Unitary.isQuasisimple_statedSU_of_card (p := 2) (f := 3)
      card_K hk3 ?_).1
    intro h
    have := congrArg Prod.snd h
    norm_num at this

theorem le_layerCent_of_normal {u : Fin 4 → ZMod 9} {S : Subgroup SUI}
    (hSC : S ≤ Subgroup.centralizer ({τ (Multiplicative.ofAdd u)} : Set SUI))
    (hCS : Subgroup.centralizer ({τ (Multiplicative.ofAdd u)} : Set SUI) ≤
      Subgroup.normalizer (S : Set SUI)) (hq : CFSG.IsQuasisimple S) :
    S ≤ layerCent (⊤ : Subgroup SUI) (Subgroup.zpowers (τ (Multiplicative.ofAdd u))) := by
  rw [layerCent_top_zpowers]
  exact le_inSubgroup_layer_of_normal hSC hCS hq

theorem block_le_layer {u : Fin 4 → ZMod 9} {κ : ZMod 9} {k : ℕ} (f : Fin k → Fin 5)
    (hf : Function.Injective f) (hfib : Set.range f = {i | ext9 u i = κ}) (hk : 2 ≤ k) :
    idOutsideSU {i | ext9 u i = κ} ≤
      layerCent (⊤ : Subgroup SUI) (Subgroup.zpowers (τ (Multiplicative.ofAdd u))) := by
  have hrange : idOutsideSU {i | ext9 u i = κ} =
      (embedSU hf card_K (by omega) (by norm_num : 1 ≤ 5)).range := by
    ext x
    rw [mem_range_embedSU_iff, hfib]
    exact Iff.rfl
  refine le_layerCent_of_normal (fun x hx => mem_centralizer_of_isBlockDiag
    (IsIdOutside.isBlockDiag hx)) ?_ ?_
  · exact centralizer_le_normalizer_idOutsideSU fun i j e => by
      simp only [Set.mem_ofPred_eq, e]
  · rw [hrange]
    exact CFSG.LocalCores.isQuasisimple_of_mulEquiv
      (MonoidHom.ofInjective (embedSU_injective hf card_K _ _)) (isQuasisimple_SU hk)

theorem τ_mem_idOutsideSU {u w : Fin 4 → ZMod 9} {κ : ZMod 9}
    (hw : ∀ i, ¬ext9 u i = κ → ext9 w i = 0) :
    τ (Multiplicative.ofAdd w) ∈ idOutsideSU {i | ext9 u i = κ} :=
  isIdOutside_τ hw

theorem range_eq_setOf {k : ℕ} {f : Fin k → Fin 5} {P : Fin 5 → Prop}
    (h : ∀ i, (∃ a, f a = i) ↔ P i) : Set.range f = {i | P i} :=
  Set.ext h

theorem inner_of_witness {u : Fin 4 → ZMod 9} (r : (Fin 4 → ZMod 3) → (Fin 4 → ZMod 9))
    (hr : ∀ w, τ (Multiplicative.ofAdd (r w)) ∈
      layerCent (⊤ : Subgroup SUI) (Subgroup.zpowers (τ (Multiplicative.ofAdd u))))
    (hc : ∀ w i j, ext9 u i = ext9 u j → ext9 (ι3v w - r w) i = ext9 (ι3v w - r w) j) :
    ∀ a ∈ A0, ∃ y ∈ layerCent (⊤ : Subgroup SUI) (Subgroup.zpowers (τ (Multiplicative.ofAdd u))),
      y⁻¹ * a ∈ Subgroup.centralizer ((layerCent (⊤ : Subgroup SUI)
        (Subgroup.zpowers (τ (Multiplicative.ofAdd u))) : Subgroup SUI) : Set SUI) := by
  rintro _ ⟨w, rfl⟩
  refine ⟨_, hr (Multiplicative.toAdd w), ?_⟩
  have e : (τ (Multiplicative.ofAdd (r (Multiplicative.toAdd w))))⁻¹ * δ w =
      τ (Multiplicative.ofAdd (ι3v (Multiplicative.toAdd w) - r (Multiplicative.toAdd w))) := by
    rw [show δ w = τ (Multiplicative.ofAdd (ι3v (Multiplicative.toAdd w))) from rfl, ← map_inv,
      ← map_mul]
    congr 1
    apply Multiplicative.toAdd.injective
    simp only [toAdd_mul, toAdd_inv, toAdd_ofAdd]
    exact neg_add_eq_sub _ _
  rw [e]
  exact Subgroup.centralizer_le (layerCent_le_centralizer_τ u)
    (mem_centralizer_of_constant (hc _))

theorem good_map (φ : SUI ≃* SUI) (hA : A0.map φ.toMonoidHom = A0) {X : Subgroup SUI}
    (h : A0 ≤ layerCent (⊤ : Subgroup SUI) X ⊔ X) :
    A0 ≤ layerCent (⊤ : Subgroup SUI) (X.map φ.toMonoidHom) ⊔ X.map φ.toMonoidHom := by
  rw [← hA, ← map_top_mulEquiv φ, ← map_layerCent, ← Subgroup.map_sup]
  exact Subgroup.map_mono h

abbrev us (i : Fin 4) : Fin 4 → ZMod 9 := ι3v (std i)

abbrev bs (i : Fin 4) : SUI := δ (Multiplicative.ofAdd (std i))

abbrev Bs (i : Fin 4) : Subgroup SUI := Subgroup.zpowers (bs i)

abbrev Ys (i : Fin 4) : Subgroup SUI := layerCent (⊤ : Subgroup SUI) (Bs i)

theorem card_zpowers_δ {w : Fin 4 → ZMod 3} (hw : w ≠ 0) :
    Nat.card (Subgroup.zpowers (δ (Multiplicative.ofAdd w))) = 3 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  rw [Nat.card_zpowers]
  refine orderOf_eq_prime (δ_pow_three w) fun h => hw ?_
  have h1 : δ (Multiplicative.ofAdd w) = δ 1 := by rw [h, map_one]
  exact Multiplicative.ofAdd.injective (δ_injective h1)

theorem δ_mem_A0 (w : Fin 4 → ZMod 3) : δ (Multiplicative.ofAdd w) ∈ A0 := ⟨_, rfl⟩

theorem zpowers_δ_le_A0 (w : Fin 4 → ZMod 3) :
    Subgroup.zpowers (δ (Multiplicative.ofAdd w)) ≤ A0 :=
  (Subgroup.zpowers_le).mpr (δ_mem_A0 w)

theorem δ_nsmul (n : ℕ) (w : Fin 4 → ZMod 3) :
    δ (Multiplicative.ofAdd (n • w)) = δ (Multiplicative.ofAdd w) ^ n := by
  rw [ofAdd_nsmul, map_pow]

theorem blk0_le : idOutsideSU {i | ext9 (us 0) i = 0} ≤ Ys 0 :=
  block_le_layer ![2, 3, 4] (by decide) (range_eq_setOf (by decide)) (by norm_num)

theorem blk1a_le : idOutsideSU {i | ext9 (us 1) i = 3} ≤ Ys 1 :=
  block_le_layer ![0, 1, 2] (by decide) (range_eq_setOf (by decide)) (by norm_num)

theorem blk1b_le : idOutsideSU {i | ext9 (us 1) i = 0} ≤ Ys 1 :=
  block_le_layer ![3, 4] (by decide) (range_eq_setOf (by decide)) le_rfl

theorem blk2a_le : idOutsideSU {i | ext9 (us 2) i = 3} ≤ Ys 2 :=
  block_le_layer ![0, 1] (by decide) (range_eq_setOf (by decide)) le_rfl

theorem blk2b_le : idOutsideSU {i | ext9 (us 2) i = 6} ≤ Ys 2 :=
  block_le_layer ![2, 3] (by decide) (range_eq_setOf (by decide)) le_rfl

theorem blk3_le : idOutsideSU {i | ext9 (us 3) i = 3} ≤ Ys 3 :=
  block_le_layer ![0, 1, 2, 3] (by decide) (range_eq_setOf (by decide)) (by norm_num)

@[expose] def r0 (w : Fin 4 → ZMod 3) : Fin 4 → ZMod 9 :=
  ![0, 0, ι3 (w 2) - ((-(w 0 + w 1)).val : ZMod 9), ι3 (w 3) - ((-(w 0 + w 1)).val : ZMod 9)]

theorem supp_r0 : ∀ w i, ¬ext9 (us 0) i = 0 → ext9 (r0 w) i = 0 := by decide

theorem const_r0 : ∀ w i j, ext9 (us 0) i = ext9 (us 0) j →
    ext9 (ι3v w - r0 w) i = ext9 (ι3v w - r0 w) j := by
  decide

theorem inner_b0 : ∀ a ∈ A0, ∃ y ∈ Ys 0, y⁻¹ * a ∈ Subgroup.centralizer (Ys 0 : Set SUI) :=
  inner_of_witness r0 (fun w => blk0_le (τ_mem_idOutsideSU (supp_r0 w))) const_r0

@[expose] def r1a (w : Fin 4 → ZMod 3) : Fin 4 → ZMod 9 :=
  ![ι3 (w 0) - ((w 0 + w 1 + w 2).val : ZMod 9), ι3 (w 1) - ((w 0 + w 1 + w 2).val : ZMod 9),
    ι3 (w 2) - ((w 0 + w 1 + w 2).val : ZMod 9), 0]

@[expose] def r1b (w : Fin 4 → ZMod 3) : Fin 4 → ZMod 9 :=
  ![0, 0, 0, ι3 (w 3) - ι3 (2 * -(w 0 + w 1 + w 2))]

theorem supp_r1a : ∀ w i, ¬ext9 (us 1) i = 3 → ext9 (r1a w) i = 0 := by decide

theorem supp_r1b : ∀ w i, ¬ext9 (us 1) i = 0 → ext9 (r1b w) i = 0 := by decide

theorem const_r1 : ∀ w i j, ext9 (us 1) i = ext9 (us 1) j →
    ext9 (ι3v w - (r1a w + r1b w)) i = ext9 (ι3v w - (r1a w + r1b w)) j := by
  decide

theorem inner_b1 : ∀ a ∈ A0, ∃ y ∈ Ys 1, y⁻¹ * a ∈ Subgroup.centralizer (Ys 1 : Set SUI) := by
  refine inner_of_witness (fun w => r1a w + r1b w) (fun w => ?_) const_r1
  rw [ofAdd_add, map_mul]
  exact Subgroup.mul_mem _ (blk1a_le (τ_mem_idOutsideSU (supp_r1a w)))
    (blk1b_le (τ_mem_idOutsideSU (supp_r1b w)))

@[expose] def r2a (w : Fin 4 → ZMod 3) : Fin 4 → ZMod 9 :=
  ![ι3 (w 0) - ι3 (2 * (w 0 + w 1)), ι3 (w 1) - ι3 (2 * (w 0 + w 1)), 0, 0]

@[expose] def r2b (w : Fin 4 → ZMod 3) : Fin 4 → ZMod 9 :=
  ![0, 0, ι3 (w 2) - ι3 (2 * (w 2 + w 3)), ι3 (w 3) - ι3 (2 * (w 2 + w 3))]

theorem supp_r2a : ∀ w i, ¬ext9 (us 2) i = 3 → ext9 (r2a w) i = 0 := by decide

theorem supp_r2b : ∀ w i, ¬ext9 (us 2) i = 6 → ext9 (r2b w) i = 0 := by decide

theorem const_r2 : ∀ w i j, ext9 (us 2) i = ext9 (us 2) j →
    ext9 (ι3v w - (r2a w + r2b w)) i = ext9 (ι3v w - (r2a w + r2b w)) j := by
  decide

theorem inner_b2 : ∀ a ∈ A0, ∃ y ∈ Ys 2, y⁻¹ * a ∈ Subgroup.centralizer (Ys 2 : Set SUI) := by
  refine inner_of_witness (fun w => r2a w + r2b w) (fun w => ?_) const_r2
  rw [ofAdd_add, map_mul]
  exact Subgroup.mul_mem _ (blk2a_le (τ_mem_idOutsideSU (supp_r2a w)))
    (blk2b_le (τ_mem_idOutsideSU (supp_r2b w)))

@[expose] def r3 (w : Fin 4 → ZMod 3) : Fin 4 → ZMod 9 :=
  ![ι3 (w 0) - ι3 (w 0 + w 1 + w 2 + w 3), ι3 (w 1) - ι3 (w 0 + w 1 + w 2 + w 3),
    ι3 (w 2) - ι3 (w 0 + w 1 + w 2 + w 3), ι3 (w 3) - ι3 (w 0 + w 1 + w 2 + w 3)]

theorem supp_r3 : ∀ w i, ¬ext9 (us 3) i = 3 → ext9 (r3 w) i = 0 := by decide

theorem const_r3 : ∀ w i j, ext9 (us 3) i = ext9 (us 3) j →
    ext9 (ι3v w - r3 w) i = ext9 (ι3v w - r3 w) j := by
  decide

theorem inner_b3 : ∀ a ∈ A0, ∃ y ∈ Ys 3, y⁻¹ * a ∈ Subgroup.centralizer (Ys 3 : Set SUI) :=
  inner_of_witness r3 (fun w => blk3_le (τ_mem_idOutsideSU (supp_r3 w))) const_r3

theorem decomp_b3 : ∀ w : Fin 4 → ZMod 3,
    w = (w - (w 0 + w 1 + w 2 + w 3) • std 3) + (w 0 + w 1 + w 2 + w 3).val • std 3 := by
  decide

theorem supp_b3 : ∀ w : Fin 4 → ZMod 3, ∀ i, ¬ext9 (us 3) i = 3 →
    ext9 (ι3v (w - (w 0 + w 1 + w 2 + w 3) • std 3)) i = 0 := by
  decide

theorem good_b3 : A0 ≤ Ys 3 ⊔ Bs 3 := by
  rintro _ ⟨w, rfl⟩
  obtain ⟨w, rfl⟩ : ∃ w' : Fin 4 → ZMod 3, Multiplicative.ofAdd w' = w :=
    ⟨Multiplicative.toAdd w, rfl⟩
  rw [decomp_b3 w, ofAdd_add, map_mul, δ_nsmul]
  exact Subgroup.mul_mem _ (Subgroup.mem_sup_left (blk3_le (τ_mem_idOutsideSU (supp_b3 w))))
    (Subgroup.mem_sup_right (Subgroup.pow_mem _ (Subgroup.mem_zpowers _) _))

abbrev X' : Subgroup SUI := Subgroup.zpowers (δ (Multiplicative.ofAdd ![1, 2, 1, 1]))

theorem X'_eq : X' = (Bs 3).map (reindexSU (Equiv.swap 1 4)).toMonoidHom := by
  rw [MonoidHom.map_zpowers]
  change _ = Subgroup.zpowers (reindexSU (Equiv.swap 1 4) (bs 3))
  rw [reindexSU_δ]
  have e : res3 (ext3 (std 3) ∘ ⇑(Equiv.swap (1 : Fin 5) 4)) = ![1, 2, 1, 1] := by decide
  rw [e]

theorem good_X' : A0 ≤ layerCent (⊤ : Subgroup SUI) X' ⊔ X' := by
  rw [X'_eq]
  exact good_map _ (map_reindexSU_A0 _) good_b3

theorem card_X' : Nat.card X' = 3 := card_zpowers_δ (by decide)

theorem X'_le_Y0 : X' ≤ Ys 0 ⊔ Bs 0 := by
  refine (Subgroup.zpowers_le).mpr ?_
  have e : (![1, 2, 1, 1] : Fin 4 → ZMod 3) = ![0, 0, 1, 1] + std 0 := by decide
  rw [e, ofAdd_add, map_mul]
  exact Subgroup.mul_mem _ (Subgroup.mem_sup_left (blk0_le (τ_mem_idOutsideSU
    (w := ι3v ![0, 0, 1, 1]) (by decide)))) (Subgroup.mem_sup_right (Subgroup.mem_zpowers _))

theorem Bs3_le_Y1 : Bs 3 ≤ Ys 1 ⊔ Bs 1 := by
  refine (Subgroup.zpowers_le).mpr ?_
  have e : std 3 = ![0, 0, 0, 1] + std 1 := by decide
  change δ (Multiplicative.ofAdd (std 3)) ∈ _
  rw [e, ofAdd_add, map_mul]
  exact Subgroup.mul_mem _ (Subgroup.mem_sup_left (blk1b_le (τ_mem_idOutsideSU
    (w := ι3v ![0, 0, 0, 1]) (by decide)))) (Subgroup.mem_sup_right (Subgroup.mem_zpowers _))

theorem Bs0_le_Y2 : Bs 0 ≤ Ys 2 ⊔ Bs 2 :=
  le_sup_of_le_left ((Subgroup.zpowers_le).mpr (blk2a_le (τ_mem_idOutsideSU
    (w := ι3v (std 0)) (by decide))))

theorem orderThreeAt_std (i : Fin 4) : OrderThreeAt (⊤ : Subgroup SUI) A0 (Bs i) := by
  fin_cases i
  · exact ⟨Or.inl inner_b0, X', X', zpowers_δ_le_A0 _, card_X', X'_le_Y0, zpowers_δ_le_A0 _,
      card_X', le_sup_right, good_X'⟩
  · exact ⟨Or.inl inner_b1, Bs 3, Bs 3, zpowers_δ_le_A0 _, card_zpowers_δ (by decide),
      Bs3_le_Y1, zpowers_δ_le_A0 _, card_zpowers_δ (by decide), le_sup_right, good_b3⟩
  · exact ⟨Or.inl inner_b2, Bs 0, X', zpowers_δ_le_A0 _, card_zpowers_δ (by decide),
      Bs0_le_Y2, zpowers_δ_le_A0 _, card_X', X'_le_Y0, good_X'⟩
  · exact ⟨Or.inl inner_b3, Bs 3, Bs 3, zpowers_δ_le_A0 _, card_zpowers_δ (by decide),
      le_sup_right, zpowers_δ_le_A0 _, card_zpowers_δ (by decide), le_sup_right, good_b3⟩

theorem orderThreeAt_A0 : ∀ B : Subgroup SUI, B ≤ A0 → Nat.card B = 3 →
    OrderThreeAt (⊤ : Subgroup SUI) A0 B :=
  orderThreeAt_of_std orderThreeAt_std

theorem terminalOrderThreeU58 : TerminalOrderThreeU58 := by
  intro G _ _ I A hAI hAe ⟨e⟩ hA B hBA hB3
  apply OrderThreeAt.of_subgroupOf hAI hBA
  set e' : I ≃* SUI := e.trans equivSUI
  have hA'e : IsElemAbelian 3 ((A.subgroupOf I).map e'.toMonoidHom) :=
    CFSG.RankThree.PartTwo.Sec21.isElemAbelian_map (isElemAbelian_subgroupOf hAe I) _
  have hcardA : Nat.card ((A.subgroupOf I).map e'.toMonoidHom) = 3 ^ 4 := by
    rw [Subgroup.card_map_of_injective e'.injective,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAI).toEquiv, hA]
  obtain ⟨x, hx⟩ := exists_map_conj_eq_A0 hA'e hcardA
  set φ : I ≃* SUI := e'.trans (MulAut.conj x)
  have hφA : (A.subgroupOf I).map φ.toMonoidHom = A0 := by
    rw [← hx, Subgroup.map_map]
    rfl
  have hB' : (B.subgroupOf I).map φ.toMonoidHom ≤ A0 := by
    rw [← hφA]
    exact Subgroup.map_mono (fun x hx => hBA hx)
  have hcardB : Nat.card ((B.subgroupOf I).map φ.toMonoidHom) = 3 := by
    rw [Subgroup.card_map_of_injective φ.injective,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe (hBA.trans hAI)).toEquiv, hB3]
  have h := (orderThreeAt_A0 _ hB' hcardB).map φ.symm
  have hsymm : ∀ X : Subgroup I, (X.map φ.toMonoidHom).map φ.symm.toMonoidHom = X := by
    intro X
    rw [Subgroup.map_map, show φ.symm.toMonoidHom.comp φ.toMonoidHom = MonoidHom.id I from by
      ext; simp, Subgroup.map_id]
  rwa [← hφA, hsymm, hsymm, show (⊤ : Subgroup SUI).map φ.symm.toMonoidHom = ⊤ from by
    rw [← MonoidHom.range_eq_map]; exact MonoidHom.range_eq_top.mpr φ.symm.surjective] at h

end CFSG.RankThree.PartTwo.Sec21.TablesU58
