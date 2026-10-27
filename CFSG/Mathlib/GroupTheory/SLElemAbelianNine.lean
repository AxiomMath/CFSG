module

public import CFSG.Open.LocalVocabulary
public import CFSG.Open.StatedDefs
public import CFSG.Adapters.StatedSLTwoField
public import CFSG.GroupTheory.ElemAbelianClosure
public import CFSG.Open.Defs

@[expose] public section

namespace CFSG.SLElemAbelianNine

open CFSG.Open (StatedClassicalModel)
open CFSG.Open

private abbrev SL (n : Type*) [Fintype n] [DecidableEq n] : Type _ :=
  Matrix.SpecialLinearGroup n (ZMod 2)

private def Zmat : Matrix (Fin 2) (Fin 2) (ZMod 2) := Matrix.of ![![0, 1], ![1, 1]]

private theorem det_Zmat : Zmat.det = 1 := by
  rw [Matrix.det_fin_two]
  norm_num [Zmat]
  decide +kernel

private def Z : SL (Fin 2) := ⟨Zmat, det_Zmat⟩

private theorem Z_pow_three : Z ^ 3 = 1 := by
  apply Subtype.ext
  change Zmat ^ 3 = 1
  ext i j
  fin_cases i <;> fin_cases j <;> decide +kernel

private theorem Z_ne_one : Z ≠ 1 := by
  intro h
  have h' := congrArg (fun x : SL (Fin 2) =>
    (x : Matrix (Fin 2) (Fin 2) (ZMod 2)) 0 1) h
  simp [Z, Zmat] at h'

private theorem orderOf_Z : orderOf Z = 3 :=
  orderOf_eq_prime Z_pow_three Z_ne_one

private def reindexSL {n m : Type} [Fintype n] [Fintype m] [DecidableEq n] [DecidableEq m]
    (e : n ≃ m) : SL n ≃* SL m where
  toFun A := ⟨Matrix.reindex e e (A : Matrix n n (ZMod 2)), by
    rw [Matrix.det_reindex_self e]; exact A.prop⟩
  invFun B := ⟨Matrix.reindex e.symm e.symm (B : Matrix m m (ZMod 2)), by
    rw [Matrix.det_reindex_self e.symm]; exact B.prop⟩
  left_inv A := by
    apply Subtype.ext
    ext i j
    simp [Matrix.reindex_apply, Equiv.symm_apply_apply]
  right_inv B := by
    apply Subtype.ext
    ext i j
    simp [Matrix.reindex_apply]
  map_mul' A B := by
    apply Subtype.ext
    change ((A : Matrix n n (ZMod 2)) * (B : Matrix n n (ZMod 2))).submatrix e.symm e.symm =
      ((A : Matrix n n (ZMod 2)).submatrix e.symm e.symm) *
        ((B : Matrix n n (ZMod 2)).submatrix e.symm e.symm)
    rw [Matrix.submatrix_mul_equiv (A : Matrix n n (ZMod 2))
      (B : Matrix n n (ZMod 2)) e.symm e.symm e.symm]

private def blk {n₁ n₂ : Type} [Fintype n₁] [Fintype n₂] [DecidableEq n₁] [DecidableEq n₂] :
    SL n₁ × SL n₂ →* SL (n₁ ⊕ n₂) where
  toFun AB :=
    ⟨Matrix.fromBlocks (AB.1 : Matrix n₁ n₁ (ZMod 2)) 0 0
      (AB.2 : Matrix n₂ n₂ (ZMod 2)), by
      rw [Matrix.det_fromBlocks_zero₁₂, AB.1.prop, AB.2.prop, mul_one]⟩
  map_one' := Subtype.ext (by
    change Matrix.fromBlocks (1 : Matrix n₁ n₁ (ZMod 2)) 0 0
      (1 : Matrix n₂ n₂ (ZMod 2)) = 1
    rw [Matrix.fromBlocks_one])
  map_mul' AB CD := Subtype.ext (by
    change Matrix.fromBlocks ((AB.1 : Matrix n₁ n₁ (ZMod 2)) * (CD.1 : Matrix n₁ n₁ (ZMod 2)))
        0 0
      ((AB.2 : Matrix n₂ n₂ (ZMod 2)) * (CD.2 : Matrix n₂ n₂ (ZMod 2))) =
      Matrix.fromBlocks (AB.1 : Matrix n₁ n₁ (ZMod 2)) 0 0
        (AB.2 : Matrix n₂ n₂ (ZMod 2)) *
      Matrix.fromBlocks (CD.1 : Matrix n₁ n₁ (ZMod 2)) 0 0
        (CD.2 : Matrix n₂ n₂ (ZMod 2))
    rw [Matrix.fromBlocks_multiply]
    simp)

private theorem blk_val {n₁ n₂ : Type} [Fintype n₁] [Fintype n₂] [DecidableEq n₁]
    [DecidableEq n₂] (A : SL n₁) (B : SL n₂) :
    (blk (A, B) : Matrix (n₁ ⊕ n₂) (n₁ ⊕ n₂) (ZMod 2)) =
      Matrix.fromBlocks (A : Matrix n₁ n₁ (ZMod 2)) 0 0
        (B : Matrix n₂ n₂ (ZMod 2)) := rfl

private theorem blk_injective {n₁ n₂ : Type} [Fintype n₁] [Fintype n₂] [DecidableEq n₁]
    [DecidableEq n₂] : Function.Injective (blk (n₁ := n₁) (n₂ := n₂)) := by
  rintro ⟨A, B⟩ ⟨C, D⟩ h
  have hm : Matrix.fromBlocks (A : Matrix n₁ n₁ (ZMod 2)) 0 0
      (B : Matrix n₂ n₂ (ZMod 2)) =
      Matrix.fromBlocks (C : Matrix n₁ n₁ (ZMod 2)) 0 0
        (D : Matrix n₂ n₂ (ZMod 2)) := by
    simpa only [blk_val] using congrArg (fun x : SL (n₁ ⊕ n₂) =>
      (x : Matrix (n₁ ⊕ n₂) (n₁ ⊕ n₂) (ZMod 2))) h
  obtain ⟨h1, -, -, h2⟩ := Matrix.fromBlocks_inj.mp hm
  exact Prod.ext (Subtype.ext h1) (Subtype.ext h2)

private def psi {n₁ n₂ : Type} [Fintype n₁] [Fintype n₂] [DecidableEq n₁] [DecidableEq n₂] :
    Multiplicative (Matrix n₁ n₂ (ZMod 2)) →* SL (n₁ ⊕ n₂) where
  toFun N :=
    ⟨Matrix.fromBlocks (1 : Matrix n₁ n₁ (ZMod 2)) N.toAdd 0
      (1 : Matrix n₂ n₂ (ZMod 2)), by
      rw [Matrix.det_fromBlocks_zero₂₁]
      simp⟩
  map_one' := Subtype.ext (by
    change Matrix.fromBlocks (1 : Matrix n₁ n₁ (ZMod 2)) 0 0
      (1 : Matrix n₂ n₂ (ZMod 2)) = 1
    rw [Matrix.fromBlocks_one])
  map_mul' N N' := Subtype.ext (by
    change Matrix.fromBlocks (1 : Matrix n₁ n₁ (ZMod 2)) (N * N').toAdd 0
      (1 : Matrix n₂ n₂ (ZMod 2)) =
      Matrix.fromBlocks (1 : Matrix n₁ n₁ (ZMod 2)) N.toAdd 0
        (1 : Matrix n₂ n₂ (ZMod 2)) *
      Matrix.fromBlocks (1 : Matrix n₁ n₁ (ZMod 2)) N'.toAdd 0
        (1 : Matrix n₂ n₂ (ZMod 2))
    rw [Matrix.fromBlocks_multiply]
    simp [add_comm])

private theorem psi_val {n₁ n₂ : Type} [Fintype n₁] [Fintype n₂] [DecidableEq n₁]
    [DecidableEq n₂] (N : Multiplicative (Matrix n₁ n₂ (ZMod 2))) :
    (psi (n₁ := n₁) (n₂ := n₂) N : Matrix (n₁ ⊕ n₂) (n₁ ⊕ n₂) (ZMod 2)) =
      Matrix.fromBlocks (1 : Matrix n₁ n₁ (ZMod 2)) N.toAdd 0
        (1 : Matrix n₂ n₂ (ZMod 2)) := rfl

private theorem psi_injective {n₁ n₂ : Type} [Fintype n₁] [Fintype n₂] [DecidableEq n₁]
    [DecidableEq n₂] : Function.Injective (psi (n₁ := n₁) (n₂ := n₂)) := by
  rintro N N' h
  have hm : Matrix.fromBlocks (1 : Matrix n₁ n₁ (ZMod 2)) N.toAdd 0
      (1 : Matrix n₂ n₂ (ZMod 2)) =
      Matrix.fromBlocks (1 : Matrix n₁ n₁ (ZMod 2)) N'.toAdd 0
        (1 : Matrix n₂ n₂ (ZMod 2)) := by
    simpa only [psi_val] using congrArg (fun x : SL (n₁ ⊕ n₂) =>
      (x : Matrix (n₁ ⊕ n₂) (n₁ ⊕ n₂) (ZMod 2))) h
  exact Multiplicative.ext (Matrix.fromBlocks_inj.mp hm).2.1

private theorem psi_range_isPGroup {n₁ n₂ : Type} [Fintype n₁] [Fintype n₂]
    [DecidableEq n₁] [DecidableEq n₂] :
    IsPGroup 2 (psi (n₁ := n₁) (n₂ := n₂)).range := by
  rintro ⟨x, hx⟩
  obtain ⟨N, rfl⟩ := MonoidHom.mem_range.mp hx
  refine ⟨1, ?_⟩
  apply Subtype.ext
  show psi N ^ 2 = (1 : SL (n₁ ⊕ n₂))
  have hNN : N * N = 1 := by
    apply Multiplicative.ext
    rw [toAdd_mul, toAdd_one]
    ext i j
    simp only [Matrix.add_apply, Matrix.zero_apply]
    exact CharTwo.add_self_eq_zero _
  rw [pow_two, ← map_mul, hNN, map_one]

private theorem psi_range_ne_bot {n₁ n₂ : Type} [Fintype n₁] [Fintype n₂]
    [DecidableEq n₁] [DecidableEq n₂] (i : n₁) (j : n₂) :
    (psi (n₁ := n₁) (n₂ := n₂)).range ≠ ⊥ := by
  intro h
  have hmem : psi (Multiplicative.ofAdd (Matrix.single i j (1 : ZMod 2))) ∈
      (psi (n₁ := n₁) (n₂ := n₂)).range := ⟨_, rfl⟩
  rw [h] at hmem
  have h1 : psi (Multiplicative.ofAdd (Matrix.single i j (1 : ZMod 2))) = 1 :=
    Subgroup.mem_bot.mp hmem
  have h2 : Multiplicative.ofAdd (Matrix.single i j (1 : ZMod 2)) = 1 := by
    apply psi_injective
    rw [h1, map_one]
  have h3 : Matrix.single i j (1 : ZMod 2) = 0 := by
    have := congrArg Multiplicative.toAdd h2
    simpa using this
  have h4 : (1 : ZMod 2) = 0 := by
    simpa using congrArg (fun M : Matrix n₁ n₂ (ZMod 2) => M i j) h3
  exact one_ne_zero h4

private theorem blk_psi_conj {n₁ n₂ : Type} [Fintype n₁] [Fintype n₂] [DecidableEq n₁]
    [DecidableEq n₂] (A : SL n₁) (B : SL n₂)
    (N : Multiplicative (Matrix n₁ n₂ (ZMod 2))) :
    blk (A, B) * psi N * (blk (A, B))⁻¹ =
      psi (Multiplicative.ofAdd ((A : Matrix n₁ n₁ (ZMod 2)) * N.toAdd *
        ((B⁻¹ : SL n₂) : Matrix n₂ n₂ (ZMod 2)))) := by
  have hb : (blk (A, B))⁻¹ = blk (A⁻¹, B⁻¹) := by
    rw [← map_inv, Prod.inv_mk]
  rw [hb]
  apply Subtype.ext
  simp only [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_inv,
    blk_val, psi_val]
  rw [Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply]
  simp [Matrix.mul_adjugate, A.prop, B.prop]

private theorem blk_conj_mem_psi_range {n₁ n₂ : Type} [Fintype n₁] [Fintype n₂]
    [DecidableEq n₁] [DecidableEq n₂] (A : SL n₁) (B : SL n₂)
    {h : SL (n₁ ⊕ n₂)} (hh : h ∈ (psi (n₁ := n₁) (n₂ := n₂)).range) :
    blk (A, B) * h * (blk (A, B))⁻¹ ∈ (psi (n₁ := n₁) (n₂ := n₂)).range := by
  obtain ⟨N, hN⟩ := MonoidHom.mem_range.mp hh
  rw [← hN]
  exact ⟨Multiplicative.ofAdd ((A : Matrix n₁ n₁ (ZMod 2)) * N.toAdd *
    ((B⁻¹ : SL n₂) : Matrix n₂ n₂ (ZMod 2))), (blk_psi_conj A B N).symm⟩

private theorem blk_range_le_normalizer {n₁ n₂ : Type} [Fintype n₁] [Fintype n₂]
    [DecidableEq n₁] [DecidableEq n₂] :
    (blk (n₁ := n₁) (n₂ := n₂)).range ≤
      Subgroup.normalizer ((psi (n₁ := n₁) (n₂ := n₂)).range :
        Set (SL (n₁ ⊕ n₂))) := by
  rintro g ⟨AB, rfl⟩
  obtain ⟨A, B⟩ := AB
  rw [Subgroup.mem_normalizer_iff]
  intro h
  constructor
  · exact blk_conj_mem_psi_range A B
  · intro hh
    have h2 := blk_conj_mem_psi_range (A⁻¹) (B⁻¹) hh
    have hg : blk (A⁻¹, B⁻¹) = (blk (A, B))⁻¹ := by
      rw [← map_inv, Prod.inv_mk]
    rw [hg, inv_inv] at h2
    convert h2 using 1
    group

private def Z' (k : ℕ) : SL (Fin 2 ⊕ Fin k) :=
  blk (n₁ := Fin 2) (n₂ := Fin k) (Z, (1 : SL (Fin k)))

private theorem Z'_pow_three (k : ℕ) : (Z' k) ^ 3 = 1 := by
  have h : (Z, (1 : SL (Fin k))) ^ 3 = 1 := by
    ext <;> simp [Z_pow_three]
  unfold Z'
  rw [← map_pow, h, map_one]

private theorem Z'_ne_one (k : ℕ) : Z' k ≠ 1 := by
  intro h
  have h' : blk (n₁ := Fin 2) (n₂ := Fin k) (Z, (1 : SL (Fin k))) = 1 := by
    simpa only [Z'] using h
  have h1 : (Z, (1 : SL (Fin k))) = 1 :=
    blk_injective (n₁ := Fin 2) (n₂ := Fin k) (by rw [h', map_one])
  exact Z_ne_one (by simpa using congrArg Prod.fst h1)

private theorem orderOf_Z' (k : ℕ) : orderOf (Z' k) = 3 :=
  orderOf_eq_prime (Z'_pow_three k) (Z'_ne_one k)

private theorem isElemAbelian_prod {G H : Type} [Group G] [Group H] {p : ℕ}
    {A : Subgroup G} {B : Subgroup H} (hA : IsElemAbelian p A) (hB : IsElemAbelian p B) :
    IsElemAbelian p (A.prod B) := by
  have hcA := hA.1
  have hcB := hB.1
  refine ⟨⟨⟨fun a b => Subtype.ext (Prod.ext ?_ ?_)⟩⟩,
    fun x hx => Prod.ext (hA.2 _ hx.1) (hB.2 _ hx.2)⟩
  · exact congrArg Subtype.val (hcA.is_comm.comm
      ⟨(a : G × H).1, a.2.1⟩ ⟨(b : G × H).1, b.2.1⟩)
  · exact congrArg Subtype.val (hcB.is_comm.comm
      ⟨(a : G × H).2, a.2.2⟩ ⟨(b : G × H).2, b.2.2⟩)

private def E_block (k : ℕ) : Subgroup (SL (Fin 2 ⊕ (Fin 2 ⊕ Fin k))) :=
  ((Subgroup.zpowers Z).prod (Subgroup.zpowers (Z' k))).map
    (blk (n₁ := Fin 2) (n₂ := Fin 2 ⊕ Fin k))

private def T_block (k : ℕ) : Subgroup (SL (Fin 2 ⊕ (Fin 2 ⊕ Fin k))) :=
  (psi (n₁ := Fin 2) (n₂ := Fin 2 ⊕ Fin k)).range

private theorem E_block_isElemAbelian (k : ℕ) : IsElemAbelian 3 (E_block k) :=
  (isElemAbelian_prod (isElemAbelian_zpowers Z_pow_three)
    (isElemAbelian_zpowers (Z'_pow_three k))).map
    (blk (n₁ := Fin 2) (n₂ := Fin 2 ⊕ Fin k))

private theorem E_block_card (k : ℕ) : Nat.card (E_block k) = 9 := by
  have hcard : Nat.card (Subgroup.zpowers Z) * Nat.card (Subgroup.zpowers (Z' k)) = 9 := by
    rw [Nat.card_zpowers, Nat.card_zpowers, orderOf_Z, orderOf_Z']
  change Nat.card (((Subgroup.zpowers Z).prod (Subgroup.zpowers (Z' k))).map
    (blk (n₁ := Fin 2) (n₂ := Fin 2 ⊕ Fin k))) = 9
  rw [Subgroup.card_map_of_injective
      (blk_injective (n₁ := Fin 2) (n₂ := Fin 2 ⊕ Fin k)),
    Nat.card_congr (Subgroup.prodEquiv (Subgroup.zpowers Z)
      (Subgroup.zpowers (Z' k))).toEquiv, Nat.card_prod]
  exact hcard

private theorem T_block_isPGroup (k : ℕ) : IsPGroup 2 (T_block k) :=
  psi_range_isPGroup (n₁ := Fin 2) (n₂ := Fin 2 ⊕ Fin k)

private theorem T_block_ne_bot (k : ℕ) : T_block k ≠ ⊥ :=
  psi_range_ne_bot (0 : Fin 2) (Sum.inl (0 : Fin 2) : Fin 2 ⊕ Fin k)

private theorem E_block_le_normalizer (k : ℕ) :
    E_block k ≤ Subgroup.normalizer
      (T_block k : Set (SL (Fin 2 ⊕ (Fin 2 ⊕ Fin k)))) := by
  intro x hx
  change x ∈ ((Subgroup.zpowers Z).prod (Subgroup.zpowers (Z' k))).map
    (blk (n₁ := Fin 2) (n₂ := Fin 2 ⊕ Fin k)) at hx
  obtain ⟨y, -, rfl⟩ := Subgroup.mem_map.mp hx
  exact blk_range_le_normalizer (n₁ := Fin 2) (n₂ := Fin 2 ⊕ Fin k) ⟨y, rfl⟩

private theorem transport {G H : Type} [Group G] [Group H] (φ : G ≃* H)
    {E T : Subgroup H} (hE : IsElemAbelian 3 E) (hcard : Nat.card E = 9)
    (hT : T ≠ ⊥) (hP : IsPGroup 2 T)
    (hN : E ≤ Subgroup.normalizer (T : Set H)) :
    ∃ E' T' : Subgroup G, IsElemAbelian 3 E' ∧ Nat.card E' = 9 ∧ T' ≠ ⊥ ∧
      IsPGroup 2 T' ∧ E' ≤ Subgroup.normalizer (T' : Set G) := by
  refine ⟨E.map φ.symm.toMonoidHom, T.map φ.symm.toMonoidHom, ?_, ?_, ?_, ?_, ?_⟩
  · exact hE.map φ.symm.toMonoidHom
  · rw [Subgroup.card_map_of_injective φ.symm.injective, hcard]
  · intro h
    exact hT ((Subgroup.map_eq_bot_iff_of_injective T φ.symm.injective).mp h)
  · exact hP.map φ.symm.toMonoidHom
  · calc E.map φ.symm.toMonoidHom
        ≤ (Subgroup.normalizer (T : Set H)).map φ.symm.toMonoidHom :=
          Subgroup.map_mono (f := φ.symm.toMonoidHom) hN
      _ = Subgroup.normalizer (T.map φ.symm.toMonoidHom : Set G) :=
          Subgroup.map_equiv_normalizer_eq T φ.symm

private theorem exists_of_k (k : ℕ) {G : Type} [Group G]
    (φ : G ≃* SL (Fin 2 ⊕ (Fin 2 ⊕ Fin k))) :
    ∃ E T : Subgroup G, IsElemAbelian 3 E ∧ Nat.card E = 9 ∧ T ≠ ⊥ ∧
      IsPGroup 2 T ∧ E ≤ Subgroup.normalizer (T : Set G) :=
  transport φ (E_block_isElemAbelian k) (E_block_card k) (T_block_ne_bot k)
    (T_block_isPGroup k) (E_block_le_normalizer k)

theorem exists_elemAbelian_nine_normalizer {J : Type} [Group J] {m : ℕ} (hm : m = 4 ∨ m = 5)
    (hJ : StatedClassicalModel J .PSL m 2 1) :
    ∃ E T : Subgroup J, CFSG.Open.IsElemAbelian 3 E ∧ Nat.card E = 9 ∧ T ≠ ⊥ ∧
      IsPGroup 2 T ∧ E ≤ Subgroup.normalizer (T : Set J) := by
  obtain ⟨e⟩ := CFSG.Open.StatedAPI.nonempty_mulEquiv_specialLinear_zmod_two_of_psl hJ
  rcases hm with rfl | rfl
  · let eq : Fin 2 ⊕ (Fin 2 ⊕ Fin 0) ≃ Fin 4 :=
      Fintype.equivOfCardEq (by simp)
    exact exists_of_k 0 (e.trans (reindexSL eq.symm))
  · let eq : Fin 2 ⊕ (Fin 2 ⊕ Fin 1) ≃ Fin 5 :=
      Fintype.equivOfCardEq (by simp)
    exact exists_of_k 1 (e.trans (reindexSL eq.symm))

end CFSG.SLElemAbelianNine

end
