module

public import CFSG.RankThree.PartTwo.Sec21.Item233ComponentsLemma
public import CFSG.RankThree.PartTwo.Sec21.Item233TablesL44

public section

namespace CFSG.RankThree.PartTwo.Sec21

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.Assembly (IsElemAbelian)
open CFSG.Assembly.RankThreeEven (projSL projSU projSp)

section Model

open CFSG.RankThree.PartTwo.Sec21.TablesL44 CFSG.RankThree.PartTwo.KFacts.KS21.L44
  CFSG.RankThree.PartTwo.Sec21.Tables

theorem ext_ne {i j : Fin 4} (h : i ≠ j) : ∃ v : Fin 3 → ZMod 3, ext v i ≠ ext v j := by
  revert i j
  decide

theorem entry_rel (g : M) (w : (Fin 3 → ZMod 3) → (Fin 3 → ZMod 3))
    (hw : ∀ v, g * δ (Multiplicative.ofAdd v) * g⁻¹ = δ (Multiplicative.ofAdd (w v)))
    (v : Fin 3 → ZMod 3) (i j : Fin 4) :
    (g : Matrix (Fin 4) (Fin 4) F4) i j * eω (ext v j) =
      eω (ext (w v) i) * (g : Matrix (Fin 4) (Fin 4) F4) i j := by
  have h1 : g * δ (Multiplicative.ofAdd v) = δ (Multiplicative.ofAdd (w v)) * g := by
    rw [← hw v, inv_mul_cancel_right]
  have h2 := congrArg (fun x : M => (x : Matrix (Fin 4) (Fin 4) F4) i j) h1
  simp only [Matrix.SpecialLinearGroup.coe_mul, coe_δ, dg, Matrix.mul_diagonal,
    Matrix.diagonal_mul] at h2
  exact h2

theorem entry_ext (g : M) (w : (Fin 3 → ZMod 3) → (Fin 3 → ZMod 3))
    (hw : ∀ v, g * δ (Multiplicative.ofAdd v) * g⁻¹ = δ (Multiplicative.ofAdd (w v)))
    (v : Fin 3 → ZMod 3) (i j : Fin 4) (hg : (g : Matrix (Fin 4) (Fin 4) F4) i j ≠ 0) :
    ext v j = ext (w v) i := by
  have h := entry_rel g w hw v i j
  have h' : eω (ext v j) = eω (ext (w v) i) :=
    mul_left_cancel₀ hg (by rw [h, mul_comm])
  exact eω_injective h'

theorem w_bijective (g : M) (w : (Fin 3 → ZMod 3) → (Fin 3 → ZMod 3))
    (hw : ∀ v, g * δ (Multiplicative.ofAdd v) * g⁻¹ = δ (Multiplicative.ofAdd (w v))) :
    Function.Bijective w := by
  have hinj : Function.Injective w := by
    intro v v' h
    have h1 : g * δ (Multiplicative.ofAdd v) * g⁻¹ =
        g * δ (Multiplicative.ofAdd v') * g⁻¹ := by
      rw [hw v, hw v', h]
    have h2 := mul_left_cancel (mul_right_cancel h1)
    exact Multiplicative.ofAdd.injective (δ_injective h2)
  exact ⟨hinj, Finite.surjective_of_injective hinj⟩

theorem col_unique (g : M) (w : (Fin 3 → ZMod 3) → (Fin 3 → ZMod 3))
    (hw : ∀ v, g * δ (Multiplicative.ofAdd v) * g⁻¹ = δ (Multiplicative.ofAdd (w v)))
    (i i' j : Fin 4) (hi : (g : Matrix (Fin 4) (Fin 4) F4) i j ≠ 0)
    (hi' : (g : Matrix (Fin 4) (Fin 4) F4) i' j ≠ 0) : i = i' := by
  by_contra hne
  obtain ⟨u, hu⟩ := ext_ne hne
  obtain ⟨v, rfl⟩ := (w_bijective g w hw).2 u
  apply hu
  rw [← entry_ext g w hw v i j hi, ← entry_ext g w hw v i' j hi']

theorem monomial_of_normalizes (g : M)
    (hg : ∀ v : Fin 3 → ZMod 3, ∃ w : Fin 3 → ZMod 3,
      g * δ (Multiplicative.ofAdd v) * g⁻¹ = δ (Multiplicative.ofAdd w)) :
    ∃ σ : Equiv.Perm (Fin 4), ∀ v : Fin 3 → ZMod 3,
      g * δ (Multiplicative.ofAdd v) * g⁻¹ = reindexSL σ (δ (Multiplicative.ofAdd v)) := by
  choose w hw using hg
  have hrow : ∀ i : Fin 4, ∃ j, (g : Matrix (Fin 4) (Fin 4) F4) i j ≠ 0 := fun i => by
    by_contra h
    push_neg at h
    have hd := g.2
    rw [Matrix.det_eq_zero_of_row_eq_zero i h] at hd
    exact zero_ne_one hd
  choose f hf using hrow
  have finj : Function.Injective f := fun i i' h =>
    col_unique g w hw i i' (f i) (hf i) (h ▸ hf i')
  let σ : Equiv.Perm (Fin 4) := Equiv.ofBijective f (Finite.injective_iff_bijective.mp finj)
  refine ⟨σ, fun v => ?_⟩
  have hσ : ext (w v) = ext v ∘ σ := by
    funext i
    exact (entry_ext g w hw v i (f i) (hf i)).symm
  have hwv : w v = res (ext v ∘ σ) := by
    rw [← hσ, res_ext]
  rw [hw v, reindexSL_δ, hwv]

theorem reindexSL_mem_A0 (σ : Equiv.Perm (Fin 4)) {a : M} (ha : a ∈ A0) :
    reindexSL σ a ∈ A0 := by
  have h : reindexSL σ a ∈ A0.map (reindexSL σ).toMonoidHom :=
    Subgroup.mem_map_of_mem _ ha
  rwa [map_reindexSL_A0] at h

@[expose] noncomputable def permAut (σ : Equiv.Perm (Fin 4)) : MulAut A0 :=
  (MulEquiv.subgroupMap (reindexSL σ) A0).trans (MulEquiv.subgroupCongr (map_reindexSL_A0 σ))

theorem permAut_apply (σ : Equiv.Perm (Fin 4)) (a : A0) :
    ((permAut σ a : A0) : M) = reindexSL σ a := rfl

theorem reindexSL_reindexSL (σ τ : Equiv.Perm (Fin 4)) (g : M) :
    reindexSL σ (reindexSL τ g) = reindexSL (τ * σ) g := by
  apply Subtype.ext
  simp only [coe_reindexSL, Matrix.submatrix_submatrix, Equiv.Perm.coe_mul]

theorem reindexSL_one (g : M) : reindexSL (1 : Equiv.Perm (Fin 4)) g = g := by
  apply Subtype.ext
  simp only [coe_reindexSL, Equiv.Perm.coe_one, Matrix.submatrix_id_id]

theorem permAut_mul (σ τ : Equiv.Perm (Fin 4)) : permAut σ * permAut τ = permAut (τ * σ) := by
  apply MulEquiv.ext
  intro a
  apply Subtype.ext
  exact reindexSL_reindexSL σ τ a

theorem permAut_one : permAut (1 : Equiv.Perm (Fin 4)) = 1 := by
  apply MulEquiv.ext
  intro a
  apply Subtype.ext
  exact reindexSL_one a

theorem permAut_inv (σ : Equiv.Perm (Fin 4)) : (permAut σ)⁻¹ = permAut σ⁻¹ := by
  have h : permAut σ⁻¹ * permAut σ = 1 := by
    rw [permAut_mul, mul_inv_cancel, permAut_one]
  exact (eq_inv_of_mul_eq_one_left h).symm

theorem permAut_conj (σ τ : Equiv.Perm (Fin 4)) :
    permAut τ * permAut σ * (permAut τ)⁻¹ = permAut (τ⁻¹ * σ * τ) := by
  rw [permAut_inv, permAut_mul, permAut_mul, mul_assoc]

@[expose] noncomputable def permMat (σ : Equiv.Perm (Fin 4)) : Matrix (Fin 4) (Fin 4) F4 :=
  (1 : Matrix (Fin 4) (Fin 4) F4).submatrix σ id

theorem permMat_mul (σ : Equiv.Perm (Fin 4)) (g : Matrix (Fin 4) (Fin 4) F4) :
    permMat σ * g = g.submatrix σ σ * permMat σ := by
  ext i j
  simp [permMat, Matrix.mul_apply, Matrix.one_apply, Equiv.apply_eq_iff_eq_symm_apply]
  rw [Finset.sum_eq_single (σ i)]
  · simp
  · intro b _ hb
    rw [if_neg (fun h => hb ((Equiv.apply_eq_iff_eq_symm_apply σ).mpr h).symm)]
  · intro h
    exact absurd (Finset.mem_univ _) h

theorem permMat_det (σ : Equiv.Perm (Fin 4)) : (permMat σ).det = 1 := by
  rw [permMat, Matrix.det_permute, Matrix.det_one]
  rcases Int.units_eq_one_or σ.sign with h | h <;> simp [h, CharTwo.neg_eq]

@[expose] noncomputable def permSL (σ : Equiv.Perm (Fin 4)) : M := ⟨permMat σ, permMat_det σ⟩

theorem permSL_conj (σ : Equiv.Perm (Fin 4)) (g : M) :
    permSL σ * g * (permSL σ)⁻¹ = reindexSL σ g := by
  rw [mul_inv_eq_iff_eq_mul]
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, coe_reindexSL]
  exact permMat_mul σ _

theorem normalizerMonoidHom_coe_apply (x : Subgroup.normalizer (A0 : Set M)) (a : A0) :
    ((A0.normalizerMonoidHom x a : A0) : M) = (x : M) * (a : M) * (x : M)⁻¹ := rfl

theorem permSL_mem_normalizer (σ : Equiv.Perm (Fin 4)) :
    permSL σ ∈ Subgroup.normalizer (A0 : Set M) := by
  rw [Subgroup.mem_normalizer_iff]
  intro h
  rw [permSL_conj]
  constructor
  · exact reindexSL_mem_A0 σ
  · intro hh
    have hh' : reindexSL σ h ∈ A0.map (reindexSL σ).toMonoidHom := by
      rw [map_reindexSL_A0]
      exact hh
    obtain ⟨a, ha, hae⟩ := Subgroup.mem_map.mp hh'
    have : a = h := (reindexSL σ).injective hae
    rwa [this] at ha

theorem exists_permAut_of_mem_starOf {φ : MulAut A0} (hφ : φ ∈ starOf A0 (⊤ : Subgroup M)) :
    ∃ σ : Equiv.Perm (Fin 4), φ = permAut σ := by
  obtain ⟨x, -, rfl⟩ := Subgroup.mem_map.mp hφ
  have hg : ∀ v : Fin 3 → ZMod 3, ∃ w : Fin 3 → ZMod 3,
      (x : M) * δ (Multiplicative.ofAdd v) * (x : M)⁻¹ = δ (Multiplicative.ofAdd w) := by
    intro v
    have hmem : (x : M) * δ (Multiplicative.ofAdd v) * (x : M)⁻¹ ∈ δ.range :=
      (Subgroup.mem_normalizer_iff.mp x.2 _).mp (δ_mem_A0 v)
    obtain ⟨y, hy⟩ := hmem
    exact ⟨Multiplicative.toAdd y, by rw [ofAdd_toAdd, hy]⟩
  obtain ⟨σ, hσ⟩ := monomial_of_normalizes (x : M) hg
  refine ⟨σ, ?_⟩
  apply MulEquiv.ext
  intro a
  apply Subtype.ext
  obtain ⟨y, hy⟩ : (a : M) ∈ δ.range := a.2
  have hv : (a : M) = δ (Multiplicative.ofAdd (Multiplicative.toAdd y)) := by
    rw [ofAdd_toAdd, hy]
  rw [normalizerMonoidHom_coe_apply, permAut_apply, hv, hσ]

theorem permAut_mem_starOf (σ : Equiv.Perm (Fin 4)) :
    permAut σ ∈ starOf A0 (⊤ : Subgroup M) := by
  refine Subgroup.mem_map.mpr ⟨⟨permSL σ, permSL_mem_normalizer σ⟩,
    Subgroup.mem_subgroupOf.mpr (Subgroup.mem_top _), ?_⟩
  apply MulEquiv.ext
  intro a
  apply Subtype.ext
  rw [normalizerMonoidHom_coe_apply, permAut_apply]
  exact permSL_conj σ a

theorem comm_identity_aux {P : Type*} [Group P] (hP : ∀ x y : P, x * y = y * x) (x y p q : P) :
    y * x * (p * q) = x * p * (y * q) := by
  rw [hP y x, mul_assoc x y, mul_assoc x p, ← mul_assoc y p, hP y p, mul_assoc p y q]

@[expose] def commHomL44 {P : Type*} [Group P] (hP : ∀ x y : P, x * y = y * x) (φ : MulAut P) :
    P →* P where
  toFun a := a⁻¹ * φ a
  map_one' := by simp
  map_mul' a b := by
    simp only [mul_inv_rev, map_mul]
    exact comm_identity_aux hP _ _ _ _

theorem commHomL44_ker {P : Type*} [Group P] (hP : ∀ x y : P, x * y = y * x) (φ : MulAut P) :
    (commHomL44 hP φ).ker = fixedSubgroupOf φ := by
  ext x
  rw [MonoidHom.mem_ker, mem_fixedSubgroupOf]
  show x⁻¹ * φ x = 1 ↔ φ x = x
  rw [inv_mul_eq_one, eq_comm]

theorem commHomL44_range {P : Type*} [Group P] (hP : ∀ x y : P, x * y = y * x) (φ : MulAut P) :
    (commHomL44 hP φ).range = commOf φ := by
  apply le_antisymm
  · rintro _ ⟨a, rfl⟩
    exact mem_commOf φ a
  · unfold commOf
    rw [Subgroup.closure_le]
    rintro _ ⟨a, rfl⟩
    exact ⟨a, rfl⟩

theorem card_commOf_mul_card_fixed {P : Type*} [Group P] [Finite P]
    (hP : ∀ x y : P, x * y = y * x) (φ : MulAut P) :
    Nat.card (commOf φ) * Nat.card (fixedSubgroupOf φ) = Nat.card P := by
  rw [← commHomL44_range hP φ, ← commHomL44_ker hP φ, mul_comm]
  exact Subgroup.card_ker_mul_card_range (commHomL44 hP φ)

theorem A0_comm (x y : A0) : x * y = y * x := by
  obtain ⟨u, hu⟩ : (x : M) ∈ δ.range := x.2
  obtain ⟨w, hw⟩ : (y : M) ∈ δ.range := y.2
  apply Subtype.ext
  change (x : M) * (y : M) = (y : M) * (x : M)
  rw [← hu, ← hw, ← map_mul, ← map_mul, mul_comm]

theorem card_commOf_mul_fixed_A0 (φ : MulAut A0) :
    Nat.card (commOf φ) * Nat.card (fixedSubgroupOf φ) = 3 ^ 3 := by
  rw [← card_A0]
  exact card_commOf_mul_card_fixed A0_comm φ

theorem ext_sum (v : Fin 3 → ZMod 3) : ∑ i, ext v i = 0 := by
  rw [Fin.sum_univ_four]
  change v 0 + v 1 + v 2 + -(v 0 + v 1 + v 2) = 0
  exact add_neg_cancel _

theorem fixed_iff_ext (σ : Equiv.Perm (Fin 4)) (v : Fin 3 → ZMod 3) :
    reindexSL σ (δ (Multiplicative.ofAdd v)) = δ (Multiplicative.ofAdd v) ↔
      ext v ∘ σ = ext v := by
  rw [reindexSL_δ]
  have hs : ∑ i, (ext v ∘ σ) i = 0 := (Equiv.sum_comp σ (ext v)).trans (ext_sum v)
  constructor
  · intro h
    have h1 : res (ext v ∘ σ) = v := Multiplicative.ofAdd.injective (δ_injective h)
    calc ext v ∘ σ = ext (res (ext v ∘ σ)) := (ext_res hs).symm
      _ = ext v := by rw [h1]
  · intro h
    rw [h, res_ext]

theorem mem_fixed_permAut_iff (σ : Equiv.Perm (Fin 4)) (v : Fin 3 → ZMod 3) :
    (⟨δ (Multiplicative.ofAdd v), δ_mem_A0 v⟩ : A0) ∈ fixedSubgroupOf (permAut σ) ↔
      ext v ∘ σ = ext v := by
  rw [← fixed_iff_ext σ v, mem_fixedSubgroupOf, ← Subtype.coe_inj, permAut_apply]

theorem permAut_fixed_card (σ : Equiv.Perm (Fin 4)) :
    Nat.card (fixedSubgroupOf (permAut σ)) =
      (Finset.univ.filter fun v : Fin 3 → ZMod 3 => ext v ∘ σ = ext v).card := by
  rw [← Fintype.card_subtype, ← Nat.card_eq_fintype_card]
  symm
  refine Nat.card_eq_of_bijective
    (fun v => ⟨⟨δ (Multiplicative.ofAdd v.1), δ_mem_A0 _⟩, (mem_fixed_permAut_iff σ v.1).mpr v.2⟩)
    ⟨?_, ?_⟩
  · intro v w h
    have h' : δ (Multiplicative.ofAdd v.1) = δ (Multiplicative.ofAdd w.1) :=
      congrArg (fun x : fixedSubgroupOf (permAut σ) => ((x : A0) : M)) h
    exact Subtype.ext (Multiplicative.ofAdd.injective (δ_injective h'))
  · rintro ⟨⟨a, ha⟩, hfix⟩
    obtain ⟨y, rfl⟩ : a ∈ δ.range := ha
    have hv := (mem_fixed_permAut_iff σ (Multiplicative.toAdd y)).mp hfix
    exact ⟨⟨Multiplicative.toAdd y, hv⟩, rfl⟩

theorem fixcount_eq_nine_imp_swap :
    ∀ σ : Equiv.Perm (Fin 4),
      (Finset.univ.filter fun v : Fin 3 → ZMod 3 => ext v ∘ σ = ext v).card = 9 →
        ∃ a b : Fin 4, a ≠ b ∧ σ = Equiv.swap a b := by
  decide

theorem isReflectionOn_permAut_imp (σ : Equiv.Perm (Fin 4)) (h : IsReflectionOn (permAut σ)) :
    ∃ a b : Fin 4, a ≠ b ∧ σ = Equiv.swap a b := by
  apply fixcount_eq_nine_imp_swap σ
  have h1 := card_commOf_mul_fixed_A0 (permAut σ)
  rw [h.2, permAut_fixed_card] at h1
  omega

theorem swap_side_ne : ∀ i j a : Fin 4, i ≠ j → a ≠ Equiv.swap i a j := by
  decide

theorem exists_perm_map_pair {i j a b : Fin 4} (hij : i ≠ j) (hab : a ≠ b) :
    ∃ τ : Equiv.Perm (Fin 4), τ i = a ∧ τ j = b := by
  have hside : a ≠ Equiv.swap i a j := swap_side_ne i j a hij
  refine ⟨Equiv.swap (Equiv.swap i a j) b * Equiv.swap i a, ?_, ?_⟩
  · simp only [Equiv.Perm.mul_apply, Equiv.swap_apply_left]
    exact Equiv.swap_apply_of_ne_of_ne hside hab
  · simp only [Equiv.Perm.mul_apply]
    rw [Equiv.swap_apply_left]

theorem permAut_swap_ne_one {i j : Fin 4} (hij : i ≠ j) : permAut (Equiv.swap i j) ≠ 1 := by
  intro h
  obtain ⟨v, hv⟩ := ext_ne hij
  have key : (⟨δ (Multiplicative.ofAdd v), δ_mem_A0 v⟩ : A0) ∈
      fixedSubgroupOf (permAut (Equiv.swap i j)) := by
    rw [h, mem_fixedSubgroupOf]
    rfl
  rw [mem_fixed_permAut_iff] at key
  have h1 := congrFun key i
  simp only [Function.comp_apply, Equiv.swap_apply_left] at h1
  exact hv h1.symm

theorem permAut_swap_mem_D (D : Set (MulAut A0)) (hrefl : ∀ φ ∈ D, IsReflectionOn φ)
    (hconj : ∀ g ∈ starOf A0 (⊤ : Subgroup M), ∀ φ ∈ D, g * φ * g⁻¹ ∈ D)
    (hcl : Subgroup.closure D = starOf A0 (⊤ : Subgroup M)) {i j : Fin 4} (hij : i ≠ j) :
    permAut (Equiv.swap i j) ∈ D := by
  have hne : D.Nonempty := by
    by_contra hD
    rw [Set.not_nonempty_iff_eq_empty] at hD
    have h1 : permAut (Equiv.swap i j) ∈ starOf A0 (⊤ : Subgroup M) := permAut_mem_starOf _
    rw [← hcl, hD, Subgroup.closure_empty, Subgroup.mem_bot] at h1
    exact permAut_swap_ne_one hij h1
  obtain ⟨φ0, hφ0⟩ := hne
  have hφS : φ0 ∈ starOf A0 (⊤ : Subgroup M) := hcl ▸ Subgroup.subset_closure hφ0
  obtain ⟨σ, rfl⟩ := exists_permAut_of_mem_starOf hφS
  obtain ⟨a, b, hab, rfl⟩ := isReflectionOn_permAut_imp σ (hrefl _ hφ0)
  obtain ⟨τ, hτi, hτj⟩ := exists_perm_map_pair hij hab
  have hτswap : Equiv.swap a b = τ * Equiv.swap i j * τ⁻¹ := by
    rw [← hτi, ← hτj]
    exact Equiv.swap_apply_apply τ i j
  have hc : τ⁻¹ * Equiv.swap a b * τ = Equiv.swap i j := by
    rw [hτswap]
    simp [mul_assoc]
  have h := hconj (permAut τ) (permAut_mem_starOf τ) _ hφ0
  rw [permAut_conj, hc] at h
  exact h

theorem fibre_pair_decide : ∀ i j a b : Fin 4, i ≠ j →
    (∀ v : Fin 3 → ZMod 3, ext v i = ext v j → ext v a = ext v b) →
      a = b ∨ ((a = i ∨ a = j) ∧ (b = i ∨ b = j)) := by
  decide

theorem perfect_hom_trivial {P A : Type*} [Group P] [CommMonoid A]
    (hP : Group.IsPerfect P) (f : P →* A) (x : P) : f x = 1 := by
  have h1 : commutator P ≤ (f.toHomUnits).ker := Abelianization.commutator_subset_ker _
  rw [hP.commutator_eq_top] at h1
  have h2 := MonoidHom.mem_ker.mp (h1 (Subgroup.mem_top x))
  simpa using congrArg Units.val h2

theorem entry_comm_ext (g : M) (v : Fin 3 → ZMod 3)
    (hv : g * δ (Multiplicative.ofAdd v) = δ (Multiplicative.ofAdd v) * g) (a b : Fin 4)
    (hab : (g : Matrix (Fin 4) (Fin 4) F4) a b ≠ 0) : ext v b = ext v a := by
  have h2 := congrArg (fun x : M => (x : Matrix (Fin 4) (Fin 4) F4) a b) hv
  simp only [Matrix.SpecialLinearGroup.coe_mul, coe_δ, dg, Matrix.mul_diagonal,
    Matrix.diagonal_mul] at h2
  have h3 : (g : Matrix (Fin 4) (Fin 4) F4) a b * eω (ext v b) =
      (g : Matrix (Fin 4) (Fin 4) F4) a b * eω (ext v a) := by
    rw [h2, mul_comm]
  exact eω_injective (mul_left_cancel₀ hab h3)

theorem entry_T_support {i j : Fin 4} (hij : i ≠ j) (g : M)
    (hg : ∀ v : Fin 3 → ZMod 3, ext v i = ext v j →
      g * δ (Multiplicative.ofAdd v) = δ (Multiplicative.ofAdd v) * g)
    (a b : Fin 4) (hab : (g : Matrix (Fin 4) (Fin 4) F4) a b ≠ 0) :
    a = b ∨ ((a = i ∨ a = j) ∧ (b = i ∨ b = j)) :=
  fibre_pair_decide i j a b hij fun v hv => (entry_comm_ext g v (hg v hv) a b hab).symm

theorem diag_eq_one_of_perfect {P : Subgroup M} (hP : Group.IsPerfect P) (k : Fin 4)
    (hrow : ∀ g ∈ P, ∀ l, l ≠ k → (g : Matrix (Fin 4) (Fin 4) F4) k l = 0) :
    ∀ g ∈ P, (g : Matrix (Fin 4) (Fin 4) F4) k k = 1 := by
  let f : P →* F4 :=
    { toFun := fun g => (g : Matrix (Fin 4) (Fin 4) F4) k k
      map_one' := by simp
      map_mul' := fun g h => by
        simp only [Subgroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply]
        rw [Finset.sum_eq_single k]
        · intro l _ hl
          rw [hrow _ g.2 l hl, zero_mul]
        · simp }
  intro g hg
  exact perfect_hom_trivial hP f ⟨g, hg⟩

theorem isIdOutside_of_perfect {i j : Fin 4} (hij : i ≠ j) {P : Subgroup M}
    (hP : Group.IsPerfect P)
    (hPC : ∀ g ∈ P, ∀ v : Fin 3 → ZMod 3, ext v i = ext v j →
      g * δ (Multiplicative.ofAdd v) = δ (Multiplicative.ofAdd v) * g) :
    ∀ g ∈ P, IsIdOutside ({i, j} : Set (Fin 4)) (g : Matrix (Fin 4) (Fin 4) F4) := by
  have hrowT : ∀ g ∈ P, ∀ k l : Fin 4, k ≠ i → k ≠ j → l ≠ k →
      (g : Matrix (Fin 4) (Fin 4) F4) k l = 0 := by
    intro g hg k l hki hkj hl
    by_contra hc
    rcases entry_T_support hij g (hPC g hg) k l hc with h | ⟨h1, _⟩
    · exact hl h.symm
    · tauto
  have hdiag : ∀ k : Fin 4, k ≠ i → k ≠ j → ∀ g ∈ P,
      (g : Matrix (Fin 4) (Fin 4) F4) k k = 1 :=
    fun k hki hkj => diag_eq_one_of_perfect hP k (fun g hg l hl => hrowT g hg k l hki hkj hl)
  intro g hg a b hab
  by_cases hne : a = b
  · have hb : b ≠ i ∧ b ≠ j := by
      rw [hne] at hab
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or] at hab
      tauto
    rw [hne, Matrix.one_apply_eq]
    exact hdiag b hb.1 hb.2 g hg
  · rw [Matrix.one_apply_ne hne]
    by_contra hc
    rcases entry_T_support hij g (hPC g hg) a b hc with h | ⟨ha, hb⟩
    · exact hne h
    · simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or] at hab
      tauto

theorem mul_apply_of_row_one {n R : Type*} [Fintype n] [DecidableEq n] [Semiring R]
    (M N : Matrix n n R) (a b : n) (h : ∀ k, M a k = (1 : Matrix n n R) a k) :
    (M * N) a b = N a b := by
  rw [Matrix.mul_apply]
  simp only [h]
  have h1 := congrFun (congrFun (Matrix.one_mul N) a) b
  rw [Matrix.mul_apply] at h1
  exact h1

theorem mul_apply_of_col_one {n R : Type*} [Fintype n] [DecidableEq n] [Semiring R]
    (M N : Matrix n n R) (a b : n) (h : ∀ k, N k b = (1 : Matrix n n R) k b) :
    (M * N) a b = M a b := by
  rw [Matrix.mul_apply]
  simp only [h]
  have h1 := congrFun (congrFun (Matrix.mul_one M) a) b
  rw [Matrix.mul_apply] at h1
  exact h1

theorem isIdOutside_inv {c : Set (Fin 4)} (x : M)
    (hx : IsIdOutside c (x : Matrix (Fin 4) (Fin 4) F4)) :
    IsIdOutside c ((x⁻¹ : M) : Matrix (Fin 4) (Fin 4) F4) := by
  have hxy : (x : Matrix (Fin 4) (Fin 4) F4) * ((x⁻¹ : M) : Matrix (Fin 4) (Fin 4) F4) = 1 := by
    rw [← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel, Matrix.SpecialLinearGroup.coe_one]
  have hyx : ((x⁻¹ : M) : Matrix (Fin 4) (Fin 4) F4) * (x : Matrix (Fin 4) (Fin 4) F4) = 1 := by
    rw [← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel, Matrix.SpecialLinearGroup.coe_one]
  intro i j hij
  rcases hij with hi | hj
  · have hrow : ∀ k, (x : Matrix (Fin 4) (Fin 4) F4) i k = (1 : Matrix (Fin 4) (Fin 4) F4) i k :=
      fun k => hx i k (Or.inl hi)
    calc ((x⁻¹ : M) : Matrix (Fin 4) (Fin 4) F4) i j
        = ((x : Matrix (Fin 4) (Fin 4) F4) * ((x⁻¹ : M) : Matrix (Fin 4) (Fin 4) F4)) i j :=
          (mul_apply_of_row_one _ _ i j hrow).symm
      _ = (1 : Matrix (Fin 4) (Fin 4) F4) i j := by rw [hxy]
  · have hcol : ∀ k, (x : Matrix (Fin 4) (Fin 4) F4) k j = (1 : Matrix (Fin 4) (Fin 4) F4) k j :=
      fun k => hx k j (Or.inr hj)
    calc ((x⁻¹ : M) : Matrix (Fin 4) (Fin 4) F4) i j
        = (((x⁻¹ : M) : Matrix (Fin 4) (Fin 4) F4) * (x : Matrix (Fin 4) (Fin 4) F4)) i j :=
          (mul_apply_of_col_one _ _ i j hcol).symm
      _ = (1 : Matrix (Fin 4) (Fin 4) F4) i j := by rw [hyx]

@[expose] def blockSub (c : Set (Fin 4)) : Subgroup M where
  carrier := {x | IsIdOutside c (x : Matrix (Fin 4) (Fin 4) F4)}
  one_mem' := by
    show IsIdOutside c ((1 : M) : Matrix (Fin 4) (Fin 4) F4)
    rw [Matrix.SpecialLinearGroup.coe_one]
    intro i j _
    rfl
  mul_mem' := fun {x y} hx hy => by
    show IsIdOutside c ((x * y : M) : Matrix (Fin 4) (Fin 4) F4)
    rw [Matrix.SpecialLinearGroup.coe_mul]
    exact IsIdOutside.mul hx hy
  inv_mem' := fun {x} hx => by
    show IsIdOutside c ((x⁻¹ : M) : Matrix (Fin 4) (Fin 4) F4)
    exact isIdOutside_inv x hx

theorem mem_blockSub {c : Set (Fin 4)} {x : M} :
    x ∈ blockSub c ↔ IsIdOutside c (x : Matrix (Fin 4) (Fin 4) F4) := Iff.rfl

theorem blockSub_mono {c c' : Set (Fin 4)} (h : c ⊆ c') : blockSub c ≤ blockSub c' := by
  intro x hx
  rw [mem_blockSub] at hx ⊢
  intro i j hij
  apply hx i j
  rcases hij with hi | hj
  · exact Or.inl (fun hc => hi (h hc))
  · exact Or.inr (fun hc => hj (h hc))

theorem blockSub_le_cv (v : Fin 3 → ZMod 3) (κ : ZMod 3) :
    blockSub {i : Fin 4 | ext v i = κ} ≤
      Subgroup.centralizer ({δ (Multiplicative.ofAdd v)} : Set M) := by
  intro x hx
  exact mem_centralizer_of_isBlockDiag (IsIdOutside.isBlockDiag (mem_blockSub.mp hx))

theorem blockSub_01_eq : blockSub {i : Fin 4 | i = 0 ∨ i = 1} = ι01.range := by
  ext x
  rw [mem_blockSub, mem_range_ι01_iff]

theorem blockSub_012_eq : blockSub {i : Fin 4 | i ≠ 3} = ι012.range := by
  ext x
  rw [mem_blockSub, mem_range_ι012_iff]

theorem isQuasisimple_blockSub_01 : CFSG.IsQuasisimple (blockSub {i : Fin 4 | i = 0 ∨ i = 1}) := by
  rw [blockSub_01_eq]
  exact isQuasisimple_range_ι01

theorem isQuasisimple_blockSub_012 : CFSG.IsQuasisimple (blockSub {i : Fin 4 | i ≠ 3}) := by
  rw [blockSub_012_eq]
  exact isQuasisimple_range_ι012

theorem mem_blockSub_reindex (σ : Equiv.Perm (Fin 4)) (c : Set (Fin 4)) (x : M) :
    x ∈ blockSub c ↔ reindexSL σ x ∈ blockSub (σ ⁻¹' c) := by
  have hone : ∀ i j : Fin 4, (1 : Matrix (Fin 4) (Fin 4) F4) (σ i) (σ j) =
      (1 : Matrix (Fin 4) (Fin 4) F4) i j := by
    intro i j
    simp [Matrix.one_apply]
  rw [mem_blockSub, mem_blockSub]
  constructor
  · intro h i j hij
    have hij' : σ i ∉ c ∨ σ j ∉ c := by
      simpa only [Set.mem_preimage] using hij
    change (x : Matrix (Fin 4) (Fin 4) F4) (σ i) (σ j) = _
    rw [h (σ i) (σ j) hij', hone]
  · intro h a b hab
    have hc : σ.symm a ∉ σ ⁻¹' c ∨ σ.symm b ∉ σ ⁻¹' c := by
      simpa only [Set.mem_preimage, Equiv.apply_symm_apply] using hab
    have h1 := h (σ.symm a) (σ.symm b) hc
    change (x : Matrix (Fin 4) (Fin 4) F4) (σ (σ.symm a)) (σ (σ.symm b)) = _ at h1
    have h2 := hone (σ.symm a) (σ.symm b)
    rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply] at h1 h2
    rw [h1]
    exact h2.symm

theorem isQuasisimple_blockSub_perm (σ : Equiv.Perm (Fin 4)) {c : Set (Fin 4)}
    (h0 : CFSG.IsQuasisimple (blockSub c)) : CFSG.IsQuasisimple (blockSub (σ ⁻¹' c)) := by
  have hmap : (blockSub c).map (reindexSL σ).toMonoidHom = blockSub (σ ⁻¹' c) := by
    ext y
    rw [Subgroup.mem_map]
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact (mem_blockSub_reindex σ c x).mp hx
    · intro hy
      refine ⟨(reindexSL σ).symm y, ?_, by simp⟩
      rw [mem_blockSub_reindex σ c, MulEquiv.apply_symm_apply]
      exact hy
  exact CFSG.LocalCores.isQuasisimple_of_mulEquiv
    (((blockSub c).equivMapOfInjective (reindexSL σ).toMonoidHom (reindexSL σ).injective).trans
      (MulEquiv.subgroupCongr hmap)) h0

theorem isQuasisimple_blockSub_pair {a b : Fin 4} (hab : a ≠ b) :
    CFSG.IsQuasisimple (blockSub {i : Fin 4 | i = a ∨ i = b}) := by
  obtain ⟨τ, rfl, rfl⟩ := exists_perm_map_pair (i := 0) (j := 1) (a := a) (b := b) (by decide) hab
  have hset : τ.symm ⁻¹' {i : Fin 4 | i = 0 ∨ i = 1} = {i : Fin 4 | i = τ 0 ∨ i = τ 1} := by
    ext x
    simp only [Set.mem_preimage, Set.mem_setOf_eq, Equiv.symm_apply_eq]
  rw [← hset]
  exact isQuasisimple_blockSub_perm τ.symm isQuasisimple_blockSub_01

theorem isQuasisimple_blockSub_compl (d : Fin 4) :
    CFSG.IsQuasisimple (blockSub {i : Fin 4 | i ≠ d}) := by
  have hset : (Equiv.swap d 3) ⁻¹' {i : Fin 4 | i ≠ 3} = {i : Fin 4 | i ≠ d} := by
    ext x
    simp [Equiv.swap_apply_eq_iff]
  rw [← hset]
  exact isQuasisimple_blockSub_perm (Equiv.swap d 3) isQuasisimple_blockSub_012

theorem components_eq_range_of_finite {H : Type*} [Group H] [Finite H] {ι : Type*} [Finite ι]
    (Y : ι → Subgroup H) (hq : ∀ i, CFSG.IsQuasisimple (Y i)) (hn : ∀ i, (Y i).Normal)
    (hs : ∀ P : Subgroup H, Group.IsPerfect P → P ≤ ⨆ i, Y i) :
    {K : Subgroup H | CFSG.IsComponent K} = Set.range Y := by
  let e : ι ≃ Fin (Nat.card ι) := Finite.equivFin ι
  have key := components_eq_of_commuting_quasisimple (fun k : Fin (Nat.card ι) => Y (e.symm k))
    (fun k => hq _) (fun k => hn _)
    (fun P hP => (hs P hP).trans (Equiv.iSup_comp e.symm).ge)
  rw [key]
  exact Function.Surjective.range_comp e.symm.surjective Y

theorem eq_zero_of_ext_const (v : Fin 3 → ZMod 3) (κ : ZMod 3) (h : ∀ i, ext v i = κ) :
    v = 0 := by
  have h0 := h 0
  have h1 := h 1
  have h2 := h 2
  have h3 := h 3
  simp [ext] at h0 h1 h2 h3
  have hκ0 : ∀ x : ZMod 3, -(x + x + x) = x → x = 0 := by decide
  have hκ : κ = 0 := by
    apply hκ0 κ
    rw [h0, h1, h2] at h3
    exact h3
  funext i
  fin_cases i <;> simp [h0, h1, h2, hκ]

theorem finset_shape : ∀ F : Finset (Fin 4), 1 < F.card → F ≠ Finset.univ →
    (∃ a b : Fin 4, a ≠ b ∧ ∀ k, k ∈ F ↔ (k = a ∨ k = b)) ∨
      (∃ d : Fin 4, ∀ k, k ∈ F ↔ k ≠ d) := by
  decide

theorem isQuasisimple_blockSub_fibre {v : Fin 3 → ZMod 3} (hv : v ≠ 0) {κ : ZMod 3}
    (hbig : ∃ i j : Fin 4, i ≠ j ∧ ext v i = κ ∧ ext v j = κ) :
    CFSG.IsQuasisimple (blockSub {i : Fin 4 | ext v i = κ}) := by
  obtain ⟨i, j, hij, hi, hj⟩ := hbig
  set F : Finset (Fin 4) := Finset.univ.filter (fun k => ext v k = κ) with hFdef
  have hmem : ∀ k, k ∈ F ↔ ext v k = κ := fun k => by simp [hFdef]
  have hcard : 1 < F.card :=
    Finset.one_lt_card.mpr ⟨i, (hmem i).mpr hi, j, (hmem j).mpr hj, hij⟩
  have hne : F ≠ Finset.univ := by
    intro h
    apply hv
    apply eq_zero_of_ext_const v κ
    intro k
    have hk : k ∈ F := by
      rw [h]
      exact Finset.mem_univ k
    exact (hmem k).mp hk
  rcases finset_shape F hcard hne with ⟨a, b, hab, hF⟩ | ⟨d, hF⟩
  · have hS : {k : Fin 4 | ext v k = κ} = {k : Fin 4 | k = a ∨ k = b} := by
      ext k
      simp only [Set.mem_setOf_eq]
      rw [← hmem k, hF k]
    rw [hS]
    exact isQuasisimple_blockSub_pair hab
  · have hS : {k : Fin 4 | ext v k = κ} = {k : Fin 4 | k ≠ d} := by
      ext k
      simp only [Set.mem_setOf_eq]
      rw [← hmem k, hF k]
    rw [hS]
    exact isQuasisimple_blockSub_compl d

section BlockParts

@[expose] noncomputable def blkM (T : Set (Fin 4)) (A : Matrix (Fin 4) (Fin 4) F4) :
    Matrix (Fin 4) (Fin 4) F4 :=
  Matrix.of fun i j => by
    classical
    exact if i ∈ T then A i j else (1 : Matrix (Fin 4) (Fin 4) F4) i j

theorem blkM_apply_mem {T : Set (Fin 4)} {A : Matrix (Fin 4) (Fin 4) F4} {i : Fin 4} (h : i ∈ T)
    (j : Fin 4) : blkM T A i j = A i j := by
  simp [blkM, h]

theorem blkM_apply_not_mem {T : Set (Fin 4)} {A : Matrix (Fin 4) (Fin 4) F4} {i : Fin 4}
    (h : i ∉ T) (j : Fin 4) : blkM T A i j = (1 : Matrix (Fin 4) (Fin 4) F4) i j := by
  simp [blkM, h]

theorem blkM_univ (A : Matrix (Fin 4) (Fin 4) F4) : blkM Set.univ A = A := by
  ext i j
  exact blkM_apply_mem (Set.mem_univ i) j

theorem blkM_one (T : Set (Fin 4)) : blkM T (1 : Matrix (Fin 4) (Fin 4) F4) = 1 := by
  ext i j
  by_cases hi : i ∈ T
  · rw [blkM_apply_mem hi]
  · rw [blkM_apply_not_mem hi]

theorem blkM_eq_one_of_subsingleton {T : Set (Fin 4)} {A : Matrix (Fin 4) (Fin 4) F4}
    (hA : ∀ i k, i ∈ T → k ∉ T → A i k = 0) (hT : ∀ i ∈ T, ∀ j ∈ T, i = j)
    (hdiag : ∀ k ∈ T, A k k = 1) :
    blkM T A = 1 := by
  ext i j
  by_cases hi : i ∈ T
  · rw [blkM_apply_mem hi j]
    by_cases hj : j ∈ T
    · have hij : j = i := hT j hj i hi
      rw [hij, hdiag i hi, Matrix.one_apply_eq]
    · rw [hA i j hi hj, Matrix.one_apply_ne (fun (h : i = j) => hj (h ▸ hi))]
  · rw [blkM_apply_not_mem hi j]

end BlockParts

section Join

@[expose] def SatBlock (U : Set (Fin 4)) (A : Matrix (Fin 4) (Fin 4) F4) : Prop :=
  ∀ i k, i ∈ U → k ∉ U → A i k = 0

theorem satBlock_union {U W : Set (Fin 4)} {A : Matrix (Fin 4) (Fin 4) F4}
    (hU : SatBlock U A) (hW : SatBlock W A) : SatBlock (U ∪ W) A := by
  intro i k hi hk
  rcases (Set.mem_union _ _ _).mp hi with hi' | hi'
  · exact hU i k hi' (fun h => hk (Set.mem_union_left W h))
  · exact hW i k hi' (fun h => hk (Set.mem_union_right U h))

theorem satBlock_fibre {v : Fin 3 → ZMod 3} {A : Matrix (Fin 4) (Fin 4) F4}
    (hb : IsBlockDiag (ext v) A) (κ : ZMod 3) : SatBlock {i : Fin 4 | ext v i = κ} A := by
  intro i k hi hk
  apply hb i k
  intro h
  apply hk
  show ext v k = κ
  rw [← h]
  exact hi

theorem blkM_mul_of_sat {U : Set (Fin 4)} {A B : Matrix (Fin 4) (Fin 4) F4}
    (hA : SatBlock U A) : blkM U (A * B) = blkM U A * blkM U B := by
  ext i j
  by_cases hi : i ∈ U
  · rw [blkM_apply_mem hi, Matrix.mul_apply, Matrix.mul_apply]
    apply Finset.sum_congr rfl
    intro k _
    rw [blkM_apply_mem hi]
    by_cases hk : k ∈ U
    · rw [blkM_apply_mem hk]
    · rw [hA i k hi hk]
      simp
  · rw [blkM_apply_not_mem hi]
    simp [Matrix.mul_apply, Matrix.one_apply, blkM_apply_not_mem hi]

theorem isIdOutside_blkM {U : Set (Fin 4)} {A : Matrix (Fin 4) (Fin 4) F4} (hA : SatBlock U A) :
    IsIdOutside U (blkM U A) := by
  intro a b hab
  by_cases ha : a ∈ U
  · have hb : b ∉ U := by
      rcases hab with h | h
      · exact absurd ha h
      · exact h
    have hne : a ≠ b := fun h => hb (h ▸ ha)
    rw [blkM_apply_mem ha b, hA a b ha hb, Matrix.one_apply_ne hne]
  · rw [blkM_apply_not_mem ha b]

theorem blkM_mul_disjoint {U W : Set (Fin 4)} {A : Matrix (Fin 4) (Fin 4) F4}
    (hA : SatBlock U A) (hd : ∀ i, i ∈ U → i ∉ W) :
    blkM U A * blkM W A = blkM (U ∪ W) A := by
  ext i j
  rw [Matrix.mul_apply]
  by_cases hiU : i ∈ U
  · rw [blkM_apply_mem (Set.mem_union_left W hiU) j]
    calc ∑ k, blkM U A i k * blkM W A k j
        = ∑ k, A i k * (1 : Matrix (Fin 4) (Fin 4) F4) k j := by
          apply Finset.sum_congr rfl
          intro k _
          rw [blkM_apply_mem hiU]
          by_cases hkW : k ∈ W
          · rw [hA i k hiU (fun hkU => hd k hkU hkW)]
            simp
          · rw [blkM_apply_not_mem hkW]
      _ = A i j := by rw [← Matrix.mul_apply, Matrix.mul_one]
  · have hrow : ∑ k, blkM U A i k * blkM W A k j = ∑ k, (1 : Matrix (Fin 4) (Fin 4) F4) i k *
        blkM W A k j := by
      apply Finset.sum_congr rfl
      intro k _
      rw [blkM_apply_not_mem hiU]
    by_cases hiW : i ∈ W
    · rw [blkM_apply_mem (Set.mem_union_right U hiW) j, hrow, ← Matrix.mul_apply, Matrix.one_mul,
        blkM_apply_mem hiW j]
    · have hiUW : i ∉ U ∪ W := fun h => ((Set.mem_union _ _ _).mp h).elim hiU hiW
      rw [blkM_apply_not_mem hiUW j, hrow, ← Matrix.mul_apply, Matrix.one_mul,
        blkM_apply_not_mem hiW j]

theorem blkM_fibre_prod {v : Fin 3 → ZMod 3} {A : Matrix (Fin 4) (Fin 4) F4}
    (hb : IsBlockDiag (ext v) A) :
    blkM {i : Fin 4 | ext v i = 0} A * blkM {i : Fin 4 | ext v i = 1} A *
      blkM {i : Fin 4 | ext v i = 2} A = A := by
  have hd01 : ∀ i, i ∈ {i : Fin 4 | ext v i = 0} → i ∉ {i : Fin 4 | ext v i = 1} := by
    intro i h0 h1
    exact absurd ((show ext v i = 0 from h0).symm.trans (show ext v i = 1 from h1)) (by decide)
  have hd2 : ∀ i, i ∈ {i : Fin 4 | ext v i = 0} ∪ {i : Fin 4 | ext v i = 1} →
      i ∉ {i : Fin 4 | ext v i = 2} := by
    intro i h01 h2
    rcases (Set.mem_union _ _ _).mp h01 with h0 | h1
    · exact absurd ((show ext v i = 0 from h0).symm.trans (show ext v i = 2 from h2)) (by decide)
    · exact absurd ((show ext v i = 1 from h1).symm.trans (show ext v i = 2 from h2)) (by decide)
  have e1 := blkM_mul_disjoint (satBlock_fibre hb 0) hd01
  have e2 := blkM_mul_disjoint (satBlock_union (satBlock_fibre hb 0) (satBlock_fibre hb 1)) hd2
  have hU : ({i : Fin 4 | ext v i = 0} ∪ {i : Fin 4 | ext v i = 1}) ∪
      {i : Fin 4 | ext v i = 2} = Set.univ := by
    apply Set.eq_univ_of_forall
    intro i
    rcases (by decide : ∀ x : ZMod 3, x = 0 ∨ x = 1 ∨ x = 2) (ext v i) with h | h | h <;>
      simp [h]
  rw [e1, e2, hU, blkM_univ]

theorem det_blkM_fibre_eq_one {v : Fin 3 → ZMod 3} {Q : Type*} [Group Q]
    (hQ : Group.IsPerfect Q) (f : Q →* M)
    (hf : ∀ q, f q ∈ Subgroup.centralizer ({δ (Multiplicative.ofAdd v)} : Set M))
    (κ : ZMod 3) (q : Q) :
    Matrix.det (blkM {i : Fin 4 | ext v i = κ} ((f q : M) : Matrix (Fin 4) (Fin 4) F4)) = 1 := by
  let Fdet : Q →* F4 :=
    { toFun := fun x =>
        Matrix.det (blkM {i : Fin 4 | ext v i = κ} ((f x : M) : Matrix (Fin 4) (Fin 4) F4))
      map_one' := by
        simp only [map_one, Matrix.SpecialLinearGroup.coe_one, blkM_one, Matrix.det_one]
      map_mul' := fun x y => by
        simp only [map_mul, Matrix.SpecialLinearGroup.coe_mul]
        rw [blkM_mul_of_sat (satBlock_fibre (isBlockDiag_of_mem_centralizer (hf x)) κ),
          Matrix.det_mul] }
  exact perfect_hom_trivial hQ Fdet q

theorem mem_iSup_fibre_of_perfect {v : Fin 3 → ZMod 3} {Q : Type*} [Group Q]
    (hQ : Group.IsPerfect Q) (f : Q →* M)
    (hf : ∀ q, f q ∈ Subgroup.centralizer ({δ (Multiplicative.ofAdd v)} : Set M)) (q : Q)
    (κ : ZMod 3) (b : M)
    (hb : (b : Matrix (Fin 4) (Fin 4) F4) =
      blkM {i : Fin 4 | ext v i = κ} ((f q : M) : Matrix (Fin 4) (Fin 4) F4)) :
    b ∈ ⨆ κ' : {κ' : ZMod 3 // ∃ i j : Fin 4, i ≠ j ∧ ext v i = κ' ∧ ext v j = κ'},
      blockSub {i : Fin 4 | ext v i = κ'.1} := by
  haveI : Group.IsPerfect Q := hQ
  have hPr : Group.IsPerfect f.range := Group.IsPerfect.range f
  have hSat := satBlock_fibre (isBlockDiag_of_mem_centralizer (hf q)) κ
  by_cases hbig : ∃ i j : Fin 4, i ≠ j ∧ ext v i = κ ∧ ext v j = κ
  · refine Subgroup.mem_iSup_of_mem ⟨κ, hbig⟩ (mem_blockSub.mpr ?_)
    rw [hb]
    exact isIdOutside_blkM hSat
  · have hT : ∀ i ∈ {i : Fin 4 | ext v i = κ}, ∀ j ∈ {i : Fin 4 | ext v i = κ}, i = j := by
      intro i hi j hj
      by_contra hne
      exact hbig ⟨i, j, hne, hi, hj⟩
    have hrow : ∀ k : Fin 4, ext v k = κ → ∀ g ∈ f.range, ∀ l : Fin 4, l ≠ k →
        (g : Matrix (Fin 4) (Fin 4) F4) k l = 0 := by
      intro k hk g hg l hl
      obtain ⟨q', rfl⟩ := MonoidHom.mem_range.mp hg
      apply isBlockDiag_of_mem_centralizer (hf q') k l
      intro hkl
      exact hl (hT k hk l (hkl.symm.trans hk)).symm
    have hd : ∀ k ∈ {i : Fin 4 | ext v i = κ},
        ((f q : M) : Matrix (Fin 4) (Fin 4) F4) k k = 1 :=
      fun k hk => diag_eq_one_of_perfect hPr k (hrow k hk) (f q) (MonoidHom.mem_range.mpr ⟨q, rfl⟩)
    have hone : b = 1 := by
      apply Subtype.ext
      rw [Matrix.SpecialLinearGroup.coe_one, hb]
      exact blkM_eq_one_of_subsingleton hSat hT hd
    rw [hone]
    exact one_mem _

theorem mem_iSup_big_of_perfect {v : Fin 3 → ZMod 3} {Q : Type*} [Group Q]
    (hQ : Group.IsPerfect Q) (f : Q →* M)
    (hf : ∀ q, f q ∈ Subgroup.centralizer ({δ (Multiplicative.ofAdd v)} : Set M)) (q : Q) :
    f q ∈ ⨆ κ : {κ : ZMod 3 // ∃ i j : Fin 4, i ≠ j ∧ ext v i = κ ∧ ext v j = κ},
      blockSub {i : Fin 4 | ext v i = κ.1} := by
  have hsl : ∀ κ : ZMod 3, ∃ b : M, (b : Matrix (Fin 4) (Fin 4) F4) =
      blkM {i : Fin 4 | ext v i = κ} ((f q : M) : Matrix (Fin 4) (Fin 4) F4) :=
    fun κ => ⟨⟨_, det_blkM_fibre_eq_one hQ f hf κ q⟩, rfl⟩
  obtain ⟨b0, hb0⟩ := hsl 0
  obtain ⟨b1, hb1⟩ := hsl 1
  obtain ⟨b2, hb2⟩ := hsl 2
  have hprod : f q = b0 * b1 * b2 := by
    apply Subtype.ext
    rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, hb0, hb1, hb2]
    exact (blkM_fibre_prod (isBlockDiag_of_mem_centralizer (hf q))).symm
  rw [hprod]
  exact mul_mem (mul_mem (mem_iSup_fibre_of_perfect hQ f hf q 0 b0 hb0)
    (mem_iSup_fibre_of_perfect hQ f hf q 1 b1 hb1)) (mem_iSup_fibre_of_perfect hQ f hf q 2 b2 hb2)

theorem blk_iSup_map (v : Fin 3 → ZMod 3) :
    (⨆ κ : {κ : ZMod 3 // ∃ i j : Fin 4, i ≠ j ∧ ext v i = κ ∧ ext v j = κ},
      (blockSub {i : Fin 4 | ext v i = κ.1}).subgroupOf
        (Subgroup.centralizer ({δ (Multiplicative.ofAdd v)} : Set M))).map
      (Subgroup.centralizer ({δ (Multiplicative.ofAdd v)} : Set M)).subtype =
    ⨆ κ : {κ : ZMod 3 // ∃ i j : Fin 4, i ≠ j ∧ ext v i = κ ∧ ext v j = κ},
      blockSub {i : Fin 4 | ext v i = κ.1} := by
  rw [Subgroup.map_iSup]
  refine iSup_congr fun κ => ?_
  rw [Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr (blockSub_le_cv v κ.1)]

theorem perfect_le_iSup_sub {v : Fin 3 → ZMod 3}
    (P : Subgroup (Subgroup.centralizer ({δ (Multiplicative.ofAdd v)} : Set M)))
    (hP : Group.IsPerfect P) :
    P ≤ ⨆ κ : {κ : ZMod 3 // ∃ i j : Fin 4, i ≠ j ∧ ext v i = κ ∧ ext v j = κ},
      (blockSub {i : Fin 4 | ext v i = κ.1}).subgroupOf
        (Subgroup.centralizer ({δ (Multiplicative.ofAdd v)} : Set M)) := by
  intro g hg
  have hS := mem_iSup_big_of_perfect (Q := P) hP
    ((Subgroup.centralizer ({δ (Multiplicative.ofAdd v)} : Set M)).subtype.comp P.subtype)
    (fun x => x.1.2) ⟨g, hg⟩
  have hS' : (g : M) ∈ ⨆ κ : {κ : ZMod 3 // ∃ i j : Fin 4, i ≠ j ∧ ext v i = κ ∧ ext v j = κ},
      blockSub {i : Fin 4 | ext v i = κ.1} := hS
  rw [← blk_iSup_map v] at hS'
  obtain ⟨t, ht, htg⟩ := Subgroup.mem_map.mp hS'
  have htg' : t = g := by
    apply Subtype.ext
    exact htg
  rw [← htg']
  exact ht

theorem components_big {v : Fin 3 → ZMod 3} (hv : v ≠ 0) :
    {K : Subgroup (Subgroup.centralizer ({δ (Multiplicative.ofAdd v)} : Set M)) |
        CFSG.IsComponent K} =
      Set.range (fun κ : {κ : ZMod 3 // ∃ i j : Fin 4, i ≠ j ∧ ext v i = κ ∧ ext v j = κ} =>
        (blockSub {i : Fin 4 | ext v i = κ.1}).subgroupOf
          (Subgroup.centralizer ({δ (Multiplicative.ofAdd v)} : Set M))) :=
  components_eq_range_of_finite _
    (fun κ => CFSG.LocalCores.isQuasisimple_of_mulEquiv
      (Subgroup.subgroupOfEquivOfLe (blockSub_le_cv v κ.1)).symm
      (isQuasisimple_blockSub_fibre hv κ.2))
    (fun κ => (Subgroup.normal_subgroupOf_iff_le_normalizer (blockSub_le_cv v κ.1)).mpr
      (block_normal (v := v) (κ := κ.1) (S := blockSub {i : Fin 4 | ext v i = κ.1})
        (fun x => mem_blockSub)).2)
    (fun P hP => perfect_le_iSup_sub P hP)

end Join

end Model

section Transport

open CFSG.RankThree.PartTwo.Sec21.TablesL44 CFSG.RankThree.PartTwo.KFacts.KS21.L44
  CFSG.RankThree.PartTwo.Sec21.Tables

variable {G : Type} [Group G]

theorem exists_Phi {I A : Subgroup G} (hAI : A ≤ I) (hAe : IsElemAbelian 3 A)
    (e : I ≃* projSL 4 (GaloisField 2 2)) (hA : Nat.card A = 3 ^ 3) :
    ∃ Φ : I ≃* M, (A.subgroupOf I).map Φ.toMonoidHom = A0 := by
  set e' : I ≃* M := e.trans equivSL with he'
  have hA'e : IsElemAbelian 3 ((A.subgroupOf I).map e'.toMonoidHom) :=
    CFSG.RankThree.PartTwo.Sec21.isElemAbelian_map (isElemAbelian_subgroupOf hAe I) _
  have hcardA : Nat.card ((A.subgroupOf I).map e'.toMonoidHom) = 3 ^ 3 := by
    rw [Subgroup.card_map_of_injective e'.injective,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAI).toEquiv, hA]
  obtain ⟨x, hx⟩ := exists_map_conj_eq_A0 hA'e hcardA
  refine ⟨e'.trans (MulAut.conj x), ?_⟩
  rw [← hx, Subgroup.map_map]
  rfl

@[expose] noncomputable def thetaA {I A : Subgroup G} (hAI : A ≤ I) (Φ : I ≃* M)
    (hΦA : (A.subgroupOf I).map Φ.toMonoidHom = A0) : A ≃* A0 :=
  (Subgroup.subgroupOfEquivOfLe hAI).symm.trans
    ((MulEquiv.subgroupMap Φ (A.subgroupOf I)).trans (MulEquiv.subgroupCongr hΦA))

theorem coe_thetaA {I A : Subgroup G} (hAI : A ≤ I) (Φ : I ≃* M)
    (hΦA : (A.subgroupOf I).map Φ.toMonoidHom = A0) (c : A) :
    ((thetaA hAI Φ hΦA c : A0) : M) = Φ ⟨(c : G), hAI c.2⟩ := rfl

theorem mem_A_iff_Phi {I A : Subgroup G} (Φ : I ≃* M)
    (hΦA : (A.subgroupOf I).map Φ.toMonoidHom = A0) (h : I) :
    (h : G) ∈ A ↔ Φ h ∈ A0 :=
  Subgroup.mem_subgroupOf.symm.trans
    ((Subgroup.mem_map_iff_mem (f := Φ.toMonoidHom) Φ.injective).symm.trans
      (by rw [hΦA]; exact Iff.rfl))

theorem mem_normalizer_iff_Phi {I A : Subgroup G} (hAI : A ≤ I) (Φ : I ≃* M)
    (hΦA : (A.subgroupOf I).map Φ.toMonoidHom = A0) (y : I) :
    (y : G) ∈ Subgroup.normalizer (A : Set G) ↔ Φ y ∈ Subgroup.normalizer (A0 : Set M) := by
  have key := mem_A_iff_Phi Φ hΦA
  rw [Subgroup.mem_normalizer_iff, Subgroup.mem_normalizer_iff]
  constructor
  · intro hy m
    obtain ⟨h, rfl⟩ := Φ.surjective m
    have e1 : Φ y * Φ h * (Φ y)⁻¹ = Φ (y * h * y⁻¹) := by simp only [map_mul, map_inv]
    rw [e1]
    exact (key h).symm.trans ((hy (h : G)).trans (key (y * h * y⁻¹)))
  · intro hm g
    by_cases hg : g ∈ I
    · obtain ⟨h, rfl⟩ : ∃ h : I, (h : G) = g := ⟨⟨g, hg⟩, rfl⟩
      have e1 : Φ y * Φ h * (Φ y)⁻¹ = Φ (y * h * y⁻¹) := by simp only [map_mul, map_inv]
      have k2 : Φ h ∈ A0 ↔ Φ (y * h * y⁻¹) ∈ A0 := by
        rw [← e1]
        exact hm (Φ h)
      exact (key h).trans (k2.trans (key (y * h * y⁻¹)).symm)
    · have hgA : g ∉ A := fun hgA => hg (hAI hgA)
      have hyg : (y : G) * g * (y : G)⁻¹ ∉ I := by
        intro hI
        apply hg
        have e : (y : G)⁻¹ * ((y : G) * g * (y : G)⁻¹) * (y : G) = g := by group
        rw [← e]
        exact I.mul_mem (I.mul_mem (I.inv_mem y.2) hI) y.2
      exact ⟨fun h => absurd h hgA, fun h => absurd (hAI h) hyg⟩

theorem normalizerMonoidHom_coe_apply_G {A : Subgroup G} (n : Subgroup.normalizer (A : Set G))
    (c : A) : ((A.normalizerMonoidHom n c : A) : G) = (n : G) * (c : G) * (n : G)⁻¹ := rfl

theorem congr_normalizer {I A : Subgroup G} (hAI : A ≤ I) (Φ : I ≃* M)
    (hΦA : (A.subgroupOf I).map Φ.toMonoidHom = A0) (n : Subgroup.normalizer (A : Set G))
    (hn : (n : G) ∈ I) :
    MulAut.congr (thetaA hAI Φ hΦA) (A.normalizerMonoidHom n) =
      A0.normalizerMonoidHom ⟨Φ ⟨(n : G), hn⟩,
        (mem_normalizer_iff_Phi hAI Φ hΦA ⟨(n : G), hn⟩).mp n.2⟩ := by
  apply MulEquiv.ext
  intro a'
  apply Subtype.ext
  obtain ⟨c, rfl⟩ := (thetaA hAI Φ hΦA).surjective a'
  have hxy : (⟨((A.normalizerMonoidHom n c : A) : G), hAI (A.normalizerMonoidHom n c).2⟩ : I) =
      (⟨(n : G), hn⟩ : I) * ⟨(c : G), hAI c.2⟩ * (⟨(n : G), hn⟩ : I)⁻¹ :=
    Subtype.ext (normalizerMonoidHom_coe_apply_G n c)
  rw [MulAut.congr_apply, MulEquiv.trans_apply, MulEquiv.symm_apply_apply, MulEquiv.trans_apply,
    normalizerMonoidHom_coe_apply, coe_thetaA hAI Φ hΦA, coe_thetaA hAI Φ hΦA, hxy, map_mul,
    map_mul, map_inv]

theorem starOf_map_TA {I A : Subgroup G} (hAI : A ≤ I) (Φ : I ≃* M)
    (hΦA : (A.subgroupOf I).map Φ.toMonoidHom = A0) :
    (starOf A I).map (MulAut.congr (thetaA hAI Φ hΦA)).toMonoidHom =
      starOf A0 (⊤ : Subgroup M) := by
  ext φ
  constructor
  · intro hφ
    obtain ⟨ψ, hψ, rfl⟩ := Subgroup.mem_map.mp hφ
    obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp hψ
    rw [MulEquiv.coe_toMonoidHom, congr_normalizer hAI Φ hΦA x (Subgroup.mem_subgroupOf.mp hx)]
    exact Subgroup.mem_map.mpr ⟨_, Subgroup.mem_subgroupOf.mpr (Subgroup.mem_top _), rfl⟩
  · intro hφ
    obtain ⟨m, -, rfl⟩ := Subgroup.mem_map.mp hφ
    obtain ⟨y, hy⟩ : ∃ y : I, Φ y = (m : M) := ⟨Φ.symm (m : M), Φ.apply_symm_apply _⟩
    have hyN : (y : G) ∈ Subgroup.normalizer (A : Set G) :=
      (mem_normalizer_iff_Phi hAI Φ hΦA y).mpr (by rw [hy]; exact m.2)
    refine Subgroup.mem_map.mpr ⟨A.normalizerMonoidHom ⟨(y : G), hyN⟩, ?_, ?_⟩
    · exact Subgroup.mem_map.mpr ⟨⟨(y : G), hyN⟩, Subgroup.mem_subgroupOf.mpr y.2, rfl⟩
    · rw [MulEquiv.coe_toMonoidHom, congr_normalizer hAI Φ hΦA ⟨(y : G), hyN⟩ y.2]
      congr 1
      apply Subtype.ext
      exact hy

theorem commOf_congr_TA {P Q : Type*} [Group P] [Group Q] (e : P ≃* Q) (φ : MulAut P) :
    commOf (MulAut.congr e φ) = (commOf φ).map e.toMonoidHom := by
  rw [commOf, commOf, MonoidHom.map_closure]
  congr 1
  ext y
  simp only [Set.mem_range, Set.mem_image, MulAut.congr_apply, MulEquiv.trans_apply]
  constructor
  · rintro ⟨z, rfl⟩
    exact ⟨_, ⟨e.symm z, rfl⟩, by simp⟩
  · rintro ⟨_, ⟨x, rfl⟩, rfl⟩
    exact ⟨e x, by simp⟩

theorem isReflectionOn_congr {P Q : Type*} [Group P] [Group Q] (e : P ≃* Q) (φ : MulAut P)
    (h : IsReflectionOn φ) : IsReflectionOn (MulAut.congr e φ) := by
  obtain ⟨h1, h2⟩ := h
  refine ⟨?_, ?_⟩
  · exact (orderOf_injective (MulAut.congr e).toMonoidHom (MulAut.congr e).injective φ).trans h1
  · rw [commOf_congr_TA, Subgroup.card_map_of_injective e.injective]
    exact h2

theorem congr_thetaA_apply {I A : Subgroup G} (hAI : A ≤ I) (Φ : I ≃* M)
    (hΦA : (A.subgroupOf I).map Φ.toMonoidHom = A0) (φ : MulAut A) (a : A) :
    MulAut.congr (thetaA hAI Φ hΦA) φ (thetaA hAI Φ hΦA a) = thetaA hAI Φ hΦA (φ a) := by
  simp only [MulAut.congr_apply, MulEquiv.trans_apply, MulEquiv.symm_apply_apply]

@[expose] noncomputable def thetaC {I H : Subgroup G} (hHI : H ≤ I) (Φ : I ≃* M)
    {C : Subgroup M} (hΦH : (H.subgroupOf I).map Φ.toMonoidHom = C) : H ≃* C :=
  (Subgroup.subgroupOfEquivOfLe hHI).symm.trans
    ((MulEquiv.subgroupMap Φ (H.subgroupOf I)).trans (MulEquiv.subgroupCongr hΦH))

theorem coe_thetaC {I H : Subgroup G} (hHI : H ≤ I) (Φ : I ≃* M) {C : Subgroup M}
    (hΦH : (H.subgroupOf I).map Φ.toMonoidHom = C) (c : H) :
    ((thetaC hHI Φ hΦH c : C) : M) = Φ ⟨(c : G), hHI c.2⟩ := rfl

theorem mem_fixedInG_of {A : Subgroup G} {φ : MulAut A} {a : A} (h : φ a = a) :
    (a : G) ∈ fixedInG A φ :=
  Subgroup.mem_map.mpr ⟨a, by rw [mem_fixedSubgroupOf]; exact h, rfl⟩

theorem mem_centralizer_zpowers_iff {b x : G} :
    x ∈ Subgroup.centralizer ((Subgroup.zpowers b : Subgroup G) : Set G) ↔ b * x = x * b := by
  rw [Subgroup.mem_centralizer_iff]
  constructor
  · intro h
    exact h b (Subgroup.mem_zpowers b)
  · intro h h' hh'
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp (SetLike.mem_coe.mp hh')
    exact ((show Commute b x from h).zpow_left k).eq

theorem exists_gen_of_card_three [Finite G] {H : Subgroup G} (h : Nat.card H = 3) :
    ∃ b ∈ H, b ≠ 1 ∧ H = Subgroup.zpowers b := by
  have hne : ∃ x ∈ H, x ≠ 1 := by
    by_contra hc
    push_neg at hc
    have hbot : H = ⊥ := (Subgroup.eq_bot_iff_forall H).mpr hc
    rw [hbot, Subgroup.card_bot] at h
    exact absurd h (by norm_num)
  obtain ⟨x, hxH, hx1⟩ := hne
  have hzle : Subgroup.zpowers x ≤ H := Subgroup.zpowers_le.mpr hxH
  have hdvd : Nat.card (Subgroup.zpowers x) ∣ 3 := by
    rw [← h]
    exact Subgroup.card_dvd_of_le hzle
  rw [Nat.card_zpowers] at hdvd
  have h3 : orderOf x = 3 := by
    rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h1 | h1
    · exact absurd (orderOf_eq_one_iff.mp h1) hx1
    · exact h1
  refine ⟨x, hxH, hx1, ?_⟩
  have hcard : Nat.card H ≤ Nat.card (Subgroup.zpowers x) :=
    le_of_eq (by rw [Nat.card_zpowers, h3, h])
  exact (Subgroup.eq_of_le_of_card_ge hzle hcard).symm

theorem map_inf_centralizer_zpowers {I : Subgroup G} {K : Type*} [Group K] (Φ : I ≃* K)
    {b : G} (hb : b ∈ I) :
    ((I ⊓ Subgroup.centralizer ((Subgroup.zpowers b : Subgroup G) : Set G)).subgroupOf I).map
      Φ.toMonoidHom = Subgroup.centralizer ({Φ ⟨b, hb⟩} : Set K) := by
  ext y
  rw [Subgroup.mem_map, Subgroup.mem_centralizer_singleton_iff]
  constructor
  · rintro ⟨x, hx, rfl⟩
    have hx' := Subgroup.mem_subgroupOf.mp hx
    rw [Subgroup.mem_inf, mem_centralizer_zpowers_iff] at hx'
    rw [MulEquiv.coe_toMonoidHom, ← map_mul, ← map_mul]
    exact congrArg Φ (Subtype.ext hx'.2.symm)
  · intro hy
    obtain ⟨x, rfl⟩ := Φ.surjective y
    refine ⟨x, ?_, rfl⟩
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_inf, mem_centralizer_zpowers_iff]
    refine ⟨x.2, ?_⟩
    have h2 : Φ (⟨b, hb⟩ * x) = Φ (x * ⟨b, hb⟩) := by
      rw [map_mul, map_mul]
      exact hy.symm
    exact congrArg Subtype.val (Φ.injective h2)

theorem isPerfect_map_subgroupOf {I P : Subgroup G} (hPI : P ≤ I) (Φ : I ≃* M)
    (hP : Group.IsPerfect P) : Group.IsPerfect ((P.subgroupOf I).map Φ.toMonoidHom) := by
  haveI : Group.IsPerfect (P.subgroupOf I) :=
    Group.IsPerfect.ofSurjective (f := (Subgroup.subgroupOfEquivOfLe hPI).symm.toMonoidHom)
      (Subgroup.subgroupOfEquivOfLe hPI).symm.surjective
  exact Group.IsPerfect.map Φ.toMonoidHom

theorem exists_thetaA_eq {I A : Subgroup G} (hAI : A ≤ I) (Φ : I ≃* M)
    (hΦA : (A.subgroupOf I).map Φ.toMonoidHom = A0) (v : Fin 3 → ZMod 3) :
    ∃ a : A, ((thetaA hAI Φ hΦA a : A0) : M) = δ (Multiplicative.ofAdd v) :=
  ⟨(thetaA hAI Φ hΦA).symm ⟨δ (Multiplicative.ofAdd v), δ_mem_A0 v⟩,
    congrArg Subtype.val ((thetaA hAI Φ hΦA).apply_symm_apply _)⟩

theorem swap_fix_of_eq (w : Fin 3 → ZMod 3) {i j : Fin 4} (h : ext w i = ext w j) :
    ext w ∘ Equiv.swap i j = ext w := by
  funext t
  by_cases hi : t = i
  · subst hi
    simp [Equiv.swap_apply_left, h]
  · by_cases hj : t = j
    · subst hj
      simp [Equiv.swap_apply_right, h]
    · simp [Equiv.swap_apply_of_ne_of_ne hi hj]

theorem Phi_comm_iff {K : Type*} [Group K] {I : Subgroup G} (Φ : I ≃* K) (x y : I) :
    Φ x * Φ y = Φ y * Φ x ↔ x * y = y * x := by
  rw [← map_mul, ← map_mul, Φ.injective.eq_iff]

theorem fix_of_ext {I A : Subgroup G} (hAI : A ≤ I) (Φ : I ≃* M)
    (hΦA : (A.subgroupOf I).map Φ.toMonoidHom = A0) {ψ : MulAut A} {i j : Fin 4}
    (hψ : MulAut.congr (thetaA hAI Φ hΦA) ψ = permAut (Equiv.swap i j)) {v : Fin 3 → ZMod 3}
    (hv : ext v i = ext v j) {a : A}
    (ha : ((thetaA hAI Φ hΦA a : A0) : M) = δ (Multiplicative.ofAdd v)) :
    ψ a = a := by
  have hfix : (⟨δ (Multiplicative.ofAdd v), δ_mem_A0 v⟩ : A0) ∈
      fixedSubgroupOf (permAut (Equiv.swap i j)) :=
    (mem_fixed_permAut_iff _ v).mpr (swap_fix_of_eq v hv)
  rw [mem_fixedSubgroupOf] at hfix
  have hx : thetaA hAI Φ hΦA a = ⟨δ (Multiplicative.ofAdd v), δ_mem_A0 v⟩ := Subtype.ext ha
  apply (thetaA hAI Φ hΦA).injective
  rw [← congr_thetaA_apply hAI Φ hΦA ψ a, hψ, hx]
  exact hfix

theorem exists_swap_in_D {I A : Subgroup G} (hAI : A ≤ I) (Φ : I ≃* M)
    (hΦA : (A.subgroupOf I).map Φ.toMonoidHom = A0) (D : Set (MulAut A))
    (hrefl : ∀ φ ∈ D, IsReflectionOn φ)
    (hconj : ∀ g ∈ starOf A I, ∀ φ ∈ D, g * φ * g⁻¹ ∈ D)
    (hcl : Subgroup.closure D = starOf A I) {i j : Fin 4} (hij : i ≠ j) :
    ∃ ψ ∈ D, MulAut.congr (thetaA hAI Φ hΦA) ψ = permAut (Equiv.swap i j) := by
  have hrefl0 : ∀ φ ∈ (MulAut.congr (thetaA hAI Φ hΦA)) '' D, IsReflectionOn φ := by
    rintro _ ⟨φ, hφ, rfl⟩
    exact isReflectionOn_congr (thetaA hAI Φ hΦA) φ (hrefl φ hφ)
  have hconj0 : ∀ g ∈ starOf A0 (⊤ : Subgroup M), ∀ φ ∈ (MulAut.congr (thetaA hAI Φ hΦA)) '' D,
      g * φ * g⁻¹ ∈ (MulAut.congr (thetaA hAI Φ hΦA)) '' D := by
    intro g hg φ hφ
    obtain ⟨φ0, hφ0, rfl⟩ := hφ
    have hg' : g ∈ (starOf A I).map (MulAut.congr (thetaA hAI Φ hΦA)).toMonoidHom := by
      rw [starOf_map_TA hAI Φ hΦA]
      exact hg
    obtain ⟨g', hg'I, rfl⟩ := Subgroup.mem_map.mp hg'
    refine ⟨g' * φ0 * g'⁻¹, hconj g' hg'I φ0 hφ0, ?_⟩
    simp only [MulEquiv.coe_toMonoidHom, map_mul, map_inv]
  have hcl0 : Subgroup.closure ((MulAut.congr (thetaA hAI Φ hΦA)) '' D) =
      starOf A0 (⊤ : Subgroup M) := by
    have h1 : Subgroup.closure ((MulAut.congr (thetaA hAI Φ hΦA)) '' D) =
        (Subgroup.closure D).map (MulAut.congr (thetaA hAI Φ hΦA)).toMonoidHom := by
      rw [MonoidHom.map_closure, MulEquiv.coe_toMonoidHom]
    rw [h1, hcl, starOf_map_TA hAI Φ hΦA]
  obtain ⟨ψ, hψD, hψ⟩ := permAut_swap_mem_D _ hrefl0 hconj0 hcl0 hij
  exact ⟨ψ, hψD, hψ⟩

theorem exists_v_of_thetaA {I A : Subgroup G} (hAI : A ≤ I) (Φ : I ≃* M)
    (hΦA : (A.subgroupOf I).map Φ.toMonoidHom = A0) (a : A) :
    ∃ v : Fin 3 → ZMod 3, ((thetaA hAI Φ hΦA a : A0) : M) = δ (Multiplicative.ofAdd v) := by
  obtain ⟨y, hy⟩ := MonoidHom.mem_range.mp (thetaA hAI Φ hΦA a).2
  exact ⟨Multiplicative.toAdd y, hy.symm⟩

theorem ne_zero_of_thetaA {I A : Subgroup G} (hAI : A ≤ I) (Φ : I ≃* M)
    (hΦA : (A.subgroupOf I).map Φ.toMonoidHom = A0) {a : A} (ha : a ≠ 1)
    {v : Fin 3 → ZMod 3} (hv : ((thetaA hAI Φ hΦA a : A0) : M) = δ (Multiplicative.ofAdd v)) :
    v ≠ 0 := by
  rintro rfl
  apply ha
  apply (thetaA hAI Φ hΦA).injective
  rw [map_one]
  apply Subtype.ext
  simp [hv]

theorem commute_delta_of_fixed {I A : Subgroup G} (hAI : A ≤ I) (Φ : I ≃* M)
    (hΦA : (A.subgroupOf I).map Φ.toMonoidHom = A0) {ψ : MulAut A} {i j : Fin 4}
    (hψ : MulAut.congr (thetaA hAI Φ hΦA) ψ = permAut (Equiv.swap i j))
    {P : Subgroup G} (hPC : P ≤ Subgroup.centralizer (fixedInG A ψ : Set G))
    {x : I} (hx : (x : G) ∈ P) {v : Fin 3 → ZMod 3} (hv : ext v i = ext v j) :
    Φ x * δ (Multiplicative.ofAdd v) = δ (Multiplicative.ofAdd v) * Φ x := by
  obtain ⟨a, ha⟩ := exists_thetaA_eq hAI Φ hΦA v
  have hfix : ψ a = a := fix_of_ext hAI Φ hΦA hψ hv ha
  have hcomm : (a : G) * (x : G) = (x : G) * (a : G) :=
    Subgroup.mem_centralizer_iff.mp (hPC hx) (a : G) (mem_fixedInG_of hfix)
  have hcomm' : (⟨(a : G), hAI a.2⟩ : I) * x = x * ⟨(a : G), hAI a.2⟩ := Subtype.ext hcomm
  have hΦa : Φ ⟨(a : G), hAI a.2⟩ = δ (Multiplicative.ofAdd v) :=
    (coe_thetaA hAI Φ hΦA a).symm.trans ha
  have h := (Phi_comm_iff Φ _ x).mpr hcomm'
  rw [hΦa] at h
  exact h.symm

theorem exists_pair_of_component {w : Fin 3 → ZMod 3} (hw : w ≠ 0)
    {Y : Subgroup (Subgroup.centralizer ({δ (Multiplicative.ofAdd w)} : Set M))}
    (hY : CFSG.IsComponent Y) :
    ∃ i j : Fin 4, i ≠ j ∧ ext w i = ext w j ∧
      ∀ z : Subgroup.centralizer ({δ (Multiplicative.ofAdd w)} : Set M),
        z ∈ Y ↔ (z : M) ∈ blockSub {k : Fin 4 | ext w k = ext w i} := by
  have hmem : Y ∈ {K : Subgroup (Subgroup.centralizer ({δ (Multiplicative.ofAdd w)} : Set M)) |
      CFSG.IsComponent K} := hY
  rw [components_big hw] at hmem
  obtain ⟨κ, hκ⟩ := hmem
  obtain ⟨i, j, hij, hi, hj⟩ := κ.2
  subst hκ
  refine ⟨i, j, hij, hi.trans hj.symm, fun z => ?_⟩
  simp only [Subgroup.mem_subgroupOf]
  rw [hi]

theorem subgroupOf_le_of_perfect {I A : Subgroup G} (hAI : A ≤ I) (Φ : I ≃* M)
    (hΦA : (A.subgroupOf I).map Φ.toMonoidHom = A0) {ψ : MulAut A} {i j : Fin 4}
    (hψ : MulAut.congr (thetaA hAI Φ hΦA) ψ = permAut (Equiv.swap i j)) (hij : i ≠ j)
    {v : Fin 3 → ZMod 3} (hfib : ext v i = ext v j)
    {H : Subgroup G} (hHI : H ≤ I) {C : Subgroup M}
    (hΦH : (H.subgroupOf I).map Φ.toMonoidHom = C) {X : Subgroup H}
    (hmemY : ∀ z : C, z ∈ X.map (thetaC hHI Φ hΦH).toMonoidHom ↔
      (z : M) ∈ blockSub {k : Fin 4 | ext v k = ext v i})
    {P : Subgroup G} (hPI : P ≤ I)
    (hPC : P ≤ Subgroup.centralizer (fixedInG A ψ : Set G)) (hPperf : Group.IsPerfect P) :
    P.subgroupOf H ≤ X := by
  intro y hy
  have hyP : (y : G) ∈ P := Subgroup.mem_subgroupOf.mp hy
  have hyI : (y : G) ∈ I := hHI y.2
  have hmem : Φ ⟨(y : G), hyI⟩ ∈ (P.subgroupOf I).map Φ.toMonoidHom :=
    Subgroup.mem_map.mpr ⟨⟨(y : G), hyI⟩, Subgroup.mem_subgroupOf.mpr hyP, rfl⟩
  have hQ := isPerfect_map_subgroupOf hPI Φ hPperf
  have hcomm : ∀ g ∈ (P.subgroupOf I).map Φ.toMonoidHom, ∀ u : Fin 3 → ZMod 3,
      ext u i = ext u j → g * δ (Multiplicative.ofAdd u) = δ (Multiplicative.ofAdd u) * g := by
    intro g hg u hu
    obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp hg
    exact commute_delta_of_fixed hAI Φ hΦA hψ hPC (Subgroup.mem_subgroupOf.mp hx) hu
  have hout := isIdOutside_of_perfect hij hQ hcomm
  have hpair : ({i, j} : Set (Fin 4)) ⊆ {k : Fin 4 | ext v k = ext v i} :=
    Set.insert_subset_iff.mpr ⟨rfl, Set.singleton_subset_iff.mpr hfib.symm⟩
  have hblk : Φ ⟨(y : G), hyI⟩ ∈ blockSub {k : Fin 4 | ext v k = ext v i} :=
    blockSub_mono hpair (mem_blockSub.mpr (hout _ hmem))
  have hmY : thetaC hHI Φ hΦH y ∈ X.map (thetaC hHI Φ hΦH).toMonoidHom :=
    (hmemY (thetaC hHI Φ hΦH y)).mpr (by rw [coe_thetaC]; exact hblk)
  obtain ⟨z, hz, hzy⟩ := Subgroup.mem_map.mp hmY
  have hzy' : thetaC hHI Φ hΦH z = thetaC hHI Φ hΦH y := hzy
  rw [(thetaC hHI Φ hΦH).injective hzy'] at hz
  exact hz

theorem le_map_subtype_of_subgroupOf_le {H P : Subgroup G} {X : Subgroup H} (hPH : P ≤ H)
    (hsub : P.subgroupOf H ≤ X) : P ≤ X.map H.subtype := by
  intro x hx
  exact Subgroup.mem_map.mpr ⟨⟨x, hPH hx⟩, hsub (Subgroup.mem_subgroupOf.mpr hx), rfl⟩

theorem terminalRootComponentsL44 :
    ∀ (G : Type) [Group G] [Finite G] (I A : Subgroup G), A ≤ I → IsElemAbelian 3 A →
      (Nonempty (I ≃* projSL 4 (GaloisField 2 2)) ∧ Nat.card A = 3 ^ 3) →
      ∀ D : Set (MulAut A), (∀ φ ∈ D, IsReflectionOn φ) →
        (∀ g ∈ starOf A I, ∀ φ ∈ D, g * φ * g⁻¹ ∈ D) → Subgroup.closure D = starOf A I →
        ∀ B : Subgroup G, B ≤ A → Nat.card B = 3 →
          ∀ X : Subgroup (I ⊓ Subgroup.centralizer (B : Set G) : Subgroup G),
            CFSG.IsComponent X → ∃ φ ∈ D, ∀ P : Subgroup G, P ≤ I →
              P ≤ Subgroup.centralizer (fixedInG A φ : Set G) → Group.IsPerfect P →
                P ≤ X.map (I ⊓ Subgroup.centralizer (B : Set G)).subtype := by
  intro G _ _ I A hAI hAe hT D hrefl hconj hcl B hBA hB3 X hX
  obtain ⟨⟨e⟩, hA⟩ := hT
  obtain ⟨Φ, hΦA⟩ := exists_Phi hAI hAe e hA
  obtain ⟨b, -, hb1, rfl⟩ := exists_gen_of_card_three hB3
  have hbA : b ∈ A := hBA (Subgroup.mem_zpowers b)
  have hbI : b ∈ I := hAI hbA
  have ha1 : (⟨b, hbA⟩ : A) ≠ 1 := fun h => hb1 (congrArg Subtype.val h)
  obtain ⟨v, hv⟩ := exists_v_of_thetaA hAI Φ hΦA ⟨b, hbA⟩
  have hv0 : v ≠ 0 := ne_zero_of_thetaA hAI Φ hΦA ha1 hv
  have hΦb : Φ ⟨b, hbI⟩ = δ (Multiplicative.ofAdd v) :=
    (coe_thetaA hAI Φ hΦA ⟨b, hbA⟩).symm.trans hv
  have hHI : I ⊓ Subgroup.centralizer ((Subgroup.zpowers b : Subgroup G) : Set G) ≤ I :=
    inf_le_left
  have hΦH : ((I ⊓ Subgroup.centralizer ((Subgroup.zpowers b : Subgroup G) : Set G)).subgroupOf I).map
      Φ.toMonoidHom = Subgroup.centralizer ({δ (Multiplicative.ofAdd v)} : Set M) := by
    rw [map_inf_centralizer_zpowers Φ hbI, hΦb]
  have hY := CFSG.LocalCores.isComponent_map_mulEquiv (thetaC hHI Φ hΦH) hX
  obtain ⟨i, j, hij, hfib, hmemY⟩ := exists_pair_of_component hv0 hY
  obtain ⟨ψ, hψD, hψ⟩ := exists_swap_in_D hAI Φ hΦA D hrefl hconj hcl hij
  have hbfix : ψ ⟨b, hbA⟩ = ⟨b, hbA⟩ := fix_of_ext hAI Φ hΦA hψ hfib hv
  have hbC : b ∈ fixedInG A ψ := mem_fixedInG_of hbfix
  have hPB : ∀ P : Subgroup G, P ≤ Subgroup.centralizer (fixedInG A ψ : Set G) →
      P ≤ Subgroup.centralizer ((Subgroup.zpowers b : Subgroup G) : Set G) := by
    intro P hPC x hx
    exact mem_centralizer_zpowers_iff.mpr (Subgroup.mem_centralizer_iff.mp (hPC hx) b hbC)
  refine ⟨ψ, hψD, fun P hPI hPC hPperf => le_map_subtype_of_subgroupOf_le (le_inf hPI (hPB P hPC))
    (subgroupOf_le_of_perfect hAI Φ hΦA hψ hij hfib hHI hΦH hmemY hPI hPC hPperf)⟩

end Transport

end CFSG.RankThree.PartTwo.Sec21

end
