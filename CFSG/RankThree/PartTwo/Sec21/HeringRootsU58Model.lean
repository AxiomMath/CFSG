module

public import CFSG.RankThree.PartTwo.Sec21.Item233TablesU58
public import CFSG.RankThree.PartTwo.Sec21.Item233RootsL44

public section

namespace CFSG.RankThree.PartTwo.Sec21.RootsU58

open Matrix CFSG.RankThree.PartTwo.KFacts.KS21 CFSG.RankThree.PartTwo.KFacts.KS21.U58
open CFSG.RankThree.PartTwo.Sec21.TablesU58 CFSG.RankThree.PartTwo.Sec21.Tables
open CFSG.Assembly (IsElemAbelian)
open CFSG.Assembly.LowTwoRank

@[expose] noncomputable def eω (a : ZMod 3) : K := eζ (ι3 a)

theorem eω_injective : Function.Injective eω := eζ_injective.comp ι3_injective

theorem mU_δ (v : Fin 4 → ZMod 3) :
    mU (δ (Multiplicative.ofAdd v)) = diagonal fun i => eω (ext3 v i) := by
  have h : mU (δ (Multiplicative.ofAdd v)) = dgU (ext9 (ι3v v)) := rfl
  rw [h, ext9_ι3v]
  rfl

theorem ext_ne : ∀ i j : Fin 5, i ≠ j → ∃ v : Fin 4 → ZMod 3, ext3 v i ≠ ext3 v j := by
  decide

theorem entry_rel (g : SUI) (w : (Fin 4 → ZMod 3) → (Fin 4 → ZMod 3))
    (hw : ∀ v, g * δ (Multiplicative.ofAdd v) * g⁻¹ = δ (Multiplicative.ofAdd (w v)))
    (v : Fin 4 → ZMod 3) (i j : Fin 5) :
    mU g i j * eω (ext3 v j) = eω (ext3 (w v) i) * mU g i j := by
  have h1 : g * δ (Multiplicative.ofAdd v) = δ (Multiplicative.ofAdd (w v)) * g := by
    rw [← hw v, inv_mul_cancel_right]
  have h2 := congrArg (fun x : SUI => mU x i j) h1
  simp only [mU_mul, mU_δ, Matrix.mul_diagonal, Matrix.diagonal_mul] at h2
  exact h2

theorem entry_ext (g : SUI) (w : (Fin 4 → ZMod 3) → (Fin 4 → ZMod 3))
    (hw : ∀ v, g * δ (Multiplicative.ofAdd v) * g⁻¹ = δ (Multiplicative.ofAdd (w v)))
    (v : Fin 4 → ZMod 3) (i j : Fin 5) (hg : mU g i j ≠ 0) :
    ext3 v j = ext3 (w v) i := by
  have h := entry_rel g w hw v i j
  have h' : eω (ext3 v j) = eω (ext3 (w v) i) :=
    mul_left_cancel₀ hg (by rw [h, mul_comm])
  exact eω_injective h'

theorem w_bijective (g : SUI) (w : (Fin 4 → ZMod 3) → (Fin 4 → ZMod 3))
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

theorem col_unique (g : SUI) (w : (Fin 4 → ZMod 3) → (Fin 4 → ZMod 3))
    (hw : ∀ v, g * δ (Multiplicative.ofAdd v) * g⁻¹ = δ (Multiplicative.ofAdd (w v)))
    (i i' j : Fin 5) (hi : mU g i j ≠ 0) (hi' : mU g i' j ≠ 0) : i = i' := by
  by_contra hne
  obtain ⟨u, hu⟩ := ext_ne i i' hne
  obtain ⟨v, rfl⟩ := (w_bijective g w hw).2 u
  apply hu
  rw [← entry_ext g w hw v i j hi, ← entry_ext g w hw v i' j hi']

theorem monomial_of_normalizes (g : SUI)
    (hg : ∀ v : Fin 4 → ZMod 3, ∃ w : Fin 4 → ZMod 3,
      g * δ (Multiplicative.ofAdd v) * g⁻¹ = δ (Multiplicative.ofAdd w)) :
    ∃ σ : Equiv.Perm (Fin 5), ∀ v : Fin 4 → ZMod 3,
      g * δ (Multiplicative.ofAdd v) * g⁻¹ = reindexSU σ (δ (Multiplicative.ofAdd v)) := by
  choose w hw using hg
  have hdet : (mU g).det = 1 := ((mem_SUI_iff _).mp g.2).1
  have hrow : ∀ i : Fin 5, ∃ j, mU g i j ≠ 0 := fun i => by
    by_contra h
    push Not at h
    rw [Matrix.det_eq_zero_of_row_eq_zero i h] at hdet
    exact zero_ne_one hdet
  choose f hf using hrow
  have finj : Function.Injective f := fun i i' h =>
    col_unique g w hw i i' (f i) (hf i) (h ▸ hf i')
  let σ : Equiv.Perm (Fin 5) := Equiv.ofBijective f (Finite.injective_iff_bijective.mp finj)
  refine ⟨σ, fun v => ?_⟩
  have hσ : ext3 (w v) = ext3 v ∘ σ := by
    funext i
    exact (entry_ext g w hw v i (f i) (hf i)).symm
  have hwv : w v = res3 (ext3 v ∘ σ) := by
    rw [← hσ, res3_ext3]
  rw [hw v, reindexSU_δ, hwv]

theorem reindexSU_mem_A0 (σ : Equiv.Perm (Fin 5)) {a : SUI} (ha : a ∈ A0) :
    reindexSU σ a ∈ A0 := by
  have h : reindexSU σ a ∈ A0.map (reindexSU σ).toMonoidHom :=
    Subgroup.mem_map_of_mem _ ha
  rwa [map_reindexSU_A0] at h

@[expose] noncomputable def permAut (σ : Equiv.Perm (Fin 5)) : MulAut A0 :=
  (MulEquiv.subgroupMap (reindexSU σ) A0).trans (MulEquiv.subgroupCongr (map_reindexSU_A0 σ))

theorem permAut_apply (σ : Equiv.Perm (Fin 5)) (a : A0) :
    ((permAut σ a : A0) : SUI) = reindexSU σ a := rfl

theorem reindexSU_reindexSU (σ τ : Equiv.Perm (Fin 5)) (g : SUI) :
    reindexSU σ (reindexSU τ g) = reindexSU (τ * σ) g := by
  apply mU_injective
  simp only [mU_reindexSU, Matrix.submatrix_submatrix, Equiv.Perm.coe_mul]

theorem reindexSU_one (g : SUI) : reindexSU (1 : Equiv.Perm (Fin 5)) g = g := by
  apply mU_injective
  simp only [mU_reindexSU, Equiv.Perm.coe_one, Matrix.submatrix_id_id]

theorem permAut_mul (σ τ : Equiv.Perm (Fin 5)) : permAut σ * permAut τ = permAut (τ * σ) := by
  apply MulEquiv.ext
  intro a
  apply Subtype.ext
  exact reindexSU_reindexSU σ τ a

theorem permAut_one : permAut (1 : Equiv.Perm (Fin 5)) = 1 := by
  apply MulEquiv.ext
  intro a
  apply Subtype.ext
  exact reindexSU_one a

theorem permAut_inv (σ : Equiv.Perm (Fin 5)) : (permAut σ)⁻¹ = permAut σ⁻¹ := by
  have h : permAut σ⁻¹ * permAut σ = 1 := by
    rw [permAut_mul, mul_inv_cancel, permAut_one]
  exact (eq_inv_of_mul_eq_one_left h).symm

theorem permAut_conj (σ τ : Equiv.Perm (Fin 5)) :
    permAut τ * permAut σ * (permAut τ)⁻¹ = permAut (τ⁻¹ * σ * τ) := by
  rw [permAut_inv, permAut_mul, permAut_mul, mul_assoc]

@[expose] noncomputable def permMatU (σ : Equiv.Perm (Fin 5)) : Matrix (Fin 5) (Fin 5) K :=
  (1 : Matrix (Fin 5) (Fin 5) K).submatrix σ id

theorem permMatU_apply (σ : Equiv.Perm (Fin 5)) (i m : Fin 5) :
    permMatU σ i m = if σ i = m then 1 else 0 := by
  simp [permMatU, Matrix.one_apply]

theorem permMatU_mul (σ : Equiv.Perm (Fin 5)) (g : Matrix (Fin 5) (Fin 5) K) :
    permMatU σ * g = g.submatrix σ σ * permMatU σ := by
  ext i j
  have h1 : (permMatU σ * g) i j = g (σ i) j := by
    rw [Matrix.mul_apply]
    simp [permMatU_apply]
  have h2 : (g.submatrix σ σ * permMatU σ) i j = g (σ i) j := by
    rw [Matrix.mul_apply]
    have := Equiv.sum_comp σ (fun x => g (σ i) x * (if x = j then (1 : K) else 0))
    simp only [Matrix.submatrix_apply, permMatU_apply]
    rw [this]
    simp
  rw [h1, h2]

theorem permMatU_mul_transpose (σ : Equiv.Perm (Fin 5)) :
    permMatU σ * (permMatU σ)ᵀ = 1 := by
  ext i j
  rw [Matrix.mul_apply, Matrix.one_apply]
  simp only [Matrix.transpose_apply, permMatU_apply]
  by_cases hij : i = j
  · subst hij
    simp
  · simp [hij]

theorem transpose_permMatU_mul (σ : Equiv.Perm (Fin 5)) :
    (permMatU σ)ᵀ * permMatU σ = 1 := by
  ext i j
  rw [Matrix.mul_apply, Matrix.one_apply]
  simp only [Matrix.transpose_apply, permMatU_apply]
  rw [Equiv.sum_comp σ (fun y => (if y = i then (1 : K) else 0) * (if y = j then 1 else 0))]
  by_cases hij : i = j
  · subst hij
    simp
  · have hji : ¬j = i := fun h => hij h.symm
    simp [hij, hji]

theorem permMatU_det (σ : Equiv.Perm (Fin 5)) : (permMatU σ).det = 1 := by
  rw [permMatU, Matrix.det_permute, Matrix.det_one]
  rcases Int.units_eq_one_or σ.sign with h | h <;> simp [h, CharTwo.neg_eq]

theorem permMatU_map_frob (σ : Equiv.Perm (Fin 5)) :
    (permMatU σ).map (iterateFrobenius K 2 3) = permMatU σ := by
  ext i m
  simp only [Matrix.map_apply, permMatU_apply]
  split_ifs <;> simp

theorem permMatU_unitary (σ : Equiv.Perm (Fin 5)) :
    ((permMatU σ).map (iterateFrobenius K 2 3))ᵀ * permMatU σ = 1 := by
  rw [permMatU_map_frob, transpose_permMatU_mul]

@[expose] noncomputable def permSU (σ : Equiv.Perm (Fin 5)) : SUI :=
  ⟨⟨permMatU σ, (permMatU σ)ᵀ, permMatU_mul_transpose σ, transpose_permMatU_mul σ⟩,
    (mem_SUI_iff _).mpr ⟨permMatU_det σ, permMatU_unitary σ⟩⟩

theorem mU_permSU (σ : Equiv.Perm (Fin 5)) : mU (permSU σ) = permMatU σ := rfl

theorem permSU_conj (σ : Equiv.Perm (Fin 5)) (g : SUI) :
    permSU σ * g * (permSU σ)⁻¹ = reindexSU σ g := by
  rw [mul_inv_eq_iff_eq_mul]
  apply mU_injective
  rw [mU_mul, mU_mul, mU_reindexSU, mU_permSU]
  exact permMatU_mul σ _

theorem permSU_mem_normalizer (σ : Equiv.Perm (Fin 5)) :
    permSU σ ∈ Subgroup.normalizer (A0 : Set SUI) := by
  rw [Subgroup.mem_normalizer_iff]
  intro h
  rw [permSU_conj]
  constructor
  · exact reindexSU_mem_A0 σ
  · intro hh
    have hh' : reindexSU σ h ∈ A0.map (reindexSU σ).toMonoidHom := by
      rw [map_reindexSU_A0]
      exact hh
    obtain ⟨a, ha, hae⟩ := Subgroup.mem_map.mp hh'
    have : a = h := (reindexSU σ).injective hae
    rwa [this] at ha

theorem exists_permAut_of_mem_starOf {φ : MulAut A0} (hφ : φ ∈ starOf A0 (⊤ : Subgroup SUI)) :
    ∃ σ : Equiv.Perm (Fin 5), φ = permAut σ := by
  obtain ⟨x, -, rfl⟩ := Subgroup.mem_map.mp hφ
  have hg : ∀ v : Fin 4 → ZMod 3, ∃ w : Fin 4 → ZMod 3,
      (x : SUI) * δ (Multiplicative.ofAdd v) * (x : SUI)⁻¹ = δ (Multiplicative.ofAdd w) := by
    intro v
    have hmem : (x : SUI) * δ (Multiplicative.ofAdd v) * (x : SUI)⁻¹ ∈ δ.range :=
      (Subgroup.mem_normalizer_iff.mp x.2 _).mp (δ_mem_A0 v)
    obtain ⟨y, hy⟩ := hmem
    exact ⟨Multiplicative.toAdd y, by rw [ofAdd_toAdd, hy]⟩
  obtain ⟨σ, hσ⟩ := monomial_of_normalizes (x : SUI) hg
  refine ⟨σ, ?_⟩
  apply MulEquiv.ext
  intro a
  apply Subtype.ext
  obtain ⟨y, hy⟩ : (a : SUI) ∈ δ.range := a.2
  have hv : (a : SUI) = δ (Multiplicative.ofAdd (Multiplicative.toAdd y)) := by
    rw [ofAdd_toAdd, hy]
  rw [normalizerMonoidHom_coe_apply_G, permAut_apply, hv, hσ]

theorem permAut_mem_starOf (σ : Equiv.Perm (Fin 5)) :
    permAut σ ∈ starOf A0 (⊤ : Subgroup SUI) := by
  refine Subgroup.mem_map.mpr ⟨⟨permSU σ, permSU_mem_normalizer σ⟩,
    Subgroup.mem_subgroupOf.mpr (Subgroup.mem_top _), ?_⟩
  apply MulEquiv.ext
  intro a
  apply Subtype.ext
  rw [normalizerMonoidHom_coe_apply_G, permAut_apply]
  exact permSU_conj σ a

theorem A0_comm (x y : A0) : x * y = y * x := by
  obtain ⟨u, hu⟩ : (x : SUI) ∈ δ.range := x.2
  obtain ⟨w, hw⟩ : (y : SUI) ∈ δ.range := y.2
  apply Subtype.ext
  change (x : SUI) * (y : SUI) = (y : SUI) * (x : SUI)
  rw [← hu, ← hw, ← map_mul, ← map_mul, mul_comm u w]

theorem card_commOf_mul_fixed_A0 (φ : MulAut A0) :
    Nat.card (commOf φ) * Nat.card (fixedSubgroupOf φ) = 3 ^ 4 := by
  rw [← card_A0]
  exact card_commOf_mul_card_fixed A0_comm φ

theorem fixed_iff_ext (σ : Equiv.Perm (Fin 5)) (v : Fin 4 → ZMod 3) :
    reindexSU σ (δ (Multiplicative.ofAdd v)) = δ (Multiplicative.ofAdd v) ↔
      ext3 v ∘ σ = ext3 v := by
  rw [reindexSU_δ]
  have hs : ∑ i, (ext3 v ∘ σ) i = 0 := (Equiv.sum_comp σ (ext3 v)).trans (sum_ext3 v)
  constructor
  · intro h
    have h1 : res3 (ext3 v ∘ σ) = v := Multiplicative.ofAdd.injective (δ_injective h)
    calc ext3 v ∘ σ = ext3 (res3 (ext3 v ∘ σ)) := (ext3_res3 hs).symm
      _ = ext3 v := by rw [h1]
  · intro h
    rw [h, res3_ext3]

theorem mem_fixed_permAut_iff (σ : Equiv.Perm (Fin 5)) (v : Fin 4 → ZMod 3) :
    (⟨δ (Multiplicative.ofAdd v), δ_mem_A0 v⟩ : A0) ∈ fixedSubgroupOf (permAut σ) ↔
      ext3 v ∘ σ = ext3 v := by
  rw [← fixed_iff_ext σ v, mem_fixedSubgroupOf, ← Subtype.coe_inj, permAut_apply]

theorem permAut_fixed_card (σ : Equiv.Perm (Fin 5)) :
    Nat.card (fixedSubgroupOf (permAut σ)) =
      (Finset.univ.filter fun v : Fin 4 → ZMod 3 => ext3 v ∘ σ = ext3 v).card := by
  rw [← Fintype.card_subtype, ← Nat.card_eq_fintype_card]
  symm
  refine Nat.card_eq_of_bijective
    (fun v => ⟨⟨δ (Multiplicative.ofAdd v.1), δ_mem_A0 _⟩, (mem_fixed_permAut_iff σ v.1).mpr v.2⟩)
    ⟨?_, ?_⟩
  · intro v w h
    have h' : δ (Multiplicative.ofAdd v.1) = δ (Multiplicative.ofAdd w.1) :=
      congrArg (fun x : fixedSubgroupOf (permAut σ) => ((x : A0) : SUI)) h
    exact Subtype.ext (Multiplicative.ofAdd.injective (δ_injective h'))
  · rintro ⟨⟨a, ha⟩, hfix⟩
    obtain ⟨y, rfl⟩ : a ∈ δ.range := ha
    have hv := (mem_fixed_permAut_iff σ (Multiplicative.toAdd y)).mp hfix
    exact ⟨⟨Multiplicative.toAdd y, hv⟩, rfl⟩

theorem fixcount_eq_27_imp_swap :
    ∀ σ : Equiv.Perm (Fin 5),
      (Finset.univ.filter fun v : Fin 4 → ZMod 3 => ext3 v ∘ σ = ext3 v).card = 27 →
        ∃ a b : Fin 5, a ≠ b ∧ σ = Equiv.swap a b := by
  decide +kernel

theorem isReflectionOn_permAut_imp (σ : Equiv.Perm (Fin 5)) (h : IsReflectionOn (permAut σ)) :
    ∃ a b : Fin 5, a ≠ b ∧ σ = Equiv.swap a b := by
  apply fixcount_eq_27_imp_swap σ
  have h1 := card_commOf_mul_fixed_A0 (permAut σ)
  rw [h.2, permAut_fixed_card] at h1
  omega

theorem swap_side_ne : ∀ i j a : Fin 5, i ≠ j → a ≠ Equiv.swap i a j := by
  decide

theorem exists_perm_map_pair {i j a b : Fin 5} (hij : i ≠ j) (hab : a ≠ b) :
    ∃ τ : Equiv.Perm (Fin 5), τ i = a ∧ τ j = b := by
  have hside : a ≠ Equiv.swap i a j := swap_side_ne i j a hij
  refine ⟨Equiv.swap (Equiv.swap i a j) b * Equiv.swap i a, ?_, ?_⟩
  · simp only [Equiv.Perm.mul_apply, Equiv.swap_apply_left]
    exact Equiv.swap_apply_of_ne_of_ne hside hab
  · simp only [Equiv.Perm.mul_apply]
    rw [Equiv.swap_apply_left]

theorem permAut_swap_ne_one {i j : Fin 5} (hij : i ≠ j) : permAut (Equiv.swap i j) ≠ 1 := by
  intro h
  obtain ⟨v, hv⟩ := ext_ne i j hij
  have key : (⟨δ (Multiplicative.ofAdd v), δ_mem_A0 v⟩ : A0) ∈
      fixedSubgroupOf (permAut (Equiv.swap i j)) := by
    rw [h, mem_fixedSubgroupOf]
    rfl
  rw [mem_fixed_permAut_iff] at key
  have h1 := congrFun key i
  simp only [Function.comp_apply, Equiv.swap_apply_left] at h1
  exact hv h1.symm

theorem permAut_swap_mem_D (D : Set (MulAut A0)) (hrefl : ∀ φ ∈ D, IsReflectionOn φ)
    (hconj : ∀ g ∈ starOf A0 (⊤ : Subgroup SUI), ∀ φ ∈ D, g * φ * g⁻¹ ∈ D)
    (hcl : Subgroup.closure D = starOf A0 (⊤ : Subgroup SUI)) {i j : Fin 5} (hij : i ≠ j) :
    permAut (Equiv.swap i j) ∈ D := by
  have hne : D.Nonempty := by
    by_contra hD
    rw [Set.not_nonempty_iff_eq_empty] at hD
    have h1 : permAut (Equiv.swap i j) ∈ starOf A0 (⊤ : Subgroup SUI) := permAut_mem_starOf _
    rw [← hcl, hD, Subgroup.closure_empty, Subgroup.mem_bot] at h1
    exact permAut_swap_ne_one hij h1
  obtain ⟨φ0, hφ0⟩ := hne
  have hφS : φ0 ∈ starOf A0 (⊤ : Subgroup SUI) := hcl ▸ Subgroup.subset_closure hφ0
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

theorem fibre_pair_decide : ∀ i j a b : Fin 5, i ≠ j →
    (∀ v : Fin 4 → ZMod 3, ext3 v i = ext3 v j → ext3 v a = ext3 v b) →
      a = b ∨ ((a = i ∨ a = j) ∧ (b = i ∨ b = j)) := by
  decide

theorem entry_comm_ext (g : SUI) (v : Fin 4 → ZMod 3)
    (hv : g * δ (Multiplicative.ofAdd v) = δ (Multiplicative.ofAdd v) * g) (a b : Fin 5)
    (hab : mU g a b ≠ 0) : ext3 v b = ext3 v a := by
  have h2 := congrArg (fun x : SUI => mU x a b) hv
  simp only [mU_mul, mU_δ, Matrix.mul_diagonal, Matrix.diagonal_mul] at h2
  have h3 : mU g a b * eω (ext3 v b) = mU g a b * eω (ext3 v a) := by
    rw [h2, mul_comm]
  exact eω_injective (mul_left_cancel₀ hab h3)

theorem entry_T_support {i j : Fin 5} (hij : i ≠ j) (g : SUI)
    (hg : ∀ v : Fin 4 → ZMod 3, ext3 v i = ext3 v j →
      g * δ (Multiplicative.ofAdd v) = δ (Multiplicative.ofAdd v) * g)
    (a b : Fin 5) (hab : mU g a b ≠ 0) :
    a = b ∨ ((a = i ∨ a = j) ∧ (b = i ∨ b = j)) :=
  fibre_pair_decide i j a b hij fun v hv => (entry_comm_ext g v (hg v hv) a b hab).symm

theorem diag_eq_one_of_perfect {P : Subgroup SUI} (hP : Group.IsPerfect P) (k : Fin 5)
    (hrow : ∀ g ∈ P, ∀ l, l ≠ k → mU g k l = 0) : ∀ g ∈ P, mU g k k = 1 := by
  let f : P →* K :=
    { toFun := fun g => mU g k k
      map_one' := by simp [mU_one]
      map_mul' := fun g h => by
        simp only [Subgroup.coe_mul, mU_mul, Matrix.mul_apply]
        rw [Finset.sum_eq_single k]
        · intro l _ hl
          rw [hrow _ g.2 l hl, zero_mul]
        · simp }
  intro g hg
  exact perfect_hom_trivial hP f ⟨g, hg⟩

theorem isIdOutside_of_perfect {i j : Fin 5} (hij : i ≠ j) {P : Subgroup SUI}
    (hP : Group.IsPerfect P)
    (hPC : ∀ g ∈ P, ∀ v : Fin 4 → ZMod 3, ext3 v i = ext3 v j →
      g * δ (Multiplicative.ofAdd v) = δ (Multiplicative.ofAdd v) * g) :
    ∀ g ∈ P, IsIdOutside ({i, j} : Set (Fin 5)) (mU g) := by
  have hrowT : ∀ g ∈ P, ∀ k l : Fin 5, k ≠ i → k ≠ j → l ≠ k → mU g k l = 0 := by
    intro g hg k l hki hkj hl
    by_contra hc
    rcases entry_T_support hij g (hPC g hg) k l hc with h | ⟨h1, _⟩
    · exact hl h.symm
    · tauto
  have hdiag : ∀ k : Fin 5, k ≠ i → k ≠ j → ∀ g ∈ P, mU g k k = 1 :=
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

end CFSG.RankThree.PartTwo.Sec21.RootsU58
