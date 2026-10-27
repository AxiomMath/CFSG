module

public import CFSG.RankThree.PartTwo.Sec21.Item233TablesSp64
public import CFSG.RankThree.PartTwo.Sec21.Item233RootsL44

public section

namespace CFSG.RankThree.PartTwo.Sec21.HeringRootsSp64

open Matrix hiding ext
open CFSG.RankThree.PartTwo.KFacts.KS21 CFSG.RankThree.PartTwo.KFacts.KS21.Sp64
open CFSG.LocalAnalysis.ComponentInitial.SymplecticTorusWeyl
open CFSG.RankThree.PartTwo.Sec21.Tables CFSG.RankThree.PartTwo.Sec21.TablesSp64
open CFSG.RankThree.PartTwo.Sec21.TablesL44 (eω eω_injective eω_ne_zero eω_add eω_zero)
open CFSG.RankThree.PartTwo CFSG.RankThree CFSG.RankThree.LocalRank CFSG
open CFSG.Assembly (IsElemAbelian)
open CFSG.Assembly.LowTwoRank

theorem ext_swap (v : Fin 3 → ZMod 3) (x : Fin 3 ⊕ Fin 3) : ext v x.swap = - ext v x := by
  rcases x with i | i
  · rfl
  · change v i = - -v i
    exact (neg_neg _).symm

theorem ext_inj : ∀ x y : Fin 3 ⊕ Fin 3, (∀ v : Fin 3 → ZMod 3, ext v x = ext v y) → x = y := by
  decide +kernel

theorem Jm_apply (x y : Fin 3 ⊕ Fin 3) : Jm x y = if y = x.swap then 1 else 0 := by
  rcases x with i | i <;> rcases y with j | j <;>
    first
    | (by_cases h : i = j <;> simp [Jm, Matrix.one_apply, neg_one_F4, eq_comm, h])
    | simp [Jm, Matrix.one_apply, neg_one_F4, eq_comm]

theorem Jm_submatrix_of_mem {π : Equiv.Perm (Fin 3 ⊕ Fin 3)} (hπ : π ∈ signedPermGroup 3) :
    Jm.submatrix π π = Jm := by
  ext x y
  have hx : (π x).swap = π x.swap := (mem_signedPermGroup.mp hπ x).symm
  rw [submatrix_apply, Jm_apply, Jm_apply]
  simp only [hx, π.injective.eq_iff]

@[expose] def wv (π : Equiv.Perm (Fin 3 ⊕ Fin 3)) (v : Fin 3 → ZMod 3) : Fin 3 → ZMod 3 :=
  fun i => ext v (π (Sum.inl i))

theorem ext_comp_signed {π : Equiv.Perm (Fin 3 ⊕ Fin 3)} (hπ : π ∈ signedPermGroup 3)
    (v : Fin 3 → ZMod 3) : ext v ∘ π = ext (wv π v) := by
  funext x
  rcases x with i | i
  · rfl
  · have h := mem_signedPermGroup.mp hπ (Sum.inl i)
    change ext v (π (Sum.inr i)) = - ext v (π (Sum.inl i))
    rw [show Sum.inr i = (Sum.inl i : Fin 3 ⊕ Fin 3).swap from rfl, h, ext_swap]

theorem permMatrix_conj (π : Equiv.Perm (Fin 3 ⊕ Fin 3)) (M : Mat6) :
    π.permMatrix F4 * M * (π⁻¹).permMatrix F4 = M.submatrix π π := by
  rw [Equiv.Perm.permMatrix, PEquiv.toMatrix_toPEquiv_mul, Equiv.Perm.permMatrix,
    PEquiv.mul_toMatrix_toPEquiv]
  simp only [Matrix.submatrix_submatrix]
  rfl

@[expose] noncomputable def permGL (π : Equiv.Perm (Fin 3 ⊕ Fin 3)) :
    GL (Fin 3 ⊕ Fin 3) F4 :=
  ⟨π.permMatrix F4, (π⁻¹).permMatrix F4,
    by rw [← Matrix.permMatrix_mul, inv_mul_cancel, Matrix.permMatrix_one],
    by rw [← Matrix.permMatrix_mul, mul_inv_cancel, Matrix.permMatrix_one]⟩

theorem permGL_mem {π : Equiv.Perm (Fin 3 ⊕ Fin 3)} (hπ : π ∈ signedPermGroup 3) :
    permGL π ∈ StatedSp 3 F4 := by
  rw [mem_statedSp_iff]
  change (π.permMatrix F4)ᵀ * Jm * π.permMatrix F4 = Jm
  have hπ' : π⁻¹ ∈ signedPermGroup 3 := inv_mem hπ
  rw [Matrix.transpose_permMatrix]
  have h := permMatrix_conj π⁻¹ Jm
  rw [inv_inv] at h
  rw [h, Jm_submatrix_of_mem hπ']

@[expose] noncomputable def permSp (π : Equiv.Perm (Fin 3 ⊕ Fin 3)) (hπ : π ∈ signedPermGroup 3) :
    Sp :=
  ⟨permGL π, permGL_mem hπ⟩

theorem mat_permSp {π : Equiv.Perm (Fin 3 ⊕ Fin 3)} (hπ : π ∈ signedPermGroup 3) :
    mat (permSp π hπ) = π.permMatrix F4 := rfl

theorem mat_permSp_inv {π : Equiv.Perm (Fin 3 ⊕ Fin 3)} (hπ : π ∈ signedPermGroup 3) :
    mat (permSp π hπ)⁻¹ = (π⁻¹).permMatrix F4 := rfl

theorem permSp_conj {π : Equiv.Perm (Fin 3 ⊕ Fin 3)} (hπ : π ∈ signedPermGroup 3) (g : Sp) :
    permSp π hπ * g * (permSp π hπ)⁻¹ = reindexSp π (Jm_submatrix_of_mem hπ) g := by
  apply mat_injective
  rw [mat_mul, mat_mul, mat_permSp_inv, mat_permSp, permMatrix_conj, mat_reindexSp]

theorem exists_eq_δ (a : A0) :
    ∃ v : Fin 3 → ZMod 3, a = ⟨δ (Multiplicative.ofAdd v), δ_mem_A0 v⟩ := by
  obtain ⟨y, hy⟩ : (a : Sp) ∈ δ.range := a.2
  exact ⟨Multiplicative.toAdd y, Subtype.ext hy.symm⟩

theorem permSp_mem_normalizer {π : Equiv.Perm (Fin 3 ⊕ Fin 3)} (hπ : π ∈ signedPermGroup 3) :
    permSp π hπ ∈ Subgroup.normalizer (A0 : Set Sp) := by
  have hext : ∀ v : Fin 3 → ZMod 3, ∃ w, ext v ∘ π = ext w :=
    fun v => ⟨wv π v, ext_comp_signed hπ v⟩
  rw [Subgroup.mem_normalizer_iff]
  intro h
  rw [permSp_conj]
  constructor
  · intro hh
    have h1 : reindexSp π (Jm_submatrix_of_mem hπ) h ∈
        A0.map (reindexSp π (Jm_submatrix_of_mem hπ)).toMonoidHom := Subgroup.mem_map_of_mem _ hh
    rwa [map_reindexSp_A0 _ hext] at h1
  · intro hh
    have hh' : reindexSp π (Jm_submatrix_of_mem hπ) h ∈
        A0.map (reindexSp π (Jm_submatrix_of_mem hπ)).toMonoidHom := by
      rw [map_reindexSp_A0 _ hext]
      exact hh
    obtain ⟨a, ha, hae⟩ := Subgroup.mem_map.mp hh'
    have : a = h := (reindexSp π (Jm_submatrix_of_mem hπ)).injective hae
    rwa [this] at ha

@[expose] noncomputable def signedAut (π : Equiv.Perm (Fin 3 ⊕ Fin 3))
    (hπ : π ∈ signedPermGroup 3) : MulAut A0 :=
  A0.normalizerMonoidHom ⟨permSp π hπ, permSp_mem_normalizer hπ⟩

theorem signedAut_apply {π : Equiv.Perm (Fin 3 ⊕ Fin 3)} (hπ : π ∈ signedPermGroup 3) (a : A0) :
    ((signedAut π hπ a : A0) : Sp) = reindexSp π (Jm_submatrix_of_mem hπ) (a : Sp) :=
  (normalizerMonoidHom_coe_apply_G _ _).trans (permSp_conj hπ a)

theorem signedAut_mem_starOf {π : Equiv.Perm (Fin 3 ⊕ Fin 3)} (hπ : π ∈ signedPermGroup 3) :
    signedAut π hπ ∈ starOf A0 (⊤ : Subgroup Sp) :=
  Subgroup.mem_map.mpr ⟨⟨permSp π hπ, permSp_mem_normalizer hπ⟩,
    Subgroup.mem_subgroupOf.mpr (Subgroup.mem_top _), rfl⟩

theorem signedAut_δ {π : Equiv.Perm (Fin 3 ⊕ Fin 3)} (hπ : π ∈ signedPermGroup 3)
    (v : Fin 3 → ZMod 3) :
    ((signedAut π hπ ⟨δ (Multiplicative.ofAdd v), δ_mem_A0 v⟩ : A0) : Sp) =
      δ (Multiplicative.ofAdd (wv π v)) := by
  rw [signedAut_apply]
  exact reindexSp_δ _ (ext_comp_signed hπ v)

theorem monomial_of_normalizes (g : Sp)
    (hg : ∀ v : Fin 3 → ZMod 3, ∃ w : Fin 3 → ZMod 3,
      g * δ (Multiplicative.ofAdd v) * g⁻¹ = δ (Multiplicative.ofAdd w)) :
    ∃ π : Equiv.Perm (Fin 3 ⊕ Fin 3), π ∈ signedPermGroup 3 ∧ ∀ v : Fin 3 → ZMod 3,
      g * δ (Multiplicative.ofAdd v) * g⁻¹ = δ (Multiplicative.ofAdd (wv π v)) := by
  choose w hw using hg
  have hrel : ∀ (v : Fin 3 → ZMod 3) (x y : Fin 3 ⊕ Fin 3),
      mat g x y * eω (ext v y) = eω (ext (w v) x) * mat g x y := by
    intro v x y
    have h1 : g * δ (Multiplicative.ofAdd v) = δ (Multiplicative.ofAdd (w v)) * g := by
      rw [← hw v, inv_mul_cancel_right]
    have h2 := congrArg (fun z : Sp => mat z x y) h1
    simp only [mat_mul, coe_δ, dg, Matrix.mul_diagonal, Matrix.diagonal_mul] at h2
    exact h2
  have entry_ext : ∀ (v : Fin 3 → ZMod 3) (x y : Fin 3 ⊕ Fin 3), mat g x y ≠ 0 →
      ext v y = ext (w v) x := by
    intro v x y hxy
    have h' : eω (ext v y) = eω (ext (w v) x) :=
      mul_left_cancel₀ hxy (by rw [hrel v x y, mul_comm])
    exact eω_injective h'
  have w_inj : Function.Injective w := by
    intro v v' h
    have h1 : g * δ (Multiplicative.ofAdd v) * g⁻¹ = g * δ (Multiplicative.ofAdd v') * g⁻¹ := by
      rw [hw v, hw v', h]
    have h2 := mul_left_cancel (mul_right_cancel h1)
    exact Multiplicative.ofAdd.injective (δ_injective h2)
  have w_surj : Function.Surjective w := Finite.surjective_of_injective w_inj
  have hcol : ∀ y : Fin 3 ⊕ Fin 3, ∃ x, mat g x y ≠ 0 := by
    intro y
    by_contra h
    push Not at h
    have h1 := congrFun (congrFun (mat_inv_mul g) y) y
    rw [Matrix.mul_apply] at h1
    simp only [h, mul_zero, Finset.sum_const_zero, Matrix.one_apply_eq] at h1
    exact zero_ne_one h1
  have row_unique : ∀ x y y' : Fin 3 ⊕ Fin 3, mat g x y ≠ 0 → mat g x y' ≠ 0 → y = y' := by
    intro x y y' hy hy'
    apply ext_inj
    intro v
    rw [entry_ext v x y hy, entry_ext v x y' hy']
  have col_unique : ∀ x x' y : Fin 3 ⊕ Fin 3, mat g x y ≠ 0 → mat g x' y ≠ 0 → x = x' := by
    intro x x' y hx hx'
    apply ext_inj
    intro u
    obtain ⟨v, rfl⟩ := w_surj u
    rw [← entry_ext v x y hx, ← entry_ext v x' y hx']
  choose σ0 hσ0 using hcol
  have hinj : Function.Injective σ0 := fun y y' h =>
    row_unique (σ0 y) y y' (hσ0 y) (h ▸ hσ0 y')
  let σ : Equiv.Perm (Fin 3 ⊕ Fin 3) :=
    Equiv.ofBijective σ0 (Finite.injective_iff_bijective.mp hinj)
  have hline : IsLinePerm σ (mat g) := fun x y =>
    ⟨fun h => col_unique y (σ x) x h (hσ0 x), fun h => h ▸ hσ0 x⟩
  have hσ : σ ∈ signedPermGroup 3 := hline.mem_signedPermGroup g.2
  refine ⟨σ⁻¹, inv_mem hσ, fun v => ?_⟩
  rw [hw v]
  congr 2
  funext i
  have h1 : mat g (Sum.inl i) (σ⁻¹ (Sum.inl i)) ≠ 0 := by
    have := hσ0 (σ⁻¹ (Sum.inl i))
    have e : σ0 (σ⁻¹ (Sum.inl i)) = Sum.inl i := σ.apply_symm_apply (Sum.inl i)
    rwa [e] at this
  exact (entry_ext v _ _ h1).symm

theorem exists_signedAut_of_mem_starOf {φ : MulAut A0} (hφ : φ ∈ starOf A0 (⊤ : Subgroup Sp)) :
    ∃ (π : Equiv.Perm (Fin 3 ⊕ Fin 3)) (hπ : π ∈ signedPermGroup 3), φ = signedAut π hπ := by
  obtain ⟨x, -, rfl⟩ := Subgroup.mem_map.mp hφ
  have hg : ∀ v : Fin 3 → ZMod 3, ∃ w : Fin 3 → ZMod 3,
      (x : Sp) * δ (Multiplicative.ofAdd v) * (x : Sp)⁻¹ = δ (Multiplicative.ofAdd w) := by
    intro v
    have hmem : (x : Sp) * δ (Multiplicative.ofAdd v) * (x : Sp)⁻¹ ∈ δ.range :=
      (Subgroup.mem_normalizer_iff.mp x.2 _).mp (δ_mem_A0 v)
    obtain ⟨y, hy⟩ := hmem
    exact ⟨Multiplicative.toAdd y, by rw [ofAdd_toAdd, hy]⟩
  obtain ⟨π, hπ, hπv⟩ := monomial_of_normalizes (x : Sp) hg
  refine ⟨π, hπ, ?_⟩
  apply MulEquiv.ext
  intro a
  obtain ⟨v, rfl⟩ := exists_eq_δ a
  apply Subtype.ext
  rw [signedAut_δ hπ v]
  exact (normalizerMonoidHom_coe_apply_G _ _).trans (hπv v)

@[expose] def sgnW (σ : Equiv.Perm (Fin 3)) (s : Fin 3 → Bool) : Equiv.Perm (Fin 3 ⊕ Fin 3) :=
  permE σ * flipE s

theorem sgnW_apply_inl (σ : Equiv.Perm (Fin 3)) (s : Fin 3 → Bool) (i : Fin 3) :
    sgnW σ s (Sum.inl i) = if s i then Sum.inr (σ i) else Sum.inl (σ i) := by
  by_cases h : s i <;> simp [sgnW, permE, flipE, flipF, h]

theorem sgnW_apply_inr (σ : Equiv.Perm (Fin 3)) (s : Fin 3 → Bool) (i : Fin 3) :
    sgnW σ s (Sum.inr i) = if s i then Sum.inl (σ i) else Sum.inr (σ i) := by
  by_cases h : s i <;> simp [sgnW, permE, flipE, flipF, h]

theorem sgnW_mem (σ : Equiv.Perm (Fin 3)) (s : Fin 3 → Bool) : sgnW σ s ∈ signedPermGroup 3 := by
  rw [mem_signedPermGroup]
  intro x
  rcases x with i | i
  · change sgnW σ s (Sum.inr i) = (sgnW σ s (Sum.inl i)).swap
    rw [sgnW_apply_inr, sgnW_apply_inl]
    by_cases h : s i <;> simp [h]
  · change sgnW σ s (Sum.inl i) = (sgnW σ s (Sum.inr i)).swap
    rw [sgnW_apply_inr, sgnW_apply_inl]
    by_cases h : s i <;> simp [h]

theorem elim_eq_aux : ∀ y y' : Fin 3 ⊕ Fin 3, y.elim id id = y'.elim id id →
    y' = y ∨ y' = y.swap := by
  decide

theorem exists_sgnW {π : Equiv.Perm (Fin 3 ⊕ Fin 3)} (hπ : π ∈ signedPermGroup 3) :
    ∃ (σ : Equiv.Perm (Fin 3)) (s : Fin 3 → Bool), π = sgnW σ s := by
  let σ0 : Fin 3 → Fin 3 := fun i => (π (Sum.inl i)).elim id id
  let s : Fin 3 → Bool := fun i => (π (Sum.inl i)).isRight
  have hπl : ∀ i, π (Sum.inl i) = if s i then Sum.inr (σ0 i) else Sum.inl (σ0 i) := by
    intro i
    rcases h : π (Sum.inl i) with j | j <;> simp [σ0, s, h]
  have hπr : ∀ i, π (Sum.inr i) = if s i then Sum.inl (σ0 i) else Sum.inr (σ0 i) := by
    intro i
    have h := mem_signedPermGroup.mp hπ (Sum.inl i)
    change π (Sum.inr i) = (π (Sum.inl i)).swap at h
    rw [h, hπl i]
    by_cases hs : s i <;> simp [hs]
  have hinj : Function.Injective σ0 := by
    intro i j hij
    rcases elim_eq_aux _ _ hij with h | h
    · exact Sum.inl_injective (π.injective h).symm
    · have h' : π (Sum.inl j) = π (Sum.inr i) := by
        rw [h, ← mem_signedPermGroup.mp hπ (Sum.inl i)]
        rfl
      exact absurd (π.injective h') (by simp)
  refine ⟨Equiv.ofBijective σ0 (Finite.injective_iff_bijective.mp hinj), s, ?_⟩
  apply Equiv.ext
  intro x
  rcases x with i | i
  · rw [sgnW_apply_inl, hπl i]
    rfl
  · rw [sgnW_apply_inr, hπr i]
    rfl

@[expose] def wf (σ : Equiv.Perm (Fin 3)) (s : Fin 3 → Bool) (v : Fin 3 → ZMod 3) :
    Fin 3 → ZMod 3 :=
  flipVec s (v ∘ σ)

theorem wv_sgnW (σ : Equiv.Perm (Fin 3)) (s : Fin 3 → Bool) (v : Fin 3 → ZMod 3) :
    wv (sgnW σ s) v = wf σ s v := by
  funext i
  by_cases h : s i
  · simp [wv, wf, flipVec, sgnW_apply_inl, h, TablesSp64.ext]
  · simp [wv, wf, flipVec, sgnW_apply_inl, h, TablesSp64.ext]

@[expose] noncomputable def sAut (σ : Equiv.Perm (Fin 3)) (s : Fin 3 → Bool) : MulAut A0 :=
  signedAut (sgnW σ s) (sgnW_mem σ s)

theorem sAut_mem_starOf (σ : Equiv.Perm (Fin 3)) (s : Fin 3 → Bool) :
    sAut σ s ∈ starOf A0 (⊤ : Subgroup Sp) :=
  signedAut_mem_starOf _

theorem sAut_apply_δ (σ : Equiv.Perm (Fin 3)) (s : Fin 3 → Bool) (v : Fin 3 → ZMod 3) :
    sAut σ s ⟨δ (Multiplicative.ofAdd v), δ_mem_A0 v⟩ =
      ⟨δ (Multiplicative.ofAdd (wf σ s v)), δ_mem_A0 _⟩ :=
  Subtype.ext (by rw [sAut, signedAut_δ, wv_sgnW])

theorem exists_sAut_of_mem_starOf {φ : MulAut A0} (hφ : φ ∈ starOf A0 (⊤ : Subgroup Sp)) :
    ∃ (σ : Equiv.Perm (Fin 3)) (s : Fin 3 → Bool), φ = sAut σ s := by
  obtain ⟨π, hπ, rfl⟩ := exists_signedAut_of_mem_starOf hφ
  obtain ⟨σ, s, rfl⟩ := exists_sgnW hπ
  exact ⟨σ, s, rfl⟩

theorem sAut_mul_eq {σ₁ σ₂ σ₃ σ₄ : Equiv.Perm (Fin 3)} {s₁ s₂ s₃ s₄ : Fin 3 → Bool}
    (h : ∀ v, wf σ₁ s₁ (wf σ₂ s₂ v) = wf σ₃ s₃ (wf σ₄ s₄ v)) :
    sAut σ₁ s₁ * sAut σ₂ s₂ = sAut σ₃ s₃ * sAut σ₄ s₄ := by
  apply MulEquiv.ext
  intro a
  obtain ⟨v, rfl⟩ := exists_eq_δ a
  rw [MulAut.mul_apply, MulAut.mul_apply, sAut_apply_δ, sAut_apply_δ, sAut_apply_δ,
    sAut_apply_δ, h]

theorem A0_comm (x y : A0) : x * y = y * x := by
  obtain ⟨v, rfl⟩ := exists_eq_δ x
  obtain ⟨w, rfl⟩ := exists_eq_δ y
  apply Subtype.ext
  change δ (Multiplicative.ofAdd v) * δ (Multiplicative.ofAdd w) =
    δ (Multiplicative.ofAdd w) * δ (Multiplicative.ofAdd v)
  rw [← map_mul δ, ← map_mul δ, mul_comm]

theorem card_commOf_mul_fixed (φ : MulAut A0) :
    Nat.card (commOf φ) * Nat.card (fixedSubgroupOf φ) = 3 ^ 3 := by
  rw [← card_A0]
  exact card_commOf_mul_card_fixed A0_comm φ

theorem mem_fixed_sAut_iff (σ : Equiv.Perm (Fin 3)) (s : Fin 3 → Bool) (v : Fin 3 → ZMod 3) :
    (⟨δ (Multiplicative.ofAdd v), δ_mem_A0 v⟩ : A0) ∈ fixedSubgroupOf (sAut σ s) ↔
      wf σ s v = v := by
  rw [mem_fixedSubgroupOf, sAut_apply_δ]
  constructor
  · intro h
    have h1 : δ (Multiplicative.ofAdd (wf σ s v)) = δ (Multiplicative.ofAdd v) :=
      congrArg Subtype.val h
    exact Multiplicative.ofAdd.injective (δ_injective h1)
  · intro h
    exact Subtype.ext (by rw [h])

theorem card_fixed_sAut (σ : Equiv.Perm (Fin 3)) (s : Fin 3 → Bool) :
    Nat.card (fixedSubgroupOf (sAut σ s)) =
      (Finset.univ.filter fun v : Fin 3 → ZMod 3 => wf σ s v = v).card := by
  rw [← Fintype.card_subtype, ← Nat.card_eq_fintype_card]
  symm
  refine Nat.card_eq_of_bijective
    (fun v => ⟨⟨δ (Multiplicative.ofAdd v.1), δ_mem_A0 _⟩, (mem_fixed_sAut_iff σ s v.1).mpr v.2⟩)
    ⟨?_, ?_⟩
  · intro v w h
    have h' : δ (Multiplicative.ofAdd v.1) = δ (Multiplicative.ofAdd w.1) :=
      congrArg (fun x : fixedSubgroupOf (sAut σ s) => ((x : A0) : Sp)) h
    exact Subtype.ext (Multiplicative.ofAdd.injective (δ_injective h'))
  · rintro ⟨a, hfix⟩
    obtain ⟨v, rfl⟩ := exists_eq_δ a
    exact ⟨⟨v, (mem_fixed_sAut_iff σ s v).mp hfix⟩, rfl⟩

@[expose] def scFlip (k : Fin 3) : Fin 3 → Bool := fun l => decide (l = k)

@[expose] def stFlip (i j : Fin 3) : Fin 3 → Bool := fun l => decide (l = i ∨ l = j)

set_option synthInstance.maxSize 1000 in
set_option synthInstance.maxHeartbeats 200000 in
theorem fixcount_nine : ∀ (σ : Equiv.Perm (Fin 3)) (s : Fin 3 → Bool),
    (Finset.univ.filter fun v : Fin 3 → ZMod 3 => wf σ s v = v).card = 9 →
      (σ = 1 ∧ ∃ k, s = scFlip k) ∨
      (∃ i j : Fin 3, i ≠ j ∧ σ = Equiv.swap i j ∧ (s = (fun _ => false) ∨ s = stFlip i j)) := by
  decide +kernel

theorem reflection_types {φ : MulAut A0} (hφ : φ ∈ starOf A0 (⊤ : Subgroup Sp))
    (hr : IsReflectionOn φ) :
    (∃ k, φ = sAut 1 (scFlip k)) ∨
      (∃ i j : Fin 3, i ≠ j ∧
        (φ = sAut (Equiv.swap i j) (fun _ => false) ∨ φ = sAut (Equiv.swap i j) (stFlip i j))) := by
  obtain ⟨σ, s, rfl⟩ := exists_sAut_of_mem_starOf hφ
  have h1 := card_commOf_mul_fixed (sAut σ s)
  rw [hr.2, card_fixed_sAut] at h1
  have h9 : (Finset.univ.filter fun v : Fin 3 → ZMod 3 => wf σ s v = v).card = 9 := by omega
  rcases fixcount_nine σ s h9 with ⟨rfl, k, rfl⟩ | ⟨i, j, hij, rfl, h | h⟩
  · exact Or.inl ⟨k, rfl⟩
  · exact Or.inr ⟨i, j, hij, Or.inl (by rw [h])⟩
  · exact Or.inr ⟨i, j, hij, Or.inr (by rw [h])⟩

@[expose] noncomputable def e0 : Multiplicative (Fin 3 → ZMod 3) ≃* A0 :=
  MonoidHom.ofInjective δ_injective

@[expose] noncomputable def toV (a : A0) : Fin 3 → ZMod 3 :=
  Multiplicative.toAdd (e0.symm a)

theorem toV_δ (v : Fin 3 → ZMod 3) : toV ⟨δ (Multiplicative.ofAdd v), δ_mem_A0 v⟩ = v := by
  have h : e0 (Multiplicative.ofAdd v) = ⟨δ (Multiplicative.ofAdd v), δ_mem_A0 v⟩ := rfl
  unfold toV
  rw [← h, MulEquiv.symm_apply_apply]
  rfl

@[expose] def stabSub {X : Type*} (f : A0 → X) : Subgroup (MulAut A0) where
  carrier := {φ | ∀ a, f (φ a) = f a}
  mul_mem' {φ ψ} hφ hψ a := by
    change f (φ (ψ a)) = f a
    rw [hφ, hψ]
  one_mem' a := rfl
  inv_mem' {φ} hφ a := by
    have h := hφ (φ⁻¹ a)
    rw [MulAut.apply_inv_self] at h
    exact h.symm

theorem sAut_mem_stabSub_iff {X : Type*} (f : (Fin 3 → ZMod 3) → X) (σ : Equiv.Perm (Fin 3))
    (s : Fin 3 → Bool) :
    sAut σ s ∈ stabSub (fun a => f (toV a)) ↔ ∀ v, f (wf σ s v) = f v := by
  constructor
  · intro h v
    have := h ⟨δ (Multiplicative.ofAdd v), δ_mem_A0 v⟩
    change f (toV (sAut σ s _)) = f (toV _) at this
    rwa [sAut_apply_δ, toV_δ, toV_δ] at this
  · intro h a
    obtain ⟨v, rfl⟩ := exists_eq_δ a
    change f (toV (sAut σ s _)) = f (toV _)
    rw [sAut_apply_δ, toV_δ, toV_δ]
    exact h v

@[expose] def pf (v : Fin 3 → ZMod 3) : ZMod 3 := v 0 * v 1 * v 2

@[expose] def sqs (v : Fin 3 → ZMod 3) : Fin 3 → ZMod 3 := fun k => v k * v k

theorem st_stab_pf : ∀ i j : Fin 3, i ≠ j → ∀ s₀ : Fin 3 → Bool,
    (s₀ = (fun _ => false) ∨ s₀ = stFlip i j) → ∀ v, pf (wf (Equiv.swap i j) s₀ v) = pf v := by
  decide +kernel

theorem sc_stab_sqs : ∀ k : Fin 3, ∀ v, sqs (wf 1 (scFlip k) v) = sqs v := by
  decide +kernel

theorem sc_not_stab_pf : ∃ v, pf (wf 1 (scFlip 2) v) ≠ pf v := by
  decide

theorem swap01_not_stab_sqs : ∃ v, sqs (wf (Equiv.swap 0 1) (fun _ => false) v) ≠ sqs v := by
  decide

section Closure

variable {D : Set (MulAut A0)}

theorem exists_sc_mem (hrefl : ∀ φ ∈ D, IsReflectionOn φ)
    (hcl : Subgroup.closure D = starOf A0 (⊤ : Subgroup Sp)) : ∃ k, sAut 1 (scFlip k) ∈ D := by
  by_contra hne
  push Not at hne
  have hle : D ⊆ (stabSub (fun a => pf (toV a)) : Set (MulAut A0)) := by
    intro φ hφ
    have hst : φ ∈ starOf A0 (⊤ : Subgroup Sp) := by
      rw [← hcl]
      exact Subgroup.subset_closure hφ
    rcases reflection_types hst (hrefl φ hφ) with ⟨k, rfl⟩ | ⟨i, j, hij, rfl | rfl⟩
    · exact absurd hφ (hne k)
    · exact (sAut_mem_stabSub_iff pf _ _).mpr (st_stab_pf i j hij _ (Or.inl rfl))
    · exact (sAut_mem_stabSub_iff pf _ _).mpr (st_stab_pf i j hij _ (Or.inr rfl))
  have hcl' : Subgroup.closure D ≤ stabSub (fun a => pf (toV a)) :=
    (Subgroup.closure_le _).mpr hle
  have hmem : sAut 1 (scFlip 2) ∈ stabSub (fun a => pf (toV a)) := by
    apply hcl'
    rw [hcl]
    exact sAut_mem_starOf 1 (scFlip 2)
  obtain ⟨v, hv⟩ := sc_not_stab_pf
  exact hv ((sAut_mem_stabSub_iff pf _ _).mp hmem v)

theorem exists_st_mem (hrefl : ∀ φ ∈ D, IsReflectionOn φ)
    (hcl : Subgroup.closure D = starOf A0 (⊤ : Subgroup Sp)) :
    ∃ (i j : Fin 3) (s₀ : Fin 3 → Bool), i ≠ j ∧ (s₀ = (fun _ => false) ∨ s₀ = stFlip i j) ∧
      sAut (Equiv.swap i j) s₀ ∈ D := by
  by_contra hne
  push Not at hne
  have hle : D ⊆ (stabSub (fun a => sqs (toV a)) : Set (MulAut A0)) := by
    intro φ hφ
    have hst : φ ∈ starOf A0 (⊤ : Subgroup Sp) := by
      rw [← hcl]
      exact Subgroup.subset_closure hφ
    rcases reflection_types hst (hrefl φ hφ) with ⟨k, rfl⟩ | ⟨i, j, hij, rfl | rfl⟩
    · exact (sAut_mem_stabSub_iff sqs _ _).mpr (sc_stab_sqs k)
    · exact absurd hφ (hne i j _ hij (Or.inl rfl))
    · exact absurd hφ (hne i j _ hij (Or.inr rfl))
  have hcl' : Subgroup.closure D ≤ stabSub (fun a => sqs (toV a)) :=
    (Subgroup.closure_le _).mpr hle
  have hmem : sAut (Equiv.swap 0 1) (fun _ => false) ∈ stabSub (fun a => sqs (toV a)) := by
    apply hcl'
    rw [hcl]
    exact sAut_mem_starOf _ _
  obtain ⟨v, hv⟩ := swap01_not_stab_sqs
  exact hv ((sAut_mem_stabSub_iff sqs _ _).mp hmem v)

theorem conj_sc : ∀ (k : Fin 3) (v : Fin 3 → ZMod 3),
    wf (Equiv.swap k 2) (fun _ => false) (wf 1 (scFlip k) v) =
      wf 1 (scFlip 2) (wf (Equiv.swap k 2) (fun _ => false) v) := by
  decide +kernel

theorem conj_st : ∀ i j : Fin 3, i ≠ j → ∀ s₀ : Fin 3 → Bool,
    (s₀ = (fun _ => false) ∨ s₀ = stFlip i j) →
      ∃ (τ : Equiv.Perm (Fin 3)) (t : Fin 3 → Bool), ∀ v : Fin 3 → ZMod 3,
        wf τ t (wf (Equiv.swap i j) s₀ v) =
          wf (Equiv.swap 0 1) (fun _ => false) (wf τ t v) := by
  decide +kernel

theorem sAut_s2_mem (hrefl : ∀ φ ∈ D, IsReflectionOn φ)
    (hconj : ∀ g ∈ starOf A0 (⊤ : Subgroup Sp), ∀ φ ∈ D, g * φ * g⁻¹ ∈ D)
    (hcl : Subgroup.closure D = starOf A0 (⊤ : Subgroup Sp)) :
    sAut 1 (scFlip 2) ∈ D := by
  obtain ⟨k, hk⟩ := exists_sc_mem hrefl hcl
  have h := hconj _ (sAut_mem_starOf (Equiv.swap k 2) (fun _ => false)) _ hk
  have e : sAut (Equiv.swap k 2) (fun _ => false) * sAut 1 (scFlip k) *
      (sAut (Equiv.swap k 2) (fun _ => false))⁻¹ = sAut 1 (scFlip 2) := by
    rw [mul_inv_eq_iff_eq_mul]
    exact sAut_mul_eq (conj_sc k)
  rwa [e] at h

theorem sAut_rho01_mem (hrefl : ∀ φ ∈ D, IsReflectionOn φ)
    (hconj : ∀ g ∈ starOf A0 (⊤ : Subgroup Sp), ∀ φ ∈ D, g * φ * g⁻¹ ∈ D)
    (hcl : Subgroup.closure D = starOf A0 (⊤ : Subgroup Sp)) :
    sAut (Equiv.swap 0 1) (fun _ => false) ∈ D := by
  obtain ⟨i, j, s₀, hij, hs₀, hmem⟩ := exists_st_mem hrefl hcl
  obtain ⟨τ, t, hτ⟩ := conj_st i j hij s₀ hs₀
  have h := hconj _ (sAut_mem_starOf τ t) _ hmem
  have e : sAut τ t * sAut (Equiv.swap i j) s₀ * (sAut τ t)⁻¹ =
      sAut (Equiv.swap 0 1) (fun _ => false) := by
    rw [mul_inv_eq_iff_eq_mul]
    exact sAut_mul_eq hτ
  rwa [e] at h

end Closure

end CFSG.RankThree.PartTwo.Sec21.HeringRootsSp64

end
