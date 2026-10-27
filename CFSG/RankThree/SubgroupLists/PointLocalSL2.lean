module

public import CFSG.RankThree.SubgroupLists.SymplecticHeisenberg
public import CFSG.RankThree.SubgroupLists.SymplecticInvolutions
public import CFSG.RankThree.SubgroupLists.TransvectionRecognition
public import CFSG.LinearAlgebra.LinearGroups.Perfect

public section

namespace CFSG.RankThree.SubgroupLists

open Matrix CFSG.Assembly.LowTwoRank
open scoped MatrixGroups commutatorElement

local notation "V₄" => Fin 2 ⊕ Fin 2

variable {K : Type} [Field K] (h2 : (2 : K) ≠ 0)

include h2 in
theorem mem_eigSp_neg_of_orth {j : GL V₄ K} (hj : j ∈ StatedSp 2 K)
    (hj2 : (j : Matrix V₄ V₄ K) * j = 1) {x : V₄ → K}
    (hx : ∀ w ∈ eigSp (j : Matrix V₄ V₄ K) 1, spForm 2 K w x = 0) :
    x ∈ eigSp (j : Matrix V₄ V₄ K) (-1) := by
  obtain ⟨h1, hm, hsum⟩ := mem_eig_add_mem_eig h2 hj2 x
  set x₁ := (2 : K)⁻¹ • (x + (j : Matrix V₄ V₄ K) *ᵥ x)
  set x₂ := (2 : K)⁻¹ • (x - (j : Matrix V₄ V₄ K) *ᵥ x)
  have hx₁ : x₁ = 0 := by
    apply eq_zero_of_forall_spForm
    intro y
    obtain ⟨y₁, y₂, hy⟩ := mem_eig_add_mem_eig h2 hj2 y
    rw [hy, map_add, LinearMap.add_apply]
    have e1 : spForm 2 K ((2 : K)⁻¹ • (y + (j : Matrix V₄ V₄ K) *ᵥ y)) x₁ = 0 := by
      have := hx _ y₁
      rw [hsum, map_add, spForm_eq_zero_of_eig h2 hj y₁ hm, add_zero] at this
      exact this
    have e2 : spForm 2 K ((2 : K)⁻¹ • (y - (j : Matrix V₄ V₄ K) *ᵥ y)) x₁ = 0 := by
      rw [← LinearMap.BilinForm.IsAlt.neg_eq spForm_isAlt, spForm_eq_zero_of_eig h2 hj h1 y₂,
        neg_zero]
    rw [e1, e2, add_zero]
  rw [hsum, hx₁, zero_add]
  exact hm

include h2 in
theorem eq_spTrans_of_fix_of_sq {j u : GL V₄ K} (hj : j ∈ StatedSp 2 K)
    (hj2 : j * j = 1) (hj1 : j ≠ 1) (hjm : j ≠ -1) (hu : u ∈ StatedSp 2 K)
    (hfix : ∀ v ∈ eigSp (j : Matrix V₄ V₄ K) 1, (u : Matrix V₄ V₄ K) *ᵥ v = v)
    (hsq : ∀ v, (u : Matrix V₄ V₄ K) *ᵥ ((u : Matrix V₄ V₄ K) *ᵥ v - v) =
      (u : Matrix V₄ V₄ K) *ᵥ v - v)
    (hu1 : u ≠ 1) : ∃ a : V₄ → K, ∃ c : K, a ≠ 0 ∧ c ≠ 0 ∧ u = spTrans a c := by
  have hjj : (j : Matrix V₄ V₄ K) * j = 1 := by rw [← Units.val_mul, hj2, Units.val_one]
  set N : (V₄ → K) → (V₄ → K) := fun v => (u : Matrix V₄ V₄ K) *ᵥ v - v with hN
  have hNsq : ∀ v, N (N v) = 0 := fun v => by
    simp only [hN, hsq, sub_self]
  have hNmem : ∀ v, N v ∈ eigSp (j : Matrix V₄ V₄ K) (-1) := fun v =>
    mem_eigSp_neg_of_orth h2 hj hjj fun w hw => by
      simp only [hN, map_sub]
      rw [← hfix w hw, spForm_mulVec hu, hfix w hw, sub_self]
  have hNfix : ∀ v ∈ eigSp (j : Matrix V₄ V₄ K) 1, N v = 0 := fun v hv => by
    simp only [hN, hfix v hv, sub_self]
  obtain ⟨v₀, hv₀, hNv₀⟩ : ∃ v₀ ∈ eigSp (j : Matrix V₄ V₄ K) (-1), N v₀ ≠ 0 := by
    by_contra hcon
    push Not at hcon
    apply hu1
    apply gl_ext_mulVec
    intro v
    obtain ⟨h1, hm, hsum⟩ := mem_eig_add_mem_eig h2 hjj v
    have hv : N v = 0 := by
      rw [hsum]
      simp only [hN, mulVec_add] at hNfix hcon ⊢
      have a1 := hNfix _ h1
      have a2 := hcon _ hm
      rw [sub_eq_zero] at a1 a2
      rw [a1, a2, sub_self]
    simp only [hN, sub_eq_zero] at hv
    rw [hv, Units.val_one, one_mulVec]
  set a := N v₀ with ha
  clear_value a
  have haE : a ∈ eigSp (j : Matrix V₄ V₄ K) (-1) := ha ▸ hNmem v₀
  have hNa : N a = 0 := ha ▸ hNsq v₀
  have hW : eigSp (j : Matrix V₄ V₄ K) (-1) ⊓ eigSp (u : Matrix V₄ V₄ K) 1 = K ∙ a := by
    have hle : K ∙ a ≤ eigSp (j : Matrix V₄ V₄ K) (-1) ⊓ eigSp (u : Matrix V₄ V₄ K) 1 := by
      rw [Submodule.span_singleton_le_iff_mem]
      refine Submodule.mem_inf.mpr ⟨haE, ?_⟩
      rw [mem_eigSp, one_smul]
      have := hNa
      simp only [hN, sub_eq_zero] at this
      exact this
    have hlt : eigSp (j : Matrix V₄ V₄ K) (-1) ⊓ eigSp (u : Matrix V₄ V₄ K) 1 <
        eigSp (j : Matrix V₄ V₄ K) (-1) := by
      refine lt_of_le_of_ne inf_le_left fun h => hNv₀ ?_
      have hv₀' : v₀ ∈ eigSp (j : Matrix V₄ V₄ K) (-1) ⊓ eigSp (u : Matrix V₄ V₄ K) 1 := by
        rw [h]
        exact hv₀
      have := (Submodule.mem_inf.mp hv₀').2
      rw [mem_eigSp, one_smul] at this
      simp only [ha, hN, this, sub_self]
    have hrank := Submodule.finrank_lt_finrank_of_lt hlt
    rw [finrank_eig_neg_one_eq_two h2 hj hj2 hj1 hjm] at hrank
    symm
    apply Submodule.eq_of_le_of_finrank_le hle
    rw [finrank_span_singleton hNv₀]
    omega
  have hNline : ∀ v, ∃ t : K, N v = t • a := fun v => by
    have hmem : N v ∈ K ∙ a := by
      rw [← hW]
      refine Submodule.mem_inf.mpr ⟨hNmem v, ?_⟩
      rw [mem_eigSp, one_smul]
      have := hNsq v
      simp only [hN, sub_eq_zero] at this ⊢
      exact this
    obtain ⟨t, ht⟩ := Submodule.mem_span_singleton.mp hmem
    exact ⟨t, ht.symm⟩
  have ha0 : a ≠ 0 := hNv₀
  obtain ⟨w₀, hw₀⟩ : ∃ w₀, spForm 2 K w₀ a = 1 := by
    by_contra hcon
    push Not at hcon
    apply ha0
    apply eq_zero_of_forall_spForm
    intro x
    by_contra hx
    apply hcon ((spForm 2 K x a)⁻¹ • x)
    rw [map_smul, LinearMap.smul_apply, smul_eq_mul, inv_mul_cancel₀ hx]
  have horth : ∀ v, spForm 2 K v a = 0 → N v = 0 := by
    intro v hv
    have hsup : eigSp (j : Matrix V₄ V₄ K) 1 ⊔ K ∙ a = orth (K ∙ a) := by
      apply Submodule.eq_of_le_of_finrank_eq
      · rw [sup_le_iff]
        constructor
        · intro x hx
          rw [mem_orth]
          intro y hy
          obtain ⟨l, rfl⟩ := Submodule.mem_span_singleton.mp hy
          rw [map_smul, LinearMap.smul_apply, smul_eq_mul]
          rw [← LinearMap.BilinForm.IsAlt.neg_eq spForm_isAlt, spForm_eq_zero_of_eig h2 hj hx haE,
            neg_zero, mul_zero]
        · intro x hx
          rw [mem_orth]
          intro y hy
          obtain ⟨l, rfl⟩ := Submodule.mem_span_singleton.mp hy
          obtain ⟨m, rfl⟩ := Submodule.mem_span_singleton.mp hx
          simp [spForm_self]
      · have hdisj : eigSp (j : Matrix V₄ V₄ K) 1 ⊓ K ∙ a = ⊥ := by
          rw [eq_bot_iff]
          intro x ⟨hx1, hx2⟩
          have hxm : x ∈ eigSp (j : Matrix V₄ V₄ K) (-1) :=
            (Submodule.span_singleton_le_iff_mem _ _).mpr haE hx2
          have := eig_inf_eig h2 (j : Matrix V₄ V₄ K)
          rw [eq_bot_iff] at this
          exact this ⟨hx1, hxm⟩
        have h1 := Submodule.finrank_sup_add_finrank_inf_eq (eigSp (j : Matrix V₄ V₄ K) 1)
          (K ∙ a)
        rw [hdisj, finrank_bot, add_zero, finrank_span_singleton ha0] at h1
        have h3 := finrank_eig_add_finrank_eig h2 hjj
        rw [finrank_eig_neg_one_eq_two h2 hj hj2 hj1 hjm] at h3
        rw [h1, finrank_orth, finrank_span_singleton ha0]
        omega
    have hvmem : v ∈ eigSp (j : Matrix V₄ V₄ K) 1 ⊔ K ∙ a := by
      rw [hsup, mem_orth]
      intro y hy
      obtain ⟨l, rfl⟩ := Submodule.mem_span_singleton.mp hy
      rw [map_smul, LinearMap.smul_apply, smul_eq_mul,
        ← LinearMap.BilinForm.IsAlt.neg_eq spForm_isAlt, hv, neg_zero, mul_zero]
    obtain ⟨x, hx, y, hy, rfl⟩ := Submodule.mem_sup.mp hvmem
    obtain ⟨l, rfl⟩ := Submodule.mem_span_singleton.mp hy
    have hNy : N (l • a) = 0 := by
      have := hNa
      simp only [hN, mulVec_smul] at this ⊢
      rw [← smul_sub, this, smul_zero]
    have hNx := hNfix x hx
    simp only [hN, mulVec_add] at hNx hNy ⊢
    rw [sub_eq_zero] at hNx hNy
    rw [hNx, hNy, sub_self]
  obtain ⟨c, hc⟩ := hNline w₀
  have hNv : ∀ v, N v = (c * spForm 2 K v a) • a := by
    intro v
    have hv' : N (v - spForm 2 K v a • w₀) = 0 := horth _ (by
      rw [map_sub, map_smul, LinearMap.sub_apply, LinearMap.smul_apply, hw₀, smul_eq_mul,
        mul_one, sub_self])
    have hsplit : N v = N (v - spForm 2 K v a • w₀) + spForm 2 K v a • N w₀ := by
      simp only [hN, mulVec_sub, mulVec_smul, smul_sub]
      abel
    rw [hsplit, hv', zero_add, hc, smul_smul, mul_comm]
  refine ⟨a, c, ha0, ?_, ?_⟩
  · rintro rfl
    apply hNv₀
    rw [ha, hNv v₀, zero_mul, zero_smul]
  · apply gl_ext_mulVec
    intro v
    rw [spTrans_mulVec, ← hNv v]
    simp only [hN]
    abel

@[expose] def lineStabE (G : Subgroup (GL V₄ K)) : Subgroup (GL V₄ K) where
  carrier := {g | g ∈ G ∧ ∃ l : K, (g : Matrix V₄ V₄ K) *ᵥ spE = l • spE}
  mul_mem' := by
    rintro g h ⟨hg, l, hl⟩ ⟨hh, m, hm⟩
    refine ⟨G.mul_mem hg hh, m * l, ?_⟩
    rw [gl_mulVec_mul, hm, mulVec_smul, hl, smul_smul]
  one_mem' := ⟨G.one_mem, 1, by rw [Units.val_one, one_mulVec, one_smul]⟩
  inv_mem' := by
    rintro g ⟨hg, l, hl⟩
    refine ⟨G.inv_mem hg, l⁻¹, ?_⟩
    have hl0 : l ≠ 0 := by
      rintro rfl
      have := congrArg (fun v => ((g⁻¹ : GL V₄ K) : Matrix V₄ V₄ K) *ᵥ v) hl
      simp only [gl_inv_mulVec_mulVec, zero_smul, mulVec_zero] at this
      simpa [spE] using congrFun this (Sum.inl 0)
    have := congrArg (fun v => ((g⁻¹ : GL V₄ K) : Matrix V₄ V₄ K) *ᵥ v) hl
    simp only [gl_inv_mulVec_mulVec, mulVec_smul] at this
    calc ((g⁻¹ : GL V₄ K) : Matrix V₄ V₄ K) *ᵥ spE
        = l⁻¹ • (l • ((g⁻¹ : GL V₄ K) : Matrix V₄ V₄ K) *ᵥ spE) := by
          rw [smul_smul, inv_mul_cancel₀ hl0, one_smul]
      _ = l⁻¹ • spE := by rw [← this]

theorem mulVec_spE_eq {G : Subgroup (GL V₄ K)} (g : lineStabE G) :
    ((g : GL V₄ K) : Matrix V₄ V₄ K) *ᵥ spE =
      ((g : GL V₄ K) : Matrix V₄ V₄ K) (Sum.inl 0) (Sum.inl 0) • spE := by
  obtain ⟨-, l, hl⟩ := g.2
  rw [hl, entry_inl_zero_of_mulVec_eq_smul hl]

theorem entry_ne_zero_of_lineStabE {G : Subgroup (GL V₄ K)} (g : lineStabE G) :
    ((g : GL V₄ K) : Matrix V₄ V₄ K) (Sum.inl 0) (Sum.inl 0) ≠ 0 := by
  intro h0
  have hl := mulVec_spE_eq g
  rw [h0, zero_smul] at hl
  have := congrArg (fun v => (((g : GL V₄ K)⁻¹ : GL V₄ K) : Matrix V₄ V₄ K) *ᵥ v) hl
  simp only [gl_inv_mulVec_mulVec, mulVec_zero] at this
  simpa [spE] using congrFun this (Sum.inl 0)

@[expose] noncomputable def scalarHomE (G : Subgroup (GL V₄ K)) : lineStabE G →* Kˣ where
  toFun g := Units.mk0 _ (entry_ne_zero_of_lineStabE g)
  map_one' := by ext; simp
  map_mul' g h := by
    ext
    simp only [Units.val_mk0, Subgroup.coe_mul, Units.val_mul, Matrix.mul_apply,
      Fintype.sum_sum_type, Fin.sum_univ_two]
    have h1 := entry_eq_zero_of_mulVec_eq_smul (mulVec_spE_eq h) (i := Sum.inl 1) (by decide)
    have h2' := entry_eq_zero_of_mulVec_eq_smul (mulVec_spE_eq h) (i := Sum.inr 0) (by simp)
    have h3 := entry_eq_zero_of_mulVec_eq_smul (mulVec_spE_eq h) (i := Sum.inr 1) (by simp)
    rw [h1, h2', h3]
    ring

theorem scalarHomE_apply {G : Subgroup (GL V₄ K)} (g : lineStabE G) :
    ((scalarHomE G g : Kˣ) : K) = ((g : GL V₄ K) : Matrix V₄ V₄ K) (Sum.inl 0) (Sum.inl 0) :=
  rfl

@[expose] noncomputable def spBlockHom {G : Subgroup (GL V₄ K)} (hGS : G ≤ StatedSp 2 K) :
    lineStabE G →* SL(2, K) where
  toFun g := ⟨spBlock ((g : GL V₄ K) : Matrix V₄ V₄ K),
    det_spBlock (hGS g.2.1) (mulVec_spE_eq g)⟩
  map_one' := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [spBlock]
  map_mul' g h := by
    apply Subtype.ext
    change spBlock (((g : GL V₄ K) * (h : GL V₄ K) : GL V₄ K) : Matrix V₄ V₄ K) =
      spBlock ((g : GL V₄ K) : Matrix V₄ V₄ K) * spBlock ((h : GL V₄ K) : Matrix V₄ V₄ K)
    exact spBlock_mul (hGS h.2.1) (mulVec_spE_eq g) (mulVec_spE_eq h)

theorem coe_spBlockHom {G : Subgroup (GL V₄ K)} (hGS : G ≤ StatedSp 2 K) (g : lineStabE G) :
    ((spBlockHom hGS g : SL(2, K)) : Matrix (Fin 2) (Fin 2) K) =
      spBlock ((g : GL V₄ K) : Matrix V₄ V₄ K) :=
  rfl

theorem spE_ne_zero : (spE : V₄ → K) ≠ 0 := fun h => by
  simpa [spE] using congrFun h (Sum.inl 0)

theorem isHeisAt_smul_iff {z : V₄ → K} {l : K} (hl : l ≠ 0) {g : GL V₄ K} :
    IsHeisAt (l • z) g ↔ IsHeisAt z g := by
  constructor
  · rintro ⟨hS, hz, hv⟩
    refine ⟨hS, ?_, fun v hv' => ?_⟩
    · rw [mulVec_smul] at hz
      have := congrArg (fun w => l⁻¹ • w) hz
      simpa [smul_smul, inv_mul_cancel₀ hl] using this
    · obtain ⟨c, hc⟩ := hv v (by rw [map_smul, LinearMap.smul_apply, hv', smul_zero])
      exact ⟨c * l, by rw [hc, smul_smul]⟩
  · rintro ⟨hS, hz, hv⟩
    refine ⟨hS, by rw [mulVec_smul, hz], fun v hv' => ?_⟩
    obtain ⟨c, hc⟩ := hv v (by
      rw [map_smul, LinearMap.smul_apply, smul_eq_mul] at hv'
      exact (mul_eq_zero.mp hv').resolve_left hl)
    exact ⟨c * l⁻¹, by rw [hc, smul_smul, mul_assoc, inv_mul_cancel₀ hl, mul_one]⟩

theorem mulVec_inl_one_of_lineStab {g : GL V₄ K} {l : K}
    (hl : (g : Matrix V₄ V₄ K) *ᵥ spE = l • spE) {v : V₄ → K} (hv : v (Sum.inr 0) = 0) :
    ((g : Matrix V₄ V₄ K) *ᵥ v) (Sum.inl 1) =
      spBlock (g : Matrix V₄ V₄ K) 0 0 * v (Sum.inl 1) +
        spBlock (g : Matrix V₄ V₄ K) 0 1 * v (Sum.inr 1) := by
  have h0 := entry_eq_zero_of_mulVec_eq_smul hl (i := Sum.inl 1) (by decide)
  simp [Matrix.mulVec, dotProduct, Fintype.sum_sum_type, Fin.sum_univ_two, h0, hv, spBlock]

theorem mulVec_inr_one_of_lineStab {g : GL V₄ K} {l : K}
    (hl : (g : Matrix V₄ V₄ K) *ᵥ spE = l • spE) {v : V₄ → K} (hv : v (Sum.inr 0) = 0) :
    ((g : Matrix V₄ V₄ K) *ᵥ v) (Sum.inr 1) =
      spBlock (g : Matrix V₄ V₄ K) 1 0 * v (Sum.inl 1) +
        spBlock (g : Matrix V₄ V₄ K) 1 1 * v (Sum.inr 1) := by
  have h0 := entry_eq_zero_of_mulVec_eq_smul hl (i := Sum.inr 1) (by simp)
  simp [Matrix.mulVec, dotProduct, Fintype.sum_sum_type, Fin.sum_univ_two, h0, hv, spBlock]

theorem mulVec_inr_zero_of_lineStab {g : GL V₄ K} (hg : g ∈ StatedSp 2 K) {l : K}
    (hl : (g : Matrix V₄ V₄ K) *ᵥ spE = l • spE) {v : V₄ → K} (hv : v (Sum.inr 0) = 0) :
    ((g : Matrix V₄ V₄ K) *ᵥ v) (Sum.inr 0) = 0 := by
  have h1 := entry_inr_zero_eq_zero hg hl (j := Sum.inl 0) (by simp)
  have h2' := entry_inr_zero_eq_zero hg hl (j := Sum.inl 1) (by simp)
  have h3 := entry_inr_zero_eq_zero hg hl (j := Sum.inr 1) (by decide)
  simp [Matrix.mulVec, dotProduct, Fintype.sum_sum_type, Fin.sum_univ_two, h1, h2', h3, hv]

theorem heis_conj_param {m : GL V₄ K} (hm : m ∈ StatedSp 2 K) {l : K}
    (hl : (m : Matrix V₄ V₄ K) *ᵥ spE = l • spE)
    {l' : K} (hl' : (((m⁻¹ : GL V₄ K)) : Matrix V₄ V₄ K) *ᵥ spE = l' • spE)
    (α β γ : K) {v : V₄ → K} (hv : v (Sum.inr 0) = 0) :
    ((m * heis α β γ * m⁻¹ : GL V₄ K) : Matrix V₄ V₄ K) *ᵥ v =
      v + (l * (α * ((((m⁻¹ : GL V₄ K)) : Matrix V₄ V₄ K) *ᵥ v) (Sum.inl 1) +
        β * ((((m⁻¹ : GL V₄ K)) : Matrix V₄ V₄ K) *ᵥ v) (Sum.inr 1))) • spE := by
  have hw : ((((m⁻¹ : GL V₄ K)) : Matrix V₄ V₄ K) *ᵥ v) (Sum.inr 0) = 0 :=
    mulVec_inr_zero_of_lineStab (inv_mem hm) hl' hv
  rw [gl_mulVec_mul, gl_mulVec_mul, heis_mulVec_of_mem α β γ hw, mulVec_add, mulVec_smul,
    gl_mulVec_inv_mulVec, hl, smul_smul, mul_comm l]

theorem heisMat_inl_zero_inr_zero (α β γ : K) : heisMat α β γ (Sum.inl 0) (Sum.inr 0) = γ := by
  simp [heisMat, fromBlocks]

include h2 in
theorem exists_spTrans_mem_of_heis_mem {G : Subgroup (GL V₄ K)} (hGS : G ≤ StatedSp 2 K)
    (hsurj : Function.Surjective (spBlockHom hGS)) {h : GL V₄ K} (hhG : h ∈ G)
    (hh : IsHeisAt spE h) (hne : h ≠ 1) :
    ∃ a : V₄ → K, ∃ c : K, a ≠ 0 ∧ c ≠ 0 ∧ spTrans a c ∈ G := by
  classical
  obtain ⟨α, β, γ, rfl⟩ := exists_eq_heis_of_isHeisAt hh
  by_cases hab : α = 0 ∧ β = 0
  · obtain ⟨rfl, rfl⟩ := hab
    refine ⟨spE, -γ, spE_ne_zero, ?_, ?_⟩
    · intro hγ
      apply hne
      rw [neg_eq_zero] at hγ
      rw [hγ]
      exact Units.ext (by rw [coe_heis, heisMat_zero, Units.val_one])
    · rw [← heis_zero_zero]
      exact hhG
  set P : Matrix (Fin 2) (Fin 2) K := if α ≠ 0 then !![1, 1; 0, 1] else !![1, 0; 1, 1] with hP
  have hPdet : P.det = 1 := by
    by_cases hα : α ≠ 0 <;> simp [hP, hα, Matrix.det_fin_two_of]
  obtain ⟨A₀, hA₀⟩ : ∃ A₀ : SL(2, K), (A₀ : Matrix (Fin 2) (Fin 2) K) = P := ⟨⟨P, hPdet⟩, rfl⟩
  obtain ⟨m, hm⟩ := hsurj A₀⁻¹
  obtain ⟨hmG, l, hl⟩ := m.2
  have hmS := hGS hmG
  obtain ⟨-, l', hl'⟩ := ((lineStabE G).inv_mem m.2)
  have hl0 : l ≠ 0 := by
    have := entry_ne_zero_of_lineStabE m
    rwa [entry_inl_zero_of_mulVec_eq_smul hl] at this
  have hbinv : spBlock ((((m : GL V₄ K)⁻¹ : GL V₄ K)) : Matrix V₄ V₄ K) = P := by
    have h1 : spBlockHom hGS m⁻¹ = A₀ := by
      rw [map_inv, hm, inv_inv]
    have h3 := congrArg (fun A : SL(2, K) => (A : Matrix (Fin 2) (Fin 2) K)) h1
    rw [coe_spBlockHom, hA₀] at h3
    exact h3
  set h' := (m : GL V₄ K) * heis α β γ * (m : GL V₄ K)⁻¹ with hh'
  have hh'G : h' ∈ G := G.mul_mem (G.mul_mem hmG hhG) (G.inv_mem hmG)
  have hh'H : IsHeisAt spE h' := by
    have := (isHeisAt_heis α β γ).conj hmS
    rwa [hl, isHeisAt_smul_iff hl0] at this
  obtain ⟨α', β', γ', hh'eq⟩ := exists_eq_heis_of_isHeisAt hh'H
  have hpar : ∀ v : V₄ → K, v (Sum.inr 0) = 0 →
      l * (α * ((((m : GL V₄ K)⁻¹ : GL V₄ K) : Matrix V₄ V₄ K) *ᵥ v) (Sum.inl 1) +
        β * ((((m : GL V₄ K)⁻¹ : GL V₄ K) : Matrix V₄ V₄ K) *ᵥ v) (Sum.inr 1)) =
        α' * v (Sum.inl 1) + β' * v (Sum.inr 1) := by
    intro v hv
    have e1 := heis_conj_param hmS hl hl' α β γ hv
    have e2 := heis_mulVec_of_mem α' β' γ' hv
    rw [← hh'eq] at e2
    rw [hh'] at e2
    rw [e1] at e2
    have := congrFun e2 (Sum.inl 0)
    simpa [spE] using this
  have hv1 := hpar (Pi.single (Sum.inl 1) 1) (by simp)
  have hv3 := hpar (Pi.single (Sum.inr 1) 1) (by simp)
  rw [mulVec_inl_one_of_lineStab hl' (by simp), mulVec_inr_one_of_lineStab hl' (by simp),
    hbinv] at hv1 hv3
  simp at hv1 hv3
  have hnc : heis α β γ * h' ≠ h' * heis α β γ := by
    intro hc
    rw [hh'eq, heis_mul, heis_mul] at hc
    have := congrArg (fun g : GL V₄ K => (g : Matrix V₄ V₄ K) (Sum.inl 0) (Sum.inr 0)) hc
    simp only [coe_heis, heisMat_inl_zero_inr_zero] at this
    have hω : (2 : K) * (α * β' - α' * β) = 0 := by linear_combination this
    have hω' := (mul_eq_zero.mp hω).resolve_left h2
    by_cases hα : α ≠ 0
    · simp [hP, hα] at hv1 hv3
      rw [← hv1, ← hv3] at hω'
      have : l * α ^ 2 = 0 := by linear_combination hω'
      exact pow_ne_zero 2 hα ((mul_eq_zero.mp this).resolve_left hl0)
    · push Not at hα
      have hβ : β ≠ 0 := fun hβ => hab ⟨hα, hβ⟩
      simp [hP, hα] at hv1 hv3
      rw [hα, ← hv1, ← hv3] at hω'
      have : l * β ^ 2 = 0 := by linear_combination -hω'
      exact pow_ne_zero 2 hβ ((mul_eq_zero.mp this).resolve_left hl0)
  obtain ⟨c, hc0, hc⟩ := exists_commutator_eq_spTrans h2 spE_ne_zero (isHeisAt_heis α β γ)
    hh'H hnc
  refine ⟨spE, c, spE_ne_zero, hc0, ?_⟩
  rw [← hc]
  exact G.mul_mem (G.mul_mem (G.mul_mem hhG hh'G) (G.inv_mem hhG)) (G.inv_mem hh'G)

include h2 in
theorem exists_eigSp_eq_span_pair {j : GL V₄ K} (hj : j ∈ StatedSp 2 K) (hj2 : j * j = 1)
    (hj1 : j ≠ 1) (hjm : j ≠ -1) (he : spE ∈ eigSp (j : Matrix V₄ V₄ K) 1) :
    ∃ f ∈ eigSp (j : Matrix V₄ V₄ K) 1, spForm 2 K spE f = 1 ∧
      eigSp (j : Matrix V₄ V₄ K) 1 = Submodule.span K {spE, f} := by
  have hjj : (j : Matrix V₄ V₄ K) * j = 1 := by rw [← Units.val_mul, hj2, Units.val_one]
  obtain ⟨f₀, hf₀, hef₀⟩ : ∃ f₀ ∈ eigSp (j : Matrix V₄ V₄ K) 1, spForm 2 K spE f₀ ≠ 0 := by
    by_contra hcon
    push Not at hcon
    apply spE_ne_zero (K := K)
    apply eq_zero_of_forall_spForm
    intro x
    obtain ⟨h1, hm, hsum⟩ := mem_eig_add_mem_eig h2 hjj x
    rw [← LinearMap.BilinForm.IsAlt.neg_eq spForm_isAlt, hsum, map_add, hcon _ h1,
      spForm_eq_zero_of_eig h2 hj he hm, add_zero, neg_zero]
  set f := (spForm 2 K spE f₀)⁻¹ • f₀ with hf
  have hfE : f ∈ eigSp (j : Matrix V₄ V₄ K) 1 := Submodule.smul_mem _ _ hf₀
  have hef : spForm 2 K spE f = 1 := by
    rw [hf, map_smul, smul_eq_mul, inv_mul_cancel₀ hef₀]
  refine ⟨f, hfE, hef, ?_⟩
  symm
  apply Submodule.eq_of_le_of_finrank_eq
  · rw [Submodule.span_le]
    rintro x (rfl | rfl)
    · exact he
    · exact hfE
  · have hsum := finrank_eig_add_finrank_eig h2 hjj
    rw [finrank_eig_neg_one_eq_two h2 hj hj2 hj1 hjm] at hsum
    rw [finrank_span_pair (show spForm 2 K spE f ≠ 0 by rw [hef]; exact one_ne_zero)]
    omega

@[expose] def slNegOne : SL(2, K) := ⟨-1, by simp [Matrix.det_neg]⟩

@[expose] noncomputable def slDiag (a : K) (ha : a ≠ 0) : SL(2, K) :=
  ⟨!![a, 0; 0, a⁻¹], by simp [Matrix.det_fin_two_of, ha]⟩

@[expose] def slUpper (c : K) : SL(2, K) := ⟨!![1, c; 0, 1], by simp [Matrix.det_fin_two_of]⟩

theorem slNegOne_mul_comm (A : SL(2, K)) : slNegOne * A = A * slNegOne := by
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul]
  show (-1 : Matrix (Fin 2) (Fin 2) K) * A = A * (-1)
  simp

theorem slNegOne_mul_self : slNegOne * slNegOne = (1 : SL(2, K)) := by
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_one]
  show (-1 : Matrix (Fin 2) (Fin 2) K) * (-1) = 1
  simp

theorem slNegOne_ne_one (h2 : (2 : K) ≠ 0) : slNegOne ≠ (1 : SL(2, K)) := by
  intro h
  have := congrArg (fun A : SL(2, K) => (A : Matrix (Fin 2) (Fin 2) K) 0 0) h
  simp [slNegOne] at this
  apply h2
  linear_combination -this

theorem slUpper_ne_one : slUpper (1 : K) ≠ 1 := by
  intro h
  have := congrArg (fun A : SL(2, K) => (A : Matrix (Fin 2) (Fin 2) K) 0 1) h
  simp [slUpper] at this

theorem slDiag_comm_slUpper (a : K) (ha : a ≠ 0) (c : K) :
    slDiag a ha * slUpper c * (slDiag a ha)⁻¹ * (slUpper c)⁻¹ = slUpper ((a ^ 2 - 1) * c) := by
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul,
    Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_inv,
    Matrix.SpecialLinearGroup.coe_inv]
  show !![a, 0; 0, a⁻¹] * !![1, c; 0, 1] * adjugate !![a, 0; 0, a⁻¹] * adjugate !![1, c; 0, 1] =
    !![1, (a ^ 2 - 1) * c; 0, 1]
  rw [Matrix.adjugate_fin_two_of, Matrix.adjugate_fin_two_of]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, ha]
  ring

theorem exists_shear_of_commute {j s : GL V₄ K} (hs : s ∈ StatedSp 2 K)
    (hse : (s : Matrix V₄ V₄ K) *ᵥ spE = spE) (hsj : s * j = j * s) {f : V₄ → K}
    (hf : f ∈ eigSp (j : Matrix V₄ V₄ K) 1) (hef : spForm 2 K spE f = 1)
    (hspan : eigSp (j : Matrix V₄ V₄ K) 1 = Submodule.span K {spE, f}) :
    ∃ κ : K, (s : Matrix V₄ V₄ K) *ᵥ f = f + κ • spE := by
  have hsf : (s : Matrix V₄ V₄ K) *ᵥ f ∈ eigSp (j : Matrix V₄ V₄ K) 1 := by
    rw [mem_eigSp] at hf ⊢
    rw [Matrix.mulVec_mulVec, ← Units.val_mul, ← hsj, Units.val_mul, ← Matrix.mulVec_mulVec, hf,
      one_smul, one_smul]
  rw [hspan] at hsf
  obtain ⟨a, b, hab⟩ := Submodule.mem_span_pair.mp hsf
  have hB : spForm 2 K spE ((s : Matrix V₄ V₄ K) *ᵥ f) = 1 := by
    have := spForm_mulVec hs spE f
    rw [hse, hef] at this
    exact this
  rw [← hab] at hB
  simp only [map_add, map_smul, smul_eq_mul, spForm_self, mul_zero, zero_add, hef,
    mul_one] at hB
  refine ⟨a, ?_⟩
  rw [← hab, hB, one_smul, add_comm]

theorem inv_shear {g : GL V₄ K} {f : V₄ → K} {κ : K}
    (hge : (g : Matrix V₄ V₄ K) *ᵥ spE = spE) (hgf : (g : Matrix V₄ V₄ K) *ᵥ f = f + κ • spE) :
    ((g⁻¹ : GL V₄ K) : Matrix V₄ V₄ K) *ᵥ spE = spE ∧
      ((g⁻¹ : GL V₄ K) : Matrix V₄ V₄ K) *ᵥ f = f - κ • spE := by
  have h1 : ((g⁻¹ : GL V₄ K) : Matrix V₄ V₄ K) *ᵥ spE = spE := by
    conv_lhs => rw [← hge]
    rw [gl_inv_mulVec_mulVec]
  refine ⟨h1, ?_⟩
  have : (g : Matrix V₄ V₄ K) *ᵥ (f - κ • spE) = f := by
    rw [mulVec_sub, mulVec_smul, hgf, hge]
    abel
  conv_lhs => rw [← this]
  rw [gl_inv_mulVec_mulVec]

theorem commutator_fix_of_shear {s s' : GL V₄ K} {f : V₄ → K} {κ κ' : K}
    (hse : (s : Matrix V₄ V₄ K) *ᵥ spE = spE) (hs'e : (s' : Matrix V₄ V₄ K) *ᵥ spE = spE)
    (hsf : (s : Matrix V₄ V₄ K) *ᵥ f = f + κ • spE)
    (hs'f : (s' : Matrix V₄ V₄ K) *ᵥ f = f + κ' • spE) :
    ((s * s' * s⁻¹ * s'⁻¹ : GL V₄ K) : Matrix V₄ V₄ K) *ᵥ spE = spE ∧
      ((s * s' * s⁻¹ * s'⁻¹ : GL V₄ K) : Matrix V₄ V₄ K) *ᵥ f = f := by
  obtain ⟨h1, h2'⟩ := inv_shear hse hsf
  obtain ⟨h3, h4⟩ := inv_shear hs'e hs'f
  constructor
  · simp only [gl_mulVec_mul, h3, h1, hs'e, hse]
  · simp only [gl_mulVec_mul, h4, mulVec_sub, mulVec_add, mulVec_smul, h1, h2', hs'e, hs'f, hse,
      hsf]
    module

include h2 in
theorem sq_of_unipotent_block {j w : GL V₄ K} (hj : j ∈ StatedSp 2 K)
    (hjj : (j : Matrix V₄ V₄ K) * j = 1) (hwe : (w : Matrix V₄ V₄ K) *ᵥ spE = spE)
    (hwj : w * j = j * w) (he : spE ∈ eigSp (j : Matrix V₄ V₄ K) 1)
    (hfix : ∀ v ∈ eigSp (j : Matrix V₄ V₄ K) 1, (w : Matrix V₄ V₄ K) *ᵥ v = v)
    (hb : spBlock (w : Matrix V₄ V₄ K) = !![1, 1; 0, 1]) (v : V₄ → K) :
    (w : Matrix V₄ V₄ K) *ᵥ ((w : Matrix V₄ V₄ K) *ᵥ v - v) =
      (w : Matrix V₄ V₄ K) *ᵥ v - v := by
  have hwe' : (w : Matrix V₄ V₄ K) *ᵥ spE = (1 : K) • spE := by rw [one_smul]; exact hwe
  have hpres : ∀ x ∈ eigSp (j : Matrix V₄ V₄ K) (-1),
      (w : Matrix V₄ V₄ K) *ᵥ x ∈ eigSp (j : Matrix V₄ V₄ K) (-1) := by
    intro x hx
    rw [mem_eigSp] at hx ⊢
    rw [Matrix.mulVec_mulVec, ← Units.val_mul, ← hwj, Units.val_mul, ← Matrix.mulVec_mulVec, hx,
      mulVec_smul]
  have hperp : ∀ x ∈ eigSp (j : Matrix V₄ V₄ K) (-1), x (Sum.inr 0) = 0 := by
    intro x hx
    have := spForm_eq_zero_of_eig h2 hj he hx
    rwa [spForm_spE_left] at this
  have hb00 : spBlock (w : Matrix V₄ V₄ K) 0 0 = 1 := by rw [hb]; rfl
  have hb01 : spBlock (w : Matrix V₄ V₄ K) 0 1 = 1 := by rw [hb]; rfl
  have hb10 : spBlock (w : Matrix V₄ V₄ K) 1 0 = 0 := by rw [hb]; rfl
  have hb11 : spBlock (w : Matrix V₄ V₄ K) 1 1 = 1 := by rw [hb]; rfl
  have hneg : ∀ x ∈ eigSp (j : Matrix V₄ V₄ K) (-1),
      (w : Matrix V₄ V₄ K) *ᵥ ((w : Matrix V₄ V₄ K) *ᵥ x - x) =
        (w : Matrix V₄ V₄ K) *ᵥ x - x := by
    intro x hx
    set y := (w : Matrix V₄ V₄ K) *ᵥ x - x with hy
    have hyU : y ∈ eigSp (j : Matrix V₄ V₄ K) (-1) := Submodule.sub_mem _ (hpres x hx) hx
    have hx0 := hperp x hx
    have hy0 := hperp y hyU
    have hy1 : y (Sum.inl 1) = x (Sum.inr 1) := by
      rw [hy, Pi.sub_apply, mulVec_inl_one_of_lineStab hwe' hx0, hb00, hb01]
      ring
    have hy3 : y (Sum.inr 1) = 0 := by
      rw [hy, Pi.sub_apply, mulVec_inr_one_of_lineStab hwe' hx0, hb10, hb11]
      ring
    set z := (w : Matrix V₄ V₄ K) *ᵥ y - y with hz
    have hzU : z ∈ eigSp (j : Matrix V₄ V₄ K) (-1) := Submodule.sub_mem _ (hpres y hyU) hyU
    have hz1 : z (Sum.inl 1) = 0 := by
      rw [hz, Pi.sub_apply, mulVec_inl_one_of_lineStab hwe' hy0, hb00, hb01, hy3]
      ring
    have hz3 : z (Sum.inr 1) = 0 := by
      rw [hz, Pi.sub_apply, mulVec_inr_one_of_lineStab hwe' hy0, hb10, hb11, hy3]
      ring
    have hz2 : z (Sum.inr 0) = 0 := hperp z hzU
    have hzE : z = z (Sum.inl 0) • spE := by
      ext i
      rcases i with i | i <;> fin_cases i <;> simp [spE, hz1, hz2, hz3]
    have hz1' : z ∈ eigSp (j : Matrix V₄ V₄ K) 1 := by
      rw [hzE]
      exact Submodule.smul_mem _ _ he
    have hzbot : z ∈ eigSp (j : Matrix V₄ V₄ K) 1 ⊓ eigSp (j : Matrix V₄ V₄ K) (-1) :=
      ⟨hz1', hzU⟩
    rw [eig_inf_eig h2] at hzbot
    have hz0 : z = 0 := hzbot
    rw [hz, sub_eq_zero] at hz0
    exact hz0
  obtain ⟨h1, hm, hv⟩ := mem_eig_add_mem_eig h2 hjj v
  have hw1 := hfix _ h1
  have hw2 := hneg _ hm
  rw [hv, mulVec_add, hw1]
  rw [show (2 : K)⁻¹ • (v + (j : Matrix V₄ V₄ K) *ᵥ v) +
      (w : Matrix V₄ V₄ K) *ᵥ ((2 : K)⁻¹ • (v - (j : Matrix V₄ V₄ K) *ᵥ v)) -
      ((2 : K)⁻¹ • (v + (j : Matrix V₄ V₄ K) *ᵥ v) +
        (2 : K)⁻¹ • (v - (j : Matrix V₄ V₄ K) *ᵥ v)) =
      (w : Matrix V₄ V₄ K) *ᵥ ((2 : K)⁻¹ • (v - (j : Matrix V₄ V₄ K) *ᵥ v)) -
        (2 : K)⁻¹ • (v - (j : Matrix V₄ V₄ K) *ᵥ v) by abel, hw2]

include h2 in
theorem exists_spTrans_mem_of_kernel_trivial (hK : ∃ s : Finset K, s.card = 4)
    {G : Subgroup (GL V₄ K)} (hGS : G ≤ StatedSp 2 K)
    (hsurj : Function.Surjective (spBlockHom hGS))
    (hker : ∀ h : lineStabE G, scalarHomE G h = 1 → spBlockHom hGS h = 1 → h = 1) :
    ∃ a : V₄ → K, ∃ c : K, a ≠ 0 ∧ c ≠ 0 ∧ spTrans a c ∈ G := by
  have : Group.IsPerfect SL(2, K) := CFSG.LinearGroups.special_linear_dimension_two_perfect hK
  set S : Subgroup (lineStabE G) := commutator (lineStabE G) with hSdef
  have hscS : ∀ s ∈ S, scalarHomE G s = 1 := by
    intro s hs
    have hle : S ≤ (scalarHomE G).ker := by
      rw [hSdef, commutator_def, Subgroup.commutator_le]
      intro a _ b _
      rw [MonoidHom.mem_ker, map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
      exact mul_comm _ _
    exact hle hs
  have hinj : ∀ s ∈ S, ∀ s' ∈ S, spBlockHom hGS s = spBlockHom hGS s' → s = s' := by
    intro s hs s' hs' h
    have := hker (s * s'⁻¹) (by rw [map_mul, map_inv, hscS s hs, hscS s' hs', inv_one, mul_one])
      (by rw [map_mul, map_inv, h, mul_inv_cancel])
    exact mul_inv_eq_one.mp this
  have honto : ∀ A : SL(2, K), ∃ s ∈ S, spBlockHom hGS s = A := by
    intro A
    have hmap : S.map (spBlockHom hGS) = ⊤ := by
      rw [hSdef, commutator_def, Subgroup.map_commutator, ← MonoidHom.range_eq_map,
        MonoidHom.range_eq_top.mpr hsurj, ← commutator_def]
      exact Group.IsPerfect.commutator_eq_top
    have hA : A ∈ S.map (spBlockHom hGS) := hmap ▸ Subgroup.mem_top A
    obtain ⟨s, hs, rfl⟩ := hA
    exact ⟨s, hs, rfl⟩
  have hfixe : ∀ s ∈ S, ((s : GL V₄ K) : Matrix V₄ V₄ K) *ᵥ spE = spE := by
    intro s hs
    have h := mulVec_spE_eq s
    rw [← scalarHomE_apply, hscS s hs, Units.val_one, one_smul] at h
    exact h
  obtain ⟨j, hjS, hjb⟩ := honto slNegOne
  have hjj : j * j = 1 := hinj _ (S.mul_mem hjS hjS) _ S.one_mem (by
    rw [map_mul, hjb, map_one, slNegOne_mul_self])
  have hcomm : ∀ s ∈ S, j * s = s * j := fun s hs =>
    hinj _ (S.mul_mem hjS hs) _ (S.mul_mem hs hjS) (by
      rw [map_mul, map_mul, hjb, slNegOne_mul_comm])
  set J : GL V₄ K := (j : GL V₄ K) with hJdef
  have hJS : J ∈ StatedSp 2 K := hGS j.2.1
  have hJe : (J : Matrix V₄ V₄ K) *ᵥ spE = spE := hfixe j hjS
  have hJJ : J * J = 1 := by
    have := congrArg (fun x : lineStabE G => (x : GL V₄ K)) hjj
    simpa using this
  have hJJm : (J : Matrix V₄ V₄ K) * J = 1 := by rw [← Units.val_mul, hJJ, Units.val_one]
  have hJ1 : J ≠ 1 := by
    intro h
    have hj1 : j = 1 := Subtype.ext h
    rw [hj1, map_one] at hjb
    exact slNegOne_ne_one h2 hjb.symm
  have hJm : J ≠ -1 := by
    intro h
    rw [h, Units.val_neg, Units.val_one, Matrix.neg_mulVec, Matrix.one_mulVec] at hJe
    apply spE_ne_zero (K := K)
    have h2e : (2 : K) • (spE : V₄ → K) = 0 := by
      rw [two_smul]
      nth_rewrite 1 [← hJe]
      exact neg_add_cancel _
    exact (smul_eq_zero.mp h2e).resolve_left h2
  have hJcomm : ∀ s ∈ S, (s : GL V₄ K) * J = J * (s : GL V₄ K) := by
    intro s hs
    have := congrArg (fun x : lineStabE G => (x : GL V₄ K)) (hcomm s hs)
    simpa using this.symm
  have he : spE ∈ eigSp (J : Matrix V₄ V₄ K) 1 := by rw [mem_eigSp, one_smul]; exact hJe
  obtain ⟨f, hf, hef, hspan⟩ := exists_eigSp_eq_span_pair h2 hJS hJJ hJ1 hJm he
  have hshear : ∀ s ∈ S, ∃ κ : K, ((s : GL V₄ K) : Matrix V₄ V₄ K) *ᵥ f = f + κ • spE :=
    fun s hs => exists_shear_of_commute (hGS s.2.1) (hfixe s hs) (hJcomm s hs) hf hef hspan
  obtain ⟨a, ha0, ha1⟩ : ∃ a : K, a ≠ 0 ∧ a ^ 2 - 1 ≠ 0 := by
    classical
    obtain ⟨s, hs⟩ := hK
    obtain ⟨a, -, ha⟩ := Finset.exists_mem_notMem_of_card_lt_card
      (s := ({0, 1, -1} : Finset K)) (t := s) (by
        rw [hs]
        calc ({0, 1, -1} : Finset K).card ≤ 3 := Finset.card_le_three
          _ < 4 := by norm_num)
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at ha
    refine ⟨a, ha.1, ?_⟩
    intro h
    have : (a - 1) * (a + 1) = 0 := by linear_combination h
    rcases mul_eq_zero.mp this with h' | h'
    · exact ha.2.1 (by linear_combination h')
    · exact ha.2.2 (by linear_combination h')
  obtain ⟨d', hd'S, hd'b⟩ := honto (slDiag a ha0)
  obtain ⟨u', hu'S, hu'b⟩ := honto (slUpper (a ^ 2 - 1)⁻¹)
  set w := d' * u' * d'⁻¹ * u'⁻¹ with hwdef
  have hwS : w ∈ S :=
    S.mul_mem (S.mul_mem (S.mul_mem hd'S hu'S) (S.inv_mem hd'S)) (S.inv_mem hu'S)
  have hwb : spBlockHom hGS w = slUpper 1 := by
    rw [hwdef, map_mul, map_mul, map_mul, map_inv, map_inv, hd'b, hu'b, slDiag_comm_slUpper,
      mul_inv_cancel₀ ha1]
  set W : GL V₄ K := (w : GL V₄ K) with hWdef
  have hWG : W ∈ G := w.2.1
  have hWS : W ∈ StatedSp 2 K := hGS hWG
  have hWe : (W : Matrix V₄ V₄ K) *ᵥ spE = spE := hfixe w hwS
  have hWexp : W = (d' : GL V₄ K) * (u' : GL V₄ K) * (d' : GL V₄ K)⁻¹ * (u' : GL V₄ K)⁻¹ := by
    simp [hWdef, hwdef]
  obtain ⟨κ, hκ⟩ := hshear d' hd'S
  obtain ⟨κ', hκ'⟩ := hshear u' hu'S
  have hWf : (W : Matrix V₄ V₄ K) *ᵥ f = f := by
    rw [hWexp]
    exact (commutator_fix_of_shear (hfixe d' hd'S) (hfixe u' hu'S) hκ hκ').2
  have hWfix : ∀ v ∈ eigSp (J : Matrix V₄ V₄ K) 1, (W : Matrix V₄ V₄ K) *ᵥ v = v := by
    intro v hv
    rw [hspan] at hv
    obtain ⟨α, β, rfl⟩ := Submodule.mem_span_pair.mp hv
    rw [mulVec_add, mulVec_smul, mulVec_smul, hWe, hWf]
  have hWb : spBlock (W : Matrix V₄ V₄ K) = !![1, 1; 0, 1] := by
    have := congrArg (fun A : SL(2, K) => (A : Matrix (Fin 2) (Fin 2) K)) hwb
    rw [coe_spBlockHom] at this
    exact this
  have hWsq := sq_of_unipotent_block h2 hJS hJJm hWe (hJcomm w hwS) he hWfix hWb
  have hW1 : W ≠ 1 := by
    intro h
    have hw1 : w = 1 := Subtype.ext h
    rw [hw1, map_one] at hwb
    exact slUpper_ne_one hwb.symm
  obtain ⟨b, c, hb0, hc0, hbc⟩ := eq_spTrans_of_fix_of_sq h2 hJS hJJ hJ1 hJm hWS hWfix hWsq hW1
  exact ⟨b, c, hb0, hc0, hbc ▸ hWG⟩

include h2 in
theorem exists_spTrans_mem_of_spBlock_surjective (hK : ∃ s : Finset K, s.card = 4)
    {G : Subgroup (GL V₄ K)} (hGS : G ≤ StatedSp 2 K)
    (hsurj : Function.Surjective (spBlockHom hGS)) :
    ∃ a : V₄ → K, ∃ c : K, a ≠ 0 ∧ c ≠ 0 ∧ spTrans a c ∈ G := by
  by_cases hker : ∀ h : lineStabE G, scalarHomE G h = 1 → spBlockHom hGS h = 1 → h = 1
  · exact exists_spTrans_mem_of_kernel_trivial h2 hK hGS hsurj hker
  push Not at hker
  obtain ⟨h, hsc, hb, hne⟩ := hker
  have hS := hGS h.2.1
  have he : ((h : GL V₄ K) : Matrix V₄ V₄ K) *ᵥ spE = spE := by
    have h' := mulVec_spE_eq h
    rw [← scalarHomE_apply, hsc, Units.val_one, one_smul] at h'
    exact h'
  have hblock : spBlock ((h : GL V₄ K) : Matrix V₄ V₄ K) = 1 := by
    have := congrArg (fun A : SL(2, K) => (A : Matrix (Fin 2) (Fin 2) K)) hb
    rw [coe_spBlockHom] at this
    simpa using this
  have hH : IsHeisAt spE (h : GL V₄ K) := by
    rw [eq_heis_of_fix hS he hblock]
    exact isHeisAt_heis _ _ _
  exact exists_spTrans_mem_of_heis_mem h2 hGS hsurj h.2.1 hH fun h1 => hne (Subtype.ext h1)

theorem exists_spTrans_mem_of_unipotent_blocks {p : ℕ} [Fact p.Prime] (hp5 : 5 ≤ p)
    {G : Subgroup (GL V₄ (ZMod p))} (hGS : G ≤ StatedSp 2 (ZMod p)) (g g' : lineStabE G)
    (hg : spBlockHom hGS g ^ p = 1) (hg1 : spBlockHom hGS g ≠ 1)
    (hg' : spBlockHom hGS g' ^ p = 1)
    (hgg' : spBlockHom hGS g' ∉ Subgroup.zpowers (spBlockHom hGS g)) :
    ∃ a : V₄ → ZMod p, ∃ c : ZMod p, a ≠ 0 ∧ c ≠ 0 ∧ spTrans a c ∈ G := by
  have h2 : (2 : ZMod p) ≠ 0 := by
    intro h
    have : ((2 : ℕ) : ZMod p) = 0 := by exact_mod_cast h
    rw [ZMod.natCast_eq_zero_iff] at this
    have := Nat.le_of_dvd (by norm_num) this
    omega
  have hK : ∃ s : Finset (ZMod p), s.card = 4 := by
    refine ⟨Finset.image (fun n : Fin 4 => ((n : ℕ) : ZMod p)) Finset.univ, ?_⟩
    rw [Finset.card_image_of_injective _ (fun a b hab => ?_), Finset.card_univ, Fintype.card_fin]
    have h' : ((a : ℕ) : ZMod p) = ((b : ℕ) : ZMod p) := hab
    rw [ZMod.natCast_eq_natCast_iff', Nat.mod_eq_of_lt (by omega),
      Nat.mod_eq_of_lt (by omega)] at h'
    exact Fin.ext h'
  refine exists_spTrans_mem_of_spBlock_surjective h2 hK hGS ?_
  set T : SL(2, ZMod p) →* GL (Fin 2) (ZMod p) := Matrix.SpecialLinearGroup.toGL with hT
  have hTinj : Function.Injective T := Matrix.SpecialLinearGroup.toGL_injective
  have hcl := closure_pair_eq_statedSL (T (spBlockHom hGS g)) (T (spBlockHom hGS g'))
    (by rw [← map_pow, hg, map_one]) (fun h => hg1 (hTinj (by rw [h, map_one])))
    (by rw [← map_pow, hg', map_one]) (by
      rintro ⟨k, hk⟩
      apply hgg'
      refine ⟨k, hTinj ?_⟩
      rw [map_zpow]
      exact hk)
  intro A
  have hA : T A ∈ Subgroup.closure {T (spBlockHom hGS g), T (spBlockHom hGS g')} := by
    rw [hcl, CFSG.Assembly.LowTwoRank.statedSL_eq_range_toGL]
    exact ⟨A, rfl⟩
  have hle : Subgroup.closure {T (spBlockHom hGS g), T (spBlockHom hGS g')} ≤
      (((spBlockHom hGS).range).map T) := by
    rw [Subgroup.closure_le]
    rintro x (rfl | rfl)
    · exact ⟨_, ⟨g, rfl⟩, rfl⟩
    · exact ⟨_, ⟨g', rfl⟩, rfl⟩
  obtain ⟨B, ⟨b, rfl⟩, hB⟩ := hle hA
  exact ⟨b, hTinj hB⟩

end CFSG.RankThree.SubgroupLists
