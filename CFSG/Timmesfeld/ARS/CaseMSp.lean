module

public import CFSG.Timmesfeld.ARS.Sec12Frame

public section

namespace CFSG.Timmesfeld.ARS

open Matrix CFSG.Assembly.LowTwoRank CFSG.LieType.Universal CFSG.LieType.Universal.Symplectic

namespace CaseM

variable {n : ℕ} {F : Type} [Field F]
abbrev spGram (n : ℕ) (F : Type) [Field F] : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F :=
  fromBlocks 0 1 (-1) 0

abbrev spForm (u v : Fin n ⊕ Fin n → F) : F := u ⬝ᵥ (spGram n F *ᵥ v)

abbrev spNil (v : Fin n ⊕ Fin n → F) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F :=
  vecMulVec v (v ᵥ* spGram n F)

abbrev spTrans (v : Fin n ⊕ Fin n → F) (c : F) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F :=
  1 + c • spNil v

theorem spGram_transpose : (spGram n F)ᵀ = - spGram n F := by
  simp [fromBlocks_transpose, fromBlocks_neg]

theorem spGram_mul_self : spGram n F * spGram n F = -1 := by
  simp [fromBlocks_multiply, fromBlocks_neg, ← fromBlocks_one]

theorem spForm_comm (u v : Fin n ⊕ Fin n → F) : spForm v u = - spForm u v := by
  rw [spForm, spForm, dotProduct_mulVec, dotProduct_comm, ← vecMul_transpose, spGram_transpose,
    vecMul_neg]
  simp

theorem spNil_mul_spNil (v w : Fin n ⊕ Fin n → F) :
    spNil v * spNil w = spForm v w • vecMulVec v (w ᵥ* spGram n F) := by
  rw [spNil, spNil, vecMulVec_mul_vecMulVec, ← dotProduct_mulVec]
  ext a b
  simp [vecMulVec_apply, mul_left_comm]

theorem spTrans_commute_of_spForm_eq_zero {v w : Fin n ⊕ Fin n → F} (h : spForm v w = 0)
    (a b : F) : spTrans v a * spTrans w b = spTrans w b * spTrans v a := by
  have h' : spForm w v = 0 := by rw [spForm_comm, h, neg_zero]
  simp only [spTrans, add_mul, mul_add, one_mul, mul_one, smul_mul_smul, spNil_mul_spNil, h, h',
    zero_smul, smul_zero, add_zero]
  abel

theorem vecMul_spGram_ne_zero {v : Fin n ⊕ Fin n → F} (hv : v ≠ 0) : v ᵥ* spGram n F ≠ 0 := by
  intro h
  apply hv
  have : v ᵥ* spGram n F ᵥ* spGram n F = 0 := by rw [h, zero_vecMul]
  rw [vecMul_vecMul, spGram_mul_self, vecMul_neg, vecMul_one, neg_eq_zero] at this
  exact this

theorem spForm_eq_zero_of_commute {v w : Fin n ⊕ Fin n → F} (hv : v ≠ 0)
    (h : spTrans v 1 * spTrans w 1 = spTrans w 1 * spTrans v 1) :
    spForm v w = 0 ∨ ∃ l : F, w = l • v := by
  by_contra hc
  push Not at hc
  obtain ⟨hB, hprop⟩ := hc
  have hN : spNil v * spNil w = spNil w * spNil v := by
    simp only [spTrans, one_smul, add_mul, mul_add, one_mul, mul_one] at h
    have := congrArg (fun M => M - 1 - spNil v - spNil w) h
    convert this using 1 <;> abel
  rw [spNil_mul_spNil, spNil_mul_spNil, spForm_comm v w] at hN
  have hvJ := vecMul_spGram_ne_zero hv
  obtain ⟨b, hb⟩ := Function.ne_iff.1 hvJ
  have hb' : (v ᵥ* spGram n F) b ≠ 0 := by simpa using hb
  refine hprop (-(w ᵥ* spGram n F) b / (v ᵥ* spGram n F) b) ?_
  ext a
  have hab := congrFun (congrFun hN a) b
  simp only [Matrix.smul_apply, vecMulVec_apply, smul_eq_mul] at hab
  have hab' : v a * (w ᵥ* spGram n F) b = -(w a * (v ᵥ* spGram n F) b) := by
    have := mul_left_cancel₀ hB (by rw [hab]; ring : spForm v w * (v a * (w ᵥ* spGram n F) b) =
      spForm v w * (-(w a * (v ᵥ* spGram n F) b)))
    exact this
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [div_mul_eq_mul_div, eq_div_iff hb']
  linear_combination hab'



theorem spForm_self (u : Fin n ⊕ Fin n → F) : spForm u u = 0 := by
  simp [spForm, dotProduct, Fintype.sum_sum_type, mulVec, fromBlocks, Matrix.one_apply,
    mul_comm]

theorem mat_transpose_mul (x : StatedSp n F) :
    (SpExtras.mat n F x)ᵀ * spGram n F * SpExtras.mat n F x = spGram n F := by
  have hx : (x : GL (Fin n ⊕ Fin n) F) ∈ TauCeti.GLSymplectic (Fin n) F := by
    rw [← CFSG.ClassicalGroups.Symplectic.statedSp_eq_GLSymplectic]
    exact x.2
  exact (CFSG.ClassicalGroups.Symplectic.blueprintGram_iff_mem_symplecticGroup _).2
    (TauCeti.GLSymplectic.mem_iff_mem_symplecticGroup.1 hx)

theorem mat_mul_spNil (x : StatedSp n F) (v : Fin n ⊕ Fin n → F) :
    SpExtras.mat n F x * spNil v = spNil (SpExtras.mat n F x *ᵥ v) * SpExtras.mat n F x := by
  rw [spNil, spNil, mul_vecMulVec, vecMulVec_mul, ← vecMul_transpose, vecMul_vecMul,
    vecMul_vecMul, ← Matrix.mul_assoc, mat_transpose_mul]

theorem mat_conj_of_mat_eq {x : StatedSp n F} {v : Fin n ⊕ Fin n → F} {c : F}
    (hx : SpExtras.mat n F x = spTrans v c) (g : StatedSp n F) :
    SpExtras.mat n F (g * x * g⁻¹) = spTrans (SpExtras.mat n F g *ᵥ v) c := by
  have h1 : SpExtras.mat n F g * spTrans v c =
      spTrans (SpExtras.mat n F g *ᵥ v) c * SpExtras.mat n F g := by
    rw [spTrans, spTrans, Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, Matrix.one_mul,
      Matrix.mul_smul, Matrix.smul_mul, mat_mul_spNil]
  rw [map_mul, map_mul, hx, h1, Matrix.mul_assoc, ← map_mul, mul_inv_cancel, map_one,
    Matrix.mul_one]

theorem spNil_inl (i : Fin n) :
    spNil (Pi.single (Sum.inl i) 1 : Fin n ⊕ Fin n → F) = single (.inl i) (.inr i) 1 := by
  ext a b
  rcases a with a | a <;> rcases b with b | b <;>
    simp [vecMulVec_apply, Pi.single_apply, Matrix.single_apply, vecMul, dotProduct,
      fromBlocks, Matrix.one_apply, eq_comm]
  split_ifs <;> aesop

theorem spNil_inr (i : Fin n) :
    spNil (Pi.single (Sum.inr i) 1 : Fin n ⊕ Fin n → F) = -single (.inr i) (.inl i) 1 := by
  ext a b
  rcases a with a | a <;> rcases b with b | b <;>
    simp [vecMulVec_apply, Pi.single_apply, Matrix.single_apply, vecMul, dotProduct,
      fromBlocks, Matrix.one_apply, eq_comm]
  split_ifs <;> aesop

theorem mem_rootGroup_pos_iff {i : Fin n} {γ : Fin n → ℤ} (hγ : toStd n γ = 2 • Pi.single i 1)
    (x : StatedSp n F) : x ∈ Symplectic.rootGroup n F γ ↔
      ∃ c, SpExtras.mat n F x = spTrans (Pi.single (Sum.inl i) 1) c := by
  have hr : stdVec (TauCeti.GLSymplecticFin.RootSubgroupIndex.positiveLong i) = toStd n γ :=
    hγ.symm
  rw [SpExtras.mem_rootGroup_iff hr]
  constructor
  · rintro ⟨c, rfl⟩
    exact ⟨c, by rw [SpExtras.mat_elt, spTrans, spNil_inl]; rfl⟩
  · rintro ⟨c, hc⟩
    refine ⟨c, SpExtras.mat_injective ?_⟩
    rw [hc, SpExtras.mat_elt, spTrans, spNil_inl]
    rfl

theorem mem_rootGroup_neg_iff {i : Fin n} {γ : Fin n → ℤ}
    (hγ : toStd n γ = -(2 • Pi.single i 1)) (x : StatedSp n F) : x ∈ Symplectic.rootGroup n F γ ↔
      ∃ c, SpExtras.mat n F x = spTrans (Pi.single (Sum.inr i) 1) c := by
  have hr : stdVec (TauCeti.GLSymplecticFin.RootSubgroupIndex.negativeLong i) = toStd n γ :=
    hγ.symm
  rw [SpExtras.mem_rootGroup_iff hr]
  constructor
  · rintro ⟨c, rfl⟩
    refine ⟨-c, ?_⟩
    rw [SpExtras.mat_elt, spTrans, spNil_inr, smul_neg, neg_smul, neg_neg]
    rfl
  · rintro ⟨c, hc⟩
    refine ⟨-c, SpExtras.mat_injective ?_⟩
    rw [hc, SpExtras.mat_elt, spTrans, spNil_inr, smul_neg, neg_smul]
    rfl



@[expose] def IsTransGroup (v : Fin n ⊕ Fin n → F) (X : Subgroup (StatedSp n F)) : Prop :=
  (∀ x, x ∈ X ↔ ∃ c, SpExtras.mat n F x = spTrans v c) ∧
    ∀ c, ∃ x : StatedSp n F, SpExtras.mat n F x = spTrans v c

theorem IsTransGroup.eq {v : Fin n ⊕ Fin n → F} {X Y : Subgroup (StatedSp n F)}
    (hX : IsTransGroup v X) (hY : IsTransGroup v Y) : X = Y := by
  ext x
  rw [hX.1, hY.1]

theorem spTrans_smul (v : Fin n ⊕ Fin n → F) (l c : F) :
    spTrans (l • v) c = spTrans v (l * l * c) := by
  simp only [spTrans, spNil, smul_vecMul, vecMulVec_smul, smul_vecMulVec, smul_smul]
  ring_nf

theorem IsTransGroup.of_smul {v : Fin n ⊕ Fin n → F} {l : F} (hl : l ≠ 0)
    {X : Subgroup (StatedSp n F)} (h : IsTransGroup (l • v) X) : IsTransGroup v X := by
  have hll : l * l ≠ 0 := mul_ne_zero hl hl
  refine ⟨fun x => ?_, fun c => ?_⟩
  · rw [h.1]
    constructor
    · rintro ⟨c, hc⟩
      exact ⟨l * l * c, by rw [hc, spTrans_smul]⟩
    · rintro ⟨c, hc⟩
      refine ⟨(l * l)⁻¹ * c, ?_⟩
      rw [hc, spTrans_smul, ← mul_assoc, mul_inv_cancel₀ hll, one_mul]
  · obtain ⟨x, hx⟩ := h.2 ((l * l)⁻¹ * c)
    exact ⟨x, by rw [hx, spTrans_smul, ← mul_assoc, mul_inv_cancel₀ hll, one_mul]⟩

theorem IsTransGroup.conjSub {v : Fin n ⊕ Fin n → F} {X : Subgroup (StatedSp n F)}
    (h : IsTransGroup v X) (g : StatedSp n F) :
    IsTransGroup (SpExtras.mat n F g *ᵥ v) (CFSG.Timmesfeld.ARS.conjSub X g) := by
  refine ⟨fun x => ?_, fun c => ?_⟩
  · rw [mem_conjSub, h.1]
    constructor
    · rintro ⟨c, hc⟩
      refine ⟨c, ?_⟩
      have := mat_conj_of_mat_eq hc g
      rwa [show g * (g⁻¹ * x * g) * g⁻¹ = x by group] at this
    · rintro ⟨c, hc⟩
      refine ⟨c, ?_⟩
      have := mat_conj_of_mat_eq hc g⁻¹
      rwa [show g⁻¹ * x * g⁻¹⁻¹ = g⁻¹ * x * g by group, mulVec_mulVec, ← map_mul,
        inv_mul_cancel, map_one, one_mulVec] at this
  · obtain ⟨x, hx⟩ := h.2 c
    exact ⟨g * x * g⁻¹, mat_conj_of_mat_eq hx g⟩

theorem IsTransGroup.commuting {v w : Fin n ⊕ Fin n → F} {X Y : Subgroup (StatedSp n F)}
    (hX : IsTransGroup v X) (hY : IsTransGroup w Y) (h : spForm v w = 0) :
    CFSG.Timmesfeld.ARS.Commuting X Y := by
  intro x hx y hy
  obtain ⟨a, ha⟩ := (hX.1 x).1 hx
  obtain ⟨b, hb⟩ := (hY.1 y).1 hy
  apply SpExtras.mat_injective
  rw [map_mul, map_mul, ha, hb, spTrans_commute_of_spForm_eq_zero h]

theorem IsTransGroup.spForm_eq_zero {v w : Fin n ⊕ Fin n → F} {X Y : Subgroup (StatedSp n F)}
    (hX : IsTransGroup v X) (hY : IsTransGroup w Y) (hv : v ≠ 0)
    (hc : CFSG.Timmesfeld.ARS.Commuting X Y) :
    spForm v w = 0 ∨ ∃ l : F, w = l • v := by
  obtain ⟨x, hx⟩ := hX.2 1
  obtain ⟨y, hy⟩ := hY.2 1
  refine spForm_eq_zero_of_commute hv ?_
  have := congrArg (SpExtras.mat n F) (hc x ((hX.1 x).2 ⟨1, hx⟩) y ((hY.1 y).2 ⟨1, hy⟩)).eq
  rwa [map_mul, map_mul, hx, hy] at this



abbrev colMat (p q : Fin n → Fin n ⊕ Fin n → F) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F :=
  Matrix.of fun a x => Sum.elim (fun i => p i a) (fun i => q i a) x

theorem colMat_mulVec_inl (p q : Fin n → Fin n ⊕ Fin n → F) (i : Fin n) :
    colMat p q *ᵥ Pi.single (Sum.inl i) 1 = p i := by
  ext a
  simp [colMat, mulVec, dotProduct, Pi.single_apply]

theorem colMat_mulVec_inr (p q : Fin n → Fin n ⊕ Fin n → F) (i : Fin n) :
    colMat p q *ᵥ Pi.single (Sum.inr i) 1 = q i := by
  ext a
  simp [colMat, mulVec, dotProduct, Pi.single_apply]

theorem colMat_gram (p q : Fin n → Fin n ⊕ Fin n → F) (x y : Fin n ⊕ Fin n) :
    ((colMat p q)ᵀ * spGram n F * colMat p q) x y =
      spForm (Sum.elim p q x) (Sum.elim p q y) := by
  rw [Matrix.mul_assoc, Matrix.mul_apply]
  simp only [spForm, dotProduct, mulVec, Matrix.mul_apply, Matrix.transpose_apply]
  rcases x with i | i <;> rcases y with j | j <;>
    simp [colMat, Finset.mul_sum]

theorem exists_mem_statedSp_mulVec {p q : Fin n → Fin n ⊕ Fin n → F}
    (hpp : ∀ i j, spForm (p i) (p j) = 0) (hqq : ∀ i j, spForm (q i) (q j) = 0)
    (hpq : ∀ i j, spForm (p i) (q j) = if i = j then 1 else 0) :
    ∃ g : StatedSp n F, ∀ i, SpExtras.mat n F g *ᵥ Pi.single (Sum.inl i) 1 = p i ∧
      SpExtras.mat n F g *ᵥ Pi.single (Sum.inr i) 1 = q i := by
  have hqp : ∀ i j, spForm (q i) (p j) = -(if j = i then 1 else 0) := fun i j => by
    rw [spForm_comm, hpq]
  have hgram : (colMat p q)ᵀ * spGram n F * colMat p q = spGram n F := by
    ext x y
    rw [colMat_gram]
    rcases x with i | i <;> rcases y with j | j
    · simp [hpp]
    · simp [hpq, Matrix.one_apply]
    · simp [hqp, Matrix.one_apply, eq_comm]
    · simp [hqq]
  have hdet : (colMat p q).det ≠ 0 := by
    have hinv : (-(spGram n F * (colMat p q)ᵀ * spGram n F)) * colMat p q = 1 := by
      rw [Matrix.neg_mul, Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc (colMat p q)ᵀ,
        hgram, spGram_mul_self, neg_neg]
    exact (isUnit_det_of_left_inverse hinv).ne_zero
  let g0 : GL (Fin n ⊕ Fin n) F := Matrix.GeneralLinearGroup.mkOfDetNeZero _ hdet
  have hg0 : g0 ∈ StatedSp n F := by
    rw [CFSG.ClassicalGroups.Symplectic.statedSp_eq_GLSymplectic,
      TauCeti.GLSymplectic.mem_iff_mem_symplecticGroup,
      ← CFSG.ClassicalGroups.Symplectic.blueprintGram_iff_mem_symplecticGroup]
    exact hgram
  refine ⟨⟨g0, hg0⟩, fun i => ⟨?_, ?_⟩⟩
  · exact colMat_mulVec_inl p q i
  · exact colMat_mulVec_inr p q i



abbrev longC3 : Fin 3 → Fin 3 → ℤ := ![![2, 2, 1], ![0, 2, 1], ![0, 0, 1]]

theorem toStd_longC3 (i : Fin 3) : toStd 3 (longC3 i) = 2 • Pi.single i 1 := by
  ext a
  fin_cases i <;> fin_cases a <;> simp [toStd]

theorem toStd_neg_longC3 (i : Fin 3) : toStd 3 (-longC3 i) = -(2 • Pi.single i 1) := by
  rw [SpExtras.toStd_neg', toStd_longC3]

theorem longC3_two : longC3 2 = Pi.single 2 1 := by
  ext a; fin_cases a <;> rfl

theorem isTransGroup_pos (i : Fin 3) :
    IsTransGroup (Pi.single (Sum.inl i) 1) (Symplectic.rootGroup 3 F (longC3 i)) := by
  refine ⟨mem_rootGroup_pos_iff (toStd_longC3 i), fun c => ?_⟩
  exact ⟨SpExtras.elt (TauCeti.GLSymplecticFin.RootSubgroupIndex.positiveLong i) c, by
    rw [SpExtras.mat_elt, spTrans, spNil_inl]; rfl⟩

theorem isTransGroup_neg (i : Fin 3) :
    IsTransGroup (Pi.single (Sum.inr i) 1) (Symplectic.rootGroup 3 F (-longC3 i)) := by
  refine ⟨mem_rootGroup_neg_iff (toStd_neg_longC3 i), fun c => ?_⟩
  exact ⟨SpExtras.elt (TauCeti.GLSymplecticFin.RootSubgroupIndex.negativeLong i) (-c), by
    rw [SpExtras.mat_elt, spTrans, spNil_inr, smul_neg, neg_smul]; rfl⟩

theorem commuting_map_iff {G : Type*} [Group G] {K : Type*} [Group K] {Φ : K →* G}
    (hΦ : Function.Injective Φ) {X Y : Subgroup K} :
    Commuting (X.map Φ) (Y.map Φ) ↔ Commuting X Y := by
  constructor
  · intro h x hx y hy
    exact hΦ (by rw [map_mul, map_mul]; exact h _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩)
  · rintro h _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    exact (h x hx y hy).map Φ

theorem mat_mulVec_ne_zero (g : StatedSp 3 F) {v : Fin 3 ⊕ Fin 3 → F} (hv : v ≠ 0) :
    SpExtras.mat 3 F g *ᵥ v ≠ 0 := by
  intro h
  apply hv
  have := congrArg (SpExtras.mat 3 F g⁻¹ *ᵥ ·) h
  simp only [mulVec_mulVec, ← map_mul, inv_mul_cancel, map_one, one_mulVec, mulVec_zero] at this
  exact this

theorem spForm_smul_right (u v : Fin 3 ⊕ Fin 3 → F) (l : F) :
    spForm u (l • v) = l * spForm u v := by
  simp [spForm, mulVec_smul, dotProduct_smul]

theorem spForm_smul_left (u v : Fin 3 ⊕ Fin 3 → F) (l : F) :
    spForm (l • u) v = l * spForm u v := by
  simp [spForm, smul_dotProduct]

theorem IsTransGroup.smul {v : Fin 3 ⊕ Fin 3 → F} {l : F} (hl : l ≠ 0)
    {X : Subgroup (StatedSp 3 F)} (h : IsTransGroup v X) : IsTransGroup (l • v) X := by
  have hl' : l⁻¹ ≠ 0 := inv_ne_zero hl
  have := IsTransGroup.of_smul (v := l • v) hl' (by rwa [smul_smul, inv_mul_cancel₀ hl, one_smul])
  exact this

theorem exists_aligned_sp {G : Type*} [Group G] (Φ : StatedSp 3 F →* G)
    (hΦ : Function.Injective Φ) {P Q : Fin 3 → Subgroup G}
    (hP : ∀ i, ∃ g, P i = (CFSG.Timmesfeld.ARS.conjSub
      (Symplectic.rootGroup 3 F (Pi.single 2 1)) g).map Φ)
    (hQ : ∀ i, ∃ g, Q i = (CFSG.Timmesfeld.ARS.conjSub
      (Symplectic.rootGroup 3 F (Pi.single 2 1)) g).map Φ)
    (hopp : ∀ i, ¬ Commuting (P i) (Q i))
    (hcomm : ∀ i j, i ≠ j → Commuting (P i ⊔ Q i) (P j ⊔ Q j)) :
    ∃ g : StatedSp 3 F, ∀ i,
      (Symplectic.rootGroup 3 F (longC3 i)).map (Φ.comp (MulAut.conj g).toMonoidHom) = P i ∧
      (Symplectic.rootGroup 3 F (-longC3 i)).map (Φ.comp (MulAut.conj g).toMonoidHom) =
        Q i := by
  choose h hh using hP
  choose k hk using hQ
  obtain ⟨X₀, hX₀def⟩ : ∃ X₀, X₀ = Symplectic.rootGroup 3 F (Pi.single 2 1) := ⟨_, rfl⟩
  rw [← hX₀def] at hh hk
  obtain ⟨e, hedef⟩ : ∃ e : Fin 3 ⊕ Fin 3 → F, e = Pi.single (Sum.inl 2) 1 := ⟨_, rfl⟩
  have he0 : e ≠ 0 := fun h0 => by
    have := congrFun h0 (Sum.inl 2)
    simp [hedef] at this
  have hX₀ : IsTransGroup e X₀ := by
    rw [hX₀def, hedef, ← longC3_two]
    exact isTransGroup_pos 2
  obtain ⟨p, hpdef⟩ : ∃ p : Fin 3 → Fin 3 ⊕ Fin 3 → F,
      p = fun i => SpExtras.mat 3 F (h i) *ᵥ e := ⟨_, rfl⟩
  obtain ⟨q, hqdef⟩ : ∃ q : Fin 3 → Fin 3 ⊕ Fin 3 → F,
      q = fun i => SpExtras.mat 3 F (k i) *ᵥ e := ⟨_, rfl⟩
  have hpT : ∀ i, IsTransGroup (p i) (CFSG.Timmesfeld.ARS.conjSub X₀ (h i)) := fun i => by
    rw [hpdef]; exact hX₀.conjSub (h i)
  have hqT : ∀ i, IsTransGroup (q i) (CFSG.Timmesfeld.ARS.conjSub X₀ (k i)) := fun i => by
    rw [hqdef]; exact hX₀.conjSub (k i)
  have hp0 : ∀ i, p i ≠ 0 := fun i => by rw [hpdef]; exact mat_mulVec_ne_zero (h i) he0
  have hq0 : ∀ i, q i ≠ 0 := fun i => by rw [hqdef]; exact mat_mulVec_ne_zero (k i) he0
  have hc : ∀ {X Y : Subgroup G}, Commuting X Y → ∀ {A B : Subgroup (StatedSp 3 F)},
      X = A.map Φ → Y = B.map Φ → Commuting A B := fun hXY A B hA hB =>
    (commuting_map_iff hΦ).1 (hA ▸ hB ▸ hXY)
  have hprop : ∀ {v w : Fin 3 ⊕ Fin 3 → F} {X Y : Subgroup (StatedSp 3 F)}, IsTransGroup v X →
      IsTransGroup w Y → w ≠ 0 → (∃ l : F, w = l • v) → Y = X := by
    rintro v w X Y hX hY hw ⟨l, rfl⟩
    have hl : l ≠ 0 := fun hl => hw (by rw [hl, zero_smul])
    exact (hY.of_smul hl).eq hX
  have hBpq : ∀ i, spForm (p i) (q i) ≠ 0 := fun i hB =>
    hopp i (by rw [hh i, hk i]; exact (commuting_map_iff hΦ).2 ((hpT i).commuting (hqT i) hB))
  have hBpp : ∀ i j, spForm (p i) (p j) = 0 := by
    intro i j
    by_cases hij : i = j
    · rw [hij]; exact spForm_self _
    rcases (hpT i).spForm_eq_zero (hpT j) (hp0 i)
        (hc ((hcomm i j hij).mono le_sup_left le_sup_left) (hh i) (hh j)) with h0 | hl
    · exact h0
    · exfalso
      have hPji : P j = P i := by rw [hh i, hh j, hprop (hpT i) (hpT j) (hp0 j) hl]
      exact hopp i (by rw [← hPji]; exact ((hcomm i j hij).mono le_sup_right le_sup_left).symm)
  have hBqq : ∀ i j, spForm (q i) (q j) = 0 := by
    intro i j
    by_cases hij : i = j
    · rw [hij]; exact spForm_self _
    rcases (hqT i).spForm_eq_zero (hqT j) (hq0 i)
        (hc ((hcomm i j hij).mono le_sup_right le_sup_right) (hk i) (hk j)) with h0 | hl
    · exact h0
    · exfalso
      have hQji : Q j = Q i := by rw [hk i, hk j, hprop (hqT i) (hqT j) (hq0 j) hl]
      exact hopp i (by rw [← hQji]; exact ((hcomm i j hij).mono le_sup_left le_sup_right))
  have hBpq' : ∀ i j, i ≠ j → spForm (p i) (q j) = 0 := by
    intro i j hij
    rcases (hpT i).spForm_eq_zero (hqT j) (hp0 i)
        (hc ((hcomm i j hij).mono le_sup_left le_sup_right) (hh i) (hk j)) with h0 | hl
    · exact h0
    · exfalso
      have hQP : Q j = P i := by rw [hh i, hk j, hprop (hpT i) (hqT j) (hq0 j) hl]
      exact hopp j (by rw [hQP]; exact ((hcomm i j hij).mono le_sup_left le_sup_left).symm)
  have hq'T : ∀ i, IsTransGroup ((spForm (p i) (q i))⁻¹ • q i)
      (CFSG.Timmesfeld.ARS.conjSub X₀ (k i)) := fun i => (hqT i).smul (inv_ne_zero (hBpq i))
  obtain ⟨g, hg⟩ := exists_mem_statedSp_mulVec (p := p)
    (q := fun i => (spForm (p i) (q i))⁻¹ • q i) hBpp
    (fun i j => by rw [spForm_smul_left, spForm_smul_right, hBqq, mul_zero, mul_zero])
    (fun i j => by
      rw [spForm_smul_right]
      by_cases hij : i = j
      · subst hij
        rw [ite_eq_left_iff.2 (fun h => absurd rfl h), inv_mul_cancel₀ (hBpq i)]
      · rw [ite_eq_right_iff.2 (fun h => absurd h hij), hBpq' i j hij, mul_zero])
  refine ⟨g, fun i => ⟨?_, ?_⟩⟩
  · rw [← Subgroup.map_map, hh i]
    congr 1
    have := (isTransGroup_pos (F := F) i).conjSub g
    rw [(hg i).1] at this
    exact this.eq (hpT i)
  · rw [← Subgroup.map_map, hk i]
    congr 1
    have := (isTransGroup_neg (F := F) i).conjSub g
    rw [(hg i).2] at this
    exact this.eq (hq'T i)

end CaseM

variable {G : Type*} [Group G] {R : Set (Subgroup G)} {A A₀ : Subgroup G}

theorem Sec12.exists_aligned_sp (hS : Sec12 R A A₀) {E C : Subgroup G} {P Q : Fin 3 → Subgroup G}
    (hfr : Sec12.IsSubframe R A A₀ E C P Q) {F : Type} [Field F] (Φ : StatedSp 3 F →* G)
    (hΦ : Function.Injective Φ)
    (hΔ : ∀ X : Subgroup G, X ∈ leviSet R A A₀ ↔ ∃ g, X = (conjSub
      (Symplectic.rootGroup 3 F (Pi.single 2 1)) g).map Φ) :
    ∃ g : StatedSp 3 F, ∀ i,
      (Symplectic.rootGroup 3 F (CaseM.longC3 i)).map (Φ.comp (MulAut.conj g).toMonoidHom) =
        P i ∧
      (Symplectic.rootGroup 3 F (-CaseM.longC3 i)).map (Φ.comp (MulAut.conj g).toMonoidHom) =
        Q i :=
  CaseM.exists_aligned_sp Φ hΦ (fun i => (hΔ (P i)).1 (hfr.memP i).1)
    (fun i => (hΔ (Q i)).1 (hfr.memQ i).1)
    (fun i => (hfr.opposite i).not_commuting (hS.hyp.root.ne_bot _ (hfr.memP i).1.1.1))
    hfr.commuting

end CFSG.Timmesfeld.ARS
