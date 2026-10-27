module

public import CFSG.Quasithin.Background.SmithB45Sp4Herm
public import CFSG.Quasithin.Background.SmithB42Sp4Nat

public section

namespace CFSG.Quasithin.B45Sp4

open CFSG.Quasithin.B42Sp4 CFSG.Quasithin.H.Sp4 CFSG.Assembly.LowTwoRank
open CFSG.LocalAnalysis.ComponentInitial.SymplecticFour (sym2 sym2_transpose tau coe_tau lam
  coe_lam radical mem_unipotent_iff eq_sym2 tau_mul_tau tau_comm tau_injective card_radical unitri
  tau_sq)
open CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag (unipotent)
open scoped Matrix

section Count

theorem card_le_card_inf_ker_mul {G H : Type} [AddCommGroup G] [AddCommGroup H] [Finite G]
    [Finite H] (φ : G →+ H) (A : AddSubgroup G) (C : AddSubgroup H)
    (hA : ∀ x ∈ A, φ x ∈ C) : Nat.card A ≤ Nat.card ↥(A ⊓ φ.ker) * Nat.card C := by
  set ψ : ↥A →+ H := φ.comp A.subtype with hψ
  have h1 : Nat.card ↥A = Nat.card ψ.ker * Nat.card ψ.range := by
    rw [← AddSubgroup.index_ker, AddSubgroup.card_mul_index]
  have h2 : Nat.card ψ.range ≤ Nat.card C := by
    apply AddSubgroup.card_le_of_le
    rintro _ ⟨x, rfl⟩
    exact hA x.1 x.2
  have h3 : Nat.card ψ.ker = Nat.card ↥(A ⊓ φ.ker) := by
    refine Nat.card_congr
      { toFun := fun x => ⟨x.1.1, x.1.2, x.2⟩
        invFun := fun y => ⟨⟨y.1, y.2.1⟩, y.2.2⟩
        left_inv := fun x => rfl
        right_inv := fun y => rfl }
  rw [h1, h3]
  exact Nat.mul_le_mul_left _ h2

end Count

section Flag

variable {F : Type} [Field F] [CharP F 2] [Finite F] {ι : Type} [Fintype ι] [DecidableEq ι]

@[expose] def flagFix (a : ℕ) {n : ℕ} (ord : Fin n ≃ ι) (E : Set (Matrix ι ι F)) (k : ℕ) :
    AddSubgroup (Matrix ι ι F) :=
  matFix a ι F E ⊓
    { carrier := {Y | ∀ m : Fin n, (m : ℕ) < k → ∀ i, Y i (ord m) = 0}
      add_mem' := fun {Y Z} hY hZ m hm i => by
        rw [Matrix.add_apply, hY m hm i, hZ m hm i, add_zero]
      zero_mem' := fun m _ i => rfl
      neg_mem' := fun {Y} hY m hm i => by
        rw [Matrix.neg_apply, hY m hm i, neg_zero] }

omit [CharP F 2] [Finite F] [DecidableEq ι] in
theorem mem_flagFix {a : ℕ} {n : ℕ} {ord : Fin n ≃ ι} {E : Set (Matrix ι ι F)} {k : ℕ}
    {Y : Matrix ι ι F} :
    Y ∈ flagFix a ord E k ↔ Y ∈ matFix a ι F E ∧ ∀ m : Fin n, (m : ℕ) < k → ∀ i, Y i (ord m) = 0 :=
  Iff.rfl

@[expose] def colHom (r : ι) : Matrix ι ι F →+ (ι → F) where
  toFun Y i := Y i r
  map_zero' := rfl
  map_add' _ _ := rfl

@[expose] def vecFix (E : Set (Matrix ι ι F)) : AddSubgroup (ι → F) where
  carrier := {v | ∀ g ∈ E, g *ᵥ v = v}
  add_mem' := fun {v w} hv hw g hg => by rw [Matrix.mulVec_add, hv g hg, hw g hg]
  zero_mem' := fun g _ => Matrix.mulVec_zero g
  neg_mem' := fun {v} hv g hg => by rw [Matrix.mulVec_neg, hv g hg]

omit [Finite F] in
theorem mul_eq_of_tw {a : ℕ} {g Y : Matrix ι ι F} (hg : g * g = 1) (hY : tw a g Y = Y) :
    g * Y = Y * (frobPow a g)ᵀ := by
  have hσ : (frobPow a g)ᵀ * (frobPow a g)ᵀ = 1 := by
    rw [← Matrix.transpose_mul, ← frobPow_mul, hg, frobPow_one, Matrix.transpose_one]
  calc g * Y = g * Y * ((frobPow a g)ᵀ * (frobPow a g)ᵀ) := by rw [hσ, Matrix.mul_one]
    _ = tw a g Y * (frobPow a g)ᵀ := by rw [tw_apply, Matrix.mul_assoc, Matrix.mul_assoc,
          Matrix.mul_assoc]
    _ = Y * (frobPow a g)ᵀ := by rw [hY]

theorem card_matFix_le_pow (a : ℕ) {n : ℕ} (ord : Fin n ≃ ι) (E : Set (Matrix ι ι F))
    (hinv : ∀ g ∈ E, g * g = 1) (htri : ∀ g ∈ E, ∀ k l : Fin n, k < l → g (ord k) (ord l) = 0)
    (hdiag : ∀ g ∈ E, ∀ k : Fin n, g (ord k) (ord k) = 1) :
    Nat.card ↥(matFix a ι F E) ≤ Nat.card ↥(vecFix E) ^ n := by
  classical
  have hstep : ∀ k : Fin n, Nat.card ↥(flagFix a ord E k) ≤
      Nat.card ↥(flagFix a ord E (k + 1)) * Nat.card ↥(vecFix E) := by
    intro k
    have hle := card_le_card_inf_ker_mul (colHom (ord k)) (flagFix a ord E k) (vecFix E) ?_
    · have heq : flagFix a ord E k ⊓ (colHom (F := F) (ord k)).ker = flagFix a ord E (k + 1) := by
        ext Y
        simp only [AddSubgroup.mem_inf, AddMonoidHom.mem_ker, mem_flagFix]
        constructor
        · rintro ⟨⟨hY, hcol⟩, hk⟩
          refine ⟨hY, fun m hm i => ?_⟩
          rcases Nat.lt_succ_iff_lt_or_eq.mp hm with h | h
          · exact hcol m h i
          · have : m = k := Fin.ext h
            rw [this]
            exact congrFun hk i
        · rintro ⟨hY, hcol⟩
          refine ⟨⟨hY, fun m hm i => hcol m (by omega) i⟩, ?_⟩
          funext i
          exact hcol k (by omega) i
      rwa [heq] at hle
    ·
      intro Y hY g hg
      obtain ⟨hYf, hcol⟩ := mem_flagFix.mp hY
      have h1 := mul_eq_of_tw (hinv g hg) (hYf g hg)
      funext i
      show (g *ᵥ fun j => Y j (ord k)) i = Y i (ord k)
      have h2 : (g *ᵥ fun j => Y j (ord k)) i = (g * Y) i (ord k) := by
        rw [Matrix.mulVec, dotProduct, Matrix.mul_apply]
      rw [h2, h1, Matrix.mul_apply, ← Equiv.sum_comp ord]
      rw [Finset.sum_eq_single k]
      · rw [Matrix.transpose_apply, frobPow, Matrix.map_apply, hdiag g hg k, one_pow, mul_one]
      · intro m _ hmk
        rcases lt_or_gt_of_ne hmk with h | h
        · rw [hcol m h i, zero_mul]
        · rw [Matrix.transpose_apply, frobPow, Matrix.map_apply, htri g hg k m h,
            zero_pow (by positivity), mul_zero]
      · intro h
        exact absurd (Finset.mem_univ k) h
  have hind : ∀ k : ℕ, k ≤ n → Nat.card ↥(matFix a ι F E) ≤
      Nat.card ↥(flagFix a ord E k) * Nat.card ↥(vecFix E) ^ k := by
    intro k
    induction k with
    | zero =>
      intro _
      rw [pow_zero, mul_one]
      apply AddSubgroup.card_le_of_le
      intro Y hY
      exact mem_flagFix.mpr ⟨hY, fun m hm => absurd hm (Nat.not_lt_zero _)⟩
    | succ k ih =>
      intro hk
      have h1 := ih (by omega)
      have h2 := hstep ⟨k, by omega⟩
      calc Nat.card ↥(matFix a ι F E) ≤ Nat.card ↥(flagFix a ord E k) *
            Nat.card ↥(vecFix E) ^ k := h1
        _ ≤ Nat.card ↥(flagFix a ord E (k + 1)) * Nat.card ↥(vecFix E) *
            Nat.card ↥(vecFix E) ^ k := Nat.mul_le_mul_right _ h2
        _ = Nat.card ↥(flagFix a ord E (k + 1)) * Nat.card ↥(vecFix E) ^ (k + 1) := by
            ring
  have hbot : flagFix a ord E n = ⊥ := by
    rw [eq_bot_iff]
    intro Y hY
    rw [AddSubgroup.mem_bot]
    obtain ⟨-, hcol⟩ := mem_flagFix.mp hY
    ext i j
    have := hcol (ord.symm j) (ord.symm j).2 i
    rwa [Equiv.apply_symm_apply] at this
  have h := hind n le_rfl
  rwa [hbot, AddSubgroup.card_bot, one_mul] at h

end Flag

section Sp

variable {F : Type} [Field F] [CharP F 2]

@[expose] def ordU : Fin 4 ≃ Fin 2 ⊕ Fin 2 where
  toFun := ![Sum.inr 0, Sum.inr 1, Sum.inl 1, Sum.inl 0]
  invFun := Sum.elim ![3, 2] ![0, 1]
  left_inv := by decide
  right_inv := by decide

omit [CharP F 2] in
theorem unipotent_tri {g : StatedSp 2 F} (hg : g ∈ unipotent 2 F) (k l : Fin 4) (hkl : k < l) :
    spM g (ordU k) (ordU l) = 0 := by
  obtain ⟨C, hC, t, rfl⟩ := mem_unipotent_iff.1 hg
  rw [spM, coe_tau_mul_lam]
  fin_cases k <;> fin_cases l <;> simp_all [ordU, unitri]

omit [CharP F 2] in
theorem unipotent_diag {g : StatedSp 2 F} (hg : g ∈ unipotent 2 F) (k : Fin 4) :
    spM g (ordU k) (ordU k) = 1 := by
  obtain ⟨C, hC, t, rfl⟩ := mem_unipotent_iff.1 hg
  rw [spM, coe_tau_mul_lam]
  fin_cases k <;> simp [ordU, unitri]

omit [CharP F 2] in
theorem spM_mul (x y : StatedSp 2 F) : spM (x * y) = spM x * spM y := rfl

omit [CharP F 2] in
theorem spM_one : spM (1 : StatedSp 2 F) = 1 := rfl

omit [CharP F 2] in
theorem spM_injective : Function.Injective (spM : StatedSp 2 F → _) :=
  fun _ _ h => Subtype.ext (Units.ext h)

omit [CharP F 2] in
theorem card_vecFix_image (E : Subgroup (StatedSp 2 F)) :
    Nat.card ↥(vecFix (spM '' (E : Set (StatedSp 2 F)))) = Nat.card ↥(fixK E) := by
  refine Nat.card_congr (Equiv.subtypeEquivRight fun v => ?_)
  constructor
  · intro h γ hγ
    exact h _ ⟨γ, hγ, rfl⟩
  · rintro h _ ⟨γ, hγ, rfl⟩
    exact h γ hγ

omit [CharP F 2] in
theorem mem_matFix_image {a : ℕ} {E : Subgroup (StatedSp 2 F)}
    {Y : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F} :
    Y ∈ matFix a _ F (spM '' (E : Set (StatedSp 2 F))) ↔ ∀ γ ∈ E, tw a (spM γ) Y = Y := by
  constructor
  · intro h γ hγ
    exact h _ ⟨γ, hγ, rfl⟩
  · rintro h _ ⟨γ, hγ, rfl⟩
    exact h γ hγ

variable [Finite F]

theorem card_matFix_unipotent (a : ℕ) (E : Subgroup (StatedSp 2 F)) (hE : ∀ x ∈ E, x * x = 1)
    (hEU : E ≤ unipotent 2 F) :
    Nat.card ↥(matFix a _ F (spM '' (E : Set (StatedSp 2 F)))) ≤ Nat.card ↥(fixK E) ^ 4 := by
  rw [← card_vecFix_image]
  refine card_matFix_le_pow a ordU _ ?_ ?_ ?_
  · rintro _ ⟨γ, hγ, rfl⟩
    rw [← spM_mul, hE γ hγ, spM_one]
  · rintro _ ⟨γ, hγ, rfl⟩ k l hkl
    exact unipotent_tri (hEU hγ) k l hkl
  · rintro _ ⟨γ, hγ, rfl⟩ k
    exact unipotent_diag (hEU hγ) k

@[expose] noncomputable def conjSub (h : StatedSp 2 F) (E : Subgroup (StatedSp 2 F)) :
    Subgroup (StatedSp 2 F) :=
  E.map (MulAut.conj h⁻¹).toMonoidHom

omit [CharP F 2] [Finite F] in
theorem mem_conjSub {h : StatedSp 2 F} {E : Subgroup (StatedSp 2 F)} {x : StatedSp 2 F} :
    x ∈ conjSub h E ↔ h * x * h⁻¹ ∈ E := by
  rw [conjSub, Subgroup.mem_map_equiv]
  simp

omit [CharP F 2] [Finite F] in
theorem card_conjSub (h : StatedSp 2 F) (E : Subgroup (StatedSp 2 F)) :
    Nat.card ↥(conjSub h E) = Nat.card ↥E :=
  Subgroup.card_map_of_injective (MulAut.conj h⁻¹).injective

@[expose] noncomputable def hermFixConj {a : ℕ} (hF : Nat.card F = 2 ^ (2 * a)) (h : StatedSp 2 F)
    (E : Subgroup (StatedSp 2 F)) :
    ↥(hermFix a _ F (spM '' (E : Set (StatedSp 2 F)))) ≃
      ↥(hermFix a _ F (spM '' (conjSub h E : Set (StatedSp 2 F)))) where
  toFun Y := ⟨tw a (spM h⁻¹) Y, by
    refine mem_hermFix.mpr ⟨tw_mem_hermA hF _ (mem_hermFix.mp Y.2).1, ?_⟩
    rintro _ ⟨γ, hγ, rfl⟩
    have hγ' := mem_conjSub.mp hγ
    have hY := (mem_hermFix.mp Y.2).2 _ ⟨_, hγ', rfl⟩
    rw [← tw_mul, ← spM_mul,
      show γ * h⁻¹ = h⁻¹ * (h * γ * h⁻¹) by group, spM_mul, tw_mul, hY]⟩
  invFun Z := ⟨tw a (spM h) Z, by
    refine mem_hermFix.mpr ⟨tw_mem_hermA hF _ (mem_hermFix.mp Z.2).1, ?_⟩
    rintro _ ⟨γ, hγ, rfl⟩
    have hγ' : h⁻¹ * γ * h ∈ conjSub h E := by
      rw [mem_conjSub]
      simpa [mul_assoc] using hγ
    have hZ := (mem_hermFix.mp Z.2).2 _ ⟨_, hγ', rfl⟩
    rw [← tw_mul, ← spM_mul, show γ * h = h * (h⁻¹ * γ * h) by group, spM_mul, tw_mul, hZ]⟩
  left_inv Y := by
    apply Subtype.ext
    show tw a (spM h) (tw a (spM h⁻¹) Y) = Y
    rw [← tw_mul, ← spM_mul, mul_inv_cancel, spM_one, tw_one]
  right_inv Z := by
    apply Subtype.ext
    show tw a (spM h⁻¹) (tw a (spM h) Z) = Z
    rw [← tw_mul, ← spM_mul, inv_mul_cancel, spM_one, tw_one]

end Sp

section Radical

variable {F : Type} [Field F] [CharP F 2]

omit [CharP F 2] in
theorem frobPow_fromBlocks {a : ℕ} (A B C D : Matrix (Fin 2) (Fin 2) F) :
    frobPow a (Matrix.fromBlocks A B C D) =
      Matrix.fromBlocks (frobPow a A) (frobPow a B) (frobPow a C) (frobPow a D) := by
  rw [frobPow, Matrix.fromBlocks_map]
  rfl

omit [CharP F 2] in
theorem frobPow_one' {a : ℕ} : frobPow a (1 : Matrix (Fin 2) (Fin 2) F) = 1 := by
  ext i j
  by_cases h : i = j <;> simp [frobPow, Matrix.one_apply, h]

omit [CharP F 2] in
theorem tw_tau_fromBlocks (a : ℕ) {C : Matrix (Fin 2) (Fin 2) F} (hC : Cᵀ = C)
    (A B C' D : Matrix (Fin 2) (Fin 2) F) :
    tw a (spM (tau hC)) (Matrix.fromBlocks A B C' D) =
      Matrix.fromBlocks (A + C * C' + (B + C * D) * frobPow a C) (B + C * D)
        (C' + D * frobPow a C) D := by
  have hσC : (frobPow a C)ᵀ = frobPow a C := by rw [← frobPow_transpose, hC]
  rw [tw_apply, spM, coe_tau, frobPow_fromBlocks, frobPow_one', frobPow_zero',
    Matrix.fromBlocks_transpose, Matrix.transpose_one, Matrix.transpose_zero, hσC,
    Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply]
  simp only [Matrix.one_mul, Matrix.zero_mul, Matrix.mul_one, Matrix.mul_zero, zero_add,
    Matrix.add_mul]

omit [CharP F 2] in
theorem fix_tau {a : ℕ} {C : Matrix (Fin 2) (Fin 2) F} (hC : Cᵀ = C)
    {Y : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F} (hY : tw a (spM (tau hC)) Y = Y) :
    C * Y.toBlocks₂₂ = 0 ∧ Y.toBlocks₂₂ * frobPow a C = 0 ∧
      C * Y.toBlocks₂₁ + Y.toBlocks₁₂ * frobPow a C = 0 := by
  rw [← Matrix.fromBlocks_toBlocks Y, tw_tau_fromBlocks] at hY
  obtain ⟨h11, h12, h21, -⟩ := Matrix.fromBlocks_inj.mp hY
  have hCD : C * Y.toBlocks₂₂ = 0 := by
    have := congrArg (· - Y.toBlocks₁₂) h12
    simpa using this
  refine ⟨hCD, ?_, ?_⟩
  · have := congrArg (· - Y.toBlocks₂₁) h21
    simpa using this
  · rw [hCD, add_zero, add_assoc] at h11
    exact left_eq_add.mp h11.symm

variable [Finite F]

theorem exists_line_mem {E : Subgroup (StatedSp 2 F)} (hER : E ≤ radical F)
    (hE : Nat.card F ^ 2 < Nat.card E) (b c d : F) :
    ∃ l : F, l ≠ 0 ∧ tau (sym2_transpose (l * b) (l * c) (l * d)) ∈ E := by
  classical
  set X := radical F with hX
  set E' : Subgroup ↥X := E.subgroupOf X with hE'
  have hcardE' : Nat.card E' = Nat.card E := by
    rw [hE']
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hER).toEquiv
  have hq1 : 1 ≤ Nat.card F := Nat.card_pos
  have hidx : E'.index < Nat.card F := by
    have h1 := E'.card_mul_index
    rw [hcardE', card_radical] at h1
    by_contra h
    push Not at h
    have : Nat.card F ^ 2 * Nat.card F < Nat.card E * E'.index :=
      Nat.mul_lt_mul_of_lt_of_le hE h (by omega)
    rw [h1] at this
    ring_nf at this
    omega
  have : Finite (↥X ⧸ E') := Finite.of_surjective _ (QuotientGroup.mk_surjective)
  let φ : F → ↥X ⧸ E' := fun l =>
    QuotientGroup.mk ⟨tau (sym2_transpose (l * b) (l * c) (l * d)), _, _, rfl⟩
  have hninj : ¬ Function.Injective φ := fun hinj => by
    have h1 := Nat.card_le_card_of_injective φ hinj
    have h2 : Nat.card (↥X ⧸ E') = E'.index := rfl
    omega
  simp only [Function.Injective, not_forall] at hninj
  obtain ⟨l₁, l₂, heq, hne⟩ := hninj
  have hmem := QuotientGroup.eq.mp heq
  rw [Subgroup.mem_subgroupOf] at hmem
  refine ⟨l₁ + l₂, fun h => hne ?_, ?_⟩
  · have := eq_neg_of_add_eq_zero_left h
    rw [this, CharTwo.neg_eq]
  · have hinv : (tau (sym2_transpose (l₁ * b) (l₁ * c) (l₁ * d)))⁻¹ =
        tau (sym2_transpose (l₁ * b) (l₁ * c) (l₁ * d)) :=
      inv_eq_of_mul_eq_one_right (by rw [← sq]; exact tau_sq _)
    have h3 : tau (sym2_transpose ((l₁ + l₂) * b) ((l₁ + l₂) * c) ((l₁ + l₂) * d)) =
        (tau (sym2_transpose (l₁ * b) (l₁ * c) (l₁ * d)))⁻¹ *
          tau (sym2_transpose (l₂ * b) (l₂ * c) (l₂ * d)) := by
      rw [hinv, tau_mul_tau]
      refine CFSG.LocalAnalysis.ComponentInitial.SymplecticFour.tau_congr _ _ ?_
      ext i j
      fin_cases i <;> fin_cases j <;> simp [sym2] <;> ring
    rw [h3]
    exact hmem

end Radical

section RadicalFix

variable {F : Type} [Field F] [CharP F 2]

theorem eq_of_add_eq_zero' {x y : F} (h : x + y = 0) : x = y := by
  have := eq_neg_of_add_eq_zero_left h
  rw [this, CharTwo.neg_eq]

theorem scalar_core {a : ℕ} {l m n x θ c₀ c₁ b₀ b₁ : F} (hl : l ≠ 0) (hm : m ≠ 0) (hn : n ≠ 0)
    (hx : x ≠ 0) (hθ : θ ^ 2 ^ a ≠ θ)
    (e1 : l * c₀ + b₀ * l ^ 2 ^ a = 0) (e2 : m * c₁ + b₁ * m ^ 2 ^ a = 0)
    (e3 : n * c₁ + b₀ * n ^ 2 ^ a = 0) (e4 : n * c₀ + b₁ * n ^ 2 ^ a = 0)
    (e5 : x * c₀ + b₀ * x ^ 2 ^ a = 0)
    (e6 : x * (m * θ * l⁻¹) * c₁ + b₁ * (x * (m * θ * l⁻¹)) ^ 2 ^ a = 0) :
    c₀ = 0 ∧ c₁ = 0 ∧ b₀ = 0 ∧ b₁ = 0 := by
  have hpos : ∀ y : F, y ≠ 0 → y ^ 2 ^ a ≠ 0 := fun y hy => pow_ne_zero _ hy
  have hc₀ : c₀ = 0 := by
    by_contra hc₀
    have hA := eq_of_add_eq_zero' e1
    have hB := eq_of_add_eq_zero' e5
    have hC := eq_of_add_eq_zero' e4
    have hD := eq_of_add_eq_zero' e2
    have hE := eq_of_add_eq_zero' e6
    have hb₁ : b₁ ≠ 0 := by
      intro h
      rw [h, zero_mul] at hC
      exact mul_ne_zero hn hc₀ hC
    have hc₁ : c₁ ≠ 0 := by
      intro h
      rw [h, mul_zero] at hD
      exact mul_ne_zero hb₁ (hpos m hm) hD.symm
    have h1 : l * x ^ 2 ^ a = x * l ^ 2 ^ a := by
      have : c₀ * (l * x ^ 2 ^ a) = c₀ * (x * l ^ 2 ^ a) := by
        calc c₀ * (l * x ^ 2 ^ a) = (l * c₀) * x ^ 2 ^ a := by ring
          _ = b₀ * l ^ 2 ^ a * x ^ 2 ^ a := by rw [hA]
          _ = (b₀ * x ^ 2 ^ a) * l ^ 2 ^ a := by ring
          _ = (x * c₀) * l ^ 2 ^ a := by rw [hB]
          _ = c₀ * (x * l ^ 2 ^ a) := by ring
      exact mul_left_cancel₀ hc₀ this
    set t := m * θ * l⁻¹ with ht
    have h2 : m * (x * t) ^ 2 ^ a = x * t * m ^ 2 ^ a := by
      have : c₁ * (m * (x * t) ^ 2 ^ a) = c₁ * (x * t * m ^ 2 ^ a) := by
        calc c₁ * (m * (x * t) ^ 2 ^ a) = (m * c₁) * (x * t) ^ 2 ^ a := by ring
          _ = b₁ * m ^ 2 ^ a * (x * t) ^ 2 ^ a := by rw [hD]
          _ = (b₁ * (x * t) ^ 2 ^ a) * m ^ 2 ^ a := by ring
          _ = (x * t * c₁) * m ^ 2 ^ a := by rw [hE]
          _ = c₁ * (x * t * m ^ 2 ^ a) := by ring
      exact mul_left_cancel₀ hc₁ this
    apply hθ
    have hlσ := hpos l hl
    have hmσ := hpos m hm
    rw [ht, mul_pow, mul_pow, mul_pow, inv_pow] at h2
    have h3 : x ^ 2 ^ a * θ ^ 2 ^ a * l = x * θ * l ^ 2 ^ a := by
      have := congrArg (· * (l * l ^ 2 ^ a)) h2
      field_simp at this
      linear_combination this
    have h5 : (x * l ^ 2 ^ a) * θ ^ 2 ^ a = (x * l ^ 2 ^ a) * θ := by
      calc (x * l ^ 2 ^ a) * θ ^ 2 ^ a = (l * x ^ 2 ^ a) * θ ^ 2 ^ a := by rw [h1]
        _ = x ^ 2 ^ a * θ ^ 2 ^ a * l := by ring
        _ = x * θ * l ^ 2 ^ a := h3
        _ = (x * l ^ 2 ^ a) * θ := by ring
    exact mul_left_cancel₀ (mul_ne_zero hx hlσ) h5
  have hb₀ : b₀ = 0 := by
    rw [hc₀, mul_zero, zero_add] at e1
    exact (mul_eq_zero.mp e1).resolve_right (hpos l hl)
  have hc₁ : c₁ = 0 := by
    rw [hb₀, zero_mul, add_zero] at e3
    exact (mul_eq_zero.mp e3).resolve_left hn
  have hb₁ : b₁ = 0 := by
    rw [hc₁, mul_zero, zero_add] at e2
    exact (mul_eq_zero.mp e2).resolve_right (hpos m hm)
  exact ⟨hc₀, hc₁, hb₀, hb₁⟩

end RadicalFix

section RadicalCard

variable {F : Type} [Field F] [CharP F 2] [Finite F]

omit [CharP F 2] [Finite F] in
theorem frobPow_sym2 (a : ℕ) (b c d : F) :
    frobPow a (sym2 b c d) = sym2 (b ^ 2 ^ a) (c ^ 2 ^ a) (d ^ 2 ^ a) := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

theorem blocks_eq_zero_of_mem_matFix {a : ℕ} (ha : 1 ≤ a) (hF : Nat.card F = 2 ^ (2 * a))
    {E : Subgroup (StatedSp 2 F)} (hER : E ≤ radical F) (hE : Nat.card F ^ 2 < Nat.card E)
    {Y : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F}
    (hY : Y ∈ matFix a _ F (spM '' (E : Set (StatedSp 2 F)))) :
    Y.toBlocks₁₂ = 0 ∧ Y.toBlocks₂₁ = 0 ∧ Y.toBlocks₂₂ = 0 := by
  have hfix := mem_matFix_image.mp hY
  have h2a : 2 ^ a ≠ 0 := by positivity
  obtain ⟨l, hl, hlE⟩ := exists_line_mem hER hE 1 0 0
  obtain ⟨m, hm, hmE⟩ := exists_line_mem hER hE 0 0 1
  obtain ⟨n, hn, hnE⟩ := exists_line_mem hER hE 0 1 0
  obtain ⟨θ, hθ⟩ := exists_ne_frob ha hF
  obtain ⟨x, hx, hxE⟩ := exists_line_mem hER hE 1 0 (m * θ * l⁻¹)
  obtain ⟨hl1, -, hl3⟩ := fix_tau _ (hfix _ hlE)
  obtain ⟨hm1, -, hm3⟩ := fix_tau _ (hfix _ hmE)
  obtain ⟨-, -, hn3⟩ := fix_tau _ (hfix _ hnE)
  obtain ⟨-, -, hx3⟩ := fix_tau _ (hfix _ hxE)
  rw [frobPow_sym2] at hl3 hm3 hn3 hx3
  set B := Y.toBlocks₁₂ with hB
  set C' := Y.toBlocks₂₁ with hC'
  set D := Y.toBlocks₂₂ with hD
  have hD0 : D = 0 := by
    ext i j
    have h1 := congrFun (congrFun hl1 0) j
    have h2 := congrFun (congrFun hm1 1) j
    simp [sym2, Matrix.mul_apply, Fin.sum_univ_two] at h1 h2
    fin_cases i
    · simpa [hl] using h1
    · simpa [hm] using h2
  have ev : ∀ {M N : Matrix (Fin 2) (Fin 2) F}, M + N = 0 → ∀ i j, M i j + N i j = 0 :=
    fun h i j => by simpa using congrFun (congrFun h i) j
  have l00 := ev hl3 0 0
  have l01 := ev hl3 0 1
  have l10 := ev hl3 1 0
  have m10 := ev hm3 1 0
  have m01 := ev hm3 0 1
  have m11 := ev hm3 1 1
  have n01 := ev hn3 0 1
  have n10 := ev hn3 1 0
  have x00 := ev hx3 0 0
  have x11 := ev hx3 1 1
  simp [sym2, Matrix.mul_apply, Fin.sum_univ_two] at l00 l01 l10 m10 m01 m11 n01 n10 x00
  simp [sym2, Matrix.mul_apply, Fin.sum_univ_two] at x11
  obtain ⟨hc0, hc1, hb0, hb1⟩ := scalar_core hl hm hn hx hθ l00 m11 n01 n10 x00 x11
  have hc01 : C' 0 1 = 0 := l01.resolve_left hl
  have hb10 : B 1 0 = 0 := l10.resolve_right hl
  have hc10 : C' 1 0 = 0 := m10.resolve_left hm
  have hb01 : B 0 1 = 0 := m01.resolve_right hm
  refine ⟨?_, ?_, hD0⟩
  · ext i j
    fin_cases i <;> fin_cases j <;> simpa
  · ext i j
    fin_cases i <;> fin_cases j <;> simpa

theorem card_matFix_radical_le {a : ℕ} (ha : 1 ≤ a) (hF : Nat.card F = 2 ^ (2 * a))
    {E : Subgroup (StatedSp 2 F)} (hER : E ≤ radical F) (hE : Nat.card F ^ 2 < Nat.card E) :
    Nat.card ↥(matFix a _ F (spM '' (E : Set (StatedSp 2 F)))) ≤ Nat.card F ^ 4 := by
  have hinj : Function.Injective (fun Y : ↥(matFix a _ F (spM '' (E : Set (StatedSp 2 F)))) =>
      (Y : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F).toBlocks₁₁) := by
    intro Y Z h
    obtain ⟨h12, h21, h22⟩ := blocks_eq_zero_of_mem_matFix ha hF hER hE Y.2
    obtain ⟨k12, k21, k22⟩ := blocks_eq_zero_of_mem_matFix ha hF hER hE Z.2
    apply Subtype.ext
    rw [← Matrix.fromBlocks_toBlocks (Y : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F),
      ← Matrix.fromBlocks_toBlocks (Z : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F)]
    simp only at h
    rw [h, h12, h21, h22, k12, k21, k22]
  calc Nat.card ↥(matFix a _ F (spM '' (E : Set (StatedSp 2 F))))
      ≤ Nat.card (Matrix (Fin 2) (Fin 2) F) := Nat.card_le_card_of_injective _ hinj
    _ = Nat.card F ^ 4 := by
        show Nat.card (Fin 2 → Fin 2 → F) = _
        rw [Nat.card_fun, Nat.card_fun]
        simp only [Nat.card_eq_fintype_card, Fintype.card_fin]
        ring

end RadicalCard

section Lev

variable {F : Type} [Field F] [CharP F 2] [Finite F]

theorem le_radical_of_finrank_two {E : Subgroup (StatedSp 2 F)} (hE : ∀ x ∈ E, x * x = 1)
    (hEU : E ≤ unipotent 2 F) (hcard : Nat.card F ^ 2 < Nat.card E)
    (hc : 2 ≤ Module.finrank F (fixK E)) : E ≤ radical F := by
  classical
  by_contra hER
  obtain ⟨g₀, hg₀E, hlev⟩ : ∃ g₀ ∈ E, lev g₀ ≠ 0 := by
    by_contra h
    push Not at h
    exact hER fun g hg => (unipotent_facts (hEU hg)).2.2 (h g hg)
  have hcomm : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x := by
    intro x hx y hy
    have hx' : x⁻¹ = x := inv_eq_of_mul_eq_one_right (hE x hx)
    have hy' : y⁻¹ = y := inv_eq_of_mul_eq_one_right (hE y hy)
    have hxy : (x * y)⁻¹ = x * y := inv_eq_of_mul_eq_one_right (hE _ (E.mul_mem hx hy))
    rw [← hxy, _root_.mul_inv_rev, hx', hy']
  let φ : ↥E →* Multiplicative F :=
    { toFun := fun x => Multiplicative.ofAdd (lev (x : StatedSp 2 F))
      map_one' := by
        show Multiplicative.ofAdd (lev (1 : StatedSp 2 F)) = 1
        simp [lev]
      map_mul' := fun x y => by
        show Multiplicative.ofAdd (lev ((x : StatedSp 2 F) * (y : StatedSp 2 F))) = _
        rw [lev_mul (hEU x.2) (hEU y.2), ofAdd_add] }
  have hker : Nat.card F < Nat.card φ.ker := by
    have h1 := φ.ker.card_mul_index
    rw [Subgroup.index_ker] at h1
    have h2 : Nat.card φ.range ≤ Nat.card F := by
      calc Nat.card φ.range ≤ Nat.card (Multiplicative F) := Finite.card_subtype_le _
        _ = Nat.card F := rfl
    by_contra h
    push Not at h
    have : Nat.card E ≤ Nat.card F * Nat.card F := by
      rw [← h1]
      exact Nat.mul_le_mul h h2
    nlinarith [hcard]
  have hkerR : ∀ x ∈ φ.ker, ((x : ↥E) : StatedSp 2 F) ∈ radical F ∧
      radD ((x : ↥E) : StatedSp 2 F) = 0 := by
    intro x hx
    have hx0 : lev ((x : ↥E) : StatedSp 2 F) = 0 :=
      congrArg Multiplicative.toAdd (MonoidHom.mem_ker.mp hx)
    have hxR := (unipotent_facts (hEU x.2)).2.2 hx0
    exact ⟨hxR, radD_eq_zero_of_comm hxR (hEU hg₀E) hlev (hcomm _ x.2 _ hg₀E)⟩
  obtain ⟨x₁, hx₁ker, hx₁b⟩ : ∃ x ∈ φ.ker, radB ((x : ↥E) : StatedSp 2 F) ≠ 0 := by
    by_contra h
    push Not at h
    have hinj : Function.Injective (fun x : ↥φ.ker => radA (((x : ↥E) : StatedSp 2 F))) := by
      intro x y hxy
      obtain ⟨hxR, hxD⟩ := hkerR x x.2
      obtain ⟨hyR, hyD⟩ := hkerR y y.2
      have := radB_eq_of_radA_radD hxR hyR hxy (by rw [h x x.2, h y y.2]) (by rw [hxD, hyD])
      exact Subtype.ext (Subtype.ext this)
    have := Nat.card_le_card_of_injective _ hinj
    omega
  obtain ⟨hx₁R, hx₁D⟩ := hkerR x₁ hx₁ker
  have hle : fixK E ≤ Submodule.span F {Pi.single (Sum.inl 0) 1} := by
    intro v hv
    have h1 := hv _ (x₁ : ↥E).2
    have h0 := hv g₀ hg₀E
    obtain ⟨C, hC, hx₁eq⟩ := hx₁R
    rw [hx₁eq] at h1 hx₁b hx₁D
    have hCb : C 0 1 ≠ 0 := by
      have : radB (tau hC) = C 0 1 := by rw [radB, coe_tau]; simp
      rwa [this] at hx₁b
    have hCd : C 1 1 = 0 := by
      have : radD (tau hC) = C 1 1 := by rw [radD, coe_tau]; simp
      rwa [this] at hx₁D
    have hC10 : C 1 0 = C 0 1 := by
      have := congrFun (congrFun hC 0) 1
      simpa using this
    have e0 := congrFun h1 (Sum.inl 0)
    have e1 := congrFun h1 (Sum.inl 1)
    rw [tau_mulVec_inl, add_eq_left] at e0 e1
    simp only [Fin.sum_univ_two] at e0 e1
    rw [hC10, hCd, zero_mul, add_zero] at e1
    have hy0 : v (Sum.inr 0) = 0 := (mul_eq_zero.mp e1).resolve_left hCb
    rw [hy0, mul_zero, zero_add] at e0
    have hy1 : v (Sum.inr 1) = 0 := (mul_eq_zero.mp e0).resolve_left hCb
    have hx1 : v (Sum.inl 1) = 0 := by
      have e := congrFun h0 (Sum.inl 0)
      rw [Matrix.mulVec, dotProduct, Fintype.sum_sum_type] at e
      simp only [Fin.sum_univ_two, hy0, hy1, mul_zero, add_zero] at e
      have hd : spM g₀ (Sum.inl 0) (Sum.inl 0) = 1 := unipotent_diag (hEU hg₀E) 3
      have hl : spM g₀ (Sum.inl 0) (Sum.inl 1) = lev g₀ := rfl
      rw [hd, hl, one_mul, add_eq_left] at e
      exact (mul_eq_zero.mp e).resolve_left hlev
    rw [Submodule.mem_span_singleton]
    refine ⟨v (Sum.inl 0), ?_⟩
    funext i
    rcases i with i | i <;> fin_cases i <;> simp [hx1, hy0, hy1]
  have h3 := Submodule.finrank_mono hle
  have h4 : Module.finrank F ↥(F ∙ (Pi.single (Sum.inl 0) 1 : Fin 2 ⊕ Fin 2 → F)) = 1 :=
    finrank_span_singleton (by simp)
  omega

end Lev

section Bounds

variable {F : Type} [Field F] [CharP F 2] [Finite F] {a : ℕ}

theorem card_hermA_eq (ha : 1 ≤ a) (hF : Nat.card F = 2 ^ (2 * a)) :
    Nat.card ↥(hermA a (Fin 2 ⊕ Fin 2) F) = Nat.card F ^ 8 := by
  have h := card_hermA_sq (ι := Fin 2 ⊕ Fin 2) ha hF
  simp only [Fintype.card_sum, Fintype.card_fin] at h
  refine Nat.pow_left_injective (n := 2) (by norm_num) ?_
  simp only
  rw [h, ← pow_mul]

theorem card_hermFix_le_pow (ha : 1 ≤ a) (hF : Nat.card F = 2 ^ (2 * a))
    (E : Subgroup (StatedSp 2 F)) (hE : ∀ x ∈ E, x * x = 1) (hEU : E ≤ unipotent 2 F) :
    Nat.card ↥(hermFix a _ F (spM '' (E : Set (StatedSp 2 F)))) ≤
      Nat.card F ^ (2 * Module.finrank F (fixK E)) := by
  have h1 := card_matFix_unipotent a E hE hEU
  rw [card_matFix ha hF, card_fixK, ← pow_mul] at h1
  have h2 : Nat.card F ^ (Module.finrank F (fixK E) * 4) =
      (Nat.card F ^ (2 * Module.finrank F (fixK E))) ^ 2 := by
    rw [← pow_mul]
    ring_nf
  rw [h2] at h1
  exact (Nat.pow_le_pow_iff_left (by norm_num)).mp h1

omit [CharP F 2] [Finite F] in
theorem finrank_fixK_le (E : Subgroup (StatedSp 2 F)) : Module.finrank F (fixK E) ≤ 4 := by
  have := Submodule.finrank_le (fixK E)
  simpa using this

theorem card_hermFix_le (ha : 1 ≤ a) (hF : Nat.card F = 2 ^ (2 * a))
    (S : Set (Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F)) :
    Nat.card ↥(hermFix a _ F S) ≤ Nat.card F ^ 8 := by
  rw [← card_hermA_eq ha hF]
  exact AddSubgroup.card_le_of_le inf_le_left

theorem bounds_of_le_unipotent (ha : 1 ≤ a) (hF : Nat.card F = 2 ^ (2 * a))
    (E : Subgroup (StatedSp 2 F)) (hE : ∀ x ∈ E, x * x = 1) (hEU : E ≤ unipotent 2 F) :
    Nat.card E ^ 2 * Nat.card ↥(hermFix a _ F (spM '' (E : Set (StatedSp 2 F)))) ≤
        Nat.card F ^ 8 ∧
      (Nat.card F < Nat.card E →
        Nat.card F ^ 4 * Nat.card ↥(hermFix a _ F (spM '' (E : Set (StatedSp 2 F)))) ≤
          Nat.card F ^ 8) := by
  have hpow := card_hermFix_le_pow ha hF E hE hEU
  have hc4 := finrank_fixK_le E
  have hcube := card_le_cube E hE
  have hCq8 := card_hermFix_le ha hF (spM '' (E : Set (StatedSp 2 F)))
  set q := Nat.card F with hq
  set C := Nat.card ↥(hermFix a _ F (spM '' (E : Set (StatedSp 2 F)))) with hC
  set c := Module.finrank F (fixK E) with hc
  have hq1 : 1 ≤ q := Nat.card_pos
  have hmono : ∀ {m n : ℕ}, m ≤ n → q ^ m ≤ q ^ n := fun h => Nat.pow_le_pow_right hq1 h
  rcases (by omega : c = 4 ∨ c = 3 ∨ c = 2 ∨ c ≤ 1) with h4 | h3 | h2 | h1
  · have hb := eq_bot_of_finrank_fixK (Γ₀ := E) (by omega)
    have hE1 : Nat.card E = 1 := by rw [hb, Subgroup.card_bot]
    refine ⟨by rw [hE1, one_pow, one_mul]; exact hCq8, fun h => by omega⟩
  · have hEq := card_le_of_finrank_fixK_three (Γ₀ := E) h3
    rw [h3] at hpow
    refine ⟨?_, fun h => by omega⟩
    calc Nat.card E ^ 2 * C ≤ q ^ 2 * q ^ 6 := Nat.mul_le_mul (Nat.pow_le_pow_left hEq 2) hpow
      _ = q ^ 8 := by ring
  · rw [h2] at hpow
    refine ⟨?_, fun _ => ?_⟩
    · by_cases hsmall : Nat.card E ≤ q ^ 2
      · calc Nat.card E ^ 2 * C ≤ (q ^ 2) ^ 2 * q ^ 4 :=
              Nat.mul_le_mul (Nat.pow_le_pow_left hsmall 2) hpow
          _ = q ^ 8 := by ring
      · push Not at hsmall
        have hER := le_radical_of_finrank_two hE hEU hsmall (by omega)
        have hM := card_matFix_radical_le ha hF hER hsmall
        rw [card_matFix ha hF] at hM
        have hC2 : C ≤ q ^ 2 := by
          have : C ^ 2 ≤ (q ^ 2) ^ 2 := by rw [← pow_mul]; exact hM
          exact (Nat.pow_le_pow_iff_left (by norm_num)).mp this
        calc Nat.card E ^ 2 * C ≤ (q ^ 3) ^ 2 * q ^ 2 :=
              Nat.mul_le_mul (Nat.pow_le_pow_left hcube 2) hC2
          _ = q ^ 8 := by ring
    · calc q ^ 4 * C ≤ q ^ 4 * q ^ 4 := Nat.mul_le_mul_left _ hpow
        _ = q ^ 8 := by ring
  · have hC2 : C ≤ q ^ 2 := hpow.trans (hmono (by omega))
    refine ⟨?_, fun _ => ?_⟩
    · calc Nat.card E ^ 2 * C ≤ (q ^ 3) ^ 2 * q ^ 2 :=
            Nat.mul_le_mul (Nat.pow_le_pow_left hcube 2) hC2
        _ = q ^ 8 := by ring
    · calc q ^ 4 * C ≤ q ^ 4 * q ^ 2 := Nat.mul_le_mul_left _ hC2
        _ ≤ q ^ 8 := by rw [← pow_add]; exact hmono (by norm_num)

omit [CharP F 2] [Finite F] in
theorem isPGroup_of_sq (E : Subgroup (StatedSp 2 F)) (hE : ∀ x ∈ E, x * x = 1) :
    IsPGroup 2 E := fun x => ⟨1, Subtype.ext (by
  rw [pow_one, Subgroup.coe_pow, pow_two]
  exact hE x x.2)⟩

theorem card_bounds (ha : 1 ≤ a) (hF : Nat.card F = 2 ^ (2 * a))
    (E : Subgroup (StatedSp 2 F)) (hE : ∀ x ∈ E, x * x = 1) :
    Nat.card E ^ 2 * Nat.card ↥(hermFix a _ F (spM '' (E : Set (StatedSp 2 F)))) ≤
        Nat.card F ^ 8 ∧
      (Nat.card F < Nat.card E →
        Nat.card F ^ 4 * Nat.card ↥(hermFix a _ F (spM '' (E : Set (StatedSp 2 F)))) ≤
          Nat.card F ^ 8) := by
  obtain ⟨h, hh⟩ := exists_conj_le_unipotent (isPGroup_of_sq E hE)
  set E' := conjSub h E with hE'
  have hE'U : E' ≤ unipotent 2 F := by
    intro x hx
    have := hh _ (mem_conjSub.mp hx)
    simpa [mul_assoc] using this
  have hE'sq : ∀ x ∈ E', x * x = 1 := by
    intro x hx
    have h1 := hE _ (mem_conjSub.mp hx)
    have h2 : h * (x * x) * h⁻¹ = 1 := by
      rw [show h * (x * x) * h⁻¹ = (h * x * h⁻¹) * (h * x * h⁻¹) by group, h1]
    have h3 : x * x = h⁻¹ * (h * (x * x) * h⁻¹) * h := by group
    rw [h3, h2, mul_one, inv_mul_cancel]
  have hcard : Nat.card E' = Nat.card E := card_conjSub h E
  have hfix := Nat.card_congr (hermFixConj hF h E)
  obtain ⟨h1, h2⟩ := bounds_of_le_unipotent ha hF E' hE'sq hE'U
  rw [hcard, ← hfix] at h1 h2
  exact ⟨h1, h2⟩

end Bounds

section Quad

variable {F : Type} [Field F] [CharP F 2] [Finite F] {a : ℕ}

omit [Finite F] in
omit [CharP F 2] in
theorem quad_expand {ι : Type} [Fintype ι] [DecidableEq ι] (u w u' w' Y : Matrix ι ι F) :
    (1 + w) * ((1 + u) * Y * (1 + u')ᵀ - Y) * (1 + w')ᵀ - ((1 + u) * Y * (1 + u')ᵀ - Y) =
      w * Y * u'ᵀ + u * Y * w'ᵀ + w * u * Y * (1 + u'ᵀ + w'ᵀ + u'ᵀ * w'ᵀ) +
        (1 + u + w) * Y * (u'ᵀ * w'ᵀ) := by
  simp only [Matrix.transpose_add, Matrix.transpose_one]
  noncomm_ring

omit [Finite F] in
theorem frobPow_sub_one {ι : Type} [Fintype ι] [DecidableEq ι] (X : Matrix ι ι F) :
    frobPow a (X - 1) = frobPow a X - 1 := by
  ext i j
  simp only [frobPow, Matrix.map_apply, Matrix.sub_apply, Matrix.one_apply]
  rw [sub_pow_char_pow]
  split_ifs <;> simp

omit [CharP F 2] [Finite F] in
theorem eq_zero_of_frobPow {ι : Type} {M : Matrix ι ι F} (h : frobPow a M = 0) : M = 0 := by
  ext i j
  have := congrFun (congrFun h i) j
  simp only [frobPow, Matrix.map_apply, Matrix.zero_apply] at this
  exact pow_eq_zero_iff (by positivity) |>.mp this

theorem eq_zero_of_hermA (ha : 1 ≤ a) (hF : Nat.card F = 2 ^ (2 * a)) {ι : Type} [Fintype ι]
    (T : Matrix ι ι F →ₗ[F] Matrix ι ι F) (hT : ∀ Y ∈ hermA a ι F, T Y = 0) (Y : Matrix ι ι F) :
    T Y = 0 := by
  obtain ⟨θ, hθ⟩ := exists_ne_frob ha hF
  set p := (matFixEquiv hF hθ (∅ : Set (Matrix ι ι F))).symm ⟨Y, fun g hg => absurd hg id⟩
  have hp : (p.1 : Matrix ι ι F) + θ • (p.2 : Matrix ι ι F) = Y := by
    have := (matFixEquiv hF hθ (∅ : Set (Matrix ι ι F))).apply_symm_apply
      ⟨Y, fun g hg => absurd hg id⟩
    exact congrArg Subtype.val this
  rw [← hp, map_add, map_smul, hT _ (mem_hermFix.mp p.1.2).1, hT _ (mem_hermFix.mp p.2.2).1,
    smul_zero, add_zero]

theorem card_le_of_quadratic (ha : 1 ≤ a) (hF : Nat.card F = 2 ^ (2 * a))
    (E : Subgroup (StatedSp 2 F)) (hE : ∀ x ∈ E, x * x = 1)
    (hQ : ∀ x ∈ E, ∀ y ∈ E, ∀ Y ∈ hermA a (Fin 2 ⊕ Fin 2) F,
      tw a (spM y) (tw a (spM x) Y - Y) = tw a (spM x) Y - Y) :
    Nat.card E ≤ 2 ^ a := by
  classical
  have : Fintype F := Fintype.ofFinite F
  by_cases hbot : E = ⊥
  · rw [hbot, Subgroup.card_bot]
    exact Nat.one_le_two_pow
  obtain ⟨⟨x₀, hx₀E⟩, hx₀1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hbot
  have hx₀1' : x₀ ≠ 1 := fun h => hx₀1 (Subtype.ext h)
  obtain ⟨h, hh⟩ := exists_conj_le_unipotent (isPGroup_of_sq E hE)
  set v : Fin 2 ⊕ Fin 2 → F := spM h *ᵥ Pi.single (Sum.inl 0) 1 with hv
  have hvfix : ∀ y ∈ E, spM y *ᵥ v = v := by
    intro y hy
    have h1 := (unipotent_facts (hh y hy)).1
    have h2 : spM y * spM h = spM h * spM (h⁻¹ * y * h) := by
      rw [← spM_mul, ← spM_mul, show h * (h⁻¹ * y * h) = y * h by group]
    rw [hv, Matrix.mulVec_mulVec, h2, ← Matrix.mulVec_mulVec]
    exact congrArg (spM h *ᵥ ·) h1
  have hv0 : v ≠ 0 := by
    intro h0
    have h1 : spM h⁻¹ *ᵥ v = Pi.single (Sum.inl 0) 1 := by
      rw [hv, Matrix.mulVec_mulVec, ← spM_mul, inv_mul_cancel, spM_one, Matrix.one_mulVec]
    rw [h0, Matrix.mulVec_zero] at h1
    have := congrFun h1 (Sum.inl 0)
    simp at this
  have hQM : ∀ x ∈ E, ∀ y ∈ E, ∀ Y : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F,
      tw a (spM y) (tw a (spM x) Y - Y) - (tw a (spM x) Y - Y) = 0 := by
    intro x hx y hy Y
    let T : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F →ₗ[F] _ :=
      (twLin a (spM y) - LinearMap.id) ∘ₗ (twLin a (spM x) - LinearMap.id)
    have hT : ∀ Z, T Z = tw a (spM y) (tw a (spM x) Z - Z) - (tw a (spM x) Z - Z) := by
      intro Z
      simp [T, twLin_apply, tw_sub]
    rw [← hT]
    refine eq_zero_of_hermA ha hF T (fun Z hZ => ?_) Y
    rw [hT, hQ x hx y hy Z hZ, sub_self]
  have hexp : ∀ x ∈ E, ∀ y ∈ E, ∀ Y : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F,
      tw a (spM y) (tw a (spM x) Y - Y) - (tw a (spM x) Y - Y) =
        (spM y - 1) * Y * (frobPow a (spM x - 1))ᵀ + (spM x - 1) * Y * (frobPow a (spM y - 1))ᵀ +
          (spM y - 1) * (spM x - 1) * Y *
            (1 + (frobPow a (spM x - 1))ᵀ + (frobPow a (spM y - 1))ᵀ +
              (frobPow a (spM x - 1))ᵀ * (frobPow a (spM y - 1))ᵀ) +
          (1 + (spM x - 1) + (spM y - 1)) * Y *
            ((frobPow a (spM x - 1))ᵀ * (frobPow a (spM y - 1))ᵀ) := by
    intro x _ y _ Y
    rw [frobPow_sub_one, frobPow_sub_one, ← quad_expand]
    simp only [tw_apply, add_sub_cancel]
  have hvx : ∀ x ∈ E, (spM x - 1) *ᵥ v = 0 := fun x hx => by
    rw [Matrix.sub_mulVec, hvfix x hx, Matrix.one_mulVec, sub_self]
  have hprod : ∀ x ∈ E, ∀ y ∈ E, (spM y - 1) * (spM x - 1) = 0 ∧
      (frobPow a (spM x - 1))ᵀ * (frobPow a (spM y - 1))ᵀ = 0 := by
    intro x hx y hy
    have hσ : (frobPow a (spM x - 1))ᵀ * (frobPow a (spM y - 1))ᵀ = 0 := by
      have hz : ∀ z : Fin 2 ⊕ Fin 2 → F,
          z ᵥ* ((frobPow a (spM x - 1))ᵀ * (frobPow a (spM y - 1))ᵀ) = 0 := by
        intro z
        have h1 := hexp x hx y hy (Matrix.vecMulVec v z)
        rw [hQM x hx y hy] at h1
        have hu : (spM x - 1) * Matrix.vecMulVec v z = 0 := by
          rw [Matrix.mul_vecMulVec, hvx x hx, Matrix.zero_vecMulVec]
        have hw : (spM y - 1) * Matrix.vecMulVec v z = 0 := by
          rw [Matrix.mul_vecMulVec, hvx y hy, Matrix.zero_vecMulVec]
        have hA : (spM y - 1) * Matrix.vecMulVec v z * (frobPow a (spM x - 1))ᵀ = 0 := by
          rw [hw, Matrix.zero_mul]
        have hB : (spM x - 1) * Matrix.vecMulVec v z * (frobPow a (spM y - 1))ᵀ = 0 := by
          rw [hu, Matrix.zero_mul]
        have hC : ∀ M : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F,
            (spM y - 1) * (spM x - 1) * Matrix.vecMulVec v z * M = 0 := fun M => by
          rw [Matrix.mul_assoc (spM y - 1) (spM x - 1), hu, Matrix.mul_zero, Matrix.zero_mul]
        have hD : ∀ M : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F,
            (1 + (spM x - 1) + (spM y - 1)) * Matrix.vecMulVec v z * M =
              Matrix.vecMulVec v z * M := fun M => by
          simp only [Matrix.add_mul, hu, hw, Matrix.one_mul, add_zero]
        rw [hA, hB, hC, hD, zero_add, zero_add, zero_add, Matrix.vecMulVec_mul] at h1
        replace h1 := h1.symm
        funext i
        obtain ⟨j, hj⟩ : ∃ j, v j ≠ 0 := by
          by_contra h
          push Not at h
          exact hv0 (funext h)
        have := congrFun (congrFun h1 j) i
        rw [Matrix.vecMulVec_apply, Matrix.zero_apply] at this
        exact (mul_eq_zero.mp this).resolve_left hj
      ext i j
      have := congrFun (hz (Pi.single i 1)) j
      rwa [Matrix.single_one_vecMul] at this
    refine ⟨?_, hσ⟩
    apply eq_zero_of_frobPow (a := a)
    rw [frobPow_mul]
    have := congrArg Matrix.transpose hσ
    rwa [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.transpose_transpose,
      Matrix.transpose_zero] at this
  have hrel : ∀ x ∈ E, ∀ y ∈ E, ∀ p q r t : Fin 2 ⊕ Fin 2,
      (spM y - 1) p r * (spM x - 1) q t ^ 2 ^ a = (spM x - 1) p r * (spM y - 1) q t ^ 2 ^ a := by
    intro x hx y hy p q r t
    obtain ⟨h1, h2⟩ := hprod x hx y hy
    have h3 := hexp x hx y hy (Matrix.vecMulVec (Pi.single r 1) (Pi.single t 1))
    rw [hQM x hx y hy, h1, h2, Matrix.zero_mul, Matrix.zero_mul, Matrix.mul_zero, add_zero,
      add_zero] at h3
    have h4 := congrFun (congrFun h3 p) q
    rw [Matrix.zero_apply, Matrix.add_apply] at h4
    have e : ∀ M N : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F,
        (M * Matrix.vecMulVec (Pi.single r (1 : F)) (Pi.single t (1 : F)) * N) p q =
          M p r * N t q := fun M N => by
      rw [Matrix.mul_vecMulVec, Matrix.vecMulVec_mul, Matrix.vecMulVec_apply,
        Matrix.mulVec_single_one, Matrix.single_one_vecMul]
      rfl
    rw [e, e] at h4
    simp only [Matrix.transpose_apply, frobPow, Matrix.map_apply] at h4
    exact eq_of_add_eq_zero' h4.symm
  set u := spM x₀ - 1 with hu
  have hu0 : u ≠ 0 := by
    intro h
    apply hx₀1'
    apply spM_injective
    rw [spM_one]
    exact sub_eq_zero.mp h
  obtain ⟨q₀, t₀, hq₀⟩ : ∃ q t, u q t ≠ 0 := by
    by_contra h
    push Not at h
    exact hu0 (Matrix.ext h)
  have huσ : u q₀ t₀ ^ 2 ^ a ≠ 0 := pow_ne_zero _ hq₀
  let κ : ↥E → F := fun y => (spM (y : StatedSp 2 F) - 1) q₀ t₀ ^ 2 ^ a / u q₀ t₀ ^ 2 ^ a
  have hκ : ∀ y : ↥E, spM (y : StatedSp 2 F) - 1 = κ y • u := by
    intro y
    ext p r
    have := hrel x₀ hx₀E y y.2 p q₀ r t₀
    rw [← hu] at this
    rw [Matrix.smul_apply, smul_eq_mul]
    show (spM (y : StatedSp 2 F) - 1) p r =
      (spM (y : StatedSp 2 F) - 1) q₀ t₀ ^ 2 ^ a / u q₀ t₀ ^ 2 ^ a * u p r
    rw [div_mul_eq_mul_div, eq_div_iff huσ]
    linear_combination this
  have hκσ : ∀ y : ↥E, κ y ^ 2 ^ a = κ y := by
    intro y
    have h1 := hrel x₀ hx₀E y y.2 q₀ q₀ t₀ t₀
    rw [← hu] at h1
    have h2 := congrFun (congrFun (hκ y) q₀) t₀
    rw [Matrix.smul_apply, smul_eq_mul] at h2
    rw [h2, mul_pow] at h1
    have h3 : κ y * (u q₀ t₀ * u q₀ t₀ ^ 2 ^ a) = κ y ^ 2 ^ a * (u q₀ t₀ * u q₀ t₀ ^ 2 ^ a) := by
      linear_combination h1
    exact (mul_right_cancel₀ (mul_ne_zero hq₀ huσ) h3).symm
  have hinj : Function.Injective (fun y : ↥E =>
      (⟨κ y, hκσ y⟩ : {c : F // c ^ 2 ^ a = c})) := by
    intro y y' h
    have h1 : κ y = κ y' := congrArg Subtype.val h
    apply Subtype.ext
    apply spM_injective
    have h2 := hκ y
    have h3 := hκ y'
    rw [h1] at h2
    have := h2.trans h3.symm
    exact sub_left_injective this
  calc Nat.card E ≤ Nat.card {c : F // c ^ 2 ^ a = c} := Nat.card_le_card_of_injective _ hinj
    _ = (Finset.univ.filter fun c : F => c ^ 2 ^ a = c).card := by
        rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
    _ ≤ 2 ^ a := card_frobFix_le ha

end Quad

end CFSG.Quasithin.B45Sp4
