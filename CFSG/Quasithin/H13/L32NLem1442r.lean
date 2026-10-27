module

public import CFSG.Quasithin.H13.L32NLem1442q
public import CFSG.Quasithin.H13.L32N1447AModel

public section

namespace CFSG.Quasithin.H13.L1442Q

open Matrix L1442M Mat8Cert

@[expose] def gensG (b₁ b₂ : Bool) : List (List ℕ) :=
  if b₂ then (if b₁ then G5Cert.gSG else G5Cert.gAG) else G5ACert.gGA b₁

@[expose] def wsG (b₁ b₂ : Bool) : List (List ℕ) :=
  if b₂ then [[], [4], [3], [3, 4], [1], [4, 1], [3, 1], [3, 4, 1]]
  else if b₁ then [[], [2], [3, 3, 3, 2], [3, 3, 3, 3], [1], [2, 1], [3, 3, 3, 2, 1],
    [3, 3, 3, 3, 1]]
  else [[], [2], [2, 2], [3, 3, 2, 3], [1], [2, 1], [2, 2, 1], [3, 3, 2, 3, 1]]

@[expose] def matsG (b₁ b₂ : Bool) : List (List ℕ) :=
  if b₂ then [[1, 2, 4, 8, 16, 32, 64, 128], [2, 3, 12, 4, 32, 48, 192, 64],
    [4, 8, 1, 2, 64, 128, 16, 32], [8, 12, 3, 1, 128, 192, 48, 16],
    [16, 32, 64, 128, 1, 2, 4, 8], [32, 48, 192, 64, 2, 3, 12, 4],
    [64, 128, 16, 32, 4, 8, 1, 2], [128, 192, 48, 16, 8, 12, 3, 1]]
  else if b₁ then [[1, 2, 4, 8, 16, 32, 64, 128], [2, 1, 4, 8, 32, 16, 64, 128],
    [4, 12, 5, 6, 64, 192, 80, 96], [8, 9, 10, 12, 128, 144, 160, 192],
    [16, 32, 64, 128, 1, 2, 4, 8], [32, 16, 64, 128, 2, 1, 4, 8],
    [64, 192, 80, 96, 4, 12, 5, 6], [128, 144, 160, 192, 8, 9, 10, 12]]
  else [[1, 2, 4, 8, 16, 32, 64, 128], [2, 4, 1, 8, 32, 64, 16, 128],
    [4, 1, 2, 8, 64, 16, 32, 128], [8, 12, 9, 10, 128, 192, 144, 160],
    [16, 32, 64, 128, 1, 2, 4, 8], [32, 64, 16, 128, 2, 4, 1, 8],
    [64, 16, 32, 128, 4, 1, 2, 8], [128, 192, 144, 160, 8, 12, 9, 10]]

@[expose] def allowedG (b₁ b₂ : Bool) : List ℕ := if b₂ && !b₁ then [0, 1, 2, 3] else [0, 1]

@[expose] def qNG (b₂ : Bool) : ℕ → Bool := if b₂ then G5Cert.quadN else G5ACert.quadA

@[expose] def minvG (b₂ : Bool) : List ℕ :=
  if b₂ then [192, 64, 48, 16, 12, 4, 3, 1] else [224, 208, 176, 112, 14, 13, 11, 7]

@[expose] def formCheck (b₁ b₂ : Bool) : Bool :=
  let gens := gensG b₁ b₂
  let q := qNG b₂
  (gens.all validB) &&
    (gens.all fun c => (List.range 256).all fun n => q (mv8 c n) == q n) &&
    ((List.range 256).all fun n => n == 0 ||
      (List.range 8).any fun k => q (n ^^^ 2 ^ k) ^^ q n ^^ q (2 ^ k)) &&
    ((matsG b₁ b₂).length == 8) &&
    ((List.range 8).all fun i => (matsG b₁ b₂).getD i [] == evalW gens ((wsG b₁ b₂).getD i [])) &&
    ((List.range 8).all fun i => mv8 ((matsG b₁ b₂).getD i []) 1 == 2 ^ i) &&
    ((List.range 256).all fun v =>
      !(gens.all fun c => mul8 (colsM (matsG b₁ b₂) v) c == mul8 c (colsM (matsG b₁ b₂) v)) ||
        (allowedG b₁ b₂).contains v) &&
    ((List.range 256).all fun n => n == 0 ||
      gens.any fun c => (List.range 8).any fun j => S8Cert.dotN (c.getD j 0) n != n.testBit j)

theorem cov_of_codes {S : Set (GL (Fin 8) (ZMod 2))} {gens : List (List ℕ)}
    (hS : ∀ c ∈ gens, ∃ g ∈ S, colsOf (g : Matrix (Fin 8) (Fin 8) (ZMod 2)) = c)
    (h : ∀ n < 256, n ≠ 0 → ∃ c ∈ gens, ∃ j < 8, S8Cert.dotN (c.getD j 0) n ≠ n.testBit j) :
    ∀ w : Fin 8 → ZMod 2, (∀ g ∈ S, (g : Matrix (Fin 8) (Fin 8) (ZMod 2))ᵀ *ᵥ w = w) → w = 0 := by
  intro w hw
  by_contra hne
  have hn : code8 w ≠ 0 := fun h0 => hne (by rw [← vec8_code8 w, h0, vec8_zero])
  obtain ⟨c, hc, j, hj, hcj⟩ := h _ (code8_lt w) hn
  obtain ⟨g, hg, rfl⟩ := hS c hc
  apply hcj
  have h1 := congrFun (hw g hg) ⟨j, hj⟩
  have h2 : ((g : Matrix (Fin 8) (Fin 8) (ZMod 2))ᵀ *ᵥ w) ⟨j, hj⟩ =
      b2z (S8Cert.dotN ((colsOf (g : Matrix (Fin 8) (Fin 8) (ZMod 2))).getD j 0) (code8 w)) := by
    rw [S8Cert.dotN_spec, vec8_code8]
    have h3 : vec8 ((colsOf (g : Matrix (Fin 8) (Fin 8) (ZMod 2))).getD j 0) =
        fun i => (g : Matrix (Fin 8) (Fin 8) (ZMod 2)) i ⟨j, hj⟩ := by
      funext i
      have := congrFun (congrFun (dec8_colsOf (g : Matrix (Fin 8) (Fin 8) (ZMod 2))) i) ⟨j, hj⟩
      rw [← this]
      rfl
    rw [h3, Matrix.mulVec, dotProduct, dotProduct]
    rfl
  have h4 : w ⟨j, hj⟩ = b2z ((code8 w).testBit j) :=
    calc w ⟨j, hj⟩ = vec8 (code8 w) ⟨j, hj⟩ := by rw [vec8_code8]
      _ = b2z ((code8 w).testBit j) := rfl
  rw [h2, h4] at h1
  exact b2z_inj h1

theorem formCheck_tt : formCheck true true = true := by decide +kernel

theorem formCheck_ft : formCheck false true = true := by decide +kernel

theorem formCheck_tf : formCheck true false = true := by decide +kernel

theorem formCheck_ff : formCheck false false = true := by decide +kernel

theorem formCheck_all (b₁ b₂ : Bool) : formCheck b₁ b₂ = true := by
  cases b₁ <;> cases b₂
  · exact formCheck_ff
  · exact formCheck_ft
  · exact formCheck_tf
  · exact formCheck_tt

theorem formCheck_spec (b₁ b₂ : Bool) :
    (∀ c ∈ gensG b₁ b₂, Valid8 c) ∧
    (∀ c ∈ gensG b₁ b₂, ∀ n < 256, qNG b₂ (mv8 c n) = qNG b₂ n) ∧
    (∀ n < 256, n ≠ 0 → ∃ k < 8, (qNG b₂ (n ^^^ 2 ^ k) ^^ qNG b₂ n ^^ qNG b₂ (2 ^ k)) = true) ∧
    (matsG b₁ b₂).length = 8 ∧
    (∀ i < 8, (matsG b₁ b₂).getD i [] = evalW (gensG b₁ b₂) ((wsG b₁ b₂).getD i [])) ∧
    (∀ i < 8, mv8 ((matsG b₁ b₂).getD i []) 1 = 2 ^ i) ∧
    (∀ v < 256, (∀ c ∈ gensG b₁ b₂, mul8 (colsM (matsG b₁ b₂) v) c =
      mul8 c (colsM (matsG b₁ b₂) v)) → v ∈ allowedG b₁ b₂) ∧
    (∀ n < 256, n ≠ 0 → ∃ c ∈ gensG b₁ b₂, ∃ j < 8,
      S8Cert.dotN (c.getD j 0) n ≠ n.testBit j) := by
  have h := formCheck_all b₁ b₂
  simp only [formCheck, Bool.and_eq_true, List.all_eq_true, beq_iff_eq, List.mem_range] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨hv, hinv⟩, hnd⟩, hlen⟩, hmats⟩, hbas⟩, hcom⟩, hcov⟩ := h
  refine ⟨fun c hc => S7Cert.validB_iff.mp (hv c hc), hinv, fun n hn hn0 => ?_, hlen, hmats,
    hbas, fun v hv' hcomm => ?_, fun n hn hn0 => ?_⟩
  · have := hnd n hn
    simp only [Bool.or_eq_true, beq_iff_eq, hn0, false_or, List.any_eq_true, List.mem_range] at this
    exact this
  · have := hcom v hv'
    simp only [Bool.or_eq_true, Bool.not_eq_true', List.contains_iff_mem] at this
    rcases this with h1 | h1
    · exfalso
      have h2 : ((gensG b₁ b₂).all fun c => mul8 (colsM (matsG b₁ b₂) v) c ==
          mul8 c (colsM (matsG b₁ b₂) v)) = true := by
        simp only [List.all_eq_true, beq_iff_eq]
        exact hcomm
      rw [h2] at h1
      exact Bool.noConfusion h1
    · exact h1
  · have := hcov n hn
    simp only [Bool.or_eq_true, beq_iff_eq, hn0, false_or, List.any_eq_true, List.mem_range,
      bne_iff_ne, ne_eq] at this
    obtain ⟨c, hc, j, hj, hcj⟩ := this
    exact ⟨c, hc, j, hj, hcj⟩

theorem gensG_unit (b₁ b₂ : Bool) : ∀ c ∈ gensG b₁ b₂, ∃ u : GL (Fin 8) (ZMod 2),
    (u : Matrix (Fin 8) (Fin 8) (ZMod 2)) = dec8 c := by
  unfold gensG
  cases b₂
  · exact G5ACert.gGA_unit b₁
  · cases b₁
    · exact G5Cert.gAG_unit
    · exact G5Cert.gSG_unit

theorem g5_eq (b₁ b₂ : Bool) : g5 b₁ b₂ = genSub (gensG b₁ b₂) := by
  unfold gensG
  cases b₂
  · exact G5ACert.gA5_eq b₁
  · cases b₁
    · exact G5Cert.gA_eq
    · exact G5Cert.gS_eq

theorem qNG_spec (b₂ : Bool) (n : ℕ) : b2z (qNG b₂ n) = quadOf (q5 b₂) (vec8 n) := by
  cases b₂
  · exact Q1447A.quadA_spec n
  · exact G5Cert.quadN_spec n

theorem minvG_spec (b₂ : Bool) : (q5 b₂ + (q5 b₂)ᵀ) * dec8 (minvG b₂) = 1 := by
  cases b₂ <;> decide +kernel

@[expose] def sW : List ℕ := [2, 3, 8, 12, 32, 48, 128, 192]

@[expose] def sW2 : List ℕ := [3, 1, 12, 4, 48, 16, 192, 64]

@[expose] noncomputable def pairsG (b₁ b₂ : Bool) :
    List (Matrix (Fin 8) (Fin 8) (ZMod 2) × Matrix (Fin 8) (Fin 8) (ZMod 2)) :=
  if b₂ && !b₁ then [(1, 1), (dec8 sW, dec8 sW2), (dec8 sW2, dec8 sW)] else [(1, 1)]

theorem colsM_zero (b₁ b₂ : Bool) : colsM (matsG b₁ b₂) 0 = [0, 0, 0, 0, 0, 0, 0, 0] := by
  cases b₁ <;> cases b₂ <;> decide +kernel

theorem colsM_one (b₁ b₂ : Bool) : colsM (matsG b₁ b₂) 1 = one8 := by
  cases b₁ <;> cases b₂ <;> decide +kernel

theorem colsM_two : colsM (matsG false true) 2 = sW := by decide +kernel

theorem colsM_three : colsM (matsG false true) 3 = sW2 := by decide +kernel

theorem dec8_zeros : dec8 [0, 0, 0, 0, 0, 0, 0, 0] = 0 := by decide +kernel

theorem sW_mul : mul8 sW sW2 = one8 ∧ mul8 sW2 sW = one8 := by decide +kernel

theorem sW_comm : ∀ c ∈ gensG false true, mul8 sW c = mul8 c sW ∧ mul8 sW2 c = mul8 c sW2 := by
  decide +kernel

theorem sW_pol : (dec8 sW2)ᵀ * (q5 true + (q5 true)ᵀ) * dec8 sW2 =
      (q5 true + (q5 true)ᵀ) * dec8 sW ∧
    (dec8 sW)ᵀ * (q5 true + (q5 true)ᵀ) * dec8 sW = (q5 true + (q5 true)ᵀ) * dec8 sW2 := by
  constructor <;> decide +kernel

theorem pol_of_mat {Q₀ A m : Matrix (Fin 8) (Fin 8) (ZMod 2)}
    (h : mᵀ * (Q₀ + Q₀ᵀ) * m = (Q₀ + Q₀ᵀ) * A) (x y : Fin 8 → ZMod 2) :
    quadOf Q₀ (m *ᵥ (x + y)) + quadOf Q₀ (m *ᵥ x) + quadOf Q₀ (m *ᵥ y) =
      polarB Q₀ (A *ᵥ y) x := by
  rw [Matrix.mulVec_add, ← polarB_apply, polarB_def, polarB_symm, polarB_def, Matrix.mulVec_mulVec,
    Matrix.dotProduct_mulVec, ← Matrix.vecMul_transpose, Matrix.vecMul_vecMul,
    ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, ← Matrix.mul_assoc, h]

theorem quad_eq_model (b₁ b₂ : Bool) {Q' : (Fin 8 → ZMod 2) → ZMod 2}
    {B' : LinearMap.BilinForm (ZMod 2) (Fin 8 → ZMod 2)}
    (hQ' : ∀ x y, Q' (x + y) = Q' x + Q' y + B' x y) (hB' : B' ≠ 0)
    (hinv' : ∀ g ∈ g5 b₁ b₂, ∀ x, Q' ((g : Matrix (Fin 8) (Fin 8) (ZMod 2)) *ᵥ x) = Q' x) :
    ∃ m : GL (Fin 8) (ZMod 2), (∀ g ∈ g5 b₁ b₂, m * g = g * m) ∧
      ∀ x, Q' x = quadOf (q5 b₂) ((m : Matrix (Fin 8) (Fin 8) (ZMod 2)) *ᵥ x) := by
  classical
  obtain ⟨hval, hinvc, hndc, hlen, hmats, hbas, hcomc, hcovc⟩ := formCheck_spec b₁ b₂
  set S : Set (GL (Fin 8) (ZMod 2)) :=
    {g | colsOf (g : Matrix (Fin 8) (Fin 8) (ZMod 2)) ∈ gensG b₁ b₂} with hS
  have hSg : ∀ g ∈ S, g ∈ g5 b₁ b₂ := fun g hg => by
    rw [g5_eq]
    exact Subgroup.subset_closure hg
  have hgensS : ∀ c ∈ gensG b₁ b₂, ∃ g ∈ S, colsOf (g : Matrix (Fin 8) (Fin 8) (ZMod 2)) = c := by
    intro c hc
    obtain ⟨u, hu⟩ := gensG_unit b₁ b₂ c hc
    have hcu : colsOf (u : Matrix (Fin 8) (Fin 8) (ZMod 2)) = c := by
      rw [hu, colsOf_dec8 (hval c hc)]
    exact ⟨u, show colsOf (u : Matrix (Fin 8) (Fin 8) (ZMod 2)) ∈ gensG b₁ b₂ by rw [hcu]; exact hc,
      hcu⟩
  have hinv₀ : ∀ g ∈ S, ∀ x, quadOf (q5 b₂) ((g : Matrix (Fin 8) (Fin 8) (ZMod 2)) *ᵥ x) =
      quadOf (q5 b₂) x := fun g hg => inv_of_codes (qNG_spec b₂) (hinvc _ hg)
  have hnd₀ := nondeg_of_codes (qNG_spec b₂) hndc
  have hcomm : ∀ A : Matrix (Fin 8) (Fin 8) (ZMod 2),
      (∀ g ∈ S, A * (g : Matrix (Fin 8) (Fin 8) (ZMod 2)) =
        (g : Matrix (Fin 8) (Fin 8) (ZMod 2)) * A) → A = 0 ∨ ∃ p ∈ pairsG b₁ b₂, A = p.1 := by
    intro A hA
    have hA' : ∀ c ∈ gensG b₁ b₂, A * dec8 c = dec8 c * A := by
      intro c hc
      obtain ⟨g, hg, hgc⟩ := hgensS c hc
      rw [← hgc, dec8_colsOf]
      exact hA g hg
    obtain ⟨v, hv, hAv⟩ := comm_of_codes hval hlen hmats hbas hcomc hA'
    unfold allowedG at hv
    unfold pairsG
    cases b₁ <;> cases b₂ <;>
      simp only [Bool.and_true, Bool.and_false, Bool.not_true, Bool.not_false,
        Bool.false_eq_true, ↓reduceIte, List.mem_cons, List.not_mem_nil, or_false] at hv ⊢
    · rcases hv with rfl | rfl
      · exact Or.inl (by rw [hAv, colsM_zero, dec8_zeros])
      · exact Or.inr ⟨(1, 1), by simp, by rw [hAv, colsM_one, dec8_one8]⟩
    · rcases hv with rfl | rfl | rfl | rfl
      · exact Or.inl (by rw [hAv, colsM_zero, dec8_zeros])
      · exact Or.inr ⟨(1, 1), by simp, by rw [hAv, colsM_one, dec8_one8]⟩
      · exact Or.inr ⟨(dec8 sW, dec8 sW2), by simp, by rw [hAv, colsM_two]⟩
      · exact Or.inr ⟨(dec8 sW2, dec8 sW), by simp, by rw [hAv, colsM_three]⟩
    · rcases hv with rfl | rfl
      · exact Or.inl (by rw [hAv, colsM_zero, dec8_zeros])
      · exact Or.inr ⟨(1, 1), by simp, by rw [hAv, colsM_one, dec8_one8]⟩
    · rcases hv with rfl | rfl
      · exact Or.inl (by rw [hAv, colsM_zero, dec8_zeros])
      · exact Or.inr ⟨(1, 1), by simp, by rw [hAv, colsM_one, dec8_one8]⟩
  have hscal : ∀ g ∈ S, b₂ = true → b₁ = false →
      dec8 sW * (g : Matrix (Fin 8) (Fin 8) (ZMod 2)) =
        (g : Matrix (Fin 8) (Fin 8) (ZMod 2)) * dec8 sW ∧
      dec8 sW2 * (g : Matrix (Fin 8) (Fin 8) (ZMod 2)) =
        (g : Matrix (Fin 8) (Fin 8) (ZMod 2)) * dec8 sW2 := by
    rintro g hg rfl rfl
    have hc := sW_comm _ hg
    have hlg : (colsOf (g : Matrix (Fin 8) (Fin 8) (ZMod 2))).length = 8 :=
      (valid8_colsOf _).1
    rw [← dec8_colsOf (g : Matrix (Fin 8) (Fin 8) (ZMod 2)), ← dec8_mul8 _ _ hlg,
      ← dec8_mul8 _ _ rfl, hc.1, ← dec8_mul8 _ _ hlg, ← dec8_mul8 _ _ rfl, hc.2]
    exact ⟨rfl, rfl⟩
  have hLpol : ∀ p ∈ pairsG b₁ b₂, ∀ x y, quadOf (q5 b₂) (p.2 *ᵥ (x + y)) +
      quadOf (q5 b₂) (p.2 *ᵥ x) + quadOf (q5 b₂) (p.2 *ᵥ y) = polarB (q5 b₂) (p.1 *ᵥ y) x := by
    intro p hp
    unfold pairsG at hp
    by_cases hb : b₂ && !b₁
    · simp only [hb, ↓reduceIte] at hp
      have hb₂ : b₂ = true := by revert hb; cases b₂ <;> simp
      subst hb₂
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl | rfl
      · exact pol_of_mat (by simp)
      · exact pol_of_mat sW_pol.1
      · exact pol_of_mat sW_pol.2
    · simp only [hb, Bool.false_eq_true, ↓reduceIte] at hp
      rw [List.mem_singleton.mp hp]
      exact pol_of_mat (by simp)
  have hLinv : ∀ p ∈ pairsG b₁ b₂, ∀ g ∈ S, ∀ x, quadOf (q5 b₂) (p.2 *ᵥ
      ((g : Matrix (Fin 8) (Fin 8) (ZMod 2)) *ᵥ x)) = quadOf (q5 b₂) (p.2 *ᵥ x) := by
    intro p hp g hg x
    unfold pairsG at hp
    by_cases hb : b₂ && !b₁
    · simp only [hb, ↓reduceIte] at hp
      have hb₂ : b₂ = true := by revert hb; cases b₂ <;> simp
      have hb₁ : b₁ = false := by revert hb; cases b₁ <;> simp
      obtain ⟨h1, h2⟩ := hscal g hg hb₂ hb₁
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl | rfl
      · rw [Matrix.one_mulVec, Matrix.one_mulVec, hinv₀ g hg]
      · show quadOf (q5 b₂) (dec8 sW2 *ᵥ ((g : Matrix (Fin 8) (Fin 8) (ZMod 2)) *ᵥ x)) =
          quadOf (q5 b₂) (dec8 sW2 *ᵥ x)
        rw [Matrix.mulVec_mulVec, h2, ← Matrix.mulVec_mulVec, hinv₀ g hg]
      · show quadOf (q5 b₂) (dec8 sW *ᵥ ((g : Matrix (Fin 8) (Fin 8) (ZMod 2)) *ᵥ x)) =
          quadOf (q5 b₂) (dec8 sW *ᵥ x)
        rw [Matrix.mulVec_mulVec, h1, ← Matrix.mulVec_mulVec, hinv₀ g hg]
    · simp only [hb, Bool.false_eq_true, ↓reduceIte] at hp
      rw [List.mem_singleton.mp hp, Matrix.one_mulVec, Matrix.one_mulVec, hinv₀ g hg]
  have hcov := cov_of_codes hgensS hcovc
  obtain ⟨p, hp, hpQ⟩ := exists_eq_quad hinv₀ hnd₀ (minvG_spec b₂) hcomm hLpol hLinv hcov hQ' hB'
    fun g hg => hinv' g (hSg g hg)
  unfold pairsG at hp
  by_cases hb : b₂ && !b₁
  · simp only [hb, ↓reduceIte] at hp
    have hb₂ : b₂ = true := by revert hb; cases b₂ <;> simp
    have hb₁ : b₁ = false := by revert hb; cases b₁ <;> simp
    have hcen : ∀ (u : GL (Fin 8) (ZMod 2)), ((u : Matrix (Fin 8) (Fin 8) (ZMod 2)) = dec8 sW ∨
        (u : Matrix (Fin 8) (Fin 8) (ZMod 2)) = dec8 sW2) → ∀ g ∈ g5 b₁ b₂, u * g = g * u := by
      intro u hu g hg
      have hle : g5 b₁ b₂ ≤ Subgroup.centralizer ({u} : Set (GL (Fin 8) (ZMod 2))) := by
        rw [g5_eq]
        refine (Subgroup.closure_le _).mpr fun h hh => ?_
        rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff]
        obtain ⟨h1, h2⟩ := hscal h hh hb₂ hb₁
        apply Units.ext
        rw [Units.val_mul, Units.val_mul]
        rcases hu with hu | hu <;> rw [hu]
        · exact h1.symm
        · exact h2.symm
      exact (Subgroup.mem_centralizer_singleton_iff.mp (hle hg)).symm
    have hmul := sW_mul
    let uW : GL (Fin 8) (ZMod 2) := ⟨dec8 sW, dec8 sW2,
      by rw [← dec8_mul8 _ _ rfl, hmul.1, dec8_one8],
      by rw [← dec8_mul8 _ _ rfl, hmul.2, dec8_one8]⟩
    let uW2 : GL (Fin 8) (ZMod 2) := ⟨dec8 sW2, dec8 sW,
      by rw [← dec8_mul8 _ _ rfl, hmul.2, dec8_one8],
      by rw [← dec8_mul8 _ _ rfl, hmul.1, dec8_one8]⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl
    · exact ⟨1, fun g _ => by rw [one_mul, mul_one], fun x => by rw [hpQ, Units.val_one]⟩
    · exact ⟨uW2, hcen uW2 (Or.inr rfl), hpQ⟩
    · exact ⟨uW, hcen uW (Or.inl rfl), hpQ⟩
  · simp only [hb, Bool.false_eq_true, ↓reduceIte] at hp
    rw [List.mem_singleton.mp hp] at hpQ
    exact ⟨1, fun g _ => by rw [one_mul, mul_one], fun x => by rw [hpQ, Units.val_one]⟩

end CFSG.Quasithin.H13.L1442Q
