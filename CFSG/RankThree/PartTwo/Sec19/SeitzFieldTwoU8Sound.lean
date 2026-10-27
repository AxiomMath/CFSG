module

public import Certificates.Data.HuppertU38F.Check
public import CFSG.LieType.SeitzGeneration.UnitaryPhanShift
public import CFSG.RankThree.PartTwo.KFacts.AutPSU
public import CFSG.LieType.SeitzGeneration.HeisSmallSound

public section

namespace CFSG.RankThree.PartTwo.Sec19.U38F

open CFSG.LieType.SeitzGeneration CFSG.LieType.SeitzGeneration.HeisSmall HuppertU38F
open CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial Matrix

theorem mem_cols4 {a b c : Q8} (ha : a ∈ l4) (hb : b ∈ l4) (hc : c ∈ l4) :
    (a, b, c) ∈ cols4 := by
  simp only [cols4, List.mem_flatMap, List.mem_map]
  exact ⟨a, ha, b, hb, c, hc, rfl⟩

theorem unitaryOk_ip {A : M3 Q8} (hu : unitaryOk A = true) :
    ip (A.a00, A.a10, A.a20) (A.a00, A.a10, A.a20) = 1 ∧
    ip (A.a01, A.a11, A.a21) (A.a01, A.a11, A.a21) = 1 ∧
    ip (A.a02, A.a12, A.a22) (A.a02, A.a12, A.a22) = 1 ∧
    ip (A.a00, A.a10, A.a20) (A.a01, A.a11, A.a21) = 0 ∧
    ip (A.a00, A.a10, A.a20) (A.a02, A.a12, A.a22) = 0 ∧
    ip (A.a01, A.a11, A.a21) (A.a02, A.a12, A.a22) = 0 := by
  have h := of_decide_eq_true hu
  refine ⟨congrArg M3.a00 h, congrArg M3.a11 h, congrArg M3.a22 h, congrArg M3.a01 h,
    congrArg M3.a02 h, congrArg M3.a12 h⟩

theorem forallUnitary_sound {P : M3 Q8 → Bool} (hP : forallUnitary P = true) {A : M3 Q8}
    (hA : entriesL4 A = true) (hu : unitaryOk A = true) : P A = true := by
  obtain ⟨h00, h01, h02, h10, h11, h12, h20, h21, h22⟩ := of_decide_eq_true hA
  obtain ⟨e0, e1, e2, e01, e02, e12⟩ := unitaryOk_ip hu
  have s1 : stage1 (A.a00, A.a10, A.a20) = true := decide_eq_true e0
  have s2 : stage2 (A.a00, A.a10, A.a20) (A.a01, A.a11, A.a21) = true := decide_eq_true ⟨e1, e01⟩
  have s3 : stage3 (A.a00, A.a10, A.a20) (A.a01, A.a11, A.a21) (A.a02, A.a12, A.a22) = true :=
    decide_eq_true ⟨e2, e02, e12⟩
  unfold forallUnitary at hP
  rw [List.all_eq_true] at hP
  have h0 := hP _ (mem_cols4 h00 h10 h20)
  rw [s1, Bool.not_true, Bool.false_or, List.all_eq_true] at h0
  have h1 := h0 _ (mem_cols4 h01 h11 h21)
  rw [s2, Bool.not_true, Bool.false_or, List.all_eq_true] at h1
  have h2 := h1 _ (mem_cols4 h02 h12 h22)
  rw [s3, Bool.not_true, Bool.false_or] at h2
  exact h2

theorem mem_orbitOf {gu : List (M3 Q8)} {Y A : M3 Q8} :
    A ∈ orbitOf gu Y ↔ ∃ g ∈ gu, ∃ l ∈ f4nz, A = M3.smul l (g * Y * gstar g) := by
  simp only [orbitOf, List.mem_flatMap, List.mem_map]
  constructor
  · rintro ⟨g, hg, l, hl, rfl⟩
    exact ⟨g, hg, l, hl, rfl⟩
  · rintro ⟨g, hg, l, hl, rfl⟩
    exact ⟨g, hg, l, hl, rfl⟩

theorem u38Check_parts {letters : List (M3 Q8)} {words2 : List (List ℕ)} {table : List U38Entry}
    (h : u38Check letters words2 table = true) :
    guList.all (fun g => unitaryOk g && entriesL4 g) = true ∧
    coverBool 8 (words2.map (evalW letters)) = true ∧
    table.all (u38EntryOk letters) = true ∧
    forallUnitary (classOk (table.map fun e => orbitOf guList e.Y)) = true := by
  unfold u38Check at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h
  exact ⟨h1, h2, h3, h4⟩

theorem class_sound {letters : List (M3 Q8)} {words2 : List (List ℕ)} {table : List U38Entry}
    (h : u38Check letters words2 table = true) {A : M3 Q8} (hA : entriesL4 A = true)
    (hu : unitaryOk A = true) (hns : isScalar A = false) (h3 : isScalar (A * A * A) = true) :
    ∃ e ∈ table, ∃ g ∈ guList, (entriesL4 g = true ∧ unitaryOk g = true) ∧
      ∃ l ∈ f4nz, A = M3.smul l (g * e.Y * gstar g) := by
  obtain ⟨hgu, -, -, hcls⟩ := u38Check_parts h
  have h1 := forallUnitary_sound hcls hA hu
  unfold classOk at h1
  rw [hns, h3] at h1
  simp only [Bool.false_or, Bool.not_true, Bool.or_eq_true, List.any_eq_true, decide_eq_true_eq,
    List.mem_map, Bool.false_eq_true, false_or] at h1
  obtain ⟨o, ⟨e, he, rfl⟩, hAo⟩ := h1
  obtain ⟨g, hg, l, hl, hAe⟩ := mem_orbitOf.1 hAo
  have hg' := (List.all_eq_true.1 hgu) g hg
  rw [Bool.and_eq_true] at hg'
  exact ⟨e, he, g, hg, ⟨hg'.2, hg'.1⟩, l, hl, hAe⟩

theorem entryOk_spec {letters : List (M3 Q8)} {e : U38Entry} (h : u38EntryOk letters e = true) :
    (∀ G ∈ e.gens, sgOk G = true ∧ (entriesL4 G = true ∨ commutes G e.Y = true)) ∧
      e.words.map (evalW e.gens) = letters := by
  unfold u38EntryOk at h
  rw [Bool.and_eq_true, List.all_eq_true] at h
  refine ⟨fun G hG => ?_, of_decide_eq_true h.2⟩
  have := h.1 G hG
  rw [Bool.and_eq_true, Bool.or_eq_true] at this
  exact this

theorem sgOk_spec {G : M3 Q8} (h : sgOk G = true) :
    G.det = 1 ∧ (G.map (· ^ 8)).transpose * G = 1 := by
  unfold sgOk at h
  rw [Bool.and_eq_true] at h
  exact ⟨of_decide_eq_true h.1, of_decide_eq_true h.2⟩

section KLevel

variable {ℓ f : ℕ} {K : Type} [Field K]

def GoodQ (Q : Subgroup (unitarySU ℓ f K 3)) (A : Matrix (Fin 3) (Fin 3) K) : Prop :=
  ∃ g ∈ Q, ((g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = A

theorem goodQ_one (Q : Subgroup (unitarySU ℓ f K 3)) : GoodQ Q (1 : Matrix (Fin 3) (Fin 3) K) :=
  ⟨1, Q.one_mem, rfl⟩

theorem goodQ_mul {Q : Subgroup (unitarySU ℓ f K 3)} {A B : Matrix (Fin 3) (Fin 3) K}
    (hA : GoodQ Q A) (hB : GoodQ Q B) : GoodQ Q (A * B) := by
  obtain ⟨g, hg, rfl⟩ := hA
  obtain ⟨g', hg', rfl⟩ := hB
  exact ⟨g * g', Q.mul_mem hg hg', rfl⟩

theorem goodQ_evalW {Q : Subgroup (unitarySU ℓ f K 3)} {L : Type} [Field L] (ι : L →+* K)
    {letters : List (M3 L)} (hl : ∀ x ∈ letters, GoodQ Q (toMat ι x)) :
    ∀ w : List ℕ, GoodQ Q (toMat ι (evalW letters w))
  | [] => by simpa [evalW, toMat_one] using goodQ_one Q
  | i :: w => by
    rw [evalW, toMat_mul]
    refine goodQ_mul ?_ (goodQ_evalW ι hl w)
    by_cases hi : i < letters.length
    · rw [List.getD_eq_getElem _ _ hi]
      exact hl _ (List.getElem_mem hi)
    · rw [List.getD_eq_default _ _ (not_lt.1 hi), toMat_one]
      exact goodQ_one Q

theorem heisB12_le_of_goodQ {L : Type} [Field L] [DecidableEq L] [Fintype L]
    (h : UnitaryFieldData ℓ f K) (ι : L →+* K) (hι : Function.Surjective ι) {q : ℕ}
    (hq : ℓ ^ f = q) {Q : Subgroup (unitarySU ℓ f K 3)} {letters : List (M3 L)}
    {ws₂ : List (List ℕ)} (hl : ∀ x ∈ letters, GoodQ Q (toMat ι x))
    (hcov : CoverOk q (ws₂.map (evalW letters))) : heisB12 ℓ f K ≤ Q := by
  subst hq
  have hL2 : ∀ x ∈ ws₂.map (evalW letters), GoodQ Q (toMat ι x) := by
    intro x hx
    obtain ⟨w, -, rfl⟩ := List.mem_map.1 hx
    exact goodQ_evalW ι hl w
  intro g hg
  obtain ⟨A, hA, hgA⟩ := mem_heisB12.1 hg
  obtain ⟨hdet, hu⟩ := (mem_unitarySU_iff h).1 hA
  obtain ⟨e10, e11, enorm⟩ := su2_entries h hdet hu
  obtain ⟨a, ha⟩ := hι ((A : Matrix (Fin 2) (Fin 2) K) 0 0)
  obtain ⟨b, hb⟩ := hι ((A : Matrix (Fin 2) (Fin 2) K) 0 1)
  have hn : a * a ^ ℓ ^ f + b * b ^ ℓ ^ f = 1 := by
    apply ι.injective
    simp only [map_add, map_mul, map_pow, ha, hb, enorm, map_one]
  obtain ⟨g', hg', hgg⟩ := hL2 _ (hcov a b hn)
  have hmat : toMat ι (blockM3 (ℓ ^ f) a b) = ((g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) := by
    rw [hgA]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [toMat, blockM3, ha, hb, e10, e11]
  have : g' = g := Subtype.ext (Units.ext (hgg.trans hmat))
  exact this ▸ hg'

theorem fixed_of_mem_l4 (ι : Q8 →+* K) {σ : K ≃+* K} (hσω : σ (ι w0) = ι w0) {a : Q8}
    (ha : a ∈ l4) : σ (ι a) = ι a := by
  simp only [l4, List.mem_cons, List.not_mem_nil, or_false] at ha
  rcases ha with rfl | rfl | rfl | rfl
  · simp
  · simp
  · exact hσω
  · rw [map_mul, map_mul, hσω]

theorem map_toMat_fixed (ι : Q8 →+* K) {σ : K ≃+* K} (hσω : σ (ι w0) = ι w0) {G : M3 Q8}
    (hE : entriesL4 G = true) : (toMat ι G).map σ = toMat ι G := by
  obtain ⟨h00, h01, h02, h10, h11, h12, h20, h21, h22⟩ := of_decide_eq_true hE
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp only [Matrix.map_apply, toMat, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Matrix.of_apply,
      Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val',
      Matrix.cons_val_fin_one, Fin.isValue] <;>
    first
      | exact fixed_of_mem_l4 ι hσω h00 | exact fixed_of_mem_l4 ι hσω h01
      | exact fixed_of_mem_l4 ι hσω h02 | exact fixed_of_mem_l4 ι hσω h10
      | exact fixed_of_mem_l4 ι hσω h11 | exact fixed_of_mem_l4 ι hσω h12
      | exact fixed_of_mem_l4 ι hσω h20 | exact fixed_of_mem_l4 ι hσω h21
      | exact fixed_of_mem_l4 ι hσω h22

theorem exists_su_of_matrix (h : UnitaryFieldData ℓ f K) {A : Matrix (Fin 3) (Fin 3) K}
    (hdet : A.det = 1) (hu : (A.map h.bar)ᵀ * A = 1) :
    ∃ g : unitarySU ℓ f K 3, ((g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = A := by
  let g : GL (Fin 3) K := Matrix.SpecialLinearGroup.toGL ⟨A, hdet⟩
  have hg : g ∈ unitarySU ℓ f K 3 := (mem_unitarySU_iff h).2 ⟨hdet, hu⟩
  exact ⟨⟨g, hg⟩, rfl⟩

theorem goodIn_of_gen (h : UnitaryFieldData ℓ f K) (hq : ℓ ^ f = 8) (ι : Q8 →+* K)
    {σ : K ≃+* K} (hσω : σ (ι w0) = ι w0) (Q : Subgroup (unitarySU ℓ f K 3))
    (hR : ∀ g : unitarySU ℓ f K 3, (∀ i j, σ (((g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) i j) =
      ((g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) i j) → g ∈ Q)
    (Ye : M3 Q8)
    (hC : ∀ g : unitarySU ℓ f K 3, ((g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) * toMat ι Ye =
      toMat ι Ye * ((g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) → g ∈ Q)
    {G : M3 Q8} (hG : sgOk G = true) (hcase : entriesL4 G = true ∨ commutes G Ye = true) :
    GoodQ Q (toMat ι G) := by
  obtain ⟨hdet, hu⟩ := sgOk_spec hG
  have hdetK : (toMat ι G).det = 1 := by rw [toMat_det, hdet, map_one]
  have huK : ((toMat ι G).map h.bar)ᵀ * toMat ι G = 1 := by
    have h1 := toMat_transpose_map h ι G
    rw [hq] at h1
    rw [← h1, ← toMat_mul, hu, toMat_one]
  obtain ⟨x, hx⟩ := exists_su_of_matrix h hdetK huK
  refine ⟨x, ?_, hx⟩
  rcases hcase with hE | hCm
  · apply hR x
    intro i j
    rw [hx]
    exact congrFun (congrFun (map_toMat_fixed ι hσω hE) i) j
  · apply hC x
    rw [hx]
    have := congrArg (toMat ι) (of_decide_eq_true hCm)
    rwa [toMat_mul, toMat_mul] at this

theorem eq_top_of_entry (h : UnitaryFieldData ℓ f K) (hq : ℓ ^ f = 8) (ι : Q8 →+* K)
    (hι : Function.Surjective ι) {σ : K ≃+* K} (hσω : σ (ι w0) = ι w0)
    {letters : List (M3 Q8)} {words2 : List (List ℕ)}
    (hcover : coverBool 8 (words2.map (evalW letters)) = true) {e : U38Entry}
    (he : u38EntryOk letters e = true) (Q : Subgroup (unitarySU ℓ f K 3))
    (hR : ∀ g : unitarySU ℓ f K 3, (∀ i j, σ (((g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) i j) =
      ((g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) i j) → g ∈ Q)
    (hC : ∀ g : unitarySU ℓ f K 3, ((g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) * toMat ι e.Y =
      toMat ι e.Y * ((g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) → g ∈ Q) : Q = ⊤ := by
  obtain ⟨hgens, hwords⟩ := entryOk_spec he
  have hG : ∀ G ∈ e.gens, GoodQ Q (toMat ι G) := fun G hG' =>
    goodIn_of_gen h hq ι hσω Q hR e.Y hC (hgens G hG').1 (hgens G hG').2
  have hl : ∀ x ∈ letters, GoodQ Q (toMat ι x) := by
    intro x hx
    rw [← hwords] at hx
    obtain ⟨w, -, rfl⟩ := List.mem_map.1 hx
    exact goodQ_evalW ι hG w
  have hB : heisB12 ℓ f K ≤ Q := heisB12_le_of_goodQ h ι hι hq hl (of_decide_eq_true hcover)
  obtain ⟨s, hs⟩ := exists_shift_su h
  have hsc : s ∈ Q := by
    apply hR s
    intro i j
    rw [hs]
    fin_cases i <;> fin_cases j <;> simp [hS]
  exact eq_top_of_shift_of_heisB12_le h (by rw [hq]; norm_num) hs hsc hB

open CFSG.RankThree.PartTwo.KFacts
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher (glAut coe_glAut)

theorem comm_conj {A B G H : Matrix (Fin 3) (Fin 3) K} (hHG : H * G = 1)
    (hAB : A * B = B * A) : (G * A * H) * (G * B * H) = (G * B * H) * (G * A * H) := by
  have e1 : G * A * H * (G * B * H) = G * (A * B) * H := by
    calc G * A * H * (G * B * H) = G * A * (H * G) * B * H := by simp only [Matrix.mul_assoc]
      _ = G * (A * B) * H := by rw [hHG, Matrix.mul_one]; simp only [Matrix.mul_assoc]
  have e2 : G * B * H * (G * A * H) = G * (B * A) * H := by
    calc G * B * H * (G * A * H) = G * B * (H * G) * A * H := by simp only [Matrix.mul_assoc]
      _ = G * (B * A) * H := by rw [hHG, Matrix.mul_one]; simp only [Matrix.mul_assoc]
  rw [e1, e2, hAB]

theorem toMat_gstar (h : UnitaryFieldData ℓ f K) (hq : ℓ ^ f = 8) (ι : Q8 →+* K) (g : M3 Q8) :
    toMat ι (gstar g) = ((toMat ι g).map h.bar)ᵀ := by
  have h1 := toMat_transpose_map h ι g
  rw [hq] at h1
  exact h1

theorem glAut_eq_iff (σ : K ≃+* K) (y : GL (Fin 3) K) :
    glAut σ y = y ↔ ∀ i j, σ (((y : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) i j) =
      ((y : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) i j := by
  constructor
  · intro h i j
    have := congrArg (fun z : GL (Fin 3) K => ((z : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) i j) h
    simpa [coe_glAut] using this
  · intro h
    apply Units.ext
    rw [coe_glAut]
    ext i j
    exact h i j

theorem eq_top_of_class (h : UnitaryFieldData ℓ f K) (hq : ℓ ^ f = 8) (ι : Q8 →+* K)
    (hι : Function.Surjective ι) {σ : K ≃+* K} (hσω : σ (ι w0) = ι w0)
    {letters : List (M3 Q8)} {words2 : List (List ℕ)} {table : List U38Entry}
    (hcheck : u38Check letters words2 table = true) {Ym : M3 Q8} (hYe : entriesL4 Ym = true)
    (hYu : unitaryOk Ym = true) (hYns : isScalar Ym = false)
    (hY3 : isScalar (Ym * Ym * Ym) = true) (Q : Subgroup (unitarySU ℓ f K 3))
    (hR : ∀ g : unitarySU ℓ f K 3, (∀ i j, σ (((g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) i j) =
      ((g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) i j) → g ∈ Q)
    (hC : ∀ g : unitarySU ℓ f K 3, ((g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) * toMat ι Ym =
      toMat ι Ym * ((g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) → g ∈ Q) : Q = ⊤ := by
  obtain ⟨e, he, g, hg, ⟨hgE, hgU⟩, l, hl, hYm⟩ := class_sound hcheck hYe hYu hYns hY3
  obtain ⟨-, hcov, htab, -⟩ := u38Check_parts hcheck
  have hentry := (List.all_eq_true.1 htab) e he
  have hGu : ((toMat ι g).map h.bar)ᵀ * toMat ι g = 1 := by
    have h1 := toMat_transpose_map h ι g
    rw [hq] at h1
    rw [← h1, ← toMat_mul, of_decide_eq_true hgU, toMat_one]
  let gU : GL (Fin 3) K := ⟨toMat ι g, ((toMat ι g).map h.bar)ᵀ, mul_eq_one_comm.2 hGu, hGu⟩
  have hgUm : gU ∈ unitaryIsom3 h := hGu
  let c : MulAut (unitarySU ℓ f K 3) := suConj h ⟨gU, hgUm⟩
  have hgUfix : glAut σ gU = gU := by
    rw [glAut_eq_iff]
    intro i j
    exact congrFun (congrFun (map_toMat_fixed ι hσω hgE) i) j
  have hcx : ∀ x : unitarySU ℓ f K 3, (((c x : unitarySU ℓ f K 3) : GL (Fin 3) K) :
      Matrix (Fin 3) (Fin 3) K) = toMat ι g * ((x : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *
        ((toMat ι g).map h.bar)ᵀ := fun x => by
    rw [coe_suConj]
    rfl
  let Q'' : Subgroup (unitarySU ℓ f K 3) := Q.comap c.toMonoidHom
  have hR'' : ∀ x : unitarySU ℓ f K 3, (∀ i j, σ (((x : GL (Fin 3) K) :
      Matrix (Fin 3) (Fin 3) K) i j) = ((x : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) i j) →
        x ∈ Q'' := by
    intro x hx
    show c x ∈ Q
    apply hR
    rw [← glAut_eq_iff]
    have hxfix : glAut σ (x : GL (Fin 3) K) = (x : GL (Fin 3) K) := (glAut_eq_iff σ _).2 hx
    have h1 : ((c x : unitarySU ℓ f K 3) : GL (Fin 3) K) = gU * (x : GL (Fin 3) K) * gU⁻¹ := by
      rw [coe_suConj]
      rfl
    rw [h1, map_mul, map_mul, map_inv, hgUfix, hxfix]
  have hC'' : ∀ x : unitarySU ℓ f K 3, ((x : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *
      toMat ι e.Y = toMat ι e.Y * ((x : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) → x ∈ Q'' := by
    intro x hx
    show c x ∈ Q
    apply hC
    have hY : toMat ι Ym = ι l • (toMat ι g * toMat ι e.Y * ((toMat ι g).map h.bar)ᵀ) := by
      rw [hYm, toMat_smul, toMat_mul, toMat_mul, toMat_gstar h hq ι]
    rw [hcx, hY, Matrix.mul_smul, Matrix.smul_mul, comm_conj hGu hx]
  have hQ'' : Q'' = ⊤ := eq_top_of_entry h hq ι hι hσω hcov hentry Q'' hR'' hC''
  rw [eq_top_iff]
  intro z _
  have hz : c⁻¹ z ∈ Q'' := hQ'' ▸ Subgroup.mem_top _
  have hz' : c (c⁻¹ z) ∈ Q := hz
  rwa [MulAut.apply_inv_self] at hz'

end KLevel

end CFSG.RankThree.PartTwo.Sec19.U38F
