module

public import CFSG.RankThree.PartTwo.Sec4.RonanK432RowSp82Mat
public import CFSG.Quasithin.H13.L32NMat8
public import Certificates.Data.RudvalisFF81Sp8Codes
public import CFSG.Open.StatedAPI

public section

namespace CFSG.RankThree.PartTwo.Sec21.FF81.Sp8

open CFSG.Quasithin.H13.Mat8Cert CFSG.Quasithin.G2U
open CFSG.RankThree.PartTwo.Sec4.RonanK432 (H8 sm8)
open CFSG.Assembly.LowTwoRank (StatedSp)
open Matrix
open scoped Matrix

abbrev ι8 : Type := Fin 4 ⊕ Fin 4

abbrev jM : Matrix ι8 ι8 (ZMod 2) := fromBlocks 0 1 (-1) 0

abbrev φ8 : ι8 ≃ Fin 8 := finSumFinEquiv

@[expose] def decS (A : List ℕ) : Matrix ι8 ι8 (ZMod 2) := sm8 (dec8 A)

@[expose] def vecS (n : ℕ) : ι8 → ZMod 2 := fun i => vec8 n (φ8 i)

theorem dec8_mulS (A B : List ℕ) : dec8 (mulS A B) = dec8 A * dec8 B := by
  ext i j
  have hget : (mulS A B).getD j 0 = mv8 A (B.getD j 0) := by
    fin_cases j <;> rfl
  have h := congrFun (dec8_mulVec A (B.getD j 0)) i
  simp only [dec8, Matrix.of_apply, Matrix.mul_apply, hget]
  rw [← h]
  simp only [Matrix.mulVec, dotProduct, dec8, Matrix.of_apply]

theorem decS_mulS (A B : List ℕ) : decS (mulS A B) = decS A * decS B := by
  rw [decS, decS, decS, dec8_mulS, sm8, sm8, sm8, Matrix.submatrix_mul_equiv]

theorem decS_one8 : decS one8 = 1 := by
  rw [decS, dec8_one8, sm8, Matrix.submatrix_one_equiv]

theorem decS_mulVec (A : List ℕ) (n : ℕ) : decS A *ᵥ vecS n = vecS (mv8 A n) := by
  have h : vecS n = vec8 n ∘ φ8 := rfl
  rw [h, decS, sm8, Matrix.submatrix_mulVec_equiv, Function.comp_assoc, Equiv.self_comp_symm,
    Function.comp_id, dec8_mulVec]
  rfl

theorem vecS_inj {m n : ℕ} (hm : m < 256) (hn : n < 256) (h : vecS m = vecS n) : m = n := by
  refine vec8_inj hm hn ?_
  funext i
  have := congrFun h (φ8.symm i)
  simpa [vecS] using this

@[expose] def codeV (v : ι8 → ZMod 2) : ℕ := code8 (v ∘ φ8.symm)

theorem codeV_lt (v : ι8 → ZMod 2) : codeV v < 256 := code8_lt _

theorem vecS_codeV (v : ι8 → ZMod 2) : vecS (codeV v) = v := by
  funext i
  simp [vecS, codeV, vec8_code8]

theorem decS_injOn {A A' : List ℕ} (hA : Valid8 A) (hA' : Valid8 A') (h : decS A = decS A') :
    A = A' := by
  refine dec8_injOn hA hA' ?_
  have h' := congrArg (fun M => M.submatrix φ8.symm φ8.symm) h
  simpa [decS, sm8, Matrix.submatrix_submatrix] using h'

theorem valid8_mulS {A : List ℕ} (hA : Valid8 A) (B : List ℕ) : Valid8 (mulS A B) := by
  refine ⟨rfl, fun c hc => ?_⟩
  simp only [mulS, List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact mv8_lt hA _

@[expose] def matS : H8 →* Matrix ι8 ι8 (ZMod 2) :=
  (Units.coeHom (Matrix ι8 ι8 (ZMod 2))).comp (StatedSp 4 (ZMod 2)).subtype

theorem matS_apply (g : H8) : matS g = ((g : GL ι8 (ZMod 2)) : Matrix ι8 ι8 (ZMod 2)) := rfl

theorem matS_injective : Function.Injective matS := by
  intro g h e
  exact Subtype.ext (Units.ext e)

theorem symp_matS (g : H8) : (matS g)ᵀ * jM * matS g = jM :=
  CFSG.Open.StatedAPI.mem_statedSp_iff.mp g.2

@[expose] def codeS (g : H8) : List ℕ :=
  colsOf ((matS g).submatrix φ8.symm φ8.symm)

theorem decS_codeS (g : H8) : decS (codeS g) = matS g := by
  rw [decS, codeS, dec8_colsOf, sm8, Matrix.submatrix_submatrix]
  simp

theorem valid8_codeS (g : H8) : Valid8 (codeS g) := valid8_colsOf _

theorem codeS_injective : Function.Injective codeS := fun g h e =>
  matS_injective (by rw [← decS_codeS, ← decS_codeS h, e])

theorem codeS_eq_of_decS {g : H8} {c : List ℕ} (hc : Valid8 c) (h : decS c = matS g) :
    codeS g = c :=
  decS_injOn (valid8_codeS g) hc (by rw [decS_codeS, h])

theorem codeS_mul (g h : H8) : codeS (g * h) = mulS (codeS g) (codeS h) :=
  codeS_eq_of_decS (valid8_mulS (valid8_codeS g) _)
    (by rw [decS_mulS, decS_codeS, decS_codeS, map_mul])

theorem codeS_one : codeS 1 = one8 :=
  codeS_eq_of_decS valid8_one8 (by rw [decS_one8, map_one])

theorem eq_of_codeS {g h : H8} (e : codeS g = codeS h) : g = h := codeS_injective e

theorem commute_iff_codeS (g h : H8) : g * h = h * g ↔ mulS (codeS g) (codeS h) =
    mulS (codeS h) (codeS g) := by
  rw [← codeS_mul, ← codeS_mul]
  exact ⟨fun e => by rw [e], fun e => codeS_injective e⟩

theorem fin_four_vals : ((0 : Fin 4) : ℕ) = 0 ∧ ((1 : Fin 4) : ℕ) = 1 ∧ ((2 : Fin 4) : ℕ) = 2 ∧
    ((3 : Fin 4) : ℕ) = 3 := ⟨rfl, rfl, rfl, rfl⟩

theorem neg_zmod2 (x : ZMod 2) : -x = x := by fin_cases x <;> rfl

theorem jM_mulVec (x : ι8 → ZMod 2) (i : ι8) : (jM *ᵥ x) i = x i.swap := by
  rcases i with a | a <;>
    simp [jM, Matrix.mulVec, dotProduct, Fintype.sum_sum_type, Matrix.one_apply, neg_zmod2]

theorem form_vecS (u w : ℕ) : vecS u ⬝ᵥ (jM *ᵥ vecS w) = b2z (b4N u w) := by
  rw [b4N_spec]
  have f : ∀ i : Fin 4, φ8 (Sum.inl i) = Fin.castAdd 4 i ∧ φ8 (Sum.inr i) = Fin.natAdd 4 i :=
    fun i => ⟨rfl, rfl⟩
  simp only [dotProduct, jM_mulVec, Fintype.sum_sum_type, Sum.swap_inl, Sum.swap_inr,
    Fin.sum_univ_four, vecS, f, b4V, q4V, Pi.add_apply]
  have e0 : (Fin.castAdd 4 (0 : Fin 4) : Fin 8) = 0 := rfl
  have e1 : (Fin.castAdd 4 (1 : Fin 4) : Fin 8) = 1 := rfl
  have e2 : (Fin.castAdd 4 (2 : Fin 4) : Fin 8) = 2 := rfl
  have e3 : (Fin.castAdd 4 (3 : Fin 4) : Fin 8) = 3 := rfl
  have e4 : (Fin.natAdd 4 (0 : Fin 4) : Fin 8) = 4 := rfl
  have e5 : (Fin.natAdd 4 (1 : Fin 4) : Fin 8) = 5 := rfl
  have e6 : (Fin.natAdd 4 (2 : Fin 4) : Fin 8) = 6 := rfl
  have e7 : (Fin.natAdd 4 (3 : Fin 4) : Fin 8) = 7 := rfl
  rw [e0, e1, e2, e3, e4, e5, e6, e7]
  have key : ∀ a b c d : ZMod 2, (a + c) * (b + d) + a * b + c * d = a * d + c * b := by decide
  linear_combination -(key (vec8 u 0) (vec8 u 4) (vec8 w 0) (vec8 w 4)) -
    key (vec8 u 1) (vec8 u 5) (vec8 w 1) (vec8 w 5) -
    key (vec8 u 2) (vec8 u 6) (vec8 w 2) (vec8 w 6) -
    key (vec8 u 3) (vec8 u 7) (vec8 w 3) (vec8 w 7)

theorem b2z_jB (x y : ι8) : jM x y = b2z (((φ8 x : ℕ) + 4 == φ8 y) ||
    ((φ8 y : ℕ) + 4 == φ8 x)) := by
  rcases x with a | a <;> rcases y with b | b <;> fin_cases a <;> fin_cases b <;> decide

theorem transpose_mul_decS (c : List ℕ) (x y : ι8) : ((decS c)ᵀ * jM * decS c) x y =
    b2z (b4N (c.getD (φ8 x) 0) (c.getD (φ8 y) 0)) := by
  rw [← form_vecS, Matrix.mul_assoc, Matrix.mul_apply]
  simp only [Matrix.transpose_apply, dotProduct, Matrix.mulVec]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Matrix.mul_apply]
  rfl

theorem spS_spec {c : List ℕ} (h : spS c = true) : (decS c)ᵀ * jM * decS c = jM := by
  simp only [spS, Bool.and_eq_true, List.all_eq_true, List.mem_range, beq_iff_eq] at h
  ext x y
  rw [transpose_mul_decS, b2z_jB, h.2 _ (φ8 x).2 _ (φ8 y).2]

theorem valid8_of_validS {c : List ℕ} (h : validS c = true) : Valid8 c := by
  simp only [validS, Bool.and_eq_true, beq_iff_eq, List.all_eq_true, decide_eq_true_eq] at h
  exact ⟨h.1, h.2⟩

theorem valid8_of_spS {c : List ℕ} (h : spS c = true) : Valid8 c := by
  simp only [spS, Bool.and_eq_true] at h
  exact valid8_of_validS h.1

theorem jM_mul_jM : jM * jM = 1 := by decide

@[expose] def mkS (c : List ℕ) (h : spS c = true) : H8 :=
  ⟨⟨decS c, jM * (decS c)ᵀ * jM,
      mul_eq_one_comm.mp (by
        rw [Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc _ jM, spS_spec h, jM_mul_jM]),
      by rw [Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc _ jM, spS_spec h, jM_mul_jM]⟩,
    CFSG.Open.StatedAPI.mem_statedSp_iff.mpr (spS_spec h)⟩

theorem matS_mkS (c : List ℕ) (h : spS c = true) : matS (mkS c h) = decS c := rfl

theorem codeS_mkS (c : List ℕ) (h : spS c = true) : codeS (mkS c h) = c :=
  codeS_eq_of_decS (valid8_of_spS h) rfl

theorem spS_codeS (g : H8) : spS (codeS g) = true := by
  have hv := valid8_codeS g
  simp only [spS, validS, Bool.and_eq_true, beq_iff_eq, List.all_eq_true, decide_eq_true_eq,
    List.mem_range]
  refine ⟨⟨hv.1, hv.2⟩, fun i hi j hj => ?_⟩
  have h := congrFun (congrFun (symp_matS g) (φ8.symm ⟨i, hi⟩)) (φ8.symm ⟨j, hj⟩)
  rw [← decS_codeS, transpose_mul_decS, b2z_jB] at h
  simpa using b2z_inj h

@[expose] def subS (gens : List (List ℕ)) : Subgroup H8 :=
  Subgroup.closure {g | codeS g ∈ gens}

theorem image_gens {gens : List (List ℕ)} (hg : gens.all spS = true) :
    matS '' {g | codeS g ∈ gens} = {y | ∃ c ∈ gens, decS c = y} := by
  ext y
  constructor
  · rintro ⟨g, hg', rfl⟩
    exact ⟨codeS g, hg', decS_codeS g⟩
  · rintro ⟨c, hc, rfl⟩
    have hs : spS c = true := List.all_eq_true.mp hg c hc
    exact ⟨mkS c hs, by rw [Set.mem_setOf_eq, codeS_mkS]; exact hc, rfl⟩

theorem found_spec {es : Array (List ℕ)} {m : Std.HashMap (List ℕ) ℕ} {y : List ℕ}
    (h : found es m y = true) : ∃ t < es.size, es.getD t [] = y := by
  simp only [found] at h
  split at h
  · rename_i t _
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h
    exact ⟨t, h.1, h.2⟩
  · exact absurd h Bool.false_ne_true

section Tables

variable {gens : List (List ℕ)} {n : ℕ} (h : tabOK gens (tabS gens n) n = true)
include h

theorem tabOK_parts : (tabS gens n).size = n ∧ closedCheck mulS gens (tabS gens n) = true ∧
    distinctCheck (tabS gens n) = true ∧ allCheck validS (tabS gens n) = true ∧
    gens.all spS = true := by
  simp only [tabOK, Bool.and_eq_true, beq_iff_eq] at h
  exact ⟨h.1.1.1.1, h.1.1.1.2, h.1.1.2, h.1.2, h.2⟩

theorem mem_subS_iff (g : H8) :
    g ∈ subS gens ↔ ∃ t < (tabS gens n).size, (tabS gens n).getD t [] = codeS g := by
  obtain ⟨-, hcl, -, hval, hg⟩ := tabOK_parts h
  have himg : matS '' (Subgroup.closure {g | codeS g ∈ gens} : Set H8) =
      {y | ∃ t < (tabS gens n).size, decS ((tabS gens n).getD t []) = y} :=
    image_closure_eq decS one8 mulS gens matS decS_one8 decS_mulS {g | codeS g ∈ gens}
      (image_gens hg) _ hcl
  constructor
  · intro hgS
    have hm : matS g ∈ matS '' (subS gens : Set H8) := ⟨g, hgS, rfl⟩
    rw [subS, himg] at hm
    obtain ⟨t, ht, e⟩ := hm
    exact ⟨t, ht, (codeS_eq_of_decS (valid8_of_validS (allCheck_spec hval ht)) e).symm⟩
  · rintro ⟨t, ht, e⟩
    have hm : matS g ∈ matS '' (Subgroup.closure {g | codeS g ∈ gens} : Set H8) := by
      rw [himg]
      exact ⟨t, ht, by rw [e, decS_codeS]⟩
    obtain ⟨g', hg', e'⟩ := hm
    rw [← matS_injective e']
    exact hg'

theorem card_subS : Nat.card (subS gens) = n := by
  obtain ⟨hsize, hcl, hdist, hval, hg⟩ := tabOK_parts h
  rw [← hsize]
  refine card_closure_eq decS one8 mulS gens matS matS_injective decS_one8 decS_mulS _
    (image_gens hg) _ hcl hdist fun t ht t' ht' e => ?_
  exact decS_injOn (valid8_of_validS (allCheck_spec hval ht))
    (valid8_of_validS (allCheck_spec hval ht')) e

theorem exists_of_lt {t : ℕ} (ht : t < (tabS gens n).size) :
    ∃ g ∈ subS gens, codeS g = (tabS gens n).getD t [] := by
  obtain ⟨-, -, -, hval, hg⟩ := tabOK_parts h
  have hv := allCheck_spec hval ht
  have hs : ∃ g : H8, decS ((tabS gens n).getD t []) = matS g := by
    have himg : matS '' (Subgroup.closure {g | codeS g ∈ gens} : Set H8) =
        {y | ∃ t < (tabS gens n).size, decS ((tabS gens n).getD t []) = y} :=
      image_closure_eq decS one8 mulS gens matS decS_one8 decS_mulS {g | codeS g ∈ gens}
        (image_gens hg) _ (tabOK_parts h).2.1
    have hm : decS ((tabS gens n).getD t []) ∈ matS '' (Subgroup.closure {g | codeS g ∈ gens} :
        Set H8) := by
      rw [himg]
      exact ⟨t, ht, rfl⟩
    obtain ⟨g, -, e⟩ := hm
    exact ⟨g, e.symm⟩
  obtain ⟨g, hgm⟩ := hs
  have hc := codeS_eq_of_decS (valid8_of_validS hv) hgm
  exact ⟨g, (mem_subS_iff h g).mpr ⟨t, ht, hc.symm⟩, hc⟩

theorem exists_of_found {m : Std.HashMap (List ℕ) ℕ} {c : List ℕ}
    (hf : found (tabS gens n) m c = true) : ∃ g ∈ subS gens, codeS g = c := by
  obtain ⟨t, ht, e⟩ := found_spec hf
  rw [← e]
  exact exists_of_lt h ht

theorem mem_subS_of_found {m : Std.HashMap (List ℕ) ℕ} {g : H8}
    (hf : found (tabS gens n) m (codeS g) = true) : g ∈ subS gens := by
  obtain ⟨g', hg', e⟩ := exists_of_found h hf
  rwa [codeS_injective e] at hg'

theorem allCheck_mem {p : List ℕ → Bool} (hp : allCheck p (tabS gens n) = true) {g : H8}
    (hg : g ∈ subS gens) : p (codeS g) = true := by
  obtain ⟨t, ht, e⟩ := (mem_subS_iff h g).mp hg
  rw [← e]
  exact allCheck_spec hp ht

end Tables

theorem subS_le {gens : List (List ℕ)} {K : Subgroup H8} (hK : ∀ g : H8, codeS g ∈ gens → g ∈ K) :
    subS gens ≤ K :=
  (Subgroup.closure_le K).mpr fun g hg => hK g hg

theorem mem_subS_of_codeS {gens : List (List ℕ)} {g : H8} (hg : codeS g ∈ gens) :
    g ∈ subS gens :=
  Subgroup.subset_closure hg

theorem cfoundS_spec {es : Array (List ℕ)} {m : Std.HashMap (List ℕ) ℕ} {a x : List ℕ}
    (h : cfoundS es m a x = true) :
    ∃ t < es.size, mulS (es.getD t []) a = mulS x (es.getD t []) := by
  simp only [cfoundS] at h
  split at h
  · rename_i t _
    simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h
    exact ⟨t, h.1, h.2⟩
  · exact absurd h Bool.false_ne_true

theorem conj_eq_of_mulS {n a x : H8} (h : mulS (codeS n) (codeS a) = mulS (codeS x) (codeS n)) :
    n * a * n⁻¹ = x := by
  rw [← codeS_mul, ← codeS_mul] at h
  rw [codeS_injective h]
  group

@[expose] def zeroS : List ℕ := [0, 0, 0, 0, 0, 0, 0, 0]

theorem mv8_zeroS (v : ℕ) : mv8 zeroS v = 0 := by
  simp [mv8, zeroS]

theorem mulS_zeroS_left (B : List ℕ) : mulS zeroS B = zeroS := by
  simp only [mulS, mv8_zeroS]
  rfl

theorem mulS_zeroS_right (A : List ℕ) : mulS A zeroS = zeroS := by
  simp only [mulS, zeroS, List.getD_cons_zero, List.getD_cons_succ]
  simp [mv8]

theorem mulS_nil (A : List ℕ) : mulS A [] = zeroS := by
  simp only [mulS, List.getD_nil]
  simp [mv8, zeroS]

theorem build_mem {P : List ℕ → Prop} (one : List ℕ) (mul : List ℕ → List ℕ → List ℕ)
    (gens : List (List ℕ)) (h1 : P one) (hstep : ∀ x, P x → ∀ s : ℕ, P (mul x (gens.getD s one)))
    (par : List (ℕ × ℕ)) : ∀ x ∈ build one mul gens par, P x := by
  suffices key : ∀ (par : List (ℕ × ℕ)) (acc : Array (List ℕ)), (∀ x ∈ acc, P x) →
      ∀ x ∈ par.foldl (fun acc ps => acc.push (mul (acc.getD ps.1 one) (gens.getD ps.2 one))) acc,
        P x by
    refine key par #[one] ?_
    intro x hx
    rw [Array.mem_singleton.mp hx]
    exact h1
  intro par
  induction par with
  | nil => exact fun acc h => h
  | cons ps par ih =>
    intro acc h
    rw [List.foldl_cons]
    refine ih _ fun x hx => ?_
    rcases Array.mem_push.mp hx with hx | rfl
    · exact h x hx
    · refine hstep _ ?_ ps.2
      rw [Array.getD]
      split_ifs with hi
      · exact h _ (Array.getElem_mem hi)
      · exact h1

theorem take_drop_eight {g g' : List ℕ} (hg : g.length = 8) :
    (g ++ g').take 8 = g ∧ (g ++ g').drop 8 = g' :=
  ⟨List.take_left' hg, List.drop_left' hg⟩

theorem orbS_spec {r : List ℕ} {r₀ : H8} (hr : decS r = matS r₀) (hr8 : r.length = 8)
    {gp : List (List ℕ)} (hgp : ∀ gg ∈ gp, ∃ a : H8, decS (gg.take 8) = matS a ∧
      decS (gg.drop 8) = matS a⁻¹) (n : ℕ) :
    ∀ x ∈ orbS r gp n, x = zeroS ∨ ∃ v : H8, decS x = matS (v * r₀ * v⁻¹) := by
  refine build_mem r conjStepS gp (Or.inr ⟨1, by rw [hr]; simp⟩) ?_ _
  intro x hx s
  rcases hx with rfl | ⟨v, hv⟩
  · left
    simp only [conjStepS, mulS_zeroS_right, mulS_zeroS_left]
  · by_cases hs : s < gp.length
    · right
      rw [List.getD_eq_getElem _ _ hs]
      obtain ⟨a, ha, ha'⟩ := hgp _ (List.getElem_mem hs)
      refine ⟨a * v, ?_⟩
      have e : a * v * r₀ * (a * v)⁻¹ = a * (v * r₀ * v⁻¹) * a⁻¹ := by group
      rw [e, map_mul, map_mul]
      simp only [conjStepS, decS_mulS, ha, ha', hv]
    · left
      rw [List.getD_eq_default _ _ (by omega)]
      simp only [conjStepS, List.drop_eq_nil_of_le (le_of_eq hr8), mulS_nil]

@[expose] noncomputable def fixCount (g : H8) : ℕ :=
  Fintype.card {v : ι8 → ZMod 2 // matS g *ᵥ v = v}

theorem matS_mulVec_mulVec (a b : H8) (v : ι8 → ZMod 2) :
    matS a *ᵥ (matS b *ᵥ v) = matS (a * b) *ᵥ v := by
  rw [Matrix.mulVec_mulVec, map_mul]

theorem fixCount_conj (g h : H8) : fixCount (h * g * h⁻¹) = fixCount g := by
  refine Fintype.card_congr
    { toFun := fun v => ⟨matS h⁻¹ *ᵥ v.1, ?_⟩
      invFun := fun v => ⟨matS h *ᵥ v.1, ?_⟩
      left_inv := fun v => Subtype.ext ?_
      right_inv := fun v => Subtype.ext ?_ }
  · rw [matS_mulVec_mulVec, show g * h⁻¹ = h⁻¹ * (h * g * h⁻¹) by group, ← matS_mulVec_mulVec,
      v.2]
  · rw [matS_mulVec_mulVec, show h * g * h⁻¹ * h = h * g by group, ← matS_mulVec_mulVec, v.2]
  · simp only [matS_mulVec_mulVec, mul_inv_cancel, map_one, Matrix.one_mulVec]
  · simp only [matS_mulVec_mulVec, inv_mul_cancel, map_one, Matrix.one_mulVec]

theorem fixCount_eq_fixS (g : H8) : fixCount g = fixS (codeS g) := by
  have hcard : Fintype.card {v : ι8 → ZMod 2 // matS g *ᵥ v = v} =
      Fintype.card {n : Fin 256 // mv8 (codeS g) n = n} := by
    refine Fintype.card_congr
      { toFun := fun v => ⟨⟨codeV v.1, codeV_lt _⟩, ?_⟩
        invFun := fun n => ⟨vecS n.1, ?_⟩
        left_inv := fun v => Subtype.ext ?_
        right_inv := fun n => Subtype.ext (Fin.ext ?_) }
    · refine vecS_inj (mv8_lt (valid8_codeS g) _) (codeV_lt _) ?_
      rw [← decS_mulVec, decS_codeS, vecS_codeV, v.2]
    · rw [← decS_codeS, decS_mulVec, n.2]
    · exact vecS_codeV _
    · exact vecS_inj (codeV_lt _) n.1.2 (vecS_codeV _)
  have e1 : Fintype.card {n : Fin 256 // mv8 (codeS g) n = n} =
      ((Finset.range 256).filter fun v => mv8 (codeS g) v = v).card := by
    rw [← Fintype.card_coe]
    exact Fintype.card_congr
      { toFun := fun n => ⟨n.1.1, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr n.1.2, n.2⟩⟩
        invFun := fun v => ⟨⟨v.1, Finset.mem_range.mp (Finset.mem_filter.mp v.2).1⟩,
          (Finset.mem_filter.mp v.2).2⟩
        left_inv := fun n => rfl
        right_inv := fun v => rfl }
  rw [fixCount, hcard, e1, fixS]
  simp only [Finset.card, Finset.filter_val, Finset.range_val, Multiset.range, Multiset.filter_coe,
    Multiset.coe_card]
  congr 1

@[expose] def aType (g : H8) : Prop := ∀ v : ι8 → ZMod 2, v ⬝ᵥ (jM *ᵥ (matS g *ᵥ v)) = 0

theorem form_matS (h : H8) (u w : ι8 → ZMod 2) :
    (matS h *ᵥ u) ⬝ᵥ (jM *ᵥ (matS h *ᵥ w)) = u ⬝ᵥ (jM *ᵥ w) := by
  rw [Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, ← Matrix.vecMul_transpose,
    Matrix.vecMul_vecMul, ← Matrix.mul_assoc, symp_matS, ← Matrix.dotProduct_mulVec]

theorem form_conj (g h : H8) (v : ι8 → ZMod 2) : v ⬝ᵥ (jM *ᵥ (matS (h * g * h⁻¹) *ᵥ v)) =
    (matS h⁻¹ *ᵥ v) ⬝ᵥ (jM *ᵥ (matS g *ᵥ (matS h⁻¹ *ᵥ v))) := by
  have hv : v = matS h *ᵥ (matS h⁻¹ *ᵥ v) := by
    rw [matS_mulVec_mulVec, mul_inv_cancel, map_one, Matrix.one_mulVec]
  have hM : matS (h * g * h⁻¹) *ᵥ v = matS h *ᵥ (matS g *ᵥ (matS h⁻¹ *ᵥ v)) := by
    rw [matS_mulVec_mulVec, matS_mulVec_mulVec]
  rw [hM, ← form_matS h (matS h⁻¹ *ᵥ v) (matS g *ᵥ (matS h⁻¹ *ᵥ v)), ← hv]

theorem aType_conj (g h : H8) : aType (h * g * h⁻¹) ↔ aType g := by
  constructor
  · intro hg w
    have e := form_conj g h (matS h *ᵥ w)
    rw [hg (matS h *ᵥ w), matS_mulVec_mulVec, inv_mul_cancel, map_one, Matrix.one_mulVec] at e
    exact e.symm
  · intro hg v
    rw [form_conj]
    exact hg _

theorem aType_iff (g : H8) : aType g ↔ aTypeS (codeS g) = true := by
  simp only [aTypeS, List.all_eq_true, List.mem_range, Bool.not_eq_true']
  constructor
  · intro hg n hn
    have h := hg (vecS n)
    rw [← decS_codeS, decS_mulVec, form_vecS] at h
    cases hb : b4N n (mv8 (codeS g) n)
    · rfl
    · rw [hb] at h
      exact absurd h (by decide)
  · intro hg v
    rw [← vecS_codeV v, ← decS_codeS, decS_mulVec, form_vecS, hg _ (codeV_lt v)]
    rfl

end CFSG.RankThree.PartTwo.Sec21.FF81.Sp8
