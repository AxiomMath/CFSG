module

public import CFSG.Quasithin.Vol2.GoldschmidtF431U42LocGeom

public section

namespace CFSG.Quasithin.H13.F431.U42

open CFSG.Quasithin CFSG.Open U42F431
open scoped Pointwise

@[expose] def tPrime : Y := sY 15 * sY 16

@[expose] def wConj : List ℕ := [1, 0, 1, 1, 0, 2, 0, 1]

@[expose] def chkTp : Bool :=
  (comp (comp (tpTab.getD 0 []) (tpTab.getD 20 [])) (tpTab.getD 24 []) ==
    comp (tpTab.getD 15 []) (tpTab.getD 16 [])) &&
  (comp (tpTab.getD 15 []) (comp (tpTab.getD 15 []) (tpTab.getD 16 [])) == tpTab.getD 16 []) &&
  (comp (tpTab.getD 16 []) (comp (tpTab.getD 15 []) (tpTab.getD 16 [])) == tpTab.getD 15 []) &&
  (comp (tpTab.getD 0 []) (tpTab.getD 20 []) ==
    comp (tpTab.getD 24 []) (comp (tpTab.getD 15 []) (tpTab.getD 16 [])))

@[expose] def chkNotTr : Bool := (List.range 45).all fun q =>
  tpTab.getD q [] != comp (tpTab.getD 15 []) (tpTab.getD 16 []) &&
  tpTab.getD q [] != comp (tpTab.getD 0 []) (comp (tpTab.getD 15 []) (tpTab.getD 16 [])) &&
  tpTab.getD q [] != comp (tpTab.getD 20 []) (comp (tpTab.getD 15 []) (tpTab.getD 16 [])) &&
  tpTab.getD q [] != comp (tpTab.getD 24 []) (comp (tpTab.getD 15 []) (tpTab.getD 16 []))

@[expose] def chkPairs : Bool := L0.all fun a => L0.all fun b => L0.all fun c => L0.all fun d =>
  a == b || c == d || comp (tpTab.getD a []) (tpTab.getD b []) !=
    comp (tpTab.getD c []) (tpTab.getD d []) || (a == c && b == d) || (a == d && b == c)

@[expose] def chkConj : Bool :=
  sameSet (imgSet (evalW wConj) L0) L0 &&
  (comp (evalW wConj) (comp (tpTab.getD 15 []) (tpTab.getD 16 [])) == comp t0L (evalW wConj))

theorem chkTp_true : chkTp = true := by decide +kernel

theorem chkNotTr_true : chkNotTr = true := by decide +kernel

theorem chkPairs_true : chkPairs = true := by decide +kernel

theorem chkConj_true : chkConj = true := by decide +kernel

theorem repL_tPrime :
    RepL (comp (tpTab.getD 15 []) (tpTab.getD 16 [])) ((tPrime : Y) : P45) :=
  repL_mul (repL_sY 15) (repL_sY 16)

theorem eq_of_lists {a b : Y} {la lb : PL} (ha : RepL la (a : P45))
    (hb : RepL lb (b : P45)) (h : la = lb) : a = b :=
  Subtype.ext (eq_of_repL ha (h ▸ hb))

theorem sY15_mul_tPrime : sY 15 * tPrime = sY 16 := by
  have h := chkTp_true
  simp only [chkTp, Bool.and_eq_true, beq_iff_eq] at h
  exact eq_of_lists (repL_mul (repL_sY 15) repL_tPrime) (repL_sY 16) h.1.1.2

theorem sY16_mul_tPrime : sY 16 * tPrime = sY 15 := by
  have h := chkTp_true
  simp only [chkTp, Bool.and_eq_true, beq_iff_eq] at h
  exact eq_of_lists (repL_mul (repL_sY 16) repL_tPrime) (repL_sY 15) h.1.2

theorem sY0_mul_sY20 : sY 0 * sY 20 = sY 24 * tPrime := by
  have h := chkTp_true
  simp only [chkTp, Bool.and_eq_true, beq_iff_eq] at h
  exact eq_of_lists (repL_mul (repL_sY 0) (repL_sY 20)) (repL_mul (repL_sY 24) repL_tPrime) h.2

theorem mem_L0S_fifteen : (15 : Fin 45) ∈ L0S := (mem_L0S_iff 15).2 (by simp)

theorem mem_L0S_sixteen : (16 : Fin 45) ∈ L0S := (mem_L0S_iff 16).2 (by simp)

theorem tPrime_mem_Vsub : tPrime ∈ Vsub :=
  Vsub.mul_mem (sY_mem_Vsub mem_L0S_fifteen) (sY_mem_Vsub mem_L0S_sixteen)

theorem tPrime_sq : tPrime * tPrime = 1 :=
  Vsub_sq tPrime_mem_Vsub

theorem tPrime_ne_one : tPrime ≠ 1 := by
  intro h
  have h1 : sY 15 = sY 16 := by
    have := sY15_mul_tPrime
    rw [h, mul_one] at this
    exact this
  exact absurd (sY_inj h1) (by decide)

theorem not_isConj_of_list {a : Y} {l : PL} (h : RepL l (a : P45))
    (hne : ∀ q < 45, tpTab.getD q [] ≠ l) : ¬ IsConj xY a := by
  intro hc
  obtain ⟨q, rfl⟩ := exists_sY_of_isConj hc
  exact hne q.val q.2 (repL_unique (repL_sY q) h)

theorem not_isConj_tPrime : ¬ IsConj xY tPrime := by
  have h := chkNotTr_true
  simp only [chkNotTr, List.all_eq_true, List.mem_range, Bool.and_eq_true, bne_iff_ne,
    ne_eq] at h
  exact not_isConj_of_list repL_tPrime fun q hq => (h q hq).1.1.1

theorem not_isConj_sY_mul {p : Fin 45}
    (hp : p = 0 ∨ p = 20 ∨ p = 24) : ¬ IsConj xY (sY p * tPrime) := by
  have h := chkNotTr_true
  simp only [chkNotTr, List.all_eq_true, List.mem_range, Bool.and_eq_true, bne_iff_ne,
    ne_eq] at h
  rcases hp with rfl | rfl | rfl
  · exact not_isConj_of_list (repL_mul (repL_sY 0) repL_tPrime) fun q hq => (h q hq).1.1.2
  · exact not_isConj_of_list (repL_mul (repL_sY 20) repL_tPrime) fun q hq => (h q hq).1.2
  · exact not_isConj_of_list (repL_mul (repL_sY 24) repL_tPrime) fun q hq => (h q hq).2

theorem pair_eq {a b c d : Fin 45} (ha : a ∈ L0S) (hb : b ∈ L0S)
    (hc : c ∈ L0S) (hd : d ∈ L0S) (hab : a ≠ b) (hcd : c ≠ d) (h : sY a * sY b = sY c * sY d) :
    (a = c ∧ b = d) ∨ (a = d ∧ b = c) := by
  have hk := chkPairs_true
  simp only [chkPairs, List.all_eq_true, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq,
    bne_iff_ne, ne_eq] at hk
  have hrc : RepL (comp (tpTab.getD c []) (tpTab.getD d [])) (((sY a * sY b : Y)) : P45) := by
    rw [h]
    exact repL_mul (repL_sY c) (repL_sY d)
  have hl : comp (tpTab.getD a []) (tpTab.getD b []) = comp (tpTab.getD c []) (tpTab.getD d []) :=
    repL_unique (repL_mul (repL_sY a) (repL_sY b)) hrc
  have hab' : (a : ℕ) ≠ b := fun e => hab (Fin.ext e)
  have hcd' : (c : ℕ) ≠ d := fun e => hcd (Fin.ext e)
  rcases hk a.val ha b.val hb c.val hc d.val hd with (((h1 | h1) | h1) | h1) | h1
  · exact absurd h1 hab'
  · exact absurd h1 hcd'
  · exact absurd hl h1
  · exact Or.inl ⟨Fin.ext h1.1, Fin.ext h1.2⟩
  · exact Or.inr ⟨Fin.ext h1.1, Fin.ext h1.2⟩

theorem exists_P2_conj_tPrime :
    ∃ m ∈ P2, m * tPrime * m⁻¹ = tY := by
  have h := chkConj_true
  simp only [chkConj, Bool.and_eq_true, beq_iff_eq] at h
  refine ⟨⟨wordP wConj, wordP_mem _⟩, ?_, ?_⟩
  · rw [mem_P2_iff]
    show (wordP wConj) '' L0S = L0S
    rw [L0S, image_lineSet (repL_wordP _) L0_lt, lineSet_eq_of_sameSet h.1]
  · have e : (⟨wordP wConj, wordP_mem _⟩ : Y) * tPrime = tY * ⟨wordP wConj, wordP_mem _⟩ :=
      eq_of_lists (repL_mul (repL_wordP wConj) repL_tPrime)
        (repL_mul repL_t45 (repL_wordP wConj)) h.2
    calc (⟨wordP wConj, wordP_mem _⟩ : Y) * tPrime * (⟨wordP wConj, wordP_mem _⟩ : Y)⁻¹
        = tY * ⟨wordP wConj, wordP_mem _⟩ * (⟨wordP wConj, wordP_mem _⟩ : Y)⁻¹ := by rw [e]
      _ = tY := by group

theorem conj_sY_fifteen {e : Y} (heP : e ∈ P2)
    (hc : e * tPrime = tPrime * e) : e * sY 15 * e⁻¹ = sY 15 ∨ e * sY 15 * e⁻¹ = sY 16 := by
  have himg : ∀ p : Fin 45, p ∈ L0S → (e : P45) p ∈ L0S := by
    intro p hp
    have h := (mem_P2_iff e).1 heP
    rw [← h]
    exact ⟨p, hp, rfl⟩
  have h15 := himg 15 mem_L0S_fifteen
  have h16 := himg 16 mem_L0S_sixteen
  have hne : (e : P45) 15 ≠ (e : P45) 16 := fun h => absurd ((e : P45).injective h) (by decide)
  have hprod : sY ((e : P45) 15) * sY ((e : P45) 16) = sY 15 * sY 16 := by
    rw [← sY_conj, ← sY_conj]
    have : e * tPrime * e⁻¹ = tPrime := by rw [hc]; group
    calc e * sY 15 * e⁻¹ * (e * sY 16 * e⁻¹) = e * (sY 15 * sY 16) * e⁻¹ := by group
      _ = tPrime := this
  rcases pair_eq h15 h16 mem_L0S_fifteen mem_L0S_sixteen hne (by decide) hprod with h | h
  · left
    rw [sY_conj, h.1]
  · right
    rw [sY_conj, h.1]

end CFSG.Quasithin.H13.F431.U42
