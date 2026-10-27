module

public import CFSG.LocalAnalysis.WeakClosure81.W183FinSp44Emb
public import CFSG.LocalAnalysis.WeakClosure81.W183FinSp44Klein
public import CFSG.LocalAnalysis.WeakClosure81.W183FinSp44DataG3
import CFSG.Mathlib.Decide.Nodup
import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X3AutBridge

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open Subgroup
open CFSG.LocalAnalysis.UniquenessCase.UC22 (IsSp4)

namespace Sp44

private theorem w183finSp44G3_mem_Pel_of_mem_invs {x : El} (hx : x ∈ invs) : x ∈ Pel :=
  (List.mem_filter.mp hx).1

private theorem w183finSp44G3_ne_one_of_mem_invs {x : El} (hx : x ∈ invs) : x ≠ oneE := by
  have hcond := (List.mem_filter.mp hx).2
  rw [Bool.and_eq_true_iff] at hcond
  exact of_decide_eq_true hcond.1

private theorem w183finSp44G3_invsA_mem {i : Nat} (hi : i < n127) : invsA[i]! ∈ invs := by
  rw [invsA, List.getElem!_toArray, List.getElem!_eq_getElem?_getD]
  have hsome : invs[i]? = some (invs[i]'hi) :=
    (List.getElem?_eq_some_getElem_iff hi).mpr trivial
  simpa [hsome] using List.mem_of_getElem? hsome

private theorem w183finSp44G3_invsA_ne_one {i : Nat} (hi : i < n127) : invsA[i]! ≠ oneE :=
  w183finSp44G3_ne_one_of_mem_invs (w183finSp44G3_invsA_mem hi)

private theorem w183finSp44G3_valid_invsA {i : Nat} (hi : i < n127) :
    validB invsA[i]! = true :=
  Pel_valid _ (w183finSp44G3_mem_Pel_of_mem_invs (w183finSp44G3_invsA_mem hi))

private def w183finSp44G3_invsKey (x : El) : Nat :=
  e2 x.1 0 1 + 4 * (e2 x.1 0 2 + 4 * (e2 x.1 0 3 + 4 * (e2 x.1 1 2 + 4 * x.2)))

private theorem w183finSp44G3_invs_nodup : invs.Nodup :=
  CFSG.Decide.nodup_of_bitsetNodup w183finSp44G3_invsKey (by decide +kernel)

private theorem w183finSp44G3_invsA_ne {i j : Nat} (hi : i < n127) (hj : j < n127)
    (hij : i < j) : invsA[i]! ≠ invsA[j]! := by
  intro h
  have hi' : i < invs.length := hi
  have hj' : j < invs.length := hj
  have h1 : invs[i]! = invs[i]'hi' := by
    rw [List.getElem!_eq_getElem?_getD, ← List.getD_eq_getElem?_getD]
    exact (List.getElem_eq_getD (l := invs) (i := i) (h := hi') default).symm
  have h2 : invs[j]! = invs[j]'hj' := by
    rw [List.getElem!_eq_getElem?_getD, ← List.getD_eq_getElem?_getD]
    exact (List.getElem_eq_getD (l := invs) (i := j) (h := hj') default).symm
  have e1 : invsA[i]! = invs[i]'hi' := by
    rw [invsA, List.getElem!_toArray]; exact h1
  have e2 : invsA[j]! = invs[j]'hj' := by
    rw [invsA, List.getElem!_toArray]; exact h2
  have h' : invs[i]'hi' = invs[j]'hj' := by
    rw [← e1, ← e2]; exact h
  exact absurd ((List.Nodup.getElem_inj_iff w183finSp44G3_invs_nodup (hi := hi')
    (hj := hj')).mp h') (ne_of_lt hij)

private theorem w183finSp44G3_mem_klein_iff {a b x : El} :
    x ∈ klein a b ↔ x = oneE ∨ x = a ∨ x = b ∨ x = gmulE a b := by
  rw [klein]
  simp only [List.mem_cons, List.mem_nil_iff, List.not_mem_nil, false_or, or_false]

private theorem w183finSp44G3_valid_klein {a b x : El} (ha : validB a = true)
    (hb : validB b = true) (hx : x ∈ klein a b) : validB x = true := by
  rw [w183finSp44G3_mem_klein_iff] at hx
  rcases hx with rfl | rfl | rfl | rfl
  · exact validB_oneE
  · exact ha
  · exact hb
  · exact validB_gmulE ha hb

private theorem w183finSp44G3_memK_eq_true {K : List El} {x : El} :
    memK K x = true ↔ x ∈ K := by
  rw [memK, List.any_eq_true]
  constructor
  · rintro ⟨y, hy, hyx⟩
    have hyx' : y = x := beq_iff_eq.mp hyx
    rwa [hyx'] at hy
  · intro hx
    exact ⟨x, hx, by rw [beq_iff_eq]⟩

private theorem w183finSp44G3_innAutOf_normal : (innAutOf S4).Normal where
  conj_mem := by
    rintro _ ⟨x, rfl⟩ φ
    refine ⟨φ x, MulEquiv.ext fun y => ?_⟩
    simp [MulAut.conj_apply, MulAut.mul_apply]

private def w183finSp44G3_poolB : Bool := g3Pool.all fun m => validB (m, 0)

private theorem w183finSp44G3_poolB_eq : w183finSp44G3_poolB = true := by decide +kernel

private theorem w183finSp44G3_pool_valid {m : Nat} (hm : m ∈ g3Pool) :
    validB (m, 0) = true :=
  (List.all_eq_true.mp w183finSp44G3_poolB_eq) m hm

private def w183finSp44G3_rowPoolB : Bool :=
  g3Rows.flatten.all fun e => e / 16 < g3Pool.length

private theorem w183finSp44G3_rowPoolB_eq : w183finSp44G3_rowPoolB = true := by decide +kernel

private theorem w183finSp44G3_row_pool_lt {e : Nat} (he : e ∈ g3Rows.flatten) :
    e / 16 < g3Pool.length :=
  of_decide_eq_true ((List.all_eq_true.mp w183finSp44G3_rowPoolB_eq) e he)

private def w183finSp44G3_rowModB : Bool :=
  g3Rows.flatten.all fun e => decide (e % 2 = 0 → e / 2 % 4 < 3)

private theorem w183finSp44G3_rowModB_eq : w183finSp44G3_rowModB = true := by decide +kernel

private theorem w183finSp44G3_rowMod {e : Nat} (he : e ∈ g3Rows.flatten) (he2 : e % 2 = 0) :
    e / 2 % 4 < 3 :=
  (of_decide_eq_true ((List.all_eq_true.mp w183finSp44G3_rowModB_eq) e he)) he2

private theorem w183finSp44G3_g3Rows_length : g3Rows.length = 8 := by decide +kernel

private theorem w183finSp44G3_mem_flatten {k : Nat} (hk : k < 8) {e : Nat}
    (he : e ∈ g3Rows.getD k []) : e ∈ g3Rows.flatten := by
  have hk' : k < g3Rows.length := by rw [w183finSp44G3_g3Rows_length]; exact hk
  have h2 : g3Rows.getD k [] = g3Rows[k] := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk']; rfl
  exact List.mem_flatten.mpr ⟨g3Rows[k], List.getElem_mem hk', h2 ▸ he⟩

private theorem w183finSp44G3_exists_row (p : Nat × Nat) (hp : p ∈ pairsL) :
    ∃ k < 8, ∃ e ∈ g3Rows.getD k [], checkG3 invsA[p.1]! invsA[p.2]! e = true := by
  obtain ⟨b, hb, hpb⟩ := List.mem_flatMap.mp hp
  obtain ⟨k, hk, rfl⟩ := List.mem_iff_getElem.mp hb
  have hk8 : k < 8 := by simpa [pairBlocks] using hk
  have h2 : pairBlocks.getD k (0, 0) = pairBlocks[k] := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk]; rfl
  have hg := g3_blocks k hk8
  simp only [g3BlockOK, Bool.and_eq_true, beq_iff_eq] at hg
  obtain ⟨hlen, hall⟩ := hg
  rw [h2] at hlen hall
  obtain ⟨e, he, hcheck⟩ :=
    CFSG.QuasithinUnique.Setup.X3Aut.exists_of_all_zip
      (fun (a : Nat × Nat) (b : Nat) => checkG3 invsA[a.1]! invsA[a.2]! b)
      (pairsFrom (pairBlocks[k]).1 (pairBlocks[k]).2) (g3Rows.getD k []) hall hlen p hpb
  exact ⟨k, hk8, e, he, hcheck⟩

private theorem w183finSp44G3_check_even {a b : El} {e : Nat} (he2 : e % 2 = 0)
    (h : checkG3 a b e = true) :
    (gmulE (g3Pool.getD (e / 16) 0, 0)
        ([a, b, gmulE a b].getD (e / 2 % 4) oneE) =
      gmulE ([a, b, gmulE a b].getD (e / 2 % 4) oneE)
        (g3Pool.getD (e / 16) 0, 0)) ∧
    (gmulE (g3Pool.getD (e / 16) 0, 0) ([a, b].getD (e / 8 % 2) oneE) ≠
      gmulE ([a, b].getD (e / 8 % 2) oneE) (g3Pool.getD (e / 16) 0, 0)) := by
  simp only [checkG3] at h
  rw [if_pos (by rw [beq_iff_eq]; exact he2)] at h
  rw [Bool.and_eq_true] at h
  exact ⟨beq_iff_eq.mp h.1, bne_iff_ne.mp h.2⟩

private theorem w183finSp44G3_check_odd {a b : El} {e : Nat} (he2 : e % 2 = 1)
    (h : checkG3 a b e = true) :
    a.2 = 0 ∧ b.2 = 0 ∧
      ((klein a b).drop 1).all (fun x =>
        memK (klein a b) (conjE (g3Pool.getD (e / 16) 0, 0) x) &&
          (conjE (g3Pool.getD (e / 16) 0, 0) x != x)) = true := by
  simp only [checkG3] at h
  rw [if_neg (by rw [beq_iff_eq]; omega)] at h
  rw [Bool.and_eq_true, Bool.and_eq_true] at h
  exact ⟨beq_iff_eq.mp h.1.1, beq_iff_eq.mp h.1.2, h.2⟩

private theorem w183finSp44G3_mem_autConj_iff {h : MulAut S4} {A : Subgroup (MulAut S4)}
    {y : MulAut S4} : y ∈ autConj h A ↔ h⁻¹ * y * h ∈ A := by
  rw [autConj, Subgroup.mem_map]
  constructor
  · rintro ⟨x, hx, hxeq⟩
    rw [← hxeq]
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    have heq : h⁻¹ * (h * x * h⁻¹) * h = x := by group
    rwa [heq]
  · intro hy
    refine ⟨MulAut.conj h⁻¹ y, ?_, ?_⟩
    · show (MulAut.conj h⁻¹) y ∈ A
      rw [MulAut.conj_apply]
      have heq : h⁻¹ * y * h⁻¹⁻¹ = h⁻¹ * y * h := by group
      rwa [heq]
    · show (MulAut.conj h) ((MulAut.conj h⁻¹) y) = y
      rw [MulAut.conj_apply, MulAut.conj_apply]
      group

private theorem w183finSp44G3_le_inn_of_autConj_le {h : MulAut S4} {A : Subgroup (MulAut S4)}
    (hle : autConj h A ≤ innAutOf S4) : A ≤ innAutOf S4 := by
  intro x hx
  have hmem : h * x * h⁻¹ ∈ autConj h A := by
    rw [w183finSp44G3_mem_autConj_iff]
    have heq : h⁻¹ * (h * x * h⁻¹) * h = x := by group
    rwa [heq]
  have hIn := hle hmem
  have hconj := w183finSp44G3_innAutOf_normal.conj_mem' (h * x * h⁻¹) hIn h
  have heq : h⁻¹ * (h * x * h⁻¹) * h = x := by group
  rwa [heq] at hconj

private theorem w183finSp44G3_ti1_of_autConj {h : MulAut S4} {A : Subgroup (MulAut S4)}
    (hTI1 : ∀ t ∈ A, t ≠ 1 → ∀ g ∈ innAutOf S4, g * t = t * g → ∀ a ∈ A, g * a = a * g) :
    ∀ t ∈ autConj h A, t ≠ 1 → ∀ g ∈ innAutOf S4, g * t = t * g →
      ∀ a ∈ autConj h A, g * a = a * g := by
  intro t ht ht1 g hg hgt a ha
  rw [w183finSp44G3_mem_autConj_iff] at ht ha
  have ht1' : h⁻¹ * t * h ≠ 1 := by
    intro hcon
    apply ht1
    calc t = h * (h⁻¹ * t * h) * h⁻¹ := by group
      _ = h * 1 * h⁻¹ := by rw [hcon]
      _ = 1 := by group
  have hg' : h⁻¹ * g * h ∈ innAutOf S4 := w183finSp44G3_innAutOf_normal.conj_mem' g hg h
  have hgt' : (h⁻¹ * g * h) * (h⁻¹ * t * h) = (h⁻¹ * t * h) * (h⁻¹ * g * h) := by
    calc (h⁻¹ * g * h) * (h⁻¹ * t * h) = h⁻¹ * (g * t) * h := by group
      _ = h⁻¹ * (t * g) * h := by rw [hgt]
      _ = (h⁻¹ * t * h) * (h⁻¹ * g * h) := by group
  have hga := hTI1 (h⁻¹ * t * h) ht ht1' (h⁻¹ * g * h) hg' hgt' (h⁻¹ * a * h) ha
  calc g * a = h * (h⁻¹ * g * h) * (h⁻¹ * a * h) * h⁻¹ := by group
    _ = h * ((h⁻¹ * g * h) * (h⁻¹ * a * h)) * h⁻¹ := by group
    _ = h * ((h⁻¹ * a * h) * (h⁻¹ * g * h)) * h⁻¹ := by rw [hga]
    _ = a * g := by group

private theorem w183finSp44G3_concl_of_autConj {h : MulAut S4} {A : Subgroup (MulAut S4)}
    (hconcl : ∃ n ∈ innAutOf S4, (∀ x ∈ autConj h A, n * x * n⁻¹ ∈ autConj h A) ∧
      ∀ x ∈ autConj h A, x ≠ 1 → n * x * n⁻¹ ≠ x) :
    ∃ n ∈ innAutOf S4, (∀ x ∈ A, n * x * n⁻¹ ∈ A) ∧
      ∀ x ∈ A, x ≠ 1 → n * x * n⁻¹ ≠ x := by
  obtain ⟨n, hn, hmem, hfix⟩ := hconcl
  refine ⟨h⁻¹ * n * h, w183finSp44G3_innAutOf_normal.conj_mem' n hn h, ?_, ?_⟩
  · intro x hx
    have hx' : h * x * h⁻¹ ∈ autConj h A := by
      rw [w183finSp44G3_mem_autConj_iff]
      have heq : h⁻¹ * (h * x * h⁻¹) * h = x := by group
      rwa [heq]
    have hthis := hmem (h * x * h⁻¹) hx'
    rw [w183finSp44G3_mem_autConj_iff] at hthis
    have heq : (h⁻¹ * n * h) * x * (h⁻¹ * n * h)⁻¹ =
        h⁻¹ * (n * (h * x * h⁻¹) * n⁻¹) * h := by group
    rw [heq]
    exact hthis
  · intro x hx hx1 hfixx
    have hx' : h * x * h⁻¹ ∈ autConj h A := by
      rw [w183finSp44G3_mem_autConj_iff]
      have heq : h⁻¹ * (h * x * h⁻¹) * h = x := by group
      rwa [heq]
    have hne : h * x * h⁻¹ ≠ 1 := by
      intro hcon
      apply hx1
      calc x = h⁻¹ * (h * x * h⁻¹) * h := by group
        _ = 1 := by rw [hcon]; group
    have hconj : n * (h * x * h⁻¹) * n⁻¹ = h * x * h⁻¹ := by
      calc n * (h * x * h⁻¹) * n⁻¹
          = h * ((h⁻¹ * n * h) * x * (h⁻¹ * n * h)⁻¹) * h⁻¹ := by group
        _ = h * x * h⁻¹ := by rw [hfixx]
    exact hfix (h * x * h⁻¹) hx' hne hconj

private theorem w183finSp44G3_mem_drop_a (a b : El) : a ∈ (klein a b).drop 1 := by
  change a ∈ [a, b, gmulE a b]
  exact List.mem_cons_self

private theorem w183finSp44G3_mem_drop_b (a b : El) : b ∈ (klein a b).drop 1 := by
  change b ∈ [a, b, gmulE a b]
  exact List.mem_cons_of_mem _ List.mem_cons_self

private theorem w183finSp44G3_mem_drop_ab (a b : El) : gmulE a b ∈ (klein a b).drop 1 := by
  change gmulE a b ∈ [a, b, gmulE a b]
  exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)

theorem ti1_four_group (A : Subgroup (MulAut S4)) (hcard : Nat.card A = 4)
    (hel : IsElemAbelian 2 A)
    (hTI1 : ∀ t ∈ A, t ≠ 1 → ∀ g ∈ innAutOf S4, g * t = t * g → ∀ a ∈ A, g * a = a * g) :
    A ≤ innAutOf S4 ∧ ∃ n ∈ innAutOf S4, (∀ x ∈ A, n * x * n⁻¹ ∈ A) ∧
      ∀ x ∈ A, x ≠ 1 → n * x * n⁻¹ ≠ x := by
  classical
  obtain ⟨h, p, hp, hA'⟩ := exists_conj_klein A hel hcard
  have hTI1aut := w183finSp44G3_ti1_of_autConj (h := h) hTI1
  have hTI1k : ∀ t ∈ kleinSub invsA[p.1]! invsA[p.2]!, t ≠ 1 →
      ∀ g ∈ innAutOf S4, g * t = t * g →
      ∀ a ∈ kleinSub invsA[p.1]! invsA[p.2]!, g * a = a * g := by
    intro t ht ht1 g hg hgt a ha
    exact hTI1aut t (hA'.symm ▸ ht) ht1 g hg hgt a (hA'.symm ▸ ha)
  obtain ⟨h12, h2, -⟩ := (mem_pairsL_iff p).mp hp
  have h2n : p.2 < n127 := by rw [n127, invs_length]; exact h2
  have h1n : p.1 < n127 := lt_trans h12 h2n
  have ha_valid : validB invsA[p.1]! = true := w183finSp44G3_valid_invsA h1n
  have hb_valid : validB invsA[p.2]! = true := w183finSp44G3_valid_invsA h2n
  have ha_ne : invsA[p.1]! ≠ oneE := w183finSp44G3_invsA_ne_one h1n
  have hb_ne : invsA[p.2]! ≠ oneE := w183finSp44G3_invsA_ne_one h2n
  have hab_ne : invsA[p.1]! ≠ invsA[p.2]! := w183finSp44G3_invsA_ne h1n h2n h12
  obtain ⟨-, helk⟩ := card_isElemAbelian_kleinSub hp
  have haa : autOf invsA[p.1]! * autOf invsA[p.1]! = 1 := by
    have hmem : autOf invsA[p.1]! ∈ kleinSub invsA[p.1]! invsA[p.2]! :=
      (mem_kleinSub_iff hp (autOf invsA[p.1]!)).mpr
        ⟨invsA[p.1]!, w183finSp44G3_mem_klein_iff.mpr (Or.inr (Or.inl rfl)), rfl⟩
    have := helk.2 (autOf invsA[p.1]!) hmem
    simpa [pow_two] using this
  have hbb : autOf invsA[p.2]! * autOf invsA[p.2]! = 1 := by
    have hmem : autOf invsA[p.2]! ∈ kleinSub invsA[p.1]! invsA[p.2]! :=
      (mem_kleinSub_iff hp (autOf invsA[p.2]!)).mpr
        ⟨invsA[p.2]!, w183finSp44G3_mem_klein_iff.mpr (Or.inr (Or.inr (Or.inl rfl))), rfl⟩
    have := helk.2 (autOf invsA[p.2]!) hmem
    simpa [pow_two] using this
  obtain ⟨k, hk8, e, he, hcheck⟩ := w183finSp44G3_exists_row p hp
  have heflat : e ∈ g3Rows.flatten := w183finSp44G3_mem_flatten hk8 he
  have hpM_lt : e / 16 < g3Pool.length := w183finSp44G3_row_pool_lt heflat
  have hpM_def : g3Pool.getD (e / 16) 0 = g3Pool[e / 16] := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hpM_lt]; rfl
  have hpool_valid : validB (g3Pool.getD (e / 16) 0, 0) = true := by
    rw [hpM_def]
    exact w183finSp44G3_pool_valid (List.getElem_mem hpM_lt)
  have hmain : kleinSub invsA[p.1]! invsA[p.2]! ≤ innAutOf S4 ∧
      ∃ n ∈ innAutOf S4,
        (∀ x ∈ kleinSub invsA[p.1]! invsA[p.2]!, n * x * n⁻¹ ∈ kleinSub invsA[p.1]! invsA[p.2]!) ∧
        ∀ x ∈ kleinSub invsA[p.1]! invsA[p.2]!, x ≠ 1 → n * x * n⁻¹ ≠ x := by
    by_cases he2 : e % 2 = 0
    · exfalso
      have heven := w183finSp44G3_check_even (a := invsA[p.1]!) (b := invsA[p.2]!) he2 hcheck
      let pE : El := (g3Pool.getD (e / 16) 0, 0)
      let t : El := [invsA[p.1]!, invsA[p.2]!, gmulE invsA[p.1]! invsA[p.2]!].getD
        (e / 2 % 4) oneE
      let x : El := [invsA[p.1]!, invsA[p.2]!].getD (e / 8 % 2) oneE
      have hpE_valid : validB pE = true := hpool_valid
      have hcommE : gmulE pE t = gmulE t pE := heven.1
      have hncommE : gmulE pE x ≠ gmulE x pE := heven.2
      have hidx : e / 2 % 4 < 3 := w183finSp44G3_rowMod heflat he2
      have ht_mem : t ∈ klein invsA[p.1]! invsA[p.2]! := by
        show [invsA[p.1]!, invsA[p.2]!, gmulE invsA[p.1]! invsA[p.2]!].getD
          (e / 2 % 4) oneE ∈ klein invsA[p.1]! invsA[p.2]!
        rw [List.getD_eq_getElem (l := [invsA[p.1]!, invsA[p.2]!,
          gmulE invsA[p.1]! invsA[p.2]!]) (d := oneE) hidx]
        exact List.mem_cons_of_mem oneE
          (List.getElem_mem (l := [invsA[p.1]!, invsA[p.2]!,
            gmulE invsA[p.1]! invsA[p.2]!]) hidx)
      have ht_valid : validB t = true :=
        w183finSp44G3_valid_klein ha_valid hb_valid ht_mem
      have ht_cases : t = invsA[p.1]! ∨ t = invsA[p.2]! ∨
          t = gmulE invsA[p.1]! invsA[p.2]! := by
        have ht_eq : t = [invsA[p.1]!, invsA[p.2]!,
            gmulE invsA[p.1]! invsA[p.2]!][e / 2 % 4] := by
          show [invsA[p.1]!, invsA[p.2]!, gmulE invsA[p.1]! invsA[p.2]!].getD
            (e / 2 % 4) oneE = _
          rw [List.getD_eq_getElem (l := [invsA[p.1]!, invsA[p.2]!,
            gmulE invsA[p.1]! invsA[p.2]!]) (d := oneE) hidx]
        rw [ht_eq]
        rcases List.mem_cons.mp (List.getElem_mem (l := [invsA[p.1]!, invsA[p.2]!,
          gmulE invsA[p.1]! invsA[p.2]!]) hidx) with h0 | h0
        · exact Or.inl h0
        rcases List.mem_cons.mp h0 with h0 | h0
        · exact Or.inr (Or.inl h0)
        rcases List.mem_cons.mp h0 with h0 | h0
        · exact Or.inr (Or.inr h0)
        · exact (List.not_mem_nil h0).elim
      have ht_ne : autOf t ≠ 1 := by
        rcases ht_cases with h0 | h0 | h0
        · rw [h0]
          intro hcon
          exact ha_ne (autOf_inj ha_valid validB_oneE (by rw [hcon, autOf_oneE]))
        · rw [h0]
          intro hcon
          exact hb_ne (autOf_inj hb_valid validB_oneE (by rw [hcon, autOf_oneE]))
        · rw [h0]
          intro hcon
          rw [autOf_gmulE ha_valid hb_valid] at hcon
          have hab_eq : autOf invsA[p.1]! = autOf invsA[p.2]! := by
            have h1 : autOf invsA[p.1]! * autOf invsA[p.2]! =
                autOf invsA[p.1]! * autOf invsA[p.1]! := by rw [hcon, haa]
            exact (mul_left_cancel h1).symm
          exact hab_ne (autOf_inj ha_valid hb_valid hab_eq)
      have hx_lt : e / 8 % 2 < 2 := Nat.mod_lt _ (by norm_num)
      have hx_mem : x ∈ klein invsA[p.1]! invsA[p.2]! := by
        have hx_eq : x = [invsA[p.1]!, invsA[p.2]!][e / 8 % 2] := by
          show [invsA[p.1]!, invsA[p.2]!].getD (e / 8 % 2) oneE = _
          rw [List.getD_eq_getElem (l := [invsA[p.1]!, invsA[p.2]!]) (d := oneE) hx_lt]
        rw [hx_eq]
        rcases List.mem_cons.mp
            (List.getElem_mem (l := [invsA[p.1]!, invsA[p.2]!]) hx_lt) with h0 | h0
        · rw [h0]
          exact w183finSp44G3_mem_klein_iff.mpr (Or.inr (Or.inl rfl))
        · rcases List.mem_cons.mp h0 with h0 | h0
          · rw [h0]
            exact w183finSp44G3_mem_klein_iff.mpr (Or.inr (Or.inr (Or.inl rfl)))
          · exact (List.not_mem_nil h0).elim
      have hx_valid : validB x = true :=
        w183finSp44G3_valid_klein ha_valid hb_valid hx_mem
      have hpInn : autOf pE ∈ innAutOf S4 := (autOf_inner_iff hpE_valid).mpr rfl
      have hcomm_aut : autOf pE * autOf t = autOf t * autOf pE := by
        rw [← autOf_gmulE hpE_valid ht_valid, ← autOf_gmulE ht_valid hpE_valid, hcommE]
      have hncomm_aut : autOf pE * autOf x ≠ autOf x * autOf pE := by
        intro hcon
        apply hncommE
        apply autOf_inj (validB_gmulE hpE_valid hx_valid) (validB_gmulE hx_valid hpE_valid)
        rw [autOf_gmulE hpE_valid hx_valid, autOf_gmulE hx_valid hpE_valid]
        exact hcon
      have htA' : autOf t ∈ kleinSub invsA[p.1]! invsA[p.2]! :=
        (mem_kleinSub_iff hp (autOf t)).mpr ⟨t, ht_mem, rfl⟩
      have hxA' : autOf x ∈ kleinSub invsA[p.1]! invsA[p.2]! :=
        (mem_kleinSub_iff hp (autOf x)).mpr ⟨x, hx_mem, rfl⟩
      exact hncomm_aut (hTI1k (autOf t) htA' ht_ne (autOf pE) hpInn hcomm_aut (autOf x) hxA')
    · have hodd : e % 2 = 1 := by omega
      have hodd_data := w183finSp44G3_check_odd (a := invsA[p.1]!) (b := invsA[p.2]!) hodd hcheck
      obtain ⟨ha0, hb0, hall⟩ := hodd_data
      have hle_k : kleinSub invsA[p.1]! invsA[p.2]! ≤ innAutOf S4 := by
        intro y hy
        obtain ⟨xc, hxc_mem, rfl⟩ := (mem_kleinSub_iff hp y).mp hy
        rw [w183finSp44G3_mem_klein_iff] at hxc_mem
        rcases hxc_mem with h0 | h0 | h0 | h0
        · rw [h0, autOf_oneE]; exact Subgroup.one_mem _
        · rw [h0]; exact (autOf_inner_iff ha_valid).mpr ha0
        · rw [h0]; exact (autOf_inner_iff hb_valid).mpr hb0
        · rw [h0, autOf_gmulE ha_valid hb_valid]
          exact Subgroup.mul_mem _
            ((autOf_inner_iff ha_valid).mpr ha0) ((autOf_inner_iff hb_valid).mpr hb0)
      refine ⟨hle_k, ?_⟩
      refine ⟨autOf (g3Pool.getD (e / 16) 0, 0),
        (autOf_inner_iff hpool_valid).mpr rfl, ?_, ?_⟩
      · intro y hy
        obtain ⟨xc, hxc_mem, rfl⟩ := (mem_kleinSub_iff hp y).mp hy
        have hxc_valid : validB xc = true := w183finSp44G3_valid_klein ha_valid hb_valid hxc_mem
        rw [← autOf_conjE hpool_valid hxc_valid]
        have hxc_cases := (w183finSp44G3_mem_klein_iff).mp hxc_mem
        rcases hxc_cases with h0 | h0 | h0 | h0
        · rw [h0, autOf_conjE hpool_valid validB_oneE, autOf_oneE, mul_one, mul_inv_cancel]
          exact Subgroup.one_mem _
        · rw [h0]
          have hfa := (List.all_eq_true.mp hall) _ (w183finSp44G3_mem_drop_a _ _)
          rw [Bool.and_eq_true] at hfa
          exact (mem_kleinSub_iff hp (autOf (conjE (g3Pool.getD (e / 16) 0, 0) invsA[p.1]!))).mpr
            ⟨conjE (g3Pool.getD (e / 16) 0, 0) invsA[p.1]!,
              w183finSp44G3_memK_eq_true.mp hfa.1, rfl⟩
        · rw [h0]
          have hfb := (List.all_eq_true.mp hall) _ (w183finSp44G3_mem_drop_b _ _)
          rw [Bool.and_eq_true] at hfb
          exact (mem_kleinSub_iff hp (autOf (conjE (g3Pool.getD (e / 16) 0, 0) invsA[p.2]!))).mpr
            ⟨conjE (g3Pool.getD (e / 16) 0, 0) invsA[p.2]!,
              w183finSp44G3_memK_eq_true.mp hfb.1, rfl⟩
        · rw [h0]
          have hfab := (List.all_eq_true.mp hall) _ (w183finSp44G3_mem_drop_ab _ _)
          rw [Bool.and_eq_true] at hfab
          exact (mem_kleinSub_iff hp (autOf (conjE (g3Pool.getD (e / 16) 0, 0)
            (gmulE invsA[p.1]! invsA[p.2]!)))).mpr
            ⟨conjE (g3Pool.getD (e / 16) 0, 0) (gmulE invsA[p.1]! invsA[p.2]!),
              w183finSp44G3_memK_eq_true.mp hfab.1, rfl⟩
      · intro y hy hy1
        obtain ⟨xc, hxc_mem, rfl⟩ := (mem_kleinSub_iff hp y).mp hy
        have hxc_valid : validB xc = true := w183finSp44G3_valid_klein ha_valid hb_valid hxc_mem
        have hxc_ne : xc ≠ oneE := by
          intro h0
          apply hy1
          rw [h0, autOf_oneE]
        have hcne : conjE (g3Pool.getD (e / 16) 0, 0) xc ≠ xc := by
          have hxc_cases := (w183finSp44G3_mem_klein_iff).mp hxc_mem
          rcases hxc_cases with h0 | h0 | h0 | h0
          · rw [h0] at hxc_ne ⊢
            exact absurd rfl hxc_ne
          · rw [h0]
            have hfa := (List.all_eq_true.mp hall) _ (w183finSp44G3_mem_drop_a _ _)
            rw [Bool.and_eq_true] at hfa
            exact bne_iff_ne.mp hfa.2
          · rw [h0]
            have hfb := (List.all_eq_true.mp hall) _ (w183finSp44G3_mem_drop_b _ _)
            rw [Bool.and_eq_true] at hfb
            exact bne_iff_ne.mp hfb.2
          · rw [h0]
            have hfab := (List.all_eq_true.mp hall) _ (w183finSp44G3_mem_drop_ab _ _)
            rw [Bool.and_eq_true] at hfab
            exact bne_iff_ne.mp hfab.2
        rw [← autOf_conjE hpool_valid hxc_valid]
        intro heq
        exact hcne (autOf_inj (validB_conjE hpool_valid hxc_valid) hxc_valid heq)
  obtain ⟨hle_k, hconcl_k⟩ := hmain
  have hle_aut : autConj h A ≤ innAutOf S4 := by rw [hA']; exact hle_k
  have hconcl_aut : ∃ n ∈ innAutOf S4,
      (∀ x ∈ autConj h A, n * x * n⁻¹ ∈ autConj h A) ∧
      ∀ x ∈ autConj h A, x ≠ 1 → n * x * n⁻¹ ≠ x := by
    rw [hA']; exact hconcl_k
  exact ⟨w183finSp44G3_le_inn_of_autConj_le hle_aut,
    w183finSp44G3_concl_of_autConj hconcl_aut⟩

end Sp44

theorem finG3Sp44_holds
    (Y : Type) [Group Y] [Finite Y] (L : Subgroup Y) (hLn : L.Normal) (hSp : IsSp4 ↥L 2)
    (hC : Subgroup.centralizer (L : Set Y) = ⊥) (A : Subgroup Y) (hcard : Nat.card A = 4)
    (hel : IsElemAbelian 2 A)
    (hTI1 : ∀ t ∈ A, t ≠ 1 → ∀ g ∈ L, g * t = t * g → ∀ a ∈ A, g * a = a * g) :
    A ≤ L ∧ ∃ n ∈ L, (∀ x ∈ A, n * x * n⁻¹ ∈ A) ∧ ∀ x ∈ A, x ≠ 1 → n * x * n⁻¹ ≠ x := by
  obtain ⟨f, hf, hLf⟩ := Sp44.exists_emb Y L hLn hSp hC
  set A' : Subgroup (MulAut Sp44.S4) := A.map f with hA'def
  have hA'card : Nat.card A' = 4 := by
    rw [hA'def, Subgroup.card_map_of_injective hf, hcard]
  have hA'el : IsElemAbelian 2 A' := by
    rw [hA'def]
    exact CFSG.Open.IsElemAbelian.map hel f
  have hA'TI : ∀ t ∈ A', t ≠ 1 → ∀ g ∈ innAutOf Sp44.S4, g * t = t * g →
      ∀ a ∈ A', g * a = a * g := by
    intro t htA ht1 g hg hgt a haA
    rw [hA'def] at htA haA
    obtain ⟨t₀, ht₀, rfl⟩ := Subgroup.mem_map.mp htA
    obtain ⟨a₀, ha₀, rfl⟩ := Subgroup.mem_map.mp haA
    have hg' : g ∈ L.map f := by rwa [← hLf] at hg
    obtain ⟨g₀, hg₀, rfl⟩ := Subgroup.mem_map.mp hg'
    have ht₁ : t₀ ≠ 1 := fun h => ht1 (by rw [h, map_one])
    have hgt₀ : g₀ * t₀ = t₀ * g₀ := hf (by rw [map_mul, map_mul]; exact hgt)
    show f g₀ * f a₀ = f a₀ * f g₀
    simpa using congrArg f (hTI1 t₀ ht₀ ht₁ g₀ hg₀ hgt₀ a₀ ha₀)
  obtain ⟨hA'inn, n', hn'inn, hn'norm, hn'fpf⟩ := Sp44.ti1_four_group A' hA'card hA'el hA'TI
  refine ⟨?_, ?_⟩
  · intro x hx
    have hxinn : f x ∈ innAutOf Sp44.S4 := hA'inn (Subgroup.mem_map_of_mem f hx)
    have hximg : f x ∈ L.map f := by rwa [← hLf] at hxinn
    obtain ⟨l, hl, hlf⟩ := Subgroup.mem_map.mp hximg
    rwa [hf hlf] at hl
  · have hn'img : n' ∈ L.map f := by rwa [← hLf] at hn'inn
    obtain ⟨n, hn, hnf⟩ := Subgroup.mem_map.mp hn'img
    refine ⟨n, hn, ?_, ?_⟩
    · intro x hx
      have hx' : f x ∈ A' := Subgroup.mem_map_of_mem f hx
      have hmem : n' * f x * n'⁻¹ ∈ A' := hn'norm (f x) hx'
      rw [hA'def] at hmem
      obtain ⟨a, ha, haf⟩ := Subgroup.mem_map.mp hmem
      have hxa : n * x * n⁻¹ = a := by
        apply hf
        rw [map_mul, map_mul, map_inv, hnf]
        exact haf.symm
      rw [hxa]
      exact ha
    · intro x hx hx1 hfix
      have hx' : f x ∈ A' := Subgroup.mem_map_of_mem f hx
      have hx1' : f x ≠ 1 := fun h => hx1 (hf (by rw [h, map_one]))
      refine hn'fpf (f x) hx' hx1' ?_
      have hthis : n' * f x * n'⁻¹ = f (n * x * n⁻¹) := by
        rw [← hnf, map_mul, map_mul, map_inv]
      rw [hthis, hfix]

end CFSG.LocalAnalysis.WeakClosure81

end