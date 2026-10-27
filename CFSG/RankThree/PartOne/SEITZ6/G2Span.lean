module

public import CFSG.RankThree.PartOne.SEITZ6.G2Form
public import CFSG.RankThree.PartOne.SEITZ6.G2Bruhat

public section

namespace CFSG.RankThree.PartOne.SEITZ6

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Ree
  CFSG.LieType.Steinberg.Adjoint CFSG.RankThree.PartOne.SEITZ3

variable {K : Type} [Field K]

theorem vand3 {k : Type*} [Field k] {V : Type*} [AddCommGroup V] [Module k V] (W : Submodule k V)
    {t₁ t₂ t₃ : k} (h₁₂ : t₁ ≠ t₂) (h₁₃ : t₁ ≠ t₃) (h₂₃ : t₂ ≠ t₃) (h₁ : t₁ ≠ 0) (h₂ : t₂ ≠ 0)
    (h₃ : t₃ ≠ 0) {u₁ u₂ u₃ : V}
    (e₁ : t₁ • u₁ + t₁ ^ 2 • u₂ + t₁ ^ 3 • u₃ ∈ W)
    (e₂ : t₂ • u₁ + t₂ ^ 2 • u₂ + t₂ ^ 3 • u₃ ∈ W)
    (e₃ : t₃ • u₁ + t₃ ^ 2 • u₂ + t₃ ^ 3 • u₃ ∈ W) :
    u₁ ∈ W ∧ u₂ ∈ W ∧ u₃ ∈ W := by
  have d12 : t₁ - t₂ ≠ 0 := sub_ne_zero.2 h₁₂
  have d13 : t₁ - t₃ ≠ 0 := sub_ne_zero.2 h₁₃
  have d23 : t₂ - t₃ ≠ 0 := sub_ne_zero.2 h₂₃
  have d21 : t₂ - t₁ ≠ 0 := sub_ne_zero.2 h₁₂.symm
  have d31 : t₃ - t₁ ≠ 0 := sub_ne_zero.2 h₁₃.symm
  have d32 : t₃ - t₂ ≠ 0 := sub_ne_zero.2 h₂₃.symm
  have key : ∀ (a b c : k), a • (t₁ • u₁ + t₁ ^ 2 • u₂ + t₁ ^ 3 • u₃) +
      b • (t₂ • u₁ + t₂ ^ 2 • u₂ + t₂ ^ 3 • u₃) +
        c • (t₃ • u₁ + t₃ ^ 2 • u₂ + t₃ ^ 3 • u₃) ∈ W :=
    fun a b c => W.add_mem (W.add_mem (W.smul_mem a e₁) (W.smul_mem b e₂)) (W.smul_mem c e₃)
  refine ⟨?_, ?_, ?_⟩
  · have := key (t₂ * t₃ / (t₁ * (t₁ - t₂) * (t₁ - t₃)))
      (t₁ * t₃ / (t₂ * (t₂ - t₁) * (t₂ - t₃))) (t₁ * t₂ / (t₃ * (t₃ - t₁) * (t₃ - t₂)))
    convert this using 1
    match_scalars <;> field_simp <;> ring
  · have := key (-(t₂ + t₃) / (t₁ * (t₁ - t₂) * (t₁ - t₃)))
      (-(t₁ + t₃) / (t₂ * (t₂ - t₁) * (t₂ - t₃))) (-(t₁ + t₂) / (t₃ * (t₃ - t₁) * (t₃ - t₂)))
    convert this using 1
    match_scalars <;> field_simp <;> ring
  · have := key (1 / (t₁ * (t₁ - t₂) * (t₁ - t₃))) (1 / (t₂ * (t₂ - t₁) * (t₂ - t₃)))
      (1 / (t₃ * (t₃ - t₁) * (t₃ - t₂)))
    convert this using 1
    match_scalars <;> field_simp <;> ring

theorem exists_three_nonzero (k : Subfield K) (hk : 4 ≤ Nat.card k) :
    ∃ t₁ t₂ t₃ : k, t₁ ≠ t₂ ∧ t₁ ≠ t₃ ∧ t₂ ≠ t₃ ∧ t₁ ≠ 0 ∧ t₂ ≠ 0 ∧ t₃ ≠ 0 := by
  classical
  have hfin : Finite k := Nat.finite_of_card_ne_zero (by omega)
  have : Fintype k := Fintype.ofFinite k
  have hcard : 2 < (Finset.univ.erase (0 : k)).card := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ]
    rw [← Nat.card_eq_fintype_card]
    omega
  obtain ⟨a, ha, b, hb, c, hc, hab, hac, hbc⟩ := Finset.two_lt_card.1 hcard
  exact ⟨a, b, c, hab, hac, hbc, (Finset.mem_erase.1 ha).1, (Finset.mem_erase.1 hb).1,
    (Finset.mem_erase.1 hc).1⟩

theorem coeff_mem_of_poly (k : Subfield K) (hk : 4 ≤ Nat.card k)
    (W : Submodule k (RootModule .G2 K)) (X : ℕ → Module.End K (RootModule .G2 K))
    (A : K → Module.End K (RootModule .G2 K))
    (hA : ∀ c, A c = ∑ m ∈ Finset.range 4, c ^ m • X m) (hX0 : X 0 = 1)
    (hW : ∀ t : k, ∀ w ∈ W, A (t : K) w ∈ W) {v : RootModule .G2 K} (hv : v ∈ W) :
    X 1 v ∈ W ∧ X 2 v ∈ W ∧ X 3 v ∈ W := by
  obtain ⟨t₁, t₂, t₃, h12, h13, h23, h1, h2, h3⟩ := exists_three_nonzero k hk
  have e : ∀ t : k, (t : K) • X 1 v + (t : K) ^ 2 • X 2 v + (t : K) ^ 3 • X 3 v ∈ W := by
    intro t
    have h := W.sub_mem (hW t v hv) hv
    rw [hA] at h
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, pow_zero, one_smul, hX0,
      pow_one, LinearMap.add_apply, LinearMap.smul_apply, Module.End.one_apply] at h
    convert h using 1
    abel
  exact vand3 W h12 h13 h23 h1 h2 h3 (e t₁) (e t₂) (e t₃)

@[expose] def oddTarget : Col (Tag.rootCertificate .G2) → Option GIdx
  | some (c', z) => if z % 2 = 1 then some c' else none
  | none => none

theorem oddTarget_eq_some {u : Col (Tag.rootCertificate .G2)} {c' : GIdx}
    (h : oddTarget u = some c') : ∃ z : ℤ, u = some (c', z) ∧ z % 2 = 1 := by
  rcases u with _ | ⟨a, z⟩
  · simp [oddTarget] at h
  · simp only [oddTarget] at h
    split_ifs at h with hz
    · cases h
      exact ⟨z, rfl, hz⟩

@[expose] def moveList (c : GIdx) : List GIdx :=
  (List.finRange (Tag.rank .G2)).flatMap fun i => [1, 2, 3].flatMap fun j =>
    (oddTarget (xCol (Tag.rootCertificate .G2) (Tag.stringData .G2) i j c)).toList ++
      (oddTarget (yCol (Tag.rootCertificate .G2) (Tag.stringData .G2) i j c)).toList

@[expose] def longIdx : List GIdx :=
  ((List.finRange (Tag.rootCertificate .G2).roots.length).filter
    fun m => decide (m.val ∈ [0, 2, 3, 6, 7, 10])).map Sum.inr

@[expose] def reachStep (L : List GIdx) : List GIdx := L ++ L.flatMap moveList

@[expose] def reachN : ℕ → List GIdx → List GIdx
  | 0, L => L
  | n + 1, L => reachN n (reachStep L)

@[expose] def reachAll (n : ℕ) : Bool := gIdxList.all fun a => decide (a ∈ reachN n longIdx)

theorem reachAll_three : reachAll 3 = true := by decide +kernel

theorem mem_reachN_three (a : GIdx) : a ∈ reachN 3 longIdx := by
  have h := reachAll_three
  simp only [reachAll, List.all_eq_true, decide_eq_true_eq] at h
  exact h a (mem_gIdxList a)

theorem mem_reachN {P : GIdx → Prop} (hP : ∀ c, P c → ∀ c' ∈ moveList c, P c') :
    ∀ (n : ℕ) (L : List GIdx), (∀ c ∈ L, P c) → ∀ c ∈ reachN n L, P c := by
  intro n
  induction n with
  | zero => intro L hL; exact hL
  | succ n ih =>
    intro L hL
    refine ih (reachStep L) fun c hc => ?_
    simp only [reachStep, List.mem_append, List.mem_flatMap] at hc
    rcases hc with hc | ⟨d, hd, hc⟩
    · exact hL c hc
    · exact hP d (hL d hd) c hc

theorem mem_moveList {c c' : GIdx} :
    c' ∈ moveList c ↔ ∃ i : Fin (Tag.rank .G2), ∃ j ∈ [1, 2, 3],
      oddTarget (xCol (Tag.rootCertificate .G2) (Tag.stringData .G2) i j c) = some c' ∨
      oddTarget (yCol (Tag.rootCertificate .G2) (Tag.stringData .G2) i j c) = some c' := by
  simp only [moveList, List.mem_flatMap, List.mem_finRange, true_and, List.mem_append,
    Option.mem_toList]

section Action


theorem xp0_smul (c : K) (x : RootModule .G2 K) :
    (xp 0 c : adjointGroup .G2 K) • x = xOp .G2 K e0 c x := by
  simp only [xp, rt0_eq, xPar_simple]
  show ((rootOperatorFamily .G2).elt K (simpleRoot .G2 e0) c) x = _
  rw [(rootOperatorFamily .G2).elt_simple]

theorem xp1_smul (c : K) (x : RootModule .G2 K) :
    (xp 1 c : adjointGroup .G2 K) • x = xOp .G2 K e1 c x := by
  simp only [xp, rt1_eq, xPar_simple]
  show ((rootOperatorFamily .G2).elt K (simpleRoot .G2 e1) c) x = _
  rw [(rootOperatorFamily .G2).elt_simple]

theorem xp2_smul (c : K) (x : RootModule .G2 K) :
    (xp 2 c : adjointGroup .G2 K) • x = yOp .G2 K e0 c x := by
  simp only [xp, rt2_eq, xPar_neg_simple]
  show ((rootOperatorFamily .G2).elt K (-simpleRoot .G2 e0) c) x = _
  rw [(rootOperatorFamily .G2).elt_neg_simple]

theorem xp5_smul (c : K) (x : RootModule .G2 K) :
    (xp 5 c : adjointGroup .G2 K) • x = yOp .G2 K e1 c x := by
  simp only [xp, rt5_eq, xPar_neg_simple]
  show ((rootOperatorFamily .G2).elt K (-simpleRoot .G2 e1) c) x = _
  rw [(rootOperatorFamily .G2).elt_neg_simple]

@[expose] def longOrbit (R : Subgroup (adjointGroup .G2 K)) : Set (RootModule .G2 K) :=
  {x | ∃ r ∈ R, ∃ σ ∈ longPos, x = r • rootVec .G2 K (rt σ)}

theorem smul_mem_span (k : Subfield K) {R : Subgroup (adjointGroup .G2 K)}
    {r : adjointGroup .G2 K} (hr : r ∈ R) {w : RootModule .G2 K}
    (hw : w ∈ Submodule.span k (longOrbit R)) : r • w ∈ Submodule.span k (longOrbit R) := by
  induction hw using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨r', hr', σ, hσ, rfl⟩ := hx
    exact Submodule.subset_span ⟨r * r', R.mul_mem hr hr', σ, hσ, (mul_smul r r' _).symm⟩
  | zero => simp
  | add x y _ _ hx hy =>
    rw [smul_add]
    exact add_mem hx hy
  | smul a x _ hx =>
    have : r • (a • x) = a • (r • x) := smul_smul_comm r (a : K) x
    rw [this]
    exact Submodule.smul_mem _ a hx

variable (k : Subfield K) (hk : 4 ≤ Nat.card k)
  {R : Subgroup (adjointGroup .G2 K)} (hR : ∀ p < 12, ∀ c ∈ k, xp p c ∈ R)

include hR in
theorem xOp_mem_span (i : Fin (Tag.rank .G2)) (t : k) {w : RootModule .G2 K}
    (hw : w ∈ Submodule.span k (longOrbit R)) :
    xOp .G2 K i (t : K) w ∈ Submodule.span k (longOrbit R) := by
  have hi : i = e0 ∨ i = e1 := by
    fin_cases i
    · exact .inl rfl
    · exact .inr rfl
  rcases hi with rfl | rfl
  · rw [← xp0_smul]
    exact smul_mem_span k (hR 0 (by norm_num) _ t.2) hw
  · rw [← xp1_smul]
    exact smul_mem_span k (hR 1 (by norm_num) _ t.2) hw

include hR in
theorem yOp_mem_span (i : Fin (Tag.rank .G2)) (t : k) {w : RootModule .G2 K}
    (hw : w ∈ Submodule.span k (longOrbit R)) :
    yOp .G2 K i (t : K) w ∈ Submodule.span k (longOrbit R) := by
  have hi : i = e0 ∨ i = e1 := by
    fin_cases i
    · exact .inl rfl
    · exact .inr rfl
  rcases hi with rfl | rfl
  · rw [← xp2_smul]
    exact smul_mem_span k (hR 2 (by norm_num) _ t.2) hw
  · rw [← xp5_smul]
    exact smul_mem_span k (hR 5 (by norm_num) _ t.2) hw

theorem single_mem_of_odd [CharP K 2] {W : Submodule k (RootModule .G2 K)} {c' : GIdx} {z : ℤ}
    (hz : z % 2 = 1)
    (h : toVec (Tag.rootCertificate_check .G2) K (some (c', z)) ∈ W) :
    Finsupp.single (toLabel (Tag.rootCertificate_check .G2) c') 1 ∈ W := by
  have hz1 : (z : K) = 1 := by
    obtain ⟨q, hq⟩ : ∃ q : ℤ, z = 2 * q + 1 := ⟨z / 2, by omega⟩
    rw [hq]
    push_cast
    rw [show (2 : K) = 0 from CharP.cast_eq_zero K 2, zero_mul, zero_add]
  rwa [toVec_some, hz1, one_smul] at h

include hk hR in
theorem mem_span_move [CharP K 2] {c : GIdx}
    (hc : Finsupp.single (toLabel (Tag.rootCertificate_check .G2) c) 1 ∈
      Submodule.span k (longOrbit R)) :
    ∀ c' ∈ moveList c, Finsupp.single (toLabel (Tag.rootCertificate_check .G2) c') 1 ∈
      Submodule.span k (longOrbit R) := by
  intro c' hc'
  obtain ⟨i, j, hj, h⟩ := mem_moveList.1 hc'
  rcases h with h | h
  · obtain ⟨z, hz, hz2⟩ := oddTarget_eq_some h
    have hcoeff := coeff_mem_of_poly k hk (Submodule.span k (longOrbit R)) (xCoeff .G2 K i)
      (xOp .G2 K i) (fun c => xOp_eq_sum_xCoeff i c) (xCoeff_zero i)
      (fun t w hw => xOp_mem_span k hR i t hw) hc
    refine single_mem_of_odd k hz2 ?_
    rw [← hz, ← xCoeff_toLabel (Tag.rootCertificate_check .G2) K (Tag.stringData_check .G2) i j c]
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
    rcases hj with rfl | rfl | rfl
    · exact hcoeff.1
    · exact hcoeff.2.1
    · exact hcoeff.2.2
  · obtain ⟨z, hz, hz2⟩ := oddTarget_eq_some h
    have hcoeff := coeff_mem_of_poly k hk (Submodule.span k (longOrbit R)) (yCoeff .G2 K i)
      (yOp .G2 K i) (fun c => yOp_eq_sum_yCoeff i c) (yCoeff_zero i)
      (fun t w hw => yOp_mem_span k hR i t hw) hc
    refine single_mem_of_odd k hz2 ?_
    rw [← hz, ← yCoeff_toLabel (Tag.rootCertificate_check .G2) K (Tag.stringData_check .G2) i j c]
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
    rcases hj with rfl | rfl | rfl
    · exact hcoeff.1
    · exact hcoeff.2.1
    · exact hcoeff.2.2

include hk hR in
theorem single_mem_span [CharP K 2] (b : Label .G2) :
    Finsupp.single b 1 ∈ Submodule.span k (longOrbit R) := by
  obtain ⟨c, rfl⟩ := surjective_toLabel (Tag.rootCertificate_check .G2) b
  refine mem_reachN (P := fun c => Finsupp.single (toLabel (Tag.rootCertificate_check .G2) c) 1 ∈
      Submodule.span k (longOrbit R)) (fun c hc c' hc' => mem_span_move k hk hR hc c' hc')
    3 longIdx ?_ c (mem_reachN_three c)
  intro c hc
  simp only [longIdx, List.mem_map, List.mem_filter, List.mem_finRange, true_and,
    decide_eq_true_eq] at hc
  obtain ⟨m, hm, rfl⟩ := hc
  rw [single_toLabel_inr]
  refine Submodule.subset_span ⟨1, R.one_mem, m.val, ?_, by rw [one_smul]⟩
  simp only [longPos, Finset.mem_insert, Finset.mem_singleton]
  simpa using hm

include hk hR in
theorem rootVec_mem_span [CharP K 2] (γ : Fin (Tag.rank .G2) → ℤ) (hγ : IsRoot .G2 γ) :
    rootVec .G2 K γ ∈ Submodule.span k (longOrbit R) := by
  rw [rootVec_eq_single K hγ]
  exact single_mem_span k hk hR _

include hk hR in
theorem hVec_mem_span [CharP K 2] (i : Fin (Tag.rank .G2)) :
    hVec .G2 K i ∈ Submodule.span k (longOrbit R) :=
  single_mem_span k hk hR (Sum.inl i)

end Action

end CFSG.RankThree.PartOne.SEITZ6
