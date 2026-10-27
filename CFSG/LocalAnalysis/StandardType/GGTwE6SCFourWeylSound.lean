module

public import CFSG.HardMathSupport.Timmesfeld.CrossChar.E6ThreeSc
public import CFSG.LieType.SeitzGeneration.ExcWideThree.TwE6Order3Core
public import CFSG.LocalAnalysis.StandardType.GGTwE6SCFourWeylRank
public import CFSG.LieType.SeitzGeneration.ExcWideThree.TwE6Order3Defs

public section

namespace CFSG.StandardType.SCFourCover

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.HardMathSupport.Timmesfeld.Steinberg
  CFSG.HardMathSupport.Timmesfeld.CrossChar WeylFix
open CFSG.LieType.SeitzGeneration.ExcWideThree.E6Order3 (exists_root72 reflIdx reflIdx_spec len72
  isRoot_root72)

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

private theorem exists_of_allPairs {α β : Type} {p : α → β → Bool} :
    ∀ {l₁ : List α} {l₂ : List β}, allPairs p l₁ l₂ = true → ∀ {a : α}, a ∈ l₁ →
      ∃ b ∈ l₂, p a b = true
  | [], [], _, _, ha => absurd ha List.not_mem_nil
  | x :: xs, y :: ys, h, a, ha => by
    simp only [allPairs, Bool.and_eq_true] at h
    rcases List.mem_cons.1 ha with rfl | ha
    · exact ⟨y, List.mem_cons.2 (Or.inl rfl), h.1⟩
    · obtain ⟨b, hb, hab⟩ := exists_of_allPairs h.2 ha
      exact ⟨b, List.mem_cons_of_mem _ hb, hab⟩
  | [], _ :: _, h, _, _ => by simp [allPairs] at h
  | _ :: _, [], h, _, _ => by simp [allPairs] at h

private theorem searchOK_at {a0 : ℕ} (ha0 : a0 < 72) :
    allPairs entryOK (leavesFrom a0) (entriesAt.getD a0 []) = true := by
  have e : ∀ l₁ l₂ : List ℕ, searchOK (l₁ ++ l₂) = (searchOK l₁ && searchOK l₂) :=
    fun _ _ => List.all_append
  have h : searchOK (List.range 72) = true := by
    rw [show List.range 72 = List.range' 0 18 ++ List.range' 18 18 ++ List.range' 36 18 ++
      List.range' 54 18 by decide, e, e, e, searchOK_0, searchOK_1, searchOK_2, searchOK_3]
    rfl
  exact List.all_eq_true.1 h a0 (List.mem_range.2 ha0)

private theorem mem_leavesFrom {G : ℕ × ℕ → Prop} {a0 a1 a2 a3 a4 a5 : ℕ}
    (h2 : a2 ∈ adjRoots.getD a0 []) (h3 : a3 ∈ adjRoots.getD a2 [])
    (h4 : a4 ∈ adjRoots.getD a3 []) (h5 : a5 ∈ adjRoots.getD a4 [])
    (h1 : a1 ∈ adjRoots.getD a3 [])
    (o30 : orthB a3 a0 = true) (o40 : orthB a4 a0 = true) (o42 : orthB a4 a2 = true)
    (o50 : orthB a5 a0 = true) (o52 : orthB a5 a2 = true) (o53 : orthB a5 a3 = true)
    (o10 : orthB a1 a0 = true) (o12 : orthB a1 a2 = true) (o14 : orthB a1 a4 = true)
    (o15 : orthB a1 a5 = true)
    (hp : ∀ olds v, (∀ p ∈ olds, G p) → G v → prune olds v = false)
    (g0 : G (0, a0)) (g1 : G (1, a1)) (g2 : G (2, a2)) (g3 : G (3, a3)) (g4 : G (4, a4))
    (g5 : G (5, a5)) (hw : wTest [a0, a1, a2, a3, a4, a5] = true) :
    [a0, a1, a2, a3, a4, a5] ∈ leavesFrom a0 := by
  have p3 := hp [(0, a0), (2, a2)] (3, a3) (by simp [g0, g2]) g3
  have p4 := hp [(0, a0), (2, a2), (3, a3)] (4, a4) (by simp [g0, g2, g3]) g4
  have p5 := hp [(0, a0), (2, a2), (3, a3), (4, a4)] (5, a5) (by simp [g0, g2, g3, g4]) g5
  have p1 := hp [(0, a0), (2, a2), (3, a3), (4, a4), (5, a5)] (1, a1)
    (by simp [g0, g2, g3, g4, g5]) g1
  simp only [leavesFrom, List.mem_flatMap]
  refine ⟨a2, h2, a3, h3, ?_⟩
  simp only [o30, p3, Bool.not_false, Bool.and_self, cond_true, List.mem_flatMap]
  refine ⟨a4, h4, ?_⟩
  simp only [o40, o42, p4, Bool.not_false, Bool.and_self, cond_true, List.mem_flatMap]
  refine ⟨a5, h5, ?_⟩
  simp only [o50, o52, o53, p5, Bool.not_false, Bool.and_self, cond_true, List.mem_flatMap]
  refine ⟨a1, h1, ?_⟩
  simp only [o10, o12, o14, o15, p1, hw, Bool.not_false, Bool.and_self, cond_true]
  exact List.mem_singleton.2 rfl

private theorem getD_tuple (f : Fin Tag.E6.rank → ℕ) (j : Fin Tag.E6.rank) :
    [f 0, f 1, f 2, f 3, f 4, f 5].getD j 0 = f j := by
  obtain ⟨j, hj⟩ := j
  have hj' : j < 6 := hj
  interval_cases j <;> rfl

private theorem sum_six {M : Type*} [AddCommMonoid M] (g : Fin Tag.E6.rank → M) :
    ∑ j, g j = g 0 + g 1 + g 2 + g 3 + g 4 + g 5 :=
  Fin.sum_univ_six g


private theorem represents_tupleOf : ∀ {rs : List ℕ}, (∀ b ∈ rs, b < 72) →
    e6Certificate.Represents (tupleOf rs)
      (rs.map fun b => rootReflection (e6Certificate.root b)).prod
  | [], _ => RootCertificate.represents_one e6Certificate_check
  | b :: rs, h => by
    have ih := represents_tupleOf fun b' hb' => h b' (List.mem_cons_of_mem _ hb')
    have hb : b < 72 := h b (List.mem_cons.2 (Or.inl rfl))
    have e : tupleOf (b :: rs) = (tupleOf rs).map (reflIdx 72 b) := rfl
    rw [e, List.map_cons, List.prod_cons]
    refine ⟨by rw [List.length_map, ih.1], fun j => ?_⟩
    have hj : (j : ℕ) < (tupleOf rs).length := by rw [ih.1]; exact j.2
    rw [List.getD_eq_getElem _ _ (by rw [List.length_map]; exact hj), List.getElem_map,
      ← List.getD_eq_getElem _ 0 hj]
    have hc := ih.2 j
    obtain ⟨h1, h2⟩ := reflIdx_spec 72 b hb hb _ (len72 ▸ hc.1)
    refine ⟨len72.symm ▸ h1, ?_⟩
    rw [h2, hc.2, mul_smul]

variable {u : WeylGroup Tag.E6} {f : Fin Tag.E6.rank → ℕ}

private theorem represents_tuple (hf72 : ∀ j, f j < 72)
    (hf : ∀ j, e6Certificate.root (f j) = u • Pi.single j 1) :
    e6Certificate.Represents [f 0, f 1, f 2, f 3, f 4, f 5] u :=
  ⟨rfl, fun j => by rw [getD_tuple, len72]; exact ⟨hf72 j, hf j⟩⟩

private theorem wTest_tuple (hf72 : ∀ j, f j < 72)
    (hf : ∀ j, e6Certificate.root (f j) = u • Pi.single j 1) :
    wTest [f 0, f 1, f 2, f 3, f 4, f 5] = true := by
  have e : wTest [f 0, f 1, f 2, f 3, f 4, f 5] = (List.range 6).all fun i =>
      (r3 (f 0) i + 2 * r3 (f 2) i + r3 (f 4) i + 2 * r3 (f 5) i) % 3 ==
        [1, 0, 2, 0, 1, 2].getD i 0 := rfl
  rw [e, List.all_eq_true]
  intro i hi
  rw [List.mem_range] at hi
  obtain ⟨k, rfl⟩ : ∃ k : Fin Tag.E6.rank, (k : ℕ) = i := ⟨⟨i, hi⟩, rfl⟩
  have h3 : (3 : ZMod 3) = 0 := by decide
  have hv : (u • e6Omega3) k =
      ∑ j : Fin Tag.E6.rank, e6Omega3 j * e6Certificate.root (f j) k := by
    rw [← RootCertificate.tupleVec_eq (represents_tuple hf72 hf), RootCertificate.tupleVec,
      Finset.sum_apply]
    exact Finset.sum_congr rfl fun j _ => by rw [getD_tuple]; rfl
  have hd := (ZMod.intCast_zmod_eq_zero_iff_dvd _ 3).2 (three_dvd_smul_e6Omega3_sub u k)
  have hE : e6Omega3 0 = 4 ∧ e6Omega3 1 = 3 ∧ e6Omega3 2 = 5 ∧ e6Omega3 3 = 6 ∧
      e6Omega3 4 = 4 ∧ e6Omega3 5 = 2 := by decide
  obtain ⟨e0, e1, e2, e3, e4, e5⟩ := hE
  rw [hv, sum_six, e0, e1, e2, e3, e4, e5] at hd
  push_cast at hd
  have hY : ∀ k : Fin Tag.E6.rank,
      (([1, 0, 2, 0, 1, 2].getD k 0 : ℕ) : ZMod 3) = ((e6Omega3 k : ℤ) : ZMod 3) := by decide
  have hY3 : ∀ k : Fin Tag.E6.rank, [1, 0, 2, 0, 1, 2].getD k 0 < 3 := by decide
  rw [beq_iff_eq, ← Nat.mod_eq_of_lt (hY3 k), ← ZMod.natCast_eq_natCast_iff', hY k]
  push_cast
  rw [r3_cast (hf72 0) k, r3_cast (hf72 2) k, r3_cast (hf72 4) k, r3_cast (hf72 5) k]
  linear_combination hd + (-((e6Certificate.root (f 0) k : ℤ) : ZMod 3) -
    ((e6Certificate.root (f 1) k : ℤ) : ZMod 3) - ((e6Certificate.root (f 2) k : ℤ) : ZMod 3) -
    2 * ((e6Certificate.root (f 3) k : ℤ) : ZMod 3) -
    ((e6Certificate.root (f 4) k : ℤ) : ZMod 3)) * h3

theorem mem_closure_rootReflection_of_card_fix {V : Finset (Fin Tag.E6.rank → ZMod 3)}
    (hV : 81 ≤ V.card) (hu : ∀ b ∈ V, ∀ v, triPairing b (u • v) = triPairing b v) :
    u ∈ Subgroup.closure
      (rootReflection '' {α | IsRoot Tag.E6 α ∧ ∀ b ∈ V, triPairing b α = 0}) := by
  choose f hf72 hf using fun j : Fin Tag.E6.rank =>
    exists_root72 (IsRoot.smul (isRoot_single Tag.E6 j) u)
  have ho : ∀ j : Fin Tag.E6.rank, OrthRow V j (f j) := fun j => orthRow_of_fix hu (hf72 j) (hf j)
  have hmem := mem_leavesFrom (G := fun p => OrthRow V p.1 p.2)
    (mem_adjRoots_of_cartan hf72 hf (i := 0) (j := 2) (by decide))
    (mem_adjRoots_of_cartan hf72 hf (i := 2) (j := 3) (by decide))
    (mem_adjRoots_of_cartan hf72 hf (i := 3) (j := 4) (by decide))
    (mem_adjRoots_of_cartan hf72 hf (i := 4) (j := 5) (by decide))
    (mem_adjRoots_of_cartan hf72 hf (i := 3) (j := 1) (by decide))
    (orthB_of_cartan hf72 hf (i := 3) (j := 0) (by decide))
    (orthB_of_cartan hf72 hf (i := 4) (j := 0) (by decide))
    (orthB_of_cartan hf72 hf (i := 4) (j := 2) (by decide))
    (orthB_of_cartan hf72 hf (i := 5) (j := 0) (by decide))
    (orthB_of_cartan hf72 hf (i := 5) (j := 2) (by decide))
    (orthB_of_cartan hf72 hf (i := 5) (j := 3) (by decide))
    (orthB_of_cartan hf72 hf (i := 1) (j := 0) (by decide))
    (orthB_of_cartan hf72 hf (i := 1) (j := 2) (by decide))
    (orthB_of_cartan hf72 hf (i := 1) (j := 4) (by decide))
    (orthB_of_cartan hf72 hf (i := 1) (j := 5) (by decide))
    (fun olds v ho hv => prune_eq_false_of_card (by omega) ho hv)
    (ho 0) (ho 1) (ho 2) (ho 3) (ho 4) (ho 5) (wTest_tuple hf72 hf)
  obtain ⟨e, -, hok⟩ := exists_of_allPairs (searchOK_at (hf72 0)) hmem
  simp only [entryOK, Bool.and_eq_true, beq_iff_eq, List.all_eq_true, decide_eq_true_eq] at hok
  obtain ⟨htup, hall⟩ := hok
  have hrep := represents_tupleOf (rs := e.map Prod.fst) fun b hb => by
    obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hb
    exact (hall p hp).1
  rw [htup] at hrep
  rw [RootCertificate.represents_unique (represents_tuple hf72 hf) hrep]
  refine Subgroup.list_prod_mem _ fun x hx => ?_
  obtain ⟨a, ha, rfl⟩ := List.mem_map.1 hx
  obtain ⟨p, hp, rfl⟩ := List.mem_map.1 ha
  refine Subgroup.subset_closure ⟨e6Certificate.root p.1, ⟨isRoot_root72 (hall p hp).1, ?_⟩, rfl⟩
  refine triPairing_eq_zero_of_coefOK (fun j hj => ?_) (hall p hp).1 (hall p hp).2
  have h := ho ⟨j, hj⟩
  rwa [← getD_tuple f ⟨j, hj⟩] at h

end CFSG.StandardType.SCFourCover

end
