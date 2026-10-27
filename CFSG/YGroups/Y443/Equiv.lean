module

public import CFSG.YGroups.Y443.Basic
public import CFSG.YGroups.Bound
public import Mathlib.Algebra.Order.Ring.Star

public section

namespace CFSG.YGroups

open CFSG.Open (MonsterY443 MonsterY443Gen MonsterY443Adj monsterY443Rels monsterY443ArmLength
  monsterY443SpiderWord)
open CFSG.Certificates.CosetEnumeration (evalWord evalWord_nil evalWord_cons evalWord_append)

namespace Y443

theorem evalWord_replicate_flatten {G : Type*} [Group G] (g : ℕ → G) (w : List ℕ) (n : ℕ) :
    evalWord g (List.replicate n w).flatten = (evalWord g w) ^ n := by
  induction n with
  | zero => simp
  | succ n ih => rw [List.replicate_succ, List.flatten_cons, evalWord_append, ih, pow_succ']

theorem evalWord_pair {G : Type*} [Group G] (g : ℕ → G) (s t m : ℕ) :
    evalWord g (List.replicate m [s, t]).flatten = (g s * g t) ^ m := by
  rw [evalWord_replicate_flatten, evalWord_cons, evalWord_cons, evalWord_nil, mul_one]

theorem pairWord_mem_yRels {p q r s t : ℕ} (hst : s < t) (ht : t < ngen p q r) :
    pairWord p q r s t ∈ yRels p q r := by
  simp only [yRels, List.mem_append, List.mem_map, List.mem_range, List.mem_flatMap,
    List.mem_filter]
  exact Or.inl (Or.inr ⟨s, by omega, t, ⟨ht, by simpa using hst⟩, rfl⟩)

theorem yGen_pair_pow {p q r s t : ℕ} (hst : s < t) (ht : t < ngen p q r) :
    (yGen p q r s * yGen p q r t) ^ pairExp p q r s t = 1 := by
  have h := evalWord_yGen_of_mem (pairWord_mem_yRels hst ht)
  rwa [pairWord, evalWord_pair] at h

theorem pow_eq_one_of_swap {G : Type*} [Group G] {x y : G} (hx : x * x = 1) (hy : y * y = 1)
    {m : ℕ} (h : (y * x) ^ m = 1) : (x * y) ^ m = 1 := by
  have h1 : x * y = (y * x)⁻¹ := by
    rw [mul_inv_rev, inv_eq_of_mul_eq_one_right hx, inv_eq_of_mul_eq_one_right hy]
  rw [h1, inv_pow, h, inv_one]

@[expose] noncomputable def letterImage (c : ℕ) : MonsterY443 :=
  PresentedGroup.of (y443GenOfLetter c)

theorem spider_eval :
    evalWord letterImage (spiderWord 4 4) =
      PresentedGroup.mk monsterY443Rels monsterY443SpiderWord := by
  simp only [spiderWord, evalWord_cons, evalWord_nil, mul_one, monsterY443SpiderWord,
    CFSG.Open.monsterY443Node, map_mul, mul_assoc]
  rfl

theorem rels_letterImage : ∀ w ∈ yRels 4 4 3, evalWord letterImage w = 1 := by
  intro w hw
  simp only [yRels, List.mem_append, List.mem_map, List.mem_range, List.mem_flatMap,
    List.mem_filter] at hw
  rcases hw with (⟨s, hs, rfl⟩ | ⟨s, hs, t, ⟨ht, hst⟩, rfl⟩) | hsp
  · rw [evalWord_cons, evalWord_cons, evalWord_nil, mul_one]
    exact gen_mul_self _
  · have hs' : s < 12 := hs
    have ht' : t < 12 := ht
    have hst' : s < t := by simpa using hst
    rw [pairWord, evalWord_pair]
    by_cases hedge : (s, t) ∈ yEdges 4 4 3
    · have hpe : pairExp 4 4 3 s t = 3 := by simp [pairExp, hedge]
      rw [hpe]
      exact gen_pair_adj ((y443Adj_iff_edge hs' ht' hst').2 hedge)
    · have hpe : pairExp 4 4 3 s t = 2 := by simp [pairExp, hedge]
      rw [hpe]
      refine gen_pair_nonadj ?_ (fun h => hedge ((y443Adj_iff_edge hs' ht' hst').1 h))
      intro heq
      have := congrArg y443LetterOfGen heq
      rw [y443LetterOfGen_genOfLetter s hs', y443LetterOfGen_genOfLetter t ht'] at this
      omega
  · split_ifs at hsp with hpqr
    · simp only [List.mem_cons, List.mem_nil_iff, or_false] at hsp
      subst hsp
      rw [evalWord_replicate_flatten, spider_eval]
      exact Y443.spider_pow
    · simp at hsp

noncomputable def toOpen : YGroup 4 4 3 →* MonsterY443 :=
  PresentedGroup.toGroup (f := fun c : Fin (ngen 4 4 3) => letterImage c) (by
    rintro x ⟨w, hw, rfl⟩
    rw [lift_wordFG, evalWord_congr (g' := letterImage)]
    · exact rels_letterImage w hw
    · intro c hc
      simp [lt_ngen_of_mem_yRels hw c hc])

theorem toOpen_yGen {c : ℕ} (hc : c < 12) :
    toOpen (yGen 4 4 3 c) = PresentedGroup.of (y443GenOfLetter c) := by
  rw [yGen_of_lt (show c < ngen 4 4 3 from hc), toOpen, PresentedGroup.toGroup.of]
  rfl

theorem lift_pair {s t : MonsterY443Gen} (hst : s ≠ t) (m : ℕ)
    (hm : ∀ a b : ℕ, a < b → b < 12 → (a = y443LetterOfGen s ∧ b = y443LetterOfGen t ∨
      a = y443LetterOfGen t ∧ b = y443LetterOfGen s) → pairExp 4 4 3 a b = m) :
    (yGen 4 4 3 (y443LetterOfGen s) * yGen 4 4 3 (y443LetterOfGen t)) ^ m = 1 := by
  have hs := y443LetterOfGen_lt s
  have ht := y443LetterOfGen_lt t
  have hne : y443LetterOfGen s ≠ y443LetterOfGen t := by
    intro h
    exact hst (by
      have := congrArg y443GenOfLetter h
      rwa [y443GenOfLetter_letterOfGen, y443GenOfLetter_letterOfGen] at this)
  rcases lt_or_gt_of_ne hne with h | h
  · rw [← hm _ _ h ht (Or.inl ⟨rfl, rfl⟩)]
    exact yGen_pair_pow h (show _ < ngen 4 4 3 from ht)
  · have h1 := yGen_pair_pow (p := 4) (q := 4) (r := 3) h (show _ < ngen 4 4 3 from hs)
    rw [hm _ _ h hs (Or.inr ⟨rfl, rfl⟩)] at h1
    exact pow_eq_one_of_swap (yGen_mul_self _ _ _ _) (yGen_mul_self _ _ _ _) h1

theorem spider_lift :
    FreeGroup.lift (fun g => yGen 4 4 3 (y443LetterOfGen g)) monsterY443SpiderWord =
      evalWord (yGen 4 4 3) (spiderWord 4 4) := by
  simp only [spiderWord, evalWord_cons, evalWord_nil, mul_one, monsterY443SpiderWord,
    CFSG.Open.monsterY443Node, map_mul, FreeGroup.lift_apply_of, mul_assoc]
  rfl

theorem rels_yGen : ∀ r ∈ monsterY443Rels,
    FreeGroup.lift (fun g => yGen 4 4 3 (y443LetterOfGen g)) r = 1 := by
  rintro r (((⟨s, rfl⟩ | ⟨s, t, hadj, rfl⟩) | ⟨s, t, hne, hnadj, rfl⟩) | rfl)
  · rw [map_pow, FreeGroup.lift_apply_of, pow_two]
    exact yGen_mul_self _ _ _ _
  · rw [map_pow, map_mul, FreeGroup.lift_apply_of, FreeGroup.lift_apply_of]
    refine lift_pair (fun h => ?_) 3 ?_
    · subst h
      exact not_adj_self _ hadj
    · intro a b hab hb hmem
      have key : ∀ a b : ℕ, a < b → b < 12 → (a, b) ∈ yEdges 4 4 3 → pairExp 4 4 3 a b = 3 :=
        fun a b _ _ he => by simp [pairExp, he]
      have hedge : ∀ x y : MonsterY443Gen, MonsterY443Adj x y →
          y443LetterOfGen x < y443LetterOfGen y → (y443LetterOfGen x, y443LetterOfGen y) ∈
            yEdges 4 4 3 := by
        intro x y hxy hlt
        have h := (y443Adj_iff_edge (y443LetterOfGen_lt x) (y443LetterOfGen_lt y) hlt).1
        rw [y443GenOfLetter_letterOfGen, y443GenOfLetter_letterOfGen] at h
        exact h hxy
      rcases hmem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact key _ _ hab hb (hedge s t hadj hab)
      · exact key _ _ hab hb (hedge t s (adj_symm hadj) hab)
  · rw [map_pow, map_mul, FreeGroup.lift_apply_of, FreeGroup.lift_apply_of]
    refine lift_pair hne 2 ?_
    intro a b hab hb hmem
    have key : ∀ a b : ℕ, a < b → b < 12 → (a, b) ∉ yEdges 4 4 3 → pairExp 4 4 3 a b = 2 :=
      fun a b _ _ he => by simp [pairExp, he]
    have hedge : ∀ x y : MonsterY443Gen, ¬ MonsterY443Adj x y →
        y443LetterOfGen x < y443LetterOfGen y → (y443LetterOfGen x, y443LetterOfGen y) ∉
          yEdges 4 4 3 := by
      intro x y hxy hlt hmem'
      have := (y443Adj_iff_edge (y443LetterOfGen_lt x) (y443LetterOfGen_lt y) hlt).2 hmem'
      rw [y443GenOfLetter_letterOfGen, y443GenOfLetter_letterOfGen] at this
      exact hxy this
    rcases hmem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact key _ _ hab hb (hedge s t hnadj hab)
    · exact key _ _ hab hb (hedge t s (fun h => hnadj (adj_symm h)) hab)
  · rw [map_pow, spider_lift]
    have h := evalWord_yGen_of_mem (p := 4) (q := 4) (r := 3)
      (w := (List.replicate 10 (spiderWord 4 4)).flatten) (by
        simp only [yRels, List.mem_append]
        refine Or.inr ?_
        simp)
    rwa [evalWord_replicate_flatten] at h

noncomputable def ofOpen : MonsterY443 →* YGroup 4 4 3 :=
  PresentedGroup.toGroup (f := fun g => yGen 4 4 3 (y443LetterOfGen g)) rels_yGen

theorem ofOpen_of (g : MonsterY443Gen) :
    ofOpen (PresentedGroup.of g) = yGen 4 4 3 (y443LetterOfGen g) := by
  rw [ofOpen, PresentedGroup.toGroup.of]

end Y443

noncomputable def y443EquivOpen : YGroup 4 4 3 ≃* MonsterY443 :=
  MonoidHom.toMulEquiv Y443.toOpen Y443.ofOpen
    (by
      refine PresentedGroup.ext fun c => ?_
      have hc : (c : ℕ) < 12 := c.2
      rw [MonoidHom.comp_apply, MonoidHom.id_apply]
      have h1 : Y443.toOpen (PresentedGroup.of c) = PresentedGroup.of (y443GenOfLetter c) := by
        rw [← yGen_of_lt c.2]
        exact Y443.toOpen_yGen hc
      rw [h1, Y443.ofOpen_of, y443LetterOfGen_genOfLetter c hc]
      exact yGen_of_lt c.2)
    (by
      refine PresentedGroup.ext fun g => ?_
      rw [MonoidHom.comp_apply, MonoidHom.id_apply, Y443.ofOpen_of,
        Y443.toOpen_yGen (y443LetterOfGen_lt g), y443GenOfLetter_letterOfGen])

@[simp] theorem y443EquivOpen_yGen {c : ℕ} (hc : c < 12) :
    y443EquivOpen (yGen 4 4 3 c) = PresentedGroup.of (y443GenOfLetter c) :=
  Y443.toOpen_yGen hc

@[simp] theorem y443EquivOpen_symm_of (g : MonsterY443Gen) :
    y443EquivOpen.symm (PresentedGroup.of g) = yGen 4 4 3 (y443LetterOfGen g) :=
  Y443.ofOpen_of g

theorem y443EquivOpen_yGen_zero :
    y443EquivOpen (yGen 4 4 3 0) = PresentedGroup.of (none : MonsterY443Gen) :=
  y443EquivOpen_yGen (by norm_num)

theorem y443EquivOpen_yGen_node (i : Fin 3) (j : Fin (monsterY443ArmLength i)) :
    y443EquivOpen (yGen 4 4 3 (1 + y443ArmOffset i + j)) = PresentedGroup.of (some ⟨i, j⟩) := by
  have h := y443EquivOpen_yGen (c := y443LetterOfGen (some ⟨i, j⟩))
    (y443LetterOfGen_lt _)
  rw [y443GenOfLetter_letterOfGen] at h
  exact h

end CFSG.YGroups
