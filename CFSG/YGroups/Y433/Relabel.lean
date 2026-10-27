module

public import CFSG.YGroups.Exact.Model
public import CFSG.YGroups.Y443.Equiv

public section

namespace CFSG.YGroups

namespace Relabel

open CFSG.Certificates.CosetEnumeration (evalWord evalWord_nil evalWord_cons)

theorem map_evalWord {G H : Type*} [Group G] [Group H] (φ : G →* H) (g : ℕ → G) (w : List ℕ) :
    φ (evalWord g w) = evalWord (fun c => φ (g c)) w := by
  induction w with
  | nil => simp
  | cons c w ih => rw [evalWord_cons, map_mul, ih, evalWord_cons]

theorem evalWord_spiderWord {G : Type*} [Group G] (g : ℕ → G) (p q : ℕ) :
    evalWord g (spiderWord p q) =
      (g 0 * g 1 * g 2) * (g 0 * g (1 + p) * g (2 + p)) *
        (g 0 * g (1 + p + q) * g (2 + p + q)) := by
  simp only [spiderWord, evalWord_cons, evalWord_nil, mul_one, mul_assoc]

theorem pow_eq_one_rotate {G : Type*} [Group G] {x y z : G} {n : ℕ} (h : (x * y * z) ^ n = 1) :
    (y * z * x) ^ n = 1 := by
  have e : y * z * x = x⁻¹ * (x * y * z) * x := by group
  have := conj_pow (a := x⁻¹) (b := x * y * z) (i := n)
  rw [inv_inv] at this
  rw [e, this, h]
  group

theorem evalWord_yRels_eq_one {G : Type*} [Group G] {p q r : ℕ} (g : ℕ → G)
    (hsq : ∀ s, s < ngen p q r → g s * g s = 1)
    (hpair : ∀ t, t < ngen p q r → ∀ s, s < t → (g s * g t) ^ pairExp p q r s t = 1)
    (hspider : 2 ≤ p → 2 ≤ q → 2 ≤ r → evalWord g (spiderWord p q) ^ 10 = 1) :
    ∀ w ∈ yRels p q r, evalWord g w = 1 := by
  intro w hw
  simp only [yRels, List.mem_append, List.mem_map, List.mem_range, List.mem_flatMap,
    List.mem_filter] at hw
  rcases hw with (⟨s, hs, rfl⟩ | ⟨s, hs, t, ⟨ht, hst⟩, rfl⟩) | hsp
  · rw [evalWord_cons, evalWord_cons, evalWord_nil, mul_one]
    exact hsq s hs
  · rw [pairWord, Y443.evalWord_pair]
    exact hpair t ht s (by simpa using hst)
  · split_ifs at hsp with h
    · simp only [List.mem_cons, List.mem_nil_iff, or_false] at hsp
      subst hsp
      rw [Y443.evalWord_replicate_flatten]
      exact hspider h.1 h.2.1 h.2.2
    · simp at hsp

theorem yModelHom_evalWord {p q r : ℕ} {H : Type*} [Group H] {img : ℕ → H}
    {h : ∀ w ∈ yRels p q r, evalWord img w = 1} (w : List ℕ) (hw : ∀ c ∈ w, c < ngen p q r) :
    yModelHom img h (evalWord (yGen p q r) w) = evalWord img w := by
  rw [map_evalWord]
  exact evalWord_congr fun c hc => yModelHom_yGen (hw c hc)

@[expose] def PairsPreserved (p q r p' q' r' : ℕ) (m : ℕ → ℕ) : Prop :=
  ∀ t, t < ngen p q r → ∀ s, s < t →
    (m s < m t ∧ m t < ngen p' q' r' ∧ pairExp p' q' r' (m s) (m t) = pairExp p q r s t) ∨
    (m t < m s ∧ m s < ngen p' q' r' ∧ pairExp p' q' r' (m t) (m s) = pairExp p q r s t)

instance (p q r p' q' r' : ℕ) (m : ℕ → ℕ) : Decidable (PairsPreserved p q r p' q' r' m) := by
  unfold PairsPreserved
  infer_instance

theorem yGen_pair_pow_of_preserved {p q r p' q' r' : ℕ} {m : ℕ → ℕ}
    (hm : PairsPreserved p q r p' q' r' m) {s t : ℕ} (ht : t < ngen p q r) (hst : s < t) :
    (yGen p' q' r' (m s) * yGen p' q' r' (m t)) ^ pairExp p q r s t = 1 := by
  rcases hm t ht s hst with ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩
  · rw [← h3]
    exact Y443.yGen_pair_pow h1 h2
  · rw [← h3]
    exact Y443.pow_eq_one_of_swap (yGen_mul_self _ _ _ _) (yGen_mul_self _ _ _ _)
      (Y443.yGen_pair_pow h1 h2)

noncomputable def hom {p q r p' q' r' : ℕ} (m : ℕ → ℕ) (hm : PairsPreserved p q r p' q' r' m)
    (hspider : 2 ≤ p → 2 ≤ q → 2 ≤ r →
      evalWord (fun c => yGen p' q' r' (m c)) (spiderWord p q) ^ 10 = 1) :
    YGroup p q r →* YGroup p' q' r' :=
  yModelHom (fun c => yGen p' q' r' (m c))
    (evalWord_yRels_eq_one _ (fun _ _ => yGen_mul_self _ _ _ _)
      (fun _ ht _ hs => yGen_pair_pow_of_preserved hm ht hs) hspider)

theorem hom_yGen {p q r p' q' r' : ℕ} {m : ℕ → ℕ} {hm : PairsPreserved p q r p' q' r' m}
    {hspider : 2 ≤ p → 2 ≤ q → 2 ≤ r →
      evalWord (fun c => yGen p' q' r' (m c)) (spiderWord p q) ^ 10 = 1} {c : ℕ}
    (hc : c < ngen p q r) : hom m hm hspider (yGen p q r c) = yGen p' q' r' (m c) :=
  yModelHom_yGen hc

theorem hom_evalWord {p q r p' q' r' : ℕ} {m : ℕ → ℕ} {hm : PairsPreserved p q r p' q' r' m}
    {hspider : 2 ≤ p → 2 ≤ q → 2 ≤ r →
      evalWord (fun c => yGen p' q' r' (m c)) (spiderWord p q) ^ 10 = 1} (w : List ℕ)
    (hw : ∀ c ∈ w, c < ngen p q r) :
    hom m hm hspider (evalWord (yGen p q r) w) = evalWord (fun c => yGen p' q' r' (m c)) w :=
  yModelHom_evalWord w hw

theorem commute_yGen_of_not_edge {p q r s t : ℕ} (hs : s < ngen p q r) (ht : t < ngen p q r)
    (hne : s ≠ t) (h1 : (s, t) ∉ yEdges p q r) (h2 : (t, s) ∉ yEdges p q r) :
    Commute (yGen p q r s) (yGen p q r t) := by
  rcases lt_or_gt_of_ne hne with hst | hts
  · have hp := Y443.yGen_pair_pow (p := p) (q := q) (r := r) hst ht
    rw [show pairExp p q r s t = 2 by simp [pairExp, h1]] at hp
    exact Y443.commute_of_sq_eq_one (yGen_mul_self _ _ _ _) (yGen_mul_self _ _ _ _) hp
  · have hp := Y443.yGen_pair_pow (p := p) (q := q) (r := r) hts hs
    rw [show pairExp p q r t s = 2 by simp [pairExp, h2]] at hp
    exact (Y443.commute_of_sq_eq_one (yGen_mul_self _ _ _ _) (yGen_mul_self _ _ _ _) hp).symm

theorem commute_yGen_evalWord {p q r s : ℕ} {w : List ℕ} (hs : s < ngen p q r)
    (h : ∀ c ∈ w, c < ngen p q r ∧ c ≠ s ∧ (s, c) ∉ yEdges p q r ∧ (c, s) ∉ yEdges p q r) :
    Commute (yGen p q r s) (evalWord (yGen p q r) w) := by
  unfold evalWord
  refine Commute.list_prod_right _ _ ?_
  intro x hx
  obtain ⟨c, hc, rfl⟩ := List.mem_map.1 hx
  obtain ⟨h1, h2, h3, h4⟩ := h c hc
  exact commute_yGen_of_not_edge hs h1 (Ne.symm h2) h3 h4

theorem mem_center_of_commute_yGen {p q r : ℕ} {x : YGroup p q r}
    (h : ∀ c, c < ngen p q r → yGen p q r c * x = x * yGen p q r c) :
    x ∈ Subgroup.center (YGroup p q r) := by
  rw [Subgroup.mem_center_iff]
  have hle : Subgroup.closure (yGen p q r '' Set.Iio (ngen p q r)) ≤
      Subgroup.centralizer {x} := by
    rw [Subgroup.closure_le]
    rintro _ ⟨c, hc, rfl⟩
    rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff]
    exact h c hc
  intro g
  have hg : g ∈ Subgroup.closure (yGen p q r '' Set.Iio (ngen p q r)) := by
    rw [closure_yGen]
    trivial
  exact Subgroup.mem_centralizer_singleton_iff.1 (hle hg)

end Relabel

end CFSG.YGroups
