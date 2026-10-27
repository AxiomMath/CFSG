module

public import CFSG.GroupTheory.CommutingProductFixedSubgroup
public import Mathlib.Order.SupIndep
public import Mathlib.Data.Nat.Totient
public import Mathlib.Data.Sym.Sym2.Init
public import Mathlib.Tactic.NormNum.GCD

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open Subgroup

private theorem le_normalizer_finset_sup_of_all {G : Type} [Group G] {X : Subgroup G}
    {t : Finset (Subgroup G)} (ht : ∀ W ∈ t, X ≤ normalizer (W : Set G)) :
    X ≤ normalizer ((t.sup id : Subgroup G) : Set G) := by
  classical
  induction t using Finset.induction_on with
  | empty =>
      have h : Subgroup.normalizer ((⊥ : Subgroup G) : Set G) = ⊤ :=
        Subgroup.normalizer_eq_top_iff.mpr inferInstance
      intro x _
      rw [Finset.sup_empty, h]
      exact Subgroup.mem_top x
  | insert W t hWt ih =>
      rw [Finset.sup_insert]
      intro x hx
      exact Subgroup.inf_normalizer_le_normalizer_sup W (t.sup id)
        ⟨ht W (Finset.mem_insert_self _ _) hx,
          ih (fun W' hW' => ht W' (Finset.mem_insert_of_mem hW')) hx⟩

private theorem eq_of_mul_eq_mul_of_disjoint_components {G : Type} [Group G]
    {A B : Subgroup G} (h : Disjoint A B) {a a' : G} (ha : a ∈ A) (ha' : a' ∈ A)
    {b b' : G} (hb : b ∈ B) (hb' : b' ∈ B) (heq : a * b = a' * b') :
    a = a' ∧ b = b' := by
  have hinj := Subgroup.mul_injective_of_disjoint h
  have hpair : ((⟨a, ha⟩ : A), (⟨b, hb⟩ : B)) = ((⟨a', ha'⟩ : A), (⟨b', hb'⟩ : B)) :=
    hinj (by simpa using heq)
  exact ⟨by simpa using congrArg (fun p : A × B => (p.1 : G)) hpair,
    by simpa using congrArg (fun p : A × B => (p.2 : G)) hpair⟩

private theorem coboundary_mul_of_comm {G : Type} [Group G] {x w y : G}
    (h1 : Commute w (x * y * x⁻¹)) (h2 : Commute w y) :
    (x * w * x⁻¹ * w⁻¹) * (x * y * x⁻¹ * y⁻¹) =
      x * (w * y) * x⁻¹ * (w * y)⁻¹ := by
  have hcomm : Commute w⁻¹ ((x * y * x⁻¹) * y⁻¹) :=
    (h1.inv_left).mul_right (h2.inv_left.inv_right)
  calc (x * w * x⁻¹ * w⁻¹) * (x * y * x⁻¹ * y⁻¹)
      = x * w * x⁻¹ * (w⁻¹ * ((x * y * x⁻¹) * y⁻¹)) := by group
    _ = x * w * x⁻¹ * (((x * y * x⁻¹) * y⁻¹) * w⁻¹) := by rw [hcomm.eq]
    _ = x * (w * y) * x⁻¹ * (w * y)⁻¹ := by group

theorem exists_coboundary_of_supIndep {G : Type} [Group G] {X : Subgroup G}
    {s : Finset (Subgroup G)} (hs : s.SupIndep id)
    (hY : ∀ a ∈ s.sup id, ∀ b ∈ s.sup id, a * b = b * a)
    (hXW : ∀ W ∈ s, X ≤ normalizer (W : Set G)) (T : Set G)
    (hW : ∀ W ∈ s, ∀ d : G → G, (∀ x ∈ X, d x ∈ W) →
      (∀ x ∈ X, ∀ y ∈ X, d (x * y) = d x * (x * d y * x⁻¹)) → (∀ t ∈ T, d t = 1) →
      ∃ w ∈ W, ∀ x ∈ X, d x = x * w * x⁻¹ * w⁻¹)
    {δ : G → G} (hδY : ∀ x ∈ X, δ x ∈ s.sup id)
    (hδ : ∀ x ∈ X, ∀ y ∈ X, δ (x * y) = δ x * (x * δ y * x⁻¹)) (hδT : ∀ t ∈ T, δ t = 1) :
    ∃ y ∈ s.sup id, ∀ x ∈ X, δ x = x * y * x⁻¹ * y⁻¹ := by
  classical
  let P : Finset (Subgroup G) → Prop := fun t =>
    ∀ (ht : t.SupIndep id)
      (hYt : ∀ a ∈ t.sup id, ∀ b ∈ t.sup id, a * b = b * a)
      (hXWt : ∀ W ∈ t, X ≤ normalizer (W : Set G))
      (hWt : ∀ W ∈ t, ∀ d : G → G, (∀ x ∈ X, d x ∈ W) →
        (∀ x ∈ X, ∀ y ∈ X, d (x * y) = d x * (x * d y * x⁻¹)) →
        (∀ t' ∈ T, d t' = 1) →
        ∃ w ∈ W, ∀ x ∈ X, d x = x * w * x⁻¹ * w⁻¹)
      (δ : G → G) (hδYt : ∀ x ∈ X, δ x ∈ t.sup id)
      (hδt : ∀ x ∈ X, ∀ y ∈ X, δ (x * y) = δ x * (x * δ y * x⁻¹))
      (hδTt : ∀ t' ∈ T, δ t' = 1),
    ∃ y ∈ t.sup id, ∀ x ∈ X, δ x = x * y * x⁻¹ * y⁻¹
  have hmain : P s := by
    refine Finset.induction_on (motive := P) s ?_ ?_
    · intro ht hYt hXWt hWt δ hδYt hδt hδTt
      refine ⟨1, ?_, ?_⟩
      · rw [Finset.sup_empty]
        exact Subgroup.one_mem ⊥
      · intro x hx
        have hx1 : δ x = 1 := by
          have h := hδYt x hx
          rwa [Finset.sup_empty, Subgroup.mem_bot] at h
        rw [hx1]
        simp
    · intro W s' hWnotin ih ht hYt hXWt hWt δ hδYt hδt hδTt
      have hsup : (insert W s').sup id = W ⊔ s'.sup id := Finset.sup_insert
      have hs' : s'.SupIndep id := ht.subset (Finset.subset_insert W s')
      have hdisj : Disjoint W (s'.sup id) :=
        ht (Finset.subset_insert W s') (Finset.mem_insert_self W s') hWnotin
      have hXY' : X ≤ normalizer ((s'.sup id : Subgroup G) : Set G) :=
        le_normalizer_finset_sup_of_all fun W' hW' => hXWt W' (Finset.mem_insert_of_mem hW')
      have hY' : ∀ a ∈ s'.sup id, ∀ b ∈ s'.sup id, a * b = b * a := fun a ha b hb =>
        hYt a (by rw [hsup]; exact Subgroup.mem_sup_right ha)
          b (by rw [hsup]; exact Subgroup.mem_sup_right hb)
      have hXW' : ∀ W' ∈ s', X ≤ normalizer (W' : Set G) :=
        fun W' hW' => hXWt W' (Finset.mem_insert_of_mem hW')
      have hW' : ∀ W' ∈ s', ∀ d : G → G, (∀ x ∈ X, d x ∈ W') →
          (∀ x ∈ X, ∀ y ∈ X, d (x * y) = d x * (x * d y * x⁻¹)) →
          (∀ t' ∈ T, d t' = 1) →
          ∃ w ∈ W', ∀ x ∈ X, d x = x * w * x⁻¹ * w⁻¹ :=
        fun W' hW' => hWt W' (Finset.mem_insert_of_mem hW')
      have hdecomp : ∀ x ∈ X, ∃ w ∈ W, ∃ r ∈ s'.sup id, w * r = δ x := by
        intro x hx
        have hmem : δ x ∈ W ⊔ s'.sup id := by
          rw [← hsup]
          exact hδYt x hx
        exact CFSG.GroupTheory.exists_mul_of_mem_sup_of_commute
          (A := W) (B := s'.sup id)
          (fun a ha b hb => hYt a (by rw [hsup]; exact Subgroup.mem_sup_left ha)
            b (by rw [hsup]; exact Subgroup.mem_sup_right hb))
          hmem
      have hex : ∀ x ∈ X, ∃ p : W × (s'.sup id : Subgroup G), (p.1 : G) * (p.2 : G) = δ x := by
        intro x hx
        obtain ⟨w, hw, r, hr, hwr⟩ := hdecomp x hx
        exact ⟨(⟨w, hw⟩, ⟨r, hr⟩), hwr⟩
      let dW : G → G := fun x => if hx : x ∈ X then (Classical.choose (hex x hx)).1 else 1
      let r : G → G := fun x => if hx : x ∈ X then (Classical.choose (hex x hx)).2 else 1
      have hdW_mem : ∀ x ∈ X, dW x ∈ W := by
        intro x hx
        dsimp only [dW]
        rw [dif_pos hx]
        exact (Classical.choose (hex x hx)).1.2
      have hr_mem : ∀ x ∈ X, r x ∈ s'.sup id := by
        intro x hx
        dsimp only [r]
        rw [dif_pos hx]
        exact (Classical.choose (hex x hx)).2.2
      have hdec : ∀ x ∈ X, dW x * r x = δ x := by
        intro x hx
        dsimp only [dW, r]
        simp only [dif_pos hx]
        exact Classical.choose_spec (hex x hx)
      have hkey : ∀ x ∈ X, ∀ y ∈ X,
          dW (x * y) * r (x * y) =
            (dW x * (x * dW y * x⁻¹)) * (r x * (x * r y * x⁻¹)) := by
        intro x hx y hy
        have hxy : x * y ∈ X := X.mul_mem hx hy
        have hA : x * dW y * x⁻¹ ∈ W :=
          (Subgroup.le_normalizer_iff.mp (hXWt W (Finset.mem_insert_self W s'))) x hx
            (dW y) (hdW_mem y hy)
        have hcomm : Commute (r x) (x * dW y * x⁻¹) :=
          hYt (r x) (by rw [hsup]; exact Subgroup.mem_sup_right (hr_mem x hx))
            (x * dW y * x⁻¹) (by rw [hsup]; exact Subgroup.mem_sup_left hA)
        calc dW (x * y) * r (x * y)
            = δ (x * y) := hdec (x * y) hxy
          _ = δ x * (x * δ y * x⁻¹) := hδt x hx y hy
          _ = (dW x * r x) * (x * (dW y * r y) * x⁻¹) := by
                rw [← hdec x hx, ← hdec y hy]
          _ = (dW x * r x) * ((x * dW y * x⁻¹) * (x * r y * x⁻¹)) := by
                rw [show x * (dW y * r y) * x⁻¹ =
                  (x * dW y * x⁻¹) * (x * r y * x⁻¹) by group]
          _ = (dW x * (x * dW y * x⁻¹)) * (r x * (x * r y * x⁻¹)) :=
                hcomm.mul_mul_mul_comm (dW x) (x * r y * x⁻¹)
      have hdW_cross : ∀ x ∈ X, ∀ y ∈ X, dW (x * y) = dW x * (x * dW y * x⁻¹) := by
        intro x hx y hy
        have hxy : x * y ∈ X := X.mul_mem hx hy
        have hA : x * dW y * x⁻¹ ∈ W :=
          (Subgroup.le_normalizer_iff.mp (hXWt W (Finset.mem_insert_self W s'))) x hx
            (dW y) (hdW_mem y hy)
        have hB : x * r y * x⁻¹ ∈ s'.sup id :=
          (Subgroup.le_normalizer_iff.mp hXY') x hx (r y) (hr_mem y hy)
        exact (eq_of_mul_eq_mul_of_disjoint_components hdisj (hdW_mem (x * y) hxy)
          (W.mul_mem (hdW_mem x hx) hA) (hr_mem (x * y) hxy)
          ((s'.sup id).mul_mem (hr_mem x hx) hB) (hkey x hx y hy)).1
      have hr_cross : ∀ x ∈ X, ∀ y ∈ X, r (x * y) = r x * (x * r y * x⁻¹) := by
        intro x hx y hy
        have hxy : x * y ∈ X := X.mul_mem hx hy
        have hA : x * dW y * x⁻¹ ∈ W :=
          (Subgroup.le_normalizer_iff.mp (hXWt W (Finset.mem_insert_self W s'))) x hx
            (dW y) (hdW_mem y hy)
        have hB : x * r y * x⁻¹ ∈ s'.sup id :=
          (Subgroup.le_normalizer_iff.mp hXY') x hx (r y) (hr_mem y hy)
        exact (eq_of_mul_eq_mul_of_disjoint_components hdisj (hdW_mem (x * y) hxy)
          (W.mul_mem (hdW_mem x hx) hA) (hr_mem (x * y) hxy)
          ((s'.sup id).mul_mem (hr_mem x hx) hB) (hkey x hx y hy)).2
      have hdW_one : ∀ t ∈ T, dW t = 1 := by
        intro t ht
        by_cases htX : t ∈ X
        · have h1 : dW t * r t = 1 * 1 := by rw [hdec t htX, hδTt t ht, mul_one]
          exact (eq_of_mul_eq_mul_of_disjoint_components hdisj (hdW_mem t htX) W.one_mem
            (hr_mem t htX) (s'.sup id).one_mem h1).1
        · dsimp only [dW]
          rw [dif_neg htX]
      have hr_one : ∀ t ∈ T, r t = 1 := by
        intro t ht
        by_cases htX : t ∈ X
        · have h1 : dW t * r t = 1 * 1 := by rw [hdec t htX, hδTt t ht, mul_one]
          exact (eq_of_mul_eq_mul_of_disjoint_components hdisj (hdW_mem t htX) W.one_mem
            (hr_mem t htX) (s'.sup id).one_mem h1).2
        · dsimp only [r]
          rw [dif_neg htX]
      obtain ⟨y', hy'mem, hy'⟩ := ih hs' hY' hXW' hW' r hr_mem hr_cross hr_one
      obtain ⟨w, hw_mem, hw⟩ :=
        hWt W (Finset.mem_insert_self W s') dW hdW_mem hdW_cross hdW_one
      refine ⟨w * y', ?_, ?_⟩
      · rw [hsup]
        exact Subgroup.mul_mem_sup hw_mem hy'mem
      · intro x hx
        have hy'conj : x * y' * x⁻¹ ∈ s'.sup id :=
          (Subgroup.le_normalizer_iff.mp hXY') x hx y' hy'mem
        have hcomm1 : Commute w (x * y' * x⁻¹) :=
          hYt w (by rw [hsup]; exact Subgroup.mem_sup_left hw_mem) (x * y' * x⁻¹)
            (by rw [hsup]; exact Subgroup.mem_sup_right hy'conj)
        have hcomm2 : Commute w y' :=
          hYt w (by rw [hsup]; exact Subgroup.mem_sup_left hw_mem) y'
            (by rw [hsup]; exact Subgroup.mem_sup_right hy'mem)
        rw [← hdec x hx, hw x hx, hy' x hx]
        exact coboundary_mul_of_comm hcomm1 hcomm2
  exact hmain hs hY hXW hW δ hδY hδ hδT

end CFSG.LocalAnalysis.WeakClosure81
