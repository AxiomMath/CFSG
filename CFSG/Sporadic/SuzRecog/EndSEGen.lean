module

public import CFSG.LocalAnalysis.OddStandard.Seitz77L34Inv
public import CFSG.LocalAnalysis.OddStandard.Seitz77Thompson

public section

namespace CFSG.Sporadic.SuzRecog.EndSEGen

open Subgroup CFSG.ComponentClassification.PSL3Four CFSG.PSL3Four.Native
open CFSG.OddStandard.Seitz77

private def LRep (l : List ℕ) (g : Equiv.Perm (Fin 42)) : Prop :=
  l.length = 42 ∧ ∀ i : Fin 42, l.getD i 0 = (g i : ℕ)

private def lcomp (p q : List ℕ) : List ℕ := q.map fun i => p.getD i 0

private theorem LRep.comp {p q : List ℕ} {a b : Equiv.Perm (Fin 42)} (ha : LRep p a)
    (hb : LRep q b) : LRep (lcomp p q) (a * b) := by
  refine ⟨by rw [lcomp, List.length_map, hb.1], fun i => ?_⟩
  have hi : (i : ℕ) < q.length := by rw [hb.1]; exact i.2
  rw [lcomp, List.getD_eq_getElem _ _ (by rw [List.length_map]; exact hi), List.getElem_map,
    ← List.getD_eq_getElem q 0 hi, hb.2 i, ha.2 (b i), Equiv.Perm.mul_apply]

private theorem LRep.perm_eq {l : List ℕ} {a b : Equiv.Perm (Fin 42)} (ha : LRep l a)
    (hb : LRep l b) : a = b :=
  Equiv.ext fun i => Fin.ext ((ha.2 i).symm.trans (hb.2 i))

private theorem LRep.list_eq {l l' : List ℕ} {a : Equiv.Perm (Fin 42)} (ha : LRep l a)
    (ha' : LRep l' a) : l = l' := by
  refine List.ext_getElem (ha.1.trans ha'.1.symm) fun n h h' => ?_
  have hn : n < 42 := ha.1 ▸ h
  have e := (ha.2 ⟨n, hn⟩).trans (ha'.2 ⟨n, hn⟩).symm
  rwa [List.getD_eq_getElem _ _ h, List.getD_eq_getElem _ _ h'] at e

private theorem lrep_one : LRep (List.range 42) 1 :=
  ⟨List.length_range, by decide⟩

private theorem lrep_of_tabRep {t : Tab} {g : Equiv.Perm (Fin 42)} (h : TabRep t g) :
    LRep t.toList g := by
  refine ⟨by rw [Array.length_toList]; exact h.1, fun i => ?_⟩
  have hi : (i : ℕ) < t.size := by rw [h.1]; exact i.2
  rw [List.getD_eq_getElem _ _ (by rw [Array.length_toList]; exact hi), Array.getElem_toList,
    ← h.2 i, getElem!_pos t (i : ℕ) hi]

private def gen (k : ℕ) : Equiv.Perm (Fin 42) := if k = 0 then g₁ else if k = 1 then g₂ else g₃

private def genL (k : ℕ) : List ℕ :=
  if k = 0 then g₁T.toList else if k = 1 then g₂T.toList else g₃T.toList

private def wperm : List ℕ → Equiv.Perm (Fin 42)
  | [] => 1
  | k :: w => gen k * wperm w

private def wlist : List ℕ → List ℕ
  | [] => List.range 42
  | k :: w => lcomp (genL k) (wlist w)

private theorem lrep_gen (k : ℕ) : LRep (genL k) (gen k) := by
  unfold genL gen
  split_ifs
  · exact lrep_of_tabRep tabRep_g₁
  · exact lrep_of_tabRep tabRep_g₂
  · exact lrep_of_tabRep tabRep_g₃

private theorem lrep_wlist : ∀ w : List ℕ, LRep (wlist w) (wperm w)
  | [] => lrep_one
  | k :: w => (lrep_gen k).comp (lrep_wlist w)

private theorem gen_mem_S (k : ℕ) : gen k ∈ S := by
  unfold gen
  split_ifs
  · exact g₁_mem_S
  · exact g₂_mem_S
  · exact g₃_mem_S

private theorem wperm_mem_S : ∀ w : List ℕ, wperm w ∈ S
  | [] => S.one_mem
  | k :: w => S.mul_mem (gen_mem_S k) (wperm_mem_S w)

private theorem wperm_append : ∀ v w : List ℕ, wperm (v ++ w) = wperm v * wperm w
  | [], w => (one_mul _).symm
  | k :: v, w => by
    rw [List.cons_append, wperm, wperm, wperm_append v w, mul_assoc]

private theorem commute_of {v w : List ℕ} (h : wlist (w ++ v) = wlist (v ++ w)) :
    wperm w * wperm v = wperm v * wperm w := by
  rw [← wperm_append, ← wperm_append]
  have h' := lrep_wlist (v ++ w)
  rw [← h] at h'
  exact (lrep_wlist (w ++ v)).perm_eq h'

private theorem orderOf_of {w : List ℕ} (h1 : wlist (w ++ w) = List.range 42)
    (h2 : wlist w ≠ List.range 42) : orderOf (wperm w) = 2 := by
  have hsq : wperm w ^ 2 = 1 := by
    rw [pow_two, ← wperm_append]
    have h := lrep_wlist (w ++ w)
    rw [h1] at h
    exact h.perm_eq lrep_one
  refine orderOf_eq_prime hsq fun he => h2 ?_
  have h := lrep_wlist w
  rw [he] at h
  exact h.list_eq lrep_one

theorem S_le_of_closed (K : Subgroup (Equiv.Perm (Fin 42))) (hr : r₁ ∈ K)
    (hK : ∀ x ∈ K, orderOf x = 2 → ∀ y ∈ S, y * x = x * y → y ∈ K) : S ≤ K := by
  have step : ∀ v w : List ℕ, wperm v ∈ K → orderOf (wperm v) = 2 →
      wlist (w ++ v) = wlist (v ++ w) → wperm w ∈ K := fun v w hv hv2 h =>
    hK _ hv hv2 _ (wperm_mem_S w) (commute_of h)
  have hr' : wperm [0, 0, 1, 0] = r₁ := by simp [wperm, gen, r₁, pow_two, mul_assoc]
  have h0 : wperm [0, 0, 1, 0] ∈ K := hr' ▸ hr
  have h0' : orderOf (wperm [0, 0, 1, 0]) = 2 := orderOf_of (by decide) (by decide)
  have h1 := step _ [0, 0, 1, 0, 1, 0, 0, 1, 0, 1] h0 h0' (by decide)
  have h1' : orderOf (wperm [0, 0, 1, 0, 1, 0, 0, 1, 0, 1]) = 2 :=
    orderOf_of (by decide) (by decide)
  have h2 := step _ [1] h1 h1' (by decide)
  have h3 := step _ [2] h1 h1' (by decide)
  have h4 := step _ [1, 0, 0, 1, 0, 1] h0 h0' (by decide)
  have h5 := step _ [1, 0, 1, 0, 1, 0, 0, 1, 0, 1, 0, 1] h4
    (orderOf_of (by decide) (by decide)) (by decide)
  have h6 := step _ [0, 1, 0, 1, 0, 0, 1, 0, 0] h0 h0' (by decide)
  have h7 := step _ ([1, 0, 1, 0, 1, 0, 0, 1, 0, 1, 0, 1] ++ [0]) h6
    (orderOf_of (by decide) (by decide)) (by decide)
  have hg₁ : g₁ ∈ K := by
    have h := K.mul_mem (K.inv_mem h5) h7
    rw [wperm_append, inv_mul_cancel_left] at h
    simpa [wperm, gen] using h
  have hg₂ : g₂ ∈ K := by simpa [wperm, gen] using h2
  have hg₃ : g₃ ∈ K := by simpa [wperm, gen] using h3
  rw [S, Subgroup.closure_le]
  intro x hx
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
  rcases hx with rfl | rfl | rfl
  · exact hg₁
  · exact hg₂
  · exact hg₃

theorem eq_top_of_involution_centralizers {H : Subgroup S}
    (h1 : ∃ x ∈ H, orderOf x = 2)
    (h2 : ∀ x ∈ H, orderOf x = 2 → centralizer ({x} : Set S) ≤ H) : H = ⊤ := by
  obtain ⟨x, hxH, hx2⟩ := h1
  obtain ⟨c, hc⟩ := isConj_iff.mp (L34.isConj_r₁S_of_orderOf_eq_two hx2)
  set K : Subgroup (Equiv.Perm (Fin 42)) :=
    (H.comap (MulAut.conj c).toMonoidHom).map S.subtype with hKdef
  have hmemK : ∀ s : S, (s : Equiv.Perm (Fin 42)) ∈ K ↔ c * s * c⁻¹ ∈ H := by
    intro s
    constructor
    · rintro ⟨t, ht, hts⟩
      rw [← Subtype.ext hts]
      exact ht
    · intro hs
      exact ⟨s, hs, rfl⟩
  have hr : r₁ ∈ K :=
    (hmemK L34.r₁S).mpr (hc ▸ hxH)
  have hK : ∀ y ∈ K, orderOf y = 2 → ∀ w ∈ S, w * y = y * w → w ∈ K := by
    rintro _ ⟨s, hs, rfl⟩ hs2 w hw hcomm
    have hsH : c * s * c⁻¹ ∈ H := hs
    have hs2' : orderOf (c * s * c⁻¹) = 2 := by
      rw [← MulAut.conj_apply, MulEquiv.orderOf_eq, ← Subgroup.orderOf_coe]
      exact hs2
    refine (hmemK ⟨w, hw⟩).mpr (h2 _ hsH hs2' ?_)
    rw [mem_centralizer_singleton_iff]
    have hcomm' : (⟨w, hw⟩ : S) * s = s * ⟨w, hw⟩ := Subtype.ext hcomm
    calc c * ⟨w, hw⟩ * c⁻¹ * (c * s * c⁻¹) = c * ((⟨w, hw⟩ : S) * s) * c⁻¹ := by group
      _ = c * (s * ⟨w, hw⟩) * c⁻¹ := by rw [hcomm']
      _ = c * s * c⁻¹ * (c * ⟨w, hw⟩ * c⁻¹) := by group
  have hSK := S_le_of_closed K hr hK
  rw [eq_top_iff]
  intro y _
  have hy := (hmemK (c⁻¹ * y * c)).mp (hSK (c⁻¹ * y * c).2)
  simpa [mul_assoc] using hy

end CFSG.Sporadic.SuzRecog.EndSEGen
