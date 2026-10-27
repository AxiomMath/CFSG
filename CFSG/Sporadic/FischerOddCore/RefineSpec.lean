module

public import CFSG.Sporadic.FischerOddCore.LabelSpec
public import CFSG.Certificates.NativeRefine
public import Mathlib.Data.List.GetD
import Mathlib.Tactic.NormNum.Inv
import Mathlib.Tactic.NormNum.Pow

public noncomputable section

namespace CFSG.Sporadic.FischerOddCore

open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Certificates CFSG.Certificates.Native
open CFSG.Sporadic.FischerOddCore.Native

variable {n : ℕ}

@[expose] def ColMap (n : ℕ) (c c' : Array ℕ) (σ : Equiv.Perm (Fin n)) : Prop :=
  ∀ v : Fin n, c'[((σ v : Fin n) : ℕ)]! = c[(v : ℕ)]!

section Refine

variable {nbr : Array (List ℕ)} {t : Array ℕ} {T σ : Equiv.Perm (Fin n)}
  (hnbr : ∀ x : Fin n, PointList n nbr[(x : ℕ)]!) (hσ : NbrInv nbr σ) (ht : Rep n t T)
  (hcomm : σ * T = T * σ)

include hnbr hσ in
theorem nbrSum_map {c c' : Array ℕ} (hc : ColMap n c c' σ) (v : Fin n) :
    nbrSum nbr c' (σ v) = nbrSum nbr c v := by
  suffices h : ∀ F : ℕ → ℕ,
      ((nbr[((σ v : Fin n) : ℕ)]!).map fun w => F c'[w]!).sum =
        ((nbr[(v : ℕ)]!).map fun w => F c[w]!).sum by
    exact h hcol
  intro F
  have hp := ((nbr_perm hnbr hσ v).map (fun w => F c'[w]!)).sum_eq
  rw [List.map_map] at hp
  refine hp.trans ?_
  show _ = ((nbr[(v : ℕ)]!).map fun w => F c[w]!).sum
  refine congrArg List.sum (List.map_congr_left fun w hw => ?_)
  have hwn := (hnbr v).lt w hw
  simp only [Function.comp_apply]
  rw [permNat_lt σ hwn, hc ⟨w, hwn⟩]

include ht hcomm in
theorem colMap_t {c c' : Array ℕ} (hc : ColMap n c c' σ) (v : Fin n) :
    c'[t[((σ v : Fin n) : ℕ)]!]! = c[t[(v : ℕ)]!]! := by
  have e : T (σ v) = σ (T v) := by
    rw [← Equiv.Perm.mul_apply, ← hcomm, Equiv.Perm.mul_apply]
  rw [ht (σ v), ht v, e, hc (T v)]

include hnbr hσ ht hcomm in
theorem stepT_map {c c' : Array ℕ} (hc : ColMap n c c' σ) :
    ColMap n (stepT n nbr t c) (stepT n nbr t c') σ := by
  intro v
  unfold stepT
  rw [getElem!_ofFn_nat _ (σ v).2, getElem!_ofFn_nat _ v.2]
  simp only
  rw [hc v, colMap_t ht hcomm hc v, nbrSum_map hnbr hσ hc v]

include hnbr hσ ht hcomm in
theorem refineT_map {c c' : Array ℕ} (hc : ColMap n c c' σ) :
    ∀ k, ColMap n (refineT n nbr t c k) (refineT n nbr t c' k) σ
  | 0 => hc
  | k + 1 => stepT_map hnbr hσ ht hcomm (refineT_map hc k)

theorem idxOf?_map {pre : List ℕ} {f : ℕ → ℕ} {a : ℕ} (hf : ∀ x ∈ pre, f x = f a → x = a) :
    (pre.map f).idxOf? (f a) = pre.idxOf? a := by
  induction pre with
  | nil => rfl
  | cons x xs ih =>
    rw [List.map_cons, List.idxOf?_cons, List.idxOf?_cons,
      ih fun y hy => hf y (List.mem_cons_of_mem _ hy)]
    congr 1
    by_cases h : x = a
    · simp [h]
    · have : f x ≠ f a := fun e => h (hf x (List.mem_cons_self) e)
      simp [h, this]

theorem permNat_injOn {a x : ℕ} (ha : a < n) (hx : x < n) (h : permNat σ x = permNat σ a) :
    x = a := by
  rw [permNat_lt σ hx, permNat_lt σ ha] at h
  exact congrArg Fin.val (σ.injective (Fin.ext h))

include ht hcomm in
theorem initT_map {pre : List ℕ} (hpre : ∀ x ∈ pre, x < n) :
    ColMap n (initT n t pre) (initT n t (pre.map (permNat σ))) σ := by
  intro v
  unfold initT
  rw [getElem!_ofFn_nat _ (σ v).2, getElem!_ofFn_nat _ v.2]
  simp only
  have hidx : (pre.map (permNat σ)).idxOf? ((σ v : Fin n) : ℕ) = pre.idxOf? (v : ℕ) := by
    rw [show ((σ v : Fin n) : ℕ) = permNat σ v by rw [permNat_lt σ v.2]]
    exact idxOf?_map fun x hx h => permNat_injOn v.2 (hpre x hx) h
  have hfix : (t[((σ v : Fin n) : ℕ)]! == ((σ v : Fin n) : ℕ)) = (t[(v : ℕ)]! == (v : ℕ)) := by
    have e : T (σ v) = σ (T v) := by
      rw [← Equiv.Perm.mul_apply, ← hcomm, Equiv.Perm.mul_apply]
    rw [ht (σ v), ht v, e]
    by_cases h : T v = v
    · rw [h]
      simp
    · have h' : σ (T v) ≠ σ v := fun e' => h (σ.injective e')
      have h1 : ((σ (T v) : Fin n) : ℕ) ≠ ((σ v : Fin n) : ℕ) := fun e' => h' (Fin.ext e')
      have h2 : ((T v : Fin n) : ℕ) ≠ (v : ℕ) := fun e' => h (Fin.ext e')
      simp [h1, h2]
  rw [hidx, hfix]

include hnbr hσ ht hcomm in
theorem colourT_map {pre : List ℕ} (hpre : ∀ x ∈ pre, x < n) (k : ℕ) :
    ColMap n (colourT n nbr t pre k) (colourT n nbr t (pre.map (permNat σ)) k) σ :=
  refineT_map hnbr hσ ht hcomm (initT_map ht hcomm hpre) k

end Refine

theorem cellCount_eq (c : Array ℕ) (col : ℕ) :
    cellCount n c col = Set.ncard {w : Fin n | c[(w : ℕ)]! = col} := by
  rw [cellCount, ← card_fin_subtype_eq_countP, ← Nat.card_coe_set_eq]
  exact Nat.card_congr (Equiv.subtypeEquivRight fun w => by simp)

theorem colInj_injective {c : Array ℕ} (h : colInj n c = true) {v w : Fin n}
    (hvw : c[(v : ℕ)]! = c[(w : ℕ)]!) : v = w := by
  have hs := strictIncr_pairwise h
  have hnd : ((List.range n).map fun w => c[w]!).Nodup := by
    have := (List.mergeSort_perm ((List.range n).map fun w => c[w]!)
      fun a b => decide (a ≤ b)).nodup_iff
    exact this.1 (hs.imp ne_of_lt)
  have hinj := List.inj_on_of_nodup_map hnd
  exact Fin.ext (hinj (List.mem_range.2 v.2) (List.mem_range.2 w.2) hvw)

section Bounds

variable {nbr : Array (List ℕ)} {t : Array ℕ} {T : Equiv.Perm (Fin n)}

@[expose] def ptsPt (n : ℕ) (hn : 0 < n) (pts : List ℕ) (s : ℕ) : Fin n :=
  ⟨pts.getD s 0 % n, Nat.mod_lt _ hn⟩

theorem ptsPt_val {hn : 0 < n} {pts : List ℕ} (hpts : ∀ x ∈ pts, x < n) {s : ℕ}
    (hs : s < pts.length) : (ptsPt n hn pts s : ℕ) = pts.getD s 0 := by
  show pts.getD s 0 % n = pts.getD s 0
  apply Nat.mod_eq_of_lt
  rw [List.getD_eq_getElem _ _ hs]
  exact hpts _ (List.getElem_mem _)

theorem take_map_permNat {σ : Equiv.Perm (Fin n)} {hn : 0 < n} {pts : List ℕ}
    (hpts : ∀ x ∈ pts, x < n) {s : ℕ} (hs : s ≤ pts.length)
    (hfix : ∀ j < s, σ (ptsPt n hn pts j) = ptsPt n hn pts j) :
    (pts.take s).map (permNat σ) = pts.take s := by
  apply List.ext_getElem (by simp)
  intro j h1 h2
  simp only [List.length_map, List.length_take] at h1
  have hj : j < pts.length := by omega
  have hjs : j < s := by omega
  rw [List.getElem_map, List.getElem_take]
  have hp : (ptsPt n hn pts j : ℕ) = pts[j] := by
    rw [ptsPt_val hpts hj, List.getD_eq_getElem _ _ hj]
  have h1 : (⟨pts[j], hpts _ (List.getElem_mem hj)⟩ : Fin n) = ptsPt n hn pts j := Fin.ext hp.symm
  rw [permNat_lt σ (hpts _ (List.getElem_mem hj)), h1, hfix j hjs, hp]

theorem card_le_of_boundsOK {K : Subgroup (Equiv.Perm (Fin n))} [Finite K]
    (hnbr : ∀ x : Fin n, PointList n nbr[(x : ℕ)]!) (ht : Rep n t T)
    (hK : ∀ σ ∈ K, NbrInv nbr σ ∧ σ * T = T * σ) (hn : 0 < n) {pts bounds : List ℕ} {k : ℕ}
    (hpts : ∀ x ∈ pts, x < n) (hok : boundsOK n nbr t pts bounds k = true) :
    (∀ s < pts.length, (MulAction.orbit (stabChain (G := K) (ptsPt n hn pts) s)
      (ptsPt n hn pts s)).ncard ≤ bounds.getD s 0) ∧
    stabChain (G := K) (ptsPt n hn pts) pts.length = ⊥ ∧ Nat.card K ≤ bounds.prod := by
  rw [boundsOK, Bool.and_eq_true, Bool.and_eq_true, beq_iff_eq] at hok
  obtain ⟨⟨hlen, hcells⟩, hinj⟩ := hok
  have hmap : ∀ s ≤ pts.length, ∀ σ ∈ stabChain (G := K) (ptsPt n hn pts) s,
      ColMap n (colourT n nbr t (pts.take s) k) (colourT n nbr t (pts.take s) k)
        (σ : Equiv.Perm (Fin n)) := by
    intro s hs σ hσ
    have hfix : ∀ j < s, (σ : Equiv.Perm (Fin n)) (ptsPt n hn pts j) = ptsPt n hn pts j :=
      fun j hj => (mem_stabChain.1 hσ) j hj
    have h := colourT_map hnbr (hK _ σ.2).1 ht (hK _ σ.2).2
      (pre := pts.take s) (fun x hx => hpts x (List.mem_of_mem_take hx)) k
    rwa [take_map_permNat hpts hs hfix] at h
  have horb : ∀ s < pts.length, (MulAction.orbit (stabChain (G := K) (ptsPt n hn pts) s)
      (ptsPt n hn pts s)).ncard ≤ bounds.getD s 0 := by
    intro s hs
    have hc := allLt_spec hcells hs
    rw [beq_iff_eq, cellCount_eq] at hc
    rw [← hc]
    refine Set.ncard_le_ncard ?_ (Set.toFinite _)
    rintro _ ⟨σ, rfl⟩
    have e := hmap s hs.le σ σ.2 (ptsPt n hn pts s)
    rw [← ptsPt_val hpts hs]
    exact e
  have htriv : stabChain (G := K) (ptsPt n hn pts) pts.length = ⊥ := by
    rw [eq_bot_iff]
    intro σ hσ
    rw [Subgroup.mem_bot]
    apply Subtype.ext
    apply Equiv.ext
    intro v
    have e := hmap pts.length le_rfl σ hσ v
    rw [List.take_length] at e
    exact colInj_injective hinj e
  refine ⟨horb, htriv, ?_⟩
  have h := card_le_prod_of_stabChain (G := K) (ptsPt n hn pts) (fun s => bounds.getD s 0)
    pts.length horb htriv
  refine h.trans (le_of_eq ?_)
  rw [hlen]
  clear h horb htriv hmap hcells hinj hlen
  induction bounds using List.reverseRecOn with
  | nil => simp
  | append_singleton l a ih =>
    rw [List.length_append, List.length_singleton, Finset.prod_range_succ, List.prod_append,
      List.prod_singleton, List.getD_append_right _ _ _ _ le_rfl, Nat.sub_self,
      List.getD_cons_zero]
    congr 1
    rw [← ih]
    apply Finset.prod_congr rfl
    intro s hs
    rw [List.getD_append _ _ _ _ (Finset.mem_range.1 hs)]

end Bounds

end CFSG.Sporadic.FischerOddCore
