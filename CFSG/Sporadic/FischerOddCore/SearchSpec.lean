module

public import CFSG.Sporadic.FischerOddCore.RefineSpec
import Mathlib.Tactic.NormNum.Inv
import Mathlib.Tactic.NormNum.Pow

public noncomputable section

namespace CFSG.Sporadic.FischerOddCore

open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Certificates CFSG.Certificates.Native
open CFSG.Sporadic.FischerOddCore.Native

variable {n : ℕ}

section Orbits

variable {gens : Array (Array ℕ)} {Gs : ℕ → Equiv.Perm (Fin n)} {reps : List ℕ}
  {oc : Array (ℕ × ℕ × ℕ × ℕ)}

theorem orbitRec_spec (hgens : ∀ g < gens.size, Rep n gens[g]! (Gs g)) (hsize : oc.size = n)
    (hok : ∀ w < n, orbitRecOK gens reps oc w = true) :
    ∀ (w : Fin n) (k : ℕ), oc[(w : ℕ)]!.1 = k → k ≠ 0 → ∃ hr : reps.getD (k - 1) 0 < n,
      ∃ g ∈ Subgroup.closure {x | ∃ j < gens.size, Gs j = x}, g ⟨_, hr⟩ = w := by
  intro w
  induction hd : oc[(w : ℕ)]!.2.2.2 using Nat.strong_induction_on generalizing w with
  | _ d ih =>
    intro k hkw hk
    have h := hok w w.2
    unfold orbitRecOK at h
    simp only [Bool.or_eq_true, beq_iff_eq, hkw, hk, false_or, Bool.and_eq_true,
      decide_eq_true_eq] at h
    obtain ⟨⟨-, hd0⟩, h⟩ := h
    by_cases h1 : oc[(w : ℕ)]!.2.2.2 = 1
    · rw [ite_eq_left (by simpa using h1), beq_iff_eq] at h
      refine ⟨h ▸ w.2, 1, Subgroup.one_mem _, ?_⟩
      exact Fin.ext h.symm
    · rw [ite_eq_right (by simpa using h1)] at h
      simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h
      obtain ⟨⟨⟨hpk, hpd⟩, hg⟩, hgw⟩ := h
      have hp : oc[(w : ℕ)]!.2.1 < n := by
        by_contra hp
        rw [getElem!_neg oc _ (by rw [hsize]; exact hp)] at hpk
        exact hk hpk.symm
      obtain ⟨hr, g', hg', hg'p⟩ := ih _ (hd ▸ hpd) ⟨_, hp⟩ rfl k hpk hk
      refine ⟨hr, Gs oc[(w : ℕ)]!.2.2.1 * g', Subgroup.mul_mem _
        (Subgroup.subset_closure ⟨_, hg, rfl⟩) hg', ?_⟩
      rw [Equiv.Perm.mul_apply, hg'p]
      exact Fin.ext (((hgens _ hg) ⟨_, hp⟩).symm.trans hgw)

end Orbits

section Leaves

variable {nbr : Array (List ℕ)} {t : Array ℕ} {T : Equiv.Perm (Fin n)}

theorem colourMatch {c src : Array ℕ} (hinj : colInj n src = true) {τ : Equiv.Perm (Fin n)}
    (hmap : ColMap n src c τ) {A : Array ℕ}
    (hfull : allLt n (fun v => decide (A[v]! < n) && c[A[v]!]! == src[v]!) = true) :
    Rep n A τ := by
  intro v
  have h := allLt_spec hfull v.2
  simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h
  obtain ⟨hlt, hc⟩ := h
  set u := τ⁻¹ ⟨A[(v : ℕ)]!, hlt⟩
  have hu : τ u = ⟨A[(v : ℕ)]!, hlt⟩ := by simp [u]
  have e := hmap u
  rw [hu] at e
  have huv : u = v := colInj_injective hinj (e.symm.trans hc)
  have hτv : τ v = ⟨A[(v : ℕ)]!, hlt⟩ := by rw [← hu, huv]
  rw [hτv]

theorem imgSorted_eq_of_nbrInv (hnbr : ∀ x : Fin n, PointList n nbr[(x : ℕ)]!)
    {τ : Equiv.Perm (Fin n)} (hτ : NbrInv nbr τ) {A : Array ℕ} (hA : Rep n A τ) (x : Fin n) :
    imgSorted A nbr[(x : ℕ)]! = nbr[A[(x : ℕ)]!]! := by
  obtain ⟨hpl, hfin⟩ := PointList.img hA (hnbr x)
  rw [hA x]
  refine hpl.eq_of_finSet_eq (hnbr (τ x)) ?_
  rw [hfin]
  ext y
  simp only [finSet, Set.mem_smul_set, Set.mem_ofPred_eq, Equiv.Perm.smul_def]
  constructor
  · rintro ⟨z, hz, rfl⟩
    exact (hτ x z).1 hz
  · intro hy
    refine ⟨τ⁻¹ y, ?_, by simp⟩
    rw [hτ x (τ⁻¹ y)]
    simpa using hy

theorem leafOK_spec (hnbr : ∀ x : Fin n, PointList n nbr[(x : ℕ)]!) (ht : Rep n t T)
    {acc : Array (Array ℕ)} {Acc : ℕ → Equiv.Perm (Fin n)}
    (hacc : ∀ k < acc.size, Rep n acc[k]! (Acc k)) {c src : Array ℕ} {N : SNode}
    (hinj : colInj n src = true) (hok : leafOK n nbr t acc c src N = true)
    {τ : Equiv.Perm (Fin n)} (hτ : NbrInv nbr τ) (hτT : τ * T = T * τ) (hmap : ColMap n src c τ) :
    ∃ k < acc.size, τ = Acc k := by
  unfold leafOK at hok
  simp only at hok
  by_cases h1 : N.out = 1
  · rw [ite_eq_left (by simpa using h1)] at hok
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hok
    obtain ⟨⟨hfull, hk⟩, heq⟩ := hok
    exact ⟨N.acc, hk, eq_of_eqA (colourMatch hinj hmap hfull) (hacc _ hk) heq⟩
  · rw [ite_eq_right (by simpa using h1)] at hok
    by_cases h2 : N.out = 2
    · rw [ite_eq_left (by simpa using h2)] at hok
      exfalso
      by_cases hfull : allLt n (fun v => decide ((colMatch n c src)[v]! < n) &&
          c[(colMatch n c src)[v]!]! == src[v]!) = true
      · rw [ite_eq_left hfull] at hok
        simp only [Bool.and_eq_true, decide_eq_true_eq] at hok
        obtain ⟨hx, hv⟩ := hok
        have hA := colourMatch hinj hmap hfull
        set x := violSearch n nbr t (colMatch n c src)
        unfold violAt at hv
        simp only [Bool.or_eq_true, bne_iff_ne, ne_eq] at hv
        rcases hv with hv | hv
        · exact hv (imgSorted_eq_of_nbrInv hnbr hτ hA ⟨x, hx⟩)
        · apply hv
          rw [ht ⟨x, hx⟩, hA (T ⟨x, hx⟩), hA ⟨x, hx⟩, ht (τ ⟨x, hx⟩), ← Equiv.Perm.mul_apply,
            hτT, Equiv.Perm.mul_apply]
      · rw [ite_eq_right hfull] at hok
        simp only [Bool.and_eq_true, decide_eq_true_eq] at hok
        obtain ⟨hv, hall⟩ := hok
        set v := missSearch n (colMatch n c src)
        have := allLt_spec hall (τ ⟨v, hv⟩).2
        rw [bne_iff_ne, hmap ⟨v, hv⟩] at this
        exact this rfl
    · rw [ite_eq_right (by simpa using h2)] at hok
      exact absurd hok (by decide)

end Leaves

theorem getElem!_toArray_map_range {α : Type*} [Inhabited α] (f : ℕ → α) {L d : ℕ}
    (hd : d ≤ L) : ((List.range (L + 1)).map f).toArray[d]! = f d := by
  rw [getElem!_pos _ d (by simp; omega), List.getElem_toArray, List.getElem_map,
    List.getElem_range]

theorem branch_step {pool : Array (Array ℕ)} {Pool : ℕ → Equiv.Perm (Fin n)}
    {H : Subgroup (Equiv.Perm (Fin n))}
    (hpool : ∀ j < pool.size, Rep n pool[j]! (Pool j) ∧ Pool j ∈ H) {nodes : Array SNode}
    {N : SNode} {c : Array ℕ} {col : ℕ} (hb : branchOK n pool nodes c col N = true)
    {y : Fin n} (hcol : c[(y : ℕ)]! = col) :
    ∃ g ∈ H, (∀ x : Fin n, (x : ℕ) ∈ N.pre → g x = x) ∧
      ∃ ch < nodes.size, (nodes[ch]!).pre = N.pre ++ [((g y : Fin n) : ℕ)] := by
  unfold branchOK at hb
  simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true, decide_eq_true_eq] at hb
  obtain ⟨⟨⟨⟨⟨⟨-, hsize⟩, hpoolj⟩, hfix⟩, hkids⟩, horb⟩, hcover⟩ := hb
  have hcov := allLt_spec hcover y.2
  rw [Bool.or_eq_true, bne_iff_ne, bne_iff_ne] at hcov
  obtain ⟨k, hkdef⟩ : ∃ k, (orbitCert n (nodeGens pool N) (N.kids.map Prod.fst))[(y : ℕ)]!.1 = k :=
    ⟨_, rfl⟩
  have hk : k ≠ 0 := by
    rw [← hkdef]
    rcases hcov with hcov | hcov
    · exact absurd hcol hcov
    · exact hcov
  have hgsize : (nodeGens pool N).size = N.pool.length := by simp [nodeGens]
  rw [Array.all_eq_true] at hfix
  have hgens : ∀ g < (nodeGens pool N).size,
      Rep n (nodeGens pool N)[g]! (Pool (N.pool.getD g 0)) ∧
      Pool (N.pool.getD g 0) ∈ H ∧ ∀ x ∈ N.pre, ((nodeGens pool N)[g]!)[x]! = x := by
    intro g hg
    have hg' : g < N.pool.length := hgsize ▸ hg
    have hj := hpoolj _ (List.getElem_mem hg')
    have hgen : (nodeGens pool N)[g]! = pool[N.pool[g]]! := by
      unfold nodeGens
      rw [getElem!_pos _ g (by simpa using hg'), List.getElem_toArray, List.getElem_map]
    rw [List.getD_eq_getElem _ _ hg', hgen]
    refine ⟨(hpool _ hj).1, (hpool _ hj).2, fun x hx => ?_⟩
    have := hfix g hg
    rw [List.all_eq_true] at this
    have h2 := this x hx
    rw [← getElem!_pos _ g hg, hgen, beq_iff_eq] at h2
    exact h2
  obtain ⟨hr, g, hgcl, hgr⟩ := orbitRec_spec (Gs := fun j => Pool (N.pool.getD j 0))
    (fun g hg => (hgens g hg).1) hsize (fun w hw => allLt_spec horb hw) y k hkdef hk
  have hclH : Subgroup.closure {x | ∃ j < (nodeGens pool N).size, Pool (N.pool.getD j 0) = x} ≤
      H := by
    rw [Subgroup.closure_le]
    rintro _ ⟨j, hj, rfl⟩
    exact (hgens j hj).2.1
  have hclfix : ∀ g' ∈ Subgroup.closure
      {x | ∃ j < (nodeGens pool N).size, Pool (N.pool.getD j 0) = x},
      ∀ x : Fin n, (x : ℕ) ∈ N.pre → g' x = x := by
    intro g' hg'
    induction hg' using Subgroup.closure_induction with
    | mem z hz =>
      obtain ⟨j, hj, rfl⟩ := hz
      intro x hx
      apply Fin.ext
      rw [← (hgens j hj).1 x]
      exact (hgens j hj).2.2 x hx
    | one => intro x _; rfl
    | mul z w _ _ hz hw => intro x hx; rw [Equiv.Perm.mul_apply, hw x hx, hz x hx]
    | inv z _ hz =>
      intro x hx
      rw [Equiv.Perm.inv_eq_iff_eq]
      exact (hz x hx).symm
  have hk1 : k - 1 < N.kids.length := by
    have := allLt_spec horb y.2
    unfold orbitRecOK at this
    simp only [Bool.or_eq_true, beq_iff_eq, hkdef, hk, false_or, Bool.and_eq_true,
      decide_eq_true_eq, List.length_map] at this
    omega
  obtain ⟨hch, hchpre⟩ := hkids _ (List.getElem_mem hk1)
  have hgy : g⁻¹ y = ⟨_, hr⟩ := by
    rw [Equiv.Perm.inv_eq_iff_eq]
    exact hgr.symm
  refine ⟨g⁻¹, H.inv_mem (hclH hgcl), fun x hx => ?_, _, hch, ?_⟩
  · rw [Equiv.Perm.inv_eq_iff_eq]
    exact (hclfix g hgcl x hx).symm
  · rw [hchpre, hgy]
    congr 2
    show (N.kids[k - 1]).1 = (N.kids.map Prod.fst).getD (k - 1) 0
    rw [List.getD_eq_getElem _ _ (by simpa using hk1), List.getElem_map]

theorem searchOK_facts {nbr : Array (List ℕ)} {t : Array ℕ} {base : List ℕ}
    {pool : Array (Array ℕ)} {nodes : Array SNode} {acc : Array (Array ℕ)} {K chunks : ℕ}
    (hc : 0 < chunks) (hok : searchOK n nbr t base pool nodes acc K chunks = true) :
    0 < nodes.size ∧ (nodes[0]!).pre = [] ∧ colInj n (colourT n nbr t base K) = true ∧
      ∀ i < nodes.size, (if (nodes[i]!).pre.length < base.length then
        branchOK n pool nodes (colourT n nbr t (nodes[i]!).pre K)
          ((colourT n nbr t (base.take (nodes[i]!).pre.length) K)[base.getD
            (nodes[i]!).pre.length 0]!) (nodes[i]!)
      else leafOK n nbr t acc (colourT n nbr t (nodes[i]!).pre K) (colourT n nbr t base K)
        (nodes[i]!)) = true := by
  unfold searchOK at hok
  rw [Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq,
    getElem!_toArray_map_range _ le_rfl, List.take_length] at hok
  obtain ⟨⟨⟨hpos, hroot⟩, hinj⟩, hnodes⟩ := hok
  refine ⟨hpos, hroot, hinj, fun i hi => ?_⟩
  have h := parLt_spec hc hnodes i hi
  by_cases hd : (nodes[i]!).pre.length < base.length
  · rw [ite_eq_left hd] at h ⊢
    rwa [getElem!_toArray_map_range _ hd.le] at h
  · rw [ite_eq_right hd] at h ⊢
    exact h

theorem exists_mul_eq_acc_of_searchOK {nbr : Array (List ℕ)} {t : Array ℕ}
    {T : Equiv.Perm (Fin n)} (hnbr : ∀ x : Fin n, PointList n nbr[(x : ℕ)]!) (ht : Rep n t T)
    {base : List ℕ} (hbase : ∀ x ∈ base, x < n) {pool : Array (Array ℕ)}
    {Pool : ℕ → Equiv.Perm (Fin n)} {H : Subgroup (Equiv.Perm (Fin n))}
    (hpool : ∀ j < pool.size, Rep n pool[j]! (Pool j) ∧ Pool j ∈ H)
    (hH : ∀ h ∈ H, NbrInv nbr h ∧ h * T = T * h) {nodes : Array SNode} {acc : Array (Array ℕ)}
    {Acc : ℕ → Equiv.Perm (Fin n)} (hacc : ∀ k < acc.size, Rep n acc[k]! (Acc k))
    {K chunks : ℕ} (hc : 0 < chunks) (hok : searchOK n nbr t base pool nodes acc K chunks = true)
    {σ : Equiv.Perm (Fin n)} (hσ : NbrInv nbr σ) (hσT : σ * T = T * σ) :
    ∃ h ∈ H, ∃ k < acc.size, h * σ = Acc k := by
  obtain ⟨hpos, hroot, hinj, hnodes⟩ := searchOK_facts hc hok
  have hadm : ∀ h ∈ H, NbrInv nbr (h * σ) ∧ h * σ * T = T * (h * σ) := fun h hh =>
    ⟨AdjFacts.nbrInv_mul (hH h hh).1 hσ, by
      rw [mul_assoc, hσT, ← mul_assoc, (hH h hh).2, mul_assoc]⟩
  have hbase' : ∀ d, ∀ x ∈ base.take d, x < n := fun d x hx => hbase x (List.mem_of_mem_take hx)
  have key : ∀ d ≤ base.length, ∃ h ∈ H, ∃ i < nodes.size,
      (nodes[i]!).pre = (base.take d).map (permNat (h * σ)) := by
    intro d
    induction d with
    | zero =>
      intro _
      exact ⟨1, H.one_mem, 0, hpos, by rw [hroot]; rfl⟩
    | succ d ih =>
      intro hd
      obtain ⟨h, hh, i, hi, hpre⟩ := ih (by omega)
      have hlen : (nodes[i]!).pre.length = d := by
        rw [hpre, List.length_map, List.length_take]
        omega
      have hdl : d < base.length := by omega
      have hb := hnodes i hi
      rw [hlen, ite_eq_left hdl] at hb
      have hmap := colourT_map hnbr (hadm h hh).1 ht (hadm h hh).2 (hbase' d) K
      rw [← hpre] at hmap
      have hbd : base[d] < n := hbase _ (List.getElem_mem hdl)
      have hgd : base.getD d 0 = base[d] := List.getD_eq_getElem _ _ hdl
      have hbd' : base.getD d 0 < n := hgd ▸ hbd
      obtain ⟨g, hgH, hgfix, ch, hch, hchpre⟩ := branch_step hpool hb (hmap ⟨_, hbd'⟩)
      refine ⟨g * h, H.mul_mem hgH hh, ch, hch, ?_⟩
      have e : (⟨base.getD d 0, hbd'⟩ : Fin n) = ⟨base[d], hbd⟩ := Fin.ext hgd
      rw [hchpre, hpre, List.take_add_one, List.map_append, List.getElem?_eq_getElem hdl,
        Option.toList_some, List.map_singleton, permNat_lt _ hbd, e]
      congr 1
      apply List.map_congr_left
      intro x hx
      have hxn := hbase' d x hx
      have hmem : (((h * σ) ⟨x, hxn⟩ : Fin n) : ℕ) ∈ (nodes[i]!).pre := by
        rw [hpre]
        exact List.mem_map.2 ⟨x, hx, by rw [permNat_lt _ hxn]⟩
      rw [permNat_lt _ hxn, permNat_lt _ hxn,
        show (g * h * σ) ⟨x, hxn⟩ = g ((h * σ) ⟨x, hxn⟩) by rw [mul_assoc]; rfl, hgfix _ hmem]
  obtain ⟨h, hh, i, hi, hpre⟩ := key base.length le_rfl
  rw [List.take_length] at hpre
  have hb := hnodes i hi
  have hlen : (nodes[i]!).pre.length = base.length := by rw [hpre, List.length_map]
  rw [hlen, ite_eq_right (lt_irrefl _)] at hb
  have hmap := colourT_map hnbr (hadm h hh).1 ht (hadm h hh).2 hbase K
  rw [← hpre] at hmap
  obtain ⟨k, hk, hkeq⟩ := leafOK_spec hnbr ht hacc hinj hb (hadm h hh).1 (hadm h hh).2 hmap
  exact ⟨h, hh, k, hk, hkeq⟩

end CFSG.Sporadic.FischerOddCore
