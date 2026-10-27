module

public import CFSG.Certificates.NativeInvariantMerge

public section

namespace CFSG.Quasithin

open CFSG.Certificates CFSG.Certificates.Native CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native

variable {n m : ℕ}

@[expose] def mergeTargetsOK (n : Nat) (G : Array (Array Nat)) (b x : Nat)
    (L : List (Nat × Nat × Nat)) (ts : List Nat) : Bool :=
  let st := L.foldl (mergeStep n G) (true, mergeInit n b x)
  decide (b < n) && decide (x < n) && st.1 &&
    ts.all fun t => decide (t < n) && st.2[t]! == st.2[b]!

@[expose] def ValidTargetMerge (S : Fin m → Equiv.Perm (Fin n)) (b x : Fin n)
    (L : List (Fin m × Fin n × Fin n)) (ts : List (Fin n)) : Prop :=
  (∀ (k : ℕ) (hk : k < L.length), mergeRel S b x L k (L[k]'hk).2.1 (L[k]'hk).2.2) ∧
    ∀ t ∈ ts, mergeRel S b x L L.length b t

theorem invariant_merge_targets_soundness (S : Fin m → Equiv.Perm (Fin n)) (b x : Fin n)
    (L : List (Fin m × Fin n × Fin n)) (ts : List (Fin n)) (hv : ValidTargetMerge S b x L ts)
    (R : Fin n → Fin n → Prop) (hR : Equivalence R)
    (hinv : ∀ i u v, R u v → R (S i u) (S i v)) (hbx : R b x) : ∀ t ∈ ts, R b t :=
  fun t ht => mergeRel_le hR hinv hbx L.length (fun l hl _ => hv.1 l hl) b t (hv.2 t ht)

section Native

variable {S : Fin m → Equiv.Perm (Fin n)} {G : Array (Array ℕ)}
  (hrep : ∀ i : Fin m, Rep n G[(i : ℕ)]! (S i)) {b x : Fin n} {L : List (Fin m × Fin n × Fin n)}
  {ts : List (Fin n)}
include hrep

theorem validTargetMerge_of_mergeTargetsOK
    (h : mergeTargetsOK n G b x (mergeVals L) (ts.map Fin.val) = true) :
    ValidTargetMerge S b x L ts := by
  simp only [mergeTargetsOK, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨-, -⟩, hflag⟩, hall⟩ := h
  have hlen : (mergeVals L).length = L.length := by simp [mergeVals]
  have hfin : mergeState n G b x (mergeVals L) L.length =
      (mergeVals L).foldl (mergeStep n G) (true, mergeInit n b x) := by
    rw [mergeState, List.take_of_length_le (by omega)]
  refine ⟨fun k hk => ?_, fun t ht => ?_⟩
  · have hf : (mergeState n G b x (mergeVals L) L.length).1 = true := by rw [hfin]; exact hflag
    exact mergeLabels_rel hrep k (by omega) _ _
      (mergeState_flag L.length le_rfl hf k hk hk)
  · apply mergeLabels_rel hrep L.length le_rfl
    rw [hfin]
    have := List.all_eq_true.1 hall (t : ℕ) (List.mem_map_of_mem ht)
    simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at this
    exact this.2.symm

end Native

end CFSG.Quasithin
