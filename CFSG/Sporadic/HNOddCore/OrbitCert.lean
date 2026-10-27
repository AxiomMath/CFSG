module

public import CFSG.Sporadic.HNOddCore.Restrict

public section

namespace CFSG.Sporadic.HNOddCore

open CFSG.ONSchreier CFSG.ONSchreier.Native

@[expose] def orbitCertOK (m : Nat) (gens : Array (Array Nat)) (L pos par lab : Array Nat) : Bool :=
  decide (0 < L.size) && pointsOK m L pos &&
    (allBelowN L.size fun k => k == 0 || (decide (par[k]! < k) && decide (lab[k]! < gens.size) &&
      (gens[lab[k]!]!)[L[par[k]!]!]! == L[k]!)) &&
    allBelowN L.size fun k => allBelowN gens.size fun s =>
      decide (pos[(gens[s]!)[L[k]!]!]! < L.size) &&
        L[pos[(gens[s]!)[L[k]!]!]!]! == (gens[s]!)[L[k]!]!

@[expose] def orbitRecs (gens : Array (Array Nat)) (L pos : Array Nat) : Array Nat × Array Nat :=
  Id.run do
  let mut par : Array Nat := Array.replicate L.size 0
  let mut lab : Array Nat := Array.replicate L.size 0
  let mut done : Array Bool := Array.replicate L.size false
  for j in [0:L.size] do
    for s in [0:gens.size] do
      let k := pos[(gens[s]!)[L[j]!]!]!
      if k < L.size && j < k && !done[k]! then
        done := done.set! k true
        par := par.set! k j
        lab := lab.set! k s
  return (par, lab)

variable {m : ℕ} {gens : Array (Array ℕ)} {σ : ℕ → Equiv.Perm (Fin m)}

theorem orbitCertOK_spec {L pos par lab : Array ℕ} (h : orbitCertOK m gens L pos par lab = true) :
    0 < L.size ∧ pointsOK m L pos = true ∧
    (∀ k < L.size, 0 < k → par[k]! < k ∧ lab[k]! < gens.size ∧
      (gens[lab[k]!]!)[L[par[k]!]!]! = L[k]!) ∧
    ∀ k < L.size, ∀ s < gens.size, pos[(gens[s]!)[L[k]!]!]! < L.size ∧
      L[pos[(gens[s]!)[L[k]!]!]!]! = (gens[s]!)[L[k]!]! := by
  unfold orbitCertOK at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h
  refine ⟨h1, h2, fun k hk hk0 => ?_, fun k hk s hs => ?_⟩
  · have := allBelowN_spec h3 hk
    simp only [Bool.or_eq_true, beq_iff_eq, Bool.and_eq_true, decide_eq_true_eq] at this
    rcases this with h0 | ⟨⟨ha, hb⟩, hc⟩
    · omega
    · exact ⟨ha, hb, hc⟩
  · have := allBelowN_spec (allBelowN_spec h4 hk) hs
    simpa only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] using this

theorem perm_preimage_of_image {S : Set (Fin m)} {g : Equiv.Perm (Fin m)}
    (h : ∀ x ∈ S, g x ∈ S) : ∀ x ∈ S, g⁻¹ x ∈ S := by
  have hpow : ∀ k : ℕ, ∀ x ∈ S, (g ^ k) x ∈ S := by
    intro k
    induction k with
    | zero => intro x hx; simpa using hx
    | succ k ih => intro x hx; rw [pow_succ', Equiv.Perm.mul_apply]; exact h _ (ih x hx)
  have h1 : g⁻¹ = g ^ (orderOf g - 1) := by
    rw [eq_comm, ← mul_eq_one_iff_eq_inv, ← pow_succ, Nat.sub_add_cancel (orderOf_pos g),
      pow_orderOf_eq_one]
  intro x hx
  rw [h1]
  exact hpow _ x hx

theorem orbit_eq_of_orbitCertOK {L pos par lab : Array ℕ}
    (hrep : ∀ s < gens.size, PRep m gens[s]! (σ s))
    (h : orbitCertOK m gens L pos par lab = true) :
    let hL := ptList_of_pointsOK (orbitCertOK_spec h).2.1
    MulAction.orbit (Subgroup.closure (Set.range fun s : Fin gens.size => σ s))
        (hL.pt ⟨0, (orbitCertOK_spec h).1⟩) =
      Set.range hL.pt := by
  intro hL
  obtain ⟨h0, hpts, htree, hcl⟩ := orbitCertOK_spec h
  set K := Subgroup.closure (Set.range fun s : Fin gens.size => σ s)
  apply Set.Subset.antisymm
  ·
    have hgen : ∀ s : Fin gens.size, ∀ x ∈ Set.range hL.pt, σ s x ∈ Set.range hL.pt := by
      rintro s _ ⟨k, rfl⟩
      obtain ⟨hlt, heq⟩ := hcl k k.2 s s.2
      refine ⟨⟨_, hlt⟩, Fin.ext ?_⟩
      have hr := hrep s s.2 (hL.pt k)
      rw [PtList.pt_val] at hr
      rw [PtList.pt_val, heq, hr]
    have hK : ∀ g ∈ K, ∀ x ∈ Set.range hL.pt, g x ∈ Set.range hL.pt := by
      intro g hg
      induction hg using Subgroup.closure_induction with
      | mem g hg =>
        obtain ⟨s, rfl⟩ := hg
        exact hgen s
      | one => intro x hx; exact hx
      | mul a b _ _ ha hb => intro x hx; exact ha _ (hb x hx)
      | inv a _ ha => exact perm_preimage_of_image ha
    rintro _ ⟨g, rfl⟩
    exact hK g g.2 _ ⟨_, rfl⟩
  ·
    rintro _ ⟨⟨k, hk⟩, rfl⟩
    induction k using Nat.strong_induction_on with
    | _ k ih =>
      rcases Nat.eq_zero_or_pos k with rfl | hk0
      · exact MulAction.mem_orbit_self _
      · obtain ⟨hp, hl, he⟩ := htree k hk hk0
        obtain ⟨g, hg⟩ := ih _ hp (lt_trans hp hk)
        have hg' : g • hL.pt ⟨0, h0⟩ = hL.pt ⟨par[k]!, lt_trans hp hk⟩ := hg
        have hσ : σ lab[k]! ∈ K := Subgroup.subset_closure ⟨⟨_, hl⟩, rfl⟩
        refine ⟨⟨σ lab[k]!, hσ⟩ * g, ?_⟩
        show (⟨σ lab[k]!, hσ⟩ * g) • hL.pt ⟨0, h0⟩ = hL.pt ⟨k, hk⟩
        rw [mul_smul, hg']
        apply Fin.ext
        show (σ lab[k]! (hL.pt ⟨par[k]!, lt_trans hp hk⟩) : ℕ) = (hL.pt ⟨k, hk⟩ : ℕ)
        have hr := hrep _ hl (hL.pt ⟨par[k]!, lt_trans hp hk⟩)
        rw [PtList.pt_val] at hr
        rw [← hr, PtList.pt_val, he]

end CFSG.Sporadic.HNOddCore
