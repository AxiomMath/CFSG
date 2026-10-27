module

public import CFSG.Milestones.ASVolI.F48.Rest.PermCheck
public import CFSG.Sporadic.HNOddCore.SixB
public import CFSG.Milestones.ASVolI.F48.Small.Pres

public section

namespace CFSG.ASVolI

open CFSG.ONSchreier CFSG.ONSchreier.Native

section Words

variable {N n : ℕ}

@[expose] def burnsideF48t_RecL (N : ℕ) (L Li : Array (Array ℕ)) (σ : Fin n → Equiv.Perm (Fin N)) :
    Prop :=
  ∀ i : Fin n, PRep N L[(i : ℕ)]! (σ i) ∧ PRep N Li[(i : ℕ)]! (σ i)⁻¹

theorem burnsideF48t_prep_evA {L Li : Array (Array ℕ)} {σ : Fin n → Equiv.Perm (Fin N)}
    (h : burnsideF48t_RecL N L Li σ) (w : List (Fin n × Bool)) :
    PRep N (burnsideF48t_evA N L Li w) (burnsideF48s_ev σ w) := by
  induction w with
  | nil => exact prep_pid
  | cons l w ih =>
    rw [burnsideF48t_evA, burnsideF48s_ev_cons]
    refine prep_pcomp ?_ ih
    obtain ⟨i, b⟩ := l
    cases b
    · exact (h i).2
    · exact (h i).1

theorem burnsideF48t_ev_eq_one_of {L Li : Array (Array ℕ)} {σ : Fin n → Equiv.Perm (Fin N)}
    (h : burnsideF48t_RecL N L Li σ) {w : List (Fin n × Bool)}
    (hw : peq N (burnsideF48t_evA N L Li w) (pid N) = true) : burnsideF48s_ev σ w = 1 :=
  eq_of_peq (burnsideF48t_prep_evA h w) prep_pid hw

end Words

section Closed

variable {N : ℕ}

@[expose] def burnsideF48t_arr (σ : Equiv.Perm (Fin N)) : Array ℕ :=
  Array.ofFn fun i : Fin N => (σ i : ℕ)

theorem burnsideF48t_prep_arr (σ : Equiv.Perm (Fin N)) : PRep N (burnsideF48t_arr σ) σ := fun x => by
  rw [burnsideF48t_arr, getElem!_ofFn_nat _ x.2]

theorem burnsideF48t_pcomp_arr {t u : Array ℕ} {σ τ : Equiv.Perm (Fin N)} (ht : PRep N t σ)
    (hu : PRep N u τ) : pcomp N t u = burnsideF48t_arr (σ * τ) := by
  have h := prep_pcomp ht hu
  rw [pcomp, burnsideF48t_arr]
  congr 1
  funext i
  have := h i
  rw [pcomp_get i.2] at this
  exact this

theorem burnsideF48t_pid_arr : pid N = burnsideF48t_arr (1 : Equiv.Perm (Fin N)) := by
  rw [pid, burnsideF48t_arr]
  rfl

end Closed

section Checks

open CFSG.Sporadic.HNOddCore CFSG.Monster.B.Co2.Native CFSG.Certificates.Native

variable {N : ℕ}

theorem burnsideF48t_mem_of_sift (hn : 1 ≤ N) {O : Array (Array ℕ)} {W : Array (List ℤ)}
    {b : List (Fin N)} {sizes : List ℕ} (hb : b.Nodup) (hc : chainCheck N O W b sizes = true)
    {t : Array ℕ} {g : Equiv.Perm (Fin N)} (ht : CFSG.ONSchreier.PRep N t g)
    (hs : burnsideF48t_sift N (burnsideF48t_levels N O W b) b t = true) : g ∈ arrGen N O :=
  (mem_arrGen_iff_sift hn hb hc ht).1 hs

theorem burnsideF48t_sift_of_mem (hn : 1 ≤ N) {O : Array (Array ℕ)} {W : Array (List ℤ)}
    {b : List (Fin N)} {sizes : List ℕ} (hb : b.Nodup) (hc : chainCheck N O W b sizes = true)
    {t : Array ℕ} {g : Equiv.Perm (Fin N)} (ht : CFSG.ONSchreier.PRep N t g) (hg : g ∈ arrGen N O) :
    burnsideF48t_sift N (burnsideF48t_levels N O W b) b t = true :=
  (mem_arrGen_iff_sift hn hb hc ht).2 hg

theorem burnsideF48t_preserves {m : ℕ} {gens : Array (Array ℕ)} {σ : ℕ → Equiv.Perm (Fin m)}
    (hrep : ∀ s < gens.size, CFSG.ONSchreier.PRep m gens[s]! (σ s)) {S : Set (Fin m)}
    (hS : ∀ s < gens.size, ∀ x ∈ S, σ s x ∈ S) :
    ∀ g ∈ Subgroup.closure (Set.range fun s : Fin gens.size => σ s), ∀ x ∈ S, g x ∈ S := by
  intro g hg
  induction hg using Subgroup.closure_induction with
  | mem g hg =>
    obtain ⟨s, rfl⟩ := hg
    exact hS s s.2
  | one => intro x hx; exact hx
  | mul a b _ _ ha hb => intro x hx; exact ha _ (hb x hx)
  | inv a _ ha => exact perm_preimage_of_image ha

end Checks

end CFSG.ASVolI
