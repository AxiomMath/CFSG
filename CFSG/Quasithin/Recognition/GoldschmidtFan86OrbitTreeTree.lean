module

public import CFSG.Quasithin.Recognition.GoldschmidtFan86OrbitTreeArc

public section

namespace CFSG.Quasithin.Fan86

open SimpleGraph CFSG.Quasithin.F6.GoldAmL3T

variable {V : Type*} {Γ : SimpleGraph V} {A : Set V}

theorem orbitGraph_connected (hconn : OrbitConn Γ A) (hne : A.Nonempty) :
    (orbitGraph Γ A).Connected := by
  obtain ⟨u₀, hu₀⟩ := hne
  let S : Set V := {u | ∃ hu : u ∈ A, (orbitGraph Γ A).Reachable ⟨u₀, hu₀⟩ ⟨u, hu⟩}
  have hS : S = A := by
    refine hconn S (fun u hu => hu.1) ⟨u₀, hu₀, Reachable.refl _⟩ ?_
    rintro u ⟨hu, hr⟩ u' hu' ⟨hne, w, hw', hw⟩
    exact ⟨hu', hr.trans (Adj.reachable (show (orbitGraph Γ A).Adj ⟨u, hu⟩ ⟨u', hu'⟩ from
      ⟨hne.symm, w, hw, hw'⟩))⟩
  have key : ∀ v : ↥A, (orbitGraph Γ A).Reachable ⟨u₀, hu₀⟩ v := by
    intro v
    have hv : v.1 ∈ S := by
      rw [hS]
      exact v.2
    exact hv.2
  exact (connected_iff _).2 ⟨fun a b => (key a).symm.trans (key b), ⟨⟨u₀, hu₀⟩⟩⟩

theorem getVert_ne_add_two_of_isCycle {W : Type*} {Δ : SimpleGraph W} {u : W} {c : Δ.Walk u u}
    (hc : c.IsCycle) {i : ℕ} (hi : i + 2 ≤ c.length) : c.getVert i ≠ c.getVert (i + 2) := by
  have h3 := hc.three_le_length
  have hinj := hc.getVert_injOn
  by_cases h0 : i = 0
  · subst h0
    intro h
    rw [Walk.getVert_zero] at h
    have h2 : c.getVert 2 = c.getVert c.length := by
      rw [Walk.getVert_length]
      exact h.symm
    have := hinj (show 2 ∈ {i | 1 ≤ i ∧ i ≤ c.length} by simp; omega)
      (show c.length ∈ {i | 1 ≤ i ∧ i ≤ c.length} by simp; omega) h2
    omega
  · intro h
    have := hinj (show i ∈ {i | 1 ≤ i ∧ i ≤ c.length} by simp; omega)
      (show i + 2 ∈ {i | 1 ≤ i ∧ i ≤ c.length} by simp; omega) h
    omega

theorem orbitGraph_acyclic (hT : Γ.IsTree) (hP : OrbitPartner Γ A) :
    (orbitGraph Γ A).IsAcyclic := by
  intro v c hc
  let Q : Arc (orbitGraph Γ A) c.length :=
    { vert := fun i => c.getVert i
      adj := fun i hi => c.adj_getVert_succ hi
      nb := fun i hi => getVert_ne_add_two_of_isCycle hc hi }
  have h := Arc.dist_eq hT (hP.liftArc Q) (2 * c.length) le_rfl
  have h0 : (hP.liftArc Q).vert 0 = v.1 := by
    have h' := hP.liftArc_vert_even Q 0
    rw [mul_zero] at h'
    rw [h']
    show (c.getVert 0).1 = v.1
    rw [Walk.getVert_zero]
  have h1 : (hP.liftArc Q).vert (2 * c.length) = v.1 := by
    rw [hP.liftArc_vert_even Q c.length]
    show (c.getVert c.length).1 = v.1
    rw [Walk.getVert_length]
  rw [h0, h1, dist_self] at h
  have := hc.three_le_length
  omega

theorem orbitGraph_isTree (hT : Γ.IsTree) (hP : OrbitPartner Γ A) (hconn : OrbitConn Γ A)
    (hne : A.Nonempty) : (orbitGraph Γ A).IsTree :=
  ⟨orbitGraph_connected hconn hne, orbitGraph_acyclic hT hP⟩

end CFSG.Quasithin.Fan86
