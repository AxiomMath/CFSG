module

public import CFSG.Sporadic.Schreier.ONCompactSpec
public import CFSG.Sporadic.Th.OrbitSpec

public section

namespace CFSG.Sporadic.ONOddCore

open CFSG.ONSchreier CFSG.ONSchreier.Native

variable {n : ℕ} {root : ℕ} {steps : Array (Array ℕ)} {L : CLevel}
  {gens : List (Equiv.Perm (Fin n))}

theorem getD_mem_list {α : Type*} {l : List α} {j : ℕ} (hj : j < l.length) (d : α) :
    l.getD j d ∈ l := by
  rw [List.getD_eq_getElem _ _ hj]
  exact List.getElem_mem hj

theorem smul_perm_subgroup (K : Subgroup (Equiv.Perm (Fin n))) (g : K) (x : Fin n) :
    g • x = (g : Equiv.Perm (Fin n)) x := rfl

theorem tree_mem_orbit (hL : CLevelFacts n root steps L)
    (hS : ∀ j < steps.size, PRep n steps[j]! (gens.getD j 1)) (hlen : steps.size = gens.length)
    (hr : root < n) :
    ∀ k < L.pts.size, ∃ g ∈ Subgroup.closure {g | g ∈ gens},
      ((g ⟨root, hr⟩ : Fin n) : ℕ) = L.pts[k]! := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro hk
    by_cases hk0 : k = 0
    · subst hk0
      exact ⟨1, one_mem _, by rw [hL.root]; rfl⟩
    · have hpos : 0 < k := Nat.pos_of_ne_zero hk0
      have hp := hL.par_lt k hk hpos
      obtain ⟨g, hg, hgr⟩ := ih _ hp (by omega)
      have hl := hL.lab_lt k hk hpos
      refine ⟨gens.getD (L.lab[k]!) 1 * g, mul_mem (Subgroup.subset_closure ?_) hg, ?_⟩
      · exact getD_mem_list (by rw [← hlen]; exact hl) 1
      · rw [Equiv.Perm.mul_apply, ← hS _ hl (g ⟨root, hr⟩), hgr, hL.edge k hk hpos]

theorem tree_closed (hL : CLevelFacts n root steps L)
    (hS : ∀ j < steps.size, PRep n steps[j]! (gens.getD j 1)) {z : Fin n}
    (hz : L.pos[(z : ℕ)]! < L.pts.size) {j : ℕ} (hj : j < steps.size) :
    L.pos[((gens.getD j 1 z : Fin n) : ℕ)]! < L.pts.size := by
  have h := (hL.closed _ hz j hj).1
  rw [hL.pts_pos z z.isLt hz, hS j hj z] at h
  exact h

theorem mem_orbit_iff_tree (hL : CLevelFacts n root steps L)
    (hS : ∀ j < steps.size, PRep n steps[j]! (gens.getD j 1)) (hlen : steps.size = gens.length)
    (hr : root < n) (z : Fin n) :
    z ∈ MulAction.orbit (Subgroup.closure {g | g ∈ gens}) (⟨root, hr⟩ : Fin n) ↔
      L.pos[(z : ℕ)]! < L.pts.size := by
  set K := Subgroup.closure {g | g ∈ gens}
  set T : Set (Fin n) := {y | L.pos[(y : ℕ)]! < L.pts.size}
  have hinv : ∀ g ∈ K, ∀ y ∈ T, g y ∈ T := by
    intro g hg
    induction hg using Subgroup.closure_induction with
    | mem g hg =>
      obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hg
      intro y hy
      have e : gens[j] = gens.getD j 1 := (List.getD_eq_getElem _ _ hj).symm
      rw [e]
      exact tree_closed hL hS hy (by rw [hlen]; exact hj)
    | one => exact fun y hy => hy
    | mul g h _ _ hg hh => exact fun y hy => hg _ (hh y hy)
    | inv g _ hg =>
      exact CFSG.Sporadic.Th.inv_smul_mem_of_subset_of_finite (G := Equiv.Perm (Fin n))
        (Set.toFinite T) hg
  have hroot : (⟨root, hr⟩ : Fin n) ∈ T := by
    show L.pos[root]! < L.pts.size
    have := hL.pos_pts 0 hL.pos
    rw [hL.root] at this
    rw [this]
    exact hL.pos
  constructor
  · rintro ⟨g, rfl⟩
    exact hinv g g.2 _ hroot
  · intro hz
    obtain ⟨g, hg, hgr⟩ := tree_mem_orbit hL hS hlen hr _ hz
    refine ⟨⟨g, hg⟩, Fin.ext ?_⟩
    show ((g ⟨root, hr⟩ : Fin n) : ℕ) = z
    rw [hgr, hL.pts_pos z z.isLt hz]

theorem card_orbit_tree (hL : CLevelFacts n root steps L)
    (hS : ∀ j < steps.size, PRep n steps[j]! (gens.getD j 1)) (hlen : steps.size = gens.length)
    (hr : root < n) :
    Nat.card (MulAction.orbit (Subgroup.closure {g | g ∈ gens}) (⟨root, hr⟩ : Fin n)) =
      L.pts.size := by
  have hset : MulAction.orbit (Subgroup.closure {g | g ∈ gens}) (⟨root, hr⟩ : Fin n) =
      {y : Fin n | L.pos[(y : ℕ)]! < L.pts.size} :=
    Set.ext fun z => mem_orbit_iff_tree hL hS hlen hr z
  rw [hset]
  have e : Fin L.pts.size ≃ {y : Fin n | L.pos[(y : ℕ)]! < L.pts.size} :=
    { toFun := fun k => ⟨⟨L.pts[(k : ℕ)]!, hL.pts_lt k k.isLt⟩, by
        show L.pos[L.pts[(k : ℕ)]!]! < L.pts.size
        rw [hL.pos_pts k k.isLt]
        exact k.isLt⟩
      invFun := fun z => ⟨L.pos[((z : Fin n) : ℕ)]!, z.2⟩
      left_inv := fun k => Fin.ext (hL.pos_pts k k.isLt)
      right_inv := fun z => Subtype.ext (Fin.ext (hL.pts_pos _ (z : Fin n).isLt z.2)) }
  rw [← Nat.card_congr e, Nat.card_fin]

theorem le_of_mem_orbit_tree (hL : CLevelFacts n root steps L)
    (hS : ∀ j < steps.size, PRep n steps[j]! (gens.getD j 1)) (hlen : steps.size = gens.length)
    (hr : root < n) (hmin : ∀ k < L.pts.size, root ≤ L.pts[k]!) {y : Fin n}
    (hy : y ∈ MulAction.orbit (Subgroup.closure {g | g ∈ gens}) (⟨root, hr⟩ : Fin n)) :
    root ≤ y := by
  have h := (mem_orbit_iff_tree hL hS hlen hr y).1 hy
  have := hmin _ h
  rwa [hL.pts_pos y y.isLt h] at this

end CFSG.Sporadic.ONOddCore
