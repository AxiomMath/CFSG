module

public import CFSG.Quasithin.Recognition.GoldschmidtFan86TutteRedWalk
public import CFSG.Quasithin.Background.GoldschmidtAmalgamL3TSlide
public import CFSG.Quasithin.Recognition.GoldschmidtFan86TutteRedArc

public section

namespace CFSG.Quasithin.Fan86.Tutte.Red

open CFSG.Quasithin.F6.GoldAmL3T

variable {W : Type} {Γ : SimpleGraph W} {H : Type} [Group H] [MulAction H W]

@[expose] def ArcTrans (H : Type) [Group H] [MulAction H W] (Γ : SimpleGraph W) (s : ℕ) : Prop :=
  ∀ P Q : Arc Γ s, ∃ h : H, ∀ i, i ≤ s → h • P.vert i = Q.vert i

theorem exists_moving (hcard : ∀ w, Nat.card (Γ.neighborSet w) = 3) {ω : ℕ → W}
    (hω : ∀ i, Γ.Adj (ω i) (ω (i + 1))) (hω' : ∀ i, ω i ≠ ω (i + 2)) {k : ℕ} (hk : 1 ≤ k)
    (ht : ArcTrans H Γ (k + 1)) :
    ∃ g ∈ (walkArc ω hω hω' k).stab H, g ∉ (walkArc ω hω hω' (k + 1)).stab H := by
  have hadj : Γ.Adj (ω k) (ω (k - 1)) := by
    have := (hω (k - 1)).symm
    rwa [show k - 1 + 1 = k by omega] at this
  obtain ⟨a, b, hab, ha, hay, hb, hby, hall⟩ := exists_two_others (hcard (ω k)) hadj
  have hnext : Γ.Adj (ω k) (ω (k + 1)) := hω k
  have hnext' : ω (k + 1) ≠ ω (k - 1) := by
    have h := hω' (k - 1)
    rw [show k - 1 + 2 = k + 1 by omega] at h
    exact h.symm
  obtain ⟨w, hw, hwy, hwn⟩ : ∃ w, Γ.Adj (ω k) w ∧ w ≠ ω (k - 1) ∧ w ≠ ω (k + 1) := by
    rcases hall _ hnext hnext' with h | h
    · exact ⟨b, hb, hby, fun e => hab (h.symm.trans e.symm)⟩
    · exact ⟨a, ha, hay, fun e => hab (e.trans h)⟩
  let Q := snocArc (walkArc ω hω hω' k) w hw (fun _ => hwy)
  obtain ⟨g, hg⟩ := ht (walkArc ω hω hω' (k + 1)) Q
  have hQlt : ∀ i, i ≤ k → Q.vert i = ω i := fun i hi => snocArc_vert_le _ w hw _ hi
  have hQlast : Q.vert (k + 1) = w := snocArc_vert_last _ w hw _
  refine ⟨g, (Arc.mem_stab H).2 fun i hi => ?_, fun hmem => ?_⟩
  · have := hg i (by omega)
    rwa [hQlt i hi] at this
  · have h1 := (Arc.mem_stab H).1 hmem (k + 1) le_rfl
    have h2 := hg (k + 1) le_rfl
    rw [hQlast] at h2
    exact hwn (h2.symm.trans h1)

theorem not_arcTrans_all (hcard : ∀ w, Nat.card (Γ.neighborSet w) = 3)
    (hfin : ∀ w : W, Finite (MulAction.stabilizer H w)) (hex : ∃ u v, Γ.Adj u v) :
    ¬ ∀ k, 1 ≤ k → ArcTrans H Γ k := by
  intro hall
  obtain ⟨u, v, huv⟩ := hex
  obtain ⟨ω, -, -, hω, hω'⟩ := exists_walk (fun a b hab => exists_other (hcard a) hab) huv
  let S : ℕ → Subgroup H := fun k => (walkArc ω hω hω' k).stab H
  have hmem : ∀ k g, g ∈ S k ↔ ∀ i, i ≤ k → g • ω i = ω i := fun k g => Arc.mem_stab H
  have hfinS : ∀ k, (S k : Set H).Finite := fun k => by
    have := hfin (ω 0)
    refine (Set.toFinite (MulAction.stabilizer H (ω 0) : Set H)).subset fun g hg => ?_
    exact (hmem k g).1 hg 0 (Nat.zero_le _)
  have hsub : ∀ k, (S (k + 1) : Set H) ⊆ S k := fun k g hg =>
    (hmem k g).2 fun i hi => (hmem (k + 1) g).1 hg i (by omega)
  have hlt : ∀ n, Set.ncard (S (n + 1 + 1) : Set H) < Set.ncard (S (n + 1) : Set H) := fun n => by
    obtain ⟨g, hg, hg'⟩ := exists_moving (H := H) hcard hω hω' (k := n + 1) (by omega)
      (hall (n + 1 + 1) (by omega))
    refine Set.ncard_lt_ncard (Set.ssubset_iff_subset_ne.2 ⟨hsub (n + 1), fun e => hg' ?_⟩)
      (hfinS (n + 1))
    have : g ∈ (S (n + 1 + 1) : Set H) := e ▸ hg
    exact this
  have hbound : ∀ n, Set.ncard (S (n + 1) : Set H) + n ≤ Set.ncard (S 1 : Set H) := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      have := hlt n
      omega
  have hpos : 0 < Set.ncard (S (Set.ncard (S 1 : Set H) + 1) : Set H) :=
    Set.ncard_pos (hfinS _) |>.2 ⟨1, (S _).one_mem⟩
  have := hbound (Set.ncard (S 1 : Set H))
  omega

end CFSG.Quasithin.Fan86.Tutte.Red
