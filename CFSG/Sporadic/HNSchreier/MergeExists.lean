module

public import CFSG.Certificates.NativeInvariantMerge
public import Mathlib.GroupTheory.GroupAction.Primitive
public import Mathlib.GroupTheory.Perm.Basic

public section

namespace CFSG.Sporadic.HNSchreier

open CFSG.Certificates
open scoped Pointwise

variable {n m : ℕ}

theorem mergeRel_append_of_le (S : Fin m → Equiv.Perm (Fin n)) (b x : Fin n)
    (L : List (Fin m × Fin n × Fin n)) (t : Fin m × Fin n × Fin n) :
    ∀ k ≤ L.length, mergeRel S b x (L ++ [t]) k = mergeRel S b x L k
  | 0, _ => rfl
  | k + 1, hk => by
    have ih := mergeRel_append_of_le S b x L t k (by omega)
    have hget : (L ++ [t])[k]? = L[k]? := List.getElem?_append_left (by omega)
    simp only [mergeRel, hget, ih]

theorem mergeRel_append_last (S : Fin m → Equiv.Perm (Fin n)) (b x : Fin n)
    (L : List (Fin m × Fin n × Fin n)) (t : Fin m × Fin n × Fin n) :
    mergeRel S b x (L ++ [t]) (L.length + 1) = Relation.EqvGen fun a c =>
      mergeRel S b x L L.length a c ∨ (a = S t.1 t.2.1 ∧ c = S t.1 t.2.2) := by
  have hget : (L ++ [t])[L.length]? = some t := by simp
  rw [mergeRel, hget, mergeRel_append_of_le S b x L t L.length le_rfl]

open Classical in
noncomputable def relCount (R : Fin n → Fin n → Prop) : ℕ :=
  (Finset.univ.filter fun p : Fin n × Fin n => R p.1 p.2).card

theorem relCount_le (R : Fin n → Fin n → Prop) : relCount R ≤ n * n := by
  classical
  unfold relCount
  calc _ ≤ (Finset.univ : Finset (Fin n × Fin n)).card := Finset.card_filter_le _ _
    _ = n * n := by simp

theorem relCount_lt {R R' : Fin n → Fin n → Prop} (h : ∀ a c, R a c → R' a c) {u v : Fin n}
    (huv : R' u v) (hn : ¬ R u v) : relCount R < relCount R' := by
  classical
  unfold relCount
  apply Finset.card_lt_card
  refine ⟨fun p hp => ?_, fun hsub => ?_⟩
  · simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp ⊢
    exact h _ _ hp
  · have : (u, v) ∈ Finset.univ.filter fun p : Fin n × Fin n => R p.1 p.2 :=
      hsub (by simp [huv])
    simp at this
    exact hn this

def StepsValid (S : Fin m → Equiv.Perm (Fin n)) (b x : Fin n)
    (L : List (Fin m × Fin n × Fin n)) : Prop :=
  ∀ (k : ℕ) (hk : k < L.length), mergeRel S b x L k (L[k]'hk).2.1 (L[k]'hk).2.2

theorem exists_validInvariantMerge (S : Fin m → Equiv.Perm (Fin n)) (b x : Fin n)
    (h : ∀ R : Fin n → Fin n → Prop, Equivalence R → (∀ i u v, R u v → R (S i u) (S i v)) →
      R b x → ∀ u v, R u v) :
    ∃ L, ValidInvariantMerge S b x L := by
  classical
  suffices key : ∀ N, ∀ L, StepsValid S b x L → n * n - relCount (mergeRel S b x L L.length) ≤ N →
      ∃ L', ValidInvariantMerge S b x L' by
    exact key _ [] (fun k hk => absurd hk (by simp)) le_rfl
  intro N
  induction N with
  | zero =>
    intro L hL hN
    refine ⟨L, hL, fun a c => ?_⟩
    by_contra hac
    have hlt := relCount_lt (R := mergeRel S b x L L.length)
      (R' := fun _ _ => True) (fun _ _ _ => trivial) (u := a) (v := c) trivial hac
    have : relCount (fun _ _ : Fin n => True) ≤ n * n := relCount_le _
    omega
  | succ N ih =>
    intro L hL hN
    by_cases huniv : ∀ a c, mergeRel S b x L L.length a c
    · exact ⟨L, hL, huniv⟩
    ·
      have hR := mergeRel_equivalence S b x L L.length
      have hbx : mergeRel S b x L L.length b x := by
        have h0 : mergeRel S b x L 0 b x := Relation.EqvGen.rel _ _ ⟨rfl, rfl⟩
        have mono : ∀ k, mergeRel S b x L 0 b x → mergeRel S b x L k b x := by
          intro k
          induction k with
          | zero => exact id
          | succ k ihk =>
            intro h0
            exact CFSG.Certificates.mergeRel_mono (ihk h0)
        exact mono _ h0
      have hninv : ¬ ∀ i u v, mergeRel S b x L L.length u v →
          mergeRel S b x L L.length (S i u) (S i v) := fun hinv =>
        huniv (h _ hR hinv hbx)
      push Not at hninv
      obtain ⟨i, u, v, huv, hn⟩ := hninv
      let L' := L ++ [(i, u, v)]
      have hL' : StepsValid S b x L' := by
        intro k hk
        simp only [L', List.length_append, List.length_singleton] at hk
        rcases Nat.lt_or_ge k L.length with hkl | hkl
        · rw [mergeRel_append_of_le S b x L _ k hkl.le]
          have := hL k hkl
          simpa [L', List.getElem_append_left hkl] using this
        · have hk' : k = L.length := by omega
          subst hk'
          rw [mergeRel_append_of_le S b x L _ L.length le_rfl]
          simpa [L'] using huv
      have hsub : ∀ a c, mergeRel S b x L L.length a c → mergeRel S b x L' L'.length a c := by
        intro a c hac
        have : L'.length = L.length + 1 := by simp [L']
        rw [this, mergeRel_append_last]
        exact Relation.EqvGen.rel _ _ (Or.inl hac)
      have hnew : mergeRel S b x L' L'.length (S i u) (S i v) := by
        have : L'.length = L.length + 1 := by simp [L']
        rw [this, mergeRel_append_last]
        exact Relation.EqvGen.rel _ _ (Or.inr ⟨rfl, rfl⟩)
      have hlt := relCount_lt hsub hnew hn
      have hle := relCount_le (mergeRel S b x L' L'.length)
      exact ih L' hL' (by omega)

theorem exists_validInvariantMerge_of_preprimitive (S : Fin m → Equiv.Perm (Fin n))
    [hprim : MulAction.IsPreprimitive (Subgroup.closure (Set.range S)) (Fin n)] (b x : Fin n)
    (hxb : x ≠ b) : ∃ L, ValidInvariantMerge S b x L := by
  classical
  apply exists_validInvariantMerge
  intro R hR hinv hbx u v
  set P := Subgroup.closure (Set.range S)
  have hinvS : ∀ i, ∀ a c, R a c ↔ R (S i a) (S i c) := by
    intro i a c
    refine ⟨hinv i a c, fun h => ?_⟩
    have hinj : Function.Injective fun p : {p : Fin n × Fin n // R p.1 p.2} =>
        (⟨(S i p.1.1, S i p.1.2), hinv i _ _ p.2⟩ : {p : Fin n × Fin n // R p.1 p.2}) := by
      intro p q hpq
      have := congrArg (fun r : {p : Fin n × Fin n // R p.1 p.2} => r.1) hpq
      simp only [Prod.mk.injEq] at this
      exact Subtype.ext (Prod.ext ((S i).injective this.1) ((S i).injective this.2))
    obtain ⟨p, hp⟩ := (Finite.injective_iff_surjective.1 hinj) ⟨(S i a, S i c), h⟩
    have := congrArg (fun r : {p : Fin n × Fin n // R p.1 p.2} => r.1) hp
    simp only [Prod.mk.injEq] at this
    rw [← (S i).injective this.1, ← (S i).injective this.2]
    exact p.2
  have hinvP : ∀ g ∈ P, ∀ a c, R a c ↔ R (g a) (g c) := by
    intro g hg
    induction hg using Subgroup.closure_induction with
    | mem g hg =>
      obtain ⟨i, rfl⟩ := hg
      exact hinvS i
    | one => intro a c; rfl
    | mul g h _ _ hg hh => intro a c; rw [hh, hg]; rfl
    | inv g _ hg =>
      intro a c
      rw [hg (g⁻¹ a) (g⁻¹ c)]
      simp
  let B : Set (Fin n) := {y | R b y}
  have hblock : MulAction.IsBlock P B := by
    rw [MulAction.isBlock_iff_smul_eq_or_disjoint]
    intro g
    by_cases hd : Disjoint (g • B) B
    · exact Or.inr hd
    · left
      obtain ⟨y, hy1, hy2⟩ := Set.not_disjoint_iff.1 hd
      obtain ⟨z, hz, rfl⟩ := hy1
      have hgz : R b ((g : Equiv.Perm (Fin n)) z) := hy2
      ext w
      constructor
      · rintro ⟨w', hw', rfl⟩
        have h1 : R ((g : Equiv.Perm (Fin n)) b) ((g : Equiv.Perm (Fin n)) w') :=
          (hinvP g g.2 b w').1 hw'
        have h2 : R ((g : Equiv.Perm (Fin n)) b) ((g : Equiv.Perm (Fin n)) z) :=
          (hinvP g g.2 b z).1 hz
        exact hR.trans hgz (hR.trans (hR.symm h2) h1)
      · intro hw
        refine ⟨(g : Equiv.Perm (Fin n))⁻¹ w, ?_, by simp [Subgroup.smul_def]⟩
        have h1 := (hinvP g⁻¹ (inv_mem g.2) b w).1 hw
        have h2 := (hinvP g⁻¹ (inv_mem g.2) b ((g : Equiv.Perm (Fin n)) z)).1 hgz
        simp only [Equiv.Perm.coe_inv, Equiv.symm_apply_apply] at h1 h2
        show R b ((g : Equiv.Perm (Fin n))⁻¹ w)
        have h3 : R ((g : Equiv.Perm (Fin n))⁻¹ b) z := h2
        exact hR.trans (hR.symm (hR.trans h3 (hR.symm hz))) h1
  rcases hprim.isTrivialBlock_of_isBlock hblock with hsub | huniv
  · exact absurd (hsub (show R b b from hR.refl b) hbx) hxb.symm
  · have hu : R b u := by
      have : u ∈ B := by rw [huniv]; trivial
      exact this
    have hv : R b v := by
      have : v ∈ B := by rw [huniv]; trivial
      exact this
    exact hR.trans (hR.symm hu) hv

end CFSG.Sporadic.HNSchreier
