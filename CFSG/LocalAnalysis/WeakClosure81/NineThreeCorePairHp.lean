module

public import CFSG.LocalAnalysis.WeakClosure81.NineThreeCorePairMem

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.CGT.Timmesfeld75 Subgroup
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G] {V T A K S X : Subgroup G} {p : ℕ} {g x : G}

private theorem nine3_pair_hp_list_prod_inv {W : Subgroup G}
    (hW : ∀ a ∈ W, ∀ b ∈ W, a * b = b * a) {ι : Type*}
    (l : List ι) (f : ι → G) (hf : ∀ x ∈ l, f x ∈ W) :
    ((l.map f).prod)⁻¹ = (l.map fun x => (f x)⁻¹).prod := by
  induction l with
  | nil => simp
  | cons x xs ih =>
      rw [List.map_cons, List.prod_cons, List.map_cons, List.prod_cons, mul_inv_rev]
      have hxW : f x ∈ W := hf x (by simp)
      have hP : (xs.map f).prod ∈ W := by
        apply Subgroup.list_prod_mem
        intro y hy
        obtain ⟨z, hz, rfl⟩ := List.mem_map.mp hy
        exact hf z (by simp [hz])
      rw [hW _ (W.inv_mem hP) _ (W.inv_mem hxW),
        ih (fun y hy => hf y (by simp [hy]))]

private theorem nine3_pair_hp_list_prod_reindex {W : Subgroup G}
    (hW : ∀ a ∈ W, ∀ b ∈ W, a * b = b * a) {m : ℕ} (τ : Equiv.Perm (Fin m))
    (f : Fin m → G) (hf : ∀ k, f k ∈ W) :
    ((List.finRange m).map fun l => f (τ l)).prod = ((List.finRange m).map f).prod := by
  have hperm : List.Perm ((List.finRange m).map (fun l => f (τ l)))
      ((List.finRange m).map f) := by
    have h := (Equiv.Perm.map_finRange_perm τ).map f
    rwa [List.map_map] at h
  refine List.Perm.prod_eq' hperm (List.pairwise_of_reflexive_of_forall_ne ?_)
  intro a ha b hb _
  obtain ⟨k, -, rfl⟩ := List.mem_map.mp ha
  obtain ⟨l, -, rfl⟩ := List.mem_map.mp hb
  exact hW _ (hf (τ k)) _ (hf (τ l))

theorem nine3_pair_hp (hc : Nine3Choice V T A K S X p g x)
    (hc' : Nine3Choice V T A K S X p g⁻¹ x) (hI : Nine3IFacts V K S)
    (h35 : Nat.card ↥(nineDelta V S) = 3 ∨ Nat.card ↥(nineDelta V S) = 5) {n : ℕ}
    {B : Fin (n + 1) → Subgroup G} {σ : Equiv.Perm (Fin (n + 1))} {bb : Fin (n + 1) → G}
    (he : Nine3PairEnum V K S A g n B σ bb) {i : G} (hi : i ∈ nineI V K) :
    ∃ π : Fin (n + 1) → Bool, ∀ j ∈ conjSubgroup (nineI V K) g, ⁅i, j⁆ =
      ((List.finRange (n + 1)).map
        fun l => if π l then ⁅g⁻¹ * bb (σ.symm l) * g, j⁆ else 1).prod := by
  classical
  have hc'' : Nine3Choice V T A K S X p g⁻¹⁻¹ x := by rw [inv_inv]; exact hc
  have hi' : g * i * g⁻¹ ∈ conjSubgroup (nineI V K) g⁻¹ := by
    rw [mem_conjSubgroup_iff]
    have h : g⁻¹ * (g * i * g⁻¹) * (g⁻¹)⁻¹ = i := by group
    rwa [h]
  obtain ⟨b, hbZ, ε, hε0, ⟨j₀, hj₀I, hb_eq⟩, hbH, hbI, hexp⟩ :=
    nine3_pair_hs hc' hc'' hI h35 he.Ω he.surj he.bb_mem he.bb0 (j := g * i * g⁻¹) hi'
  refine ⟨fun l => ε (σ.symm l), ?_⟩
  intro j hj
  let c : Fin (n + 1) → G := fun k => g⁻¹ * bb k * g
  let W : Subgroup G := nineW V S
  have hcommW : ∀ a ∈ W, ∀ b ∈ W, a * b = b * a :=
    fun a ha b hb => hc.core.nineW_mul_comm ha hb
  have hGW : ∀ k : Fin (n + 1), ⁅c k, j⁆ ∈ W := by
    intro k
    have h := nine3_pair_psi_mem hc hI he hj (σ k)
    rw [Equiv.symm_apply_apply] at h
    exact nine3_pair_P_le_W hc he.mem (σ k) h
  have hFW : ∀ k : Fin (n + 1), ⁅j, c k⁆ ∈ W := by
    intro k
    have h := W.inv_mem (hGW k)
    rwa [commutatorElement_inv] at h
  have hx : g * j * g⁻¹ ∈ nineI V K := mem_conjSubgroup_iff.mp hj
  have hxconj : MulAut.conj (g⁻¹) (g * j * g⁻¹) = j := by
    rw [MulAut.conj_apply, inv_inv]
    group
  have hyconj : MulAut.conj (g⁻¹) (g * i * g⁻¹) = i := by
    rw [MulAut.conj_apply, inv_inv]
    group
  have hcbb : ∀ k : Fin (n + 1), MulAut.conj (g⁻¹) (bb k) = c k := by
    intro k
    show MulAut.conj (g⁻¹) (bb k) = g⁻¹ * bb k * g
    rw [MulAut.conj_apply, inv_inv]
  have hpoint : ∀ k : Fin (n + 1),
      MulAut.conj (g⁻¹) (if ε k then ⁅g * j * g⁻¹, bb k⁆ else 1) =
        if ε k then ⁅j, c k⁆ else 1 := by
    intro k
    by_cases hε : ε k = true
    · rw [if_pos hε, if_pos hε, map_commutatorElement, hxconj, hcbb k]
    · rw [if_neg hε, if_neg hε, map_one]
  have h1 : ⁅j, i⁆ = ((List.finRange (n + 1)).map
      fun k => if ε k then ⁅j, c k⁆ else 1).prod := by
    have hkey := congrArg (fun z : G => (MulAut.conj (g⁻¹) : G ≃* G) z)
      (hexp (g * j * g⁻¹) hx)
    rw [map_commutatorElement, map_list_prod (MulAut.conj (g⁻¹)), hxconj, hyconj] at hkey
    have hlist : ((List.finRange (n + 1)).map
          (fun k => if ε k then ⁅g * j * g⁻¹, bb k⁆ else 1)).map (MulAut.conj (g⁻¹)) =
        (List.finRange (n + 1)).map (fun k => if ε k then ⁅j, c k⁆ else 1) := by
      rw [List.map_map]
      apply List.map_congr_left
      intro k _
      simpa only [Function.comp_apply] using hpoint k
    rw [hlist] at hkey
    exact hkey
  have hstep : ⁅i, j⁆ = (((List.finRange (n + 1)).map
      fun k => if ε k then ⁅j, c k⁆ else 1).prod)⁻¹ := by
    rw [← commutatorElement_inv (g₁ := j) (g₂ := i), h1]
  have hfW : ∀ k ∈ List.finRange (n + 1),
      (if ε k then ⁅j, c k⁆ else 1 : G) ∈ W := by
    intro k _
    by_cases hε : ε k = true
    · rw [if_pos hε]; exact hFW k
    · rw [if_neg hε]; exact W.one_mem
  have hgW : ∀ k : Fin (n + 1), (if ε k then ⁅c k, j⁆ else 1 : G) ∈ W := by
    intro k
    by_cases hε : ε k = true
    · rw [if_pos hε]; exact hGW k
    · rw [if_neg hε]; exact W.one_mem
  have hinv := nine3_pair_hp_list_prod_inv (W := W) hcommW (List.finRange (n + 1))
    (fun k => if ε k then ⁅j, c k⁆ else 1) hfW
  have hreindex := nine3_pair_hp_list_prod_reindex (W := W) hcommW σ.symm
    (fun k => if ε k then ⁅c k, j⁆ else 1) hgW
  have hpt : ∀ k : Fin (n + 1), (if ε k then ⁅j, c k⁆ else 1 : G)⁻¹ =
      if ε k then ⁅c k, j⁆ else 1 := by
    intro k
    by_cases hε : ε k = true <;> simp [hε, commutatorElement_inv]
  have hmap : (List.finRange (n + 1)).map
      (fun k => (if ε k then ⁅j, c k⁆ else 1 : G)⁻¹) =
      (List.finRange (n + 1)).map (fun k => if ε k then ⁅c k, j⁆ else 1) :=
    List.map_congr_left (fun k _ => hpt k)
  rw [hstep, hinv, hmap, ← hreindex]

end CFSG.LocalAnalysis.WeakClosure81
