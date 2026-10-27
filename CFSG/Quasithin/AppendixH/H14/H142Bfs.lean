module

public import CFSG.Milestones.ASVolI.H13

public section

namespace CFSG.Quasithin.AppendixH.H14

open CFSG.Quasithin.H.Mathieu CFSG.ASVolI.ChH CFSG.Monster.Code
open scoped Pointwise

@[expose] def maskSetOf (m : ℕ) : Finset (Fin 24) :=
  Finset.univ.filter fun i => m.testBit i = true

theorem mem_maskSetOf (m : ℕ) (i : Fin 24) : i ∈ maskSetOf m ↔ m.testBit i = true := by
  simp [maskSetOf]

theorem smul_maskSetOf {σ : Equiv.Perm (Fin 24)} {a : Array ℕ} (hσ : HasArr σ a) (m : ℕ) :
    σ • maskSetOf m = maskSetOf (permM a m) := by
  ext j
  rw [← Finset.inv_smul_mem_iff, Equiv.Perm.smul_def, mem_maskSetOf, mem_maskSetOf,
    ← bvec_ne_zero_iff, ← bvec_ne_zero_iff, ← permWord_bvec hσ]
  exact Iff.rfl

theorem maskSetOf_inj {m m' : ℕ} (hm : m < 2 ^ 24) (hm' : m' < 2 ^ 24)
    (h : maskSetOf m = maskSetOf m') : m = m' := by
  refine Nat.eq_of_testBit_eq fun i => ?_
  by_cases hi : i < 24
  · have := congrArg (fun S => (⟨i, hi⟩ : Fin 24) ∈ S) h
    simpa [mem_maskSetOf] using this
  · rw [Nat.testBit_eq_false_of_lt (hm.trans_le (Nat.pow_le_pow_right (by norm_num) (by omega))),
      Nat.testBit_eq_false_of_lt (hm'.trans_le (Nat.pow_le_pow_right (by norm_num) (by omega)))]

@[expose] def bfsOKg (gens : List (Array ℕ)) (m₀ : ℕ) (L : List (ℕ × ℕ × ℕ)) : Bool :=
  (List.range L.length).all fun k =>
    if k = 0 then (L.getD 0 (0, 0, 0)).1 == m₀ else
      decide ((L.getD k (0, 0, 0)).2.2 < k) && decide ((L.getD k (0, 0, 0)).2.1 < gens.length) &&
        (L.getD k (0, 0, 0)).1 == permM (gens.getD (L.getD k (0, 0, 0)).2.1 #[])
          (L.getD (L.getD k (0, 0, 0)).2.2 (0, 0, 0)).1

theorem mem_orbit_of_bfsg {G : Subgroup S24} {gens : List (Array ℕ)}
    (hg : ∀ a ∈ gens, ∃ σ ∈ G, HasArr σ a) {m₀ : ℕ} {L : List (ℕ × ℕ × ℕ)}
    (hL : bfsOKg gens m₀ L = true) :
    ∀ k < L.length, maskSetOf (L.getD k (0, 0, 0)).1 ∈ MulAction.orbit ↥G (maskSetOf m₀) := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro hk
    have hc := List.all_eq_true.1 hL k (List.mem_range.2 hk)
    by_cases h0 : k = 0
    · subst h0
      simp only [↓reduceIte, beq_iff_eq] at hc
      rw [hc]
      exact MulAction.mem_orbit_self _
    simp only [h0, ↓reduceIte, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hc
    obtain ⟨⟨hq, hj⟩, he⟩ := hc
    have hmem := ih _ hq (hq.trans hk)
    have hjm : gens.getD (L.getD k (0, 0, 0)).2.1 #[] ∈ gens := by
      rw [List.getD_eq_getElem _ _ hj]
      exact List.getElem_mem hj
    obtain ⟨σ, hσG, hσarr⟩ := hg _ hjm
    rw [he, ← smul_maskSetOf hσarr]
    exact MulAction.mem_orbit_of_mem_orbit (⟨σ, hσG⟩ : ↥G) hmem

theorem le_card_orbit_of_bfsg {G : Subgroup S24} {gens : List (Array ℕ)}
    (hg : ∀ a ∈ gens, ∃ σ ∈ G, HasArr σ a) {m₀ : ℕ} {L : List (ℕ × ℕ × ℕ)}
    (hL : bfsOKg gens m₀ L = true) (hnd : (L.map Prod.fst).Nodup)
    (hlt : ∀ e ∈ L, e.1 < 2 ^ 24) :
    L.length ≤ Nat.card (MulAction.orbit ↥G (maskSetOf m₀)) := by
  let f : Fin L.length → MulAction.orbit ↥G (maskSetOf m₀) := fun k =>
    ⟨maskSetOf (L.getD k (0, 0, 0)).1, mem_orbit_of_bfsg hg hL k k.2⟩
  have hf : Function.Injective f := by
    intro k k' hkk
    have hm : ∀ i : Fin L.length, L.getD i (0, 0, 0) ∈ L := fun i => by
      rw [List.getD_eq_getElem _ _ i.2]
      exact List.getElem_mem i.2
    have h := maskSetOf_inj (hlt _ (hm k)) (hlt _ (hm k')) (congrArg Subtype.val hkk)
    rw [List.getD_eq_getElem _ _ k.2, List.getD_eq_getElem _ _ k'.2] at h
    have h' : (L.map Prod.fst)[(k : ℕ)]'(by simp) = (L.map Prod.fst)[(k' : ℕ)]'(by simp) := by
      simpa using h
    exact Fin.ext ((List.Nodup.getElem_inj_iff hnd).1 h')
  simpa using Nat.card_le_card_of_injective f hf

theorem card_inf_stabilizer_mul_le {G : Subgroup S24} {gens : List (Array ℕ)}
    (hg : ∀ a ∈ gens, ∃ σ ∈ G, HasArr σ a) {m₀ : ℕ} {L : List (ℕ × ℕ × ℕ)}
    (hL : bfsOKg gens m₀ L = true) (hnd : (L.map Prod.fst).Nodup)
    (hlt : ∀ e ∈ L, e.1 < 2 ^ 24) :
    Nat.card ↥(G ⊓ MulAction.stabilizer S24 (maskSetOf m₀)) * L.length ≤ Nat.card ↥G := by
  have hmap : Subgroup.map G.subtype (MulAction.stabilizer ↥G (maskSetOf m₀))
      = G ⊓ MulAction.stabilizer S24 (maskSetOf m₀) := by
    rw [← MulAction.stabilizer_subgroupOf G (maskSetOf m₀), Subgroup.subgroupOf_map_subtype,
      inf_comm]
  have hcard := Subgroup.card_subtype G (MulAction.stabilizer ↥G (maskSetOf m₀))
  rw [hmap] at hcard
  rw [hcard]
  have h := (MulAction.stabilizer ↥G (maskSetOf m₀)).card_mul_index
  rw [MulAction.index_stabilizer] at h
  rw [← h]
  exact Nat.mul_le_mul_left _ (le_card_orbit_of_bfsg hg hL hnd hlt)

end CFSG.Quasithin.AppendixH.H14
