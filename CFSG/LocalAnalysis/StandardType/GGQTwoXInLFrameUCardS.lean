module

public import CFSG.LocalAnalysis.StandardType.GGQTwoXInLFrameUDefs

public section

namespace CFSG.StandardType

private def ggQTUcs_augEquiv (n : ℕ) : ↥(GGQTwoXInLAug n) ≃ (Fin n → ZMod 3) where
  toFun v := fun k => v.1 k.succ
  invFun x :=
    ⟨fun i => if h : i = 0 then -∑ k : Fin n, x k else x (i.pred h), by
      rw [LinearMap.mem_ker, LinearMap.sum_apply, Fin.sum_univ_succ]
      simp
      exact neg_add_cancel _⟩
  left_inv v := by
    ext i
    rcases Fin.eq_zero_or_eq_succ i with rfl | ⟨k, rfl⟩
    · have hv : ∑ i : Fin (n + 1), v.1 i = 0 := by
        have h := v.2
        rw [LinearMap.mem_ker, LinearMap.sum_apply] at h
        simpa using h
      have h0 : v.1 0 + ∑ k : Fin n, v.1 k.succ = 0 := by
        rw [← Fin.sum_univ_succ]
        exact hv
      show -∑ k : Fin n, v.1 k.succ = v.1 0
      exact neg_eq_of_add_eq_zero_left h0
    · simp
  right_inv x := by
    funext k
    simp

private lemma ggQTUcs_card_const {ι : Type} [Fintype ι] [DecidableEq ι]
    (s : Finset ι) (hs : s.Nonempty) :
    Nat.card {x : ι → ZMod 3 // ∀ i ∈ s, ∀ j ∈ s, x i = x j}
      = 3 ^ (Fintype.card ι + 1 - s.card) := by
  classical
  obtain ⟨s0, hs0⟩ := hs
  let comp : Finset ι := Finset.univ \ s
  have hcomp : comp.card = Fintype.card ι - s.card := by
    show (Finset.univ \ s).card = Fintype.card ι - s.card
    rw [Finset.card_sdiff, Finset.inter_univ, Finset.card_univ]
  let e : {x : ι → ZMod 3 // ∀ i ∈ s, ∀ j ∈ s, x i = x j} ≃
      (ZMod 3 × (↥comp → ZMod 3)) :=
    { toFun := fun x => (x.1 s0, fun k => x.1 k.1)
      invFun := fun y =>
        ⟨fun i => if hi : i ∈ s then y.1 else y.2 ⟨i, by simp [comp, hi]⟩, by
          intro i hi j hj
          simp [hi, hj]⟩
      left_inv := by
        intro x
        ext i
        by_cases hi : i ∈ s
        · simp only [hi, ↓reduceDIte]
          exact (x.2 i hi s0 hs0).symm
        · simp [hi]
      right_inv := by
        intro y
        apply Prod.ext
        · simp [hs0]
        · funext k
          have hk : (k : ι) ∉ s := by
            have h2 : (k : ι) ∈ Finset.univ \ s := k.2
            exact (Finset.mem_sdiff.1 h2).2
          simp [hk] }
  rw [Nat.card_congr e]
  simp only [Nat.card_prod, Nat.card_fun, Nat.card_zmod]
  have hcoe : Nat.card ↥comp = comp.card := by
    rw [Nat.card_eq_fintype_card, Fintype.card_coe]
  rw [hcoe, hcomp]
  have hle : s.card ≤ Fintype.card ι := Finset.card_le_univ s
  calc 3 * 3 ^ (Fintype.card ι - s.card)
      = 3 ^ (Fintype.card ι - s.card) * 3 := Nat.mul_comm _ _
    _ = 3 ^ (Fintype.card ι - s.card + 1) := (pow_succ _ _).symm
    _ = 3 ^ (Fintype.card ι + 1 - s.card) := by
        rw [show Fintype.card ι - s.card + 1 = Fintype.card ι + 1 - s.card by omega]

theorem ggQTwoXInLU_cardS {G : Type} [Group G] {Bs X L D : Subgroup G} {x : G} {n : ℕ}
    {K : Type} [Field K] (hn6 : 6 ≤ n) (C : GGQTwoXInLUCoord Bs X L x n K) (hDBs : D ≤ Bs)
    (hD9 : Nat.card ↥D = 9) {S : Finset (Fin (n + 1))} (hS0 : 0 ∉ S)
    (hD : ∀ b : ↥Bs, (b : G) ∈ D ↔ ∀ i ∈ S, ∀ j ∈ S,
        ((C.ι (Additive.ofMul b) : ↥(GGQTwoXInLAug n)) : Fin (n + 1) → ZMod 3) i =
          ((C.ι (Additive.ofMul b) : ↥(GGQTwoXInLAug n)) : Fin (n + 1) → ZMod 3) j) :
    ∃ j : Fin (n + 1), j ≠ 0 ∧ S = (Finset.univ.erase 0).erase j := by
  classical
  let T : Set ↥(GGQTwoXInLAug n) := fun v =>
    ∀ i ∈ S, ∀ j ∈ S,
      ((v : ↥(GGQTwoXInLAug n)) : Fin (n + 1) → ZMod 3) i =
        ((v : ↥(GGQTwoXInLAug n)) : Fin (n + 1) → ZMod 3) j
  have hcardDT : Nat.card ↥D = Nat.card ↥T := by
    refine Nat.card_congr ?_
    refine
      { toFun := fun d =>
          ⟨C.ι (Additive.ofMul ⟨(d : G), hDBs d.2⟩),
            (hD ⟨(d : G), hDBs d.2⟩).1 d.2⟩
        invFun := fun v => by
          let b : ↥Bs := Additive.toMul (C.ι.symm v.1)
          have hb : (b : G) ∈ D := by
            refine (hD b).2 ?_
            have hb_eq : C.ι (Additive.ofMul b) = v.1 := by
              dsimp [b]
              simp
            intro i hi j hj
            simpa only [hb_eq] using v.2 i hi j hj
          exact ⟨(b : G), hb⟩
        left_inv := fun d => by
          apply Subtype.ext
          dsimp
          simp
        right_inv := fun v => by
          ext i
          dsimp
          simp }
  let e : ↥(GGQTwoXInLAug n) ≃ (Fin n → ZMod 3) := ggQTUcs_augEquiv n
  let S' : Finset (Fin n) := Finset.univ.filter (fun k => k.succ ∈ S)
  have hS'_eq : S = S'.image Fin.succ := by
    ext i
    constructor
    · intro hi
      have hi0 : i ≠ 0 := fun h => hS0 (h ▸ hi)
      refine Finset.mem_image.2 ⟨i.pred hi0, ?_, Fin.succ_pred i hi0⟩
      simp [S', Fin.succ_pred i hi0, hi]
    · intro hi
      obtain ⟨k, hk, rfl⟩ := Finset.mem_image.1 hi
      simpa [S'] using hk
  have hS'_card : S'.card = S.card := by
    rw [hS'_eq, Finset.card_image_of_injective S' (Fin.succ_injective n)]
  let T' : Set (Fin n → ZMod 3) := fun y => ∀ i ∈ S', ∀ j ∈ S', y i = y j
  have hT_eq : ∀ v : ↥(GGQTwoXInLAug n), v ∈ T ↔ e v ∈ T' := by
    intro v
    constructor
    · intro hv i hi j hj
      have hi' : i.succ ∈ S := by simpa [S'] using hi
      have hj' : j.succ ∈ S := by simpa [S'] using hj
      simpa [e, ggQTUcs_augEquiv] using hv i.succ hi' j.succ hj'
    · intro hv i hi j hj
      rw [hS'_eq] at hi hj
      obtain ⟨k, hk, rfl⟩ := Finset.mem_image.1 hi
      obtain ⟨l, hl, rfl⟩ := Finset.mem_image.1 hj
      simpa [e, ggQTUcs_augEquiv] using hv k hk l hl
  have hcardT : Nat.card ↥T = Nat.card ↥T' :=
    Nat.card_congr (Equiv.subtypeEquiv e (fun v => hT_eq v))
  have hDT' : Nat.card ↥D = Nat.card ↥T' := hcardDT.trans hcardT
  by_cases hS : S = ∅
  · have hS'empty : S' = ∅ := by simp [S', hS]
    have hT'univ : T' = Set.univ := by
      ext y
      refine ⟨fun _ => trivial, ?_⟩
      intro _ i hi
      simp [hS'empty] at hi
    have hDT'univ : Nat.card ↥D = Nat.card ↥(Set.univ : Set (Fin n → ZMod 3)) := by
      rw [hDT', hT'univ]
    have hcardUniv : Nat.card ↥(Set.univ : Set (Fin n → ZMod 3)) = 3 ^ n := by
      rw [Nat.card_congr (Equiv.Set.univ (Fin n → ZMod 3))]
      simp only [Nat.card_fun, Nat.card_zmod, Nat.card_fin]
    have hn : n = 2 := by
      have h : 3 ^ n = 3 ^ 2 := by
        rw [← hcardUniv, ← hDT'univ, hD9]
        norm_num
      exact Nat.pow_right_injective (by norm_num : 2 ≤ 3) h
    omega
  · have hSne : S.Nonempty := Finset.nonempty_iff_ne_empty.2 hS
    have hS'ne : S'.Nonempty := by
      rw [← Finset.card_pos, hS'_card]
      exact Finset.card_pos.2 hSne
    have hcardT' : Nat.card ↥T' = 3 ^ (n + 1 - S.card) := by
      have h := ggQTUcs_card_const S' hS'ne
      rw [Fintype.card_fin, hS'_card] at h
      exact h
    have h9T' : Nat.card ↥T' = 9 := by
      rw [← hDT', hD9]
    have hexp : n + 1 - S.card = 2 := by
      refine Nat.pow_right_injective (by norm_num : 2 ≤ 3) ?_
      show (3 : ℕ) ^ (n + 1 - S.card) = 3 ^ 2
      rw [← hcardT', h9T']
    have hcardErase : (Finset.univ.erase (0 : Fin (n + 1))).card = n := by
      rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, Fintype.card_fin]
      omega
    have hScard : S.card = n - 1 := by omega
    have hsubErase : S ⊆ Finset.univ.erase (0 : Fin (n + 1)) := by
      intro i hi
      rw [Finset.mem_erase]
      exact ⟨fun h => hS0 (h ▸ hi), Finset.mem_univ i⟩
    have hlt : S.card < (Finset.univ.erase (0 : Fin (n + 1))).card := by
      rw [hcardErase]
      omega
    obtain ⟨j, hjmem, hjnot⟩ := Finset.exists_mem_notMem_of_card_lt_card (s := S) hlt
    refine ⟨j, ?_, ?_⟩
    · intro hj0
      exact (Finset.mem_erase.1 hjmem).1 hj0
    · have hsub : S ⊆ (Finset.univ.erase (0 : Fin (n + 1))).erase j := by
        intro i hi
        rw [Finset.mem_erase]
        refine ⟨?_, hsubErase hi⟩
        intro hji
        exact hjnot (hji ▸ hi)
      refine Finset.eq_of_subset_of_card_le hsub ?_
      rw [Finset.card_erase_of_mem hjmem, hcardErase]
      omega

end CFSG.StandardType

end
