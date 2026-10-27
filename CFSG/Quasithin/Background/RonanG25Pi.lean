module

public import CFSG.Quasithin.Background.RonanG25Mod

public section

namespace CFSG.Quasithin.RonanG25

section Pi

variable {Γ : Type} [Group Γ] {F : Type} [Field F] {M : Type} [AddCommGroup M]

@[expose] def piAct (k : ℕ) (act : Γ → M →+ M) : Γ → (Fin k → M) →+ (Fin k → M) :=
  fun x => AddMonoidHom.compLeft (act x) (Fin k)

theorem piAct_apply (k : ℕ) (act : Γ → M →+ M) (x : Γ) (e : Fin k → M) (l : Fin k) :
    piAct k act x e l = act x (e l) := rfl

@[expose] def piPow (k : ℕ) (N : AddSubgroup M) : AddSubgroup (Fin k → M) where
  carrier := {e | ∀ l : Fin k, e l ∈ N}
  add_mem' := fun ha hb l => N.add_mem (ha l) (hb l)
  zero_mem' := fun _ => N.zero_mem
  neg_mem' := fun ha l => N.neg_mem (ha l)

theorem mem_piPow {k : ℕ} {N : AddSubgroup M} {e : Fin k → M} :
    e ∈ piPow k N ↔ ∀ l : Fin k, e l ∈ N := Iff.rfl

@[expose] def piSub (k : ℕ) (M₁ M₂ : AddSubgroup M) (j : ℕ) : AddSubgroup (Fin k → M) where
  carrier := {e | ∀ l : Fin k, e l ∈ (if l.val < j then M₂ else M₁)}
  add_mem' := fun {a b} ha hb l => by
    have h1 := ha l
    have h2 := hb l
    simp only [Pi.add_apply]
    split_ifs at h1 h2 ⊢
    · exact M₂.add_mem h1 h2
    · exact M₁.add_mem h1 h2
  zero_mem' := fun l => by
    split_ifs
    · exact M₂.zero_mem
    · exact M₁.zero_mem
  neg_mem' := fun {a} ha l => by
    have h1 := ha l
    simp only [Pi.neg_apply]
    split_ifs at h1 ⊢
    · exact M₂.neg_mem h1
    · exact M₁.neg_mem h1

theorem mem_piSub {k : ℕ} {M₁ M₂ : AddSubgroup M} {j : ℕ} {e : Fin k → M} :
    e ∈ piSub k M₁ M₂ j ↔ ∀ l : Fin k, e l ∈ (if l.val < j then M₂ else M₁) := Iff.rfl

theorem piSub_zero (k : ℕ) (M₁ M₂ : AddSubgroup M) : piSub k M₁ M₂ 0 = piPow k M₁ := by
  ext e
  rw [mem_piSub, mem_piPow]
  refine forall_congr' fun l => ?_
  rw [if_neg (Nat.not_lt_zero _)]

theorem piSub_k (k : ℕ) {M₁ M₂ : AddSubgroup M} (h : M₁ ≤ M₂) :
    piSub k M₁ M₂ k = piPow k M₂ := by
  clear h
  ext e
  rw [mem_piSub, mem_piPow]
  refine forall_congr' fun l => ?_
  rw [if_pos l.isLt]

theorem mem_piSub_single {k : ℕ} {M₁ M₂ : AddSubgroup M} {j : ℕ} (i : Fin k) (m : M) :
    Pi.single i m ∈ piSub k M₁ M₂ j ↔ m ∈ (if i.val < j then M₂ else M₁) := by
  rw [mem_piSub]
  constructor
  · intro h
    have hi := h i
    rwa [Pi.single_eq_same] at hi
  · intro h l
    by_cases hli : l = i
    · rw [hli, Pi.single_eq_same]
      exact h
    · rw [Pi.single_eq_of_ne hli]
      split_ifs
      · exact M₂.zero_mem
      · exact M₁.zero_mem

theorem mem_piSub_iff_of_succ {k j : ℕ} {M₁ M₂ : AddSubgroup M} {e : Fin k → M}
    (he : e ∈ piSub k M₁ M₂ (j + 1)) (i : Fin k) (hi : i.val = j) :
    e ∈ piSub k M₁ M₂ j ↔ e i ∈ M₁ := by
  rw [mem_piSub] at he ⊢
  constructor
  · intro h
    have h' := h i
    rwa [if_neg (show ¬ (i.val < j) by omega)] at h'
  · intro h l
    have hl := he l
    by_cases hlt : l.val < j
    · rw [if_pos hlt]
      rw [if_pos (show l.val < j + 1 by omega)] at hl
      exact hl
    · rw [if_neg hlt]
      by_cases hjl : l.val = j
      · have hli : l = i := Fin.ext (hjl.trans hi.symm)
        rw [hli]
        exact h
      · rw [if_neg (show ¬ (l.val < j + 1) by omega)] at hl
        exact hl

theorem piSub_inv (k : ℕ) {act : Γ → M →+ M} {M₁ M₂ : AddSubgroup M} (hs : ModStep act M₁ M₂)
    (j : ℕ) : AInv (piAct k act) (piSub k M₁ M₂ j) := by
  intro x e he
  rw [mem_piSub] at he ⊢
  intro l
  rw [piAct_apply]
  have hl := he l
  split_ifs at hl ⊢
  · exact hs.inv₂ x _ hl
  · exact hs.inv₁ x _ hl

theorem card_piSub (k j : ℕ) (M₁ M₂ : AddSubgroup M) :
    Nat.card ↥(piSub k M₁ M₂ j) =
      ∏ l : Fin k, Nat.card ↥(if l.val < j then M₂ else M₁ : AddSubgroup M) := by
  have e1 : ↥(piSub k M₁ M₂ j) ≃
      {f : Fin k → M // ∀ l : Fin k, f l ∈ (if l.val < j then M₂ else M₁ : AddSubgroup M)} :=
    Equiv.subtypeEquivRight (fun f => mem_piSub)
  have e2 : {f : Fin k → M // ∀ l : Fin k, f l ∈ (if l.val < j then M₂ else M₁ : AddSubgroup M)} ≃
      ∀ l : Fin k, ↥(if l.val < j then M₂ else M₁ : AddSubgroup M) :=
    Equiv.subtypePiEquivPi
  rw [Nat.card_congr (e1.trans e2), Nat.card_pi]

theorem card_piSub_succ (k j : ℕ) (i : Fin k) (hi : i.val = j) (M₁ M₂ : AddSubgroup M) :
    ∃ R : ℕ, Nat.card ↥(piSub k M₁ M₂ (j + 1)) = Nat.card M₂ * R ∧
      Nat.card ↥(piSub k M₁ M₂ j) = Nat.card M₁ * R := by
  refine ⟨∏ l ∈ Finset.univ.erase i, Nat.card ↥(if l.val < j then M₂ else M₁ : AddSubgroup M),
    ?_, ?_⟩
  · have h1 : Nat.card ↥(if i.val < j + 1 then M₂ else M₁ : AddSubgroup M) = Nat.card M₂ := by
      rw [if_pos (show i.val < j + 1 by omega)]
    have h2 : ∏ l ∈ Finset.univ.erase i,
        Nat.card ↥(if l.val < j + 1 then M₂ else M₁ : AddSubgroup M) =
        ∏ l ∈ Finset.univ.erase i, Nat.card ↥(if l.val < j then M₂ else M₁ : AddSubgroup M) := by
      refine Finset.prod_congr rfl fun l hl => ?_
      have hne : l.val ≠ j := fun h => (Finset.mem_erase.1 hl).1 (Fin.ext (h.trans hi.symm))
      have hiff : l.val < j + 1 ↔ l.val < j := by
        constructor <;> intro h <;> omega
      simp only [hiff]
    rw [card_piSub, ← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ i), h1, h2]
  · have h1 : Nat.card ↥(if i.val < j then M₂ else M₁ : AddSubgroup M) = Nat.card M₁ := by
      rw [if_neg (show ¬ (i.val < j) by omega)]
    rw [card_piSub, ← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ i), h1]

theorem piSub_step (k : ℕ) {act : Γ → M →+ M} {M₁ M₂ : AddSubgroup M} (hs : ModStep act M₁ M₂)
    (j : ℕ) (hj : j < k) :
    ModStep (piAct k act) (piSub k M₁ M₂ j) (piSub k M₁ M₂ (j + 1)) := by
  obtain ⟨i, hi⟩ : ∃ i : Fin k, i.val = j := ⟨⟨j, hj⟩, rfl⟩
  refine ⟨?_, piSub_inv k hs j, piSub_inv k hs (j + 1), ?_⟩
  · refine SetLike.lt_iff_le_and_exists.2 ⟨?_, ?_⟩
    · intro f hf
      rw [mem_piSub] at hf ⊢
      intro l
      have hl := hf l
      by_cases hlt : l.val < j
      · rw [if_pos hlt] at hl
        rw [if_pos (show l.val < j + 1 by omega)]
        exact hl
      · rw [if_neg hlt] at hl
        by_cases hlt' : l.val < j + 1
        · rw [if_pos hlt']
          exact hs.lt.le hl
        · rw [if_neg hlt']
          exact hl
    · obtain ⟨m, hm2, hm1⟩ := SetLike.exists_of_lt hs.lt
      refine ⟨Pi.single i m, ?_, ?_⟩
      · rw [mem_piSub_single, if_pos (show i.val < j + 1 by omega)]
        exact hm2
      · rw [mem_piSub_single, if_neg (show ¬ (i.val < j) by omega)]
        exact hm1
  · intro X hX1 hX2 hXinv
    obtain ⟨Y, hYdef⟩ : ∃ Y : AddSubgroup M,
        ∀ m : M, m ∈ Y ↔ ∃ f ∈ X, f i = m :=
      ⟨X.map (Pi.evalAddMonoidHom (fun _ : Fin k => M) i), fun m => AddSubgroup.mem_map⟩
    have hY1 : M₁ ≤ Y := by
      intro m hm
      rw [hYdef]
      have hsing : Pi.single i m ∈ piSub k M₁ M₂ j := by
        rw [mem_piSub_single, if_neg (show ¬ (i.val < j) by omega)]
        exact hm
      exact ⟨Pi.single i m, hX1 hsing, by simp⟩
    have hY2 : Y ≤ M₂ := by
      intro m hm
      rw [hYdef] at hm
      obtain ⟨f, hf, rfl⟩ := hm
      have h := (mem_piSub.1 (hX2 hf)) i
      rwa [if_pos (show i.val < j + 1 by omega)] at h
    have hYinv : AInv act Y := by
      intro x m hm
      rw [hYdef] at hm
      rw [hYdef]
      obtain ⟨f, hf, rfl⟩ := hm
      exact ⟨piAct k act x f, hXinv x f hf, rfl⟩
    rcases hs.simple Y hY1 hY2 hYinv with hYeq | hYeq
    · left
      refine le_antisymm ?_ hX1
      intro f hf
      refine (mem_piSub_iff_of_succ (hX2 hf) i hi).2 ?_
      have hfi : f i ∈ Y := (hYdef (f i)).2 ⟨f, hf, rfl⟩
      rw [hYeq] at hfi
      exact hfi
    · right
      refine le_antisymm hX2 ?_
      intro f hf
      have hfi : f i ∈ Y := by
        rw [hYeq]
        have h := (mem_piSub.1 hf) i
        rwa [if_pos (show i.val < j + 1 by omega)] at h
      obtain ⟨e, he, hei⟩ := (hYdef (f i)).1 hfi
      have hdiff : f - e ∈ piSub k M₁ M₂ j := by
        refine (mem_piSub_iff_of_succ ((piSub k M₁ M₂ (j + 1)).sub_mem hf (hX2 he)) i hi).2 ?_
        rw [Pi.sub_apply, hei, sub_self]
        exact M₁.zero_mem
      have h := X.add_mem (hX1 hdiff) he
      rwa [sub_add_cancel] at h

theorem piSub_natural (k : ℕ) {act : Γ → M →+ M} {M₁ M₂ : AddSubgroup M}
    (hn : ModNatural F act M₁ M₂) (j : ℕ) (hj : j < k) :
    ModNatural F (piAct k act) (piSub k M₁ M₂ j) (piSub k M₁ M₂ (j + 1)) := by
  obtain ⟨i, hi⟩ : ∃ i : Fin k, i.val = j := ⟨⟨j, hj⟩, rfl⟩
  obtain ⟨c, β, hsurj, hker, hequiv, h2, h3⟩ := hn
  have hcoord : ∀ e ∈ piSub k M₁ M₂ (j + 1), e i ∈ M₂ := by
    intro e he
    have h := (mem_piSub.1 he) i
    rwa [if_pos (show i.val < j + 1 by omega)] at h
  unfold ModNatural
  refine ⟨c.comp (Pi.evalAddMonoidHom (fun _ : Fin k => M) i), β, ?_, ?_, ?_, h2, h3⟩
  · intro w
    obtain ⟨e₀, he₀, hce⟩ := hsurj w
    refine ⟨Pi.single i e₀, ?_, ?_⟩
    · rw [mem_piSub_single, if_pos (show i.val < j + 1 by omega)]
      exact he₀
    · show c ((Pi.single i e₀ : Fin k → M) i) = w
      rw [Pi.single_eq_same]
      exact hce
  · intro e he
    show c (e i) = 0 ↔ e ∈ piSub k M₁ M₂ j
    rw [mem_piSub_iff_of_succ he i hi]
    exact hker (e i) (hcoord e he)
  · intro x e he
    exact hequiv x (e i) (hcoord e he)

theorem piSub_additional (k : ℕ) {act : Γ → M →+ M} {M₁ M₂ : AddSubgroup M}
    (hn : ModAdditional F act M₁ M₂) (j : ℕ) (hj : j < k) :
    ModAdditional F (piAct k act) (piSub k M₁ M₂ j) (piSub k M₁ M₂ (j + 1)) := by
  obtain ⟨i, hi⟩ : ∃ i : Fin k, i.val = j := ⟨⟨j, hj⟩, rfl⟩
  obtain ⟨hcard, x, e, he, hne⟩ := hn
  obtain ⟨R, hR1, hR2⟩ := card_piSub_succ k j i hi M₁ M₂
  unfold ModAdditional
  refine ⟨?_, x, Pi.single i e, (mem_piSub_single i e).2 ?_, ?_⟩
  · rw [hR1, hR2, hcard, mul_assoc]
  · rw [if_pos (show i.val < j + 1 by omega)]
    exact he
  · intro hmem
    have h := (mem_piSub.1 hmem) i
    rw [if_neg (show ¬ (i.val < j) by omega), Pi.sub_apply, piAct_apply, Pi.single_eq_same] at h
    exact hne h

theorem piSub_central (k : ℕ) {act : Γ → M →+ M} {M₁ M₂ : AddSubgroup M}
    (hs : ModStep act M₁ M₂) (hn : ModCentral act M₁ M₂) (j : ℕ) (hj : j < k) :
    ModCentral (piAct k act) (piSub k M₁ M₂ j) (piSub k M₁ M₂ (j + 1)) := by
  obtain ⟨i, hi⟩ : ∃ i : Fin k, i.val = j := ⟨⟨j, hj⟩, rfl⟩
  obtain ⟨hc, p, hp, hcard⟩ := hn
  obtain ⟨R, hR1, hR2⟩ := card_piSub_succ k j i hi M₁ M₂
  unfold ModCentral
  refine ⟨?_, p, hp, ?_⟩
  · intro x e he
    rw [mem_piSub] at he ⊢
    intro l
    rw [Pi.sub_apply, piAct_apply]
    have hel : e l ∈ M₂ := by
      have h := he l
      split_ifs at h
      · exact h
      · exact hs.lt.le h
    have hc' := hc x (e l) hel
    split_ifs
    · exact hs.lt.le hc'
    · exact hc'
  · rw [hR1, hR2, hcard, mul_assoc]

theorem piSub_chain_natural (k : ℕ) {act : Γ → M →+ M} {M₁ M₂ : AddSubgroup M}
    (hs : ModStep act M₁ M₂) (hn : ModNatural F act M₁ M₂) :
    ∀ j : ℕ, j ≤ k → ModChain F (piAct k act) (piSub k M₁ M₂ 0) (piSub k M₁ M₂ j) j 0 := by
  intro j
  induction j with
  | zero => intro _; exact ModChain.refl _ (piSub_inv k hs 0)
  | succ j ih =>
    intro hj
    exact ModChain.trans (ih (by omega))
      (ModChain.natural (piSub_step k hs j (by omega)) (piSub_natural k hn j (by omega))
        (ModChain.refl _ (piSub_inv k hs (j + 1))))

theorem piSub_chain_additional (k : ℕ) {act : Γ → M →+ M} {M₁ M₂ : AddSubgroup M}
    (hs : ModStep act M₁ M₂) (hn : ModAdditional F act M₁ M₂) :
    ∀ j : ℕ, j ≤ k → ModChain F (piAct k act) (piSub k M₁ M₂ 0) (piSub k M₁ M₂ j) 0 j := by
  intro j
  induction j with
  | zero => intro _; exact ModChain.refl _ (piSub_inv k hs 0)
  | succ j ih =>
    intro hj
    exact ModChain.trans (ih (by omega))
      (ModChain.additional (piSub_step k hs j (by omega)) (piSub_additional k hn j (by omega))
        (ModChain.refl _ (piSub_inv k hs (j + 1))))

theorem piSub_chain_central (k : ℕ) {act : Γ → M →+ M} {M₁ M₂ : AddSubgroup M}
    (hs : ModStep act M₁ M₂) (hn : ModCentral act M₁ M₂) :
    ∀ j : ℕ, j ≤ k → ModChain F (piAct k act) (piSub k M₁ M₂ 0) (piSub k M₁ M₂ j) 0 0 := by
  intro j
  induction j with
  | zero => intro _; exact ModChain.refl _ (piSub_inv k hs 0)
  | succ j ih =>
    intro hj
    exact ModChain.trans (ih (by omega))
      (ModChain.central (piSub_step k hs j (by omega)) (piSub_central k hs hn j (by omega))
        (ModChain.refl _ (piSub_inv k hs (j + 1))))

theorem ModChain.pi_natural {act : Γ → M →+ M} {M₁ M₂ : AddSubgroup M}
    (hs : ModStep act M₁ M₂) (hn : ModNatural F act M₁ M₂) (k : ℕ) :
    ModChain F (piAct k act) (piPow k M₁) (piPow k M₂) k 0 := by
  have h := piSub_chain_natural k hs hn k le_rfl
  rw [piSub_zero, piSub_k k hs.lt.le] at h
  exact h

theorem ModChain.pi_additional {act : Γ → M →+ M} {M₁ M₂ : AddSubgroup M}
    (hs : ModStep act M₁ M₂) (hn : ModAdditional F act M₁ M₂) (k : ℕ) :
    ModChain F (piAct k act) (piPow k M₁) (piPow k M₂) 0 k := by
  have h := piSub_chain_additional k hs hn k le_rfl
  rw [piSub_zero, piSub_k k hs.lt.le] at h
  exact h

theorem ModChain.pi_central {act : Γ → M →+ M} {M₁ M₂ : AddSubgroup M}
    (hs : ModStep act M₁ M₂) (hn : ModCentral act M₁ M₂) (k : ℕ) :
    ModChain F (piAct k act) (piPow k M₁) (piPow k M₂) 0 0 := by
  have h := piSub_chain_central (F := F) k hs hn k le_rfl
  rw [piSub_zero, piSub_k k hs.lt.le] at h
  exact h

end Pi

end CFSG.Quasithin.RonanG25
