module

public import CFSG.Quasithin.EmptyFaithful.Stellmacher.PushingUpAndModuleTheory.ResA7

public section

namespace CFSG.Quasithin.F53Mod

open Equiv

@[expose] def actSub (σ : Perm (Fin 5)) (Y : Subgroup orth.W) : Subgroup orth.W :=
  Y.map (orth.act σ).toMonoidHom

@[expose] def IsThreeCyc (c : Perm (Fin 5)) : Prop :=
  c ^ 3 = 1 ∧ c ≠ 1 ∧ (c * swap 0 2 = swap 0 2 * c ∨ c * swap 1 3 = swap 1 3 * c)

@[expose] def planeOf (c : Perm (Fin 5)) : Subgroup orth.W := commW orth (Subgroup.zpowers c) ⊤

@[expose] def PlaneP (c : Perm (Fin 5)) (w : orth.W) : Prop :=
  ∀ i : Fin 5, c i = i → Multiplicative.toAdd (vec w) i = 0

instance (c : Perm (Fin 5)) (w : orth.W) : Decidable (PlaneP c w) := by
  unfold PlaneP; infer_instance

theorem mem_actSub (σ : Perm (Fin 5)) (Y : Subgroup orth.W) (w : orth.W) :
    w ∈ actSub σ Y ↔ orth.act σ⁻¹ w ∈ Y := by
  constructor
  · rintro ⟨x, hx, rfl⟩
    show orth.act σ⁻¹ (orth.act σ x) ∈ Y
    rw [act_inv_act]; exact hx
  · intro h
    exact ⟨_, h, act_act_inv orth σ w⟩

theorem mem_zpowers_of_sq {s τ : Perm (Fin 5)} (hs : s ^ 2 = 1) :
    τ ∈ Subgroup.zpowers s ↔ τ = 1 ∨ τ = s := by
  rw [mem_zpowers_iff_of_pow_eq_one hs (by norm_num)]
  constructor
  · rintro ⟨k, hk, rfl⟩
    interval_cases k <;> simp
  · rintro (rfl | rfl)
    · exact ⟨0, by norm_num, by simp⟩
    · exact ⟨1, by norm_num, by simp⟩

private theorem planeF_eq : ∀ c : Perm (Fin 5), c ^ 3 = 1 → c ≠ 1 →
    (c * swap 0 2 = swap 0 2 * c ∨ c * swap 1 3 = swap 1 3 * c) →
    spanF (commGensF orth ({1, c, c ^ 2} : Finset (Perm (Fin 5))) Finset.univ) =
      Finset.univ.filter (PlaneP c) := by
  decide +kernel

theorem mem_planeOf_iff {c : Perm (Fin 5)} (hc : IsThreeCyc c) (w : orth.W) :
    w ∈ planeOf c ↔ PlaneP c w := by
  have hB : ∀ σ, σ ∈ Subgroup.zpowers c ↔ σ ∈ ({1, c, c ^ 2} : Finset (Perm (Fin 5))) := by
    intro σ
    rw [mem_zpowers_iff_of_pow_eq_one hc.1 (by norm_num)]
    constructor
    · rintro ⟨k, hk, rfl⟩
      interval_cases k <;> simp
    · intro h
      simp only [Finset.mem_insert, Finset.mem_singleton] at h
      rcases h with rfl | rfl | rfl
      · exact ⟨0, by norm_num, by simp⟩
      · exact ⟨1, by norm_num, by simp⟩
      · exact ⟨2, by norm_num, rfl⟩
  have hU : ∀ u, u ∈ (⊤ : Subgroup orth.W) ↔ u ∈ (Finset.univ : Finset orth.W) := by
    intro u; simp
  unfold planeOf
  rw [mem_commW_iff orth hB hU, planeF_eq c hc.1 hc.2.1 hc.2.2]
  simp

private theorem sup_aux1 : ∀ σ ∈ S5SylF, σ ∉ S5ThatF → ∀ c : Perm (Fin 5), c ^ 3 = 1 → c ≠ 1 →
    (c * swap 0 2 = swap 0 2 * c ∨ c * swap 1 3 = swap 1 3 * c) →
    ∀ w : orth.W, ∃ y : orth.W, PlaneP c y ∧ PlaneP c (orth.act σ⁻¹ (w * y⁻¹)) := by
  decide +kernel

private theorem sup_aux2 : ∀ σ ∈ S5SylF, σ ∉ S5ThatF → ∀ c : Perm (Fin 5), c ^ 3 = 1 → c ≠ 1 →
    (c * swap 0 2 = swap 0 2 * c ∨ c * swap 1 3 = swap 1 3 * c) →
    ∀ w : orth.W, PlaneP c w → PlaneP c (orth.act σ⁻¹ w) → w = 1 := by
  decide +kernel

theorem planeOf_sup_conj {c : Perm (Fin 5)} (hc : IsThreeCyc c) {σ : Perm (Fin 5)}
    (hσ : σ ∈ S5Syl) (hσ' : σ ∉ S5That) :
    planeOf c ⊔ actSub σ (planeOf c) = ⊤ ∧ planeOf c ⊓ actSub σ (planeOf c) = ⊥ := by
  rw [mem_S5Syl_iff] at hσ
  rw [mem_S5That_iff] at hσ'
  have h1 := sup_aux1 σ hσ hσ' c hc.1 hc.2.1 hc.2.2
  have h2 := sup_aux2 σ hσ hσ' c hc.1 hc.2.1 hc.2.2
  constructor
  · rw [eq_top_iff]
    intro w _
    obtain ⟨y, hy, hz⟩ := h1 w
    refine Subgroup.mem_sup.mpr ⟨y, (mem_planeOf_iff hc y).mpr hy, w * y⁻¹, ?_, ?_⟩
    · rw [mem_actSub, mem_planeOf_iff hc]; exact hz
    · rw [mul_comm w, mul_inv_cancel_left]
  · rw [eq_bot_iff]
    intro w hw
    rw [Subgroup.mem_inf, mem_actSub, mem_planeOf_iff hc, mem_planeOf_iff hc] at hw
    exact (Subgroup.mem_bot).mpr (h2 w hw.1 hw.2)

private theorem fix_aux : ∀ τ ∈ S5ThatF, ∀ c : Perm (Fin 5), c ^ 3 = 1 → c ≠ 1 →
    (c * swap 0 2 = swap 0 2 * c ∨ c * swap 1 3 = swap 1 3 * c) →
    ((∀ w : orth.W, PlaneP c w → orth.act τ w = w) ↔
      ((c * swap 0 2 = swap 0 2 * c → (τ = 1 ∨ τ = swap 0 2)) ∧
       (c * swap 1 3 = swap 1 3 * c → (τ = 1 ∨ τ = swap 1 3)))) := by
  decide +kernel

theorem fix_planeOf_iff {c : Perm (Fin 5)} (hc : IsThreeCyc c) {τ : Perm (Fin 5)}
    (hτ : τ ∈ S5That) :
    (∀ v ∈ planeOf c, orth.act τ v = v) ↔
      (c * swap 0 2 = swap 0 2 * c → τ ∈ Subgroup.zpowers (swap 0 2)) ∧
      (c * swap 1 3 = swap 1 3 * c → τ ∈ Subgroup.zpowers (swap 1 3)) := by
  rw [mem_S5That_iff] at hτ
  have h := fix_aux τ hτ c hc.1 hc.2.1 hc.2.2
  rw [mem_zpowers_of_sq (by decide +kernel), mem_zpowers_of_sq (by decide +kernel)]
  rw [← h]
  simp only [mem_planeOf_iff hc]

theorem fix_planeOf {c : Perm (Fin 5)} (hc : IsThreeCyc c) {τ : Perm (Fin 5)}
    (hτ : τ ∈ S5That) (hfix : ∀ v ∈ planeOf c, orth.act τ v = v) :
    τ ∈ Subgroup.zpowers (swap 0 2) ∨ τ ∈ Subgroup.zpowers (swap 1 3) := by
  obtain ⟨h1, h2⟩ := (fix_planeOf_iff hc hτ).mp hfix
  rcases hc.2.2 with h | h
  · exact Or.inl (h1 h)
  · exact Or.inr (h2 h)

private theorem card_comm_aux : ∀ c : Perm (Fin 5), c ^ 3 = 1 → c ≠ 1 →
    (c * swap 0 2 = swap 0 2 * c ∨ c * swap 1 3 = swap 1 3 * c) →
    (spanF (commGensF orth S5ThatF (Finset.univ.filter (PlaneP c)))).card = 2 := by
  decide +kernel

private theorem commW_planeOf_mem {c : Perm (Fin 5)} (hc : IsThreeCyc c) (w : orth.W) :
    w ∈ commW orth S5That (planeOf c) ↔
      w ∈ spanF (commGensF orth S5ThatF (Finset.univ.filter (PlaneP c))) := by
  refine mem_commW_iff orth mem_S5That_iff (fun u => ?_) w
  rw [mem_planeOf_iff hc]; simp

theorem card_commW_planeOf {c : Perm (Fin 5)} (hc : IsThreeCyc c) :
    Nat.card (commW orth S5That (planeOf c)) = 2 := by
  have : Nat.card (commW orth S5That (planeOf c)) =
      Nat.card (spanF (commGensF orth S5ThatF (Finset.univ.filter (PlaneP c)))) :=
    Nat.card_congr (Equiv.subtypeEquivRight fun w => commW_planeOf_mem hc w)
  rw [this, Nat.card_eq_finsetCard]
  exact card_comm_aux c hc.1 hc.2.1 hc.2.2

private theorem not_inv_aux : ∀ σ ∈ S5SylF, σ ∉ S5ThatF → ∀ c : Perm (Fin 5), c ^ 3 = 1 →
    c ≠ 1 → (c * swap 0 2 = swap 0 2 * c ∨ c * swap 1 3 = swap 1 3 * c) →
    ∃ w : orth.W, ¬ (orth.act σ⁻¹ w ∈ spanF (commGensF orth S5ThatF (Finset.univ.filter (PlaneP c))) ↔
      w ∈ spanF (commGensF orth S5ThatF (Finset.univ.filter (PlaneP c)))) := by
  decide +kernel

theorem commW_planeOf_not_invariant {c : Perm (Fin 5)} (hc : IsThreeCyc c) {σ : Perm (Fin 5)}
    (hσ : σ ∈ S5Syl) (hσ' : σ ∉ S5That) :
    actSub σ (commW orth S5That (planeOf c)) ≠ commW orth S5That (planeOf c) := by
  rw [mem_S5Syl_iff] at hσ
  rw [mem_S5That_iff] at hσ'
  intro h
  obtain ⟨w, hw⟩ := not_inv_aux σ hσ hσ' c hc.1 hc.2.1 hc.2.2
  apply hw
  rw [← commW_planeOf_mem hc, ← commW_planeOf_mem hc, ← mem_actSub, h]

private theorem le_aux : ∀ c : Perm (Fin 5), c ^ 3 = 1 → c ≠ 1 →
    (c * swap 0 2 = swap 0 2 * c ∨ c * swap 1 3 = swap 1 3 * c) →
    ∀ w : orth.W, PlaneP c w → ∃ y : orth.W, (∀ b ∈ S5ThatF, orth.act b y = y) ∧
      (∀ b ∈ S5ThatF, orth.act b (orth.act c⁻¹ (w * y⁻¹)) = orth.act c⁻¹ (w * y⁻¹)) := by
  decide +kernel

theorem planeOf_le_fixW {c : Perm (Fin 5)} (hc : IsThreeCyc c) :
    planeOf c ≤ fixW orth S5That ⊔ actSub c (fixW orth S5That) := by
  intro w hw
  rw [mem_planeOf_iff hc] at hw
  obtain ⟨y, hy, hz⟩ := le_aux c hc.1 hc.2.1 hc.2.2 w hw
  refine Subgroup.mem_sup.mpr ⟨y, ?_, w * y⁻¹, ?_, ?_⟩
  · intro b hb; rw [mem_S5That_iff] at hb; exact hy b hb
  · rw [mem_actSub]
    intro b hb; rw [mem_S5That_iff] at hb; exact hz b hb
  · rw [mul_comm w, mul_inv_cancel_left]

theorem offender_That {B : Subgroup (Perm (Fin 5))} (hB : B ≤ S5That) (hB0 : B ≠ ⊥)
    (hidx : (fixW orth B).index = Nat.card B) :
    B = Subgroup.zpowers (swap 0 2) ∨ B = Subgroup.zpowers (swap 1 3) ∨ B = S5That := by
  have hmem : ∀ x ∈ B, x = 1 ∨ x = swap 0 2 ∨ x = swap 1 3 ∨ x = swap 0 2 * swap 1 3 := by
    intro x hx
    have h1 := (mem_S5That_iff x).mp (hB hx)
    have h2 : ∀ x ∈ S5ThatF, x = 1 ∨ x = swap 0 2 ∨ x = swap 1 3 ∨ x = swap 0 2 * swap 1 3 := by
      decide +kernel
    exact h2 x h1
  have e1 : swap (0 : Fin 5) 2 * (swap 0 2 * swap 1 3) = swap 1 3 := by decide +kernel
  have e2 : swap (0 : Fin 5) 2 * swap 1 3 * swap 1 3 = swap 0 2 := by decide +kernel
  have hab2 : swap (0 : Fin 5) 2 * swap 1 3 ≠ 1 := by decide +kernel
  by_cases ha : swap (0 : Fin 5) 2 ∈ B <;> by_cases hb : swap (1 : Fin 5) 3 ∈ B
  · right; right
    refine le_antisymm hB ?_
    unfold S5That
    rw [Subgroup.closure_le]
    rintro x (rfl | rfl)
    exacts [ha, hb]
  · left
    have hab : swap (0 : Fin 5) 2 * swap 1 3 ∉ B := fun h => hb (by
      have := B.mul_mem ha h
      rwa [e1] at this)
    refine le_antisymm (fun x hx => ?_) (Subgroup.zpowers_le.mpr ha)
    rcases hmem x hx with rfl | rfl | rfl | rfl
    · exact one_mem _
    · exact Subgroup.mem_zpowers _
    · exact absurd hx hb
    · exact absurd hx hab
  · right; left
    have hab : swap (0 : Fin 5) 2 * swap 1 3 ∉ B := fun h => ha (by
      have := B.mul_mem h hb
      rwa [e2] at this)
    refine le_antisymm (fun x hx => ?_) (Subgroup.zpowers_le.mpr hb)
    rcases hmem x hx with rfl | rfl | rfl | rfl
    · exact one_mem _
    · exact absurd hx ha
    · exact Subgroup.mem_zpowers _
    · exact absurd hx hab
  · exfalso
    by_cases hab : swap (0 : Fin 5) 2 * swap 1 3 ∈ B
    · have hBeq : B = Subgroup.zpowers (swap 0 2 * swap 1 3) := by
        refine le_antisymm (fun x hx => ?_) (Subgroup.zpowers_le.mpr hab)
        rcases hmem x hx with rfl | rfl | rfl | rfl
        · exact one_mem _
        · exact absurd hx ha
        · exact absurd hx hb
        · exact Subgroup.mem_zpowers _
      subst hBeq
      have h4 : (fixW orth (Subgroup.zpowers (swap (0 : Fin 5) 2 * swap 1 3))).index = 4 := by
        have := idx_orth (swap (0 : Fin 5) 2 * swap 1 3)
        unfold idx at this
        rw [this]
        decide +kernel
      have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
      have hord : orderOf (swap (0 : Fin 5) 2 * swap 1 3) = 2 :=
        orderOf_eq_prime (by decide +kernel) hab2
      rw [h4, Nat.card_zpowers, hord] at hidx
      omega
    · apply hB0
      rw [eq_bot_iff]
      intro x hx
      rcases hmem x hx with rfl | rfl | rfl | rfl
      · exact one_mem _
      · exact absurd hx ha
      · exact absurd hx hb
      · exact absurd hx hab

theorem fixW_swap_ne : fixW orth (Subgroup.zpowers (swap 0 2)) ≠ fixW orth (Subgroup.zpowers (swap 1 3)) := by
  intro h
  have h' : ∀ w : orth.W, (orth.act (swap 0 2) w = w ↔ orth.act (swap 1 3) w = w) := fun w => by
    rw [← mem_fixW_zpowers, ← mem_fixW_zpowers, h]
  revert h'
  decide +kernel

private theorem conj_aux : ∀ σ ∈ S5SylF, σ ∉ S5ThatF →
    σ * swap 0 2 * σ⁻¹ = swap 1 3 ∧ σ * swap 1 3 * σ⁻¹ = swap 0 2 := by
  decide +kernel

theorem conj_zpowers_swap {σ : Perm (Fin 5)} (hσ : σ ∈ S5Syl) (hσ' : σ ∉ S5That) :
    (Subgroup.zpowers (swap 0 2)).map (MulAut.conj σ).toMonoidHom = Subgroup.zpowers (swap 1 3) ∧
    (Subgroup.zpowers (swap 1 3)).map (MulAut.conj σ).toMonoidHom = Subgroup.zpowers (swap 0 2) := by
  rw [mem_S5Syl_iff] at hσ
  rw [mem_S5That_iff] at hσ'
  obtain ⟨h1, h2⟩ := conj_aux σ hσ hσ'
  rw [MonoidHom.map_zpowers, MonoidHom.map_zpowers]
  exact ⟨by simpa using congrArg Subgroup.zpowers h1, by simpa using congrArg Subgroup.zpowers h2⟩

theorem exists_fixed_Syl : ∃ w : orth.W, w ≠ 1 ∧ ∀ σ ∈ S5Syl, orth.act σ w = w := by
  refine ⟨eps 4, by decide +kernel, fun σ hσ => ?_⟩
  rw [mem_S5Syl_iff] at hσ
  rw [act_eps]
  have : ∀ σ ∈ S5SylF, σ 4 = 4 := by decide +kernel
  rw [this σ hσ]

end CFSG.Quasithin.F53Mod
