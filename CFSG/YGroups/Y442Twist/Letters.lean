module

public import CFSG.YGroups.Y442Twist.Model

public section

namespace CFSG.YGroups.Y442Tw

open CFSG.YGroups CFSG.Certificates.CosetEnumeration

@[expose] def lsub (L : List ℕ) : Subgroup (YGroup 4 3 2) :=
  Subgroup.closure (yGen 4 3 2 '' {c | c ∈ L})

@[expose] def evenSub (L : List ℕ) (c₀ : ℕ) : Subgroup (YGroup 4 3 2) :=
  Subgroup.closure ((fun c => yGen 4 3 2 c₀ * yGen 4 3 2 c) '' {c | c ∈ L})

@[expose] def allL : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9]

theorem lsub_all : lsub allL = ⊤ := by
  rw [lsub, ← closure_yGen 4 3 2]
  congr 2
  ext c
  simp only [allL, ngen, Set.mem_setOf_eq, Set.mem_Iio, List.mem_cons, List.not_mem_nil,
    or_false]
  omega

theorem yGen_mem_lsub {L : List ℕ} {c : ℕ} (hc : c ∈ L) : yGen 4 3 2 c ∈ lsub L :=
  Subgroup.subset_closure ⟨c, hc, rfl⟩

theorem evalWord_mem_lsub {L : List ℕ} {w : List ℕ} (hw : ∀ c ∈ w, c ∈ L) :
    evalWord (yGen 4 3 2) w ∈ lsub L := by
  induction w with
  | nil => exact (lsub L).one_mem
  | cons c w ih =>
    rw [evalWord_cons]
    exact (lsub L).mul_mem (yGen_mem_lsub (hw c List.mem_cons_self))
      (ih fun c' hc' => hw c' (List.mem_cons_of_mem _ hc'))

theorem par432_yGen {c : ℕ} (hc : c < 10) : par432 (yGen 4 3 2 c) = Multiplicative.ofAdd 1 :=
  yModelHom_yGen (by simp only [ngen]; omega)

theorem evenSub_le_ker {L : List ℕ} (hL : ∀ c ∈ L, c < 10) {c₀ : ℕ} (hc₀ : c₀ < 10) :
    evenSub L c₀ ≤ par432.ker := by
  rw [evenSub, Subgroup.closure_le]
  rintro _ ⟨c, hc, rfl⟩
  rw [SetLike.mem_coe, MonoidHom.mem_ker, map_mul, par432_yGen hc₀, par432_yGen (hL c hc),
    ← ofAdd_add]
  decide

theorem evenSub_le_lsub {L : List ℕ} {c₀ : ℕ} (hc₀ : c₀ ∈ L) : evenSub L c₀ ≤ lsub L := by
  rw [evenSub, Subgroup.closure_le]
  rintro _ ⟨c, hc, rfl⟩
  exact (lsub L).mul_mem (yGen_mem_lsub hc₀) (yGen_mem_lsub hc)

theorem mem_evenSub_or {L : List ℕ} {c₀ : ℕ} (hc₀ : c₀ ∈ L) {y : YGroup 4 3 2}
    (hy : y ∈ lsub L) : y ∈ evenSub L c₀ ∨ yGen 4 3 2 c₀ * y ∈ evenSub L c₀ := by
  set E := evenSub L c₀
  have hgen : ∀ c ∈ L, yGen 4 3 2 c₀ * yGen 4 3 2 c ∈ E := fun c hc =>
    Subgroup.subset_closure ⟨c, hc, rfl⟩
  have h0 := yGen_mul_self 4 3 2 c₀
  have step : ∀ c ∈ L, ∀ x, (x ∈ E ∨ yGen 4 3 2 c₀ * x ∈ E) →
      (yGen 4 3 2 c * x ∈ E ∨ yGen 4 3 2 c₀ * (yGen 4 3 2 c * x) ∈ E) := by
    intro c hc x hx
    rcases hx with hx | hx
    · right
      rw [← mul_assoc]
      exact E.mul_mem (hgen c hc) hx
    · left
      have e : yGen 4 3 2 c * x = (yGen 4 3 2 c₀ * yGen 4 3 2 c)⁻¹ * (yGen 4 3 2 c₀ * x) := by
        rw [mul_inv_rev, yGen_inv, yGen_inv]
        calc yGen 4 3 2 c * x = yGen 4 3 2 c * (yGen 4 3 2 c₀ * yGen 4 3 2 c₀) * x := by
              rw [h0, mul_one]
          _ = _ := by group
      rw [e]
      exact E.mul_mem (E.inv_mem (hgen c hc)) hx
  induction hy using Subgroup.closure_induction_left with
  | one => exact Or.inl E.one_mem
  | mul_left c hc y _ ih =>
    obtain ⟨c, hc, rfl⟩ := hc
    exact step c hc y ih
  | inv_mul_cancel c hc y _ ih =>
    obtain ⟨c, hc, rfl⟩ := hc
    rw [yGen_inv]
    exact step c hc y ih

theorem mem_evenSub_or' {L : List ℕ} {c₀ : ℕ} (hc₀ : c₀ ∈ L) {y : YGroup 4 3 2}
    (hy : y ∈ lsub L) : y ∈ evenSub L c₀ ∨ y * yGen 4 3 2 c₀ ∈ evenSub L c₀ := by
  rcases mem_evenSub_or hc₀ ((lsub L).inv_mem hy) with h | h
  · exact Or.inl (by simpa using (evenSub L c₀).inv_mem h)
  · right
    have := (evenSub L c₀).inv_mem h
    rwa [mul_inv_rev, inv_inv, yGen_inv] at this

theorem evenSub_eq {L : List ℕ} (hL : ∀ c ∈ L, c < 10) {c₀ : ℕ} (hc₀ : c₀ ∈ L) :
    evenSub L c₀ = lsub L ⊓ par432.ker := by
  refine le_antisymm (le_inf (evenSub_le_lsub hc₀) (evenSub_le_ker hL (hL c₀ hc₀))) ?_
  rintro y ⟨hy, hp⟩
  rcases mem_evenSub_or hc₀ hy with h | h
  · exact h
  · exfalso
    have h2 := evenSub_le_ker hL (hL c₀ hc₀) h
    rw [MonoidHom.mem_ker, map_mul, par432_yGen (hL c₀ hc₀), MonoidHom.mem_ker.1 hp,
      mul_one] at h2
    exact absurd h2 (by decide)

theorem index_ker_par432 : par432.ker.index ≤ 2 := by
  rw [Subgroup.index_ker]
  calc Nat.card par432.range ≤ Nat.card (Multiplicative (ZMod 2)) := Subgroup.card_le_card_group _
    _ = 2 := by rw [Nat.card_congr (Multiplicative.toAdd : Multiplicative (ZMod 2) ≃ ZMod 2),
        Nat.card_zmod]

theorem index_evenSub_le {L : List ℕ} (hL : ∀ c ∈ L, c < 10) {c₀ : ℕ} (hc₀ : c₀ ∈ L) :
    (evenSub L c₀).index ≤ 2 * (lsub L).index := by
  rw [evenSub_eq hL hc₀]
  calc (lsub L ⊓ par432.ker).index ≤ (lsub L).index * par432.ker.index := Subgroup.index_inf_le
    _ ≤ (lsub L).index * 2 := Nat.mul_le_mul_left _ index_ker_par432
    _ = 2 * (lsub L).index := Nat.mul_comm _ _

end CFSG.YGroups.Y442Tw

end
