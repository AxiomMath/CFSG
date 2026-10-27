module

public import CFSG.YGroups.Model432F
public import CFSG.YGroups.DoubleCosetPoints
public import CFSG.YGroups.Y442Twist.Group

public section

namespace CFSG.YGroups.Y442Tw

open CFSG.YGroups CFSG.Certificates.CosetEnumeration

theorem yRels432_even : ∀ w ∈ yRels 4 3 2, w.length % 2 = 0 := by decide +kernel

theorem evalWord_parity (w : List ℕ) :
    evalWord (fun _ => Multiplicative.ofAdd (1 : ZMod 2)) w =
      Multiplicative.ofAdd (w.length : ZMod 2) := by
  induction w with
  | nil => rfl
  | cons c w ih =>
    rw [evalWord_cons, ih, List.length_cons, Nat.cast_succ, ← ofAdd_add, add_comm]

@[expose] noncomputable def par432 : YGroup 4 3 2 →* Multiplicative (ZMod 2) :=
  yModelHom (fun _ => Multiplicative.ofAdd 1) (by
    intro w hw
    rw [evalWord_parity, ← ofAdd_zero]
    congr 1
    rw [ZMod.natCast_eq_zero_iff]
    exact Nat.dvd_of_mod_eq_zero (yRels432_even w hw))

theorem par432_evalWord {w : List ℕ} (hw : ∀ c ∈ w, c < 10) :
    par432 (evalWord (yGen 4 3 2) w) = Multiplicative.ofAdd (w.length : ZMod 2) := by
  rw [Y442Tw.evalWord_map_hom, ← evalWord_parity]
  refine evalWord_congr fun c hc => ?_
  exact yModelHom_yGen (by simp only [ngen]; have := hw c hc; omega)

theorem par432_F432 : par432 F432 = Multiplicative.ofAdd 1 := by
  rw [F432_eq_evalWord, par432_evalWord (by decide)]
  rfl

theorem F432_ne_one_par : par432 F432 ≠ 1 := by
  rw [par432_F432]
  decide

theorem eq_one_of_rho_par
    {y : YGroup 4 3 2} (hr : rho432F y = 1) (hp : par432 y = 1) :
    y = 1 := by
  have hfin := finite_y432
  have hk : y ∈ rho432F.ker := hr
  by_contra hy
  have hF : F432 ∈ rho432F.ker := F432_mem_ker
  have hyF : y ≠ F432 := by
    rintro rfl
    exact F432_ne_one_par hp
  have h1 : (1 : YGroup 4 3 2) ∈ rho432F.ker := rho432F.ker.one_mem
  classical
  have h3 : ({1, F432, y} : Finset (YGroup 4 3 2)).card = 3 := by
    rw [Finset.card_insert_of_notMem, Finset.card_pair hyF.symm]
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
    exact ⟨fun h => F432_ne_one h.symm, fun h => hy h.symm⟩
  have hle : ({1, F432, y} : Finset (YGroup 4 3 2)).card ≤ Nat.card rho432F.ker := by
    rw [← Nat.card_eq_finsetCard]
    apply Nat.card_mono (Set.toFinite _)
    intro z hz
    simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
      Set.mem_singleton_iff] at hz
    rcases hz with rfl | rfl | rfl
    · exact h1
    · exact hF
    · exact hk
  rw [h3, card_ker_rho432F] at hle
  omega

theorem eq_one_of_chain {n : ℕ} (S : Subgroup (Equiv.Perm (Fin n))) (k : ℕ) (β : ℕ → Fin n)
    (Y : ℕ → Set (Equiv.Perm (Fin n))) (hY : ∀ l < k, Y l ⊆ S)
    (hfix : ∀ l < k, ∀ y ∈ Y l, ∀ m < l, y (β m) = β m) (o : ℕ → ℕ)
    (horb : ∀ l < k, o l ≤ (MulAction.orbit (Subgroup.closure (Y l)) (β l)).ncard)
    (hS : Nat.card S ≤ ∏ l ∈ Finset.range k, o l) {g : Equiv.Perm (Fin n)} (hg : g ∈ S)
    (hgβ : ∀ m < k, g (β m) = β m) : g = 1 := by
  have hle : ∀ l < k, Subgroup.closure (Y l) ≤ chainStab S β l := by
    intro l hl
    rw [Subgroup.closure_le]
    intro y hy
    exact ⟨hY l hl hy, hfix l hl y hy⟩
  have key : ∀ j ≤ k, (∏ l ∈ Finset.range j, o l) * Nat.card (chainStab S β j) ≤
      Nat.card S := by
    intro j
    induction j with
    | zero =>
      intro _
      rw [chainStab_zero]
      simp
    | succ j ih =>
      intro hj
      rw [Finset.prod_range_succ]
      have h1 := ih (by omega)
      have h2 := card_chainStab_step S β j (hle j (by omega)) (horb j (by omega))
      calc (∏ l ∈ Finset.range j, o l) * o j * Nat.card (chainStab S β (j + 1))
          = (∏ l ∈ Finset.range j, o l) * (o j * Nat.card (chainStab S β (j + 1))) := by ring
        _ ≤ (∏ l ∈ Finset.range j, o l) * Nat.card (chainStab S β j) :=
          Nat.mul_le_mul_left _ h2
        _ ≤ Nat.card S := h1
  have hk := key k le_rfl
  have hSpos : 0 < Nat.card S := Nat.card_pos
  have hP : 0 < ∏ l ∈ Finset.range k, o l := by
    rcases Nat.eq_zero_or_pos (∏ l ∈ Finset.range k, o l) with h | h
    · rw [h] at hS
      omega
    · exact h
  have hC : Nat.card (chainStab S β k) ≤ 1 := by
    by_contra hc
    have : (∏ l ∈ Finset.range k, o l) * 2 ≤
        (∏ l ∈ Finset.range k, o l) * Nat.card (chainStab S β k) :=
      Nat.mul_le_mul_left _ (by omega)
    omega
  have hmem : g ∈ chainStab S β k := ⟨hg, hgβ⟩
  rw [Subgroup.eq_bot_of_card_le _ hC] at hmem
  exact (Subgroup.mem_bot).1 hmem

end CFSG.YGroups.Y442Tw

end
