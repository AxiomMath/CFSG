module

public import CFSG.HardMathSupport.Cooperstein.Coordinator.NaturalBridgeHeart

public section

namespace CFSG.RankThree.PartTwo.Sec19.SolEven

open CFSG.RankThree.PartTwo CFSG.QuasithinUnique CFSG.HardMathSupport.Cooperstein.Coordinator
  Equiv Equiv.Perm

variable {n : ℕ}

abbrev permBar (n : ℕ) : Type := (Fin n → ZMod 2) ⧸ AddSubgroup.zmultiples (allOnes n)

@[expose] def vecPerm (σ : Perm (Fin n)) : (Fin n → ZMod 2) →+ (Fin n → ZMod 2) where
  toFun x := fun i => x (σ⁻¹ i)
  map_zero' := rfl
  map_add' _ _ := rfl

theorem vecPerm_apply (σ : Perm (Fin n)) (x : Fin n → ZMod 2) (i : Fin n) :
    vecPerm σ x i = x (σ⁻¹ i) := rfl

theorem vecPerm_mem_zmultiples (σ : Perm (Fin n)) {x : Fin n → ZMod 2}
    (hx : x ∈ AddSubgroup.zmultiples (allOnes n)) :
    vecPerm σ x ∈ AddSubgroup.zmultiples (allOnes n) := by
  obtain ⟨k, rfl⟩ := AddSubgroup.mem_zmultiples_iff.1 hx
  exact AddSubgroup.mem_zmultiples_iff.2 ⟨k, rfl⟩

@[expose] noncomputable def barAct (σ : Perm (Fin n)) : permBar n →+ permBar n :=
  QuotientAddGroup.map _ _ (vecPerm σ) fun _ hx => vecPerm_mem_zmultiples σ hx

theorem barAct_mk (σ : Perm (Fin n)) (x : Fin n → ZMod 2) :
    barAct σ (x : permBar n) = (vecPerm σ x : permBar n) := rfl

theorem barAct_mul (σ τ : Perm (Fin n)) (v : permBar n) :
    barAct (σ * τ) v = barAct σ (barAct τ v) := by
  obtain ⟨x, rfl⟩ := QuotientAddGroup.mk_surjective v
  rfl

theorem barAct_one (v : permBar n) : barAct 1 v = v := by
  obtain ⟨x, rfl⟩ := QuotientAddGroup.mk_surjective v
  rfl

@[expose] noncomputable def heartToBar : altHeart n →+ permBar n :=
  QuotientAddGroup.map _ _ (evenWeight n).subtype fun x hx => by
    simpa [evenWeightOnes, AddSubgroup.mem_addSubgroupOf] using hx

theorem heartToBar_mk (x : evenWeight n) :
    heartToBar (x : altHeart n) = ((x : Fin n → ZMod 2) : permBar n) := rfl

theorem heartToBar_injective : Function.Injective (heartToBar (n := n)) := by
  rw [injective_iff_map_eq_zero]
  intro v hv
  obtain ⟨x, rfl⟩ := QuotientAddGroup.mk_surjective v
  rw [heartToBar_mk, QuotientAddGroup.eq_zero_iff] at hv
  exact (QuotientAddGroup.eq_zero_iff _).2 (by
    simpa [evenWeightOnes, AddSubgroup.mem_addSubgroupOf] using hv)

theorem heartToBar_altAct (σ : Perm (Fin n)) (v : altHeart n) :
    heartToBar (altAct σ v) = barAct σ (heartToBar v) := by
  obtain ⟨x, rfl⟩ := QuotientAddGroup.mk_surjective v
  rfl

@[expose] def vecWt (x : Fin n → ZMod 2) : ℕ := (Finset.univ.filter fun i => x i = 1).card

theorem vecWt_le (x : Fin n → ZMod 2) : vecWt x ≤ n := by
  unfold vecWt
  calc (Finset.univ.filter fun i => x i = 1).card ≤ (Finset.univ : Finset (Fin n)).card :=
        Finset.card_filter_le _ _
    _ = n := by simp

theorem zmod_two_eq_zero_iff_ne_one (a : ZMod 2) : a = 0 ↔ a ≠ 1 := by
  revert a; decide

theorem zmod_two_cases' (a : ZMod 2) : a = 0 ∨ a = 1 := by
  revert a; decide

theorem vecWt_add_allOnes (x : Fin n → ZMod 2) : vecWt (x + allOnes n) = n - vecWt x := by
  classical
  have hpt : ∀ i, (x + allOnes n) i = 1 ↔ ¬ x i = 1 := by
    intro i
    show x i + 1 = 1 ↔ ¬ x i = 1
    rcases zmod_two_cases' (x i) with h | h <;> rw [h] <;> decide
  have h1 : (Finset.univ.filter fun i => (x + allOnes n) i = 1) =
      Finset.univ.filter fun i => ¬ x i = 1 :=
    Finset.filter_congr fun i _ => hpt i
  have h2 := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Fin n)))
    (fun i => x i = 1)
  simp only [Finset.card_univ, Fintype.card_fin] at h2
  unfold vecWt
  rw [h1]
  omega

theorem mem_zmultiples_allOnes_iff (z : Fin n → ZMod 2) :
    z ∈ AddSubgroup.zmultiples (allOnes n) ↔ z = 0 ∨ z = allOnes n := by
  rw [AddSubgroup.mem_zmultiples_iff]
  constructor
  · rintro ⟨k, rfl⟩
    have hk : k • allOnes n = fun _ => ((k : ZMod 2)) := by
      funext i
      simp [allOnes]
    rw [hk]
    rcases zmod_two_cases' (k : ZMod 2) with h | h
    · left
      rw [h]
      rfl
    · right
      rw [h]
      rfl
  · rintro (rfl | rfl)
    · exact ⟨0, zero_zsmul _⟩
    · exact ⟨1, one_zsmul _⟩

@[expose] noncomputable def barLen (v : permBar n) : ℕ :=
  Quotient.liftOn' v (fun x => min (vecWt x) (n - vecWt x)) fun x y h => by
    have h' : -x + y ∈ AddSubgroup.zmultiples (allOnes n) := QuotientAddGroup.leftRel_apply.1 h
    rcases (mem_zmultiples_allOnes_iff _).1 h' with h0 | h1
    · have : y = x := (neg_add_eq_zero.1 h0).symm
      rw [this]
    · have : y = x + allOnes n := neg_add_eq_iff_eq_add.1 h1
      show min (vecWt x) (n - vecWt x) = min (vecWt y) (n - vecWt y)
      rw [this, vecWt_add_allOnes]
      have := vecWt_le x
      omega

theorem barLen_mk (x : Fin n → ZMod 2) :
    barLen (x : permBar n) = min (vecWt x) (n - vecWt x) := rfl

end CFSG.RankThree.PartTwo.Sec19.SolEven
