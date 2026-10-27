module

public import CFSG.RankThree.PartOne.KE6.E6LRoots
public import CFSG.LieType.Chevalley.KernelComponentRoots
public import CFSG.RankThree.Lattice.SteinbergBIListMatrix

public noncomputable section

namespace CFSG.RankThree.PartOne.KE6

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
open CFSG.RankThree.PartOne.KD4T

@[expose] def rho6Perm : Equiv.Perm (Fin Tag.E6.rank) := Equiv.swap 0 5 * Equiv.swap 2 4

@[expose] def rho6 (k : Fin Tag.E6.rank) : Fin Tag.E6.rank := rho6Perm k

theorem rho6_rho6 (k : Fin Tag.E6.rank) : rho6 (rho6 k) = k := by
  revert k
  decide

section Rho

variable {τ : Tag} [E6Sub τ]

@[expose] def rhoτ (τ : Tag) [E6Sub τ] : Equiv.Perm (Fin τ.rank) :=
  rho6Perm.viaFintypeEmbedding ⟨e6Idx, e6Idx_injective⟩

theorem rhoτ_e6Idx (k : Fin Tag.E6.rank) : rhoτ τ (e6Idx k) = e6Idx (rho6 k) :=
  Equiv.Perm.viaFintypeEmbedding_apply_image rho6Perm ⟨e6Idx, e6Idx_injective⟩ k

theorem rhoτ_of_not_mem {i : Fin τ.rank} (hi : i ∉ e6Set τ) : rhoτ τ i = i :=
  Equiv.Perm.viaFintypeEmbedding_apply_notMem_range rho6Perm ⟨e6Idx, e6Idx_injective⟩
    (fun ⟨k, hk⟩ => hi (hk ▸ e6Idx_mem_e6Set k))

theorem rhoτ_mem {i : Fin τ.rank} (hi : i ∈ e6Set τ) : rhoτ τ i ∈ e6Set τ := by
  obtain ⟨k, rfl⟩ := exists_e6Idx_eq (τ := τ) (e6Set_lt hi)
  rw [rhoτ_e6Idx]
  exact e6Idx_mem_e6Set _

theorem rhoτ_symm_mem {i : Fin τ.rank} (hi : i ∈ e6Set τ) : (rhoτ τ).symm i ∈ e6Set τ := by
  obtain ⟨k, rfl⟩ := exists_e6Idx_eq (τ := τ) (e6Set_lt hi)
  have h : (rhoτ τ) (e6Idx (rho6 k)) = e6Idx k := by rw [rhoτ_e6Idx, rho6_rho6]
  rw [(Equiv.symm_apply_eq (rhoτ τ)).2 h.symm]
  exact e6Idx_mem_e6Set _

end Rho

section Maps

variable {τ : Tag}

@[expose] def MapsJ (τ : Tag) (J : Set (Fin τ.rank)) (w : WeylGroup τ) : Prop :=
  ∀ α ∈ parabolicRoots τ J, w • α ∈ parabolicRoots τ J

theorem MapsJ.mul {J : Set (Fin τ.rank)} {w v : WeylGroup τ} (hw : MapsJ τ J w)
    (hv : MapsJ τ J v) : MapsJ τ J (w * v) := fun α hα => by
  rw [mul_smul]
  exact hw _ (hv α hα)

theorem MapsJ.one {J : Set (Fin τ.rank)} : MapsJ τ J (1 : WeylGroup τ) := fun α hα => by
  rw [one_smul]
  exact hα

theorem mapsJ_simple {J : Set (Fin τ.rank)} {i : Fin τ.rank} (hi : i ∈ J) :
    MapsJ τ J (simple τ i) := fun α hα => by
  refine ⟨IsRoot.smul hα.1 _, fun k hk => ?_⟩
  have hs : simple τ i ∈ parabolicWeylGroup τ J := Subgroup.subset_closure ⟨i, hi, rfl⟩
  rw [smul_apply_of_mem_parabolicWeylGroup hs α hk]
  exact hα.2 k hk

theorem MapsJ.inv {J : Set (Fin τ.rank)} {w : WeylGroup τ} (hw : MapsJ τ J w) :
    MapsJ τ J w⁻¹ := by
  have hfin : (parabolicRoots τ J).Finite := (finite_setOf_isRoot τ).subset fun α hα => hα.1
  have hm : Set.MapsTo (fun α => w • α) (parabolicRoots τ J) (parabolicRoots τ J) := hw
  have hb := (hfin.injOn_iff_bijOn_of_mapsTo hm).1 (MulAction.injective w).injOn
  intro α hα
  obtain ⟨β, hβ, hβα⟩ := hb.2.2 hα
  have : w⁻¹ • α = β := by rw [← hβα]; exact inv_smul_smul w β
  rw [this]
  exact hβ

theorem mapsJ_of_mem_parabolicWeylGroup {J : Set (Fin τ.rank)} {u : WeylGroup τ}
    (hu : u ∈ parabolicWeylGroup τ J) : MapsJ τ J u := by
  induction hu using Subgroup.closure_induction with
  | mem x hx =>
    obtain ⟨i, hi, rfl⟩ := hx
    exact mapsJ_simple hi
  | one => exact MapsJ.one
  | mul x y _ _ hx hy => exact hx.mul hy
  | inv x _ hx => exact hx.inv

theorem exists_descent (J : Set (Fin τ.rank)) : ∀ (n : ℕ) (w : WeylGroup τ),
    (coxeterSystem τ).length w = n → MapsJ τ J w →
    ∃ u ∈ parabolicWeylGroup τ J, ∃ w₀ : WeylGroup τ, w = u * w₀ ∧ MapsJ τ J w₀ ∧
      ∀ j ∈ J, 0 < height (w₀⁻¹ • (Pi.single j 1 : Fin τ.rank → ℤ)) := by
  intro n
  induction n with
  | zero =>
    intro w hw hmaps
    rw [CoxeterSystem.length_eq_zero_iff] at hw
    subst hw
    refine ⟨1, one_mem _, 1, by simp, hmaps, fun j _ => ?_⟩
    rw [inv_one, one_smul, height_single]
    exact one_pos
  | succ n ih =>
    intro w hw hmaps
    by_cases hall : ∀ j ∈ J, 0 < height (w⁻¹ • (Pi.single j 1 : Fin τ.rank → ℤ))
    · exact ⟨1, one_mem _, w, by simp, hmaps, hall⟩
    · push Not at hall
      obtain ⟨j, hj, hneg⟩ := hall
      have hroot : IsRoot τ (w⁻¹ • (Pi.single j 1 : Fin τ.rank → ℤ)) :=
        IsRoot.smul (isRoot_single τ j) _
      have hneg' : height (w⁻¹ • (Pi.single j 1 : Fin τ.rank → ℤ)) < 0 := by
        rcases IsRoot.height_pos_or_neg hroot with h | h
        · exact absurd h (not_lt.2 hneg)
        · exact h
      have hlen := ((weyl_exchange_condition τ).1 w j).1 ⟨hroot, hneg'⟩
      rw [hw, Nat.add_sub_cancel] at hlen
      obtain ⟨u', hu', w₀, hw₀, hm₀, hpos⟩ := ih (simple τ j * w) hlen
        ((mapsJ_simple hj).mul hmaps)
      refine ⟨simple τ j * u', mul_mem (Subgroup.subset_closure ⟨j, hj, rfl⟩) hu', w₀, ?_, hm₀,
        hpos⟩
      rw [mul_assoc, ← hw₀, ← mul_assoc, CoxeterSystem.simple_mul_simple_self, one_mul]

end Maps

@[expose] def gramOK (τ : Tag) [E6Sub τ] (a b : Fin 36) (i j : Fin Tag.E6.rank) : Prop :=
  iform (τ := τ) (e6Lat τ (posRoot6 a)) (e6Lat τ (posRoot6 b)) =
    iform (τ := τ) (Pi.single (e6Idx i) 1) (Pi.single (e6Idx j) 1)

instance (τ : Tag) [E6Sub τ] (a b : Fin 36) (i j : Fin Tag.E6.rank) : Decidable (gramOK τ a b i j) :=
  inferInstanceAs (Decidable (_ = _))

@[expose] def Base6E7L5 (a0 a1 a2 a3 a4 : Fin 36) : Prop :=
  ∀ a5 : Fin 36,
    gramOK Tag.E7 a5 a0 5 0 →
    gramOK Tag.E7 a5 a1 5 1 →
    gramOK Tag.E7 a5 a2 5 2 →
    gramOK Tag.E7 a5 a3 5 3 →
    gramOK Tag.E7 a5 a4 5 4 →
    gramOK Tag.E7 a5 a5 5 5 →
    ((a0 = 5 ∧ a1 = 4 ∧ a2 = 3 ∧ a3 = 2 ∧ a4 = 1 ∧ a5 = 0) ∨
      (a0 = 0 ∧ a1 = 4 ∧ a2 = 1 ∧ a3 = 2 ∧ a4 = 3 ∧ a5 = 5))

instance (a0 a1 a2 a3 a4 : Fin 36) : Decidable (Base6E7L5 a0 a1 a2 a3 a4) := by
  unfold Base6E7L5
  infer_instance

@[expose] def Base6E7L4 (a0 a1 a2 a3 : Fin 36) : Prop :=
  ∀ a4 : Fin 36,
    gramOK Tag.E7 a4 a0 4 0 →
    gramOK Tag.E7 a4 a1 4 1 →
    gramOK Tag.E7 a4 a2 4 2 →
    gramOK Tag.E7 a4 a3 4 3 →
    gramOK Tag.E7 a4 a4 4 4 →
    Base6E7L5 a0 a1 a2 a3 a4

instance (a0 a1 a2 a3 : Fin 36) : Decidable (Base6E7L4 a0 a1 a2 a3) := by
  unfold Base6E7L4
  infer_instance

@[expose] def Base6E7L3 (a0 a1 a2 : Fin 36) : Prop :=
  ∀ a3 : Fin 36,
    gramOK Tag.E7 a3 a0 3 0 →
    gramOK Tag.E7 a3 a1 3 1 →
    gramOK Tag.E7 a3 a2 3 2 →
    gramOK Tag.E7 a3 a3 3 3 →
    Base6E7L4 a0 a1 a2 a3

instance (a0 a1 a2 : Fin 36) : Decidable (Base6E7L3 a0 a1 a2) := by
  unfold Base6E7L3
  infer_instance

@[expose] def Base6E7L2 (a0 a1 : Fin 36) : Prop :=
  ∀ a2 : Fin 36,
    gramOK Tag.E7 a2 a0 2 0 →
    gramOK Tag.E7 a2 a1 2 1 →
    gramOK Tag.E7 a2 a2 2 2 →
    Base6E7L3 a0 a1 a2

instance (a0 a1 : Fin 36) : Decidable (Base6E7L2 a0 a1) := by
  unfold Base6E7L2
  infer_instance

@[expose] def Base6E7L1 (a0 : Fin 36) : Prop :=
  ∀ a1 : Fin 36,
    gramOK Tag.E7 a1 a0 1 0 →
    gramOK Tag.E7 a1 a1 1 1 →
    Base6E7L2 a0 a1

instance (a0 : Fin 36) : Decidable (Base6E7L1 a0) := by
  unfold Base6E7L1
  infer_instance

theorem base6_E7 : ∀ a0 : Fin 36, gramOK Tag.E7 a0 a0 0 0 → Base6E7L1 a0 := by
  decide +kernel

@[expose] def Base6E8L5 (a0 a1 a2 a3 a4 : Fin 36) : Prop :=
  ∀ a5 : Fin 36,
    gramOK Tag.E8 a5 a0 5 0 →
    gramOK Tag.E8 a5 a1 5 1 →
    gramOK Tag.E8 a5 a2 5 2 →
    gramOK Tag.E8 a5 a3 5 3 →
    gramOK Tag.E8 a5 a4 5 4 →
    gramOK Tag.E8 a5 a5 5 5 →
    ((a0 = 5 ∧ a1 = 4 ∧ a2 = 3 ∧ a3 = 2 ∧ a4 = 1 ∧ a5 = 0) ∨
      (a0 = 0 ∧ a1 = 4 ∧ a2 = 1 ∧ a3 = 2 ∧ a4 = 3 ∧ a5 = 5))

instance (a0 a1 a2 a3 a4 : Fin 36) : Decidable (Base6E8L5 a0 a1 a2 a3 a4) := by
  unfold Base6E8L5
  infer_instance

@[expose] def Base6E8L4 (a0 a1 a2 a3 : Fin 36) : Prop :=
  ∀ a4 : Fin 36,
    gramOK Tag.E8 a4 a0 4 0 →
    gramOK Tag.E8 a4 a1 4 1 →
    gramOK Tag.E8 a4 a2 4 2 →
    gramOK Tag.E8 a4 a3 4 3 →
    gramOK Tag.E8 a4 a4 4 4 →
    Base6E8L5 a0 a1 a2 a3 a4

instance (a0 a1 a2 a3 : Fin 36) : Decidable (Base6E8L4 a0 a1 a2 a3) := by
  unfold Base6E8L4
  infer_instance

@[expose] def Base6E8L3 (a0 a1 a2 : Fin 36) : Prop :=
  ∀ a3 : Fin 36,
    gramOK Tag.E8 a3 a0 3 0 →
    gramOK Tag.E8 a3 a1 3 1 →
    gramOK Tag.E8 a3 a2 3 2 →
    gramOK Tag.E8 a3 a3 3 3 →
    Base6E8L4 a0 a1 a2 a3

instance (a0 a1 a2 : Fin 36) : Decidable (Base6E8L3 a0 a1 a2) := by
  unfold Base6E8L3
  infer_instance

@[expose] def Base6E8L2 (a0 a1 : Fin 36) : Prop :=
  ∀ a2 : Fin 36,
    gramOK Tag.E8 a2 a0 2 0 →
    gramOK Tag.E8 a2 a1 2 1 →
    gramOK Tag.E8 a2 a2 2 2 →
    Base6E8L3 a0 a1 a2

instance (a0 a1 : Fin 36) : Decidable (Base6E8L2 a0 a1) := by
  unfold Base6E8L2
  infer_instance

@[expose] def Base6E8L1 (a0 : Fin 36) : Prop :=
  ∀ a1 : Fin 36,
    gramOK Tag.E8 a1 a0 1 0 →
    gramOK Tag.E8 a1 a1 1 1 →
    Base6E8L2 a0 a1

instance (a0 : Fin 36) : Decidable (Base6E8L1 a0) := by
  unfold Base6E8L1
  infer_instance

theorem base6_E8 : ∀ a0 : Fin 36, gramOK Tag.E8 a0 a0 0 0 → Base6E8L1 a0 := by
  decide +kernel

theorem posRoot6_vec1 : ∀ k : Fin Tag.E6.rank,
    posRoot6 (![5, 4, 3, 2, 1, 0] k) = Pi.single k 1 := by
  decide +kernel

theorem posRoot6_vec2 : ∀ k : Fin Tag.E6.rank,
    posRoot6 (![0, 4, 1, 2, 3, 5] k) = Pi.single (rho6 k) 1 := by
  decide +kernel

section Base

variable {τ : Tag} [M27Ok τ] [E6Sub τ]

theorem base6_of_gram {a : Fin Tag.E6.rank → Fin 36}
    (hg : ∀ k i : Fin Tag.E6.rank, i ≤ k → gramOK τ (a k) (a i) k i) :
    (∀ k, posRoot6 (a k) = Pi.single k 1) ∨ (∀ k, posRoot6 (a k) = Pi.single (rho6 k) 1) := by
  have key : ((a 0 = 5 ∧ a 1 = 4 ∧ a 2 = 3 ∧ a 3 = 2 ∧ a 4 = 1 ∧ a 5 = 0) ∨
      (a 0 = 0 ∧ a 1 = 4 ∧ a 2 = 1 ∧ a 3 = 2 ∧ a 4 = 3 ∧ a 5 = 5)) := by
    rcases M27Ok.isE7E8 (τ := τ) with rfl | rfl
    · exact base6_E7 (a 0) (hg 0 0 le_rfl) (a 1) (hg 1 0 (by decide)) (hg 1 1 le_rfl) (a 2)
        (hg 2 0 (by decide)) (hg 2 1 (by decide)) (hg 2 2 le_rfl) (a 3) (hg 3 0 (by decide))
        (hg 3 1 (by decide)) (hg 3 2 (by decide)) (hg 3 3 le_rfl) (a 4) (hg 4 0 (by decide))
        (hg 4 1 (by decide)) (hg 4 2 (by decide)) (hg 4 3 (by decide)) (hg 4 4 le_rfl) (a 5)
        (hg 5 0 (by decide)) (hg 5 1 (by decide)) (hg 5 2 (by decide)) (hg 5 3 (by decide))
        (hg 5 4 (by decide)) (hg 5 5 le_rfl)
    · exact base6_E8 (a 0) (hg 0 0 le_rfl) (a 1) (hg 1 0 (by decide)) (hg 1 1 le_rfl) (a 2)
        (hg 2 0 (by decide)) (hg 2 1 (by decide)) (hg 2 2 le_rfl) (a 3) (hg 3 0 (by decide))
        (hg 3 1 (by decide)) (hg 3 2 (by decide)) (hg 3 3 le_rfl) (a 4) (hg 4 0 (by decide))
        (hg 4 1 (by decide)) (hg 4 2 (by decide)) (hg 4 3 (by decide)) (hg 4 4 le_rfl) (a 5)
        (hg 5 0 (by decide)) (hg 5 1 (by decide)) (hg 5 2 (by decide)) (hg 5 3 (by decide))
        (hg 5 4 (by decide)) (hg 5 5 le_rfl)
  rcases key with ⟨h0, h1, h2, h3, h4, h5⟩ | ⟨h0, h1, h2, h3, h4, h5⟩
  · left
    have ha : a = ![5, 4, 3, 2, 1, 0] := by
      funext k
      fin_cases k
      · exact h0
      · exact h1
      · exact h2
      · exact h3
      · exact h4
      · exact h5
    intro k
    rw [ha]
    exact posRoot6_vec1 k
  · right
    have ha : a = ![0, 4, 1, 2, 3, 5] := by
      funext k
      fin_cases k
      · exact h0
      · exact h1
      · exact h2
      · exact h3
      · exact h4
      · exact h5
    intro k
    rw [ha]
    exact posRoot6_vec2 k

theorem base_of_pos {v : WeylGroup τ} (hv : MapsJ τ (e6Set τ) v)
    (hpos : ∀ j ∈ e6Set τ, 0 < height (v • (Pi.single j 1 : Fin τ.rank → ℤ))) :
    (∀ k : Fin Tag.E6.rank, v • (Pi.single (e6Idx k) 1 : Fin τ.rank → ℤ) = Pi.single (e6Idx k) 1) ∨
      (∀ k : Fin Tag.E6.rank, v • (Pi.single (e6Idx k) 1 : Fin τ.rank → ℤ) =
        Pi.single (e6Idx (rho6 k)) 1) := by
  have hex : ∀ k : Fin Tag.E6.rank, ∃ a : Fin 36,
      e6Lat τ (posRoot6 a) = v • (Pi.single (e6Idx k) 1 : Fin τ.rank → ℤ) := by
    intro k
    have hmem := hv _ (single_mem_parabolicRoots (e6Idx_mem_e6Set k))
    obtain ⟨γ, hγ, hγe⟩ := mem_parabolicRoots_e6Set_iff.1 hmem
    have hp : 0 < height γ := by
      have := hpos (e6Idx k) (e6Idx_mem_e6Set k)
      rw [← hγe, height_e6Lat'] at this
      exact this
    obtain ⟨a, rfl⟩ := exists_posRoot6 hγ hp
    exact ⟨a, hγe⟩
  choose a ha using hex
  have hg : ∀ k i : Fin Tag.E6.rank, i ≤ k → gramOK τ (a k) (a i) k i := fun k i _ => by
    unfold gramOK
    rw [ha k, ha i, iform_smul]
  rcases base6_of_gram hg with h | h
  · left
    intro k
    rw [← ha k, h k, e6Lat_single]
  · right
    intro k
    rw [← ha k, h k, e6Lat_single]

end Base

theorem exists_action {τ : Tag} [M27Ok τ] [E6Sub τ] {w : WeylGroup τ}
    (hw : MapsJ τ (e6Set τ) w) :
    ∃ u ∈ parabolicWeylGroup τ (e6Set τ), ∃ π : Equiv.Perm (Fin τ.rank), (π = 1 ∨ π = rhoτ τ) ∧
      ∀ j ∈ e6Set τ, w • (Pi.single j 1 : Fin τ.rank → ℤ) = u • (Pi.single (π j) 1 : Fin τ.rank → ℤ) := by
  obtain ⟨u, hu, w₀, hw₀, hm₀, hpos⟩ := exists_descent (e6Set τ) _ w rfl hw
  have hv : MapsJ τ (e6Set τ) w₀⁻¹ := hm₀.inv
  have hinv : ∀ (x y : Fin τ.rank → ℤ), w₀⁻¹ • x = y → w₀ • y = x := fun x y h => by
    rw [← h, smul_inv_smul]
  rcases base_of_pos hv hpos with h | h
  · refine ⟨u, hu, 1, Or.inl rfl, fun j hj => ?_⟩
    obtain ⟨k, rfl⟩ := exists_e6Idx_eq (τ := τ) (e6Set_lt hj)
    rw [hw₀, mul_smul, hinv _ _ (h k)]
    rfl
  · refine ⟨u, hu, rhoτ τ, Or.inr rfl, fun j hj => ?_⟩
    obtain ⟨k, rfl⟩ := exists_e6Idx_eq (τ := τ) (e6Set_lt hj)
    rw [hw₀, mul_smul, rhoτ_e6Idx]
    have := hinv _ _ (h (rho6 k))
    rw [rho6_rho6] at this
    rw [this]

end CFSG.RankThree.PartOne.KE6
