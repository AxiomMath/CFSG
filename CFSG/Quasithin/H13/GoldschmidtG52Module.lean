module

public import CFSG.Quasithin.H13.GoldschmidtG52Classify
public import CFSG.Quasithin.H13.GoldschmidtG52Finite
public import CFSG.Quasithin.H13.A6G5

public section

namespace CFSG.Quasithin.H13.A6.G52

open CFSG.CharacterTheory.SteinbergBY CFSG.CharacterTheory.SteinbergBY.AlternatingSix Equiv Matrix

theorem g1a_mem : g1a ∈ g5G1 := ⟨by decide, Or.inl ⟨by decide, by decide⟩⟩

theorem g1b_mem : g1b ∈ g5G1 := ⟨by decide, Or.inl ⟨by decide, by decide⟩⟩

theorem g2a_mem : g2a ∈ cA6 := ⟨by decide, by decide⟩

theorem g2b_mem : g2b ∈ cA6 := ⟨by decide, by decide⟩

theorem Mrep_one_apply (g : Perm (Fin 6)) (x : Fin 4 → ZMod 2) : Mrep 1 g x = heartHom g *ᵥ x :=
  rfl

theorem Mrep_two_apply (g : Perm (Fin 6)) (x : Fin 4 → ZMod 2) :
    Mrep 2 g x = heartHom (totalPermHom g) *ᵥ x := rfl

@[expose] noncomputable def St : Representation (ZMod 2) (Perm (Fin 6)) (Fin 16 → ZMod 2) :=
  Mrep 3

theorem St_apply (g : Perm (Fin 6)) (x : Fin 16 → ZMod 2) : St g x = kronHom g *ᵥ x := rfl

theorem exists_pullback {W V : Type*} [AddCommMonoid W] [Module (ZMod 2) W] [AddCommMonoid V]
    [Module (ZMod 2) V] {ρ : Representation (ZMod 2) (Perm (Fin 6)) W}
    {τ : Representation (ZMod 2) (Perm (Fin 6)) V} (e : Representation.Equiv ρ τ)
    (L : Submodule (ZMod 2) V) (hL : Nat.card L = 4) (S : Set (Perm (Fin 6)))
    (hLS : ∀ g ∈ S, ∀ v ∈ L, τ g v ∈ L) :
    ∃ L' : Submodule (ZMod 2) W, Nat.card L' = 4 ∧ ∀ g ∈ S, ∀ x ∈ L', ρ g x ∈ L' := by
  refine ⟨L.comap e.toLinearEquiv.toLinearMap, ?_, fun g hg x hx => ?_⟩
  · rw [← hL]
    exact Nat.card_congr (e.toLinearEquiv.toEquiv.subtypeEquiv fun x => Iff.rfl)
  · have h1 : e.toLinearEquiv (ρ g x) = τ g (e.toLinearEquiv x) :=
      Representation.IntertwiningMap.isIntertwining _ _ e.toIntertwiningMap g x
    show e.toLinearEquiv (ρ g x) ∈ L
    rw [h1]
    exact hLS g hg _ hx

section Classify

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
  [FiniteDimensional (ZMod 2) V] (τ : Representation (ZMod 2) (Perm (Fin 6)) V)

omit [FiniteDimensional (ZMod 2) V] in
theorem false_of_equiv_Mrep_zero (e : Representation.Equiv (Mrep 0) τ) (L : Submodule (ZMod 2) V)
    (hL : Nat.card L = 4) : False := by
  have hV : Nat.card V = 2 := by
    rw [← Nat.card_congr e.toLinearEquiv.toEquiv]
    simp
  have : Finite V := Finite.of_equiv _ e.toLinearEquiv.toEquiv
  have : Nat.card L ≤ Nat.card V := Nat.card_le_card_of_injective _ Subtype.val_injective
  omega

omit [FiniteDimensional (ZMod 2) V] in
theorem false_of_equiv_Mrep_one (e : Representation.Equiv (Mrep 1) τ) (L : Submodule (ZMod 2) V)
    (hL : Nat.card L = 4) (hLg : ∀ g ∈ g5G1, ∀ v ∈ L, τ g v ∈ L) : False := by
  have hLS : ∀ g ∈ ({g1a, g1b} : Set (Perm (Fin 6))), ∀ v ∈ L, τ g v ∈ L := by
    intro g hg v hv
    rcases hg with rfl | rfl
    · exact hLg _ g1a_mem v hv
    · exact hLg _ g1b_mem v hv
  obtain ⟨L', hL', hS⟩ := exists_pullback e L hL _ hLS
  refine no_stable_line noLine_heart L' hL' (fun x hx => ?_) (fun x hx => ?_)
  · have := hS g1a (by simp) x hx
    rwa [Mrep_one_apply] at this
  · have := hS g1b (by simp) x hx
    rwa [Mrep_one_apply] at this

omit [FiniteDimensional (ZMod 2) V] in
theorem false_of_equiv_Mrep_two (e : Representation.Equiv (Mrep 2) τ) (L : Submodule (ZMod 2) V)
    (hL : Nat.card L = 4) (hLg : ∀ g ∈ cA6, ∀ v ∈ L, τ g v ∈ L) : False := by
  have hLS : ∀ g ∈ ({g2a, g2b} : Set (Perm (Fin 6))), ∀ v ∈ L, τ g v ∈ L := by
    intro g hg v hv
    rcases hg with rfl | rfl
    · exact hLg _ g2a_mem v hv
    · exact hLg _ g2b_mem v hv
  obtain ⟨L', hL', hS⟩ := exists_pullback e L hL _ hLS
  refine no_stable_line noLine_heartTotal L' hL' (fun x hx => ?_) (fun x hx => ?_)
  · have := hS g2a (by simp) x hx
    rwa [Mrep_two_apply] at this
  · have := hS g2b (by simp) x hx
    rwa [Mrep_two_apply] at this

theorem equiv_Mrep_three (hτ : Representation.IsIrreducible τ) (L₁ L₂ : Submodule (ZMod 2) V)
    (h₁ : Nat.card L₁ = 4) (h₂ : Nat.card L₂ = 4)
    (hL₁ : ∀ g ∈ g5G1, ∀ v ∈ L₁, τ g v ∈ L₁) (hL₂ : ∀ g ∈ cA6, ∀ v ∈ L₂, τ g v ∈ L₂) :
    Nonempty (Representation.Equiv St τ) := by
  obtain ⟨i, ⟨e⟩⟩ := exists_equiv_Mrep τ hτ
  fin_cases i
  · exact (false_of_equiv_Mrep_zero τ e L₁ h₁).elim
  · exact (false_of_equiv_Mrep_one τ e L₁ h₁ hL₁).elim
  · exact (false_of_equiv_Mrep_two τ e L₂ h₂ hL₂).elim
  · exact ⟨e⟩

end Classify

theorem kronHom_mul_inv (g : Perm (Fin 6)) : kronHom g * kronHom g⁻¹ = 1 := by
  rw [← map_mul, mul_inv_cancel, map_one]

theorem kronHom_inv_mul (g : Perm (Fin 6)) : kronHom g⁻¹ * kronHom g = 1 := by
  rw [← map_mul, inv_mul_cancel, map_one]

theorem rank_conj (g σ : Perm (Fin 6)) :
    (kronHom (g * σ * g⁻¹) - 1).rank = (kronHom σ - 1).rank := by
  have hm : kronHom (g * σ * g⁻¹) = kronHom g * kronHom σ * kronHom g⁻¹ := by
    simp only [map_mul]
  have h1 : kronHom (g * σ * g⁻¹) - 1 = kronHom g * (kronHom σ - 1) * kronHom g⁻¹ := by
    rw [hm, mul_sub, sub_mul, Matrix.mul_one, kronHom_mul_inv]
  have h2 : kronHom g⁻¹ * (kronHom (g * σ * g⁻¹) - 1) * kronHom g = kronHom σ - 1 := by
    rw [hm]
    calc kronHom g⁻¹ * (kronHom g * kronHom σ * kronHom g⁻¹ - 1) * kronHom g
        = (kronHom g⁻¹ * kronHom g) * kronHom σ * (kronHom g⁻¹ * kronHom g) -
            kronHom g⁻¹ * kronHom g := by noncomm_ring
      _ = kronHom σ - 1 := by rw [kronHom_inv_mul]; simp
  apply le_antisymm
  · rw [h1]
    exact (Matrix.rank_mul_le_left _ _).trans (Matrix.rank_mul_le_right _ _)
  · calc (kronHom σ - 1).rank
        = (kronHom g⁻¹ * (kronHom (g * σ * g⁻¹) - 1) * kronHom g).rank := by rw [h2]
      _ ≤ (kronHom (g * σ * g⁻¹) - 1).rank :=
        (Matrix.rank_mul_le_left _ _).trans (Matrix.rank_mul_le_right _ _)

theorem rank_of_isSwap {σ : Perm (Fin 6)} (hσ : σ.IsSwap) : (kronHom σ - 1).rank = 8 := by
  have hc : IsConj (swap (0 : Fin 6) 1) σ := by
    obtain ⟨a, b, hab, rfl⟩ := hσ
    exact Equiv.Perm.isConj_swap (by decide) hab
  obtain ⟨c, hc⟩ := isConj_iff.mp hc
  rw [← hc, rank_conj, rank_swap]

theorem cycleType_cyc3 : cyc3.cycleType = {3} := by
  have h := Equiv.Perm.isThreeCycle_swap_mul_swap_same (α := Fin 6) (a := 1) (b := 0) (c := 2)
    (by decide) (by decide) (by decide)
  rw [Equiv.swap_comm] at h
  exact h

theorem cycleType_cyc33 : cyc33.cycleType = {3, 3} := by
  have h : (swap (3 : Fin 6) 4 * swap 4 5).cycleType = {3} := by
    have h := Equiv.Perm.isThreeCycle_swap_mul_swap_same (α := Fin 6) (a := 4) (b := 3) (c := 5)
      (by decide) (by decide) (by decide)
    rw [Equiv.swap_comm] at h
    exact h
  have hd : Equiv.Perm.Disjoint cyc3 (swap 3 4 * swap 4 5) := by
    intro x
    fin_cases x <;> simp [cyc3, Equiv.swap_apply_def]
  rw [cyc33, hd.cycleType_mul, cycleType_cyc3, h]
  rfl

theorem order3_classes (σ : Perm (Fin 6)) (h3 : σ ^ 3 = 1) (h1 : σ ≠ 1) :
    σ.cycleType = {3} ∨ σ.cycleType = {3, 3} := by
  have hord : orderOf σ ∣ 3 := orderOf_dvd_of_pow_eq_one h3
  have hall : ∀ n ∈ σ.cycleType, n = 3 := by
    intro n hn
    have h2 : n ∣ 3 := (Equiv.Perm.dvd_of_mem_cycleType hn).trans hord
    have h3' : 2 ≤ n := Equiv.Perm.two_le_of_mem_cycleType hn
    have : n ≤ 3 := Nat.le_of_dvd (by norm_num) h2
    interval_cases n
    · omega
    · rfl
  have hsum : σ.cycleType.sum ≤ 6 := by
    rw [Equiv.Perm.sum_cycleType]
    exact (Finset.card_le_univ _).trans (by simp)
  have hne : σ.cycleType ≠ 0 := by
    intro h
    exact h1 (Equiv.Perm.cycleType_eq_zero.mp h)
  have hrep : σ.cycleType = Multiset.replicate (Multiset.card σ.cycleType) 3 :=
    Multiset.eq_replicate_card.mpr hall
  have hcard : Multiset.card σ.cycleType ≤ 2 := by
    rw [hrep, Multiset.sum_replicate] at hsum
    simp at hsum
    omega
  have hpos : 0 < Multiset.card σ.cycleType := Multiset.card_pos.mpr hne
  have : Multiset.card σ.cycleType = 1 ∨ Multiset.card σ.cycleType = 2 := by omega
  rcases this with h | h
  · left
    rw [hrep, h]
    rfl
  · right
    rw [hrep, h]
    rfl

theorem rank_of_order3 {σ : Perm (Fin 6)} (h3 : σ ^ 3 = 1) (h1 : σ ≠ 1) :
    (kronHom σ - 1).rank = 12 := by
  rcases order3_classes σ h3 h1 with h | h
  · have hc : IsConj cyc3 σ :=
      Equiv.Perm.isConj_iff_cycleType_eq.mpr (by rw [h, cycleType_cyc3])
    obtain ⟨c, hc⟩ := isConj_iff.mp hc
    rw [← hc, rank_conj, rank_cyc3]
  · have hc : IsConj cyc33 σ :=
      Equiv.Perm.isConj_iff_cycleType_eq.mpr (by rw [h, cycleType_cyc33])
    obtain ⟨c, hc⟩ := isConj_iff.mp hc
    rw [← hc, rank_conj, rank_cyc33]

section Invariants

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
  {τ : Representation (ZMod 2) (Perm (Fin 6)) V} (e : Representation.Equiv St τ)

include e

theorem natCard_eq_two_pow_sixteen : Nat.card V = 2 ^ 16 := by
  rw [← Nat.card_congr e.toLinearEquiv.toEquiv]
  simp

theorem natCard_range_sub_one (σ : Perm (Fin 6)) :
    Nat.card (LinearMap.range (τ σ - 1)) = 2 ^ (kronHom σ - 1).rank := by
  have key : ∀ y : Fin 16 → ZMod 2, (τ σ - 1) (e.toLinearEquiv y) =
      e.toLinearEquiv (Matrix.mulVecLin (kronHom σ - 1) y) := by
    intro y
    have h2 : e.toLinearEquiv (kronHom σ *ᵥ y) = τ σ (e.toLinearEquiv y) :=
      Representation.IntertwiningMap.isIntertwining _ _ e.toIntertwiningMap σ y
    have hA : Matrix.mulVecLin (kronHom σ - 1) y = kronHom σ *ᵥ y - y := by
      rw [Matrix.mulVecLin_apply, Matrix.sub_mulVec, Matrix.one_mulVec]
    rw [hA, map_sub, h2, LinearMap.sub_apply, Module.End.one_apply]
  have h1 : LinearMap.range (τ σ - 1) =
      (LinearMap.range (Matrix.mulVecLin (kronHom σ - 1))).map e.toLinearEquiv.toLinearMap := by
    ext w
    simp only [LinearMap.mem_range, Submodule.mem_map]
    constructor
    · rintro ⟨x, rfl⟩
      obtain ⟨y, rfl⟩ := e.toLinearEquiv.surjective x
      exact ⟨_, ⟨y, rfl⟩, (key y).symm⟩
    · rintro ⟨_, ⟨y, rfl⟩, rfl⟩
      exact ⟨e.toLinearEquiv y, key y⟩
  have hrank : Module.finrank (ZMod 2) (LinearMap.range (τ σ - 1)) = (kronHom σ - 1).rank := by
    rw [Matrix.rank, h1]
    exact (e.toLinearEquiv.submoduleMap _).finrank_eq.symm
  have : Finite V := Finite.of_equiv _ e.toLinearEquiv.toEquiv
  have : Module.Finite (ZMod 2) (LinearMap.range (τ σ - 1)) := Module.Finite.of_finite
  rw [Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod, hrank]

theorem natCard_range_of_isSwap {σ : Perm (Fin 6)} (hσ : σ.IsSwap) :
    Nat.card (LinearMap.range (τ σ - 1)) = 2 ^ 8 := by
  rw [natCard_range_sub_one e, rank_of_isSwap hσ]

theorem natCard_range_of_order3 {σ : Perm (Fin 6)} (h3 : σ ^ 3 = 1) (h1 : σ ≠ 1) :
    Nat.card (LinearMap.range (τ σ - 1)) = 2 ^ 12 := by
  rw [natCard_range_sub_one e, rank_of_order3 h3 h1]

end Invariants

end CFSG.Quasithin.H13.A6.G52
