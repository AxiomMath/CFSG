module

public import CFSG.Quasithin.H13.L32AVolI

public section

namespace CFSG.Quasithin.H6

open scoped MatrixGroups

instance : DecidablePred (· ∈ Lp) := fun g =>
  decidable_of_iff (g • (![1, 0, 0] : V3) = ![1, 0, 0]) MulAction.mem_stabilizer_iff.symm

instance : DecidablePred (· ∈ Ll) := fun g => inferInstanceAs (Decidable (IsLl g))

instance : DecidablePred (· ∈ borel) := fun g =>
  decidable_of_iff (g ∈ Lp ∧ g ∈ Ll) Subgroup.mem_inf.symm

theorem card_st : Nat.card St = 256 := by
  rw [Nat.card_eq_fintype_card]
  decide +kernel

theorem card_core : Nat.card Core = 64 := by
  rw [Nat.card_eq_fintype_card]
  decide +kernel

theorem card_v3 : Nat.card V3 = 8 := by
  rw [Nat.card_eq_fintype_card]
  decide

@[expose] def x3 : Γ := ⟨!![0, 0, 1; 1, 0, 0; 0, 1, 0], by decide⟩

theorem exists_conj_x3 : ∀ x : Γ, x ^ 3 = 1 → x ≠ 1 → ∃ g : Γ, g * x3 = x * g := by
  decide +kernel

theorem card_fix_conj {M : Type} [AddGroup M] (ρ : Γ →* AddMonoid.End M) (g x : Γ) :
    Nat.card {m : M // ρ (g * x * g⁻¹) m = m} = Nat.card {m : M // ρ x m = m} := by
  have hmul : ∀ (a b : Γ) (m : M), ρ (a * b) m = ρ a (ρ b m) := fun a b m => by
    rw [map_mul]
    rfl
  have hone : ∀ m : M, ρ 1 m = m := fun m => by
    rw [map_one]
    rfl
  refine Nat.card_congr
    { toFun := fun m => ⟨ρ g⁻¹ m, ?_⟩
      invFun := fun m => ⟨ρ g m, ?_⟩
      left_inv := fun m => Subtype.ext ?_
      right_inv := fun m => Subtype.ext ?_ }
  · have h1 := m.2
    calc ρ x (ρ g⁻¹ m) = ρ g⁻¹ (ρ (g * x * g⁻¹) m) := by
          rw [← hmul, ← hmul, show g⁻¹ * (g * x * g⁻¹) = x * g⁻¹ by group]
      _ = ρ g⁻¹ m := by rw [h1]
  · have h1 := m.2
    calc ρ (g * x * g⁻¹) (ρ g m) = ρ g (ρ x m) := by
          rw [← hmul, ← hmul, show g * x * g⁻¹ * g = g * x by group]
      _ = ρ g m := by rw [h1]
  · show ρ g (ρ g⁻¹ m) = m
    rw [← hmul, mul_inv_cancel, hone]
  · show ρ g⁻¹ (ρ g m) = m
    rw [← hmul, inv_mul_cancel, hone]

theorem card_fix_of_x3 {M : Type} [AddGroup M] (ρ : Γ →* AddMonoid.End M) {x : Γ}
    (hx3 : x ^ 3 = 1) (hx1 : x ≠ 1) :
    Nat.card {m : M // ρ x m = m} = Nat.card {m : M // ρ x3 m = m} := by
  obtain ⟨g, hg⟩ := exists_conj_x3 x hx3 hx1
  have hx : x = g * x3 * g⁻¹ := by rw [hg]; group
  rw [hx, card_fix_conj]

theorem card_fix_st (x : Γ) (hx3 : x ^ 3 = 1) (hx1 : x ≠ 1) :
    Nat.card {m : St // ρSt x m = m} = 4 := by
  rw [card_fix_of_x3 ρSt hx3 hx1, Nat.card_eq_fintype_card]
  decide +kernel

theorem card_fix_core (x : Γ) (hx3 : x ^ 3 = 1) (hx1 : x ≠ 1) :
    Nat.card {m : Core // ρCore x m = m} = 4 := by
  rw [card_fix_of_x3 ρCore hx3 hx1, Nat.card_eq_fintype_card]
  decide +kernel

theorem card_fix_v3 (x : Γ) (hx3 : x ^ 3 = 1) (hx1 : x ≠ 1) :
    Nat.card {m : V3 // ρV x m = m} = 2 := by
  rw [card_fix_of_x3 ρV hx3 hx1, Nat.card_eq_fintype_card]
  decide +kernel

section Iso

variable {M N : Type} [AddGroup M] [AddGroup N] {ρ : Γ →* AddMonoid.End M}
  {σ : Γ →* AddMonoid.End N}

theorem IsoMod.card_eq (h : IsoMod ρ σ) : Nat.card M = Nat.card N := by
  obtain ⟨f, hf, -⟩ := h
  exact (Nat.card_congr (Equiv.ofBijective f hf)).symm

theorem IsoMod.card_fix_eq (h : IsoMod ρ σ) (x : Γ) :
    Nat.card {m : M // ρ x m = m} = Nat.card {n : N // σ x n = n} := by
  obtain ⟨f, hf, hfe⟩ := h
  refine (Nat.card_congr ((Equiv.ofBijective f hf).subtypeEquiv fun n => ?_)).symm
  constructor
  · intro hn
    show ρ x (f n) = f n
    rw [← hfe, hn]
  · intro hn
    apply hf.1
    rw [hfe]
    exact hn

theorem card_fix_prodRep (x : Γ) :
    Nat.card {y : M × N // prodRep ρ σ x y = y} =
      Nat.card {m : M // ρ x m = m} * Nat.card {n : N // σ x n = n} := by
  rw [← Nat.card_prod]
  exact Nat.card_congr
    { toFun := fun y => (⟨y.1.1, congrArg Prod.fst y.2⟩, ⟨y.1.2, congrArg Prod.snd y.2⟩)
      invFun := fun p => ⟨(p.1.1, p.2.1), Prod.ext p.1.2 p.2.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }

end Iso

theorem isoMod_st_of_index (h65 : VolI_H_6_5) {M : Type} [AddGroup M] [Finite M]
    {ρ : Γ →* AddMonoid.End M} (h2 : ∀ m : M, m + m = 0)
    (hfaith : ∀ g : Γ, (∀ m : M, ρ g m = m) → g = 1) {m : M} (hmT : ∀ t ∈ borel, ρ t m = m)
    (hgen : AddSubgroup.closure (Set.range fun g : Γ => ρ g m) = ⊤)
    (hl : Nat.card ↥(AddSubgroup.closure {y | ∃ g ∈ Ll, ρ g m = y}) = 4) {x : Γ}
    (hx3 : x ^ 3 = 1) (hx1 : x ≠ 1) (hidx : Nat.card M = 64 * Nat.card {y : M // ρ x y = y}) :
    IsoMod ρ ρSt := by
  obtain ⟨-, hcases⟩ := h65 M ρ h2 hfaith m hmT hgen hl
  rcases hcases with h | h | h | h | h
  · exfalso
    have hc : Nat.card M = 64 := h.card_eq.trans card_core
    have hf : Nat.card {y : M // ρ x y = y} = 4 :=
      (h.card_fix_eq x).trans (card_fix_core x hx3 hx1)
    rw [hc, hf] at hidx
    norm_num at hidx
  · exact h
  · exfalso
    have hc : Nat.card M = 8 := h.card_eq.trans card_v3
    have hf : Nat.card {y : M // ρ x y = y} = 2 :=
      (h.card_fix_eq x).trans (card_fix_v3 x hx3 hx1)
    rw [hc, hf] at hidx
    norm_num at hidx
  · exfalso
    have hc : Nat.card M = 8 * 256 :=
      h.card_eq.trans ((Nat.card_prod _ _).trans (congrArg₂ (· * ·) card_v3 card_st))
    have hf : Nat.card {y : M // ρ x y = y} = 2 * 4 :=
      (h.card_fix_eq x).trans ((card_fix_prodRep x).trans
        (congrArg₂ (· * ·) (card_fix_v3 x hx3 hx1) (card_fix_st x hx3 hx1)))
    rw [hc, hf] at hidx
    norm_num at hidx
  · exfalso
    have hc : Nat.card M = 64 * 256 :=
      h.card_eq.trans ((Nat.card_prod _ _).trans (congrArg₂ (· * ·) card_core card_st))
    have hf : Nat.card {y : M // ρ x y = y} = 4 * 4 :=
      (h.card_fix_eq x).trans ((card_fix_prodRep x).trans
        (congrArg₂ (· * ·) (card_fix_core x hx3 hx1) (card_fix_st x hx3 hx1)))
    rw [hc, hf] at hidx
    norm_num at hidx

@[expose] def w0m : Matrix (Fin 3) (Fin 3) (ZMod 2) := !![0, 0, 1; 0, 1, 0; 1, 0, 0]

theorem det_graph : ∀ g : Γ,
    (w0m * (((g⁻¹ : Γ) : Matrix (Fin 3) (Fin 3) (ZMod 2))).transpose * w0m).det = 1 := by
  decide +kernel

@[expose] def graphFun (g : Γ) : Γ :=
  ⟨w0m * (((g⁻¹ : Γ) : Matrix (Fin 3) (Fin 3) (ZMod 2))).transpose * w0m, det_graph g⟩

theorem w0m_mul_self : w0m * w0m = 1 := by decide

theorem graphFun_mul (g h : Γ) : graphFun (g * h) = graphFun g * graphFun h := by
  apply Subtype.ext
  show w0m * (((g * h)⁻¹ : Γ) : Matrix (Fin 3) (Fin 3) (ZMod 2)).transpose * w0m =
    (w0m * (((g⁻¹ : Γ) : Matrix (Fin 3) (Fin 3) (ZMod 2))).transpose * w0m) *
      (w0m * (((h⁻¹ : Γ) : Matrix (Fin 3) (Fin 3) (ZMod 2))).transpose * w0m)
  rw [mul_inv_rev, Matrix.SpecialLinearGroup.coe_mul, Matrix.transpose_mul]
  simp only [Matrix.mul_assoc]
  rw [← Matrix.mul_assoc w0m w0m, w0m_mul_self, Matrix.one_mul]

theorem graphFun_graphFun : ∀ g : Γ, graphFun (graphFun g) = g := by
  decide +kernel

@[expose] def graph : Γ ≃* Γ where
  toFun := graphFun
  invFun := graphFun
  left_inv := graphFun_graphFun
  right_inv := graphFun_graphFun
  map_mul' := graphFun_mul

theorem graph_apply (g : Γ) : graph g = graphFun g := rfl

theorem graph_mem_borel_iff : ∀ g : Γ, graph g ∈ borel ↔ g ∈ borel := by
  decide +kernel

theorem graph_mem_Ll_iff : ∀ g : Γ, graph g ∈ Ll ↔ g ∈ Lp := by
  decide +kernel

end CFSG.Quasithin.H6
