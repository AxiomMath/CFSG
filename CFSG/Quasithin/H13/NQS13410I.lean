module

public import CFSG.Quasithin.H13.NQS13410E
public import CFSG.Quasithin.H13.U3S1344A

public section

namespace CFSG.Quasithin.H13.NQS134

open Subgroup Equiv CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Quasithin.A5Model

variable {G : Type} [Group G] [Finite G]

theorem inK4_of_conj_c3p : ∀ σ : Perm (Fin 5), A5.InD σ → A5.InD (c3p * σ * c3p⁻¹) →
    A5.InK4 σ := by
  decide +kernel

theorem k4_comm_c3p : ∀ σ : Perm (Fin 5), A5.InK4 σ → σ * c3p = c3p * σ → σ = 1 := by
  decide +kernel

theorem k4_fix_card : ∀ σ : Perm (Fin 5), A5.InK4 σ → σ ≠ 1 →
    (Finset.univ.filter fun x : W5 => pact σ x = x).card = 4 := by
  decide +kernel

theorem k4_fix2_card : ∀ σ ∈ [pa, pb, pc], ∀ τ ∈ [pa, pb, pc], σ ≠ τ →
    (Finset.univ.filter fun x : W5 => pact σ x = x ∧ pact τ x = x).card = 2 := by
  decide +kernel

theorem k4_cases : ∀ σ : Perm (Fin 5), A5.InK4 σ → σ = 1 ∨ σ ∈ [pa, pb, pc] := by
  decide +kernel

theorem pa_comm_c3p : pa * c3p * pa⁻¹ * c3p⁻¹ ≠ 1 ∧ A5.InK4 (pa * c3p * pa⁻¹ * c3p⁻¹) ∧
    (pa * c3p * pa⁻¹ * c3p⁻¹) ^ 2 = 1 := by
  decide +kernel

omit [Finite G] in
theorem a5Frame_conjAct_eq_one_iff {T K W : Subgroup G} (F : A5.Frame T K W)
    (g : ↥(normalizer (W : Set G))) : conjAct W g = 1 ↔ F.ρ g = 1 := by
  rw [U3.s134_conjAct_eq_one_iff]
  exact ⟨fun h => A5.Frame.rho_eq_one_of_mem F g h, fun h => A5.Frame.mem_centralizer_of_rho F g h⟩

theorem a5Frame_relIndex_mul_card_lt {T K W : Subgroup G} (F : A5.Frame T K W) {A : Subgroup G}
    (hAN : A ≤ normalizer (W : Set G))
    (hAK : ∀ a : ↥(normalizer (W : Set G)), (a : G) ∈ A → A5.InK4 (F.ρ a))
    (hA : ¬ A ≤ centralizer (W : Set G)) :
    (A ⊓ centralizer (W : Set G)).relIndex A * Nat.card ↥(W ⊓ centralizer (A : Set G)) < 16 := by
  classical
  set X := (A.subgroupOf (normalizer (W : Set G))).map F.ρ with hX
  have h1 : (A ⊓ centralizer (W : Set G)).relIndex A = Nat.card ↥X := by
    rw [← card_autOn_eq_relIndex hAN]
    exact Nat.card_congr (U3.mapMulEquivOfKer (conjAct W) F.ρ (a5Frame_conjAct_eq_one_iff F)
      (A.subgroupOf (normalizer (W : Set G)))).toEquiv
  have hXK4 : ∀ σ ∈ X, A5.InK4 σ := by
    rintro _ ⟨a, ha, rfl⟩
    exact hAK a (mem_subgroupOf.1 ha)
  obtain ⟨a₀, ha₀A, ha₀C⟩ := IsConcreteLE.not_le_iff_exists.1 hA
  set σ₀ := F.ρ ⟨a₀, hAN ha₀A⟩ with hσ₀
  have hσ₀X : σ₀ ∈ X := ⟨⟨a₀, hAN ha₀A⟩, mem_subgroupOf.2 ha₀A, rfl⟩
  have hσ₀1 : σ₀ ≠ 1 := fun h => ha₀C (A5.Frame.mem_centralizer_of_rho F _ h)
  have hfix : ∀ w : ↥(W ⊓ centralizer (A : Set G)), ∀ τ ∈ X,
      pact τ (F.ψ ⟨w, (mem_inf.1 w.2).1⟩) = F.ψ ⟨w, (mem_inf.1 w.2).1⟩ := by
    rintro w _ ⟨a, ha, rfl⟩
    rw [← F.equiv a]
    congr 1
    apply Subtype.ext
    rw [A5.conjAct_val]
    show (a : G) * w * (a : G)⁻¹ = w
    rw [mem_centralizer_iff.mp (mem_inf.1 w.2).2 (a : G) (mem_subgroupOf.1 ha),
      mul_inv_cancel_right]
  let f : ↥(W ⊓ centralizer (A : Set G)) → W5 := fun w => F.ψ ⟨w, (mem_inf.1 w.2).1⟩
  have hf : Function.Injective f := fun a b hab => Subtype.ext
    (congrArg (fun y : ↥W => (y : G)) (F.ψ.injective hab))
  have hσ₀L := (k4_cases σ₀ (hXK4 σ₀ hσ₀X)).resolve_left hσ₀1
  by_cases htwo : ∃ τ ∈ X, τ ≠ 1 ∧ τ ≠ σ₀
  · obtain ⟨τ, hτX, hτ1, hτσ⟩ := htwo
    have hτL := (k4_cases τ (hXK4 τ hτX)).resolve_left hτ1
    have hC : Nat.card ↥(W ⊓ centralizer (A : Set G)) ≤ 2 := by
      refine (card_le_of_maps_to f hf (Finset.univ.filter fun x : W5 =>
        pact σ₀ x = x ∧ pact τ x = x) fun w => ?_).trans
          (k4_fix2_card σ₀ hσ₀L τ hτL (Ne.symm hτσ)).le
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨hfix w σ₀ hσ₀X, hfix w τ hτX⟩
    have hXc : Nat.card ↥X ≤ 4 := by
      refine (card_le_of_maps_to (fun σ : ↥X => (σ : Perm (Fin 5))) Subtype.val_injective
        {1, pa, pb, pc} fun σ => ?_).trans (Finset.card_le_four)
      rcases k4_cases σ (hXK4 σ σ.2) with h | h
      · simp [h]
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at h
        rcases h with h | h | h <;> simp [h]
    rw [h1]
    nlinarith
  · push Not at htwo
    have hC : Nat.card ↥(W ⊓ centralizer (A : Set G)) ≤ 4 := by
      refine (card_le_of_maps_to f hf (Finset.univ.filter fun x : W5 => pact σ₀ x = x)
        fun w => ?_).trans (k4_fix_card σ₀ (hXK4 σ₀ hσ₀X) hσ₀1).le
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact hfix w σ₀ hσ₀X
    have hXc : Nat.card ↥X ≤ 2 := by
      refine (card_le_of_maps_to (fun σ : ↥X => (σ : Perm (Fin 5))) Subtype.val_injective
        {1, σ₀} fun σ => ?_).trans (Finset.card_le_two)
      by_cases h : (σ : Perm (Fin 5)) = 1
      · simp [h]
      · simp [htwo σ σ.2 h]
    rw [h1]
    nlinarith

theorem a5Frame_le_centralizer_of_isMaxElemAbelian {T K W R : Subgroup G} (F : A5.Frame T K W)
    (hW : IsElemAbelian 2 W) (hWR : W ≤ R) (hRN : R ≤ normalizer (W : Set G))
    (hRK : ∀ r : ↥(normalizer (W : Set G)), (r : G) ∈ R → A5.InK4 (F.ρ r)) {A : Subgroup G}
    (hA : IsMaxElemAbelian R A) : A ≤ centralizer (W : Set G) := by
  by_contra hAC
  have hle := card_le_relIndex_mul_card hW hWR hA
  have hlt := a5Frame_relIndex_mul_card_lt F (hA.1.trans hRN) (fun a ha => hRK a (hA.1 ha)) hAC
  have h16 : Nat.card ↥W = 16 := by
    rw [Nat.card_congr F.ψ.toEquiv]
    exact A5.card_W5
  omega

end CFSG.Quasithin.H13.NQS134
