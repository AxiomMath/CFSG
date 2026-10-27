module

public import CFSG.GH74.QTGen4.U42.U0Core
public import CFSG.Quasithin.Background.F1Lemma10

public section

namespace CFSG.Quasithin.F112R.U42M

open CFSG.GH74.QTGen4.U42 CFSG.Quasithin.A5Model CFSG.Quasithin.H13.A5
open scoped commutatorElement

local instance : DecidableEq U0 := fun x y =>
  if h : (x : Mc).left = (y : Mc).left ∧ (x : Mc).right = (y : Mc).right then
    isTrue (Subtype.ext (SemidirectProduct.ext h.1 h.2))
  else
    isFalse (fun hxy => h ⟨congrArg (fun u : U0 => (u : Mc).left) hxy,
      congrArg (fun u : U0 => (u : Mc).right) hxy⟩)

theorem comm_U0 : ∀ a b : U0, ⁅a, b⁆ = 1 ∨ ⁅a, b⁆ = zc := by decide +kernel

theorem sq_U0 : ∀ a : U0, a ^ 2 = 1 ∨ a ^ 2 = zc := by decide

theorem exists_comm_eq_zc : ∃ a b : U0, ⁅a, b⁆ = zc := by decide

theorem zc_sq : zc ^ 2 = 1 := by decide

theorem zc_ne_one : zc ≠ 1 := by decide

theorem mem_zpowers_zc (x : U0) : x ∈ Subgroup.zpowers zc ↔ x = 1 ∨ x = zc := by
  have hord : orderOf zc = 2 := orderOf_eq_prime zc_sq zc_ne_one
  rw [Subgroup.mem_zpowers_iff]
  constructor
  · rintro ⟨k, rfl⟩
    have h := zpow_mod_orderOf zc k
    rw [hord] at h
    rw [← h]
    rcases Int.emod_two_eq_zero_or_one k with h2 | h2 <;> simp [h2]
  · rintro (rfl | rfl)
    · exact ⟨0, by simp⟩
    · exact ⟨1, by simp⟩

theorem isSpecialPow_U0 : CFSG.Quasithin.IsSpecialPow 2 2 2 ↥U0 := by
  have hcard : Nat.card U0 = 32 := card_U0
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hp : IsPGroup 2 U0 := IsPGroup.of_card (n := 5) (by rw [hcard]; norm_num)
  haveI : Fact (IsPGroup 2 U0) := ⟨hp⟩
  have hZ := center_U0
  have hcomm : commutator U0 = Subgroup.zpowers zc := by
    apply le_antisymm
    · rw [commutator, Subgroup.commutator_def, Subgroup.closure_le]
      rintro _ ⟨a, -, b, -, rfl⟩
      exact (mem_zpowers_zc _).2 (comm_U0 a b)
    · rw [Subgroup.zpowers_le]
      obtain ⟨a, b, h⟩ := exists_comm_eq_zc
      rw [← h]
      exact Subgroup.commutator_mem_commutator (Subgroup.mem_top a) (Subgroup.mem_top b)
  have hfrat : frattini U0 = Subgroup.zpowers zc := by
    rw [CFSG.frattini_eq_closure_commutator_union_powers (p := 2), hcomm]
    apply le_antisymm
    · rw [Subgroup.closure_le]
      rintro x (hx | ⟨y, rfl⟩)
      · exact hx
      · exact (mem_zpowers_zc _).2 (sq_U0 y)
    · exact fun x hx => Subgroup.subset_closure (Or.inl hx)
  refine ⟨⟨hp, Or.inr ⟨hcomm.trans hZ.symm, hfrat.trans hZ.symm, ?_⟩⟩, by rw [hcard]; norm_num, ?_⟩
  · intro z hz
    rw [hZ] at hz
    rcases (mem_zpowers_zc z).1 hz with rfl | rfl
    · simp
    · exact zc_sq
  · rw [hZ, Nat.card_zpowers, orderOf_eq_prime zc_sq zc_ne_one]

abbrev c5 : Equiv.Perm (Fin 5) := finRotate 5

theorem c5_mem : c5 ∈ alternatingGroup (Fin 5) := by
  rw [Equiv.Perm.mem_alternatingGroup]
  decide

theorem exists_sub_pact_c5 : ∀ w : W5, ∃ u : W5, u * pact c5 u⁻¹ = w := by decide

theorem comm_inl_inr (u : W5) (σ : Equiv.Perm (Fin 5)) :
    ⁅(SemidirectProduct.inl u : Mc), (SemidirectProduct.inr σ : Mc)⁆ =
      SemidirectProduct.inl (u * pact σ u⁻¹) := by
  ext <;> simp [commutatorElement_def]

theorem perfect_Mof : ⁅Mof (alternatingGroup (Fin 5)), Mof (alternatingGroup (Fin 5))⁆ =
    Mof (alternatingGroup (Fin 5)) := by
  set M := Mof (alternatingGroup (Fin 5))
  refine le_antisymm (Subgroup.commutator_le_self M) ?_
  have hA : (alternatingGroup (Fin 5)).map (SemidirectProduct.inr : _ →* Mc) ≤ M := by
    rintro _ ⟨σ, hσ, rfl⟩
    exact mem_Mof.2 (by simpa using hσ)
  have hinr : (alternatingGroup (Fin 5)).map (SemidirectProduct.inr : _ →* Mc) ≤ ⁅M, M⁆ := by
    rw [← commutator_alternatingGroup_eq_self (by simp), Subgroup.map_commutator]
    exact Subgroup.commutator_mono hA hA
  have hinl : ∀ w : W5, (SemidirectProduct.inl w : Mc) ∈ ⁅M, M⁆ := by
    intro w
    obtain ⟨u, hu⟩ := exists_sub_pact_c5 w
    rw [← hu, ← comm_inl_inr]
    exact Subgroup.commutator_mem_commutator (mem_Mof.2 (by simp)) (hA ⟨c5, c5_mem, rfl⟩)
  intro x hx
  rw [← SemidirectProduct.inl_left_mul_inr_right x]
  exact Subgroup.mul_mem _ (hinl _) (hinr ⟨x.right, mem_Mof.1 hx, rfl⟩)

theorem eq_one_of_pact_c5 : ∀ u : W5, pact c5 u = u → u = 1 := by decide

theorem eq_one_of_central_Mof {x : Mc} (h : ∀ y ∈ Mof (alternatingGroup (Fin 5)), x * y = y * x) :
    x = 1 := by
  have hr : x.right = 1 := by
    apply pw_faithful
    intro t
    have hc := congrArg SemidirectProduct.left
      (h (SemidirectProduct.inl (Multiplicative.ofAdd t)) (mem_Mof.2 (by simp)))
    simp only [SemidirectProduct.mul_left, SemidirectProduct.left_inl, SemidirectProduct.right_inl,
      map_one, MulAut.one_apply] at hc
    rw [mul_comm (Multiplicative.ofAdd t) x.left] at hc
    have := mul_left_cancel hc
    exact Multiplicative.ofAdd.injective this
  have hl : x.left = 1 := by
    apply eq_one_of_pact_c5
    have hc := congrArg SemidirectProduct.left
      (h (SemidirectProduct.inr c5) (mem_Mof.2 (by simpa using c5_mem)))
    simp only [SemidirectProduct.mul_left, SemidirectProduct.left_inr, SemidirectProduct.right_inr,
      map_one, hr, MulAut.one_apply, mul_one, one_mul] at hc
    exact hc.symm
  exact SemidirectProduct.ext hl hr

abbrev c3 : Equiv.Perm (Fin 5) := Equiv.swap 0 1 * Equiv.swap 1 2

theorem orderOf_c3 : orderOf (SemidirectProduct.inr c3 : Mc) = 3 := by
  rw [orderOf_injective _ SemidirectProduct.inr_injective]
  apply orderOf_eq_prime
  · decide
  · decide

abbrev w34 : W5 := Multiplicative.ofAdd (e2 3 4)

theorem w34_ne_one : w34 ≠ 1 := by decide

theorem pact_c3_w34 : pact c3 w34 = w34 := by decide

theorem comm_w34_c3 : (SemidirectProduct.inl w34 : Mc) * SemidirectProduct.inr c3 =
    SemidirectProduct.inr c3 * SemidirectProduct.inl w34 := by
  apply SemidirectProduct.ext
  · rw [SemidirectProduct.mul_left, SemidirectProduct.mul_left, SemidirectProduct.left_inl,
      SemidirectProduct.right_inl, SemidirectProduct.left_inr, SemidirectProduct.right_inr,
      map_one, mul_one, one_mul, pact_c3_w34]
  · simp

end CFSG.Quasithin.F112R.U42M
