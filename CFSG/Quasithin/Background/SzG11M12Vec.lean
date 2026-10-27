module

public import CFSG.Quasithin.Background.SzG11M12Syl
public import CFSG.Quasithin.Background.G9StmtsModels

public section

namespace CFSG.Quasithin.G11.SzG11S

namespace M12Vec

open CFSG.Blueprint M12Syl

structure PCore {V : Type} [AddCommGroup V] [Module (ZMod 2) V] (H : Subgroup (GLV V)) where
  φ : ↥H ≃* ↥NativeSporadic.M12
  β : ↥(permCore 12) →ₗ[ZMod 2] V
  ker : ∀ u : ↥(permCore 12),
    β u = 0 ↔ (u = 0 ∨ (Even 12 ∧ ∀ i, (u : Fin 12 → ZMod 2) i = 1))
  equiv : ∀ (γ : ↥H) (u u' : ↥(permCore 12)),
    (u' : Fin 12 → ZMod 2) =
      permAct ((φ γ : ↥NativeSporadic.M12) : Equiv.Perm (Fin 12)) (u : Fin 12 → ZMod 2) →
      β u' = (γ : GLV V) (β u)

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V] {H : Subgroup (GLV V)}

theorem PCore.exists (h : IsPermCoreModule H NativeSporadic.M12) : Nonempty (PCore H) := by
  obtain ⟨φ, β, -, hk, he⟩ := h
  exact ⟨⟨φ, β, hk, he⟩⟩

@[expose] def pv (i j : Fin 12) : Fin 12 → ZMod 2 := Pi.single i 1 + Pi.single j 1

theorem pv_mem (i j : Fin 12) : pv i j ∈ permCore 12 := by
  show ∑ k, pv i j k = 0
  simp only [pv, Pi.add_apply, Finset.sum_add_distrib, Finset.sum_pi_single', Finset.mem_univ,
    ite_true]
  decide

@[expose] def pvm (i j : Fin 12) : ↥(permCore 12) := ⟨pv i j, pv_mem i j⟩

theorem permAct_pv (σ : Equiv.Perm (Fin 12)) (i j : Fin 12) :
    permAct σ (pv i j) = pv (σ i) (σ j) := by
  funext k
  simp only [permAct, pv, Pi.add_apply, Pi.single_apply, Equiv.Perm.inv_eq_iff_eq]

@[expose] def PCore.pr (c : PCore H) (i j : Fin 12) : V := c.β (pvm i j)

theorem PCore.pr_comm (c : PCore H) (i j : Fin 12) : c.pr i j = c.pr j i := by
  unfold PCore.pr
  congr 1
  apply Subtype.ext
  exact add_comm _ _

@[expose] def PCore.perm (c : PCore H) (γ : ↥H) : Equiv.Perm (Fin 12) :=
  ((c.φ γ : ↥NativeSporadic.M12) : Equiv.Perm (Fin 12))

theorem PCore.act_pr (c : PCore H) (γ : ↥H) (i j : Fin 12) :
    (γ : GLV V) (c.pr i j) = c.pr (c.perm γ i) (c.perm γ j) := by
  unfold PCore.pr
  refine (c.equiv γ (pvm i j) (pvm _ _) ?_).symm
  exact (permAct_pv _ i j).symm

theorem zmod2_aux (x y w : ZMod 2) : x + y + (x + w) = y + w := by
  revert x y w
  decide

theorem zmod2_aux2 (x y z : ZMod 2) (h : x + y = z) : y = z + x := by
  revert x y z
  decide

theorem pr_add (c : PCore H) (i j : Fin 12) :
    c.pr 0 i + c.pr 0 j = c.pr i j := by
  unfold PCore.pr
  rw [← map_add]
  congr 1
  apply Subtype.ext
  funext k
  exact zmod2_aux _ _ _

theorem exists_not_mem_finset (S : Finset (Fin 12)) (h : S.card < 12) : ∃ m : Fin 12, m ∉ S := by
  by_contra hc
  have : (Finset.univ : Finset (Fin 12)) ⊆ S := fun m _ => by
    by_contra hm
    exact hc ⟨m, hm⟩
  have := Finset.card_le_card this
  simp at this
  omega

theorem pr_eq (c : PCore H) {i j k l : Fin 12} (hij : i ≠ j) (hkl : k ≠ l)
    (h : c.pr i j = c.pr k l) : (i = k ∧ j = l) ∨ (i = l ∧ j = k) := by
  have h0 : c.β (pvm i j + pvm k l) = 0 := by
    rw [map_add]
    unfold PCore.pr at h
    rw [h]
    exact ZModModule.add_self _
  rcases (c.ker _).1 h0 with h1 | ⟨-, h1⟩
  · have h2 : pv i j = pv k l := by
      have := congrArg Subtype.val h1
      funext m
      have h3 := congrFun this m
      simp only [Submodule.coe_add, pvm, Pi.add_apply, ZeroMemClass.coe_zero, Pi.zero_apply] at h3
      exact (CharTwo.add_eq_zero.1 h3)
    have hi := congrFun h2 i
    have hj := congrFun h2 j
    simp only [pv, Pi.add_apply, Pi.single_apply, ite_true, hij, hij.symm, ite_false] at hi hj
    by_cases hik : i = k <;> by_cases hil : i = l <;> by_cases hjk : j = k <;>
      by_cases hjl : j = l <;> simp_all
  · exfalso
    obtain ⟨m, hm⟩ := exists_not_mem_finset {i, j, k, l} (by
      calc ({i, j, k, l} : Finset (Fin 12)).card ≤ 4 := Finset.card_le_four
        _ < 12 := by norm_num)
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hm
    have h3 := h1 m
    simp only [Submodule.coe_add, pvm, pv, Pi.add_apply, Pi.single_apply, hm.1, hm.2.1,
      hm.2.2.1, hm.2.2.2, ite_false] at h3
    simp at h3

variable [Finite V]

theorem finrank_le_six (c : PCore H) (hV : Module.finrank (ZMod 2) V = 10)
    (U : Submodule (ZMod 2) V) (hU : ∀ i j : Fin 12, i ≠ j → c.pr i j ∉ U) :
    Module.finrank (ZMod 2) U ≤ 6 := by
  have : Finite (V ⧸ U) := Finite.of_surjective _ (Submodule.Quotient.mk_surjective U)
  let f : Fin 12 → V ⧸ U := fun i => Submodule.Quotient.mk (c.pr 0 i)
  have hf : Function.Injective f := by
    intro i j hij
    by_contra hne
    apply hU i j hne
    have h1 := (Submodule.Quotient.eq U).1 hij
    have h2 : c.pr 0 i - c.pr 0 j = c.pr i j := by
      rw [← pr_add c i j, sub_eq_add_neg, ZModModule.neg_eq_self]
    rwa [h2] at h1
  have h12 : 12 ≤ Nat.card (V ⧸ U) := by
    have := Nat.card_le_card_of_injective f hf
    simpa using this
  have hq := Submodule.finrank_quotient_add_finrank U
  have hcard : Nat.card (V ⧸ U) = 2 ^ Module.finrank (ZMod 2) (V ⧸ U) :=
    (FiniteField.pow_finrank_eq_natCard 2 (V ⧸ U)).symm
  by_contra hlt
  have h3 : Module.finrank (ZMod 2) (V ⧸ U) ≤ 3 := by omega
  have h4 : 2 ^ Module.finrank (ZMod 2) (V ⧸ U) ≤ 2 ^ 3 :=
    Nat.pow_le_pow_right (by norm_num) h3
  omega

theorem fin_cover_exists_out (a b : Fin 4 → Fin 12) :
    ∃ m : Fin 12, (∀ k, m ≠ a k) ∧ (∀ k, m ≠ b k) := by
  obtain ⟨m, hm⟩ := exists_not_mem_finset (Finset.univ.image a ∪ Finset.univ.image b) (by
    calc (Finset.univ.image a ∪ Finset.univ.image b).card
        ≤ (Finset.univ.image a).card + (Finset.univ.image b).card := Finset.card_union_le _ _
      _ ≤ 4 + 4 := Nat.add_le_add (by simpa using Finset.card_image_le (s := Finset.univ) (f := a))
          (by simpa using Finset.card_image_le (s := Finset.univ) (f := b))
      _ < 12 := by norm_num)
  simp only [Finset.mem_union, Finset.mem_image, Finset.mem_univ, true_and, not_or, not_exists]
    at hm
  exact ⟨m, fun k h => hm.1 k h.symm, fun k h => hm.2 k h.symm⟩

theorem inner_rank (c : PCore H) (γ : ↥H) (h1 : γ ≠ 1)
    (h2 : γ * γ = 1) :
    3 ≤ Module.finrank (ZMod 2)
      (LinearMap.range ((γ : GLV V).toLinearMap - LinearMap.id)) := by
  have hσ1 : c.φ γ ≠ 1 := fun h => h1 (c.φ.injective (by rw [h, map_one]))
  have hσ2 : c.φ γ * c.φ γ = 1 := by rw [← map_mul, h2, map_one]
  obtain ⟨a, b, hab, hne, hdist⟩ := invol_cycles (c.φ γ) hσ1 hσ2
  have hp : ∀ k, c.perm γ (a k) = b k := fun k => (hab k).1
  have a_inj : ∀ k l, a k = a l ↔ k = l := by
    intro k l
    refine ⟨fun h => ?_, fun h => by rw [h]⟩
    by_contra hkl
    exact (hdist k l hkl).1 h
  have hab_ne : ∀ k l, a k ≠ b l := by
    intro k l h
    by_cases hkl : k = l
    · subst hkl
      exact hne k h
    · exact (hdist k l hkl).2.1 h
  let Y : Fin 3 → ↥(permCore 12) := fun l => pvm (b 0) (b l.succ) + pvm (a 0) (a l.succ)
  let y : Fin 3 → V := fun l => c.β (Y l)
  have hy : ∀ l, y l ∈ LinearMap.range ((γ : GLV V).toLinearMap - LinearMap.id) := by
    intro l
    refine ⟨c.pr (a 0) (a l.succ), ?_⟩
    simp only [LinearMap.sub_apply, LinearMap.id_apply, LinearEquiv.coe_coe]
    rw [c.act_pr γ, hp, hp]
    show _ = c.β (pvm (b 0) (b l.succ) + pvm (a 0) (a l.succ))
    rw [map_add, sub_eq_add_neg, ZModModule.neg_eq_self]
    rfl
  have hli : LinearIndependent (ZMod 2) y := by
    rw [Fintype.linearIndependent_iff]
    intro g hg k
    have h0 : c.β (∑ l, g l • Y l) = 0 := by
      rw [map_sum]
      simpa [map_smul, y] using hg
    have hcoord : ∀ m, ((∑ l, g l • Y l : ↥(permCore 12)) : Fin 12 → ZMod 2) m =
        ∑ l, g l * (pv (b 0) (b l.succ) m + pv (a 0) (a l.succ) m) := by
      intro m
      simp [Y, pvm, Finset.sum_apply, mul_add]
    have hA : ∀ k l : Fin 3, pv (b 0) (b l.succ) (a k.succ) + pv (a 0) (a l.succ) (a k.succ) =
        if l = k then 1 else 0 := by
      intro k l
      simp only [pv, Pi.add_apply, Pi.single_apply, a_inj, hab_ne, Fin.succ_ne_zero, Fin.succ_inj,
        ite_false]
      by_cases hlk : l = k
      · subst hlk
        simp
      · simp [hlk, Ne.symm hlk]
    obtain ⟨m, hma, hmb⟩ := fin_cover_exists_out a b
    have hO : ∀ l : Fin 3, pv (b 0) (b l.succ) m + pv (a 0) (a l.succ) m = 0 := by
      intro l
      simp [pv, hma, hmb]
    rcases (c.ker _).1 h0 with h3 | ⟨-, h3⟩
    · have h4 := congrFun (congrArg Subtype.val h3) (a k.succ)
      rw [hcoord] at h4
      simp only [hA, ZeroMemClass.coe_zero, Pi.zero_apply] at h4
      simpa using h4
    · exfalso
      have h4 := h3 m
      rw [hcoord] at h4
      simp only [hO, mul_zero, Finset.sum_const_zero] at h4
      exact absurd h4 (by decide)
  calc 3 = Fintype.card (Fin 3) := by simp
    _ = Module.finrank (ZMod 2) (Submodule.span (ZMod 2) (Set.range y)) :=
        (finrank_span_eq_card hli).symm
    _ ≤ _ := Submodule.finrank_mono (Submodule.span_le.2 (Set.range_subset_iff.2 hy))

theorem permAct_mem_core (σ : Equiv.Perm (Fin 12)) {u : Fin 12 → ZMod 2}
    (hu : u ∈ permCore 12) : permAct σ u ∈ permCore 12 := by
  show ∑ j, permAct σ u j = 0
  have : ∑ j, permAct σ u j = ∑ j, u j := Equiv.sum_comp σ⁻¹ u
  rw [this]
  exact hu

@[expose] def onesM : ↥(permCore 12) := ⟨fun _ => 1, by
  show ∑ j : Fin 12, (1 : ZMod 2) = 0
  decide⟩

omit [Finite V] in
theorem beta_ones (c : PCore H) : c.β onesM = 0 :=
  (c.ker onesM).2 (Or.inr ⟨by decide, fun _ => rfl⟩)

theorem fixed_E8 (c : PCore H) (E : Subgroup (GLV V))
    (hEH : E ≤ H) (hcard : Nat.card E = 8)
    (hcomm : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x) (hsq : ∀ x ∈ E, x * x = 1) :
    3 ≤ Module.finrank (ZMod 2) (fixedSpace E) := by
  let E' : Subgroup ↥NativeSporadic.M12 := (E.subgroupOf H).map c.φ.toMonoidHom
  have hE'card : Nat.card E' = 8 := by
    have h1 : Nat.card E' = Nat.card (E.subgroupOf H) :=
      Subgroup.card_map_of_injective c.φ.injective
    rw [h1, ← hcard]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hEH).toEquiv
  have hmemE' : ∀ x ∈ E', ∃ γ : ↥H, (γ : GLV V) ∈ E ∧ c.φ γ = x := by
    rintro _ ⟨γ, hγ, rfl⟩
    exact ⟨γ, hγ, rfl⟩
  have hE'comm : ∀ x ∈ E', ∀ y ∈ E', x * y = y * x := by
    intro x hx y hy
    obtain ⟨γ, hγ, rfl⟩ := hmemE' x hx
    obtain ⟨δ, hδ, rfl⟩ := hmemE' y hy
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (hcomm _ hγ _ hδ)
  have hE'sq : ∀ x ∈ E', x * x = 1 := by
    intro x hx
    obtain ⟨γ, hγ, rfl⟩ := hmemE' x hx
    rw [← map_mul, ← map_one c.φ]
    congr 1
    exact Subtype.ext (hsq _ hγ)
  obtain ⟨u, hu1, hu2, hu3⟩ := e8_vectors E' hE'card hE'comm hE'sq
  let U : Fin 3 → ↥(permCore 12) := fun k => ⟨u k, by
    show ∑ j, u k j = 0
    exact hu1 k⟩
  let w : Fin 3 → V := fun k => c.β (U k)
  have hfix : ∀ k, ∀ x ∈ E, (x : GLV V) (w k) = w k := by
    intro k x hx
    let γ : ↥H := ⟨x, hEH hx⟩
    have hγE' : c.φ γ ∈ E' := ⟨γ, hx, rfl⟩
    obtain ⟨c', hc'⟩ := hu2 k (c.φ γ) hγE'
    have hσσ : ∀ j, (c.perm γ) ((c.perm γ) j) = j := by
      intro j
      have := hE'sq _ hγE'
      have h2 := congrArg (fun τ : ↥NativeSporadic.M12 => (τ : Equiv.Perm (Fin 12)) j) this
      simpa [PCore.perm] using h2
    have hinv : ∀ j, (c.perm γ)⁻¹ j = c.perm γ j := fun j =>
      Equiv.Perm.inv_eq_iff_eq.2 (hσσ j).symm
    have hU' : permAct (c.perm γ) (u k) = u k + c' • (fun _ => 1) := by
      funext j
      simp only [permAct, hinv, Pi.add_apply, Pi.smul_apply, smul_eq_mul, mul_one]
      have := hc' j
      rw [add_comm (u k j) c']
      exact zmod2_aux2 _ _ _ this
    have h1 := c.equiv γ (U k) ⟨permAct (c.perm γ) (u k), permAct_mem_core _ (U k).2⟩ rfl
    show (γ : GLV V) (c.β (U k)) = c.β (U k)
    rw [← h1]
    have h3 : (⟨permAct (c.perm γ) (u k), permAct_mem_core _ (U k).2⟩ : ↥(permCore 12)) =
        U k + c' • onesM := by
      apply Subtype.ext
      exact hU'
    rw [h3, map_add, map_smul, beta_ones, smul_zero, add_zero]
  have hli : LinearIndependent (ZMod 2) w := by
    rw [Fintype.linearIndependent_iff]
    intro g hg
    have h0 : c.β (∑ k, g k • U k) = 0 := by
      rw [map_sum]
      simpa [map_smul, w] using hg
    have hcoord : ∀ j, ((∑ k, g k • U k : ↥(permCore 12)) : Fin 12 → ZMod 2) j =
        ∑ k, g k * u k j := by
      intro j
      simp [U, Finset.sum_apply]
    have hconst : ∃ c' : ZMod 2, ∀ j, ∑ k, g k * u k j = c' := by
      rcases (c.ker _).1 h0 with h3 | ⟨-, h3⟩
      · refine ⟨0, fun j => ?_⟩
        rw [← hcoord j, h3]
        rfl
      · refine ⟨1, fun j => ?_⟩
        rw [← hcoord j]
        exact h3 j
    exact fun k => congrFun (hu3 g hconst) k
  calc 3 = Fintype.card (Fin 3) := by simp
    _ = Module.finrank (ZMod 2) (Submodule.span (ZMod 2) (Set.range w)) :=
        (finrank_span_eq_card hli).symm
    _ ≤ _ := by
      apply Submodule.finrank_mono
      rw [Submodule.span_le]
      rintro _ ⟨k, rfl⟩ x hx
      exact hfix k x hx

end M12Vec

end CFSG.Quasithin.G11.SzG11S
