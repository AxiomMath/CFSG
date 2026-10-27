module

public import CFSG.Quasithin.Vol2.Ch10SecEFix
public import CFSG.Quasithin.Background.E2Three
public import CFSG.Quasithin.Background.B4L3FactA
public import CFSG.Quasithin.Background.A4Defs

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecE

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.QuasithinUnique.A5.Delta5 Equiv

theorem two_eq_zero_of_card {F : Type*} [Field F] [Finite F] {n : ℕ} (hn : 1 ≤ n)
    (h : Nat.card F = 2 ^ n) : (2 : F) = 0 := by
  have := Fintype.ofFinite F
  have h1 : ((Fintype.card F : ℕ) : F) = 0 := FiniteField.cast_card_eq_zero F
  rw [← Nat.card_eq_fintype_card, h, Nat.cast_pow, Nat.cast_ofNat] at h1
  exact (pow_eq_zero_iff (by omega)).mp h1

theorem odd_orderOf_of_pow_three {X : Type*} [Group X] {x : X} (h3 : x ^ 3 = 1) (h1 : x ≠ 1) :
    Odd (orderOf x) := by
  rw [orderOf_eq_prime h3 h1]
  decide

theorem cThree_ne_one : cThree ≠ 1 := by decide +kernel

theorem cThree'_ne_one : cThree' ≠ 1 := by decide +kernel

variable {W : Type*} [CommGroup W]

theorem exists_fix_of_isA5Module {K : Subgroup (MulAut W)} (h : E2.IsA5Module K) :
    ∃ k ∈ oTwoUpper K, k * k ≠ 1 ∧ ∃ w ∈ commV (oTwoUpper K), k w = w ∧
      ∃ d ∈ oTwoUpper K, d w ≠ w := by
  obtain ⟨θ, β, hβ⟩ := h
  set k : ↥K := θ.symm cThree
  set d : ↥K := θ.symm cThree'
  have hodd : ∀ (x : ↥K) (σ : Perm (Fin 5)), θ x = σ → σ ^ 3 = 1 → σ ≠ 1 →
      (x : MulAut W) ∈ oTwoUpper K := by
    intro x σ hx h3 h1
    refine mem_oTwoUpper_of_odd x.2 ?_
    rw [Subgroup.orderOf_coe, ← MulEquiv.orderOf_eq θ, hx]
    exact odd_orderOf_of_pow_three h3 h1
  have hk : (k : MulAut W) ∈ oTwoUpper K :=
    hodd k cThree (θ.apply_symm_apply _) cThree_pow_three cThree_ne_one
  have hd : (d : MulAut W) ∈ oTwoUpper K :=
    hodd d cThree' (θ.apply_symm_apply _) cThree'_pow_three cThree'_ne_one
  have hinv := commV_invariant K
  have hco : ∀ (x : ↥K) (u : ↥(commV K)), ((Multiplicative.toAdd
      (β ⟨(x : MulAut W) u, hinv _ x.2 _ u.2⟩) : evenWeight 5) : Fin 5 → ZMod 2) =
      pact (θ x) ((Multiplicative.toAdd (β u) : evenWeight 5) : Fin 5 → ZMod 2) := fun x u =>
    funext fun i => hβ x u _ i
  set z : ↥(commV K) := β.symm (Multiplicative.ofAdd ⟨zThree, isEven_zThree⟩)
  set w : W := (d : MulAut W) (z : W) * (z : W)⁻¹
  have hwK : w ∈ commV K := (commV K).mul_mem (hinv _ d.2 _ z.2) ((commV K).inv_mem z.2)
  have hβw : ((Multiplicative.toAdd (β ⟨w, hwK⟩) : evenWeight 5) : Fin 5 → ZMod 2) = vThree := by
    have e1 : (⟨w, hwK⟩ : ↥(commV K)) = ⟨(d : MulAut W) z, hinv _ d.2 _ z.2⟩ * z⁻¹ := rfl
    rw [e1, map_mul, map_inv, toAdd_mul, toAdd_inv, AddSubgroup.coe_add, AddSubgroup.coe_neg,
      hco d z]
    have hz : ((Multiplicative.toAdd (β z) : evenWeight 5) : Fin 5 → ZMod 2) = zThree := by
      simp [z]
    rw [hz, show θ d = cThree' from θ.apply_symm_apply _, ← pact_cThree'_zThree]
    congr 1
    funext i
    exact ZMod.neg_eq_self_mod_two _
  refine ⟨k, hk, ?_, w, Subgroup.subset_closure ⟨d, hd, z, rfl⟩, ?_, d, hd, ?_⟩
  · intro hkk
    apply cThree_mul_self_ne_one
    have : θ (k * k) = 1 := by
      rw [show k * k = 1 from Subtype.ext hkk, map_one]
    rwa [map_mul, show θ k = cThree from θ.apply_symm_apply _] at this
  · have e2 := hco k ⟨w, hwK⟩
    rw [hβw, show θ k = cThree from θ.apply_symm_apply _, pact_cThree_vThree, ← hβw] at e2
    have := β.injective (Multiplicative.toAdd.injective (Subtype.ext e2))
    exact congrArg Subtype.val this
  · intro hdw
    have e2 := hco d ⟨w, hwK⟩
    rw [hβw, show θ d = cThree' from θ.apply_symm_apply _] at e2
    apply pact_cThree'_vThree
    rw [← e2, ← hβw]
    congr 4

theorem oTwoUpper_top_perm_five :
    oTwoUpper (⊤ : Subgroup (Perm (Fin 5))) = alternatingGroup (Fin 5) := by
  apply le_antisymm
  · refine (Subgroup.closure_le _).mpr ?_
    rintro σ ⟨-, ho⟩
    rw [SetLike.mem_coe, Equiv.Perm.mem_alternatingGroup]
    rcases Int.units_eq_one_or (Perm.sign σ) with h | h
    · exact h
    · exfalso
      have h1 : Perm.sign (σ ^ orderOf σ) = 1 := by rw [pow_orderOf_eq_one, map_one]
      rw [map_pow, h, ho.neg_one_pow] at h1
      exact absurd h1 (by decide)
  · rw [← Equiv.Perm.closure_three_cycles_eq_alternating]
    refine (Subgroup.closure_le _).mpr fun σ hσ => mem_oTwoUpper_of_odd (Subgroup.mem_top σ) ?_
    rw [Equiv.Perm.IsThreeCycle.orderOf hσ]
    decide

theorem isSimpleGroup_oTwoUpper_of_isA5Module {K : Subgroup (MulAut W)} (h : E2.IsA5Module K) :
    IsSimpleGroup ↥(oTwoUpper K) := by
  obtain ⟨θ, -⟩ := h
  have : Finite ↥K := Finite.of_equiv _ θ.symm.toEquiv
  have h1 : (oTwoUpper K).subgroupOf K = oTwoUpper (⊤ : Subgroup ↥K) := by
    apply Subgroup.map_injective K.subtype_injective
    rw [← oTwoUpper_map, Subgroup.map_subgroupOf_eq_of_le (oTwoUpper_le K),
      ← MonoidHom.range_eq_map, Subgroup.range_subtype]
  have h2 : (oTwoUpper (⊤ : Subgroup ↥K)).map θ.toMonoidHom = alternatingGroup (Fin 5) := by
    rw [← oTwoUpper_map, Subgroup.map_top_of_surjective _ θ.surjective, oTwoUpper_top_perm_five]
  let e : ↥(oTwoUpper K) ≃* ↥(alternatingGroup (Fin 5)) :=
    ((Subgroup.subgroupOfEquivOfLe (oTwoUpper_le K)).symm.trans (MulEquiv.subgroupCongr h1)).trans
      ((Subgroup.equivMapOfInjective _ θ.toMonoidHom θ.injective).trans
        (MulEquiv.subgroupCongr h2))
  exact e.isSimpleGroup

theorem mul_self_eq_one_of_isL2Natural {K : Subgroup (MulAut W)} {C : Subgroup W} {m : ℕ}
    (h : E2.IsL2Natural K C m) {k : MulAut W} (hk : k ∈ K) {w : W} (hw : w ∈ commV K)
    (hwC : w ∉ C) (hkw : k w = w) : k * k = 1 := by
  obtain ⟨hm, F, hF, hFt, hcard, e, β, -, hker, hβ⟩ := h
  have h2 : (2 : F) = 0 := two_eq_zero_of_card hm (by rw [Nat.card_eq_fintype_card, hcard])
  have hβw : Multiplicative.toAdd (β ⟨w, hw⟩) ≠ 0 := by
    intro h0
    have h1 : β ⟨w, hw⟩ = 1 := Multiplicative.toAdd.injective h0
    have hmem : (⟨w, hw⟩ : ↥(commV K)) ∈ β.ker := h1
    rw [hker, Subgroup.mem_subgroupOf] at hmem
    exact hwC hmem.2
  have hfix := hβ ⟨k, hk⟩ ⟨w, hw⟩ (by rw [show (k : MulAut W) w = w from hkw]; exact hw)
  have e1 : (⟨((⟨k, hk⟩ : ↥K) : MulAut W) (w : W), by
      rw [show (k : MulAut W) w = w from hkw]; exact hw⟩ : ↥(commV K)) = ⟨w, hw⟩ :=
    Subtype.ext hkw
  rw [e1] at hfix
  have hsq := mul_self_eq_one_of_mulVec_eq h2 (e ⟨k, hk⟩).2 hβw hfix.symm
  have h3 : e (⟨k, hk⟩ * ⟨k, hk⟩) = 1 := by
    rw [map_mul]
    exact Subtype.ext hsq
  have h4 : (⟨k, hk⟩ * ⟨k, hk⟩ : ↥K) = 1 := e.injective (by rw [h3, map_one])
  exact congrArg Subtype.val h4

end CFSG.Quasithin.Vol2.Ch10.SecE
