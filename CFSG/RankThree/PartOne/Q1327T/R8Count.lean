module

public import CFSG.RankThree.PartOne.Q1327T.R8Weights
public import CFSG.RankThree.PartOne.N143X.EvenSmall
public import CFSG.RankThree.PartOne.Q1327T.R8Core

public section

namespace CFSG.RankThree.PartOne.Q1327T.R8

open Matrix Module CFSG.RankThree.PartOne.N143X

variable {K : Type} [Field K] [Finite K] {ι : Type} [Fintype ι] [DecidableEq ι]

theorem exists_weight_set [CharP K 2] {f : ℕ} (hK : Nat.card K = 2 ^ f) {p : ℕ} [Fact p.Prime]
    (hp5 : 5 ≤ p) (E : Subgroup (GL ι K)) [hE : IsElementaryAbelian p E]
    (β : MulAut E) (hβW : β ∈ E.normalizerMonoidHom.range) (hβ : orderOf β = 3)
    (hfpf : ∀ x : E, β x = x → x = 1) :
    ∃ (X : Finset (E →* rootsOfUnity p (AlgebraicClosure K))) (c : (ZMod p)ˣ),
      (c : ZMod p) = ((2 ^ f : ℕ) : ZMod p) ∧ (∀ χ ∈ X, χ ≠ 1) ∧
      (∀ e : E, (∀ χ ∈ X, χ e = 1) → e = 1) ∧ X.card ≤ Fintype.card ι ∧ 3 ∣ X.card ∧
      (∀ χ ∈ X, chPow p (c : ZMod p) χ ∈ X) := by
  classical
  have hp := (Fact.out : p.Prime)
  have hpK : (p : K) ≠ 0 := N143X.natCast_ne_zero_of_card_two_pow hK hp (by omega)
  let L := AlgebraicClosure K
  have hpL : (p : L) ≠ 0 := fun h0 =>
    hpK ((algebraMap K L).injective (by rw [map_natCast, map_zero]; exact h0))
  have hexp : ∀ e : E, (e : GL ι K) ^ p = 1 := fun e =>
    elemPow_eq_one_of_isElementaryAbelian (A := E) e e.2
  have hcomm : ∀ e e' : E, (e : GL ι K) * e' = e' * e := fun e e' =>
    congrArg Subtype.val (IsMulCommutative.is_comm.comm e e')
  obtain ⟨hfin, hcard⟩ := nat_card_wts_le L E hpL hexp hcomm
  have : Fintype (Wts L E) := Fintype.ofFinite _
  have : CharP L 2 := inferInstance
  let σ : L →+* L := iterateFrobenius L 2 f
  have hσpow : ∀ x : L, σ x = x ^ (2 ^ f) := fun x => rfl
  have hσ : ∀ x : K, σ (algebraMap K L x) = algebraMap K L x := by
    intro x
    rw [hσpow, ← map_pow]
    congr 1
    have : Fintype K := Fintype.ofFinite K
    have := FiniteField.pow_card x
    rwa [Fintype.card_eq_nat_card, hK] at this
  have hqne : ((2 ^ f : ℕ) : ZMod p) ≠ 0 := by
    intro h0
    have := (ZMod.natCast_eq_zero_iff (2 ^ f) p).1 h0
    have h2 : p ∣ 2 := hp.dvd_of_dvd_pow this
    have := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 h2
    omega
  set X : Finset (E →* rootsOfUnity p L) :=
    (Finset.univ.filter fun w : Wts L E => wtRoots hexp w ≠ 1).image (wtRoots hexp) with hX
  have hXmem : ∀ χ, χ ∈ X ↔ ∃ w : Wts L E, wtRoots hexp w = χ ∧ χ ≠ 1 := by
    intro χ
    rw [hX, Finset.mem_image]
    constructor
    · rintro ⟨w, hw, rfl⟩
      exact ⟨w, rfl, (Finset.mem_filter.1 hw).2⟩
    · rintro ⟨w, rfl, h1⟩
      exact ⟨w, Finset.mem_filter.2 ⟨Finset.mem_univ _, h1⟩, rfl⟩
  have hX1 : ∀ χ ∈ X, χ ≠ 1 := fun χ hχ => ((hXmem χ).1 hχ).choose_spec.2
  refine ⟨X, Units.mk0 _ hqne, rfl, hX1, ?_, ?_, ?_, ?_⟩
  · intro e he
    refine eq_of_forall_weight_eq L E hpL hexp hcomm (a := e) (b := 1) fun χ hχ => ?_
    rw [weight_one L E hχ]
    by_cases h1 : wtRoots hexp ⟨χ, hχ⟩ = 1
    · exact (wtRoots_eq_one_iff hexp ⟨χ, hχ⟩).1 h1 e
    · have hmem : wtRoots hexp ⟨χ, hχ⟩ ∈ X := (hXmem _).2 ⟨⟨χ, hχ⟩, rfl, h1⟩
      have := he _ hmem
      have h2 := congrArg (fun z : rootsOfUnity p L => ((z : Lˣ) : L)) this
      simpa [wtRoots_apply] using h2
  · calc X.card ≤ (Finset.univ.filter fun w : Wts L E => wtRoots hexp w ≠ 1).card :=
          Finset.card_image_le
      _ ≤ Fintype.card (Wts L E) := Finset.card_filter_le _ _
      _ ≤ Fintype.card ι := by
          rw [← Nat.card_eq_fintype_card]
          exact hcard
  ·
    have hβi : orderOf β⁻¹ = 3 := by rwa [orderOf_inv]
    have hfpf' : ∀ x : E, β⁻¹ x = x → x = 1 := fun x hx => hfpf x (by
      have := congrArg (⇑β) hx
      simpa using this.symm)
    refine three_dvd_card_of_fixedFree (fun a b => Subtype.ext (hcomm a b)) β⁻¹ hβi hfpf' X hX1 ?_
    intro χ hχ
    obtain ⟨w, rfl, h1⟩ := (hXmem χ).1 hχ
    refine (hXmem _).2 ⟨weightAction (L := L) ⟨β, hβW⟩ w, ?_, ?_⟩
    · ext e
      rfl
    · intro h0
      apply h1
      ext e
      have := DFunLike.congr_fun h0 (β e)
      simpa using this
  ·
    intro χ hχ
    obtain ⟨w, rfl, h1⟩ := (hXmem χ).1 hχ
    refine (hXmem _).2 ⟨frobWt σ hσ w, ?_, ?_⟩
    · ext e
      have h2 : (w.1 e) ^ ((2 ^ f : ℕ) : ZMod p).val = (w.1 e) ^ (2 ^ f) := by
        rw [ZMod.val_natCast, ← pow_eq_pow_mod _ (weight_pow_eq_one L E hexp w.2 e)]
      simp only [chPow_apply, Units.val_mk0]
      rw [wtRoots_apply, Subgroup.coe_pow, Units.val_pow_eq_pow_val, wtRoots_apply, frobWt_apply,
        hσpow]
      exact h2.symm
    · intro h0
      apply h1
      have hμ : ∀ z : rootsOfUnity p L, z ^ p = 1 := fun z =>
        Subtype.ext (by rw [Subgroup.coe_pow]; exact (mem_rootsOfUnity p (z : Lˣ)).1 z.2)
      have h3 := congrArg (chPow p (((Units.mk0 _ hqne)⁻¹ : (ZMod p)ˣ) : ZMod p)) h0
      rw [← chPow_mul hμ, ← Units.val_mul, inv_mul_cancel, Units.val_one, chPow_one] at h3
      rw [h3]
      ext e
      simp [chPow_apply]

theorem two_pow_three_zmod_seven : (2 : ZMod 7) ^ 3 = 1 := by decide

theorem orderOf_two_facts {p g : ℕ} [Fact p.Prime] (hp5 : 5 ≤ p) (hpg : p ∣ 2 ^ g + 1)
    (c : (ZMod p)ˣ) (hc : (c : ZMod p) = 2) :
    Even (orderOf c) ∧ orderOf c ≠ 2 ∧ orderOf c ≠ 6 := by
  have hp := (Fact.out : p.Prime)
  have hcg : (c : ZMod p) ^ g = -1 := by
    have h0 : ((2 ^ g + 1 : ℕ) : ZMod p) = 0 := (ZMod.natCast_eq_zero_iff _ _).2 hpg
    push_cast at h0
    rw [hc]
    exact eq_neg_of_add_eq_zero_left h0
  have hneg : (-1 : ZMod p) ≠ 1 := by
    intro h
    have h2' : (2 : ZMod p) = 0 := by
      rw [← one_add_one_eq_two]
      nth_rewrite 2 [← h]
      exact add_neg_cancel 1
    have h2 : ((2 : ℕ) : ZMod p) = 0 := by exact_mod_cast h2'
    have := (ZMod.natCast_eq_zero_iff 2 p).1 h2
    have := Nat.le_of_dvd (by norm_num) this
    omega
  have hcg1 : c ^ g ≠ 1 := fun h => hneg (by
    rw [← hcg, ← Units.val_pow_eq_pow_val, h, Units.val_one])
  have hc2g : c ^ (2 * g) = 1 := by
    apply Units.ext
    rw [Units.val_pow_eq_pow_val, pow_mul', hcg, Units.val_one]
    exact neg_one_sq
  have hdvd : orderOf c ∣ 2 * g := orderOf_dvd_of_pow_eq_one hc2g
  have hndvd : ¬ orderOf c ∣ g := fun h => hcg1 (orderOf_dvd_iff_pow_eq_one.1 h)
  refine ⟨?_, ?_, ?_⟩
  · by_contra hodd
    rw [Nat.not_even_iff_odd] at hodd
    exact hndvd ((Nat.Coprime.dvd_of_dvd_mul_left (Nat.coprime_two_right.2 hodd) hdvd))
  · intro h2
    have h4 : (c : ZMod p) ^ 2 = 1 := by
      rw [← Units.val_pow_eq_pow_val, ← h2, pow_orderOf_eq_one, Units.val_one]
    rw [hc] at h4
    have h3 : ((3 : ℕ) : ZMod p) = 0 := by
      push_cast
      linear_combination h4
    have := (ZMod.natCast_eq_zero_iff 3 p).1 h3
    have := Nat.le_of_dvd (by norm_num) this
    omega
  · intro h6
    have h4 : (c : ZMod p) ^ 6 = 1 := by
      rw [← Units.val_pow_eq_pow_val, ← h6, pow_orderOf_eq_one, Units.val_one]
    rw [hc] at h4
    have h63 : ((63 : ℕ) : ZMod p) = 0 := by
      push_cast
      linear_combination h4
    have hd63 : p ∣ 63 := (ZMod.natCast_eq_zero_iff 63 p).1 h63
    have hp7 : p = 7 := by
      have h' : p ∣ 7 * 9 := by simpa using hd63
      rcases hp.dvd_mul.1 h' with h7 | h9
      · exact (Nat.prime_dvd_prime_iff_eq hp (by norm_num)).1 h7
      · have : p ∣ 3 := hp.dvd_of_dvd_pow (show p ∣ 3 ^ 2 by simpa using h9)
        have := Nat.le_of_dvd (by norm_num) this
        omega
    subst hp7
    have h3 : c ^ 3 = 1 := by
      apply Units.ext
      rw [Units.val_pow_eq_pow_val, hc, Units.val_one]
      exact two_pow_three_zmod_seven
    have := orderOf_dvd_of_pow_eq_one h3
    rw [h6] at this
    omega

theorem twelve_le_of_dvd {p g m : ℕ} [Fact p.Prime] (hp5 : 5 ≤ p) (hpg : p ∣ 2 ^ g + 1)
    (c : (ZMod p)ˣ) (hc : (c : ZMod p) = 2) (hm : 0 < m) (h3 : 3 ∣ m) (ho : orderOf c ∣ m) :
    12 ≤ m := by
  obtain ⟨he, h2, h6⟩ := orderOf_two_facts hp5 hpg c hc
  have hpos : 0 < orderOf c := orderOf_pos c
  have hlcm : Nat.lcm 3 (orderOf c) ∣ m := Nat.lcm_dvd h3 ho
  have hle : Nat.lcm 3 (orderOf c) ≤ m := Nat.le_of_dvd hm hlcm
  have h12 : 12 ≤ Nat.lcm 3 (orderOf c) := by
    by_cases hbig : 12 ≤ orderOf c
    · exact hbig.trans (Nat.le_of_dvd (Nat.lcm_pos (by norm_num) hpos) (Nat.dvd_lcm_right _ _))
    · push Not at hbig
      obtain ⟨k, hk⟩ := he
      have : orderOf c = 4 ∨ orderOf c = 8 ∨ orderOf c = 10 := by omega
      rcases this with h | h | h <;> rw [h] <;> decide
  omega

end CFSG.RankThree.PartOne.Q1327T.R8
