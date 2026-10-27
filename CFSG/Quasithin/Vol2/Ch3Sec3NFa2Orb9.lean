module

public import Mathlib.GroupTheory.PGroup
public import Mathlib.GroupTheory.GroupAction.CardCommute

public section

namespace CFSG.Quasithin.H13.NFa2

theorem card_dvd_of_free_orbits {A X : Type*} [Group A] [Finite A] [MulAction A X] [Finite X]
    (S : Set X) (hS : ∀ a : A, ∀ x ∈ S, a • x ∈ S)
    (hfree : ∀ x ∈ S, ∀ a : A, a • x = x → a = 1) : Nat.card A ∣ S.ncard := by
  classical
  let act : MulAction A S :=
    { smul := fun a x => ⟨a • x.1, hS a x.1 x.2⟩
      one_smul := fun x => Subtype.ext (one_smul A x.1)
      mul_smul := fun a b x => Subtype.ext (mul_smul a b x.1) }
  letI := act
  letI : Fintype A := Fintype.ofFinite A
  letI : Fintype S := Fintype.ofFinite S
  letI : Fintype (Quotient (MulAction.orbitRel A S)) := Fintype.ofFinite _
  letI : ∀ b : S, Fintype (MulAction.stabilizer A b) := fun b => Fintype.ofFinite _
  have hstab : ∀ x : S, MulAction.stabilizer A x = ⊥ := by
    intro x
    rw [eq_bot_iff]
    intro a ha
    rw [MulAction.mem_stabilizer_iff] at ha
    exact Subgroup.mem_bot.2 (hfree x.1 x.2 a (congrArg Subtype.val ha))
  have key := MulAction.card_eq_sum_card_group_div_card_stabilizer A S
  have hone : ∀ ω : Quotient (MulAction.orbitRel A S),
      Nat.card (MulAction.stabilizer A ω.out) = 1 := fun ω => by
    rw [hstab ω.out, Subgroup.card_bot]
  simp only [← Nat.card_eq_fintype_card, hone, Nat.div_one, Finset.sum_const,
    Finset.card_univ, smul_eq_mul] at key
  rw [← Nat.card_coe_set_eq, key]
  exact dvd_mul_left _ _

theorem nine_dvd_of_commute_pow {G : Type*} [Group G] {g x : G} (hg : orderOf g = 9)
    (hx : g ^ 3 * x ≠ x * g ^ 3) {n : ℕ} (hn : g ^ n * x = x * g ^ n) : 9 ∣ n := by
  by_contra hdvd
  apply hx
  have hgn : g ^ n = g ^ (n % 9) := by
    rw [← pow_mod_orderOf, hg]
  have hr0 : n % 9 ≠ 0 := fun h => hdvd (Nat.dvd_of_mod_eq_zero h)
  have hc : Commute (g ^ (n % 9)) x := by
    rw [← hgn]
    exact hn
  have hj : ∀ k : Fin 9, k.val ≠ 0 → ∃ j : Fin 9, (k.val * j.val) % 9 = 3 := by decide
  obtain ⟨j, hj⟩ := hj ⟨n % 9, Nat.mod_lt _ (by norm_num)⟩ hr0
  have hj' : (n % 9 * (j : ℕ)) % 9 = 3 := hj
  have e : g ^ 3 = (g ^ (n % 9)) ^ (j : ℕ) := by
    rw [← pow_mul, pow_eq_pow_iff_modEq, hg]
    exact hj'.symm
  rw [e]
  exact (hc.pow_left _).eq

theorem cube_central_of_elemAbelian_card_le_64 {G : Type*} [Group G] [Finite G] (g : G)
    (W : Subgroup G) (hg : orderOf g = 9) (hW2 : ∀ x ∈ W, x ^ 2 = 1)
    (hWc : ∀ x ∈ W, ∀ y ∈ W, x * y = y * x) (hcard : Nat.card ↥W ≤ 64)
    (hn : g ∈ Subgroup.normalizer (W : Set G))
    (x₀ : G) (hx₀ : x₀ ∈ W) (hx₀1 : x₀ ≠ 1) (hfix : g ^ 3 * x₀ * (g ^ 3)⁻¹ = x₀) :
    ∀ y ∈ W, g ^ 3 * y * (g ^ 3)⁻¹ = y := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Finite (ConjAct G) := inferInstanceAs (Finite G)
  set F : Subgroup G := W ⊓ Subgroup.centralizer ({g ^ 3} : Set G) with hFdef
  have hFW : F ≤ W := inf_le_left
  have hmemF : ∀ z, z ∈ F ↔ z ∈ W ∧ g ^ 3 * z = z * g ^ 3 := by
    intro z
    simp only [hFdef, Subgroup.mem_inf, Subgroup.mem_centralizer_iff, Set.mem_singleton_iff,
      forall_eq]
  have hx₀F : x₀ ∈ F := (hmemF x₀).2 ⟨hx₀, mul_inv_eq_iff_eq_mul.1 hfix⟩
  have hpg : ∀ H : Subgroup G, H ≤ W → IsPGroup 2 ↥H := fun H hH x =>
    ⟨1, Subtype.ext (by simpa using hW2 x.1 (hH x.2))⟩
  obtain ⟨m, hm⟩ := (IsPGroup.iff_card (p := 2)).1 (hpg W le_rfl)
  obtain ⟨d, hd⟩ := (IsPGroup.iff_card (p := 2)).1 (hpg F hFW)
  have hd1 : 1 ≤ d := by
    rcases Nat.eq_zero_or_pos d with h0 | h0
    · exfalso
      rw [h0, pow_zero] at hd
      obtain ⟨hs, -⟩ := Nat.card_eq_one_iff_unique.1 hd
      have h1 : (⟨x₀, hx₀F⟩ : ↥F) = 1 := hs.elim _ _
      exact hx₀1 (by simpa using congrArg Subtype.val h1)
    · exact h0
  have hm6 : m ≤ 6 := by
    have h64 : 2 ^ m ≤ 2 ^ 6 := by
      rw [← hm]
      norm_num
      exact hcard
    exact (Nat.pow_le_pow_iff_right (by norm_num)).1 h64
  intro y hy
  by_contra hyP
  set S : Set G := (W : Set G) \ (F : Set G) with hSdef
  have hyS : y ∈ S := by
    refine ⟨hy, fun hyF => hyP ?_⟩
    exact mul_inv_eq_iff_eq_mul.2 ((hmemF y).1 hyF).2
  set A : Subgroup (ConjAct G) := Subgroup.zpowers (ConjAct.toConjAct g) with hAdef
  have h9 : orderOf (ConjAct.toConjAct g) = 9 := by
    rw [← hg]
    exact orderOf_injective (ConjAct.toConjAct : G ≃* ConjAct G).toMonoidHom
      ConjAct.toConjAct.injective g
  have hAcard : Nat.card ↥A = 9 := by
    rw [hAdef, Nat.card_zpowers, h9]
  have hApow : ∀ a : ↥A, ∃ n : ℕ, (a : ConjAct G) = ConjAct.toConjAct (g ^ n) := by
    intro a
    obtain ⟨n, hn⟩ := mem_powers_iff_mem_zpowers.2 a.2
    exact ⟨n, by rw [← hn, map_pow]⟩
  have hinv : ∀ n : ℕ, ∀ x ∈ S, g ^ n * x * (g ^ n)⁻¹ ∈ S := by
    intro n x hx
    obtain ⟨hxW, hxF⟩ := hx
    have hbN : g ^ n ∈ Subgroup.normalizer (W : Set G) :=
      (Subgroup.normalizer (W : Set G)).pow_mem hn n
    have hbW : g ^ n * x * (g ^ n)⁻¹ ∈ W := (Subgroup.mem_normalizer_iff.1 hbN x).1 hxW
    refine ⟨hbW, fun hbF => hxF ?_⟩
    have hbF' : g ^ n * x * (g ^ n)⁻¹ ∈ F := hbF
    have hc : Commute (g ^ 3) (g ^ n * x * (g ^ n)⁻¹) := ((hmemF _).1 hbF').2
    have hbc : Commute (g ^ 3) (g ^ n) := (Commute.refl g).pow_pow 3 n
    have h := ((hbc.inv_right).mul_right hc).mul_right hbc
    have e : (g ^ n)⁻¹ * (g ^ n * x * (g ^ n)⁻¹) * g ^ n = x := by group
    rw [e] at h
    exact (hmemF x).2 ⟨hxW, h.eq⟩
  have hS : ∀ a : ↥A, ∀ x ∈ S, a • x ∈ S := by
    intro a x hx
    obtain ⟨n, hn⟩ := hApow a
    have hsmul : a • x = g ^ n * x * (g ^ n)⁻¹ := by
      show (a : ConjAct G) • x = _
      rw [hn, ConjAct.toConjAct_smul]
    rw [hsmul]
    exact hinv n x hx
  have hfree : ∀ x ∈ S, ∀ a : ↥A, a • x = x → a = 1 := by
    intro x hx a hax
    obtain ⟨n, hn⟩ := hApow a
    have hsmul : g ^ n * x * (g ^ n)⁻¹ = x := by
      have hax' : (a : ConjAct G) • x = x := hax
      rw [hn, ConjAct.toConjAct_smul] at hax'
      exact hax'
    have hcomm : g ^ n * x = x * g ^ n := mul_inv_eq_iff_eq_mul.1 hsmul
    have hnotF : ¬ g ^ 3 * x = x * g ^ 3 := fun h => hx.2 ((hmemF x).2 ⟨hx.1, h⟩)
    have hdvd : 9 ∣ n := nine_dvd_of_commute_pow hg hnotF hcomm
    have hdvd' : orderOf g ∣ n := by rw [hg]; exact hdvd
    have hgn : g ^ n = 1 := orderOf_dvd_iff_pow_eq_one.1 hdvd'
    apply Subtype.ext
    rw [Subgroup.coe_one, hn, hgn, map_one]
  have hS9 : 9 ∣ S.ncard := by
    have := card_dvd_of_free_orbits (A := ↥A) (X := G) S hS hfree
    rwa [hAcard] at this
  have hcount : S.ncard + (F : Set G).ncard = (W : Set G).ncard :=
    Set.ncard_sdiff_add_ncard_of_subset (fun z hz => hFW hz)
  have hWn : (W : Set G).ncard = 2 ^ m := by
    rw [← Nat.card_coe_set_eq]
    exact hm
  have hFn : (F : Set G).ncard = 2 ^ d := by
    rw [← Nat.card_coe_set_eq]
    exact hd
  have hsum : S.ncard + 2 ^ d = 2 ^ m := by
    rw [← hWn, ← hFn]
    exact hcount
  have hpos : 0 < S.ncard := (Set.ncard_pos (Set.toFinite _)).2 ⟨y, hyS⟩
  have hdm : d < m := by
    by_contra h
    rw [not_lt] at h
    have := Nat.pow_le_pow_right (show 0 < 2 by norm_num) h
    omega
  obtain ⟨k, hk⟩ := hS9
  rw [hk] at hsum hpos
  interval_cases m <;> interval_cases d <;> norm_num at hsum <;> omega

end CFSG.Quasithin.H13.NFa2
