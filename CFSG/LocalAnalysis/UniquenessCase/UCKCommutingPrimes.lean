module

public import CFSG.LocalAnalysis.UniquenessCase.UCKUnfaithful
public import CFSG.RepresentationTheory.QuaternionKernelOrbit
public import CFSG.GroupTheory.Frattini.NormalConjugation
public import CFSG.Mathlib.Arithmetic.TwoPowSubOnePrimes
public import CFSG.Mathlib.Arithmetic.TwoPowModThree

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UCK

open Subgroup
open CFSG.GroupTheory
open CFSG.RankThree.PartOne.FixedRank36
open scoped IsMulCommutative

variable {p : ℕ} [Fact p.Prime] {Γ : Type} [Group Γ] [Finite Γ]
  {V : Type} [AddCommGroup V] [Module (ZMod p) V] [Finite V]

theorem exists_quaternion_quotient_of_simpleUnder (ρ : Representation (ZMod p) Γ V) (hp : 2 < p)
    {D T : Subgroup Γ} (hD : Nat.card D = 3) (hfix : fixV ρ D = ⊥)
    (hT : IsPGroup 2 T) (hDT : D ≤ Subgroup.normalizer (T : Set Γ))
    (hDTc : ⁅D, T⁆ = T) {W : Submodule (ZMod p) V}
    (hW : CFSG.RepresentationTheory.IsSimpleUnder ρ (T ⊔ D) W)
    (hWt : ∃ t ∈ T, ∃ w ∈ W, ρ t w ≠ w) :
    ∃ φ : ↥T →* QuaternionGroup 2, Function.Surjective φ ∧
      ∀ t : ↥T, φ t = 1 ↔ ∀ w ∈ W, ρ t w = w := by
  obtain ⟨hWinv, hWs⟩ := hW
  exact k43gen_unfaithful (ρ := ρ) (hp := hp) (D := D) (T := T) (hD := hD)
    (hfix := hfix) (hT := hT) (hDT := hDT) (hDTc := hDTc) (W := W)
    (hWinv := hWinv) (hWs := hWs) (hWt := hWt)

theorem normalizer_sup_zpowers_and_fixV (ρ : Representation (ZMod p) Γ V)
    {T : Subgroup Γ} {d x : Γ} (hdT : d ∈ Subgroup.normalizer (T : Set Γ))
    (hxT : x ∈ Subgroup.normalizer (T : Set Γ)) (hdx : Commute d x)
    (hfixx : fixV ρ (Subgroup.zpowers x) = ⊥) :
    x ∈ Subgroup.normalizer ((T ⊔ Subgroup.zpowers d : Subgroup Γ) : Set Γ) ∧
      ∀ v : V, ρ x v = v → v = 0 := by
  have hxzd : x ∈ Subgroup.normalizer (Subgroup.zpowers d : Set Γ) :=
    Subgroup.centralizer_le_normalizer _ (by
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
      exact (hdx.zpow_left k).eq)
  refine ⟨?_, ?_⟩
  · exact Subgroup.normalizer_inf_normalizer_le_normalizer_sup T (Subgroup.zpowers d)
      (Subgroup.mem_inf.mpr ⟨hxT, hxzd⟩)
  · intro v hv
    have hmem := (CFSG.LocalAnalysis.UniquenessCase.UC6.mem_fixV_zpowers_uc6 ρ x v).mpr hv
    rwa [hfixx, Submodule.mem_bot] at hmem

theorem eq_one_of_commute_three_prime (ρ : Representation (ZMod p) Γ V) (hp2 : p ≠ 2) (hp3 : p ≠ 3)
    {T : Subgroup Γ} (hT : IsPGroup 2 T) {d x : Γ} (hd : orderOf d = 3) {r : ℕ} (hr : r.Prime)
    (hr5 : 5 ≤ r) (hx : orderOf x = r) (hdx : Commute d x)
    (hdT : d ∈ Subgroup.normalizer (T : Set Γ)) (hxT : x ∈ Subgroup.normalizer (T : Set Γ))
    (hTd : ⁅Subgroup.zpowers d, T⁆ = T) (hTx : ⁅Subgroup.zpowers x, T⁆ = T)
    (hfixd : fixV ρ (Subgroup.zpowers d) = ⊥) (hfixx : fixV ρ (Subgroup.zpowers x) = ⊥) :
    ∀ t ∈ T, ρ t = 1 := by
  have hp2lt : 2 < p := by
    have h2 : 2 ≤ p := (Fact.out : p.Prime).two_le
    omega
  let N : Subgroup Γ := T ⊔ Subgroup.zpowers d
  have hTN : T ≤ N := le_sup_left
  have hN : N ≤ Subgroup.normalizer (T : Set Γ) :=
    sup_le Subgroup.le_normalizer (Subgroup.zpowers_le.mpr hdT)
  obtain ⟨hxN, hfix⟩ := normalizer_sup_zpowers_and_fixV ρ hdT hxT hdx hfixx
  have hxr : x ^ r = 1 := by rw [← hx]; exact pow_orderOf_eq_one x
  by_contra hnt
  push Not at hnt
  have hD3 : Nat.card (Subgroup.zpowers d) = 3 := by rw [Nat.card_zpowers, hd]
  obtain ⟨W, hWinv, hWt, hWs⟩ :=
    exists_irreducible_unfaithful (ρ := ρ) (hp2 := hp2) (r := 3) (hr := Nat.prime_three)
      (hr2 := by norm_num) (hrp := Ne.symm hp3) (D := Subgroup.zpowers d) (T := T)
      (hD := hD3) (hT := hT) (hDT := Subgroup.zpowers_le.mpr hdT) (hnt := hnt)
  have hW : CFSG.RepresentationTheory.IsSimpleUnder ρ N W := ⟨hWinv, hWs⟩
  have hQ : ∀ W' : Submodule (ZMod p) V, CFSG.RepresentationTheory.IsSimpleUnder ρ N W' →
      (∃ t ∈ T, ∃ w ∈ W', ρ t w ≠ w) →
      ∃ φ : ↥T →* QuaternionGroup 2, Function.Surjective φ ∧
        ∀ t : ↥T, φ t = 1 ↔ ∀ w ∈ W', ρ t w = w := by
    intro W' hW' hWt'
    exact exists_quaternion_quotient_of_simpleUnder ρ hp2lt hD3 hfixd hT
      (Subgroup.zpowers_le.mpr hdT) hTd hW' hWt'
  have htriv := CFSG.RepresentationTheory.acts_trivially_of_quaternion_quotients
    (ρ := ρ) (N := N) hTN hN hT hp2 hr hr5 hxN hxT hxr hfix hQ hTx hW
  obtain ⟨t, ht, w, hw, hne⟩ := hWt
  exact hne (htriv t ht w hw)

section Frattini

variable {q : ℕ} [Fact q.Prime] {P : Subgroup Γ} [P.Normal]
  [IsElementaryAbelian q (↥P ⧸ frattini ↥P)]

theorem fixV_frattiniRep_zpowers_eq_bot (hP : IsPGroup q P) {a : Γ} {r : ℕ}
    (hr : r.Prime) (ha : orderOf a = r)
    (hC : P ⊓ Subgroup.centralizer ({a} : Set Γ) = ⊥) :
    fixV (frattiniRep q (MulAut.conjNormal (H := P))) (Subgroup.zpowers a) = ⊥ := by
  rw [Submodule.eq_bot_iff]
  intro v hv
  exact frattiniRep_conjNormal_eq_zero_of_inf_centralizer_eq_bot hP hr ha hC v
    ((CFSG.LocalAnalysis.UniquenessCase.UC6.mem_fixV_zpowers_uc6
      (frattiniRep q (MulAut.conjNormal (H := P))) a v).mp hv)

theorem frattiniRep_eq_one_of_even (hq2 : q ≠ 2) (hP : IsPGroup q P) (hP1 : P ≠ ⊥)
    {T A : Subgroup Γ} (hT : IsPGroup 2 T) (hAT : A ≤ Subgroup.normalizer (T : Set Γ))
    (hAc : ∀ a ∈ A, ∀ b ∈ A, Commute a b)
    (hAP : ∀ a ∈ A, a ≠ 1 → P ⊓ Subgroup.centralizer ({a} : Set Γ) = ⊥)
    (hTA : ∀ a ∈ A, a ≠ 1 → ⁅Subgroup.zpowers a, T⁆ = T)
    {n : ℕ} (hn : 3 ≤ n) (heven : Even n)
    (hπ : ∀ r : ℕ, r.Prime → r ∣ 2 ^ n - 1 → ∃ a ∈ A, orderOf a = r) :
    ∀ t ∈ T, frattiniRep q (MulAut.conjNormal (H := P)) t = 1 := by
  have hd3dvd : 3 ∣ 2 ^ n - 1 := by
    have hmod : (2 : ℕ) ^ n ≡ 1 [MOD 3] := by
      rw [Nat.ModEq, CFSG.two_pow_mod_three_of_even heven]
    exact (Nat.modEq_iff_dvd' (Nat.one_le_pow' n 1)).mp hmod.symm
  obtain ⟨d, hdA, hd⟩ := hπ 3 Nat.prime_three hd3dvd
  obtain ⟨r, hr, hr5, hrdvd⟩ := CFSG.exists_prime_five_le_dvd_two_pow_sub_one hn
  obtain ⟨x, hxA, hx⟩ := hπ r hr hrdvd
  have hd1 : d ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hd
    exact Nat.prime_three.ne_one hd.symm
  have hx1 : x ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hx
    exact hr.ne_one hx.symm
  have hq3 : q ≠ 3 := by
    have hne := orderOf_ne_of_inf_centralizer_eq_bot hP hP1
      (Subgroup.subset_normalizer_of_normal (H := P) (S := {d}) (Set.mem_singleton d))
      (hAP d hdA hd1)
    intro h
    exact hne (hd.trans h.symm)
  refine eq_one_of_commute_three_prime (ρ := frattiniRep q (MulAut.conjNormal (H := P)))
    hq2 hq3 hT hd hr hr5 hx (hAc d hdA x hxA) (hAT hdA) (hAT hxA)
    (hTA d hdA hd1) (hTA x hxA hx1) ?_ ?_
  · exact fixV_frattiniRep_zpowers_eq_bot hP Nat.prime_three hd (hAP d hdA hd1)
  · exact fixV_frattiniRep_zpowers_eq_bot hP hr hx (hAP x hxA hx1)

theorem not_exists_ne_one_of_odd (hq2 : q ≠ 2) (hP : IsPGroup q P)
    {T A : Subgroup Γ} (hT : IsPGroup 2 T) (hAT : A ≤ Subgroup.normalizer (T : Set Γ))
    (hAP : ∀ a ∈ A, a ≠ 1 → P ⊓ Subgroup.centralizer ({a} : Set Γ) = ⊥)
    (hTA : ∀ a ∈ A, a ≠ 1 → ⁅Subgroup.zpowers a, T⁆ = T)
    {n : ℕ} (hn : 3 ≤ n) (hodd : Odd n)
    (hπ : ∀ r : ℕ, r.Prime → r ∣ 2 ^ n - 1 → ∃ a ∈ A, orderOf a = r) :
    ¬ ∃ t ∈ T, frattiniRep q (MulAut.conjNormal (H := P)) t ≠ 1 := by
  rintro ⟨t, ht, htne⟩
  have h8 : 8 ≤ 2 ^ n := by
    calc 8 = 2 ^ 3 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  obtain ⟨r, hr, hrdvd⟩ := Nat.exists_prime_and_dvd (show 2 ^ n - 1 ≠ 1 by omega)
  have hoddval : Odd (2 ^ n - 1) := by
    have he : Even (2 ^ n) := even_two.pow_of_ne_zero (by omega)
    exact Nat.Even.sub_odd (Nat.one_le_pow' n 1) he odd_one
  have hr2 : r ≠ 2 := by
    rintro rfl
    exact (Nat.not_even_iff_odd.mpr hoddval) (even_iff_two_dvd.mpr hrdvd)
  obtain ⟨a, haA, har⟩ := hπ r hr hrdvd
  have hane : a ≠ 1 := by
    intro h
    rw [h, orderOf_one] at har
    exact hr.ne_one har.symm
  obtain ⟨k, hk⟩ := orderOf_two_eq_two_pow_of_fixV_eq_bot
    (ρ := frattiniRep q (MulAut.conjNormal (H := P))) (hp2 := hq2) (T := T) (hT := hT)
    (b := a) (r := r) (hr := hr) (hr2 := hr2) (hbr := har) (hbT := hAT haA)
    (hTb := hTA a haA hane)
    (hfix := fixV_frattiniRep_zpowers_eq_bot hP hr har (hAP a haA hane))
    (hnt := ⟨t, ht, htne⟩)
  exact CFSG.not_exists_orderOf_two_eq_two_pow_of_odd hodd hr hrdvd ⟨k, hk⟩

theorem le_centralizer_of_semiregular (hq2 : q ≠ 2) (hP : IsPGroup q P) (hP1 : P ≠ ⊥)
    {T A : Subgroup Γ} (hT : IsPGroup 2 T) (hAT : A ≤ Subgroup.normalizer (T : Set Γ))
    (hAc : ∀ a ∈ A, ∀ b ∈ A, Commute a b)
    (hAP : ∀ a ∈ A, a ≠ 1 → P ⊓ Subgroup.centralizer ({a} : Set Γ) = ⊥)
    (hTA : ∀ a ∈ A, a ≠ 1 → ⁅Subgroup.zpowers a, T⁆ = T)
    {n : ℕ} (hn : 3 ≤ n) (hπ : ∀ r : ℕ, r.Prime → r ∣ 2 ^ n - 1 → ∃ a ∈ A, orderOf a = r) :
    T ≤ Subgroup.centralizer (P : Set Γ) := by
  have hρ : ∀ t ∈ T, frattiniRep q (MulAut.conjNormal (H := P)) t = 1 := by
    rcases Nat.even_or_odd n with heven | hodd
    · exact frattiniRep_eq_one_of_even hq2 hP hP1 hT hAT hAc hAP hTA hn heven hπ
    · by_contra hnt
      push Not at hnt
      exact not_exists_ne_one_of_odd hq2 hP hT hAT hAP hTA hn hodd hπ hnt
  intro t ht
  exact mem_centralizer_of_frattiniRep_conjNormal_eq_one hP hq2
    (hT.to_le (Subgroup.zpowers_le.mpr ht)) (hρ t ht)

end Frattini


