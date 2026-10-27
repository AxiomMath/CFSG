module

public import CFSG.Quasithin.Vol2.Ch12Sec2OrbitTransfer
public import CFSG.Quasithin.H13.StatementsL2

public section

namespace CFSG.Quasithin.H13.Orbit

open CFSG.Quasithin CFSG.Quasithin.H.Mathieu
open scoped Pointwise

section Weight

variable {n : ℕ}

abbrev wtP (x : G6.PermMod n) : ℕ := hammingNorm (Multiplicative.toAdd x)

theorem zmod_two_eq_iff {a b : ZMod 2} : a = b ↔ (a ≠ 0 ↔ b ≠ 0) := by
  revert a b
  decide

theorem permMod_eq_iff {x y : G6.PermMod n} :
    x = y ↔ ∀ i, (Multiplicative.toAdd x i ≠ 0 ↔ Multiplicative.toAdd y i ≠ 0) := by
  constructor
  · rintro rfl i
    exact Iff.rfl
  · intro h
    apply Multiplicative.toAdd.injective
    funext i
    exact zmod_two_eq_iff.2 (h i)

theorem exists_alt_permAct_eq (hn : 3 ≤ n) {x y : G6.PermMod n} (h : wtP x = wtP y) :
    ∃ σ ∈ alternatingGroup (Fin n), G6.permAct n σ x = y := by
  classical
  have hs : (Finset.univ.filter fun i => Multiplicative.toAdd x i ≠ 0) ∈
      Set.powersetCard (Fin n) (wtP x) := rfl
  have ht : (Finset.univ.filter fun i => Multiplicative.toAdd y i ≠ 0) ∈
      Set.powersetCard (Fin n) (wtP x) := h.symm
  have := Set.powersetCard.isPretransitive_alternatingGroup (α := Fin n) (n := wtP x)
    (by simpa using hn)
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (alternatingGroup (Fin n))
    (⟨_, hs⟩ : Set.powersetCard (Fin n) (wtP x)) ⟨_, ht⟩
  have hgs : g • (Finset.univ.filter fun i => Multiplicative.toAdd x i ≠ 0) =
      Finset.univ.filter fun i => Multiplicative.toAdd y i ≠ 0 :=
    congrArg Subtype.val hg
  refine ⟨g, g.2, permMod_eq_iff.2 fun i => ?_⟩
  rw [G6.permAct_apply]
  have h1 : i ∈ g • (Finset.univ.filter fun i => Multiplicative.toAdd x i ≠ 0) ↔
      i ∈ Finset.univ.filter fun i => Multiplicative.toAdd y i ≠ 0 := by rw [hgs]
  rw [← Finset.inv_smul_mem_iff] at h1
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at h1
  exact h1

theorem wtP_permAct (σ : Equiv.Perm (Fin n)) (x : G6.PermMod n) :
    wtP (G6.permAct n σ x) = wtP x := by
  classical
  have := Fintype.card_congr ((σ⁻¹ : Equiv.Perm (Fin n)).subtypeEquiv
    (p := fun i => Multiplicative.toAdd x (σ⁻¹ i) ≠ 0)
    (q := fun i => Multiplicative.toAdd x i ≠ 0) fun i => Iff.rfl)
  rw [Fintype.card_subtype, Fintype.card_subtype] at this
  exact this

theorem wtP_le (x : G6.PermMod n) : wtP x ≤ n := by
  have := hammingNorm_le_card_fintype (x := Multiplicative.toAdd x)
  rwa [Fintype.card_fin] at this

theorem wtP_eq_zero {x : G6.PermMod n} : wtP x = 0 ↔ x = 1 := by
  rw [wtP, hammingNorm_eq_zero, toAdd_eq_zero]

theorem mem_coreMod_iff (x : G6.PermMod n) : x ∈ G6.coreMod n ↔ Even (wtP x) := by
  classical
  rw [G6.mem_coreMod, ← ZMod.natCast_eq_zero_iff_even]
  have : ∑ i, Multiplicative.toAdd x i = (wtP x : ZMod 2) := by
    rw [← Finset.sum_filter_ne_zero, wtP, hammingNorm, Finset.cast_card]
    apply Finset.sum_congr rfl
    intro i hi
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
    revert hi
    generalize Multiplicative.toAdd x i = a
    revert a
    decide
  rw [this]

theorem allOnes_mul_self : G6.allOnes n * G6.allOnes n = 1 := by
  apply Multiplicative.toAdd.injective
  funext i
  change (1 : ZMod 2) + 1 = 0
  decide

theorem mem_zpowers_iff_of_mul_self {G : Type*} [Group G] {p : G} (hp : p * p = 1) (m : G) :
    m ∈ Subgroup.zpowers p ↔ m = 1 ∨ m = p := by
  constructor
  · rintro ⟨k, rfl⟩
    have h2 : p ^ (2 : ℤ) = 1 := by rw [zpow_two, hp]
    change p ^ k = 1 ∨ p ^ k = p
    rw [← Int.emod_add_mul_ediv k 2, zpow_add, zpow_mul, h2, one_zpow, mul_one]
    rcases Int.emod_two_eq_zero_or_one k with h | h <;> rw [h] <;> simp
  · rintro (rfl | rfl)
    · exact Subgroup.one_mem _
    · exact Subgroup.mem_zpowers _

theorem mem_zpowers_allOnes (k : G6.PermMod n) :
    k ∈ Subgroup.zpowers (G6.allOnes n) ↔ k = 1 ∨ k = G6.allOnes n :=
  mem_zpowers_iff_of_mul_self allOnes_mul_self k

theorem wtP_mul_allOnes (x : G6.PermMod n) : wtP (x * G6.allOnes n) = n - wtP x := by
  classical
  have h : ∀ i, (Multiplicative.toAdd (x * G6.allOnes n) i ≠ 0 ↔
      ¬ (Multiplicative.toAdd x i ≠ 0)) := by
    intro i
    change Multiplicative.toAdd x i + 1 ≠ 0 ↔ _
    generalize Multiplicative.toAdd x i = a
    revert a
    decide
  have h2 := Finset.card_filter_add_card_filter_not
    (s := Finset.univ) (fun i : Fin n => Multiplicative.toAdd x i ≠ 0)
  rw [Finset.card_univ, Fintype.card_fin] at h2
  rw [wtP, hammingNorm, Finset.filter_congr (fun i _ => h i)]
  rw [wtP, hammingNorm]
  omega

theorem wtP_allOnes : wtP (G6.allOnes n) = n := by
  have := wtP_mul_allOnes (n := n) 1
  rwa [one_mul, (wtP_eq_zero (n := n)).2 rfl, Nat.sub_zero] at this

theorem wtP_eq_self_iff {x : G6.PermMod n} : wtP x = n ↔ x = G6.allOnes n := by
  constructor
  · intro h
    have h1 := wtP_mul_allOnes x
    rw [h, Nat.sub_self, wtP_eq_zero] at h1
    calc x = x * G6.allOnes n * G6.allOnes n := by rw [mul_assoc, allOnes_mul_self, mul_one]
      _ = G6.allOnes n := by rw [h1, one_mul]
  · rintro rfl
    exact wtP_allOnes

theorem card_coreMod_wt (P : ℕ → Prop) [DecidablePred P] :
    Nat.card {x : ↥(G6.coreMod n) // P (wtP (x : G6.PermMod n))} =
      ∑ k ∈ Finset.range (n + 1), if Even k ∧ P k then n.choose k else 0 := by
  classical
  have e1 : {x : ↥(G6.coreMod n) // P (wtP (x : G6.PermMod n))} ≃
      {x : G6.PermMod n // Even (wtP x) ∧ P (wtP x)} :=
    { toFun := fun x => ⟨x.1, (mem_coreMod_iff _).1 x.1.2, x.2⟩
      invFun := fun x => ⟨⟨x.1, (mem_coreMod_iff _).2 x.2.1⟩, x.2.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  let e0 : G6.PermMod n ≃ Finset (Fin n) :=
    { toFun := fun x => Finset.univ.filter fun i => Multiplicative.toAdd x i ≠ 0
      invFun := fun s => Multiplicative.ofAdd fun i => if i ∈ s then 1 else 0
      left_inv := fun x => by
        refine (permMod_eq_iff.2 fun i => ?_)
        simp only [toAdd_ofAdd, Finset.mem_filter, Finset.mem_univ, true_and]
        by_cases hi : Multiplicative.toAdd x i ≠ 0
        · simp [hi]
        · simp [hi]
      right_inv := fun s => by
        ext i
        by_cases hi : i ∈ s <;> simp [hi] }
  have e2 : {x : G6.PermMod n // Even (wtP x) ∧ P (wtP x)} ≃
      {s : Finset (Fin n) // Even s.card ∧ P s.card} :=
    e0.subtypeEquiv fun _ => Iff.rfl
  have key := Finset.sum_powerset_apply_card (fun k => if Even k ∧ P k then (1 : ℕ) else 0)
    (x := (Finset.univ : Finset (Fin n)))
  rw [Nat.card_congr (e1.trans e2), Nat.card_eq_fintype_card, Fintype.card_subtype,
    Finset.card_filter, ← Finset.powerset_univ]
  refine key.trans ?_
  rw [Finset.card_univ, Fintype.card_fin]
  apply Finset.sum_congr rfl
  intro k _
  split_ifs <;> simp

end Weight

section Models

variable {n : ℕ}

theorem altDn_mem_ker {k : G6.PermMod n} :
    k ∈ Subgroup.zpowers (G6.allOnes n) ⊓ G6.coreMod n ↔
      (k = 1 ∨ k = G6.allOnes n) ∧ Even (wtP k) := by
  rw [Subgroup.mem_inf, mem_zpowers_allOnes, mem_coreMod_iff]

theorem altDn_ker_odd (hn : Odd n) {k : G6.PermMod n}
    (hk : k ∈ Subgroup.zpowers (G6.allOnes n) ⊓ G6.coreMod n) : k = 1 := by
  obtain ⟨h | h, he⟩ := altDn_mem_ker.1 hk
  · exact h
  · rw [h, wtP_allOnes] at he
    exact absurd he (Nat.not_even_iff_odd.2 hn)

theorem altDn_card_ker_odd (hn : Odd n) : Nat.card ↥(FFModel.altDn n).ker = 1 := by
  change Nat.card ↥(Subgroup.zpowers (G6.allOnes n) ⊓ G6.coreMod n) = 1
  rw [Nat.card_eq_one_iff_unique]
  refine ⟨⟨fun a b => Subtype.ext ?_⟩, ⟨1⟩⟩
  rw [altDn_ker_odd hn a.2, altDn_ker_odd hn b.2]

theorem altDn_mem_ker_even (hn : Even n) {k : G6.PermMod n} :
    k ∈ Subgroup.zpowers (G6.allOnes n) ⊓ G6.coreMod n ↔ k = 1 ∨ k = G6.allOnes n := by
  rw [altDn_mem_ker]
  constructor
  · exact fun h => h.1
  · rintro (rfl | rfl)
    · exact ⟨Or.inl rfl, by rw [(wtP_eq_zero (n := n)).2 rfl]; exact ⟨0, rfl⟩⟩
    · exact ⟨Or.inr rfl, by rw [wtP_allOnes]; exact hn⟩

theorem allOnes_ne_one (hn : n ≠ 0) : G6.allOnes n ≠ 1 := by
  intro h
  have := wtP_allOnes (n := n)
  rw [h, (wtP_eq_zero (n := n)).2 rfl] at this
  exact hn this.symm

theorem altDn_card_ker_even (hn : Even n) (hn0 : n ≠ 0) :
    Nat.card ↥(FFModel.altDn n).ker = 2 := by
  change Nat.card ↥(Subgroup.zpowers (G6.allOnes n) ⊓ G6.coreMod n) = 2
  have hle : Subgroup.zpowers (G6.allOnes n) ≤ G6.coreMod n := by
    intro k hk
    have := ((altDn_mem_ker_even hn).2 ((mem_zpowers_allOnes k).1 hk))
    exact this.2
  rw [inf_eq_left.2 hle, Nat.card_zpowers]
  exact orderOf_eq_prime (by rw [sq, allOnes_mul_self]) (allOnes_ne_one hn0)

theorem altDn_classFn_odd (hn : Odd n) (hn3 : 3 ≤ n) :
    (∀ m ∈ G6.coreMod n, ∀ k ∈ Subgroup.zpowers (G6.allOnes n) ⊓ G6.coreMod n,
      wtP (m * k) = wtP m) ∧
    (∀ γ : ↥(alternatingGroup (Fin n)), ∀ m ∈ G6.coreMod n,
      wtP (G6.permAct n (γ : Equiv.Perm (Fin n)) m) = wtP m) ∧
    (∀ m ∈ G6.coreMod n, ∀ m' ∈ G6.coreMod n, wtP m = wtP m' →
      ∃ γ : ↥(alternatingGroup (Fin n)), ∃ k ∈ Subgroup.zpowers (G6.allOnes n) ⊓ G6.coreMod n,
        G6.permAct n (γ : Equiv.Perm (Fin n)) m = m' * k) := by
  refine ⟨fun m _ k hk => ?_, fun γ m _ => wtP_permAct _ m, fun m _ m' _ h => ?_⟩
  · rw [altDn_ker_odd hn hk, mul_one]
  · obtain ⟨σ, hσ, hσm⟩ := exists_alt_permAct_eq hn3 h
    exact ⟨⟨σ, hσ⟩, 1, Subgroup.one_mem _, by rw [mul_one]; exact hσm⟩

abbrev minWt (n : ℕ) (x : G6.PermMod n) : ℕ := min (wtP x) (n - wtP x)

theorem altDn_classFn_even (hn : Even n) (hn3 : 3 ≤ n) :
    (∀ m ∈ G6.coreMod n, ∀ k ∈ Subgroup.zpowers (G6.allOnes n) ⊓ G6.coreMod n,
      minWt n (m * k) = minWt n m) ∧
    (∀ γ : ↥(alternatingGroup (Fin n)), ∀ m ∈ G6.coreMod n,
      minWt n (G6.permAct n (γ : Equiv.Perm (Fin n)) m) = minWt n m) ∧
    (∀ m ∈ G6.coreMod n, ∀ m' ∈ G6.coreMod n, minWt n m = minWt n m' →
      ∃ γ : ↥(alternatingGroup (Fin n)), ∃ k ∈ Subgroup.zpowers (G6.allOnes n) ⊓ G6.coreMod n,
        G6.permAct n (γ : Equiv.Perm (Fin n)) m = m' * k) := by
  refine ⟨fun m _ k hk => ?_, fun γ m _ => ?_, fun m _ m' _ h => ?_⟩
  · rcases (altDn_mem_ker_even hn).1 hk with rfl | rfl
    · rw [mul_one]
    · have h1 := wtP_mul_allOnes m
      have h2 := wtP_le m
      rw [minWt, minWt, h1]
      omega
  · rw [minWt, minWt, wtP_permAct]
  · have h1 := wtP_le m
    have h2 := wtP_le m'
    have h3 := wtP_mul_allOnes m'
    rw [minWt, minWt] at h
    by_cases he : wtP m = wtP m'
    · obtain ⟨σ, hσ, hσm⟩ := exists_alt_permAct_eq hn3 he
      exact ⟨⟨σ, hσ⟩, 1, Subgroup.one_mem _, by rw [mul_one]; exact hσm⟩
    · have he' : wtP m = wtP (m' * G6.allOnes n) := by
        rw [h3]
        omega
      obtain ⟨σ, hσ, hσm⟩ := exists_alt_permAct_eq hn3 he'
      exact ⟨⟨σ, hσ⟩, G6.allOnes n, (altDn_mem_ker_even hn).2 (Or.inr rfl), hσm⟩

theorem altCore_classFn (hn3 : 3 ≤ n) :
    (∀ m ∈ G6.coreMod n, ∀ k ∈ (⊥ : Subgroup (G6.PermMod n)), wtP (m * k) = wtP m) ∧
    (∀ γ : ↥(alternatingGroup (Fin n)), ∀ m ∈ G6.coreMod n,
      wtP (G6.permAct n (γ : Equiv.Perm (Fin n)) m) = wtP m) ∧
    (∀ m ∈ G6.coreMod n, ∀ m' ∈ G6.coreMod n, wtP m = wtP m' →
      ∃ γ : ↥(alternatingGroup (Fin n)), ∃ k ∈ (⊥ : Subgroup (G6.PermMod n)),
        G6.permAct n (γ : Equiv.Perm (Fin n)) m = m' * k) := by
  refine ⟨fun m _ k hk => ?_, fun γ m _ => wtP_permAct _ m, fun m _ m' _ h => ?_⟩
  · rw [Subgroup.mem_bot.1 hk, mul_one]
  · obtain ⟨σ, hσ, hσm⟩ := exists_alt_permAct_eq hn3 h
    exact ⟨⟨σ, hσ⟩, 1, Subgroup.one_mem _, by rw [mul_one]; exact hσm⟩

theorem altCore_card_ker : Nat.card ↥(altCoreModel n).ker = 1 := by
  change Nat.card ↥(⊥ : Subgroup (G6.PermMod n)) = 1
  exact Subgroup.card_bot

end Models

theorem wtP_mem_of_coreMod {n : ℕ} {x : G6.PermMod n} (hx : x ∈ G6.coreMod n) (h1 : x ≠ 1) :
    Even (wtP x) ∧ wtP x ≠ 0 ∧ wtP x ≤ n :=
  ⟨(mem_coreMod_iff x).1 hx, fun h => h1 (wtP_eq_zero.1 h), wtP_le x⟩

theorem orbitAltNaturalFive :
    ∀ (V : Type) [CommGroup V] [Finite V] (H : Subgroup (MulAut V)),
      AlternatingNatural H ⊤ ⊥ 5 → OrbitLengthsIn H [10, 5] ∧ OrbitsSeparated H := by
  intro V _ _ H hH
  obtain ⟨π, β, hR⟩ := (realizes_iff (FFModel.altDn 5) H ⊤ ⊥).1 hH
  obtain ⟨hker, hact, htrans⟩ := altDn_classFn_odd (n := 5) ⟨2, rfl⟩ (by norm_num)
  refine orbits_of_classFn hR (fun x => wtP (n := 5) x) hker hact htrans {2, 4}
    (fun c => ∑ k ∈ Finset.range 6, if Even k ∧ k = c then Nat.choose 5 k else 0) [10, 5]
    (by rw [altDn_card_ker_odd (n := 5) ⟨2, rfl⟩]; norm_num) (fun m hm => ?_)
    (fun m => card_coreMod_wt (n := 5) (· = wtP (n := 5) m.1))
    (by rw [altDn_card_ker_odd (n := 5) ⟨2, rfl⟩]; decide) (by decide)
  have hm1 : m.1 ≠ 1 := fun h => hm (by rw [h]; exact Subgroup.one_mem _)
  obtain ⟨⟨r, hr⟩, h0, hle⟩ := wtP_mem_of_coreMod m.2 hm1
  simp only [Finset.mem_insert, Finset.mem_singleton]
  omega

theorem orbitAltNaturalSix :
    ∀ (V : Type) [CommGroup V] [Finite V] (H : Subgroup (MulAut V)),
      AlternatingNatural H ⊤ ⊥ 6 → OrbitLengthsIn H [15] ∧ OrbitsSeparated H := by
  intro V _ _ H hH
  obtain ⟨π, β, hR⟩ := (realizes_iff (FFModel.altDn 6) H ⊤ ⊥).1 hH
  obtain ⟨hker, hact, htrans⟩ := altDn_classFn_even (n := 6) ⟨3, rfl⟩ (by norm_num)
  refine orbits_of_classFn hR (fun x => minWt 6 x) hker hact htrans {2}
    (fun c => ∑ k ∈ Finset.range 7, if Even k ∧ min k (6 - k) = c then Nat.choose 6 k else 0)
    [15] (by rw [altDn_card_ker_even (n := 6) ⟨3, rfl⟩ (by norm_num)]; norm_num)
    (fun m hm => ?_) (fun m => card_coreMod_wt (n := 6) (fun k => min k (6 - k) = minWt 6 m.1))
    (by rw [altDn_card_ker_even (n := 6) ⟨3, rfl⟩ (by norm_num)]; decide) (by decide)
  have hm1 : m.1 ≠ 1 := fun h => hm ((altDn_mem_ker_even ⟨3, rfl⟩).2 (Or.inl h))
  have hm2 : m.1 ≠ G6.allOnes 6 := fun h => hm ((altDn_mem_ker_even ⟨3, rfl⟩).2 (Or.inr h))
  obtain ⟨⟨r, hr⟩, h0, hle⟩ := wtP_mem_of_coreMod m.2 hm1
  have h6 : wtP (n := 6) m.1 ≠ 6 := fun h => hm2 (wtP_eq_self_iff.1 h)
  simp only [Finset.mem_singleton, minWt, min_def]
  split_ifs <;> omega

theorem orbitAltNaturalSeven :
    ∀ (V : Type) [CommGroup V] [Finite V] (H : Subgroup (MulAut V)),
      AlternatingNatural H ⊤ ⊥ 7 → OrbitLengthsIn H [21, 35, 7] ∧ OrbitsSeparated H := by
  intro V _ _ H hH
  obtain ⟨π, β, hR⟩ := (realizes_iff (FFModel.altDn 7) H ⊤ ⊥).1 hH
  obtain ⟨hker, hact, htrans⟩ := altDn_classFn_odd (n := 7) ⟨3, rfl⟩ (by norm_num)
  refine orbits_of_classFn hR (fun x => wtP (n := 7) x) hker hact htrans {2, 4, 6}
    (fun c => ∑ k ∈ Finset.range 8, if Even k ∧ k = c then Nat.choose 7 k else 0) [21, 35, 7]
    (by rw [altDn_card_ker_odd (n := 7) ⟨3, rfl⟩]; norm_num) (fun m hm => ?_)
    (fun m => card_coreMod_wt (n := 7) (· = wtP (n := 7) m.1))
    (by rw [altDn_card_ker_odd (n := 7) ⟨3, rfl⟩]; decide) (by decide)
  have hm1 : m.1 ≠ 1 := fun h => hm (by rw [h]; exact Subgroup.one_mem _)
  obtain ⟨⟨r, hr⟩, h0, hle⟩ := wtP_mem_of_coreMod m.2 hm1
  simp only [Finset.mem_insert, Finset.mem_singleton]
  omega

theorem orbitAltNaturalEight :
    ∀ (V : Type) [CommGroup V] [Finite V] (H : Subgroup (MulAut V)),
      AlternatingNatural H ⊤ ⊥ 8 → OrbitLengthsIn H [28, 35] ∧ OrbitsSeparated H := by
  intro V _ _ H hH
  obtain ⟨π, β, hR⟩ := (realizes_iff (FFModel.altDn 8) H ⊤ ⊥).1 hH
  obtain ⟨hker, hact, htrans⟩ := altDn_classFn_even (n := 8) ⟨4, rfl⟩ (by norm_num)
  refine orbits_of_classFn hR (fun x => minWt 8 x) hker hact htrans {2, 4}
    (fun c => ∑ k ∈ Finset.range 9, if Even k ∧ min k (8 - k) = c then Nat.choose 8 k else 0)
    [28, 35] (by rw [altDn_card_ker_even (n := 8) ⟨4, rfl⟩ (by norm_num)]; norm_num)
    (fun m hm => ?_) (fun m => card_coreMod_wt (n := 8) (fun k => min k (8 - k) = minWt 8 m.1))
    (by rw [altDn_card_ker_even (n := 8) ⟨4, rfl⟩ (by norm_num)]; decide) (by decide)
  have hm1 : m.1 ≠ 1 := fun h => hm ((altDn_mem_ker_even ⟨4, rfl⟩).2 (Or.inl h))
  have hm2 : m.1 ≠ G6.allOnes 8 := fun h => hm ((altDn_mem_ker_even ⟨4, rfl⟩).2 (Or.inr h))
  obtain ⟨⟨r, hr⟩, h0, hle⟩ := wtP_mem_of_coreMod m.2 hm1
  have h8 : wtP (n := 8) m.1 ≠ 8 := fun h => hm2 (wtP_eq_self_iff.1 h)
  simp only [Finset.mem_insert, Finset.mem_singleton, minWt, min_def]
  split_ifs <;> omega

theorem altCore_choose_fixed {n : ℕ} (hn3 : 3 ≤ n) {V : Type*} [CommGroup V]
    {H : Subgroup (MulAut V)} {π : (altCoreModel n).Gam →* ↥H}
    {β : ↥(⊤ : Subgroup V) →* ↥(altCoreModel n).sec ⧸
      (altCoreModel n).ker.subgroupOf (altCoreModel n).sec}
    (hR : RealizesBy (altCoreModel n) H ⊤ ⊥ π β) {z : V} (hzH : z ∈ fixV H)
    {m : ↥(altCoreModel n).sec} (hm : coordOf β z = QuotientGroup.mk m) :
    ∑ k ∈ Finset.range (n + 1),
      (if Even k ∧ k = wtP (n := n) m.1 then n.choose k else 0) = 1 := by
  obtain ⟨hker, hact, htrans⟩ := altCore_classFn hn3
  have hc := card_orbitIn_of_classFn (D := altCoreModel n) (fun x => wtP (n := n) x) hR hker hact
    htrans hm
  have ho : orbitIn H z = {z} := by
    ext w
    constructor
    · rintro ⟨h, hh, rfl⟩
      exact hzH h hh
    · rintro rfl
      exact ⟨1, H.one_mem, rfl⟩
  have h1 : Nat.card ↑(orbitIn H z) = 1 := by
    rw [ho]
    exact Nat.card_unique
  rw [h1, altCore_card_ker, one_mul] at hc
  exact (card_coreMod_wt (n := n) (· = wtP (n := n) m.1)).symm.trans hc.symm

theorem altCore_wtP_mul_allOnes {n : ℕ} (m' z₀ : ↥(altCoreModel n).sec)
    (hz₀ : z₀.1 = G6.allOnes n) : wtP (n := n) (m' * z₀).1 = n - wtP (n := n) m'.1 := by
  have h := wtP_mul_allOnes (n := n) m'.1
  rw [← hz₀] at h
  exact h

theorem altCore_ne_of_not_mem {n : ℕ} {m z₀ : ↥(altCoreModel n).sec}
    (hmz : (m⁻¹ * z₀).1 ∉ (altCoreModel n).ker) : m.1 ≠ z₀.1 := by
  intro h
  apply hmz
  have : m⁻¹ * z₀ = 1 := by
    rw [inv_mul_eq_one]
    exact Subtype.ext h
  rw [this]
  exact Subgroup.one_mem _

theorem orbitAltCoreSix :
    ∀ (V : Type) [CommGroup V] [Finite V] (H : Subgroup (MulAut V)) (z : V), z ≠ 1 →
      z ∈ fixV H → (altCoreModel 6).Realizes H ⊤ ⊥ →
        OrbitLengthsInMod H z [15] ∧ OrbitsSeparatedMod H z := by
  intro V _ _ H z hz1 hzH hH
  obtain ⟨π, β, hR⟩ := (realizes_iff (altCoreModel 6) H ⊤ ⊥).1 hH
  obtain ⟨hker, hact, htrans⟩ := altCore_classFn (n := 6) (by norm_num)
  obtain ⟨z₀, hz₀, hz₀k⟩ := exists_coordOf_eq hR hz1
  have hz₀1 : z₀.1 ≠ 1 := fun h => hz₀k (by rw [h]; exact Subgroup.one_mem _)
  have hc := altCore_choose_fixed (n := 6) (by norm_num) hR hzH hz₀
  have hz₀w : wtP (n := 6) z₀.1 = 6 := by
    obtain ⟨⟨r, hr⟩, h0, hle⟩ := wtP_mem_of_coreMod z₀.2 hz₀1
    have : wtP (n := 6) z₀.1 = 2 ∨ wtP (n := 6) z₀.1 = 4 ∨ wtP (n := 6) z₀.1 = 6 := by omega
    rcases this with h | h | h
    · rw [h] at hc
      exact absurd hc (by decide)
    · rw [h] at hc
      exact absurd hc (by decide)
    · exact h
  have hz₀a : z₀.1 = G6.allOnes 6 := wtP_eq_self_iff.1 hz₀w
  refine orbitsMod_of_classFn hR (fun x => wtP (n := 6) x) hker hact htrans z₀ hz₀ {2, 4}
    (fun c => ∑ k ∈ Finset.range 7, if Even k ∧ k = c then Nat.choose 6 k else 0) [15]
    (by rw [altCore_card_ker]; norm_num) (fun m hm hmz => ?_)
    (fun m => card_coreMod_wt (n := 6) (· = wtP (n := 6) m.1))
    (by rw [altCore_card_ker]; decide) (fun m m' hmS hm'S hN => ?_)
  · have hm1 : m.1 ≠ 1 := fun h => hm (by rw [h]; exact Subgroup.one_mem _)
    have hm2 : m.1 ≠ G6.allOnes 6 := hz₀a ▸ altCore_ne_of_not_mem hmz
    obtain ⟨⟨r, hr⟩, h0, hle⟩ := wtP_mem_of_coreMod m.2 hm1
    have h6 : wtP (n := 6) m.1 ≠ 6 := fun h => hm2 (wtP_eq_self_iff.1 h)
    simp only [Finset.mem_insert, Finset.mem_singleton]
    omega
  · have key : ∀ c ∈ ({2, 4} : Finset ℕ), ∀ c' ∈ ({2, 4} : Finset ℕ),
        (∑ k ∈ Finset.range 7, if Even k ∧ k = c then Nat.choose 6 k else 0) =
          (∑ k ∈ Finset.range 7, if Even k ∧ k = c' then Nat.choose 6 k else 0) →
        c = c' ∨ c = 6 - c' := by decide
    have h := altCore_wtP_mul_allOnes (n := 6) m' z₀ hz₀a
    have h' := key _ hmS _ hm'S hN
    change wtP (n := 6) m.1 = wtP (n := 6) m'.1 ∨ wtP (n := 6) m.1 = wtP (n := 6) (m' * z₀).1
    rw [h]
    exact h'

theorem orbitAltCoreEight :
    ∀ (V : Type) [CommGroup V] [Finite V] (H : Subgroup (MulAut V)) (z : V), z ≠ 1 →
      z ∈ fixV H → (altCoreModel 8).Realizes H ⊤ ⊥ →
        OrbitLengthsInMod H z [28, 70] ∧ OrbitsSeparatedMod H z := by
  intro V _ _ H z hz1 hzH hH
  obtain ⟨π, β, hR⟩ := (realizes_iff (altCoreModel 8) H ⊤ ⊥).1 hH
  obtain ⟨hker, hact, htrans⟩ := altCore_classFn (n := 8) (by norm_num)
  obtain ⟨z₀, hz₀, hz₀k⟩ := exists_coordOf_eq hR hz1
  have hz₀1 : z₀.1 ≠ 1 := fun h => hz₀k (by rw [h]; exact Subgroup.one_mem _)
  have hc := altCore_choose_fixed (n := 8) (by norm_num) hR hzH hz₀
  have hz₀w : wtP (n := 8) z₀.1 = 8 := by
    obtain ⟨⟨r, hr⟩, h0, hle⟩ := wtP_mem_of_coreMod z₀.2 hz₀1
    have : wtP (n := 8) z₀.1 = 2 ∨ wtP (n := 8) z₀.1 = 4 ∨ wtP (n := 8) z₀.1 = 6 ∨
        wtP (n := 8) z₀.1 = 8 := by omega
    rcases this with h | h | h | h
    · rw [h] at hc
      exact absurd hc (by decide)
    · rw [h] at hc
      exact absurd hc (by decide)
    · rw [h] at hc
      exact absurd hc (by decide)
    · exact h
  have hz₀a : z₀.1 = G6.allOnes 8 := wtP_eq_self_iff.1 hz₀w
  refine orbitsMod_of_classFn hR (fun x => wtP (n := 8) x) hker hact htrans z₀ hz₀ {2, 4, 6}
    (fun c => ∑ k ∈ Finset.range 9, if Even k ∧ k = c then Nat.choose 8 k else 0) [28, 70]
    (by rw [altCore_card_ker]; norm_num) (fun m hm hmz => ?_)
    (fun m => card_coreMod_wt (n := 8) (· = wtP (n := 8) m.1))
    (by rw [altCore_card_ker]; decide) (fun m m' hmS hm'S hN => ?_)
  · have hm1 : m.1 ≠ 1 := fun h => hm (by rw [h]; exact Subgroup.one_mem _)
    have hm2 : m.1 ≠ G6.allOnes 8 := hz₀a ▸ altCore_ne_of_not_mem hmz
    obtain ⟨⟨r, hr⟩, h0, hle⟩ := wtP_mem_of_coreMod m.2 hm1
    have h8 : wtP (n := 8) m.1 ≠ 8 := fun h => hm2 (wtP_eq_self_iff.1 h)
    simp only [Finset.mem_insert, Finset.mem_singleton]
    omega
  · have key : ∀ c ∈ ({2, 4, 6} : Finset ℕ), ∀ c' ∈ ({2, 4, 6} : Finset ℕ),
        (∑ k ∈ Finset.range 9, if Even k ∧ k = c then Nat.choose 8 k else 0) =
          (∑ k ∈ Finset.range 9, if Even k ∧ k = c' then Nat.choose 8 k else 0) →
        c = c' ∨ c = 8 - c' := by decide
    have h := altCore_wtP_mul_allOnes (n := 8) m' z₀ hz₀a
    have h' := key _ hmS _ hm'S hN
    change wtP (n := 8) m.1 = wtP (n := 8) m'.1 ∨ wtP (n := 8) m.1 = wtP (n := 8) (m' * z₀).1
    rw [h]
    exact h'

end CFSG.Quasithin.H13.Orbit
