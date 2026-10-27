module

public import Mathlib.GroupTheory.PGroup
import CFSG.GroupTheory.FixedCosetCommutator
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.SubgroupConjAction
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.GroupAction.Defs

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.Q35Natural

variable {Γ : Type*} [Group Γ] [Finite Γ] {Z N : Subgroup Γ}

omit [Finite Γ] in
private lemma pow_five_eq_one_of_conj_mem {c x : Γ}
    (hZc : ∀ z ∈ Z, ∀ g : Γ, g * z = z * g) (hc : orderOf c = 5)
    (hcx : c * x * c⁻¹ * x⁻¹ ∈ Z) :
    (c * x * c⁻¹ * x⁻¹) ^ 5 = 1 := by
  set w : Γ := c * x * c⁻¹ * x⁻¹ with hw
  have hwZ : w ∈ Z := hcx
  have hc5 : c ^ 5 = 1 := by rw [← hc]; exact pow_orderOf_eq_one c
  have hconj : ∀ k : ℕ, c ^ k * x * (c ^ k)⁻¹ = w ^ k * x := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      have hwk : w ^ k ∈ Z := Subgroup.pow_mem Z hwZ k
      calc c ^ (k + 1) * x * (c ^ (k + 1))⁻¹
          = c * (c ^ k * x * (c ^ k)⁻¹) * c⁻¹ := by group
        _ = c * (w ^ k * x) * c⁻¹ := by rw [ih]
        _ = (c * w ^ k) * x * c⁻¹ := by group
        _ = (w ^ k * c) * x * c⁻¹ := by rw [hZc _ hwk c]
        _ = w ^ k * (c * x * c⁻¹) := by group
        _ = w ^ k * (w * x) := by rw [show c * x * c⁻¹ = w * x by rw [hw]; group]
        _ = w ^ (k + 1) * x := by rw [pow_succ']; group
  have h5 := hconj 5
  rw [hc5] at h5
  simp only [inv_one, one_mul, mul_one] at h5
  have : w ^ 5 * x = 1 * x := by rw [one_mul]; exact h5.symm
  exact mul_right_cancel this

private lemma eq_one_of_mem_isPGroup_two_of_pow_five {w : Γ}
    (hZ2 : IsPGroup 2 Z) (hw : w ∈ Z) (hw5 : w ^ 5 = 1) : w = 1 := by
  have hfactTwo : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨a, ha⟩ := hZ2.exists_card_eq
  have hd5 : orderOf w ∣ 5 := orderOf_dvd_of_pow_eq_one hw5
  have hdZ : orderOf w ∣ 2 ^ a := by
    rw [← ha]
    exact Subgroup.orderOf_dvd_natCard Z hw
  have hcop : Nat.Coprime (2 ^ a) 5 :=
    Nat.Coprime.pow_left a (by decide : Nat.Coprime 2 5)
  have hd1 : orderOf w ∣ 1 := by
    have h := Nat.dvd_gcd hdZ hd5
    rwa [hcop.gcd_eq_one] at h
  exact orderOf_eq_one_iff.mp (Nat.dvd_one.mp hd1)

private theorem card_modEq_five_inf_centralizer {S : Subgroup Γ} {c : Γ}
    (hc : orderOf c = 5) (hcN : c ∈ Subgroup.normalizer (S : Set Γ)) :
    Nat.card S ≡ Nat.card ↥(S ⊓ Subgroup.centralizer ({c} : Set Γ)) [MOD 5] := by
  classical
  let A : Subgroup Γ := Subgroup.zpowers c
  have hAcard : Nat.card A = 5 := by
    rw [show A = Subgroup.zpowers c from rfl, Nat.card_zpowers, hc]
  have hfactFive : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  have hA5 : IsPGroup 5 ↥A := IsPGroup.of_card (n := 1) (by simpa using hAcard)
  let hNormAS : Subgroup.Normalizes A S := ⟨Subgroup.zpowers_le.mpr hcN⟩
  have hmod := hA5.card_modEq_card_fixedPoints (α := ↥S)
  let C : Subgroup Γ := S ⊓ Subgroup.centralizer ({c} : Set Γ)
  have hCeq : (MulAction.fixedPoints ↥A ↥S) = (fixedPointSubgroup ↥A ↥S : Set ↥S) := rfl
  have hCsub : fixedPointSubgroup ↥A ↥S = C.subgroupOf S := by
    ext x
    constructor
    · intro hx
      rw [Subgroup.mem_subgroupOf]
      refine Subgroup.mem_inf.mpr ⟨x.2, ?_⟩
      rw [Subgroup.mem_centralizer_singleton_iff]
      have h : (⟨c, Subgroup.mem_zpowers c⟩ : A) • x = x :=
        (FixedPoints.mem_subgroup ↥A ↥S x).mp hx ⟨c, Subgroup.mem_zpowers c⟩
      have h' : c * (x : Γ) * c⁻¹ = (x : Γ) := by
        simpa using congrArg Subtype.val h
      calc (x : Γ) * c = (c * (x : Γ) * c⁻¹) * c := by rw [h']
        _ = c * (x : Γ) := by group
    · intro hx
      rw [Subgroup.mem_subgroupOf, Subgroup.mem_inf] at hx
      rw [FixedPoints.mem_subgroup]
      intro a
      obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp a.2
      apply Subtype.ext
      have hxc : (x : Γ) * c = c * (x : Γ) :=
        Subgroup.mem_centralizer_singleton_iff.mp hx.2
      change (a : Γ) * (x : Γ) * (a : Γ)⁻¹ = (x : Γ)
      rw [← hn]
      have hcomm : Commute (c ^ n) (x : Γ) :=
        (show Commute c (x : Γ) from hxc.symm).zpow_left n
      calc c ^ n * (x : Γ) * (c ^ n)⁻¹ = ((x : Γ) * c ^ n) * (c ^ n)⁻¹ := by rw [hcomm]
        _ = (x : Γ) := by group
  have hcardC : Nat.card ↥(MulAction.fixedPoints ↥A ↥S) = Nat.card ↥C := by
    rw [hCeq]
    change Nat.card ↥(fixedPointSubgroup ↥A ↥S) = Nat.card ↥C
    rw [hCsub]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe (inf_le_left : C ≤ S)).toEquiv
  rwa [hcardC] at hmod

private lemma pow_two_modEq_five {a b : ℕ} (hab : a ≤ b) (hb : b ≤ a + 4)
    (h : 2 ^ (a + 4) ≡ 2 ^ b [MOD 5]) : b = a ∨ b = a + 4 := by
  obtain ⟨d, rfl⟩ : ∃ d, b = a + d := ⟨b - a, by omega⟩
  have hd : d ≤ 4 := by omega
  have hcop : Nat.gcd 5 (2 ^ a) = 1 :=
    (Nat.Coprime.pow_left a (by decide : Nat.Coprime 2 5)).symm.gcd_eq_one
  rw [pow_add, pow_add] at h
  have h3 : 2 ^ 4 ≡ 2 ^ d [MOD 5] := Nat.ModEq.cancel_left_of_coprime hcop h
  interval_cases d
  · left; omega
  · exfalso; norm_num [Nat.ModEq] at h3
  · exfalso; norm_num [Nat.ModEq] at h3
  · exfalso; norm_num [Nat.ModEq] at h3
  · right; omega

private def conjFix (N : Subgroup Γ) (hZc : ∀ z ∈ Z, ∀ g : Γ, g * z = z * g) (t : Γ) :
    Subgroup Γ where
  carrier := {x | x ∈ N ∧ t * x * t⁻¹ * x⁻¹ ∈ Z}
  one_mem' := ⟨N.one_mem, by simp⟩
  mul_mem' := by
    intro x y hx hy
    have hZn : Z.Normal :=
      Subgroup.normal_of_le_center (fun z hz => Subgroup.mem_center_iff.mpr (hZc z hz))
    refine ⟨N.mul_mem hx.1 hy.1, ?_⟩
    have hconj : x * (t * y * t⁻¹ * y⁻¹) * x⁻¹ ∈ Z := hZn.conj_mem _ hy.2 x
    have heq : t * (x * y) * t⁻¹ * (x * y)⁻¹ =
        (t * x * t⁻¹ * x⁻¹) * (x * (t * y * t⁻¹ * y⁻¹) * x⁻¹) := by group
    rw [heq]
    exact Z.mul_mem hx.2 hconj
  inv_mem' := by
    intro x hx
    have hZn : Z.Normal :=
      Subgroup.normal_of_le_center (fun z hz => Subgroup.mem_center_iff.mpr (hZc z hz))
    refine ⟨N.inv_mem hx.1, ?_⟩
    have hconj : x⁻¹ * (t * x * t⁻¹ * x⁻¹)⁻¹ * (x⁻¹)⁻¹ ∈ Z :=
      hZn.conj_mem _ (Z.inv_mem hx.2) x⁻¹
    have heq : t * x⁻¹ * t⁻¹ * (x⁻¹)⁻¹ =
        x⁻¹ * (t * x * t⁻¹ * x⁻¹)⁻¹ * (x⁻¹)⁻¹ := by group
    rw [heq]
    exact hconj

omit [Finite Γ] in
private lemma mem_conjFix (N : Subgroup Γ) (hZc : ∀ z ∈ Z, ∀ g : Γ, g * z = z * g)
    (t x : Γ) :
    x ∈ conjFix N hZc t ↔ x ∈ N ∧ t * x * t⁻¹ * x⁻¹ ∈ Z := Iff.rfl


theorem mem_of_orderOf_five_of_conj [N.Normal] (hZN : Z ≤ N)
    (hZc : ∀ z ∈ Z, ∀ g : Γ, g * z = z * g) (hZ2 : IsPGroup 2 Z)
    (hcard : Nat.card N = 16 * Nat.card Z) (hsq : ∀ x ∈ N, x * x ∈ Z)
    (hker : ∀ g : Γ, (∀ x ∈ N, g * x * g⁻¹ * x⁻¹ ∈ Z) → g ∈ N)
    {c : Γ} (hc : orderOf c = 5) {x : Γ} (hx : x ∈ N) (hcx : c * x * c⁻¹ * x⁻¹ ∈ Z) :
    x ∈ Z := by
  classical
  have _ : ∀ x ∈ N, x * x ∈ Z := hsq
  have hfactTwo : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨a, hZa⟩ := hZ2.exists_card_eq
  have hNcard : Nat.card N = 2 ^ (a + 4) := by
    calc Nat.card N = 16 * Nat.card Z := hcard
      _ = 2 ^ 4 * 2 ^ a := by rw [hZa]; norm_num
      _ = 2 ^ (a + 4) := by rw [← pow_add]; congr 1; omega
  have hw5 : (c * x * c⁻¹ * x⁻¹) ^ 5 = 1 := pow_five_eq_one_of_conj_mem hZc hc hcx
  have hw1 : c * x * c⁻¹ * x⁻¹ = 1 :=
    eq_one_of_mem_isPGroup_two_of_pow_five hZ2 hcx hw5
  have hcx' : c * x = x * c := by
    have h1 : c * x * c⁻¹ = x := by
      calc c * x * c⁻¹ = (c * x * c⁻¹ * x⁻¹) * x := by group
        _ = 1 * x := by rw [hw1]
        _ = x := by group
    calc c * x = (c * x * c⁻¹) * c := by group
      _ = x * c := by rw [h1]
  let C : Subgroup Γ := N ⊓ Subgroup.centralizer ({c} : Set Γ)
  have hZC : Z ≤ C := by
    intro z hz
    refine Subgroup.mem_inf.mpr ⟨hZN hz, ?_⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact (hZc z hz c).symm
  have hcN : c ∈ Subgroup.normalizer (N : Set Γ) := by
    rw [Subgroup.normalizer_eq_top N]
    exact Subgroup.mem_top c
  have hmod : Nat.card N ≡ Nat.card ↥C [MOD 5] :=
    card_modEq_five_inf_centralizer hc hcN
  have hCdvd : Nat.card C ∣ 2 ^ (a + 4) := by
    rw [← hNcard]
    exact Subgroup.card_dvd_of_le (inf_le_left : C ≤ N)
  obtain ⟨m, hmle, hm⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hCdvd
  have ham : a ≤ m := by
    have hle : 2 ^ a ≤ 2 ^ m := by
      rw [← hZa, ← hm]
      exact Subgroup.card_le_of_le hZC
    exact (Nat.pow_le_pow_iff_right (a := 2) (by norm_num : 1 < 2)).mp hle
  have hmod2 : 2 ^ (a + 4) ≡ 2 ^ m [MOD 5] := by
    rw [← hNcard, ← hm]
    exact hmod
  rcases pow_two_modEq_five ham hmle hmod2 with hm_a | hm_a4
  · have hZCeq : Z = C :=
      Subgroup.eq_of_le_of_card_ge (H := Z) (K := C) hZC (by rw [hm, hm_a, hZa])
    have hCZ : C = Z := hZCeq.symm
    have hxC : x ∈ C := by
      refine Subgroup.mem_inf.mpr ⟨hx, ?_⟩
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact hcx'.symm
    exact hCZ ▸ hxC
  · have hCN : C = N := by
      refine Subgroup.eq_of_le_of_card_ge (inf_le_left : C ≤ N) ?_
      rw [hm, hm_a4, hNcard]
    have hcNmem : c ∈ N := hker c (fun y hy => by
      have hyC : y ∈ C := hCN.symm ▸ hy
      have hycomm : y * c = c * y :=
        Subgroup.mem_centralizer_singleton_iff.mp (Subgroup.mem_inf.mp hyC).2
      rw [show c * y * c⁻¹ * y⁻¹ = 1 by
        calc c * y * c⁻¹ * y⁻¹ = (y * c) * c⁻¹ * y⁻¹ := by rw [hycomm]
          _ = 1 := by group]
      exact Z.one_mem)
    have hdvd : orderOf c ∣ Nat.card N := Subgroup.orderOf_dvd_natCard N hcNmem
    rw [hc, hNcard] at hdvd
    have : (5 : ℕ) ∣ 2 := Nat.Prime.dvd_of_dvd_pow Nat.prime_five hdvd
    norm_num at this

theorem mem_of_commute_of_orderOf_five [N.Normal] (hZN : Z ≤ N)
    (hZc : ∀ z ∈ Z, ∀ g : Γ, g * z = z * g) (hZ2 : IsPGroup 2 Z)
    (hcard : Nat.card N = 16 * Nat.card Z) (hsq : ∀ x ∈ N, x * x ∈ Z)
    (hker : ∀ g : Γ, (∀ x ∈ N, g * x * g⁻¹ * x⁻¹ ∈ Z) → g ∈ N)
    {c : Γ} (hc : orderOf c = 5) {t : Γ} (ht : ∃ k : ℕ, t ^ 2 ^ k = 1) (htc : t * c = c * t) :
    t ∈ Z := by
  classical
  have hfactTwo : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hZn : Z.Normal :=
    Subgroup.normal_of_le_center (fun z hz => Subgroup.mem_center_iff.mpr (hZc z hz))
  have hZnInst : Z.Normal := hZn
  obtain ⟨a, hZa⟩ := hZ2.exists_card_eq
  have hNcard : Nat.card N = 2 ^ (a + 4) := by
    calc Nat.card N = 16 * Nat.card Z := hcard
      _ = 2 ^ 4 * 2 ^ a := by rw [hZa]; norm_num
      _ = 2 ^ (a + 4) := by rw [← pow_add]; congr 1; omega
  have hN2 : IsPGroup 2 ↥N := IsPGroup.of_card hNcard
  let F : Subgroup Γ := conjFix N hZc t
  have hZF : Z ≤ F := by
    intro z hz
    rw [mem_conjFix N hZc t z]
    refine ⟨hZN hz, ?_⟩
    rw [show t * z * t⁻¹ * z⁻¹ = 1 by rw [hZc z hz t]; group]
    exact Z.one_mem
  have hFN : F ≤ N := fun y hy => ((mem_conjFix N hZc t y).mp hy).1
  have hconj_mem : ∀ {g y : Γ}, t * g = g * t → y ∈ F → g * y * g⁻¹ ∈ F := by
    intro g y hgt hy
    obtain ⟨hyN, hyZ⟩ := (mem_conjFix N hZc t y).mp hy
    rw [mem_conjFix N hZc t (g * y * g⁻¹)]
    refine ⟨Subgroup.Normal.conj_mem inferInstance y hyN g, ?_⟩
    have heq : t * (g * y * g⁻¹) * t⁻¹ * (g * y * g⁻¹)⁻¹ =
        g * (t * y * t⁻¹ * y⁻¹) * g⁻¹ := by
      have hginv : g⁻¹ * t⁻¹ = t⁻¹ * g⁻¹ := by
        rw [← mul_inv_rev, ← mul_inv_rev, hgt]
      calc t * (g * y * g⁻¹) * t⁻¹ * (g * y * g⁻¹)⁻¹
          = (t * g) * y * (g⁻¹ * t⁻¹) * (g * y⁻¹ * g⁻¹) := by group
        _ = (g * t) * y * (t⁻¹ * g⁻¹) * (g * y⁻¹ * g⁻¹) := by rw [hgt, hginv]
        _ = g * (t * y * t⁻¹ * y⁻¹) * g⁻¹ := by group
    rw [heq]
    exact Subgroup.Normal.conj_mem inferInstance _ hyZ g
  have hconj_mem_inv : ∀ {g y : Γ}, t * g = g * t → y ∈ F → g⁻¹ * y * g ∈ F := by
    intro g y hgt hy
    obtain ⟨hyN, hyZ⟩ := (mem_conjFix N hZc t y).mp hy
    rw [mem_conjFix N hZc t (g⁻¹ * y * g)]
    refine ⟨by simpa using Subgroup.Normal.conj_mem inferInstance y hyN g⁻¹, ?_⟩
    have heq : t * (g⁻¹ * y * g) * t⁻¹ * (g⁻¹ * y * g)⁻¹ =
        g⁻¹ * (t * y * t⁻¹ * y⁻¹) * g := by
      have h1 : t * g⁻¹ = g⁻¹ * t := by
        calc t * g⁻¹ = g⁻¹ * (g * t) * g⁻¹ := by group
          _ = g⁻¹ * (t * g) * g⁻¹ := by rw [hgt]
          _ = g⁻¹ * t := by group
      have h2 : g * t⁻¹ = t⁻¹ * g := by
        calc g * t⁻¹ = t⁻¹ * (t * g) * t⁻¹ := by group
          _ = t⁻¹ * (g * t) * t⁻¹ := by rw [hgt]
          _ = t⁻¹ * g := by group
      calc t * (g⁻¹ * y * g) * t⁻¹ * (g⁻¹ * y * g)⁻¹
          = (t * g⁻¹) * y * (g * t⁻¹) * (g⁻¹ * y⁻¹ * g) := by group
        _ = (g⁻¹ * t) * y * (t⁻¹ * g) * (g⁻¹ * y⁻¹ * g) := by rw [h1, h2]
        _ = g⁻¹ * (t * y * t⁻¹ * y⁻¹) * g := by group
    rw [heq]
    simpa using Subgroup.Normal.conj_mem inferInstance _ hyZ g⁻¹
  have hcF : c ∈ Subgroup.normalizer (F : Set Γ) := by
    rw [Subgroup.mem_normalizer_iff]
    intro y
    constructor
    · intro hy
      exact hconj_mem htc hy
    · intro hy
      have h := hconj_mem_inv htc hy
      have h' : c⁻¹ * (c * y * c⁻¹) * c = y := by group
      rwa [h'] at h
  have hFmod : Nat.card F ≡ Nat.card ↥(F ⊓ Subgroup.centralizer ({c} : Set Γ)) [MOD 5] :=
    card_modEq_five_inf_centralizer hc hcF
  have hFZ : F ⊓ Subgroup.centralizer ({c} : Set Γ) = Z := by
    apply le_antisymm
    · intro y hy
      obtain ⟨hyF, hyC⟩ := Subgroup.mem_inf.mp hy
      have hyN : y ∈ N := ((mem_conjFix N hZc t y).mp hyF).1
      have hycomm : y * c = c * y := Subgroup.mem_centralizer_singleton_iff.mp hyC
      exact mem_of_orderOf_five_of_conj hZN hZc hZ2 hcard hsq hker hc hyN (by
        rw [show c * y * c⁻¹ * y⁻¹ = 1 by rw [hycomm.symm]; group]
        exact Z.one_mem)
    · intro z hz
      exact Subgroup.mem_inf.mpr ⟨hZF hz, by
        rw [Subgroup.mem_centralizer_singleton_iff]
        exact (hZc z hz c).symm⟩
  have hFmodZ : Nat.card F ≡ Nat.card Z [MOD 5] := by
    rw [hFZ] at hFmod
    exact hFmod
  have hFdvd : Nat.card F ∣ 2 ^ (a + 4) := by
    rw [← hNcard]
    exact Subgroup.card_dvd_of_le hFN
  obtain ⟨m, hmle, hm⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hFdvd
  have ham : a ≤ m := by
    have hle : 2 ^ a ≤ 2 ^ m := by
      rw [← hZa, ← hm]
      exact Subgroup.card_le_of_le hZF
    exact (Nat.pow_le_pow_iff_right (a := 2) (by norm_num : 1 < 2)).mp hle
  have hmod2 : 2 ^ (a + 4) ≡ 2 ^ m [MOD 5] := by
    have hNm : 2 ^ (a + 4) ≡ 2 ^ a [MOD 5] := by
      have h1 : 2 ^ (a + 4) = 2 ^ a * 16 := by rw [pow_add]; norm_num
      rw [h1]
      have h3 : 2 ^ a * 16 ≡ 2 ^ a * 1 [MOD 5] :=
        Nat.ModEq.mul_left _ (by norm_num [Nat.ModEq] : (16 : ℕ) ≡ 1 [MOD 5])
      simpa using h3
    have hFm : 2 ^ m ≡ 2 ^ a [MOD 5] := by
      rw [← hm, ← hZa]
      exact hFmodZ
    exact hNm.trans hFm.symm
  have hA2 : IsPGroup 2 ↥(Subgroup.zpowers t) := by
    obtain ⟨k, hk⟩ := ht
    have hdvd : orderOf t ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one hk
    obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd
    have hAcard : Nat.card ↥(Subgroup.zpowers t) = 2 ^ j := by
      rw [Nat.card_zpowers, hj]
    exact IsPGroup.of_card hAcard
  have hlt : Z < N := by
    refine lt_of_le_of_ne hZN ?_
    intro hEq
    have hpos : 0 < Nat.card Z := Nat.card_pos
    have hcard_eq : Nat.card Z = Nat.card N := by rw [hEq]
    rw [hcard] at hcard_eq
    omega
  obtain ⟨r, hrN, hrZ, hrcomm⟩ :=
    CFSG.GroupTheory.exists_commutatorElement_mem_of_isPGroup (p := 2) (P := Subgroup.zpowers t)
      (Q := N) (K₀ := Z) hA2 hN2 hlt
      (Subgroup.le_normalizer_of_normal (H := Z) (K := N))
      (Subgroup.le_normalizer_of_normal (H := N) (K := Subgroup.zpowers t))
      (Subgroup.le_normalizer_of_normal (H := Z) (K := Subgroup.zpowers t))
  have hrF : r ∈ F := by
    rw [mem_conjFix N hZc t r]
    refine ⟨hrN, ?_⟩
    have h := hrcomm t (Subgroup.mem_zpowers t)
    rwa [commutatorElement_def] at h
  have hFneZ : F ≠ Z := by
    intro hEq
    exact hrZ (hEq ▸ hrF)
  rcases pow_two_modEq_five ham hmle hmod2 with hm_a | hm_a4
  · have hZCeq : Z = F :=
      Subgroup.eq_of_le_of_card_ge (H := Z) (K := F) hZF (by rw [hm, hm_a, hZa])
    exact absurd hZCeq.symm hFneZ
  · have hFNcard : Nat.card F = Nat.card N := by rw [hm, hm_a4, hNcard]
    have hFeqN : F = N :=
      Subgroup.eq_of_le_of_card_ge (H := F) (K := N) hFN (by rw [hFNcard])
    have htN : t ∈ N := hker t (fun y hy => by
      have hyF : y ∈ F := by rw [hFeqN]; exact hy
      exact ((mem_conjFix N hZc t y).mp hyF).2)
    exact mem_of_orderOf_five_of_conj hZN hZc hZ2 hcard hsq hker hc htN (by
      rw [show c * t * c⁻¹ * t⁻¹ = 1 by rw [htc.symm]; group]
      exact Z.one_mem)

theorem card_dvd_five_of_isPGroup [N.Normal] (hZN : Z ≤ N)
    (hZc : ∀ z ∈ Z, ∀ g : Γ, g * z = z * g) (hZ2 : IsPGroup 2 Z)
    (hcard : Nat.card N = 16 * Nat.card Z) (hsq : ∀ x ∈ N, x * x ∈ Z)
    (hker : ∀ g : Γ, (∀ x ∈ N, g * x * g⁻¹ * x⁻¹ ∈ Z) → g ∈ N)
    {R : Subgroup Γ} (hR : IsPGroup 5 R) : Nat.card R ∣ 5 := by
  classical
  have hfactTwo : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hfactFive : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  have hZn : Z.Normal :=
    Subgroup.normal_of_le_center (fun z hz => Subgroup.mem_center_iff.mpr (hZc z hz))
  have hZnInst : Z.Normal := hZn
  obtain ⟨a, hZa⟩ := hZ2.exists_card_eq
  let Z' : Subgroup ↥N := Z.subgroupOf N
  have hZ'card : Nat.card Z' = Nat.card Z :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hZN).toEquiv
  let X := ↥((Z' : Set ↥N)ᶜ)
  let Xact : MulAction ↥R X :=
    { smul := fun r x =>
        ⟨r • (x : ↥N), by
          intro hx
          have hxZ : ((r • (x : ↥N) : ↥N) : Γ) ∈ Z :=
            Subgroup.mem_subgroupOf.mp hx
          have hcoe : ((r • (x : ↥N) : ↥N) : Γ) = (r : Γ) * (x : Γ) * (r : Γ)⁻¹ :=
            Subgroup.conjMulDistribMulActionOfLeNormalizer_smul_coe R N r (x : ↥N)
          have hxmem : (x : Γ) ∈ Z := by
            have hconj := Subgroup.Normal.conj_mem hZn
              ((r : Γ) * (x : Γ) * (r : Γ)⁻¹) (hcoe ▸ hxZ) (r : Γ)⁻¹
            simpa [mul_assoc] using hconj
          exact x.2 (Subgroup.mem_subgroupOf.mpr hxmem)⟩
      one_smul := fun x => Subtype.ext (one_smul _ _)
      mul_smul := fun r s x => Subtype.ext (mul_smul _ _ _) }
  have hfree : ∀ x : X, MulAction.stabilizer ↥R x = ⊥ := by
    intro x
    rw [Subgroup.eq_bot_iff_forall]
    intro r hr
    by_contra hr1
    have hrx : r • x = x := MulAction.mem_stabilizer_iff.mp hr
    have hxcoe : ((r • (x : ↥N) : ↥N) : Γ) = (r : Γ) * (x : Γ) * (r : Γ)⁻¹ :=
      Subgroup.conjMulDistribMulActionOfLeNormalizer_smul_coe R N r (x : ↥N)
    have hxeq : (r : Γ) * (x : Γ) * (r : Γ)⁻¹ = (x : Γ) := by
      rw [← hxcoe]
      exact congrArg (fun y : ↥N => (y : Γ)) (congrArg Subtype.val hrx)
    have hcomm : Commute (r : Γ) (x : Γ) := by
      show (r : Γ) * (x : Γ) = (x : Γ) * (r : Γ)
      calc (r : Γ) * (x : Γ) = ((r : Γ) * (x : Γ) * (r : Γ)⁻¹) * (r : Γ) := by group
        _ = (x : Γ) * (r : Γ) := by rw [hxeq]
    obtain ⟨j, hj⟩ := hR.exists_orderOf_eq_pow r
    have hj0 : j ≠ 0 := by
      rintro rfl
      rw [pow_zero] at hj
      exact hr1 (orderOf_eq_one_iff.mp hj)
    have hordG : orderOf (r : Γ) = 5 ^ j := by
      rw [Subgroup.orderOf_coe, hj]
    obtain ⟨k, rfl⟩ : ∃ k, j = k + 1 := ⟨j - 1, by omega⟩
    have hdvd : 5 ^ k ∣ orderOf (r : Γ) := by
      rw [hordG, pow_succ]
      exact dvd_mul_right (5 ^ k) 5
    let r' : Γ := (r : Γ) ^ 5 ^ k
    have hr'ord : orderOf r' = 5 := by
      rw [show r' = (r : Γ) ^ 5 ^ k from rfl,
        orderOf_pow_of_dvd (x := (r : Γ)) (n := 5 ^ k) (by positivity : (5 : ℕ) ^ k ≠ 0)
          hdvd, hordG, pow_succ, Nat.mul_div_cancel_left 5 (by positivity : 0 < (5 : ℕ) ^ k)]
    have hr'comm : Commute r' (x : Γ) := by
      rw [show r' = (r : Γ) ^ 5 ^ k from rfl]
      exact hcomm.pow_left _
    have hmemZ : r' * (x : Γ) * r'⁻¹ * (x : Γ)⁻¹ ∈ Z := by
      have h := hr'comm.commutator_eq
      rw [commutatorElement_def] at h
      rw [h]
      exact Z.one_mem
    exact x.2 (Subgroup.mem_subgroupOf.mpr
      (mem_of_orderOf_five_of_conj hZN hZc hZ2 hcard hsq hker hr'ord (x : ↥N).2 hmemZ))
  have hXcard : Nat.card X = 15 * Nat.card Z := by
    have hXeq : Nat.card X = Nat.card ↥N - Nat.card Z' := by
      have hFinN : Fintype ↥N := Fintype.ofFinite ↥N
      have hFinZ' : Fintype Z' := Fintype.ofFinite Z'
      have hFinX : Fintype X := Fintype.ofFinite X
      rw [Nat.card_eq_fintype_card, Fintype.card_compl_set,
        Nat.card_eq_fintype_card, Nat.card_eq_fintype_card (α := Z')]
      rfl
    rw [hXeq, hZ'card]
    omega
  have hdvd : Nat.card ↥R ∣ Nat.card X := by
    let e := MulAction.selfEquivOrbitsQuotientProd (G := ↥R) (X := X) hfree
    have hXprod : Nat.card X =
        Nat.card (Quotient (MulAction.orbitRel ↥R X)) * Nat.card ↥R := by
      rw [Nat.card_congr e, Nat.card_prod]
    rw [hXprod]
    exact Nat.dvd_mul_left _ _
  obtain ⟨m, hm⟩ := hR.exists_card_eq
  have hdvd15 : 5 ^ m ∣ 15 := by
    have hdvdX : 5 ^ m ∣ Nat.card X := by rw [← hm]; exact hdvd
    rw [hXcard] at hdvdX
    have hcop : Nat.Coprime (5 ^ m) (Nat.card Z) := by
      rw [hZa]
      exact Nat.Coprime.pow_right a (Nat.Coprime.pow_left m (by decide : Nat.Coprime 5 2))
    exact Nat.Coprime.dvd_of_dvd_mul_right hcop hdvdX
  have hm1 : m ≤ 1 := by
    by_contra h
    have h2 : 2 ≤ m := by omega
    have hle : 5 ^ 2 ≤ 5 ^ m := Nat.pow_le_pow_right (by norm_num) h2
    have hdivle : 5 ^ m ≤ 15 := Nat.le_of_dvd (by norm_num) hdvd15
    norm_num at hle
    omega
  rw [hm]
  interval_cases m <;> norm_num

end CFSG.LocalAnalysis.UniquenessCase.UC22.Q35Natural
