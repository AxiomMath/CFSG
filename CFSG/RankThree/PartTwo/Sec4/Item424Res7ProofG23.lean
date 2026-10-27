module

public import CFSG.RankThree.PartTwo.Sec4.Item413CoverProofG2Cent
public import CFSG.RankThree.PartTwo.Sec4.Item424Res7ProofInvol
public import CFSG.RankThree.PartTwo.Sec6.Item611Res3ProofG2
public import CFSG.RankThree.PartTwo.Sec21.Item211Res5ProofG2Data

public section

namespace CFSG.RankThree.PartTwo.Sec4.Res417Five.TorusSep

open CFSG CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.HardMathSupport.Timmesfeld.LieRank CFSG.Quasithin.G2U

set_option maxRecDepth 100000 in
theorem torus_facts_two : Lta * LA 2 = LA 2 ^ 2 * Lta ∧ Ltb * LA 2 = LA 2 ^ 2 * Ltb := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem tAB_facts : Lta * Ltb * (Lta * Ltb) = 1 ∧ Lta * Ltb ≠ 1 := by
  decide +kernel

theorem word_eq_elt {i j k l : ℕ} (hi : i < 3) (hj : j < 3) (hk : k < 3) (hl : l < 3) :
    aX 0 ^ i * aX 1 ^ j * aX 2 ^ k * aX 3 ^ l = specA.elt ![(i : ZMod 3), j, k, l] := by
  rw [elt_four]
  simp [ZMod.val_natCast, Nat.mod_eq_of_lt hi, Nat.mod_eq_of_lt hj, Nat.mod_eq_of_lt hk,
    Nat.mod_eq_of_lt hl]

theorem word_inj {i j k l i' j' k' l' : ℕ} (hi : i < 3) (hj : j < 3) (hk : k < 3) (hl : l < 3)
    (hi' : i' < 3) (hj' : j' < 3) (hk' : k' < 3) (hl' : l' < 3)
    (h : aX 0 ^ i * aX 1 ^ j * aX 2 ^ k * aX 3 ^ l =
      aX 0 ^ i' * aX 1 ^ j' * aX 2 ^ k' * aX 3 ^ l') :
    i = i' ∧ j = j' ∧ k = k' ∧ l = l' := by
  rw [word_eq_elt hi hj hk hl, word_eq_elt hi' hj' hk' hl'] at h
  have h1 := specA.elt_injective h
  have h0 := congrArg ZMod.val (congrFun h1 0)
  have h1' := congrArg ZMod.val (congrFun h1 1)
  have h2 := congrArg ZMod.val (congrFun h1 2)
  have h3 := congrArg ZMod.val (congrFun h1 3)
  simp [ZMod.val_natCast, Nat.mod_eq_of_lt, hi, hj, hk, hl, hi', hj', hk', hl'] at h0 h1' h2 h3
  exact ⟨h0, h1', h2, h3⟩

theorem aX_pow (i : Fin 4) : aX i ^ 3 = 1 := specA.pow i

theorem aX_comm (i j : Fin 4) : aX i * aX j = aX j * aX i := specA.comm i j

theorem conj_eq_inv_of {M : Type*} [Group M] {S : Subgroup M} {t x : S} (h : t * x = x ^ 2 * t)
    (h3 : x ^ 3 = 1) : t * x * t⁻¹ = x⁻¹ := by
  rw [h, mul_inv_cancel_right, eq_inv_iff_mul_eq_one, ← pow_succ, h3]

theorem conj_eq_of {M : Type*} [Group M] {S : Subgroup M} {t x : S} (h : t * x = x * t) :
    t * x * t⁻¹ = x := by
  rw [h, mul_inv_cancel_right]

noncomputable abbrev tAB : RG := tA * tB

theorem torus_conj :
    tA * aX 0 * tA⁻¹ = (aX 0)⁻¹ ∧ tA * aX 1 * tA⁻¹ = (aX 1)⁻¹ ∧
      tA * aX 2 * tA⁻¹ = (aX 2)⁻¹ ∧ tA * aX 3 * tA⁻¹ = aX 3 ∧
    tB * aX 0 * tB⁻¹ = (aX 0)⁻¹ ∧ tB * aX 1 * tB⁻¹ = aX 1 ∧
      tB * aX 2 * tB⁻¹ = (aX 2)⁻¹ ∧ tB * aX 3 * tB⁻¹ = (aX 3)⁻¹ := by
  obtain ⟨⟨ta0, ta1, ta3⟩, ⟨tb0, tb1, tb3⟩⟩ := torus_facts
  obtain ⟨ta2, tb2⟩ := torus_facts_two
  have hsq : ∀ (s : RG) (S : M14) (i : Fin 4), valHom s = S → S * LA i = LA i ^ 2 * S →
      s * aX i = aX i ^ 2 * s := fun s S i hs h => valHom_injective (by
        rw [map_mul, map_mul, map_pow, valHom_aX, hs]
        exact h)
  have cm : ∀ (s : RG) (S : M14) (i : Fin 4), valHom s = S → S * LA i = LA i * S →
      s * aX i = aX i * s := fun s S i hs h => valHom_injective (by
        rw [map_mul, map_mul, valHom_aX, hs]
        exact h)
  exact ⟨conj_eq_inv_of (t := tA) (x := aX 0) (hsq _ _ 0 valHom_tA ta0) (aX_pow 0),
    conj_eq_inv_of (t := tA) (x := aX 1) (hsq _ _ 1 valHom_tA ta1) (aX_pow 1),
    conj_eq_inv_of (t := tA) (x := aX 2) (hsq _ _ 2 valHom_tA ta2) (aX_pow 2),
    conj_eq_of (t := tA) (x := aX 3) (cm _ _ 3 valHom_tA ta3),
    conj_eq_inv_of (t := tB) (x := aX 0) (hsq _ _ 0 valHom_tB tb0) (aX_pow 0),
    conj_eq_of (t := tB) (x := aX 1) (cm _ _ 1 valHom_tB tb1),
    conj_eq_inv_of (t := tB) (x := aX 2) (hsq _ _ 2 valHom_tB tb2) (aX_pow 2),
    conj_eq_inv_of (t := tB) (x := aX 3) (hsq _ _ 3 valHom_tB tb3) (aX_pow 3)⟩

theorem tAB_conj :
    tAB * aX 0 * tAB⁻¹ = aX 0 ∧ tAB * aX 2 * tAB⁻¹ = aX 2 ∧
      tAB * aX 1 * tAB⁻¹ = (aX 1)⁻¹ ∧ tAB * aX 3 * tAB⁻¹ = (aX 3)⁻¹ := by
  obtain ⟨a0, a1, a2, a3, b0, b1, b2, b3⟩ := torus_conj
  have e : ∀ x : RG, tAB * x * tAB⁻¹ = tA * (tB * x * tB⁻¹) * tA⁻¹ := fun x => by
    simp only [tAB]
    group
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [e, b0, show tA * (aX 0)⁻¹ * tA⁻¹ = (tA * aX 0 * tA⁻¹)⁻¹ by group, a0, inv_inv]
  · rw [e, b2, show tA * (aX 2)⁻¹ * tA⁻¹ = (tA * aX 2 * tA⁻¹)⁻¹ by group, a2, inv_inv]
  · rw [e, b1, a1]
  · rw [e, b3, show tA * (aX 3)⁻¹ * tA⁻¹ = (tA * aX 3 * tA⁻¹)⁻¹ by group, a3]

theorem orderOf_tAB : orderOf tAB = 2 := by
  obtain ⟨h1, h2⟩ := tAB_facts
  have hv : valHom tAB = Lta * Ltb := by rw [map_mul, valHom_tA, valHom_tB]
  refine orderOf_eq_prime ?_ ?_
  · exact valHom_injective (by rw [map_pow, hv, sq, map_one]; exact h1)
  · intro h
    apply h2
    rw [← hv, h, map_one]

noncomputable abbrev F₀ : Subgroup RG := Subgroup.closure {aX 0, aX 2}

noncomputable abbrev R₀ : Subgroup RG := Subgroup.closure {aX 3, aX 1}

theorem exists_pow_mul_pow_of_mem {M : Type*} [Group M] {S : Subgroup M} {a b : S}
    (ha : a ^ 3 = 1) (hb : b ^ 3 = 1) (hab : a * b = b * a) {x : S}
    (hx : x ∈ Subgroup.closure ({a, b} : Set S)) :
    ∃ i j : ℕ, i < 3 ∧ j < 3 ∧ x = a ^ i * b ^ j := by
  induction hx using Subgroup.closure_induction with
  | mem y hy =>
    rcases hy with rfl | rfl
    · exact ⟨1, 0, by norm_num, by norm_num, by simp⟩
    · exact ⟨0, 1, by norm_num, by norm_num, by simp⟩
  | one => exact ⟨0, 0, by norm_num, by norm_num, by simp⟩
  | mul y z _ _ hy hz =>
    obtain ⟨i, j, -, -, rfl⟩ := hy
    obtain ⟨i', j', -, -, rfl⟩ := hz
    have hc : Commute a b := hab
    refine ⟨(i + i') % 3, (j + j') % 3, Nat.mod_lt _ (by norm_num), Nat.mod_lt _ (by norm_num), ?_⟩
    rw [← pow_eq_pow_mod _ ha, ← pow_eq_pow_mod _ hb, pow_add, pow_add]
    calc a ^ i * b ^ j * (a ^ i' * b ^ j') = a ^ i * (b ^ j * a ^ i') * b ^ j' := by group
      _ = a ^ i * (a ^ i' * b ^ j) * b ^ j' := by rw [(hc.pow_pow i' j).eq]
      _ = a ^ i * a ^ i' * (b ^ j * b ^ j') := by group
  | inv y _ hy =>
    obtain ⟨i, j, -, -, rfl⟩ := hy
    have hc : Commute a b := hab
    refine ⟨(2 * i) % 3, (2 * j) % 3, Nat.mod_lt _ (by norm_num), Nat.mod_lt _ (by norm_num), ?_⟩
    have h1 : ∀ (c : S) (n : ℕ), c ^ 3 = 1 → (c ^ n)⁻¹ = c ^ (2 * n) := fun c n hc3 =>
      inv_eq_of_mul_eq_one_right (by
        rw [← pow_add, show n + 2 * n = 3 * n by ring, pow_mul, hc3, one_pow])
    rw [← pow_eq_pow_mod _ ha, ← pow_eq_pow_mod _ hb, mul_inv_rev,
      (hc.pow_pow i j).symm.inv_inv.eq, h1 a i ha, h1 b j hb]

theorem aX_indep :
    aX 0 ≠ 1 ∧ aX 2 ∉ Subgroup.zpowers (aX 0) ∧ aX 3 ≠ 1 ∧ aX 1 ∉ Subgroup.zpowers (aX 3) := by
  have w : ∀ {i j k l i' j' k' l' : ℕ}, i < 3 → j < 3 → k < 3 → l < 3 → i' < 3 → j' < 3 →
      k' < 3 → l' < 3 → (i, j, k, l) ≠ (i', j', k', l') →
      aX 0 ^ i * aX 1 ^ j * aX 2 ^ k * aX 3 ^ l ≠
        aX 0 ^ i' * aX 1 ^ j' * aX 2 ^ k' * aX 3 ^ l' := by
    intro i j k l i' j' k' l' hi hj hk hl hi' hj' hk' hl' hne h
    obtain ⟨e1, e2, e3, e4⟩ := word_inj hi hj hk hl hi' hj' hk' hl' h
    exact hne (by rw [e1, e2, e3, e4])
  have n0 : aX 0 ≠ 1 := by
    have := w (i := 1) (j := 0) (k := 0) (l := 0) (i' := 0) (j' := 0) (k' := 0) (l' := 0)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by decide)
    simpa using this
  have n3 : aX 3 ≠ 1 := by
    have := w (i := 0) (j := 0) (k := 0) (l := 1) (i' := 0) (j' := 0) (k' := 0) (l' := 0)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by decide)
    simpa using this
  refine ⟨n0, CFSG.RankThree.Asc83Table.not_mem_zpowers_of_ne (x := aX 0) (y := aX 2) (aX_pow 0)
    ?_ ?_ ?_, n3,
    CFSG.RankThree.Asc83Table.not_mem_zpowers_of_ne (x := aX 3) (y := aX 1) (aX_pow 3) ?_ ?_ ?_⟩
  · have := w (i := 0) (j := 0) (k := 1) (l := 0) (i' := 0) (j' := 0) (k' := 0) (l' := 0)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by decide)
    simpa using this
  · have := w (i := 0) (j := 0) (k := 1) (l := 0) (i' := 1) (j' := 0) (k' := 0) (l' := 0)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by decide)
    simpa using this
  · have := w (i := 0) (j := 0) (k := 1) (l := 0) (i' := 2) (j' := 0) (k' := 0) (l' := 0)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by decide)
    simpa using this
  · have := w (i := 0) (j := 1) (k := 0) (l := 0) (i' := 0) (j' := 0) (k' := 0) (l' := 0)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by decide)
    simpa using this
  · have := w (i := 0) (j := 1) (k := 0) (l := 0) (i' := 0) (j' := 0) (k' := 0) (l' := 1)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by decide)
    simpa using this
  · have := w (i := 0) (j := 1) (k := 0) (l := 0) (i' := 0) (j' := 0) (k' := 0) (l' := 2)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by decide)
    simpa using this

theorem card_F₀ : Nat.card F₀ = 9 :=
  CFSG.RankThree.Asc83Table.card_closure_pair_eq_nine (x := aX 0) (y := aX 2) (aX_pow 0)
    (aX_pow 2) (aX_comm 0 2) aX_indep.1 aX_indep.2.1

theorem card_R₀ : Nat.card R₀ = 9 :=
  CFSG.RankThree.Asc83Table.card_closure_pair_eq_nine (x := aX 3) (y := aX 1) (aX_pow 3)
    (aX_pow 1) (aX_comm 3 1) aX_indep.2.2.1 aX_indep.2.2.2

theorem pow_mul_pow_comm {M : Type*} [Group M] {S : Subgroup M} {a b : S} (h : a * b = b * a)
    (m n : ℕ) : a ^ m * b ^ n = b ^ n * a ^ m :=
  (Commute.pow_pow (show Commute a b from h) m n).eq

theorem pow_three_of_mem_pair {M : Type*} [Group M] {S : Subgroup M} {a b : S} (ha : a ^ 3 = 1)
    (hb : b ^ 3 = 1) (hab : a * b = b * a) {x : S}
    (hx : x ∈ Subgroup.closure ({a, b} : Set S)) : x ^ 3 = 1 := by
  obtain ⟨i, k, -, -, rfl⟩ := exists_pow_mul_pow_of_mem ha hb hab hx
  rw [(Commute.pow_pow (show Commute a b from hab) i k).mul_pow, ← pow_mul, ← pow_mul,
    mul_comm i, mul_comm k, pow_mul, pow_mul, ha, hb, one_pow, one_pow, one_mul]

theorem R₀_inf_F₀ : R₀ ⊓ F₀ = ⊥ := by
  rw [Subgroup.eq_bot_iff_forall]
  rintro x ⟨hxR, hxF⟩
  obtain ⟨l, j, hl, hj, rfl⟩ := exists_pow_mul_pow_of_mem (a := aX 3) (b := aX 1) (aX_pow 3)
    (aX_pow 1) (aX_comm 3 1) hxR
  obtain ⟨i, k, hi, hk, hx⟩ := exists_pow_mul_pow_of_mem (a := aX 0) (b := aX 2) (aX_pow 0)
    (aX_pow 2) (aX_comm 0 2) hxF
  have h : aX 0 ^ 0 * aX 1 ^ j * aX 2 ^ 0 * aX 3 ^ l =
      aX 0 ^ i * aX 1 ^ 0 * aX 2 ^ k * aX 3 ^ 0 := by
    simp only [pow_zero, one_mul, mul_one]
    rw [← hx, pow_mul_pow_comm (a := aX 3) (b := aX 1) (aX_comm 3 1) l j]
  obtain ⟨-, e2, -, e4⟩ := word_inj (by norm_num) hj (by norm_num) hl hi (by norm_num) hk
    (by norm_num) h
  rw [e2, e4, pow_zero, pow_zero, one_mul]

section Sylow

open CFSG.RankThree.PartTwo.Sec21.Item211Res5Proof in
theorem exists_conj_of_le_centralizer_z {F₁ F₂ : Subgroup (adjointGroup .G2 (ZMod 3))}
    (h₁ : F₁ ≤ Subgroup.centralizer ({CFSG.LieType.HighestRoot.g2z} : Set _))
    (h₂ : F₂ ≤ Subgroup.centralizer ({CFSG.LieType.HighestRoot.g2z} : Set _))
    (he₁ : ∀ x ∈ F₁, x ^ 3 = 1) (he₂ : ∀ x ∈ F₂, x ^ 3 = 1) (hc₁ : Nat.card F₁ = 9)
    (hc₂ : Nat.card F₂ = 9) :
    ∃ w : adjointGroup .G2 (ZMod 3), ∀ x ∈ F₂, w * x * w⁻¹ ∈ F₁ := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hK : ringChar (ZMod 3) ≠ 2 := by rw [ZMod.ringChar_zmod_n]; norm_num
  have hB := blockPair_g2 (K := ZMod 3) hK
  set Φ := MonoidHom.noncommCoprod (g2RhoA (ZMod 3)) (g2RhoV (ZMod 3))
    (fun a b => g2RhoA_comm a b) with hΦ
  set R := Φ.range with hR
  have hle : ∀ {F : Subgroup (adjointGroup .G2 (ZMod 3))},
      F ≤ Subgroup.centralizer ({CFSG.LieType.HighestRoot.g2z} : Set _) →
      (∀ x ∈ F, x ^ 3 = 1) → F ≤ R := by
    intro F hF he x hx
    obtain ⟨a, b, hab⟩ := hB.decomp x (Subgroup.mem_centralizer_singleton_iff.mp (hF hx))
      (he x hx)
    exact ⟨(a, b), by rw [hab]; rfl⟩
  have hR₁ := hle h₁ he₁
  have hR₂ := hle h₂ he₂
  have hRdvd : Nat.card R ∣ 576 := by
    have h1 := Subgroup.card_dvd_of_surjective Φ.rangeRestrict_surjective
    rw [Nat.card_prod, CFSG.SL2MinimalFaithful.card_specialLinearGroup_fin_two,
      Nat.card_zmod] at h1
    exact h1
  have hcard : ∀ {F : Subgroup (adjointGroup .G2 (ZMod 3))}, F ≤ R →
      Nat.card (F.subgroupOf R) = Nat.card F := fun hF =>
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hF).toEquiv
  have h9 : 9 ∣ Nat.card R := by
    rw [← hc₁, ← hcard hR₁]
    exact Subgroup.card_subgroup_dvd_card _
  have hfact : (Nat.card R).factorization 3 = 2 := by
    have hR0 : Nat.card R ≠ 0 := Nat.card_pos.ne'
    have h2 : 2 ≤ (Nat.card R).factorization 3 :=
      (Nat.prime_three.pow_dvd_iff_le_factorization hR0).mp (by simpa using h9)
    have h3 : ¬ 3 ≤ (Nat.card R).factorization 3 := by
      intro h
      have h27 := (Nat.prime_three.pow_dvd_iff_le_factorization hR0).mpr h
      have := h27.trans hRdvd
      norm_num at this
    omega
  have hS : ∀ {F : Subgroup (adjointGroup .G2 (ZMod 3))}, F ≤ R → Nat.card F = 9 →
      Nat.card (F.subgroupOf R) = 3 ^ (Nat.card R).factorization 3 := fun hF h9' => by
    rw [hcard hF, h9', hfact]
    norm_num
  set S₁ := Sylow.ofCard (F₁.subgroupOf R) (hS hR₁ hc₁)
  set S₂ := Sylow.ofCard (F₂.subgroupOf R) (hS hR₂ hc₂)
  obtain ⟨w, hw⟩ := MulAction.exists_smul_eq R S₂ S₁
  refine ⟨w, fun x hx => ?_⟩
  have hxR : x ∈ R := hR₂ hx
  have hmem : (⟨x, hxR⟩ : R) ∈ (S₂ : Subgroup R) := Subgroup.mem_subgroupOf.mpr hx
  have h1 : w * ⟨x, hxR⟩ * w⁻¹ ∈ (S₁ : Subgroup R) := by
    rw [← hw, Sylow.coe_subgroup_smul]
    exact ⟨⟨x, hxR⟩, hmem, rfl⟩
  exact Subgroup.mem_subgroupOf.mp h1

end Sylow

section Gen

variable {M : Type*} [Group M] {S : Subgroup M}

theorem comm_of_mem_pair {y a b x : S} (ha : y * a = a * y) (hb : y * b = b * y)
    (hx : x ∈ Subgroup.closure ({a, b} : Set S)) : y * x = x * y := by
  have hle : Subgroup.closure ({a, b} : Set S) ≤ Subgroup.centralizer ({y} : Set S) := by
    rw [Subgroup.closure_le]
    rintro _ (rfl | rfl)
    · exact Subgroup.mem_centralizer_singleton_iff.mpr ha.symm
    · exact Subgroup.mem_centralizer_singleton_iff.mpr hb.symm
  exact (Subgroup.mem_centralizer_singleton_iff.mp (hle hx)).symm

theorem comm_of_conj_eq {y x : S} (h : y * x * y⁻¹ = x) : y * x = x * y := by
  calc y * x = (y * x * y⁻¹) * y := by group
    _ = x * y := by rw [h]

theorem torusSep_of_iso {Y : Type} [Group Y] (Ψ : Y ≃* S) {F : Subgroup Y} (u : Fin 4 → S)
    (τa τb : S) (hcomm : ∀ i j, u i * u j = u j * u i) (hpow : ∀ i, u i ^ 3 = 1)
    (h0 : (τa * τb) * u 0 * (τa * τb)⁻¹ = u 0) (h2 : (τa * τb) * u 2 * (τa * τb)⁻¹ = u 2)
    (h1 : (τa * τb) * u 1 * (τa * τb)⁻¹ = (u 1)⁻¹) (h3 : (τa * τb) * u 3 * (τa * τb)⁻¹ = (u 3)⁻¹)
    (ha3 : τa * u 3 * τa⁻¹ = u 3) (ha1 : τa * u 1 * τa⁻¹ = (u 1)⁻¹)
    (hcardR : Nat.card (Subgroup.closure ({u 3, u 1} : Set S)) = 9)
    (hinter : Subgroup.closure ({u 3, u 1} : Set S) ⊓ Subgroup.closure ({u 0, u 2} : Set S) = ⊥)
    (hΨF : ∀ y : Y, y ∈ F ↔ Ψ y ∈ Subgroup.closure ({u 0, u 2} : Set S)) :
    ∃ r₁ r₂ h h' : Y, r₁ * r₂ = r₂ * r₁ ∧ r₁ ^ 3 = 1 ∧ r₂ ^ 3 = 1 ∧
      Nat.card (Subgroup.closure ({r₁, r₂} : Set Y)) = 9 ∧
      Subgroup.closure ({r₁, r₂} : Set Y) ⊓ F = ⊥ ∧
      (∀ f ∈ F, f * r₁ = r₁ * f ∧ f * r₂ = r₂ * f) ∧
      (∀ f ∈ F, h * f * h⁻¹ = f) ∧ h * r₁ * h⁻¹ = r₁⁻¹ ∧ h * r₂ * h⁻¹ = r₂⁻¹ ∧
      h' * r₁ * h'⁻¹ = r₁ ∧ h' * r₂ * h'⁻¹ = r₂⁻¹ := by
  have hsymm : ∀ v w : S, Ψ.symm v * Ψ.symm w * (Ψ.symm v)⁻¹ = Ψ.symm (v * w * v⁻¹) :=
    fun v w => by rw [map_mul, map_mul, map_inv]
  have hcl : Subgroup.closure ({Ψ.symm (u 3), Ψ.symm (u 1)} : Set Y) =
      (Subgroup.closure ({u 3, u 1} : Set S)).map Ψ.symm.toMonoidHom := by
    rw [MonoidHom.map_closure, Set.image_pair]
    rfl
  have hpre : ∀ f ∈ F, Ψ f ∈ Subgroup.closure ({u 0, u 2} : Set S) := fun f hf => (hΨF f).mp hf
  refine ⟨Ψ.symm (u 3), Ψ.symm (u 1), Ψ.symm (τa * τb), Ψ.symm τa, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_⟩
  · rw [← map_mul, ← map_mul, hcomm]
  · rw [← map_pow, hpow, map_one]
  · rw [← map_pow, hpow, map_one]
  · rw [hcl, Subgroup.card_map_of_injective Ψ.symm.injective, hcardR]
  · rw [Subgroup.eq_bot_iff_forall]
    rintro x ⟨hxR, hxF⟩
    rw [hcl] at hxR
    obtain ⟨x', hx', rfl⟩ := hxR
    have hx'F : x' ∈ Subgroup.closure ({u 0, u 2} : Set S) := by
      have h := hpre _ hxF
      change Ψ (Ψ.symm x') ∈ _ at h
      rwa [MulEquiv.apply_symm_apply] at h
    have h1' : x' ∈ Subgroup.closure ({u 3, u 1} : Set S) ⊓
        Subgroup.closure ({u 0, u 2} : Set S) := ⟨hx', hx'F⟩
    rw [hinter, Subgroup.mem_bot] at h1'
    change Ψ.symm x' = 1
    rw [h1', map_one]
  · intro f hf
    have hfF := hpre f hf
    have c3 : u 3 * Ψ f = Ψ f * u 3 := comm_of_mem_pair (hcomm 3 0) (hcomm 3 2) hfF
    have c1 : u 1 * Ψ f = Ψ f * u 1 := comm_of_mem_pair (hcomm 1 0) (hcomm 1 2) hfF
    constructor
    · apply Ψ.injective
      rw [map_mul, map_mul, MulEquiv.apply_symm_apply, c3]
    · apply Ψ.injective
      rw [map_mul, map_mul, MulEquiv.apply_symm_apply, c1]
  · intro f hf
    have hc : (τa * τb) * Ψ f = Ψ f * (τa * τb) :=
      comm_of_mem_pair (comm_of_conj_eq h0) (comm_of_conj_eq h2) (hpre f hf)
    apply Ψ.injective
    rw [map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply, hc, mul_inv_cancel_right]
  · rw [hsymm, h3, map_inv]
  · rw [hsymm, h1, map_inv]
  · rw [hsymm, ha3]
  · rw [hsymm, ha1, map_inv]

end Gen

section Main

theorem noFour_g23 {Y : Type} [Group Y] [Finite Y] (hY : ChevalleyExceptionalModel Y .G2 3 1) :
    ∀ x : Y, x ≠ 1 → x ^ 3 = 1 → ∀ u v : Y, u * u = 1 → v * v = 1 → u * v = v * u →
      x * u = u * x → x * v = v * x → u = 1 ∨ v = 1 ∨ u = v := by
  classical
  intro x hx1 hx3 u v hu hv huv hxu hxv
  by_contra hne
  push Not at hne
  obtain ⟨hu1, hv1, huv'⟩ := hne
  set V := Subgroup.closure ({u, v} : Set Y) with hV
  have hpair : ({u, v} : Set Y).Pairwise Commute := by
    rintro a (rfl | rfl) b (rfl | rfl) -
    · exact Commute.refl _
    · exact huv
    · exact huv.symm
    · exact Commute.refl _
  have hVc := Subgroup.isMulCommutative_closure hpair
  have hVe : CFSG.Assembly.IsElemAbelian 2 V := by
    refine ⟨hVc, fun y hy => ?_⟩
    induction hy using Subgroup.closure_induction with
    | mem y hy =>
      rcases hy with rfl | rfl
      · rw [sq, hu]
      · rw [sq, hv]
    | one => exact one_pow 2
    | mul y z hy hz ihy ihz =>
      have hyz : Commute y z := congrArg Subtype.val (hVc.is_comm.comm ⟨y, hy⟩ ⟨z, hz⟩)
      rw [hyz.mul_pow, ihy, ihz, one_mul]
    | inv y _ ihy => rw [inv_pow, ihy, inv_one]
  have hxV : ∀ w ∈ V, x * w = w * x := by
    have hle : V ≤ Subgroup.centralizer ({x} : Set Y) := by
      rw [Subgroup.closure_le]
      rintro _ (rfl | rfl)
      · exact Subgroup.mem_centralizer_singleton_iff.mpr hxu.symm
      · exact Subgroup.mem_centralizer_singleton_iff.mpr hxv.symm
    exact fun w hw => (Subgroup.mem_centralizer_singleton_iff.mp (hle hw)).symm
  have hcard := CFSG.RankThree.PartTwo.Sec6.kS611G2Cent_holds Y hY x hx1 hx3 V hVe hxV
  have : Fintype V := Fintype.ofFinite V
  have huV : u ∈ V := Subgroup.subset_closure (by simp)
  have hvV : v ∈ V := Subgroup.subset_closure (by simp)
  have h3 : ({⟨1, V.one_mem⟩, ⟨u, huV⟩, ⟨v, hvV⟩} : Finset V).card = 3 := by
    refine Finset.card_eq_three.mpr ⟨_, _, _, ?_, ?_, ?_, rfl⟩
    · exact fun h => hu1 (congrArg Subtype.val h).symm
    · exact fun h => hv1 (congrArg Subtype.val h).symm
    · exact fun h => huv' (congrArg Subtype.val h)
  have h4 := Finset.card_le_univ ({⟨1, V.one_mem⟩, ⟨u, huV⟩, ⟨v, hvV⟩} : Finset V)
  rw [h3, Fintype.card_eq_nat_card] at h4
  omega

theorem nonempty_mulEquiv_g23 {Y : Type} [Group Y] (hY : ChevalleyExceptionalModel Y .G2 3 1) :
    Nonempty (Y ≃* adjointGroup .G2 (ZMod 3)) := by
  obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := hY
  have f : K ≃+* ZMod 3 :=
    CFSG.ClassicalInvolution.Upgrade.fieldIsoOfCard (by rw [hK, Nat.card_zmod]; norm_num)
  have hinj := baseChangeGL_injective (τ := .G2) (f : K →+* ZMod 3)
  exact ⟨(e.trans ((QuotientGroup.quotientMulEquivOfEq
    (center_adjointGroup_eq_bot (τ := .G2) (K := K))).trans QuotientGroup.quotientBot)).trans
    (((adjointGroup .G2 K).equivMapOfInjective _ hinj).trans
      (MulEquiv.subgroupCongr (map_baseChangeGL_adjointGroup_eq_of_ringEquiv f)))⟩

section ConjGen

variable {M : Type*} [Group M] {S : Subgroup M}

theorem exists_iso_of_model {Y : Type} [Group Y] [Finite Y]
    (hY : ChevalleyExceptionalModel Y .G2 3 1) {F T : Subgroup Y}
    (hFe : CFSG.Assembly.IsElemAbelian 3 F) (hF9 : Nat.card F = 9) (hT2 : IsPGroup 2 T)
    (hFT : F ≤ Subgroup.normalizer (T : Set Y)) (hTF : ¬ T ≤ Subgroup.centralizer (F : Set Y))
    (θ : adjointGroup .G2 (ZMod 3) ≃* S) {u₀ u₂ τ : S} (hu₀ : u₀ ^ 3 = 1) (hu₂ : u₂ ^ 3 = 1)
    (hu : u₀ * u₂ = u₂ * u₀) (hτ : orderOf τ = 2) (hτ₀ : τ * u₀ = u₀ * τ)
    (hτ₂ : τ * u₂ = u₂ * τ) (hcard : Nat.card (Subgroup.closure ({u₀, u₂} : Set S)) = 9) :
    ∃ Ψ : Y ≃* S, ∀ y : Y, y ∈ F ↔ Ψ y ∈ Subgroup.closure ({u₀, u₂} : Set S) := by
  obtain ⟨e⟩ := nonempty_mulEquiv_g23 hY
  have hK : ringChar (ZMod 3) ≠ 2 := by rw [ZMod.ringChar_zmod_n]; norm_num
  set F₀' := Subgroup.closure ({u₀, u₂} : Set S) with hF₀'
  have hT1 : T ≠ ⊥ := by
    rintro rfl
    exact hTF bot_le
  obtain ⟨t, ht1, ht2, hFt⟩ := exists_involution_centralized (noFour_g23 hY) hFe hF9 hT2 hT1 hFT
  have hot : orderOf (e t) = 2 := by
    refine orderOf_eq_prime ?_ ?_
    · rw [← map_pow, sq, ht2, map_one]
    · intro h
      exact ht1 (e.injective (h.trans (map_one e).symm))
  obtain ⟨a, ha⟩ := isConj_iff.mp (CFSG.LieType.HighestRoot.g2_isConj_g2z hK hot)
  have hot₀ : orderOf (θ.symm τ) = 2 := by
    rw [MulEquiv.orderOf_eq]
    exact hτ
  obtain ⟨b, hb⟩ := isConj_iff.mp (CFSG.LieType.HighestRoot.g2_isConj_g2z hK hot₀)
  set ψ₁ : Y ≃* adjointGroup .G2 (ZMod 3) := e.trans (MulAut.conj a) with hψ₁
  set ψ₂ : S ≃* adjointGroup .G2 (ZMod 3) := θ.symm.trans (MulAut.conj b) with hψ₂
  have hψ₁t : ψ₁ t = CFSG.LieType.HighestRoot.g2z := ha
  have hψ₂h : ψ₂ τ = CFSG.LieType.HighestRoot.g2z := hb
  set F₁ := F.map ψ₁.toMonoidHom with hF₁
  set F₂ := F₀'.map ψ₂.toMonoidHom with hF₂
  have hF₁z : F₁ ≤ Subgroup.centralizer
      ({CFSG.LieType.HighestRoot.g2z} : Set (adjointGroup .G2 (ZMod 3))) := by
    rintro _ ⟨f, hf, rfl⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    change ψ₁ f * _ = _ * ψ₁ f
    rw [← hψ₁t, ← map_mul, ← map_mul, (hFt f hf)]
  have hF₂z : F₂ ≤ Subgroup.centralizer
      ({CFSG.LieType.HighestRoot.g2z} : Set (adjointGroup .G2 (ZMod 3))) := by
    rintro _ ⟨x, hx, rfl⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    change ψ₂ x * _ = _ * ψ₂ x
    have hc : τ * x = x * τ := comm_of_mem_pair hτ₀ hτ₂ hx
    rw [← hψ₂h, ← map_mul, ← map_mul, hc]
  have he₁ : ∀ x ∈ F₁, x ^ 3 = 1 := by
    rintro _ ⟨f, hf, rfl⟩
    change ψ₁ f ^ 3 = 1
    rw [← map_pow, hFe.2 f hf, map_one]
  have he₂ : ∀ x ∈ F₂, x ^ 3 = 1 := by
    rintro _ ⟨x, hx, rfl⟩
    change ψ₂ x ^ 3 = 1
    rw [← map_pow, pow_three_of_mem_pair hu₀ hu₂ hu hx, map_one]
  have hc₁ : Nat.card F₁ = 9 := by
    rw [hF₁, Subgroup.card_map_of_injective ψ₁.injective, hF9]
  have hc₂ : Nat.card F₂ = 9 := by
    rw [hF₂, Subgroup.card_map_of_injective ψ₂.injective, hcard]
  obtain ⟨w, hw⟩ := exists_conj_of_le_centralizer_z hF₁z hF₂z he₁ he₂ hc₁ hc₂
  obtain ⟨φ, hφ⟩ : ∃ φ : S ≃* adjointGroup .G2 (ZMod 3), ∀ x, φ x = (MulAut.conj w) (ψ₂ x) :=
    ⟨ψ₂.trans (MulAut.conj w), fun x => rfl⟩
  refine ⟨ψ₁.trans φ.symm, fun y => ?_⟩
  have hΨy : (ψ₁.trans φ.symm) y = φ.symm (ψ₁ y) := rfl
  rw [hΨy]
  have hmap : F₂.map (MulAut.conj w).toMonoidHom = F₁ := by
    apply Subgroup.eq_of_le_of_card_ge
    · rintro _ ⟨x, hx, rfl⟩
      exact hw x hx
    · rw [hc₁, Subgroup.card_map_of_injective (MulAut.conj w).injective, hc₂]
  constructor
  · intro hy
    have h1 : ψ₁ y ∈ F₁ := ⟨y, hy, rfl⟩
    rw [← hmap] at h1
    obtain ⟨_, ⟨x, hx, rfl⟩, hxy⟩ := h1
    have hx' : φ x = ψ₁ y := by
      rw [hφ]
      exact hxy
    rw [← hx', MulEquiv.symm_apply_apply]
    exact hx
  · intro hy
    have h1 : ψ₁ y ∈ F₁ := by
      rw [← hmap]
      refine ⟨ψ₂ (φ.symm (ψ₁ y)), ⟨φ.symm (ψ₁ y), hy, rfl⟩, ?_⟩
      change (MulAut.conj w) (ψ₂ (φ.symm (ψ₁ y))) = ψ₁ y
      rw [← hφ, MulEquiv.apply_symm_apply]
    obtain ⟨y', hy', hyy⟩ := h1
    rw [← ψ₁.injective hyy]
    exact hy'

end ConjGen

theorem k417G2TorusSep_holds : K417G2TorusSep := by
  intro Y _ _ hY F T hFe hF9 hT2 hFT hTF
  obtain ⟨a0, a2, a1, a3⟩ := tAB_conj
  obtain ⟨-, b1, -, b3, -⟩ := torus_conj
  obtain ⟨θ, -⟩ : ∃ θ : adjointGroup .G2 (ZMod 3) ≃* RG, True :=
    ⟨Subgroup.equivMapOfInjective _ (glHom (RingEquiv.refl (ZMod 3))) (glHom_injective _),
      trivial⟩
  obtain ⟨Ψ, hΨF⟩ := exists_iso_of_model hY hFe hF9 hT2 hFT hTF θ (aX_pow 0) (aX_pow 2)
    (aX_comm 0 2) orderOf_tAB (comm_of_conj_eq a0) (comm_of_conj_eq a2) card_F₀
  exact torusSep_of_iso Ψ aX tA tB aX_comm aX_pow a0 a2 a1 a3 b3 b1 card_R₀ R₀_inf_F₀ hΨF

theorem k417G2CoverCent_holds : K417G2CoverCent :=
  k417G2CoverCent_of k417G2TorusSep_holds

end Main

end CFSG.RankThree.PartTwo.Sec4.Res417Five.TorusSep
