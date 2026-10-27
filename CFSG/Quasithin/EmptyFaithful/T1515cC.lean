module

public import CFSG.Quasithin.Background.OrderingMax
public import CFSG.Quasithin.Background.C2Thirteen
public import CFSG.Quasithin.EmptyFaithful.T1515cA

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits

section Uniqueness

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem mem_normalizer_sup1515c {K Q : Subgroup G} {y : G}
    (hK : y ∈ Subgroup.normalizer (K : Set G)) (hQ : y ∈ Subgroup.normalizer (Q : Set G)) :
    y ∈ Subgroup.normalizer ((K ⊔ Q : Subgroup G) : Set G) := by
  rw [C2Eleven.mem_normalizer_iff_conjByElt] at hK hQ ⊢
  rw [C2Thirteen.conjByElt_sup, hK, hQ]

omit [Finite G] in
theorem le_of_isShort2_of_le_sup1515c {K Q X : Subgroup G} (hQ : IsPGroup 2 Q)
    (hN : Q ≤ Subgroup.normalizer (K : Set G)) (hX : IsShort2 X) (hXH : X ≤ K ⊔ Q) : X ≤ K := by
  have hXN : K ⊔ Q ≤ Subgroup.normalizer (K : Set G) := sup_le Subgroup.le_normalizer hN
  let N : Subgroup ↥X := K.subgroupOf X
  have hNn : N.Normal := by
    refine ⟨fun n hn g => ?_⟩
    have hg : (g : G) ∈ Subgroup.normalizer (K : Set G) := hXN (hXH g.2)
    have := (Subgroup.mem_normalizer_iff.mp hg (n : G)).mp (Subgroup.mem_subgroupOf.mp hn)
    rw [Subgroup.mem_subgroupOf]
    simpa [mul_assoc] using this
  have hpg : IsPGroup 2 (↥X ⧸ N) := by
    intro q
    induction q using QuotientGroup.induction_on with
    | H g =>
      obtain ⟨k, hk⟩ := exists_pow_mem_of_mem_sup1515c hQ hN (hXH g.2)
      refine ⟨k, ?_⟩
      rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
      simpa using hk
  have hNtop : N = ⊤ := hX.1 N hpg
  intro l hl
  have : (⟨l, hl⟩ : ↥X) ∈ N := by rw [hNtop]; trivial
  exact Subgroup.mem_subgroupOf.mp this

omit [Finite G] in
theorem eq_one_of_odd_orderOf_of_oTwoUpper_eq_bot1515c {X : Subgroup G} (hY : oTwoUpper X = ⊥) {x : G}
    (hx : x ∈ X) (ho : Odd (orderOf x)) : x = 1 := by
  have : x ∈ oTwoUpper X := mem_oTwoUpper_of_odd hx ho
  rw [hY] at this
  exact Subgroup.mem_bot.mp this

theorem isPGroup_two_of_odd_orderOf_eq_one1515c {X : Subgroup G}
    (h : ∀ x ∈ X, Odd (orderOf x) → x = 1) : IsPGroup 2 X := by
  intro x
  obtain ⟨k, m, hm, hkm⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos (x : G)).ne'
  have h2k : (2 ^ k : ℕ) ≠ 0 := by positivity
  have hodd : Odd (orderOf ((x : G) ^ 2 ^ k)) := by
    rw [orderOf_pow' _ h2k, hkm, Nat.gcd_mul_right_left, Nat.mul_div_cancel_left _ (by positivity)]
    exact hm
  have h1 : (x : G) ^ 2 ^ k = 1 := h _ (X.pow_mem x.2 _) hodd
  exact ⟨k, Subtype.ext (by simpa using h1)⟩

theorem oTwoUpper_ne_bot_of_isUniqueM1515c {Mz T Mc M S G1 : Subgroup G} (hS : IsSylowTwoOf S G1)
    (hSMz : S ≤ Mz) (hMzG : Mz ≤ G1) (hST : S ≤ T) (hU : IsUniqueM (Mz ⊔ T) Mc)
    (hM : InM T M) (hMc : M ≠ Mc) : oTwoUpper Mz ≠ ⊥ := by
  intro hY
  have hMz2 : IsPGroup 2 Mz :=
    isPGroup_two_of_odd_orderOf_eq_one1515c fun x hx ho =>
      eq_one_of_odd_orderOf_of_oTwoUpper_eq_bot1515c hY hx ho
  have hSyl : IsSylowTwoOf S Mz := A4.isSylowTwoOf_mono hS hSMz hMzG
  have hMzS : Mz ≤ S := (A4.isSylowTwoOf_iff_maximal.mp hSyl).2.2 Mz le_rfl hMz2 hSMz
  have hMzT : Mz ≤ T := hMzS.trans hST
  rw [sup_eq_right.mpr hMzT] at hU
  exact hMc (hU.2 M hM)

theorem normalizer_oTwoUpper_le_of_isUniqueM1515c {Mz T Mc : Subgroup G}
    (hU : IsUniqueM (Mz ⊔ T) Mc) (hTN : T ≤ Subgroup.normalizer (Mz : Set G)) (hCT : CharTwo Mz)
    (hY : oTwoUpper Mz ≠ ⊥) : Subgroup.normalizer (oTwoUpper Mz : Set G) ≤ Mc := by
  set Y := oTwoUpper Mz with hYdef
  set Q := pCoreOf 2 Mz with hQ
  have hYMz : Y ≤ Mz := oTwoUpper_le Mz
  have hMzN : Mz ≤ Subgroup.normalizer (Y : Set G) := le_normalizer_oTwoUpper Mz
  have hTNY : T ≤ Subgroup.normalizer (Y : Set G) :=
    hTN.trans (normalizer_le_normalizer_oTwoUpper Mz)
  have hsup : Mz ⊔ T ≤ Subgroup.normalizer (Y : Set G) := sup_le hMzN hTNY
  have hP : pCoreOf 2 Y ≠ ⊥ := by
    intro hP
    have hYQ : Y ≤ Subgroup.centralizer (Q : Set G) := by
      intro y hy
      rw [Subgroup.mem_centralizer_iff]
      intro q hq
      have hyMz : y ∈ Mz := hYMz hy
      have hqMz : q ∈ Mz := pCoreOf_le 2 Mz hq
      have h1 : y * q * y⁻¹ ∈ Q :=
        (Subgroup.mem_normalizer_iff.mp (le_normalizer_pCoreOf 2 Mz hyMz) q).mp hq
      have h2 : q * y⁻¹ * q⁻¹ ∈ Y := by
        have := (Subgroup.mem_normalizer_iff.mp (hMzN hqMz) y⁻¹).mp (Y.inv_mem hy)
        exact this
      have hc1 : y * q * y⁻¹ * q⁻¹ ∈ Q := Q.mul_mem h1 (Q.inv_mem hq)
      have hc2 : y * q * y⁻¹ * q⁻¹ ∈ Y := by
        have := Y.mul_mem hy h2
        simpa [mul_assoc] using this
      have hYQnorm : Y ≤ Subgroup.normalizer ((Y ⊓ Q : Subgroup G) : Set G) := fun g hg =>
        Subgroup.inf_normalizer_le_normalizer_inf
          ⟨Subgroup.le_normalizer hg, le_normalizer_pCoreOf 2 Mz (hYMz hg)⟩
      have hle : Y ⊓ Q ≤ pCoreOf 2 Y :=
        le_pCoreOf_of_le_normalizer 2 inf_le_left hYQnorm
          ((pCoreOf_isPGroup 2 Mz).to_le inf_le_right)
      have : y * q * y⁻¹ * q⁻¹ ∈ pCoreOf 2 Y := hle ⟨hc2, hc1⟩
      rw [hP, Subgroup.mem_bot] at this
      have h3 : y * q = q * y := by
        have := congrArg (· * (q * y)) this
        simpa [mul_assoc] using this
      exact h3.symm
    have hYQ' : Y ≤ Q := fun y hy => hCT ⟨hYMz hy, hYQ hy⟩
    have : Y = ⊥ := by
      rw [eq_bot_iff, hYdef, oTwoUpper, Subgroup.closure_le]
      intro x hx
      have hxQ : x ∈ Q := hYQ' (Subgroup.subset_closure hx)
      obtain ⟨k, hk⟩ := (pCoreOf_isPGroup 2 Mz) ⟨x, hxQ⟩
      have hk' : x ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
      have hdvd : orderOf x ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one hk'
      have hcop : Nat.Coprime (orderOf x) (2 ^ k) :=
        Nat.Coprime.pow_right k (Nat.coprime_two_right.mpr hx.2)
      have : orderOf x = 1 := Nat.Coprime.eq_one_of_dvd hcop hdvd
      exact Subgroup.mem_bot.mpr (orderOf_eq_one_iff.mp this)
    exact hY this
  have hloc : IsTwoLocal (Subgroup.normalizer (pCoreOf 2 Y : Set G)) :=
    ⟨pCoreOf 2 Y, hP, pCoreOf_isPGroup 2 Y, rfl⟩
  obtain ⟨M', hM'max, hle⟩ := exists_maxTwoLocal_ge hloc
  have hNY : Subgroup.normalizer (Y : Set G) ≤ Subgroup.normalizer (pCoreOf 2 Y : Set G) :=
    normalizer_le_normalizer_pCoreOf 2 Y
  have hInM : InM (Mz ⊔ T) M' := ⟨hM'max, hsup.trans (hNY.trans hle)⟩
  have hEq := hU.2 M' hInM
  rw [hEq] at hle
  exact hNY.trans hle

end Uniqueness

end CFSG.Quasithin
