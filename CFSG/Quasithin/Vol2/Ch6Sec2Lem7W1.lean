module

public import CFSG.Quasithin.EmptyFaithful.SBc3List
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.DoubleA3.Lemma36Cent
public import CFSG.Quasithin.Background.FFC8A
public import Certificates.Data.ExceptionalSL3

public section

namespace CFSG.Quasithin.H13

open CFSG.Open hiding StatedSL StatedClassicalModel StatedProj StatedLieTag StatedLieAdmissible
open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank

section OddCore

variable {Γ : Type*} [Group Γ]

theorem mem_map_conj_iff627 {H : Subgroup Γ} {k x : Γ} :
    x ∈ H.map (MulAut.conj k).toMonoidHom ↔ k⁻¹ * x * k ∈ H := by
  constructor
  · rintro ⟨h, hh, rfl⟩
    simpa [MulAut.conj_apply, mul_assoc] using hh
  · intro hx
    exact ⟨k⁻¹ * x * k, hx, by simp [MulAut.conj_apply, mul_assoc]⟩

variable [Finite Γ]

theorem oddCoreIn_le_oddCoreIn627 {N K : Subgroup Γ} (hNK : N ≤ K)
    (hn : K ≤ Subgroup.normalizer (N : Set Γ)) : oddCoreIn N ≤ oddCoreIn K := by
  refine DoubleA3.le_oddCoreIn_of_odd ((oddCoreIn_le N).trans hNK) (fun k hk => ?_)
    (odd_card_oddCoreIn N)
  set c := MulAut.conj k with hc
  set C := (oddCoreIn N).map c.toMonoidHom with hC
  have hkN : k ∈ Subgroup.normalizer (N : Set Γ) := hn hk
  have hNmap : N.map c.toMonoidHom = N := Subgroup.mem_normalizer_iff_map_conj_eq.mp hkN
  have hCN : C ≤ N := by
    rw [← hNmap]
    exact Subgroup.map_mono (oddCoreIn_le N)
  have hNC : N ≤ Subgroup.normalizer (C : Set Γ) := by
    intro n hnN
    have hn' : k⁻¹ * n * k ∈ N := by
      have := (Subgroup.mem_normalizer_iff.mp ((Subgroup.normalizer _).inv_mem hkN) n).mp hnN
      simpa [mul_assoc] using this
    have h1 := le_normalizer_oddCoreIn N hn'
    rw [Subgroup.mem_normalizer_iff]
    intro x
    rw [hC, mem_map_conj_iff627, mem_map_conj_iff627]
    rw [Subgroup.mem_normalizer_iff] at h1
    rw [h1 (k⁻¹ * x * k)]
    constructor <;> intro h <;> convert h using 1 <;> group
  have hCodd : Odd (Nat.card C) := by
    rw [hC, Subgroup.card_map_of_injective c.injective]
    exact odd_card_oddCoreIn N
  have hle : C ≤ oddCoreIn N := DoubleA3.le_oddCoreIn_of_odd hCN hNC hCodd
  have heq : C = oddCoreIn N := Subgroup.eq_of_le_of_card_ge hle
    (by rw [hC, Subgroup.card_map_of_injective c.injective])
  exact Subgroup.mem_normalizer_iff_map_conj_eq.mpr heq

abbrev cenOdd627 (X : Subgroup Γ) : Subgroup Γ :=
  X ⊓ Subgroup.centralizer (oddCoreIn X : Set Γ)

omit [Finite Γ] in
theorem le_normalizer_cenOdd627 (X : Subgroup Γ) :
    X ≤ Subgroup.normalizer (cenOdd627 X : Set Γ) := by
  intro x hx
  rw [Subgroup.mem_normalizer_iff]
  intro y
  have hxO := le_normalizer_oddCoreIn X hx
  constructor
  · rintro ⟨hyX, hyC⟩
    refine ⟨X.mul_mem (X.mul_mem hx hyX) (X.inv_mem hx), Subgroup.mem_centralizer_iff.mpr ?_⟩
    intro o ho
    have ho' : x⁻¹ * o * x ∈ oddCoreIn X := by
      have := (Subgroup.mem_normalizer_iff.mp ((Subgroup.normalizer _).inv_mem hxO) o).mp ho
      simpa [mul_assoc] using this
    have h1 := Subgroup.mem_centralizer_iff.mp hyC _ ho'
    calc o * (x * y * x⁻¹) = x * ((x⁻¹ * o * x) * y) * x⁻¹ := by group
      _ = x * (y * (x⁻¹ * o * x)) * x⁻¹ := by rw [h1]
      _ = x * y * x⁻¹ * o := by group
  · rintro ⟨hyX, hyC⟩
    have hyX' : y ∈ X := by
      have := X.mul_mem (X.mul_mem (X.inv_mem hx) hyX) hx
      simpa [mul_assoc] using this
    refine ⟨hyX', Subgroup.mem_centralizer_iff.mpr ?_⟩
    intro o ho
    have ho' : x * o * x⁻¹ ∈ oddCoreIn X := (Subgroup.mem_normalizer_iff.mp hxO o).mp ho
    have h1 := Subgroup.mem_centralizer_iff.mp hyC _ ho'
    calc o * y = x⁻¹ * ((x * o * x⁻¹) * (x * y * x⁻¹)) * x := by group
      _ = x⁻¹ * ((x * y * x⁻¹) * (x * o * x⁻¹)) * x := by rw [h1]
      _ = y * o := by group

theorem commute_of_odd_cenOdd627 {X J P : Subgroup Γ} (hJY : J ≤ cenOdd627 X)
    (hJn : cenOdd627 X ≤ Subgroup.normalizer (J : Set Γ)) (hPJ : P ≤ J)
    (hPn : J ≤ Subgroup.normalizer (P : Set Γ)) (hP : Odd (Nat.card P)) :
    ∀ y ∈ cenOdd627 X, ∀ p ∈ P, y * p = p * y := by
  intro y hy p hp
  have h1 : P ≤ oddCoreIn J := DoubleA3.le_oddCoreIn_of_odd hPJ hPn hP
  have h2 : oddCoreIn J ≤ oddCoreIn (cenOdd627 X) := oddCoreIn_le_oddCoreIn627 hJY hJn
  have h3 : oddCoreIn (cenOdd627 X) ≤ oddCoreIn X :=
    oddCoreIn_le_oddCoreIn627 inf_le_left (le_normalizer_cenOdd627 X)
  exact (Subgroup.mem_centralizer_iff.mp hy.2 p (h3 (h2 (h1 hp)))).symm

end OddCore

section Factors

theorem isQuasisimple_of_simple_of_four_dvd627 {G : Type*} [Group G] [Finite G]
    (hs : IsSimpleGroup G) (h4 : 4 ∣ Nat.card G) : CFSG.IsQuasisimple G := by
  have hnc : ∃ a b : G, a * b ≠ b * a := by
    by_contra hcon
    push Not at hcon
    let _ : CommGroup G := { ‹Group G› with mul_comm := hcon }
    have hp : (Nat.card G).Prime := IsSimpleGroup.prime_card
    have h2 : 2 ∣ Nat.card G := (show 2 ∣ 4 by norm_num).trans h4
    have h22 : Nat.card G = 2 := ((Nat.prime_dvd_prime_iff_eq Nat.prime_two hp).mp h2).symm
    rw [h22] at h4
    omega
  exact (CFSG.LocalCores.isQuasisimple_of_isSimpleGroup hnc).1

variable {K : Type} [Field K] [CharP K 2]

@[expose] def sl2x627 : Matrix.SpecialLinearGroup (Fin 2) K :=
  ⟨!![0, 1; 1, 1], by rw [Matrix.det_fin_two_of]; simp [CharTwo.neg_eq]⟩

@[expose] def sl2y627 : Matrix.SpecialLinearGroup (Fin 2) K :=
  ⟨!![1, 1; 0, 1], by rw [Matrix.det_fin_two_of]; simp⟩

theorem sl2x627_coe : ((sl2x627 (K := K) : Matrix.SpecialLinearGroup (Fin 2) K) :
    Matrix (Fin 2) (Fin 2) K) = !![0, 1; 1, 1] := rfl

omit [CharP K 2] in
theorem sl2y627_coe : ((sl2y627 (K := K) : Matrix.SpecialLinearGroup (Fin 2) K) :
    Matrix (Fin 2) (Fin 2) K) = !![1, 1; 0, 1] := rfl

theorem orderOf_sl2x627 : orderOf (sl2x627 (K := K)) = 3 := by
  have h2 : (1 : K) + 1 = 0 := CharTwo.add_self_eq_zero 1
  refine orderOf_eq_prime ?_ ?_
  · apply Subtype.ext
    rw [Matrix.SpecialLinearGroup.coe_pow, sl2x627_coe, Matrix.SpecialLinearGroup.coe_one]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [pow_succ, Matrix.mul_apply, Fin.sum_univ_two, h2]
  · intro h
    have := congrArg (fun g : Matrix.SpecialLinearGroup (Fin 2) K =>
      (g : Matrix (Fin 2) (Fin 2) K) 0 0) h
    simp only [sl2x627_coe, Matrix.SpecialLinearGroup.coe_one] at this
    simp at this

theorem sl2x627_mul_ne : sl2x627 (K := K) * sl2y627 ≠ sl2y627 * sl2x627 := by
  intro h
  have := congrArg (fun g : Matrix.SpecialLinearGroup (Fin 2) K =>
    (g : Matrix (Fin 2) (Fin 2) K) 0 0) h
  simp only [Matrix.SpecialLinearGroup.coe_mul, sl2x627_coe, sl2y627_coe] at this
  simp [Matrix.mul_apply, Fin.sum_univ_two] at this

end Factors

section FactorCases

theorem mem_zpowers_of_card_six627 {G : Type*} [Group G] [Finite G] (h6 : Nat.card G = 6)
    {x y : G} (hx : orderOf x = 3) (hy : orderOf y = 3) : y ∈ Subgroup.zpowers x := by
  have hidx : (Subgroup.zpowers x).index = 2 := by
    have := (Subgroup.zpowers x).index_mul_card
    rw [Nat.card_zpowers, hx, h6] at this
    omega
  by_contra hyx
  have h1 : y * y ∈ Subgroup.zpowers x := Subgroup.mul_self_mem_of_index_two hidx y
  have hy3 : y ^ 3 = 1 := by rw [← hy]; exact pow_orderOf_eq_one y
  have e : y = (y * y)⁻¹ := by
    rw [eq_inv_iff_mul_eq_one, ← hy3]
    simp [pow_succ, mul_assoc]
  exact hyx (e ▸ Subgroup.inv_mem _ h1)

theorem sl2Two_data627 {Γ : Type} [Group Γ] {G : Subgroup Γ} {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = 2) (e : ↥G ≃* ↥(StatedSL 2 K)) :
    ∃ x ∈ G, orderOf x = 3 ∧ (∀ y ∈ G, orderOf y = 3 → y ∈ Subgroup.zpowers x) ∧
      ∃ y ∈ G, x * y ≠ y * x := by
  have : CharP K 2 := R3c.charP_two_of_natCard_eq_two_pow (f := 1) (by simpa using hK)
  set φ := specialLinearGroupEquivStatedSL 2 K with hφ
  set x₀ : ↥G := e.symm (φ sl2x627) with hx₀
  set y₀ : ↥G := e.symm (φ sl2y627) with hy₀
  have hx₀3 : orderOf x₀ = 3 := by
    rw [hx₀, MulEquiv.orderOf_eq, MulEquiv.orderOf_eq, orderOf_sl2x627]
  have hG6 : Nat.card ↥G = 6 := by
    rw [Nat.card_congr e.toEquiv, R3c.card_statedSL_two_pow (n := 1) (by simpa using hK)]
    norm_num
  have : Finite ↥G := Nat.finite_of_card_ne_zero (by rw [hG6]; norm_num)
  refine ⟨(x₀ : Γ), x₀.2, by rw [Subgroup.orderOf_coe, hx₀3], fun y hy hy3 => ?_,
    (y₀ : Γ), y₀.2, fun h => ?_⟩
  · have hy3' : orderOf (⟨y, hy⟩ : ↥G) = 3 := by rw [Subgroup.orderOf_mk, hy3]
    obtain ⟨k, hk⟩ := mem_zpowers_of_card_six627 hG6 hx₀3 hy3'
    exact ⟨k, by simpa using congrArg Subtype.val hk⟩
  · apply sl2x627_mul_ne (K := K)
    apply φ.injective
    apply e.symm.injective
    rw [map_mul, map_mul, map_mul, map_mul]
    exact Subtype.ext (by simpa using h)

theorem factor_cases627 {Γ : Type} [Group Γ] [Finite Γ] {G : Subgroup Γ}
    (hf : B56FactorList ↥G) :
    (∃ L ≤ G, (L.subgroupOf G).Normal ∧ CFSG.IsQuasisimple ↥L ∧ 3 ∣ Nat.card L) ∨
      (∃ x ∈ G, orderOf x = 3 ∧ (∀ y ∈ G, orderOf y = 3 → y ∈ Subgroup.zpowers x) ∧
        ∃ y ∈ G, x * y ≠ y * x) := by
  rcases hf with ⟨n, K, _, _, hn, hK, ⟨e⟩⟩ | ⟨⟨e⟩⟩ | ⟨m, K, _, _, hm, hmo, hK, ⟨e⟩⟩
  · rcases Nat.lt_or_ge 1 n with h2 | h1
    · left
      have : CharP K 2 := R3c.charP_two_of_natCard_eq_two_pow hK
      have h4 : 4 ≤ Nat.card K := by
        rw [hK]
        calc 4 = 2 ^ 2 := by norm_num
          _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) h2
      have := CFSG.Quasithin.H13.NQRigid.isSimpleGroup_statedSL_two_charTwo (F := K) h4
      have hs : IsSimpleGroup ↥G := e.isSimpleGroup
      have hcard : Nat.card ↥G = 2 ^ n * (4 ^ n - 1) := by
        rw [Nat.card_congr e.toEquiv, R3c.card_statedSL_two_pow hK]
      refine ⟨G, le_rfl, ?_, isQuasisimple_of_simple_of_four_dvd627 hs ?_, ?_⟩
      · rw [Subgroup.subgroupOf_self]
        infer_instance
      · rw [hcard]
        exact Dvd.dvd.mul_right ((show (4 : ℕ) ∣ 2 ^ 2 by norm_num).trans (pow_dvd_pow 2 h2)) _
      · rw [hcard]
        refine Dvd.dvd.mul_left ?_ _
        simpa using Nat.sub_dvd_pow_sub_pow 4 1 n
    · right
      obtain rfl : n = 1 := le_antisymm h1 hn
      exact sl2Two_data627 (by simpa using hK) e
  · left
    set M : Subgroup ↥G := (alternatingGroup (Fin 5)).map e.symm.toMonoidHom with hM
    have hMn : M.Normal := Subgroup.Normal.map inferInstance _ e.symm.surjective
    have eM : ↥(M.map G.subtype) ≃* ↥(alternatingGroup (Fin 5)) :=
      (Subgroup.equivMapOfInjective M G.subtype G.subtype_injective).symm.trans
        (Subgroup.equivMapOfInjective _ e.symm.toMonoidHom e.symm.injective).symm
    have hA5 : Nat.card ↥(alternatingGroup (Fin 5)) = 60 := by
      have := two_mul_card_alternatingGroup (α := Fin 5)
      rw [Fintype.card_perm, Fintype.card_fin] at this
      rw [Nat.card_eq_fintype_card]
      have h120 : Nat.factorial 5 = 120 := by decide
      omega
    have : IsSimpleGroup ↥(alternatingGroup (Fin 5)) :=
      alternatingGroup.isSimpleGroup (by norm_num : 5 ≤ Nat.card (Fin 5))
    have hs : IsSimpleGroup ↥(M.map G.subtype) := eM.isSimpleGroup
    refine ⟨M.map G.subtype, Subgroup.map_subtype_le M, ?_,
      isQuasisimple_of_simple_of_four_dvd627 hs ?_, ?_⟩
    · rw [Subgroup.subgroupOf, Subgroup.comap_map_eq_self_of_injective G.subtype_injective]
      exact hMn
    · rw [Nat.card_congr eM.toEquiv, hA5]
      norm_num
    · rw [Nat.card_congr eM.toEquiv, hA5]
      norm_num
  · left
    have := CFSG.Quasithin.H13.NQRigid.isSimpleGroup_statedSL_three_odd hK hmo
    have hs : IsSimpleGroup ↥G := e.isSimpleGroup
    have hcard : Nat.card ↥G = (2 ^ m) ^ 3 * ((2 ^ m) ^ 2 - 1) * ((2 ^ m) ^ 3 - 1) := by
      rw [Nat.card_congr e.toEquiv, CFSG.SectionRank.OddCover.card_statedSL_three, hK]
    refine ⟨G, le_rfl, ?_, isQuasisimple_of_simple_of_four_dvd627 hs ?_, ?_⟩
    · rw [Subgroup.subgroupOf_self]
      infer_instance
    · rw [hcard]
      refine Dvd.dvd.mul_right (Dvd.dvd.mul_right ?_ _) _
      rw [← pow_mul]
      exact (show (4 : ℕ) ∣ 2 ^ 2 by norm_num).trans
        (pow_dvd_pow 2 (by omega : 2 ≤ m * 3))
    · rw [hcard]
      refine Dvd.dvd.mul_right (Dvd.dvd.mul_left ?_ _) _
      rw [← pow_mul, mul_comm, pow_mul]
      simpa using Nat.sub_dvd_pow_sub_pow 4 1 m

end FactorCases

section Main

theorem le_normalizer_zpowers627 {Γ : Type*} [Group Γ] [Finite Γ] {J : Subgroup Γ} {x : Γ}
    (h : ∀ j ∈ J, j * x * j⁻¹ ∈ Subgroup.zpowers x) :
    J ≤ Subgroup.normalizer (Subgroup.zpowers x : Set Γ) := by
  intro j hj
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  refine Subgroup.eq_of_le_of_card_ge ?_ ?_
  · rw [MonoidHom.map_zpowers, Subgroup.zpowers_le]
    exact h j hj
  · rw [Subgroup.card_map_of_injective (MulAut.conj j).injective]

theorem one_le_of_card_eq_two_pow627 {K : Type} [Field K] [Finite K] {n : ℕ}
    (hK : Nat.card K = 2 ^ n) : 1 ≤ n := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · have := Finite.one_lt_card_iff_nontrivial.2 (inferInstance : Nontrivial K)
    simp [hK] at this
  · exact hn

variable {Q : Type} [CommGroup Q] [Finite Q]

theorem b56Case1_cenOdd627 [Finite (MulAut Q)] {X A : Subgroup (MulAut Q)}
    (hA : IsFFStarOffender (cenOdd627 X) A) (hA4 : Nat.card A = 4)
    (huniq : ∀ L₁ L₂ : Subgroup (MulAut Q), IsSubnormal L₁ X → IsSubnormal L₂ X →
      CFSG.IsQuasisimple ↥L₁ → CFSG.IsQuasisimple ↥L₂ → 3 ∣ Nat.card L₁ → 3 ∣ Nat.card L₂ →
        L₁ = L₂)
    (hcases : B56Case1 (ffJ (cenOdd627 X)) ∨ B56Case2 (ffJ (cenOdd627 X)) ∨
      B56Case3 (ffJ (cenOdd627 X)) ∨ B56Case4 (ffJ (cenOdd627 X)) ∨
        B56Case5 (ffJ (cenOdd627 X))) :
    B56Case1 (ffJ (cenOdd627 X)) := by
  classical
  set Y := cenOdd627 X with hY
  set J := ffJ Y with hJ
  have hAJ : A ≤ J := B6.le_ffJ hA
  have hJY : J ≤ Y := B6.ffJ_le Y
  have hJn : Y ≤ Subgroup.normalizer (J : Set (MulAut Q)) := B6.le_normalizer_ffJ Y
  have hYsn : IsSubnormal Y X := A3.subnormal_of_normal inf_le_left
    ((Subgroup.normal_subgroupOf_iff_le_normalizer inf_le_left).mpr (le_normalizer_cenOdd627 X))
  have hJsn : IsSubnormal J X := A3.subnormal_trans (A3.subnormal_of_normal hJY
    ((Subgroup.normal_subgroupOf_iff_le_normalizer hJY).mpr hJn)) hYsn
  have hfac : ∀ G : Subgroup (MulAut Q), G ≤ J → (G.subgroupOf J).Normal → B56FactorList ↥G →
      ∃ L ≤ G, IsSubnormal L X ∧ CFSG.IsQuasisimple ↥L ∧ 3 ∣ Nat.card L := by
    intro G hGJ hGn hf
    have hGsn : IsSubnormal G X := A3.subnormal_trans (A3.subnormal_of_normal hGJ hGn) hJsn
    rcases factor_cases627 hf with ⟨L, hLG, hLn, hLq, hL3⟩ | ⟨x, hxG, hx3, hxall, y, hyG, hxy⟩
    · exact ⟨L, hLG, A3.subnormal_trans (A3.subnormal_of_normal hLG hLn) hGsn, hLq, hL3⟩
    · exfalso
      have hGnorm : J ≤ Subgroup.normalizer (G : Set (MulAut Q)) :=
        (Subgroup.normal_subgroupOf_iff_le_normalizer hGJ).mp hGn
      have hxJ : ∀ j ∈ J, j * x * j⁻¹ ∈ Subgroup.zpowers x := fun j hj =>
        hxall _ ((Subgroup.mem_normalizer_iff.mp (hGnorm hj) x).mp hxG)
          (by rw [show j * x * j⁻¹ = MulAut.conj j x from rfl, MulEquiv.orderOf_eq, hx3])
      have hPJ : Subgroup.zpowers x ≤ J := (Subgroup.zpowers_le.mpr hxG).trans hGJ
      have hPodd : Odd (Nat.card (Subgroup.zpowers x)) := by
        rw [Nat.card_zpowers, hx3]
        decide
      have h1 := commute_of_odd_cenOdd627 hJY hJn hPJ (le_normalizer_zpowers627 hxJ) hPodd y
        (hJY (hGJ hyG)) x (Subgroup.mem_zpowers x)
      exact hxy h1.symm
  have htwo : ∀ G₁ G₂ : Subgroup (MulAut Q), G₁ ⊔ G₂ = J → G₁ ⊓ G₂ = ⊥ →
      (∀ a ∈ G₁, ∀ b ∈ G₂, a * b = b * a) → B56FactorList ↥G₁ → B56FactorList ↥G₂ → False := by
    intro G₁ G₂ hsup hinf hc hf₁ hf₂
    obtain ⟨hn₁, hn₂⟩ := SBc3.normal_of_commute hc
    rw [hsup] at hn₁ hn₂
    obtain ⟨L₁, hL₁, hsn₁, hq₁, h3₁⟩ := hfac G₁ (hsup ▸ le_sup_left) hn₁ hf₁
    obtain ⟨L₂, hL₂, hsn₂, hq₂, h3₂⟩ := hfac G₂ (hsup ▸ le_sup_right) hn₂ hf₂
    have heq := huniq L₁ L₂ hsn₁ hsn₂ hq₁ hq₂ h3₁ h3₂
    apply SBc3.ne_bot_of_isQuasisimple hq₁
    rw [eq_bot_iff, ← hinf]
    exact le_inf hL₁ (heq ▸ hL₂)
  rcases hcases with h1 | ⟨⟨e⟩, -⟩ | ⟨G₁, G₂, hsup, hinf, hc, hf₁, hf₂, -⟩ |
      ⟨G₁, G₂, t, hJt, -, hc, -, hc₂, -, -, -, -, -, ht₁, ht₂, -, hout⟩ |
      ⟨G₁, G₂, hsup, hinf, hc, -, ⟨e₁⟩, -, -, h₂⟩
  · exact h1
  · exfalso
    have h6 : Nat.card J = 6 := by
      rw [Nat.card_congr e.toEquiv, Nat.card_perm, Nat.card_fin]
      rfl
    have h4 := Subgroup.card_dvd_of_le hAJ
    rw [hA4, h6] at h4
    omega
  · exact (htwo G₁ G₂ hsup hinf hc hf₁ hf₂).elim
  · exfalso
    have hc' : ∀ a ∈ G₂, ∀ b ∈ G₁, a * b = b * a := fun a ha b hb => (hc b hb a ha).symm
    have h₂J : G₂ ≤ J := by rw [hJt]; exact le_sup_right.trans le_sup_left
    have hn₂ : J ≤ Subgroup.normalizer (G₂ : Set (MulAut Q)) := by
      refine (Subgroup.normal_subgroupOf_iff_le_normalizer h₂J).mp
        ((Subgroup.normal_subgroupOf_iff h₂J).2 fun h k hh hk => ?_)
      rw [hJt, sup_comm G₁ G₂] at hk
      exact SBc3.conj_mem_of_mem_sup_zpowers hc' ht₂ ht₁ k hk h hh
    have hodd : Odd (Nat.card G₂) := by
      rw [hc₂]
      decide
    have htJ : t ∈ J := by
      rw [hJt]
      exact Subgroup.mem_sup_right (Subgroup.mem_zpowers t)
    have hct := commute_of_odd_cenOdd627 hJY hJn h₂J hn₂ hodd t (hJY htJ)
    refine hout ⟨1, G₂.one_mem, fun x hx => ?_⟩
    rw [hct x hx, mul_inv_cancel_right, one_mul, inv_one, mul_one]
  · exfalso
    have hf₁ : B56FactorList ↥G₁ :=
      Or.inr (Or.inr ⟨1, ZMod 2, inferInstance, inferInstance, le_rfl, odd_one, by simp, ⟨e₁⟩⟩)
    have hf₂ : B56FactorList ↥G₂ := by
      rcases h₂ with ⟨⟨e₂⟩, -⟩ | ⟨n, F, _, _, hF, π, hR⟩
      · exact Or.inr (Or.inr ⟨1, ZMod 2, inferInstance, inferInstance, le_rfl, odd_one, by simp,
          ⟨e₂⟩⟩)
      · exact Or.inl ⟨n, F, inferInstance, inferInstance, one_le_of_card_eq_two_pow627 hF, hF,
          ⟨(FFC.equivOfRealizes (FFModel.nat_faithful _) hR).symm⟩⟩
    exact htwo G₁ G₂ hsup hinf hc hf₁ hf₂

end Main

end CFSG.Quasithin.H13
