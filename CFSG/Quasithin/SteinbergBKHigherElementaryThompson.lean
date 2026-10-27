module

public import CFSG.Foundations.HigherElementaryThompson
import CFSG.Quasithin.Background.BlueprintB2Thompson
import CFSG.GroupTheory.ElementaryAbelianTransport

public section

namespace CFSG.Quasithin.SteinbergBK

open Subgroup CFSG

variable {S : Type*} [Group S]

theorem mem_omegaOneCenter_iff (J : Subgroup S) (z : S) :
    z ∈ omegaOneCenter J ↔ z ∈ J ∧ (∀ y ∈ J, y * z = z * y) ∧ z ^ 2 = 1 := by
  constructor
  · rintro ⟨⟨w, hw, rfl⟩, hz⟩
    exact ⟨w.2, fun y hy => congrArg Subtype.val (mem_center_iff.mp hw ⟨y, hy⟩), hz⟩
  · rintro ⟨hzJ, hc, hz⟩
    exact ⟨⟨⟨z, hzJ⟩, mem_center_iff.mpr fun y => Subtype.ext (hc y y.2), rfl⟩, hz⟩

theorem map_subtype_omegaOneCenter (R : Subgroup S) (J : Subgroup R) :
    (omegaOneCenter J).map R.subtype = omegaOneCenter (J.map R.subtype) := by
  ext s
  rw [mem_map, mem_omegaOneCenter_iff]
  constructor
  · rintro ⟨z, hz, rfl⟩
    rw [mem_omegaOneCenter_iff] at hz
    obtain ⟨hzJ, hzc, hz2⟩ := hz
    refine ⟨mem_map_of_mem _ hzJ, ?_, ?_⟩
    · rintro _ ⟨y, hy, rfl⟩
      exact congrArg Subtype.val (hzc y hy)
    · rw [coe_subtype, ← coe_pow, hz2, coe_one]
  · rintro ⟨⟨z, hzJ, rfl⟩, hc, hz2⟩
    refine ⟨z, (mem_omegaOneCenter_iff J z).mpr ⟨hzJ, fun y hy => ?_, ?_⟩, rfl⟩
    · exact Subtype.ext (hc _ (mem_map_of_mem _ hy))
    · apply Subtype.ext
      rw [coe_pow]
      exact hz2

theorem isElementaryAbelian_of_le_of_isElementaryAbelian {A B : Subgroup S}
    (hA : IsElementaryAbelian 2 A) (hBA : B ≤ A) : IsElementaryAbelian 2 B :=
  CFSG.IsElementaryAbelian.of_le hA hBA

variable [Finite S]

theorem le_higherElemThompson_of_le_pRank {j : ℕ} (hj : j < pRank 2 S) {A : Subgroup S}
    (hA : IsElementaryAbelian 2 A) (hrank : pRank 2 S - j ≤ pRank 2 A) :
    A ≤ higherElemThompson S j := by
  intro a ha
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have := hA
  obtain ⟨r, hr⟩ := IsPGroup.iff_card.mp (IsElementaryAbelian.isPGroup 2 A)
  have hrA : pRank 2 A = r := pRank_eq_of_card_eq_pow one_lt_two hr
  have ha2 : a ^ 2 = 1 := elemPow_eq_one_of_isElementaryAbelian a ha
  obtain ⟨K, hK, haK, hKA⟩ := Sylow.exists_subgroup_card_pow_prime_le_le Nat.prime_two
    (H := zpowers a) (L := A) (n := pRank 2 S - j)
    (by rw [Nat.card_zpowers]
        exact (orderOf_dvd_of_pow_eq_one ha2).trans (dvd_pow_self 2 (by omega)))
    (by rw [hr]; exact Nat.pow_dvd_pow 2 (by omega)) (zpowers_le.mpr ha)
  have hKfam : K ∈ higherElemThompsonFamily S j :=
    (mem_higherElemThompsonFamily_iff j K).mpr
      ⟨isElementaryAbelian_of_le_of_isElementaryAbelian hA hKA, hK⟩
  exact (le_sSup hKfam : K ≤ higherElemThompson S j) (haK (mem_zpowers a))

theorem exists_mem_higherElemThompsonFamily (j : ℕ) :
    ∃ A : Subgroup S, A ∈ higherElemThompsonFamily S j := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨A0, hA0e, hA0c⟩ := Quasithin.BlueprintB2.exists_card_eq_pow_pRank S 2
  obtain ⟨A, hA, -, hAA0⟩ := Sylow.exists_subgroup_card_pow_prime_le_le Nat.prime_two
    (H := ⊥) (L := A0) (n := pRank 2 S - j) (by rw [card_bot]; exact one_dvd _)
    (by rw [hA0c]; exact Nat.pow_dvd_pow 2 (Nat.sub_le _ _)) bot_le
  exact ⟨A, (mem_higherElemThompsonFamily_iff j A).mpr
    ⟨isElementaryAbelian_of_le_of_isElementaryAbelian hA0e hAA0, hA⟩⟩

theorem higherElemThompson_characteristic (j : ℕ) : (higherElemThompson S j).Characteristic := by
  rw [characteristic_iff_map_le]
  intro ϕ
  rw [map_le_iff_le_comap]
  refine sSup_le fun A hA => ?_
  rw [← map_le_iff_le_comap]
  refine le_sSup ?_
  rw [mem_higherElemThompsonFamily_iff] at hA ⊢
  obtain ⟨hAe, hAc⟩ := hA
  have := hAe
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact ⟨IsElementaryAbelian.map ϕ.toMonoidHom, by rw [card_map_of_injective ϕ.injective, hAc]⟩

theorem higherElemThompsonOmega_characteristic (j : ℕ) :
    (higherElemThompsonOmega S j).Characteristic := by
  have hJ := characteristic_iff_map_le.mp (higherElemThompson_characteristic (S := S) j)
  rw [characteristic_iff_map_le]
  rintro ϕ _ ⟨z, hz, rfl⟩
  rw [SetLike.mem_coe, higherElemThompsonOmega, mem_omegaOneCenter_iff] at hz
  rw [higherElemThompsonOmega, mem_omegaOneCenter_iff]
  obtain ⟨hzJ, hzc, hz2⟩ := hz
  refine ⟨hJ ϕ ⟨z, hzJ, rfl⟩, fun y hy => ?_, ?_⟩
  · have hy' : ϕ.symm y ∈ higherElemThompson S j := by
      have h1 := hJ ϕ.symm ⟨y, hy, rfl⟩
      exact h1
    have h2 := congrArg ϕ (hzc _ hy')
    simpa using h2
  · simp [← map_pow, hz2]

theorem omegaOne_centralizer_eq {i : ℕ} (hi : i < pRank 2 S) :
    closure {x : S | x ∈ centralizer (higherElemThompson S i : Set S) ∧ x ^ 2 = 1} =
      higherElemThompsonOmega S i := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set J := higherElemThompson S i with hJ
  refine le_antisymm (closure_le _ |>.mpr ?_) fun z hz => subset_closure ?_
  · rintro x ⟨hxC, hx2⟩
    obtain ⟨A, hA⟩ := exists_mem_higherElemThompsonFamily (S := S) i
    have hAJ : A ≤ J := le_sSup hA
    obtain ⟨hAe, hAc⟩ := (mem_higherElemThompsonFamily_iff i A).mp hA
    have := hAe
    have hxA : zpowers x ≤ centralizer (A : Set S) :=
      zpowers_le.mpr (centralizer_le (SetLike.coe_subset_coe.mpr hAJ) hxC)
    have := IsElementaryAbelian.zpowers_of_pow_eq_one hx2
    have hBe : IsElementaryAbelian 2 ↥(A ⊔ zpowers x) :=
      IsElementaryAbelian.sup_of_le_centralizer hxA
    obtain ⟨b, hb⟩ := IsPGroup.iff_card.mp (IsElementaryAbelian.isPGroup 2 ↥(A ⊔ zpowers x))
    have hrank : pRank 2 S - i ≤ pRank 2 ↥(A ⊔ zpowers x) := by
      rw [pRank_eq_of_card_eq_pow one_lt_two hb]
      have h1 := card_le_of_le (le_sup_left : A ≤ A ⊔ zpowers x)
      rw [hAc, hb] at h1
      exact (Nat.pow_le_pow_iff_right one_lt_two).mp h1
    have hBJ := le_higherElemThompson_of_le_pRank hi hBe hrank
    have hxJ : x ∈ J := hBJ (mem_sup_right (mem_zpowers x))
    rw [SetLike.mem_coe, higherElemThompsonOmega, mem_omegaOneCenter_iff]
    exact ⟨hxJ, fun y hy => mem_centralizer_iff.mp hxC y hy, hx2⟩
  · rw [higherElemThompsonOmega, mem_omegaOneCenter_iff] at hz
    exact ⟨mem_centralizer_iff.mpr hz.2.1, hz.2.2⟩

omit [Finite S] in
theorem higherElemThompsonOmega_isElementaryAbelian (j : ℕ) :
    IsElementaryAbelian 2 (higherElemThompsonOmega S j) := by
  have hmem := fun z => (mem_omegaOneCenter_iff (higherElemThompson S j) z).mp
  exact
    { toIsMulCommutative := ⟨⟨fun a b => Subtype.ext ((hmem b b.2).2.1 a (hmem a a.2).1)⟩⟩
      exponent_dvd_p := Monoid.exponent_dvd_of_forall_pow_eq_one fun x => Subtype.ext (by
        rw [coe_pow, (hmem x x.2).2.2, coe_one]) }

theorem pRank_le_pRank_of_subgroup (R : Subgroup S) : pRank 2 R ≤ pRank 2 S := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨A, hAe, hAc⟩ := Quasithin.BlueprintB2.exists_card_eq_pow_pRank R 2
  have := hAe
  have h := Quasithin.BlueprintB2.card_le_pow_pRank
    (IsElementaryAbelian.map_subtype (p := 2) (H := A))
  rw [card_map_of_injective R.subtype_injective, hAc] at h
  exact (Nat.pow_le_pow_iff_right one_lt_two).mp h

theorem higher_elementary_thompson_intersections_and_central_involutions (hS : IsPGroup 2 S) :
    (∀ j : ℕ, (higherElemThompson S j).Characteristic ∧
      (higherElemThompsonOmega S j).Characteristic) ∧
    (∀ i j : ℕ, i ≤ j → j < pRank 2 S →
      higherElemThompson S 0 ≠ ⊥ ∧ higherElemThompson S 0 ≤ higherElemThompson S i ∧
      higherElemThompson S i ≤ higherElemThompson S j ∧
      (∀ A : Subgroup S, IsElementaryAbelian 2 A → pRank 2 S - j ≤ pRank 2 A →
        A ≤ higherElemThompson S j) ∧
      higherElemThompsonOmega S j ≤
        closure {x : S | x ∈ centralizer (higherElemThompson S i : Set S) ∧ x ^ 2 = 1} ∧
      closure {x : S | x ∈ centralizer (higherElemThompson S i : Set S) ∧ x ^ 2 = 1} =
        higherElemThompsonOmega S i ∧
      IsElementaryAbelian 2 (higherElemThompsonOmega S i) ∧ higherElemThompsonOmega S j ≠ ⊥) ∧
    (∀ j : ℕ, j < pRank 2 S → ∀ R : Subgroup S, higherElemThompson S j ≤ R →
      pRank 2 R = pRank 2 S ∧
      map R.subtype '' higherElemThompsonFamily R j = higherElemThompsonFamily S j ∧
      (higherElemThompson R j).map R.subtype = higherElemThompson S j ∧
      (higherElemThompsonOmega R j).map R.subtype = higherElemThompsonOmega S j) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨A0, hA0e, hA0c⟩ := Quasithin.BlueprintB2.exists_card_eq_pow_pRank S 2
  set m := pRank 2 S with hm
  have hA0J : ∀ j, j < m → A0 ≤ higherElemThompson S j := fun j hj =>
    le_higherElemThompson_of_le_pRank hj hA0e (by
      have := hA0e
      rw [pRank_eq_of_card_eq_pow one_lt_two hA0c]
      exact Nat.sub_le _ _)
  have hJ0 : ∀ j, j < m → higherElemThompson S 0 ≤ higherElemThompson S j := fun j hj =>
    sSup_le fun A hA => le_higherElemThompson_of_le_pRank hj hA.1 (by rw [hA.2]; omega)
  have hJ0ne : 0 < m → higherElemThompson S 0 ≠ ⊥ := by
    intro hm0 h
    have h1 := hA0J 0 hm0
    rw [h, le_bot_iff] at h1
    rw [h1, card_bot] at hA0c
    have := Nat.one_lt_two_pow (n := m) (by omega)
    omega
  refine ⟨fun j => ⟨higherElemThompson_characteristic j,
    higherElemThompsonOmega_characteristic j⟩, fun i j hij hj => ?_, fun j hj R hR => ?_⟩
  · have hi : i < m := lt_of_le_of_lt hij hj
    have hJij : higherElemThompson S i ≤ higherElemThompson S j :=
      sSup_le fun A hA => le_higherElemThompson_of_le_pRank hj hA.1 (by rw [hA.2]; omega)
    refine ⟨hJ0ne (by omega), hJ0 i hi, hJij, fun A hA hrank =>
      le_higherElemThompson_of_le_pRank hj hA hrank, ?_, omegaOne_centralizer_eq hi,
      higherElemThompsonOmega_isElementaryAbelian i, ?_⟩
    · intro z hz
      rw [higherElemThompsonOmega, mem_omegaOneCenter_iff] at hz
      refine subset_closure ⟨?_, hz.2.2⟩
      exact centralizer_le (SetLike.coe_subset_coe.mpr hJij) (mem_centralizer_iff.mpr hz.2.1)
    ·
      set J := higherElemThompson S j with hJ
      have hJne : J ≠ ⊥ := fun h => hJ0ne (by omega) (le_bot_iff.mp (h ▸ hJ0 j hj))
      have : Nontrivial J := (nontrivial_iff_ne_bot J).mpr hJne
      have hZ2 : IsPGroup 2 (center J) := (hS.to_subgroup J).to_subgroup (center J)
      have : Nontrivial (center J) := (hS.to_subgroup J).center_nontrivial
      obtain ⟨n, hn, hcard⟩ := hZ2.nontrivial_iff_card.mp inferInstance
      obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' (G := center J) 2
        (by rw [hcard]; exact dvd_pow_self 2 hn.ne')
      have hz2 : ((z : J) : S) ^ 2 = 1 := by
        have h1 : z ^ 2 = 1 := hz ▸ pow_orderOf_eq_one z
        have h2 := congrArg (fun w : center J => ((w : J) : S)) h1
        simpa using h2
      have hz1 : ((z : J) : S) ≠ 1 := by
        intro h
        have h1 : z = 1 := Subtype.ext (Subtype.ext h)
        rw [h1, orderOf_one] at hz
        omega
      intro hbot
      have hzE : ((z : J) : S) ∈ higherElemThompsonOmega S j := ⟨⟨z.1, z.2, rfl⟩, hz2⟩
      rw [hbot, mem_bot] at hzE
      exact hz1 hzE
  ·
    have hA0R : A0 ≤ R := (hA0J j hj).trans hR
    have hRrank : pRank 2 R = m := by
      refine le_antisymm (pRank_le_pRank_of_subgroup R) ?_
      have := hA0e
      have h := Quasithin.BlueprintB2.card_le_pow_pRank (R := R)
        (IsElementaryAbelian.subgroupOf (p := 2) hA0R)
      rw [Nat.card_congr (subgroupOfEquivOfLe hA0R).toEquiv, hA0c] at h
      exact (Nat.pow_le_pow_iff_right one_lt_two).mp h
    have hfam : map R.subtype '' higherElemThompsonFamily R j = higherElemThompsonFamily S j := by
      ext A
      constructor
      · rintro ⟨B, hB, rfl⟩
        rw [mem_higherElemThompsonFamily_iff, hRrank] at hB
        obtain ⟨hBe, hBc⟩ := hB
        have := hBe
        rw [mem_higherElemThompsonFamily_iff, card_map_of_injective R.subtype_injective]
        exact ⟨IsElementaryAbelian.map_subtype (p := 2), hBc⟩
      · intro hA
        have hAR : A ≤ R := (le_sSup hA : A ≤ higherElemThompson S j).trans hR
        refine ⟨A.subgroupOf R, ?_, map_subgroupOf_eq_of_le hAR⟩
        obtain ⟨hAe, hAc⟩ := (mem_higherElemThompsonFamily_iff j A).mp hA
        have := hAe
        rw [mem_higherElemThompsonFamily_iff, hRrank,
          Nat.card_congr (subgroupOfEquivOfLe hAR).toEquiv]
        exact ⟨IsElementaryAbelian.subgroupOf (p := 2) hAR, hAc⟩
    have hJ : (higherElemThompson R j).map R.subtype = higherElemThompson S j := by
      rw [higherElemThompson, higherElemThompson, ← hfam, (gc_map_comap R.subtype).l_sSup,
        sSup_image]
    refine ⟨hRrank, hfam, hJ, ?_⟩
    rw [higherElemThompsonOmega, higherElemThompsonOmega, map_subtype_omegaOneCenter, hJ]

end CFSG.Quasithin.SteinbergBK
