module

public import CFSG.RankThree.PartTwo.KFacts.KP2Alternating7
import CFSG.RankThree.PartTwo.Late.Transitivity

public section

namespace CFSG.RankThree.PartTwo.KFacts.KP2

open Equiv Subgroup

private theorem sw_zero_one_conj_eNineF :
    ∀ i j : Fin 3, ∃ k l : Fin 3,
      sw 0 1 * eNineF i j * (sw 0 1)⁻¹ = eNineF k l := by
  decide +kernel

private theorem sw_zero_one_mem_normalizer_eNine :
    sw 0 1 ∈ Subgroup.normalizer (eNine : Set (Perm (Fin 7))) := by
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  apply Subgroup.eq_of_le_of_card_ge
  · rintro _ ⟨x, hx, rfl⟩
    obtain ⟨i, j, rfl⟩ := hx
    obtain ⟨k, l, hkl⟩ := sw_zero_one_conj_eNineF i j
    exact ⟨k, l, by simpa [MulAut.conj_apply] using hkl⟩
  · rw [Subgroup.card_map_of_injective (MulAut.conj (sw 0 1)).injective]

private theorem sign_sw_zero_one : Perm.sign (sw 0 1) = -1 :=
  Perm.sign_swap (by decide)

theorem exists_conj_eq_eNine {P : Subgroup (Perm (Fin 7))} (hP : Nat.card P = 9) :
    ∃ g ∈ alternatingGroup (Fin 7), P.map (MulAut.conj g).toMonoidHom = eNine := by
  have hcardS7 : Nat.card (Perm (Fin 7)) = 5040 := by
    rw [Nat.card_perm, Nat.card_fin]
    norm_num
  have hfact : (Nat.card (Perm (Fin 7))).factorization 3 = 2 := by
    rw [hcardS7]
    decide +kernel
  have hPcard : Nat.card P = 3 ^ (Nat.card (Perm (Fin 7))).factorization 3 := by
    rw [hP, hfact]
    norm_num
  have hEcard : Nat.card eNine = 3 ^ (Nat.card (Perm (Fin 7))).factorization 3 := by
    rw [card_eNine, hfact]
    norm_num
  let P3 : Sylow 3 (Perm (Fin 7)) := Sylow.ofCard P hPcard
  let E3 : Sylow 3 (Perm (Fin 7)) := Sylow.ofCard eNine hEcard
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (Perm (Fin 7)) P3 E3
  have hPcoe : (P3 : Subgroup (Perm (Fin 7))) = P := Sylow.coe_ofCard P hPcard
  have hEcoe : (E3 : Subgroup (Perm (Fin 7))) = eNine := Sylow.coe_ofCard eNine hEcard
  have hmap3 : (E3 : Subgroup (Perm (Fin 7))) =
      (P3 : Subgroup (Perm (Fin 7))).map (MulAut.conj g).toMonoidHom := by
    rw [← hg, Sylow.coe_subgroup_smul, Subgroup.pointwise_smul_def]
    rfl
  have hmap : P.map (MulAut.conj g).toMonoidHom = eNine := by
    rw [hPcoe, hEcoe] at hmap3
    exact hmap3.symm
  have hswmap : eNine.map (MulAut.conj (sw 0 1)).toMonoidHom = eNine :=
    Subgroup.mem_normalizer_iff_map_conj_eq.1 sw_zero_one_mem_normalizer_eNine
  have hcomp : (MulAut.conj (sw 0 1 * g)).toMonoidHom =
      ((MulAut.conj (sw 0 1)).toMonoidHom).comp (MulAut.conj g).toMonoidHom := by
    ext z
    simp [MulAut.conj_apply, mul_assoc]
  have hmap' : P.map (MulAut.conj (sw 0 1 * g)).toMonoidHom = eNine := by
    rw [hcomp, ← Subgroup.map_map, hmap, hswmap]
  by_cases hgA : g ∈ alternatingGroup (Fin 7)
  · exact ⟨g, hgA, hmap⟩
  · refine ⟨sw 0 1 * g, ?_, hmap'⟩
    rw [Perm.mem_alternatingGroup]
    have hgneg : Perm.sign g = -1 := by
      rcases Int.units_eq_one_or (Perm.sign g) with h | h
      · exact absurd (Perm.mem_alternatingGroup.2 h) hgA
      · exact h
    rw [map_mul, sign_sw_zero_one, hgneg, Int.units_mul_self]

private theorem rFour_conj_vTwoF_vOneF :
    ∀ m : Fin 4, ∃ n : Fin 4, rFour * vTwoF n * rFour⁻¹ = vOneF m := by
  decide +kernel

theorem vOne_eq_map_vTwo : vOne = vTwo.map (MulAut.conj rFour).toMonoidHom := by
  apply Subgroup.eq_of_le_of_card_ge
  · rintro _ ⟨m, rfl⟩
    obtain ⟨n, hn⟩ := rFour_conj_vTwoF_vOneF m
    exact ⟨vTwoF n, ⟨n, rfl⟩, by simpa [MulAut.conj_apply] using hn⟩
  · rw [Subgroup.card_map_of_injective (MulAut.conj rFour).injective, card_vTwo, card_vOne]

private theorem eNineF_conj_vOneF :
    ∀ m n : Fin 4, m ≠ 0 → n ≠ 0 →
      ∃ i j : Fin 3, eNineF i j * vOneF m * (eNineF i j)⁻¹ = vOneF n := by
  decide +kernel

private theorem eNineF_conj_vTwoF :
    ∀ m n : Fin 4, m ≠ 0 → n ≠ 0 →
      ∃ i j : Fin 3, eNineF i j * vTwoF m * (eNineF i j)⁻¹ = vTwoF n := by
  decide +kernel

private theorem eq_bot_or_eq_vOne_of_le {V : Subgroup (Perm (Fin 7))} (hV : V ≤ vOne)
    (hN : eNine ≤ Subgroup.normalizer (V : Set (Perm (Fin 7)))) :
    V = ⊥ ∨ V = vOne := by
  by_cases hbot : V = ⊥
  · exact Or.inl hbot
  · right
    have hne : ∃ x ∈ V, x ≠ 1 := by
      by_contra h
      apply hbot
      rw [Subgroup.eq_bot_iff_forall]
      intro y hy
      by_contra hy1
      exact h ⟨y, hy, hy1⟩
    obtain ⟨x, hxV, hx1⟩ := hne
    obtain ⟨m, hm⟩ := hV hxV
    have hm0 : m ≠ 0 := by
      intro hm0
      exact hx1 (hm.trans (by rw [hm0]; rfl))
    have hle : vOne ≤ V := by
      intro y hy
      obtain ⟨n, rfl⟩ := hy
      by_cases hn0 : n = 0
      · rw [hn0]
        exact V.one_mem
      · obtain ⟨i, j, hij⟩ := eNineF_conj_vOneF m n hm0 hn0
        have hmem : eNineF i j * x * (eNineF i j)⁻¹ ∈ V :=
          (Subgroup.mem_normalizer_iff.1 (hN ⟨i, j, rfl⟩) x).1 hxV
        rwa [hm, hij] at hmem
    exact le_antisymm hV hle

private theorem eq_bot_or_eq_vTwo_of_le {V : Subgroup (Perm (Fin 7))} (hV : V ≤ vTwo)
    (hN : eNine ≤ Subgroup.normalizer (V : Set (Perm (Fin 7)))) :
    V = ⊥ ∨ V = vTwo := by
  by_cases hbot : V = ⊥
  · exact Or.inl hbot
  · right
    have hne : ∃ x ∈ V, x ≠ 1 := by
      by_contra h
      apply hbot
      rw [Subgroup.eq_bot_iff_forall]
      intro y hy
      by_contra hy1
      exact h ⟨y, hy, hy1⟩
    obtain ⟨x, hxV, hx1⟩ := hne
    obtain ⟨m, hm⟩ := hV hxV
    have hm0 : m ≠ 0 := by
      intro hm0
      exact hx1 (hm.trans (by rw [hm0]; rfl))
    have hle : vTwo ≤ V := by
      intro y hy
      obtain ⟨n, rfl⟩ := hy
      by_cases hn0 : n = 0
      · rw [hn0]
        exact V.one_mem
      · obtain ⟨i, j, hij⟩ := eNineF_conj_vTwoF m n hm0 hn0
        have hmem : eNineF i j * x * (eNineF i j)⁻¹ ∈ V :=
          (Subgroup.mem_normalizer_iff.1 (hN ⟨i, j, rfl⟩) x).1 hxV
        rwa [hm, hij] at hmem
    exact le_antisymm hV hle

private theorem tInv_mem_normalizer_vOne :
    tInv ∈ Subgroup.normalizer (vOne : Set (Perm (Fin 7))) := by
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  apply Subgroup.eq_of_le_of_card_ge
  · rintro _ ⟨x, hx, rfl⟩
    exact tInv_conj_mem_vOne hx
  · rw [Subgroup.card_map_of_injective (MulAut.conj tInv).injective, card_vOne]

private theorem tInv_mem_normalizer_vTwo :
    tInv ∈ Subgroup.normalizer (vTwo : Set (Perm (Fin 7))) := by
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  apply Subgroup.eq_of_le_of_card_ge
  · rintro _ ⟨x, hx, rfl⟩
    exact tInv_conj_mem_vTwo hx
  · rw [Subgroup.card_map_of_injective (MulAut.conj tInv).injective, card_vTwo]

theorem exists_inv_mem_normalizer {P V : Subgroup (Perm (Fin 7))} (hP : Nat.card P = 9)
    (hV : IsPGroup 2 V) (hPV : P ≤ Subgroup.normalizer (V : Set (Perm (Fin 7)))) :
    ∃ τ ∈ alternatingGroup (Fin 7), (∀ e ∈ P, τ * e * τ⁻¹ = e⁻¹) ∧
      τ ∈ Subgroup.normalizer (V : Set (Perm (Fin 7))) := by
  obtain ⟨g, hgA, hg⟩ := exists_conj_eq_eNine hP
  let V' := V.map (MulAut.conj g).toMonoidHom
  have hV' : IsPGroup 2 V' := hV.map (MulAut.conj g).toMonoidHom
  have h3 : ¬ 3 ∣ Nat.card V' := by
    have hcard : Nat.card V' = Nat.card V :=
      Subgroup.card_map_of_injective (MulAut.conj g).injective
    rw [hcard]
    intro hdiv
    obtain ⟨n, hn⟩ := (IsPGroup.iff_card (p := 2) (G := V)).1 hV
    rw [hn] at hdiv
    have h32 : 3 ∣ 2 := Nat.prime_three.dvd_of_dvd_pow hdiv
    norm_num at h32
  have hN : eNine ≤ Subgroup.normalizer (V' : Set (Perm (Fin 7))) := by
    rw [← hg]
    calc P.map (MulAut.conj g).toMonoidHom
        ≤ (Subgroup.normalizer (V : Set (Perm (Fin 7)))).map
            (MulAut.conj g).toMonoidHom := Subgroup.map_mono hPV
      _ = Subgroup.normalizer (V' : Set (Perm (Fin 7))) :=
          Subgroup.map_equiv_normalizer_eq V (MulAut.conj g)
  have hcases : V' = ⊥ ∨ V' = vOne ∨ V' = vTwo := by
    rcases le_vOne_or_le_vTwo (Q := V') h3 (hN cOne_mem_eNine) (hN cTwo_mem_eNine) with h | h
    · rcases eq_bot_or_eq_vOne_of_le h hN with hbot | hv1
      · exact Or.inl hbot
      · exact Or.inr (Or.inl hv1)
    · rcases eq_bot_or_eq_vTwo_of_le h hN with hbot | hv2
      · exact Or.inl hbot
      · exact Or.inr (Or.inr hv2)
  have ht : tInv ∈ Subgroup.normalizer (V' : Set (Perm (Fin 7))) := by
    rcases hcases with h | h | h
    · rw [h, Subgroup.mem_normalizer_iff_map_conj_eq, Subgroup.map_bot]
    · rw [h]
      exact tInv_mem_normalizer_vOne
    · rw [h]
      exact tInv_mem_normalizer_vTwo
  refine ⟨g⁻¹ * tInv * g, ?_, ?_, ?_⟩
  · change g⁻¹ * tInv * g ∈ alternatingGroup (Fin 7)
    exact (alternatingGroup (Fin 7)).mul_mem
      ((alternatingGroup (Fin 7)).mul_mem ((alternatingGroup (Fin 7)).inv_mem hgA)
        tInv_mem_alternatingGroup) hgA
  · intro e he
    have he' : MulAut.conj g e ∈ eNine := by
      rw [← hg]
      exact ⟨e, he, rfl⟩
    have hstep : tInv * MulAut.conj g e * tInv⁻¹ = (MulAut.conj g e)⁻¹ :=
      tInv_conj_eq_inv he'
    change (g⁻¹ * tInv * g) * e * (g⁻¹ * tInv * g)⁻¹ = e⁻¹
    calc (g⁻¹ * tInv * g) * e * (g⁻¹ * tInv * g)⁻¹
        = g⁻¹ * (tInv * MulAut.conj g e * tInv⁻¹) * g := by
          rw [MulAut.conj_apply]
          group
      _ = g⁻¹ * (MulAut.conj g e)⁻¹ * g := by rw [hstep]
      _ = e⁻¹ := by
          rw [MulAut.conj_apply]
          group
  · have hle : V.map (MulAut.conj (g⁻¹ * tInv * g)).toMonoidHom ≤ V := by
      rintro _ ⟨v, hv, rfl⟩
      have hv' : MulAut.conj g v ∈ V' := ⟨v, hv, rfl⟩
      have ht' : tInv * MulAut.conj g v * tInv⁻¹ ∈ V' :=
        (Subgroup.mem_normalizer_iff.1 ht (MulAut.conj g v)).1 hv'
      obtain ⟨v', hv'V, hv'eq⟩ := Subgroup.mem_map.1 ht'
      have hv'eq' : g * v' * g⁻¹ = tInv * (g * v * g⁻¹) * tInv⁻¹ := by
        simpa [MulAut.conj_apply] using hv'eq
      have hgoal : (MulAut.conj (g⁻¹ * tInv * g)) v = v' := by
        change (g⁻¹ * tInv * g) * v * (g⁻¹ * tInv * g)⁻¹ = v'
        rw [show (g⁻¹ * tInv * g) * v * (g⁻¹ * tInv * g)⁻¹ =
            g⁻¹ * (tInv * (g * v * g⁻¹) * tInv⁻¹) * g by group]
        rw [← hv'eq']
        group
      have hgoal' :
          (MulEquiv.toMonoidHom (MulAut.conj (g⁻¹ * tInv * g))) v = v' := by
        simpa using hgoal
      rw [hgoal']
      exact hv'V
    exact Subgroup.mem_normalizer_iff_map_conj_eq.2
      (Subgroup.eq_of_le_of_card_ge hle (by
        change Nat.card V ≤
          Nat.card (V.map (MulAut.conj (g⁻¹ * tInv * g)).toMonoidHom)
        rw [Subgroup.card_map_of_injective (MulAut.conj (g⁻¹ * tInv * g)).injective]))

private theorem rFour_pow_fix_inv_eNineF :
    ∀ (k : Fin 4) (i j : Fin 3), eNineF i j ≠ 1 →
      (rFour ^ (k : ℕ) * eNineF i j * (rFour ^ (k : ℕ))⁻¹ = eNineF i j → k = 0) ∧
      (rFour ^ (k : ℕ) * eNineF i j * (rFour ^ (k : ℕ))⁻¹ = (eNineF i j)⁻¹ → k = 2) := by
  decide +kernel

private theorem closure_pair_eq_eNine {x y : Perm (Fin 7)} (hx : x ∈ eNine) (hy : y ∈ eNine)
    (hx1 : x ≠ 1) (hyx : y ∉ Subgroup.zpowers x) :
    Subgroup.closure ({x, y} : Set (Perm (Fin 7))) = eNine := by
  set K := Subgroup.closure ({x, y} : Set (Perm (Fin 7))) with hK
  have hKle : K ≤ eNine := by
    rw [hK, Subgroup.closure_le]
    intro z hz
    rcases hz with rfl | rfl
    · exact hx
    · exact hy
  have hxK : x ∈ K := Subgroup.subset_closure (by simp)
  have hyK : y ∈ K := Subgroup.subset_closure (by simp)
  have hlt : Subgroup.zpowers x < K := by
    refine lt_of_le_of_ne (Subgroup.zpowers_le_of_mem hxK) ?_
    intro hEq
    exact hyx (hEq ▸ hyK)
  obtain ⟨i, j, rfl⟩ := hx
  have h3x : orderOf (eNineF i j) = 3 :=
    orderOf_eq_prime (eNineF_pow_three i j) hx1
  have h3 : 3 < Nat.card K := by
    calc 3 = Nat.card (Subgroup.zpowers (eNineF i j)) := by rw [Nat.card_zpowers, h3x]
      _ < Nat.card K := Subgroup.card_lt_of_lt hlt
  have hdvd : Nat.card K ∣ 9 := by
    have := Subgroup.card_dvd_of_le hKle
    simpa [card_eNine] using this
  have hcard : Nat.card K = 9 := by
    have hdvd' : Nat.card K ∣ 3 ^ 2 := by simpa using hdvd
    obtain ⟨k, hk2, hk⟩ := (Nat.dvd_prime_pow Nat.prime_three (m := 2)).1 hdvd'
    interval_cases k
    · rw [hk] at h3
      norm_num at h3
    · rw [hk] at h3
      norm_num at h3
    · simpa using hk
  exact Subgroup.eq_of_le_of_card_ge hKle (by rw [hcard, card_eNine])

private theorem mem_normalizer_eNine_of_fixes_inv {g x y : Perm (Fin 7)} (hx : x ∈ eNine)
    (hy : y ∈ eNine) (hx1 : x ≠ 1) (hyx : y ∉ Subgroup.zpowers x)
    (h1 : g * x * g⁻¹ = x) (h2 : g * y * g⁻¹ = y⁻¹) :
    g ∈ Subgroup.normalizer (eNine : Set (Perm (Fin 7))) := by
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  have hgen := closure_pair_eq_eNine hx hy hx1 hyx
  have himg : MulAut.conj g '' ({x, y} : Set (Perm (Fin 7))) = {x, y⁻¹} := by
    ext z
    simp only [Set.mem_image, Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · rintro ⟨w, hw, hwz⟩
      rcases hw with hwx | hwy
      · subst w
        left
        rw [← hwz, MulAut.conj_apply, h1]
      · subst w
        right
        rw [← hwz, MulAut.conj_apply, h2]
    · intro hz
      rcases hz with hzx | hzy
      · subst z
        exact ⟨x, Or.inl rfl, by rw [MulAut.conj_apply, h1]⟩
      · subst z
        exact ⟨y, Or.inr rfl, by rw [MulAut.conj_apply, h2]⟩
  have hclos : Subgroup.closure ({x, y⁻¹} : Set (Perm (Fin 7))) =
      Subgroup.closure ({x, y} : Set (Perm (Fin 7))) := by
    apply le_antisymm
    · rw [Subgroup.closure_le]
      intro z hz
      rcases hz with hzx | hzy
      · subst z
        exact Subgroup.subset_closure (by simp)
      · subst z
        exact Subgroup.inv_mem _ (Subgroup.subset_closure (by simp))
    · rw [Subgroup.closure_le]
      intro z hz
      rcases hz with hzx | hzy
      · subst z
        exact Subgroup.subset_closure (by simp)
      · subst z
        have hyinv : y⁻¹ ∈ Subgroup.closure ({x, y⁻¹} : Set (Perm (Fin 7))) :=
          Subgroup.subset_closure (by simp)
        simpa using Subgroup.inv_mem _ hyinv
  calc eNine.map (MulAut.conj g).toMonoidHom
      = (Subgroup.closure ({x, y} : Set (Perm (Fin 7)))).map
          (MulAut.conj g).toMonoidHom := by rw [hgen]
    _ = Subgroup.closure (MulAut.conj g '' ({x, y} : Set (Perm (Fin 7)))) :=
        MonoidHom.map_closure _ _
    _ = Subgroup.closure ({x, y⁻¹} : Set (Perm (Fin 7))) := by rw [himg]
    _ = Subgroup.closure ({x, y} : Set (Perm (Fin 7))) := hclos
    _ = eNine := hgen

theorem not_mem_alternatingGroup_of_fix_inv {P : Subgroup (Perm (Fin 7))} (hP : Nat.card P = 9)
    {π e₁ e₂ : Perm (Fin 7)} (he₁ : e₁ ∈ P) (he₂ : e₂ ∈ P) (he₁1 : e₁ ≠ 1)
    (he₂1 : e₂ ∉ Subgroup.zpowers e₁) (h1 : π * e₁ * π⁻¹ = e₁)
    (h2 : π * e₂ * π⁻¹ = e₂⁻¹) : π ∉ alternatingGroup (Fin 7) := by
  intro hπA
  obtain ⟨g, hgA, hg⟩ := exists_conj_eq_eNine hP
  let x := MulAut.conj g e₁
  let y := MulAut.conj g e₂
  let π' := MulAut.conj g π
  have hx : x ∈ eNine := by
    rw [← hg]
    exact ⟨e₁, he₁, rfl⟩
  have hy : y ∈ eNine := by
    rw [← hg]
    exact ⟨e₂, he₂, rfl⟩
  have hx1 : x ≠ 1 := by
    intro h
    apply he₁1
    have h' := congrArg (MulAut.conj g⁻¹) h
    have h'' : g⁻¹ * (g * e₁ * g⁻¹) * g = 1 := by
      simpa [x, MulAut.conj_apply] using h'
    calc e₁ = g⁻¹ * (g * e₁ * g⁻¹) * g := by group
      _ = 1 := h''
  have hyx : y ∉ Subgroup.zpowers x := by
    intro h
    apply he₂1
    have hmap : y ∈ (Subgroup.zpowers e₁).map (MulAut.conj g).toMonoidHom := by
      rw [MonoidHom.map_zpowers]
      exact h
    obtain ⟨z, hz, hzg⟩ := Subgroup.mem_map.1 hmap
    exact (MulAut.conj g).injective hzg ▸ hz
  have hfix : π' * x * π'⁻¹ = x := by
    change (g * π * g⁻¹) * (g * e₁ * g⁻¹) * (g * π * g⁻¹)⁻¹ = g * e₁ * g⁻¹
    rw [show (g * π * g⁻¹) * (g * e₁ * g⁻¹) * (g * π * g⁻¹)⁻¹ =
        g * (π * e₁ * π⁻¹) * g⁻¹ by group, h1]
  have hinv : π' * y * π'⁻¹ = y⁻¹ := by
    change (g * π * g⁻¹) * (g * e₂ * g⁻¹) * (g * π * g⁻¹)⁻¹ = (g * e₂ * g⁻¹)⁻¹
    rw [show (g * π * g⁻¹) * (g * e₂ * g⁻¹) * (g * π * g⁻¹)⁻¹ =
        g * (π * e₂ * π⁻¹) * g⁻¹ by group, h2]
    group
  have hπ'A : π' ∈ alternatingGroup (Fin 7) := by
    change g * π * g⁻¹ ∈ alternatingGroup (Fin 7)
    exact (alternatingGroup (Fin 7)).mul_mem
      ((alternatingGroup (Fin 7)).mul_mem hgA hπA)
      ((alternatingGroup (Fin 7)).inv_mem hgA)
  have hπ'N : π' ∈ Subgroup.normalizer (eNine : Set (Perm (Fin 7))) :=
    mem_normalizer_eNine_of_fixes_inv hx hy hx1 hyx hfix hinv
  obtain ⟨k, i, j, hk⟩ := exists_rFour_pow_of_mem_normalizer hπ'N hπ'A
  obtain ⟨a, b, hxeq⟩ := hx
  obtain ⟨c, d, hyeq⟩ := hy
  have hx1' : eNineF a b ≠ 1 := by
    rw [← hxeq]
    exact hx1
  have hy1' : eNineF c d ≠ 1 := by
    intro h
    exact hyx (by rw [hxeq, hyeq, h]; exact Subgroup.one_mem _)
  have hfix_r : rFour ^ (k : ℕ) * eNineF a b * (rFour ^ (k : ℕ))⁻¹ = eNineF a b := by
    have hconj : (rFour ^ (k : ℕ) * eNineF i j) * eNineF a b *
        (rFour ^ (k : ℕ) * eNineF i j)⁻¹ = eNineF a b := by
      rw [← hk, ← hxeq]
      exact hfix
    have hcomm : eNineF i j * eNineF a b = eNineF a b * eNineF i j :=
      eNineF_comm i j a b
    have hex : eNineF i j * eNineF a b * (eNineF i j)⁻¹ = eNineF a b := by
      rw [hcomm]
      group
    have heq : (rFour ^ (k : ℕ) * eNineF i j) * eNineF a b *
        (rFour ^ (k : ℕ) * eNineF i j)⁻¹ =
        rFour ^ (k : ℕ) * eNineF a b * (rFour ^ (k : ℕ))⁻¹ := by
      calc (rFour ^ (k : ℕ) * eNineF i j) * eNineF a b *
            (rFour ^ (k : ℕ) * eNineF i j)⁻¹
          = rFour ^ (k : ℕ) * (eNineF i j * eNineF a b * (eNineF i j)⁻¹) *
              (rFour ^ (k : ℕ))⁻¹ := by group
        _ = rFour ^ (k : ℕ) * eNineF a b * (rFour ^ (k : ℕ))⁻¹ := by rw [hex]
    rw [heq] at hconj
    exact hconj
  have hinv_r : rFour ^ (k : ℕ) * eNineF c d * (rFour ^ (k : ℕ))⁻¹ = (eNineF c d)⁻¹ := by
    have hconj : (rFour ^ (k : ℕ) * eNineF i j) * eNineF c d *
        (rFour ^ (k : ℕ) * eNineF i j)⁻¹ = (eNineF c d)⁻¹ := by
      rw [← hk, ← hyeq]
      exact hinv
    have hcomm : eNineF i j * eNineF c d = eNineF c d * eNineF i j :=
      eNineF_comm i j c d
    have hex : eNineF i j * eNineF c d * (eNineF i j)⁻¹ = eNineF c d := by
      rw [hcomm]
      group
    have heq : (rFour ^ (k : ℕ) * eNineF i j) * eNineF c d *
        (rFour ^ (k : ℕ) * eNineF i j)⁻¹ =
        rFour ^ (k : ℕ) * eNineF c d * (rFour ^ (k : ℕ))⁻¹ := by
      calc (rFour ^ (k : ℕ) * eNineF i j) * eNineF c d *
            (rFour ^ (k : ℕ) * eNineF i j)⁻¹
          = rFour ^ (k : ℕ) * (eNineF i j * eNineF c d * (eNineF i j)⁻¹) *
              (rFour ^ (k : ℕ))⁻¹ := by group
        _ = rFour ^ (k : ℕ) * eNineF c d * (rFour ^ (k : ℕ))⁻¹ := by rw [hex]
    rw [heq] at hconj
    exact hconj
  obtain ⟨hk0, -⟩ := rFour_pow_fix_inv_eNineF k a b hx1'
  obtain ⟨-, hk2⟩ := rFour_pow_fix_inv_eNineF k c d hy1'
  exact absurd ((hk0 hfix_r).symm.trans (hk2 hinv_r)) (by decide)

private theorem rFour_swap_eigenlines_left :
    ∀ (d : Fin 8) (a b c e : Fin 3), eNineF a b ≠ 1 → eNineF c e ≠ 1 →
      autRep d * eNineF a b * (autRep d)⁻¹ = eNineF a b →
      autRep d * eNineF c e * (autRep d)⁻¹ = (eNineF c e)⁻¹ →
      (rFour * eNineF a b * rFour⁻¹ = 1 ∨
        rFour * eNineF a b * rFour⁻¹ = eNineF c e ∨
        rFour * eNineF a b * rFour⁻¹ = (eNineF c e) ^ 2) := by
  decide +kernel

private theorem rFour_swap_eigenlines_right :
    ∀ (d : Fin 8) (a b c e : Fin 3), eNineF a b ≠ 1 → eNineF c e ≠ 1 →
      autRep d * eNineF a b * (autRep d)⁻¹ = eNineF a b →
      autRep d * eNineF c e * (autRep d)⁻¹ = (eNineF c e)⁻¹ →
      (rFour * eNineF c e * rFour⁻¹ = 1 ∨
        rFour * eNineF c e * rFour⁻¹ = eNineF a b ∨
        rFour * eNineF c e * rFour⁻¹ = (eNineF a b) ^ 2) := by
  decide +kernel

theorem exists_swap_of_fix_inv {P : Subgroup (Perm (Fin 7))} (hP : Nat.card P = 9)
    {π e₁ e₂ : Perm (Fin 7)} (he₁ : e₁ ∈ P) (he₂ : e₂ ∈ P) (he₁1 : e₁ ≠ 1)
    (he₂1 : e₂ ∉ Subgroup.zpowers e₁) (h1 : π * e₁ * π⁻¹ = e₁)
    (h2 : π * e₂ * π⁻¹ = e₂⁻¹) :
    ∃ r ∈ alternatingGroup (Fin 7), r * e₁ * r⁻¹ ∈ Subgroup.zpowers e₂ ∧
      r * e₂ * r⁻¹ ∈ Subgroup.zpowers e₁ ∧ ∀ e ∈ P, r ^ 2 * e * (r ^ 2)⁻¹ = e⁻¹ := by
  obtain ⟨g, hgA, hg⟩ := exists_conj_eq_eNine hP
  let x := MulAut.conj g e₁
  let y := MulAut.conj g e₂
  let π' := MulAut.conj g π
  have hx : x ∈ eNine := by
    rw [← hg]
    exact ⟨e₁, he₁, rfl⟩
  have hy : y ∈ eNine := by
    rw [← hg]
    exact ⟨e₂, he₂, rfl⟩
  have hx1 : x ≠ 1 := by
    intro h
    apply he₁1
    have h' := congrArg (MulAut.conj g⁻¹) h
    have h'' : g⁻¹ * (g * e₁ * g⁻¹) * g = 1 := by
      simpa [x, MulAut.conj_apply] using h'
    calc e₁ = g⁻¹ * (g * e₁ * g⁻¹) * g := by group
      _ = 1 := h''
  have hyx : y ∉ Subgroup.zpowers x := by
    intro h
    apply he₂1
    have hmap : y ∈ (Subgroup.zpowers e₁).map (MulAut.conj g).toMonoidHom := by
      rw [MonoidHom.map_zpowers]
      exact h
    obtain ⟨z, hz, hzg⟩ := Subgroup.mem_map.1 hmap
    exact (MulAut.conj g).injective hzg ▸ hz
  have hfix : π' * x * π'⁻¹ = x := by
    change (g * π * g⁻¹) * (g * e₁ * g⁻¹) * (g * π * g⁻¹)⁻¹ = g * e₁ * g⁻¹
    rw [show (g * π * g⁻¹) * (g * e₁ * g⁻¹) * (g * π * g⁻¹)⁻¹ =
        g * (π * e₁ * π⁻¹) * g⁻¹ by group, h1]
  have hinv : π' * y * π'⁻¹ = y⁻¹ := by
    change (g * π * g⁻¹) * (g * e₂ * g⁻¹) * (g * π * g⁻¹)⁻¹ = (g * e₂ * g⁻¹)⁻¹
    rw [show (g * π * g⁻¹) * (g * e₂ * g⁻¹) * (g * π * g⁻¹)⁻¹ =
        g * (π * e₂ * π⁻¹) * g⁻¹ by group, h2]
    group
  have hπ'N : π' ∈ Subgroup.normalizer (eNine : Set (Perm (Fin 7))) :=
    mem_normalizer_eNine_of_fixes_inv hx hy hx1 hyx hfix hinv
  obtain ⟨d, i, j, hd⟩ := exists_autRep_of_mem_normalizer hπ'N
  obtain ⟨a, b, hxeq⟩ := hx
  obtain ⟨c, e, hyeq⟩ := hy
  have hx1' : eNineF a b ≠ 1 := by
    rw [← hxeq]
    exact hx1
  have hy1' : eNineF c e ≠ 1 := by
    intro h
    exact hyx (by rw [hxeq, hyeq, h]; exact Subgroup.one_mem _)
  have hAx : autRep d * eNineF a b * (autRep d)⁻¹ = eNineF a b := by
    have hconj : (autRep d * eNineF i j) * eNineF a b *
        (autRep d * eNineF i j)⁻¹ = eNineF a b := by
      rw [← hd, ← hxeq]
      exact hfix
    have hcomm : eNineF i j * eNineF a b = eNineF a b * eNineF i j :=
      eNineF_comm i j a b
    have hex : eNineF i j * eNineF a b * (eNineF i j)⁻¹ = eNineF a b := by
      rw [hcomm]
      group
    have heq : (autRep d * eNineF i j) * eNineF a b *
        (autRep d * eNineF i j)⁻¹ =
        autRep d * eNineF a b * (autRep d)⁻¹ := by
      calc (autRep d * eNineF i j) * eNineF a b *
            (autRep d * eNineF i j)⁻¹
          = autRep d * (eNineF i j * eNineF a b * (eNineF i j)⁻¹) *
              (autRep d)⁻¹ := by group
        _ = autRep d * eNineF a b * (autRep d)⁻¹ := by rw [hex]
    rw [heq] at hconj
    exact hconj
  have hAy : autRep d * eNineF c e * (autRep d)⁻¹ = (eNineF c e)⁻¹ := by
    have hconj : (autRep d * eNineF i j) * eNineF c e *
        (autRep d * eNineF i j)⁻¹ = (eNineF c e)⁻¹ := by
      rw [← hd, ← hyeq]
      exact hinv
    have hcomm : eNineF i j * eNineF c e = eNineF c e * eNineF i j :=
      eNineF_comm i j c e
    have hex : eNineF i j * eNineF c e * (eNineF i j)⁻¹ = eNineF c e := by
      rw [hcomm]
      group
    have heq : (autRep d * eNineF i j) * eNineF c e *
        (autRep d * eNineF i j)⁻¹ =
        autRep d * eNineF c e * (autRep d)⁻¹ := by
      calc (autRep d * eNineF i j) * eNineF c e *
            (autRep d * eNineF i j)⁻¹
          = autRep d * (eNineF i j * eNineF c e * (eNineF i j)⁻¹) *
              (autRep d)⁻¹ := by group
        _ = autRep d * eNineF c e * (autRep d)⁻¹ := by rw [hex]
    rw [heq] at hconj
    exact hconj
  have hu := rFour_swap_eigenlines_left d a b c e hx1' hy1' hAx hAy
  have hv := rFour_swap_eigenlines_right d a b c e hx1' hy1' hAx hAy
  have hu' : ∃ u : Fin 3, rFour * eNineF a b * rFour⁻¹ = (eNineF c e) ^ (u : ℕ) := by
    rcases hu with h | h | h
    · exact ⟨0, by simpa using h⟩
    · exact ⟨1, by simpa using h⟩
    · exact ⟨2, by simpa using h⟩
  have hv' : ∃ v : Fin 3, rFour * eNineF c e * rFour⁻¹ = (eNineF a b) ^ (v : ℕ) := by
    rcases hv with h | h | h
    · exact ⟨0, by simpa using h⟩
    · exact ⟨1, by simpa using h⟩
    · exact ⟨2, by simpa using h⟩
  obtain ⟨u, hu⟩ := hu'
  obtain ⟨v, hv⟩ := hv'
  let r := g⁻¹ * rFour * g
  have hrA : r ∈ alternatingGroup (Fin 7) := by
    change g⁻¹ * rFour * g ∈ alternatingGroup (Fin 7)
    exact (alternatingGroup (Fin 7)).mul_mem
      ((alternatingGroup (Fin 7)).mul_mem ((alternatingGroup (Fin 7)).inv_mem hgA)
        rFour_spec.1) hgA
  have hr1 : r * e₁ * r⁻¹ ∈ Subgroup.zpowers e₂ := by
    have hxeq' : g * e₁ * g⁻¹ = eNineF a b := by simpa [x] using hxeq
    have hyeq' : g * e₂ * g⁻¹ = eNineF c e := by simpa [y] using hyeq
    have hpow : g⁻¹ * (eNineF c e) ^ (u : ℕ) * g = e₂ ^ (u : ℕ) := by
      have hconj : MulAut.conj g⁻¹ ((eNineF c e) ^ (u : ℕ)) = e₂ ^ (u : ℕ) := by
        rw [map_pow]
        have hsingle : MulAut.conj g⁻¹ (eNineF c e) = e₂ := by
          rw [← hyeq', MulAut.conj_apply]
          group
        rw [hsingle]
      simpa [MulAut.conj_apply] using hconj
    have heq : r * e₁ * r⁻¹ = e₂ ^ (u : ℕ) := by
      calc r * e₁ * r⁻¹
          = g⁻¹ * (rFour * (g * e₁ * g⁻¹) * rFour⁻¹) * g := by
            change (g⁻¹ * rFour * g) * e₁ * (g⁻¹ * rFour * g)⁻¹ =
              g⁻¹ * (rFour * (g * e₁ * g⁻¹) * rFour⁻¹) * g
            group
        _ = g⁻¹ * (rFour * eNineF a b * rFour⁻¹) * g := by rw [hxeq']
        _ = g⁻¹ * (eNineF c e) ^ (u : ℕ) * g := by rw [hu]
        _ = e₂ ^ (u : ℕ) := hpow
    rw [heq]
    exact Subgroup.npow_mem_zpowers e₂ (u : ℕ)
  have hr2 : r * e₂ * r⁻¹ ∈ Subgroup.zpowers e₁ := by
    have hxeq' : g * e₁ * g⁻¹ = eNineF a b := by simpa [x] using hxeq
    have hyeq' : g * e₂ * g⁻¹ = eNineF c e := by simpa [y] using hyeq
    have hpow : g⁻¹ * (eNineF a b) ^ (v : ℕ) * g = e₁ ^ (v : ℕ) := by
      have hconj : MulAut.conj g⁻¹ ((eNineF a b) ^ (v : ℕ)) = e₁ ^ (v : ℕ) := by
        rw [map_pow]
        have hsingle : MulAut.conj g⁻¹ (eNineF a b) = e₁ := by
          rw [← hxeq', MulAut.conj_apply]
          group
        rw [hsingle]
      simpa [MulAut.conj_apply] using hconj
    have heq : r * e₂ * r⁻¹ = e₁ ^ (v : ℕ) := by
      calc r * e₂ * r⁻¹
          = g⁻¹ * (rFour * (g * e₂ * g⁻¹) * rFour⁻¹) * g := by
            change (g⁻¹ * rFour * g) * e₂ * (g⁻¹ * rFour * g)⁻¹ =
              g⁻¹ * (rFour * (g * e₂ * g⁻¹) * rFour⁻¹) * g
            group
        _ = g⁻¹ * (rFour * eNineF c e * rFour⁻¹) * g := by rw [hyeq']
        _ = g⁻¹ * (eNineF a b) ^ (v : ℕ) * g := by rw [hv]
        _ = e₁ ^ (v : ℕ) := hpow
    rw [heq]
    exact Subgroup.npow_mem_zpowers e₁ (v : ℕ)
  have hr2eq : r ^ 2 = g⁻¹ * tInv * g := by
    change (g⁻¹ * rFour * g) ^ 2 = g⁻¹ * tInv * g
    rw [show g⁻¹ * rFour * g = MulAut.conj g⁻¹ rFour by
      rw [MulAut.conj_apply]
      group]
    rw [← map_pow, rFour_spec.2.2.2.1, MulAut.conj_apply]
    group
  refine ⟨r, hrA, hr1, hr2, ?_⟩
  intro e he
  have he' : MulAut.conj g e ∈ eNine := by
    rw [← hg]
    exact ⟨e, he, rfl⟩
  have hstep : tInv * MulAut.conj g e * tInv⁻¹ = (MulAut.conj g e)⁻¹ :=
    tInv_conj_eq_inv he'
  change r ^ 2 * e * (r ^ 2)⁻¹ = e⁻¹
  rw [hr2eq]
  change (g⁻¹ * tInv * g) * e * (g⁻¹ * tInv * g)⁻¹ = e⁻¹
  calc (g⁻¹ * tInv * g) * e * (g⁻¹ * tInv * g)⁻¹
      = g⁻¹ * (tInv * MulAut.conj g e * tInv⁻¹) * g := by
        rw [MulAut.conj_apply]
        group
    _ = g⁻¹ * (MulAut.conj g e)⁻¹ * g := by rw [hstep]
    _ = e⁻¹ := by
        rw [MulAut.conj_apply]
        group

private theorem eNine_conj_vTwoF :
    ∀ (i j : Fin 3) (m : Fin 4), ∃ n : Fin 4,
      eNineF i j * vTwoF m * (eNineF i j)⁻¹ = vTwoF n := by
  decide +kernel

private theorem cOne_conj_vTwoF (m : Fin 4) :
    ∃ n : Fin 4, cOne * vTwoF m * cOne⁻¹ = vTwoF n := by
  obtain ⟨n, hn⟩ := eNine_conj_vTwoF 1 0 m
  exact ⟨n, by simpa [eNineF] using hn⟩

private theorem cTwo_conj_vTwoF (m : Fin 4) :
    ∃ n : Fin 4, cTwo * vTwoF m * cTwo⁻¹ = vTwoF n := by
  obtain ⟨n, hn⟩ := eNine_conj_vTwoF 0 1 m
  exact ⟨n, by simpa [eNineF] using hn⟩

private theorem cOne_mem_normalizer_vTwo :
    cOne ∈ Subgroup.normalizer (vTwo : Set (Perm (Fin 7))) := by
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  apply Subgroup.eq_of_le_of_card_ge
  · rintro _ ⟨x, hx, rfl⟩
    obtain ⟨m, rfl⟩ := hx
    obtain ⟨n, hn⟩ := cOne_conj_vTwoF m
    exact ⟨n, by simpa [MulAut.conj_apply] using hn⟩
  · rw [Subgroup.card_map_of_injective (MulAut.conj cOne).injective, card_vTwo]

private theorem cTwo_mem_normalizer_vTwo :
    cTwo ∈ Subgroup.normalizer (vTwo : Set (Perm (Fin 7))) := by
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  apply Subgroup.eq_of_le_of_card_ge
  · rintro _ ⟨x, hx, rfl⟩
    obtain ⟨m, rfl⟩ := hx
    obtain ⟨n, hn⟩ := cTwo_conj_vTwoF m
    exact ⟨n, by simpa [MulAut.conj_apply] using hn⟩
  · rw [Subgroup.card_map_of_injective (MulAut.conj cTwo).injective, card_vTwo]

private theorem eNine_le_normalizer_vTwo :
    eNine ≤ Subgroup.normalizer (vTwo : Set (Perm (Fin 7))) := by
  rintro _ ⟨i, j, rfl⟩
  exact Subgroup.mul_mem _ (Subgroup.pow_mem _ cOne_mem_normalizer_vTwo i)
    (Subgroup.pow_mem _ cTwo_mem_normalizer_vTwo j)

theorem eq_bot_or_eq_map_vTwo {P Q : Subgroup (Perm (Fin 7))} (hP : Nat.card P = 9)
    (hQ : IsPGroup 2 Q) (hPQ : P ≤ Subgroup.normalizer (Q : Set (Perm (Fin 7)))) :
    Q = ⊥ ∨ ∃ g : Perm (Fin 7), Q = vTwo.map (MulAut.conj g).toMonoidHom := by
  obtain ⟨g, -, hg⟩ := exists_conj_eq_eNine hP
  let Q' := Q.map (MulAut.conj g).toMonoidHom
  have hQ' : IsPGroup 2 Q' := hQ.map (MulAut.conj g).toMonoidHom
  have h3 : ¬ 3 ∣ Nat.card Q' := by
    have hcard : Nat.card Q' = Nat.card Q :=
      Subgroup.card_map_of_injective (MulAut.conj g).injective
    rw [hcard]
    intro hdiv
    obtain ⟨n, hn⟩ := (IsPGroup.iff_card (p := 2) (G := Q)).1 hQ
    rw [hn] at hdiv
    have h32 : 3 ∣ 2 := Nat.prime_three.dvd_of_dvd_pow hdiv
    norm_num at h32
  have hN : eNine ≤ Subgroup.normalizer (Q' : Set (Perm (Fin 7))) := by
    rw [← hg]
    calc P.map (MulAut.conj g).toMonoidHom
        ≤ (Subgroup.normalizer (Q : Set (Perm (Fin 7)))).map
            (MulAut.conj g).toMonoidHom := Subgroup.map_mono hPQ
      _ = Subgroup.normalizer (Q' : Set (Perm (Fin 7))) :=
          Subgroup.map_equiv_normalizer_eq Q (MulAut.conj g)
  have hQQ' : Q = Q'.map (MulAut.conj g⁻¹).toMonoidHom := by
    dsimp only [Q']
    rw [CFSG.RankThree.PartTwo.Late.map_conj_map_conj, inv_mul_cancel,
      CFSG.RankThree.PartTwo.Late.map_conj_one]
  rcases le_vOne_or_le_vTwo (Q := Q') h3 (hN cOne_mem_eNine) (hN cTwo_mem_eNine) with h1 | h2
  · rcases eq_bot_or_eq_vOne_of_le h1 hN with hbot | hv1
    · left
      rw [hQQ', hbot, Subgroup.map_bot]
    · right
      exact ⟨g⁻¹ * rFour, by rw [hQQ', hv1, vOne_eq_map_vTwo, map_conj_map_conj]⟩
  · rcases eq_bot_or_eq_vTwo_of_le h2 hN with hbot | hv2
    · left
      rw [hQQ', hbot, Subgroup.map_bot]
    · right
      exact ⟨g⁻¹, by rw [hQQ', hv2]⟩

theorem exists_le_normalizer_map_vTwo {P : Subgroup (Perm (Fin 7))} (hP : Nat.card P = 9) :
    ∃ g : Perm (Fin 7), P ≤ Subgroup.normalizer
      ((vTwo.map (MulAut.conj g).toMonoidHom : Subgroup (Perm (Fin 7))) : Set (Perm (Fin 7))) := by
  obtain ⟨g, -, hg⟩ := exists_conj_eq_eNine hP
  refine ⟨g⁻¹, ?_⟩
  have h := Subgroup.map_mono (f := (MulAut.conj g⁻¹).toMonoidHom) eNine_le_normalizer_vTwo
  rw [Subgroup.map_equiv_normalizer_eq] at h
  rw [← hg] at h
  rw [CFSG.RankThree.PartTwo.Late.map_conj_map_conj, inv_mul_cancel,
    CFSG.RankThree.PartTwo.Late.map_conj_one] at h
  exact h

theorem card_map_vTwo (g : Perm (Fin 7)) :
    Nat.card (vTwo.map (MulAut.conj g).toMonoidHom) = 4 := by
  rw [Subgroup.card_map_of_injective (MulAut.conj g).injective, card_vTwo]

theorem map_vTwo_le_alternatingGroup (g : Perm (Fin 7)) :
    vTwo.map (MulAut.conj g).toMonoidHom ≤ alternatingGroup (Fin 7) := by
  rintro _ ⟨v, hv, rfl⟩
  exact (inferInstance : (alternatingGroup (Fin 7)).Normal).conj_mem v
    ((vTwo_le_centTwo.trans inf_le_right) hv) g

end CFSG.RankThree.PartTwo.KFacts.KP2
