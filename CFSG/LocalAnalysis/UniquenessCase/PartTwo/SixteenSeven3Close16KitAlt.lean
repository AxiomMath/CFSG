module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSeven3Close16Alt
public import CFSG.Sporadic.Suz.Simple

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {G : Type} [Group G] [Finite G]
variable {D : Data G} {V L : Subgroup G} {hV : IsElemAbelian 2 V}

private theorem exists_three_normalizer_alt_eight
    {B : Subgroup (alternatingGroup (Fin 8))} (hB : Nat.card B = 7) :
    ∃ y : alternatingGroup (Fin 8), orderOf y = 3 ∧
      y ∈ normalizer (B : Set (alternatingGroup (Fin 8))) ∧
      ∃ a ∈ B, y * a * y⁻¹ ≠ a := by
  have hB_ne_bot : B ≠ ⊥ := by
    intro h
    rw [Subgroup.eq_bot_iff_card] at h
    rw [hB] at h
    norm_num at h
  obtain ⟨a, ha1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hB_ne_bot
  let c : alternatingGroup (Fin 8) := a
  have hcB : c ∈ B := a.2
  have hc7 : orderOf c = 7 := by
    have hdvd : orderOf (a : alternatingGroup (Fin 8)) ∣ 7 := by
      simpa [hB] using Subgroup.orderOf_dvd_natCard B a.2
    have hne : orderOf (a : alternatingGroup (Fin 8)) ≠ 1 := by
      intro h
      exact ha1 (Subtype.ext (orderOf_eq_one_iff.mp h))
    rcases (by norm_num : Nat.Prime 7).eq_one_or_self_of_dvd _ hdvd with h | h
    · exact absurd h hne
    · exact h
  let cp : Equiv.Perm (Fin 8) := (c : Equiv.Perm (Fin 8))
  have hcp7 : orderOf cp = 7 := (Subgroup.orderOf_coe c).trans hc7
  have hcyc : cp.cycleType = ({7} : Multiset ℕ) := by
    have hall : ∀ n ∈ cp.cycleType, n = 7 := by
      intro n hn
      have h2 : 2 ≤ n := Equiv.Perm.two_le_of_mem_cycleType hn
      have hdvd : n ∣ 7 := by
        simpa [hcp7] using Equiv.Perm.dvd_of_mem_cycleType hn
      rcases (by norm_num : Nat.Prime 7).eq_one_or_self_of_dvd n hdvd with h1 | h7
      · omega
      · exact h7
    have hrep : cp.cycleType = Multiset.replicate cp.cycleType.card 7 :=
      Multiset.eq_replicate_card.mpr hall
    have hcp_ne_one : cp ≠ 1 := by
      intro h
      rw [h, orderOf_one] at hcp7
      norm_num at hcp7
    have hcard_ge : 1 ≤ cp.cycleType.card :=
      Nat.one_le_iff_ne_zero.mpr (Equiv.Perm.card_cycleType_eq_zero.not.mpr hcp_ne_one)
    have hsum_le : cp.cycleType.card * 7 ≤ 8 := by
      have h := Equiv.Perm.sum_cycleType cp
      rw [hrep, Multiset.sum_replicate] at h
      have h' : cp.cycleType.card * 7 = cp.support.card := by simpa using h
      rw [h']
      simpa using Finset.card_le_univ cp.support
    have hcard1 : cp.cycleType.card = 1 := by omega
    rw [hcard1] at hrep
    simpa using hrep
  let c0 : Equiv.Perm (Fin 8) := Fin.cycleRange (6 : Fin 8)
  have hc0 : c0.cycleType = ({7} : Multiset ℕ) := by
    have := Fin.cycleType_cycleRange (n := 8) (i := (6 : Fin 8)) (by decide)
    simpa [c0] using this
  have hconj : IsConj cp c0 :=
    Equiv.Perm.isConj_iff_cycleType_eq.mpr (hcyc.trans hc0.symm)
  obtain ⟨σ, hσ⟩ := isConj_iff.mp hconj
  let y0 : Equiv.Perm (Fin 8) :=
    Equiv.swap (1 : Fin 8) (2 : Fin 8) * Equiv.swap (2 : Fin 8) (4 : Fin 8) *
      (Equiv.swap (3 : Fin 8) (6 : Fin 8) * Equiv.swap (6 : Fin 8) (5 : Fin 8))
  have hy0conj' : y0 * c0 = c0 ^ 2 * y0 := by
    ext i
    fin_cases i <;> decide
  have hy0conj : y0 * c0 * y0⁻¹ = c0 ^ 2 := by
    rw [hy0conj', mul_assoc, mul_inv_cancel, mul_one]
  have hy0pow : y0 ^ 3 = 1 := by
    ext i
    fin_cases i <;> decide
  have hy0ne : y0 ≠ 1 := by
    intro h
    have h1 : y0 (1 : Fin 8) = (1 : Equiv.Perm (Fin 8)) (1 : Fin 8) :=
      congrArg (fun f : Equiv.Perm (Fin 8) => f (1 : Fin 8)) h
    rw [show (1 : Equiv.Perm (Fin 8)) (1 : Fin 8) = (1 : Fin 8) from rfl] at h1
    rw [show y0 (1 : Fin 8) = (2 : Fin 8) by decide] at h1
    exact (by decide : (2 : Fin 8) ≠ (1 : Fin 8)) h1
  have hy0order : orderOf y0 = 3 := orderOf_eq_prime hy0pow hy0ne
  have hy0_mem : y0 ∈ alternatingGroup (Fin 8) := by
    have h12 : (Equiv.swap (1 : Fin 8) (2 : Fin 8)).IsSwap := ⟨1, 2, by decide, rfl⟩
    have h24 : (Equiv.swap (2 : Fin 8) (4 : Fin 8)).IsSwap := ⟨2, 4, by decide, rfl⟩
    have h36 : (Equiv.swap (3 : Fin 8) (6 : Fin 8)).IsSwap := ⟨3, 6, by decide, rfl⟩
    have h65 : (Equiv.swap (6 : Fin 8) (5 : Fin 8)).IsSwap := ⟨6, 5, by decide, rfl⟩
    simpa [y0] using (alternatingGroup (Fin 8)).mul_mem
      (Equiv.Perm.mul_mem_alternatingGroup_of_isSwap h12 h24)
      (Equiv.Perm.mul_mem_alternatingGroup_of_isSwap h36 h65)
  let yperm : Equiv.Perm (Fin 8) := σ⁻¹ * y0 * σ
  have hyperm_mem : yperm ∈ alternatingGroup (Fin 8) := by
    have hN : (alternatingGroup (Fin 8)).Normal := alternatingGroup.normal
    have h := hN.conj_mem y0 hy0_mem σ⁻¹
    simpa [yperm] using h
  let y : alternatingGroup (Fin 8) := ⟨yperm, hyperm_mem⟩
  have hsemiconj : SemiconjBy σ⁻¹ y0 yperm := by
    simp only [SemiconjBy, yperm]
    group
  have horder_perm : orderOf yperm = 3 :=
    (SemiconjBy.orderOf_eq σ⁻¹ hsemiconj).symm.trans hy0order
  have horder_y : orderOf y = 3 :=
    (Subgroup.orderOf_mk yperm hyperm_mem).trans horder_perm
  have hcp_eq : cp = σ⁻¹ * c0 * σ := by
    calc cp = σ⁻¹ * (σ * cp * σ⁻¹) * σ := by group
      _ = σ⁻¹ * c0 * σ := by rw [hσ]
  have hyperm_conj : yperm * cp * yperm⁻¹ = cp ^ 2 := by
    rw [hcp_eq, show yperm = σ⁻¹ * y0 * σ from rfl]
    calc σ⁻¹ * y0 * σ * (σ⁻¹ * c0 * σ) * (σ⁻¹ * y0 * σ)⁻¹
        = σ⁻¹ * (y0 * c0 * y0⁻¹) * σ := by group
      _ = σ⁻¹ * c0 ^ 2 * σ := by rw [hy0conj]
      _ = (σ⁻¹ * c0 * σ) ^ 2 := by
        simp only [pow_two]
        group
  have hyc : y * c * y⁻¹ = c ^ 2 := by
    apply Subtype.ext
    simpa [y, c, yperm, cp] using hyperm_conj
  have hB_eq : B = Subgroup.zpowers c := by
    refine (Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hcB) ?_).symm
    rw [Nat.card_zpowers, hc7, hB]
  have hmap_le : B.map (MulAut.conj y) ≤ B := by
    rw [hB_eq]
    change (Subgroup.zpowers c).map (MulAut.conj y).toMonoidHom ≤ Subgroup.zpowers c
    rw [MonoidHom.map_zpowers]
    refine Subgroup.zpowers_le.mpr ?_
    change (MulAut.conj y) c ∈ Subgroup.zpowers c
    rw [MulAut.conj_apply, hyc]
    exact Subgroup.npow_mem_zpowers c 2
  have hmap_eq : B.map (MulAut.conj y) = B := by
    refine Subgroup.eq_of_le_of_card_ge hmap_le ?_
    rw [Subgroup.card_map_of_injective (MulAut.conj y).injective, hB]
  have hy_normalizer : y ∈ normalizer (B : Set (alternatingGroup (Fin 8))) :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mpr hmap_eq
  refine ⟨y, horder_y, hy_normalizer, c, hcB, ?_⟩
  intro h
  have h2 : c ^ 2 = c := by
    rw [← hyc]
    exact h
  have hc1 : c = 1 := by
    have h3 : c ^ 2 * c⁻¹ = c * c⁻¹ := by rw [h2]
    simpa [pow_two, mul_assoc] using h3
  exact absurd hc7 (by rw [hc1, orderOf_one]; norm_num)

theorem close16_alt_eight_normalizer_three {X : Type} [Group X] (hX : IsAlt X 8)
    {B : Subgroup X} (hB : Nat.card B = 7) :
    ∃ y : X, orderOf y = 3 ∧ y ∈ normalizer (B : Set X) ∧ ∃ a ∈ B, y * a * y⁻¹ ≠ a := by
  obtain ⟨e⟩ := hX
  let B' : Subgroup (alternatingGroup (Fin 8)) := B.map e.toMonoidHom
  have hB' : Nat.card B' = 7 := by
    rw [show Nat.card B' = Nat.card B from
      Subgroup.card_map_of_injective (f := e.toMonoidHom) e.injective, hB]
  obtain ⟨y', hy'3, hy'N, a', ha'B', hya'⟩ := exists_three_normalizer_alt_eight hB'
  have he_mem : ∀ z : X, e z ∈ B' ↔ z ∈ B := by
    intro z
    rw [Subgroup.mem_map]
    constructor
    · rintro ⟨w, hw, hwe⟩
      exact (e.injective hwe) ▸ hw
    · intro hz
      exact ⟨z, hz, rfl⟩
  refine ⟨e.symm y', ?_, ?_, e.symm a', ?_, ?_⟩
  · exact (orderOf_injective e.symm.toMonoidHom e.symm.injective y').trans hy'3
  · rw [Subgroup.mem_normalizer_iff]
    intro h
    rw [← he_mem h, ← he_mem (e.symm y' * h * (e.symm y')⁻¹)]
    rw [show e (e.symm y' * h * (e.symm y')⁻¹) = y' * e h * y'⁻¹ by simp [map_mul]]
    exact (Subgroup.mem_normalizer_iff.mp hy'N) (e h)
  · have : e (e.symm a') ∈ B' := by simpa using ha'B'
    exact (he_mem (e.symm a')).mp this
  · intro h
    exact hya' (by simpa [map_mul] using congrArg e h)

theorem close16_exists_three_normalizing (hS : Close16Setting D V L hV)
    {B : Subgroup (MulAut (Vtil ⊥ V hV))} (hBL : B ≤ lBar ⊥ V hV L) (hB : Nat.card B = 7) :
    ∃ y ∈ lBar ⊥ V hV L, orderOf y = 3 ∧ y ∈ normalizer (B : Set (MulAut (Vtil ⊥ V hV))) ∧
      ∃ a ∈ B, y * a * y⁻¹ ≠ a := by
  have hcard : Nat.card ↥(B.subgroupOf (lBar ⊥ V hV L)) = 7 := by
    rw [← hB]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hBL).toEquiv
  obtain ⟨y, hy3, hyN, a, haB, hya⟩ :=
    close16_alt_eight_normalizer_three (close16_lbar_isAlt hS) hcard
  refine ⟨(y : MulAut (Vtil ⊥ V hV)), y.2, ?_, ?_, (a : MulAut (Vtil ⊥ V hV)), haB, ?_⟩
  · rw [← Subgroup.orderOf_coe] at hy3
    exact hy3
  · rw [Subgroup.mem_normalizer_iff]
    intro g
    constructor
    · intro hg
      have := (Subgroup.mem_normalizer_iff.1 hyN ⟨g, hBL hg⟩).1 hg
      exact this
    · intro hg
      have hgL : g ∈ lBar ⊥ V hV L := by
        have h1 : (y : MulAut (Vtil ⊥ V hV))⁻¹ * ((y : MulAut (Vtil ⊥ V hV)) * g *
            (y : MulAut (Vtil ⊥ V hV))⁻¹) * (y : MulAut (Vtil ⊥ V hV)) ∈ lBar ⊥ V hV L :=
          (lBar ⊥ V hV L).mul_mem ((lBar ⊥ V hV L).mul_mem ((lBar ⊥ V hV L).inv_mem y.2)
            (hBL hg)) y.2
        simpa [mul_assoc] using h1
      exact (Subgroup.mem_normalizer_iff.1 hyN ⟨g, hgL⟩).2 hg
  · intro h
    exact hya (Subtype.ext h)

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
