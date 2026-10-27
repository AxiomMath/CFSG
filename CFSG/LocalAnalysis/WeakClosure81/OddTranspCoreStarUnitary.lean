module

public import CFSG.LocalAnalysis.WeakClosure81.OddTranspCoreTwo
public import CFSG.Open.FischerThreeTranspositionMilestoneDefs
import CFSG.Fischer.Classification.Unitary.Model

public section

namespace CFSG.LocalAnalysis.WeakClosure81.CoreStar

open CFSG.Blueprint.Fischer CFSG.Open Matrix

open CFSG.Fischer.Classification.Unitary CFSG.ClassicalGroups.Unitary in
private theorem exists_unitary_star_vectors {m : ℕ} (hm : 4 ≤ m) :
    ∃ u w v : Fin m → K, herm frob u u = 0 ∧ herm frob w w = 0 ∧ herm frob v v = 0 ∧
      herm frob w v = 0 ∧ herm frob u w ≠ 0 ∧ herm frob u v = 0 ∧ v ≠ 0 := by
  obtain ⟨i, j, k, l, hij, hik, hil, hjk, hjl, hkl⟩ : ∃ i j k l : Fin m,
      i ≠ j ∧ i ≠ k ∧ i ≠ l ∧ j ≠ k ∧ j ≠ l ∧ k ≠ l :=
    ⟨⟨0, by omega⟩, ⟨1, by omega⟩, ⟨2, by omega⟩, ⟨3, by omega⟩, by simp, by simp, by simp,
      by simp, by simp, by simp⟩
  refine ⟨Pi.single i 1 + Pi.single j 1, Pi.single i 1 + Pi.single j ω,
    Pi.single k 1 + Pi.single l ω, isotropic_single_add_single hij one_ne_zero,
    isotropic_single_add_single hij omega_ne_zero, isotropic_single_add_single hkl omega_ne_zero,
    ?_, ?_, ?_, fun h => ?_⟩
  · rw [herm_single_add_single_left, Pi.add_apply, Pi.add_apply, Pi.single_eq_of_ne hik,
      Pi.single_eq_of_ne hil, Pi.single_eq_of_ne hjk, Pi.single_eq_of_ne hjl]
    simp only [add_zero, mul_zero]
  · rw [herm_single_add_single_left, Pi.add_apply, Pi.add_apply, Pi.single_eq_same,
      Pi.single_eq_of_ne hij, Pi.single_eq_of_ne hij.symm, Pi.single_eq_same, map_one, one_mul,
      add_zero, zero_add]
    exact fun h => omega_ne_one (add_left_cancel (h.trans (add_self_K 1).symm))
  · rw [herm_single_add_single_left, Pi.add_apply, Pi.add_apply, Pi.single_eq_of_ne hik,
      Pi.single_eq_of_ne hil, Pi.single_eq_of_ne hjk, Pi.single_eq_of_ne hjl]
    simp only [add_zero, mul_zero]
  · have e := congrFun h k
    rw [Pi.add_apply, Pi.single_eq_same, Pi.single_eq_of_ne hkl, add_zero, Pi.zero_apply] at e
    exact one_ne_zero e

open CFSG.Fischer.Classification.Unitary CFSG.ClassicalGroups.Unitary in
private theorem hasCoreStar_of_mulEquiv_U2 {G : Type} [Group G] {t : G}
    (hP : Pair G {x | IsConj t x}) {m : ℕ} (hm : 4 ≤ m) (φ : G ≃* U2 m)
    (hφ : φ '' {x | IsConj t x} = DU m) : HasCoreStar G t := by
  obtain ⟨u, w, v, hu, hw, hv, hwv, huw, huv, hv0⟩ := exists_unitary_star_vectors hm
  have hm3 : 3 ≤ m := by omega
  have hvw : herm frob v w = 0 := herm_eq_zero_comm frob frob_frob hwv
  have hne0 : ∀ x : Fin m → K, herm frob u x ≠ 0 → x ≠ 0 := fun x hx h =>
    hx (by rw [h, herm_zero_right])
  have hu0 : u ≠ 0 := fun h => huw (by rw [h, herm_zero_left])
  have h₂ : herm frob (w + v) (w + v) = 0 := by
    simp only [herm_add_left, herm_add_right, hw, hv, hwv, hvw, add_zero]
  have h₃ : herm frob (w + ω • v) (w + ω • v) = 0 := by
    simp only [herm_add_left, herm_add_right, herm_smul_left, herm_smul_right, hw, hv, hwv, hvw,
      mul_zero, add_zero]
  have hu₂ : herm frob u (w + v) = herm frob u w := by simp only [herm_add_right, huv, add_zero]
  have hu₃ : herm frob u (w + ω • v) = herm frob u w := by
    simp only [herm_add_right, herm_smul_right, huv, mul_zero, add_zero]
  have h12 : herm frob w (w + v) = 0 := by simp only [herm_add_right, hw, hwv, add_zero]
  have h13 : herm frob w (w + ω • v) = 0 := by
    simp only [herm_add_right, herm_smul_right, hw, hwv, mul_zero, add_zero]
  have h23 : herm frob (w + v) (w + ω • v) = 0 := by
    simp only [herm_add_left, herm_add_right, herm_smul_right, hw, hv, hwv, hvw, mul_zero,
      add_zero]
  have hc1 : ∀ (a b : Fin m → K) (c : K), herm frob u a = herm frob u w →
      herm frob u b = herm frob u w → b = c • a → c = 1 := fun a b c ha hb hab => by
    rw [hab, herm_smul_right, ha] at hb
    exact mul_right_cancel₀ huw (hb.trans (one_mul _).symm)
  have n12 : ¬ ∃ c : K, w + v = c • w := by
    rintro ⟨c, hc⟩
    obtain rfl := hc1 w _ c rfl hu₂ hc
    rw [one_smul] at hc
    exact hv0 (by simpa using hc)
  have n13 : ¬ ∃ c : K, w + ω • v = c • w := by
    rintro ⟨c, hc⟩
    obtain rfl := hc1 w _ c rfl hu₃ hc
    rw [one_smul] at hc
    exact hv0 (by simpa [omega_ne_zero] using hc)
  have n23 : ¬ ∃ c : K, w + ω • v = c • (w + v) := by
    rintro ⟨c, hc⟩
    obtain rfl := hc1 _ _ c hu₂ hu₃ hc
    rw [one_smul] at hc
    have h' : (ω - 1) • v = 0 := by rw [sub_smul, one_smul, add_left_cancel hc, sub_self]
    rcases smul_eq_zero.1 h' with h | h
    · exact omega_ne_one (sub_eq_zero.1 h)
    · exact hv0 h
  have hD : ∀ x : Fin m → K, x ≠ 0 → herm frob x x = 0 → IsConj t (φ.symm (tqU x)) := by
    intro x hx0 hx
    have hmem : tqU x ∈ φ '' {x | IsConj t x} := by
      rw [hφ]
      exact tqU_mem_DU hx0 hx
    obtain ⟨g, hg, hgx⟩ := hmem
    rw [← hgx, φ.symm_apply_apply]
    exact hg
  have hcomm : ∀ a b : Fin m → K, a ≠ 0 → herm frob a a = 0 → b ≠ 0 → herm frob b b = 0 →
      (φ.symm (tqU a) * φ.symm (tqU b) = φ.symm (tqU b) * φ.symm (tqU a) ↔
        herm frob a b = 0) := fun a b ha0 ha hb0 hb => by
    rw [← map_mul, ← map_mul, φ.symm.injective.eq_iff]
    exact tqU_commute_iff hm3 ha0 ha hb0 hb
  have hne : ∀ a b : Fin m → K, a ≠ 0 → herm frob a a = 0 → b ≠ 0 → herm frob b b = 0 →
      (¬ ∃ c : K, b = c • a) → φ.symm (tqU a) ≠ φ.symm (tqU b) := fun a b ha0 ha hb0 hb h e =>
    h ((tqU_eq_tqU_iff hm3 ha0 ha hb0 hb).1 (φ.symm.injective e))
  have hord : ∀ x : Fin m → K, herm frob x x = 0 → herm frob u x ≠ 0 →
      orderOf (φ.symm (tqU u) * φ.symm (tqU x)) = 3 := fun x hx hux =>
    CFSG.Fischer.Pair.orderOf_mul_eq_three hP (hD u hu0 hu) (hD x (hne0 x hux) hx)
      fun e => hux ((hcomm u x hu0 hu (hne0 x hux) hx).1 e)
  have hu₂' : herm frob u (w + v) ≠ 0 := hu₂ ▸ huw
  have hu₃' : herm frob u (w + ω • v) ≠ 0 := hu₃ ▸ huw
  exact hasCoreStar_of_center (hD u hu0 hu) (hD w (hne0 w huw) hw) (hD _ (hne0 _ hu₂') h₂)
    (hD _ (hne0 _ hu₃') h₃) (hord w hw huw) (hord _ h₂ hu₂') (hord _ h₃ hu₃')
    ((hcomm _ _ (hne0 w huw) hw (hne0 _ hu₂') h₂).2 h12)
    ((hcomm _ _ (hne0 w huw) hw (hne0 _ hu₃') h₃).2 h13)
    ((hcomm _ _ (hne0 _ hu₂') h₂ (hne0 _ hu₃') h₃).2 h23)
    (hne _ _ (hne0 w huw) hw (hne0 _ hu₂') h₂ n12)
    (hne _ _ (hne0 w huw) hw (hne0 _ hu₃') h₃ n13)
    (hne _ _ (hne0 _ hu₂') h₂ (hne0 _ hu₃') h₃ n23)

theorem hasCoreStar_of_unitaryModel {G : Type} [Group G] {t : G}
    (hP : Pair G {x | IsConj t x}) {m : ℕ} (hm : 4 ≤ m)
    (hmod : fischerCentralQuotientModel {x : G | IsConj t x}
      (fischerMatrixGroup fun A => A.det = 1 ∧
        ∀ x y, fischerHermitianF4 m (A *ᵥ x) (A *ᵥ y) = fischerHermitianF4 m x y)
      (fischerTransvections (fischerHermitianF4 m)
        fun v => v ≠ 0 ∧ fischerHermitianF4 m v v = 0)) :
    HasCoreStar G t := by
  obtain ⟨φ, hφ⟩ :=
    (CFSG.Fischer.Classification.fischerCentralQuotientModel_iff_U2 (m := m)).1 hmod
  exact hasCoreStar_of_mulEquiv_U2 hP hm φ hφ

end CFSG.LocalAnalysis.WeakClosure81.CoreStar
