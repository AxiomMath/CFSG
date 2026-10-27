module

public import CFSG.RankThree.PartTwo.KFacts.KP2Alternating10
import CFSG.RankThree.PartTwo.KFacts.KS14Orders

public section

namespace CFSG.RankThree.PartTwo.Sec17.Proof171Gen

open Equiv Equiv.Perm
open CFSG.RankThree.PartTwo.KFacts.KP2
open scoped commutatorElement

theorem commutatorElement_mul_of_commute {M : Type*} [Group M] {z₁ z₂ a b : M}
    (h1a : Commute z₁ a) (h1b : Commute z₁ b) (h2a : Commute z₂ a) (h2b : Commute z₂ b)
    (h12 : Commute z₁ z₂) : ⁅z₁ * a, z₂ * b⁆ = ⁅a, b⁆ := by
  have hc1 : Commute z₁ (a * z₂ * b * a⁻¹) :=
    ((h1a.mul_right h12).mul_right h1b).mul_right h1a.inv_right
  have hc2 : Commute z₂ (a * b * a⁻¹ * b⁻¹) :=
    ((h2a.mul_right h2b).mul_right h2a.inv_right).mul_right h2b.inv_right
  have h3 : a * z₂ * a⁻¹ = z₂ := by rw [← h2a.eq, mul_inv_cancel_right]
  calc ⁅z₁ * a, z₂ * b⁆ = (z₁ * (a * z₂ * b * a⁻¹) * z₁⁻¹) * b⁻¹ * z₂⁻¹ := by
        rw [commutatorElement_def]
        group
    _ = (a * z₂ * b * a⁻¹) * b⁻¹ * z₂⁻¹ := by rw [hc1.eq, mul_inv_cancel_right]
    _ = (a * z₂ * a⁻¹) * (a * b * a⁻¹ * b⁻¹) * z₂⁻¹ := by group
    _ = z₂ * (a * b * a⁻¹ * b⁻¹) * z₂⁻¹ := by rw [h3]
    _ = ⁅a, b⁆ := by rw [hc2.eq, mul_inv_cancel_right, commutatorElement_def]

theorem card_centralizer_replicate :
    ((Fintype.card (Fin 10) - (Multiset.replicate 2 3).sum).factorial *
        (Multiset.replicate 2 3).prod *
        ∏ n ∈ (Multiset.replicate 2 3).toFinset, ((Multiset.replicate 2 3).count n).factorial =
      432) ∧
    ((Fintype.card (Fin 10) - (Multiset.replicate 3 3).sum).factorial *
        (Multiset.replicate 3 3).prod *
        ∏ n ∈ (Multiset.replicate 3 3).toFinset, ((Multiset.replicate 3 3).count n).factorial =
      162) := by
  decide

theorem isThreeCycle_of_card_centralizer {x : Perm (Fin 10)} (h3 : x ^ 3 = 1) (h1 : x ≠ 1)
    (hc : 2520 ≤ Nat.card (Subgroup.centralizer ({x} : Set (Perm (Fin 10))))) :
    x.IsThreeCycle := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have ho : orderOf x = 3 := orderOf_eq_prime h3 h1
  obtain ⟨n, hn⟩ := cycleType_prime_order (ho ▸ Nat.prime_three)
  rw [ho] at hn
  have hsum := sum_cycleType_le x
  rw [hn, Multiset.sum_replicate, smul_eq_mul, Fintype.card_fin] at hsum
  rw [nat_card_centralizer, hn] at hc
  have hn2 : n = 0 ∨ n = 1 ∨ n = 2 := by omega
  rcases hn2 with rfl | rfl | rfl
  · exact hn
  · rw [card_centralizer_replicate.1] at hc
    omega
  · rw [card_centralizer_replicate.2] at hc
    omega

theorem isThreeCycle_dThree : dThree.IsThreeCycle :=
  card_support_eq_three_iff.mp (by decide +kernel)

theorem card_map_embedSeven :
    Nat.card ((alternatingGroup (Fin 7)).map embedSeven) = 2520 := by
  rw [Subgroup.card_map_of_injective embedSeven_injective,
    KFacts.KS14.card_alternatingGroup_five_seven_ten.2.1]

theorem le_of_le_centralizer_dThree {H R : Subgroup (Perm (Fin 10))}
    (hH : H ≤ Subgroup.centralizer ({dThree} : Set (Perm (Fin 10))) ⊓ alternatingGroup (Fin 10))
    (hHp : ⁅H, H⁆ = H) (hH7 : 2520 ≤ Nat.card H)
    (hR : R ≤ Subgroup.centralizer ({dThree} : Set (Perm (Fin 10))) ⊓ alternatingGroup (Fin 10))
    (hR3 : ¬ 3 ∣ Nat.card R) : R ≤ H := by
  set E7 := (alternatingGroup (Fin 7)).map embedSeven with hE7
  have hc : ∀ σ : Perm (Fin 7), Commute (embedSeven σ) dThree := embedSeven_commute
  have hHE : H ≤ E7 := by
    rw [← hHp, Subgroup.commutator_le]
    intro u hu v hv
    obtain ⟨i, σ, hσ, rfl⟩ := exists_eq_of_commute_dThree_of_mem
      (Subgroup.mem_centralizer_singleton_iff.mp (hH hu).1) (hH hu).2
    obtain ⟨j, τ, hτ, rfl⟩ := exists_eq_of_commute_dThree_of_mem
      (Subgroup.mem_centralizer_singleton_iff.mp (hH hv).1) (hH hv).2
    rw [commutatorElement_mul_of_commute ((hc σ).pow_right _).symm ((hc τ).pow_right _).symm
      ((hc σ).pow_right _).symm ((hc τ).pow_right _).symm (Commute.pow_pow_self dThree _ _),
      ← map_commutatorElement]
    refine ⟨⁅σ, τ⁆, ?_, rfl⟩
    rw [commutatorElement_def]
    exact mul_mem (mul_mem (mul_mem hσ hτ) (inv_mem hσ)) (inv_mem hτ)
  have hHeq : H = E7 := Subgroup.eq_of_le_of_card_ge hHE (by rw [card_map_embedSeven]; exact hH7)
  rw [hHeq]
  intro r hr
  obtain ⟨σ, rfl⟩ := exists_embedSeven_of_mem hR3 hr
    (Subgroup.mem_centralizer_singleton_iff.mp (hR hr).1)
  have hs : embedSeven σ ∈ alternatingGroup (Fin 10) := (hR hr).2
  rw [Perm.mem_alternatingGroup, sign_embedSeven] at hs
  exact ⟨σ, hs, rfl⟩

theorem le_of_le_centralizer_of_isThreeCycle {x : Perm (Fin 10)} (hx : x.IsThreeCycle)
    {H R : Subgroup (Perm (Fin 10))}
    (hH : H ≤ Subgroup.centralizer ({x} : Set (Perm (Fin 10))) ⊓ alternatingGroup (Fin 10))
    (hHp : ⁅H, H⁆ = H) (hH7 : 2520 ≤ Nat.card H)
    (hR : R ≤ Subgroup.centralizer ({x} : Set (Perm (Fin 10))) ⊓ alternatingGroup (Fin 10))
    (hR3 : ¬ 3 ∣ Nat.card R) : R ≤ H := by
  obtain ⟨h, hh⟩ := isConj_iff.mp (isConj_iff_cycleType_eq.mpr
    (hx.trans isThreeCycle_dThree.symm))
  have hconj : ∀ K : Subgroup (Perm (Fin 10)),
      K ≤ Subgroup.centralizer ({x} : Set (Perm (Fin 10))) ⊓ alternatingGroup (Fin 10) →
      K.map (MulAut.conj h).toMonoidHom ≤
        Subgroup.centralizer ({dThree} : Set (Perm (Fin 10))) ⊓ alternatingGroup (Fin 10) := by
    rintro K hK _ ⟨y, hy, rfl⟩
    have hyx : y * x = x * y := Subgroup.mem_centralizer_singleton_iff.mp (hK hy).1
    refine ⟨Subgroup.mem_centralizer_singleton_iff.mpr ?_, ?_⟩
    · change h * y * h⁻¹ * dThree = dThree * (h * y * h⁻¹)
      rw [← hh]
      calc h * y * h⁻¹ * (h * x * h⁻¹) = h * (y * x) * h⁻¹ := by group
        _ = h * (x * y) * h⁻¹ := by rw [hyx]
        _ = h * x * h⁻¹ * (h * y * h⁻¹) := by group
    · exact (Subgroup.Normal.conj_mem inferInstance y (hK hy).2 h)
  have hle := le_of_le_centralizer_dThree (hconj H hH)
    (by rw [← Subgroup.map_commutator, hHp])
    (by rwa [Subgroup.card_map_of_injective (MulAut.conj h).injective])
    (hconj R hR) (by rwa [Subgroup.card_map_of_injective (MulAut.conj h).injective])
  exact (Subgroup.map_le_map_iff_of_injective (MulAut.conj h).injective).mp hle

theorem kOneF_comm : ∀ (a : Fin 6) (m : Fin 4), a.val / 2 ≠ 0 →
    kOneF m * axisElt a = axisElt a * kOneF m := by
  decide +kernel

theorem kTwoF_comm : ∀ (a : Fin 6) (m : Fin 4), a.val / 2 ≠ 1 →
    kTwoF m * axisElt a = axisElt a * kTwoF m := by
  decide +kernel

theorem kThreeF_comm : ∀ (a : Fin 6) (m : Fin 4), a.val / 2 ≠ 2 →
    kThreeF m * axisElt a = axisElt a * kThreeF m := by
  decide +kernel

theorem kF_sign : ∀ m : Fin 4, Perm.sign (kOneF m) = 1 ∧ Perm.sign (kTwoF m) = 1 ∧
    Perm.sign (kThreeF m) = 1 := by
  decide +kernel

theorem le_centralizer_axisElt_or {a b : Fin 6} (hab : a.val / 2 ≠ b.val / 2)
    {K : Subgroup (Perm (Fin 10))} (hK : K = kOne ∨ K = kTwo ∨ K = kThree) :
    K ≤ Subgroup.centralizer ({axisElt a} : Set (Perm (Fin 10))) ⊓ alternatingGroup (Fin 10) ∨
      K ≤ Subgroup.centralizer ({axisElt b} : Set (Perm (Fin 10))) ⊓
        alternatingGroup (Fin 10) := by
  have hle : ∀ (F : Fin 4 → Perm (Fin 10)) (e : Fin 6),
      (∀ m, F m * axisElt e = axisElt e * F m) → (∀ m, Perm.sign (F m) = 1) →
      K = {x | ∃ m, x = F m} →
      K ≤ Subgroup.centralizer ({axisElt e} : Set (Perm (Fin 10))) ⊓
        alternatingGroup (Fin 10) := by
    intro F e hc hs hKF x hx
    have hx' : x ∈ ({x | ∃ m, x = F m} : Set (Perm (Fin 10))) := by
      rw [← hKF]
      exact hx
    obtain ⟨m, rfl⟩ := hx'
    exact ⟨Subgroup.mem_centralizer_singleton_iff.mpr (hc m), hs m⟩
  rcases hK with rfl | rfl | rfl
  · by_cases ha : a.val / 2 = 0
    · exact Or.inr (hle kOneF b (fun m => kOneF_comm b m (by omega)) (fun m => (kF_sign m).1)
        rfl)
    · exact Or.inl (hle kOneF a (fun m => kOneF_comm a m ha) (fun m => (kF_sign m).1) rfl)
  · by_cases ha : a.val / 2 = 1
    · exact Or.inr (hle kTwoF b (fun m => kTwoF_comm b m (by omega))
        (fun m => (kF_sign m).2.1) rfl)
    · exact Or.inl (hle kTwoF a (fun m => kTwoF_comm a m ha) (fun m => (kF_sign m).2.1) rfl)
  · by_cases ha : a.val / 2 = 2
    · exact Or.inr (hle kThreeF b (fun m => kThreeF_comm b m (by omega))
        (fun m => (kF_sign m).2.2) rfl)
    · exact Or.inl (hle kThreeF a (fun m => kThreeF_comm a m ha) (fun m => (kF_sign m).2.2)
        rfl)

end CFSG.RankThree.PartTwo.Sec17.Proof171Gen
