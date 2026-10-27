module

public import CFSG.RankThree.PartOne.KC.LinearPlaneStatements

public section

namespace CFSG.RankThree.PartOne

open Subgroup CFSG CFSG.RankThree.LocalRank

namespace KCOrthogonalNoninner

theorem noninner_plane_conclusion_of_core {T : Type*} [Group T] [Finite T] {p ℓ f : ℕ}
    (hp : p.Prime) (B A : Subgroup (MulAut T)) (hAB : A ≤ B)
    (hAel : IsElementaryAbelian p A) (hAcard : Nat.card A = p ^ 2)
    (hAH : ¬ A ≤ (MulAut.conj : T →* MulAut T).range)
    (hcap : Nat.card (A ⊓ (MulAut.conj : T →* MulAut T).range : Subgroup (MulAut T)) = p)
    (hpf : p ∣ f) (hq : 2 ^ p ≤ ℓ ^ f)
    (hcore : ∀ a ∈ A, a ∉ (MulAut.conj : T →* MulAut T).range →
      inSubgroup (aschbacherSolvableCore p) (B ⊓ Subgroup.centralizer {a}) = ⊥)
    (hodd : 3 < ℓ ^ f → ∀ t ∈ (MulAut.conj : T →* MulAut T).range, orderOf t = p →
      ∀ A' : Subgroup (MulAut T), A' ≤ B ⊓ Subgroup.centralizer {t} → IsPGroup p A' →
        Odd (Nat.card (⁅inSubgroup (aschbacherSolvableCore p) (B ⊓ Subgroup.centralizer {t}), A'⁆ :
          Subgroup (MulAut T)))) :
    Nat.card (A ⊓ (MulAut.conj : T →* MulAut T).range : Subgroup (MulAut T)) = p ∧ p ∣ f ∧
      2 ^ p ≤ ℓ ^ f ∧
      (∀ a ∈ A, a ∉ (MulAut.conj : T →* MulAut T).range →
        inSubgroup (aschbacherSolvableCore p) (B ⊓ Subgroup.centralizer {a}) = ⊥) ∧
      autThetaT p B A = ⊥ ∧
      ∀ t ∈ A, t ≠ 1 →
        PlaneProductIsSubgroup p B A t ∧ ¬ 2 ∣ Nat.card (autPlaneProduct p B A t) ∧
          (t ∉ (MulAut.conj : T →* MulAut T).range → autPlaneProduct p B A t = ⊥) := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have := hAel
  have hpA : ∀ a ∈ A, a ^ p = 1 := fun a ha =>
    elemPow_eq_one_of_isElementaryAbelian (p := p) (A := A) a ha
  obtain ⟨a0, ha0A, ha0H⟩ := IsConcreteLE.not_le_iff_exists.mp hAH
  have ha01 : a0 ≠ 1 := fun h => ha0H (h ▸ one_mem _)
  have hq3 : 3 < ℓ ^ f := by
    have : 2 ^ 2 ≤ 2 ^ p := Nat.pow_le_pow_right (by norm_num) hp.two_le
    omega
  have hθ : autThetaT p B A = ⊥ := by
    refine eq_bot_iff.mpr ((iInf_le_of_le a0 (iInf_le_of_le ha0A
      (iInf_le_of_le ha01 le_rfl))).trans (hcore a0 ha0A ha0H).le)
  have hprod : ∀ t : MulAut T, autPlaneProduct p B A t =
      ⁅inSubgroup (aschbacherSolvableCore p) (B ⊓ Subgroup.centralizer ({t} : Set _)), A⁆ := by
    intro t
    rw [autPlaneProduct, hθ, sup_bot_eq]
  have hAp : IsPGroup p A := IsPGroup.of_card hAcard
  refine ⟨hcap, hpf, hq, hcore, hθ, fun t htA ht1 => ⟨?_, ?_, ?_⟩⟩
  · unfold PlaneProductIsSubgroup
    rw [hθ, sup_bot_eq, Subgroup.coe_bot, Set.mul_singleton]
    simp
  · by_cases htH : t ∈ (MulAut.conj : T →* MulAut T).range
    · have htord : orderOf t = p := orderOf_eq_prime (hpA t htA) ht1
      have hAle : A ≤ B ⊓ Subgroup.centralizer {t} := fun a ha =>
        ⟨hAB ha, Subgroup.mem_centralizer_singleton_iff.mpr
          (congrArg Subtype.val ((IsMulCommutative.is_comm (M := ↥A)).comm ⟨a, ha⟩ ⟨t, htA⟩))⟩
      have hodd' := hodd hq3 t htH htord A hAle hAp
      rw [hprod]
      exact fun h => (Nat.not_even_iff_odd.mpr hodd') (even_iff_two_dvd.mpr h)
    · rw [hprod, hcore t htA htH, Subgroup.commutator_bot_left]
      simp
  · intro htH
    rw [hprod, hcore t htA htH, Subgroup.commutator_bot_left]

end KCOrthogonalNoninner

end CFSG.RankThree.PartOne
