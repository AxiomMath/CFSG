module

public import CFSG.LocalAnalysis.UniquenessCase.UC22K147Excl
import CFSG.LieType.Suzuki.SuzukiOuterCyclic
import CFSG.Quasithin.Background.F918Z8Op4d
import CFSG.LocalAnalysis.WeakClosure81.SzStructurePair
import CFSG.Blueprint.LieModelAPI
import CFSG.Timmesfeld.Orders.Bang
public import CFSG.LocalAnalysis.ComponentClassification.OuterAutomorphisms

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.Excl147

open Subgroup CFSG.Timmesfeld
open CFSG.ComponentClassification.OuterAutomorphisms (Outer equivalence)

private theorem orderOf_two_eq_of_ppd {ℓ k : ℕ} (h : IsPrimitivePrimeDivisor ℓ k) (hk : 0 < k) :
    orderOf (2 : ZMod ℓ) = k := by
  apply Nat.dvd_antisymm
  · exact orderOf_dvd_of_pow_eq_one ((Bang.dvd_two_pow_sub_one_iff _).1 h.dvd)
  · exact (h.dvd_sub_one_iff hk _).1 ((Bang.dvd_two_pow_sub_one_iff _).2 (pow_orderOf_eq_one _))

private theorem inner_of_sq_eq_one {X : Type} [Group X] {n : ℕ}
    (hX : IsSz X n) {α : MulAut X} (hα : α ^ 2 = 1) : ∃ s : X, ∀ y, α y = s * y * s⁻¹ := by
  obtain ⟨-, -, a, ha, K, _, _, rfl, hK, ⟨e⟩⟩ := CFSG.Blueprint.LieModel.suzukiModel hX
  have hcard : Nat.card (Outer X) ∣ 2 * a + 1 := by
    rw [Nat.card_congr (equivalence e).toEquiv]
    exact (CFSG.LieType.Suzuki.suzukiGroup_outer_isCyclic_card_dvd ha hK).2
  have h1 : orderOf (α : Outer X) ∣ 2 :=
    orderOf_dvd_of_pow_eq_one (by rw [← QuotientGroup.mk_pow, hα, QuotientGroup.mk_one])
  have h2 : orderOf (α : Outer X) ∣ 2 * a + 1 := (_root_.orderOf_dvd_natCard _).trans hcard
  rcases (Nat.dvd_prime Nat.prime_two).1 h1 with h3 | h3
  · obtain ⟨s, hs⟩ : α ∈ CFSG.ComponentClassification.OuterAutomorphisms.inner X :=
      (QuotientGroup.eq_one_iff α).1 (orderOf_eq_one_iff.1 h3)
    exact ⟨s, fun y => by rw [← hs, MulAut.conj_apply]⟩
  · rw [h3] at h2
    omega

theorem facts_of_isSz {X : Type} [Group X] [Finite X] {n : ℕ}
    (hX : IsSz X n) : ∃ ℓ : ℕ, ℓ.Prime ∧ ℓ ≠ 2 ∧ orderOf (2 : ZMod ℓ) = 4 * n ∧ Facts X ℓ := by
  have hQ : CFSG.Quasithin.IsSz n X := (CFSG.Blueprint.LieModel.suzukiModel hX).2
  have hsimple : IsSimpleGroup X := by
    obtain ⟨-, a, ha, K, _, _, hn, hK, ⟨e'⟩⟩ := hQ
    rw [hn] at hK
    haveI := (CFSG.LieType.Ree.suzuki_simple ha hK).2.2
    exact e'.isSimpleGroup
  obtain ⟨m, hm, rfl, ⟨e⟩⟩ := CFSG.Quasithin.opq4d_exists_mulEquiv_suzukiMatrixGroup hQ
  obtain ⟨ℓ, hppd⟩ := exists_isPrimitivePrimeDivisor (k := 4 * (2 * m + 1)) (by omega) (by omega)
  have hℓ := hppd.prime
  have hℓ2 := hppd.ne_two (by omega)
  haveI : Fact ℓ.Prime := ⟨hℓ⟩
  have hdvd : ℓ ∣ (2 ^ (2 * m + 1)) ^ 2 + 1 := by
    rw [← pow_mul]
    refine (hppd.dvd_add_one_iff (by omega) _).2 ⟨⟨1, by ring⟩, ?_⟩
    exact Nat.not_dvd_of_pos_of_lt (by omega) (by omega)
  have hcard : ℓ ∣ Nat.card (CFSG.BenderSuzuki.MatrixGroups.SuzukiMatrixGroup m) := by
    rw [CFSG.Quasithin.opq4d_card_suzukiMatrixGroup (by omega)]
    exact Dvd.dvd.mul_right (Dvd.dvd.mul_right hdvd _) _
  haveI : Finite (CFSG.BenderSuzuki.MatrixGroups.SuzukiMatrixGroup m) := Finite.of_equiv X e.toEquiv
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' ℓ hcard
  have hP : IsPGroup ℓ (zpowers x) := IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hx, pow_one])
  obtain ⟨S, hS⟩ := hP.exists_le_sylow
  have hxS : x ∈ (S : Subgroup (CFSG.BenderSuzuki.MatrixGroups.SuzukiMatrixGroup m)) :=
    hS (mem_zpowers x)
  have hx1 : x ≠ 1 := fun h => by
    rw [h, orderOf_one] at hx
    exact hℓ.one_lt.ne hx
  have hS1 : (S : Subgroup (CFSG.BenderSuzuki.MatrixGroups.SuzukiMatrixGroup m)) ≠ ⊥ := fun h =>
    hx1 (by rw [h, mem_bot] at hxS; exact hxS)
  obtain ⟨s, hss, hsinv⟩ := CFSG.Quasithin.opq4d_suzuki_exists_involution_inverts hm hℓ hℓ2 S hS1
  have hsx : s * x * s⁻¹ = x⁻¹ := hsinv x hxS
  have hs1 : s ≠ 1 := fun h => inv_ne_of_orderOf hx hℓ hℓ2 (by rw [← hsx, h]; group)
  have hs2 : orderOf s = 2 := orderOf_eq_prime (by rw [pow_two]; exact hss) hs1
  have hs₀ : orderOf (e.symm s) = 2 := by rw [MulEquiv.orderOf_eq]; exact hs2
  have hx₀ : orderOf (e.symm x) = ℓ := by rw [MulEquiv.orderOf_eq]; exact hx
  have hsx₀ : e.symm s * e.symm x * (e.symm s)⁻¹ = (e.symm x)⁻¹ := by
    rw [← map_inv, ← map_mul, ← map_mul, hsx, map_inv]
  refine ⟨ℓ, hℓ, hℓ2, orderOf_two_eq_of_ppd hppd (by omega), ?_⟩
  refine ⟨hsimple, ⟨e.symm s, hs₀⟩, fun s' hs' => ?_, fun α hα => ?_⟩
  · obtain ⟨hss₀, hs₀1⟩ := mul_self_and_ne_one hs₀
    obtain ⟨hss', hs'1⟩ := mul_self_and_ne_one hs'
    obtain ⟨c, hc⟩ := isConj_iff.1
      (CFSG.LocalAnalysis.WeakClosure81.SevenK.isConj_of_involutions_of_isSz hQ hss₀ hs₀1 hss' hs'1)
    refine ⟨c * e.symm x * c⁻¹, by rw [← MulAut.conj_apply, MulEquiv.orderOf_eq, hx₀], ?_⟩
    rw [← hc]
    calc c * e.symm s * c⁻¹ * (c * e.symm x * c⁻¹) * (c * e.symm s * c⁻¹)⁻¹
        = c * (e.symm s * e.symm x * (e.symm s)⁻¹) * c⁻¹ := by group
      _ = (c * e.symm x * c⁻¹)⁻¹ := by rw [hsx₀]; group
  · exact inner_of_sq_eq_one hX hα

end CFSG.LocalAnalysis.UniquenessCase.UC22.Excl147
