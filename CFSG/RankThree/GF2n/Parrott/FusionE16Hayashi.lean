module

public import CFSG.RankThree.GF2n.Parrott.FusionE16Core
public import CFSG.RankThree.GF2n.Parrott.A1ModelFacts
public import CFSG.LargeExtraspecial.Setting

public section

namespace CFSG.RankThree.GF2n.Parrott

open CFSG CFSG.Open
open CFSG.Sporadic.Co2Smith (x45P)
open CFSG.ComponentClassification.CatFactsSmall.PSp43

theorem weaklyClosed_pCore_centralizer_of_equiv_lieModel
    {G : Type} [Group G] [Finite G] {j : G} (hj : orderOf j = 2)
    {X : Type} [Group X] (hX : CFSG.Blueprint.LieModel X .PSp 2 3 1) {x : X} (hx : orderOf x = 2)
    (hx2 : ∃ T : Sylow 2 X, x ∈ (T : Subgroup X) ∧ ∀ s ∈ (T : Subgroup X), x * s = s * x)
    (e : ↥(Subgroup.centralizer ({j} : Set G)) ≃* ↥(Subgroup.centralizer ({x} : Set X))) :
    ∀ g : G, g * j * g⁻¹ ∈ inSubgroup (pCore 2) (Subgroup.centralizer ({j} : Set G)) →
      g * j * g⁻¹ = j := by
  intro g hg
  obtain ⟨e₀⟩ := equiv_of_lieModel hX
  have hx' : orderOf (e₀ x) = 2 := by rw [MulEquiv.orderOf_eq]; exact hx
  have hcardC : Nat.card (Subgroup.centralizer ({e₀ x} : Set ↥QP45.originalSubgroup)) =
      Nat.card (Subgroup.centralizer ({x} : Set X)) :=
    (Nat.card_congr (CFSG.Sporadic.Co2Smith.centralizerEquivOfEquiv e₀ x).toEquiv).symm
  have h64 : 64 ∣ Nat.card (Subgroup.centralizer ({x} : Set X)) := by
    obtain ⟨T, hxT, hxc⟩ := hx2
    have hXcard : Nat.card X = 25920 := by
      rw [Nat.card_congr e₀.toEquiv, CFSG.Sporadic.Co2Smith.card_QP45]
    have hT64 : Nat.card T = 64 := by
      have : Finite X := Nat.finite_of_card_ne_zero (by rw [hXcard]; norm_num)
      rw [T.card_eq_multiplicity, hXcard, show (25920 : ℕ) = 2 ^ 6 * 405 by norm_num,
        Nat.factorization_mul (by norm_num) (by norm_num), Finsupp.add_apply,
        Nat.Prime.factorization_pow Nat.prime_two, Finsupp.single_eq_same,
        Nat.factorization_eq_zero_of_not_dvd (by norm_num), add_zero]
      norm_num
    have hTle : (T : Subgroup X) ≤ Subgroup.centralizer ({x} : Set X) := fun s hs =>
      Subgroup.mem_centralizer_singleton_iff.mpr (hxc s hs).symm
    have h1 : Nat.card (T : Subgroup X) ∣ Nat.card (Subgroup.centralizer ({x} : Set X)) :=
      Subgroup.card_dvd_of_le hTle
    rwa [show Nat.card (T : Subgroup X) = 64 from hT64] at h1
  have hconj : IsConj (e₀ x) x45P := by
    rcases qp45_involution_classes (e₀ x) hx' with h | h
    · exact h
    · exfalso
      have h1 := CFSG.GroupTheory.card_centralizer_eq_of_isConj h
      have h2 : Nat.card (Subgroup.centralizer ({x} : Set X)) = 96 := by
        rw [← hcardC, h1, qp45_card_centralizer_ut]
      rw [h2] at h64
      omega
  obtain ⟨c, hc⟩ := isConj_iff.mp hconj
  let e' : ↥(Subgroup.centralizer ({j} : Set G)) ≃*
      ↥(Subgroup.centralizer ({x45P} : Set ↥QP45.originalSubgroup)) :=
    (e.trans (CFSG.Sporadic.Co2Smith.centralizerEquivOfEquiv e₀ x)).trans
      ((CFSG.Sporadic.Co2Smith.centralizerEquivOfEquiv (MulAut.conj c) (e₀ x)).trans
        (MulEquiv.subgroupCongr (by rw [MulAut.conj_apply, hc]) |>.trans (MulEquiv.refl _)))
  have := weaklyClosed_pCore_centralizer_of_equiv_x45P hj e' g⁻¹
  simpa using this (by simpa using hg)

theorem _root_.CFSG.LargeExtraspecial.Setting.weaklyClosed_QG_of_equiv_lieModel
    {G : Type} [Group G] [Finite G] (S : CFSG.LargeExtraspecial.Setting G)
    {X : Type} [Group X] (hX : CFSG.Blueprint.LieModel X .PSp 2 3 1) {x : X} (hx : orderOf x = 2)
    (hx2 : ∃ T : Sylow 2 X, x ∈ (T : Subgroup X) ∧ ∀ s ∈ (T : Subgroup X), x * s = s * x)
    (e : ↥S.M ≃* ↥(Subgroup.centralizer ({x} : Set X))) :
    ∀ g : G, g * S.z * g⁻¹ ∈ S.QG → g * S.z * g⁻¹ = S.z := by
  intro g hg
  refine weaklyClosed_pCore_centralizer_of_equiv_lieModel S.orderOf_z hX hx hx2 e g ?_
  obtain ⟨q, hq, hqg⟩ := hg
  have hle : S.Q ≤ pCore 2 ↥S.M := le_sSup ⟨S.normal, S.extraspecial.1⟩
  exact ⟨q, hle hq, hqg⟩

end CFSG.RankThree.GF2n.Parrott
