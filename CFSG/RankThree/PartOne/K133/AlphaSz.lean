module

public import CFSG.LieType.Ree.SuzukiSplitTorusCentralizers
public import CFSG.RankThree.PartOne.S15K.SL2Model
public import CFSG.RankThree.PartOne.HNB.Tools

public section

namespace CFSG.RankThree.PartOne.K133

open CFSG CFSG.LieType.Ree CFSG.Blueprint
open scoped commutatorElement

theorem exists_two_subgroup_of_suzukiT {a : ℕ} {F : Type}
    [Field F] [Finite F] (hF : Nat.card F = 2 ^ (2 * a + 1)) {r : ℕ} (hr : r.Prime)
    (hr2 : r ≠ 2) {y : suzukiGroup a F} (hyT : y ∈ suzukiT a F) (hy : orderOf y = r) :
    ∃ S : Subgroup (suzukiGroup a F), S ≠ ⊥ ∧ IsPGroup 2 S ∧
      y ∈ Subgroup.normalizer (S : Set (suzukiGroup a F)) ∧ ⁅S, Subgroup.zpowers y⁆ = S := by
  classical
  have : Fact r.Prime := ⟨hr⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have := finite_suzukiGroup hF
  obtain ⟨l, hl⟩ := mem_suzukiT_iff.1 hyT
  obtain ⟨-, hUcard, -, -, -, -, -, hUsolv, -⟩ := suzuki_unipotent_structure hF
  have hyN : y ∈ Subgroup.normalizer (suzukiU a F : Set (suzukiGroup a F)) :=
    suzukiT_le_normalizer hF hyT
  have hU2 : IsPGroup 2 (suzukiU a F) :=
    IsPGroup.of_card (n := (2 * a + 1) * 2) (by rw [hUcard, pow_mul])
  have hP : Subgroup.zpowers y ≤ Subgroup.normalizer (suzukiU a F : Set (suzukiGroup a F)) :=
    Subgroup.zpowers_le.mpr hyN
  have hcop : Nat.Coprime (Nat.card (Subgroup.zpowers y)) (Nat.card (suzukiU a F)) := by
    rw [Nat.card_zpowers, hy, hUcard, ← pow_mul]
    exact Nat.Coprime.pow_right _ ((Nat.coprime_primes hr Nat.prime_two).mpr hr2)
  have hdbl := HNB.commutator_double_eq_self_of_coprime_solvable (Subgroup.zpowers y)
    (suzukiU a F) hP hcop hUsolv
  have hle : ⁅suzukiU a F, Subgroup.zpowers y⁆ ≤ suzukiU a F :=
    Subgroup.le_normalizer_iff_commutator_le_left.1 hP
  refine ⟨⁅suzukiU a F, Subgroup.zpowers y⁆, ?_, hU2.to_le hle,
    Subgroup.normalizer_commutator_ge_right _ _ (Subgroup.mem_zpowers y), hdbl⟩
  intro hbot
  have hl1 : l ≠ 1 := by
    rintro rfl
    rw [suzukiDElt_one] at hl
    rw [← hl, orderOf_one] at hy
    exact hr.one_lt.ne hy
  have hcent : suzukiU a F ≤ Subgroup.centralizer (Subgroup.zpowers y : Set (suzukiGroup a F)) :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.1 hbot
  have hs : suzukiSElt a F 1 0 ∈ suzukiU a F := suzukiSElt_mem_suzukiU a F 1 0
  have hcomm : y * suzukiSElt a F 1 0 = suzukiSElt a F 1 0 * y :=
    Subgroup.mem_centralizer_iff.1 (hcent hs) y (Subgroup.mem_zpowers y)
  have hconj := suzukiDElt_conj' hF l 1 0
  rw [hl] at hconj
  have h1 : y * suzukiSElt a F 1 0 * y⁻¹ = suzukiSElt a F 1 0 := by
    rw [hcomm, mul_assoc, mul_inv_cancel, mul_one]
  rw [h1] at hconj
  obtain ⟨h1', -⟩ := (suzukiSElt_inj (a := a) (K := F)).1 hconj.symm
  apply hl1
  rw [mul_one] at h1'
  have h3 : l⁻¹ = 1 := Units.ext (h1'.trans Units.val_one.symm)
  exact inv_eq_one.1 h3

theorem exists_two_subgroup_of_suzuki {a : ℕ} {F : Type}
    [Field F] [Finite F] (hF : Nat.card F = 2 ^ (2 * a + 1)) {r : ℕ} (hr : r.Prime)
    (hr2 : r ≠ 2) (hrq : r ∣ 2 ^ (2 * a + 1) - 1) {x : suzukiGroup a F} (hx : orderOf x = r) :
    ∃ S : Subgroup (suzukiGroup a F), S ≠ ⊥ ∧ IsPGroup 2 S ∧
      x ∈ Subgroup.normalizer (S : Set (suzukiGroup a F)) ∧ ⁅S, Subgroup.zpowers x⁆ = S := by
  obtain ⟨g, hg⟩ := exists_conj_mem_suzukiT hF hr hr2 hrq hx
  have hconj : (MulAut.conj g⁻¹) x = g⁻¹ * x * g := by
    simp
  have hyord : orderOf (g⁻¹ * x * g) = r := by
    rw [← hconj, MulEquiv.orderOf_eq]
    exact hx
  refine S15K.exists_two_subgroup_of_mulEquiv (MulAut.conj g⁻¹) (a := x) ?_
  rw [hconj]
  exact exists_two_subgroup_of_suzukiT hF hr hr2 hg hyord

theorem exists_two_subgroup_of_suzukiModel {K : Type} [Group K]
    {f : ℕ} (hK : SuzukiModel K 2 f) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hpf : p ∣ 2 ^ f - 1)
    {b : K} (hb1 : b ≠ 1) (hbp : b ^ p = 1) :
    ∃ S : Subgroup K, S ≠ ⊥ ∧ IsPGroup 2 S ∧ b ∈ Subgroup.normalizer (S : Set K) ∧
      ⁅S, Subgroup.zpowers b⁆ = S := by
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨-, a, -, F, hFfield, hFfin, hf, hcard, ⟨e⟩⟩ := hK
  have hF : Nat.card F = 2 ^ (2 * a + 1) := by rw [hcard, hf]
  have hbord : orderOf b = p := orderOf_eq_prime hbp hb1
  have hxord : orderOf (e b) = p := by rw [MulEquiv.orderOf_eq]; exact hbord
  have hpq : p ∣ 2 ^ (2 * a + 1) - 1 := by rwa [← hf]
  exact S15K.exists_two_subgroup_of_mulEquiv e (exists_two_subgroup_of_suzuki hF hp hp2 hpq hxord)

end CFSG.RankThree.PartOne.K133
