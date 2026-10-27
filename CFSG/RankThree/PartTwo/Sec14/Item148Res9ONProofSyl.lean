module

public import Mathlib.GroupTheory.Transfer
public import Mathlib.GroupTheory.IsPerfect

public section

namespace CFSG.RankThree.PartTwo.Sec14.Res9ON

theorem commutator_eq_bot_of_isMulCommutative {X : Type*} [Group X] {P : Subgroup X}
    (hP : IsMulCommutative P) : _root_.commutator ↥P = ⊥ := by
  rw [commutator_def, eq_bot_iff, Subgroup.commutator_le]
  intro a _ b _
  rw [Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm]
  exact hP.is_comm.comm a b

theorem not_isMulCommutative_of_isPerfect {X : Type*} [Group X] [Finite X]
    (hX : Group.IsPerfect X) {p : ℕ} {z : X} (hz : z ∈ Subgroup.center X) (hzp : orderOf z = p)
    {P : Subgroup X} (hP : ¬ p ∣ P.index) : ¬ IsMulCommutative P := by
  intro hPc
  let ϕ : ↥P →* Abelianization ↥P := Abelianization.of
  have htriv : MonoidHom.transfer ϕ z = 1 := by
    have hker : _root_.commutator X ≤ (MonoidHom.transfer ϕ).ker :=
      Abelianization.commutator_subset_ker _
    rw [hX.commutator_eq_top] at hker
    exact hker (Subgroup.mem_top z)
  have hkey : ∀ (k : ℕ) (g₀ : X), g₀⁻¹ * z ^ k * g₀ ∈ P → g₀⁻¹ * z ^ k * g₀ = z ^ k := by
    intro k g₀ _
    have hzk : z ^ k ∈ Subgroup.center X := Subgroup.pow_mem _ hz k
    have hc : g₀ * z ^ k = z ^ k * g₀ := Subgroup.mem_center_iff.mp hzk g₀
    calc g₀⁻¹ * z ^ k * g₀ = g₀⁻¹ * (z ^ k * g₀) := by rw [mul_assoc]
      _ = g₀⁻¹ * (g₀ * z ^ k) := by rw [hc]
      _ = z ^ k := by group
  have h1 := MonoidHom.transfer_eq_pow ϕ z hkey
  rw [htriv] at h1
  have h2 : (⟨z ^ P.index, MonoidHom.transfer_eq_pow_aux z hkey⟩ : ↥P) ∈ ϕ.ker := by
    rw [MonoidHom.mem_ker, ← h1]
  rw [Abelianization.ker_of, commutator_eq_bot_of_isMulCommutative hPc, Subgroup.mem_bot] at h2
  have h3 : z ^ P.index = 1 := congrArg Subtype.val h2
  exact hP (hzp ▸ orderOf_dvd_of_pow_eq_one h3)

theorem exists_ne_comm_of_isPerfect {X : Type*} [Group X] [Finite X]
    (hX : Group.IsPerfect X) {p : ℕ} {z : X} (hz : z ∈ Subgroup.center X) (hzp : orderOf z = p)
    {P : Subgroup X} (hP : ¬ p ∣ P.index) :
    ∃ x ∈ P, ∃ y ∈ P, x * y ≠ y * x := by
  by_contra hne
  push Not at hne
  exact not_isMulCommutative_of_isPerfect hX hz hzp hP
    ⟨⟨fun a b => Subtype.ext (hne a a.2 b b.2)⟩⟩

end CFSG.RankThree.PartTwo.Sec14.Res9ON
