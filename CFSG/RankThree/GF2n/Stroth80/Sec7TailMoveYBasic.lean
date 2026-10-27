module

public import CFSG.RankThree.GF2n.Stroth80.Sec7TailMoveFrameAPI
public import CFSG.RankThree.GF2n.Stroth80.Sec7TailMoveGroup

public section

namespace CFSG.RankThree.GF2n.Stroth80

open Subgroup CFSG.CGT.Timmesfeld75
open scoped commutatorElement

variable {K E X : Type*} [Field K] [AddCommGroup E] [Module K E] [FiniteDimensional K E]
  [Group X] [Finite X]
  {B : LinearMap.BilinForm K E} {φ : X →* (E ≃ₗ[K] E)} {V L Nb Rb : Subgroup X}
  {Tt : X → Submodule K E} {q : ℕ}

theorem natCard_conjSubgroup_eq {G : Type*} [Group G] (g : G) (T : Subgroup G) :
    Nat.card (conjSubgroup g T) = Nat.card T :=
  Subgroup.card_map_of_injective (MulAut.conj g).injective

theorem isPGroup_two_zpowers_of_sq {k : X} (hk : k * k = 1) : IsPGroup 2 (zpowers k) := by
  have hk2 : k ^ 2 = 1 := by
    rw [pow_two]
    exact hk
  have hord : orderOf k ∣ 2 := orderOf_dvd_of_pow_eq_one hk2
  rw [IsPGroup.iff_card]
  rcases (Nat.dvd_prime Nat.prime_two).mp hord with h1 | h1
  · exact ⟨0, by simp [Nat.card_zpowers, h1]⟩
  · exact ⟨1, by simp [Nat.card_zpowers, h1]⟩

theorem MoveFrame.not_mem_normalizer_of_not_forall (F : MoveFrame B φ V L Nb Rb Tt q) (h : X)
    (hN : ¬ ∀ a ∈ V, h * a * h⁻¹ ∈ Nb) : h ∉ normalizer (V : Set X) := by
  intro hnorm
  apply hN
  intro b hb
  have hbV : h * b * h⁻¹ ∈ V := (Subgroup.mem_normalizer_iff.mp hnorm b).mp hb
  exact F.L_le_Nb (F.V_le_L hbV)

theorem MoveFrame.Y_comm_V (F : MoveFrame B φ V L Nb Rb Tt q) (h : X)
    (hK : ∀ a ∈ V, h * a * h⁻¹ ∈ normalizer (V : Set X))
    (hN : ¬ ∀ a ∈ V, h * a * h⁻¹ ∈ Nb)  :
  ∀ v ∈ V, ∀ a ∈ V, v * (h * a * h⁻¹) = (h * a * h⁻¹) * v := by
  have hYK : ∀ y ∈ conjSubgroup h V, y ∈ normalizer (V : Set X) := by
    intro y hy
    obtain ⟨a, ha, rfl⟩ := mem_conjSubgroup_iff'.mp hy
    exact hK a ha
  have hti : ∀ g : X, ∀ y ∈ conjSubgroup h V, y ≠ 1 → g * y * g⁻¹ ∈ conjSubgroup h V →
      g ∈ normalizer ((conjSubgroup h V : Subgroup X) : Set X) :=
    fun g y hy hy1 hgy => F.ti_conj h g hy hy1 hgy
  have hsq : ∀ y ∈ conjSubgroup h V, y * y = 1 := by
    intro y hy
    obtain ⟨a, ha, rfl⟩ := mem_conjSubgroup_iff'.mp hy
    have e : h * a * h⁻¹ * (h * a * h⁻¹) = h * (a * a) * h⁻¹ := by group
    rw [e, F.V_sq a ha, mul_one, mul_inv_cancel]
  have hcomm : ∀ a ∈ conjSubgroup h V, ∀ b ∈ conjSubgroup h V, a * b = b * a := by
    intro a ha b hb
    obtain ⟨a', ha', rfl⟩ := mem_conjSubgroup_iff'.mp ha
    obtain ⟨b', hb', rfl⟩ := mem_conjSubgroup_iff'.mp hb
    have e1 : h * a' * h⁻¹ * (h * b' * h⁻¹) = h * (a' * b') * h⁻¹ := by group
    have e2 : h * b' * h⁻¹ * (h * a' * h⁻¹) = h * (b' * a') * h⁻¹ := by group
    rw [e1, e2, F.V_comm a' ha' b' hb']
  have hle : conjSubgroup h V ≤ normalizer (V : Set X) := by
    intro y hy
    exact hYK y hy
  have hsl := F.semilinear (conjSubgroup h V) hle hsq hcomm
  have hY4 : 4 ≤ Nat.card ↥(conjSubgroup h V) := by
    rw [natCard_conjSubgroup_eq, F.V_card]
    exact F.q_ge
  have hVY : V ⊓ conjSubgroup h V = ⊥ := by
    rw [Subgroup.eq_bot_iff_forall]
    intro x hx
    obtain ⟨hxV, hxY⟩ := Subgroup.mem_inf.mp hx
    obtain ⟨a, ha, rfl⟩ := mem_conjSubgroup_iff'.mp hxY
    by_contra hne
    have ha1 : a ≠ 1 := by
      rintro rfl
      apply hne
      simp
    exact F.not_mem_normalizer_of_not_forall h hN (F.ti h a ha ha1 hxV)
  have key := comm_of_semilinear V (conjSubgroup h V) hYK hti hsl hY4 hVY
  intro v hv a ha
  exact key v hv (h * a * h⁻¹) (mem_conjSubgroup_iff'.mpr ⟨a, ha, rfl⟩)

theorem MoveFrame.Y_inf_V (F : MoveFrame B φ V L Nb Rb Tt q) (h : X)
    (hK : ∀ a ∈ V, h * a * h⁻¹ ∈ normalizer (V : Set X))
    (hN : ¬ ∀ a ∈ V, h * a * h⁻¹ ∈ Nb)  :
  ∀ a ∈ V, a ≠ 1 → h * a * h⁻¹ ∉ V := by
  intro a ha ha1 hmem
  exact F.not_mem_normalizer_of_not_forall h hN (F.ti h a ha ha1 hmem)

theorem MoveFrame.Y_le_Rb (F : MoveFrame B φ V L Nb Rb Tt q) (h : X)
    (hK : ∀ a ∈ V, h * a * h⁻¹ ∈ normalizer (V : Set X))
    (hN : ¬ ∀ a ∈ V, h * a * h⁻¹ ∈ Nb)  :
  ∀ a ∈ V, h * a * h⁻¹ ∈ Rb := by
  intro a ha
  have hkc : ∀ v ∈ V, (h * a * h⁻¹) * v = v * (h * a * h⁻¹) := fun v hv =>
    (F.Y_comm_V h hK hN v hv a ha).symm
  have hsq : (h * a * h⁻¹) * (h * a * h⁻¹) = 1 := by
    have e : h * a * h⁻¹ * (h * a * h⁻¹) = h * (a * a) * h⁻¹ := by group
    rw [e, F.V_sq a ha, mul_one, mul_inv_cancel]
  exact F.two_elements (h * a * h⁻¹) (hK a ha) hkc (isPGroup_two_zpowers_of_sq hsq)

theorem MoveFrame.Y_inf_Nb (F : MoveFrame B φ V L Nb Rb Tt q) (h : X)
    (hK : ∀ a ∈ V, h * a * h⁻¹ ∈ normalizer (V : Set X))
    (hN : ¬ ∀ a ∈ V, h * a * h⁻¹ ∈ Nb)  :
  ∀ a ∈ V, h * a * h⁻¹ ∈ Nb → a = 1 := by
  intro a₁ ha₁ hy₁
  by_contra ha₁1
  obtain ⟨a₀, ha₀, hy₀⟩ : ∃ a₀ ∈ V, h * a₀ * h⁻¹ ∉ Nb := by
    by_contra hc
    push_neg at hc
    exact hN hc
  have ha₀1 : a₀ ≠ 1 := by
    rintro rfl
    apply hy₀
    simp
  have hy₀Rb : h * a₀ * h⁻¹ ∈ Rb := F.Y_le_Rb h hK hN a₀ ha₀
  obtain ⟨w₀, hw₀, hw₀ne⟩ : ∃ w ∈ Tt 1, φ (h * a₀ * h⁻¹) w ≠ w := by
    by_contra hc
    push_neg at hc
    exact hy₀ (F.Rb_fix_Nb _ hy₀Rb hc)
  obtain ⟨a, ha, ha1⟩ := F.exists_ne_one
  rw [← F.range_opm_V ha ha1] at hw₀
  obtain ⟨z, rfl⟩ := LinearMap.mem_range.mp hw₀
  have hc0 : φ (h * a₀ * h⁻¹) * φ a = φ a * φ (h * a₀ * h⁻¹) := by
    rw [← map_mul, ← map_mul, F.Y_comm_V h hK hN a ha a₀ ha₀]
  have hc1 : φ a * φ (h * a₁ * h⁻¹) = φ (h * a₁ * h⁻¹) * φ a := by
    rw [← map_mul, ← map_mul, F.Y_comm_V h hK hN a ha a₁ ha₁]
  have hmem : opm (φ (h * a₀ * h⁻¹)) z ∈ LinearMap.range (opm (φ (h * a₁ * h⁻¹))) := by
    rw [F.Tt_range h a₁ ha₁ ha₁1, ← F.Tt_range h a₀ ha₀ ha₀1]
    exact LinearMap.mem_range_self _ z
  obtain ⟨z₁, hz₁⟩ := LinearMap.mem_range.mp hmem
  have hchain : opm (φ (h * a₀ * h⁻¹)) (opm (φ a) z) =
      opm (φ (h * a₁ * h⁻¹)) (opm (φ a) z₁) := by
    rw [opm_comm_of_comm hc0 z, ← hz₁, opm_comm_of_comm hc1 z₁]
  have hw1 : opm (φ a) z₁ ∈ Tt 1 := by
    rw [← F.range_opm_V ha ha1]
    exact LinearMap.mem_range_self _ z₁
  have hfix : φ (h * a₁ * h⁻¹) (opm (φ a) z₁) = opm (φ a) z₁ := F.Nb_fixes _ hy₁ _ hw1
  have hw0ne : opm (φ (h * a₀ * h⁻¹)) (opm (φ a) z) ≠ 0 := by
    rw [opm_apply]
    exact sub_ne_zero.mpr hw₀ne
  apply hw0ne
  rw [hchain, opm_apply, hfix, sub_self]

end CFSG.RankThree.GF2n.Stroth80
