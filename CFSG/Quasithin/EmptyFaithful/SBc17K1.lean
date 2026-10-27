module

public import CFSG.Quasithin.EmptyFaithful.S14612DA
public import CFSG.Quasithin.EmptyFaithful.S146F21

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits
open scoped commutatorElement

namespace SBc17

variable {G : Type} [Group G]

theorem seventeen_dvd_card_of_sl2_sixteen [Finite G] {K : Subgroup G}
    (hφ : Nonempty (OTwoQuot K ≃* Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 4))) :
    17 ∣ Nat.card ↥K := by
  obtain ⟨φ⟩ := hφ
  have : Fintype (GaloisField 2 4) := Fintype.ofFinite _
  have hq : Fintype.card (GaloisField 2 4) = 16 := by
    rw [← Nat.card_eq_fintype_card, GaloisField.card 2 4 (by norm_num)]
    norm_num
  have hSL : Nat.card (Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 4)) = 4080 := by
    rw [Matrix.card_SL_field 2, hq, Fin.prod_univ_two]
    norm_num
  have h1 : Nat.card (OTwoQuot K) = 4080 := by
    rw [Nat.card_congr φ.toEquiv, hSL]
  have h2 := Subgroup.card_eq_card_quotient_mul_card_subgroup (CFSG.Open.pCore 2 ↥K)
  have h3 : Nat.card ↥K = Nat.card (OTwoQuot K) * Nat.card ↥(CFSG.Open.pCore 2 ↥K) := h2
  rw [h3, h1]
  exact Dvd.dvd.mul_right (by norm_num) _

omit [Group G] in
theorem exists_rotation_of_odd {p : ℕ} [NeZero p] {d : DihedralGroup p} (hd : Odd (orderOf d)) :
    ∃ i : ZMod p, d = DihedralGroup.r i := by
  rcases d with i | i
  · exact ⟨i, rfl⟩
  · rw [DihedralGroup.orderOf_sr] at hd
    exact absurd hd (by decide)

theorem commutator_oTwoUpper_le {T M H H₀ H₁ H₂ : Subgroup G} {p : ℕ} {t : G} [NeZero p]
    (hdec : IsDecP T M H p H₀ H₁ H₂ t) :
    ⁅oTwoUpper H₁, oTwoUpper H₁⁆ ≤ pCoreOf 2 H := by
  obtain ⟨hN, ⟨e⟩⟩ := hdec.dihedral₁
  let π : ↥H₁ →* DihedralGroup p :=
    (e : (↥H₁ ⧸ (pCoreOf 2 H).subgroupOf H₁) →* DihedralGroup p).comp
      (QuotientGroup.mk' ((pCoreOf 2 H).subgroupOf H₁))
  let R : Subgroup (DihedralGroup p) := Subgroup.zpowers (DihedralGroup.r 1)
  have hRc : ∀ u ∈ R, ∀ v ∈ R, u * v = v * u := by
    intro u hu v hv
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hu
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hv
    exact (Commute.zpow_zpow_self (DihedralGroup.r 1) i j).eq
  have hrot : ∀ i : ZMod p, (DihedralGroup.r i : DihedralGroup p) ∈ R := by
    intro i
    refine Subgroup.mem_zpowers_iff.mpr ⟨(i.val : ℤ), ?_⟩
    rw [zpow_natCast, DihedralGroup.r_one_pow, ZMod.natCast_zmod_val]
  have hmem : ∀ x (hx : x ∈ oTwoUpper H₁), π ⟨x, oTwoUpper_le H₁ hx⟩ ∈ R := by
    intro x hx
    induction hx using Subgroup.closure_induction with
    | mem y hy =>
      obtain ⟨i, hi⟩ := exists_rotation_of_odd (d := π ⟨y, hy.1⟩) (by
        have h1 : orderOf (π ⟨y, hy.1⟩) ∣ orderOf (⟨y, hy.1⟩ : ↥H₁) := orderOf_map_dvd _ _
        rw [Subgroup.orderOf_mk] at h1
        exact Odd.of_dvd_nat hy.2 h1)
      rw [hi]
      exact hrot i
    | one =>
      have h1 : (⟨1, oTwoUpper_le H₁ (one_mem _)⟩ : ↥H₁) = 1 := rfl
      rw [h1, map_one]
      exact R.one_mem
    | mul y z hy hz ihy ihz =>
      have : (⟨y * z, oTwoUpper_le H₁ (mul_mem hy hz)⟩ : ↥H₁) = ⟨y, oTwoUpper_le H₁ hy⟩ * ⟨z, oTwoUpper_le H₁ hz⟩ := rfl
      rw [this, map_mul]
      exact R.mul_mem ihy ihz
    | inv y hy ihy =>
      have : (⟨y⁻¹, oTwoUpper_le H₁ (inv_mem hy)⟩ : ↥H₁) = (⟨y, oTwoUpper_le H₁ hy⟩ : ↥H₁)⁻¹ := rfl
      rw [this, map_inv]
      exact R.inv_mem ihy
  refine Subgroup.commutator_le.mpr fun x hx y hy => ?_
  have hxH := oTwoUpper_le H₁ hx
  have hyH := oTwoUpper_le H₁ hy
  have h1 : π ⟨x, hxH⟩ * π ⟨y, hyH⟩ = π ⟨y, hyH⟩ * π ⟨x, hxH⟩ :=
    hRc _ (hmem x hx) _ (hmem y hy)
  have h2 : π ⁅(⟨x, hxH⟩ : ↥H₁), ⟨y, hyH⟩⁆ = 1 := by
    rw [map_commutatorElement]
    exact commutatorElement_eq_one_iff_mul_comm.mpr h1
  have h3 : (QuotientGroup.mk ⁅(⟨x, hxH⟩ : ↥H₁), ⟨y, hyH⟩⁆ :
      ↥H₁ ⧸ (pCoreOf 2 H).subgroupOf H₁) = 1 := by
    apply e.injective
    rw [map_one]
    exact h2
  have h4 := (QuotientGroup.eq_one_iff _).mp h3
  rw [Subgroup.mem_subgroupOf] at h4
  simpa [commutatorElement_def] using h4

theorem kOne_dichotomy [Finite G] {T M H H₀ H₁ H₂ K₁ K₂ : Subgroup G} {p : ℕ} {t s : G}
    (hp5 : p = 5) (hdec : IsDecP T M H p H₀ H₁ H₂ t) (hset : Setup14615 T M H H₁ H₂ K₁ K₂ s) :
    IsPGroup 2 ↥⁅K₁, K₁⁆ ∨ 17 ∣ Nat.card ↥K₁ := by
  rcases hset.shape with ⟨-, -, -, hφ⟩ | ⟨hK₁e, -⟩
  · exact Or.inr (seventeen_dvd_card_of_sl2_sixteen hφ)
  · left
    subst hK₁e
    have : NeZero p := ⟨by omega⟩
    have hle := commutator_oTwoUpper_le hdec
    exact (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 H).to_le hle

end SBc17

end CFSG.Quasithin
