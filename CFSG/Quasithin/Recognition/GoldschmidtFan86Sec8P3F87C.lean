module

public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec8P3F87V
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec4Loc
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec8Stmt3

public section

namespace CFSG.Quasithin.Fan86.F87

open SimpleGraph CFSG.Quasithin.F6.GoldAmL3T
open scoped Pointwise

variable {V G : Type*} [Group G] [MulAction G V] {Γ : SimpleGraph V}
  {F : FanTree Γ G} {L : ZLab Γ G} {α : V}

theorem z_mem_calpha (h7 : Fan7 F L) (D : D10Set L α) : L.z α ∈ D.calpha := by
  have : L.z α ∈ L.zGroup 2 α ⊓ D.calpha := by
    rw [(fan73b_dset h7 D).2]
    exact Subgroup.mem_zpowers _
  exact this.2

theorem finite_calpha (F : FanTree Γ G) (D : D10Set L α) : Finite ↥D.calpha := by
  have : Finite ↥(MulAction.stabilizer G α) := F.loc_finite α
  exact Finite.of_injective (Subgroup.inclusion (show D.calpha ≤ MulAction.stabilizer G α from
    fun g hg => F.nbrStab_le_stabilizer α (Subgroup.mem_inf.1 hg).1))
    (Subgroup.inclusion_injective _)

theorem eq_one_or_eq_of_sq {H : Type*} [Group H] [Finite H] [IsCyclic H] {b c : H}
    (hb1 : b ≠ 1) (hb : b ^ 2 = 1) (hc : c ^ 2 = 1) : c = 1 ∨ c = b := by
  classical
  have := Fintype.ofFinite H
  by_contra h
  push Not at h
  have hcard := IsCyclic.card_pow_eq_one_le (α := H) (n := 2) (by norm_num)
  have hsub : ({1, b, c} : Finset H) ⊆ Finset.univ.filter (fun x => x ^ 2 = 1) := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rcases hx with rfl | rfl | rfl
    · exact one_pow 2
    · exact hb
    · exact hc
  have h3 : ({1, b, c} : Finset H).card = 3 :=
    Finset.card_eq_three.2 ⟨1, b, c, hb1.symm, fun hac => h.1 hac.symm, fun hbc => h.2 hbc.symm,
      rfl⟩
  have := Finset.card_le_card hsub
  omega

theorem calpha_cases (h7 : Fan7 F L) (h84 : Fan84a F L) (D : D10Set L α) {c : G}
    (hc : c ∈ D.calpha) : orderOf c = 4 ∨ c = 1 ∨ c = L.z α := by
  obtain ⟨hcyc, hle⟩ := h84 α D
  have := finite_calpha F D
  have hz := z_mem_calpha h7 D
  have hzz : (⟨L.z α, hz⟩ : ↥D.calpha) ^ 2 = 1 :=
    Subtype.ext (by simpa [pow_two] using L.z_mul_self D.val)
  have hz1 : (⟨L.z α, hz⟩ : ↥D.calpha) ≠ 1 := fun h => L.z_ne_one D.val (congrArg Subtype.val h)
  have hzo : orderOf (⟨L.z α, hz⟩ : ↥D.calpha) = 2 := orderOf_eq_prime hzz hz1
  have h2 : 2 ∣ Nat.card ↥D.calpha := hzo ▸ orderOf_dvd_natCard _
  have hpos : 0 < Nat.card ↥D.calpha := Nat.card_pos
  have h4 : Nat.card ↥D.calpha = 2 ∨ Nat.card ↥D.calpha = 4 := by omega
  have hdvd : orderOf c ∣ 4 := by
    rw [← Subgroup.orderOf_mk c hc]
    refine (orderOf_dvd_natCard _).trans ?_
    rcases h4 with h | h
    · rw [h]
      norm_num
    · rw [h]
  have hle4 : orderOf c ≤ 4 := Nat.le_of_dvd (by norm_num) hdvd
  have hsq : orderOf c ≠ 4 → c ^ 2 = 1 := by
    intro hne
    refine orderOf_dvd_iff_pow_eq_one.1 ?_
    interval_cases hoc : orderOf c <;> simp_all
  by_cases h4c : orderOf c = 4
  · exact Or.inl h4c
  · right
    have hc2 := hsq h4c
    have hcc : (⟨c, hc⟩ : ↥D.calpha) ^ 2 = 1 := Subtype.ext hc2
    rcases eq_one_or_eq_of_sq hz1 hzz hcc with h | h
    · exact Or.inl (congrArg Subtype.val h)
    · exact Or.inr (congrArg Subtype.val h)

theorem calpha_sq (h7 : Fan7 F L) (h84 : Fan84a F L) (D : D10Set L α) {c : G}
    (hc : c ∈ D.calpha) (h4 : orderOf c = 4) : c * c = L.z α := by
  rcases calpha_cases h7 h84 D (mul_mem hc hc) with h | h | h
  · have : orderOf (c * c) = 2 := by
      rw [← pow_two, orderOf_pow' _ (by norm_num), h4]
      norm_num
    omega
  · exfalso
    have : c ^ 2 = 1 := by rw [pow_two, h]
    have := orderOf_dvd_of_pow_eq_one this
    rw [h4] at this
    omega
  · exact h

theorem calpha_eq_zpowers (h84 : Fan84a F L) (D : D10Set L α) {c : G}
    (hc : c ∈ D.calpha) (h4 : orderOf c = 4) : D.calpha = Subgroup.zpowers c := by
  obtain ⟨-, hle⟩ := h84 α D
  have := finite_calpha F D
  refine (Subgroup.eq_of_le_of_card_ge (H := Subgroup.zpowers c) (K := D.calpha) ?_ ?_).symm
  · exact (Subgroup.zpowers_le).2 hc
  · rw [Nat.card_zpowers, h4]
    exact hle

theorem exists_vc (h7 : Fan7 F L) (h84 : Fan84a F L) (D : D10Set L α) {h : G}
    (hh : h ∈ ballStab Γ G 2 α) :
    h ∈ L.zGroup 2 α ∨ ∃ v ∈ L.zGroup 2 α, ∃ c ∈ D.calpha, orderOf c = 4 ∧ h = v * c := by
  have h71c : Fan71c F L := h7.2.2.1
  have hCN : D.calpha ≤ Subgroup.normalizer (L.zGroup 2 α : Set G) := by
    intro c hc
    rw [Subgroup.mem_normalizer_iff]
    have hcH := calpha_le_ballStab h7 D hc
    have hcH' := inv_mem hcH
    intro g
    constructor
    · intro hv
      have : c * g * c⁻¹ = g := by rw [ballStab_comm h71c hcH hv, mul_inv_cancel_right]
      rw [this]
      exact hv
    · intro hv
      have h1 := ballStab_comm h71c hcH' hv
      have : g = c * g * c⁻¹ := by
        calc g = c⁻¹ * (c * g * c⁻¹) * c := by group
          _ = (c * g * c⁻¹) * c⁻¹ * c := by rw [h1]
          _ = c * g * c⁻¹ := by group
      exact this.symm ▸ hv
  have hmul : (↑(D.calpha ⊔ L.zGroup 2 α) : Set G) =
      (D.calpha : Set G) * (L.zGroup 2 α : Set G) :=
    Subgroup.coe_mul_of_left_le_normalizer_right _ _ hCN
  have hh' : h ∈ D.calpha ⊔ L.zGroup 2 α := by
    rw [sup_comm, ← (fan73b_dset h7 D).1]
    exact hh
  rw [← SetLike.mem_coe, hmul] at hh'
  obtain ⟨c, hc, v, hv, hcvh⟩ := hh'
  have hcvh' : c * v = h := hcvh
  subst hcvh'
  have hcv : c * v = v * c := ballStab_comm h71c (calpha_le_ballStab h7 D hc) hv
  rcases calpha_cases h7 h84 D hc with h4 | h1 | hz
  · exact Or.inr ⟨v, hv, c, hc, h4, hcv⟩
  · left
    rw [h1, one_mul]
    exact hv
  · left
    rw [hz]
    exact mul_mem (z_mem_zGroup (by simp) D.val) hv

end CFSG.Quasithin.Fan86.F87
