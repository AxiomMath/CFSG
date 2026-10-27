module

public import CFSG.Quasithin.H13.NQCatT513Inner

public section

namespace CFSG.Quasithin.H13.NQCat.T513P

theorem card_map_mul_card_ker_inf {G H : Type*} [Group G] [Group H] (f : G →* H)
    (A : Subgroup G) : Nat.card ↥(A.map f) * Nat.card ↥(f.ker ⊓ A) = Nat.card ↥A := by
  set g : ↥A →* H := f.comp A.subtype with hg
  have h1 := Subgroup.card_ker_mul_card_range g
  have hrange : g.range = A.map f := by
    ext x
    simp only [MonoidHom.mem_range, Subgroup.mem_map, hg, MonoidHom.comp_apply,
      Subgroup.coe_subtype]
    constructor
    · rintro ⟨a, rfl⟩
      exact ⟨a, a.2, rfl⟩
    · rintro ⟨y, hy, rfl⟩
      exact ⟨⟨y, hy⟩, rfl⟩
  have hker : Nat.card g.ker = Nat.card ↥(f.ker ⊓ A) := by
    have : g.ker = f.ker.subgroupOf A := rfl
    rw [this, ← Subgroup.card_map_of_injective A.subtype_injective,
      Subgroup.subgroupOf_map_subtype]
  rw [hrange, hker] at h1
  linarith

theorem index_eq_one_of_simple {D : Type*} [Group D] [Finite D] [IsSimpleGroup D]
    (H : Subgroup D) (h : (H.index).factorial < Nat.card D) : H.index = 1 := by
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal H.normalCore with hb | ht
  · exfalso
    have hdvd := H.index_normalCore_dvd_factorial_index
    rw [hb, Subgroup.index_bot] at hdvd
    exact absurd (Nat.le_of_dvd (Nat.factorial_pos _) hdvd) (not_le.mpr h)
  · have : H = ⊤ := eq_top_iff.mpr (ht ▸ H.normalCore_le)
    rw [this, Subgroup.index_top]

theorem not_isSolvable_of_simple {D : Type*} [Group D] [IsSimpleGroup D]
    (h : ¬ (Nat.card D).Prime) : ¬ Group.IsSolvable D := by
  intro hs
  have hc := (IsSimpleGroup.comm_iff_isSolvable (G := D)).2 hs
  have : IsMulCommutative D := ⟨⟨hc⟩⟩
  exact h (Group.is_simple_iff_prime_card.1 inferInstance)

theorem card_alt5 : Nat.card (alternatingGroup (Fin 5)) = 60 := by
  rw [Nat.card_eq_fintype_card, card_alternatingGroup, Fintype.card_fin]
  decide

theorem alt5_le_of_sixty_dvd {R : Subgroup (Equiv.Perm (Fin 5))} (h60 : 60 ∣ Nat.card ↥R) :
    alternatingGroup (Fin 5) ≤ R := by
  set A := alternatingGroup (Fin 5) with hA
  have hAi : A.index = 2 := by
    have h := Subgroup.card_mul_index A
    rw [card_alt5, Nat.card_perm, Nat.card_fin] at h
    have : (Nat.factorial 5) = 120 := rfl
    omega
  have hAn : A.Normal := Subgroup.normal_of_index_eq_two hAi
  set c := Nat.card ↥(R ⊓ A) with hc
  have hcR : Nat.card ↥(A.subgroupOf R) = c := by
    rw [← Subgroup.card_map_of_injective R.subtype_injective, Subgroup.subgroupOf_map_subtype,
      inf_comm]
  have hcA : Nat.card ↥(R.subgroupOf A) = c := by
    rw [← Subgroup.card_map_of_injective A.subtype_injective, Subgroup.subgroupOf_map_subtype]
  have h1 := Subgroup.card_mul_index (A.subgroupOf R)
  have h2 := Subgroup.card_mul_index (R.subgroupOf A)
  rw [hcR] at h1
  rw [hcA, card_alt5] at h2
  have hrel : (A.subgroupOf R).index ∣ 2 := hAi ▸ Subgroup.relIndex_dvd_index_of_normal A R
  have hrel2 : (A.subgroupOf R).index ≤ 2 := Nat.le_of_dvd (by norm_num) hrel
  have hRpos : 60 ≤ Nat.card ↥R := Nat.le_of_dvd Nat.card_pos h60
  have hc30 : 30 ≤ c := by nlinarith
  have hidx : (R.subgroupOf A).index ≤ 2 := by nlinarith
  have hfact : ((R.subgroupOf A).index).factorial < Nat.card ↥A := by
    rw [card_alt5]
    have : ((R.subgroupOf A).index).factorial ≤ Nat.factorial 2 := Nat.factorial_le hidx
    have h2' : Nat.factorial 2 = 2 := rfl
    omega
  have hone := index_eq_one_of_simple (R.subgroupOf A) hfact
  exact Subgroup.relIndex_eq_one.mp hone

theorem false_of_sym5 {R : Subgroup (Equiv.Perm (Fin 5))} (h60 : 60 ∣ Nat.card ↥R)
    (U : Subgroup ↥R) (hidx : U.index ≤ 3) (hU : Group.IsSolvable ↥U) : False := by
  set A := alternatingGroup (Fin 5) with hA
  have hAR := alt5_le_of_sixty_dvd h60
  set A' : Subgroup ↥R := A.subgroupOf R with hA'
  let e : ↥A' ≃* ↥A := Subgroup.subgroupOfEquivOfLe hAR
  have : IsSimpleGroup ↥A' := e.isSimpleGroup
  have hcA' : Nat.card ↥A' = 60 := by rw [Nat.card_congr e.toEquiv, card_alt5]
  have hUi : U.index ≠ 0 := Subgroup.index_ne_zero_of_finite
  have hrel : (U.subgroupOf A').index ≤ 3 := by
    have h := Subgroup.relIndex_le_of_le_right (H := U) (le_top : A' ≤ ⊤)
      (by rw [Subgroup.relIndex_top_right]; exact hUi)
    rw [Subgroup.relIndex_top_right] at h
    exact h.trans hidx
  have hfact : ((U.subgroupOf A').index).factorial < Nat.card ↥A' := by
    rw [hcA']
    have : ((U.subgroupOf A').index).factorial ≤ Nat.factorial 3 := Nat.factorial_le hrel
    have h3 : Nat.factorial 3 = 6 := rfl
    omega
  have hAU : A' ≤ U := Subgroup.relIndex_eq_one.mp (index_eq_one_of_simple _ hfact)
  have hsA : Group.IsSolvable ↥A' :=
    Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective hAU)
  exact not_isSolvable_of_simple (D := ↥A') (by rw [hcA']; norm_num) hsA

end CFSG.Quasithin.H13.NQCat.T513P
