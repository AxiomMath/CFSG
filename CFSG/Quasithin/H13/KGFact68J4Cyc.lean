module

public import CFSG.Quasithin.H13.KGFact68SporCyc
public import CFSG.Quasithin.H13.KGFact1468Spor

public section

namespace CFSG.Quasithin.H13.KG68

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Sporadic.J4Schreier CFSG.Sporadic.J4

theorem comm_of_mem_center {G : Type*} [Group G] {S : Subgroup G} (z : Subgroup.center ↥S)
    {s : G} (hs : s ∈ S) : s * ((z : ↥S) : G) = ((z : ↥S) : G) * s := by
  have := Subgroup.mem_center_iff.mp z.2 ⟨s, hs⟩
  exact congrArg Subtype.val this

theorem isCyclic_center_of_map {G H : Type*} [Group G] [Group H] (ψ : G ≃* H) {T : Subgroup G}
    {S : Subgroup H} (hψ : T.map ψ.toMonoidHom = S) (hS : IsCyclic (Subgroup.center ↥S)) :
    IsCyclic (Subgroup.center ↥T) := by
  let eT : ↥T ≃* ↥S := (ψ.subgroupMap T).trans (MulEquiv.subgroupCongr hψ)
  exact isCyclic_of_surjective (Subgroup.centerCongr eT).symm.toMonoidHom
    (Subgroup.centerCongr eT).symm.surjective

theorem fix_kgen : ∀ a < 2 ^ 11, (∀ i < 4, app11 generatorColumns[i]! a = a) → a = 0 ∨ a = 1 := by
  decide +kernel

theorem generatorColumns_lt : ∀ i < 4, ∀ j < 11, (generatorColumns[i]!)[j]?.getD 0 < 2 ^ 11 := by
  decide +kernel

theorem center_S0_mem
    (z : Subgroup.center ↥(S0Sylow : Subgroup J)) :
    ((z : ↥(S0Sylow : Subgroup J)) : J) = 1 ∨ ((z : ↥(S0Sylow : Subgroup J)) : J) = η 1 := by
  have hNS : N ≤ (S0Sylow : Subgroup J) := by
    rw [S0Sylow_coe]
    exact N_le_S0
  have hUS : U ≤ (S0Sylow : Subgroup J) := by
    rw [S0Sylow_coe]
    exact U_le_S0
  have hcomm : ∀ s ∈ (S0Sylow : Subgroup J),
      s * ((z : ↥(S0Sylow : Subgroup J)) : J) = ((z : ↥(S0Sylow : Subgroup J)) : J) * s :=
    fun s hs => @comm_of_mem_center J (Subgroup.toGroup J) _ z s hs
  have hzN : ((z : ↥(S0Sylow : Subgroup J)) : J) ∈ N := by
    rw [← KG1468.j4_centralizer_N, Subgroup.mem_centralizer_iff]
    intro n hn
    exact hcomm n (hNS hn)
  obtain ⟨a, ha, hza⟩ := exists_η_eq hzN
  have hfix : ∀ i < 4, app11 generatorColumns[i]! a = a := by
    intro i hi
    have hk : kgen i ∈ (S0Sylow : Subgroup J) :=
      hUS (Subgroup.subset_closure ⟨⟨i, hi⟩, rfl⟩)
    have h1 := kgen_acts hi a
    have h2 : kgen i * η a * (kgen i)⁻¹ = η a := by
      rw [hza, hcomm _ hk, mul_inv_cancel_right]
    rw [h2] at h1
    exact η_injOn (vecMulN_lt (generatorColumns_lt i hi) a) ha h1.symm
  rcases fix_kgen a ha hfix with rfl | rfl
  · left
    rw [← hza, η_zero]
  · right
    exact hza.symm

theorem isCyclic_center_S0 :
    IsCyclic (Subgroup.center ↥(S0Sylow : Subgroup J)) := by
  have hinj : Function.Injective fun z : Subgroup.center ↥(S0Sylow : Subgroup J) =>
      decide (((z : ↥(S0Sylow : Subgroup J)) : J) = 1) := by
    intro z₁ z₂ h
    simp only at h
    apply Subtype.ext
    apply Subtype.ext
    rcases center_S0_mem z₁ with h1 | h1 <;> rcases center_S0_mem z₂ with h2 | h2
    · rw [h1, h2]
    · exfalso
      rw [h1, h2] at h
      have hη : η 1 ≠ 1 := by
        intro h'
        have := η_injOn (i := 1) (k := 0) (by norm_num) (by norm_num) (h'.trans η_zero.symm)
        omega
      simp [hη] at h
    · exfalso
      rw [h1, h2] at h
      have hη : η 1 ≠ 1 := by
        intro h'
        have := η_injOn (i := 1) (k := 0) (by norm_num) (by norm_num) (h'.trans η_zero.symm)
        omega
      simp [hη] at h
    · rw [h1, h2]
  have hle : Nat.card (Subgroup.center ↥(S0Sylow : Subgroup J)) ≤ 2 := by
    have := Nat.card_le_card_of_injective _ hinj
    simpa using this
  have hpos : 0 < Nat.card (Subgroup.center ↥(S0Sylow : Subgroup J)) := Nat.card_pos
  interval_cases h : Nat.card (Subgroup.center ↥(S0Sylow : Subgroup J))
  · have : Subsingleton (Subgroup.center ↥(S0Sylow : Subgroup J)) :=
      (Nat.card_eq_one_iff_unique.mp h).1
    exact isCyclic_of_subsingleton
  · have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    exact isCyclic_of_prime_card h

open CFSG.Blueprint.NativeSporadic (Carrier) in
theorem j4SylowCenterCyclic_holds :
    J4SylowCenterCyclic := by
  intro T
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Finite J := Nat.finite_of_card_ne_zero (by rw [card_J4J]; norm_num)
  have : Finite (Carrier .J4) := Finite.of_equiv J (seedEquiv j4Facts.mat).symm.toEquiv
  have hS0 : IsSylowTwoOf (S0Sylow : Subgroup J) ⊤ :=
    K1.isSylowTwoOf_top_iff.mpr ⟨S0Sylow.isPGroup', S0Sylow.not_dvd_index⟩
  have hT : IsSylowTwoOf (T : Subgroup (Carrier .J4)) ⊤ :=
    K1.isSylowTwoOf_top_iff.mpr ⟨T.isPGroup', T.not_dvd_index⟩
  let eJ : Carrier .J4 ≃* J := seedEquiv j4Facts.mat
  obtain ⟨ψ, hψ⟩ := @KG1468.exists_map_sylow_eq J (Subgroup.toGroup J) _ _ hS0 (Carrier .J4) _ _
    eJ _ hT
  exact @isCyclic_center_of_map (Carrier .J4) J _ (Subgroup.toGroup J) ψ _ _ hψ
    isCyclic_center_S0

theorem sporadicSylowCenterCyclic_holds :
    SporadicSylowCenterCyclic :=
  sporadicSylowCenterCyclic_of_j4 j4SylowCenterCyclic_holds

end CFSG.Quasithin.H13.KG68
