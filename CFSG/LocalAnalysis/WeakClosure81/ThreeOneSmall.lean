module

public import CFSG.Quasithin.Background.A1bBasic

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin Equiv

namespace ThreeOne

variable {Ω : Type*} [Fintype Ω] [DecidableEq Ω]

theorem card_mul_pred_dvd_card (h2 : 2 ≤ Fintype.card Ω) {K : Subgroup (Perm Ω)}
    (hK : MulAction.IsMultiplyPretransitive K Ω 2) :
    Fintype.card Ω * (Fintype.card Ω - 1) ∣ Nat.card K := by
  classical
  haveI : Nontrivial Ω := Fintype.one_lt_card_iff_nontrivial.mp (by omega)
  obtain ⟨x, y, hxy⟩ := exists_pair_ne Ω
  have hncard : ({x, y} : Set Ω).ncard = 2 := Set.ncard_pair hxy
  have hidx := MulAction.IsMultiplyPretransitive.index_of_fixingSubgroup_eq (G := K)
    ({x, y} : Set Ω) (by rwa [hncard])
  have hdvd : (fixingSubgroup K ({x, y} : Set Ω)).index ∣ Nat.card K :=
    Subgroup.index_dvd_card _
  rw [hidx, hncard] at hdvd
  have hfac : Nat.choose (Nat.card Ω) 2 * Nat.factorial 2
      = Fintype.card Ω * (Fintype.card Ω - 1) := by
    rw [Nat.mul_comm, ← Nat.descFactorial_eq_factorial_mul_choose, Nat.card_eq_fintype_card,
      Nat.descFactorial_succ, Nat.descFactorial_one, Nat.mul_comm]
  rwa [hfac] at hdvd

theorem card_alternatingGroup_dvd_factorial (h5 : 5 ≤ Fintype.card Ω) {K : Subgroup (Perm Ω)}
    (hK : K ≤ alternatingGroup Ω) (hne : K ≠ alternatingGroup Ω) :
    Nat.card (alternatingGroup Ω) ∣ (K.relIndex (alternatingGroup Ω)).factorial := by
  classical
  haveI : IsSimpleGroup (alternatingGroup Ω) :=
    alternatingGroup.isSimpleGroup (by simpa [Nat.card_eq_fintype_card] using h5)
  let K' : Subgroup (alternatingGroup Ω) := K.subgroupOf (alternatingGroup Ω)
  have hK'ne : K' ≠ ⊤ := by
    intro h
    exact hne (le_antisymm hK (Subgroup.subgroupOf_eq_top.1 h))
  have hnc : K'.normalCore = ⊥ := by
    rcases Subgroup.Normal.eq_bot_or_eq_top K'.normalCore with h | h
    · exact h
    · exact absurd (top_le_iff.1 (h ▸ K'.normalCore_le)) hK'ne
  have hdvd := Subgroup.index_normalCore_dvd_factorial_index K'
  rw [hnc, Subgroup.index_bot] at hdvd
  simpa only [K', Subgroup.relIndex] using hdvd

theorem isSylowIn_inf_alternatingGroup {T : Subgroup (Perm Ω)} (hT : IsSylowIn 2 T ⊤) :
    IsSylowIn 2 (T ⊓ alternatingGroup Ω) (alternatingGroup Ω) :=
  hT.inf_normal le_top inferInstance

theorem two_mul_card_inf_alternatingGroup {T : Subgroup (Perm Ω)} (hT : IsSylowIn 2 T ⊤)
    (h2 : 2 ≤ Fintype.card Ω) : 2 * Nat.card ↥(T ⊓ alternatingGroup Ω) = Nat.card T := by
  classical
  haveI : Nontrivial Ω := Fintype.one_lt_card_iff_nontrivial.mp (by omega)
  have hnotle : ¬ T ≤ alternatingGroup Ω := by
    intro hle
    have hprod : T.relIndex (alternatingGroup Ω) * (alternatingGroup Ω).relIndex ⊤
        = T.relIndex ⊤ :=
      Subgroup.relIndex_mul_relIndex (H := T) (K := alternatingGroup Ω) (L := ⊤) hle le_top
    have h2dvd : 2 ∣ T.relIndex ⊤ := by
      rw [← hprod, Subgroup.relIndex_top_right, alternatingGroup.index_eq_two]
      exact dvd_mul_left 2 _
    exact hT.2.2 h2dvd
  have hex : ∃ t : T, Perm.sign t.1 = -1 := by
    by_contra h
    apply hnotle
    intro x hx
    rw [Equiv.Perm.mem_alternatingGroup]
    rcases Int.units_eq_one_or (Perm.sign x) with h1 | h1
    · exact h1
    · exact absurd h1 fun hx' => h ⟨⟨x, hx⟩, hx'⟩
  obtain ⟨t, ht⟩ := hex
  let f : T →* ℤˣ := Perm.sign.comp T.subtype
  have hf : f t = -1 := by simpa [f] using ht
  have hrange : f.range = ⊤ := by
    refine eq_top_iff.2 ?_
    intro u _
    rcases Int.units_eq_one_or u with rfl | rfl
    · exact ⟨1, map_one f⟩
    · exact ⟨t, hf⟩
  have hker : f.ker = (T ⊓ alternatingGroup Ω).subgroupOf T := by
    ext x
    simp [MonoidHom.mem_ker, f, Subgroup.mem_subgroupOf, Equiv.Perm.mem_alternatingGroup]
  have hcard_range : Nat.card f.range = 2 := by
    rw [hrange, Subgroup.card_top, Nat.card_eq_fintype_card, Fintype.card_units_int]
  have hcard_ker : Nat.card f.ker = Nat.card ↥(T ⊓ alternatingGroup Ω) := by
    rw [hker]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv
  have hcard := Subgroup.card_ker_mul_card_range f
  rw [hcard_range, hcard_ker] at hcard
  omega

theorem card_eq_of_isSylowIn_top {G : Type*} [Group G] [Finite G] {T : Subgroup G}
    (hT : IsSylowIn 2 T ⊤) {k m : ℕ} (hG : Nat.card G = 2 ^ k * m) (hm : ¬ 2 ∣ m) :
    Nat.card T = 2 ^ k := by
  have hm0 : m ≠ 0 := fun h => hm (h ▸ dvd_zero 2)
  have hfac : (2 ^ k * m).factorization 2 = k := by
    rw [Nat.factorization_mul (pow_ne_zero k (by norm_num)) hm0, Finsupp.add_apply,
      Nat.factorization_pow_self Nat.prime_two, Nat.factorization_eq_zero_of_not_dvd hm, add_zero]
  have h := hT.card_eq
  rw [Subgroup.card_top, hG, hfac] at h
  exact h

end ThreeOne

end CFSG.LocalAnalysis.WeakClosure81

end
