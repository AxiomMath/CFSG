module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154E3CycTwoP3M4AA2AABAAA

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Open CFSG.Quasithin Subgroup

variable {W : Type} [CommGroup W]

private theorem s16h_e3_CycTwoExp3_card_of_rank3_2 {X : Type*} [Group X]
    (hE : IsElemAbelianOfRank 3 2 X) : Nat.card X = 9 := by
  obtain ⟨e⟩ := hE
  rw [Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card]
  simp [Fintype.card_pi]

private theorem s16h_e3_CycTwoExp3_pow_of_rank3_2 {X : Type*} [Group X]
    (hE : IsElemAbelianOfRank 3 2 X) (x : X) : x ^ 3 = 1 := by
  obtain ⟨e⟩ := hE
  apply e.injective
  rw [map_pow, map_one]
  apply Multiplicative.toAdd.injective
  rw [toAdd_pow, toAdd_one]
  funext i
  rw [Pi.smul_apply, Pi.zero_apply, nsmul_eq_mul, ZMod.natCast_self, zero_mul]

theorem s16h_e3_CycTwoExp3_pow_three
    [Finite W] [Finite (MulAut W)]
    (hexp : ∀ w : W, w ^ 2 = 1) (hcard : Nat.card W = 2 ^ 4)
    {A : Subgroup (MulAut W)} (h2 : 2 ≤ CFSG.Open.pRank 3 A)
    {g : MulAut W} (hg : ∃ k : ℕ, orderOf g = 3 ^ k) : g ^ 3 = 1 := by
  obtain ⟨E, -, hE⟩ := s16h_e3_CycTwoP3M4AA2AABAAA_exists_elemAbelian hexp hcard h2
  have hEcard : Nat.card ↥E = 9 := s16h_e3_CycTwoExp3_card_of_rank3_2 hE
  have hEp : IsPGroup 3 ↥E := IsPGroup.of_card (n := 2) (by rw [hEcard]; norm_num)
  have hEidx : E.index = 2240 := by
    have h := Subgroup.card_mul_index E
    rw [hEcard, s16h_e3_CycTwoP3M4AA2AABAAA_aut_card hexp hcard] at h
    omega
  have hEnotdvd : ¬ 3 ∣ E.index := by rw [hEidx]; norm_num
  let S0 : Sylow 3 (MulAut W) := hEp.toSylow hEnotdvd
  have hS0exp : ∀ x : MulAut W, x ∈ S0 → x ^ 3 = 1 := by
    intro x hx
    have hxE : x ∈ E := (IsPGroup.mem_toSylow hEp hEnotdvd).mp hx
    have hx3 := s16h_e3_CycTwoExp3_pow_of_rank3_2 hE ⟨x, hxE⟩
    simpa using hx3
  obtain ⟨k, hk⟩ := hg
  have hgp : IsPGroup 3 (Subgroup.zpowers g) :=
    IsPGroup.of_card (n := k) (by rw [Nat.card_zpowers, hk])
  obtain ⟨S, hS⟩ := IsPGroup.exists_le_sylow hgp
  haveI : Finite (Sylow 3 (MulAut W)) := Sylow.finite_of_finiteIndex S0
  let e : S0 ≃* S := Sylow.equiv S0 S
  set y : S0 := e.symm ⟨g, hS (Subgroup.mem_zpowers g)⟩ with hy
  have h1 : e y = ⟨g, hS (Subgroup.mem_zpowers g)⟩ := by
    rw [hy]; exact e.apply_symm_apply _
  have hy3 : (y : S0) ^ 3 = 1 := Subtype.ext (hS0exp (y : MulAut W) y.2)
  have hge : (⟨g, hS (Subgroup.mem_zpowers g)⟩ : S) ^ 3 = 1 := by
    rw [← h1, ← map_pow, hy3, map_one]
  simpa using congrArg Subtype.val hge

theorem s16h_e3_CycTwoExp3_mem_of_normal
    [Finite W] [Finite (MulAut W)]
    (hexp : ∀ w : W, w ^ 2 = 1) (hcard : Nat.card W = 2 ^ 4)
    {A D : Subgroup (MulAut W)} (hDA : D ≤ A) (hD : IsElemAbelianOfRank 3 2 ↥D)
    (hDn : (D.subgroupOf A).Normal) {g : MulAut W} (hgA : g ∈ A)
    (hg : ∃ k : ℕ, orderOf g = 3 ^ k) : g ∈ D := by
  have hDcard : Nat.card ↥D = 9 := s16h_e3_CycTwoExp3_card_of_rank3_2 hD
  have hAcard_dvd : Nat.card ↥A ∣ Nat.card (MulAut W) := Subgroup.card_subgroup_dvd_card A
  have hA27 : ¬ 3 ^ 3 ∣ Nat.card ↥A := fun h =>
    s16h_e3_CycTwoP3M4AA2AABAAA_not_three_cube_dvd hexp hcard (h.trans hAcard_dvd)
  have hDsubcard : Nat.card ↥(D.subgroupOf A) = 9 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hDA).toEquiv, hDcard]
  have hDsubP : IsPGroup 3 ↥(D.subgroupOf A) :=
    IsPGroup.of_card (n := 2) (by rw [hDsubcard]; norm_num)
  have hnotdvd : ¬ 3 ∣ (D.subgroupOf A).index := by
    intro h3
    have hmul := Subgroup.card_mul_index (D.subgroupOf A)
    rw [hDsubcard] at hmul
    obtain ⟨m, hm⟩ := h3
    have h27 : 3 ^ 3 ∣ Nat.card ↥A := by
      rw [← hmul, hm]
      exact ⟨m, by ring⟩
    exact hA27 h27
  let P0 : Sylow 3 ↥A := hDsubP.toSylow hnotdvd
  have hP0normal : P0.Normal := by
    change (P0 : Subgroup ↥A).Normal
    rw [IsPGroup.toSylow_coe hDsubP hnotdvd]
    exact hDn
  haveI : Finite (Sylow 3 ↥A) := Sylow.finite_of_finiteIndex P0
  haveI : Unique (Sylow 3 ↥A) := Sylow.unique_of_normal P0 hP0normal
  obtain ⟨k, hk⟩ := hg
  have hgp : IsPGroup 3 (Subgroup.zpowers (⟨g, hgA⟩ : ↥A)) :=
    IsPGroup.of_card (n := k) (by rw [Nat.card_zpowers, Subgroup.orderOf_mk, hk])
  obtain ⟨S, hS⟩ := IsPGroup.exists_le_sylow hgp
  have hSP : S = P0 := Subsingleton.elim S P0
  have hmemP : (⟨g, hgA⟩ : ↥A) ∈ P0 := by
    have h1 := hS (Subgroup.mem_zpowers (⟨g, hgA⟩ : ↥A))
    rwa [hSP] at h1
  have hmemD : (⟨g, hgA⟩ : ↥A) ∈ D.subgroupOf A :=
    (IsPGroup.mem_toSylow hDsubP hnotdvd).mp hmemP
  exact Subgroup.mem_subgroupOf.mp hmemD

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
