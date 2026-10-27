module

public import CFSG.Quasithin.Background.E6EighteenE
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_19IdentEven
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_19IdentLieG2
public import CFSG.Dihedral.Glauberman.DicksonMaxUp
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.UnitaryKernelsRootCenter

public section

namespace CFSG.Quasithin

namespace E6

open CFSG.Open CFSG.QuasithinUnique CFSG.QuasithinUnique.Ch1
open BenderSuzuki.MatrixGroups CFSG.Glauberman.Dickson CFSG.Glauberman.Dickson.MaxUp

@[expose] def a7Four : alternatingGroup (Fin 7) :=
  ⟨Equiv.swap 0 1 * Equiv.swap 1 2 * Equiv.swap 2 3 * Equiv.swap 4 5,
    Equiv.Perm.mem_alternatingGroup.mpr (by decide)⟩

theorem a7Four_facts : a7Four ^ 4 = 1 ∧ a7Four ^ 2 ≠ 1 := by
  refine ⟨Subtype.ext ?_, fun h => ?_⟩
  · simp only [Subgroup.coe_pow, Subgroup.coe_one, a7Four]
    decide
  · have := congrArg Subtype.val h
    simp only [Subgroup.coe_pow, Subgroup.coe_one, a7Four] at this
    revert this
    decide

theorem IsA7Group.exists_two_elt {B : Type*} [Group B] [Finite B] (h : IsA7Group B) :
    ∃ y : B, y ^ 4 = 1 ∧ y ^ 2 ≠ 1 := by
  obtain ⟨⟨φ⟩, hZ⟩ := h
  obtain ⟨h4, h2⟩ := a7Four_facts
  obtain ⟨y₀, hy₀⟩ := QuotientGroup.mk_surjective (φ.symm a7Four)
  have hc : y₀ ^ 4 ∈ Subgroup.center B := by
    rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_pow, hy₀, ← map_pow, h4, map_one]
  have hcz : (y₀ ^ 4) ^ Nat.card (Subgroup.center B) = 1 := by
    have := pow_card_eq_one' (G := Subgroup.center B) (x := ⟨y₀ ^ 4, hc⟩)
    exact congrArg Subtype.val this
  have himg : ∀ n : ℕ, (QuotientGroup.mk (y₀ ^ n) : B ⧸ Subgroup.center B) =
      φ.symm (a7Four ^ n) := fun n => by
    rw [QuotientGroup.mk_pow, hy₀, map_pow]
  refine ⟨y₀ ^ Nat.card (Subgroup.center B), ?_, fun h1 => ?_⟩
  · rw [← pow_mul, mul_comm, pow_mul, hcz]
  · have h3 : a7Four ^ (2 * Nat.card (Subgroup.center B)) = 1 := by
      apply φ.symm.injective
      rw [map_one, ← himg, pow_mul, ← pow_mul, mul_comm, pow_mul, h1, QuotientGroup.mk_one]
    rcases hZ with hz | hz
    · rw [hz, mul_one] at h3
      exact h2 h3
    · rw [hz, show 2 * 3 = 4 + 2 by norm_num, pow_add, h4, one_mul] at h3
      exact h2 h3

theorem noA7Fix_psl2_even {X : Type} [Group X] [Finite X] {f : ℕ} (hf : 1 ≤ f)
    (h : Assembly.LowTwoRank.StatedClassicalModel X .PSL 2 2 f) : NoA7Fix X := by
  intro α _ _ hA
  obtain ⟨B, -, hB⟩ := hA
  obtain ⟨y, hy4, hy2⟩ := hB.exists_two_elt
  obtain ⟨-, F, _, _, hcard, ⟨e⟩⟩ := h
  let e' : X ≃* PSL2MatrixGroup F :=
    e.trans (CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj 2 F).symm
  set x : X := ((y : ↥(Id2519.fixSubgroup α)) : X) with hxdef
  have hx4 : x ^ (2 ^ 2) = 1 := by
    have := congrArg (fun z : ↥B => ((z : ↥(Id2519.fixSubgroup α)) : X)) hy4
    simpa [hxdef] using this
  have hz : (e' x) ^ (2 ^ 2) = 1 := by rw [← map_pow, hx4, map_one]
  have h2 := Id2519.two_power_sq_eq_one_psl2 hf hcard (e' x) hz
  have hx2 : x ^ 2 = 1 := e'.injective (by rw [map_pow, h2, map_one])
  apply hy2
  apply Subtype.ext
  apply Subtype.ext
  simpa [hxdef] using hx2

theorem noA7Fix_psl2_odd {X : Type} [Group X] [Finite X] {p : ℕ}
    (h : Assembly.LowTwoRank.StatedClassicalModel X .PSL 2 p 1) : NoA7Fix X := by
  intro α _ hne hA
  obtain ⟨B, hBc, hB⟩ := hA
  obtain ⟨hadm, F, _, _, hcard, ⟨e⟩⟩ := h
  have : Fact p.Prime := ⟨hadm.1⟩
  have hp2 : p ≠ 2 := by
    rintro rfl
    exact hadm.2.2.2.1 (by simp)
  let e' : X ≃* PSL2MatrixGroup F :=
    e.trans (CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj 2 F).symm
  let H : Subgroup (PSL2MatrixGroup F) :=
    (B.map (Id2519.fixSubgroup α).subtype).map e'.toMonoidHom
  let eH : ↥B ≃* ↥H := (B.equivMapOfInjective _ (Id2519.fixSubgroup α).subtype_injective).trans
    (Subgroup.equivMapOfInjective _ e'.toMonoidHom e'.injective)
  have hHcard : Nat.card ↥H = Nat.card ↥B := (Nat.card_congr eH.toEquiv).symm
  have hBq : CFSG.IsQuasisimple ↥B := hBc.1
  have hHq : CFSG.IsQuasisimple ↥H := CFSG.LocalCores.isQuasisimple_of_mulEquiv eH hBq
  have hnsolv : ¬ Group.IsSolvable ↥H := by
    intro hsolv
    have : Group.IsPerfect ↥H := hHq.1
    have : Nontrivial ↥H := CFSG.LocalCores.isQuasisimple_nontrivial hHq
    exact Group.IsPerfect.not_isSolvable _ hsolv
  have hB2520 : 2520 ≤ Nat.card ↥B := Nat.le_of_dvd Nat.card_pos hB.dvd_card
  have hlt : Nat.card ↥B < Nat.card X := by
    have h1 : Nat.card ↥B ≤ Nat.card ↥(Id2519.fixSubgroup α) := Subgroup.card_le_card_group B
    have h2 := Subgroup.card_lt_of_lt (lt_top_iff_ne_top.2 (fixSubgroup_ne_top hne))
    rw [Subgroup.card_top] at h2
    omega
  have hXcard : Nat.card X = p ^ 1 * ((p ^ 1) ^ 2 - 1) / 2 := by
    rw [Nat.card_congr e'.toEquiv]
    exact card_psl2_odd (f := 1) hcard hp2
  rcases dickson_psl2_subgroup_list (p := p) (f := 1) hcard H with
    ⟨m, hm, hmc, hel⟩ | ⟨z, hz, hzc, hcyc⟩ | ⟨z, hz2, hz, ⟨ed⟩⟩ | ⟨-, ⟨eA4⟩⟩ | ⟨-, ⟨eS4⟩⟩ |
      ⟨-, ⟨eA5⟩⟩ | ⟨m, t', hm1, hmf, ht1, ht2, E, C, hE, hEel, hEcard, hCcyc, hCcard, hdisj, hsup,
        hfaith, φ, hφ, ⟨eS⟩⟩ | ⟨m, hmf, ⟨eL⟩⟩ | ⟨m, hmf, ⟨eG⟩⟩
  · exact hnsolv (Group.isSolvable_of_comm fun a b => hel.1.is_comm.comm a b)
  · exact hnsolv (Group.isSolvable_of_comm fun a b => hcyc.commGroup.mul_comm a b)
  · have : NeZero z := ⟨by omega⟩
    have : Group.IsSolvable (DihedralGroup z) :=
      CFSG.ProperTwoGeneratedCore.UnitaryKernels.isSolvable_dihedralGroup z
    exact hnsolv (Group.isSolvable_of_surjective (f := ed.symm.toMonoidHom) ed.symm.surjective)
  · have := hHcard ▸ Nat.card_congr eA4.toEquiv
    rw [card_alternatingFour'] at this
    omega
  · have := hHcard ▸ Nat.card_congr eS4.toEquiv
    rw [card_permFour] at this
    omega
  · have := hHcard ▸ Nat.card_congr eA5.toEquiv
    rw [card_alternatingFive'] at this
    omega
  ·
    have hE2 : Group.IsSolvable ↥E := Group.isSolvable_of_comm fun a b => hEel.1.is_comm.comm a b
    have hC2 : Group.IsSolvable ↥C := by
      have : CommGroup ↥C := IsCyclic.commGroup
      infer_instance
    have hS : Group.IsSolvable (↥E ⋊[φ] ↥C) :=
      Group.isSolvable_of_ker_le_range (SemidirectProduct.inl : ↥E →* (↥E ⋊[φ] ↥C))
        SemidirectProduct.rightHom (SemidirectProduct.range_inl_eq_ker_rightHom).ge
    exact hnsolv (Group.isSolvable_of_surjective (f := eS.symm.toMonoidHom) eS.symm.surjective)
  ·
    have hm1 : m = 1 := Nat.dvd_one.mp hmf
    subst hm1
    have h1 : Nat.card ↥H = Nat.card (PSL2MatrixGroup (GaloisField p 1)) :=
      Nat.card_congr eL.toEquiv
    have h2 : Nat.card ↥B = Nat.card X := by
      rw [← hHcard, h1, card_psl2_galoisField hp2 one_ne_zero, hXcard]
      norm_num
    exact hlt.ne h2
  · have := Nat.dvd_one.mp hmf
    omega

theorem noA7Fix_suzuki {X : Type} [Group X] [Finite X] {f : ℕ}
    (h : Blueprint.SuzukiModel X 2 f) : NoA7Fix X := by
  obtain ⟨-, a, -, F, _, _, hfa, hcard, ⟨e⟩⟩ := h
  subst hfa
  refine noA7Fix_of_not_dvd fun h3 => ?_
  have hXcard : Nat.card X = (2 ^ (2 * a + 1)) ^ 2 * (2 ^ (2 * a + 1) - 1) *
      ((2 ^ (2 * a + 1)) ^ 2 + 1) := by
    rw [Nat.card_congr e.toEquiv]
    exact CFSG.LieType.Ree.suzuki_order hcard
  rw [hXcard] at h3
  exact Id2519.not_three_dvd_suzuki_order a ((show 3 ∣ 2520 by norm_num).trans h3)

theorem noA7Fix_psl3_two
    {X : Type} [Group X] [Finite X]
    (h : Assembly.LowTwoRank.StatedClassicalModel X .PSL 3 2 1) : NoA7Fix X :=
  noA7Fix_of_card_le (by rw [Id2519.card_of_psl_three_two h]; norm_num)

theorem noA7Fix_psl33
    {X : Type} [Group X] [Finite X]
    (h : Assembly.LowTwoRank.StatedClassicalModel X .PSL 3 3 1) : NoA7Fix X :=
  noA7Fix_of_not_dvd (by rw [Unc25G2.A312Sub.card_psl_three_three h]; norm_num)

theorem noA7Fix_psu33 {X : Type} [Group X] [Finite X]
    (h : Assembly.LowTwoRank.StatedClassicalModel X .PSU 3 3 1) : NoA7Fix X :=
  noA7Fix_of_not_dvd (by rw [Id2519.card_psu_three_three h]; norm_num)

end E6

end CFSG.Quasithin
